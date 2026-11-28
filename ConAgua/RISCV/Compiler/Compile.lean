import ConAgua.L.Semantics
import ConAgua.RISCV.Compiler.Asm
import Std.Data.HashMap
import Std.Data.HashSet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Single-Pass `MiniL → RV64` Compiler (`ConAgua.RISCV.Compiler.Compile`)

Compiles `ConAgua.RISCV.MiniL` programs to pure RV64 assembly (`List AsmItem`) and links
to `Array (BitVec 32)` via `ConAgua.RISCV.Compiler.link`.

## Register & ABI Pins
- `gp` (`x3`): descriptor table base `T`
- `s0` (`x8`): remaining fuel
- `sp` (`x2`): current L stack / frame pointer
- `s1` (`x9`): saved trampoline `sp`
- `s2` (`x18`): saved trampoline `ra`
- `t0..t6`: scratch
- `a0..a7`: expression result (`a0`), function results (`a0..a7`), and stub arguments (`a0..a5`)
- Exit: LP64 function return (`ret`) restoring `[sp, ra, gp, tp, s0..s11]` with `(a0 = verdict/code, a1 = status)` where `0 = ok`, `1 = exhausted/decline`, `2 = abort/error`.
-/

namespace ConAgua.RISCV.Compiler

open ConAgua.RISCV.RV64
open _root_.L

/-! ## 1. Descriptor Table (`Tab`) & Static Analysis -/

/-- Binary search tree mapping `TieredArray.code ↦ descriptor position`. -/
inductive NTree where
  | leaf
  | node (l : NTree) (k v : Nat) (r : NTree)
  deriving Repr, Inhabited, DecidableEq

def NTree.find (k : Nat) : NTree → Option Nat
  | .leaf => none
  | .node l k' v r => if k < k' then find k l else if k = k' then some v else find k r

def NTree.ofSorted (a : Array (Nat × Nat)) (lo hi : Nat) : NTree :=
  if lo < hi then
    let m := (lo + hi) / 2
    .node (ofSorted a lo m) a[m]!.1 a[m]!.2 (ofSorted a (m + 1) hi)
  else .leaf
termination_by hi - lo

def maxRes : Nat := 8

/-- Descriptor table layout for a compiled `MiniL` program. -/
structure Tab where
  nb : Nat
  nw : Nat
  arrAt : List TieredArray
  lmap : NTree
  rom : List UInt8 := []
  nres : Nat := 1
  ng : Nat := 0
  deriving Repr, DecidableEq, Inhabited

def Tab.pos8 (t : Tab) (a : ArrId) : Nat :=
  (t.lmap.find (TieredArray.t0 a).code).getD 0

def Tab.pos64 (t : Tab) (s : TieredArray) : Nat :=
  (t.lmap.find s.code).getD 0

def Tab.wAt (t : Tab) (p : Nat) : TieredArray :=
  t.arrAt.getD p ⟨0, false⟩

def Tab.stackTop : Int := 0
def Tab.stackLimit : Int := 8
def Tab.dbase (_ : Tab) (p : Nat) : Int := 16 + 8 * (p : Int)
def Tab.dlen (t : Tab) (p : Nat) : Int := 16 + 8 * ((t.nb + t.nw : Nat) : Int) + 8 * (p : Int)
def Tab.dlen32 (t : Tab) (p : Nat) : Int := 16 + 16 * ((t.nb + t.nw : Nat) : Int) + 8 * (p : Int)

def Tab.base8 (t : Tab) (a : ArrId) : Int := t.dbase (t.pos8 a)
def Tab.len8 (t : Tab) (a : ArrId) : Int := t.dlen (t.pos8 a)
def Tab.base64 (t : Tab) (s : TieredArray) : Int := t.dbase (t.pos64 s)
def Tab.len64 (t : Tab) (s : TieredArray) : Int := t.dlen (t.pos64 s)
def Tab.len32 (t : Tab) (s : TieredArray) : Int := t.dlen32 (t.pos64 s)

def Tab.romWords (t : Tab) : Nat := (t.rom.length + 7) / 8
def Tab.romBase (t : Tab) : Int := 16 + 24 * ((t.nb + t.nw : Nat) : Int)
def Tab.nxres (t : Tab) : Nat := t.nres - maxRes
def Tab.resBase (t : Tab) : Int := t.romBase + 8 * (t.romWords : Int)
def Tab.resOff (t : Tab) (i : Nat) : Int := t.resBase + 8 * ((i - maxRes : Nat) : Int)
def Tab.globBase (t : Tab) : Int := t.resBase + 8 * (t.nxres : Int)
def Tab.globOff (t : Tab) (g : GVar) : Int := t.globBase + 8 * (g.id : Int)
def Tab.args (t : Tab) : Int := t.globBase + 8 * (t.ng : Int)
def Tab.saveBase (tab : Tab) (entryNparams : Nat := 0) : Int :=
  tab.args + 8 * Int.ofNat (max 1 entryNparams)

def layoutOf (bs : List ArrId) (ws : List (ArrId × Bool)) : List TieredArray :=
  bs.map TieredArray.t0 ++
    ws.flatMap fun (a, ti) => if ti then [TieredArray.t0 a, tier1 a] else [TieredArray.t0 a]

def lmapOf (l : List TieredArray) : NTree :=
  let es := (l.zipIdx.map fun (s, i) => (s.code, i)).toArray.qsort (fun x y => x.1 < y.1)
  NTree.ofSorted es 0 es.size

def Tab.ofArrs (bs : List ArrId) (ws : List (ArrId × Bool))
    (rom : List UInt8 := []) (nres : Nat := 1) (ng : Nat := 0) : Tab :=
  let l := layoutOf bs ws
  { nb := bs.length
    nw := l.length - bs.length
    arrAt := l
    lmap := lmapOf l
    rom := rom
    nres := max 1 nres
    ng := ng }

def romIdx (d : List UInt8) : List UInt8 → Nat
  | [] => 0
  | b :: rom => if d.isPrefixOf (b :: rom) then 0 else romIdx d rom + 1

private def addUniq {α : Type} [DecidableEq α] (xs : List α) (x : α) : List α :=
  if x ∈ xs then xs else xs ++ [x]

private def collectExprInfo (e : Expr) :
    (List ArrId × List (ArrId × Bool) × List (List UInt8) × Nat × Nat) :=
  match e with
  | .const _ => ([], [], [], 0, 0)
  | .var x => ([], [], [], x + 1, 0)
  | .bin _ a b =>
    let (b1, w1, r1, v1, g1) := collectExprInfo a
    let (b2, w2, r2, v2, g2) := collectExprInfo b
    (b1 ++ b2, w1 ++ w2, r1 ++ r2, max v1 v2, max g1 g2)
  | .ld8 a i =>
    let (b, w, r, v, g) := collectExprInfo i
    (a :: b, w, r, v, g)
  | .ld64 a i =>
    let (b, w, r, v, g) := collectExprInfo i
    (b, (a, false) :: w, r, v, g)
  | .len8 a => ([a], [], [], 0, 0)
  | .len64 a => ([], [(a, false)], [], 0, 0)
  | .cmpw _ a b =>
    let (b1, w1, r1, v1, g1) := collectExprInfo a
    let (b2, w2, r2, v2, g2) := collectExprInfo b
    (b1 ++ b2, w1 ++ w2, r1 ++ r2, max v1 v2, max g1 g2)
  | .ldc d i =>
    let (b, w, r, v, g) := collectExprInfo i
    (b, w, d :: r, v, g)
  | .glob gv => ([], [], [], 0, gv.id + 1)
  | .ld64t a t i | .ld32t a t i | .ld32h a t i _ =>
    let (b1, w1, r1, v1, g1) := collectExprInfo t
    let (b2, w2, r2, v2, g2) := collectExprInfo i
    (b1 ++ b2, (a, true) :: w1 ++ w2, r1 ++ r2, max v1 v2, max g1 g2)
  | .len64t a t =>
    let (b, w, r, v, g) := collectExprInfo t
    (b, (a, true) :: w, r, v, g)
  | .ld8x8 src i =>
    let (b, w, r, v, g) := collectExprInfo i
    match src with
    | .arr a => (a :: b, w, r, v, g)
    | .rom d => (b, w, d :: r, v, g)

private def collectCondInfo : Cond →
    (List ArrId × List (ArrId × Bool) × List (List UInt8) × Nat × Nat)
  | .cmp _ a b => collectExprInfo (.cmpw .eq a b)
  | .and p q | .or p q =>
    let (b1, w1, r1, v1, g1) := collectCondInfo p
    let (b2, w2, r2, v2, g2) := collectCondInfo q
    (b1 ++ b2, w1 ++ w2, r1 ++ r2, max v1 v2, max g1 g2)
  | .not p => collectCondInfo p

private def collectWArrInfo : WArr →
    (List ArrId × List (ArrId × Bool) × List (List UInt8) × Nat × Nat)
  | .plain a => ([], [(a, false)], [], 0, 0)
  | .tier a t =>
    let (b, w, r, v, g) := collectExprInfo t
    (b, (a, true) :: w, r, v, g)

private def mergeInfo5
    (x y : List ArrId × List (ArrId × Bool) × List (List UInt8) × Nat × Nat) :
    (List ArrId × List (ArrId × Bool) × List (List UInt8) × Nat × Nat) :=
  (x.1 ++ y.1, x.2.1 ++ y.2.1, x.2.2.1 ++ y.2.2.1, max x.2.2.2.1 y.2.2.2.1, max x.2.2.2.2 y.2.2.2.2)

private def collectExprsInfo (es : List Expr) :
    (List ArrId × List (ArrId × Bool) × List (List UInt8) × Nat × Nat) :=
  es.foldl (fun acc e => mergeInfo5 acc (collectExprInfo e)) ([], [], [], 0, 0)

private def collectStmtInfo : Stmt →
    (List ArrId × List (ArrId × Bool) × List (List UInt8) × Nat × Nat × Nat)
  | .skip | .brk => ([], [], [], 0, 0, 1)
  | .set x e =>
    let (b, w, r, v, g) := collectExprInfo e
    (b, w, r, max (x + 1) v, g, 1)
  | .st8 a i e =>
    let (b, w, r, v, g) := mergeInfo5 (collectExprInfo i) (collectExprInfo e)
    (a :: b, w, r, v, g, 1)
  | .st64 a i e =>
    let (b, w, r, v, g) := mergeInfo5 (collectExprInfo i) (collectExprInfo e)
    (b, (a, false) :: w, r, v, g, 1)
  | .seq s t | .ite _ s t =>
    let (b1, w1, r1, v1, g1, n1) := collectStmtInfo s
    let (b2, w2, r2, v2, g2, n2) := collectStmtInfo t
    (b1 ++ b2, w1 ++ w2, r1 ++ r2, max v1 v2, max g1 g2, max n1 n2)
  | .while c s =>
    let (bc, wc, rc, vc, gc) := collectCondInfo c
    let (bs, ws, rs, vs, gs, ns) := collectStmtInfo s
    (bc ++ bs, wc ++ ws, rc ++ rs, max vc vs, max gc gs, ns)
  | .ret es =>
    let (b, w, r, v, g) := collectExprsInfo es
    (b, w, r, v, g, max 1 es.length)
  | .call xs _ args =>
    let (b, w, r, v, g) := collectExprsInfo args
    let vx := xs.foldl (fun m x => max m (x + 1)) 0
    (b, w, r, max v vx, g, max 1 xs.length)
  | .abort e =>
    let (b, w, r, v, g) := collectExprInfo e
    (b, w, r, v, g, 1)
  | .gset gv e =>
    let (b, w, r, v, g) := collectExprInfo e
    (b, w, r, v, max (gv.id + 1) g, 1)
  | .st64t a t i e | .st32t a t i e =>
    let (b, w, r, v, g) := mergeInfo5 (collectExprInfo t) (mergeInfo5 (collectExprInfo i) (collectExprInfo e))
    (b, (a, true) :: w, r, v, g, 1)
  | .copy64 d di s si n =>
    let info := mergeInfo5 (collectWArrInfo d)
      (mergeInfo5 (collectExprInfo di) (mergeInfo5 (collectWArrInfo s)
        (mergeInfo5 (collectExprInfo si) (collectExprInfo n))))
    (info.1, info.2.1, info.2.2.1, info.2.2.2.1, info.2.2.2.2, 1)
  | .copy8w d di s si n =>
    let sInfo := match s with | .arr a => ([a], [], [], 0, 0) | .rom d => ([], [], [d], 0, 0)
    let info := mergeInfo5 (collectWArrInfo d)
      (mergeInfo5 (collectExprInfo di) (mergeInfo5 sInfo
        (mergeInfo5 (collectExprInfo si) (collectExprInfo n))))
    (info.1, info.2.1, info.2.2.1, info.2.2.2.1, info.2.2.2.2, 1)
  | .scan8 x s i e c =>
    let sInfo := match s with | .arr a => ([a], [], [], 0, 0) | .rom d => ([], [], [d], 0, 0)
    let info := mergeInfo5 sInfo (mergeInfo5 (collectExprInfo i) (collectExprInfo e))
    (info.1, info.2.1, c :: info.2.2.1, max (x + 1) info.2.2.2.1, info.2.2.2.2, 1)

private def collectCondStmtInfo : Stmt →
    (List ArrId × List (ArrId × Bool) × List (List UInt8) × Nat × Nat × Nat)
  | .ite c s t =>
    let (bc, wc, rc, vc, gc) := collectCondInfo c
    let (bs1, ws1, rs1, vs1, gs1, ns1) := collectCondStmtInfo s
    let (bs2, ws2, rs2, vs2, gs2, ns2) := collectCondStmtInfo t
    (bc ++ bs1 ++ bs2, wc ++ ws1 ++ ws2, rc ++ rs1 ++ rs2,
      max vc (max vs1 vs2), max gc (max gs1 gs2), max ns1 ns2)
  | .while c s =>
    let (bc, wc, rc, vc, gc) := collectCondInfo c
    let (bs, ws, rs, vs, gs, ns) := collectCondStmtInfo s
    (bc ++ bs, wc ++ ws, rc ++ rs, max vc vs, max gc gs, ns)
  | .seq s t =>
    let (b1, w1, r1, v1, g1, n1) := collectCondStmtInfo s
    let (b2, w2, r2, v2, g2, n2) := collectCondStmtInfo t
    (b1 ++ b2, w1 ++ w2, r1 ++ r2, max v1 v2, max g1 g2, max n1 n2)
  | s => collectStmtInfo s

private def mergeWordArrs (ws : List (ArrId × Bool)) : List (ArrId × Bool) :=
  ws.foldl (fun acc (a, ti) =>
    match acc.find? (fun p => p.1 == a) with
    | none => acc ++ [(a, ti)]
    | some (_, oldTi) =>
      if !oldTi && ti then acc.map (fun p => if p.1 == a then (a, true) else p) else acc) []

private def appendRomBytes (rom : List UInt8) (d : List UInt8) : List UInt8 :=
  if romIdx d rom < rom.length || d.isEmpty then rom else rom ++ d

/-- Derive a default `Tab` from a `Prog` (collecting all byte/word arrays, ROMs, results, globals). -/
def Tab.ofProg (p : Prog) : Tab :=
  let (bs, ws, rs, _, ng, nres) := p.foldl (fun acc (_, fd) =>
    let info := collectCondStmtInfo fd.body
    (acc.1 ++ info.1, acc.2.1 ++ info.2.1, acc.2.2.1 ++ info.2.2.1,
      max acc.2.2.2.1 info.2.2.2.1, max acc.2.2.2.2.1 info.2.2.2.2.1,
      max acc.2.2.2.2.2 info.2.2.2.2.2)) ([], [], [], 0, 0, 1)
  let bUniq := bs.foldl addUniq []
  let wUniq := mergeWordArrs ws
  let rom := rs.foldl appendRomBytes []
  Tab.ofArrs bUniq wUniq rom nres ng

/-- Compute maximum expression temporary stack depth needed by `e`. -/
def maxTempsExpr : Expr → Nat
  | .const _ | .var _ | .len8 _ | .len64 _ | .glob _ => 0
  | .ld8 _ i | .ld64 _ i | .ldc _ i | .len64t _ i | .ld8x8 _ i => maxTempsExpr i
  | .bin _ a b | .cmpw _ a b | .ld64t _ a b | .ld32t _ a b | .ld32h _ a b _ =>
    max (maxTempsExpr a) (1 + maxTempsExpr b)

def maxTempsCond : Cond → Nat
  | .cmp _ a b => max (maxTempsExpr a) (1 + maxTempsExpr b)
  | .and p q | .or p q => max (maxTempsCond p) (maxTempsCond q)
  | .not p => maxTempsCond p

def maxTempsExprs (es : List Expr) : Nat :=
  (es.zipIdx).foldl (fun acc (e, idx) => max acc (idx + max 1 (maxTempsExpr e))) 0

def maxTempsStmt : Stmt → Nat
  | .skip | .brk => 0
  | .set _ e | .abort e | .gset _ e => maxTempsExpr e
  | .st8 _ i e | .st64 _ i e => max (maxTempsExpr i) (1 + maxTempsExpr e)
  | .seq s t => max (maxTempsStmt s) (maxTempsStmt t)
  | .ite c s t => max (maxTempsCond c) (max (maxTempsStmt s) (maxTempsStmt t))
  | .while c s => max (maxTempsCond c) (maxTempsStmt s)
  | .ret es => maxTempsExprs es
  | .call _ _ args => maxTempsExprs args
  | .st64t _ t i e | .st32t _ t i e =>
    max (maxTempsExpr t) (max (1 + maxTempsExpr i) (2 + maxTempsExpr e))
  | .copy64 d di s si n =>
    let dt := match d with | .plain _ => 0 | .tier _ t => maxTempsExpr t
    let st := match s with | .plain _ => 0 | .tier _ t => 2 + maxTempsExpr t
    max dt (max (1 + maxTempsExpr di) (max st (max (3 + maxTempsExpr si) (4 + max 1 (maxTempsExpr n)))))
  | .copy8w d di _ si n =>
    let dt := match d with | .plain _ => 0 | .tier _ t => maxTempsExpr t
    max dt (max (1 + maxTempsExpr di) (max (3 + maxTempsExpr si) (4 + max 1 (maxTempsExpr n))))
  | .scan8 _ _ i e _ => max (maxTempsExpr i) (1 + maxTempsExpr e)

def numLocalsFn (fd : FunDecl) : Nat :=
  let (_, _, _, maxV, _, _) := collectCondStmtInfo fd.body
  max fd.nlocals (max fd.nparams maxV)

/-! ## 2. Offset & Memory Addressing Helpers -/

def fitsImm12Int (off : Int) : Bool :=
  (-2048 ≤ off) && (off ≤ 2047)

/-- True iff `off` fits two signed 12-bit positive steps `(2047 + rem)` with `1 ≤ rem ≤ 2047`. -/
def fitsDoublePos12Int (off : Int) : Bool :=
  (2048 ≤ off) && (off ≤ 4094)

/-- Split a 32-bit offset `off` into `(hi20, lo12)` satisfying `sextImmU hi20 + sextImm12 lo12 = ofInt 64 off`. -/
def splitMemOff32? (off : Int) : Option (BitVec 20 × BitVec 12) :=
  let off32 : BitVec 32 := BitVec.ofInt 32 off
  let lo12 : BitVec 12 := off32.extractLsb' 0 12
  let hi20 : BitVec 20 := (off32 + 0x800#32).extractLsb' 12 20
  if sextImmU hi20 + sextImm12 lo12 == BitVec.ofInt 64 off then
    some (hi20, lo12)
  else none

def addImmOff (rd rs tmp : Reg) (off : Int) : List AsmItem :=
  if off == 0 then
    if rd == rs then [] else [Asm.mv rd rs]
  else if fitsImm12Int off then
    [Asm.addi rd rs (BitVec.ofInt 12 off)]
  else if fitsDoublePos12Int off then
    [Asm.addi rd rs 2047#12, Asm.addi rd rd (BitVec.ofInt 12 (off - 2047))]
  else
    li tmp (BitVec.ofInt 64 off) ++ [Asm.add rd rs tmp]

def loadMemOff (op : LoadOp) (rd base tmp : Reg) (off : Int) : List AsmItem :=
  if fitsImm12Int off then
    [Asm.raw (.load op rd base (BitVec.ofInt 12 off))]
  else if fitsDoublePos12Int off then
    [Asm.addi tmp base 2047#12, Asm.raw (.load op rd tmp (BitVec.ofInt 12 (off - 2047)))]
  else match splitMemOff32? off with
  | some (hi20, lo12) =>
    [Asm.raw (.lui tmp hi20), Asm.add tmp base tmp, Asm.raw (.load op rd tmp lo12)]
  | none =>
    li tmp (BitVec.ofInt 64 off) ++ [Asm.add tmp base tmp, Asm.raw (.load op rd tmp 0#12)]

def storeMemOff (op : StoreOp) (base rs tmp : Reg) (off : Int) : List AsmItem :=
  if fitsImm12Int off then
    [Asm.raw (.store op base rs (BitVec.ofInt 12 off))]
  else if fitsDoublePos12Int off then
    [Asm.addi tmp base 2047#12, Asm.raw (.store op tmp rs (BitVec.ofInt 12 (off - 2047)))]
  else match splitMemOff32? off with
  | some (hi20, lo12) =>
    [Asm.raw (.lui tmp hi20), Asm.add tmp base tmp, Asm.raw (.store op tmp rs lo12)]
  | none =>
    li tmp (BitVec.ofInt 64 off) ++ [Asm.add tmp base tmp, Asm.raw (.store op tmp rs 0#12)]

/-- `gp`-relative load that reuses hoisted `t5 = gp + 2047` for `[2048, 4094]` offsets when enabled. -/
def loadMemOffGp (useT5 : Bool) (op : LoadOp) (rd tmp : Reg) (off : Int) : List AsmItem :=
  if useT5 && fitsDoublePos12Int off then
    [Asm.raw (.load op rd AbiReg.t5 (BitVec.ofInt 12 (off - 2047)))]
  else
    loadMemOff op rd AbiReg.gp tmp off

/-- `gp`-relative store that reuses hoisted `t5 = gp + 2047` for `[2048, 4094]` offsets when enabled. -/
def storeMemOffGp (useT5 : Bool) (op : StoreOp) (rs tmp : Reg) (off : Int) : List AsmItem :=
  if useT5 && fitsDoublePos12Int off then
    [Asm.raw (.store op AbiReg.t5 rs (BitVec.ofInt 12 (off - 2047)))]
  else
    storeMemOff op AbiReg.gp rs tmp off

def slotOff (idx : Nat) : Int :=
  8 * ((1 + idx : Nat) : Int)

def resReg (i : Nat) : Reg :=
  match i with
  | 0 => AbiReg.a0
  | 1 => AbiReg.a1
  | 2 => AbiReg.a2
  | 3 => AbiReg.a3
  | 4 => AbiReg.a4
  | 5 => AbiReg.a5
  | 6 => AbiReg.a6
  | _ => AbiReg.a7

/-! ## 3. Code Generation (`compileE`, `compileC`, `compileS`) -/

def errLabel : String := "ca_error"
def exhaustedLabel : String := "ca_exhausted"
def abortLabel : String := "ca_abort"
def enterLabel : String := "ca_enter"
def startLabel : String := "ca_start"
def retRestoreLabel : String := "ca_ret_restore"

/-- All 16 caller registers saved on entry and restored on function return (`128` bytes):
    `sp, ra, gp, tp, s0..s11`. Covers every register in `RV64.lp64CalleeSaved` plus `ra`. -/
def callerSaveRegs : List Reg :=
  [AbiReg.sp, AbiReg.ra, AbiReg.gp, AbiReg.tp,
   AbiReg.s0, AbiReg.s1, AbiReg.s2, AbiReg.s3,
   AbiReg.s4, AbiReg.s5, AbiReg.s6, AbiReg.s7,
   AbiReg.s8, AbiReg.s9, AbiReg.s10, AbiReg.s11]

/-- Save all 16 registers in `callerSaveRegs` into `[base + saveOff, base + saveOff + 128)`.
    Uses only scratch registers `t0`, `t1`. -/
def callerSaveAsm (base : Reg) (saveOff : Int) : List AsmItem :=
  addImmOff AbiReg.t0 base AbiReg.t1 saveOff ++
  (callerSaveRegs.zipIdx).map fun (r, i) => Asm.sd AbiReg.t0 r (BitVec.ofNat 12 (8 * i))

/-- Restore all 16 registers in `callerSaveRegs` from `[base + saveOff, base + saveOff + 128)`
    and return via `Asm.ret` (`jalr zero, ra, 0`). Uses only scratch registers `t0`, `t1` and
    leaves all argument/result registers `a0..a7` and memory untouched. -/
def callerRestoreRetAsm (base : Reg) (saveOff : Int) : List AsmItem :=
  addImmOff AbiReg.t0 base AbiReg.t1 saveOff ++
  ((callerSaveRegs.zipIdx).map fun (r, i) => Asm.ld r AbiReg.t0 (BitVec.ofNat 12 (8 * i))) ++
  [Asm.ret]

def fnLabel (f : FnName) : String := "fn_" ++ f

/-- Returns `some sh` (`sh < 64`) when `w = 2 ^ sh` (checked explicitly against `1#64 <<< sh`). -/
def isPow2Shift64 (w : UInt64) : Option (BitVec 6) :=
  let k := ctz64 w.toBitVec
  if k < 64 && w.toBitVec == (1#64 <<< k) then some (BitVec.ofNat 6 k) else none

/-- Emit `rd := rs * w` using `tmp` as scratch (`tmp ≠ rd`, `tmp ≠ rs`, `rd ≠ zero`).
    Replaces `0`, `1`, powers of two, and `2^k ± 1` multipliers (`≤ 2` words, zero code bloat
    vs `li+mul`) with shift-add/sub sequences, falling back to hardware `MUL`. -/
def emitMulConstTo (rd rs tmp : Reg) (w : UInt64) : List AsmItem :=
  let n := w.toNat
  if n == 0 then [Asm.addi rd AbiReg.zero 0#12]
  else if n == 1 then (if rd == rs then [] else [Asm.mv rd rs])
  else match isPow2Shift64 w with
  | some sh => [Asm.slli rd rs sh]
  | none =>
    if n == 3 then [Asm.slli tmp rs 1#6, Asm.add rd rs tmp]
    else if n == 5 then [Asm.slli tmp rs 2#6, Asm.add rd rs tmp]
    else if n == 7 then [Asm.slli tmp rs 3#6, Asm.sub rd tmp rs]
    else if n == 9 then [Asm.slli tmp rs 3#6, Asm.add rd rs tmp]
    else if n == 15 then [Asm.slli tmp rs 4#6, Asm.sub rd tmp rs]
    else if n == 17 then [Asm.slli tmp rs 4#6, Asm.add rd rs tmp]
    else if n == 255 then [Asm.slli tmp rs 8#6, Asm.sub rd tmp rs]
    else if n == 257 then [Asm.slli tmp rs 8#6, Asm.add rd rs tmp]
    else li tmp (BitVec.ofNat 64 n) ++ [Asm.mul rd rs tmp]

/-- Emit `rd := rd * w` using `tmp` as scratch (`rd ≠ tmp`, neither is `zero`). -/
def emitMulConst (rd tmp : Reg) (w : UInt64) : List AsmItem :=
  emitMulConstTo rd rd tmp w

/-- Emit a single register-register ALU/M-extension instruction for `op`. -/
def emitBinOp (op : BinOp) (rd rs1 rs2 : Reg) : AsmItem :=
  match op with
  | .add   => Asm.add rd rs1 rs2
  | .sub   => Asm.sub rd rs1 rs2
  | .and   => Asm.and rd rs1 rs2
  | .or    => Asm.or rd rs1 rs2
  | .xor   => Asm.xor rd rs1 rs2
  | .shl   => Asm.sll rd rs1 rs2
  | .shr   => Asm.srl rd rs1 rs2
  | .mul   => Asm.mul rd rs1 rs2
  | .mulhi => Asm.mulhu rd rs1 rs2

/-- Returns `some sh` (`1 ≤ sh ≤ 52`) when `w = (1 <<< (64 - sh)) - 1`, i.e., `w` is a
    contiguous low-bit mask of `12..63` bits (so `x &&& w = (x <<< sh) >>> sh`). -/
def lowMaskShift? (w : UInt64) : Option (BitVec 6) :=
  let n := w.toNat
  if n == 0 || n == 0xffffffffffffffff then none
  else
    let k := ctz64 (w.toBitVec + 1#64)
    if 12 ≤ k && k < 64 && w.toBitVec == (1#64 <<< k) - 1#64 then
      some (BitVec.ofNat 6 (64 - k))
    else none

/-- Emit `rd := op.eval rs w` using `t0` as scratch (`w` on RHS; `rd ≠ zero, t0`; `rs ≠ t0`). -/
def emitBinConstRhsTo (rd rs : Reg) (op : BinOp) (w : UInt64) : List AsmItem :=
  let bv : BitVec 64 := w.toBitVec
  let mvIf := if rd == rs then [] else [Asm.mv rd rs]
  match op with
  | .add =>
    if w == 0 then mvIf
    else if fitsImm12 bv then [Asm.addi rd rs (bv.extractLsb' 0 12)]
    else li AbiReg.t0 bv ++ [Asm.add rd rs AbiReg.t0]
  | .sub =>
    if w == 0 then mvIf
    else
      let neg := -bv
      if fitsImm12 neg then [Asm.addi rd rs (neg.extractLsb' 0 12)]
      else li AbiReg.t0 bv ++ [Asm.sub rd rs AbiReg.t0]
  | .and =>
    if w == 0 then [Asm.addi rd AbiReg.zero 0#12]
    else if w == 0xffffffffffffffff then mvIf
    else if fitsImm12 bv then [Asm.andi rd rs (bv.extractLsb' 0 12)]
    else match lowMaskShift? w with
      | some sh => [Asm.slli rd rs sh, Asm.srli rd rd sh]
      | none => li AbiReg.t0 bv ++ [Asm.and rd rs AbiReg.t0]
  | .or =>
    if w == 0 then mvIf
    else if fitsImm12 bv then [Asm.ori rd rs (bv.extractLsb' 0 12)]
    else li AbiReg.t0 bv ++ [Asm.or rd rs AbiReg.t0]
  | .xor =>
    if w == 0 then mvIf
    else if fitsImm12 bv then [Asm.xori rd rs (bv.extractLsb' 0 12)]
    else li AbiReg.t0 bv ++ [Asm.xor rd rs AbiReg.t0]
  | .shl =>
    let sh := w.toNat % 64
    if sh == 0 then mvIf
    else [Asm.slli rd rs (BitVec.ofNat 6 sh)]
  | .shr =>
    let sh := w.toNat % 64
    if sh == 0 then mvIf
    else [Asm.srli rd rs (BitVec.ofNat 6 sh)]
  | .mul => emitMulConstTo rd rs AbiReg.t0 w
  | .mulhi =>
    if w == 0 then [Asm.addi rd AbiReg.zero 0#12]
    else li AbiReg.t0 bv ++ [Asm.mulhu rd rs AbiReg.t0]

/-- Emit `a0 := op.eval a0 w` using `t0` as scratch (`w` on RHS). -/
def emitBinConstRhs (op : BinOp) (w : UInt64) : List AsmItem :=
  emitBinConstRhsTo AbiReg.a0 AbiReg.a0 op w

/-- Pure, never-trapping leaf expression directly emitted into `rd` using `tmp` as scratch.
    Modifies only `rd` and `tmp`, preserves memory and all other registers. -/
def emitSimpleExpr (tab : Tab) (rd tmp : Reg) : Expr → Option (List AsmItem)
  | .const w => some (li rd (BitVec.ofNat 64 w.toNat))
  | .var x   => some (loadMemOff .ld rd AbiReg.sp tmp (slotOff x))
  | .len8 a  => some (loadMemOff .ld rd AbiReg.gp tmp (tab.len8 a))
  | .len64 a => some (loadMemOff .ld rd AbiReg.gp tmp (tab.len64 (TieredArray.t0 a)))
  | .glob g  => some (loadMemOff .ld rd AbiReg.gp tmp (tab.globOff g))
  | _        => none

/-- Emit materialized comparison `rd := (c.evalW rL rR)`. -/
def emitCmpwTo (rd : Reg) (c : Cmp) (rL rR : Reg) : List AsmItem :=
  match c with
  | .eq  => [Asm.sub rd rL rR, Asm.sltiu rd rd 1#12]
  | .ne  => [Asm.sub rd rL rR, Asm.sltu rd AbiReg.zero rd]
  | .ult => [Asm.sltu rd rL rR]
  | .ule => [Asm.sltu rd rR rL, Asm.xori rd rd 1#12]
  | .slt => [Asm.slt rd rL rR]
  | .sle => [Asm.slt rd rR rL, Asm.xori rd rd 1#12]

/-- Emit materialized comparison `a0 := (c.evalW rL rR)`. -/
def emitCmpw (c : Cmp) (rL rR : Reg) : List AsmItem :=
  emitCmpwTo AbiReg.a0 c rL rR

/-- Emit conditional branch jumping to `target` iff `c.eval rL rR == want`. -/
def brCmp (op : Cmp) (want : Bool) (rL rR : Reg) (target : String) : AsmItem :=
  match op, want with
  | .eq, true   | .ne, false  => Asm.beq rL rR target
  | .ne, true   | .eq, false  => Asm.bne rL rR target
  | .ult, true  => Asm.bltu rL rR target
  | .ult, false => Asm.bgeu rL rR target
  | .ule, true  => Asm.bgeu rR rL target
  | .ule, false => Asm.bltu rR rL target
  | .slt, true  => Asm.blt rL rR target
  | .slt, false => Asm.bge rL rR target
  | .sle, true  => Asm.bge rR rL target
  | .sle, false => Asm.blt rR rL target

/-- Extract literal word when `e = .const w`, avoiding nested pattern splitters. -/
def _root_.L.Expr.constVal? : Expr → Option UInt64
  | .const w => some w
  | _        => none

/-- Compile expression `e` leaving its value in `a0`.
    Preserves `gp`, `s0`, `sp`, `s1`, `s2`, and frame slots `< nlocals + tmp`. -/
def compileE (tab : Tab) (nlocals : Nat) (tmp : Nat) : Expr → List AsmItem
  | .const w =>
    li AbiReg.a0 (BitVec.ofNat 64 w.toNat)
  | .var x =>
    loadMemOff .ld AbiReg.a0 AbiReg.sp AbiReg.t0 (slotOff x)
  | .len8 a =>
    loadMemOff .ld AbiReg.a0 AbiReg.gp AbiReg.t0 (tab.len8 a)
  | .len64 a =>
    loadMemOff .ld AbiReg.a0 AbiReg.gp AbiReg.t0 (tab.len64 (TieredArray.t0 a))
  | .glob g =>
    loadMemOff .ld AbiReg.a0 AbiReg.gp AbiReg.t0 (tab.globOff g)
  | .bin op a b =>
    match b.constVal? with
    | some w => compileE tab nlocals tmp a ++ emitBinConstRhs op w
    | none =>
      match a.constVal? with
      | some w =>
        let cb := compileE tab nlocals tmp b
        match op with
        | .add | .and | .or | .xor | .mul | .mulhi =>
          cb ++ emitBinConstRhs op w
        | .sub =>
          if w == 0 then cb ++ [Asm.sub AbiReg.a0 AbiReg.zero AbiReg.a0]
          else cb ++ li AbiReg.t0 w.toBitVec ++ [Asm.sub AbiReg.a0 AbiReg.t0 AbiReg.a0]
        | .shl => cb ++ li AbiReg.t0 w.toBitVec ++ [Asm.sll AbiReg.a0 AbiReg.t0 AbiReg.a0]
        | .shr => cb ++ li AbiReg.t0 w.toBitVec ++ [Asm.srl AbiReg.a0 AbiReg.t0 AbiReg.a0]
      | none =>
        match emitSimpleExpr tab AbiReg.t0 AbiReg.t1 b with
        | some cb =>
          compileE tab nlocals tmp a ++ cb ++ [emitBinOp op AbiReg.a0 AbiReg.a0 AbiReg.t0]
        | none =>
          match emitSimpleExpr tab AbiReg.t0 AbiReg.t1 a with
          | some ca =>
            compileE tab nlocals tmp b ++ ca ++ [emitBinOp op AbiReg.a0 AbiReg.t0 AbiReg.a0]
          | none =>
            compileE tab nlocals tmp a ++
            storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + tmp)) ++
            compileE tab nlocals (tmp + 1) b ++
            loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nlocals + tmp)) ++
            [emitBinOp op AbiReg.a0 AbiReg.t0 AbiReg.a0]
  | .cmpw c a b =>
    if c == .eq && b.constVal? == some 0 then
      compileE tab nlocals tmp a ++ [Asm.sltiu AbiReg.a0 AbiReg.a0 1#12]
    else if c == .eq && a.constVal? == some 0 then
      compileE tab nlocals tmp b ++ [Asm.sltiu AbiReg.a0 AbiReg.a0 1#12]
    else if c == .ne && b.constVal? == some 0 then
      compileE tab nlocals tmp a ++ [Asm.sltu AbiReg.a0 AbiReg.zero AbiReg.a0]
    else if c == .ne && a.constVal? == some 0 then
      compileE tab nlocals tmp b ++ [Asm.sltu AbiReg.a0 AbiReg.zero AbiReg.a0]
    else
      match emitSimpleExpr tab AbiReg.t0 AbiReg.t1 b with
      | some cb =>
        compileE tab nlocals tmp a ++ cb ++ emitCmpw c AbiReg.a0 AbiReg.t0
      | none =>
        match emitSimpleExpr tab AbiReg.t0 AbiReg.t1 a with
        | some ca =>
          compileE tab nlocals tmp b ++ ca ++ emitCmpw c AbiReg.t0 AbiReg.a0
        | none =>
          compileE tab nlocals tmp a ++
          storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + tmp)) ++
          compileE tab nlocals (tmp + 1) b ++
          loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nlocals + tmp)) ++
          emitCmpw c AbiReg.t0 AbiReg.a0
  | .ld8 a i =>
    compileE tab nlocals tmp i ++
    loadMemOff .ld AbiReg.t0 AbiReg.gp AbiReg.t1 (tab.len8 a) ++
    [Asm.bgeu AbiReg.a0 AbiReg.t0 errLabel] ++
    loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (tab.base8 a) ++
    [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.a0, Asm.lbu AbiReg.a0 AbiReg.t1 0#12]
  | .ld64 a i =>
    compileE tab nlocals tmp i ++
    loadMemOff .ld AbiReg.t0 AbiReg.gp AbiReg.t1 (tab.len64 (TieredArray.t0 a)) ++
    [Asm.bgeu AbiReg.a0 AbiReg.t0 errLabel] ++
    loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (tab.base64 (TieredArray.t0 a)) ++
    [Asm.slli AbiReg.t2 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2,
     Asm.ld AbiReg.a0 AbiReg.t1 0#12]
  | .ldc d i =>
    compileE tab nlocals tmp i ++
    li AbiReg.t0 (BitVec.ofNat 64 d.length) ++
    [Asm.bgeu AbiReg.a0 AbiReg.t0 errLabel] ++
    addImmOff AbiReg.t1 AbiReg.gp AbiReg.t2 (tab.romBase + (romIdx d tab.rom : Int)) ++
    [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.a0, Asm.lbu AbiReg.a0 AbiReg.t1 0#12]
  | .ld64t a t i =>
    match t.constVal? with
    | some w =>
      let s := tierA a w
      compileE tab nlocals tmp i ++
      loadMemOff .ld AbiReg.t2 AbiReg.gp AbiReg.t3 (tab.len64 s) ++
      [Asm.bgeu AbiReg.a0 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t3 (tab.base64 s) ++
      [Asm.slli AbiReg.t3 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3,
       Asm.ld AbiReg.a0 AbiReg.t1 0#12]
    | none =>
      let head := match emitSimpleExpr tab AbiReg.t0 AbiReg.t1 t with
        | some ct => compileE tab nlocals tmp i ++ ct
        | none =>
          compileE tab nlocals tmp t ++
          storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + tmp)) ++
          compileE tab nlocals (tmp + 1) i ++
          loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nlocals + tmp))
      head ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
       Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (tab.len64 (TieredArray.t0 a)) ++
      [Asm.bgeu AbiReg.a0 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t3 (tab.base64 (TieredArray.t0 a)) ++
      [Asm.slli AbiReg.t3 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3,
       Asm.ld AbiReg.a0 AbiReg.t1 0#12]
  | .len64t a t =>
    match t.constVal? with
    | some w =>
      loadMemOff .ld AbiReg.a0 AbiReg.gp AbiReg.t2 (tab.len64 (tierA a w))
    | none =>
      compileE tab nlocals tmp t ++
      [Asm.andi AbiReg.t0 AbiReg.a0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
       Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.a0 AbiReg.t1 AbiReg.t2 (tab.len64 (TieredArray.t0 a))
  | .ld8x8 src i =>
    let setupSrc := match src with
      | .arr a =>
        loadMemOff .ld AbiReg.t0 AbiReg.gp AbiReg.t2 (tab.len8 a) ++
        loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (tab.base8 a)
      | .rom d =>
        li AbiReg.t0 (BitVec.ofNat 64 d.length) ++
        addImmOff AbiReg.t1 AbiReg.gp AbiReg.t2 (tab.romBase + (romIdx d tab.rom : Int))
    let readBytes :=
      [Asm.lbu AbiReg.a0 AbiReg.t1 7#12] ++
      ([6, 5, 4, 3, 2, 1, 0].flatMap fun k =>
        [Asm.lbu AbiReg.t2 AbiReg.t1 (BitVec.ofInt 12 (k : Int)),
         Asm.slli AbiReg.a0 AbiReg.a0 8#6,
         Asm.or AbiReg.a0 AbiReg.a0 AbiReg.t2])
    compileE tab nlocals tmp i ++
    setupSrc ++
    [Asm.addi AbiReg.t2 AbiReg.zero 8#12,
     Asm.bltu AbiReg.t0 AbiReg.t2 errLabel,
     Asm.addi AbiReg.t0 AbiReg.t0 (-8#12),
     Asm.bltu AbiReg.t0 AbiReg.a0 errLabel,
     Asm.add AbiReg.t1 AbiReg.t1 AbiReg.a0] ++ readBytes
  | .ld32t a t i =>
    match t.constVal? with
    | some w =>
      let s := tierA a w
      compileE tab nlocals tmp i ++
      loadMemOff .ld AbiReg.t2 AbiReg.gp AbiReg.t3 (tab.len64 s) ++
      [Asm.srli AbiReg.t3 AbiReg.a0 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t3 (tab.base64 s) ++
      [Asm.slli AbiReg.t3 AbiReg.a0 2#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3,
       Asm.lwu AbiReg.a0 AbiReg.t1 0#12]
    | none =>
      let head := match emitSimpleExpr tab AbiReg.t0 AbiReg.t1 t with
        | some ct => compileE tab nlocals tmp i ++ ct
        | none =>
          compileE tab nlocals tmp t ++
          storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + tmp)) ++
          compileE tab nlocals (tmp + 1) i ++
          loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nlocals + tmp))
      head ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
       Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (tab.len64 (TieredArray.t0 a)) ++
      [Asm.srli AbiReg.t3 AbiReg.a0 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t3 (tab.base64 (TieredArray.t0 a)) ++
      [Asm.slli AbiReg.t3 AbiReg.a0 2#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3,
       Asm.lwu AbiReg.a0 AbiReg.t1 0#12]
  | .ld32h a t i hi =>
    match t.constVal? with
    | some w =>
      let s := tierA a w
      compileE tab nlocals tmp i ++
      loadMemOff .ld AbiReg.t2 AbiReg.gp AbiReg.t3 (tab.len64 s) ++
      [Asm.bgeu AbiReg.a0 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t3 (tab.base64 s) ++
      [Asm.slli AbiReg.t3 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3,
       Asm.lwu AbiReg.a0 AbiReg.t1 (if hi then 4#12 else 0#12)]
    | none =>
      let head := match emitSimpleExpr tab AbiReg.t0 AbiReg.t1 t with
        | some ct => compileE tab nlocals tmp i ++ ct
        | none =>
          compileE tab nlocals tmp t ++
          storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + tmp)) ++
          compileE tab nlocals (tmp + 1) i ++
          loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nlocals + tmp))
      head ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
       Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (tab.len64 (TieredArray.t0 a)) ++
      [Asm.bgeu AbiReg.a0 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t3 (tab.base64 (TieredArray.t0 a)) ++
      [Asm.slli AbiReg.t3 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3,
       Asm.lwu AbiReg.a0 AbiReg.t1 (if hi then 4#12 else 0#12)]

/-- Compile condition `c`, jumping to `target` iff `c` evaluates to `want`. -/
def compileC (tab : Tab) (nlocals : Nat) (tmp : Nat) (pfx : String) (lblId : Nat)
    (c : Cond) (want : Bool) (target : String) : (List AsmItem × Nat) :=
  match c with
  | .cmp op a b =>
    let code :=
      if b.constVal? == some 0 then
        compileE tab nlocals tmp a ++ [brCmp op want AbiReg.a0 AbiReg.zero target]
      else if a.constVal? == some 0 then
        compileE tab nlocals tmp b ++ [brCmp op want AbiReg.zero AbiReg.a0 target]
      else
        match emitSimpleExpr tab AbiReg.t0 AbiReg.t1 b with
        | some cb =>
          compileE tab nlocals tmp a ++ cb ++ [brCmp op want AbiReg.a0 AbiReg.t0 target]
        | none =>
          match emitSimpleExpr tab AbiReg.t0 AbiReg.t1 a with
          | some ca =>
            compileE tab nlocals tmp b ++ ca ++ [brCmp op want AbiReg.t0 AbiReg.a0 target]
          | none =>
            compileE tab nlocals tmp a ++
            storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + tmp)) ++
            compileE tab nlocals (tmp + 1) b ++
            loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nlocals + tmp)) ++
            [brCmp op want AbiReg.t0 AbiReg.a0 target]
    (code, lblId)
  | .not p =>
    compileC tab nlocals tmp pfx lblId p (!want) target
  | .and p q =>
    if want then
      let skipLbl := s!"{pfx}_and_{lblId}"
      let (cp, id1) := compileC tab nlocals tmp pfx (lblId + 1) p false skipLbl
      let (cq, id2) := compileC tab nlocals tmp pfx id1 q true target
      (cp ++ cq ++ [Asm.lbl skipLbl], id2)
    else
      let (cp, id1) := compileC tab nlocals tmp pfx lblId p false target
      let (cq, id2) := compileC tab nlocals tmp pfx id1 q false target
      (cp ++ cq, id2)
  | .or p q =>
    if want then
      let (cp, id1) := compileC tab nlocals tmp pfx lblId p true target
      let (cq, id2) := compileC tab nlocals tmp pfx id1 q true target
      (cp ++ cq, id2)
    else
      let skipLbl := s!"{pfx}_or_{lblId}"
      let (cp, id1) := compileC tab nlocals tmp pfx (lblId + 1) p true skipLbl
      let (cq, id2) := compileC tab nlocals tmp pfx id1 q false target
      (cp ++ cq ++ [Asm.lbl skipLbl], id2)

def compileEvalExprsToTemps (tab : Tab) (nlocals tmp : Nat) : List Expr → List AsmItem
  | [] => []
  | e :: es =>
    (if e.constVal? == some 0 then
       storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t0 (slotOff (nlocals + tmp))
     else
       compileE tab nlocals tmp e ++
       storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + tmp))) ++
    compileEvalExprsToTemps tab nlocals (tmp + 1) es

def copyTempsToResults (tab : Tab) (nlocals tmp count : Nat) : List AsmItem :=
  if count == 0 then
    if 0 < tab.nres then [Asm.addi AbiReg.a0 AbiReg.zero 0#12] else []
  else
    (List.range (min count tab.nres)).flatMap fun i =>
      if i < maxRes then
        loadMemOff .ld (resReg i) AbiReg.sp AbiReg.t0 (slotOff (nlocals + tmp + i))
      else
        loadMemOff .ld AbiReg.t1 AbiReg.sp AbiReg.t2 (slotOff (nlocals + tmp + i)) ++
        storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t2 (tab.resOff i)

/-- Unrolled copy of `nparams` incoming call arguments from `[t0 + 8*i]` into local frame slots `[0..nparams)`. -/
def unrollCopyParams (nparams : Nat) : List AsmItem :=
  (List.range nparams).flatMap fun i =>
    loadMemOff .ld AbiReg.t4 AbiReg.t0 AbiReg.t2 (8 * Int.ofNat i) ++
    storeMemOff .sd AbiReg.sp AbiReg.t4 AbiReg.t2 (slotOff i)

/-- Unrolled zero-initialization of `count` local frame slots `[lo .. lo + count)`. -/
def unrollZeroLocals (lo count : Nat) : List AsmItem :=
  (List.range count).flatMap fun i =>
    storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t2 (slotOff (lo + i))

/-- Sound syntactic check: `false` implies `s` can never finish with `.normal` (always returns/aborts/breaks/exhausts/errors). -/
def stmtMayFallthrough : Stmt → Bool
  | .ret _ | .abort _ => false
  | .seq s1 s2 => if stmtMayFallthrough s1 then stmtMayFallthrough s2 else false
  | .ite _ s1 s2 => stmtMayFallthrough s1 || stmtMayFallthrough s2
  | _ => true

/-- Minimum return value count guaranteed on any `.ret es` inside `s` (clamped at least `1` since empty `.ret []` sets `a0 := 0`). -/
def stmtMinRetRaw : Stmt → Option Nat
  | .ret es => some (max 1 es.length)
  | .seq s1 s2 =>
    match stmtMinRetRaw s1, stmtMinRetRaw s2 with
    | none, y => y
    | x, none => x
    | some a, some b => some (min a b)
  | .ite _ s1 s2 =>
    match stmtMinRetRaw s1, stmtMinRetRaw s2 with
    | none, y => y
    | x, none => x
    | some a, some b => some (min a b)
  | .while _ b => stmtMinRetRaw b
  | _ => none

/-- Guaranteed minimum number of initialized return slots on return from `fd` (at least `1` whenever falling through). -/
def fnMinRet (fd : FunDecl) : Nat :=
  if stmtMayFallthrough fd.body then 1
  else match stmtMinRetRaw fd.body with
    | none => 100
    | some k => k

def copyResultsToLocals (tab : Tab) (xs : List Var) : List AsmItem :=
  (xs.zipIdx).flatMap fun (x, i) =>
    if i < tab.nres then
      if i < maxRes then
        storeMemOff .sd AbiReg.sp (resReg i) AbiReg.t0 (slotOff x)
      else
        loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (tab.resOff i) ++
        storeMemOff .sd AbiReg.sp AbiReg.t1 AbiReg.t2 (slotOff x)
    else
      storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t0 (slotOff x)

def evalWArrTierToTemp (tab : Tab) (nlocals tmp : Nat) (w : WArr) :
    (ArrId × List AsmItem) :=
  match w with
  | .plain a => (a, storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t0 (slotOff (nlocals + tmp)))
  | .tier a t =>
    (a, compileE tab nlocals tmp t ++
        storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + tmp)))

/-- Evaluate index/value pair `(i, e)` into `(t0, a0)` avoiding stack spills when either is simple. -/
def compileStorePair (tab : Tab) (nlocals : Nat) (i e : Expr) : List AsmItem :=
  match emitSimpleExpr tab AbiReg.t0 AbiReg.t1 i with
  | some ci => compileE tab nlocals 0 e ++ ci
  | none =>
    match emitSimpleExpr tab AbiReg.a0 AbiReg.t1 e with
    | some ce => compileE tab nlocals 0 i ++ [Asm.mv AbiReg.t0 AbiReg.a0] ++ ce
    | none =>
      compileE tab nlocals 0 i ++
      storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff nlocals) ++
      compileE tab nlocals 1 e ++
      loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff nlocals)

/-- Evaluate tiered store triple `(t, i, e)` into `(t0, t3, a0)` avoiding stack spills when simple. -/
def compileTierStoreTriple (tab : Tab) (nlocals : Nat) (t i e : Expr) : List AsmItem :=
  match emitSimpleExpr tab AbiReg.t0 AbiReg.t1 t with
  | some ct =>
    match emitSimpleExpr tab AbiReg.t3 AbiReg.t4 i with
    | some ci => compileE tab nlocals 0 e ++ ct ++ ci
    | none =>
      match emitSimpleExpr tab AbiReg.a0 AbiReg.t4 e with
      | some ce =>
        compileE tab nlocals 0 i ++ [Asm.mv AbiReg.t3 AbiReg.a0] ++ ct ++ ce
      | none =>
        compileE tab nlocals 0 i ++
        storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff nlocals) ++
        compileE tab nlocals 1 e ++
        loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t1 (slotOff nlocals) ++
        ct
  | none =>
    compileE tab nlocals 0 t ++
    storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff nlocals) ++
    compileE tab nlocals 1 i ++
    storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + 1)) ++
    compileE tab nlocals 2 e ++
    loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff nlocals) ++
    loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t1 (slotOff (nlocals + 1))

/-- Compile a statement `s`. -/
def compileS (tab : Tab) (nlocals : Nat) (pfx : String) (lblId : Nat)
    (brkLbl : Option String) (retLbl : String) (s : Stmt) : (List AsmItem × Nat) :=
  match s with
  | .skip => ([], lblId)
  | .set x e =>
    let code :=
      if e.constVal? == some 0 then
        storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t0 (slotOff x)
      else
        compileE tab nlocals 0 e ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff x)
    (code, lblId)
  | .gset g e =>
    let code :=
      if e.constVal? == some 0 then
        storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.globOff g)
      else
        compileE tab nlocals 0 e ++ storeMemOff .sd AbiReg.gp AbiReg.a0 AbiReg.t0 (tab.globOff g)
    (code, lblId)
  | .st8 _ _ _ => ([], lblId)
  | .st64 a i e =>
    let code :=
      compileStorePair tab nlocals i e ++
      loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (tab.len64 (TieredArray.t0 a)) ++
      [Asm.bgeu AbiReg.t0 AbiReg.t1 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (tab.base64 (TieredArray.t0 a)) ++
      [Asm.slli AbiReg.t2 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2,
       Asm.sd AbiReg.t1 AbiReg.a0 0#12]
    (code, lblId)
  | .st64t a t i e =>
    let code :=
      compileTierStoreTriple tab nlocals t i e ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
       Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t4 (tab.len64 (TieredArray.t0 a)) ++
      [Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t4 (tab.base64 (TieredArray.t0 a)) ++
      [Asm.slli AbiReg.t4 AbiReg.t3 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4,
       Asm.sd AbiReg.t1 AbiReg.a0 0#12]
    (code, lblId)
  | .st32t a t i e =>
    let code :=
      compileTierStoreTriple tab nlocals t i e ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
       Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t4 (tab.len64 (TieredArray.t0 a)) ++
      [Asm.srli AbiReg.t4 AbiReg.t3 1#6, Asm.bgeu AbiReg.t4 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t4 (tab.base64 (TieredArray.t0 a)) ++
      [Asm.slli AbiReg.t4 AbiReg.t3 2#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4,
       Asm.sw AbiReg.t1 AbiReg.a0 0#12]
    (code, lblId)
  | .seq s1 s2 =>
    let (c1, id1) := compileS tab nlocals pfx lblId brkLbl retLbl s1
    let (c2, id2) := compileS tab nlocals pfx id1 brkLbl retLbl s2
    (c1 ++ c2, id2)
  | .ite cond s1 .skip =>
    let endLbl := s!"{pfx}_endif_{lblId}"
    let (cc, id1) := compileC tab nlocals 0 pfx (lblId + 1) cond false endLbl
    let (c1, id2) := compileS tab nlocals pfx id1 brkLbl retLbl s1
    (cc ++ c1 ++ [Asm.lbl endLbl], id2)
  | .ite cond .skip s2 =>
    let endLbl := s!"{pfx}_endif_{lblId}"
    let (cc, id1) := compileC tab nlocals 0 pfx (lblId + 1) cond true endLbl
    let (c2, id2) := compileS tab nlocals pfx id1 brkLbl retLbl s2
    (cc ++ c2 ++ [Asm.lbl endLbl], id2)
  | .ite cond s1 s2 =>
    let elseLbl := s!"{pfx}_else_{lblId}"
    let endLbl  := s!"{pfx}_endif_{lblId}"
    let (cc, id1) := compileC tab nlocals 0 pfx (lblId + 1) cond false elseLbl
    let (c1, id2) := compileS tab nlocals pfx id1 brkLbl retLbl s1
    let (c2, id3) := compileS tab nlocals pfx id2 brkLbl retLbl s2
    (cc ++ c1 ++ [Asm.j endLbl, Asm.lbl elseLbl] ++ c2 ++ [Asm.lbl endLbl], id3)
  | .while cond body =>
    let loopLbl := s!"{pfx}_while_{lblId}"
    let endLbl  := s!"{pfx}_endw_{lblId}"
    let (cc, id1) := compileC tab nlocals 0 pfx (lblId + 1) cond false endLbl
    let (cb, id2) := compileS tab nlocals pfx id1 (some endLbl) retLbl body
    let code :=
      [Asm.lbl loopLbl] ++
      cc ++
      cb ++
      [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
       Asm.addi AbiReg.s0 AbiReg.s0 (-1#12),
       Asm.j loopLbl,
       Asm.lbl endLbl]
    (code, id2)
  | .brk =>
    let tgt := brkLbl.getD retLbl
    ([Asm.j tgt], lblId)
  | .ret [e] =>
    (compileE tab nlocals 0 e ++ [Asm.j retLbl], lblId)
  | .ret es =>
    let code :=
      compileEvalExprsToTemps tab nlocals 0 es ++
      copyTempsToResults tab nlocals 0 es.length ++
      [Asm.j retLbl]
    (code, lblId)
  | .call xs f args =>
    let code :=
      compileEvalExprsToTemps tab nlocals 0 args ++
      [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
       Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++
      (if args.isEmpty then [] else addImmOff AbiReg.t0 AbiReg.sp AbiReg.t2 (slotOff nlocals)) ++
      [Asm.call (fnLabel f)] ++
      copyResultsToLocals tab xs
    (code, lblId)
  | .abort e =>
    (compileE tab nlocals 0 e ++ [Asm.j abortLabel], lblId)
  | .copy64 d di src si n =>
    let (da, cd) := evalWArrTierToTemp tab nlocals 0 d
    let cdi := compileE tab nlocals 1 di ++
      storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + 1))
    let (sa, cs) := evalWArrTierToTemp tab nlocals 2 src
    let csi := compileE tab nlocals 3 si ++
      storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + 3))
    let cn := compileE tab nlocals 4 n ++
      storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + 4))
    let loopLbl := s!"{pfx}_c64_{lblId}"
    let doneLbl := s!"{pfx}_c64_done_{lblId}"
    let code :=
      cd ++ cdi ++ cs ++ csi ++ cn ++
      -- Bounds check dest: di + n ≤ len64(d)
      loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff nlocals) ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
       Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (tab.len64 (TieredArray.t0 da)) ++
      loadMemOff .ld AbiReg.t1 AbiReg.sp AbiReg.t6 (slotOff (nlocals + 1)) ++ -- di
      loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t6 (slotOff (nlocals + 4)) ++ -- n
      [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel,
       Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3,
       Asm.bltu AbiReg.t0 AbiReg.t1 errLabel] ++
      loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (tab.base64 (TieredArray.t0 da)) ++
      [Asm.slli AbiReg.t1 AbiReg.t1 3#6, Asm.add AbiReg.t1 AbiReg.t5 AbiReg.t1] ++ -- t1 = dst_ptr
      -- Bounds check src: si + n ≤ len64(s)
      loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t2 (slotOff (nlocals + 2)) ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
       Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (tab.len64 (TieredArray.t0 sa)) ++
      loadMemOff .ld AbiReg.t2 AbiReg.sp AbiReg.t6 (slotOff (nlocals + 3)) ++ -- si
      [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel,
       Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3,
       Asm.bltu AbiReg.t0 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (tab.base64 (TieredArray.t0 sa)) ++
      [Asm.slli AbiReg.t2 AbiReg.t2 3#6, Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2, -- t2 = src_ptr
       Asm.lbl loopLbl,
       Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
       Asm.ld AbiReg.t4 AbiReg.t2 0#12,
       Asm.sd AbiReg.t1 AbiReg.t4 0#12,
       Asm.addi AbiReg.t1 AbiReg.t1 8#12,
       Asm.addi AbiReg.t2 AbiReg.t2 8#12,
       Asm.addi AbiReg.t3 AbiReg.t3 (-1#12),
       Asm.j loopLbl,
       Asm.lbl doneLbl]
    (code, lblId + 1)
  | .copy8w d di src si n =>
    let (da, cd) := evalWArrTierToTemp tab nlocals 0 d
    let cdi := compileE tab nlocals 1 di ++
      storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + 1))
    let csi := compileE tab nlocals 3 si ++
      storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + 3))
    let cn := compileE tab nlocals 4 n ++
      storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + 4))
    let srcSetup := match src with
      | .arr a =>
        loadMemOff .ld AbiReg.t0 AbiReg.gp AbiReg.t6 (tab.len8 a) ++
        loadMemOff .ld AbiReg.t5 AbiReg.gp AbiReg.t6 (tab.base8 a)
      | .rom bs =>
        li AbiReg.t0 (BitVec.ofNat 64 bs.length) ++
        addImmOff AbiReg.t5 AbiReg.gp AbiReg.t6 (tab.romBase + (romIdx bs tab.rom : Int))
    let loopLbl := s!"{pfx}_c8w_{lblId}"
    let doneLbl := s!"{pfx}_c8w_done_{lblId}"
    let code :=
      cd ++ cdi ++ csi ++ cn ++
      loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff nlocals) ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
       Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (tab.len64 (TieredArray.t0 da)) ++
      loadMemOff .ld AbiReg.t1 AbiReg.sp AbiReg.t6 (slotOff (nlocals + 1)) ++
      loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t6 (slotOff (nlocals + 4)) ++
      [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel,
       Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3,
       Asm.bltu AbiReg.t0 AbiReg.t1 errLabel] ++
      loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (tab.base64 (TieredArray.t0 da)) ++
      [Asm.slli AbiReg.t1 AbiReg.t1 3#6, Asm.add AbiReg.t1 AbiReg.t5 AbiReg.t1] ++
      srcSetup ++
      loadMemOff .ld AbiReg.t2 AbiReg.sp AbiReg.t6 (slotOff (nlocals + 3)) ++
      [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel,
       Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3,
       Asm.bltu AbiReg.t0 AbiReg.t2 errLabel,
       Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2,
       Asm.lbl loopLbl,
       Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
       Asm.lbu AbiReg.t4 AbiReg.t2 0#12,
       Asm.sd AbiReg.t1 AbiReg.t4 0#12,
       Asm.addi AbiReg.t1 AbiReg.t1 8#12,
       Asm.addi AbiReg.t2 AbiReg.t2 1#12,
       Asm.addi AbiReg.t3 AbiReg.t3 (-1#12),
       Asm.j loopLbl,
       Asm.lbl doneLbl]
    (code, lblId + 1)
  | .scan8 x src i e c =>
    let ci := compileE tab nlocals 0 i ++
      storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff nlocals)
    let ce := compileE tab nlocals 1 e
    let srcSetup := match src with
      | .arr a =>
        loadMemOff .ld AbiReg.t0 AbiReg.gp AbiReg.t5 (tab.len8 a) ++
        loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t5 (tab.base8 a)
      | .rom bs =>
        li AbiReg.t0 (BitVec.ofNat 64 bs.length) ++
        addImmOff AbiReg.t1 AbiReg.gp AbiReg.t5 (tab.romBase + (romIdx bs tab.rom : Int))
    let loopLbl := s!"{pfx}_scan_{lblId}"
    let doneLbl := s!"{pfx}_scan_done_{lblId}"
    let code :=
      ci ++ ce ++
      -- a0 = ve, load vi into t3
      loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t5 (slotOff nlocals) ++
      srcSetup ++
      [Asm.bltu AbiReg.a0 AbiReg.t3 errLabel,
       Asm.bltu AbiReg.t0 AbiReg.a0 errLabel] ++
      addImmOff AbiReg.t2 AbiReg.gp AbiReg.t5 (tab.romBase + (romIdx c tab.rom : Int)) ++
      [Asm.lbl loopLbl,
       Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl,
       Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3,
       Asm.lbu AbiReg.t4 AbiReg.t4 0#12,
       Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4,
       Asm.lbu AbiReg.t5 AbiReg.t5 0#12,
       Asm.bne AbiReg.t5 AbiReg.zero doneLbl,
       Asm.addi AbiReg.t3 AbiReg.t3 1#12,
       Asm.j loopLbl,
       Asm.lbl doneLbl] ++
      storeMemOff .sd AbiReg.sp AbiReg.t3 AbiReg.t5 (slotOff x)
    (code, lblId + 1)

/-! ## 3b. Translation-Validated Register Allocation & Frame Layout -/

/-- Callee-saved register bank available to all functions (`10` registers). -/
def calleeSavedBank : List Reg :=
  [AbiReg.s3, AbiReg.s4, AbiReg.s5, AbiReg.s6, AbiReg.s7,
   AbiReg.s8, AbiReg.s9, AbiReg.s10, AbiReg.s11, AbiReg.tp]

/-- Extra caller-saved register bank available to leaf functions with zero save/restore cost (`7` registers). -/
def leafExtraBank : List Reg :=
  [AbiReg.a1, AbiReg.a2, AbiReg.a3, AbiReg.a4, AbiReg.a5, AbiReg.a6, AbiReg.a7]

/-- Allocatable registers for a function (`a1..a7` first for leaves, then `s3..s11, tp`). -/
def allowedRegs (isLeaf : Bool) : List Reg :=
  if isLeaf then leafExtraBank ++ calleeSavedBank else calleeSavedBank

/-- Syntactic check: true iff `s` contains any `.call` statement. -/
def stmtHasCall : Stmt → Bool
  | .call .. => true
  | .seq s1 s2 | .ite _ s1 s2 => stmtHasCall s1 || stmtHasCall s2
  | .while _ b => stmtHasCall b
  | _ => false

/-- Syntactic check: true iff `s` contains `.copy64`, `.copy8w`, or `.scan8` (which clobber `t5`). -/
def stmtHasCopyScan : Stmt → Bool
  | .copy64 .. | .copy8w .. | .scan8 .. => true
  | .seq s1 s2 | .ite _ s1 s2 => stmtHasCopyScan s1 || stmtHasCopyScan s2
  | .while _ b => stmtHasCopyScan b
  | _ => false

/-- Syntactic check: true iff `s` is literally `.abort (.const 0)`. -/
def isAbort0Stmt : Stmt → Bool
  | .abort (.const 0) => true
  | _ => false

/-- Syntactic check: true iff `s` contains any `.abort (.const 0)` statement. -/
def stmtHasAbort0 : Stmt → Bool
  | .abort (.const 0) => true
  | .seq s1 s2 | .ite _ s1 s2 => stmtHasAbort0 s1 || stmtHasAbort0 s2
  | .while _ b => stmtHasAbort0 b
  | _ => false

/-- True iff `es` is `[.var x_0, ..., .var x_{k-1}]` matching `xs` element-by-element. -/
def isVarList : List Var → List Expr → Bool
  | [], [] => true
  | x :: xs, (.var y) :: es => (x == y) && isVarList xs es
  | _, _ => false

/-- Decidable duplicate-free check on a list of local variable indices. -/
def listNodupNat : List Nat → Bool
  | [] => true
  | x :: xs => !(x ∈ xs) && listNodupNat xs

/-- Decidable guard for direct tail-call optimization of `.seq (.call xs f args) (.ret es)`. -/
def isTailCallRet (tab : Tab) (xs : List Var) (es : List Expr) (args : List Expr) : Bool :=
  !xs.isEmpty && isVarList xs es && listNodupNat xs &&
    args.length ≤ maxRes && xs.length ≤ tab.nres && xs.length ≤ maxRes

/-- Match a tail-call-return pair `(.call xs f args, .ret es)` eligible for TCO. -/
def tailCallRetMatch (tab : Tab) : Stmt → Stmt → Option (List Var × FnName × List Expr × List Expr)
  | .call xs f args, .ret es =>
    if isTailCallRet tab xs es args then some (xs, f, args, es) else none
  | _, _ => none

private def stmtSz : Stmt → Nat
  | .skip | .brk => 0
  | .seq s1 s2 => stmtSz s1 + stmtSz s2
  | .ite _ s1 s2 => 1 + stmtSz s1 + stmtSz s2
  | .while _ b => 2 + stmtSz b
  | _ => 1

private def stmtHasAbort : Stmt → Bool
  | .abort _ => true
  | .seq s1 s2 | .ite _ s1 s2 => stmtHasAbort s1 || stmtHasAbort s2
  | .while _ b => stmtHasAbort b
  | _ => false

private def isColdBranch (s : Stmt) : Bool :=
  stmtHasAbort s || stmtSz s >= 15

private def countGp2047Expr (tab : Tab) (w : Nat) : Expr → Nat
  | .len8 a => if fitsDoublePos12Int (tab.len8 a) then w else 0
  | .len64 a => if fitsDoublePos12Int (tab.len64 (TieredArray.t0 a)) then w else 0
  | .glob g => if fitsDoublePos12Int (tab.globOff g) then w else 0
  | .bin _ a b | .cmpw _ a b => countGp2047Expr tab w a + countGp2047Expr tab w b
  | .ld8 a i =>
    (if fitsDoublePos12Int (tab.len8 a) then w else 0) +
    (if fitsDoublePos12Int (tab.base8 a) then w else 0) + countGp2047Expr tab w i
  | .ld64 a i =>
    (if fitsDoublePos12Int (tab.len64 (TieredArray.t0 a)) then w else 0) +
    (if fitsDoublePos12Int (tab.base64 (TieredArray.t0 a)) then w else 0) + countGp2047Expr tab w i
  | .ldc _ i => countGp2047Expr tab w i
  | .ld64t a t i | .ld32t a t i | .ld32h a t i _ =>
    match t.constVal? with
    | some wt =>
      let s := tierA a wt
      (if fitsDoublePos12Int (tab.len64 s) then w else 0) +
      (if fitsDoublePos12Int (tab.base64 s) then w else 0) + countGp2047Expr tab w i
    | none => countGp2047Expr tab w t + countGp2047Expr tab w i
  | .len64t a t =>
    match t.constVal? with
    | some wt => if fitsDoublePos12Int (tab.len64 (tierA a wt)) then w else 0
    | none => countGp2047Expr tab w t
  | .ld8x8 src i =>
    let s := match src with
      | .arr a =>
        (if fitsDoublePos12Int (tab.len8 a) then w else 0) +
        (if fitsDoublePos12Int (tab.base8 a) then w else 0)
      | .rom _ => 0
    s + countGp2047Expr tab w i
  | _ => 0

private def countGp2047Cond (tab : Tab) (w : Nat) : Cond → Nat
  | .cmp _ a b => countGp2047Expr tab w a + countGp2047Expr tab w b
  | .and p q | .or p q => countGp2047Cond tab w p + countGp2047Cond tab w q
  | .not p => countGp2047Cond tab w p

private def countGp2047Stmt (tab : Tab) (w : Nat) : Stmt → (Nat × Nat)
  | .skip | .brk => (0, 0)
  | .set _ e | .abort e => (countGp2047Expr tab w e, 0)
  | .gset g e => ((if fitsDoublePos12Int (tab.globOff g) then w else 0) + countGp2047Expr tab w e, 0)
  | .st8 a i e =>
    ((if fitsDoublePos12Int (tab.len8 a) then w else 0) +
     (if fitsDoublePos12Int (tab.base8 a) then w else 0) +
     countGp2047Expr tab w i + countGp2047Expr tab w e, 0)
  | .st64 a i e =>
    ((if fitsDoublePos12Int (tab.len64 (TieredArray.t0 a)) then w else 0) +
     (if fitsDoublePos12Int (tab.base64 (TieredArray.t0 a)) then w else 0) +
     countGp2047Expr tab w i + countGp2047Expr tab w e, 0)
  | .st64t a t i e | .st32t a t i e =>
    match t.constVal? with
    | some wt =>
      let s := tierA a wt
      ((if fitsDoublePos12Int (tab.len64 s) then w else 0) +
       (if fitsDoublePos12Int (tab.base64 s) then w else 0) +
       countGp2047Expr tab w i + countGp2047Expr tab w e, 0)
    | none => (countGp2047Expr tab w t + countGp2047Expr tab w i + countGp2047Expr tab w e, 0)
  | .seq s1 s2 =>
    let a := countGp2047Stmt tab w s1; let b := countGp2047Stmt tab w s2
    (a.1 + b.1, a.2 + b.2)
  | .ite c s1 s2 =>
    let rc := countGp2047Cond tab w c
    let a := countGp2047Stmt tab w s1; let b := countGp2047Stmt tab w s2
    (rc + a.1 + b.1, a.2 + b.2)
  | .while c b =>
    let w' := min (w * 8) 1000
    let rc := countGp2047Cond tab w' c
    let rb := countGp2047Stmt tab w' b
    (rc + rb.1, rb.2)
  | .ret es => (es.foldl (fun acc e => acc + countGp2047Expr tab w e) 0, 0)
  | .call _ _ args => (args.foldl (fun acc e => acc + countGp2047Expr tab w e) 0, w)
  | _ => (0, 0)

/-- Heuristic decision to hoist `t5 := gp + 2047` in functions without `copy64`/`copy8w`/`scan8`
    when loop-weighted `gp + [2048, 4094]` descriptor accesses outweigh setup + post-call reloads. -/
def shouldUseT5Gp (tab : Tab) (fd : FunDecl) : Bool :=
  if stmtHasCopyScan fd.body then false
  else
    let (gpSc, callSc) := countGp2047Stmt tab 1 fd.body
    gpSc >= callSc + 2

/-- Syntactic check: true iff expression `e` references local variable `x`. -/
def exprUsesVar (x : Var) : Expr → Bool
  | .var y => y == x
  | .bin _ a b | .cmpw _ a b | .ld64t _ a b | .ld32t _ a b | .ld32h _ a b _ =>
    exprUsesVar x a || exprUsesVar x b
  | .ld8 _ i | .ld64 _ i | .ldc _ i | .len64t _ i | .ld8x8 _ i => exprUsesVar x i
  | _ => false

/-- Syntactic check: true iff condition `c` references local variable `x`. -/
def condUsesVar (x : Var) : Cond → Bool
  | .cmp _ a b => exprUsesVar x a || exprUsesVar x b
  | .and p q | .or p q => condUsesVar x p || condUsesVar x q
  | .not p => condUsesVar x p

/-- Syntactic check: true iff tiered array target `w` references local variable `x`. -/
def warrUsesVar (x : Var) : WArr → Bool
  | .plain _ => false
  | .tier _ t => exprUsesVar x t

/-- Syntactic check: true iff statement `s` reads local variable `x` anywhere. -/
def stmtUsesVar (x : Var) : Stmt → Bool
  | .skip | .brk => false
  | .set _ e | .gset _ e | .abort e => exprUsesVar x e
  | .st8 _ i e | .st64 _ i e | .scan8 _ _ i e _ => exprUsesVar x i || exprUsesVar x e
  | .st64t _ t i e | .st32t _ t i e => exprUsesVar x t || exprUsesVar x i || exprUsesVar x e
  | .seq s1 s2 => stmtUsesVar x s1 || stmtUsesVar x s2
  | .ite c s1 s2 => condUsesVar x c || stmtUsesVar x s1 || stmtUsesVar x s2
  | .while c b => condUsesVar x c || stmtUsesVar x b
  | .ret es | .call _ _ es => es.any (exprUsesVar x)
  | .copy64 d di s si n =>
    warrUsesVar x d || exprUsesVar x di || warrUsesVar x s || exprUsesVar x si || exprUsesVar x n
  | .copy8w d di _ si n =>
    warrUsesVar x d || exprUsesVar x di || exprUsesVar x si || exprUsesVar x n

/-- Sound two-bit liveness summary `(mayReadBeforeWrite, mustWriteOnNormalExit)` for local `x`.
    When `(stmtVarLive x s).1 = false`, executing `s` never observes the initial value of `x`. -/
def stmtVarLive (x : Var) : Stmt → (Bool × Bool)
  | .skip | .brk => (false, false)
  | .set y e => (exprUsesVar x e, y == x)
  | .gset _ e | .abort e => (exprUsesVar x e, false)
  | .st8 _ i e | .st64 _ i e => (exprUsesVar x i || exprUsesVar x e, false)
  | .st64t _ t i e | .st32t _ t i e => (exprUsesVar x t || exprUsesVar x i || exprUsesVar x e, false)
  | .ret es => (es.any (exprUsesVar x), false)
  | .call xs _ args => (args.any (exprUsesVar x), x ∈ xs)
  | .seq s1 s2 =>
    let (r1, w1) := stmtVarLive x s1
    let (r2, w2) := stmtVarLive x s2
    (r1 || (!w1 && r2), w1 || w2)
  | .ite c s1 s2 =>
    let (r1, w1) := stmtVarLive x s1
    let (r2, w2) := stmtVarLive x s2
    (condUsesVar x c || r1 || r2, w1 && w2)
  | .while c b =>
    let (rb, _) := stmtVarLive x b
    (condUsesVar x c || rb, false)
  | .copy64 d di s si n =>
    (warrUsesVar x d || exprUsesVar x di || warrUsesVar x s || exprUsesVar x si || exprUsesVar x n, false)
  | .copy8w d di _ si n =>
    (warrUsesVar x d || exprUsesVar x di || exprUsesVar x si || exprUsesVar x n, false)
  | .scan8 y _ i e _ =>
    (exprUsesVar x i || exprUsesVar x e, y == x)

/-- True iff non-parameter local `x` may be read before being written and therefore requires zero-init. -/
def varNeedsZeroInit (fd : FunDecl) (x : Var) : Bool :=
  (stmtVarLive x fd.body).1

/-- Exact 2-bit backward liveness and call-free validator for a single variable `x`.
    Given `(needAfter, needBrk)` ("might `x` be read after normal exit / `.brk` before overwrite?"),
    returns `(needBefore, callFreeOk)` where `callFreeOk = true` guarantees `x` is never live
    across any `.call` inside `s`. Structurally recursive on `Stmt` via the height-2 `Bool` lattice. -/
def stmtVarCallFree (x : Var) : Stmt → Bool → Bool → (Bool × Bool)
  | .skip, na, _ => (na, true)
  | .brk, _, nb => (nb, true)
  | .set y e, na, _ => (exprUsesVar x e || (na && y != x), true)
  | .gset _ e, na, _ => (exprUsesVar x e || na, true)
  | .st8 _ i e, na, _ | .st64 _ i e, na, _ =>
    (exprUsesVar x i || exprUsesVar x e || na, true)
  | .st64t _ t i e, na, _ | .st32t _ t i e, na, _ =>
    (exprUsesVar x t || exprUsesVar x i || exprUsesVar x e || na, true)
  | .ret es, _, _ => (es.any (exprUsesVar x), true)
  | .abort e, _, _ => (exprUsesVar x e, true)
  | .call xs _ args, na, _ =>
    let needAfterCall := na && !(x ∈ xs)
    (args.any (exprUsesVar x) || needAfterCall, !needAfterCall)
  | .copy64 d di s si n, na, _ =>
    (warrUsesVar x d || exprUsesVar x di || warrUsesVar x s || exprUsesVar x si || exprUsesVar x n || na, true)
  | .copy8w d di _ si n, na, _ =>
    (warrUsesVar x d || exprUsesVar x di || exprUsesVar x si || exprUsesVar x n || na, true)
  | .scan8 y _ i e _, na, _ => (exprUsesVar x i || exprUsesVar x e || (na && y != x), true)
  | .seq s1 s2, na, nb =>
    let (n2, ok2) := stmtVarCallFree x s2 na nb
    let (n1, ok1) := stmtVarCallFree x s1 n2 nb
    (n1, ok1 && ok2)
  | .ite c s1 s2, na, nb =>
    let (n1, ok1) := stmtVarCallFree x s1 na nb
    let (n2, ok2) := stmtVarCallFree x s2 na nb
    (condUsesVar x c || n1 || n2, ok1 && ok2)
  | .while c b, na, _ =>
    if condUsesVar x c || na then
      (true, (stmtVarCallFree x b true na).2)
    else
      let (nb, okb) := stmtVarCallFree x b false na
      if nb then (true, (stmtVarCallFree x b true na).2)
      else (false, okb)

/-- Exact 2-bit backward liveness, register non-interference, and call-free validator for a single
    variable `y`. Given `clobbers x` ("does writing `x` overwrite `y`'s register?") and `isCS`
    ("is `y` in a caller-saved register of a non-leaf function?"), checks that `y` is never
    clobbered while live by any write to another variable or any `.call`.
    Note `(stmtVarSafe y clobbers isCS s na nb).1 = (stmtVarCallFree y s na nb).1`. -/
def stmtVarSafe (y : Var) (clobbers : Var → Bool) (isCS : Bool) :
    Stmt → Bool → Bool → (Bool × Bool)
  | .skip, na, _ => (na, true)
  | .brk, _, nb => (nb, true)
  | .set x e, na, _ =>
    let na' := na && (x != y)
    (exprUsesVar y e || na', !(clobbers x && na'))
  | .scan8 x _ i e _, na, _ =>
    let na' := na && (x != y)
    (exprUsesVar y i || exprUsesVar y e || na', !(clobbers x && na'))
  | .gset _ e, na, _ => (exprUsesVar y e || na, true)
  | .st8 _ i e, na, _ | .st64 _ i e, na, _ => (exprUsesVar y i || exprUsesVar y e || na, true)
  | .st64t _ t i e, na, _ | .st32t _ t i e, na, _ =>
    (exprUsesVar y t || exprUsesVar y i || exprUsesVar y e || na, true)
  | .ret es, _, _ => (es.any (exprUsesVar y), true)
  | .abort e, _, _ => (exprUsesVar y e, true)
  | .call xs _ args, na, _ =>
    let needAfterCall := na && !(y ∈ xs)
    let ok := (!needAfterCall || !isCS) && (!na || !(xs.any clobbers))
    (args.any (exprUsesVar y) || needAfterCall, ok)
  | .copy64 d di s si n, na, _ =>
    (warrUsesVar y d || exprUsesVar y di || warrUsesVar y s || exprUsesVar y si || exprUsesVar y n || na, true)
  | .copy8w d di _ si n, na, _ =>
    (warrUsesVar y d || exprUsesVar y di || exprUsesVar y si || exprUsesVar y n || na, true)
  | .seq s1 s2, na, nb =>
    let (n2, ok2) := stmtVarSafe y clobbers isCS s2 na nb
    let (n1, ok1) := stmtVarSafe y clobbers isCS s1 n2 nb
    (n1, ok1 && ok2)
  | .ite c s1 s2, na, nb =>
    let (n1, ok1) := stmtVarSafe y clobbers isCS s1 na nb
    let (n2, ok2) := stmtVarSafe y clobbers isCS s2 na nb
    (condUsesVar y c || n1 || n2, ok1 && ok2)
  | .while c b, na, _ =>
    if condUsesVar y c || na then
      (true, (stmtVarSafe y clobbers isCS b true na).2)
    else
      let (nb, okb) := stmtVarSafe y clobbers isCS b false na
      if nb then (true, (stmtVarSafe y clobbers isCS b true na).2)
      else (false, okb)

/-- Partial map assigning local variables to hardware registers. -/
abbrev RegAlloc := List (Var × Reg)

/-- Decidable translation-validation checker for a per-function register assignment.
    Verifies every `(x, r)` has `x < nlocals`, `r ∈ allowedRegs true` (`a1..a7, s3..s11, tp`),
    and variable keys are duplicate-free (multiple non-interfering variables may share a register). -/
def regAllocValid (_isLeaf : Bool) (nlocals : Nat) (alloc : RegAlloc) : Bool :=
  let bank := allowedRegs true
  let rec go (seenV : List Var) : RegAlloc → Bool
    | [] => true
    | (x, r) :: rest =>
      (x < nlocals) && (r ∈ bank) && !(x ∈ seenV) &&
        go (x :: seenV) rest
  go [] alloc

/-- Extra decidable validation for register-argument passing: copying incoming parameter `i`
    (`i < min nparams maxRes`) in ascending order never overwrites an unread incoming parameter
    register `resReg j` (`i < j < min nparams maxRes`). Non-parameter locals (`x ≥ nparams`) are
    never written during `copyParamsR` and may freely use `a1..a7`. -/
def regAllocArgsValid (_isLeaf : Bool) (nparams : Nat) (alloc : RegAlloc) : Bool :=
  (List.range (min nparams maxRes)).all fun i =>
    match alloc.lookup i with
    | some ri =>
      (List.range (min nparams maxRes)).all fun j =>
        !(i < j && ri == resReg j)
    | none => true

/-- Verify that copying call results `xs` in ascending index order never overwrites a later
    result register `resReg j` (`i < j < min xs.length maxRes`). -/
def callResListValid (alloc : RegAlloc) (xs : List Var) : Bool :=
  (xs.zipIdx).all fun (x, i) =>
    match alloc.lookup x with
    | some r =>
      (List.range (min xs.length maxRes)).all fun j =>
        !(i < j && r == resReg j)
    | none => true

/-- Structural check of `callResListValid` across all `.call` statements in `s`. -/
def stmtCallResValid (alloc : RegAlloc) : Stmt → Bool
  | .call xs _ _ => callResListValid alloc xs
  | .seq s1 s2 | .ite _ s1 s2 => stmtCallResValid alloc s1 && stmtCallResValid alloc s2
  | .while _ b => stmtCallResValid alloc b
  | _ => true

/-- Decidable translation-validation checker for live-range register sharing and caller-saved
    (`leafExtraBank = a1..a7`) allocation:
    1. Every allocated local is actually read (`stmtUsesVar x fd.body`).
    2. In non-leaf functions, every `.call` satisfies `stmtCallResValid`.
    3. Every allocated `(y, ry)` satisfies `stmtVarSafe` across `fd.body` (never clobbered while
       live by any same-register variable or by a `.call` if `ry ∈ leafExtraBank`), and if live
       at entry is never clobbered by a later parameter copy or local zero-initialization. -/
def regAllocGraphValid (isLeaf : Bool) (nlocals : Nat) (alloc : RegAlloc) (fd : FunDecl) : Bool :=
  (isLeaf || stmtCallResValid alloc fd.body) &&
  alloc.all fun (y, ry) =>
    stmtUsesVar y fd.body &&
    let clobbers (x : Var) : Bool := (x != y) && (alloc.lookup x == some ry)
    let isCS := !isLeaf && (ry ∈ leafExtraBank)
    let (needEntry, okBody) := stmtVarSafe y clobbers isCS fd.body false false
    let okEntry :=
      if !needEntry then true
      else if y < fd.nparams then
        (List.range fd.nparams).all (fun x => !(x > y && clobbers x)) &&
        (List.range (nlocals - fd.nparams)).all (fun j =>
          let x := fd.nparams + j
          !(varNeedsZeroInit fd x && clobbers x))
      else
        varNeedsZeroInit fd y &&
        (List.range (nlocals - fd.nparams)).all (fun j =>
          let x := fd.nparams + j
          !(x > y && varNeedsZeroInit fd x && clobbers x))
    okBody && okEntry

private def addVarScore (arr : Array Nat) (x w : Nat) : Array Nat :=
  if h : x < arr.size then arr.set x (arr[x] + w) else arr

private def scoreExpr (w : Nat) : Expr → Array Nat → Array Nat
  | .var x, a => addVarScore a x w
  | .bin _ x y, a | .cmpw _ x y, a | .ld64t _ x y, a | .ld32t _ x y, a | .ld32h _ x y _, a =>
    scoreExpr w y (scoreExpr w x a)
  | .ld8 _ i, a | .ld64 _ i, a | .ldc _ i, a | .len64t _ i, a | .ld8x8 _ i, a =>
    scoreExpr w i a
  | _, a => a

private def scoreCond (w : Nat) : Cond → Array Nat → Array Nat
  | .cmp _ x y, a => scoreExpr w y (scoreExpr w x a)
  | .and p q, a | .or p q, a => scoreCond w q (scoreCond w p a)
  | .not p, a => scoreCond w p a

private def scoreWArr (w : Nat) : WArr → Array Nat → Array Nat
  | .plain _, a => a
  | .tier _ t, a => scoreExpr w t a

private def scoreStmtHot (w : Nat) : Stmt → Array Nat → Array Nat
  | .skip, a | .brk, a => a
  | .set x e, a => scoreExpr w e (addVarScore a x w)
  | .gset _ e, a => scoreExpr w e a
  | .abort _, a => a
  | .st8 _ i e, a | .st64 _ i e, a => scoreExpr w e (scoreExpr w i a)
  | .st64t _ t i e, a | .st32t _ t i e, a => scoreExpr w e (scoreExpr w i (scoreExpr w t a))
  | .seq s1 s2, a => scoreStmtHot w s2 (scoreStmtHot w s1 a)
  | .ite c s1 .skip, a =>
    let a1 := scoreCond w c a
    if isColdBranch s1 then a1 else scoreStmtHot w s1 a1
  | .ite c .skip s2, a =>
    let a1 := scoreCond w c a
    if isColdBranch s2 then a1 else scoreStmtHot w s2 a1
  | .ite c s1 s2, a =>
    let a1 := scoreCond w c a
    let a2 := if stmtHasAbort s1 && !stmtHasAbort s2 then a1 else scoreStmtHot w s1 a1
    if stmtHasAbort s2 && !stmtHasAbort s1 then a2 else scoreStmtHot w s2 a2
  | .while c b, a =>
    let w' := min (w * 10) 100000
    scoreStmtHot w' b (scoreCond w' c a)
  | .ret es, a => es.foldl (fun acc e => scoreExpr w e acc) a
  | .call xs _ args, a =>
    let a1 := args.foldl (fun acc e => scoreExpr w e acc) a
    xs.foldl (fun acc x => addVarScore acc x w) a1
  | .copy64 d di s si n, a =>
    scoreExpr w n (scoreExpr w si (scoreWArr w s (scoreExpr w di (scoreWArr w d a))))
  | .copy8w d di _ si n, a =>
    scoreExpr w n (scoreExpr w si (scoreExpr w di (scoreWArr w d a)))
  | .scan8 x _ i e _, a => scoreExpr w e (scoreExpr w i (addVarScore a x w))

private def findRegPrefHints : Stmt → List (Var × Nat)
  | .call xs _ args =>
    let resH := if xs.length > 1 then
      xs.zipIdx.filterMap fun (x, i) => if 1 ≤ i && i < maxRes then some (x, i) else none
    else []
    let argH := args.zipIdx.filterMap fun (e, i) =>
      match e with
      | .var x => if 1 ≤ i && i < maxRes then some (x, i) else none
      | _ => none
    resH ++ argH
  | .ret es =>
    if es.length > 1 then
      es.zipIdx.filterMap fun (e, i) =>
        match e with
        | .var x => if 1 ≤ i && i < maxRes then some (x, i) else none
        | _ => none
    else []
  | .seq s1 s2 | .ite _ s1 s2 => findRegPrefHints s1 ++ findRegPrefHints s2
  | .while _ b => findRegPrefHints b
  | _ => []

private def findMoveHints : Stmt → List (Var × Var)
  | .set x (.var y) => if x != y then [(x, y)] else []
  | .seq s1 s2 | .ite _ s1 s2 => findMoveHints s1 ++ findMoveHints s2
  | .while _ b => findMoveHints b
  | _ => []

private def exprVarsList : Expr → List Var
  | .var x => [x]
  | .bin _ a b | .cmpw _ a b | .ld64t _ a b | .ld32t _ a b | .ld32h _ a b _ =>
    exprVarsList a ++ exprVarsList b
  | .ld8 _ i | .ld64 _ i | .ldc _ i | .len64t _ i | .ld8x8 _ i => exprVarsList i
  | _ => []

private def condVarsList : Cond → List Var
  | .cmp _ a b => exprVarsList a ++ exprVarsList b
  | .and p q | .or p q => condVarsList p ++ condVarsList q
  | .not p => condVarsList p

private def warrVarsList : WArr → List Var
  | .plain _ => []
  | .tier _ t => exprVarsList t

private def varSetUnion (a b : List Var) : List Var :=
  b.foldl (fun acc x => if x ∈ acc then acc else x :: acc) a

private def varSetDiff (a b : List Var) : List Var :=
  a.filter (fun x => !(x ∈ b))

private def addInterfEdge (a : Array (List Var)) (u v : Var) : Array (List Var) :=
  if u == v then a
  else
    let a1 := if hu : u < a.size then
      if v ∈ a[u] then a else a.set u (v :: a[u])
    else a
    if hv : v < a1.size then
      if u ∈ a1[v] then a1 else a1.set v (u :: a1[v])
    else a1

private def addDefInterf (defs la : List Var) (a : Array (List Var)) : Array (List Var) :=
  let all := varSetUnion defs la
  defs.foldl (fun acc d => all.foldl (fun acc2 y => addInterfEdge acc2 d y) acc) a

private def buildInterfGo (nl : Nat) (used : Array Bool) :
    Stmt → List Var → List Var → Array (List Var) → (List Var × Array (List Var))
  | .skip, la, _, a => (la, a)
  | .brk, _, lb, a => (lb, a)
  | .set x e, la, _, a =>
    let a1 := if used.getD x false then addDefInterf [x] la a else a
    (varSetUnion (exprVarsList e) (varSetDiff la [x]), a1)
  | .scan8 x _ i e _, la, _, a =>
    let a1 := if used.getD x false then addDefInterf [x] la a else a
    (varSetUnion (exprVarsList i) (varSetUnion (exprVarsList e) (varSetDiff la [x])), a1)
  | .gset _ e, la, _, a => (varSetUnion (exprVarsList e) la, a)
  | .abort e, _, _, a => (exprVarsList e, a)
  | .ret es, _, _, a => (es.foldl (fun acc e => varSetUnion (exprVarsList e) acc) [], a)
  | .st8 _ i e, la, _, a | .st64 _ i e, la, _, a =>
    (varSetUnion (exprVarsList i) (varSetUnion (exprVarsList e) la), a)
  | .st64t _ t i e, la, _, a | .st32t _ t i e, la, _, a =>
    (varSetUnion (exprVarsList t) (varSetUnion (exprVarsList i) (varSetUnion (exprVarsList e) la)), a)
  | .call xs _ args, la, _, a =>
    let a1 := addDefInterf xs la a
    let liveAcross := varSetDiff la xs
    (args.foldl (fun acc e => varSetUnion (exprVarsList e) acc) liveAcross, a1)
  | .copy64 d di s si n, la, _, a =>
    (varSetUnion (warrVarsList d) (varSetUnion (exprVarsList di)
      (varSetUnion (warrVarsList s) (varSetUnion (exprVarsList si)
        (varSetUnion (exprVarsList n) la)))), a)
  | .copy8w d di _ si n, la, _, a =>
    (varSetUnion (warrVarsList d) (varSetUnion (exprVarsList di)
      (varSetUnion (exprVarsList si) (varSetUnion (exprVarsList n) la))), a)
  | .seq s1 s2, la, lb, a =>
    let (l2, a2) := buildInterfGo nl used s2 la lb a
    buildInterfGo nl used s1 l2 lb a2
  | .ite c s1 s2, la, lb, a =>
    let (l1, a1) := buildInterfGo nl used s1 la lb a
    let (l2, a2) := buildInterfGo nl used s2 la lb a1
    (varSetUnion (condVarsList c) (varSetUnion l1 l2), a2)
  | .while c b, la, _, a =>
    let rec fixLoop (cur : List Var) : Nat → List Var
      | 0 => cur
      | fuel + 1 =>
        let (lb1, _) := buildInterfGo nl used b cur la a
        let nxt := varSetUnion (condVarsList c) (varSetUnion la lb1)
        if nxt.length == cur.length && nxt.all (fun x => x ∈ cur) then cur
        else fixLoop nxt fuel
    let lhead := fixLoop (varSetUnion (condVarsList c) la) (nl + 2)
    let (_, a1) := buildInterfGo nl used b lhead la a
    (lhead, a1)

/-- Unverified heuristic live-range graph-coloring register allocator with copy coalescing.
    - Eliminates dead/unused locals (`!stmtUsesVar x fd.body`).
    - Colors call-free locals into `leafExtraBank` (`a1..a7`, zero save/restore cost), pre-pinning
      call-free parameters `1..7` and multi-result call outputs `xs[1..7]` to `resReg i`.
    - Colors live-across-call (and overflow leaf) locals into `calleeSavedBank` (`s3..s11, tp`),
      reusing already-open callee-saved registers for any non-interfering local (0 extra save cost)
      and opening a new callee-saved register when loop-weighted access score ≥ 3.
    - All outputs are translation-validated by `regAllocValid && regAllocArgsValid && regAllocGraphValid`. -/
def chooseRegAlloc (fd : FunDecl) : RegAlloc := Id.run do
  let nl := numLocalsFn fd
  let isLeaf := !stmtHasCall fd.body
  let used := (Array.range nl).map fun x => stmtUsesVar x fd.body
  let hotScores := scoreStmtHot 1 fd.body (Array.replicate nl 0)
  let hotScores := (List.range (min fd.nparams nl)).foldl (fun acc i =>
    if used.getD i false then addVarScore acc i 1 else acc) hotScores
  let (l0, a0) := buildInterfGo nl used fd.body [] [] (Array.replicate nl [])
  let params := (List.range fd.nparams).filter (fun x => used.getD x false)
  let zlocs := (List.range (nl - fd.nparams)).filterMap fun j =>
    let x := fd.nparams + j
    if varNeedsZeroInit fd x && used.getD x false then some x else none
  let adj := addDefInterf (params ++ zlocs) l0 a0
  let cf := (Array.range nl).map fun x =>
    isLeaf || (stmtVarCallFree x fd.body false false).2
  let isCF (x : Var) : Bool := cf.getD x false
  let csRegs : List Reg := leafExtraBank.reverse
  let mut acc : RegAlloc := []
  let mut assigned : Array (Option Reg) := Array.replicate nl none
  let canAssign (x : Var) (r : Reg) (cur : RegAlloc) (asgn : Array (Option Reg)) : Bool :=
    if !used.getD x false then false
    else if (asgn.getD x none).isSome then false
    else if !((adj.getD x []).all (fun y => asgn.getD y none != some r)) then false
    else
      let cand := (x, r) :: cur
      let okArgs := if x < min fd.nparams maxRes then regAllocArgsValid isLeaf fd.nparams cand else true
      let okRes := isLeaf || stmtCallResValid cand fd.body
      okArgs && okRes
  for i in List.range (min fd.nparams maxRes) do
    if 1 ≤ i && i < nl && used.getD i false && isCF i then
      let r := resReg i
      if canAssign i r acc assigned then
        acc := (i, r) :: acc
        assigned := assigned.set! i (some r)
  for (x, i) in findRegPrefHints fd.body do
    if x < nl && used.getD x false && isCF x && (assigned.getD x none).isNone then
      let r := resReg i
      if canAssign x r acc assigned then
        acc := (x, r) :: acc
        assigned := assigned.set! x (some r)
  let mvHints := findMoveHints fd.body
  let tryCoalesce (x : Var) (bank : List Reg) (cur : RegAlloc) (asgn : Array (Option Reg)) : Option Reg :=
    mvHints.findSome? fun (u, v) =>
      let other? := if u == x then some v else if v == x then some u else none
      match other? with
      | some y =>
        match asgn.getD y none with
        | some r => if r ∈ bank && canAssign x r cur asgn then some r else none
        | none => none
      | none => none
  let cfVars := (((List.range nl).filter (fun i =>
    used.getD i false && isCF i && (assigned.getD i none).isNone)).map
    fun i => (i, hotScores.getD i 0)).toArray.qsort
    (fun a b => if a.2 != b.2 then a.2 > b.2 else a.1 < b.1)
  let mut usedCS : List Reg := acc.map Prod.snd
  for (x, _) in cfVars do
    let chosen? :=
      match tryCoalesce x csRegs acc assigned with
      | some r => some r
      | none =>
        match csRegs.find? (fun r => r ∈ usedCS && canAssign x r acc assigned) with
        | some r => some r
        | none => csRegs.find? (fun r => canAssign x r acc assigned)
    match chosen? with
    | some r =>
      acc := (x, r) :: acc
      assigned := assigned.set! x (some r)
      if !(r ∈ usedCS) then usedCS := r :: usedCS
    | none => pure ()
  let restVars := (((List.range nl).filter (fun i =>
    used.getD i false && (assigned.getD i none).isNone)).map
    fun i => (i, hotScores.getD i 0)).toArray.qsort
    (fun a b => if a.2 != b.2 then a.2 > b.2 else a.1 < b.1)
  let mut openCallee : List Reg := []
  for (x, hotSc) in restVars do
    let chosen? :=
      match tryCoalesce x openCallee acc assigned with
      | some r => some r
      | none =>
        match openCallee.reverse.find? (fun r => canAssign x r acc assigned) with
        | some r => some r
        | none =>
          if hotSc >= 3 then
            calleeSavedBank.find? (fun r => !(r ∈ openCallee) && canAssign x r acc assigned)
          else none
    match chosen? with
    | some r =>
      acc := (x, r) :: acc
      assigned := assigned.set! x (some r)
      if !(r ∈ openCallee) then openCallee := r :: openCallee
    | none => pure ()
  return acc.reverse

/-- Pure non-trapping leaf expression predicate matching `emitSimpleExprR`. -/
def isSimpleExpr : Expr → Bool
  | .const _ | .var _ | .len8 _ | .len64 _ | .glob _ => true
  | _ => false

/-- Expressions whose `compileETo tab fl tmp a0 e` uses 0 stack temp slots and never writes `t4`,
    allowing binary/comparison ops to hold the LHS in `t4` instead of spilling to `sp`. -/
def exprNoT4 : Expr → Bool
  | .const _ | .var _ | .len8 _ | .len64 _ | .glob _ => true
  | .ld8 _ i | .ld64 _ i | .ldc _ i | .len64t _ i | .ld8x8 _ i => exprNoT4 i
  | .bin _ a b | .cmpw _ a b =>
    (isSimpleExpr b && exprNoT4 a) || (isSimpleExpr a && exprNoT4 b)
  | .ld64t _ t i | .ld32t _ t i | .ld32h _ t i _ =>
    isSimpleExpr t && exprNoT4 i

/-- True iff `e` reads any variable allocated to a register in `forbidden`. -/
def exprReadsForbidden (alloc : RegAlloc) (forbidden : List Reg) : Expr → Bool
  | .var x =>
    match alloc.lookup x with
    | some r => r ∈ forbidden
    | none => false
  | .bin _ a b | .cmpw _ a b | .ld64t _ a b | .ld32t _ a b | .ld32h _ a b _ =>
    exprReadsForbidden alloc forbidden a || exprReadsForbidden alloc forbidden b
  | .ld8 _ i | .ld64 _ i | .ldc _ i | .len64t _ i | .ld8x8 _ i =>
    exprReadsForbidden alloc forbidden i
  | _ => false

/-- Decidable conflict check for evaluating `es` in reverse index order (`idx + len - 1 .. idx`)
    directly into `resReg (idx + i)`: ensures each `e` avoids registers already written by `rest`. -/
def revDirectSafeAux (alloc : RegAlloc) (idx : Nat) : List Expr → Bool
  | [] => true
  | e :: rest =>
    let written := (List.range rest.length).map (fun d => resReg (idx + 1 + d))
    !exprReadsForbidden alloc written e && revDirectSafeAux alloc (idx + 1) rest

/-- True iff `es` (`es.length ≤ maxRes`) can be evaluated directly into `a0..a7` in reverse order
    without overwriting any register read by an earlier-index expression. -/
def revDirectSafe (_isLeaf : Bool) (alloc : RegAlloc) (es : List Expr) : Bool :=
  es.length ≤ maxRes && revDirectSafeAux alloc 0 es

/-- Tight expression temp-slot depth needed by `compileETo` (always `≤ maxTempsExpr`). -/
def usedTempsExpr : Expr → Nat
  | .const _ | .var _ | .len8 _ | .len64 _ | .glob _ => 0
  | .ld8 _ i | .ld64 _ i | .ldc _ i | .len64t _ i | .ld8x8 _ i => usedTempsExpr i
  | .bin _ a b =>
    if isSimpleExpr b then usedTempsExpr a
    else if isSimpleExpr a then usedTempsExpr b
    else if exprNoT4 b then usedTempsExpr a
    else max (usedTempsExpr a) (1 + usedTempsExpr b)
  | .cmpw _ a b =>
    if isSimpleExpr b then usedTempsExpr a
    else if isSimpleExpr a then usedTempsExpr b
    else if exprNoT4 b then usedTempsExpr a
    else max (usedTempsExpr a) (1 + usedTempsExpr b)
  | .ld64t _ t i | .ld32t _ t i | .ld32h _ t i _ =>
    if isSimpleExpr t then usedTempsExpr i
    else max (usedTempsExpr t) (1 + usedTempsExpr i)

def usedTempsCond : Cond → Nat
  | .cmp _ a b =>
    if isSimpleExpr b then usedTempsExpr a
    else if isSimpleExpr a then usedTempsExpr b
    else if exprNoT4 b then usedTempsExpr a
    else max (usedTempsExpr a) (1 + usedTempsExpr b)
  | .and p q | .or p q => max (usedTempsCond p) (usedTempsCond q)
  | .not p => usedTempsCond p

def usedTempsExprs (es : List Expr) : Nat :=
  (es.zipIdx).foldl (fun acc (e, idx) => max acc (idx + max 1 (usedTempsExpr e))) 0

def maxUsedTempsExprs : List Expr → Nat
  | [] => 0
  | e :: rest => max (usedTempsExpr e) (maxUsedTempsExprs rest)

/-- Tight statement temp-slot depth needed by `compileSR` (always `≤ maxTempsStmt`). -/
def usedTempsStmt : Stmt → Nat
  | .skip | .brk => 0
  | .set _ e | .abort e | .gset _ e => usedTempsExpr e
  | .st8 _ i e | .st64 _ i e =>
    if isSimpleExpr i then usedTempsExpr e
    else if isSimpleExpr e then usedTempsExpr i
    else max (usedTempsExpr i) (1 + usedTempsExpr e)
  | .st64t _ t i e | .st32t _ t i e =>
    if isSimpleExpr t then
      if isSimpleExpr i then usedTempsExpr e
      else if isSimpleExpr e then usedTempsExpr i
      else max (usedTempsExpr i) (1 + usedTempsExpr e)
    else
      max (usedTempsExpr t) (max (1 + usedTempsExpr i) (2 + usedTempsExpr e))
  | .seq s1 s2 => max (usedTempsStmt s1) (usedTempsStmt s2)
  | .ite c s1 s2 => max (usedTempsCond c) (max (usedTempsStmt s1) (usedTempsStmt s2))
  | .while c b => max (usedTempsCond c) (usedTempsStmt b)
  | .ret [e] => usedTempsExpr e
  | .ret es => usedTempsExprs es
  | .call _ _ args => usedTempsExprs args
  | .copy64 d di s si n =>
    let dt := match d with | .plain _ => 0 | .tier _ t => usedTempsExpr t
    let st := match s with | .plain _ => 0 | .tier _ t => 2 + usedTempsExpr t
    max dt (max (1 + usedTempsExpr di) (max st (max (3 + usedTempsExpr si) (4 + max 1 (usedTempsExpr n)))))
  | .copy8w d di _ si n =>
    let dt := match d with | .plain _ => 0 | .tier _ t => usedTempsExpr t
    max dt (max (1 + usedTempsExpr di) (max (3 + usedTempsExpr si) (4 + max 1 (usedTempsExpr n))))
  | .scan8 _ _ i e _ =>
    if isSimpleExpr e then usedTempsExpr i
    else max (usedTempsExpr i) (1 + usedTempsExpr e)

def usedTempsCallArgs (alloc : RegAlloc) (args : List Expr) : Nat :=
  if revDirectSafe true alloc args then maxUsedTempsExprs args
  else usedTempsExprs args

def usedTempsRetR (isLeaf : Bool) (alloc : RegAlloc) : List Expr → Nat
  | [] => 0
  | [e] => usedTempsExpr e
  | es =>
    if revDirectSafe isLeaf alloc es then maxUsedTempsExprs es
    else usedTempsExprs es

/-- Register-argument-aware statement temp-slot depth needed by `compileSR` (always `≤ maxTempsStmt`).
    Definitionally equal to `usedTempsStmt` on all leaf/array/store/copy/scan statements. -/
def usedTempsStmtR (isLeaf : Bool) (alloc : RegAlloc) : Stmt → Nat
  | .seq s1 s2 => max (usedTempsStmtR isLeaf alloc s1) (usedTempsStmtR isLeaf alloc s2)
  | .ite c s1 s2 => max (usedTempsCond c) (max (usedTempsStmtR isLeaf alloc s1) (usedTempsStmtR isLeaf alloc s2))
  | .while c b => max (usedTempsCond c) (usedTempsStmtR isLeaf alloc b)
  | .ret es => usedTempsRetR isLeaf alloc es
  | .call _ _ args => usedTempsCallArgs alloc args
  | s => usedTempsStmt s

/-- Per-function register allocation and compact stack-frame geometry.
    Stack frame slots `[0 .. frameSlots)` are laid out as:
    `[ra (if !isLeaf)] ++ savedRegs ++ spilledVars ++ temps`. -/
structure FrameLayout where
  isLeaf : Bool
  nlocals : Nat
  alloc : RegAlloc
  savedRegs : List Reg
  spilledVars : List Var
  usedTemps : Nat
  useT5Gp : Bool := false
  deriving Repr, DecidableEq, Inhabited

def FrameLayout.raSlots (fl : FrameLayout) : Nat :=
  if fl.isLeaf then 0 else 1

def FrameLayout.protectedSlots (fl : FrameLayout) : Nat :=
  fl.raSlots + fl.savedRegs.length

def FrameLayout.spillIdx (fl : FrameLayout) (x : Var) : Nat :=
  fl.spilledVars.idxOf x

def FrameLayout.savedOff (fl : FrameLayout) (i : Nat) : Int :=
  8 * ((fl.raSlots + i : Nat) : Int)

def FrameLayout.varSlotOff (fl : FrameLayout) (x : Var) : Int :=
  8 * ((fl.protectedSlots + fl.spillIdx x : Nat) : Int)

def FrameLayout.tempSlotOff (fl : FrameLayout) (tmp : Nat) : Int :=
  8 * ((fl.protectedSlots + fl.spilledVars.length + tmp : Nat) : Int)

def FrameLayout.frameSlots (fl : FrameLayout) : Nat :=
  fl.protectedSlots + fl.spilledVars.length + fl.usedTemps

def FrameLayout.frameBytes (fl : FrameLayout) : Int :=
  8 * (fl.frameSlots : Int)

/-- Compute validated register allocation and compact stack-frame layout for `fd` from an explicit
    `rawAlloc` hint (without `t5` gp-hoisting). -/
def fnFrameLayoutWith (rawAlloc : RegAlloc) (fd : FunDecl) : FrameLayout :=
  let nlocals := numLocalsFn fd
  let isLeaf := !stmtHasCall fd.body
  let alloc :=
    if regAllocValid isLeaf nlocals rawAlloc &&
       regAllocArgsValid isLeaf fd.nparams rawAlloc &&
       regAllocGraphValid isLeaf nlocals rawAlloc fd
    then rawAlloc else []
  let savedRegs := calleeSavedBank.filter (fun r => alloc.any fun p => p.2 == r)
  let spilledVars := (List.range nlocals).filter (fun x =>
    (alloc.lookup x).isNone && stmtUsesVar x fd.body)
  let usedTemps := usedTempsStmtR isLeaf alloc fd.body
  { isLeaf, nlocals, alloc, savedRegs, spilledVars, usedTemps, useT5Gp := false }

/-- Compute validated register allocation and compact stack-frame layout for `fd` (without `t5` gp-hoisting). -/
def fnFrameLayout (fd : FunDecl) : FrameLayout :=
  let nlocals := numLocalsFn fd
  let isLeaf := !stmtHasCall fd.body
  let rawAlloc := chooseRegAlloc fd
  let alloc :=
    if regAllocValid isLeaf nlocals rawAlloc &&
       regAllocArgsValid isLeaf fd.nparams rawAlloc &&
       regAllocGraphValid isLeaf nlocals rawAlloc fd
    then rawAlloc else []
  let savedRegs := calleeSavedBank.filter (fun r => alloc.any fun p => p.2 == r)
  let spilledVars := (List.range nlocals).filter (fun x =>
    (alloc.lookup x).isNone && stmtUsesVar x fd.body)
  let usedTemps := usedTempsStmtR isLeaf alloc fd.body
  { isLeaf, nlocals, alloc, savedRegs, spilledVars, usedTemps, useT5Gp := false }

theorem fnFrameLayout_eq_with (fd : FunDecl) :
    fnFrameLayout fd = fnFrameLayoutWith (chooseRegAlloc fd) fd := rfl

/-- Compute validated register allocation and frame layout for `fd` under descriptor table `tab`
    from an explicit `rawAlloc` hint. -/
def fnFrameLayoutForWith (rawAlloc : RegAlloc) (tab : Tab) (fd : FunDecl) : FrameLayout :=
  { fnFrameLayoutWith rawAlloc fd with useT5Gp := shouldUseT5Gp tab fd }

/-- Compute validated register allocation and frame layout for `fd` under descriptor table `tab`,
    enabling `t5 := gp + 2047` hoisting when profitable and safe (`!stmtHasCopyScan fd.body`). -/
def fnFrameLayoutFor (tab : Tab) (fd : FunDecl) : FrameLayout :=
  { fnFrameLayout fd with useT5Gp := shouldUseT5Gp tab fd }

theorem fnFrameLayoutFor_eq_with (tab : Tab) (fd : FunDecl) :
    fnFrameLayoutFor tab fd = fnFrameLayoutForWith (chooseRegAlloc fd) tab fd := rfl

/-- Return hardware register holding expression `e` directly (`x0` for `0`, or assigned var reg). -/
def exprReg? (alloc : RegAlloc) : Expr → Option Reg
  | .const w => if w == 0 then some AbiReg.zero else none
  | .var x => alloc.lookup x
  | _ => none

/-- Pure, never-trapping leaf expression directly emitted into `rd` using `tmp` as scratch. -/
def emitSimpleExprR (tab : Tab) (fl : FrameLayout) (rd tmp : Reg) : Expr → Option (List AsmItem)
  | .const w => some (li rd (BitVec.ofNat 64 w.toNat))
  | .var x =>
    match fl.alloc.lookup x with
    | some rx => some (if rd == rx then [] else [Asm.mv rd rx])
    | none => some (loadMemOff .ld rd AbiReg.sp tmp (fl.varSlotOff x))
  | .len8 a => some (loadMemOffGp fl.useT5Gp .ld rd tmp (tab.len8 a))
  | .len64 a => some (loadMemOffGp fl.useT5Gp .ld rd tmp (tab.len64 (TieredArray.t0 a)))
  | .glob g => some (loadMemOffGp fl.useT5Gp .ld rd tmp (tab.globOff g))
  | _ => none

/-- Load tail for a 64-bit array element at index `i` (register `ri`), folding small constant offsets. -/
def ld64Tail (rd ri tmp : Reg) (i : Expr) : List AsmItem :=
  match i.constVal? with
  | some wi =>
    if wi.toNat < 256 then [Asm.ld rd AbiReg.t1 (BitVec.ofNat 12 (8 * wi.toNat))]
    else [Asm.slli tmp ri 3#6, Asm.add AbiReg.t1 AbiReg.t1 tmp, Asm.ld rd AbiReg.t1 0#12]
  | none => [Asm.slli tmp ri 3#6, Asm.add AbiReg.t1 AbiReg.t1 tmp, Asm.ld rd AbiReg.t1 0#12]

/-- Load tail for a 32-bit half-word array element at index `i` (register `ri`), folding small constant offsets. -/
def ld32tTail (rd ri : Reg) (i : Expr) : List AsmItem :=
  match i.constVal? with
  | some wi =>
    if wi.toNat < 512 then [Asm.lwu rd AbiReg.t1 (BitVec.ofNat 12 (4 * wi.toNat))]
    else [Asm.slli AbiReg.t3 ri 2#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3, Asm.lwu rd AbiReg.t1 0#12]
  | none => [Asm.slli AbiReg.t3 ri 2#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3, Asm.lwu rd AbiReg.t1 0#12]

/-- Load tail for low/high 32-bit half of a 64-bit array element at index `i` (register `ri`). -/
def ld32hTail (rd ri tmp : Reg) (i : Expr) (hi : Bool) : List AsmItem :=
  let offBi : BitVec 12 := if hi then 4#12 else 0#12
  match i.constVal? with
  | some wi =>
    if wi.toNat < 255 then [Asm.lwu rd AbiReg.t1 (BitVec.ofNat 12 (8 * wi.toNat + if hi then 4 else 0))]
    else [Asm.slli tmp ri 3#6, Asm.add AbiReg.t1 AbiReg.t1 tmp, Asm.lwu rd AbiReg.t1 offBi]
  | none => [Asm.slli tmp ri 3#6, Asm.add AbiReg.t1 AbiReg.t1 tmp, Asm.lwu rd AbiReg.t1 offBi]

/-- Store tail for a 64-bit array element at index `i` (register `ri`), folding small constant offsets. -/
def st64Tail (re ri tmp : Reg) (i : Expr) : List AsmItem :=
  match i.constVal? with
  | some w =>
    if w.toNat < 256 then [Asm.sd AbiReg.t1 re (BitVec.ofNat 12 (8 * w.toNat))]
    else [Asm.slli tmp ri 3#6, Asm.add AbiReg.t1 AbiReg.t1 tmp, Asm.sd AbiReg.t1 re 0#12]
  | none => [Asm.slli tmp ri 3#6, Asm.add AbiReg.t1 AbiReg.t1 tmp, Asm.sd AbiReg.t1 re 0#12]

/-- Store tail for a 32-bit array element at index `i` (register `ri`), folding small constant offsets. -/
def st32tTail (re ri tmp : Reg) (i : Expr) : List AsmItem :=
  match i.constVal? with
  | some w =>
    if w.toNat < 512 then [Asm.sw AbiReg.t1 re (BitVec.ofNat 12 (4 * w.toNat))]
    else [Asm.slli tmp ri 2#6, Asm.add AbiReg.t1 AbiReg.t1 tmp, Asm.sw AbiReg.t1 re 0#12]
  | none => [Asm.slli tmp ri 2#6, Asm.add AbiReg.t1 AbiReg.t1 tmp, Asm.sw AbiReg.t1 re 0#12]

/-- Shared codegen for low/high 32-bit half load from a plain 64-bit array (`ld64 & 0xffffffff` / `ld64 >> 32`). -/
def emitLd32hPlainFrom (tab : Tab) (fl : FrameLayout) (rd : Reg) (a : ArrId) (i : Expr)
    (hi : Bool) (compI0 : Unit → List AsmItem) : List AsmItem :=
  let (ci, ri) := match exprReg? fl.alloc i with
    | some r => ([], r)
    | none => (compI0 (), AbiReg.a0)
  ci ++
  loadMemOffGp fl.useT5Gp .ld AbiReg.t0 AbiReg.t1 (tab.len64 (TieredArray.t0 a)) ++
  [Asm.bgeu ri AbiReg.t0 errLabel] ++
  loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (tab.base64 (TieredArray.t0 a)) ++
  ld32hTail rd ri AbiReg.t2 i hi

/-- Shared codegen for `.ld32h a t i hi` and fused `(.ld64t a t i) & 0xffffffff` / `>> 32`. -/
def emitLd32hFrom (tab : Tab) (fl : FrameLayout) (tmp : Nat) (rd : Reg) (a : ArrId)
    (t i : Expr) (hi : Bool)
    (compI0 compT0 compI1 : Unit → List AsmItem) : List AsmItem :=
  match t.constVal? with
  | some w =>
    let s := tierA a w
    let (ci, ri) := match exprReg? fl.alloc i with
      | some r => ([], r)
      | none => (compI0 (), AbiReg.a0)
    ci ++
    loadMemOffGp fl.useT5Gp .ld AbiReg.t2 AbiReg.t3 (tab.len64 s) ++
    [Asm.bgeu ri AbiReg.t2 errLabel] ++
    loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t3 (tab.base64 s) ++
    ld32hTail rd ri AbiReg.t3 i hi
  | none =>
    let (head, rt, ri) := match exprReg? fl.alloc t with
      | some r =>
        match exprReg? fl.alloc i with
        | some ri => ([], r, ri)
        | none => (compI0 (), r, AbiReg.a0)
      | none =>
        match emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 t with
        | some ct =>
          match exprReg? fl.alloc i with
          | some ri => (ct, AbiReg.t0, ri)
          | none => (compI0 () ++ ct, AbiReg.t0, AbiReg.a0)
        | none =>
          (compT0 () ++
           storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp) ++
           compI1 () ++
           loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff tmp),
           AbiReg.t0, AbiReg.a0)
    head ++
    [Asm.andi AbiReg.t0 rt 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
     Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
    loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (tab.len64 (TieredArray.t0 a)) ++
    [Asm.bgeu ri AbiReg.t2 errLabel] ++
    loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t3 (tab.base64 (TieredArray.t0 a)) ++
    ld32hTail rd ri AbiReg.t3 i hi

/-- Non-peephole codegen for `.bin op a b`, parameterized by recursive subexpression compilers
    so `compileETo` keeps flat, fast equation lemmas. -/
def compileBinFallback (tab : Tab) (fl : FrameLayout) (tmp : Nat) (rd : Reg) (op : BinOp) (a b : Expr)
    (compA0 compB0 compB1 : Unit → List AsmItem) : List AsmItem :=
  match b.constVal? with
  | some w =>
    match exprReg? fl.alloc a with
    | some ra => emitBinConstRhsTo rd ra op w
    | none => compA0 () ++ emitBinConstRhsTo rd AbiReg.a0 op w
  | none =>
    match a.constVal? with
    | some w =>
      let (cb, rb) := match exprReg? fl.alloc b with
        | some r => ([], r)
        | none => (compB0 (), AbiReg.a0)
      match op with
      | .add | .and | .or | .xor | .mul | .mulhi =>
        cb ++ emitBinConstRhsTo rd rb op w
      | .sub =>
        if w == 0 then cb ++ [Asm.sub rd AbiReg.zero rb]
        else cb ++ li AbiReg.t0 w.toBitVec ++ [Asm.sub rd AbiReg.t0 rb]
      | .shl => cb ++ li AbiReg.t0 w.toBitVec ++ [Asm.sll rd AbiReg.t0 rb]
      | .shr => cb ++ li AbiReg.t0 w.toBitVec ++ [Asm.srl rd AbiReg.t0 rb]
    | none =>
      match exprReg? fl.alloc b with
      | some rb =>
        match exprReg? fl.alloc a with
        | some ra => [emitBinOp op rd ra rb]
        | none => compA0 () ++ [emitBinOp op rd AbiReg.a0 rb]
      | none =>
        match exprReg? fl.alloc a with
        | some ra =>
          compB0 () ++ [emitBinOp op rd ra AbiReg.a0]
        | none =>
          match emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 b with
          | some cb =>
            compA0 () ++ cb ++ [emitBinOp op rd AbiReg.a0 AbiReg.t0]
          | none =>
            match emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 a with
            | some ca =>
              compB0 () ++ ca ++ [emitBinOp op rd AbiReg.t0 AbiReg.a0]
            | none =>
              if exprNoT4 b then
                compA0 () ++
                [Asm.mv AbiReg.t4 AbiReg.a0] ++
                compB0 () ++
                [emitBinOp op rd AbiReg.t4 AbiReg.a0]
              else
                compA0 () ++
                storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp) ++
                compB1 () ++
                loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff tmp) ++
                [emitBinOp op rd AbiReg.t0 AbiReg.a0]

/-- Codegen for `(inner >> k) & mask` fused to `slli; srli`. -/
def emitShrMaskFrom (fl : FrameLayout) (rd : Reg) (inner : Expr) (lsh : Nat) (lm : BitVec 6)
    (compInner : Unit → List AsmItem) : List AsmItem :=
  let (ci, ri) := match exprReg? fl.alloc inner with
    | some r => ([], r)
    | none => (compInner (), AbiReg.a0)
  let s1 :=
    if lsh == 0 then (if rd == ri then [] else [Asm.mv rd ri])
    else [Asm.slli rd ri (BitVec.ofNat 6 lsh)]
  ci ++ s1 ++ [Asm.srli rd rd lm]

/-- Compile expression `e` under `fl`, placing its result directly into `rd`
    (`rd` is `a0` or an allocated variable register; never clobbers `rd` until final write). -/
def compileETo (tab : Tab) (fl : FrameLayout) (tmp : Nat) (rd : Reg) (e : Expr) : List AsmItem :=
  match e with
  | .const w => li rd (BitVec.ofNat 64 w.toNat)
  | .var x =>
    match fl.alloc.lookup x with
    | some rx => if rd == rx then [] else [Asm.mv rd rx]
    | none => loadMemOff .ld rd AbiReg.sp AbiReg.t0 (fl.varSlotOff x)
  | .len8 a => loadMemOffGp fl.useT5Gp .ld rd AbiReg.t0 (tab.len8 a)
  | .len64 a => loadMemOffGp fl.useT5Gp .ld rd AbiReg.t0 (tab.len64 (TieredArray.t0 a))
  | .glob g => loadMemOffGp fl.useT5Gp .ld rd AbiReg.t0 (tab.globOff g)
  | .bin op a b =>
    let fb := fun () => compileBinFallback tab fl tmp rd op a b
      (fun () => compileETo tab fl tmp AbiReg.a0 a)
      (fun () => compileETo tab fl tmp AbiReg.a0 b)
      (fun () => compileETo tab fl (tmp + 1) AbiReg.a0 b)
    match op, a, b with
    | .and, .bin .shr inner (.const k), .const mask =>
      let sh := k.toNat % 64
      match lowMaskShift? mask with
      | some lm =>
        if 0 < sh && sh ≤ lm.toNat then
          emitShrMaskFrom fl rd inner (lm.toNat - sh) lm (fun () => compileETo tab fl tmp AbiReg.a0 inner)
        else fb ()
      | none => fb ()
    | .and, .ld64 arr i, .const 0xffffffff =>
      emitLd32hPlainFrom tab fl rd arr i false (fun () => compileETo tab fl tmp AbiReg.a0 i)
    | .shr, .ld64 arr i, .const 32 =>
      emitLd32hPlainFrom tab fl rd arr i true (fun () => compileETo tab fl tmp AbiReg.a0 i)
    | .and, .ld64t arr t i, .const 0xffffffff =>
      emitLd32hFrom tab fl tmp rd arr t i false
        (fun () => compileETo tab fl tmp AbiReg.a0 i)
        (fun () => compileETo tab fl tmp AbiReg.a0 t)
        (fun () => compileETo tab fl (tmp + 1) AbiReg.a0 i)
    | .shr, .ld64t arr t i, .const 32 =>
      emitLd32hFrom tab fl tmp rd arr t i true
        (fun () => compileETo tab fl tmp AbiReg.a0 i)
        (fun () => compileETo tab fl tmp AbiReg.a0 t)
        (fun () => compileETo tab fl (tmp + 1) AbiReg.a0 i)
    | _, _, _ => fb ()
  | .cmpw c a b =>
    if c == .eq && b.constVal? == some 0 then
      match exprReg? fl.alloc a with
      | some ra => [Asm.sltiu rd ra 1#12]
      | none => compileETo tab fl tmp AbiReg.a0 a ++ [Asm.sltiu rd AbiReg.a0 1#12]
    else if c == .eq && a.constVal? == some 0 then
      match exprReg? fl.alloc b with
      | some rb => [Asm.sltiu rd rb 1#12]
      | none => compileETo tab fl tmp AbiReg.a0 b ++ [Asm.sltiu rd AbiReg.a0 1#12]
    else if c == .ne && b.constVal? == some 0 then
      match exprReg? fl.alloc a with
      | some ra => [Asm.sltu rd AbiReg.zero ra]
      | none => compileETo tab fl tmp AbiReg.a0 a ++ [Asm.sltu rd AbiReg.zero AbiReg.a0]
    else if c == .ne && a.constVal? == some 0 then
      match exprReg? fl.alloc b with
      | some rb => [Asm.sltu rd AbiReg.zero rb]
      | none => compileETo tab fl tmp AbiReg.a0 b ++ [Asm.sltu rd AbiReg.zero AbiReg.a0]
    else
      match exprReg? fl.alloc b with
      | some rb =>
        match exprReg? fl.alloc a with
        | some ra => emitCmpwTo rd c ra rb
        | none => compileETo tab fl tmp AbiReg.a0 a ++ emitCmpwTo rd c AbiReg.a0 rb
      | none =>
        match exprReg? fl.alloc a with
        | some ra => compileETo tab fl tmp AbiReg.a0 b ++ emitCmpwTo rd c ra AbiReg.a0
        | none =>
          match emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 b with
          | some cb => compileETo tab fl tmp AbiReg.a0 a ++ cb ++ emitCmpwTo rd c AbiReg.a0 AbiReg.t0
          | none =>
            match emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 a with
            | some ca => compileETo tab fl tmp AbiReg.a0 b ++ ca ++ emitCmpwTo rd c AbiReg.t0 AbiReg.a0
            | none =>
              if exprNoT4 b then
                compileETo tab fl tmp AbiReg.a0 a ++
                [Asm.mv AbiReg.t4 AbiReg.a0] ++
                compileETo tab fl tmp AbiReg.a0 b ++
                emitCmpwTo rd c AbiReg.t4 AbiReg.a0
              else
                compileETo tab fl tmp AbiReg.a0 a ++
                storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp) ++
                compileETo tab fl (tmp + 1) AbiReg.a0 b ++
                loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff tmp) ++
                emitCmpwTo rd c AbiReg.t0 AbiReg.a0
  | .ld8 a i =>
    let (ci, ri) := match exprReg? fl.alloc i with
      | some r => ([], r)
      | none => (compileETo tab fl tmp AbiReg.a0 i, AbiReg.a0)
    let tail := match i.constVal? with
      | some w =>
        if w.toNat < 2048 then [Asm.lbu rd AbiReg.t1 (BitVec.ofNat 12 w.toNat)]
        else [Asm.add AbiReg.t1 AbiReg.t1 ri, Asm.lbu rd AbiReg.t1 0#12]
      | none => [Asm.add AbiReg.t1 AbiReg.t1 ri, Asm.lbu rd AbiReg.t1 0#12]
    ci ++
    loadMemOffGp fl.useT5Gp .ld AbiReg.t0 AbiReg.t1 (tab.len8 a) ++
    [Asm.bgeu ri AbiReg.t0 errLabel] ++
    loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (tab.base8 a) ++
    tail
  | .ld64 a i =>
    let (ci, ri) := match exprReg? fl.alloc i with
      | some r => ([], r)
      | none => (compileETo tab fl tmp AbiReg.a0 i, AbiReg.a0)
    ci ++
    loadMemOffGp fl.useT5Gp .ld AbiReg.t0 AbiReg.t1 (tab.len64 (TieredArray.t0 a)) ++
    [Asm.bgeu ri AbiReg.t0 errLabel] ++
    loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (tab.base64 (TieredArray.t0 a)) ++
    ld64Tail rd ri AbiReg.t2 i
  | .ldc d i =>
    let (ci, ri) := match exprReg? fl.alloc i with
      | some r => ([], r)
      | none => (compileETo tab fl tmp AbiReg.a0 i, AbiReg.a0)
    ci ++
    li AbiReg.t0 (BitVec.ofNat 64 d.length) ++
    [Asm.bgeu ri AbiReg.t0 errLabel, Asm.add AbiReg.t1 AbiReg.gp ri] ++
    loadMemOff .lbu rd AbiReg.t1 AbiReg.t2 (tab.romBase + (romIdx d tab.rom : Int))
  | .ld64t a t i =>
    match t.constVal? with
    | some w =>
      let s := tierA a w
      let (ci, ri) := match exprReg? fl.alloc i with
        | some r => ([], r)
        | none => (compileETo tab fl tmp AbiReg.a0 i, AbiReg.a0)
      ci ++
      loadMemOffGp fl.useT5Gp .ld AbiReg.t2 AbiReg.t3 (tab.len64 s) ++
      [Asm.bgeu ri AbiReg.t2 errLabel] ++
      loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t3 (tab.base64 s) ++
      ld64Tail rd ri AbiReg.t3 i
    | none =>
      let (head, rt, ri) := match exprReg? fl.alloc t with
        | some r =>
          match exprReg? fl.alloc i with
          | some ri => ([], r, ri)
          | none => (compileETo tab fl tmp AbiReg.a0 i, r, AbiReg.a0)
        | none =>
          match emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 t with
          | some ct =>
            match exprReg? fl.alloc i with
            | some ri => (ct, AbiReg.t0, ri)
            | none => (compileETo tab fl tmp AbiReg.a0 i ++ ct, AbiReg.t0, AbiReg.a0)
          | none =>
            (compileETo tab fl tmp AbiReg.a0 t ++
             storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp) ++
             compileETo tab fl (tmp + 1) AbiReg.a0 i ++
             loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff tmp),
             AbiReg.t0, AbiReg.a0)
      head ++
      [Asm.andi AbiReg.t0 rt 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
       Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (tab.len64 (TieredArray.t0 a)) ++
      [Asm.bgeu ri AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t3 (tab.base64 (TieredArray.t0 a)) ++
      ld64Tail rd ri AbiReg.t3 i
  | .len64t a t =>
    match t.constVal? with
    | some w => loadMemOffGp fl.useT5Gp .ld rd AbiReg.t2 (tab.len64 (tierA a w))
    | none =>
      let (ct, rt) := match exprReg? fl.alloc t with
        | some r => ([], r)
        | none => (compileETo tab fl tmp AbiReg.a0 t, AbiReg.a0)
      ct ++
      [Asm.andi AbiReg.t0 rt 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
       Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld rd AbiReg.t1 AbiReg.t2 (tab.len64 (TieredArray.t0 a))
  | .ld8x8 src i =>
    let setupSrc := match src with
      | .arr a =>
        loadMemOffGp fl.useT5Gp .ld AbiReg.t0 AbiReg.t2 (tab.len8 a) ++
        loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (tab.base8 a)
      | .rom d =>
        li AbiReg.t0 (BitVec.ofNat 64 d.length) ++
        addImmOff AbiReg.t1 AbiReg.gp AbiReg.t2 (tab.romBase + (romIdx d tab.rom : Int))
    let readBytes :=
      [Asm.lbu rd AbiReg.t1 7#12] ++
      ([6, 5, 4, 3, 2, 1, 0].flatMap fun k =>
        [Asm.lbu AbiReg.t2 AbiReg.t1 (BitVec.ofInt 12 (k : Int)),
         Asm.slli rd rd 8#6,
         Asm.or rd rd AbiReg.t2])
    let (ci, ri) := match exprReg? fl.alloc i with
      | some r => ([], r)
      | none => (compileETo tab fl tmp AbiReg.a0 i, AbiReg.a0)
    ci ++ setupSrc ++
    [Asm.addi AbiReg.t2 AbiReg.zero 8#12,
     Asm.bltu AbiReg.t0 AbiReg.t2 errLabel,
     Asm.addi AbiReg.t0 AbiReg.t0 (-8#12),
     Asm.bltu AbiReg.t0 ri errLabel,
     Asm.add AbiReg.t1 AbiReg.t1 ri] ++ readBytes
  | .ld32t a t i =>
    match t.constVal? with
    | some w =>
      let s := tierA a w
      let (ci, ri) := match exprReg? fl.alloc i with
        | some r => ([], r)
        | none => (compileETo tab fl tmp AbiReg.a0 i, AbiReg.a0)
      ci ++
      loadMemOffGp fl.useT5Gp .ld AbiReg.t2 AbiReg.t3 (tab.len64 s) ++
      [Asm.srli AbiReg.t3 ri 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
      loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t3 (tab.base64 s) ++
      ld32tTail rd ri i
    | none =>
      let (head, rt, ri) := match exprReg? fl.alloc t with
        | some r =>
          match exprReg? fl.alloc i with
          | some ri => ([], r, ri)
          | none => (compileETo tab fl tmp AbiReg.a0 i, r, AbiReg.a0)
        | none =>
          match emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 t with
          | some ct =>
            match exprReg? fl.alloc i with
            | some ri => (ct, AbiReg.t0, ri)
            | none => (compileETo tab fl tmp AbiReg.a0 i ++ ct, AbiReg.t0, AbiReg.a0)
          | none =>
            (compileETo tab fl tmp AbiReg.a0 t ++
             storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp) ++
             compileETo tab fl (tmp + 1) AbiReg.a0 i ++
             loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff tmp),
             AbiReg.t0, AbiReg.a0)
      head ++
      [Asm.andi AbiReg.t0 rt 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
       Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (tab.len64 (TieredArray.t0 a)) ++
      [Asm.srli AbiReg.t3 ri 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t3 (tab.base64 (TieredArray.t0 a)) ++
      ld32tTail rd ri i
  | .ld32h a t i hi =>
    emitLd32hFrom tab fl tmp rd a t i hi
      (fun () => compileETo tab fl tmp AbiReg.a0 i)
      (fun () => compileETo tab fl tmp AbiReg.a0 t)
      (fun () => compileETo tab fl (tmp + 1) AbiReg.a0 i)

/-- Compile condition `c` under `fl`, jumping to `target` iff `c` evaluates to `want`. -/
def compileCR (tab : Tab) (fl : FrameLayout) (tmp : Nat) (pfx : String) (lblId : Nat)
    (c : Cond) (want : Bool) (target : String) : (List AsmItem × Nat) :=
  match c with
  | .cmp op a b =>
    let code :=
      match exprReg? fl.alloc a, exprReg? fl.alloc b with
      | some ra, some rb => [brCmp op want ra rb target]
      | none, some rb => compileETo tab fl tmp AbiReg.a0 a ++ [brCmp op want AbiReg.a0 rb target]
      | some ra, none => compileETo tab fl tmp AbiReg.a0 b ++ [brCmp op want ra AbiReg.a0 target]
      | none, none =>
        match emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 b with
        | some cb => compileETo tab fl tmp AbiReg.a0 a ++ cb ++ [brCmp op want AbiReg.a0 AbiReg.t0 target]
        | none =>
          match emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 a with
          | some ca => compileETo tab fl tmp AbiReg.a0 b ++ ca ++ [brCmp op want AbiReg.t0 AbiReg.a0 target]
          | none =>
            if exprNoT4 b then
              compileETo tab fl tmp AbiReg.a0 a ++
              [Asm.mv AbiReg.t4 AbiReg.a0] ++
              compileETo tab fl tmp AbiReg.a0 b ++
              [brCmp op want AbiReg.t4 AbiReg.a0 target]
            else
              compileETo tab fl tmp AbiReg.a0 a ++
              storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp) ++
              compileETo tab fl (tmp + 1) AbiReg.a0 b ++
              loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff tmp) ++
              [brCmp op want AbiReg.t0 AbiReg.a0 target]
    (code, lblId)
  | .not p => compileCR tab fl tmp pfx lblId p (!want) target
  | .and p q =>
    if want then
      let skipLbl := s!"{pfx}_and_{lblId}"
      let (cp, id1) := compileCR tab fl tmp pfx (lblId + 1) p false skipLbl
      let (cq, id2) := compileCR tab fl tmp pfx id1 q true target
      (cp ++ cq ++ [Asm.lbl skipLbl], id2)
    else
      let (cp, id1) := compileCR tab fl tmp pfx lblId p false target
      let (cq, id2) := compileCR tab fl tmp pfx id1 q false target
      (cp ++ cq, id2)
  | .or p q =>
    if want then
      let (cp, id1) := compileCR tab fl tmp pfx lblId p true target
      let (cq, id2) := compileCR tab fl tmp pfx id1 q true target
      (cp ++ cq, id2)
    else
      let skipLbl := s!"{pfx}_or_{lblId}"
      let (cp, id1) := compileCR tab fl tmp pfx (lblId + 1) p true skipLbl
      let (cq, id2) := compileCR tab fl tmp pfx id1 q false target
      (cp ++ cq ++ [Asm.lbl skipLbl], id2)

def compileEvalExprsToTempsR (tab : Tab) (fl : FrameLayout) (tmp : Nat) : List Expr → List AsmItem
  | [] => []
  | e :: es =>
    (match exprReg? fl.alloc e with
     | some r => storeMemOff .sd AbiReg.sp r AbiReg.t0 (fl.tempSlotOff tmp)
     | none =>
       compileETo tab fl tmp AbiReg.a0 e ++
       storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp)) ++
    compileEvalExprsToTempsR tab fl (tmp + 1) es

def copyTempsToResultsR (tab : Tab) (fl : FrameLayout) (tmp count : Nat) : List AsmItem :=
  if count == 0 then
    if 0 < tab.nres then [Asm.addi AbiReg.a0 AbiReg.zero 0#12] else []
  else
    (List.range (min count tab.nres)).flatMap fun i =>
      if i < maxRes then
        loadMemOff .ld (resReg i) AbiReg.sp AbiReg.t0 (fl.tempSlotOff (tmp + i))
      else
        loadMemOff .ld AbiReg.t1 AbiReg.sp AbiReg.t2 (fl.tempSlotOff (tmp + i)) ++
        storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t2 (tab.resOff i)

def copyResultsToLocalsR (tab : Tab) (fl : FrameLayout) (xs : List Var) : List AsmItem :=
  (xs.zipIdx).flatMap fun (x, i) =>
    match fl.alloc.lookup x with
    | some rx =>
      if i < tab.nres then
        if i < maxRes then
          if rx == resReg i then [] else [Asm.mv rx (resReg i)]
        else
          loadMemOff .ld rx AbiReg.gp AbiReg.t2 (tab.resOff i)
      else
        [Asm.addi rx AbiReg.zero 0#12]
    | none =>
      if !(x ∈ fl.spilledVars) then []
      else if i < tab.nres then
        if i < maxRes then
          storeMemOff .sd AbiReg.sp (resReg i) AbiReg.t0 (fl.varSlotOff x)
        else
          loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (tab.resOff i) ++
          storeMemOff .sd AbiReg.sp AbiReg.t1 AbiReg.t2 (fl.varSlotOff x)
      else
        storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t0 (fl.varSlotOff x)

def evalWArrTierToTempR (tab : Tab) (fl : FrameLayout) (tmp : Nat) (w : WArr) :
    (ArrId × List AsmItem) :=
  match w with
  | .plain a => (a, storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t0 (fl.tempSlotOff tmp))
  | .tier a t =>
    match exprReg? fl.alloc t with
    | some rt => (a, storeMemOff .sd AbiReg.sp rt AbiReg.t0 (fl.tempSlotOff tmp))
    | none =>
      (a, compileETo tab fl tmp AbiReg.a0 t ++
          storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp))

/-- Evaluate store index/value pair `(i, e)` into registers `(ri, re)` avoiding stack spills. -/
def compileStorePairR (tab : Tab) (fl : FrameLayout) (i e : Expr) : (List AsmItem × Reg × Reg) :=
  match exprReg? fl.alloc i, exprReg? fl.alloc e with
  | some ri, some re => ([], ri, re)
  | some ri, none => (compileETo tab fl 0 AbiReg.a0 e, ri, AbiReg.a0)
  | none, some re => (compileETo tab fl 0 AbiReg.a0 i, AbiReg.a0, re)
  | none, none =>
    match emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 i with
    | some ci => (compileETo tab fl 0 AbiReg.a0 e ++ ci, AbiReg.t0, AbiReg.a0)
    | none =>
      match emitSimpleExprR tab fl AbiReg.a0 AbiReg.t1 e with
      | some ce =>
        (compileETo tab fl 0 AbiReg.a0 i ++ [Asm.mv AbiReg.t0 AbiReg.a0] ++ ce, AbiReg.t0, AbiReg.a0)
      | none =>
        (compileETo tab fl 0 AbiReg.a0 i ++
         storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 0) ++
         compileETo tab fl 1 AbiReg.a0 e ++
         loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 0),
         AbiReg.t0, AbiReg.a0)

/-- Evaluate tiered store triple `(t, i, e)` into registers `(rt, ri, re)` avoiding stack spills. -/
def compileTierStoreTripleR (tab : Tab) (fl : FrameLayout) (t i e : Expr) :
    (List AsmItem × Reg × Reg × Reg) :=
  match exprReg? fl.alloc t with
  | some rt =>
    match exprReg? fl.alloc i, exprReg? fl.alloc e with
    | some ri, some re => ([], rt, ri, re)
    | some ri, none => (compileETo tab fl 0 AbiReg.a0 e, rt, ri, AbiReg.a0)
    | none, some re => (compileETo tab fl 0 AbiReg.a0 i, rt, AbiReg.a0, re)
    | none, none =>
      match emitSimpleExprR tab fl AbiReg.t3 AbiReg.t4 i with
      | some ci => (compileETo tab fl 0 AbiReg.a0 e ++ ci, rt, AbiReg.t3, AbiReg.a0)
      | none =>
        match emitSimpleExprR tab fl AbiReg.a0 AbiReg.t4 e with
        | some ce =>
          (compileETo tab fl 0 AbiReg.a0 i ++ [Asm.mv AbiReg.t3 AbiReg.a0] ++ ce, rt, AbiReg.t3, AbiReg.a0)
        | none =>
          (compileETo tab fl 0 AbiReg.a0 i ++
           storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 0) ++
           compileETo tab fl 1 AbiReg.a0 e ++
           loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 0),
           rt, AbiReg.t3, AbiReg.a0)
  | none =>
    match emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 t with
    | some ct =>
      match emitSimpleExprR tab fl AbiReg.t3 AbiReg.t4 i with
      | some ci => (compileETo tab fl 0 AbiReg.a0 e ++ ct ++ ci, AbiReg.t0, AbiReg.t3, AbiReg.a0)
      | none =>
        match emitSimpleExprR tab fl AbiReg.a0 AbiReg.t4 e with
        | some ce =>
          (compileETo tab fl 0 AbiReg.a0 i ++ [Asm.mv AbiReg.t3 AbiReg.a0] ++ ct ++ ce, AbiReg.t0, AbiReg.t3, AbiReg.a0)
        | none =>
          (compileETo tab fl 0 AbiReg.a0 i ++
           storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 0) ++
           compileETo tab fl 1 AbiReg.a0 e ++
           loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 0) ++ ct,
           AbiReg.t0, AbiReg.t3, AbiReg.a0)
    | none =>
      (compileETo tab fl 0 AbiReg.a0 t ++
       storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 0) ++
       compileETo tab fl 1 AbiReg.a0 i ++
       storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 1) ++
       compileETo tab fl 2 AbiReg.a0 e ++
       loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 0) ++
       loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 1),
       AbiReg.t0, AbiReg.t3, AbiReg.a0)

/-- Evaluate expressions `es` in reverse index order (`idx + es.length - 1 .. idx`) directly
    into argument/result registers `resReg (idx + i)` (`a0..a7`) with zero stack temp spills. -/
def compileEvalRevToRegs (tab : Tab) (fl : FrameLayout) (idx : Nat) : List Expr → List AsmItem
  | [] => []
  | e :: rest =>
    compileEvalRevToRegs tab fl (idx + 1) rest ++
    compileETo tab fl 0 (resReg idx) e

/-- Evaluate call arguments `args` into `a0..a7` (`resReg 0..7`) + overflow pointer `t0` (for `args.length > maxRes`),
    followed by budget check and decrement (`s0`). Whenever `revDirectSafe true fl.alloc args` holds,
    evaluates directly in reverse order into `a7..a0` with zero stack spills. -/
def compileCallArgsR (tab : Tab) (fl : FrameLayout) (args : List Expr) : List AsmItem :=
  let budget :=
    [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
     Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)]
  if revDirectSafe true fl.alloc args then
    compileEvalRevToRegs tab fl 0 args ++ budget
  else
    compileEvalExprsToTempsR tab fl 0 args ++
    budget ++
    ((List.range (min args.length maxRes)).flatMap fun i =>
      loadMemOff .ld (resReg i) AbiReg.sp AbiReg.t0 (fl.tempSlotOff i)) ++
    (if maxRes < args.length then
      addImmOff AbiReg.t0 AbiReg.sp AbiReg.t2 (fl.tempSlotOff maxRes)
     else [])

/-- Evaluate return list `es` into `a0..a7` (and `tab.resOff` for `i ≥ maxRes`), evaluating
    directly into `a0..a7` in reverse order with zero temp spills whenever `revDirectSafe` holds.
    For frameless leaf functions (`fl.isLeaf && fl.frameSlots == 0`), emits `ret` directly in place
    of `j retLbl`. -/
def compileRetR (tab : Tab) (fl : FrameLayout) (retLbl : String) (isTail : Bool) (es : List Expr) :
    List AsmItem :=
  let jRet :=
    if isTail then []
    else if fl.isLeaf && fl.frameSlots == 0 then [Asm.ret]
    else [Asm.j retLbl]
  match es with
  | [] => copyTempsToResultsR tab fl 0 0 ++ jRet
  | [e] => compileETo tab fl 0 AbiReg.a0 e ++ jRet
  | _ =>
    if revDirectSafe fl.isLeaf fl.alloc es then
      compileEvalRevToRegs tab fl 0 es ++ jRet
    else
      compileEvalExprsToTempsR tab fl 0 es ++
      copyTempsToResultsR tab fl 0 es.length ++
      jRet

def saveCalleeRegs (fl : FrameLayout) : List AsmItem :=
  fl.savedRegs.zipIdx.flatMap fun (r, i) =>
    storeMemOff .sd AbiReg.sp r AbiReg.t2 (fl.savedOff i)

def restoreCalleeRegs (fl : FrameLayout) : List AsmItem :=
  fl.savedRegs.zipIdx.flatMap fun (r, i) =>
    loadMemOff .ld r AbiReg.sp AbiReg.t0 (fl.savedOff i)

/-- Epilogue frame tear-down sequence (shared by normal epilogue and direct tail calls).
    Restores callee-saved registers, reloads `ra` (when non-leaf), and pops `sp`; preserves `a0..a7` and `s0`. -/
def framePopItems (fl : FrameLayout) : List AsmItem :=
  if fl.frameBytes == 0 then []
  else
    restoreCalleeRegs fl ++
    (if fl.isLeaf then [] else [Asm.ld AbiReg.ra AbiReg.sp 0#12]) ++
    addImmOff AbiReg.sp AbiReg.sp AbiReg.t0 fl.frameBytes

/-- Compile statement `s` under register-allocated frame layout `fl`.
    When `isTail = true`, execution falling off the end of `s` immediately reaches `retLbl`. -/
def compileSR (tab : Tab) (fl : FrameLayout) (pfx : String) (lblId : Nat)
    (brkLbl : Option String) (retLbl : String) (isTail : Bool) (s : Stmt) : (List AsmItem × Nat) :=
  let abort0Lbl := s!"{pfx}_abort0stub"
  match s with
  | .skip => ([], lblId)
  | .set x e =>
    let code :=
      match fl.alloc.lookup x with
      | some rx => compileETo tab fl 0 rx e
      | none =>
        if !(x ∈ fl.spilledVars) then
          if isSimpleExpr e then [] else compileETo tab fl 0 AbiReg.a0 e
        else
          match exprReg? fl.alloc e with
          | some r => storeMemOff .sd AbiReg.sp r AbiReg.t0 (fl.varSlotOff x)
          | none =>
            compileETo tab fl 0 AbiReg.a0 e ++
            storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.varSlotOff x)
    (code, lblId)
  | .gset g e =>
    let code :=
      match exprReg? fl.alloc e with
      | some r => storeMemOffGp fl.useT5Gp .sd r AbiReg.t0 (tab.globOff g)
      | none =>
        compileETo tab fl 0 AbiReg.a0 e ++
        storeMemOffGp fl.useT5Gp .sd AbiReg.a0 AbiReg.t0 (tab.globOff g)
    (code, lblId)
  | .st8 _ _ _ => ([], lblId)
  | .st64 a i e =>
    let (cp, ri, re) := compileStorePairR tab fl i e
    let code :=
      cp ++
      loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (tab.len64 (TieredArray.t0 a)) ++
      [Asm.bgeu ri AbiReg.t1 errLabel] ++
      loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (tab.base64 (TieredArray.t0 a)) ++
      st64Tail re ri AbiReg.t2 i
    (code, lblId)
  | .st64t a t i e =>
    match t.constVal? with
    | some wt =>
      let sa := tierA a wt
      let (cp, ri, re) := compileStorePairR tab fl i e
      let code :=
        cp ++
        loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (tab.len64 sa) ++
        [Asm.bgeu ri AbiReg.t1 errLabel] ++
        loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (tab.base64 sa) ++
        st64Tail re ri AbiReg.t2 i
      (code, lblId)
    | none =>
      let (cp, rt, ri, re) := compileTierStoreTripleR tab fl t i e
      let code :=
        cp ++
        [Asm.andi AbiReg.t0 rt 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
         Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
        loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t4 (tab.len64 (TieredArray.t0 a)) ++
        [Asm.bgeu ri AbiReg.t2 errLabel] ++
        loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t4 (tab.base64 (TieredArray.t0 a)) ++
        st64Tail re ri AbiReg.t4 i
      (code, lblId)
  | .st32t a t i e =>
    match t.constVal? with
    | some wt =>
      let sa := tierA a wt
      let (cp, ri, re) := compileStorePairR tab fl i e
      let code :=
        cp ++
        loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (tab.len64 sa) ++
        [Asm.srli AbiReg.t2 ri 1#6, Asm.bgeu AbiReg.t2 AbiReg.t1 errLabel] ++
        loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (tab.base64 sa) ++
        st32tTail re ri AbiReg.t2 i
      (code, lblId)
    | none =>
      let (cp, rt, ri, re) := compileTierStoreTripleR tab fl t i e
      let code :=
        cp ++
        [Asm.andi AbiReg.t0 rt 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
         Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
        loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t4 (tab.len64 (TieredArray.t0 a)) ++
        [Asm.srli AbiReg.t4 ri 1#6, Asm.bgeu AbiReg.t4 AbiReg.t2 errLabel] ++
        loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t4 (tab.base64 (TieredArray.t0 a)) ++
        st32tTail re ri AbiReg.t4 i
      (code, lblId)
  | .seq s1 s2 =>
    match tailCallRetMatch tab s1 s2 with
    | some (_, f, args, _) =>
      (compileCallArgsR tab fl args ++ framePopItems fl ++ [Asm.j (fnLabel f)], lblId)
    | none =>
      let (c1, id1) := compileSR tab fl pfx lblId brkLbl retLbl false s1
      let (c2, id2) := compileSR tab fl pfx id1 brkLbl retLbl isTail s2
      (c1 ++ c2, id2)
  | .ite cond s1 .skip =>
    if isAbort0Stmt s1 then
      compileCR tab fl 0 pfx lblId cond true abort0Lbl
    else
      let endLbl := s!"{pfx}_endif_{lblId}"
      let (cc, id1) := compileCR tab fl 0 pfx (lblId + 1) cond false endLbl
      let (c1, id2) := compileSR tab fl pfx id1 brkLbl retLbl false s1
      (cc ++ c1 ++ [Asm.lbl endLbl], id2)
  | .ite cond .skip s2 =>
    if isAbort0Stmt s2 then
      compileCR tab fl 0 pfx lblId cond false abort0Lbl
    else
      let endLbl := s!"{pfx}_endif_{lblId}"
      let (cc, id1) := compileCR tab fl 0 pfx (lblId + 1) cond true endLbl
      let (c2, id2) := compileSR tab fl pfx id1 brkLbl retLbl false s2
      (cc ++ c2 ++ [Asm.lbl endLbl], id2)
  | .ite cond s1 s2 =>
    let elseLbl := s!"{pfx}_else_{lblId}"
    let endLbl  := s!"{pfx}_endif_{lblId}"
    let (cc, id1) := compileCR tab fl 0 pfx (lblId + 1) cond false elseLbl
    let (c1, id2) := compileSR tab fl pfx id1 brkLbl retLbl false s1
    let (c2, id3) := compileSR tab fl pfx id2 brkLbl retLbl isTail s2
    let jEnd := if stmtMayFallthrough s1 then [Asm.j endLbl] else []
    (cc ++ c1 ++ jEnd ++ [Asm.lbl elseLbl] ++ c2 ++ [Asm.lbl endLbl], id3)
  | .while cond body =>
    let loopLbl := s!"{pfx}_while_{lblId}"
    let endLbl  := s!"{pfx}_endw_{lblId}"
    let (cc, id1) := compileCR tab fl 0 pfx (lblId + 1) cond false endLbl
    let (cb, id2) := compileSR tab fl pfx id1 (some endLbl) retLbl false body
    let code :=
      [Asm.lbl loopLbl] ++
      cc ++
      cb ++
      [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
       Asm.addi AbiReg.s0 AbiReg.s0 (-1#12),
       Asm.j loopLbl,
       Asm.lbl endLbl]
    (code, id2)
  | .brk =>
    let tgt := brkLbl.getD retLbl
    ([Asm.j tgt], lblId)
  | .ret es =>
    (compileRetR tab fl retLbl isTail es, lblId)
  | .call xs f args =>
    let reloadT5 := if fl.useT5Gp then [Asm.addi AbiReg.t5 AbiReg.gp 2047#12] else []
    let code :=
      compileCallArgsR tab fl args ++
      [Asm.call (fnLabel f)] ++
      reloadT5 ++
      copyResultsToLocalsR tab fl xs
    (code, lblId)
  | .abort e =>
    if e.constVal? == some 0 then ([Asm.j abort0Lbl], lblId)
    else (compileETo tab fl 0 AbiReg.a0 e ++ [Asm.j abortLabel], lblId)
  | .copy64 d di src si n =>
    let (da, cd) := evalWArrTierToTempR tab fl 0 d
    let cdi := compileETo tab fl 1 AbiReg.a0 di ++
      storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 1)
    let (sa, cs) := evalWArrTierToTempR tab fl 2 src
    let csi := compileETo tab fl 3 AbiReg.a0 si ++
      storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 3)
    let cn := compileETo tab fl 4 AbiReg.a0 n ++
      storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 4)
    let loopLbl := s!"{pfx}_c64_{lblId}"
    let doneLbl := s!"{pfx}_c64_done_{lblId}"
    let code :=
      cd ++ cdi ++ cs ++ csi ++ cn ++
      loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 0) ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
       Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (tab.len64 (TieredArray.t0 da)) ++
      loadMemOff .ld AbiReg.t1 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 1) ++
      loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 4) ++
      [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel,
       Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3,
       Asm.bltu AbiReg.t0 AbiReg.t1 errLabel] ++
      loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (tab.base64 (TieredArray.t0 da)) ++
      [Asm.slli AbiReg.t1 AbiReg.t1 3#6, Asm.add AbiReg.t1 AbiReg.t5 AbiReg.t1] ++
      loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t2 (fl.tempSlotOff 2) ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
       Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (tab.len64 (TieredArray.t0 sa)) ++
      loadMemOff .ld AbiReg.t2 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 3) ++
      [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel,
       Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3,
       Asm.bltu AbiReg.t0 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (tab.base64 (TieredArray.t0 sa)) ++
      [Asm.slli AbiReg.t2 AbiReg.t2 3#6, Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2,
       Asm.lbl loopLbl,
       Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
       Asm.ld AbiReg.t4 AbiReg.t2 0#12,
       Asm.sd AbiReg.t1 AbiReg.t4 0#12,
       Asm.addi AbiReg.t1 AbiReg.t1 8#12,
       Asm.addi AbiReg.t2 AbiReg.t2 8#12,
       Asm.addi AbiReg.t3 AbiReg.t3 (-1#12),
       Asm.j loopLbl,
       Asm.lbl doneLbl]
    (code, lblId + 1)
  | .copy8w d di src si n =>
    let (da, cd) := evalWArrTierToTempR tab fl 0 d
    let cdi := compileETo tab fl 1 AbiReg.a0 di ++
      storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 1)
    let csi := compileETo tab fl 3 AbiReg.a0 si ++
      storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 3)
    let cn := compileETo tab fl 4 AbiReg.a0 n ++
      storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 4)
    let srcSetup := match src with
      | .arr a =>
        loadMemOff .ld AbiReg.t0 AbiReg.gp AbiReg.t6 (tab.len8 a) ++
        loadMemOff .ld AbiReg.t5 AbiReg.gp AbiReg.t6 (tab.base8 a)
      | .rom bs =>
        li AbiReg.t0 (BitVec.ofNat 64 bs.length) ++
        addImmOff AbiReg.t5 AbiReg.gp AbiReg.t6 (tab.romBase + (romIdx bs tab.rom : Int))
    let loopLbl := s!"{pfx}_c8w_{lblId}"
    let doneLbl := s!"{pfx}_c8w_done_{lblId}"
    let code :=
      cd ++ cdi ++ csi ++ cn ++
      loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 0) ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
       Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (tab.len64 (TieredArray.t0 da)) ++
      loadMemOff .ld AbiReg.t1 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 1) ++
      loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 4) ++
      [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel,
       Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3,
       Asm.bltu AbiReg.t0 AbiReg.t1 errLabel] ++
      loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (tab.base64 (TieredArray.t0 da)) ++
      [Asm.slli AbiReg.t1 AbiReg.t1 3#6, Asm.add AbiReg.t1 AbiReg.t5 AbiReg.t1] ++
      srcSetup ++
      loadMemOff .ld AbiReg.t2 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 3) ++
      [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel,
       Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3,
       Asm.bltu AbiReg.t0 AbiReg.t2 errLabel,
       Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2,
       Asm.lbl loopLbl,
       Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
       Asm.lbu AbiReg.t4 AbiReg.t2 0#12,
       Asm.sd AbiReg.t1 AbiReg.t4 0#12,
       Asm.addi AbiReg.t1 AbiReg.t1 8#12,
       Asm.addi AbiReg.t2 AbiReg.t2 1#12,
       Asm.addi AbiReg.t3 AbiReg.t3 (-1#12),
       Asm.j loopLbl,
       Asm.lbl doneLbl]
    (code, lblId + 1)
  | .scan8 x src i e c =>
    let ieCode :=
      match emitSimpleExprR tab fl AbiReg.a0 AbiReg.t5 e with
      | some ce =>
        let ci := match exprReg? fl.alloc i with
          | some ri => [Asm.mv AbiReg.t3 ri]
          | none => compileETo tab fl 0 AbiReg.a0 i ++ [Asm.mv AbiReg.t3 AbiReg.a0]
        ci ++ ce
      | none =>
        compileETo tab fl 0 AbiReg.a0 i ++
        storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 0) ++
        compileETo tab fl 1 AbiReg.a0 e ++
        loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t5 (fl.tempSlotOff 0)
    let srcSetup := match src with
      | .arr a =>
        loadMemOff .ld AbiReg.t0 AbiReg.gp AbiReg.t5 (tab.len8 a) ++
        loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t5 (tab.base8 a)
      | .rom bs =>
        li AbiReg.t0 (BitVec.ofNat 64 bs.length) ++
        addImmOff AbiReg.t1 AbiReg.gp AbiReg.t5 (tab.romBase + (romIdx bs tab.rom : Int))
    let loopLbl := s!"{pfx}_scan_{lblId}"
    let doneLbl := s!"{pfx}_scan_done_{lblId}"
    let storeX := match fl.alloc.lookup x with
      | some rx => [Asm.mv rx AbiReg.t3]
      | none => if !(x ∈ fl.spilledVars) then [] else storeMemOff .sd AbiReg.sp AbiReg.t3 AbiReg.t5 (fl.varSlotOff x)
    let code :=
      ieCode ++
      srcSetup ++
      [Asm.bltu AbiReg.a0 AbiReg.t3 errLabel,
       Asm.bltu AbiReg.t0 AbiReg.a0 errLabel] ++
      addImmOff AbiReg.t2 AbiReg.gp AbiReg.t5 (tab.romBase + (romIdx c tab.rom : Int)) ++
      [Asm.lbl loopLbl,
       Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl,
       Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3,
       Asm.lbu AbiReg.t4 AbiReg.t4 0#12,
       Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4,
       Asm.lbu AbiReg.t5 AbiReg.t5 0#12,
       Asm.bne AbiReg.t5 AbiReg.zero doneLbl,
       Asm.addi AbiReg.t3 AbiReg.t3 1#12,
       Asm.j loopLbl,
       Asm.lbl doneLbl] ++
      storeX
    (code, lblId + 1)

def copyParamsR (fl : FrameLayout) (nparams : Nat) : List AsmItem :=
  (List.range nparams).flatMap fun i =>
    if i < maxRes then
      let src := resReg i
      match fl.alloc.lookup i with
      | some rx => if rx == src then [] else [Asm.mv rx src]
      | none =>
        if !(i ∈ fl.spilledVars) then []
        else storeMemOff .sd AbiReg.sp src AbiReg.t2 (fl.varSlotOff i)
    else
      let off : Int := 8 * Int.ofNat (i - maxRes)
      match fl.alloc.lookup i with
      | some rx => loadMemOff .ld rx AbiReg.t0 AbiReg.t2 off
      | none =>
        if !(i ∈ fl.spilledVars) then []
        else
          loadMemOff .ld AbiReg.t4 AbiReg.t0 AbiReg.t2 off ++
          storeMemOff .sd AbiReg.sp AbiReg.t4 AbiReg.t2 (fl.varSlotOff i)

def zeroLocalsR (fl : FrameLayout) (fd : FunDecl) : List AsmItem :=
  (List.range (fl.nlocals - fd.nparams)).flatMap fun j =>
    let x := fd.nparams + j
    if !varNeedsZeroInit fd x then []
    else match fl.alloc.lookup x with
      | some rx => [Asm.addi rx AbiReg.zero 0#12]
      | none =>
        if !(x ∈ fl.spilledVars) then []
        else storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t2 (fl.varSlotOff x)

/-! ## 4. Function & Program Compilation -/

/-- True iff `items` contains a conditional branch targeting `tgt`. -/
def hasBranchTo (tgt : String) (items : List AsmItem) : Bool :=
  items.any fun it => match it with
    | .br _ _ _ t | .brLong _ _ _ t => t == tgt
    | _ => false

/-- Rewrite branch target `old1 → new1` and optional `old2 → new2` for cold tail stubs. -/
def retargetBranchTarget (old1 new1 old2 : String) (new2? : Option String) (t : String) : String :=
  if t == old1 then new1
  else match new2? with
    | some new2 => if t == old2 then new2 else t
    | none => t

/-- Rewrite `.br`/`.brLong` targeting `old1`/`old2` to per-function cold trampoline stubs. -/
def retargetBranchItem (old1 new1 old2 : String) (new2? : Option String) : AsmItem → AsmItem
  | .br op r1 r2 t => .br op r1 r2 (retargetBranchTarget old1 new1 old2 new2? t)
  | .brLong op r1 r2 t => .brLong op r1 r2 (retargetBranchTarget old1 new1 old2 new2? t)
  | it => it

/-- Compile a single function declaration `f` using an explicit `rawAlloc` register-allocation hint. -/
def compileFnWith (rawAlloc : RegAlloc) (tab : Tab) (f : FnName) (fd : FunDecl) : List AsmItem :=
  let fl := fnFrameLayoutForWith rawAlloc tab fd
  let frameBytes := fl.frameBytes
  let pfx := fnLabel f
  let epilogueZero := s!"{pfx}_ret0"
  let epilogue := s!"{pfx}_epilogue"
  let errStubLbl := s!"{pfx}_errstub"
  let exhStubLbl := s!"{pfx}_exhstub"
  let abort0Lbl := s!"{pfx}_abort0stub"
  let framePush : List AsmItem :=
    if frameBytes == 0 then []
    else
      li AbiReg.t2 (BitVec.ofInt 64 frameBytes) ++
      [Asm.bltu AbiReg.sp AbiReg.t2 errLabel,
       Asm.sub AbiReg.sp AbiReg.sp AbiReg.t2,
       Asm.ld AbiReg.t2 AbiReg.gp 8#12,
       Asm.bltu AbiReg.sp AbiReg.t2 errLabel] ++
      (if fl.isLeaf then [] else [Asm.sd AbiReg.sp AbiReg.ra 0#12]) ++
      saveCalleeRegs fl
  let t5Init : List AsmItem :=
    if fl.useT5Gp then [Asm.addi AbiReg.t5 AbiReg.gp 2047#12] else []
  let prologue : List AsmItem :=
    [Asm.lbl pfx] ++ framePush ++ copyParamsR fl fd.nparams ++ zeroLocalsR fl fd ++ t5Init
  let canTailElide := !stmtMayFallthrough fd.body
  let (bodyCode, _) := compileSR tab fl pfx 0 none epilogue canTailElide fd.body
  let hasErr := hasBranchTo errLabel prologue || hasBranchTo errLabel bodyCode
  let hasExh := hasBranchTo exhaustedLabel bodyCode
  let hasAb0 := stmtHasAbort0 fd.body
  let needRetarget := hasErr || hasExh
  let exhSub? : Option String := if hasExh then some exhStubLbl else none
  let rt := retargetBranchItem errLabel errStubLbl exhaustedLabel exhSub?
  let fallthroughZero : List AsmItem :=
    [Asm.lbl epilogueZero] ++
    (if stmtMayFallthrough fd.body then copyTempsToResultsR tab fl 0 0 else [])
  let epilogueCode : List AsmItem := [Asm.lbl epilogue] ++ framePopItems fl ++ [Asm.ret]
  let coldStubs : List AsmItem :=
    (if needRetarget then [Asm.lbl errStubLbl, Asm.j errLabel] else []) ++
    (if hasExh then [Asm.lbl exhStubLbl, Asm.j exhaustedLabel] else []) ++
    (if hasAb0 then [Asm.lbl abort0Lbl, Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.j abortLabel] else [])
  (if needRetarget then prologue.map rt ++ bodyCode.map rt else prologue ++ bodyCode) ++
    fallthroughZero ++ epilogueCode ++ coldStubs

/-- Compile a single function declaration `f` with validated register allocation & compact frame. -/
def compileFn (tab : Tab) (f : FnName) (fd : FunDecl) : List AsmItem :=
  let fl := fnFrameLayoutFor tab fd
  let frameBytes := fl.frameBytes
  let pfx := fnLabel f
  let epilogueZero := s!"{pfx}_ret0"
  let epilogue := s!"{pfx}_epilogue"
  let errStubLbl := s!"{pfx}_errstub"
  let exhStubLbl := s!"{pfx}_exhstub"
  let abort0Lbl := s!"{pfx}_abort0stub"
  let framePush : List AsmItem :=
    if frameBytes == 0 then []
    else
      li AbiReg.t2 (BitVec.ofInt 64 frameBytes) ++
      [Asm.bltu AbiReg.sp AbiReg.t2 errLabel,
       Asm.sub AbiReg.sp AbiReg.sp AbiReg.t2,
       Asm.ld AbiReg.t2 AbiReg.gp 8#12,
       Asm.bltu AbiReg.sp AbiReg.t2 errLabel] ++
      (if fl.isLeaf then [] else [Asm.sd AbiReg.sp AbiReg.ra 0#12]) ++
      saveCalleeRegs fl
  let t5Init : List AsmItem :=
    if fl.useT5Gp then [Asm.addi AbiReg.t5 AbiReg.gp 2047#12] else []
  let prologue : List AsmItem :=
    [Asm.lbl pfx] ++ framePush ++ copyParamsR fl fd.nparams ++ zeroLocalsR fl fd ++ t5Init
  let canTailElide := !stmtMayFallthrough fd.body
  let (bodyCode, _) := compileSR tab fl pfx 0 none epilogue canTailElide fd.body
  let hasErr := hasBranchTo errLabel prologue || hasBranchTo errLabel bodyCode
  let hasExh := hasBranchTo exhaustedLabel bodyCode
  let hasAb0 := stmtHasAbort0 fd.body
  let needRetarget := hasErr || hasExh
  let exhSub? : Option String := if hasExh then some exhStubLbl else none
  let rt := retargetBranchItem errLabel errStubLbl exhaustedLabel exhSub?
  let fallthroughZero : List AsmItem :=
    [Asm.lbl epilogueZero] ++
    (if stmtMayFallthrough fd.body then copyTempsToResultsR tab fl 0 0 else [])
  let epilogueCode : List AsmItem := [Asm.lbl epilogue] ++ framePopItems fl ++ [Asm.ret]
  let coldStubs : List AsmItem :=
    (if needRetarget then [Asm.lbl errStubLbl, Asm.j errLabel] else []) ++
    (if hasExh then [Asm.lbl exhStubLbl, Asm.j exhaustedLabel] else []) ++
    (if hasAb0 then [Asm.lbl abort0Lbl, Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.j abortLabel] else [])
  (if needRetarget then prologue.map rt ++ bodyCode.map rt else prologue ++ bodyCode) ++
    fallthroughZero ++ epilogueCode ++ coldStubs

theorem compileFn_eq_with (tab : Tab) (f : FnName) (fd : FunDecl) :
    compileFn tab f fd = compileFnWith (chooseRegAlloc fd) tab f fd := rfl

/-- Trampoline + runtime exit stubs (`ca_enter`, `ca_exhausted`, `ca_error`, `ca_abort`, `ca_ret_restore`). -/
def compileTrampoline (tab : Tab) (entry : FnName) (entryNparams : Nat) : List AsmItem :=
  [Asm.lbl enterLabel] ++
  callerSaveAsm AbiReg.a0 (tab.saveBase entryNparams) ++
  [Asm.mv AbiReg.s1 AbiReg.sp,
   Asm.mv AbiReg.s2 AbiReg.ra,
   Asm.mv AbiReg.gp AbiReg.a0,
   Asm.mv AbiReg.s0 AbiReg.a1,
   Asm.ld AbiReg.sp AbiReg.gp 0#12,
   Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
   Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++
  ((List.range (min entryNparams maxRes)).flatMap fun i =>
    loadMemOff .ld (resReg i) AbiReg.gp AbiReg.t2 (tab.args + 8 * Int.ofNat i)) ++
  addImmOff AbiReg.t0 AbiReg.gp AbiReg.t2
    (tab.args + 8 * Int.ofNat (if maxRes < entryNparams then maxRes else 0)) ++
  li AbiReg.t1 (BitVec.ofNat 64 entryNparams) ++
  [Asm.call (fnLabel entry),
   Asm.addi AbiReg.a1 AbiReg.zero 0#12,
   Asm.j retRestoreLabel,
   -- Exhausted exit: (a0 = 0, a1 = 1)
   Asm.lbl exhaustedLabel,
   Asm.addi AbiReg.a0 AbiReg.zero 0#12,
   Asm.addi AbiReg.a1 AbiReg.zero 1#12,
   Asm.j retRestoreLabel,
   -- Error exit: (a0 = 0, a1 = 2)
   Asm.lbl errLabel,
   Asm.addi AbiReg.a0 AbiReg.zero 0#12,
   -- Abort exit: (a0 = abort code, a1 = 2)
   Asm.lbl abortLabel,
   Asm.addi AbiReg.a1 AbiReg.zero 2#12,
   Asm.lbl retRestoreLabel] ++
  callerRestoreRetAsm AbiReg.gp (tab.saveBase entryNparams)

/-! ## 5. Region Layout Constants & ROM Word Packing -/

def abiSlot : Nat := 2 ^ 35
def abiStack : Nat := 2 ^ 30
def abiFuel : Nat := 2 ^ 62 - 1
def abiWords : Nat := 2 ^ 32

def Tab.nbuf (tab : Tab) : Nat := min tab.nb 2
def Tab.slotOf (tab : Tab) (p : Nat) : Nat := p + 2 - tab.nbuf
def Tab.nslot (tab : Tab) : Nat := tab.slotOf (tab.nb + tab.nw)
def abiNeed (tab : Tab) : Nat := abiSlot * tab.nslot

/-- Little-endian 64-bit word from up to 8 bytes (padded with zeros). -/
def romWord64 (bs : List UInt8) : BitVec 64 :=
  BitVec.ofNat 64 ((bs.zipIdx).foldl (fun acc (b, i) => acc + b.toNat * 2 ^ (8 * i)) 0)

def romWords64 : List UInt8 → List (BitVec 64)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    romWord64 [b0, b1, b2, b3, b4, b5, b6, b7] :: romWords64 rest
  | [] => []
  | bs => [romWord64 bs]

/-- Extract static call sites with enclosing loop depth from a `_root_.L.Stmt`. -/
def stmtCallsDepth (d : Nat) : Stmt → List (FnName × Nat)
  | .call _ f _ => [(f, d)]
  | .seq s1 s2 => stmtCallsDepth d s1 ++ stmtCallsDepth d s2
  | .ite _ s1 s2 => stmtCallsDepth d s1 ++ stmtCallsDepth d s2
  | .while _ b => stmtCallsDepth (d + 1) b
  | _ => []

/-- Maximum loop nesting depth inside a `_root_.L.Stmt`. -/
def stmtLoopDepth : Stmt → Nat
  | .while _ b => 1 + stmtLoopDepth b
  | .seq s1 s2 => max (stmtLoopDepth s1) (stmtLoopDepth s2)
  | .ite _ s1 s2 => max (stmtLoopDepth s1) (stmtLoopDepth s2)
  | _ => 0

/-- Pure-integer, entry-point-agnostic static call-graph layout hint generator for the
    `64 KiB` 2-way associative `I$`. Computes Kosaraju recursive SCCs, 24-iteration integer
    PageRank weighted by loop-nesting depth (`8^min(d,3)`), and emits a hot-threshold (`≥ 10%`)
    highest-scored-callee-first DFS ordering to cluster callers with hot callees while deferring
    cold functions to the tail of ROM. Verified via `applyOrderHint` / `orderProgFns_perm`. -/
def chooseFnOrder (p : Prog) : List FnName := Id.run do
  let mut adj : Std.HashMap FnName (List (FnName × Nat)) := {}
  let mut totalEdges : Nat := 0
  for (f, fd) in p do
    let mut agg : Std.HashMap FnName Nat := {}
    for (g, d) in stmtCallsDepth 0 fd.body do
      agg := agg.insert g (agg.getD g 0 + 8 ^ (min d 3))
    let cs := agg.toList
    totalEdges := totalEdges + cs.length
    adj := adj.insert f cs
  let mut rev : Std.HashMap FnName (List FnName) := {}
  let mut isRec : Std.HashSet FnName := {}
  for (f, _) in p do
    for (g, _) in adj.getD f [] do
      if g == f then isRec := isRec.insert f
      rev := rev.insert g (f :: rev.getD g [])
  let maxSteps := 2 * p.length + totalEdges + 1
  let mut vis : Std.HashSet FnName := {}
  let mut finish : Array FnName := #[]
  for (root, _) in p do
    if !vis.contains root then
      let mut stk : List (FnName × Bool) := [(root, false)]
      for _ in [:maxSteps] do
        match stk with
        | [] => break
        | (u, done) :: rest =>
          stk := rest
          if done then finish := finish.push u
          else if !vis.contains u then
            vis := vis.insert u
            stk := (u, true) :: stk
            for (v, _) in adj.getD u [] do
              if !vis.contains v then stk := (v, false) :: stk
  let mut vis2 : Std.HashSet FnName := {}
  for i in [:finish.size] do
    let root := finish[finish.size - 1 - i]!
    if !vis2.contains root then
      let mut comp : Array FnName := #[]
      let mut stk : List FnName := [root]
      for _ in [:maxSteps] do
        match stk with
        | [] => break
        | u :: rest =>
          stk := rest
          if !vis2.contains u then
            vis2 := vis2.insert u; comp := comp.push u
            for v in rev.getD u [] do
              if !vis2.contains v then stk := v :: stk
      if comp.size > 1 then
        for u in comp do isRec := isRec.insert u
  let mut sc : Std.HashMap FnName Nat := {}
  for (f, _) in p do sc := sc.insert f 10000
  for _ in [:24] do
    let mut nxt : Std.HashMap FnName Nat := {}
    for (f, _) in p do nxt := nxt.insert f 1500
    for (f, _) in p do
      let sf := sc.getD f 0
      let cs := adj.getD f []
      let totW := cs.foldl (fun a (_, w) => a + w) 0
      if totW > 0 then
        let mult := if isRec.contains f then 115 else 100
        let budget := (sf * 85 * mult) / 10000
        for (g, w) in cs do
          nxt := nxt.insert g (nxt.getD g 0 + (budget * w) / totW)
    let mut mx : Nat := 1
    for (_, v) in nxt.toList do if v > mx then mx := v
    let mut norm : Std.HashMap FnName Nat := {}
    for (k, v) in nxt.toList do norm := norm.insert k ((v * 1000000) / mx)
    sc := norm
  let mut finalSc : Std.HashMap FnName Nat := {}
  for (f, fd) in p do
    let m1 := if stmtLoopDepth fd.body > 0 then 2 else 1
    let m2 := if isRec.contains f then 4 else 1
    finalSc := finalSc.insert f (sc.getD f 0 * m1 * m2)
  let seeds := p.toArray.qsort fun a b =>
    let sa := finalSc.getD a.1 0; let sb := finalSc.getD b.1 0
    if sa != sb then sa > sb else a.1 < b.1
  let mut vis3 : Std.HashSet FnName := {}
  let mut out : Array FnName := #[]
  for (root, _) in seeds do
    if !vis3.contains root then
      let mut stk : List FnName := [root]
      for _ in [:maxSteps] do
        match stk with
        | [] => break
        | u :: rest =>
          stk := rest
          if !vis3.contains u then
            vis3 := vis3.insert u; out := out.push u
            let su := finalSc.getD u 0
            let cs := ((adj.getD u []).filter fun (g, _) =>
              finalSc.getD g 0 * 10 >= su).toArray.qsort fun a b =>
              let ka := a.2 * (finalSc.getD a.1 0 + 1)
              let kb := b.2 * (finalSc.getD b.1 0 + 1)
              if ka != kb then ka > kb else a.1 < b.1
            for i in [:cs.size] do
              let g := cs[cs.size - 1 - i]!.1
              if !vis3.contains g then stk := g :: stk
  return out.toList

/-- Extract the first entry matching `name` from `p`, returning `(entry?, rest)`. -/
def extractByName (name : FnName) : Prog → Option (FnName × FunDecl) × Prog
  | [] => (none, [])
  | (f, fd) :: rest =>
    if f == name then (some (f, fd), rest)
    else
      let (res, rest') := extractByName name rest
      (res, (f, fd) :: rest')

/-- Reorder `p` by extracting function entries in `hint` order, then appending the rest.
    Always produces an exact `List.Perm` of `p` regardless of `hint`. -/
def applyOrderHint : List FnName → Prog → Prog
  | [], p => p
  | name :: rest, p =>
    match extractByName name p with
    | (none, p') => applyOrderHint rest p'
    | (some entry, p') => entry :: applyOrderHint rest p'

/-- Reorder `p`'s functions for instruction-cache locality; always a `List.Perm` of `p`. -/
def orderProgFns (p : Prog) : Prog :=
  if p.length ≤ 1 then p else applyOrderHint (chooseFnOrder p) p

theorem extractByName_perm (name : FnName) : ∀ (p : Prog),
    match extractByName name p with
    | (none, p') => p' = p
    | (some entry, p') => (entry :: p').Perm p
  | [] => rfl
  | (f, fd) :: rest => by
    unfold extractByName
    by_cases hfn : (f == name) = true
    · simp only [hfn, ↓reduceIte]
      exact List.Perm.refl _
    · have hfnF : (f == name) = false := Bool.eq_false_iff.mpr hfn
      simp only [hfnF, Bool.false_eq_true, ↓reduceIte]
      have ih := extractByName_perm name rest
      cases h : extractByName name rest with
      | mk o rest' =>
        rw [h] at ih
        cases o with
        | none => dsimp only; rw [ih]
        | some e =>
          dsimp only
          exact (List.Perm.swap (f, fd) e rest').trans (List.Perm.cons (f, fd) ih)

theorem applyOrderHint_perm : ∀ (hint : List FnName) (p : Prog),
    (applyOrderHint hint p).Perm p
  | [], p => List.Perm.refl p
  | name :: rest, p => by
    unfold applyOrderHint
    have hex := extractByName_perm name p
    cases h : extractByName name p with
    | mk o p' =>
      rw [h] at hex
      cases o with
      | none => rw [hex]; exact applyOrderHint_perm rest p
      | some entry =>
        exact (List.Perm.cons entry (applyOrderHint_perm rest p')).trans hex

theorem orderProgFns_perm (p : Prog) : (orderProgFns p).Perm p := by
  unfold orderProgFns
  split
  · exact List.Perm.refl p
  · exact applyOrderHint_perm _ p

/-- Compile a `MiniL` program (without entry stub, starting at `ca_enter`). -/
def compileProgAsm (tab : Tab) (p : Prog) (entry : FnName) (entryNparams : Nat := 0) : List AsmItem :=
  compileTrampoline tab entry entryNparams ++
  ((orderProgFns p).flatMap fun (f, fd) => compileFn tab f fd)

def maxVarExpr : Expr → Nat
  | .const _ | .len8 _ | .len64 _ | .glob _ => 0
  | .var x => x + 1
  | .ld8 _ i | .ld64 _ i | .ldc _ i | .len64t _ i | .ld8x8 _ i => maxVarExpr i
  | .bin _ a b | .cmpw _ a b | .ld64t _ a b | .ld32t _ a b | .ld32h _ a b _ =>
    max (maxVarExpr a) (maxVarExpr b)

def maxVarWArr : WArr → Nat
  | .plain _ => 0
  | .tier _ t => maxVarExpr t

def maxVarCond : Cond → Nat
  | .cmp _ a b => max (maxVarExpr a) (maxVarExpr b)
  | .and p q | .or p q => max (maxVarCond p) (maxVarCond q)
  | .not p => maxVarCond p

def maxVarExprs : List Expr → Nat
  | [] => 0
  | e :: es => max (maxVarExpr e) (maxVarExprs es)

def maxVarVars : List Var → Nat
  | [] => 0
  | x :: xs => max (x + 1) (maxVarVars xs)

def maxVarStmt : Stmt → Nat
  | .skip | .brk => 0
  | .set x e => max (x + 1) (maxVarExpr e)
  | .gset _ e | .abort e => maxVarExpr e
  | .st8 _ i e | .st64 _ i e => max (maxVarExpr i) (maxVarExpr e)
  | .st64t _ t i e | .st32t _ t i e => max (maxVarExpr t) (max (maxVarExpr i) (maxVarExpr e))
  | .seq s t => max (maxVarStmt s) (maxVarStmt t)
  | .ite c s t => max (maxVarCond c) (max (maxVarStmt s) (maxVarStmt t))
  | .while c s => max (maxVarCond c) (maxVarStmt s)
  | .ret es => maxVarExprs es
  | .call xs _ args => max (maxVarExprs args) (maxVarVars xs)
  | .copy64 d di s si n =>
    max (maxVarWArr d) (max (maxVarExpr di) (max (maxVarWArr s) (max (maxVarExpr si) (maxVarExpr n))))
  | .copy8w d di _ si n =>
    max (maxVarWArr d) (max (maxVarExpr di) (max (maxVarExpr si) (maxVarExpr n)))
  | .scan8 x _ i e _ => max (x + 1) (max (maxVarExpr i) (maxVarExpr e))

private theorem collectExprInfo_maxV_le : ∀ (e : Expr),
    (collectExprInfo e).2.2.2.1 ≤ maxVarExpr e
  | .const _ | .len8 _ | .len64 _ | .glob _ => Nat.le_refl 0
  | .var _ => Nat.le_refl _
  | .ld8 _ i | .ld64 _ i | .ldc _ i | .len64t _ i => collectExprInfo_maxV_le i
  | .ld8x8 src i => by cases src <;> exact collectExprInfo_maxV_le i
  | .bin _ a b | .cmpw _ a b | .ld64t _ a b | .ld32t _ a b | .ld32h _ a b _ => by
    have ha := collectExprInfo_maxV_le a
    have hb := collectExprInfo_maxV_le b
    simp only [collectExprInfo, maxVarExpr]
    exact Nat.max_le.mpr ⟨Nat.le_trans ha (Nat.le_max_left _ _), Nat.le_trans hb (Nat.le_max_right _ _)⟩

private theorem collectWArrInfo_maxV_le : ∀ (w : WArr),
    (collectWArrInfo w).2.2.2.1 ≤ maxVarWArr w
  | .plain _ => Nat.le_refl 0
  | .tier _ t => collectExprInfo_maxV_le t

private theorem collectCondInfo_maxV_le : ∀ (c : Cond),
    (collectCondInfo c).2.2.2.1 ≤ maxVarCond c
  | .cmp _ a b => collectExprInfo_maxV_le (.cmpw .eq a b)
  | .and p q | .or p q => by
    have hp := collectCondInfo_maxV_le p
    have hq := collectCondInfo_maxV_le q
    simp only [collectCondInfo, maxVarCond]
    exact Nat.max_le.mpr ⟨Nat.le_trans hp (Nat.le_max_left _ _), Nat.le_trans hq (Nat.le_max_right _ _)⟩
  | .not p => collectCondInfo_maxV_le p

private theorem collectExprsInfo_foldl_maxV_le (es : List Expr)
    (acc : List ArrId × List (ArrId × Bool) × List (List UInt8) × Nat × Nat) :
    (es.foldl (fun acc e => mergeInfo5 acc (collectExprInfo e)) acc).2.2.2.1 ≤
      max acc.2.2.2.1 (maxVarExprs es) := by
  induction es generalizing acc with
  | nil => exact Nat.le_max_left _ _
  | cons e es ih =>
    have he := collectExprInfo_maxV_le e
    have hrest := ih (mergeInfo5 acc (collectExprInfo e))
    have hm : (mergeInfo5 acc (collectExprInfo e)).2.2.2.1 =
        max acc.2.2.2.1 (collectExprInfo e).2.2.2.1 := rfl
    rw [hm] at hrest
    simp only [List.foldl_cons, maxVarExprs]
    omega

private theorem collectExprsInfo_maxV_le (es : List Expr) :
    (collectExprsInfo es).2.2.2.1 ≤ maxVarExprs es := by
  have h := collectExprsInfo_foldl_maxV_le es ([], [], [], 0, 0)
  have h0 : (([], [], [], 0, 0) :
      List ArrId × List (ArrId × Bool) × List (List UInt8) × Nat × Nat).2.2.2.1 = 0 := rfl
  rw [h0] at h
  dsimp only [collectExprsInfo]
  omega

private theorem foldl_max_vars_le (xs : List Var) (m : Nat) :
    xs.foldl (fun acc x => max acc (x + 1)) m ≤ max m (maxVarVars xs) := by
  induction xs generalizing m with
  | nil => exact Nat.le_max_left _ _
  | cons x xs ih =>
    have hrest := ih (max m (x + 1))
    simp only [List.foldl_cons, maxVarVars]
    omega

private theorem collectStmtInfo_maxV_le : ∀ (s : Stmt),
    (collectStmtInfo s).2.2.2.1 ≤ maxVarStmt s
  | .skip | .brk => Nat.le_refl 0
  | .set _ e => by
    have he := collectExprInfo_maxV_le e
    simp only [collectStmtInfo, maxVarStmt]
    exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans he (Nat.le_max_right _ _)⟩
  | .st8 _ i e | .st64 _ i e => by
    have hi := collectExprInfo_maxV_le i
    have he := collectExprInfo_maxV_le e
    simp only [collectStmtInfo, mergeInfo5, maxVarStmt]
    omega
  | .seq s t => by
    have hs := collectStmtInfo_maxV_le s
    have ht := collectStmtInfo_maxV_le t
    simp only [collectStmtInfo, maxVarStmt]
    exact Nat.max_le.mpr ⟨Nat.le_trans hs (Nat.le_max_left _ _), Nat.le_trans ht (Nat.le_max_right _ _)⟩
  | .ite _ s t => by
    have hs := collectStmtInfo_maxV_le s
    have ht := collectStmtInfo_maxV_le t
    simp only [collectStmtInfo, maxVarStmt]
    exact Nat.le_trans
      (Nat.max_le.mpr ⟨Nat.le_trans hs (Nat.le_max_left _ _), Nat.le_trans ht (Nat.le_max_right _ _)⟩)
      (Nat.le_max_right _ _)
  | .while c s => by
    have hc := collectCondInfo_maxV_le c
    have hs := collectStmtInfo_maxV_le s
    simp only [collectStmtInfo, maxVarStmt]
    exact Nat.max_le.mpr ⟨Nat.le_trans hc (Nat.le_max_left _ _), Nat.le_trans hs (Nat.le_max_right _ _)⟩
  | .ret es => collectExprsInfo_maxV_le es
  | .call xs _ args => by
    have ha := collectExprsInfo_maxV_le args
    have hx := foldl_max_vars_le xs 0
    simp only [collectStmtInfo, maxVarStmt]
    exact Nat.max_le.mpr ⟨Nat.le_trans ha (Nat.le_max_left _ _), Nat.le_trans hx (Nat.le_max_right _ _)⟩
  | .abort e | .gset _ e => collectExprInfo_maxV_le e
  | .st64t _ t i e | .st32t _ t i e => by
    have ht := collectExprInfo_maxV_le t
    have hi := collectExprInfo_maxV_le i
    have he := collectExprInfo_maxV_le e
    simp only [collectStmtInfo, mergeInfo5, maxVarStmt]
    omega
  | .copy64 d di s si n => by
    have hd := collectWArrInfo_maxV_le d
    have hdi := collectExprInfo_maxV_le di
    have hs := collectWArrInfo_maxV_le s
    have hsi := collectExprInfo_maxV_le si
    have hn := collectExprInfo_maxV_le n
    simp only [collectStmtInfo, mergeInfo5, maxVarStmt]
    omega
  | .copy8w d di s si n => by
    have hd := collectWArrInfo_maxV_le d
    have hdi := collectExprInfo_maxV_le di
    have hsi := collectExprInfo_maxV_le si
    have hn := collectExprInfo_maxV_le n
    cases s <;> simp only [collectStmtInfo, mergeInfo5, maxVarStmt] <;> omega
  | .scan8 _ s i e _ => by
    have hi := collectExprInfo_maxV_le i
    have he := collectExprInfo_maxV_le e
    cases s <;> simp only [collectStmtInfo, mergeInfo5, maxVarStmt] <;> omega

private theorem collectCondStmtInfo_maxV_le : ∀ (s : Stmt),
    (collectCondStmtInfo s).2.2.2.1 ≤ maxVarStmt s
  | .ite c s t => by
    have hc := collectCondInfo_maxV_le c
    have hs := collectCondStmtInfo_maxV_le s
    have ht := collectCondStmtInfo_maxV_le t
    simp only [collectCondStmtInfo, maxVarStmt]
    exact Nat.max_le.mpr
      ⟨Nat.le_trans hc (Nat.le_max_left _ _),
       Nat.le_trans
         (Nat.max_le.mpr ⟨Nat.le_trans hs (Nat.le_max_left _ _), Nat.le_trans ht (Nat.le_max_right _ _)⟩)
         (Nat.le_max_right _ _)⟩
  | .while c s => by
    have hc := collectCondInfo_maxV_le c
    have hs := collectCondStmtInfo_maxV_le s
    simp only [collectCondStmtInfo, maxVarStmt]
    exact Nat.max_le.mpr ⟨Nat.le_trans hc (Nat.le_max_left _ _), Nat.le_trans hs (Nat.le_max_right _ _)⟩
  | .seq s t => by
    have hs := collectCondStmtInfo_maxV_le s
    have ht := collectCondStmtInfo_maxV_le t
    simp only [collectCondStmtInfo, maxVarStmt]
    exact Nat.max_le.mpr ⟨Nat.le_trans hs (Nat.le_max_left _ _), Nat.le_trans ht (Nat.le_max_right _ _)⟩
  | .skip | .brk | .set _ _ | .st8 _ _ _ | .st64 _ _ _ | .ret _ | .call _ _ _
  | .abort _ | .gset _ _ | .st64t _ _ _ _ | .copy64 _ _ _ _ _ | .copy8w _ _ _ _ _
  | .scan8 _ _ _ _ _ | .st32t _ _ _ _ => collectStmtInfo_maxV_le _

theorem numLocalsFn_le_maxVar (fd : FunDecl) :
    numLocalsFn fd ≤ max fd.nlocals (max fd.nparams (maxVarStmt fd.body)) := by
  have h := collectCondStmtInfo_maxV_le fd.body
  simp only [numLocalsFn]
  exact Nat.max_le.mpr
    ⟨Nat.le_max_left _ _,
     Nat.le_trans (Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans h (Nat.le_max_right _ _)⟩)
       (Nat.le_max_right _ _)⟩

end ConAgua.RISCV.Compiler
