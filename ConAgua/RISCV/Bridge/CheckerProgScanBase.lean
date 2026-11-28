import Lean
import ConAgua.Checker.ProgWf
import ConAgua.Checker.ProgTree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Shared Base for Single-Pass Fused Kernel Scan of `L.Checker.checkerProg` & `checkerProgI`

Pure `L` / `ConAgua.Checker.*` definitions, literal tables, single-pass AST scan
(`stmtScanL` / `stmtScanIL`) fusing well-formedness, arg/ROM checks, `fnMinRetL`,
and `(maxTemps, bound32)` metrics (dropping `maxVar` since `fastStmt` bounds every
variable `< fd.nlocals`), and the async-aware `kernel_eq_true` command elaborator.

Does NOT import `ProgSimMain`, `MiniL`, `CheckerLinkSize`, or `CheckerLinkLabelsSR`,
so `CheckerProgScan` compiles in parallel with the entire `ConAgua.RISCV.Compiler.*` stack.
-/

namespace ConAgua.RISCV.Bridge

/-! ## 1. `kernel_eq_true` Command Elaborator & Literal Tables -/

section KernelUtils
open Lean Elab Command Meta Term

/-- Prove `theorem <id> : <term> = true` directly in the kernel without MetaM re-evaluation.
    Uses `addConstAsync` when `Elab.async` is enabled so independent kernel checks run in parallel. -/
syntax (name := kernelEqTrueCmd) "kernel_eq_true " ident " : " term : command

@[command_elab kernelEqTrueCmd] meta def elabKernelEqTrue : CommandElab := fun stx => do
  let `(kernel_eq_true $n:ident : $lhsS:term) := stx | throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM <| withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 262144 }) do
    let lhs ← elabTermEnsuringType lhsS (Lean.mkConst ``Bool)
    synthesizeSyntheticMVarsNoPostponing
    let lhs ← instantiateMVars lhs
    let boolTy := Lean.mkConst ``Bool
    let bTrue := Lean.mkConst ``Bool.true
    let ty := mkApp3 (Lean.mkConst ``Eq [1]) boolTy lhs bTrue
    let pf := mkApp2 (Lean.mkConst ``Eq.refl [1]) boolTy bTrue
    if Elab.async.get (← getOptions) then
      let env ← getEnv
      let async ← env.addConstAsync name .thm
      setEnv async.mainEnv
      async.commitSignature { name, levelParams := [], type := ty }
      let cancelTk ← IO.CancelToken.new
      let act ← Core.wrapAsyncAsSnapshot (desc := s!"kernel_eq_true {name}") (cancelTk? := cancelTk) fun _ => do
        setEnv async.asyncEnv
        addDecl <| .thmDecl { name, levelParams := [], type := ty, value := pf }
        async.commitConst (← getEnv)
        async.commitCheckEnv (← getEnv)
      Core.logSnapshotTask { stx? := none, task := (← BaseIO.asTask (act ())), cancelTk? := cancelTk }
      Core.logSnapshotTask { stx? := none, cancelTk? := none, task := (← getEnv).checked.map fun _ => default }
    else
      addDecl <| .thmDecl { name, levelParams := [], type := ty, value := pf }

end KernelUtils

/-! ## 2. Minimum Return Count & Argument/ROM Checkers on `L` -/

def stmtMayFallL : L.Stmt → Bool
  | .ret _ | .abort _ => false
  | .seq s₁ s₂ => if stmtMayFallL s₁ then stmtMayFallL s₂ else false
  | .ite _ s₁ s₂ => stmtMayFallL s₁ || stmtMayFallL s₂
  | _ => true

def stmtMinRetRawL : L.Stmt → Option Nat
  | .ret es => some (max 1 es.length)
  | .seq s₁ s₂ =>
    match stmtMinRetRawL s₁, stmtMinRetRawL s₂ with
    | none, y => y
    | x, none => x
    | some a, some b => some (min a b)
  | .ite _ s₁ s₂ =>
    match stmtMinRetRawL s₁, stmtMinRetRawL s₂ with
    | none, y => y
    | x, none => x
    | some a, some b => some (min a b)
  | .while _ b => stmtMinRetRawL b
  | _ => none

def fnMinRetL (fd : L.FunDecl) : Nat :=
  if stmtMayFallL fd.body then 1
  else match stmtMinRetRawL fd.body with
    | none => 100
    | some k => k

def stmtRetOkNTree (rt : L.Compiler.NTree) : L.Stmt → Bool
  | .seq s₁ s₂ => stmtRetOkNTree rt s₁ && stmtRetOkNTree rt s₂
  | .ite _ s₁ s₂ => stmtRetOkNTree rt s₁ && stmtRetOkNTree rt s₂
  | .while _ s => stmtRetOkNTree rt s
  | .call xs f _ =>
    if xs.length ≤ 1 then true
    else match rt.find (L.Compiler.nameCode f) with
      | some r => decide (xs.length ≤ r)
      | none => false
  | _ => true

def bsrcRomsOk (romOk : List UInt8 → Bool) : L.BSrc → Bool
  | .arr _ => true
  | .rom d => romOk d

def exprRomsOk (romOk : List UInt8 → Bool) : L.Expr → Bool
  | .const _ | .var _ | .len8 _ | .len64 _ | .glob _ => true
  | .bin _ a b | .cmpw _ a b => exprRomsOk romOk a && exprRomsOk romOk b
  | .ld8 _ i | .ld64 _ i | .len64t _ i => exprRomsOk romOk i
  | .ldc d i => romOk d && exprRomsOk romOk i
  | .ld64t _ t i | .ld32t _ t i | .ld32h _ t i _ => exprRomsOk romOk t && exprRomsOk romOk i
  | .ld8x8 b i => bsrcRomsOk romOk b && exprRomsOk romOk i

def condRomsOk (romOk : List UInt8 → Bool) : L.Cond → Bool
  | .cmp _ a b => exprRomsOk romOk a && exprRomsOk romOk b
  | .and p q | .or p q => condRomsOk romOk p && condRomsOk romOk q
  | .not p => condRomsOk romOk p

def warrRomsOk (romOk : List UInt8 → Bool) : L.WArr → Bool
  | .plain _ => true
  | .tier _ t => exprRomsOk romOk t

def stmtArgsAndRomsOk (t rt : L.Compiler.NTree) (romOk : List UInt8 → Bool) : L.Stmt → Bool
  | .skip | .brk => true
  | .abort e | .set _ e | .gset _ e => exprRomsOk romOk e
  | .st8 _ i e | .st64 _ i e => exprRomsOk romOk i && exprRomsOk romOk e
  | .seq s₁ s₂ => stmtArgsAndRomsOk t rt romOk s₁ && stmtArgsAndRomsOk t rt romOk s₂
  | .ite c s₁ s₂ => condRomsOk romOk c && stmtArgsAndRomsOk t rt romOk s₁ && stmtArgsAndRomsOk t rt romOk s₂
  | .while c s => condRomsOk romOk c && stmtArgsAndRomsOk t rt romOk s
  | .ret es => es.all (exprRomsOk romOk)
  | .call xs f args =>
    (match t.find (L.Compiler.nameCode f) with
    | some n => decide (args.length = n)
    | none => false) &&
    (if xs.length ≤ 1 then true
     else match rt.find (L.Compiler.nameCode f) with
      | some r => decide (xs.length ≤ r)
      | none => false) &&
    args.all (exprRomsOk romOk)
  | .st64t _ tt i e | .st32t _ tt i e =>
    exprRomsOk romOk tt && exprRomsOk romOk i && exprRomsOk romOk e
  | .copy64 dst di src si n =>
    warrRomsOk romOk dst && exprRomsOk romOk di &&
    warrRomsOk romOk src && exprRomsOk romOk si && exprRomsOk romOk n
  | .copy8w dst di src si n =>
    warrRomsOk romOk dst && exprRomsOk romOk di &&
    bsrcRomsOk romOk src && exprRomsOk romOk si && exprRomsOk romOk n
  | .scan8 _ s i e c =>
    bsrcRomsOk romOk s && exprRomsOk romOk i && exprRomsOk romOk e && romOk c

/-- Witness list containing all distinct ROM slices used in `checkerProg` & `checkerProgI`. -/
def checkerAllowedRoms : List (List UInt8) :=
  ([3, 200, 609, 712, 982, 1137, 1138, 1139, 1377, 1563, 1873] : List Nat).flatMap fun i =>
    match L.Checker.checkerProgI[i]? with
    | some p => L.Compiler.Stmt.roms p.2.body
    | none => []

section LiteralTables
open Lean Elab Term

private meta def bytes256ToExpr (bs : List UInt8) : Lean.Expr :=
  let arr := bs.toArray
  let ty := mkApp (Lean.mkConst ``List [0]) (Lean.mkConst ``UInt8)
  let k := 256
  let n := (arr.size + k - 1) / k
  let chunks := (List.range n).map fun i => toExpr (arr.extract (i * k) ((i + 1) * k)).toList
  mkApp2 (Lean.mkConst ``List.flatten [0]) (Lean.mkConst ``UInt8)
    (chunks.foldr (fun c acc => mkApp3 (Lean.mkConst ``List.cons [0]) ty c acc)
      (mkApp (Lean.mkConst ``List.nil [0]) ty))

private meta def evalRomsExpr : TermElabM Lean.Expr := do
  let ty := mkApp (Lean.mkConst ``List [0]) (Lean.mkConst ``UInt8)
  let rs : List (List UInt8) :=
    ([3, 200, 609, 712, 982, 1137, 1138, 1139, 1377, 1563, 1873] : List Nat).flatMap fun i =>
      match L.Checker.checkerProgI[i]? with
      | some p => L.Compiler.Stmt.roms p.2.body
      | none => []
  return rs.foldr (fun d acc => mkApp3 (Lean.mkConst ``List.cons [0]) ty (bytes256ToExpr d) acc)
    (mkApp (Lean.mkConst ``List.nil [0]) ty)

private meta def evalRomsWithLenExpr : TermElabM Lean.Expr := do
  let listTy := mkApp (Lean.mkConst ``List [0]) (Lean.mkConst ``UInt8)
  let pairTy := mkApp2 (Lean.mkConst ``Prod [0, 0]) (Lean.mkConst ``Nat) listTy
  let rs : List (List UInt8) :=
    ([3, 200, 609, 712, 982, 1137, 1138, 1139, 1377, 1563, 1873] : List Nat).flatMap fun i =>
      match L.Checker.checkerProgI[i]? with
      | some p => L.Compiler.Stmt.roms p.2.body
      | none => []
  return rs.foldr (fun d acc =>
    let pair := mkApp4 (Lean.mkConst ``Prod.mk [0, 0]) (Lean.mkConst ``Nat) listTy (mkNatLit d.length) (bytes256ToExpr d)
    mkApp3 (Lean.mkConst ``List.cons [0]) pairTy pair acc)
    (mkApp (Lean.mkConst ``List.nil [0]) pairTy)

private meta partial def balancedNTree (arr : Array (Nat × Nat)) (lo hi : Nat) : L.Compiler.NTree :=
  if lo ≥ hi then .leaf
  else
    let mid := (lo + hi) / 2
    let (k, v) := arr[mid]!
    .node (balancedNTree arr lo mid) k v (balancedNTree arr (mid + 1) hi)

private meta def ntreeToExprLocal : L.Compiler.NTree → Lean.Expr
  | .leaf => Lean.mkConst ``L.Compiler.NTree.leaf
  | .node l k v r =>
    mkApp4 (Lean.mkConst ``L.Compiler.NTree.node)
      (ntreeToExprLocal l) (mkNatLit k) (mkNatLit v) (ntreeToExprLocal r)

private meta def mkMinRetTreeExpr (p : L.Prog) : Lean.Expr :=
  let pairs := (p.filterMap fun (f, fd) =>
    let r := fnMinRetL fd
    if r ≤ 1 then none else some (L.Compiler.nameCode f, r)).toArray
  let sorted := pairs.qsort (fun a b => a.1 < b.1)
  ntreeToExprLocal (balancedNTree sorted 0 sorted.size)

local elab "minret_tree_lit%" : term => return mkMinRetTreeExpr L.Checker.checkerProg
local elab "minret_treeI_lit%" : term => return mkMinRetTreeExpr L.Checker.checkerProgI
local elab "allowed_roms_lit%" : term => evalRomsExpr
local elab "allowed_roms_len_lit%" : term => evalRomsWithLenExpr
local elab "lmap_lit%" : term => return L.Compiler.ntreeToExpr L.Checker.checkerTab.lmap

noncomputable def minRetTreeLit : L.Compiler.NTree := minret_tree_lit%
noncomputable def minRetTreeILit : L.Compiler.NTree := minret_treeI_lit%
noncomputable def allowedRomsLit : List (List UInt8) := allowed_roms_lit%
noncomputable def allowedRomsWithLenLit : List (Nat × List UInt8) := allowed_roms_len_lit%
def checkerLmapLit : L.Compiler.NTree := lmap_lit%

end LiteralTables

kernel_eq_true allowedRomsLit_eq_b : allowedRomsLit == checkerAllowedRoms
kernel_eq_true allowedRomsWithLen_snd_eq_b : allowedRomsWithLenLit.map Prod.snd == allowedRomsLit

theorem allowedRomsLit_eq : allowedRomsLit = checkerAllowedRoms :=
  beq_iff_eq.mp allowedRomsLit_eq_b

private theorem allowedRomsWithLen_snd_eq : allowedRomsWithLenLit.map Prod.snd = allowedRomsLit :=
  beq_iff_eq.mp allowedRomsWithLen_snd_eq_b

theorem checkerLmapLit_eq : L.Checker.checkerTab.lmap = checkerLmapLit := rfl
theorem checkerNb_eq : L.Checker.checkerTab.nb = 2 := rfl
theorem checkerNg_eq : L.Checker.checkerTab.ng = 12 := rfl
theorem checkerNres_eq : L.Checker.checkerTab.nres = 10 := rfl

def romFastOkGo (n : Nat) (d : List UInt8) : List (Nat × List UInt8) → Bool
  | [] => false
  | (plen, r) :: rest => (n == plen && d == r) || romFastOkGo n d rest

def romFastOk (roms : List (Nat × List UInt8)) (d : List UInt8) : Bool :=
  romFastOkGo d.length d roms

private theorem romFastOkGo_mem {n : Nat} {d : List UInt8} : ∀ {roms : List (Nat × List UInt8)},
    romFastOkGo n d roms = true → d ∈ roms.map Prod.snd
  | [], h => by cases h
  | (plen, r) :: rest, h => by
    simp only [romFastOkGo, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.map_cons, List.mem_cons] at h ⊢
    rcases h with ⟨_, rfl⟩ | hr
    · exact Or.inl rfl
    · exact Or.inr (romFastOkGo_mem hr)

theorem romFastOk_imp_elem {d : List UInt8}
    (h : romFastOk allowedRomsWithLenLit d = true) :
    allowedRomsLit.elem d = true := by
  have hm : d ∈ allowedRomsWithLenLit.map Prod.snd := romFastOkGo_mem h
  rw [allowedRomsWithLen_snd_eq] at hm
  exact List.elem_eq_true_of_mem hm

/-! ## 3. Statement Well-Formedness Checkers on `L` -/

def brkOkL (inLoop : Bool) : L.Stmt → Bool
  | .brk => inLoop
  | .seq s₁ s₂ | .ite _ s₁ s₂ => brkOkL inLoop s₁ && brkOkL inLoop s₂
  | .while _ s => brkOkL true s
  | _ => true

def noSt8L : L.Stmt → Bool
  | .st8 _ _ _ => false
  | .seq s₁ s₂ | .ite _ s₁ s₂ => noSt8L s₁ && noSt8L s₂
  | .while _ s => noSt8L s
  | _ => true

def const0OnlyL_E : L.Expr → Bool
  | .bin _ a b | .cmpw _ a b => const0OnlyL_E a && const0OnlyL_E b
  | .ld8 _ i | .ld64 _ i | .ldc _ i | .ld8x8 _ i => const0OnlyL_E i
  | .ld64t _ t i | .ld32h _ t i _ => const0OnlyL_E t && const0OnlyL_E i
  | .len64t _ t => const0OnlyL_E t
  | .ld32t _ t i =>
    (match t with | .const w => w == 0 || w.toNat % 2 == 1 | _ => true) &&
    const0OnlyL_E t && const0OnlyL_E i
  | _ => true

def const0OnlyL_C : L.Cond → Bool
  | .cmp _ a b => const0OnlyL_E a && const0OnlyL_E b
  | .and p q | .or p q => const0OnlyL_C p && const0OnlyL_C q
  | .not p => const0OnlyL_C p

def const0OnlyL_S : L.Stmt → Bool
  | .abort e | .set _ e | .gset _ e => const0OnlyL_E e
  | .st8 _ i e | .st64 _ i e => const0OnlyL_E i && const0OnlyL_E e
  | .seq s₁ s₂ => const0OnlyL_S s₁ && const0OnlyL_S s₂
  | .ite c s₁ s₂ => const0OnlyL_C c && const0OnlyL_S s₁ && const0OnlyL_S s₂
  | .while c s => const0OnlyL_C c && const0OnlyL_S s
  | .ret es | .call _ _ es => es.all const0OnlyL_E
  | .st64t _ t i e => const0OnlyL_E t && const0OnlyL_E i && const0OnlyL_E e
  | .st32t _ t i e =>
    (match t with | .const w => w == 0 || w.toNat % 2 == 1 | _ => true) &&
    const0OnlyL_E t && const0OnlyL_E i && const0OnlyL_E e
  | .copy64 d di s si n =>
    (match d with | .tier _ t => const0OnlyL_E t | _ => true) && const0OnlyL_E di &&
    (match s with | .tier _ t => const0OnlyL_E t | _ => true) && const0OnlyL_E si && const0OnlyL_E n
  | .copy8w d di _ si n =>
    (match d with | .tier _ t => const0OnlyL_E t | _ => true) && const0OnlyL_E di && const0OnlyL_E si && const0OnlyL_E n
  | .scan8 _ _ i e _ => const0OnlyL_E i && const0OnlyL_E e
  | _ => true

def fastDom8 (lm : L.Compiler.NTree) (nb : Nat) (a : L.ArrId) : Bool :=
  match lm.find (L.TieredArray.t0 a).code with | some p => decide (p < nb) | none => false

def fastDom64 (lm : L.Compiler.NTree) (nb : Nat) (s : L.TieredArray) : Bool :=
  match lm.find s.code with | some p => decide (nb ≤ p) | none => false

def fastTier32 (lm : L.Compiler.NTree) (nb : Nat) (a : L.ArrId) (e : L.Expr) : Bool :=
  match e with
  | .const w => (w == 0 || w.toNat % 2 == 1) && fastDom64 lm nb (L.tierA a w)
  | _ => fastDom64 lm nb (L.tier1 a)

def fastExpr (lm : L.Compiler.NTree) (nb ng nl : Nat) : L.Expr → Bool
  | .const _ => true
  | .var x => decide (x < nl)
  | .bin _ a b | .cmpw _ a b => fastExpr lm nb ng nl a && fastExpr lm nb ng nl b
  | .ld8 a i => fastDom8 lm nb a && fastExpr lm nb ng nl i
  | .ld64 a i => fastDom64 lm nb (L.TieredArray.t0 a) && fastExpr lm nb ng nl i
  | .len8 a => fastDom8 lm nb a
  | .len64 a => fastDom64 lm nb (L.TieredArray.t0 a)
  | .ldc _ i => fastExpr lm nb ng nl i
  | .glob g => decide (g.id < ng)
  | .ld64t a t i | .ld32h a t i _ => fastDom64 lm nb (L.tier1 a) && fastExpr lm nb ng nl t && fastExpr lm nb ng nl i
  | .ld32t a t i => fastTier32 lm nb a t && fastExpr lm nb ng nl t && fastExpr lm nb ng nl i
  | .len64t a t => fastDom64 lm nb (L.tier1 a) && fastExpr lm nb ng nl t
  | .ld8x8 (.arr a) i => fastDom8 lm nb a && fastExpr lm nb ng nl i
  | .ld8x8 (.rom _) i => fastExpr lm nb ng nl i

def fastCond (lm : L.Compiler.NTree) (nb ng nl : Nat) : L.Cond → Bool
  | .cmp _ a b => fastExpr lm nb ng nl a && fastExpr lm nb ng nl b
  | .and p q | .or p q => fastCond lm nb ng nl p && fastCond lm nb ng nl q
  | .not p => fastCond lm nb ng nl p

def fastWArr (lm : L.Compiler.NTree) (nb ng nl : Nat) : L.WArr → Bool
  | .plain a => fastDom64 lm nb (L.TieredArray.t0 a)
  | .tier a t => fastDom64 lm nb (L.tier1 a) && fastExpr lm nb ng nl t

def fastBSrc (lm : L.Compiler.NTree) (nb : Nat) : L.BSrc → Bool
  | .arr a => fastDom8 lm nb a
  | .rom _ => true

def fastStmt (lm : L.Compiler.NTree) (nb ng nres : Nat) (tr : L.Compiler.NTree)
    (nl : Nat) (inLoop : Bool) : L.Stmt → Bool
  | .skip => true
  | .brk => inLoop
  | .set x e => decide (x < nl) && fastExpr lm nb ng nl e
  | .st8 _ _ _ => false
  | .st64 a i e => fastDom64 lm nb (L.TieredArray.t0 a) && fastExpr lm nb ng nl i && fastExpr lm nb ng nl e
  | .seq s₁ s₂ => fastStmt lm nb ng nres tr nl inLoop s₁ && fastStmt lm nb ng nres tr nl inLoop s₂
  | .ite c s₁ s₂ => fastCond lm nb ng nl c && fastStmt lm nb ng nres tr nl inLoop s₁ && fastStmt lm nb ng nres tr nl inLoop s₂
  | .while c s => fastCond lm nb ng nl c && fastStmt lm nb ng nres tr nl true s
  | .ret es => decide (es.length ≤ nres) && es.all (fastExpr lm nb ng nl)
  | .call xs f args => (tr.find (L.Compiler.nameCode f)).isSome && decide (xs.all (· < nl)) && args.all (fastExpr lm nb ng nl)
  | .abort e => fastExpr lm nb ng nl e
  | .gset g e => decide (g.id < ng) && fastExpr lm nb ng nl e
  | .st64t a t i e => fastDom64 lm nb (L.tier1 a) && fastExpr lm nb ng nl t && fastExpr lm nb ng nl i && fastExpr lm nb ng nl e
  | .st32t a t i e => fastTier32 lm nb a t && fastExpr lm nb ng nl t && fastExpr lm nb ng nl i && fastExpr lm nb ng nl e
  | .copy64 d di s si n => fastWArr lm nb ng nl d && fastExpr lm nb ng nl di && fastWArr lm nb ng nl s && fastExpr lm nb ng nl si && fastExpr lm nb ng nl n
  | .copy8w d di s si n => fastWArr lm nb ng nl d && fastExpr lm nb ng nl di && fastBSrc lm nb s && fastExpr lm nb ng nl si && fastExpr lm nb ng nl n
  | .scan8 x s i e c => decide (x < nl) && fastBSrc lm nb s && fastExpr lm nb ng nl i && fastExpr lm nb ng nl e && decide (256 ≤ c.length)

/-! ## 4. Function-Name Label Safety Checker on `L` (Identical to `fnCharsSafeFast`) -/

def isPrefixCharsL : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | p :: ps, x :: xs => p == x && isPrefixCharsL ps xs

def fixedSufRevL : List (List Char) :=
  ["_ret0", "_epilogue", "_errstub", "_exhstub", "_abort0stub"].map (fun s => s.toList.reverse)

def dynTagRevL : List (List Char) :=
  ["_and_", "_or_", "_else_", "_endif_", "_while_", "_endw_",
   "_c64_", "_c64_done_", "_c8w_", "_c8w_done_", "_scan_", "_scan_done_"].map (fun s => s.toList.reverse)

def dropDigitsRevL : List Char → Bool → List Char × Bool
  | c :: cs, seen => if c.isDigit then dropDigitsRevL cs true else (c :: cs, seen)
  | [], seen => ([], seen)

def fnCharsSafeFastL (cs : List Char) : Bool :=
  match cs with
  | [] => false
  | _ =>
    let rev := cs.reverse
    if fixedSufRevL.any (fun sr => isPrefixCharsL sr rev) then false
    else
      let (rest, seenDigit) := dropDigitsRevL rev false
      !seenDigit || !(dynTagRevL.any (fun tr => isPrefixCharsL tr rest))

/-! ## 5. AST Metrics `(maxTemps, bound32)` on `L` (Dropping `maxVar`) -/

def maxResL : Nat := 8

def exprTempsAndBoundL : L.Expr → Nat × Nat
  | .const _ => (0, 10)
  | .var _ | .len8 _ | .len64 _ | .glob _ => (0, 6)
  | .bin _ a b =>
    let (ta, ba) := exprTempsAndBoundL a
    let (tb, bb) := exprTempsAndBoundL b
    (max ta (1 + tb), ba + bb + 17)
  | .cmpw _ a b =>
    let (ta, ba) := exprTempsAndBoundL a
    let (tb, bb) := exprTempsAndBoundL b
    (max ta (1 + tb), ba + bb + 14)
  | .ld8 _ i =>
    let (ti, bi) := exprTempsAndBoundL i
    (ti, bi + 19)
  | .ld64 _ i =>
    let (ti, bi) := exprTempsAndBoundL i
    (ti, bi + 20)
  | .ldc _ i =>
    let (ti, bi) := exprTempsAndBoundL i
    (ti, bi + 22)
  | .ld64t _ a b =>
    let (ta, ba) := exprTempsAndBoundL a
    let (tb, bb) := exprTempsAndBoundL b
    (max ta (1 + tb), ba + bb + 35)
  | .len64t _ i =>
    let (ti, bi) := exprTempsAndBoundL i
    (ti, bi + 9)
  | .ld8x8 _ i =>
    let (ti, bi) := exprTempsAndBoundL i
    (ti, bi + 54)
  | .ld32t _ a b =>
    let (ta, ba) := exprTempsAndBoundL a
    let (tb, bb) := exprTempsAndBoundL b
    (max ta (1 + tb), ba + bb + 36)
  | .ld32h _ a b _ =>
    let (ta, ba) := exprTempsAndBoundL a
    let (tb, bb) := exprTempsAndBoundL b
    (max ta (1 + tb), ba + bb + 35)

def warrTempsAndBoundL : L.WArr → Nat × Nat
  | .plain _ => (0, 6)
  | .tier _ t =>
    let (tt, bt) := exprTempsAndBoundL t
    (tt, bt + 6)

def condTempsAndBoundL : L.Cond → Nat × Nat
  | .cmp _ a b =>
    let (ta, ba) := exprTempsAndBoundL a
    let (tb, bb) := exprTempsAndBoundL b
    (max ta (1 + tb), ba + bb + 17)
  | .and p q | .or p q =>
    let (tp, bp) := condTempsAndBoundL p
    let (tq, bq) := condTempsAndBoundL q
    (max tp tq, bp + bq)
  | .not p => condTempsAndBoundL p

def exprsTempsAndBoundLGo (idx mt b32 : Nat) : List L.Expr → Nat × Nat
  | [] => (mt, b32)
  | e :: es =>
    let (te, be) := exprTempsAndBoundL e
    exprsTempsAndBoundLGo (idx + 1) (max mt (idx + max 1 te)) (b32 + be + 6) es

def exprsTempsAndBoundL (es : List L.Expr) : Nat × Nat :=
  exprsTempsAndBoundLGo 0 0 0 es

def stmtTempsAndBoundL : L.Stmt → Nat × Nat
  | .skip => (0, 0)
  | .brk => (0, 4)
  | .set _ e =>
    let (te, be) := exprTempsAndBoundL e
    (te, be + 6)
  | .gset _ e =>
    let (te, be) := exprTempsAndBoundL e
    (te, be + 6)
  | .abort e =>
    let (te, be) := exprTempsAndBoundL e
    (te, be + 4)
  | .st8 _ i e =>
    let (ti, _) := exprTempsAndBoundL i
    let (te, _) := exprTempsAndBoundL e
    (max ti (1 + te), 0)
  | .st64 _ i e =>
    let (ti, bi) := exprTempsAndBoundL i
    let (te, be) := exprTempsAndBoundL e
    (max ti (1 + te), bi + be + 32)
  | .st64t _ t i e =>
    let (tt, bt) := exprTempsAndBoundL t
    let (ti, bi) := exprTempsAndBoundL i
    let (te, be) := exprTempsAndBoundL e
    (max tt (max (1 + ti) (2 + te)), bt + bi + be + 47)
  | .st32t _ t i e =>
    let (tt, bt) := exprTempsAndBoundL t
    let (ti, bi) := exprTempsAndBoundL i
    let (te, be) := exprTempsAndBoundL e
    (max tt (max (1 + ti) (2 + te)), bt + bi + be + 48)
  | .seq s₁ s₂ =>
    let (t1, b1) := stmtTempsAndBoundL s₁
    let (t2, b2) := stmtTempsAndBoundL s₂
    (max t1 t2, b1 + b2)
  | .ite c s₁ s₂ =>
    let (tc, bc) := condTempsAndBoundL c
    let (t1, b1) := stmtTempsAndBoundL s₁
    let (t2, b2) := stmtTempsAndBoundL s₂
    (max tc (max t1 t2), bc + b1 + b2 + 4)
  | .while c s =>
    let (tc, bc) := condTempsAndBoundL c
    let (ts, bs) := stmtTempsAndBoundL s
    (max tc ts, bc + bs + 10)
  | .ret es =>
    let (te, be) := exprsTempsAndBoundL es
    (te, be + 124)
  | .call xs _ args =>
    let (ta, ba) := exprsTempsAndBoundL args
    (ta, ba + 16 + 6 * min args.length maxResL + 12 * xs.length)
  | .copy64 d di s si n =>
    let (td, bd) := warrTempsAndBoundL d
    let (tdi, bdi) := exprTempsAndBoundL di
    let (ts, bs) := warrTempsAndBoundL s
    let (tsi, bsi) := exprTempsAndBoundL si
    let (tn, bn) := exprTempsAndBoundL n
    let st := match s with | .plain _ => 0 | .tier _ _ => 2 + ts
    (max td (max (1 + tdi) (max st (max (3 + tsi) (4 + max 1 tn)))),
     bd + bdi + bs + bsi + bn + 120)
  | .copy8w d di _ si n =>
    let (td, bd) := warrTempsAndBoundL d
    let (tdi, bdi) := exprTempsAndBoundL di
    let (tsi, bsi) := exprTempsAndBoundL si
    let (tn, bn) := exprTempsAndBoundL n
    (max td (max (1 + tdi) (max (3 + tsi) (4 + max 1 tn))),
     bd + bdi + bsi + bn + 115)
  | .scan8 _ _ i e _ =>
    let (ti, bi) := exprTempsAndBoundL i
    let (te, be) := exprTempsAndBoundL e
    (max ti (1 + te), bi + be + 70)

def fnBoundAndFrameL (fd : L.FunDecl) : Nat :=
  let (mt, b32) := stmtTempsAndBoundL fd.body
  let nl := max fd.nlocals fd.nparams
  if (nl + mt).blt 100000 then
    59 + 12 * fd.nparams + 6 * (nl - fd.nparams) + b32
  else
    5000000

/-! ## 6. Truly Single-Pass Structural AST Scans (`stmtScanL` & `stmtScanIL`) -/

inductive ScanRes where
  | fail
  | ok (mt b32 : Nat)

inductive StmtScanRes where
  | fail
  | ok (mayFall : Bool) (minRet mt b32 : Nat)

inductive StmtScanIRes where
  | fail
  | ok (mayFall : Bool) (minRet : Nat)

def fastDom8Opt (lm : L.Compiler.NTree) (nb : Nat) (a : L.ArrId) : Bool :=
  match lm.find (L.TieredArray.t0 a).code with | some p => p.blt nb | none => false

def fastDom64Opt (lm : L.Compiler.NTree) (nb : Nat) (s : L.TieredArray) : Bool :=
  match lm.find s.code with | some p => nb.ble p | none => false

def fastTier32Opt (lm : L.Compiler.NTree) (nb : Nat) (a : L.ArrId) (e : L.Expr) : Bool :=
  match e with
  | .const w =>
    if w == 0 then fastDom64Opt lm nb (L.TieredArray.t0 a)
    else if w.toNat % 2 == 1 then fastDom64Opt lm nb (L.tier1 a)
    else false
  | _ => fastDom64Opt lm nb (L.tier1 a)

def exprScanL (lm : L.Compiler.NTree) (nb ng nl : Nat) (romOk : List UInt8 → Bool)
    (b32 : Nat) : L.Expr → ScanRes
  | .const _ => .ok 0 (b32 + 10)
  | .var x => if x.blt nl then .ok 0 (b32 + 6) else .fail
  | .len8 a => if fastDom8Opt lm nb a then .ok 0 (b32 + 6) else .fail
  | .len64 a => if fastDom64Opt lm nb (L.TieredArray.t0 a) then .ok 0 (b32 + 6) else .fail
  | .glob g => if g.id.blt ng then .ok 0 (b32 + 6) else .fail
  | .bin _ a b =>
    match exprScanL lm nb ng nl romOk (b32 + 17) a with
    | .fail => .fail
    | .ok ta b1 =>
      match exprScanL lm nb ng nl romOk b1 b with
      | .fail => .fail
      | .ok tb b2 => .ok (max ta (1 + tb)) b2
  | .cmpw _ a b =>
    match exprScanL lm nb ng nl romOk (b32 + 14) a with
    | .fail => .fail
    | .ok ta b1 =>
      match exprScanL lm nb ng nl romOk b1 b with
      | .fail => .fail
      | .ok tb b2 => .ok (max ta (1 + tb)) b2
  | .ld8 a i =>
    if fastDom8Opt lm nb a then exprScanL lm nb ng nl romOk (b32 + 19) i else .fail
  | .ld64 a i =>
    if fastDom64Opt lm nb (L.TieredArray.t0 a) then exprScanL lm nb ng nl romOk (b32 + 20) i else .fail
  | .ldc d i =>
    if romOk d then exprScanL lm nb ng nl romOk (b32 + 22) i else .fail
  | .ld64t a t i =>
    if fastDom64Opt lm nb (L.tier1 a) then
      match exprScanL lm nb ng nl romOk (b32 + 35) t with
      | .fail => .fail
      | .ok tt b1 =>
        match exprScanL lm nb ng nl romOk b1 i with
        | .fail => .fail
        | .ok ti b2 => .ok (max tt (1 + ti)) b2
    else .fail
  | .ld32t a t i =>
    if fastTier32Opt lm nb a t then
      match exprScanL lm nb ng nl romOk (b32 + 36) t with
      | .fail => .fail
      | .ok tt b1 =>
        match exprScanL lm nb ng nl romOk b1 i with
        | .fail => .fail
        | .ok ti b2 => .ok (max tt (1 + ti)) b2
    else .fail
  | .ld32h a t i _ =>
    if fastDom64Opt lm nb (L.tier1 a) then
      match exprScanL lm nb ng nl romOk (b32 + 35) t with
      | .fail => .fail
      | .ok tt b1 =>
        match exprScanL lm nb ng nl romOk b1 i with
        | .fail => .fail
        | .ok ti b2 => .ok (max tt (1 + ti)) b2
    else .fail
  | .len64t a t =>
    if fastDom64Opt lm nb (L.tier1 a) then exprScanL lm nb ng nl romOk (b32 + 9) t else .fail
  | .ld8x8 b i =>
    let bok := match b with | .arr a => fastDom8Opt lm nb a | .rom d => romOk d
    if bok then exprScanL lm nb ng nl romOk (b32 + 54) i else .fail

def condScanL (lm : L.Compiler.NTree) (nb ng nl : Nat) (romOk : List UInt8 → Bool)
    (b32 : Nat) : L.Cond → ScanRes
  | .cmp _ a b =>
    match exprScanL lm nb ng nl romOk (b32 + 17) a with
    | .fail => .fail
    | .ok ta b1 =>
      match exprScanL lm nb ng nl romOk b1 b with
      | .fail => .fail
      | .ok tb b2 => .ok (max ta (1 + tb)) b2
  | .and p q | .or p q =>
    match condScanL lm nb ng nl romOk b32 p with
    | .fail => .fail
    | .ok tp b1 =>
      match condScanL lm nb ng nl romOk b1 q with
      | .fail => .fail
      | .ok tq b2 => .ok (max tp tq) b2
  | .not p => condScanL lm nb ng nl romOk b32 p

def warrScanL (lm : L.Compiler.NTree) (nb ng nl : Nat) (romOk : List UInt8 → Bool)
    (b32 : Nat) : L.WArr → ScanRes
  | .plain a => if fastDom64Opt lm nb (L.TieredArray.t0 a) then .ok 0 (b32 + 6) else .fail
  | .tier a t => if fastDom64Opt lm nb (L.tier1 a) then exprScanL lm nb ng nl romOk (b32 + 6) t else .fail

def exprsScanLGo (lm : L.Compiler.NTree) (nb ng nl : Nat) (romOk : List UInt8 → Bool)
    (idx mt b32 : Nat) : List L.Expr → ScanRes
  | [] => .ok mt b32
  | e :: es =>
    match exprScanL lm nb ng nl romOk (b32 + 6) e with
    | .fail => .fail
    | .ok te b1 => exprsScanLGo lm nb ng nl romOk (idx + 1) (max mt (idx + max 1 te)) b1 es

def varsLtL (nl : Nat) : List L.Var → Bool
  | [] => true
  | x :: xs => x.blt nl && varsLtL nl xs

def combineMinRet (a b : Nat) : Nat :=
  if a == 0 then b else if b == 0 then a else min a b

def stmtScanL (lm : L.Compiler.NTree) (nb ng nres : Nat) (tr rt : L.Compiler.NTree)
    (romOk : List UInt8 → Bool) (nl : Nat) (inLoop : Bool) (b32 : Nat) : L.Stmt → StmtScanRes
  | .skip => .ok true 0 0 b32
  | .brk => if inLoop then .ok true 0 0 (b32 + 4) else .fail
  | .set x e =>
    if x.blt nl then
      match exprScanL lm nb ng nl romOk (b32 + 6) e with
      | .fail => .fail
      | .ok te b1 => .ok true 0 te b1
    else .fail
  | .gset g e =>
    if g.id.blt ng then
      match exprScanL lm nb ng nl romOk (b32 + 6) e with
      | .fail => .fail
      | .ok te b1 => .ok true 0 te b1
    else .fail
  | .abort e =>
    match exprScanL lm nb ng nl romOk (b32 + 4) e with
    | .fail => .fail
    | .ok te b1 => .ok false 0 te b1
  | .st8 _ _ _ => .fail
  | .st64 a i e =>
    if fastDom64Opt lm nb (L.TieredArray.t0 a) then
      match exprScanL lm nb ng nl romOk (b32 + 32) i with
      | .fail => .fail
      | .ok ti b1 =>
        match exprScanL lm nb ng nl romOk b1 e with
        | .fail => .fail
        | .ok te b2 => .ok true 0 (max ti (1 + te)) b2
    else .fail
  | .st64t a t i e =>
    if fastDom64Opt lm nb (L.tier1 a) then
      match exprScanL lm nb ng nl romOk (b32 + 47) t with
      | .fail => .fail
      | .ok tt b1 =>
        match exprScanL lm nb ng nl romOk b1 i with
        | .fail => .fail
        | .ok ti b2 =>
          match exprScanL lm nb ng nl romOk b2 e with
          | .fail => .fail
          | .ok te b3 => .ok true 0 (max tt (max (1 + ti) (2 + te))) b3
    else .fail
  | .st32t a t i e =>
    if fastTier32Opt lm nb a t then
      match exprScanL lm nb ng nl romOk (b32 + 48) t with
      | .fail => .fail
      | .ok tt b1 =>
        match exprScanL lm nb ng nl romOk b1 i with
        | .fail => .fail
        | .ok ti b2 =>
          match exprScanL lm nb ng nl romOk b2 e with
          | .fail => .fail
          | .ok te b3 => .ok true 0 (max tt (max (1 + ti) (2 + te))) b3
    else .fail
  | .seq s₁ s₂ =>
    match stmtScanL lm nb ng nres tr rt romOk nl inLoop b32 s₁ with
    | .fail => .fail
    | .ok mf1 mr1 t1 b1 =>
      match stmtScanL lm nb ng nres tr rt romOk nl inLoop b1 s₂ with
      | .fail => .fail
      | .ok mf2 mr2 t2 b2 => .ok (mf1 && mf2) (combineMinRet mr1 mr2) (max t1 t2) b2
  | .ite c s₁ s₂ =>
    match condScanL lm nb ng nl romOk (b32 + 4) c with
    | .fail => .fail
    | .ok tc b1 =>
      match stmtScanL lm nb ng nres tr rt romOk nl inLoop b1 s₁ with
      | .fail => .fail
      | .ok mf1 mr1 t1 b2 =>
        match stmtScanL lm nb ng nres tr rt romOk nl inLoop b2 s₂ with
        | .fail => .fail
        | .ok mf2 mr2 t2 b3 => .ok (mf1 || mf2) (combineMinRet mr1 mr2) (max tc (max t1 t2)) b3
  | .while c s =>
    match condScanL lm nb ng nl romOk (b32 + 10) c with
    | .fail => .fail
    | .ok tc b1 =>
      match stmtScanL lm nb ng nres tr rt romOk nl true b1 s with
      | .fail => .fail
      | .ok _ mrs ts b2 => .ok true mrs (max tc ts) b2
  | .ret es =>
    if es.length.ble nres then
      match exprsScanLGo lm nb ng nl romOk 0 0 (b32 + 124) es with
      | .fail => .fail
      | .ok te b1 => .ok false (max 1 es.length) te b1
    else .fail
  | .call xs f args =>
    let nc := L.Compiler.nameCode f
    match tr.find nc with
    | none => .fail
    | some n =>
      if args.length == n && varsLtL nl xs &&
         (xs.length.ble 1 || match rt.find nc with | some r => xs.length.ble r | none => false) then
        match exprsScanLGo lm nb ng nl romOk 0 0 (b32 + 16 + 6 * min args.length maxResL + 12 * xs.length) args with
        | .fail => .fail
        | .ok ta b1 => .ok true 0 ta b1
      else .fail
  | .copy64 d di s si n =>
    match warrScanL lm nb ng nl romOk (b32 + 120) d with
    | .fail => .fail
    | .ok td b1 =>
      match exprScanL lm nb ng nl romOk b1 di with
      | .fail => .fail
      | .ok tdi b2 =>
        match warrScanL lm nb ng nl romOk b2 s with
        | .fail => .fail
        | .ok ts b3 =>
          match exprScanL lm nb ng nl romOk b3 si with
          | .fail => .fail
          | .ok tsi b4 =>
            match exprScanL lm nb ng nl romOk b4 n with
            | .fail => .fail
            | .ok tn b5 =>
              let st := match s with | .plain _ => 0 | .tier _ _ => 2 + ts
              .ok true 0 (max td (max (1 + tdi) (max st (max (3 + tsi) (4 + max 1 tn))))) b5
  | .copy8w d di s si n =>
    let sok := match s with | .arr a => fastDom8Opt lm nb a | .rom d => romOk d
    if sok then
      match warrScanL lm nb ng nl romOk (b32 + 115) d with
      | .fail => .fail
      | .ok td b1 =>
        match exprScanL lm nb ng nl romOk b1 di with
        | .fail => .fail
        | .ok tdi b2 =>
          match exprScanL lm nb ng nl romOk b2 si with
          | .fail => .fail
          | .ok tsi b3 =>
            match exprScanL lm nb ng nl romOk b3 n with
            | .fail => .fail
            | .ok tn b4 => .ok true 0 (max td (max (1 + tdi) (max (3 + tsi) (4 + max 1 tn)))) b4
    else .fail
  | .scan8 x s i e c =>
    let sok := match s with | .arr a => fastDom8Opt lm nb a | .rom d => romOk d
    if x.blt nl && sok && Nat.ble 256 c.length && romOk c then
      match exprScanL lm nb ng nl romOk (b32 + 70) i with
      | .fail => .fail
      | .ok ti b1 =>
        match exprScanL lm nb ng nl romOk b1 e with
        | .fail => .fail
        | .ok te b2 => .ok true 0 (max ti (1 + te)) b2
    else .fail

@[inline] def okIfI (b : Bool) (mf : Bool) (mr : Nat) : StmtScanIRes :=
  if b then .ok mf mr else .fail

def stmtScanIL (rt : L.Compiler.NTree) (inLoop : Bool) : L.Stmt → StmtScanIRes
  | .skip => .ok true 0
  | .brk => okIfI inLoop true 0
  | .st8 _ _ _ => .fail
  | .abort e => okIfI (const0OnlyL_E e) false 0
  | .set _ e | .gset _ e => okIfI (const0OnlyL_E e) true 0
  | .st64 _ i e => okIfI (const0OnlyL_E i && const0OnlyL_E e) true 0
  | .st64t _ t i e => okIfI (const0OnlyL_E t && const0OnlyL_E i && const0OnlyL_E e) true 0
  | .st32t _ t i e =>
    okIfI ((match t with | .const w => w == 0 || w.toNat % 2 == 1 | _ => true) &&
       const0OnlyL_E t && const0OnlyL_E i && const0OnlyL_E e) true 0
  | .seq s₁ s₂ =>
    match stmtScanIL rt inLoop s₁ with
    | .fail => .fail
    | .ok mf1 mr1 =>
      match stmtScanIL rt inLoop s₂ with
      | .fail => .fail
      | .ok mf2 mr2 => .ok (mf1 && mf2) (combineMinRet mr1 mr2)
  | .ite c s₁ s₂ =>
    if const0OnlyL_C c then
      match stmtScanIL rt inLoop s₁ with
      | .fail => .fail
      | .ok mf1 mr1 =>
        match stmtScanIL rt inLoop s₂ with
        | .fail => .fail
        | .ok mf2 mr2 => .ok (mf1 || mf2) (combineMinRet mr1 mr2)
    else .fail
  | .while c s =>
    if const0OnlyL_C c then
      match stmtScanIL rt true s with
      | .fail => .fail
      | .ok _ mr => .ok true mr
    else .fail
  | .ret es => okIfI (es.all const0OnlyL_E) false (max 1 es.length)
  | .call xs f args =>
    okIfI ((xs.length.ble 1 || match rt.find (L.Compiler.nameCode f) with | some r => xs.length.ble r | none => false) &&
       args.all const0OnlyL_E) true 0
  | .copy64 d di s si n =>
    okIfI ((match d with | .tier _ t => const0OnlyL_E t | _ => true) && const0OnlyL_E di &&
       (match s with | .tier _ t => const0OnlyL_E t | _ => true) && const0OnlyL_E si && const0OnlyL_E n) true 0
  | .copy8w d di _ si n =>
    okIfI ((match d with | .tier _ t => const0OnlyL_E t | _ => true) && const0OnlyL_E di &&
       const0OnlyL_E si && const0OnlyL_E n) true 0
  | .scan8 _ _ i e _ => okIfI (const0OnlyL_E i && const0OnlyL_E e) true 0

/-! ## 7. Soundness of Single-Pass Scans Against Split Specifications -/

private theorem nat_blt_eq_decide {a b : Nat} : a.blt b = decide (a < b) := by
  by_cases h : a < b
  · have hb : a.blt b = true := by simp only [Nat.blt, Nat.ble_eq]; omega
    simp [hb, h]
  · have hb : a.blt b = false := by
      cases h' : a.blt b with
      | false => rfl
      | true =>
        simp only [Nat.blt, Nat.ble_eq] at h'
        omega
    simp [hb, h]

private theorem nat_ble_eq_decide {a b : Nat} : a.ble b = decide (a ≤ b) := by
  by_cases h : a ≤ b
  · have hb : a.ble b = true := Nat.ble_eq.mpr h
    simp [hb, h]
  · have hb : a.ble b = false := by
      cases h' : a.ble b with
      | false => rfl
      | true => exact False.elim (h (Nat.ble_eq.mp h'))
    simp [hb, h]

private theorem fastDom8Opt_eq (lm : L.Compiler.NTree) (nb : Nat) (a : L.ArrId) :
    fastDom8Opt lm nb a = fastDom8 lm nb a := by
  dsimp only [fastDom8Opt, fastDom8]
  cases lm.find (L.TieredArray.t0 a).code <;> simp [nat_blt_eq_decide]

private theorem fastDom64Opt_eq (lm : L.Compiler.NTree) (nb : Nat) (s : L.TieredArray) :
    fastDom64Opt lm nb s = fastDom64 lm nb s := by
  dsimp only [fastDom64Opt, fastDom64]
  cases lm.find s.code <;> simp [nat_ble_eq_decide]

private theorem fastTier32Opt_eq (lm : L.Compiler.NTree) (nb : Nat) (a : L.ArrId) (e : L.Expr) :
    fastTier32Opt lm nb a e = fastTier32 lm nb a e := by
  cases e with
  | const w =>
    dsimp only [fastTier32Opt, fastTier32]
    by_cases hw0 : w == 0
    · have hw : w = 0 := beq_iff_eq.mp hw0
      subst hw
      have hta : L.tierA a 0 = L.TieredArray.t0 a := rfl
      simp [hta, fastDom64Opt_eq]
    · simp only [hw0, Bool.false_eq_true, Bool.false_or]
      by_cases hodd : w.toNat % 2 == 1
      · have hmod : w.toNat % 2 = 1 := beq_iff_eq.mp hodd
        have hand : (w &&& 1).toNat = 1 := by
          rw [UInt64.toNat_and, show (1 : UInt64).toNat = 1 from rfl, Nat.and_one_is_mod]
          exact hmod
        have hta : L.tierA a w = L.tier1 a := by
          dsimp only [L.tierA, L.tier1]
          have hne : (w &&& 1 != 0) = true := by
            rw [bne_iff_ne]
            intro heq
            have := congrArg UInt64.toNat heq
            simp only [UInt64.toNat_zero] at this
            omega
          simp [hne]
        simp [hodd, hta, fastDom64Opt_eq]
      · simp [hodd]
  | _ => exact fastDom64Opt_eq lm nb (L.tier1 a)

private theorem varsLtL_eq (nl : Nat) : ∀ xs : List L.Var,
    varsLtL nl xs = decide (xs.all (· < nl))
  | [] => rfl
  | x :: xs => by
    have ih := varsLtL_eq nl xs
    dsimp only [varsLtL]
    rw [nat_blt_eq_decide, ih, List.all_cons]
    cases h1 : decide (x < nl) <;> cases h2 : decide (xs.all (· < nl)) <;> simp_all

theorem exprScanL_sound {lm : L.Compiler.NTree} {nb ng nl : Nat} {romOk : List UInt8 → Bool} :
    ∀ {e : L.Expr} {b32 mt b32' : Nat},
      exprScanL lm nb ng nl romOk b32 e = .ok mt b32' →
      exprRomsOk romOk e = true ∧
      fastExpr lm nb ng nl e = true ∧
      mt = (exprTempsAndBoundL e).1 ∧
      b32' = b32 + (exprTempsAndBoundL e).2
  | .const _, b32, mt, b32', h => by
    cases h; exact ⟨rfl, rfl, rfl, rfl⟩
  | .var x, b32, mt, b32', h => by
    dsimp only [exprScanL] at h
    rw [nat_blt_eq_decide] at h
    by_cases hx : decide (x < nl) = true
    · simp only [hx] at h; cases h; exact ⟨rfl, hx, rfl, rfl⟩
    · simp only [hx] at h; cases h
  | .len8 a, b32, mt, b32', h => by
    dsimp only [exprScanL] at h
    rw [fastDom8Opt_eq] at h
    by_cases ha : fastDom8 lm nb a = true
    · simp only [ha] at h; cases h; exact ⟨rfl, ha, rfl, rfl⟩
    · simp only [ha] at h; cases h
  | .len64 a, b32, mt, b32', h => by
    dsimp only [exprScanL] at h
    rw [fastDom64Opt_eq] at h
    by_cases ha : fastDom64 lm nb (L.TieredArray.t0 a) = true
    · simp only [ha] at h; cases h; exact ⟨rfl, ha, rfl, rfl⟩
    · simp only [ha] at h; cases h
  | .glob g, b32, mt, b32', h => by
    dsimp only [exprScanL] at h
    rw [nat_blt_eq_decide] at h
    by_cases hg : decide (g.id < ng) = true
    · simp only [hg] at h; cases h; exact ⟨rfl, hg, rfl, rfl⟩
    · simp only [hg] at h; cases h
  | .bin _ a b, b32, mt, b32', h => by
    dsimp only [exprScanL] at h
    cases ha : exprScanL lm nb ng nl romOk (b32 + 17) a with
    | fail => rw [ha] at h; cases h
    | ok ta b1 =>
      rw [ha] at h; dsimp only at h
      cases hb : exprScanL lm nb ng nl romOk b1 b with
      | fail => rw [hb] at h; cases h
      | ok tb b2 =>
        rw [hb] at h; cases h
        obtain ⟨ra, fa, mta, ba⟩ := exprScanL_sound ha
        obtain ⟨rb, fb, mtb, bb⟩ := exprScanL_sound hb
        simp only [exprRomsOk, fastExpr, exprTempsAndBoundL, Bool.and_eq_true]
        exact ⟨⟨ra, rb⟩, ⟨fa, fb⟩, by rw [mta, mtb], by omega⟩
  | .cmpw _ a b, b32, mt, b32', h => by
    dsimp only [exprScanL] at h
    cases ha : exprScanL lm nb ng nl romOk (b32 + 14) a with
    | fail => rw [ha] at h; cases h
    | ok ta b1 =>
      rw [ha] at h; dsimp only at h
      cases hb : exprScanL lm nb ng nl romOk b1 b with
      | fail => rw [hb] at h; cases h
      | ok tb b2 =>
        rw [hb] at h; cases h
        obtain ⟨ra, fa, mta, ba⟩ := exprScanL_sound ha
        obtain ⟨rb, fb, mtb, bb⟩ := exprScanL_sound hb
        simp only [exprRomsOk, fastExpr, exprTempsAndBoundL, Bool.and_eq_true]
        exact ⟨⟨ra, rb⟩, ⟨fa, fb⟩, by rw [mta, mtb], by omega⟩
  | .ld8 a i, b32, mt, b32', h => by
    dsimp only [exprScanL] at h
    rw [fastDom8Opt_eq] at h
    by_cases ha : fastDom8 lm nb a = true
    · simp only [ha] at h
      obtain ⟨ri, fi, mti, bi⟩ := exprScanL_sound h
      simp only [exprRomsOk, fastExpr, exprTempsAndBoundL, Bool.and_eq_true]
      exact ⟨ri, ⟨ha, fi⟩, mti, by omega⟩
    · simp only [ha] at h; cases h
  | .ld64 a i, b32, mt, b32', h => by
    dsimp only [exprScanL] at h
    rw [fastDom64Opt_eq] at h
    by_cases ha : fastDom64 lm nb (L.TieredArray.t0 a) = true
    · simp only [ha] at h
      obtain ⟨ri, fi, mti, bi⟩ := exprScanL_sound h
      simp only [exprRomsOk, fastExpr, exprTempsAndBoundL, Bool.and_eq_true]
      exact ⟨ri, ⟨ha, fi⟩, mti, by omega⟩
    · simp only [ha] at h; cases h
  | .ldc d i, b32, mt, b32', h => by
    dsimp only [exprScanL] at h
    by_cases hd : romOk d = true
    · simp only [hd] at h
      obtain ⟨ri, fi, mti, bi⟩ := exprScanL_sound h
      simp only [exprRomsOk, fastExpr, exprTempsAndBoundL, Bool.and_eq_true]
      exact ⟨⟨hd, ri⟩, fi, mti, by omega⟩
    · simp only [hd] at h; cases h
  | .ld64t a t i, b32, mt, b32', h => by
    dsimp only [exprScanL] at h
    rw [fastDom64Opt_eq] at h
    by_cases ha : fastDom64 lm nb (L.tier1 a) = true
    · simp only [ha] at h
      cases ht : exprScanL lm nb ng nl romOk (b32 + 35) t with
      | fail => rw [ht] at h; cases h
      | ok tt b1 =>
        rw [ht] at h; dsimp only at h
        cases hi : exprScanL lm nb ng nl romOk b1 i with
        | fail => rw [hi] at h; cases h
        | ok ti b2 =>
          rw [hi] at h; cases h
          obtain ⟨rt', ft, mtt, bt⟩ := exprScanL_sound ht
          obtain ⟨ri, fi, mti, bi⟩ := exprScanL_sound hi
          simp only [exprRomsOk, fastExpr, exprTempsAndBoundL, Bool.and_eq_true]
          exact ⟨⟨rt', ri⟩, ⟨⟨ha, ft⟩, fi⟩, by rw [mtt, mti], by omega⟩
    · simp only [ha] at h; cases h
  | .ld32t a t i, b32, mt, b32', h => by
    dsimp only [exprScanL] at h
    rw [fastTier32Opt_eq] at h
    by_cases ha : fastTier32 lm nb a t = true
    · simp only [ha] at h
      cases ht : exprScanL lm nb ng nl romOk (b32 + 36) t with
      | fail => rw [ht] at h; cases h
      | ok tt b1 =>
        rw [ht] at h; dsimp only at h
        cases hi : exprScanL lm nb ng nl romOk b1 i with
        | fail => rw [hi] at h; cases h
        | ok ti b2 =>
          rw [hi] at h; cases h
          obtain ⟨rt', ft, mtt, bt⟩ := exprScanL_sound ht
          obtain ⟨ri, fi, mti, bi⟩ := exprScanL_sound hi
          simp only [exprRomsOk, fastExpr, exprTempsAndBoundL, Bool.and_eq_true]
          exact ⟨⟨rt', ri⟩, ⟨⟨ha, ft⟩, fi⟩, by rw [mtt, mti], by omega⟩
    · simp only [ha] at h; cases h
  | .ld32h a t i _, b32, mt, b32', h => by
    dsimp only [exprScanL] at h
    rw [fastDom64Opt_eq] at h
    by_cases ha : fastDom64 lm nb (L.tier1 a) = true
    · simp only [ha] at h
      cases ht : exprScanL lm nb ng nl romOk (b32 + 35) t with
      | fail => rw [ht] at h; cases h
      | ok tt b1 =>
        rw [ht] at h; dsimp only at h
        cases hi : exprScanL lm nb ng nl romOk b1 i with
        | fail => rw [hi] at h; cases h
        | ok ti b2 =>
          rw [hi] at h; cases h
          obtain ⟨rt', ft, mtt, bt⟩ := exprScanL_sound ht
          obtain ⟨ri, fi, mti, bi⟩ := exprScanL_sound hi
          simp only [exprRomsOk, fastExpr, exprTempsAndBoundL, Bool.and_eq_true]
          exact ⟨⟨rt', ri⟩, ⟨⟨ha, ft⟩, fi⟩, by rw [mtt, mti], by omega⟩
    · simp only [ha] at h; cases h
  | .len64t a t, b32, mt, b32', h => by
    dsimp only [exprScanL] at h
    rw [fastDom64Opt_eq] at h
    by_cases ha : fastDom64 lm nb (L.tier1 a) = true
    · simp only [ha] at h
      obtain ⟨rt', ft, mtt, bt⟩ := exprScanL_sound h
      simp only [exprRomsOk, fastExpr, exprTempsAndBoundL, Bool.and_eq_true]
      exact ⟨rt', ⟨ha, ft⟩, mtt, by omega⟩
    · simp only [ha] at h; cases h
  | .ld8x8 b i, b32, mt, b32', h => by
    dsimp only [exprScanL] at h
    cases b with
    | arr a =>
      dsimp only at h
      simp only [fastDom8Opt_eq] at h
      by_cases ha : fastDom8 lm nb a = true
      · simp only [ha] at h
        obtain ⟨ri, fi, mti, bi⟩ := exprScanL_sound h
        simp only [exprRomsOk, bsrcRomsOk, fastExpr, exprTempsAndBoundL, Bool.and_eq_true]
        exact ⟨⟨by trivial, ri⟩, ⟨ha, fi⟩, mti, by omega⟩
      · simp only [ha] at h; cases h
    | rom d =>
      dsimp only at h
      by_cases hd : romOk d = true
      · simp only [hd] at h
        obtain ⟨ri, fi, mti, bi⟩ := exprScanL_sound h
        simp only [exprRomsOk, bsrcRomsOk, fastExpr, exprTempsAndBoundL, Bool.and_eq_true]
        exact ⟨⟨hd, ri⟩, fi, mti, by omega⟩
      · simp only [hd] at h; cases h

theorem condScanL_sound {lm : L.Compiler.NTree} {nb ng nl : Nat} {romOk : List UInt8 → Bool} :
    ∀ {c : L.Cond} {b32 mt b32' : Nat},
      condScanL lm nb ng nl romOk b32 c = .ok mt b32' →
      condRomsOk romOk c = true ∧
      fastCond lm nb ng nl c = true ∧
      mt = (condTempsAndBoundL c).1 ∧
      b32' = b32 + (condTempsAndBoundL c).2
  | .cmp _ a b, b32, mt, b32', h => by
    dsimp only [condScanL] at h
    cases ha : exprScanL lm nb ng nl romOk (b32 + 17) a with
    | fail => rw [ha] at h; cases h
    | ok ta b1 =>
      rw [ha] at h; dsimp only at h
      cases hb : exprScanL lm nb ng nl romOk b1 b with
      | fail => rw [hb] at h; cases h
      | ok tb b2 =>
        rw [hb] at h; cases h
        obtain ⟨ra, fa, mta, ba⟩ := exprScanL_sound ha
        obtain ⟨rb, fb, mtb, bb⟩ := exprScanL_sound hb
        simp only [condRomsOk, fastCond, condTempsAndBoundL, Bool.and_eq_true]
        exact ⟨⟨ra, rb⟩, ⟨fa, fb⟩, by rw [mta, mtb], by omega⟩
  | .and p q, b32, mt, b32', h | .or p q, b32, mt, b32', h => by
    dsimp only [condScanL] at h
    cases hp : condScanL lm nb ng nl romOk b32 p with
    | fail => rw [hp] at h; cases h
    | ok tp b1 =>
      rw [hp] at h; dsimp only at h
      cases hq : condScanL lm nb ng nl romOk b1 q with
      | fail => rw [hq] at h; cases h
      | ok tq b2 =>
        rw [hq] at h; cases h
        obtain ⟨rp, fp, mtp, bp⟩ := condScanL_sound hp
        obtain ⟨rq, fq, mtq, bq⟩ := condScanL_sound hq
        simp only [condRomsOk, fastCond, condTempsAndBoundL, Bool.and_eq_true]
        exact ⟨⟨rp, rq⟩, ⟨fp, fq⟩, by rw [mtp, mtq], by omega⟩
  | .not p, b32, mt, b32', h => condScanL_sound (c := p) h

theorem warrScanL_sound {lm : L.Compiler.NTree} {nb ng nl : Nat} {romOk : List UInt8 → Bool} :
    ∀ {w : L.WArr} {b32 mt b32' : Nat},
      warrScanL lm nb ng nl romOk b32 w = .ok mt b32' →
      warrRomsOk romOk w = true ∧
      fastWArr lm nb ng nl w = true ∧
      mt = (warrTempsAndBoundL w).1 ∧
      b32' = b32 + (warrTempsAndBoundL w).2
  | .plain a, b32, mt, b32', h => by
    dsimp only [warrScanL] at h
    rw [fastDom64Opt_eq] at h
    by_cases ha : fastDom64 lm nb (L.TieredArray.t0 a) = true
    · simp only [ha] at h; cases h; exact ⟨rfl, ha, rfl, rfl⟩
    · simp only [ha] at h; cases h
  | .tier a t, b32, mt, b32', h => by
    dsimp only [warrScanL] at h
    rw [fastDom64Opt_eq] at h
    by_cases ha : fastDom64 lm nb (L.tier1 a) = true
    · simp only [ha] at h
      obtain ⟨rt', ft, mtt, bt⟩ := exprScanL_sound h
      simp only [warrRomsOk, fastWArr, warrTempsAndBoundL, Bool.and_eq_true]
      exact ⟨rt', ⟨ha, ft⟩, mtt, by omega⟩
    · simp only [ha] at h; cases h

private theorem exprsTempsAndBoundLGo_shift (es : List L.Expr) :
    ∀ (idx mt b1 b2 : Nat),
      exprsTempsAndBoundLGo idx mt (b1 + b2) es =
        ((exprsTempsAndBoundLGo idx mt b2 es).1, b1 + (exprsTempsAndBoundLGo idx mt b2 es).2) := by
  induction es with
  | nil => intro idx mt b1 b2; rfl
  | cons e es ih =>
    intro idx mt b1 b2
    dsimp only [exprsTempsAndBoundLGo]
    rw [show b1 + b2 + (exprTempsAndBoundL e).2 + 6 = b1 + (b2 + (exprTempsAndBoundL e).2 + 6) by omega]
    exact ih _ _ _ _

theorem exprsScanLGo_sound {lm : L.Compiler.NTree} {nb ng nl : Nat} {romOk : List UInt8 → Bool} :
    ∀ {es : List L.Expr} {idx mt0 b32 mt b32' : Nat},
      exprsScanLGo lm nb ng nl romOk idx mt0 b32 es = .ok mt b32' →
      es.all (exprRomsOk romOk) = true ∧
      es.all (fastExpr lm nb ng nl) = true ∧
      mt = (exprsTempsAndBoundLGo idx mt0 0 es).1 ∧
      b32' = b32 + (exprsTempsAndBoundLGo idx mt0 0 es).2
  | [], idx, mt0, b32, mt, b32', h => by
    cases h; exact ⟨rfl, rfl, rfl, rfl⟩
  | e :: es, idx, mt0, b32, mt, b32', h => by
    dsimp only [exprsScanLGo] at h
    cases he : exprScanL lm nb ng nl romOk (b32 + 6) e with
    | fail => rw [he] at h; cases h
    | ok te b1 =>
      rw [he] at h; dsimp only at h
      obtain ⟨re, fe, mte, be⟩ := exprScanL_sound he
      obtain ⟨res, fes, mtes, bes⟩ := exprsScanLGo_sound h
      have hsh := exprsTempsAndBoundLGo_shift es (idx + 1) (max mt0 (idx + max 1 te)) ((exprTempsAndBoundL e).2 + 6) 0
      dsimp only [exprsTempsAndBoundLGo]
      rw [← mte, show 0 + (exprTempsAndBoundL e).2 + 6 = (exprTempsAndBoundL e).2 + 6 + 0 by omega, hsh]
      simp only [List.all_cons, Bool.and_eq_true]
      exact ⟨⟨re, res⟩, ⟨fe, fes⟩, mtes, by omega⟩

private theorem combineMinRet_spec {mr1 mr2 : Nat} {s₁ s₂ : L.Stmt}
    (h1 : (if mr1 == 0 then none else some mr1) = stmtMinRetRawL s₁)
    (h2 : (if mr2 == 0 then none else some mr2) = stmtMinRetRawL s₂) :
    (if combineMinRet mr1 mr2 == 0 then none else some (combineMinRet mr1 mr2)) =
      match stmtMinRetRawL s₁, stmtMinRetRawL s₂ with
      | none, y => y
      | x, none => x
      | some a, some b => some (min a b) := by
  rw [← h1, ← h2]
  cases mr1 <;> cases mr2 <;> simp [combineMinRet]

theorem stmtScanL_sound {lm : L.Compiler.NTree} {nb ng nres : Nat}
    {tr rt : L.Compiler.NTree} {romOk : List UInt8 → Bool} :
    ∀ {nl : Nat} {inLoop : Bool} {b32 : Nat} {s : L.Stmt}
      {mf : Bool} {mr mt b32' : Nat},
      stmtScanL lm nb ng nres tr rt romOk nl inLoop b32 s = .ok mf mr mt b32' →
      stmtArgsAndRomsOk tr rt romOk s = true ∧
      fastStmt lm nb ng nres tr nl inLoop s = true ∧
      mf = stmtMayFallL s ∧
      (if mr == 0 then none else some mr) = stmtMinRetRawL s ∧
      mt = (stmtTempsAndBoundL s).1 ∧
      b32' = b32 + (stmtTempsAndBoundL s).2
  | _, _, b32, .skip, mf, mr, mt, b32', h => by
    cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | _, inLoop, b32, .brk, mf, mr, mt, b32', h => by
    dsimp only [stmtScanL] at h
    by_cases hi : inLoop = true
    · simp only [hi] at h; cases h; exact ⟨rfl, hi, rfl, rfl, rfl, rfl⟩
    · simp only [hi] at h; cases h
  | nl, _, b32, .set x e, mf, mr, mt, b32', h => by
    dsimp only [stmtScanL] at h
    rw [nat_blt_eq_decide] at h
    by_cases hx : decide (x < nl) = true
    · simp only [hx] at h
      cases he : exprScanL lm nb ng nl romOk (b32 + 6) e with
      | fail => rw [he] at h; cases h
      | ok te b1 =>
        rw [he] at h; cases h
        obtain ⟨re, fe, mte, be⟩ := exprScanL_sound he
        simp only [stmtArgsAndRomsOk, fastStmt, stmtMayFallL, stmtMinRetRawL, stmtTempsAndBoundL, Bool.and_eq_true]
        exact ⟨re, ⟨hx, fe⟩, by trivial, by trivial, mte, by omega⟩
    · simp only [hx] at h; cases h
  | nl, _, b32, .gset g e, mf, mr, mt, b32', h => by
    dsimp only [stmtScanL] at h
    rw [nat_blt_eq_decide] at h
    by_cases hg : decide (g.id < ng) = true
    · simp only [hg] at h
      cases he : exprScanL lm nb ng nl romOk (b32 + 6) e with
      | fail => rw [he] at h; cases h
      | ok te b1 =>
        rw [he] at h; cases h
        obtain ⟨re, fe, mte, be⟩ := exprScanL_sound he
        simp only [stmtArgsAndRomsOk, fastStmt, stmtMayFallL, stmtMinRetRawL, stmtTempsAndBoundL, Bool.and_eq_true]
        exact ⟨re, ⟨hg, fe⟩, by trivial, by trivial, mte, by omega⟩
    · simp only [hg] at h; cases h
  | nl, _, b32, .abort e, mf, mr, mt, b32', h => by
    dsimp only [stmtScanL] at h
    cases he : exprScanL lm nb ng nl romOk (b32 + 4) e with
    | fail => rw [he] at h; cases h
    | ok te b1 =>
      rw [he] at h; cases h
      obtain ⟨re, fe, mte, be⟩ := exprScanL_sound he
      simp only [stmtArgsAndRomsOk, fastStmt, stmtMayFallL, stmtMinRetRawL, stmtTempsAndBoundL]
      exact ⟨re, fe, by trivial, by trivial, mte, by omega⟩
  | _, _, _, .st8 _ _ _, _, _, _, _, h => by cases h
  | nl, _, b32, .st64 a i e, mf, mr, mt, b32', h => by
    dsimp only [stmtScanL] at h
    rw [fastDom64Opt_eq] at h
    by_cases ha : fastDom64 lm nb (L.TieredArray.t0 a) = true
    · simp only [ha] at h
      cases hi : exprScanL lm nb ng nl romOk (b32 + 32) i with
      | fail => rw [hi] at h; cases h
      | ok ti b1 =>
        rw [hi] at h; dsimp only at h
        cases he : exprScanL lm nb ng nl romOk b1 e with
        | fail => rw [he] at h; cases h
        | ok te b2 =>
          rw [he] at h; cases h
          obtain ⟨ri, fi, mti, bi⟩ := exprScanL_sound hi
          obtain ⟨re, fe, mte, be⟩ := exprScanL_sound he
          simp only [stmtArgsAndRomsOk, fastStmt, stmtMayFallL, stmtMinRetRawL, stmtTempsAndBoundL, Bool.and_eq_true]
          exact ⟨⟨ri, re⟩, ⟨⟨ha, fi⟩, fe⟩, by trivial, by trivial, by rw [mti, mte], by omega⟩
    · simp only [ha] at h; cases h
  | nl, _, b32, .st64t a t i e, mf, mr, mt, b32', h => by
    dsimp only [stmtScanL] at h
    rw [fastDom64Opt_eq] at h
    by_cases ha : fastDom64 lm nb (L.tier1 a) = true
    · simp only [ha] at h
      cases ht : exprScanL lm nb ng nl romOk (b32 + 47) t with
      | fail => rw [ht] at h; cases h
      | ok tt b1 =>
        rw [ht] at h; dsimp only at h
        cases hi : exprScanL lm nb ng nl romOk b1 i with
        | fail => rw [hi] at h; cases h
        | ok ti b2 =>
          rw [hi] at h; dsimp only at h
          cases he : exprScanL lm nb ng nl romOk b2 e with
          | fail => rw [he] at h; cases h
          | ok te b3 =>
            rw [he] at h; cases h
            obtain ⟨rt', ft, mtt, bt⟩ := exprScanL_sound ht
            obtain ⟨ri, fi, mti, bi⟩ := exprScanL_sound hi
            obtain ⟨re, fe, mte, be⟩ := exprScanL_sound he
            simp only [stmtArgsAndRomsOk, fastStmt, stmtMayFallL, stmtMinRetRawL, stmtTempsAndBoundL, Bool.and_eq_true]
            exact ⟨⟨⟨rt', ri⟩, re⟩, ⟨⟨⟨ha, ft⟩, fi⟩, fe⟩, by trivial, by trivial, by rw [mtt, mti, mte], by omega⟩
    · simp only [ha] at h; cases h
  | nl, _, b32, .st32t a t i e, mf, mr, mt, b32', h => by
    dsimp only [stmtScanL] at h
    rw [fastTier32Opt_eq] at h
    by_cases ha : fastTier32 lm nb a t = true
    · simp only [ha] at h
      cases ht : exprScanL lm nb ng nl romOk (b32 + 48) t with
      | fail => rw [ht] at h; cases h
      | ok tt b1 =>
        rw [ht] at h; dsimp only at h
        cases hi : exprScanL lm nb ng nl romOk b1 i with
        | fail => rw [hi] at h; cases h
        | ok ti b2 =>
          rw [hi] at h; dsimp only at h
          cases he : exprScanL lm nb ng nl romOk b2 e with
          | fail => rw [he] at h; cases h
          | ok te b3 =>
            rw [he] at h; cases h
            obtain ⟨rt', ft, mtt, bt⟩ := exprScanL_sound ht
            obtain ⟨ri, fi, mti, bi⟩ := exprScanL_sound hi
            obtain ⟨re, fe, mte, be⟩ := exprScanL_sound he
            simp only [stmtArgsAndRomsOk, fastStmt, stmtMayFallL, stmtMinRetRawL, stmtTempsAndBoundL, Bool.and_eq_true]
            exact ⟨⟨⟨rt', ri⟩, re⟩, ⟨⟨⟨ha, ft⟩, fi⟩, fe⟩, by trivial, by trivial, by rw [mtt, mti, mte], by omega⟩
    · simp only [ha] at h; cases h
  | nl, inLoop, b32, .seq s₁ s₂, mf, mr, mt, b32', h => by
    dsimp only [stmtScanL] at h
    cases h1 : stmtScanL lm nb ng nres tr rt romOk nl inLoop b32 s₁ with
    | fail => rw [h1] at h; cases h
    | ok mf1 mr1 t1 b1 =>
      rw [h1] at h; dsimp only at h
      cases h2 : stmtScanL lm nb ng nres tr rt romOk nl inLoop b1 s₂ with
      | fail => rw [h2] at h; cases h
      | ok mf2 mr2 t2 b2 =>
        rw [h2] at h; cases h
        obtain ⟨a1, f1, m1, r1, mt1, bs1⟩ := stmtScanL_sound h1
        obtain ⟨a2, f2, m2, r2, mt2, bs2⟩ := stmtScanL_sound h2
        simp only [stmtArgsAndRomsOk, fastStmt, stmtMayFallL, stmtMinRetRawL, stmtTempsAndBoundL, Bool.and_eq_true]
        refine ⟨⟨a1, a2⟩, ⟨f1, f2⟩, ?_, combineMinRet_spec r1 r2, by rw [mt1, mt2], by omega⟩
        subst m1 m2; cases stmtMayFallL s₁ <;> rfl
  | nl, inLoop, b32, .ite c s₁ s₂, mf, mr, mt, b32', h => by
    dsimp only [stmtScanL] at h
    cases hc : condScanL lm nb ng nl romOk (b32 + 4) c with
    | fail => rw [hc] at h; cases h
    | ok tc b1 =>
      rw [hc] at h; dsimp only at h
      cases h1 : stmtScanL lm nb ng nres tr rt romOk nl inLoop b1 s₁ with
      | fail => rw [h1] at h; cases h
      | ok mf1 mr1 t1 b2 =>
        rw [h1] at h; dsimp only at h
        cases h2 : stmtScanL lm nb ng nres tr rt romOk nl inLoop b2 s₂ with
        | fail => rw [h2] at h; cases h
        | ok mf2 mr2 t2 b3 =>
          rw [h2] at h; cases h
          obtain ⟨rc, fc, mtc, bc⟩ := condScanL_sound hc
          obtain ⟨a1, f1, m1, r1, mt1, bs1⟩ := stmtScanL_sound h1
          obtain ⟨a2, f2, m2, r2, mt2, bs2⟩ := stmtScanL_sound h2
          simp only [stmtArgsAndRomsOk, fastStmt, stmtMayFallL, stmtMinRetRawL, stmtTempsAndBoundL, Bool.and_eq_true]
          refine ⟨⟨⟨rc, a1⟩, a2⟩, ⟨⟨fc, f1⟩, f2⟩, ?_, combineMinRet_spec r1 r2, by rw [mtc, mt1, mt2], by omega⟩
          subst m1 m2; rfl
  | nl, _, b32, .while c s, mf, mr, mt, b32', h => by
    dsimp only [stmtScanL] at h
    cases hc : condScanL lm nb ng nl romOk (b32 + 10) c with
    | fail => rw [hc] at h; cases h
    | ok tc b1 =>
      rw [hc] at h; dsimp only at h
      cases hs : stmtScanL lm nb ng nres tr rt romOk nl true b1 s with
      | fail => rw [hs] at h; cases h
      | ok _ mrs ts b2 =>
        rw [hs] at h; cases h
        obtain ⟨rc, fc, mtc, bc⟩ := condScanL_sound hc
        obtain ⟨as, fs, _, rs, mts, bs⟩ := stmtScanL_sound hs
        simp only [stmtArgsAndRomsOk, fastStmt, stmtMayFallL, stmtMinRetRawL, stmtTempsAndBoundL, Bool.and_eq_true]
        exact ⟨⟨rc, as⟩, ⟨fc, fs⟩, by trivial, rs, by rw [mtc, mts], by omega⟩
  | nl, _, b32, .ret es, mf, mr, mt, b32', h => by
    dsimp only [stmtScanL] at h
    rw [nat_ble_eq_decide] at h
    by_cases hlen : decide (es.length ≤ nres) = true
    · simp only [hlen] at h
      cases hes : exprsScanLGo lm nb ng nl romOk 0 0 (b32 + 124) es with
      | fail => rw [hes] at h; cases h
      | ok te b1 =>
        rw [hes] at h; cases h
        obtain ⟨res, fes, mtes, bes⟩ := exprsScanLGo_sound hes
        have hne : (max 1 es.length == 0) = false := beq_false_of_ne (by omega)
        simp only [stmtArgsAndRomsOk, fastStmt, stmtMayFallL, stmtMinRetRawL, stmtTempsAndBoundL,
          exprsTempsAndBoundL, Bool.and_eq_true]
        exact ⟨res, ⟨hlen, fes⟩, by trivial, by simp [hne], mtes, by omega⟩
    · simp only [hlen] at h; cases h
  | nl, _, b32, .call xs f args, mf, mr, mt, b32', h => by
    dsimp only [stmtScanL] at h
    cases htr : tr.find (L.Compiler.nameCode f) with
    | none => simp [htr] at h
    | some n =>
      simp only [htr] at h
      by_cases hc : (args.length == n && varsLtL nl xs &&
          (xs.length.ble 1 || match rt.find (L.Compiler.nameCode f) with | some r => xs.length.ble r | none => false)) = true
      · simp only [hc] at h
        cases hargs : exprsScanLGo lm nb ng nl romOk 0 0 (b32 + 16 + 6 * min args.length maxResL + 12 * xs.length) args with
        | fail => rw [hargs] at h; cases h
        | ok ta b1 =>
          rw [hargs] at h; cases h
          obtain ⟨rargs, fargs, mta, ba⟩ := exprsScanLGo_sound hargs
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, varsLtL_eq, nat_ble_eq_decide] at hc
          rcases hc with ⟨⟨harglen, hxs⟩, hret⟩
          simp only [stmtArgsAndRomsOk, fastStmt, stmtMayFallL, stmtMinRetRawL, stmtTempsAndBoundL,
            exprsTempsAndBoundL, htr, Option.isSome_some, Bool.and_eq_true, Bool.true_and,
            decide_eq_true_eq]
          refine ⟨⟨⟨harglen, ?_⟩, rargs⟩, ⟨hxs, fargs⟩, by trivial, by trivial, mta, by omega⟩
          by_cases h1 : xs.length ≤ 1
          · simp [h1]
          · simp only [h1]
            simp only [decide_eq_true_eq, h1, false_or] at hret
            exact hret
      · simp only [hc] at h; cases h
  | nl, _, b32, .copy64 d di s si n, mf, mr, mt, b32', h => by
    dsimp only [stmtScanL] at h
    cases hd : warrScanL lm nb ng nl romOk (b32 + 120) d with
    | fail => rw [hd] at h; cases h
    | ok td b1 =>
      rw [hd] at h; dsimp only at h
      cases hdi : exprScanL lm nb ng nl romOk b1 di with
      | fail => rw [hdi] at h; cases h
      | ok tdi b2 =>
        rw [hdi] at h; dsimp only at h
        cases hs : warrScanL lm nb ng nl romOk b2 s with
        | fail => rw [hs] at h; cases h
        | ok ts b3 =>
          rw [hs] at h; dsimp only at h
          cases hsi : exprScanL lm nb ng nl romOk b3 si with
          | fail => rw [hsi] at h; cases h
          | ok tsi b4 =>
            rw [hsi] at h; dsimp only at h
            cases hn : exprScanL lm nb ng nl romOk b4 n with
            | fail => rw [hn] at h; cases h
            | ok tn b5 =>
              rw [hn] at h; cases h
              obtain ⟨rd, fd, mtd, bd⟩ := warrScanL_sound hd
              obtain ⟨rdi, fdi, mtdi, bdi⟩ := exprScanL_sound hdi
              obtain ⟨rs, fs, mts, bs⟩ := warrScanL_sound hs
              obtain ⟨rsi, fsi, mtsi, bsi⟩ := exprScanL_sound hsi
              obtain ⟨rn, fn, mtn, bn⟩ := exprScanL_sound hn
              simp only [stmtArgsAndRomsOk, fastStmt, stmtMayFallL, stmtMinRetRawL, stmtTempsAndBoundL, Bool.and_eq_true]
              exact ⟨⟨⟨⟨⟨rd, rdi⟩, rs⟩, rsi⟩, rn⟩, ⟨⟨⟨⟨fd, fdi⟩, fs⟩, fsi⟩, fn⟩, by trivial, by trivial, by rw [mtd, mtdi, mts, mtsi, mtn], by omega⟩
  | nl, _, b32, .copy8w d di s si n, mf, mr, mt, b32', h => by
    dsimp only [stmtScanL] at h
    cases hsok : (match s with | .arr a => fastDom8Opt lm nb a | .rom d => romOk d) with
    | false => simp [hsok] at h
    | true =>
      simp only [hsok] at h
      cases hd : warrScanL lm nb ng nl romOk (b32 + 115) d with
      | fail => rw [hd] at h; cases h
      | ok td b1 =>
        rw [hd] at h; dsimp only at h
        cases hdi : exprScanL lm nb ng nl romOk b1 di with
        | fail => rw [hdi] at h; cases h
        | ok tdi b2 =>
          rw [hdi] at h; dsimp only at h
          cases hsi : exprScanL lm nb ng nl romOk b2 si with
          | fail => rw [hsi] at h; cases h
          | ok tsi b3 =>
            rw [hsi] at h; dsimp only at h
            cases hn : exprScanL lm nb ng nl romOk b3 n with
            | fail => rw [hn] at h; cases h
            | ok tn b4 =>
              rw [hn] at h; cases h
              obtain ⟨rd, fd, mtd, bd⟩ := warrScanL_sound hd
              obtain ⟨rdi, fdi, mtdi, bdi⟩ := exprScanL_sound hdi
              obtain ⟨rsi, fsi, mtsi, bsi⟩ := exprScanL_sound hsi
              obtain ⟨rn, fn, mtn, bn⟩ := exprScanL_sound hn
              have hsr : bsrcRomsOk romOk s = true := by
                cases s with
                | arr _ => rfl
                | rom _ => exact hsok
              have hsf : fastBSrc lm nb s = true := by
                cases s with
                | arr a => dsimp only at hsok; rw [fastDom8Opt_eq] at hsok; exact hsok
                | rom _ => rfl
              simp only [stmtArgsAndRomsOk, fastStmt, stmtMayFallL, stmtMinRetRawL, stmtTempsAndBoundL, Bool.and_eq_true]
              exact ⟨⟨⟨⟨⟨rd, rdi⟩, hsr⟩, rsi⟩, rn⟩, ⟨⟨⟨⟨fd, fdi⟩, hsf⟩, fsi⟩, fn⟩, by trivial, by trivial, by rw [mtd, mtdi, mtsi, mtn], by omega⟩
  | nl, _, b32, .scan8 x s i e c, mf, mr, mt, b32', h => by
    dsimp only [stmtScanL] at h
    cases s with
    | arr a =>
      dsimp only at h
      cases hc : (x.blt nl && fastDom8Opt lm nb a && Nat.ble 256 c.length && romOk c) with
      | false => simp only [hc, Bool.false_eq_true] at h; cases h
      | true =>
        simp only [hc] at h
        cases hi : exprScanL lm nb ng nl romOk (b32 + 70) i with
        | fail => rw [hi] at h; cases h
        | ok ti b1 =>
          rw [hi] at h; dsimp only at h
          cases he : exprScanL lm nb ng nl romOk b1 e with
          | fail => rw [he] at h; cases h
          | ok te b2 =>
            rw [he] at h; cases h
            obtain ⟨ri, fi, mti, bi⟩ := exprScanL_sound hi
            obtain ⟨re, fe, mte, be⟩ := exprScanL_sound he
            simp only [Bool.and_eq_true, nat_blt_eq_decide, nat_ble_eq_decide, fastDom8Opt_eq] at hc
            rcases hc with ⟨⟨⟨hx, ha⟩, hclen⟩, hromc⟩
            simp only [stmtArgsAndRomsOk, bsrcRomsOk, fastStmt, fastBSrc, stmtMayFallL,
              stmtMinRetRawL, stmtTempsAndBoundL, Bool.and_eq_true]
            exact ⟨⟨⟨⟨by trivial, ri⟩, re⟩, hromc⟩, ⟨⟨⟨⟨hx, ha⟩, fi⟩, fe⟩, hclen⟩, by trivial, by trivial, by rw [mti, mte], by omega⟩
    | rom d =>
      dsimp only at h
      cases hc : (x.blt nl && romOk d && Nat.ble 256 c.length && romOk c) with
      | false => simp only [hc, Bool.false_eq_true] at h; cases h
      | true =>
        simp only [hc] at h
        cases hi : exprScanL lm nb ng nl romOk (b32 + 70) i with
        | fail => rw [hi] at h; cases h
        | ok ti b1 =>
          rw [hi] at h; dsimp only at h
          cases he : exprScanL lm nb ng nl romOk b1 e with
          | fail => rw [he] at h; cases h
          | ok te b2 =>
            rw [he] at h; cases h
            obtain ⟨ri, fi, mti, bi⟩ := exprScanL_sound hi
            obtain ⟨re, fe, mte, be⟩ := exprScanL_sound he
            simp only [Bool.and_eq_true, nat_blt_eq_decide, nat_ble_eq_decide] at hc
            rcases hc with ⟨⟨⟨hx, hd⟩, hclen⟩, hromc⟩
            simp only [stmtArgsAndRomsOk, bsrcRomsOk, fastStmt, fastBSrc, stmtMayFallL,
              stmtMinRetRawL, stmtTempsAndBoundL, Bool.and_eq_true]
            exact ⟨⟨⟨⟨hd, ri⟩, re⟩, hromc⟩, ⟨⟨⟨⟨hx, by trivial⟩, fi⟩, fe⟩, hclen⟩, by trivial, by trivial, by rw [mti, mte], by omega⟩

private theorem okIfI_eq_ok {b mf mf' : Bool} {mr mr' : Nat}
    (h : okIfI b mf mr = .ok mf' mr') : b = true ∧ mf' = mf ∧ mr' = mr := by
  cases b with
  | false => cases h
  | true => cases h; exact ⟨rfl, rfl, rfl⟩

theorem stmtScanIL_sound {rt : L.Compiler.NTree} :
    ∀ {inLoop : Bool} {s : L.Stmt} {mf : Bool} {mr : Nat},
      stmtScanIL rt inLoop s = .ok mf mr →
      stmtRetOkNTree rt s = true ∧
      brkOkL inLoop s = true ∧
      const0OnlyL_S s = true ∧
      noSt8L s = true ∧
      mf = stmtMayFallL s ∧
      (if mr == 0 then none else some mr) = stmtMinRetRawL s
  | _, .skip, mf, mr, h => by cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | inLoop, .brk, mf, mr, h => by
    obtain ⟨hi, rfl, rfl⟩ := okIfI_eq_ok h
    exact ⟨rfl, hi, rfl, rfl, rfl, rfl⟩
  | _, .st8 _ _ _, _, _, h => by cases h
  | _, .abort e, mf, mr, h => by
    obtain ⟨hc, rfl, rfl⟩ := okIfI_eq_ok h
    exact ⟨rfl, rfl, hc, rfl, rfl, rfl⟩
  | _, .set _ e, mf, mr, h | _, .gset _ e, mf, mr, h => by
    obtain ⟨hc, rfl, rfl⟩ := okIfI_eq_ok h
    exact ⟨rfl, rfl, hc, rfl, rfl, rfl⟩
  | _, .st64 _ i e, mf, mr, h => by
    obtain ⟨hc, rfl, rfl⟩ := okIfI_eq_ok h
    exact ⟨rfl, rfl, hc, rfl, rfl, rfl⟩
  | _, .st64t _ t i e, mf, mr, h => by
    obtain ⟨hc, rfl, rfl⟩ := okIfI_eq_ok h
    exact ⟨rfl, rfl, hc, rfl, rfl, rfl⟩
  | _, .st32t _ t i e, mf, mr, h => by
    obtain ⟨hc, rfl, rfl⟩ := okIfI_eq_ok h
    exact ⟨rfl, rfl, hc, rfl, rfl, rfl⟩
  | inLoop, .seq s₁ s₂, mf, mr, h => by
    dsimp only [stmtScanIL] at h
    cases h1 : stmtScanIL rt inLoop s₁ with
    | fail => rw [h1] at h; cases h
    | ok mf1 mr1 =>
      rw [h1] at h; dsimp only at h
      cases h2 : stmtScanIL rt inLoop s₂ with
      | fail => rw [h2] at h; cases h
      | ok mf2 mr2 =>
        rw [h2] at h; cases h
        obtain ⟨r1, b1, c1, n1, m1, mr1eq⟩ := stmtScanIL_sound h1
        obtain ⟨r2, b2, c2, n2, m2, mr2eq⟩ := stmtScanIL_sound h2
        simp only [stmtRetOkNTree, brkOkL, const0OnlyL_S, noSt8L, stmtMayFallL, stmtMinRetRawL, Bool.and_eq_true]
        refine ⟨⟨r1, r2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨n1, n2⟩, ?_, combineMinRet_spec mr1eq mr2eq⟩
        subst m1 m2; cases stmtMayFallL s₁ <;> rfl
  | inLoop, .ite c s₁ s₂, mf, mr, h => by
    dsimp only [stmtScanIL] at h
    cases hc : const0OnlyL_C c with
    | false => simp only [hc, Bool.false_eq_true] at h; cases h
    | true =>
      simp only [hc] at h
      cases h1 : stmtScanIL rt inLoop s₁ with
      | fail => rw [h1] at h; cases h
      | ok mf1 mr1 =>
        rw [h1] at h; dsimp only at h
        cases h2 : stmtScanIL rt inLoop s₂ with
        | fail => rw [h2] at h; cases h
        | ok mf2 mr2 =>
          rw [h2] at h; cases h
          obtain ⟨r1, b1, c1, n1, m1, mr1eq⟩ := stmtScanIL_sound h1
          obtain ⟨r2, b2, c2, n2, m2, mr2eq⟩ := stmtScanIL_sound h2
          simp only [stmtRetOkNTree, brkOkL, const0OnlyL_S, noSt8L, stmtMayFallL, stmtMinRetRawL, Bool.and_eq_true]
          refine ⟨⟨r1, r2⟩, ⟨b1, b2⟩, ⟨⟨hc, c1⟩, c2⟩, ⟨n1, n2⟩, ?_, combineMinRet_spec mr1eq mr2eq⟩
          subst m1 m2; rfl
  | _, .while c s, mf, mr, h => by
    dsimp only [stmtScanIL] at h
    cases hc : const0OnlyL_C c with
    | false => simp only [hc, Bool.false_eq_true] at h; cases h
    | true =>
      simp only [hc] at h
      cases hs : stmtScanIL rt true s with
      | fail => rw [hs] at h; cases h
      | ok _ mrs =>
        rw [hs] at h; cases h
        obtain ⟨rs, bs, cs, ns, _, mrseq⟩ := stmtScanIL_sound hs
        simp only [stmtRetOkNTree, brkOkL, const0OnlyL_S, noSt8L, stmtMayFallL, stmtMinRetRawL, Bool.and_eq_true]
        exact ⟨rs, bs, ⟨hc, cs⟩, ns, by trivial, mrseq⟩
  | _, .ret es, mf, mr, h => by
    obtain ⟨hc, rfl, rfl⟩ := okIfI_eq_ok h
    have hne : (max 1 es.length == 0) = false := beq_false_of_ne (by omega)
    exact ⟨rfl, rfl, hc, rfl, rfl, by simp [stmtMinRetRawL, hne]⟩
  | _, .call xs f args, mf, mr, h => by
    obtain ⟨hc, rfl, rfl⟩ := okIfI_eq_ok h
    simp only [Bool.and_eq_true, Bool.or_eq_true, nat_ble_eq_decide, decide_eq_true_eq] at hc
    refine ⟨?_, rfl, hc.2, rfl, rfl, rfl⟩
    dsimp only [stmtRetOkNTree]
    by_cases h1 : xs.length ≤ 1
    · simp [h1]
    · simp only [h1]
      rcases hc.1 with hle | hm
      · exact False.elim (h1 hle)
      · exact hm
  | _, .copy64 _ _ _ _ _, mf, mr, h | _, .copy8w _ _ _ _ _, mf, mr, h | _, .scan8 _ _ _ _ _, mf, mr, h => by
    obtain ⟨hc, rfl, rfl⟩ := okIfI_eq_ok h
    exact ⟨rfl, rfl, hc, rfl, rfl, rfl⟩

/-! ## 8. Fused Single-Pass Slice & Function Checkers -/

def fnScanBound (fd : L.FunDecl) (mt b32 : Nat) : Nat :=
  let nl := max fd.nlocals fd.nparams
  if (nl + mt).blt 100000 then
    59 + 12 * fd.nparams + 6 * (nl - fd.nparams) + b32
  else
    5000000

noncomputable def fnFusedOk (x : L.FnName × L.FunDecl) : Bool :=
  decide ((minRetTreeLit.find (L.Compiler.nameCode x.1)).getD 1 ≤ fnMinRetL x.2) &&
  stmtArgsAndRomsOk L.Checker.checkerProg_wf.tree minRetTreeLit allowedRomsLit.elem x.2.body &&
  fastStmt checkerLmapLit 2 12 10 L.Checker.checkerProg_wf.tree x.2.nlocals false x.2.body &&
  fnCharsSafeFastL x.1.toList

noncomputable def sliceFusedGo (xs : List (L.FnName × L.FunDecl)) (acc sumCap : Nat) : Bool :=
  match xs with
  | [] => acc.blt sumCap
  | x :: rest =>
    if fnCharsSafeFastL x.1.toList then
      match stmtScanL checkerLmapLit 2 12 10 L.Checker.checkerProg_wf.tree minRetTreeLit
          (romFastOk allowedRomsWithLenLit) x.2.nlocals false 0 x.2.body with
      | .fail => false
      | .ok mf mr mt b32 =>
        let minRet := if mf then 1 else if mr == 0 then 100 else mr
        if ((minRetTreeLit.find (L.Compiler.nameCode x.1)).getD 1).ble minRet then
          sliceFusedGo rest (acc + fnScanBound x.2 mt b32) sumCap
        else false
    else false

noncomputable def sliceFusedOk (lo k sumCap : Nat) (p : L.Prog) : Bool :=
  sliceFusedGo ((p.drop lo).take k) 0 sumCap

noncomputable def fnFusedIOk (x : L.FnName × L.FunDecl) : Bool :=
  decide ((minRetTreeILit.find (L.Compiler.nameCode x.1)).getD 1 ≤ fnMinRetL x.2) &&
  stmtRetOkNTree minRetTreeILit x.2.body &&
  brkOkL false x.2.body &&
  const0OnlyL_S x.2.body &&
  noSt8L x.2.body

noncomputable def sliceFusedIGo : List (L.FnName × L.FunDecl) → Bool
  | [] => true
  | x :: rest =>
    match stmtScanIL minRetTreeILit false x.2.body with
    | .fail => false
    | .ok mf mr =>
      let minRet := if mf then 1 else if mr == 0 then 100 else mr
      if ((minRetTreeILit.find (L.Compiler.nameCode x.1)).getD 1).ble minRet then
        sliceFusedIGo rest
      else false

noncomputable def sliceFusedIOk (lo k : Nat) (p : L.Prog) : Bool :=
  sliceFusedIGo ((p.drop lo).take k)

end ConAgua.RISCV.Bridge
