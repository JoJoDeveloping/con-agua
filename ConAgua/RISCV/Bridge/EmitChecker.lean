import ConAgua.RISCV.Compiler.Compile
import ConAgua.RISCV.Linker.HybridLink
import ConAgua.RISCV.Bridge.CheckerDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RV64 Assembly Emitter for `checkerProg` (`ConAgua.RISCV.Bridge.EmitChecker`)

Emits a single unified `linkHybrid`-linked RV64 image (`checkerChipAsm`) containing:
- `checkerDriverAsm` (`ca_start` at PC = 0): 2-phase sequential driver
  (`MODE=3` → `MODE=2, PLO=0, PHI=cnt, CTLF.size=0`), shared exit stubs, and the single
  shared leaf initialization subroutine `ca_drv_init` (with re-rolled descriptor/global
  init loops and instruction-based `romStores` for the Harvard `RV64.Rom` model),
- `checkerCmpDriverAsm` (`ca_start_c` right after `checkerDriverAsm`): sequential comparator
  driver (`MODE=4 → 5 → 6 → 8 → 9`), calling `ca_drv_init` and jumping into `checkerDriverAsm`'s
  shared exit stubs,
- `orderProgFns checkerProgMini`: all compiled checker functions emitted once.

Both entry points follow the LP64 caller-save/restore function-return ABI
`(a0 = verdict/code, a1 = status)` where `0 = ok`, `1 = exhausted/decline`, `2 = abort/error`.
-/

namespace ConAgua.RISCV.Bridge

open ConAgua.RISCV.RV64
open ConAgua.RISCV.Compiler
open ConAgua.RISCV.Linker

def cmpStartLabel : String := "ca_start_c"
def drvDoneLabel : String := "ca_drv_done"
def drvInitLabel : String := "ca_drv_init"

/-- Loop filling `count` consecutive 64-bit words at `gp + off` with constant `val`.
    Clobbers `t0, t1, t2, t4`; preserves `gp, ra, sp, a0..a7, s0..s11, t3, t5`. -/
def drvFillConstLoop (loopLbl doneLbl : String) (off : Int) (val : BitVec 64)
    (count : Nat) : List AsmItem :=
  if count == 0 then []
  else
    addImmOff AbiReg.t0 AbiReg.gp AbiReg.t4 off ++
    li AbiReg.t1 val ++
    li AbiReg.t2 (BitVec.ofNat 64 count) ++
    [Asm.lbl loopLbl,
     Asm.beq AbiReg.t2 AbiReg.zero doneLbl,
     Asm.sd AbiReg.t0 AbiReg.t1,
     Asm.addi AbiReg.t0 AbiReg.t0 8#12,
     Asm.addi AbiReg.t2 AbiReg.t2 (-1#12),
     Asm.j loopLbl,
     Asm.lbl doneLbl]

/-- Loop filling `count` consecutive 64-bit words at `gp + off` with
    `gp + initOff + k * stride` (`k = 0 .. count - 1`).
    Clobbers `t0, t1, t2, t3, t4`; preserves `gp, ra, sp, a0..a7, s0..s11, t5`. -/
def drvFillStrideLoop (loopLbl doneLbl : String) (off : Int) (initOff stride : BitVec 64)
    (count : Nat) : List AsmItem :=
  if count == 0 then []
  else
    addImmOff AbiReg.t0 AbiReg.gp AbiReg.t4 off ++
    li AbiReg.t1 initOff ++
    [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1] ++
    li AbiReg.t3 stride ++
    li AbiReg.t2 (BitVec.ofNat 64 count) ++
    [Asm.lbl loopLbl,
     Asm.beq AbiReg.t2 AbiReg.zero doneLbl,
     Asm.sd AbiReg.t0 AbiReg.t1,
     Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3,
     Asm.addi AbiReg.t0 AbiReg.t0 8#12,
     Asm.addi AbiReg.t2 AbiReg.t2 (-1#12),
     Asm.j loopLbl,
     Asm.lbl doneLbl]

/-- Pack up to 4 little-endian bytes (zero-padded) into a 32-bit word. -/
def romWord32 (b0 b1 b2 b3 : UInt8) : BitVec 32 :=
  b0.toBitVec.zeroExtend 32 |||
  (b1.toBitVec.zeroExtend 32 <<< 8) |||
  (b2.toBitVec.zeroExtend 32 <<< 16) |||
  (b3.toBitVec.zeroExtend 32 <<< 24)

/-- Partition a byte list into zero-padded little-endian 32-bit words. -/
def romWords32 : List UInt8 → List (BitVec 32)
  | [] => []
  | [b0] => [romWord32 b0 0 0 0]
  | [b0, b1] => [romWord32 b0 b1 0 0]
  | [b0, b1, b2] => [romWord32 b0 b1 b2 0]
  | b0 :: b1 :: b2 :: b3 :: rest => romWord32 b0 b1 b2 b3 :: romWords32 rest

/-- Partition a list into chunks of at most 1,024 elements (4 KB of 32-bit words). -/
def romChunks1024 {α : Type} : List α → List (List α)
  | [] => []
  | x :: xs =>
    let ys := x :: xs
    ys.take 1024 :: romChunks1024 (ys.drop 1024)
termination_by xs => xs.length
decreasing_by simp [List.length_drop]; omega

/-- Insert `(slot, v)` into an association list mapping 32-bit values to slot indices. -/
def romInsertGroup (slot : Nat) (v : BitVec 32) :
    List (BitVec 32 × List Nat) → List (BitVec 32 × List Nat)
  | [] => [(v, [slot])]
  | (k, ss) :: rest =>
    if k == v then (k, slot :: ss) :: rest
    else (k, ss) :: romInsertGroup slot v rest

/-- Group a chunk's 32-bit words by value, tracking each word's slot index (`0 .. ws.length - 1`). -/
def romGroupChunkGo (slot : Nat) : List (BitVec 32) → List (BitVec 32 × List Nat)
  | [] => []
  | w :: rest => romInsertGroup slot w (romGroupChunkGo (slot + 1) rest)

def romGroupChunk (ws : List (BitVec 32)) : List (BitVec 32 × List Nat) :=
  romGroupChunkGo 0 ws

/-- Emit instructions for one value group `(v, slots)` relative to base register `t0`
    (which holds `gp + romBase + 4096 * chunkIdx + 2048`).
    Zero words emit explicit `sw zero, off(t0)`; non-zero words materialize `v` once into `t1`
    via `li32Instrs` (`addi`, `lui`, or `lui + addi`) and emit `sw t1, off(t0)` for every slot. -/
def drvRomGroupAsm (g : BitVec 32 × List Nat) : List AsmItem :=
  let (v, slots) := g
  if v == 0#32 then
    slots.map fun (s : Nat) =>
      Asm.sw AbiReg.t0 AbiReg.zero (BitVec.ofInt 12 (4 * Int.ofNat s - 2048))
  else
    (li32Instrs AbiReg.t1 v).map .instr ++
    slots.map fun (s : Nat) =>
      Asm.sw AbiReg.t0 AbiReg.t1 (BitVec.ofInt 12 (4 * Int.ofNat s - 2048))

/-- Emit instructions for one 4 KB chunk (`≤ 1024` 32-bit words) at `romBase + 4096 * chunkIdx`.
    Sets `t0 := gp + romBase + 4096 * chunkIdx + 2048` once via `addImmOff` (scratch `t1`),
    then emits each value group. Clobbers only `t0` and `t1`. -/
def drvRomChunkAsm (romBase : Int) (chunkIdx : Nat) (ws : List (BitVec 32)) : List AsmItem :=
  addImmOff AbiReg.t0 AbiReg.gp AbiReg.t1 (romBase + 4096 * Int.ofNat chunkIdx + 2048) ++
  (romGroupChunk ws).flatMap drvRomGroupAsm

/-- Emit chunked, value-grouped 32-bit `sw` instructions initializing `bs` at `gp + romBase`.
    Clobbers only `t0` and `t1`; Harvard instruction-only (no `LD` from ROM). -/
def drvRomStoresAsm (romBase : Int) (bs : List UInt8) : List AsmItem :=
  ((romChunks1024 (romWords32 bs)).zipIdx).flatMap fun (ws, ci) =>
    drvRomChunkAsm romBase ci ws

/-- Shared leaf initialization subroutine `ca_drv_init`, called by both `ca_start` and
    `ca_start_c` after saving caller registers and setting `gp := a4`.
    Uses re-rolled RV64 loops for descriptor bases, lengths, len32s, and result/global zeroing;
    uses chunked, value-grouped 32-bit `sw` stores (`drvRomStoresAsm`) because `RV64.Rom` is
    Harvard instruction-fetch-only memory (no `LD` from ROM). -/
def drvInitSubAsm (tab : Tab := checkerTabMini) : List AsmItem :=
  let resetStack : List AsmItem :=
    li AbiReg.t1 (BitVec.ofNat 64 (abiSlot + abiStack)) ++
    [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1, Asm.sd AbiReg.gp AbiReg.t1] ++
    li AbiReg.t1 (BitVec.ofNat 64 abiSlot) ++
    [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1, Asm.sd AbiReg.gp AbiReg.t1 8#12]
  let bufBaseStores : List AsmItem := (List.range tab.nbuf).flatMap fun p =>
    let srcReg := if p == 0 then AbiReg.a0 else AbiReg.a2
    storeMemOff .sd AbiReg.gp srcReg AbiReg.t0 (tab.dbase p)
  let baseStores : List AsmItem :=
    bufBaseStores ++
    drvFillStrideLoop "ca_drv_bloop" "ca_drv_bdone" (tab.dbase tab.nbuf)
      (BitVec.ofNat 64 (2 * abiSlot)) (BitVec.ofNat 64 abiSlot) (tab.nb + tab.nw - tab.nbuf)
  let bufLenStores : List AsmItem := (List.range tab.nbuf).flatMap fun p =>
    let srcReg := if p == 0 then AbiReg.a1 else AbiReg.a3
    storeMemOff .sd AbiReg.gp srcReg AbiReg.t0 (tab.dlen p)
  let lenStores : List AsmItem :=
    bufLenStores ++
    drvFillConstLoop "ca_drv_lbloop" "ca_drv_lbdone" (tab.dlen tab.nbuf)
      (BitVec.ofNat 64 abiSlot) (tab.nb - tab.nbuf) ++
    drvFillConstLoop "ca_drv_lwloop" "ca_drv_lwdone" (tab.dlen tab.nb)
      (BitVec.ofNat 64 abiWords) tab.nw
  let len32Stores : List AsmItem :=
    drvFillConstLoop "ca_drv_l32bloop" "ca_drv_l32bdone" (tab.dlen32 0)
      0#64 tab.nb ++
    drvFillConstLoop "ca_drv_l32wloop" "ca_drv_l32wdone" (tab.dlen32 tab.nb)
      (BitVec.ofNat 64 (2 * abiWords)) tab.nw
  let romStores : List AsmItem := drvRomStoresAsm tab.romBase tab.rom
  let zeroResGlobs : List AsmItem :=
    drvFillConstLoop "ca_drv_zloop" "ca_drv_zdone" tab.resBase 0#64 (tab.nxres + tab.ng)
  [Asm.lbl drvInitLabel] ++
  resetStack ++
  baseStores ++
  lenStores ++
  len32Stores ++
  romStores ++
  zeroResGlobs ++
  [Asm.ret]

/-- Two-phase sequential driver (`ca_start` at PC = 0), shared exit tails, and `ca_drv_init`. -/
def checkerDriverAsm (tab : Tab := checkerTabMini) : List AsmItem :=
  let needBytes := abiNeed tab
  let fuelM := abiFuel - 1
  let resetStack : List AsmItem :=
    li AbiReg.t1 (BitVec.ofNat 64 (abiSlot + abiStack)) ++
    [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1, Asm.sd AbiReg.gp AbiReg.t1] ++
    li AbiReg.t1 (BitVec.ofNat 64 abiSlot) ++
    [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1, Asm.sd AbiReg.gp AbiReg.t1 8#12]
  let clearDesc (pos : Nat) : List AsmItem :=
    storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dbase pos) ++
    storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dlen pos) ++
    storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dlen32 pos)
  let outPos := tab.pos64 (.t0 L.Arena.OUT)
  let hdrfPos := tab.pos64 (.t0 L.Arena.HDRF)
  let ctlfPos := tab.pos64 (.t0 L.Arena.CTLF)
  let hdrWords := L.Arena.hdrW
  let setupSeqPhaseB : List AsmItem :=
    [Asm.slli AbiReg.t3 AbiReg.a0 1#6,
     Asm.srli AbiReg.t3 AbiReg.t3 1#6] ++
    storeMemOff .sd AbiReg.gp AbiReg.t3 AbiReg.t0 (tab.globOff phiGVar) ++
    storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.globOff ploGVar) ++
    li AbiReg.t1 (BitVec.ofNat 64 2) ++
    storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.globOff modeGVar) ++
    resetStack ++
    clearDesc outPos ++
    clearDesc ctlfPos ++
    li AbiReg.t1 (BitVec.ofNat 64 (abiSlot * tab.slotOf outPos)) ++
    [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1] ++
    storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.dbase hdrfPos) ++
    li AbiReg.t1 (BitVec.ofNat 64 hdrWords) ++
    storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.dlen hdrfPos) ++
    li AbiReg.t1 (BitVec.ofNat 64 (2 * hdrWords)) ++
    storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.dlen32 hdrfPos) ++
    li AbiReg.s0 (BitVec.ofNat 64 fuelM) ++
    [Asm.ld AbiReg.sp AbiReg.gp,
     Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
     Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++
    addImmOff AbiReg.t0 AbiReg.gp AbiReg.t2 tab.args ++
    li AbiReg.t1 0#64 ++
    [Asm.call (fnLabel "check")]
  [Asm.lbl startLabel] ++
  li AbiReg.t0 (BitVec.ofNat 64 needBytes) ++
  [Asm.raw (.branch .bltu AbiReg.a5 AbiReg.t0 (mkBimm 3)),
   Asm.raw (.branch .blt AbiReg.a1 AbiReg.zero (mkBimm 2)),
   Asm.raw (.branch .bge AbiReg.a3 AbiReg.zero (mkBimm 4)),
   Asm.addi AbiReg.a0 AbiReg.zero 0#12,
   Asm.addi AbiReg.a1 AbiReg.zero 1#12,
   Asm.ret] ++
  callerSaveAsm AbiReg.a4 (tab.saveBase 0) ++
  [Asm.mv AbiReg.gp AbiReg.a4,
   Asm.call drvInitLabel] ++
  -- Phase A: MODE := 3 (`check_a(0)` sequential header mode)
  li AbiReg.t1 (BitVec.ofNat 64 3) ++
  storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.globOff modeGVar) ++
  li AbiReg.s0 (BitVec.ofNat 64 fuelM) ++
  [Asm.ld AbiReg.sp AbiReg.gp,
   Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
   Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++
  addImmOff AbiReg.t0 AbiReg.gp AbiReg.t2 tab.args ++
  li AbiReg.t1 0#64 ++
  [Asm.call (fnLabel "check"),
   -- If top bit of a0 is clear (< 2^63), Phase A returned early (e.g. front_run error)
   Asm.bge AbiReg.a0 AbiReg.zero drvDoneLabel] ++
  -- Phase B: MODE := 2, PLO := 0, PHI := a0 - 2^63, CTLF.size := 0, HDRF -> OUT
  setupSeqPhaseB ++
  [Asm.lbl drvDoneLabel,
   Asm.addi AbiReg.a1 AbiReg.zero 0#12,
   Asm.j retRestoreLabel,
   Asm.lbl exhaustedLabel,
   Asm.addi AbiReg.a0 AbiReg.zero 0#12,
   Asm.addi AbiReg.a1 AbiReg.zero 1#12,
   Asm.j retRestoreLabel,
   Asm.lbl errLabel,
   Asm.addi AbiReg.a0 AbiReg.zero 0#12,
   Asm.lbl abortLabel,
   Asm.addi AbiReg.a1 AbiReg.zero 2#12,
   Asm.lbl retRestoreLabel] ++
  callerRestoreRetAsm AbiReg.gp (tab.saveBase 0) ++
  drvInitSubAsm tab

/-- Sequential comparator driver (`ca_start_c`) matching `CmpAccSSz` (`MODE = 4 → 5 → 6 → 8 → 9`).
    Boot ABI: `a0=chal_base, a1=chal_len, a2=pins_base, a3=pins_len, a4=region_base, a5=region_len,
    a6=sol_base, a7=sol_len`. Saves `sol_base, sol_len, kS, kC` in callee-saved registers `s3..s6`,
    calls shared `ca_drv_init`, and jumps into the shared exit stubs in `checkerDriverAsm`. -/
def checkerCmpDriverAsm (tab : Tab := checkerTabMini) : List AsmItem :=
  let needBytes := abiNeed tab
  let fuelM := abiFuel - 1
  let resetStack : List AsmItem :=
    li AbiReg.t1 (BitVec.ofNat 64 (abiSlot + abiStack)) ++
    [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1, Asm.sd AbiReg.gp AbiReg.t1] ++
    li AbiReg.t1 (BitVec.ofNat 64 abiSlot) ++
    [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1, Asm.sd AbiReg.gp AbiReg.t1 8#12]
  let clearDesc (pos : Nat) : List AsmItem :=
    storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dbase pos) ++
    storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dlen pos) ++
    storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dlen32 pos)
  let callCheck : List AsmItem :=
    li AbiReg.s0 (BitVec.ofNat 64 fuelM) ++
    [Asm.ld AbiReg.sp AbiReg.gp 0#12,
     Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
     Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++
    addImmOff AbiReg.t0 AbiReg.gp AbiReg.t2 tab.args ++
    li AbiReg.t1 0#64 ++
    [Asm.call (fnLabel "check")]
  let outPos := tab.pos64 (.t0 L.Arena.OUT)
  let hdrfPos := tab.pos64 (.t0 L.Arena.HDRF)
  let ctlfPos := tab.pos64 (.t0 L.Arena.CTLF)
  let hdrWords := hdrHw
  [Asm.lbl cmpStartLabel] ++
  li AbiReg.t0 (BitVec.ofNat 64 needBytes) ++
  [Asm.raw (.branch .bltu AbiReg.a5 AbiReg.t0 (mkBimm 4)),
   Asm.raw (.branch .blt AbiReg.a1 AbiReg.zero (mkBimm 3)),
   Asm.raw (.branch .blt AbiReg.a3 AbiReg.zero (mkBimm 2)),
   Asm.raw (.branch .bge AbiReg.a7 AbiReg.zero (mkBimm 4)),
   Asm.addi AbiReg.a0 AbiReg.zero 0#12,
   Asm.addi AbiReg.a1 AbiReg.zero 1#12,
   Asm.ret] ++
  callerSaveAsm AbiReg.a4 (tab.saveBase 0) ++
  [Asm.mv AbiReg.s3 AbiReg.a6,
   Asm.mv AbiReg.s4 AbiReg.a7,
   Asm.mv AbiReg.gp AbiReg.a4,
   Asm.call drvInitLabel] ++
  -- Mode 4: check_c1 (challenge front parse + stash)
  li AbiReg.t1 (BitVec.ofNat 64 4) ++
  storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.globOff modeGVar) ++
  callCheck ++
  [Asm.bge AbiReg.a0 AbiReg.zero drvDoneLabel] ++
  -- Mode 5: check_c2 (swap descriptor 0 to sol_base/sol_len, build solution index)
  storeMemOff .sd AbiReg.gp AbiReg.s3 AbiReg.t0 (tab.dbase 0) ++
  storeMemOff .sd AbiReg.gp AbiReg.s4 AbiReg.t0 (tab.dlen 0) ++
  resetStack ++
  li AbiReg.t1 (BitVec.ofNat 64 5) ++
  storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.globOff modeGVar) ++
  callCheck ++
  [Asm.bge AbiReg.a0 AbiReg.zero drvDoneLabel,
   Asm.slli AbiReg.s5 AbiReg.a0 1#6,
   Asm.srli AbiReg.s5 AbiReg.s5 1#6] ++
  -- Mode 6: check_c3(0) (challenge preparation + side_records + solution_of + par_compact(0,0))
  resetStack ++
  li AbiReg.t1 (BitVec.ofNat 64 6) ++
  storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.globOff modeGVar) ++
  callCheck ++
  [Asm.bge AbiReg.a0 AbiReg.zero drvDoneLabel,
   Asm.slli AbiReg.s6 AbiReg.a0 1#6,
   Asm.srli AbiReg.s6 AbiReg.s6 1#6] ++
  -- Mode 8: check_bs (solution jobs 0..kS-1)
  storeMemOff .sd AbiReg.gp AbiReg.s5 AbiReg.t0 (tab.globOff phiGVar) ++
  storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.globOff ploGVar) ++
  li AbiReg.t1 (BitVec.ofNat 64 8) ++
  storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.globOff modeGVar) ++
  resetStack ++
  clearDesc outPos ++
  clearDesc ctlfPos ++
  li AbiReg.t1 (BitVec.ofNat 64 (abiSlot * tab.slotOf outPos)) ++
  [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1] ++
  storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.dbase hdrfPos) ++
  li AbiReg.t1 (BitVec.ofNat 64 hdrWords) ++
  storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.dlen hdrfPos) ++
  li AbiReg.t1 (BitVec.ofNat 64 (2 * hdrWords)) ++
  storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.dlen32 hdrfPos) ++
  callCheck ++
  li AbiReg.t1 acceptWord.toBitVec ++
  [Asm.bne AbiReg.a0 AbiReg.t1 drvDoneLabel] ++
  -- Mode 9: check_bc (challenge jobs 0..kC-1)
  storeMemOff .sd AbiReg.gp AbiReg.s6 AbiReg.t0 (tab.globOff phiGVar) ++
  storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.globOff ploGVar) ++
  li AbiReg.t1 (BitVec.ofNat 64 9) ++
  storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.globOff modeGVar) ++
  resetStack ++
  callCheck ++
  [Asm.j drvDoneLabel]

/-- Parameterized unified symbolic assembly: `ca_start` driver (with shared exit stubs and
    `ca_drv_init`), `ca_start_c` comparator driver, and `checkerProgMini` compiled once using
    explicit pure-kernel function ordering and register allocation hints. -/
def checkerChipAsmWith (fnOrder : List _root_.L.FnName)
    (allocOf : _root_.L.FnName → _root_.L.FunDecl → RegAlloc)
    (tab : Tab := checkerTabMini) (p : _root_.L.Prog := checkerProgMini) : List AsmItem :=
  checkerDriverAsm tab ++
  checkerCmpDriverAsm tab ++
  (applyOrderHint fnOrder p).flatMap (fun (f, fd) => compileFnWith (allocOf f fd) tab f fd)

/-- Unified symbolic assembly: `ca_start` driver (with shared exit stubs and `ca_drv_init`),
    `ca_start_c` comparator driver, and the compiled `checkerProgMini` functions once. -/
def checkerChipAsm (tab : Tab := checkerTabMini)
    (p : _root_.L.Prog := checkerProgMini) : List AsmItem :=
  checkerDriverAsm tab ++
  checkerCmpDriverAsm tab ++
  (orderProgFns p).flatMap (fun (f, fd) => compileFn tab f fd)

theorem checkerChipAsm_eq_with (tab : Tab := checkerTabMini)
    (p : _root_.L.Prog := checkerProgMini) (hp : 1 < p.length) :
    checkerChipAsm tab p =
      checkerChipAsmWith (chooseFnOrder p) (fun _ fd => chooseRegAlloc fd) tab p := by
  dsimp only [checkerChipAsm, checkerChipAsmWith, orderProgFns]
  rw [ite_eq_right (by omega : ¬p.length ≤ 1)]
  rfl

end ConAgua.RISCV.Bridge

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

private def hexNat (digits n : Nat) : String :=
  Id.run do
    let mut acc : List Char := []
    let mut v := n
    let mut k := 0
    while v > 0 || k < digits do
      acc := hexDigit (v &&& 0xf) :: acc
      v := v >>> 4
      k := k + 1
    return String.ofList acc

private def hexWord32 (w : BitVec 32) : String :=
  let v := w.toNat
  String.ofList [
    '0', 'x',
    hexDigit ((v >>> 28) &&& 0xf),
    hexDigit ((v >>> 24) &&& 0xf),
    hexDigit ((v >>> 20) &&& 0xf),
    hexDigit ((v >>> 16) &&& 0xf),
    hexDigit ((v >>> 12) &&& 0xf),
    hexDigit ((v >>> 8) &&& 0xf),
    hexDigit ((v >>> 4) &&& 0xf),
    hexDigit (v &&& 0xf)
  ]

private def abiRegNames : Array String := #[
  "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
  "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
  "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
  "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"
]

private def regName (r : ConAgua.RISCV.RV64.Reg) : String :=
  abiRegNames.getD r.toNat s!"x{r.toNat}"

private def pad6 (s : String) : String :=
  if s.length ≥ 6 then s
  else s ++ String.ofList (List.replicate (6 - s.length) ' ')

private def aluImmOpName : ConAgua.RISCV.RV64.AluImmOp → String
  | .addi => "addi"
  | .slti => "slti"
  | .sltiu => "sltiu"
  | .andi => "andi"
  | .ori => "ori"
  | .xori => "xori"

private def shiftImmOpName : ConAgua.RISCV.RV64.ShiftImmOp → String
  | .slli => "slli"
  | .srli => "srli"

private def aluOpName : ConAgua.RISCV.RV64.AluOp → String
  | .add => "add"
  | .sub => "sub"
  | .slt => "slt"
  | .sltu => "sltu"
  | .and => "and"
  | .or => "or"
  | .xor => "xor"
  | .sll => "sll"
  | .srl => "srl"
  | .mul => "mul"
  | .mulhu => "mulhu"

private def branchOpName : ConAgua.RISCV.RV64.BranchOp → String
  | .beq => "beq"
  | .bne => "bne"
  | .blt => "blt"
  | .bltu => "bltu"
  | .bge => "bge"
  | .bgeu => "bgeu"

private def loadOpName : ConAgua.RISCV.RV64.LoadOp → String
  | .ld => "ld"
  | .lwu => "lwu"
  | .lbu => "lbu"

private def storeOpName : ConAgua.RISCV.RV64.StoreOp → String
  | .sd => "sd"
  | .sw => "sw"

private def signedInt (i : Int) : String :=
  if i ≥ 0 then s!"+{i}" else s!"{i}"

private def hexPc (pc : Int) : String :=
  if pc ≥ 0 then hexNat 6 pc.toNat else s!"-{hexNat 6 (-pc).toNat}"

private def targetLabelSuffix (labelMap : Std.HashMap Nat (List String)) (tgt : Int) : String :=
  if tgt ≥ 0 && tgt % 4 == 0 then
    match labelMap[tgt.toNat / 4]? with
    | some (lbl :: _) => s!" {lbl}"
    | _ => ""
  else ""

private def disasmWord32 (labelMap : Std.HashMap Nat (List String)) (pc : Nat) (w : BitVec 32) : String :=
  match ConAgua.RISCV.RV64.decode w with
  | none => "<illegal>"
  | some (.aluImm op rd rs1 imm12) =>
    s!"{pad6 (aluImmOpName op)} {regName rd}, {regName rs1}, {imm12.toInt}"
  | some (.shImm op rd rs1 shamt) =>
    s!"{pad6 (shiftImmOpName op)} {regName rd}, {regName rs1}, {shamt.toNat}"
  | some (.lui rd imm20) =>
    s!"lui    {regName rd}, 0x{hexNat 5 imm20.toNat}"
  | some (.alu op rd rs1 rs2) =>
    s!"{pad6 (aluOpName op)} {regName rd}, {regName rs1}, {regName rs2}"
  | some (.jal rd jimm) =>
    let off := 2 * jimm.toInt
    let tgt := (pc : Int) + off
    s!"jal    {regName rd}, {signedInt off} (-> 0x{hexPc tgt}{targetLabelSuffix labelMap tgt})"
  | some (.jalr rd rs1 imm12) =>
    let retNote := if rd == 0#5 && rs1 == 1#5 && imm12 == 0#12 then " ; ret" else ""
    s!"jalr   {regName rd}, {imm12.toInt}({regName rs1}){retNote}"
  | some (.branch op rs1 rs2 bimm) =>
    let off := 2 * bimm.toInt
    let tgt := (pc : Int) + off
    s!"{pad6 (branchOpName op)} {regName rs1}, {regName rs2}, {signedInt off} (-> 0x{hexPc tgt}{targetLabelSuffix labelMap tgt})"
  | some (.load op rd rs1 imm12) =>
    s!"{pad6 (loadOpName op)} {regName rd}, {imm12.toInt}({regName rs1})"
  | some (.store op rs1 rs2 imm12) =>
    s!"{pad6 (storeOpName op)} {regName rs2}, {imm12.toInt}({regName rs1})"

private def buildLabelMap (lm : ConAgua.RISCV.Linker.LinkModel)
    (items : List ConAgua.RISCV.Compiler.AsmItem) : Std.HashMap Nat (List String) :=
  Id.run do
    let mut m : Std.HashMap Nat (List String) := ∅
    let mut wordOff := 0
    for it in items do
      match it with
      | .label s =>
        let prev := m.getD wordOff []
        m := m.insert wordOff (prev ++ [s])
      | _ => pure ()
      wordOff := wordOff + lm.itemSize it
    return m

private def writeWords (h : IO.FS.Handle) (labelMap : Std.HashMap Nat (List String))
    (words : Array (BitVec 32)) (startIdx stopIdx : Nat) : IO Unit := do
  let stop := min stopIdx words.size
  let mut i := startIdx
  let mut buf := ""
  let mut batch := 0
  while i < stop do
    let w := if hi : i < words.size then words[i] else 0#32
    let pc := 4 * i
    let dis := disasmWord32 labelMap pc w
    let lblSuffix :=
      match labelMap[i]? with
      | some lbls =>
        let lblStr := ", ".intercalate lbls
        s!"  [{lblStr}]"
      | none => ""
    buf := buf ++ s!"\t.word {hexWord32 w}\t# {hexNat 6 pc}: {dis}{lblSuffix}\n"
    batch := batch + 1
    if batch ≥ 256 then
      h.putStr buf
      buf := ""
      batch := 0
    i := i + 1
  if !buf.isEmpty then
    h.putStr buf

private def writeQuad (h : IO.FS.Handle) (name : String) (val : Nat) : IO Unit := do
  h.putStrLn s!"\t.globl {name}"
  h.putStrLn s!"{name}: .quad {val}"

private def runAsmMode (outPath : System.FilePath) : IO UInt32 := do
  IO.println "Assembling unified checkerChipAsm for GNU assembly..."
  let tab := ConAgua.RISCV.Bridge.checkerTabMini
  let drvItems := ConAgua.RISCV.Bridge.checkerDriverAsm tab
  let items := ConAgua.RISCV.Bridge.checkerChipAsm
  let lm := ConAgua.RISCV.Linker.hybridLinkModel (ConAgua.RISCV.Linker.computeHybridWidths items)
  let cmpEntryWord := lm.totalSize drvItems
  match ConAgua.RISCV.Linker.linkHybrid items with
  | .error e =>
    IO.eprintln s!"linkHybrid failed: {e}"
    return 1
  | .ok words =>
    if cmpEntryWord ≥ words.size then
      IO.eprintln s!"invalid ca_start_c offset {cmpEntryWord} ≥ {words.size}"
      return 1
    let labelMap := buildLabelMap lm items
    let slot := ConAgua.RISCV.Compiler.abiSlot
    let regionSize := ConAgua.RISCV.Compiler.abiNeed tab
    if let some dir := outPath.parent then
      IO.FS.createDirAll dir
    IO.FS.withFile outPath .write fun h => do
      h.putStrLn "\t.text"
      h.putStrLn "\t.balign 4"
      h.putStrLn "\t.globl ca_start"
      h.putStrLn "ca_start:"
      writeWords h labelMap words 0 cmpEntryWord
      h.putStrLn "\t.globl ca_start_c"
      h.putStrLn "ca_start_c:"
      writeWords h labelMap words cmpEntryWord words.size
      h.putStrLn "\t.section .rodata"
      h.putStrLn "\t.balign 8"
      writeQuad h "ca_region_size" regionSize
      writeQuad h "ca_slot" slot
      writeQuad h "ca_w0" (2 * slot)
      writeQuad h "ca_nw" tab.nw
      h.putStrLn "\t.section .note.GNU-stack,\"\",@progbits"
    IO.println s!"  words={words.size} ca_start_c_word={cmpEntryWord} ca_region_size={regionSize}"
    IO.println s!"Wrote {outPath}"
    return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--asm", p] => runAsmMode ⟨p⟩
  | [p] => runAsmMode ⟨p⟩
  | _ =>
    IO.eprintln "usage: emit-checker [--asm] <output.s>"
    return 1
