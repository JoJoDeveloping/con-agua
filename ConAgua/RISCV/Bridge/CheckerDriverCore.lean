import ConAgua.RISCV.Bridge.CheckerIso
import ConAgua.RISCV.Bridge.EmitChecker
import ConAgua.RISCV.Bridge.CheckerWf
import ConAgua.RISCV.Bridge.CheckerWfFast
import ConAgua.RISCV.Bridge.CheckerWfStmt
import ConAgua.RISCV.Bridge.CheckerLinkWf
import ConAgua.RISCV.Compiler.ProgSimMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Linked Checker Core Infrastructure (`ConAgua.RISCV.Bridge.CheckerDriverCore`)

Provides Sections 1–3 of the linked checker driver infrastructure:
- Section 1: `checkerCode`, `checkerRom`, `checkerCmpEntryWord`, `checkerCmpEntryPc`,
  `checkerEnv : CodeEnvGen checkerLM`, `checkerFnsLinked`, `checkerDriverAsm_decomp`,
  `checkerCmpDriverAsm_decomp`, static `checkerTabMini` lemmas, `DrvRegsSaved`, and
  `phaseAInitMem` / `phaseBMem` / `phaseBInitMem` / `cmpPhase*Mem`.
- Section 2: RV64 return determinism (`step_trap_of_rom_none`, `run_trap_of_step_trap`,
  `run_ret_deterministic`, `run_cont_ret`, `ret_ne_of_cont`), shared exit-stub return lemmas
  (`checker_exhausted_returns`, `checker_abort_returns`, `checker_err_returns`), and
  `minil_run_words_size`.
- Section 3: `checkerLayoutA` / `checkerLayoutB` / `checkerLayoutCmpB` (`ProgLayout checkerTabMini`),
  zero-word and ROM-byte extraction helpers.
-/

namespace ConAgua.RISCV.Bridge

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Compiler
open ConAgua.RISCV.Linker

/-! ## 1. Linked Checker Image, `CodeEnvGen checkerLM`, and Static Table Facts -/

/-- Linker model backing the hybrid near/mid/far linked `checkerCode`. -/
def checkerLM : LinkModel :=
  hybridLinkModel (computeHybridWidths checkerChipAsm)

/-- The linked RV64 machine-code image of `EmitChecker.checkerChipAsm` via `linkHybrid`. -/
def checkerCode : Array (BitVec 32) :=
  match linkHybrid checkerChipAsm with
  | .ok code => code
  | .error _ => #[]

/-- Architectural RV64 ROM for `checkerCode`. -/
def checkerRom : RV64.Rom :=
  RV64.romOfArray checkerCode

theorem checkerCode_eq_linkHybrid :
    linkHybrid checkerChipAsm = .ok checkerCode := by
  obtain ⟨code, hok, _⟩ := checkerChipAsm_linkHybrid_ok
  simp [checkerCode, hok]

theorem checkerCode_size_lt : checkerCode.size < 2 ^ 22 := by
  obtain ⟨code, hok, hlt⟩ := checkerChipAsm_linkHybrid_ok
  have heq : checkerCode = code := by simp [checkerCode, hok]
  rw [heq]; exact hlt

theorem checkerCode_size64 : 4 * checkerCode.size < 2 ^ 64 := by
  have h := checkerCode_size_lt; omega

noncomputable def checkerLabels : LabelMap :=
  Classical.choose (linkHybrid_ok_linkSpec checkerCode_eq_linkHybrid)

theorem checkerChipAsm_linkSpec :
    checkerLM.linkSpec checkerChipAsm = .ok (checkerCode, checkerLabels) :=
  Classical.choose_spec (linkHybrid_ok_linkSpec checkerCode_eq_linkHybrid)

/-- Decompose `checkerDriverAsm tab` into clean named slices for modular linking proofs. -/
def drvPfx : List AsmItem :=
  [Asm.lbl startLabel]

def drvNeedLi (tab : Tab) : List AsmItem :=
  li AbiReg.t0 (BitVec.ofNat 64 (abiNeed tab))

def drvBootCheck (tab : Tab) : List AsmItem :=
  [Asm.raw (.branch .bltu AbiReg.a5 AbiReg.t0 (mkBimm 3)),
   Asm.raw (.branch .blt AbiReg.a1 AbiReg.zero (mkBimm 2)),
   Asm.raw (.branch .bge AbiReg.a3 AbiReg.zero (mkBimm 4)),
   Asm.addi AbiReg.a0 AbiReg.zero 0#12,
   Asm.addi AbiReg.a1 AbiReg.zero 1#12,
   Asm.ret] ++
  callerSaveAsm AbiReg.a4 (tab.saveBase 0) ++
  [Asm.mv AbiReg.gp AbiReg.a4]

def drvResetStack : List AsmItem :=
  li AbiReg.t1 (BitVec.ofNat 64 (abiSlot + abiStack)) ++
  [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1,
   Asm.sd AbiReg.gp AbiReg.t1] ++
  li AbiReg.t1 (BitVec.ofNat 64 abiSlot) ++
  [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1,
   Asm.sd AbiReg.gp AbiReg.t1 8#12]

def drvBufBaseStores (tab : Tab) : List AsmItem :=
  (List.range tab.nbuf).flatMap fun p =>
    let srcReg := if p == 0 then AbiReg.a0 else AbiReg.a2
    storeMemOff .sd AbiReg.gp srcReg AbiReg.t0 (tab.dbase p)

def drvBufLenStores (tab : Tab) : List AsmItem :=
  (List.range tab.nbuf).flatMap fun p =>
    let srcReg := if p == 0 then AbiReg.a1 else AbiReg.a3
    storeMemOff .sd AbiReg.gp srcReg AbiReg.t0 (tab.dlen p)

def drvRomStoresGo (romBase : Int) (idx : Nat) : List (BitVec 64) → List AsmItem
  | [] => []
  | w :: ws =>
    (li AbiReg.t1 w ++ storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (romBase + 8 * (idx : Int))) ++
      drvRomStoresGo romBase (idx + 1) ws

theorem drvRomStores_eq (romBase : Int) (ws : List (BitVec 64)) :
    (ws.zipIdx.flatMap fun (w, i) =>
      li AbiReg.t1 w ++ storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (romBase + 8 * (i : Int))) =
      drvRomStoresGo romBase 0 ws := by
  have hgen : ∀ (k : Nat) (xs : List (BitVec 64)),
      ((xs.zipIdx k).flatMap fun (w, i) =>
        li AbiReg.t1 w ++ storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (romBase + 8 * (i : Int))) =
        drvRomStoresGo romBase k xs := by
    intro k xs
    induction xs generalizing k with
    | nil => simp [List.zipIdx, drvRomStoresGo]
    | cons x xs ih =>
      simp only [List.zipIdx_cons, List.flatMap_cons, drvRomStoresGo, ih (k + 1)]
  exact hgen 0 ws

def drvInitBody (tab : Tab) : List AsmItem :=
  drvResetStack ++
  drvBufBaseStores tab ++
  drvFillStrideLoop "ca_drv_bloop" "ca_drv_bdone" (tab.dbase tab.nbuf)
    (BitVec.ofNat 64 (2 * abiSlot)) (BitVec.ofNat 64 abiSlot) (tab.nb + tab.nw - tab.nbuf) ++
  drvBufLenStores tab ++
  drvFillConstLoop "ca_drv_lbloop" "ca_drv_lbdone" (tab.dlen tab.nbuf)
    (BitVec.ofNat 64 abiSlot) (tab.nb - tab.nbuf) ++
  drvFillConstLoop "ca_drv_lwloop" "ca_drv_lwdone" (tab.dlen tab.nb)
    (BitVec.ofNat 64 abiWords) tab.nw ++
  drvFillConstLoop "ca_drv_l32bloop" "ca_drv_l32bdone" (tab.dlen32 0)
    0#64 tab.nb ++
  drvFillConstLoop "ca_drv_l32wloop" "ca_drv_l32wdone" (tab.dlen32 tab.nb)
    (BitVec.ofNat 64 (2 * abiWords)) tab.nw ++
  drvRomStoresGo tab.romBase 0 (romWords64 tab.rom) ++
  drvFillConstLoop "ca_drv_zloop" "ca_drv_zdone" tab.resBase 0#64 (tab.nxres + tab.ng)

theorem drvInitSubAsm_decomp (tab : Tab) :
    drvInitSubAsm tab = [Asm.lbl drvInitLabel] ++ drvInitBody tab ++ [Asm.ret] := by
  dsimp only [drvInitSubAsm, drvInitBody, drvResetStack, drvBufBaseStores, drvBufLenStores]
  change _ = _
  rw [drvRomStores_eq]
  simp only [List.append_assoc]

def drvPhaseASetup (tab : Tab) : List AsmItem :=
  li AbiReg.t1 (BitVec.ofNat 64 3) ++
  storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.globOff modeGVar) ++
  li AbiReg.s0 (BitVec.ofNat 64 (abiFuel - 1)) ++
  [Asm.ld AbiReg.sp AbiReg.gp,
   Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
   Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++
  addImmOff AbiReg.t0 AbiReg.gp AbiReg.t2 tab.args ++
  li AbiReg.t1 0#64

def drvPhaseACall : List AsmItem :=
  [Asm.call (fnLabel "check"),
   Asm.bge AbiReg.a0 AbiReg.zero drvDoneLabel]

def drvClearDesc (tab : Tab) (pos : Nat) : List AsmItem :=
  storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dbase pos) ++
  storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dlen pos) ++
  storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dlen32 pos)

def drvPhaseBSetup (tab : Tab) : List AsmItem :=
  let outPos := tab.pos64 (.t0 L.Arena.OUT)
  let hdrfPos := tab.pos64 (.t0 L.Arena.HDRF)
  let ctlfPos := tab.pos64 (.t0 L.Arena.CTLF)
  [Asm.slli AbiReg.t3 AbiReg.a0 1#6,
   Asm.srli AbiReg.t3 AbiReg.t3 1#6] ++
  storeMemOff .sd AbiReg.gp AbiReg.t3 AbiReg.t0 (tab.globOff phiGVar) ++
  storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.globOff ploGVar) ++
  li AbiReg.t1 (BitVec.ofNat 64 2) ++
  storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.globOff modeGVar) ++
  drvResetStack ++
  drvClearDesc tab outPos ++
  drvClearDesc tab ctlfPos ++
  li AbiReg.t1 (BitVec.ofNat 64 (abiSlot * tab.slotOf outPos)) ++
  [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1] ++
  storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.dbase hdrfPos) ++
  li AbiReg.t1 (BitVec.ofNat 64 L.Arena.hdrW) ++
  storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.dlen hdrfPos) ++
  li AbiReg.t1 (BitVec.ofNat 64 (2 * L.Arena.hdrW)) ++
  storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.dlen32 hdrfPos) ++
  li AbiReg.s0 (BitVec.ofNat 64 (abiFuel - 1)) ++
  [Asm.ld AbiReg.sp AbiReg.gp,
   Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
   Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++
  addImmOff AbiReg.t0 AbiReg.gp AbiReg.t2 tab.args ++
  li AbiReg.t1 0#64

def drvPhaseBCall : List AsmItem :=
  [Asm.call (fnLabel "check")]

def drvDoneStub : List AsmItem :=
  [Asm.lbl drvDoneLabel,
   Asm.addi AbiReg.a1 AbiReg.zero 0#12,
   Asm.j retRestoreLabel]

def drvExhaustedStub : List AsmItem :=
  [Asm.lbl exhaustedLabel,
   Asm.addi AbiReg.a0 AbiReg.zero 0#12,
   Asm.addi AbiReg.a1 AbiReg.zero 1#12,
   Asm.j retRestoreLabel]

def drvErrPrefix : List AsmItem :=
  [Asm.lbl errLabel,
   Asm.addi AbiReg.a0 AbiReg.zero 0#12]

def drvAbortPrefix : List AsmItem :=
  [Asm.lbl abortLabel,
   Asm.addi AbiReg.a1 AbiReg.zero 2#12]

def drvRetRestoreStub (tab : Tab) : List AsmItem :=
  [Asm.lbl retRestoreLabel] ++ callerRestoreRetAsm AbiReg.gp (tab.saveBase 0)

private def drvEndStubsLit (tab : Tab) : List AsmItem :=
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
  callerRestoreRetAsm AbiReg.gp (tab.saveBase 0)

private theorem drvEndStubsLit_eq (tab : Tab) :
    drvEndStubsLit tab =
      drvDoneStub ++ drvExhaustedStub ++
      drvErrPrefix ++ drvAbortPrefix ++ drvRetRestoreStub tab := by
  simp only [drvEndStubsLit, drvDoneStub, drvExhaustedStub,
    drvErrPrefix, drvAbortPrefix, drvRetRestoreStub,
    List.cons_append, List.nil_append]

def drvPreDone (tab : Tab) : List AsmItem :=
  drvPfx ++ drvNeedLi tab ++ drvBootCheck tab ++ [Asm.call drvInitLabel] ++
  drvPhaseASetup tab ++ drvPhaseACall ++
  drvPhaseBSetup tab ++ drvPhaseBCall

def drvAllBeforeEx (tab : Tab) : List AsmItem :=
  drvPreDone tab ++ drvDoneStub

theorem checkerDriverAsm_decomp (tab : Tab) :
    checkerDriverAsm tab =
      drvAllBeforeEx tab ++ drvExhaustedStub ++
      drvErrPrefix ++ drvAbortPrefix ++ drvRetRestoreStub tab ++ drvInitSubAsm tab := by
  dsimp only [checkerDriverAsm, drvAllBeforeEx, drvPreDone, drvPfx, drvNeedLi, drvBootCheck,
    drvResetStack, drvPhaseASetup, drvPhaseACall, drvPhaseBSetup, drvClearDesc, drvPhaseBCall]
  change _ = _
  have hend : ∀ (xs : List AsmItem),
      xs ++ [Asm.lbl drvDoneLabel, Asm.addi AbiReg.a1 AbiReg.zero 0#12,
      Asm.j retRestoreLabel,
      Asm.lbl exhaustedLabel, Asm.addi AbiReg.a0 AbiReg.zero 0#12,
      Asm.addi AbiReg.a1 AbiReg.zero 1#12, Asm.j retRestoreLabel,
      Asm.lbl errLabel, Asm.addi AbiReg.a0 AbiReg.zero 0#12,
      Asm.lbl abortLabel, Asm.addi AbiReg.a1 AbiReg.zero 2#12,
      Asm.lbl retRestoreLabel] ++ callerRestoreRetAsm AbiReg.gp (tab.saveBase 0) =
      xs ++ (drvDoneStub ++ drvExhaustedStub ++
      drvErrPrefix ++ drvAbortPrefix ++ drvRetRestoreStub tab) := fun xs => by
    rw [List.append_assoc]; exact congrArg (xs ++ ·) (drvEndStubsLit_eq tab)
  rw [hend]
  simp only [List.cons_append, List.nil_append, List.append_assoc]

/-! ### Comparator Driver Decomposition (`checkerCmpDriverAsm`) & Entry Offset -/

def cmpDrvPfx : List AsmItem :=
  [Asm.lbl cmpStartLabel]

def cmpDrvBootCheck (tab : Tab) : List AsmItem :=
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
   Asm.mv AbiReg.gp AbiReg.a4]

def cmpDrvSetMode (m : Nat) (tab : Tab) : List AsmItem :=
  li AbiReg.t1 (BitVec.ofNat 64 m) ++
  storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.globOff modeGVar)

def cmpDrvCallPrep (tab : Tab) : List AsmItem :=
  li AbiReg.s0 (BitVec.ofNat 64 (abiFuel - 1)) ++
  [Asm.ld AbiReg.sp AbiReg.gp 0#12,
   Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
   Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++
  addImmOff AbiReg.t0 AbiReg.gp AbiReg.t2 tab.args ++
  li AbiReg.t1 0#64

def cmpDrvCallCheck (tab : Tab) : List AsmItem :=
  cmpDrvCallPrep tab ++ [Asm.call (fnLabel "check")]

def cmpDrvMode4Setup (tab : Tab) : List AsmItem :=
  cmpDrvSetMode 4 tab ++ cmpDrvCallPrep tab

def cmpDrvMode4Post : List AsmItem :=
  [Asm.bge AbiReg.a0 AbiReg.zero drvDoneLabel]

def cmpDrvMode5Setup (tab : Tab) : List AsmItem :=
  storeMemOff .sd AbiReg.gp AbiReg.s3 AbiReg.t0 (tab.dbase 0) ++
  storeMemOff .sd AbiReg.gp AbiReg.s4 AbiReg.t0 (tab.dlen 0) ++
  drvResetStack ++
  cmpDrvSetMode 5 tab ++
  cmpDrvCallPrep tab

def cmpDrvMode5Post : List AsmItem :=
  [Asm.bge AbiReg.a0 AbiReg.zero drvDoneLabel,
   Asm.slli AbiReg.s5 AbiReg.a0 1#6,
   Asm.srli AbiReg.s5 AbiReg.s5 1#6]

def cmpDrvMode6Setup (tab : Tab) : List AsmItem :=
  drvResetStack ++
  cmpDrvSetMode 6 tab ++
  cmpDrvCallPrep tab

def cmpDrvMode6Post : List AsmItem :=
  [Asm.bge AbiReg.a0 AbiReg.zero drvDoneLabel,
   Asm.slli AbiReg.s6 AbiReg.a0 1#6,
   Asm.srli AbiReg.s6 AbiReg.s6 1#6]

def cmpDrvMode8Setup (tab : Tab) : List AsmItem :=
  let outPos := tab.pos64 (.t0 L.Arena.OUT)
  let hdrfPos := tab.pos64 (.t0 L.Arena.HDRF)
  let ctlfPos := tab.pos64 (.t0 L.Arena.CTLF)
  storeMemOff .sd AbiReg.gp AbiReg.s5 AbiReg.t0 (tab.globOff phiGVar) ++
  storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.globOff ploGVar) ++
  cmpDrvSetMode 8 tab ++
  drvResetStack ++
  drvClearDesc tab outPos ++
  drvClearDesc tab ctlfPos ++
  li AbiReg.t1 (BitVec.ofNat 64 (abiSlot * tab.slotOf outPos)) ++
  [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1] ++
  storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.dbase hdrfPos) ++
  li AbiReg.t1 (BitVec.ofNat 64 hdrHw) ++
  storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.dlen hdrfPos) ++
  li AbiReg.t1 (BitVec.ofNat 64 (2 * hdrHw)) ++
  storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.dlen32 hdrfPos) ++
  cmpDrvCallPrep tab

def cmpDrvMode8Post : List AsmItem :=
  li AbiReg.t1 acceptWord.toBitVec ++
  [Asm.bne AbiReg.a0 AbiReg.t1 drvDoneLabel]

def cmpDrvMode9Setup (tab : Tab) : List AsmItem :=
  storeMemOff .sd AbiReg.gp AbiReg.s6 AbiReg.t0 (tab.globOff phiGVar) ++
  storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.globOff ploGVar) ++
  cmpDrvSetMode 9 tab ++
  drvResetStack ++
  cmpDrvCallPrep tab

def cmpDrvPreDone (tab : Tab) : List AsmItem :=
  cmpDrvPfx ++ drvNeedLi tab ++ cmpDrvBootCheck tab ++ [Asm.call drvInitLabel] ++
  cmpDrvMode4Setup tab ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode4Post ++
  cmpDrvMode5Setup tab ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode5Post ++
  cmpDrvMode6Setup tab ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode6Post ++
  cmpDrvMode8Setup tab ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode8Post ++
  cmpDrvMode9Setup tab ++ [Asm.call (fnLabel "check")]

theorem checkerCmpDriverAsm_decomp (tab : Tab) :
    checkerCmpDriverAsm tab = cmpDrvPreDone tab ++ [Asm.j drvDoneLabel] := by
  dsimp only [checkerCmpDriverAsm, cmpDrvPreDone, cmpDrvPfx, drvNeedLi,
    cmpDrvBootCheck, drvResetStack,
    cmpDrvMode4Setup, cmpDrvMode4Post, cmpDrvMode5Setup, cmpDrvMode5Post,
    cmpDrvMode6Setup, cmpDrvMode6Post, cmpDrvMode8Setup, cmpDrvMode8Post,
    cmpDrvMode9Setup, cmpDrvSetMode, cmpDrvCallPrep, drvClearDesc]
  simp only [List.cons_append, List.nil_append, List.append_assoc]

/-- Word offset of `ca_start_c` inside the unified `checkerCode` image. -/
def checkerCmpEntryWord : Nat :=
  checkerLM.totalSize (checkerDriverAsm checkerTabMini)

/-- Entry PC of `ca_start_c` (`4 * checkerCmpEntryWord`) inside the unified `checkerRom`. -/
def checkerCmpEntryPc : BitVec 64 :=
  BitVec.ofNat 64 (4 * checkerCmpEntryWord)

def checkerFnsAsm : List AsmItem :=
  (orderProgFns checkerProgMini).flatMap fun (f, fd) => compileFn checkerTabMini f fd

private theorem checkerChipAsm_eq :
    checkerChipAsm =
      checkerDriverAsm checkerTabMini ++ checkerCmpDriverAsm checkerTabMini ++ checkerFnsAsm :=
  rfl

/-- Any RV64 machine-code image linked from `EmitChecker.checkerChipAsmWith` under any
    valid `LinkModel` with explicit pure-kernel `fnOrder` and `allocOf` hints and
    `< 2 ^ 22` words (`< 16 MiB`). -/
structure LinkedCmpImage where
  lkm     : LinkModel
  fnOrder : List _root_.L.FnName
  allocOf : _root_.L.FnName → _root_.L.FunDecl → RegAlloc
  code    : Array (BitVec 32)
  labels  : LabelMap
  hlink   : lkm.linkSpec (checkerChipAsmWith fnOrder allocOf) = .ok (code, labels)
  hsz     : code.size < 2 ^ 22

def LinkedCmpImage.rom (img : LinkedCmpImage) : RV64.Rom :=
  RV64.romOfArray img.code

theorem LinkedCmpImage.size64 (img : LinkedCmpImage) : 4 * img.code.size < 2 ^ 64 := by
  have h := img.hsz; omega

def LinkedCmpImage.cmpEntryWord (img : LinkedCmpImage) : Nat :=
  img.lkm.totalSize (checkerDriverAsm checkerTabMini)

def LinkedCmpImage.cmpEntryPc (img : LinkedCmpImage) : BitVec 64 :=
  BitVec.ofNat 64 (4 * img.cmpEntryWord)

noncomputable def defaultCheckerCmpImage : LinkedCmpImage where
  lkm     := checkerLM
  fnOrder := chooseFnOrder checkerProgMini
  allocOf := fun _ fd => chooseRegAlloc fd
  code    := checkerCode
  labels  := checkerLabels
  hlink   := by
    have hgt : 1 < checkerProgMini.length := by
      obtain ⟨_, _, _, h⟩ : ∃ a b rest, _root_.L.Checker.checkerProg = a :: b :: rest := ⟨_, _, _, rfl⟩
      change 1 < _root_.L.Checker.checkerProg.length
      rw [h, List.length_cons, List.length_cons]
      omega
    rw [← checkerChipAsm_eq_with checkerTabMini checkerProgMini hgt]
    exact checkerChipAsm_linkSpec
  hsz     := checkerCode_size_lt

def linkedCmpFnsAsm (img : LinkedCmpImage) : List AsmItem :=
  (applyOrderHint img.fnOrder checkerProgMini).flatMap fun (f, fd) =>
    compileFnWith (img.allocOf f fd) checkerTabMini f fd

theorem linkedCmpChipAsm_eq (img : LinkedCmpImage) :
    checkerChipAsmWith img.fnOrder img.allocOf =
      checkerDriverAsm checkerTabMini ++ checkerCmpDriverAsm checkerTabMini ++ linkedCmpFnsAsm img :=
  rfl

noncomputable def linkedCmpEnv (img : LinkedCmpImage) : CodeEnvGen img.lkm :=
  let exPre := drvAllBeforeEx checkerTabMini
  let errPre := exPre ++ drvExhaustedStub
  let abPre := errPre ++ drvErrPrefix
  let restTail := drvInitSubAsm checkerTabMini ++ checkerCmpDriverAsm checkerTabMini ++ linkedCmpFnsAsm img
  { tab := checkerTabMini
    code := img.code
    labels := img.labels
    rom := img.rom
    hrom := romOfArray_matchesCode img.code
    hcode64 := img.size64
    errTarget := img.lkm.totalSize errPre
    herrLbl := by
      have hlinkE : img.lkm.linkSpec (errPre ++ [Asm.lbl errLabel] ++
          ([Asm.addi AbiReg.a0 AbiReg.zero 0#12] ++ drvAbortPrefix ++
           drvRetRestoreStub checkerTabMini ++ restTail)) =
          .ok (img.code, img.labels) := by
        have h := img.hlink
        rw [linkedCmpChipAsm_eq img, checkerDriverAsm_decomp] at h
        have hsp : drvErrPrefix = [Asm.lbl errLabel] ++ [Asm.addi AbiReg.a0 AbiReg.zero 0#12] := rfl
        rw [hsp] at h
        simpa only [errPre, exPre, restTail, List.append_assoc] using h
      exact linkResolved_lbl_lm img.lkm errPre errLabel _ hlinkE
    abortTarget := img.lkm.totalSize abPre
    habortLbl := by
      have hlinkA : img.lkm.linkSpec (abPre ++ [Asm.lbl abortLabel] ++
          ([Asm.addi AbiReg.a1 AbiReg.zero 2#12] ++ drvRetRestoreStub checkerTabMini ++ restTail)) =
          .ok (img.code, img.labels) := by
        have h := img.hlink
        rw [linkedCmpChipAsm_eq img, checkerDriverAsm_decomp] at h
        have hsp : drvAbortPrefix = [Asm.lbl abortLabel] ++
            [Asm.addi AbiReg.a1 AbiReg.zero 2#12] := rfl
        rw [hsp] at h
        simpa only [abPre, errPre, exPre, restTail, List.append_assoc] using h
      exact linkResolved_lbl_lm img.lkm abPre abortLabel _ hlinkA
    exhaustedTarget := img.lkm.totalSize exPre
    hexhaustedLbl := by
      have hlinkX : img.lkm.linkSpec (exPre ++ [Asm.lbl exhaustedLabel] ++
          ([Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.addi AbiReg.a1 AbiReg.zero 1#12,
            Asm.j retRestoreLabel] ++
           drvErrPrefix ++ drvAbortPrefix ++ drvRetRestoreStub checkerTabMini ++ restTail)) =
          .ok (img.code, img.labels) := by
        have h := img.hlink
        rw [linkedCmpChipAsm_eq img, checkerDriverAsm_decomp] at h
        have hsp : drvExhaustedStub = [Asm.lbl exhaustedLabel] ++
            [Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.addi AbiReg.a1 AbiReg.zero 1#12,
             Asm.j retRestoreLabel] := rfl
        rw [hsp] at h
        simpa only [exPre, restTail, List.append_assoc] using h
      exact linkResolved_lbl_lm img.lkm exPre exhaustedLabel _ hlinkX }

theorem linkedCmpFnsLinked (img : LinkedCmpImage) :
    ProgFnsLinkedWithGen (linkedCmpEnv img) img.allocOf checkerProgMini :=
  ProgFnsLinkedWithGen.of_perm (applyOrderHint_perm img.fnOrder checkerProgMini)
    (checkerDriverAsm checkerTabMini ++ checkerCmpDriverAsm checkerTabMini) [] (by
      have h := img.hlink
      rw [linkedCmpChipAsm_eq img] at h
      change img.lkm.linkSpec
        ((checkerDriverAsm checkerTabMini ++ checkerCmpDriverAsm checkerTabMini) ++ linkedCmpFnsAsm img ++ []) =
        .ok (img.code, img.labels)
      simpa only [List.append_nil, List.append_assoc] using h)

noncomputable def checkerEnv : CodeEnvGen checkerLM :=
  let exPre := drvAllBeforeEx checkerTabMini
  let errPre := exPre ++ drvExhaustedStub
  let abPre := errPre ++ drvErrPrefix
  let restTail := drvInitSubAsm checkerTabMini ++ checkerCmpDriverAsm checkerTabMini ++ checkerFnsAsm
  { tab := checkerTabMini
    code := checkerCode
    labels := checkerLabels
    rom := checkerRom
    hrom := romOfArray_matchesCode checkerCode
    hcode64 := checkerCode_size64
    errTarget := checkerLM.totalSize errPre
    herrLbl := by
      have hlinkE : checkerLM.linkSpec (errPre ++ [Asm.lbl errLabel] ++
          ([Asm.addi AbiReg.a0 AbiReg.zero 0#12] ++ drvAbortPrefix ++
           drvRetRestoreStub checkerTabMini ++ restTail)) =
          .ok (checkerCode, checkerLabels) := by
        have h := checkerChipAsm_linkSpec
        rw [checkerChipAsm_eq, checkerDriverAsm_decomp] at h
        have hsp : drvErrPrefix = [Asm.lbl errLabel] ++ [Asm.addi AbiReg.a0 AbiReg.zero 0#12] := rfl
        rw [hsp] at h
        simpa only [errPre, exPre, restTail, List.append_assoc] using h
      exact linkResolved_lbl_lm checkerLM errPre errLabel _ hlinkE
    abortTarget := checkerLM.totalSize abPre
    habortLbl := by
      have hlinkA : checkerLM.linkSpec (abPre ++ [Asm.lbl abortLabel] ++
          ([Asm.addi AbiReg.a1 AbiReg.zero 2#12] ++ drvRetRestoreStub checkerTabMini ++ restTail)) =
          .ok (checkerCode, checkerLabels) := by
        have h := checkerChipAsm_linkSpec
        rw [checkerChipAsm_eq, checkerDriverAsm_decomp] at h
        have hsp : drvAbortPrefix = [Asm.lbl abortLabel] ++
            [Asm.addi AbiReg.a1 AbiReg.zero 2#12] := rfl
        rw [hsp] at h
        simpa only [abPre, errPre, exPre, restTail, List.append_assoc] using h
      exact linkResolved_lbl_lm checkerLM abPre abortLabel _ hlinkA
    exhaustedTarget := checkerLM.totalSize exPre
    hexhaustedLbl := by
      have hlinkX : checkerLM.linkSpec (exPre ++ [Asm.lbl exhaustedLabel] ++
          ([Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.addi AbiReg.a1 AbiReg.zero 1#12,
            Asm.j retRestoreLabel] ++
           drvErrPrefix ++ drvAbortPrefix ++ drvRetRestoreStub checkerTabMini ++ restTail)) =
          .ok (checkerCode, checkerLabels) := by
        have h := checkerChipAsm_linkSpec
        rw [checkerChipAsm_eq, checkerDriverAsm_decomp] at h
        have hsp : drvExhaustedStub = [Asm.lbl exhaustedLabel] ++
            [Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.addi AbiReg.a1 AbiReg.zero 1#12,
             Asm.j retRestoreLabel] := rfl
        rw [hsp] at h
        simpa only [exPre, restTail, List.append_assoc] using h
      exact linkResolved_lbl_lm checkerLM exPre exhaustedLabel _ hlinkX }

theorem checkerFnsLinked : ProgFnsLinkedGen checkerEnv checkerProgMini :=
  ProgFnsLinkedGen.of_perm (orderProgFns_perm checkerProgMini)
    (checkerDriverAsm checkerTabMini ++ checkerCmpDriverAsm checkerTabMini) [] (by
      have h := checkerChipAsm_linkSpec
      rw [checkerChipAsm_eq] at h
      change checkerLM.linkSpec
        ((checkerDriverAsm checkerTabMini ++ checkerCmpDriverAsm checkerTabMini) ++ checkerFnsAsm ++ []) =
        .ok (checkerCode, checkerLabels)
      simpa only [List.append_nil, List.append_assoc] using h)

/-! ### Static `checkerTabMini` Constants & `romWords` Bound -/

theorem t_nb : checkerTabMini.nb = 2 := rfl
theorem t_nw : checkerTabMini.nw = 203 := rfl
theorem t_nbuf : checkerTabMini.nbuf = 2 := by simp [Tab.nbuf, t_nb]
theorem t_nslot : checkerTabMini.nslot = 205 := by simp [Tab.nslot, Tab.slotOf, t_nb, t_nw, t_nbuf]
theorem t_nxres : checkerTabMini.nxres = 2 := rfl
theorem t_ng : checkerTabMini.ng = 12 := rfl
theorem t_nres : checkerTabMini.nres = 10 := rfl

theorem checkerTabMini_romBase_eq :
    checkerTabMini.romBase = ((16 + 24 * 205 : Nat) : Int) := by
  unfold Tab.romBase; rw [t_nb, t_nw]; rfl

theorem checkerTabMini_resBase_eq :
    checkerTabMini.resBase = ((16 + 24 * 205 + 8 * checkerTabMini.romWords : Nat) : Int) := by
  unfold Tab.resBase
  rw [checkerTabMini_romBase_eq, show (8 : Int) = ((8 : Nat) : Int) from rfl,
    ← Int.natCast_mul, ← Int.natCast_add]

theorem checkerTabMini_args_eq :
    checkerTabMini.args =
      ((16 + 24 * 205 + 8 * checkerTabMini.romWords + 8 * 2 + 8 * 12 : Nat) : Int) := by
  unfold Tab.args Tab.globBase
  rw [checkerTabMini_resBase_eq, t_nxres, t_ng, show (8 : Int) = ((8 : Nat) : Int) from rfl,
    ← Int.natCast_mul, ← Int.natCast_mul, ← Int.natCast_add, ← Int.natCast_add]
theorem t_arr0 : checkerTabMini.arrAt[0]? = some (.t0 inArr) := by decide
theorem t_arr1 : checkerTabMini.arrAt[1]? = some (.t0 pbArr) := by decide
theorem t_pos8_in : checkerTabMini.pos8 inArr = 0 := by decide
theorem t_pos8_pb : checkerTabMini.pos8 pbArr = 1 := by decide
theorem t_bin : checkerTabMini.bytePosOkB inArr = true := by decide
theorem t_bpb : checkerTabMini.bytePosOkB pbArr = true := by decide
theorem t_pos_out : checkerTabMini.pos64 (.t0 L.Arena.OUT) = 180 := rfl
theorem t_pos_hdrf : checkerTabMini.pos64 (.t0 L.Arena.HDRF) = 181 := rfl
theorem t_pos_ctlf : checkerTabMini.pos64 (.t0 L.Arena.CTLF) = 182 := rfl
theorem t_word_out : checkerTabMini.wordPosOkB (.t0 L.Arena.OUT) = true := rfl
theorem t_word_hdrf : checkerTabMini.wordPosOkB (.t0 L.Arena.HDRF) = true := rfl
theorem t_word_ctlf : checkerTabMini.wordPosOkB (.t0 L.Arena.CTLF) = true := rfl
theorem t_bs_out : phaseBSMini (.t0 L.Arena.OUT) = false := rfl
theorem t_bs_hdrf : phaseBSMini (.t0 L.Arena.HDRF) = false := rfl
theorem t_bs_ctlf : phaseBSMini (.t0 L.Arena.CTLF) = false := rfl

theorem checkerTabMini_bytePos_cases {a : ArrId}
    (ha : checkerTabMini.bytePosOkB a = true) : a = inArr ∨ a = pbArr := by
  have hlt := Tab.bytePosOk_lt ha
  rw [t_nb] at hlt
  have hp : checkerTabMini.pos8 a = 0 ∨ checkerTabMini.pos8 a = 1 := by omega
  rcases hp with h0 | h1
  · left
    have ha0 := hlt.2.2.2
    rw [h0, t_arr0] at ha0
    exact Option.some.inj ha0 |> fun h => by cases h; rfl
  · right
    have ha1 := hlt.2.2.2
    rw [h1, t_arr1] at ha1
    exact Option.some.inj ha1 |> fun h => by cases h; rfl

theorem checkerTabMini_wordPos_bounds {s : TieredArray}
    (hs : checkerTabMini.wordPosOkB s = true) :
    2 ≤ checkerTabMini.pos64 s ∧ checkerTabMini.pos64 s < 205 := by
  have hlt := Tab.wordPosOk_lt hs
  rw [t_nb, t_nw] at hlt
  exact ⟨hlt.1, hlt.2.1⟩

theorem romWords64_length (bs : List UInt8) :
    (romWords64 bs).length = (bs.length + 7) / 8 := by
  match bs with
  | [] => simp [romWords64]
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: rest =>
    simp only [romWords64, List.length_cons]
    rw [romWords64_length rest]; omega
  | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _] | [_, _, _, _, _, _, _] =>
    simp [romWords64]

private theorem storeMemOff_size_ge (lkm : LinkModel) (op : StoreOp) (base rs tmp : Reg) (off : Int) :
    1 ≤ lkm.totalSize (storeMemOff op base rs tmp off) := by
  dsimp only [storeMemOff]
  split
  · simp only [Asm.raw, lkm.totalSize_instr, Nat.le_refl]
  · split
    · simp only [lkm.totalSize_cons, lkm.totalSize_nil,
        Asm.addi, Asm.raw, lkm.itemSize_instr]; omega
    · split
      · simp only [lkm.totalSize_cons, lkm.totalSize_nil,
          Asm.add, Asm.raw, lkm.itemSize_instr]; omega
      · simp only [lkm.totalSize_append, lkm.totalSize_cons,
          lkm.totalSize_nil, Asm.add, Asm.raw, lkm.itemSize_instr]; omega

private theorem drvRomStoresGo_size_ge (lkm : LinkModel) (romBase : Int) (idx : Nat) (ws : List (BitVec 64)) :
    ws.length ≤ lkm.totalSize (drvRomStoresGo romBase idx ws) := by
  induction ws generalizing idx with
  | nil => simp [drvRomStoresGo]
  | cons w ws ih =>
    simp only [drvRomStoresGo, List.length_cons, lkm.totalSize_append]
    have h1 := storeMemOff_size_ge lkm .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (romBase + 8 * (idx : Int))
    have hih := ih (idx + 1)
    omega

theorem checkerTabMini_romWords_lt : checkerTabMini.romWords < 2 ^ 22 := by
  have htot := checkerChipAsm_farTotalWords_lt
  have hle : checkerLM.totalSize checkerChipAsm ≤ farTotalWords checkerChipAsm :=
    hybrid_totalSize_le_far _ checkerChipAsm
  have hromSub : checkerLM.totalSize (drvRomStoresGo checkerTabMini.romBase 0 (romWords64 checkerTabMini.rom)) ≤
      checkerLM.totalSize checkerChipAsm := by
    rw [checkerChipAsm_eq, checkerDriverAsm_decomp, drvInitSubAsm_decomp]
    dsimp only [drvInitBody]
    simp only [checkerLM.totalSize_append]
    omega
  have hlen := drvRomStoresGo_size_ge checkerLM checkerTabMini.romBase 0 (romWords64 checkerTabMini.rom)
  rw [romWords64_length] at hlen
  change checkerTabMini.romWords ≤ _ at hlen
  omega

theorem checkerTabMini_args_lt : checkerTabMini.args.toNat + 8 ≤ abiSlot := by
  have hr := checkerTabMini_romWords_lt
  rw [checkerTabMini_args_eq, Int.toNat_natCast]
  simp only [abiSlot]
  omega

theorem checkerTabMini_abiNeed_eq :
    abiNeed checkerTabMini = 205 * abiSlot := by
  simp [abiNeed, t_nslot, Nat.mul_comm]

theorem checkerTabMini_saveBase_eq :
    checkerTabMini.saveBase 0 = checkerTabMini.args + 8 := by
  simp [Tab.saveBase]

theorem checkerTabMini_saveBase_nonneg :
    0 ≤ checkerTabMini.saveBase 0 := by
  rw [checkerTabMini_saveBase_eq, checkerTabMini_args_eq]
  omega

theorem checkerTabMini_saveBase_le_abiSlot :
    checkerTabMini.saveBase 0 + 128 ≤ (abiSlot : Int) := by
  have hr := checkerTabMini_romWords_lt
  rw [checkerTabMini_saveBase_eq, checkerTabMini_args_eq]
  simp only [abiSlot]
  omega

/-- Caller-saved registers stored in `regionBase + checkerTabMini.saveBase 0` across LP64 driver calls. -/
def DrvRegsSaved (regionBase : BitVec 64) (initSt : RV64.State) (m : ByteMem) : Prop :=
  ∀ i (hi : i < callerSaveRegs.length),
    readWord64 m (regionBase + BitVec.ofInt 64 (checkerTabMini.saveBase 0) + BitVec.ofNat 64 (8 * i)) =
      initSt.getReg (callerSaveRegs[i]'hi)

theorem checkerTabMini_saveBase_align (regionBase : BitVec 64)
    (hAlign : isAligned regionBase 8 = true) :
    isAligned (regionBase + BitVec.ofInt 64 (checkerTabMini.saveBase 0)) 8 = true := by
  have hcast : checkerTabMini.saveBase 0 =
      ((8 * ((2 + 3 * (checkerTabMini.nb + checkerTabMini.nw) + checkerTabMini.romWords +
        checkerTabMini.nxres + checkerTabMini.ng + max 1 0 : Nat) : Int))) := by
    simp only [Tab.saveBase, Tab.args, Tab.globBase, Tab.resBase, Tab.romBase, Int.ofNat_eq_natCast]
    omega
  rw [hcast]
  exact isAligned8_add_int_mul8 regionBase hAlign _

theorem checkerTabMini_saveBase_valid (regionBase : BitVec 64)
    (hNeed : regionBase.toNat + abiNeed checkerTabMini ≤ 2 ^ 64) :
    (regionBase + BitVec.ofInt 64 (checkerTabMini.saveBase 0)).toNat + 128 ≤ 2 ^ 64 := by
  have hnn := checkerTabMini_saveBase_nonneg
  have hcoe : ((checkerTabMini.saveBase 0).toNat : Int) = checkerTabMini.saveBase 0 :=
    Int.toNat_of_nonneg hnn
  have hleSlot := checkerTabMini_saveBase_le_abiSlot
  have hNeedEq : abiNeed checkerTabMini = 205 * abiSlot := checkerTabMini_abiNeed_eq
  have hSlotLe : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; omega
  have hle128 : (checkerTabMini.saveBase 0).toNat + 128 ≤ abiNeed checkerTabMini := by omega
  have hcast : BitVec.ofInt 64 (checkerTabMini.saveBase 0) =
      BitVec.ofNat 64 (checkerTabMini.saveBase 0).toNat := by
    rw [← BitVec.ofInt_natCast, hcoe]
  rw [hcast, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem drvRegsSaved_of_memEqOutside {regionBase : BitVec 64} {initSt : RV64.State}
    {s : MemSpan} {m1 m2 : ByteMem}
    (heq : MemEqOutside s m1 m2)
    (hdisj : ∀ i, i < callerSaveRegs.length → ∀ k, k < 8 →
      ¬s.contains (regionBase + BitVec.ofInt 64 (checkerTabMini.saveBase 0) +
        BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 k))
    (hsaved : DrvRegsSaved regionBase initSt m1) :
    DrvRegsSaved regionBase initSt m2 := by
  intro i hi
  rw [← hsaved i hi]
  apply loadBytes_congr
  intro k hk
  exact heq _ (hdisj i hi k hk)

theorem drvRegsSaved_of_writeWord64 {regionBase : BitVec 64} {initSt : RV64.State}
    {m : ByteMem} (waddr wval : BitVec 64)
    (hdisj : ∀ i, i < callerSaveRegs.length → ∀ k, k < 8 →
      ∀ j, j < 8 →
        regionBase + BitVec.ofInt 64 (checkerTabMini.saveBase 0) +
          BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 k ≠ waddr + BitVec.ofNat 64 j)
    (hsaved : DrvRegsSaved regionBase initSt m) :
    DrvRegsSaved regionBase initSt (writeWord64 m waddr wval) := by
  have hme : MemEqOutside { base := waddr, size := 8 } m (writeWord64 m waddr wval) :=
    MemEqOutside.writeWord64 m waddr wval fun k hk => ⟨k, hk, rfl⟩
  exact drvRegsSaved_of_memEqOutside hme
    (fun i hi k hk ⟨j, hj, hEq⟩ => hdisj i hi k hk j hj hEq)
    hsaved

theorem drvRegsSaved_of_callWriteMask {L : ProgLayout checkerTabMini} {initSt : RV64.State}
    {m1 m2 : ByteMem} (callerSp : BitVec 64)
    (hTabSave : checkerTabMini.saveBase 0 + 128 ≤ (L.tabBytes : Int))
    (hMask : ProgMemOutside (CallWriteMask L callerSp) m1 m2)
    (hsaved : DrvRegsSaved L.T initSt m1) :
    DrvRegsSaved L.T initSt m2 := by
  intro i hi
  rw [← hsaved i hi]
  apply hMask.readWord64_eq
  intro k hk
  apply saveArea_not_callWriteMask L 0 callerSp hTabSave
  refine ⟨8 * i + k, ?_, ?_⟩
  · dsimp only [callerSaveSpan]
    have hlen : callerSaveRegs.length = 16 := rfl
    omega
  · dsimp only [callerSaveSpan]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Initial `_root_.L.Mem` for Phase A (`MODE = 3`), with every word array sized to `abiWords`. -/
def phaseAInitMem (inBytes pins : ByteArray) : _root_.L.Mem :=
  loadMemMini inBytes pins (fun _ => abiWords) 3

/-- Phase B `_root_.L.Mem` constructed deterministically from Phase A's final memory `m₁`
    and return code `retA`: freezes `OUT` header into `HDRF`, clears `OUT`/`CTLF`,
    and sets `PHI = retA - 2^63`, `PLO = 0`, `MODE = 2`. -/
def phaseBMem (m₁ : _root_.L.Mem) (retA : _root_.L.Word) : _root_.L.Mem :=
  { bytes := m₁.bytes
    words := fun s =>
      if s = .t0 L.Arena.OUT then #[]
      else if s = .t0 L.Arena.CTLF then #[]
      else if s = .t0 L.Arena.HDRF then (m₁.words (.t0 L.Arena.OUT)).extract 0 L.Arena.hdrW
      else m₁.words s
    glob := fun g =>
      if g = phiGVar then retA - 9223372036854775808
      else if g = ploGVar then 0
      else if g = modeGVar then 2
      else m₁.glob g }

/-- Deterministic Phase B entry memory as a function of `(inBytes, pins)`. -/
def phaseBInitMem (inBytes pins : ByteArray) : _root_.L.Mem :=
  match runB checkerProgMini (abiFuel - 1) "check" [] (phaseAInitMem inBytes pins) with
  | .ok (rs₁, m₁, _) => phaseBMem m₁ (rs₁.headD 0)
  | .error _ => default

/-- Initial `_root_.L.Mem` for comparator Mode 4 (`check_c1`), with every word array sized to `abiWords`. -/
def cmpPhase4Mem (chalBytes pins : ByteArray) : _root_.L.Mem :=
  cmpM4SzMini (fun _ => abiWords) chalBytes pins

/-- Comparator Mode 5 `_root_.L.Mem` constructed from Mode 4's final memory `m4` and `solBytes`. -/
def cmpPhase5Mem (m4 : _root_.L.Mem) (solBytes : ByteArray) : _root_.L.Mem :=
  cmpM5Mini m4 solBytes

/-- Deterministic comparator Mode 5 entry memory as a function of `(chalBytes, solBytes, pins)`. -/
def cmpPhase5InitMem (chalBytes solBytes pins : ByteArray) : _root_.L.Mem :=
  match runB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase4Mem chalBytes pins) with
  | .ok (_, m4, _) => cmpPhase5Mem m4 solBytes
  | .error _ => default

/-- Comparator Mode 6 `_root_.L.Mem` constructed from Mode 5's final memory `m5`: `MODE := 6`. -/
def cmpPhase6Mem (m5 : _root_.L.Mem) : _root_.L.Mem :=
  m5.setG modeGVar 6

/-- Deterministic comparator Mode 6 entry memory as a function of `(chalBytes, solBytes, pins)`. -/
def cmpPhase6InitMem (chalBytes solBytes pins : ByteArray) : _root_.L.Mem :=
  match runB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase5InitMem chalBytes solBytes pins) with
  | .ok (_, m5, _) => cmpPhase6Mem m5
  | .error _ => default

/-- Comparator Mode 8 `_root_.L.Mem` constructed from Mode 6's final memory `m6` and Mode 5's return `ret5`:
    clears `OUT`/`CTLF` word arrays, freezes `hdrHw` words of `OUT` into `HDRF`, preserves `bytes`,
    and sets `PHI = ret5 - 2^63`, `PLO = 0`, `MODE = 8`. -/
def cmpPhase8Mem (m6 : _root_.L.Mem) (ret5 : _root_.L.Word) : _root_.L.Mem :=
  { bytes := m6.bytes
    words := fun s =>
      if s = .t0 L.Arena.OUT then #[]
      else if s = .t0 L.Arena.CTLF then #[]
      else if s = .t0 L.Arena.HDRF then (m6.words (.t0 L.Arena.OUT)).extract 0 hdrHw
      else m6.words s
    glob := fun g =>
      if g = phiGVar then ret5 - 9223372036854775808
      else if g = ploGVar then 0
      else if g = modeGVar then 8
      else m6.glob g }

/-- Deterministic comparator Mode 8 entry memory as a function of `(chalBytes, solBytes, pins)`. -/
def cmpPhase8InitMem (chalBytes solBytes pins : ByteArray) : _root_.L.Mem :=
  match runB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase5InitMem chalBytes solBytes pins) with
  | .ok (rs5, _, _) =>
    match runB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase6InitMem chalBytes solBytes pins) with
    | .ok (_, m6, _) => cmpPhase8Mem m6 (rs5.headD 0)
    | .error _ => default
  | .error _ => default

/-- Comparator Mode 9 `_root_.L.Mem` constructed from Mode 8's final memory `m8` and Mode 6's return `ret6`:
    `PHI = ret6 - 2^63`, `PLO = 0`, `MODE = 9`. -/
def cmpPhase9Mem (m8 : _root_.L.Mem) (ret6 : _root_.L.Word) : _root_.L.Mem :=
  seqNextMini m8 modeGVar ploGVar phiGVar 9 0 (ret6 - 9223372036854775808)

/-- Deterministic comparator Mode 9 entry memory as a function of `(chalBytes, solBytes, pins)`. -/
def cmpPhase9InitMem (chalBytes solBytes pins : ByteArray) : _root_.L.Mem :=
  match runB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase6InitMem chalBytes solBytes pins) with
  | .ok (rs6, _, _) =>
    match runB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase8InitMem chalBytes solBytes pins) with
    | .ok (_, m8, _) => cmpPhase9Mem m8 (rs6.headD 0)
    | .error _ => default
  | .error _ => default

/-! ## 2. RV64 Return Determinism, Exit-Stub Return Lemmas, and `MiniL` Array-Size Preservation -/

theorem step_trap_of_rom_none (rom : RV64.Rom) (st : RV64.State)
    (hNone : rom (st.pc.toNat / 4) = none) :
    RV64.step rom st = .trap := by
  unfold RV64.step
  split <;> simp [hNone]

theorem run_trap_of_step_trap (rom : RV64.Rom) (st : RV64.State)
    (htrap : RV64.step rom st = .trap) :
    ∀ k, RV64.run rom (k + 1) st = .trap := by
  intro k
  simp only [RV64.run, htrap]

theorem run_ret_deterministic (rom : RV64.Rom) :
    ∀ (m n : Nat) (st : RV64.State) {r₁ r₂ : RV64.State} {retPc : BitVec 64},
      RV64.run rom m st = .cont r₁ →
      RV64.run rom n st = .cont r₂ →
      r₁.pc = retPc →
      r₂.pc = retPc →
      rom (retPc.toNat / 4) = none →
      r₁ = r₂ := by
  intro m
  induction m with
  | zero =>
    intro n st r₁ r₂ retPc hm hn hpc1 _ hOut
    change (StepResult.cont st = StepResult.cont r₁) at hm
    cases hm
    cases n with
    | zero =>
      change (StepResult.cont st = StepResult.cont r₂) at hn
      cases hn; rfl
    | succ n =>
      have htrap : RV64.step rom st = .trap :=
        step_trap_of_rom_none rom st (by simpa [hpc1] using hOut)
      simp only [RV64.run, htrap] at hn
      cases hn
  | succ m ih =>
    intro n st r₁ r₂ retPc hm hn hpc1 hpc2 hOut
    cases n with
    | zero =>
      change (StepResult.cont st = StepResult.cont r₂) at hn
      cases hn
      have htrap : RV64.step rom st = .trap :=
        step_trap_of_rom_none rom st (by simpa [hpc2] using hOut)
      simp only [RV64.run, htrap] at hm
      cases hm
    | succ n =>
      simp only [RV64.run] at hm hn
      cases hstep : RV64.step rom st with
      | cont st' =>
        rw [hstep] at hm hn
        exact ih n st' hm hn hpc1 hpc2 hOut
      | trap => rw [hstep] at hm; cases hm

theorem run_cont_ret (rom : RV64.Rom) :
    ∀ (k fuel : Nat) (st r x : RV64.State) {retPc : BitVec 64},
      RV64.run rom k st = .cont r →
      RV64.run rom fuel st = .cont x →
      x.pc = retPc →
      rom (retPc.toNat / 4) = none →
      ∃ rem, RV64.run rom rem r = .cont x := by
  intro k
  induction k with
  | zero =>
    intro fuel st r x _ hk hf _ _
    change (StepResult.cont st = StepResult.cont r) at hk
    cases hk; exact ⟨fuel, hf⟩
  | succ k ih =>
    intro fuel st r x retPc hk hf hxPc hRetOut
    cases fuel with
    | zero =>
      change (StepResult.cont st = StepResult.cont x) at hf
      cases hf
      have htrap : RV64.step rom st = .trap :=
        step_trap_of_rom_none rom st (by simpa [hxPc] using hRetOut)
      simp only [RV64.run, htrap] at hk
      cases hk
    | succ fuel =>
      simp only [RV64.run] at hk hf
      cases hstep : RV64.step rom st with
      | cont st' =>
        rw [hstep] at hk hf
        exact ih fuel st' r x hk hf hxPc hRetOut
      | trap => rw [hstep] at hk; cases hk

theorem ret_ne_of_cont {rom : RV64.Rom} {fuel k : Nat} {st r x : RV64.State}
    {retPc a1 : BitVec 64}
    (hcont : RV64.run rom k st = .cont r)
    (hrun : RV64.run rom fuel st = .cont x)
    (hxPc : x.pc = retPc)
    (hRetOut : rom (retPc.toNat / 4) = none)
    (hreach : ∃ m r', RV64.run rom m r = .cont r' ∧ r'.pc = retPc ∧ r'.getReg AbiReg.a1 = a1)
    (hne : a1 ≠ x.getReg AbiReg.a1) : False := by
  obtain ⟨rem, hrem⟩ := run_cont_ret rom k fuel st r x hcont hrun hxPc hRetOut
  obtain ⟨m, r', hm, hrPc, ha1⟩ := hreach
  have heq := run_ret_deterministic rom m rem r hm hrem hrPc hxPc hRetOut
  exact hne (ha1.symm.trans (congrArg (fun s => s.getReg AbiReg.a1) heq))

theorem checker_retRestore_returns {lkm : LinkModel} (env : CodeEnvGen lkm)
    (pre tail : List AsmItem) (initSt : RV64.State) (T : BitVec 64)
    (halign : isAligned (T + BitVec.ofInt 64 (env.tab.saveBase 0)) 8 = true)
    (hlink : lkm.linkSpec (pre ++ drvRetRestoreStub env.tab ++ tail) =
      .ok (env.code, env.labels))
    (st : RV64.State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = T)
    (hsaved : ∀ i (hi : i < callerSaveRegs.length),
      readWord64 st.mem (T + BitVec.ofInt 64 (env.tab.saveBase 0) + BitVec.ofNat 64 (8 * i)) =
        initSt.getReg (callerSaveRegs[i]'hi)) :
    ∃ m r',
      RV64.run env.rom m st = .cont r' ∧
      r'.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64) ∧
      RegsRestored initSt r' ∧
      r'.getReg AbiReg.ra = initSt.getReg AbiReg.ra ∧
      (∀ r, r ≠ AbiReg.t0 → r ≠ AbiReg.t1 → r ∉ callerSaveRegs → r'.getReg r = st.getReg r) ∧
      r'.mem = st.mem := by
  let p0 := pre ++ [Asm.lbl retRestoreLabel]
  have hpc0 : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize p0) := by
    simpa only [p0, lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero] using hpc
  have hl1 : lkm.linkSpec (p0 ++ callerRestoreRetAsm AbiReg.gp (env.tab.saveBase 0) ++ tail) =
      .ok (env.code, env.labels) := by
    simpa only [p0, drvRetRestoreStub, List.append_assoc] using hlink
  exact callerRestoreRet_sim env AbiReg.gp (by decide) (by decide) (env.tab.saveBase 0) T initSt
    halign p0 tail hl1 st hpc0 hgp hsaved

def drvInitPre (tab : Tab) : List AsmItem :=
  drvPreDone tab ++ drvDoneStub ++ drvExhaustedStub ++
  drvErrPrefix ++ drvAbortPrefix ++ drvRetRestoreStub tab

theorem checkerChipAsm_linkSpec_decomp :
    checkerLM.linkSpec
      (drvPreDone checkerTabMini ++ drvDoneStub ++ drvExhaustedStub ++
       drvErrPrefix ++ drvAbortPrefix ++ drvRetRestoreStub checkerTabMini ++
       drvInitSubAsm checkerTabMini ++
       checkerCmpDriverAsm checkerTabMini ++ checkerFnsAsm) =
      .ok (checkerEnv.code, checkerEnv.labels) := by
  have h := checkerChipAsm_linkSpec
  rw [checkerChipAsm_eq, checkerDriverAsm_decomp, drvAllBeforeEx] at h
  change checkerLM.linkSpec _ = .ok (checkerCode, checkerLabels)
  simpa only [List.append_assoc] using h

theorem linkedCmpChipAsm_linkSpec_decomp (img : LinkedCmpImage) :
    img.lkm.linkSpec
      (drvPreDone checkerTabMini ++ drvDoneStub ++ drvExhaustedStub ++
       drvErrPrefix ++ drvAbortPrefix ++ drvRetRestoreStub checkerTabMini ++
       drvInitSubAsm checkerTabMini ++
       checkerCmpDriverAsm checkerTabMini ++ linkedCmpFnsAsm img) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
  have h := img.hlink
  rw [linkedCmpChipAsm_eq img, checkerDriverAsm_decomp, drvAllBeforeEx] at h
  change img.lkm.linkSpec _ = .ok (img.code, img.labels)
  simpa only [List.append_assoc] using h

theorem checker_drvInit_lbl :
    lookupLabel checkerEnv.labels drvInitLabel =
      some (checkerLM.totalSize (drvInitPre checkerTabMini)) := by
  have h := checkerChipAsm_linkSpec_decomp
  rw [drvInitSubAsm_decomp] at h
  exact linkResolved_lbl_lm checkerLM (drvInitPre checkerTabMini) drvInitLabel _
    (by simpa only [drvInitPre, List.append_assoc] using h)

theorem linkedCmp_drvInit_lbl (img : LinkedCmpImage) :
    lookupLabel (linkedCmpEnv img).labels drvInitLabel =
      some (img.lkm.totalSize (drvInitPre checkerTabMini)) := by
  have h := linkedCmpChipAsm_linkSpec_decomp img
  rw [drvInitSubAsm_decomp] at h
  exact linkResolved_lbl_lm img.lkm (drvInitPre checkerTabMini) drvInitLabel _
    (by simpa only [drvInitPre, List.append_assoc] using h)

private theorem checkerEnv_exhaustedTarget_eq :
    checkerEnv.exhaustedTarget = checkerLM.totalSize (drvAllBeforeEx checkerTabMini) := rfl

private theorem checkerEnv_errTarget_eq :
    checkerEnv.errTarget =
      checkerLM.totalSize (drvAllBeforeEx checkerTabMini ++ drvExhaustedStub) := rfl

private theorem checkerEnv_abortTarget_eq :
    checkerEnv.abortTarget =
      checkerLM.totalSize (drvAllBeforeEx checkerTabMini ++ drvExhaustedStub ++ drvErrPrefix) := rfl

private theorem linkedCmpEnv_exhaustedTarget_eq (img : LinkedCmpImage) :
    (linkedCmpEnv img).exhaustedTarget = img.lkm.totalSize (drvAllBeforeEx checkerTabMini) := rfl

private theorem linkedCmpEnv_errTarget_eq (img : LinkedCmpImage) :
    (linkedCmpEnv img).errTarget =
      img.lkm.totalSize (drvAllBeforeEx checkerTabMini ++ drvExhaustedStub) := rfl

private theorem linkedCmpEnv_abortTarget_eq (img : LinkedCmpImage) :
    (linkedCmpEnv img).abortTarget =
      img.lkm.totalSize (drvAllBeforeEx checkerTabMini ++ drvExhaustedStub ++ drvErrPrefix) := rfl

theorem inline_decline_returns {lkm : LinkModel} (env : CodeEnvGen lkm)
    (pre tail : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ [Asm.addi AbiReg.a0 AbiReg.zero 0#12,
        Asm.addi AbiReg.a1 AbiReg.zero 1#12, Asm.ret] ++ tail) =
      .ok (env.code, env.labels))
    (st : RV64.State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre)) :
    ∃ m r',
      RV64.run env.rom m st = .cont r' ∧
      r'.pc = (st.getReg AbiReg.ra &&& ~~~1#64) ∧
      r'.getReg AbiReg.a0 = 0#64 ∧
      r'.getReg AbiReg.a1 = 1#64 ∧
      (∀ q, q ≠ AbiReg.a0 → q ≠ AbiReg.a1 → r'.getReg q = st.getReg q) ∧
      r'.mem = st.mem := by
  have hl1 : lkm.linkSpec (pre ++ [Asm.addi AbiReg.a0 AbiReg.zero 0#12] ++
      ([Asm.addi AbiReg.a1 AbiReg.zero 1#12, Asm.ret] ++ tail)) =
      .ok (env.code, env.labels) := by
    simpa only [List.cons_append, List.nil_append, List.append_assoc] using hlink
  obtain ⟨hr1, hpc1, ha0_1, hoth1, hmem1⟩ :=
    run_aluImm_rd_step env pre _ .addi AbiReg.a0 AbiReg.zero 0#12 (by decide) hl1 st hpc
  let s1 := stepReg st AbiReg.a0 (evalAluImm .addi (st.getReg AbiReg.zero) 0#12)
    (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
  let p1 := pre ++ [Asm.addi AbiReg.a0 AbiReg.zero 0#12]
  have hpc1' : s1.pc = BitVec.ofNat 64 (4 * lkm.totalSize p1) := by
    simpa only [p1, lkm.totalSize_append, Asm.addi, lkm.totalSize_instr] using hpc1
  have hl2 : lkm.linkSpec (p1 ++ [Asm.addi AbiReg.a1 AbiReg.zero 1#12] ++
      ([Asm.ret] ++ tail)) =
      .ok (env.code, env.labels) := by
    simpa only [p1, List.cons_append, List.nil_append, List.append_assoc] using hl1
  obtain ⟨hr2, hpc2, ha1_2, hoth2, hmem2⟩ :=
    run_aluImm_rd_step env p1 _ .addi AbiReg.a1 AbiReg.zero 1#12 (by decide) hl2 s1 hpc1'
  let s2 := stepReg s1 AbiReg.a1 (evalAluImm .addi (s1.getReg AbiReg.zero) 1#12)
    (BitVec.ofNat 64 (4 * (lkm.totalSize p1 + 1)))
  let p2 := p1 ++ [Asm.addi AbiReg.a1 AbiReg.zero 1#12]
  have hpc2' : s2.pc = BitVec.ofNat 64 (4 * lkm.totalSize p2) := by
    simpa only [p2, lkm.totalSize_append, Asm.addi, lkm.totalSize_instr] using hpc2
  have hl3 : lkm.linkSpec (p2 ++ [Asm.ret] ++ tail) = .ok (env.code, env.labels) := by
    simpa only [p2, List.cons_append, List.nil_append, List.append_assoc] using hl2
  have h64 := linkResolved_sub_pc64 env p2 [Asm.ret] tail hl3
  have hlt : 4 * lkm.totalSize p2 < 2 ^ 64 := by
    have htw : lkm.totalSize [Asm.ret] = 1 := by simp [Asm.ret, lkm.totalSize_instr]
    rw [htw] at h64; omega
  have hstepRet := step_item_ret_lm lkm env.hrom p2 tail hl3 hlt s2 hpc2'
  have hr3 : RV64.run env.rom 1 s2 = .cont { s2 with pc := s2.getReg AbiReg.ra &&& ~~~1#64 } := by
    simp only [RV64.run, hstepRet]
  have hrun : RV64.run env.rom (1 + 1 + 1) st =
      .cont { s2 with pc := s2.getReg AbiReg.ra &&& ~~~1#64 } := by
    rw [run_add, run_add, hr1]; dsimp only; rw [hr2]; exact hr3
  have ha0Eq : s2.getReg AbiReg.a0 = 0#64 := by
    rw [hoth2 _ (by decide), ha0_1]
    change st.getReg AbiReg.zero + sextImm12 0#12 = 0#64; rw [getReg_zero]; decide
  have ha1Eq : s2.getReg AbiReg.a1 = 1#64 := by
    rw [ha1_2]
    change s1.getReg AbiReg.zero + sextImm12 1#12 = 1#64; rw [getReg_zero]; decide
  have hraEq : s2.getReg AbiReg.ra = st.getReg AbiReg.ra :=
    (hoth2 _ (by decide)).trans (hoth1 _ (by decide))
  refine ⟨3, { s2 with pc := s2.getReg AbiReg.ra &&& ~~~1#64 }, hrun, ?_, ha0Eq, ha1Eq, ?_, ?_⟩
  · change (s2.getReg AbiReg.ra &&& ~~~1#64) = (st.getReg AbiReg.ra &&& ~~~1#64)
    rw [hraEq]
  · intro q hq0 hq1
    exact (hoth2 q hq1).trans (hoth1 q hq0)
  · exact hmem2.trans hmem1

private theorem checker_exhausted_stub_returns {lkm : LinkModel} (env : CodeEnvGen lkm)
    (pre tail : List AsmItem) (initSt : RV64.State) (T : BitVec 64)
    (halign : isAligned (T + BitVec.ofInt 64 (env.tab.saveBase 0)) 8 = true)
    (hlink : lkm.linkSpec (pre ++ drvExhaustedStub ++ drvErrPrefix ++ drvAbortPrefix ++
      drvRetRestoreStub env.tab ++ tail) = .ok (env.code, env.labels))
    (st : RV64.State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = T)
    (hsaved : ∀ i (hi : i < callerSaveRegs.length),
      readWord64 st.mem (T + BitVec.ofInt 64 (env.tab.saveBase 0) + BitVec.ofNat 64 (8 * i)) =
        initSt.getReg (callerSaveRegs[i]'hi)) :
    ∃ m r',
      RV64.run env.rom m st = .cont r' ∧
      r'.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64) ∧
      RegsRestored initSt r' ∧
      r'.getReg AbiReg.ra = initSt.getReg AbiReg.ra ∧
      r'.getReg AbiReg.a0 = 0#64 ∧
      r'.getReg AbiReg.a1 = 1#64 ∧
      r'.mem = st.mem := by
  let p0 := pre ++ [Asm.lbl exhaustedLabel]
  have hpc0 : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize p0) := by
    simpa only [p0, lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero] using hpc
  have hl1 : lkm.linkSpec (p0 ++ [Asm.addi AbiReg.a0 AbiReg.zero 0#12] ++
      ([Asm.addi AbiReg.a1 AbiReg.zero 1#12, Asm.j retRestoreLabel] ++
       drvErrPrefix ++ drvAbortPrefix ++ drvRetRestoreStub env.tab ++ tail)) =
      .ok (env.code, env.labels) := by
    simpa only [p0, drvExhaustedStub, List.cons_append, List.nil_append, List.append_assoc] using hlink
  obtain ⟨hr1, hpc1, ha0_1, hoth1, hmem1⟩ :=
    run_aluImm_rd_step env p0 _ .addi AbiReg.a0 AbiReg.zero 0#12 (by decide) hl1 st hpc0
  let s1 := stepReg st AbiReg.a0 (evalAluImm .addi (st.getReg AbiReg.zero) 0#12)
    (BitVec.ofNat 64 (4 * (lkm.totalSize p0 + 1)))
  let p1 := p0 ++ [Asm.addi AbiReg.a0 AbiReg.zero 0#12]
  have hpc1' : s1.pc = BitVec.ofNat 64 (4 * lkm.totalSize p1) := by
    simpa only [p1, lkm.totalSize_append, Asm.addi, lkm.totalSize_instr] using hpc1
  have hl2 : lkm.linkSpec (p1 ++ [Asm.addi AbiReg.a1 AbiReg.zero 1#12] ++
      ([Asm.j retRestoreLabel] ++ drvErrPrefix ++ drvAbortPrefix ++
       drvRetRestoreStub env.tab ++ tail)) =
      .ok (env.code, env.labels) := by
    simpa only [p1, List.cons_append, List.nil_append, List.append_assoc] using hl1
  obtain ⟨hr2, hpc2, ha1_2, hoth2, hmem2⟩ :=
    run_aluImm_rd_step env p1 _ .addi AbiReg.a1 AbiReg.zero 1#12 (by decide) hl2 s1 hpc1'
  let s2 := stepReg s1 AbiReg.a1 (evalAluImm .addi (s1.getReg AbiReg.zero) 1#12)
    (BitVec.ofNat 64 (4 * (lkm.totalSize p1 + 1)))
  let p2 := p1 ++ [Asm.addi AbiReg.a1 AbiReg.zero 1#12]
  have hpc2' : s2.pc = BitVec.ofNat 64 (4 * lkm.totalSize p2) := by
    simpa only [p2, lkm.totalSize_append, Asm.addi, lkm.totalSize_instr] using hpc2
  have hl3 : lkm.linkSpec (p2 ++ [Asm.j retRestoreLabel] ++
      (drvErrPrefix ++ drvAbortPrefix ++ drvRetRestoreStub env.tab ++ tail)) =
      .ok (env.code, env.labels) := by
    simpa only [p2, List.cons_append, List.nil_append, List.append_assoc] using hl2
  let retPre := pre ++ drvExhaustedStub ++ drvErrPrefix ++ drvAbortPrefix
  have hlinkRetLbl : lkm.linkSpec (retPre ++ [Asm.lbl retRestoreLabel] ++
      (callerRestoreRetAsm AbiReg.gp (env.tab.saveBase 0) ++ tail)) =
      .ok (env.code, env.labels) := by
    simpa only [retPre, drvRetRestoreStub, List.append_assoc] using hlink
  have htgt := linkResolved_lbl_lm lkm retPre retRestoreLabel _ hlinkRetLbl
  have h64J : 4 * (lkm.totalSize p2 + lkm.itemSize (.j retRestoreLabel)) < 2 ^ 64 := by
    simpa [Asm.j, lkm.totalSize_singleton] using
      linkResolved_sub_pc64 env p2 [Asm.j retRestoreLabel] _ hl3
  obtain ⟨kJ, s3, hrunJ, hpc3, hothJ, _, hmemJ⟩ :=
    prog_step_j env p2 _ retRestoreLabel (lkm.totalSize retPre) htgt hl3 h64J s2 hpc2'
  have hlinkRet : lkm.linkSpec (retPre ++ drvRetRestoreStub env.tab ++ tail) =
      .ok (env.code, env.labels) := by
    simpa only [retPre, List.append_assoc] using hlink
  have hgp3 : s3.getReg AbiReg.gp = T :=
    (hothJ _ (by decide)).trans ((hoth2 _ (by decide)).trans ((hoth1 _ (by decide)).trans hgp))
  have hmem3 : s3.mem = st.mem := hmemJ.trans (hmem2.trans hmem1)
  have hsaved3 : ∀ i (hi : i < callerSaveRegs.length),
      readWord64 s3.mem (T + BitVec.ofInt 64 (env.tab.saveBase 0) + BitVec.ofNat 64 (8 * i)) =
        initSt.getReg (callerSaveRegs[i]'hi) := by
    intro i hi; rw [hmem3]; exact hsaved i hi
  obtain ⟨mR, r', hrunR, hpcR, hrestR, hraR, hothR, hmemR⟩ :=
    checker_retRestore_returns env retPre tail initSt T halign hlinkRet s3 hpc3 hgp3 hsaved3
  have ha0Eq : r'.getReg AbiReg.a0 = 0#64 := by
    rw [hothR _ (by decide) (by decide) (by decide), hothJ _ (by decide), hoth2 _ (by decide), ha0_1]
    change st.getReg AbiReg.zero + sextImm12 0#12 = 0#64; rw [getReg_zero]; decide
  have ha1Eq : r'.getReg AbiReg.a1 = 1#64 := by
    rw [hothR _ (by decide) (by decide) (by decide), hothJ _ (by decide), ha1_2]
    change s1.getReg AbiReg.zero + sextImm12 1#12 = 1#64; rw [getReg_zero]; decide
  refine ⟨1 + 1 + kJ + mR, r', ?_, hpcR, hrestR, hraR, ha0Eq, ha1Eq, hmemR.trans hmem3⟩
  rw [run_add, run_add, run_add, hr1]; dsimp only; rw [hr2]; dsimp only; rw [hrunJ]; exact hrunR

private theorem checker_abort_stub_returns {lkm : LinkModel} (env : CodeEnvGen lkm)
    (pre tail : List AsmItem) (initSt : RV64.State) (T : BitVec 64)
    (halign : isAligned (T + BitVec.ofInt 64 (env.tab.saveBase 0)) 8 = true)
    (hlink : lkm.linkSpec (pre ++ drvAbortPrefix ++ drvRetRestoreStub env.tab ++ tail) =
      .ok (env.code, env.labels))
    (st : RV64.State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = T)
    (hsaved : ∀ i (hi : i < callerSaveRegs.length),
      readWord64 st.mem (T + BitVec.ofInt 64 (env.tab.saveBase 0) + BitVec.ofNat 64 (8 * i)) =
        initSt.getReg (callerSaveRegs[i]'hi)) :
    ∃ m r',
      RV64.run env.rom m st = .cont r' ∧
      r'.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64) ∧
      RegsRestored initSt r' ∧
      r'.getReg AbiReg.ra = initSt.getReg AbiReg.ra ∧
      r'.getReg AbiReg.a0 = st.getReg AbiReg.a0 ∧
      r'.getReg AbiReg.a1 = 2#64 ∧
      r'.mem = st.mem := by
  let p0 := pre ++ [Asm.lbl abortLabel]
  have hpc0 : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize p0) := by
    simpa only [p0, lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero] using hpc
  have hl1 : lkm.linkSpec (p0 ++ [Asm.addi AbiReg.a1 AbiReg.zero 2#12] ++
      (drvRetRestoreStub env.tab ++ tail)) =
      .ok (env.code, env.labels) := by
    simpa only [p0, drvAbortPrefix, List.cons_append, List.nil_append, List.append_assoc] using hlink
  obtain ⟨hr1, hpc1, ha1_1, hoth1, hmem1⟩ :=
    run_aluImm_rd_step env p0 _ .addi AbiReg.a1 AbiReg.zero 2#12 (by decide) hl1 st hpc0
  let s1 := stepReg st AbiReg.a1 (evalAluImm .addi (st.getReg AbiReg.zero) 2#12)
    (BitVec.ofNat 64 (4 * (lkm.totalSize p0 + 1)))
  let p1 := p0 ++ [Asm.addi AbiReg.a1 AbiReg.zero 2#12]
  have hpc1' : s1.pc = BitVec.ofNat 64 (4 * lkm.totalSize p1) := by
    simpa only [p1, lkm.totalSize_append, Asm.addi, lkm.totalSize_instr] using hpc1
  have hl2 : lkm.linkSpec (p1 ++ drvRetRestoreStub env.tab ++ tail) =
      .ok (env.code, env.labels) := by
    simpa only [p1, List.append_assoc] using hl1
  have hgp1 : s1.getReg AbiReg.gp = T := (hoth1 _ (by decide)).trans hgp
  have hsaved1 : ∀ i (hi : i < callerSaveRegs.length),
      readWord64 s1.mem (T + BitVec.ofInt 64 (env.tab.saveBase 0) + BitVec.ofNat 64 (8 * i)) =
        initSt.getReg (callerSaveRegs[i]'hi) := by
    intro i hi; rw [hmem1]; exact hsaved i hi
  obtain ⟨mR, r', hrunR, hpcR, hrestR, hraR, hothR, hmemR⟩ :=
    checker_retRestore_returns env p1 tail initSt T halign hl2 s1 hpc1' hgp1 hsaved1
  have ha0Eq : r'.getReg AbiReg.a0 = st.getReg AbiReg.a0 :=
    (hothR _ (by decide) (by decide) (by decide)).trans (hoth1 _ (by decide))
  have ha1Eq : r'.getReg AbiReg.a1 = 2#64 := by
    rw [hothR _ (by decide) (by decide) (by decide), ha1_1]
    change st.getReg AbiReg.zero + sextImm12 2#12 = 2#64; rw [getReg_zero]; decide
  exact ⟨1 + mR, r', by rw [run_add, hr1]; exact hrunR, hpcR, hrestR, hraR, ha0Eq, ha1Eq,
    hmemR.trans hmem1⟩

private theorem checker_err_stub_returns {lkm : LinkModel} (env : CodeEnvGen lkm)
    (pre tail : List AsmItem) (initSt : RV64.State) (T : BitVec 64)
    (halign : isAligned (T + BitVec.ofInt 64 (env.tab.saveBase 0)) 8 = true)
    (hlink : lkm.linkSpec (pre ++ drvErrPrefix ++ drvAbortPrefix ++ drvRetRestoreStub env.tab ++ tail) =
      .ok (env.code, env.labels))
    (st : RV64.State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = T)
    (hsaved : ∀ i (hi : i < callerSaveRegs.length),
      readWord64 st.mem (T + BitVec.ofInt 64 (env.tab.saveBase 0) + BitVec.ofNat 64 (8 * i)) =
        initSt.getReg (callerSaveRegs[i]'hi)) :
    ∃ m r',
      RV64.run env.rom m st = .cont r' ∧
      r'.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64) ∧
      RegsRestored initSt r' ∧
      r'.getReg AbiReg.ra = initSt.getReg AbiReg.ra ∧
      r'.getReg AbiReg.a0 = 0#64 ∧
      r'.getReg AbiReg.a1 = 2#64 ∧
      r'.mem = st.mem := by
  let p0 := pre ++ [Asm.lbl errLabel]
  have hpc0 : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize p0) := by
    simpa only [p0, lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero] using hpc
  have hl1 : lkm.linkSpec (p0 ++ [Asm.addi AbiReg.a0 AbiReg.zero 0#12] ++
      (drvAbortPrefix ++ drvRetRestoreStub env.tab ++ tail)) =
      .ok (env.code, env.labels) := by
    simpa only [p0, drvErrPrefix, List.cons_append, List.nil_append, List.append_assoc] using hlink
  obtain ⟨hr1, hpc1, ha0_1, hoth1, hmem1⟩ :=
    run_aluImm_rd_step env p0 _ .addi AbiReg.a0 AbiReg.zero 0#12 (by decide) hl1 st hpc0
  let s1 := stepReg st AbiReg.a0 (evalAluImm .addi (st.getReg AbiReg.zero) 0#12)
    (BitVec.ofNat 64 (4 * (lkm.totalSize p0 + 1)))
  let p1 := p0 ++ [Asm.addi AbiReg.a0 AbiReg.zero 0#12]
  have hpc1' : s1.pc = BitVec.ofNat 64 (4 * lkm.totalSize p1) := by
    simpa only [p1, lkm.totalSize_append, Asm.addi, lkm.totalSize_instr] using hpc1
  have hlAb : lkm.linkSpec (p1 ++ drvAbortPrefix ++ drvRetRestoreStub env.tab ++ tail) =
      .ok (env.code, env.labels) := by
    simpa only [p1, List.append_assoc] using hl1
  have hgp1 : s1.getReg AbiReg.gp = T := (hoth1 _ (by decide)).trans hgp
  have hsaved1 : ∀ i (hi : i < callerSaveRegs.length),
      readWord64 s1.mem (T + BitVec.ofInt 64 (env.tab.saveBase 0) + BitVec.ofNat 64 (8 * i)) =
        initSt.getReg (callerSaveRegs[i]'hi) := by
    intro i hi; rw [hmem1]; exact hsaved i hi
  obtain ⟨m, r', hrun, hpcR, hrestR, hraR, ha0R, ha1R, hmemR⟩ :=
    checker_abort_stub_returns env p1 tail initSt T halign hlAb s1 hpc1' hgp1 hsaved1
  have ha0Eq : r'.getReg AbiReg.a0 = 0#64 := by
    rw [ha0R, ha0_1]
    change st.getReg AbiReg.zero + sextImm12 0#12 = 0#64; rw [getReg_zero]; decide
  exact ⟨1 + m, r', by rw [run_add, hr1]; exact hrun, hpcR, hrestR, hraR, ha0Eq, ha1R, hmemR.trans hmem1⟩

theorem checker_exhausted_returns (initSt : RV64.State) (T : BitVec 64)
    (halign : isAligned (T + BitVec.ofInt 64 (checkerTabMini.saveBase 0)) 8 = true)
    (st : RV64.State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * checkerEnv.exhaustedTarget))
    (hgp : st.getReg AbiReg.gp = T)
    (hsaved : DrvRegsSaved T initSt st.mem) :
    ∃ m r',
      RV64.run checkerEnv.rom m st = .cont r' ∧
      r'.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64) ∧
      RegsRestored initSt r' ∧
      r'.getReg AbiReg.ra = initSt.getReg AbiReg.ra ∧
      r'.getReg AbiReg.a0 = 0#64 ∧
      r'.getReg AbiReg.a1 = 1#64 ∧
      r'.mem = st.mem := by
  rw [checkerEnv_exhaustedTarget_eq] at hpc
  have hlink : checkerLM.linkSpec (drvAllBeforeEx checkerTabMini ++ drvExhaustedStub ++
      drvErrPrefix ++ drvAbortPrefix ++ drvRetRestoreStub checkerTabMini ++
      (drvInitSubAsm checkerTabMini ++ checkerCmpDriverAsm checkerTabMini ++ checkerFnsAsm)) =
      .ok (checkerEnv.code, checkerEnv.labels) := by
    simpa only [drvAllBeforeEx, List.append_assoc] using checkerChipAsm_linkSpec_decomp
  exact checker_exhausted_stub_returns checkerEnv (drvAllBeforeEx checkerTabMini) _ initSt T
    halign hlink st hpc hgp hsaved

theorem checker_abort_returns (initSt : RV64.State) (T : BitVec 64)
    (halign : isAligned (T + BitVec.ofInt 64 (checkerTabMini.saveBase 0)) 8 = true)
    (st : RV64.State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * checkerEnv.abortTarget))
    (hgp : st.getReg AbiReg.gp = T)
    (hsaved : DrvRegsSaved T initSt st.mem) :
    ∃ m r',
      RV64.run checkerEnv.rom m st = .cont r' ∧
      r'.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64) ∧
      RegsRestored initSt r' ∧
      r'.getReg AbiReg.ra = initSt.getReg AbiReg.ra ∧
      r'.getReg AbiReg.a0 = st.getReg AbiReg.a0 ∧
      r'.getReg AbiReg.a1 = 2#64 ∧
      r'.mem = st.mem := by
  rw [checkerEnv_abortTarget_eq] at hpc
  have hlink : checkerLM.linkSpec
      ((drvAllBeforeEx checkerTabMini ++ drvExhaustedStub ++ drvErrPrefix) ++ drvAbortPrefix ++
       drvRetRestoreStub checkerTabMini ++
       (drvInitSubAsm checkerTabMini ++ checkerCmpDriverAsm checkerTabMini ++ checkerFnsAsm)) =
      .ok (checkerEnv.code, checkerEnv.labels) := by
    simpa only [drvAllBeforeEx, List.append_assoc] using checkerChipAsm_linkSpec_decomp
  exact checker_abort_stub_returns checkerEnv _ _ initSt T halign hlink st hpc hgp hsaved

theorem checker_err_returns (initSt : RV64.State) (T : BitVec 64)
    (halign : isAligned (T + BitVec.ofInt 64 (checkerTabMini.saveBase 0)) 8 = true)
    (st : RV64.State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * checkerEnv.errTarget))
    (hgp : st.getReg AbiReg.gp = T)
    (hsaved : DrvRegsSaved T initSt st.mem) :
    ∃ m r',
      RV64.run checkerEnv.rom m st = .cont r' ∧
      r'.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64) ∧
      RegsRestored initSt r' ∧
      r'.getReg AbiReg.ra = initSt.getReg AbiReg.ra ∧
      r'.getReg AbiReg.a0 = 0#64 ∧
      r'.getReg AbiReg.a1 = 2#64 ∧
      r'.mem = st.mem := by
  rw [checkerEnv_errTarget_eq] at hpc
  have hlink : checkerLM.linkSpec
      ((drvAllBeforeEx checkerTabMini ++ drvExhaustedStub) ++ drvErrPrefix ++ drvAbortPrefix ++
       drvRetRestoreStub checkerTabMini ++
       (drvInitSubAsm checkerTabMini ++ checkerCmpDriverAsm checkerTabMini ++ checkerFnsAsm)) =
      .ok (checkerEnv.code, checkerEnv.labels) := by
    simpa only [drvAllBeforeEx, List.append_assoc] using checkerChipAsm_linkSpec_decomp
  exact checker_err_stub_returns checkerEnv _ _ initSt T halign hlink st hpc hgp hsaved

theorem linkedCmp_exhausted_returns (img : LinkedCmpImage) (initSt : RV64.State) (T : BitVec 64)
    (halign : isAligned (T + BitVec.ofInt 64 (checkerTabMini.saveBase 0)) 8 = true)
    (st : RV64.State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * (linkedCmpEnv img).exhaustedTarget))
    (hgp : st.getReg AbiReg.gp = T)
    (hsaved : DrvRegsSaved T initSt st.mem) :
    ∃ m r',
      RV64.run (linkedCmpEnv img).rom m st = .cont r' ∧
      r'.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64) ∧
      RegsRestored initSt r' ∧
      r'.getReg AbiReg.ra = initSt.getReg AbiReg.ra ∧
      r'.getReg AbiReg.a0 = 0#64 ∧
      r'.getReg AbiReg.a1 = 1#64 ∧
      r'.mem = st.mem := by
  rw [linkedCmpEnv_exhaustedTarget_eq] at hpc
  have hlink : img.lkm.linkSpec (drvAllBeforeEx checkerTabMini ++ drvExhaustedStub ++
      drvErrPrefix ++ drvAbortPrefix ++ drvRetRestoreStub checkerTabMini ++
      (drvInitSubAsm checkerTabMini ++ checkerCmpDriverAsm checkerTabMini ++ linkedCmpFnsAsm img)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [drvAllBeforeEx, List.append_assoc] using linkedCmpChipAsm_linkSpec_decomp img
  exact checker_exhausted_stub_returns (linkedCmpEnv img) (drvAllBeforeEx checkerTabMini) _ initSt T
    halign hlink st hpc hgp hsaved

theorem linkedCmp_abort_returns (img : LinkedCmpImage) (initSt : RV64.State) (T : BitVec 64)
    (halign : isAligned (T + BitVec.ofInt 64 (checkerTabMini.saveBase 0)) 8 = true)
    (st : RV64.State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * (linkedCmpEnv img).abortTarget))
    (hgp : st.getReg AbiReg.gp = T)
    (hsaved : DrvRegsSaved T initSt st.mem) :
    ∃ m r',
      RV64.run (linkedCmpEnv img).rom m st = .cont r' ∧
      r'.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64) ∧
      RegsRestored initSt r' ∧
      r'.getReg AbiReg.ra = initSt.getReg AbiReg.ra ∧
      r'.getReg AbiReg.a0 = st.getReg AbiReg.a0 ∧
      r'.getReg AbiReg.a1 = 2#64 ∧
      r'.mem = st.mem := by
  rw [linkedCmpEnv_abortTarget_eq] at hpc
  have hlink : img.lkm.linkSpec
      ((drvAllBeforeEx checkerTabMini ++ drvExhaustedStub ++ drvErrPrefix) ++ drvAbortPrefix ++
       drvRetRestoreStub checkerTabMini ++
       (drvInitSubAsm checkerTabMini ++ checkerCmpDriverAsm checkerTabMini ++ linkedCmpFnsAsm img)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [drvAllBeforeEx, List.append_assoc] using linkedCmpChipAsm_linkSpec_decomp img
  exact checker_abort_stub_returns (linkedCmpEnv img) _ _ initSt T halign hlink st hpc hgp hsaved

theorem linkedCmp_err_returns (img : LinkedCmpImage) (initSt : RV64.State) (T : BitVec 64)
    (halign : isAligned (T + BitVec.ofInt 64 (checkerTabMini.saveBase 0)) 8 = true)
    (st : RV64.State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * (linkedCmpEnv img).errTarget))
    (hgp : st.getReg AbiReg.gp = T)
    (hsaved : DrvRegsSaved T initSt st.mem) :
    ∃ m r',
      RV64.run (linkedCmpEnv img).rom m st = .cont r' ∧
      r'.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64) ∧
      RegsRestored initSt r' ∧
      r'.getReg AbiReg.ra = initSt.getReg AbiReg.ra ∧
      r'.getReg AbiReg.a0 = 0#64 ∧
      r'.getReg AbiReg.a1 = 2#64 ∧
      r'.mem = st.mem := by
  rw [linkedCmpEnv_errTarget_eq] at hpc
  have hlink : img.lkm.linkSpec
      ((drvAllBeforeEx checkerTabMini ++ drvExhaustedStub) ++ drvErrPrefix ++ drvAbortPrefix ++
       drvRetRestoreStub checkerTabMini ++
       (drvInitSubAsm checkerTabMini ++ checkerCmpDriverAsm checkerTabMini ++ linkedCmpFnsAsm img)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [drvAllBeforeEx, List.append_assoc] using linkedCmpChipAsm_linkSpec_decomp img
  exact checker_err_stub_returns (linkedCmpEnv img) _ _ initSt T halign hlink st hpc hgp hsaved

private theorem mem_set64_words_size (m : _root_.L.Mem) (s t : TieredArray) (i v : _root_.L.Word) :
    ((m.set64 s i v).words t).size = (m.words t).size := by
  simp only [_root_.L.Mem.set64, _root_.L.Mem.arr64]
  split
  · rename_i h; subst h; simp [Array.set!]
  · rfl

private theorem mem_copy64_words_size (m : _root_.L.Mem) (d : TieredArray) (di : _root_.L.Word)
    (s : TieredArray) (si : _root_.L.Word) :
    ∀ n t, ((m.copy64 d di s si n).words t).size = (m.words t).size
  | 0, _ => rfl
  | n + 1, t => by
    simp only [_root_.L.Mem.copy64]
    rw [mem_copy64_words_size _ d (di + 1) s (si + 1) n t, mem_set64_words_size]

private theorem mem_copy8w_words_size (m : _root_.L.Mem) (d : TieredArray) (di : _root_.L.Word)
    (b : Array UInt8) (si : _root_.L.Word) :
    ∀ n t, ((m.copy8w d di b si n).words t).size = (m.words t).size
  | 0, _ => rfl
  | n + 1, t => by
    simp only [_root_.L.Mem.copy8w]
    rw [mem_copy8w_words_size _ d (di + 1) b (si + 1) n t, mem_set64_words_size]

private theorem setLocs_mem_eq (s : _root_.L.St) (xs : List _root_.L.Var) (vs : List _root_.L.Word) :
    (s.setLocs xs vs).mem = s.mem := by
  induction xs generalizing s vs with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [_root_.L.St.setLocs]
    rw [ih]
    rfl

private theorem minil_exec_words_size (p : _root_.L.Prog) :
    ∀ (n : Nat) (s : _root_.L.Stmt) (st : _root_.L.St) {sig : _root_.L.Sig} {st' : _root_.L.St},
      _root_.L.exec p n s st = .ok (sig, st') →
      ∀ t, (st'.mem.words t).size = (st.mem.words t).size := by
  intro n
  induction n with
  | zero => intro _ _ _ _ h; cases h
  | succ n ih =>
    intro s
    induction s with
    | skip | brk =>
      intro st _ _ h t
      dsimp only [_root_.L.exec, _root_.L.step, Pure.pure, StateT.pure, Except.pure] at h
      cases h; rfl
    | set x e =>
      intro st _ _ h t
      rcases _root_.L.evalE_pure e st with ⟨v, hv⟩ | hv
      · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
        rw [hv] at h
        dsimp only [_root_.L.setLoc, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
          Pure.pure, StateT.pure, Except.pure] at h
        cases h; rfl
      · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
        rw [hv] at h; cases h
    | gset g e =>
      intro st _ _ h t
      rcases _root_.L.evalE_pure e st with ⟨v, hv⟩ | hv
      · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
        rw [hv] at h
        dsimp only [_root_.L.setG, _root_.L.St.setG, _root_.L.Mem.setG,
          modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
          Pure.pure, StateT.pure, Except.pure] at h
        cases h; rfl
      · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
        rw [hv] at h; cases h
    | ret es =>
      intro st _ _ h t
      rcases _root_.L.evalArgs_pure es st with ⟨vs, hvs⟩ | hvs
      · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
        rw [hvs] at h
        dsimp only [Pure.pure, StateT.pure, Except.pure] at h
        cases h; rfl
      · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
        rw [hvs] at h; cases h
    | abort e =>
      intro st _ _ h t
      dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
      cases h1 : _root_.L.evalE e st with
      | error err => rw [h1] at h; cases h
      | ok r1 =>
        rw [h1] at h
        dsimp only [throw, throwThe, MonadExceptOf.throw, StateT.lift] at h
        cases h
    | st8 a i e =>
      intro st _ _ h t
      rcases _root_.L.evalE_pure i st with ⟨vi, hvi⟩ | hvi
      · rcases _root_.L.evalE_pure e st with ⟨ve, hve⟩ | hve
        · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
          rw [hvi] at h; dsimp only at h; rw [hve] at h
          dsimp only [_root_.L.st8, Bind.bind, StateT.bind, Except.bind,
            get, getThe, MonadStateOf.get, StateT.get,
            Pure.pure, StateT.pure, Except.pure] at h
          by_cases hc : vi.toNat < (st.mem.arr8 a).size
          · simp only [hc, ↓reduceIte, set, MonadStateOf.set, StateT.set,
              Pure.pure, Except.pure] at h
            cases h; rfl
          · simp only [hc, ↓reduceIte, throw, throwThe, MonadExceptOf.throw, StateT.lift,
              Function.comp_apply] at h
            cases h
        · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
          rw [hvi] at h; dsimp only at h; rw [hve] at h; cases h
      · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
        rw [hvi] at h; cases h
    | st64 a i e =>
      intro st _ _ h t
      rcases _root_.L.evalE_pure i st with ⟨vi, hvi⟩ | hvi
      · rcases _root_.L.evalE_pure e st with ⟨ve, hve⟩ | hve
        · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
          rw [hvi] at h; dsimp only at h; rw [hve] at h
          dsimp only [_root_.L.st64, Bind.bind, StateT.bind, Except.bind,
            get, getThe, MonadStateOf.get, StateT.get,
            Pure.pure, StateT.pure, Except.pure] at h
          by_cases hc : vi.toNat < (st.mem.arr64 a).size
          · simp only [hc, ↓reduceIte, set, MonadStateOf.set, StateT.set,
              Pure.pure, Except.pure] at h
            cases h; exact mem_set64_words_size _ _ _ _ _
          · simp only [hc, ↓reduceIte, throw, throwThe, MonadExceptOf.throw, StateT.lift,
              Function.comp_apply] at h
            cases h
        · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
          rw [hvi] at h; dsimp only at h; rw [hve] at h; cases h
      · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
        rw [hvi] at h; cases h
    | st64t a ta i e =>
      intro st _ _ h t
      rcases _root_.L.evalE_pure ta st with ⟨u, hu⟩ | hu
      · rcases _root_.L.evalE_pure i st with ⟨vi, hvi⟩ | hvi
        · rcases _root_.L.evalE_pure e st with ⟨ve, hve⟩ | hve
          · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
            rw [hu] at h; dsimp only at h; rw [hvi] at h; dsimp only at h; rw [hve] at h
            dsimp only [_root_.L.st64, Bind.bind, StateT.bind, Except.bind,
              get, getThe, MonadStateOf.get, StateT.get,
              Pure.pure, StateT.pure, Except.pure] at h
            by_cases hc : vi.toNat < (st.mem.arr64 (_root_.L.tierA a u)).size
            · simp only [hc, ↓reduceIte, set, MonadStateOf.set, StateT.set,
                Pure.pure, Except.pure] at h
              cases h; exact mem_set64_words_size _ _ _ _ _
            · simp only [hc, ↓reduceIte, throw, throwThe, MonadExceptOf.throw, StateT.lift,
                Function.comp_apply] at h
              cases h
          · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
            rw [hu] at h; dsimp only at h; rw [hvi] at h; dsimp only at h; rw [hve] at h; cases h
        · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
          rw [hu] at h; dsimp only at h; rw [hvi] at h; cases h
      · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
        rw [hu] at h; cases h
    | st32t a ta i e =>
      intro st _ _ h t
      rcases _root_.L.evalE_pure ta st with ⟨u, hu⟩ | hu
      · rcases _root_.L.evalE_pure i st with ⟨vi, hvi⟩ | hvi
        · rcases _root_.L.evalE_pure e st with ⟨ve, hve⟩ | hve
          · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
            rw [hu] at h; dsimp only at h; rw [hvi] at h; dsimp only at h; rw [hve] at h
            dsimp only [_root_.L.st32, Bind.bind, StateT.bind, Except.bind,
              get, getThe, MonadStateOf.get, StateT.get,
              Pure.pure, StateT.pure, Except.pure] at h
            by_cases hc : (vi / 2).toNat < (st.mem.arr64 (_root_.L.tierA a u)).size
            · simp only [hc, ↓reduceIte, set, MonadStateOf.set, StateT.set,
                Pure.pure, Except.pure] at h
              cases h; exact mem_set64_words_size _ _ _ _ _
            · simp only [hc, ↓reduceIte, throw, throwThe, MonadExceptOf.throw, StateT.lift,
                Function.comp_apply] at h
              cases h
          · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
            rw [hu] at h; dsimp only at h; rw [hvi] at h; dsimp only at h; rw [hve] at h; cases h
        · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
          rw [hu] at h; dsimp only at h; rw [hvi] at h; cases h
      · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
        rw [hu] at h; cases h
    | copy64 d di s si k =>
      intro st _ _ h t
      rcases _root_.L.warr_pure d st with ⟨da, hda⟩ | hda
      · rcases _root_.L.evalE_pure di st with ⟨vdi, hvdi⟩ | hvdi
        · rcases _root_.L.warr_pure s st with ⟨sa, hsa⟩ | hsa
          · rcases _root_.L.evalE_pure si st with ⟨vsi, hvsi⟩ | hvsi
            · rcases _root_.L.evalE_pure k st with ⟨vk, hvk⟩ | hvk
              · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
                rw [hda] at h; dsimp only at h; rw [hvdi] at h; dsimp only at h
                rw [hsa] at h; dsimp only at h; rw [hvsi] at h; dsimp only at h; rw [hvk] at h
                dsimp only [get, getThe, MonadStateOf.get, StateT.get,
                  set, MonadStateOf.set, StateT.set,
                  throw, throwThe, MonadExceptOf.throw, StateT.lift,
                  Pure.pure, StateT.pure, Except.pure] at h
                split at h <;> cases h; exact mem_copy64_words_size _ _ _ _ _ _ _
              · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
                rw [hda] at h; dsimp only at h; rw [hvdi] at h; dsimp only at h
                rw [hsa] at h; dsimp only at h; rw [hvsi] at h; dsimp only at h; rw [hvk] at h; cases h
            · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
              rw [hda] at h; dsimp only at h; rw [hvdi] at h; dsimp only at h
              rw [hsa] at h; dsimp only at h; rw [hvsi] at h; cases h
          · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
            rw [hda] at h; dsimp only at h; rw [hvdi] at h; dsimp only at h; rw [hsa] at h; cases h
        · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
          rw [hda] at h; dsimp only at h; rw [hvdi] at h; cases h
      · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
        rw [hda] at h; cases h
    | copy8w d di s si k =>
      intro st _ _ h t
      rcases _root_.L.warr_pure d st with ⟨da, hda⟩ | hda
      · rcases _root_.L.evalE_pure di st with ⟨vdi, hvdi⟩ | hvdi
        · rcases _root_.L.evalE_pure si st with ⟨vsi, hvsi⟩ | hvsi
          · rcases _root_.L.evalE_pure k st with ⟨vk, hvk⟩ | hvk
            · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
              rw [hda] at h; dsimp only at h; rw [hvdi] at h; dsimp only at h
              rw [hvsi] at h; dsimp only at h; rw [hvk] at h
              dsimp only [get, getThe, MonadStateOf.get, StateT.get,
                set, MonadStateOf.set, StateT.set,
                throw, throwThe, MonadExceptOf.throw, StateT.lift,
                Pure.pure, StateT.pure, Except.pure] at h
              split at h <;> cases h; exact mem_copy8w_words_size _ _ _ _ _ _ _
            · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
              rw [hda] at h; dsimp only at h; rw [hvdi] at h; dsimp only at h
              rw [hvsi] at h; dsimp only at h; rw [hvk] at h; cases h
          · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
            rw [hda] at h; dsimp only at h; rw [hvdi] at h; dsimp only at h; rw [hvsi] at h; cases h
        · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
          rw [hda] at h; dsimp only at h; rw [hvdi] at h; cases h
      · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
        rw [hda] at h; cases h
    | scan8 x s i e c =>
      intro st _ _ h t
      rcases _root_.L.evalE_pure i st with ⟨vi, hvi⟩ | hvi
      · rcases _root_.L.evalE_pure e st with ⟨ve, hve⟩ | hve
        · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
          rw [hvi] at h; dsimp only at h; rw [hve] at h
          dsimp only [get, getThe, MonadStateOf.get, StateT.get, _root_.L.setLoc,
            modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
            throw, throwThe, MonadExceptOf.throw, StateT.lift,
            Pure.pure, StateT.pure, Except.pure] at h
          split at h <;> cases h; rfl
        · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
          rw [hvi] at h; dsimp only at h; rw [hve] at h; cases h
      · dsimp only [_root_.L.exec, _root_.L.step, Bind.bind, StateT.bind, Except.bind] at h
        rw [hvi] at h; cases h
    | seq s1 s2 ih1 ih2 =>
      intro st sig st' h t
      dsimp only [_root_.L.exec] at h
      rw [step_seq] at h
      cases h1 : _root_.L.step p (_root_.L.exec p n) s1 st with
      | error err => rw [h1] at h; cases h
      | ok r1 =>
        rcases r1 with ⟨sig1, st1⟩
        rw [h1] at h
        have hs1 : (st1.mem.words t).size = (st.mem.words t).size := ih1 st h1 t
        cases sig1 with
        | normal => exact (ih2 st1 h t).trans hs1
        | brk | ret _ => cases h; exact hs1
    | ite c s1 s2 ih1 ih2 =>
      intro st sig st' h t
      dsimp only [_root_.L.exec] at h
      rw [step_ite] at h
      rcases _root_.L.evalC_pure c st with ⟨bc, hbc⟩ | hbc
      · rw [hbc] at h
        cases bc
        · exact ih2 st h t
        · exact ih1 st h t
      · rw [hbc] at h; cases h
    | «while» c body ihb =>
      intro st sig st' h t
      dsimp only [_root_.L.exec] at h
      rw [Compiler.step_while] at h
      rcases _root_.L.evalC_pure c st with ⟨bc, hbc⟩ | hbc
      · rw [hbc] at h
        cases bc
        · change Except.ok (_root_.L.Sig.normal, st) = Except.ok (sig, st') at h
          cases h; rfl
        · change (match _root_.L.step p (_root_.L.exec p n) body st with
            | .error err => .error err
            | .ok (.normal, st2) => _root_.L.exec p n (.while c body) st2
            | .ok (.brk, st2) => .ok (.normal, st2)
            | .ok (.ret vs, st2) => .ok (.ret vs, st2)) = Except.ok (sig, st') at h
          cases h1 : _root_.L.step p (_root_.L.exec p n) body st with
          | error err => rw [h1] at h; cases h
          | ok r1 =>
            rcases r1 with ⟨sig1, st1⟩
            rw [h1] at h
            have hs1 : (st1.mem.words t).size = (st.mem.words t).size := ihb st h1 t
            cases sig1 with
            | normal => exact (ih (.while c body) st1 h t).trans hs1
            | brk | ret _ => cases h; exact hs1
      · rw [hbc] at h; cases h
    | «call» xs f args =>
      intro st sig st' h t
      dsimp only [_root_.L.exec] at h
      rw [step_call] at h
      rcases _root_.L.evalArgs_pure args st with ⟨vs, hvs⟩ | hvs
      · simp only [hvs] at h
        cases hf : p.lookup f with
        | none => simp only [hf] at h; cases h
        | some fd =>
          simp only [hf] at h
          cases hb : _root_.L.exec p n fd.body { mem := st.mem, loc := _root_.L.Locals.init vs } with
          | error err => rw [hb] at h; cases h
          | ok r1 =>
            rcases r1 with ⟨sig1, st1⟩
            rw [hb] at h
            cases h
            rw [setLocs_mem_eq]
            exact ih fd.body { mem := st.mem, loc := _root_.L.Locals.init vs } hb t
      · simp only [hvs] at h; cases h

theorem minil_run_words_size {p : _root_.L.Prog} {n : Nat} {f : _root_.L.FnName}
    {vs : List _root_.L.Word} {m : _root_.L.Mem} {rs : List _root_.L.Word} {m' : _root_.L.Mem}
    (h : _root_.L.run p n f vs m = .ok (rs, m')) :
    ∀ t, (m'.words t).size = (m.words t).size := by
  intro t
  dsimp only [_root_.L.run, _root_.L.invoke, _root_.L.lookupFn, _root_.L.callFn,
    Bind.bind, StateT.bind, Except.bind, Except.map, StateT.run] at h
  cases hf : p.lookup f with
  | none =>
    rw [hf] at h
    dsimp only [throw, throwThe, MonadExceptOf.throw, StateT.lift] at h
    cases h
  | some fd =>
    rw [hf] at h
    dsimp only [Pure.pure, StateT.pure, Except.pure,
      get, getThe, MonadStateOf.get, StateT.get,
      set, MonadStateOf.set, StateT.set,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at h
    cases hb : _root_.L.exec p n fd.body { mem := m, loc := _root_.L.Locals.init vs } with
    | error err => rw [hb] at h; cases h
    | ok r1 =>
      rcases r1 with ⟨sig1, st1⟩
      rw [hb] at h
      cases h
      exact minil_exec_words_size p n fd.body { mem := m, loc := _root_.L.Locals.init vs } hb t

/-! ## 3. Layouts (`checkerLayoutA`, `checkerLayoutB`) & Memory/ROM Helpers -/

theorem isAligned8_add_nat_mul8 (base : BitVec 64) (hal : isAligned base 8 = true)
    (off : Nat) (hmul : off % 8 = 0) :
    isAligned (base + BitVec.ofNat 64 off) 8 = true := by
  rw [show off = 8 * (off / 8) from by omega]
  exact isAligned8_add_mul8 base hal (off / 8)

theorem memSpan_offset_disjoint_left {s : MemSpan} {base : BitVec 64} {need lo sz : Nat}
    (hneed : base.toNat + need ≤ 2 ^ 64) (hle : lo + sz ≤ need)
    (hd : s.disjoint ⟨base, need⟩) :
    s.disjoint ⟨base + BitVec.ofNat 64 lo, sz⟩ := by
  by_cases hlt : base.toNat + lo < 2 ^ 64
  · have hlo64 : lo < 2 ^ 64 := by omega
    have hadd : (base + BitVec.ofNat 64 lo).toNat = base.toNat + lo := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlo64, Nat.mod_eq_of_lt hlt]
    dsimp only [MemSpan.disjoint] at hd ⊢
    rw [hadd]
    cases hd with
    | inl h => left; omega
    | inr h => right; omega
  · have hsz0 : sz = 0 := by omega
    have heq2 : base.toNat + lo = 2 ^ 64 := by omega
    have hto0 : (base + BitVec.ofNat 64 lo).toNat = 0 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      by_cases hlo64 : lo < 2 ^ 64
      · rw [Nat.mod_eq_of_lt hlo64, heq2]
      · have hloeq : lo = 2 ^ 64 := by omega
        have hbase0 : base.toNat = 0 := by omega
        rw [hloeq, hbase0]
    dsimp only [MemSpan.disjoint]
    rw [hsz0, hto0]; exact Or.inr (by omega)

theorem memSpan_offset_disjoint_offset {base : BitVec 64} {need lo1 sz1 lo2 sz2 : Nat}
    (hneed : base.toNat + need ≤ 2 ^ 64)
    (h1 : lo1 + sz1 ≤ need) (h2 : lo2 + sz2 ≤ need) (hdisj : lo1 + sz1 ≤ lo2 ∨ lo2 + sz2 ≤ lo1) :
    MemSpan.disjoint ⟨base + BitVec.ofNat 64 lo1, sz1⟩ ⟨base + BitVec.ofNat 64 lo2, sz2⟩ := by
  have addToNat : ∀ lo, base.toNat + lo ≤ 2 ^ 64 →
      (base + BitVec.ofNat 64 lo).toNat = if base.toNat + lo = 2 ^ 64 then 0 else base.toNat + lo := by
    intro lo _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    by_cases h2' : base.toNat + lo = 2 ^ 64
    · simp only [h2', ↓reduceIte]
      by_cases hlo : lo < 2 ^ 64
      · rw [Nat.mod_eq_of_lt hlo, h2']
      · have hloeq : lo = 2 ^ 64 := by omega
        have hbase0 : base.toNat = 0 := by omega
        rw [hloeq, hbase0]
    · have hlt : base.toNat + lo < 2 ^ 64 := by omega
      have hlo : lo < 2 ^ 64 := by omega
      simp only [h2', ↓reduceIte]
      rw [Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hlt]
  have ha1 := addToNat lo1 (by omega)
  have ha2 := addToNat lo2 (by omega)
  dsimp only [MemSpan.disjoint]
  rw [ha1, ha2]
  by_cases h1eq : base.toNat + lo1 = 2 ^ 64 <;> by_cases h2eq : base.toNat + lo2 = 2 ^ 64 <;>
    simp only [h1eq, h2eq, ↓reduceIte]
  · have : sz1 = 0 := by omega
    rw [this]; exact Or.inl (by omega)
  · have : sz1 = 0 := by omega
    rw [this]; exact Or.inl (by omega)
  · have : sz2 = 0 := by omega
    rw [this]; exact Or.inr (by omega)
  · omega

theorem memSpan_disjoint_symm {s1 s2 : MemSpan} (h : s1.disjoint s2) : s2.disjoint s1 := by
  dsimp only [MemSpan.disjoint] at h ⊢
  exact h.symm

/-- Phase A `ProgLayout checkerTabMini` placing slot 0 = descriptor table, slot 1 = stack,
    byte arrays `inArr`/`pbArr` at `(inBase, inLen)` and `(pinsBase, pinsLen)`,
    and word arrays `s` at slot `pos64 s` (`abiWords` = `2^32` words each). -/
def checkerLayoutA (inBase pinsBase regionBase : BitVec 64) (inLen pinsLen : Nat)
    (hIn64 : inBase.toNat + inLen ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pinsLen ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjInPins : MemSpan.disjoint ⟨inBase, inLen⟩ ⟨pinsBase, pinsLen⟩)
    (hDisjInReg : MemSpan.disjoint ⟨inBase, inLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pinsLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩) :
    ProgLayout checkerTabMini :=
  have hNeedEq : abiNeed checkerTabMini = 205 * abiSlot := checkerTabMini_abiNeed_eq
  have hSlot8 : abiSlot % 8 = 0 := by simp [abiSlot]
  have hStack8 : (abiSlot + abiStack) % 8 = 0 := by simp [abiSlot, abiStack]
  have hStackIn : abiSlot + abiStack ≤ 205 * abiSlot := by simp [abiSlot, abiStack]
  have hLimLeTop : abiSlot ≤ abiSlot + abiStack := by simp [abiStack]
  have hReg64' : regionBase.toNat + 205 * abiSlot ≤ 2 ^ 64 := by omega
  let base8Fn : ArrId → BitVec 64 := fun a =>
    if a == inArr then inBase else if a == pbArr then pinsBase else 0#64
  let cap8Fn : ArrId → Nat := fun a =>
    if a == inArr then inLen else if a == pbArr then pinsLen else 0
  let base64Fn : TieredArray → BitVec 64 := fun s =>
    if checkerTabMini.wordPosOkB s then
      regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.pos64 s)
    else 0#64
  let cap64Fn : TieredArray → Nat := fun s =>
    if checkerTabMini.wordPosOkB s then abiWords else 0
  have h8ArrSpan : ∀ a, checkerTabMini.bytePosOkB a = true →
      (MemSpan.mk (base8Fn a) (cap8Fn a) = ⟨inBase, inLen⟩ ∧ a = inArr) ∨
      (MemSpan.mk (base8Fn a) (cap8Fn a) = ⟨pinsBase, pinsLen⟩ ∧ a = pbArr) := by
    intro a ha
    rcases checkerTabMini_bytePos_cases ha with rfl | rfl
    · left; refine ⟨?_, rfl⟩; simp [base8Fn, cap8Fn]
    · right; refine ⟨?_, rfl⟩; have hne : pbArr ≠ inArr := by decide
      simp [base8Fn, cap8Fn, hne]
  have h8DisjRegSub : ∀ a lo sz, checkerTabMini.bytePosOkB a = true →
      lo + sz ≤ 205 * abiSlot →
      MemSpan.disjoint ⟨base8Fn a, cap8Fn a⟩ ⟨regionBase + BitVec.ofNat 64 lo, sz⟩ := by
    intro a lo sz ha hle
    rcases h8ArrSpan a ha with ⟨hsp, _⟩ | ⟨hsp, _⟩ <;> rw [hsp]
    · exact memSpan_offset_disjoint_left (by omega) (by rw [hNeedEq]; exact hle) hDisjInReg
    · exact memSpan_offset_disjoint_left (by omega) (by rw [hNeedEq]; exact hle) hDisjPinsReg
  have h64SpanSub : ∀ s, checkerTabMini.wordPosOkB s = true →
      abiSlot * checkerTabMini.pos64 s + 8 * cap64Fn s ≤ 205 * abiSlot ∧
      2 ≤ checkerTabMini.pos64 s ∧ checkerTabMini.pos64 s < 205 := by
    intro s hs
    have ⟨hlo, hhi⟩ := checkerTabMini_wordPos_bounds hs
    have hcap : cap64Fn s = abiWords := by simp [cap64Fn, hs]
    have h8w : 8 * abiWords = abiSlot := by simp [abiWords, abiSlot]
    rw [hcap, h8w]
    have hle : abiSlot * checkerTabMini.pos64 s + abiSlot = abiSlot * (checkerTabMini.pos64 s + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    have hmul : abiSlot * (checkerTabMini.pos64 s + 1) ≤ abiSlot * 205 :=
      Nat.mul_le_mul_left abiSlot (by omega)
    rw [Nat.mul_comm abiSlot 205] at hmul
    exact ⟨by omega, hlo, hhi⟩
  { T := regionBase
    hTAlign := hRegAlign
    tabBytes := abiSlot
    hTabMin := by have := checkerTabMini_args_lt; omega
    hTValid := by
      have : abiSlot ≤ 205 * abiSlot := by simp [abiSlot]
      omega
    stackLimit := regionBase + BitVec.ofNat 64 abiSlot
    stackTop := regionBase + BitVec.ofNat 64 (abiSlot + abiStack)
    hLimAlign := isAligned8_add_nat_mul8 regionBase hRegAlign abiSlot hSlot8
    hTopAlign := isAligned8_add_nat_mul8 regionBase hRegAlign (abiSlot + abiStack) hStack8
    hStackLe := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
          BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    hStackValid := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    base8 := base8Fn
    cap8 := cap8Fn
    h8Valid := fun a => by
      by_cases ha : checkerTabMini.bytePosOkB a = true
      · rcases h8ArrSpan a ha with ⟨hsp, _⟩ | ⟨hsp, _⟩
        · have h1 := congrArg MemSpan.base hsp
          have h2 := congrArg MemSpan.size hsp
          dsimp only at h1 h2; rw [h1, h2]; exact hIn64
        · have h1 := congrArg MemSpan.base hsp
          have h2 := congrArg MemSpan.size hsp
          dsimp only at h1 h2; rw [h1, h2]; exact hPins64
      · have hne1 : a ≠ inArr := by rintro rfl; exact ha t_bin
        have hne2 : a ≠ pbArr := by rintro rfl; exact ha t_bpb
        simp [base8Fn, cap8Fn, hne1, hne2]
    base64 := base64Fn
    cap64 := cap64Fn
    h64Align := fun s => by
      by_cases hs : checkerTabMini.wordPosOkB s = true
      · simp only [base64Fn, hs, ↓reduceIte]
        apply isAligned8_add_nat_mul8 regionBase hRegAlign
        rw [Nat.mul_mod, hSlot8, Nat.zero_mul, Nat.zero_mod]
      · simp [base64Fn, hs, isAligned]
    h64Valid := fun s => by
      by_cases hs : checkerTabMini.wordPosOkB s = true
      · obtain ⟨hle, _, _⟩ := h64SpanSub s hs
        have hcap : cap64Fn s = abiWords := by simp [cap64Fn, hs]
        rw [hcap] at hle
        simp only [base64Fn, cap64Fn, hs, ↓reduceIte]
        have hpos64 : abiSlot * checkerTabMini.pos64 s < 2 ^ 64 := by
          have : abiSlot * checkerTabMini.pos64 s ≤ 205 * abiSlot := by omega
          omega
        have hsum64 : regionBase.toNat + abiSlot * checkerTabMini.pos64 s < 2 ^ 64 := by omega
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpos64, Nat.mod_eq_of_lt hsum64]
        omega
      · simp [base64Fn, cap64Fn, hs]
    htabDisjStack := by
      have hst : (regionBase + BitVec.ofNat 64 (abiSlot + abiStack)).toNat -
          (regionBase + BitVec.ofNat 64 abiSlot).toNat = abiStack := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
            BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      rw [hst]
      have hdisjZero : MemSpan.disjoint ⟨regionBase + BitVec.ofNat 64 0, abiSlot⟩
          ⟨regionBase + BitVec.ofNat 64 abiSlot, abiStack⟩ :=
        memSpan_offset_disjoint_offset hReg64' (by simp [abiSlot]) hStackIn (Or.inl (by omega))
      simpa only [BitVec.add_zero] using hdisjZero
    h8DisjStack := fun a ha => by
      have hst : (regionBase + BitVec.ofNat 64 (abiSlot + abiStack)).toNat -
          (regionBase + BitVec.ofNat 64 abiSlot).toNat = abiStack := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
            BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      rw [hst]
      exact h8DisjRegSub a abiSlot abiStack ha hStackIn
    h8DisjTab := fun a ha => by
      have hdisjZero := h8DisjRegSub a 0 abiSlot ha (by simp [abiSlot])
      simpa only [BitVec.add_zero] using hdisjZero
    h64DisjStack := fun s hs => by
      obtain ⟨hle, hlo, _⟩ := h64SpanSub s hs
      have hst : (regionBase + BitVec.ofNat 64 (abiSlot + abiStack)).toNat -
          (regionBase + BitVec.ofNat 64 abiSlot).toNat = abiStack := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
            BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      rw [hst]
      simp only [base64Fn, hs, ↓reduceIte]
      have hdisj : abiSlot + abiStack ≤ abiSlot * checkerTabMini.pos64 s := by
        have hm : abiSlot * 2 ≤ abiSlot * checkerTabMini.pos64 s := Nat.mul_le_mul_left abiSlot hlo
        have hstLe : abiStack ≤ abiSlot := by simp [abiStack, abiSlot]
        omega
      exact memSpan_offset_disjoint_offset hReg64' hle hStackIn (Or.inr hdisj)
    h64DisjTab := fun s hs => by
      obtain ⟨hle, hlo, _⟩ := h64SpanSub s hs
      simp only [base64Fn, hs, ↓reduceIte]
      have hdisj : 0 + abiSlot ≤ abiSlot * checkerTabMini.pos64 s := by
        rw [Nat.zero_add]
        have hm : abiSlot * 1 ≤ abiSlot * checkerTabMini.pos64 s := Nat.mul_le_mul_left abiSlot (by omega)
        rwa [Nat.mul_one] at hm
      have hdisjZero := memSpan_offset_disjoint_offset hReg64' hle (by simp [abiSlot]) (Or.inr hdisj)
      simpa only [BitVec.add_zero] using hdisjZero
    h8Disj8 := fun a1 a2 ha1 ha2 hne => by
      rcases h8ArrSpan a1 ha1 with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;>
        rcases h8ArrSpan a2 ha2 with ⟨h2, rfl⟩ | ⟨h2, rfl⟩
      · exact absurd rfl hne
      · rw [h1, h2]; exact hDisjInPins
      · rw [h1, h2]; exact memSpan_disjoint_symm hDisjInPins
      · exact absurd rfl hne
    h64Disj64 := fun s1 s2 hs1 hs2 hne => by
      obtain ⟨hle1, _, _⟩ := h64SpanSub s1 hs1
      obtain ⟨hle2, _, _⟩ := h64SpanSub s2 hs2
      have hpne : checkerTabMini.pos64 s1 ≠ checkerTabMini.pos64 s2 := fun heq =>
        hne (@Tab.wordPosOk_inj checkerTabMini s1 s2 hs1 hs2 heq)
      have hcap1 : cap64Fn s1 = abiWords := by simp [cap64Fn, hs1]
      have hcap2 : cap64Fn s2 = abiWords := by simp [cap64Fn, hs2]
      rw [hcap1] at hle1; rw [hcap2] at hle2
      simp only [base64Fn, cap64Fn, hs1, hs2, ↓reduceIte]
      apply memSpan_offset_disjoint_offset hReg64' hle1 hle2
      have h8w : 8 * abiWords = abiSlot := by simp [abiWords, abiSlot]
      rcases Nat.lt_or_gt_of_ne hpne with hlt | hlt
      · left
        have hm : abiSlot * (checkerTabMini.pos64 s1 + 1) ≤ abiSlot * checkerTabMini.pos64 s2 :=
          Nat.mul_le_mul_left abiSlot (by omega)
        rw [Nat.mul_add, Nat.mul_one, ← h8w] at hm; exact hm
      · right
        have hm : abiSlot * (checkerTabMini.pos64 s2 + 1) ≤ abiSlot * checkerTabMini.pos64 s1 :=
          Nat.mul_le_mul_left abiSlot (by omega)
        rw [Nat.mul_add, Nat.mul_one, ← h8w] at hm; exact hm
    h8Disj64 := fun a s ha hs => by
      obtain ⟨hle, _, _⟩ := h64SpanSub s hs
      simp only [base64Fn, hs, ↓reduceIte]
      exact h8DisjRegSub a (abiSlot * checkerTabMini.pos64 s) (8 * cap64Fn s) ha hle }

/-- Phase B `ProgLayout checkerTabMini` parameterized by the frozen `HDRF` word capacity `hdrLen`:
    identical to `checkerLayoutA` except `OUT` and `CTLF` have capacity `0` (empty) and
    `HDRF` points to `OUT`'s slot (`pos64 OUT = 180`) with capacity `hdrLen`. -/
def checkerLayoutBGen (hdrLen : Nat) (hhdr : 8 * hdrLen ≤ abiSlot) (hhdrPos : 0 < hdrLen)
    (inBase pinsBase regionBase : BitVec 64) (inLen pinsLen : Nat)
    (hIn64 : inBase.toNat + inLen ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pinsLen ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjInPins : MemSpan.disjoint ⟨inBase, inLen⟩ ⟨pinsBase, pinsLen⟩)
    (hDisjInReg : MemSpan.disjoint ⟨inBase, inLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pinsLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩) :
    ProgLayout checkerTabMini :=
  let LA := checkerLayoutA inBase pinsBase regionBase inLen pinsLen
    hIn64 hPins64 hRegAlign hReg64 hDisjInPins hDisjInReg hDisjPinsReg
  have hNeedEq : abiNeed checkerTabMini = 205 * abiSlot := checkerTabMini_abiNeed_eq
  have hReg64' : regionBase.toNat + 205 * abiSlot ≤ 2 ^ 64 := by omega
  have hSlot8 : abiSlot % 8 = 0 := by decide
  let slotOfB : TieredArray → Nat := fun s =>
    if s = .t0 L.Arena.HDRF then checkerTabMini.pos64 (.t0 L.Arena.OUT)
    else checkerTabMini.pos64 s
  let base64B : TieredArray → BitVec 64 := fun s =>
    if s = .t0 L.Arena.OUT then 0#64
    else if s = .t0 L.Arena.CTLF then 0#64
    else if s = .t0 L.Arena.HDRF then
      regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.pos64 (.t0 L.Arena.OUT))
    else LA.base64 s
  let cap64B : TieredArray → Nat := fun s =>
    if s = .t0 L.Arena.OUT then 0
    else if s = .t0 L.Arena.CTLF then 0
    else if s = .t0 L.Arena.HDRF then hdrLen
    else LA.cap64 s
  have h64Desc : ∀ s, checkerTabMini.wordPosOkB s = true →
      (cap64B s = 0 ∧ base64B s = 0#64) ∨
      (base64B s = regionBase + BitVec.ofNat 64 (abiSlot * slotOfB s) ∧
       abiSlot * slotOfB s + 8 * cap64B s ≤ 205 * abiSlot ∧
       8 * cap64B s ≤ abiSlot ∧
       2 ≤ slotOfB s ∧ slotOfB s < 205 ∧ 0 < cap64B s) := by
    intro s hs
    by_cases hOut : s = .t0 L.Arena.OUT
    · left; subst hOut; exact ⟨by simp [cap64B], by simp [base64B]⟩
    · by_cases hCtlf : s = .t0 L.Arena.CTLF
      · left; subst hCtlf
        have hne : (TieredArray.t0 L.Arena.CTLF) ≠ (TieredArray.t0 L.Arena.OUT) := by decide
        exact ⟨by simp [cap64B, hne], by simp [base64B, hne]⟩
      · right
        by_cases hHdrf : s = .t0 L.Arena.HDRF
        · subst hHdrf
          have hne1 : (TieredArray.t0 L.Arena.HDRF) ≠ (TieredArray.t0 L.Arena.OUT) := by decide
          have hne2 : (TieredArray.t0 L.Arena.HDRF) ≠ (TieredArray.t0 L.Arena.CTLF) := by decide
          have ⟨hlo, hhi⟩ := checkerTabMini_wordPos_bounds t_word_out
          have hslot180 : abiSlot * 180 + abiSlot ≤ 205 * abiSlot := by decide
          have hle : abiSlot * checkerTabMini.pos64 (.t0 L.Arena.OUT) + 8 * hdrLen ≤ 205 * abiSlot := by
            rw [t_pos_out]; omega
          refine ⟨by simp [base64B, slotOfB, hne1, hne2], ?_, ?_, ?_, ?_, ?_⟩
          · simp [cap64B, slotOfB, hne1, hne2]; exact hle
          · simp [cap64B, hne1, hne2]; exact hhdr
          · simp [slotOfB]; exact hlo
          · simp [slotOfB]; exact hhi
          · simp [cap64B, hne1, hne2]; exact hhdrPos
        · have ⟨hlo, hhi⟩ := checkerTabMini_wordPos_bounds hs
          have hbas : LA.base64 s = regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.pos64 s) := by
            simp [LA, checkerLayoutA, hs]
          have hcap : LA.cap64 s = abiWords := by simp [LA, checkerLayoutA, hs]
          have h8w : 8 * abiWords = abiSlot := by simp [abiWords, abiSlot]
          have hmul : abiSlot * (checkerTabMini.pos64 s + 1) ≤ abiSlot * 205 :=
            Nat.mul_le_mul_left abiSlot (by omega)
          rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm abiSlot 205] at hmul
          refine ⟨by simp [base64B, slotOfB, hOut, hCtlf, hHdrf, hbas], ?_, ?_, ?_, ?_, ?_⟩
          · simp [cap64B, slotOfB, hOut, hCtlf, hHdrf, hcap, h8w]; exact hmul
          · simp [cap64B, hOut, hCtlf, hHdrf, hcap, h8w]
          · simp [slotOfB, hHdrf]; exact hlo
          · simp [slotOfB, hHdrf]; exact hhi
          · simp [cap64B, hOut, hCtlf, hHdrf, hcap, abiWords]
  have hslotInj : ∀ {s1 s2}, checkerTabMini.wordPosOkB s1 = true →
      checkerTabMini.wordPosOkB s2 = true → s1 ≠ s2 →
      0 < cap64B s1 → 0 < cap64B s2 → slotOfB s1 ≠ slotOfB s2 := by
    intro s1 s2 hs1 hs2 hne hc1 hc2
    have hOut1 : s1 ≠ .t0 L.Arena.OUT := by rintro rfl; simp [cap64B] at hc1
    have hCtlf1 : s1 ≠ .t0 L.Arena.CTLF := by rintro rfl; simp [cap64B] at hc1
    have hOut2 : s2 ≠ .t0 L.Arena.OUT := by rintro rfl; simp [cap64B] at hc2
    have hCtlf2 : s2 ≠ .t0 L.Arena.CTLF := by rintro rfl; simp [cap64B] at hc2
    by_cases hH1 : s1 = .t0 L.Arena.HDRF
    · subst hH1
      have hH2 : s2 ≠ .t0 L.Arena.HDRF := hne.symm
      simp only [slotOfB, ↓reduceIte, hH2]
      intro heq
      exact hOut2 (@Tab.wordPosOk_inj checkerTabMini (.t0 L.Arena.OUT) s2 t_word_out hs2 heq).symm
    · by_cases hH2 : s2 = .t0 L.Arena.HDRF
      · subst hH2
        simp only [slotOfB, hH1, ↓reduceIte]
        intro heq
        exact hOut1 (@Tab.wordPosOk_inj checkerTabMini s1 (.t0 L.Arena.OUT) hs1 t_word_out heq)
      · simp only [slotOfB, hH1, hH2, ↓reduceIte]
        intro heq
        exact hne (@Tab.wordPosOk_inj checkerTabMini s1 s2 hs1 hs2 heq)
  { LA with
    base64 := base64B
    cap64 := cap64B
    h64Align := fun s => by
      by_cases hOut : s = .t0 L.Arena.OUT
      · subst hOut; simp [base64B, isAligned]
      · by_cases hCtlf : s = .t0 L.Arena.CTLF
        · subst hCtlf; simp [base64B, isAligned]
        · by_cases hHdrf : s = .t0 L.Arena.HDRF
          · subst hHdrf; simp only [base64B, hOut, hCtlf, ↓reduceIte]
            apply isAligned8_add_nat_mul8 regionBase hRegAlign
            rw [Nat.mul_mod, hSlot8, Nat.zero_mul, Nat.zero_mod]
          · simp only [base64B, hOut, hCtlf, hHdrf, ↓reduceIte]
            exact LA.h64Align s
    h64Valid := fun s => by
      by_cases hs : checkerTabMini.wordPosOkB s = true
      · rcases h64Desc s hs with ⟨hc0, hb0⟩ | ⟨hb, hle, _, _, _⟩
        · rw [hc0, hb0]; simp
        · rw [hb]
          have hpos64 : abiSlot * slotOfB s < 2 ^ 64 := by
            have : abiSlot * slotOfB s ≤ 205 * abiSlot := by omega
            omega
          have hsum64 : regionBase.toNat + abiSlot * slotOfB s < 2 ^ 64 := by omega
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpos64, Nat.mod_eq_of_lt hsum64]
          omega
      · have hne1 : s ≠ .t0 L.Arena.OUT := by rintro rfl; exact hs t_word_out
        have hne2 : s ≠ .t0 L.Arena.CTLF := by rintro rfl; exact hs t_word_ctlf
        have hne3 : s ≠ .t0 L.Arena.HDRF := by rintro rfl; exact hs t_word_hdrf
        simp only [base64B, cap64B, hne1, hne2, hne3, ↓reduceIte]
        exact LA.h64Valid s
    h64DisjStack := fun s hs => by
      rcases h64Desc s hs with ⟨hc0, hb0⟩ | ⟨hb, hle, _, hlo, _, _⟩
      · rw [hc0, hb0, Nat.mul_zero]; dsimp only [MemSpan.disjoint]
        exact Or.inl (by rw [show (0#64 : BitVec 64).toNat + 0 = 0 from rfl]; exact Nat.zero_le _)
      · rw [hb]
        have hst : LA.stackTop.toNat - LA.stackLimit.toNat = abiStack := by
          dsimp only [LA, checkerLayoutA]
          have hs1 : abiSlot < 2 ^ 64 := by decide
          have hs2 : abiSlot + abiStack < 2 ^ 64 := by decide
          have hsIn : abiSlot + abiStack ≤ 205 * abiSlot := by decide
          have hr1 : regionBase.toNat + abiSlot < 2 ^ 64 := by omega
          have hr2 : regionBase.toNat + (abiSlot + abiStack) < 2 ^ 64 := by omega
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs2, Nat.mod_eq_of_lt hr2,
              BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs1, Nat.mod_eq_of_lt hr1]
          omega
        change MemSpan.disjoint ⟨regionBase + BitVec.ofNat 64 (abiSlot * slotOfB s), 8 * cap64B s⟩
          ⟨LA.stackLimit, LA.stackTop.toNat - LA.stackLimit.toNat⟩
        rw [hst]
        change MemSpan.disjoint ⟨regionBase + BitVec.ofNat 64 (abiSlot * slotOfB s), 8 * cap64B s⟩
          ⟨regionBase + BitVec.ofNat 64 abiSlot, abiStack⟩
        have hdisj : abiSlot + abiStack ≤ abiSlot * slotOfB s := by
          have hm : abiSlot * 2 ≤ abiSlot * slotOfB s := Nat.mul_le_mul_left abiSlot hlo
          have hstLe : abiStack ≤ abiSlot := by simp [abiStack, abiSlot]
          omega
        exact memSpan_offset_disjoint_offset hReg64' hle
          (by simp [abiSlot, abiStack]) (Or.inr hdisj)
    h64DisjTab := fun s hs => by
      rcases h64Desc s hs with ⟨hc0, hb0⟩ | ⟨hb, hle, _, hlo, _, _⟩
      · rw [hc0, hb0, Nat.mul_zero]; dsimp only [MemSpan.disjoint]
        exact Or.inl (by rw [show (0#64 : BitVec 64).toNat + 0 = 0 from rfl]; exact Nat.zero_le _)
      · rw [hb]
        have htabT : LA.T = regionBase + BitVec.ofNat 64 0 := (BitVec.add_zero regionBase).symm
        have htabB : LA.tabBytes = abiSlot := rfl
        rw [htabT, htabB]
        have hdisj : 0 + abiSlot ≤ abiSlot * slotOfB s := by
          rw [Nat.zero_add]
          have hm : abiSlot * 1 ≤ abiSlot * slotOfB s := Nat.mul_le_mul_left abiSlot (by omega)
          rwa [Nat.mul_one] at hm
        exact memSpan_offset_disjoint_offset hReg64' hle (by simp [abiSlot]) (Or.inr hdisj)
    h64Disj64 := fun s1 s2 hs1 hs2 hne => by
      by_cases h1z : cap64B s1 = 0
      · rcases h64Desc s1 hs1 with ⟨_, hb0⟩ | ⟨_, _, _, _, _, hpos⟩
        · rw [h1z, hb0, Nat.mul_zero]; dsimp only [MemSpan.disjoint]
          exact Or.inl (by rw [show (0#64 : BitVec 64).toNat + 0 = 0 from rfl]; exact Nat.zero_le _)
        · omega
      · by_cases h2z : cap64B s2 = 0
        · rcases h64Desc s2 hs2 with ⟨_, hb0⟩ | ⟨_, _, _, _, _, hpos⟩
          · rw [h2z, hb0, Nat.mul_zero]; dsimp only [MemSpan.disjoint]
            exact Or.inr (by rw [show (0#64 : BitVec 64).toNat + 0 = 0 from rfl]; exact Nat.zero_le _)
          · omega
        · have hsne := hslotInj hs1 hs2 hne (Nat.pos_of_ne_zero h1z) (Nat.pos_of_ne_zero h2z)
          rcases h64Desc s1 hs1 with ⟨hc0, _⟩ | ⟨hb1, hle1, hcap1, _, _, _⟩
          · exact absurd hc0 h1z
          rcases h64Desc s2 hs2 with ⟨hc0, _⟩ | ⟨hb2, hle2, hcap2, _, _, _⟩
          · exact absurd hc0 h2z
          rw [hb1, hb2]
          apply memSpan_offset_disjoint_offset hReg64' hle1 hle2
          rcases Nat.lt_or_gt_of_ne hsne with hlt | hlt
          · left
            have hm : abiSlot * (slotOfB s1 + 1) ≤ abiSlot * slotOfB s2 :=
              Nat.mul_le_mul_left abiSlot (by omega)
            rw [Nat.mul_add, Nat.mul_one] at hm; omega
          · right
            have hm : abiSlot * (slotOfB s2 + 1) ≤ abiSlot * slotOfB s1 :=
              Nat.mul_le_mul_left abiSlot (by omega)
            rw [Nat.mul_add, Nat.mul_one] at hm; omega
    h8Disj64 := fun a s ha hs => by
      rcases h64Desc s hs with ⟨hc0, hb0⟩ | ⟨hb, hle, _, _, _, _⟩
      · rw [hc0, hb0, Nat.mul_zero]; dsimp only [MemSpan.disjoint]
        exact Or.inr (by rw [show (0#64 : BitVec 64).toNat + 0 = 0 from rfl]; exact Nat.zero_le _)
      · rw [hb]
        rcases checkerTabMini_bytePos_cases ha with rfl | rfl
        · have hsp : LA.base8 inArr = inBase ∧ LA.cap8 inArr = inLen := by
            simp [LA, checkerLayoutA]
          rw [hsp.1, hsp.2]
          exact memSpan_offset_disjoint_left (by omega) (by rw [hNeedEq]; exact hle) hDisjInReg
        · have hne : pbArr ≠ inArr := by decide
          have hsp : LA.base8 pbArr = pinsBase ∧ LA.cap8 pbArr = pinsLen := by
            simp [LA, checkerLayoutA, hne]
          rw [hsp.1, hsp.2]
          exact memSpan_offset_disjoint_left (by omega) (by rw [hNeedEq]; exact hle) hDisjPinsReg }

/-- Phase B `ProgLayout checkerTabMini`: identical to `checkerLayoutA` except
    `OUT` and `CTLF` have capacity `0` (empty) and `HDRF` points to `OUT`'s slot (`pos64 OUT = 180`)
    with capacity `L.Arena.hdrW`. -/
def checkerLayoutB (inBase pinsBase regionBase : BitVec 64) (inLen pinsLen : Nat)
    (hIn64 : inBase.toNat + inLen ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pinsLen ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjInPins : MemSpan.disjoint ⟨inBase, inLen⟩ ⟨pinsBase, pinsLen⟩)
    (hDisjInReg : MemSpan.disjoint ⟨inBase, inLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pinsLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩) :
    ProgLayout checkerTabMini :=
  checkerLayoutBGen L.Arena.hdrW (by decide) (by decide)
    inBase pinsBase regionBase inLen pinsLen
    hIn64 hPins64 hRegAlign hReg64 hDisjInPins hDisjInReg hDisjPinsReg

/-- Comparator Mode 8/9 `ProgLayout checkerTabMini`: identical to `checkerLayoutA` except
    `OUT` and `CTLF` have capacity `0` (empty) and `HDRF` points to `OUT`'s slot (`pos64 OUT = 180`)
    with capacity `hdrHw` (`156`). -/
def checkerLayoutCmpB (inBase pinsBase regionBase : BitVec 64) (inLen pinsLen : Nat)
    (hIn64 : inBase.toNat + inLen ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pinsLen ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjInPins : MemSpan.disjoint ⟨inBase, inLen⟩ ⟨pinsBase, pinsLen⟩)
    (hDisjInReg : MemSpan.disjoint ⟨inBase, inLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pinsLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩) :
    ProgLayout checkerTabMini :=
  checkerLayoutBGen hdrHw (by decide) (by decide)
    inBase pinsBase regionBase inLen pinsLen
    hIn64 hPins64 hRegAlign hReg64 hDisjInPins hDisjInReg hDisjPinsReg

private theorem storeBytes_apply_lt (m : ByteMem) (addr : BitVec 64) :
    ∀ (n : Nat) (v : BitVec (8 * n)) (k : Nat), k < n → n ≤ 8 →
      storeBytes m addr n v (addr + BitVec.ofNat 64 k) = v.extractLsb' (8 * k) 8
  | 0, _, _, hk, _ => by omega
  | n + 1, v, 0, _, hn => by
    simp only [Nat.mul_zero, BitVec.add_zero, storeBytes]
    let mem' : ByteMem := fun x => if x == addr then v.extractLsb' 0 8 else m x
    have hout : MemEqOutside ⟨addr + 1#64, n⟩ mem'
        (storeBytes mem' (addr + 1#64) n (v.extractLsb' 8 (8 * n))) :=
      MemEqOutside.storeBytes mem' (addr + 1#64) n (v.extractLsb' 8 (8 * n))
        fun j hj => ⟨j, hj, rfl⟩
    have hnot : ¬(MemSpan.mk (addr + 1#64) n).contains addr := by
      intro ⟨j, hj, heq⟩
      dsimp only [MemSpan.contains] at hj heq
      have hcon := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : j < 2 ^ 64)] at hcon
      have h1lt : (1 : Nat) % 2 ^ 64 = 1 := rfl
      rw [h1lt] at hcon
      have had := addr.isLt
      omega
    rw [hout addr hnot]
    simp [mem']
  | n + 1, v, k + 1, hk, hn => by
    have hadd : addr + BitVec.ofNat 64 (k + 1) = (addr + 1#64) + BitVec.ofNat 64 k := by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have h1lt : (1 : Nat) % 2 ^ 64 = 1 := rfl
      rw [h1lt, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : 1 + k < 2 ^ 64)]
      omega
    simp only [storeBytes]
    rw [hadd, storeBytes_apply_lt _ (addr + 1#64) n (v.extractLsb' 8 (8 * n)) k (by omega) (by omega)]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_extractLsb', show i < 8 from hi, decide_true, Bool.true_and,
      show 8 * k + i < 8 * n by omega,
      show 8 + (8 * k + i) = 8 * (k + 1) + i by omega]

theorem writeWord64_apply_lt_cd (m : ByteMem) (addr : BitVec 64) (w : BitVec 64) (k : Nat)
    (hk : k < 8) :
    writeWord64 m addr w (addr + BitVec.ofNat 64 k) = w.extractLsb' (8 * k) 8 :=
  storeBytes_apply_lt m addr 8 w k hk (Nat.le_refl _)

theorem readWord64_of_zero_bytes (m : ByteMem) (addr : BitVec 64)
    (hz : ∀ j, j < 8 → m (addr + BitVec.ofNat 64 j) = 0#8) :
    readWord64 m addr = 0#64 := by
  have hcongr : loadBytes m addr 8 = loadBytes (writeWord64 m addr 0#64) addr 8 := by
    apply loadBytes_congr
    intro k hk
    rw [writeWord64_apply_lt_cd m addr 0#64 k hk, hz k hk]
    simp
  change loadBytes m addr 8 = 0#64
  rw [hcongr]
  exact readWord64_writeWord64_self m addr 0#64

private def sumBytes (k : Nat) : List UInt8 → Nat
  | [] => 0
  | b :: rest => b.toNat * 2 ^ (8 * k) + sumBytes (k + 1) rest

private theorem zipIdx_foldl_eq_sumBytes (k acc : Nat) (bs : List UInt8) :
    (bs.zipIdx k).foldl (fun a (b, i) => a + b.toNat * 2 ^ (8 * i)) acc = acc + sumBytes k bs := by
  induction bs generalizing k acc with
  | nil => simp [List.zipIdx, sumBytes]
  | cons b t ih =>
    simp only [List.zipIdx_cons, List.foldl_cons, sumBytes]
    rw [ih (k + 1) (acc + b.toNat * 2 ^ (8 * k))]; omega

private theorem sumBytes_shift (k : Nat) (bs : List UInt8) :
    sumBytes k bs = 2 ^ (8 * k) * sumBytes 0 bs := by
  induction bs generalizing k with
  | nil => simp [sumBytes]
  | cons b t ih =>
    simp only [sumBytes, Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
    rw [ih (k + 1), ih 1]
    have hp : 2 ^ (8 * (k + 1)) = 2 ^ (8 * k) * 2 ^ (8 * 1) := by
      rw [← Nat.pow_add, ← Nat.mul_add]
    rw [Nat.mul_comm b.toNat (2 ^ (8 * k)), hp, Nat.mul_add, Nat.mul_assoc]

private theorem sumBytes0_lt (bs : List UInt8) :
    sumBytes 0 bs < 2 ^ (8 * bs.length) := by
  induction bs with
  | nil => simp [sumBytes]
  | cons b t ih =>
    simp only [sumBytes, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, List.length_cons]
    rw [sumBytes_shift 1 t]
    have hb : b.toNat < 2 ^ 8 := b.toBitVec.isLt
    have hp : 2 ^ (8 * (t.length + 1)) = 2 ^ 8 * 2 ^ (8 * t.length) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [hp]
    have hmul : 2 ^ 8 * sumBytes 0 t + 2 ^ 8 ≤ 2 ^ 8 * 2 ^ (8 * t.length) := by
      rw [← Nat.mul_add_one]; exact Nat.mul_le_mul_left _ ih
    omega

private theorem sumBytes0_byte_div_mod (bs : List UInt8) (j : Nat) (hj : j < bs.length) :
    (sumBytes 0 bs / 2 ^ (8 * j)) % 2 ^ 8 = bs[j].toNat := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b t ih =>
    cases j with
    | zero =>
      simp only [sumBytes, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.div_one, List.getElem_cons_zero]
      rw [sumBytes_shift 1 t, show 8 * 1 = 8 from rfl]
      have hblt : b.toNat < 2 ^ 8 := b.toBitVec.isLt
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hblt]
    | succ j' =>
      simp only [sumBytes, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, List.getElem_cons_succ]
      rw [sumBytes_shift 1 t, show 8 * 1 = 8 from rfl]
      have hp : 2 ^ (8 * (j' + 1)) = 2 ^ 8 * 2 ^ (8 * j') := by
        rw [← Nat.pow_add]; congr 1; omega
      have hblt : b.toNat < 2 ^ 8 := b.toBitVec.isLt
      rw [hp, ← Nat.div_div_eq_div_mul, Nat.add_comm, Nat.mul_add_div (by decide : 0 < 2 ^ 8),
        Nat.div_eq_of_lt hblt, Nat.add_zero]
      exact ih j' (by simpa using hj)

theorem romWord64_extract_byte (bs : List UInt8) (hlen : bs.length ≤ 8) (j : Nat) (hj : j < bs.length) :
    (romWord64 bs).extractLsb' (8 * j) 8 = bs[j].toBitVec := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, romWord64, BitVec.toNat_ofNat, zipIdx_foldl_eq_sumBytes, Nat.zero_add]
  have hlt64 : sumBytes 0 bs < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (sumBytes0_lt bs) (Nat.pow_le_pow_right (by decide) (by omega))
  rw [Nat.mod_eq_of_lt hlt64, Nat.shiftRight_eq_div_pow, sumBytes0_byte_div_mod bs j hj]
  rfl

theorem romWords64_getElem (bs : List UInt8) (k : Nat) (hk : k < bs.length) :
    k / 8 < (romWords64 bs).length ∧
    ((romWords64 bs)[k / 8]'(by rw [romWords64_length]; omega)).extractLsb' (8 * (k % 8)) 8 = bs[k].toBitVec := by
  match bs with
  | [] => simp at hk
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    by_cases hk8 : k < 8
    · have hkdiv : k / 8 = 0 := Nat.div_eq_of_lt hk8
      have hkmod : k % 8 = k := Nat.mod_eq_of_lt hk8
      refine ⟨by rw [romWords64_length]; omega, ?_⟩
      simp only [romWords64, hkdiv, List.getElem_cons_zero, hkmod]
      have hheadEq : (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest)[k] =
          [b0, b1, b2, b3, b4, b5, b6, b7][k]'(by simp [hk8]) := by
        rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k' <;> first | rfl | omega
      rw [hheadEq]
      exact romWord64_extract_byte [b0, b1, b2, b3, b4, b5, b6, b7] (by simp) k (by simp [hk8])
    · have hkgt : 8 ≤ k := Nat.le_of_not_lt hk8
      have hlenCons : (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest).length = rest.length + 8 := rfl
      have hkrest : k - 8 < rest.length := by rw [hlenCons] at hk; omega
      obtain ⟨h1, h2⟩ := romWords64_getElem rest (k - 8) hkrest
      have hdiv : k / 8 = (k - 8) / 8 + 1 := by omega
      have hmod : k % 8 = (k - 8) % 8 := by omega
      refine ⟨by rw [hlenCons] at hk; rw [romWords64_length]; omega, ?_⟩
      simp only [romWords64, hdiv, List.getElem_cons_succ, hmod]
      have htailEq : (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest)[k] = rest[k - 8] := by
        rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k' <;> first | omega | simp
      rw [htailEq]
      exact h2
  | [b0] =>
    have hk0 : k = 0 := by simp at hk; omega
    subst hk0; exact ⟨by simp [romWords64], romWord64_extract_byte [b0] (by simp) 0 (by simp)⟩
  | [b0, b1] =>
    have hk2 : k < 2 := by simpa using hk
    have hkdiv : k / 8 = 0 := Nat.div_eq_of_lt (by omega)
    have hkmod : k % 8 = k := Nat.mod_eq_of_lt (by omega)
    refine ⟨by rw [hkdiv]; simp [romWords64], ?_⟩
    simp only [romWords64, hkdiv, List.getElem_cons_zero, hkmod]
    exact romWord64_extract_byte [b0, b1] (by simp) k (by simp [hk2])
  | [b0, b1, b2] =>
    have hk3 : k < 3 := by simpa using hk
    have hkdiv : k / 8 = 0 := Nat.div_eq_of_lt (by omega)
    have hkmod : k % 8 = k := Nat.mod_eq_of_lt (by omega)
    refine ⟨by rw [hkdiv]; simp [romWords64], ?_⟩
    simp only [romWords64, hkdiv, List.getElem_cons_zero, hkmod]
    exact romWord64_extract_byte [b0, b1, b2] (by simp) k (by simp [hk3])
  | [b0, b1, b2, b3] =>
    have hk4 : k < 4 := by simpa using hk
    have hkdiv : k / 8 = 0 := Nat.div_eq_of_lt (by omega)
    have hkmod : k % 8 = k := Nat.mod_eq_of_lt (by omega)
    refine ⟨by rw [hkdiv]; simp [romWords64], ?_⟩
    simp only [romWords64, hkdiv, List.getElem_cons_zero, hkmod]
    exact romWord64_extract_byte [b0, b1, b2, b3] (by simp) k (by simp [hk4])
  | [b0, b1, b2, b3, b4] =>
    have hk5 : k < 5 := by simpa using hk
    have hkdiv : k / 8 = 0 := Nat.div_eq_of_lt (by omega)
    have hkmod : k % 8 = k := Nat.mod_eq_of_lt (by omega)
    refine ⟨by rw [hkdiv]; simp [romWords64], ?_⟩
    simp only [romWords64, hkdiv, List.getElem_cons_zero, hkmod]
    exact romWord64_extract_byte [b0, b1, b2, b3, b4] (by simp) k (by simp [hk5])
  | [b0, b1, b2, b3, b4, b5] =>
    have hk6 : k < 6 := by simpa using hk
    have hkdiv : k / 8 = 0 := Nat.div_eq_of_lt (by omega)
    have hkmod : k % 8 = k := Nat.mod_eq_of_lt (by omega)
    refine ⟨by rw [hkdiv]; simp [romWords64], ?_⟩
    simp only [romWords64, hkdiv, List.getElem_cons_zero, hkmod]
    exact romWord64_extract_byte [b0, b1, b2, b3, b4, b5] (by simp) k (by simp [hk6])
  | [b0, b1, b2, b3, b4, b5, b6] =>
    have hk7 : k < 7 := by simpa using hk
    have hkdiv : k / 8 = 0 := Nat.div_eq_of_lt (by omega)
    have hkmod : k % 8 = k := Nat.mod_eq_of_lt (by omega)
    refine ⟨by rw [hkdiv]; simp [romWords64], ?_⟩
    simp only [romWords64, hkdiv, List.getElem_cons_zero, hkmod]
    exact romWord64_extract_byte [b0, b1, b2, b3, b4, b5, b6] (by simp) k (by simp [hk7])

theorem readWord64_writeWord64_tabOff {m : ByteMem} {base : BitVec 64} {need : Nat}
    (hneed : base.toNat + need ≤ 2 ^ 64) {off1 off2 : Int}
    (hnn1 : 0 ≤ off1) (hnn2 : 0 ≤ off2)
    (hb1 : off1.toNat + 8 ≤ need) (hb2 : off2.toNat + 8 ≤ need)
    (hdisj : off1.toNat + 8 ≤ off2.toNat ∨ off2.toNat + 8 ≤ off1.toNat) (w : BitVec 64) :
    readWord64 (writeWord64 m (base + BitVec.ofInt 64 off2) w) (base + BitVec.ofInt 64 off1) =
      readWord64 m (base + BitVec.ofInt 64 off1) := by
  have hd := memSpan_offset_disjoint_offset hneed hb1 hb2 hdisj
  have h1 : BitVec.ofInt 64 off1 = BitVec.ofNat 64 off1.toNat := by
    rw [← Int.toNat_of_nonneg hnn1, BitVec.ofInt_natCast]; rfl
  have h2 : BitVec.ofInt 64 off2 = BitVec.ofNat 64 off2.toNat := by
    rw [← Int.toNat_of_nonneg hnn2, BitVec.ofInt_natCast]; rfl
  rw [h1, h2]
  have hm := MemSpan.disjoint_to_memDisjoint
    (by
      dsimp only [MemSpan.valid]
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
    (by
      dsimp only [MemSpan.valid]
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
    hd
  exact readWord64_writeWord64_disjoint _ _ _ _ fun i1 i2 hi1 hi2 heq =>
    hm _ ⟨i1, hi1, rfl⟩ ⟨i2, hi2, heq⟩

theorem bitvec_slt_zero_iff (n : Nat) (hn : n < 2 ^ 64) :
    BitVec.slt (BitVec.ofNat 64 n) 0#64 = decide (2 ^ 63 ≤ n) := by
  rw [BitVec.slt, show (0#64 : BitVec 64).toInt = 0 from rfl,
    BitVec.toInt_eq_toNat_bmod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  apply Bool.eq_iff_iff.mpr
  simp only [Int.bmod, decide_eq_true_eq]
  have h264 : ((2 ^ 64 : Nat) : Int) = 18446744073709551616 := rfl
  have hmod : (n : Int) % ((2 ^ 64 : Nat) : Int) = (n : Int) :=
    Int.emod_eq_of_lt (by omega) (by rw [h264]; omega)
  rw [hmod]
  split <;> omega

end ConAgua.RISCV.Bridge
