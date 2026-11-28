import ConAgua.RISCV.Bridge.CheckerDriverSetup

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# End-to-End Backward Soundness of Linked Flat Checker ROM (`ConAgua.RISCV.Bridge.CheckerDriverFlat`)

Connects LP64 accepting executions of `checkerRom` through both sequential driver phases
(`MODE = 3` then `MODE = 2`) to `ConAgua.Final.{TwinAccepts, Models, NoFalse}` and `RegsRestored`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard Lean axioms only.
-/

namespace ConAgua.RISCV.Bridge

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Compiler
open ConAgua.RISCV.Linker

/-! ## 4. End-to-End Linked Checker ROM Backward Soundness Theorems -/

private theorem checkerRom_accept_runs_and_regs
    (hPlat : System.Platform.numBits = 64)
    (initSt : RV64.State) (hpc0 : initSt.pc = 0#64)
    {inBase pinsBase regionBase : BitVec 64}
    {inBytes pins : ByteArray}
    (ha0 : initSt.getReg AbiReg.a0 = inBase)
    (ha1 : initSt.getReg AbiReg.a1 = BitVec.ofNat 64 inBytes.size)
    (ha2 : initSt.getReg AbiReg.a2 = pinsBase)
    (ha3 : initSt.getReg AbiReg.a3 = BitVec.ofNat 64 pins.size)
    (ha4 : initSt.getReg AbiReg.a4 = regionBase)
    (hin64 : inBytes.size < 2 ^ 64) (hpins64 : pins.size < 2 ^ 64)
    (hIn64 : inBase.toNat + inBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjInPins : MemSpan.disjoint ⟨inBase, inBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjInReg : MemSpan.disjoint ⟨inBase, inBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hInMem : ∀ i, (hi : i < inBytes.size) → initSt.mem (inBase + BitVec.ofNat 64 i) = inBytes[i].toBitVec)
    (hPinsMem : ∀ i, (hi : i < pins.size) → initSt.mem (pinsBase + BitVec.ofNat 64 i) = pins[i].toBitVec)
    (hRegZero : ∀ k, k < abiNeed checkerTabMini → initSt.mem (regionBase + BitVec.ofNat 64 k) = 0#8)
    (hStackA : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (phaseAInitMem inBytes pins) ≤ abiStack)
    (hStackB : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (phaseBInitMem inBytes pins) ≤ abiStack)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : checkerRom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run checkerRom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha0Out : finalSt.getReg AbiReg.a0 = acceptWord.toBitVec)
    (ha1Out : finalSt.getReg AbiReg.a1 = 0#64) :
    inBytes.size < 2 ^ 63 ∧ pins.size < 2 ^ 63 ∧
    (RegsRestored initSt finalSt ∧ finalSt.getReg AbiReg.ra = initSt.getReg AbiReg.ra) ∧
    ∃ rs₁ m₁ rs₂ m₂,
      _root_.L.run checkerProgMini (abiFuel - 1) "check" [] (phaseAInitMem inBytes pins) = .ok (rs₁, m₁) ∧
      9223372036854775808 ≤ UInt64.toNat (rs₁.headD 0) ∧
      _root_.L.run checkerProgMini (abiFuel - 1) "check" [] (phaseBMem m₁ (rs₁.headD 0)) = .ok (rs₂, m₂) ∧
      rs₂.headD 0 = acceptWord := by
  let LA := checkerLayoutA inBase pinsBase regionBase inBytes.size pins.size
    hIn64 hPins64 hRegAlign hReg64 hDisjInPins hDisjInReg hDisjPinsReg
  let LB := checkerLayoutB inBase pinsBase regionBase inBytes.size pins.size
    hIn64 hPins64 hRegAlign hReg64 hDisjInPins hDisjInReg hDisjPinsReg
  let preCallA := drvPfx ++ drvNeedLi checkerTabMini ++ drvBootCheck checkerTabMini ++
    [Asm.call drvInitLabel] ++ drvPhaseASetup checkerTabMini
  let tailB := drvPhaseBSetup checkerTabMini ++ drvPhaseBCall ++ drvDoneStub ++
    drvExhaustedStub ++ drvErrPrefix ++ drvAbortPrefix ++
    drvRetRestoreStub checkerTabMini ++ drvInitSubAsm checkerTabMini ++
    checkerCmpDriverAsm checkerTabMini ++ checkerFnsAsm
  have ha1Ne1 : finalSt.getReg AbiReg.a1 ≠ 1#64 := by rw [ha1Out]; decide
  have halignSave : isAligned (regionBase + BitVec.ofInt 64 (checkerTabMini.saveBase 0)) 8 = true :=
    checkerTabMini_saveBase_align regionBase hRegAlign
  have hTabSaveA : checkerTabMini.saveBase 0 + 128 ≤ (LA.tabBytes : Int) := by
    simp only [LA, checkerLayoutA]; exact checkerTabMini_saveBase_le_abiSlot
  have hTabSaveB : checkerTabMini.saveBase 0 + 128 ≤ (LB.tabBytes : Int) := by
    simp only [LB, checkerLayoutB, checkerLayoutBGen, checkerLayoutA]
    exact checkerTabMini_saveBase_le_abiSlot
  obtain ⟨hin63, hpins63, kA0, stA0, hrunA0, hpcA0, hgpA0, hspA0, hs0A0,
      ht0A0, ht1A0, hsavedA0, hMemRelA0, hHdrA0⟩ :=
    phaseA_prefix_sim initSt hpc0 ha0 ha1 ha2 ha3 ha4 hin64 hpins64 hIn64 hPins64
      hRegAlign hReg64 hDisjInPins hDisjInReg hDisjPinsReg hInMem hPinsMem hRegZero
      hRetOut hrun hret ha1Ne1
  have hlinkFull : checkerLM.linkSpec (preCallA ++ drvPhaseACall ++ tailB) =
      .ok (checkerEnv.code, checkerEnv.labels) := by
    have h := checkerChipAsm_linkSpec
    rw [checkerChipAsm_eq', checkerDriverAsm_decomp] at h
    change checkerLM.linkSpec (preCallA ++ drvPhaseACall ++ tailB) = .ok (checkerCode, checkerLabels)
    simpa only [drvAllBeforeEx, drvPreDone, preCallA, tailB, List.append_assoc] using h
  -- Phase A call
  have hlinkCallA : checkerLM.linkSpec (preCallA ++ [Asm.call (fnLabel "check")] ++
      ([Asm.bge AbiReg.a0 AbiReg.zero drvDoneLabel] ++ tailB)) =
      .ok (checkerEnv.code, checkerEnv.labels) := by
    simpa only [drvPhaseACall, List.cons_append, List.nil_append, List.append_assoc] using hlinkFull
  have hpcCallA_64 := linkResolved_sub_pc64 checkerEnv preCallA [Asm.call (fnLabel "check")] _ hlinkCallA
  have hltCallA_64 : 4 * (checkerLM.totalSize preCallA + checkerLM.itemSize (.call (fnLabel "check"))) < 2 ^ 64 := by
    simpa only [Asm.call, checkerLM.totalSize_singleton] using hpcCallA_64
  obtain ⟨tgtA, kCallA, stA1, _, hlkpA, hrunCallA, hpcCallA, hregsCallA, hmCallA⟩ :=
    step_item_call_lm checkerLM checkerEnv.hrom preCallA _ (fnLabel "check") hlinkCallA hltCallA_64 stA0 hpcA0
  obtain ⟨checkFd, hCheck, hNparams⟩ := checkerProgMini_lookup_check
  have hargsAl : isAligned (regionBase + BitVec.ofInt 64 checkerTabMini.args) 8 = true := by
    rw [checkerTabMini_args_eq, BitVec.ofInt_natCast]
    exact isAligned8_add_nat_mul8 regionBase hRegAlign _ (by
      have harg := checkerTabMini_args_lt
      rw [checkerTabMini_args_eq, Int.toNat_natCast] at harg
      omega)
  have hNeedA : LA.stackLimit.toNat + fnFrameBytes checkFd +
      stackNeedB checkerProgMini (abiFuel - 2) checkFd.body { mem := phaseAInitMem inBytes pins, loc := Locals.init [] } ≤
      LA.stackTop.toNat := by
    unfold runStackNeedB at hStackA
    rw [show abiFuel - 1 = (abiFuel - 2) + 1 from by simp [abiFuel], hCheck] at hStackA
    dsimp only at hStackA
    have hdiff : LA.stackTop.toNat - LA.stackLimit.toNat = abiStack :=
      checkerLayout_stack_diff regionBase hReg64
    have hle : LA.stackLimit.toNat ≤ LA.stackTop.toNat := LA.hStackLe
    omega
  have hcallA := compileFns_call_sim_gen checkerEnv LA checkerProgMini
    checkerProgMini_progOkB checkerProgMini_progArgsOkB checkerFnsLinked (abiFuel - 2)
    "check" checkFd [] (phaseAInitMem inBytes pins)
    LA.stackTop (stA1.getReg AbiReg.ra) (regionBase + BitVec.ofInt 64 checkerTabMini.args)
    (checkerLM.totalSize preCallA + checkerLM.itemSize (.call (fnLabel "check")))
    hCheck (by rw [hNparams]; decide) (by simp [abiFuel]) hNeedA (Nat.le_refl _) LA.hTopAlign hargsAl
    (by
      have hra : stA1.getReg AbiReg.ra =
          BitVec.ofNat 64 (4 * (checkerLM.totalSize preCallA + checkerLM.itemSize (.call (fnLabel "check")))) :=
        (hregsCallA.getReg_eq (by decide)).symm.trans (getReg_setReg_eq stA0 AbiReg.ra _ (by decide))
      rw [hra]; exact mul4_and_not1_cd _ hltCallA_64)
    (fun _ hj => absurd hj (Nat.not_lt_zero _))
    tgtA stA1 hlkpA hpcCallA
    ((hregsCallA.getReg_eq (by decide)).symm.trans ((getReg_setReg_ne stA0 AbiReg.ra _ _ (by decide)).trans hgpA0))
    ((hregsCallA.getReg_eq (by decide)).symm.trans ((getReg_setReg_ne stA0 AbiReg.ra _ _ (by decide)).trans hspA0))
    rfl
    ((hregsCallA.getReg_eq (by decide)).symm.trans ((getReg_setReg_ne stA0 AbiReg.ra _ _ (by decide)).trans hs0A0))
    (fun _ => (hregsCallA.getReg_eq (by decide)).symm.trans ((getReg_setReg_ne stA0 AbiReg.ra _ _ (by decide)).trans ht0A0))
    (by rw [hmCallA]; exact hMemRelA0) (by rw [hmCallA]; exact hHdrA0)
    (fun _ hj => absurd hj (Nat.not_lt_zero _))
  have hgpA1 : stA1.getReg AbiReg.gp = regionBase :=
    (hregsCallA.getReg_eq (by decide)).symm.trans ((getReg_setReg_ne stA0 AbiReg.ra _ _ (by decide)).trans hgpA0)
  have hsavedA1 : DrvRegsSaved LA.T initSt stA1.mem := by
    change DrvRegsSaved regionBase initSt stA1.mem
    rw [hmCallA]; exact hsavedA0
  have hrunToA1 : RV64.run checkerEnv.rom (kA0 + kCallA) initSt = .cont stA1 := by
    rw [run_add, hrunA0]; exact hrunCallA
  -- Eliminate error outcomes of Phase A
  cases hexA : execB checkerProgMini (abiFuel - 2) checkFd.body { mem := phaseAInitMem inBytes pins, loc := Locals.init [] } with
  | error errA =>
    rw [hexA] at hcallA
    cases errA with
    | outOfFuel =>
      obtain ⟨kF, rF, hrunF, hpcF, htrF, houtF⟩ := hcallA
      have hsavedF : DrvRegsSaved regionBase initSt rF.mem :=
        drvRegsSaved_of_callWriteMask_eq LA LA.stackTop hTabSaveA houtF hsavedA1 rfl
      have hgpF : rF.getReg AbiReg.gp = regionBase := htrF.gp.trans hgpA1
      obtain ⟨mEx, rEx, hrunEx, hpcEx, _, _, _, ha1Ex, _⟩ :=
        checker_exhausted_returns initSt regionBase halignSave rF hpcF hgpF hsavedF
      have htot : RV64.run checkerEnv.rom (kA0 + kCallA + kF + mEx) initSt = .cont rEx := by
        rw [run_add, run_add, hrunToA1]; dsimp only; rw [hrunF]; exact hrunEx
      have heqFin := run_ret_deterministic checkerEnv.rom _ _ initSt hrun htot hret hpcEx hRetOut
      exact absurd (ha1Out.symm.trans (heqFin ▸ ha1Ex)) (by decide)
    | abort codeA =>
      obtain ⟨kF, rF, hrunF, hpcF, _, htrF, houtF⟩ := hcallA
      have hsavedF : DrvRegsSaved regionBase initSt rF.mem :=
        drvRegsSaved_of_callWriteMask_eq LA LA.stackTop hTabSaveA houtF hsavedA1 rfl
      have hgpF : rF.getReg AbiReg.gp = regionBase := htrF.gp.trans hgpA1
      obtain ⟨mAb, rAb, hrunAb, hpcAb, _, _, _, ha1Ab, _⟩ :=
        checker_abort_returns initSt regionBase halignSave rF hpcF hgpF hsavedF
      have htot : RV64.run checkerEnv.rom (kA0 + kCallA + kF + mAb) initSt = .cont rAb := by
        rw [run_add, run_add, hrunToA1]; dsimp only; rw [hrunF]; exact hrunAb
      have heqFin := run_ret_deterministic checkerEnv.rom _ _ initSt hrun htot hret hpcAb hRetOut
      exact absurd (ha1Out.symm.trans (heqFin ▸ ha1Ab)) (by decide)
    | oob | noFun _ =>
      obtain ⟨kF, rF, hrunF, hpcF, htrF, houtF⟩ := hcallA
      have hsavedF : DrvRegsSaved regionBase initSt rF.mem :=
        drvRegsSaved_of_callWriteMask_eq LA LA.stackTop hTabSaveA houtF hsavedA1 rfl
      have hgpF : rF.getReg AbiReg.gp = regionBase := htrF.gp.trans hgpA1
      obtain ⟨mEr, rEr, hrunEr, hpcEr, _, _, _, ha1Er, _⟩ :=
        checker_err_returns initSt regionBase halignSave rF hpcF hgpF hsavedF
      have htot : RV64.run checkerEnv.rom (kA0 + kCallA + kF + mEr) initSt = .cont rEr := by
        rw [run_add, run_add, hrunToA1]; dsimp only; rw [hrunF]; exact hrunEr
      have heqFin := run_ret_deterministic checkerEnv.rom _ _ initSt hrun htot hret hpcEr hRetOut
      exact absurd (ha1Out.symm.trans (heqFin ▸ ha1Er)) (by decide)
  | ok resA =>
    rcases resA with ⟨sigA, stA', bA'⟩
    rw [hexA] at hcallA
    dsimp only at hcallA
    obtain ⟨kFA, rA, hrunFA, hpcRA, hgpRA, _, _, _, _, _, _, hmRA, _, hresRA, houtRA⟩ := hcallA
    have hsavedRA : DrvRegsSaved regionBase initSt rA.mem :=
      drvRegsSaved_of_callWriteMask_eq LA LA.stackTop hTabSaveA houtRA hsavedA1 rfl
    have hrunToRA : RV64.run checkerEnv.rom (kA0 + kCallA + kFA) initSt = .cont rA := by
      rw [run_add, hrunToA1]; exact hrunFA
    have hrunB_A : runB checkerProgMini (abiFuel - 1) "check" [] (phaseAInitMem inBytes pins) =
        .ok (sigA.retVal, stA'.mem, bA') := by
      unfold runB
      rw [show abiFuel - 1 = (abiFuel - 2) + 1 from by simp [abiFuel], hCheck]
      dsimp only; rw [hexA]
    have hMiniA : _root_.L.run checkerProgMini (abiFuel - 1) "check" [] (phaseAInitMem inBytes pins) =
        .ok (sigA.retVal, stA'.mem) := by
      have h := execB_sound_run checkerProgMini (abiFuel - 1) "check" [] (phaseAInitMem inBytes pins)
      rw [hrunB_A] at h; exact h
    have hra0 : rA.getReg AbiReg.a0 = (sigA.retVal.headD 0).toBitVec := resultsInState_a0 hresRA
    -- Branch `bge a0, zero, drvDoneLabel`
    let pBrA := preCallA ++ [Asm.call (fnLabel "check")]
    have hpcRA' : rA.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize pBrA) := by
      rw [hpcRA]; dsimp only [pBrA]
      simp only [checkerLM.totalSize_append, Asm.call, checkerLM.totalSize_singleton]
    have hlDone : lookupLabel checkerEnv.labels drvDoneLabel = some (checkerLM.totalSize
        (preCallA ++ drvPhaseACall ++ drvPhaseBSetup checkerTabMini ++ drvPhaseBCall)) := by
      have h := checkerChipAsm_linkSpec
      rw [checkerChipAsm_eq', checkerDriverAsm_decomp, drvAllBeforeEx, drvPreDone] at h
      have hsp : drvDoneStub = [Asm.lbl drvDoneLabel] ++
          [Asm.addi AbiReg.a1 AbiReg.zero 0#12, Asm.j retRestoreLabel] := rfl
      have hlinkD : checkerLM.linkSpec ((preCallA ++ drvPhaseACall ++ drvPhaseBSetup checkerTabMini ++ drvPhaseBCall) ++
          [Asm.lbl drvDoneLabel] ++
          ([Asm.addi AbiReg.a1 AbiReg.zero 0#12, Asm.j retRestoreLabel] ++
           drvExhaustedStub ++ drvErrPrefix ++ drvAbortPrefix ++
           drvRetRestoreStub checkerTabMini ++ drvInitSubAsm checkerTabMini ++
           checkerCmpDriverAsm checkerTabMini ++ checkerFnsAsm)) =
          Except.ok (checkerEnv.code, checkerEnv.labels) := by
        change _ = Except.ok (checkerCode, checkerLabels)
        rw [hsp] at h
        simpa only [preCallA, List.append_assoc] using h
      exact linkResolved_lbl_lm checkerLM _ drvDoneLabel _ hlinkD
    have hlBrA : checkerLM.linkSpec (pBrA ++ [Asm.bge AbiReg.a0 AbiReg.zero drvDoneLabel] ++ tailB) =
        .ok (checkerEnv.code, checkerEnv.labels) := by
      simpa only [pBrA, List.append_assoc] using hlinkCallA
    have hbrA := run_br_step checkerEnv pBrA tailB .bge AbiReg.a0 AbiReg.zero drvDoneLabel _ hlDone (by decide) hlBrA rA hpcRA'
    have hretAge : 9223372036854775808 ≤ UInt64.toNat (sigA.retVal.headD 0) := by
      by_cases hge : 2 ^ 63 ≤ (sigA.retVal.headD 0).toNat
      · exact hge
      · have hlt : (rA.getReg AbiReg.a0).toNat < 2 ^ 63 := by
          rw [hra0]; exact Nat.lt_of_not_le hge
        have hbvEq : BitVec.ofNat 64 (rA.getReg AbiReg.a0).toNat = rA.getReg AbiReg.a0 :=
          BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (rA.getReg AbiReg.a0).isLt])
        have hevTrue : evalBranch .bge (rA.getReg AbiReg.a0) (rA.getReg AbiReg.zero) = true := by
          have hz : rA.getReg AbiReg.zero = 0#64 := rfl
          rw [hz]; dsimp only [evalBranch]
          rw [← hbvEq, bitvec_slt_zero_iff _ (rA.getReg AbiReg.a0).isLt]
          simp [hlt]
        rw [hevTrue] at hbrA
        obtain ⟨kBr, stD, _, hrunBr, hpcD, hothBr, _, hmBr⟩ := hbrA
        simp only [↓reduceIte] at hpcD
        have hgpD : stD.getReg AbiReg.gp = regionBase := (hothBr _ (by decide)).trans hgpRA
        have hsavedD : DrvRegsSaved regionBase initSt stD.mem := by rw [hmBr]; exact hsavedRA
        obtain ⟨mD, rD, hrunD, hpcD', _, _, ha0D, _, _⟩ :=
          drvDone_returns initSt regionBase halignSave stD hpcD hgpD hsavedD
        have htot : RV64.run checkerEnv.rom (kA0 + kCallA + kFA + kBr + mD) initSt = .cont rD := by
          rw [run_add, run_add, hrunToRA]; dsimp only; rw [hrunBr]; exact hrunD
        have heqFin := run_ret_deterministic checkerEnv.rom _ _ initSt hrun htot hret hpcD' hRetOut
        have heqAcc : sigA.retVal.headD 0 = acceptWord := by
          apply UInt64.toBitVec_inj.mp
          rw [← hra0, ← hothBr _ (by decide), ← ha0D, ← heqFin, ha0Out]
        have hne1 : sigA.retVal.headD 0 ≠ 1 := by
          rw [heqAcc]; decide
        have hLA := hMiniA
        dsimp only [phaseAInitMem] at hLA
        rw [loadMemMini_eq_loadMemM] at hLA
        obtain ⟨PA, m₇, m, hF, _, _, hres⟩ :=
          L.Checker.checkA_run inBytes pins (fun _ => abiWords)
            (inputsOK_of_mini (sz := fun _ : _root_.L.TieredArray => abiWords)
              ⟨hPlat, hin63, hpins63, fun _ => by simp only [abiWords]; omega⟩)
            3 (Or.inr rfl) (abiFuel - 1) (by simp [abiFuel]) sigA.retVal stA'.mem hLA hne1
        have hsz : PA.ds.size < 2 ^ 63 := by
          have := hF.build.decls.room; have := hF.build.decls.dsize; omega
        have hk : (sigA.retVal.headD 0).toNat = 9223372036854775808 + PA.ds.size := by
          rw [hres]
          change ((BitVec.ofNat 64 9223372036854775808 + BitVec.ofNat 64 PA.ds.size).toNat) = _
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
    -- Not taken branch into Phase B setup
    have hevFalse : evalBranch .bge (rA.getReg AbiReg.a0) (rA.getReg AbiReg.zero) = false := by
      have hz : rA.getReg AbiReg.zero = 0#64 := rfl
      have hlt2 : 2 ^ 63 ≤ (rA.getReg AbiReg.a0).toNat := by rw [hra0]; exact hretAge
      have hbvEq : BitVec.ofNat 64 (rA.getReg AbiReg.a0).toNat = rA.getReg AbiReg.a0 :=
        BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (rA.getReg AbiReg.a0).isLt])
      rw [hz]; dsimp only [evalBranch]
      rw [← hbvEq, bitvec_slt_zero_iff _ (rA.getReg AbiReg.a0).isLt]
      simp [hlt2]
    rw [hevFalse] at hbrA
    obtain ⟨kBrA, stB0, _, hrunBrA, hpcB0, hothBrA, _, hmBrA⟩ := hbrA
    simp only [Bool.false_eq_true, ↓reduceIte] at hpcB0
    let pB0 := preCallA ++ drvPhaseACall
    have hpcB0' : stB0.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize pB0) := by
      rw [hpcB0]; exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (by
        simp only [pB0, pBrA, drvPhaseACall, checkerLM.totalSize_append,
          checkerLM.totalSize_cons, checkerLM.totalSize_nil, Nat.add_zero, Nat.add_assoc]; rfl)
    have hlPhB : checkerLM.linkSpec (pB0 ++ drvPhaseBSetup checkerTabMini ++
        (drvPhaseBCall ++ drvDoneStub ++ drvExhaustedStub ++ drvErrPrefix ++
         drvAbortPrefix ++ drvRetRestoreStub checkerTabMini ++ drvInitSubAsm checkerTabMini ++
         checkerCmpDriverAsm checkerTabMini ++ checkerFnsAsm)) =
        .ok (checkerEnv.code, checkerEnv.labels) := by
      simpa only [pB0, tailB, List.append_assoc] using hlinkFull
    obtain ⟨kB1, stB1, hrunB1, hpcB1, hgpB1, hs0B1, hspB1, _, ht0B1, ht1B1, houtB1,
        hTopB, hLimB, hPhiB, hPloB, hModeB, h180BB, h180LB, h182BB, h182LB, h181BB, h181LB⟩ :=
      drvPhaseBSetup_sim regionBase hRegAlign hReg64 (sigA.retVal.headD 0) hretAge pB0 _ hlPhB
        stB0 hpcB0' ((hothBrA _ (by decide)).trans hgpRA) ((hothBrA _ (by decide)).trans hra0)
    have hsavedB1 : DrvRegsSaved regionBase initSt stB1.mem :=
      drvRegsSaved_of_progMemOutside houtB1 (phaseBWriteSpan_disj_callerSave regionBase hReg64)
        (by rw [hmBrA]; exact hsavedRA)
    have hm1Sz : (stA'.mem.words (.t0 L.Arena.OUT)).size = abiWords := by
      rw [minil_run_words_size hMiniA (.t0 L.Arena.OUT)]
      simp [phaseAInitMem, loadMemMini]
    have hMemRelB : ProgMemRel checkerTabMini LB stB1.mem (phaseBMem stA'.mem (sigA.retVal.headD 0)) :=
      phaseB_progMemRel_of_phaseA hIn64 hPins64 hRegAlign hReg64 hDisjInPins hDisjInReg hDisjPinsReg
        hmRA hm1Sz (by rw [hmBrA] at houtB1; exact houtB1)
        hPhiB hPloB hModeB h180BB h180LB h182BB h182LB h181BB h181LB
    have hHdrB : TabHeaderOk LB stB1.mem := ⟨hTopB, hLimB⟩
    -- Phase B call
    let preCallB := pB0 ++ drvPhaseBSetup checkerTabMini
    have hpcB1' : stB1.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize preCallB) := by
      simpa only [preCallB, checkerLM.totalSize_append] using hpcB1
    have hlCallB : checkerLM.linkSpec (preCallB ++ [Asm.call (fnLabel "check")] ++
        (drvDoneStub ++ drvExhaustedStub ++ drvErrPrefix ++
         drvAbortPrefix ++ drvRetRestoreStub checkerTabMini ++ drvInitSubAsm checkerTabMini ++
         checkerCmpDriverAsm checkerTabMini ++ checkerFnsAsm)) =
        .ok (checkerEnv.code, checkerEnv.labels) := by
      simpa only [preCallB, drvPhaseBCall, List.append_assoc] using hlPhB
    have hpcCallB_64 := linkResolved_sub_pc64 checkerEnv preCallB [Asm.call (fnLabel "check")] _ hlCallB
    have hltCallB_64 : 4 * (checkerLM.totalSize preCallB + checkerLM.itemSize (.call (fnLabel "check"))) < 2 ^ 64 := by
      simpa only [Asm.call, checkerLM.totalSize_singleton] using hpcCallB_64
    obtain ⟨tgtB, kCallB, stB2, _, hlkpB, hrunCallB, hpcCallB, hregsCallB, hmCallB⟩ :=
      step_item_call_lm checkerLM checkerEnv.hrom preCallB _ (fnLabel "check") hlCallB hltCallB_64 stB1 hpcB1'
    have hNeedB : LB.stackLimit.toNat + fnFrameBytes checkFd +
        stackNeedB checkerProgMini (abiFuel - 2) checkFd.body
          { mem := phaseBMem stA'.mem (sigA.retVal.headD 0), loc := Locals.init [] } ≤
        LB.stackTop.toNat := by
      have hBInit : phaseBInitMem inBytes pins = phaseBMem stA'.mem (sigA.retVal.headD 0) := by
        simp [phaseBInitMem, hrunB_A]
      rw [hBInit] at hStackB
      unfold runStackNeedB at hStackB
      rw [show abiFuel - 1 = (abiFuel - 2) + 1 from by simp [abiFuel], hCheck] at hStackB
      dsimp only at hStackB
      have hdiff : LB.stackTop.toNat - LB.stackLimit.toNat = abiStack :=
        checkerLayout_stack_diff regionBase hReg64
      have hle : LB.stackLimit.toNat ≤ LB.stackTop.toNat := LB.hStackLe
      omega
    have hcallB := compileFns_call_sim_gen checkerEnv LB checkerProgMini
      checkerProgMini_progOkB checkerProgMini_progArgsOkB checkerFnsLinked (abiFuel - 2)
      "check" checkFd [] (phaseBMem stA'.mem (sigA.retVal.headD 0))
      LB.stackTop (stB2.getReg AbiReg.ra) (regionBase + BitVec.ofInt 64 checkerTabMini.args)
      (checkerLM.totalSize preCallB + checkerLM.itemSize (.call (fnLabel "check")))
      hCheck (by rw [hNparams]; decide) (by simp [abiFuel]) hNeedB (Nat.le_refl _) LB.hTopAlign hargsAl
      (by
        have hra : stB2.getReg AbiReg.ra =
            BitVec.ofNat 64 (4 * (checkerLM.totalSize preCallB + checkerLM.itemSize (.call (fnLabel "check")))) :=
          (hregsCallB.getReg_eq (by decide)).symm.trans (getReg_setReg_eq stB1 AbiReg.ra _ (by decide))
        rw [hra]; exact mul4_and_not1_cd _ hltCallB_64)
      (fun _ hj => absurd hj (Nat.not_lt_zero _))
      tgtB stB2 hlkpB hpcCallB
      ((hregsCallB.getReg_eq (by decide)).symm.trans ((getReg_setReg_ne stB1 AbiReg.ra _ _ (by decide)).trans hgpB1))
      ((hregsCallB.getReg_eq (by decide)).symm.trans ((getReg_setReg_ne stB1 AbiReg.ra _ _ (by decide)).trans hspB1))
      rfl
      ((hregsCallB.getReg_eq (by decide)).symm.trans ((getReg_setReg_ne stB1 AbiReg.ra _ _ (by decide)).trans hs0B1))
      (fun _ => (hregsCallB.getReg_eq (by decide)).symm.trans ((getReg_setReg_ne stB1 AbiReg.ra _ _ (by decide)).trans ht0B1))
      (by rw [hmCallB]; exact hMemRelB) (by rw [hmCallB]; exact hHdrB)
      (fun _ hj => absurd hj (Nat.not_lt_zero _))
    have hgpB2 : stB2.getReg AbiReg.gp = regionBase :=
      (hregsCallB.getReg_eq (by decide)).symm.trans ((getReg_setReg_ne stB1 AbiReg.ra _ _ (by decide)).trans hgpB1)
    have hsavedB2 : DrvRegsSaved LB.T initSt stB2.mem := by
      change DrvRegsSaved regionBase initSt stB2.mem
      rw [hmCallB]; exact hsavedB1
    have hrunToB2 : RV64.run checkerEnv.rom (kA0 + kCallA + kFA + kBrA + kB1 + kCallB) initSt = .cont stB2 := by
      rw [run_add, run_add, run_add, hrunToRA]; dsimp only; rw [hrunBrA]; dsimp only; rw [hrunB1]; exact hrunCallB
    cases hexB : execB checkerProgMini (abiFuel - 2) checkFd.body
        { mem := phaseBMem stA'.mem (sigA.retVal.headD 0), loc := Locals.init [] } with
    | error errB =>
      rw [hexB] at hcallB
      cases errB with
      | outOfFuel =>
        obtain ⟨kF, rF, hrunF, hpcF, htrF, houtF⟩ := hcallB
        have hsavedF : DrvRegsSaved regionBase initSt rF.mem :=
          drvRegsSaved_of_callWriteMask_eq LB LB.stackTop hTabSaveB houtF hsavedB2 rfl
        have hgpF : rF.getReg AbiReg.gp = regionBase := htrF.gp.trans hgpB2
        obtain ⟨mEx, rEx, hrunEx, hpcEx, _, _, _, ha1Ex, _⟩ :=
          checker_exhausted_returns initSt regionBase halignSave rF hpcF hgpF hsavedF
        have htot : RV64.run checkerEnv.rom (kA0 + kCallA + kFA + kBrA + kB1 + kCallB + kF + mEx) initSt =
            .cont rEx := by
          rw [run_add, run_add, hrunToB2]; dsimp only; rw [hrunF]; exact hrunEx
        have heqFin := run_ret_deterministic checkerEnv.rom _ _ initSt hrun htot hret hpcEx hRetOut
        exact absurd (ha1Out.symm.trans (heqFin ▸ ha1Ex)) (by decide)
      | abort codeB =>
        obtain ⟨kF, rF, hrunF, hpcF, _, htrF, houtF⟩ := hcallB
        have hsavedF : DrvRegsSaved regionBase initSt rF.mem :=
          drvRegsSaved_of_callWriteMask_eq LB LB.stackTop hTabSaveB houtF hsavedB2 rfl
        have hgpF : rF.getReg AbiReg.gp = regionBase := htrF.gp.trans hgpB2
        obtain ⟨mAb, rAb, hrunAb, hpcAb, _, _, _, ha1Ab, _⟩ :=
          checker_abort_returns initSt regionBase halignSave rF hpcF hgpF hsavedF
        have htot : RV64.run checkerEnv.rom (kA0 + kCallA + kFA + kBrA + kB1 + kCallB + kF + mAb) initSt =
            .cont rAb := by
          rw [run_add, run_add, hrunToB2]; dsimp only; rw [hrunF]; exact hrunAb
        have heqFin := run_ret_deterministic checkerEnv.rom _ _ initSt hrun htot hret hpcAb hRetOut
        exact absurd (ha1Out.symm.trans (heqFin ▸ ha1Ab)) (by decide)
      | oob | noFun _ =>
        obtain ⟨kF, rF, hrunF, hpcF, htrF, houtF⟩ := hcallB
        have hsavedF : DrvRegsSaved regionBase initSt rF.mem :=
          drvRegsSaved_of_callWriteMask_eq LB LB.stackTop hTabSaveB houtF hsavedB2 rfl
        have hgpF : rF.getReg AbiReg.gp = regionBase := htrF.gp.trans hgpB2
        obtain ⟨mEr, rEr, hrunEr, hpcEr, _, _, _, ha1Er, _⟩ :=
          checker_err_returns initSt regionBase halignSave rF hpcF hgpF hsavedF
        have htot : RV64.run checkerEnv.rom (kA0 + kCallA + kFA + kBrA + kB1 + kCallB + kF + mEr) initSt =
            .cont rEr := by
          rw [run_add, run_add, hrunToB2]; dsimp only; rw [hrunF]; exact hrunEr
        have heqFin := run_ret_deterministic checkerEnv.rom _ _ initSt hrun htot hret hpcEr hRetOut
        exact absurd (ha1Out.symm.trans (heqFin ▸ ha1Er)) (by decide)
    | ok resB =>
      rcases resB with ⟨sigB, stB', bB'⟩
      rw [hexB] at hcallB
      dsimp only at hcallB
      obtain ⟨kFB, rB, hrunFB, hpcRB, hgpRB, _, _, _, _, _, _, _, _, hresRB, houtRB⟩ := hcallB
      have hsavedRB : DrvRegsSaved regionBase initSt rB.mem :=
        drvRegsSaved_of_callWriteMask_eq LB LB.stackTop hTabSaveB houtRB hsavedB2 rfl
      have hrunB_B : runB checkerProgMini (abiFuel - 1) "check" []
          (phaseBMem stA'.mem (sigA.retVal.headD 0)) = .ok (sigB.retVal, stB'.mem, bB') := by
        unfold runB
        rw [show abiFuel - 1 = (abiFuel - 2) + 1 from by simp [abiFuel], hCheck]
        dsimp only; rw [hexB]
      have hMiniB : _root_.L.run checkerProgMini (abiFuel - 1) "check" []
          (phaseBMem stA'.mem (sigA.retVal.headD 0)) = .ok (sigB.retVal, stB'.mem) := by
        have h := execB_sound_run checkerProgMini (abiFuel - 1) "check" []
          (phaseBMem stA'.mem (sigA.retVal.headD 0))
        rw [hrunB_B] at h; exact h
      have hpcDone : rB.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize (drvPreDone checkerTabMini)) := by
        rw [hpcRB]
        exact congrArg (fun n => BitVec.ofNat 64 (4 * n))
          (by simp only [drvPreDone, preCallB, pB0, preCallA, drvPhaseBCall, Asm.call,
            checkerLM.totalSize_singleton, checkerLM.totalSize_append, Nat.add_assoc])
      obtain ⟨mD, rD, hrunD, hpcD, hregsD, hraD, ha0D, _, _⟩ :=
        drvDone_returns initSt regionBase halignSave rB hpcDone hgpRB hsavedRB
      have hrb0 : rB.getReg AbiReg.a0 = (sigB.retVal.headD 0).toBitVec := resultsInState_a0 hresRB
      have htot : RV64.run checkerEnv.rom (kA0 + kCallA + kFA + kBrA + kB1 + kCallB + kFB + mD) initSt =
          .cont rD := by
        rw [run_add, run_add, hrunToB2]; dsimp only; rw [hrunFB]; exact hrunD
      have heqFin := run_ret_deterministic checkerEnv.rom _ _ initSt hrun htot hret hpcD hRetOut
      have hacc : sigB.retVal.headD 0 = acceptWord := by
        apply UInt64.toBitVec_inj.mp
        rw [← hrb0, ← ha0D, ← heqFin, ha0Out]
      have hrestored : RegsRestored initSt finalSt ∧ finalSt.getReg AbiReg.ra = initSt.getReg AbiReg.ra := by
        rw [heqFin]; exact ⟨hregsD, hraD⟩
      exact ⟨hin63, hpins63, hrestored, sigA.retVal, stA'.mem, sigB.retVal, stB'.mem,
        hMiniA, hretAge, hMiniB, hacc⟩

/-- Any accepting return `(acceptWord, 0)` of `checkerRom` from boot state `initSt` yields
    accepting two-phase `_root_.L.run` executions over `checkerProgMini`. -/
theorem checkerRom_accept_runs
    (hPlat : System.Platform.numBits = 64)
    (initSt : RV64.State) (hpc0 : initSt.pc = 0#64)
    {inBase pinsBase regionBase : BitVec 64}
    {inBytes pins : ByteArray}
    (ha0 : initSt.getReg AbiReg.a0 = inBase)
    (ha1 : initSt.getReg AbiReg.a1 = BitVec.ofNat 64 inBytes.size)
    (ha2 : initSt.getReg AbiReg.a2 = pinsBase)
    (ha3 : initSt.getReg AbiReg.a3 = BitVec.ofNat 64 pins.size)
    (ha4 : initSt.getReg AbiReg.a4 = regionBase)
    (hin64 : inBytes.size < 2 ^ 64) (hpins64 : pins.size < 2 ^ 64)
    (hIn64 : inBase.toNat + inBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjInPins : MemSpan.disjoint ⟨inBase, inBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjInReg : MemSpan.disjoint ⟨inBase, inBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hInMem : ∀ i, (hi : i < inBytes.size) → initSt.mem (inBase + BitVec.ofNat 64 i) = inBytes[i].toBitVec)
    (hPinsMem : ∀ i, (hi : i < pins.size) → initSt.mem (pinsBase + BitVec.ofNat 64 i) = pins[i].toBitVec)
    (hRegZero : ∀ k, k < abiNeed checkerTabMini → initSt.mem (regionBase + BitVec.ofNat 64 k) = 0#8)
    (hStackA : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (phaseAInitMem inBytes pins) ≤ abiStack)
    (hStackB : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (phaseBInitMem inBytes pins) ≤ abiStack)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : checkerRom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run checkerRom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha0Out : finalSt.getReg AbiReg.a0 = acceptWord.toBitVec)
    (ha1Out : finalSt.getReg AbiReg.a1 = 0#64) :
    inBytes.size < 2 ^ 63 ∧ pins.size < 2 ^ 63 ∧
    ∃ rs₁ m₁ rs₂ m₂,
      _root_.L.run checkerProgMini (abiFuel - 1) "check" [] (phaseAInitMem inBytes pins) = .ok (rs₁, m₁) ∧
      9223372036854775808 ≤ UInt64.toNat (rs₁.headD 0) ∧
      _root_.L.run checkerProgMini (abiFuel - 1) "check" [] (phaseBMem m₁ (rs₁.headD 0)) = .ok (rs₂, m₂) ∧
      rs₂.headD 0 = acceptWord := by
  have ⟨h1, h2, _, h4⟩ := checkerRom_accept_runs_and_regs hPlat initSt hpc0 ha0 ha1 ha2 ha3 ha4
    hin64 hpins64 hIn64 hPins64 hRegAlign hReg64 hDisjInPins hDisjInReg hDisjPinsReg
    hInMem hPinsMem hRegZero hStackA hStackB hRetOut hrun hret ha0Out ha1Out
  exact ⟨h1, h2, h4⟩

/-- LP64 callee-saved register and `ra` restoration theorem for `checkerRom`. -/
theorem checkerRom_accept_regsRestored
    (hPlat : System.Platform.numBits = 64)
    (initSt : RV64.State) (hpc0 : initSt.pc = 0#64)
    {inBase pinsBase regionBase : BitVec 64}
    {inBytes pins : ByteArray}
    (ha0 : initSt.getReg AbiReg.a0 = inBase)
    (ha1 : initSt.getReg AbiReg.a1 = BitVec.ofNat 64 inBytes.size)
    (ha2 : initSt.getReg AbiReg.a2 = pinsBase)
    (ha3 : initSt.getReg AbiReg.a3 = BitVec.ofNat 64 pins.size)
    (ha4 : initSt.getReg AbiReg.a4 = regionBase)
    (hin64 : inBytes.size < 2 ^ 64) (hpins64 : pins.size < 2 ^ 64)
    (hIn64 : inBase.toNat + inBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjInPins : MemSpan.disjoint ⟨inBase, inBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjInReg : MemSpan.disjoint ⟨inBase, inBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hInMem : ∀ i, (hi : i < inBytes.size) → initSt.mem (inBase + BitVec.ofNat 64 i) = inBytes[i].toBitVec)
    (hPinsMem : ∀ i, (hi : i < pins.size) → initSt.mem (pinsBase + BitVec.ofNat 64 i) = pins[i].toBitVec)
    (hRegZero : ∀ k, k < abiNeed checkerTabMini → initSt.mem (regionBase + BitVec.ofNat 64 k) = 0#8)
    (hStackA : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (phaseAInitMem inBytes pins) ≤ abiStack)
    (hStackB : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (phaseBInitMem inBytes pins) ≤ abiStack)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : checkerRom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run checkerRom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha0Out : finalSt.getReg AbiReg.a0 = acceptWord.toBitVec)
    (ha1Out : finalSt.getReg AbiReg.a1 = 0#64) :
    RegsRestored initSt finalSt ∧ finalSt.getReg AbiReg.ra = initSt.getReg AbiReg.ra :=
  (checkerRom_accept_runs_and_regs hPlat initSt hpc0 ha0 ha1 ha2 ha3 ha4
    hin64 hpins64 hIn64 hPins64 hRegAlign hReg64 hDisjInPins hDisjInReg hDisjPinsReg
    hInMem hPinsMem hRegZero hStackA hStackB hRetOut hrun hret ha0Out ha1Out).2.2.1

/-- End-to-end backward soundness: an accepting RV64 execution of the far-linked
    checker ROM `checkerRom` implies `ConAgua.Final.TwinAccepts [inBytes]`. -/
theorem checkerRom_accept_twinAccepts
    (hPlat : System.Platform.numBits = 64)
    (initSt : RV64.State) (hpc0 : initSt.pc = 0#64)
    {inBase pinsBase regionBase : BitVec 64}
    {inBytes pins : ByteArray}
    (ha0 : initSt.getReg AbiReg.a0 = inBase)
    (ha1 : initSt.getReg AbiReg.a1 = BitVec.ofNat 64 inBytes.size)
    (ha2 : initSt.getReg AbiReg.a2 = pinsBase)
    (ha3 : initSt.getReg AbiReg.a3 = BitVec.ofNat 64 pins.size)
    (ha4 : initSt.getReg AbiReg.a4 = regionBase)
    (hin64 : inBytes.size < 2 ^ 64) (hpins64 : pins.size < 2 ^ 64)
    (hIn64 : inBase.toNat + inBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjInPins : MemSpan.disjoint ⟨inBase, inBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjInReg : MemSpan.disjoint ⟨inBase, inBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hInMem : ∀ i, (hi : i < inBytes.size) → initSt.mem (inBase + BitVec.ofNat 64 i) = inBytes[i].toBitVec)
    (hPinsMem : ∀ i, (hi : i < pins.size) → initSt.mem (pinsBase + BitVec.ofNat 64 i) = pins[i].toBitVec)
    (hRegZero : ∀ k, k < abiNeed checkerTabMini → initSt.mem (regionBase + BitVec.ofNat 64 k) = 0#8)
    (hStackA : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (phaseAInitMem inBytes pins) ≤ abiStack)
    (hStackB : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (phaseBInitMem inBytes pins) ≤ abiStack)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : checkerRom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run checkerRom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha0Out : finalSt.getReg AbiReg.a0 = acceptWord.toBitVec)
    (ha1Out : finalSt.getReg AbiReg.a1 = 0#64) :
    ConAgua.Final.TwinAccepts [inBytes] := by
  obtain ⟨hin63, hpins63, rs₁, m₁, rs₂, m₂, h₁, hge, h₂, hacc⟩ :=
    checkerRom_accept_runs hPlat initSt hpc0 ha0 ha1 ha2 ha3 ha4 hin64 hpins64 hIn64 hPins64
      hRegAlign hReg64 hDisjInPins hDisjInReg hDisjPinsReg hInMem hPinsMem hRegZero hStackA hStackB
      hRetOut hrun hret ha0Out ha1Out
  refine checkerProgMini_drv_twinAccepts inBytes pins (fun _ => abiWords)
    ⟨hPlat, hin63, hpins63, fun _ => by simp [abiWords]⟩
    (abiFuel - 1) (by simp [abiFuel]) rs₁ m₁ h₁ hge
    (abiFuel - 1) (by simp [abiFuel]) (phaseBMem m₁ (rs₁.headD 0)) rs₂ m₂
    (fun a ha => by
      have hno : a ≠ .t0 L.Arena.OUT := by rintro rfl; simp [t_bs_out] at ha
      have hnh : a ≠ .t0 L.Arena.HDRF := by rintro rfl; simp [t_bs_hdrf] at ha
      have hnc : a ≠ .t0 L.Arena.CTLF := by rintro rfl; simp [t_bs_ctlf] at ha
      simp [phaseBMem, hno, hnh, hnc])
    (by
      have h1 : modeGVar ≠ phiGVar := by decide
      have h2 : modeGVar ≠ ploGVar := by decide
      simp [phaseBMem, h1, h2])
    (by
      have h1 : ploGVar ≠ phiGVar := by decide
      simp [phaseBMem, h1])
    (by simp [phaseBMem])
    (by
      simp [phaseBMem, ctlfArr])
    h₂ hacc

/-- End-to-end backward soundness: an accepting RV64 execution of `checkerRom` implies
    the input proof chunks parse and typecheck cleanly and admit a ZFC model (`ConLeche.Model V env`). -/
theorem checkerRom_accept_model.{w_u} (V : Type w_u) [ConLeche.SetTheory V]
    (hPlat : System.Platform.numBits = 64)
    (initSt : RV64.State) (hpc0 : initSt.pc = 0#64)
    {inBase pinsBase regionBase : BitVec 64}
    {inBytes pins : ByteArray}
    (ha0 : initSt.getReg AbiReg.a0 = inBase)
    (ha1 : initSt.getReg AbiReg.a1 = BitVec.ofNat 64 inBytes.size)
    (ha2 : initSt.getReg AbiReg.a2 = pinsBase)
    (ha3 : initSt.getReg AbiReg.a3 = BitVec.ofNat 64 pins.size)
    (ha4 : initSt.getReg AbiReg.a4 = regionBase)
    (hin64 : inBytes.size < 2 ^ 64) (hpins64 : pins.size < 2 ^ 64)
    (hIn64 : inBase.toNat + inBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjInPins : MemSpan.disjoint ⟨inBase, inBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjInReg : MemSpan.disjoint ⟨inBase, inBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hInMem : ∀ i, (hi : i < inBytes.size) → initSt.mem (inBase + BitVec.ofNat 64 i) = inBytes[i].toBitVec)
    (hPinsMem : ∀ i, (hi : i < pins.size) → initSt.mem (pinsBase + BitVec.ofNat 64 i) = pins[i].toBitVec)
    (hRegZero : ∀ k, k < abiNeed checkerTabMini → initSt.mem (regionBase + BitVec.ofNat 64 k) = 0#8)
    (hStackA : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (phaseAInitMem inBytes pins) ≤ abiStack)
    (hStackB : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (phaseBInitMem inBytes pins) ≤ abiStack)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : checkerRom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run checkerRom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha0Out : finalSt.getReg AbiReg.a0 = acceptWord.toBitVec)
    (ha1Out : finalSt.getReg AbiReg.a1 = 0#64) :
    ∃ pins' preC rc F env,
      ConLeche.Frontend.parseChunks [inBytes] = Except.ok rc ∧
        ConLeche.checkDeclsPure ConLeche.CheckMode.verified
          (ConLeche.fueledOps ConLeche.CheckMode.verified F) pins'
          (ConLeche.Frontend.preparePrelude preC rc.decls).toList = Except.ok env ∧
          Nonempty (ConLeche.Model V env) :=
  ConAgua.Final.twinAccepts_model V
    (checkerRom_accept_twinAccepts hPlat initSt hpc0 ha0 ha1 ha2 ha3 ha4 hin64 hpins64 hIn64 hPins64
      hRegAlign hReg64 hDisjInPins hDisjInReg hDisjPinsReg hInMem hPinsMem hRegZero hStackA hStackB
      hRetOut hrun hret ha0Out ha1Out)

/-- End-to-end soundness (`NoFalse`): `checkerRom` never accepts an input proof declaring
    a theorem of type `False`. -/
theorem checkerRom_accept_no_False.{w_u} (V : Type w_u) [ConLeche.SetTheory V]
    (hPlat : System.Platform.numBits = 64)
    (initSt : RV64.State) (hpc0 : initSt.pc = 0#64)
    {inBase pinsBase regionBase : BitVec 64}
    {inBytes pins : ByteArray}
    (hfalse : ConLeche.jsonWithTheoremFalse [inBytes])
    (ha0 : initSt.getReg AbiReg.a0 = inBase)
    (ha1 : initSt.getReg AbiReg.a1 = BitVec.ofNat 64 inBytes.size)
    (ha2 : initSt.getReg AbiReg.a2 = pinsBase)
    (ha3 : initSt.getReg AbiReg.a3 = BitVec.ofNat 64 pins.size)
    (ha4 : initSt.getReg AbiReg.a4 = regionBase)
    (hin64 : inBytes.size < 2 ^ 64) (hpins64 : pins.size < 2 ^ 64)
    (hIn64 : inBase.toNat + inBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjInPins : MemSpan.disjoint ⟨inBase, inBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjInReg : MemSpan.disjoint ⟨inBase, inBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hInMem : ∀ i, (hi : i < inBytes.size) → initSt.mem (inBase + BitVec.ofNat 64 i) = inBytes[i].toBitVec)
    (hPinsMem : ∀ i, (hi : i < pins.size) → initSt.mem (pinsBase + BitVec.ofNat 64 i) = pins[i].toBitVec)
    (hRegZero : ∀ k, k < abiNeed checkerTabMini → initSt.mem (regionBase + BitVec.ofNat 64 k) = 0#8)
    (hStackA : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (phaseAInitMem inBytes pins) ≤ abiStack)
    (hStackB : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (phaseBInitMem inBytes pins) ≤ abiStack)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : checkerRom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run checkerRom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha0Out : finalSt.getReg AbiReg.a0 = acceptWord.toBitVec)
    (ha1Out : finalSt.getReg AbiReg.a1 = 0#64) :
    False :=
  ConAgua.Final.twinAccepts_no_False V hfalse
    (checkerRom_accept_twinAccepts hPlat initSt hpc0 ha0 ha1 ha2 ha3 ha4 hin64 hpins64 hIn64 hPins64
      hRegAlign hReg64 hDisjInPins hDisjInReg hDisjPinsReg hInMem hPinsMem hRegZero hStackA hStackB
      hRetOut hrun hret ha0Out ha1Out)

/-- info: 'ConAgua.RISCV.Bridge.checkerRom_accept_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerRom_accept_runs

/-- info: 'ConAgua.RISCV.Bridge.checkerRom_accept_twinAccepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerRom_accept_twinAccepts

/-- info: 'ConAgua.RISCV.Bridge.checkerRom_accept_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerRom_accept_model

/-- info: 'ConAgua.RISCV.Bridge.checkerRom_accept_no_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerRom_accept_no_False

/-- info: 'ConAgua.RISCV.Bridge.checkerRom_accept_regsRestored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerRom_accept_regsRestored


end ConAgua.RISCV.Bridge
