import ConAgua.RISCV.Bridge.CheckerDriverCmpMode56
import ConAgua.RISCV.Bridge.CheckerDriverCmpMode8
import ConAgua.RISCV.Bridge.CheckerDriverCmpMode9

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# End-to-End Backward Soundness of Linked Comparator ROM (`ConAgua.RISCV.Bridge.CheckerDriverCmp`)

Connects LP64 accepting executions of `checkerRom` through modes 4/5/6/8/9 to
`ConAgua.Final.{TwinComparesAccepts, Models, NoFalse}` and `RegsRestored`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard Lean axioms only.
-/

namespace ConAgua.RISCV.Bridge

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Compiler
open ConAgua.RISCV.Linker

private theorem cmp_linkFull (img : LinkedCmpImage) :
    img.lkm.linkSpec (cmpPreCall4 ++ [Asm.call (fnLabel "check")] ++ cmpTail4 img) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
  have h := img.hlink
  rw [linkedCmpChipAsm_eq img, checkerCmpDriverAsm_decomp] at h
  dsimp only [cmpDrvPreDone] at h
  change img.lkm.linkSpec _ = .ok (img.code, img.labels)
  simpa only [cmpPreCall4, cmpTail4, cmpTail5, cmpTail6, cmpTail8, cmpTail9,
    List.append_assoc] using h

private theorem linkedCmp_call_check_step (img : LinkedCmpImage)
    (initSt : RV64.State) {regionBase : BitVec 64}
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : img.rom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run img.rom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha1Out : finalSt.getReg AbiReg.a1 = 0#64)
    (L : ProgLayout checkerTabMini)
    (hLT : L.T = regionBase)
    (hLTop : L.stackTop = regionBase + BitVec.ofNat 64 (abiSlot + abiStack))
    (hLLim : L.stackLimit = regionBase + BitVec.ofNat 64 abiSlot)
    (hTopAlign : isAligned L.stackTop 8 = true)
    (hTabSave : checkerTabMini.saveBase 0 + 128 ≤ (L.tabBytes : Int))
    (pre post : List AsmItem)
    (hlink : img.lkm.linkSpec (pre ++ [Asm.call (fnLabel "check")] ++ post) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels))
    (mIn : _root_.L.Mem)
    (hStack : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] mIn ≤ abiStack)
    {k0 : Nat} {st0 : RV64.State}
    (hrun0 : RV64.run (linkedCmpEnv img).rom k0 initSt = .cont st0)
    (hpc0 : st0.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize pre))
    (hgp0 : st0.getReg AbiReg.gp = regionBase)
    (hsp0 : st0.getReg AbiReg.sp = L.stackTop)
    (hs0_0 : st0.getReg AbiReg.s0 = BitVec.ofNat 64 (abiFuel - 2))
    (ht0_0 : st0.getReg AbiReg.t0 = regionBase + BitVec.ofInt 64 checkerTabMini.args)
    (hsaved0 : DrvRegsSaved regionBase initSt st0.mem)
    (hMemRel0 : ProgMemRel checkerTabMini L st0.mem mIn)
    (hHdr0 : TabHeaderOk L st0.mem) :
    ∃ (sig : _root_.L.Sig) (m' : _root_.L.Mem) (b' : Nat) (kPost : Nat) (r : RV64.State),
      runB checkerProgMini (abiFuel - 1) "check" [] mIn = .ok (sig.retVal, m', b') ∧
      cmpRunMini (abiFuel - 1) checkerProgMini mIn = .ok (sig.retVal, m') ∧
      RV64.run (linkedCmpEnv img).rom (k0 + kPost) initSt = .cont r ∧
      r.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize (pre ++ [Asm.call (fnLabel "check")])) ∧
      r.getReg AbiReg.gp = regionBase ∧
      r.getReg AbiReg.a0 = (sig.retVal.headD 0).toBitVec ∧
      (∀ q, q ∈ calleeSavedBank → r.getReg q = st0.getReg q) ∧
      DrvRegsSaved regionBase initSt r.mem ∧
      ProgMemRel checkerTabMini L r.mem m' ∧
      ProgMemOutside (CallWriteMask L L.stackTop) st0.mem r.mem := by
  have halignSave : isAligned (regionBase + BitVec.ofInt 64 (checkerTabMini.saveBase 0)) 8 = true :=
    checkerTabMini_saveBase_align regionBase hRegAlign
  obtain ⟨checkFd, hCheck, hNparams⟩ := checkerProgMini_lookup_check
  have hargsAl : isAligned (regionBase + BitVec.ofInt 64 checkerTabMini.args) 8 = true := by
    rw [checkerTabMini_args_eq, BitVec.ofInt_natCast]
    exact isAligned8_add_nat_mul8 regionBase hRegAlign _ (by
      have harg := checkerTabMini_args_lt
      rw [checkerTabMini_args_eq, Int.toNat_natCast] at harg; omega)
  have hpcCall_64 := linkResolved_sub_pc64 (linkedCmpEnv img) pre [Asm.call (fnLabel "check")] post hlink
  have hltCall_64 : 4 * (img.lkm.totalSize pre + img.lkm.itemSize (.call (fnLabel "check"))) < 2 ^ 64 := by
    simpa only [Asm.call, img.lkm.totalSize_singleton] using hpcCall_64
  obtain ⟨tgt, kCall, st1, _, hlkp, hrunCall, hpcCall, hregsCall, hmCall⟩ :=
    step_item_call_lm img.lkm (linkedCmpEnv img).hrom pre post (fnLabel "check") hlink hltCall_64 st0 hpc0
  have hNeed : L.stackLimit.toNat + fnFrameBytes checkFd +
      stackNeedB checkerProgMini (abiFuel - 2) checkFd.body { mem := mIn, loc := Locals.init [] } ≤
      L.stackTop.toNat := by
    unfold runStackNeedB at hStack
    rw [show abiFuel - 1 = (abiFuel - 2) + 1 from by simp [abiFuel], hCheck] at hStack
    dsimp only at hStack
    have hdiff : L.stackTop.toNat - L.stackLimit.toNat = abiStack := by
      rw [hLTop, hLLim]; exact checkerLayout_stack_diff regionBase hReg64
    have hle : L.stackLimit.toNat ≤ L.stackTop.toNat := L.hStackLe
    omega
  have hcall := compileFns_call_sim_callee_with (linkedCmpEnv img) L checkerProgMini img.allocOf
    checkerProgMini_progOkB checkerProgMini_progArgsOkB (linkedCmpFnsLinked img) (abiFuel - 2)
    "check" checkFd [] mIn
    L.stackTop (st1.getReg AbiReg.ra) (regionBase + BitVec.ofInt 64 checkerTabMini.args)
    (img.lkm.totalSize pre + img.lkm.itemSize (.call (fnLabel "check")))
    hCheck (by rw [hNparams]; decide) (by simp [abiFuel]) hNeed (Nat.le_refl _) hTopAlign hargsAl
    (by
      have hra : st1.getReg AbiReg.ra =
          BitVec.ofNat 64 (4 * (img.lkm.totalSize pre + img.lkm.itemSize (.call (fnLabel "check")))) :=
        (hregsCall.getReg_eq (by decide)).symm.trans (getReg_setReg_eq st0 AbiReg.ra _ (by decide))
      rw [hra]; exact mul4_and_not1_cd _ hltCall_64)
    (fun _ hj => absurd hj (Nat.not_lt_zero _))
    tgt st1 hlkp hpcCall
    (((hregsCall.getReg_eq (by decide)).symm.trans ((getReg_setReg_ne st0 AbiReg.ra _ _ (by decide)).trans hgp0)).trans hLT.symm)
    ((hregsCall.getReg_eq (by decide)).symm.trans ((getReg_setReg_ne st0 AbiReg.ra _ _ (by decide)).trans hsp0))
    rfl
    ((hregsCall.getReg_eq (by decide)).symm.trans ((getReg_setReg_ne st0 AbiReg.ra _ _ (by decide)).trans hs0_0))
    (fun _ => (hregsCall.getReg_eq (by decide)).symm.trans ((getReg_setReg_ne st0 AbiReg.ra _ _ (by decide)).trans ht0_0))
    (by rw [hmCall]; exact hMemRel0) (by rw [hmCall]; exact hHdr0)
    (fun _ hj => absurd hj (Nat.not_lt_zero _))
  have hgp1 : st1.getReg AbiReg.gp = regionBase :=
    (hregsCall.getReg_eq (by decide)).symm.trans ((getReg_setReg_ne st0 AbiReg.ra _ _ (by decide)).trans hgp0)
  have hsaved1 : DrvRegsSaved L.T initSt st1.mem := by
    rw [hLT, hmCall]; exact hsaved0
  have hrunTo1 : RV64.run (linkedCmpEnv img).rom (k0 + kCall) initSt = .cont st1 := by
    rw [run_add, hrun0]; exact hrunCall
  cases hex : execB checkerProgMini (abiFuel - 2) checkFd.body { mem := mIn, loc := Locals.init [] } with
  | error err =>
    rw [hex] at hcall
    cases err with
    | outOfFuel =>
      obtain ⟨kF, rF, hrunF, hpcF, htrF, houtF⟩ := hcall
      have hsavedF : DrvRegsSaved regionBase initSt rF.mem := by
        have h := drvRegsSaved_of_callWriteMask_eq L L.stackTop hTabSave houtF hsaved1 rfl
        rwa [hLT] at h
      have hgpF : rF.getReg AbiReg.gp = regionBase := htrF.gp.trans hgp1
      obtain ⟨mEx, rEx, hrunEx, hpcEx, _, _, _, ha1Ex, _⟩ :=
        linkedCmp_exhausted_returns img initSt regionBase halignSave rF hpcF hgpF hsavedF
      have htot : RV64.run (linkedCmpEnv img).rom (k0 + kCall + kF + mEx) initSt = .cont rEx := by
        rw [run_add, run_add, hrunTo1]; dsimp only; rw [hrunF]; exact hrunEx
      have heqFin := run_ret_deterministic (linkedCmpEnv img).rom _ _ initSt hrun htot hret hpcEx hRetOut
      exact absurd (ha1Out.symm.trans (heqFin ▸ ha1Ex)) (by decide)
    | abort code =>
      obtain ⟨kF, rF, hrunF, hpcF, _, htrF, houtF⟩ := hcall
      have hsavedF : DrvRegsSaved regionBase initSt rF.mem := by
        have h := drvRegsSaved_of_callWriteMask_eq L L.stackTop hTabSave houtF hsaved1 rfl
        rwa [hLT] at h
      have hgpF : rF.getReg AbiReg.gp = regionBase := htrF.gp.trans hgp1
      obtain ⟨mAb, rAb, hrunAb, hpcAb, _, _, _, ha1Ab, _⟩ :=
        linkedCmp_abort_returns img initSt regionBase halignSave rF hpcF hgpF hsavedF
      have htot : RV64.run (linkedCmpEnv img).rom (k0 + kCall + kF + mAb) initSt = .cont rAb := by
        rw [run_add, run_add, hrunTo1]; dsimp only; rw [hrunF]; exact hrunAb
      have heqFin := run_ret_deterministic (linkedCmpEnv img).rom _ _ initSt hrun htot hret hpcAb hRetOut
      exact absurd (ha1Out.symm.trans (heqFin ▸ ha1Ab)) (by decide)
    | oob | noFun _ =>
      obtain ⟨kF, rF, hrunF, hpcF, htrF, houtF⟩ := hcall
      have hsavedF : DrvRegsSaved regionBase initSt rF.mem := by
        have h := drvRegsSaved_of_callWriteMask_eq L L.stackTop hTabSave houtF hsaved1 rfl
        rwa [hLT] at h
      have hgpF : rF.getReg AbiReg.gp = regionBase := htrF.gp.trans hgp1
      obtain ⟨mEr, rEr, hrunEr, hpcEr, _, _, _, ha1Er, _⟩ :=
        linkedCmp_err_returns img initSt regionBase halignSave rF hpcF hgpF hsavedF
      have htot : RV64.run (linkedCmpEnv img).rom (k0 + kCall + kF + mEr) initSt = .cont rEr := by
        rw [run_add, run_add, hrunTo1]; dsimp only; rw [hrunF]; exact hrunEr
      have heqFin := run_ret_deterministic (linkedCmpEnv img).rom _ _ initSt hrun htot hret hpcEr hRetOut
      exact absurd (ha1Out.symm.trans (heqFin ▸ ha1Er)) (by decide)
  | ok res =>
    rcases res with ⟨sig, st', b'⟩
    rw [hex] at hcall; dsimp only at hcall
    obtain ⟨kF, r, hrunF, hpcR, hgpR, _, _, hcalR, _, _, _, _, hmR, _, hresR, houtR⟩ := hcall
    have hsavedR : DrvRegsSaved regionBase initSt r.mem := by
      have h := drvRegsSaved_of_callWriteMask_eq L L.stackTop hTabSave houtR hsaved1 rfl
      rwa [hLT] at h
    have hrunB : runB checkerProgMini (abiFuel - 1) "check" [] mIn = .ok (sig.retVal, st'.mem, b') := by
      unfold runB
      rw [show abiFuel - 1 = (abiFuel - 2) + 1 from by simp [abiFuel], hCheck]
      dsimp only; rw [hex]
    have hMini : cmpRunMini (abiFuel - 1) checkerProgMini mIn = .ok (sig.retVal, st'.mem) := by
      have h := execB_sound_run checkerProgMini (abiFuel - 1) "check" [] mIn
      rw [hrunB] at h; exact h
    have hcalR' : ∀ q, q ∈ calleeSavedBank → r.getReg q = st0.getReg q := by
      intro q hq
      have hqt6 : q ≠ AbiReg.t6 := by
        rcases (by simpa [calleeSavedBank] using hq :
          q = AbiReg.s3 ∨ q = AbiReg.s4 ∨ q = AbiReg.s5 ∨ q = AbiReg.s6 ∨ q = AbiReg.s7 ∨
          q = AbiReg.s8 ∨ q = AbiReg.s9 ∨ q = AbiReg.s10 ∨ q = AbiReg.s11 ∨ q = AbiReg.tp)
          with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hqs1 : q ≠ AbiReg.s1 := by
        rcases (by simpa [calleeSavedBank] using hq :
          q = AbiReg.s3 ∨ q = AbiReg.s4 ∨ q = AbiReg.s5 ∨ q = AbiReg.s6 ∨ q = AbiReg.s7 ∨
          q = AbiReg.s8 ∨ q = AbiReg.s9 ∨ q = AbiReg.s10 ∨ q = AbiReg.s11 ∨ q = AbiReg.tp)
          with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hqra : q ≠ AbiReg.ra := by
        rcases (by simpa [calleeSavedBank] using hq :
          q = AbiReg.s3 ∨ q = AbiReg.s4 ∨ q = AbiReg.s5 ∨ q = AbiReg.s6 ∨ q = AbiReg.s7 ∨
          q = AbiReg.s8 ∨ q = AbiReg.s9 ∨ q = AbiReg.s10 ∨ q = AbiReg.s11 ∨ q = AbiReg.tp)
          with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (hcalR q hq).trans ((hregsCall.getReg_eq ⟨hqt6, hqs1⟩).symm.trans (getReg_setReg_ne st0 AbiReg.ra q _ hqra))
    refine ⟨sig, st'.mem, b', kCall + kF, r, hrunB, hMini, ?_, ?_, hgpR.trans hLT, resultsInState_a0 hresR,
      hcalR', hsavedR, hmR, ?_⟩
    · rw [← Nat.add_assoc, run_add, hrunTo1]; exact hrunF
    · rw [hpcR, img.lkm.totalSize_append, Asm.call, img.lkm.totalSize_singleton]
    · rw [← hmCall]; exact houtR

private theorem cmp_mode4_step (img : LinkedCmpImage)
    (initSt : RV64.State) (hpc0 : initSt.pc = img.cmpEntryPc)
    {chalBase solBase pinsBase regionBase : BitVec 64}
    {chalBytes solBytes pins : ByteArray}
    (ha0 : initSt.getReg AbiReg.a0 = chalBase)
    (ha1 : initSt.getReg AbiReg.a1 = BitVec.ofNat 64 chalBytes.size)
    (ha2 : initSt.getReg AbiReg.a2 = pinsBase)
    (ha3 : initSt.getReg AbiReg.a3 = BitVec.ofNat 64 pins.size)
    (ha4 : initSt.getReg AbiReg.a4 = regionBase)
    (ha6 : initSt.getReg AbiReg.a6 = solBase)
    (ha7 : initSt.getReg AbiReg.a7 = BitVec.ofNat 64 solBytes.size)
    (hchal64 : chalBytes.size < 2 ^ 64) (hsol64 : solBytes.size < 2 ^ 64)
    (hpins64 : pins.size < 2 ^ 64)
    (hChal64 : chalBase.toNat + chalBytes.size ≤ 2 ^ 64)
    (hSol64 : solBase.toNat + solBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjChalPins : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjChalSol : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨solBase, solBytes.size⟩)
    (hDisjChalReg : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjSolPins : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjSolReg : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hChalMem : ∀ i, (hi : i < chalBytes.size) → initSt.mem (chalBase + BitVec.ofNat 64 i) = chalBytes[i].toBitVec)
    (hSolMem : ∀ i, (hi : i < solBytes.size) → initSt.mem (solBase + BitVec.ofNat 64 i) = solBytes[i].toBitVec)
    (hPinsMem : ∀ i, (hi : i < pins.size) → initSt.mem (pinsBase + BitVec.ofNat 64 i) = pins[i].toBitVec)
    (hRegZero : ∀ k, k < abiNeed checkerTabMini → initSt.mem (regionBase + BitVec.ofNat 64 k) = 0#8)
    (hStack4 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase4Mem chalBytes pins) ≤ abiStack)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : img.rom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run img.rom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha0Out : finalSt.getReg AbiReg.a0 = acceptWord.toBitVec)
    (ha1Out : finalSt.getReg AbiReg.a1 = 0#64) :
    chalBytes.size < 2 ^ 63 ∧ pins.size < 2 ^ 63 ∧ solBytes.size < 2 ^ 63 ∧
    ∃ (sig4 : _root_.L.Sig) (m4' : _root_.L.Mem) (b4' : Nat),
      runB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase4Mem chalBytes pins) = .ok (sig4.retVal, m4', b4') ∧
      cmpRunMini (abiFuel - 1) checkerProgMini (cmpPhase4Mem chalBytes pins) = .ok (sig4.retVal, m4') ∧
      (m4'.words (.t0 L.Arena.OUT)).size = abiWords ∧
      ((sig4.retVal.headD 0 = acceptWord ∧
        RegsRestored initSt finalSt ∧ finalSt.getReg AbiReg.ra = initSt.getReg AbiReg.ra) ∨
        (2 ^ 63 ≤ (sig4.retVal.headD 0).toNat ∧
         ∃ (k50 : Nat) (st50 : RV64.State),
           RV64.run (linkedCmpEnv img).rom k50 initSt = .cont st50 ∧
           st50.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize (cmpPreCall4 ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode4Post)) ∧
           st50.getReg AbiReg.gp = regionBase ∧
           st50.getReg AbiReg.s3 = solBase ∧
           st50.getReg AbiReg.s4 = BitVec.ofNat 64 solBytes.size ∧
           DrvRegsSaved regionBase initSt st50.mem ∧
           ProgMemRel checkerTabMini (checkerLayoutA chalBase pinsBase regionBase chalBytes.size pins.size
             hChal64 hPins64 hRegAlign hReg64 hDisjChalPins hDisjChalReg hDisjPinsReg) st50.mem m4' ∧
           (∀ i, (hi : i < solBytes.size) → st50.mem (solBase + BitVec.ofNat 64 i) = solBytes[i].toBitVec))) := by
  let LA4 := checkerLayoutA chalBase pinsBase regionBase chalBytes.size pins.size
    hChal64 hPins64 hRegAlign hReg64 hDisjChalPins hDisjChalReg hDisjPinsReg
  have ha1Ne1 : finalSt.getReg AbiReg.a1 ≠ 1#64 := by rw [ha1Out]; decide
  have halignSave : isAligned (regionBase + BitVec.ofInt 64 (checkerTabMini.saveBase 0)) 8 = true :=
    checkerTabMini_saveBase_align regionBase hRegAlign
  have hTabSave4 : checkerTabMini.saveBase 0 + 128 ≤ (LA4.tabBytes : Int) := by
    simp only [LA4, checkerLayoutA]; exact checkerTabMini_saveBase_le_abiSlot
  obtain ⟨hchal63, hpins63, hsol63, k40, st40, hrun40, hpc40, hgp40, hsp40, hs0_40,
      hs3_40, hs4_40, ht0_40, ht1_40, hsaved40, hout40, hMemRel40, hHdr40⟩ :=
    cmp_prefix_sim img initSt hpc0 ha0 ha1 ha2 ha3 ha4 ha6 ha7 hchal64 hsol64 hpins64
      hChal64 hPins64 hRegAlign hReg64 hDisjChalPins hDisjChalReg hDisjPinsReg
      hChalMem hPinsMem hRegZero hRetOut hrun hret ha1Ne1
  refine ⟨hchal63, hpins63, hsol63, ?_⟩
  have hNeedEq := checkerTabMini_abiNeed_eq
  have hlinkFull := cmp_linkFull img
  have hpc40' : st40.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize cmpPreCall4) := by
    dsimp only [cmpPreCall4]; exact hpc40
  obtain ⟨sig4, m4', b4', kPost4, r4, hrunB4, hMini4, hrunToR4, hpcR4, hgpR4, hra0_4, hcalR4, hsavedR4, hmR4, houtR4⟩ :=
    linkedCmp_call_check_step img initSt hRegAlign hReg64 hRetOut hrun hret ha1Out
      LA4 rfl rfl rfl LA4.hTopAlign hTabSave4 cmpPreCall4 (cmpTail4 img) hlinkFull
      (cmpPhase4Mem chalBytes pins) hStack4 hrun40 hpc40' hgp40 hsp40 hs0_40 ht0_40 hsaved40 hMemRel40 hHdr40
  have hm4OutSz : (m4'.words (.t0 L.Arena.OUT)).size = abiWords := by
    rw [minil_run_words_size hMini4]
    simp [cmpPhase4Mem, cmpM4SzMini, loadMemMini]
  refine ⟨sig4, m4', b4', hrunB4, hMini4, hm4OutSz, ?_⟩
  let pBr4 := cmpPreCall4 ++ [Asm.call (fnLabel "check")]
  have hlBr4 : img.lkm.linkSpec (pBr4 ++ [Asm.bge AbiReg.a0 AbiReg.zero drvDoneLabel] ++
      (cmpDrvMode5Setup checkerTabMini ++ [Asm.call (fnLabel "check")] ++ cmpTail5 img)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [pBr4, cmpTail4, cmpDrvMode4Post, List.append_assoc] using hlinkFull
  have hbr4 := run_br_step (linkedCmpEnv img) pBr4 _ .bge AbiReg.a0 AbiReg.zero drvDoneLabel _
    (checkerCmp_drvDone_lbl img) (by decide) hlBr4 r4 hpcR4
  by_cases hge4 : 2 ^ 63 ≤ (sig4.retVal.headD 0).toNat
  · right
    have hev4False : evalBranch .bge (r4.getReg AbiReg.a0) (r4.getReg AbiReg.zero) = false := by
      have hz : r4.getReg AbiReg.zero = 0#64 := rfl
      have hlt2 : 2 ^ 63 ≤ (r4.getReg AbiReg.a0).toNat := by rw [hra0_4]; exact hge4
      have hbvEq : BitVec.ofNat 64 (r4.getReg AbiReg.a0).toNat = r4.getReg AbiReg.a0 :=
        BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (r4.getReg AbiReg.a0).isLt])
      rw [hz]; dsimp only [evalBranch]; rw [← hbvEq, bitvec_slt_zero_iff _ (r4.getReg AbiReg.a0).isLt]
      simp [hlt2]
    rw [hev4False] at hbr4
    obtain ⟨kBr4, st50, _, hrunBr4, hpc50, hothBr4, _, hmBr4⟩ := hbr4
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc50
    have hpc50' : st50.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize (cmpPreCall4 ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode4Post)) := by
      rw [hpc50, ← img.lkm.totalSize_append]
      exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (by
        simp only [pBr4, cmpDrvMode4Post, Asm.bge, List.append_assoc]; rfl)
    have hs3_r4 : r4.getReg AbiReg.s3 = solBase := (hcalR4 _ (by decide)).trans hs3_40
    have hs4_r4 : r4.getReg AbiReg.s4 = BitVec.ofNat 64 solBytes.size := (hcalR4 _ (by decide)).trans hs4_40
    have hSolMem_50 : ∀ i, (hi : i < solBytes.size) → st50.mem (solBase + BitVec.ofNat 64 i) = solBytes[i].toBitVec := by
      intro i hi
      have hnotCWM := cmp_callWriteMask_not_sol hChal64 hSol64 hPins64 hRegAlign hReg64
        hDisjChalPins hDisjChalReg hDisjPinsReg hDisjChalSol hDisjSolPins hDisjSolReg i hi
      have hnotSlot0 : ¬(⟨regionBase, abiSlot⟩ : MemSpan).contains (solBase + BitVec.ofNat 64 i) := by
        have hdisjSub : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨regionBase, abiSlot⟩ := by
          dsimp only [MemSpan.disjoint] at hDisjSolReg ⊢; rw [hNeedEq] at hDisjSolReg
          rcases hDisjSolReg with h | h
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)
        exact @MemSpan.disjoint_to_memDisjoint ⟨solBase, solBytes.size⟩ ⟨regionBase, abiSlot⟩
          hSol64 (by dsimp only [MemSpan.valid]; omega) hdisjSub _ ⟨i, hi, rfl⟩
      rw [hmBr4, houtR4 _ hnotCWM, hout40 _ hnotSlot0, hSolMem i hi]
    exact ⟨hge4, k40 + kPost4 + kBr4, st50, by rw [run_add, hrunToR4]; exact hrunBr4,
      hpc50', (hothBr4 _ (by decide)).trans hgpR4, (hothBr4 _ (by decide)).trans hs3_r4,
      (hothBr4 _ (by decide)).trans hs4_r4, by rw [hmBr4]; exact hsavedR4,
      by rw [hmBr4]; exact hmR4, hSolMem_50⟩
  · left
    have hlt2 : (r4.getReg AbiReg.a0).toNat < 2 ^ 63 := by rw [hra0_4]; exact Nat.lt_of_not_le hge4
    have hev4True : evalBranch .bge (r4.getReg AbiReg.a0) (r4.getReg AbiReg.zero) = true := by
      have hz : r4.getReg AbiReg.zero = 0#64 := rfl
      have hbvEq : BitVec.ofNat 64 (r4.getReg AbiReg.a0).toNat = r4.getReg AbiReg.a0 :=
        BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (r4.getReg AbiReg.a0).isLt])
      rw [hz]; dsimp only [evalBranch]; rw [← hbvEq, bitvec_slt_zero_iff _ (r4.getReg AbiReg.a0).isLt]
      simp [hlt2]
    rw [hev4True] at hbr4
    obtain ⟨kBr4, stDone4, _, hrunBr4, hpcDone4, hothBr4, _, hmDone4⟩ := hbr4
    simp only [↓reduceIte] at hpcDone4
    have hgpDone4 : stDone4.getReg AbiReg.gp = regionBase := (hothBr4 _ (by decide)).trans hgpR4
    have hsavedDone4 : DrvRegsSaved regionBase initSt stDone4.mem := by rw [hmDone4]; exact hsavedR4
    obtain ⟨mD4, rD4, hrunD4, hpcD4, hregsD4, hraD4, ha0D4, _, _⟩ :=
      linkedCmpDrvDone_returns img initSt regionBase halignSave stDone4 hpcDone4 hgpDone4 hsavedDone4
    have htot : RV64.run (linkedCmpEnv img).rom (k40 + kPost4 + kBr4 + mD4) initSt = .cont rD4 := by
      rw [run_add, run_add, hrunToR4]; dsimp only; rw [hrunBr4]; exact hrunD4
    have heqFin := run_ret_deterministic (linkedCmpEnv img).rom _ _ initSt hrun htot hret hpcD4 hRetOut
    refine ⟨UInt64.toBitVec_inj.mp (by rw [← hra0_4, ← hothBr4 _ (by decide), ← ha0D4, ← heqFin, ha0Out]), ?_⟩
    rw [heqFin]; exact ⟨hregsD4, hraD4⟩

private theorem cmp_mode5_step (img : LinkedCmpImage)
    (initSt : RV64.State)
    {chalBase solBase pinsBase regionBase : BitVec 64}
    {chalBytes solBytes pins : ByteArray}
    (hsol64 : solBytes.size < 2 ^ 64)
    (hChal64 : chalBase.toNat + chalBytes.size ≤ 2 ^ 64)
    (hSol64 : solBase.toNat + solBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjChalPins : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjChalReg : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjSolPins : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjSolReg : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hStack5 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase5InitMem chalBytes solBytes pins) ≤ abiStack)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : img.rom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run img.rom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha0Out : finalSt.getReg AbiReg.a0 = acceptWord.toBitVec)
    (ha1Out : finalSt.getReg AbiReg.a1 = 0#64)
    {m4' : _root_.L.Mem}
    (hm4OutSz : (m4'.words (.t0 L.Arena.OUT)).size = abiWords)
    (hm5Init : cmpPhase5InitMem chalBytes solBytes pins = cmpPhase5Mem m4' solBytes)
    {k50 : Nat} {st50 : RV64.State}
    (hrun50 : RV64.run (linkedCmpEnv img).rom k50 initSt = .cont st50)
    (hpc50 : st50.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize (cmpPreCall4 ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode4Post)))
    (hgp50 : st50.getReg AbiReg.gp = regionBase)
    (hs3_50 : st50.getReg AbiReg.s3 = solBase)
    (hs4_50 : st50.getReg AbiReg.s4 = BitVec.ofNat 64 solBytes.size)
    (hsaved50 : DrvRegsSaved regionBase initSt st50.mem)
    (hMemRel_50 : ProgMemRel checkerTabMini (checkerLayoutA chalBase pinsBase regionBase chalBytes.size pins.size
      hChal64 hPins64 hRegAlign hReg64 hDisjChalPins hDisjChalReg hDisjPinsReg) st50.mem m4')
    (hSolMem_50 : ∀ i, (hi : i < solBytes.size) → st50.mem (solBase + BitVec.ofNat 64 i) = solBytes[i].toBitVec) :
    ∃ (sig5 : _root_.L.Sig) (m5' : _root_.L.Mem) (b5' : Nat),
      runB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase5Mem m4' solBytes) = .ok (sig5.retVal, m5', b5') ∧
      cmpRunMini (abiFuel - 1) checkerProgMini (cmpPhase5Mem m4' solBytes) = .ok (sig5.retVal, m5') ∧
      (m5'.words (.t0 L.Arena.OUT)).size = abiWords ∧
      ((sig5.retVal.headD 0 = acceptWord ∧
        RegsRestored initSt finalSt ∧ finalSt.getReg AbiReg.ra = initSt.getReg AbiReg.ra) ∨
        (2 ^ 63 ≤ (sig5.retVal.headD 0).toNat ∧
         ∃ (k60 : Nat) (st60 : RV64.State),
           RV64.run (linkedCmpEnv img).rom k60 initSt = .cont st60 ∧
           st60.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize (cmpPreCall5 ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode5Post)) ∧
           st60.getReg AbiReg.gp = regionBase ∧
           st60.getReg AbiReg.s5 = (sig5.retVal.headD 0 - 9223372036854775808).toBitVec ∧
           DrvRegsSaved regionBase initSt st60.mem ∧
           ProgMemRel checkerTabMini (checkerLayoutA solBase pinsBase regionBase solBytes.size pins.size
             hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg) st60.mem m5')) := by
  let LA5 := checkerLayoutA solBase pinsBase regionBase solBytes.size pins.size
    hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg
  have halignSave : isAligned (regionBase + BitVec.ofInt 64 (checkerTabMini.saveBase 0)) 8 = true :=
    checkerTabMini_saveBase_align regionBase hRegAlign
  have hTabSave5 : checkerTabMini.saveBase 0 + 128 ≤ (LA5.tabBytes : Int) := by
    simp only [LA5, checkerLayoutA]; exact checkerTabMini_saveBase_le_abiSlot
  let p50 := cmpPreCall4 ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode4Post
  have hl5Setup : img.lkm.linkSpec (p50 ++ cmpDrvMode5Setup checkerTabMini ++
      ([Asm.call (fnLabel "check")] ++ cmpTail5 img)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p50, cmpTail4, cmpDrvMode4Post, List.append_assoc] using cmp_linkFull img
  obtain ⟨k51, st51, hrun51, hpc51, hgp51, hsp51, hs0_51, _, ht0_51, ht1_51,
      hout51, h0B, h0L, hMode5, hTop5, hLim5⟩ :=
    cmpMode5Setup_sim img regionBase hRegAlign hReg64 solBase (BitVec.ofNat 64 solBytes.size) p50 _
      hl5Setup st50 hpc50 hgp50 hs3_50 hs4_50
  have hsaved51 : DrvRegsSaved regionBase initSt st51.mem :=
    drvRegsSaved_of_progMemOutside hout51 (cmp5WriteSpan_disj_callerSave regionBase hReg64) hsaved50
  have hMemRel5 : ProgMemRel checkerTabMini LA5 st51.mem (cmpPhase5Mem m4' solBytes) :=
    cmpMode5_progMemRel hChal64 hSol64 hPins64 hRegAlign hReg64
      hDisjChalPins hDisjChalReg hDisjPinsReg hDisjSolPins hDisjSolReg
      rfl hsol64 hMemRel_50 (fun i hi => hSolMem_50 i hi) hout51 h0B h0L hMode5
  have hHdr5 : TabHeaderOk LA5 st51.mem := ⟨hTop5, hLim5⟩
  have hpc51' : st51.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize cmpPreCall5) := by
    simpa only [cmpPreCall5, p50, img.lkm.totalSize_append] using hpc51
  have hlCall5 : img.lkm.linkSpec (cmpPreCall5 ++ [Asm.call (fnLabel "check")] ++ cmpTail5 img) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [cmpPreCall5, p50, List.append_assoc] using hl5Setup
  have hrunTo51 : RV64.run (linkedCmpEnv img).rom (k50 + k51) initSt = .cont st51 := by
    rw [run_add, hrun50]; exact hrun51
  have hStack5' : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase5Mem m4' solBytes) ≤ abiStack := by
    rw [← hm5Init]; exact hStack5
  obtain ⟨sig5, m5', b5', kPost5, r5, hrunB5, hMini5, hrunToR5, hpcR5, hgpR5, hra0_5, _, hsavedR5, hmR5, _⟩ :=
    linkedCmp_call_check_step img initSt hRegAlign hReg64 hRetOut hrun hret ha1Out
      LA5 rfl rfl rfl LA5.hTopAlign hTabSave5 cmpPreCall5 (cmpTail5 img) hlCall5
      (cmpPhase5Mem m4' solBytes) hStack5' hrunTo51 hpc51' hgp51 hsp51 hs0_51 ht0_51 hsaved51 hMemRel5 hHdr5
  have hm5OutSz : (m5'.words (.t0 L.Arena.OUT)).size = abiWords := by
    rw [minil_run_words_size hMini5]; simp [cmpPhase5Mem]; exact hm4OutSz
  refine ⟨sig5, m5', b5', hrunB5, hMini5, hm5OutSz, ?_⟩
  let pBr5 := cmpPreCall5 ++ [Asm.call (fnLabel "check")]
  have hlBr5 : img.lkm.linkSpec (pBr5 ++ [Asm.bge AbiReg.a0 AbiReg.zero drvDoneLabel] ++
      ([Asm.slli AbiReg.s5 AbiReg.a0 1#6, Asm.srli AbiReg.s5 AbiReg.s5 1#6] ++
       cmpDrvMode6Setup checkerTabMini ++ [Asm.call (fnLabel "check")] ++ cmpTail6 img)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [pBr5, cmpTail5, cmpDrvMode5Post, List.cons_append, List.nil_append, List.append_assoc] using hlCall5
  have hbr5 := run_br_step (linkedCmpEnv img) pBr5 _ .bge AbiReg.a0 AbiReg.zero drvDoneLabel _
    (checkerCmp_drvDone_lbl img) (by decide) hlBr5 r5 hpcR5
  by_cases hge5 : 2 ^ 63 ≤ (sig5.retVal.headD 0).toNat
  · right
    have hev5False : evalBranch .bge (r5.getReg AbiReg.a0) (r5.getReg AbiReg.zero) = false := by
      have hz : r5.getReg AbiReg.zero = 0#64 := rfl
      have hlt2 : 2 ^ 63 ≤ (r5.getReg AbiReg.a0).toNat := by rw [hra0_5]; exact hge5
      have hbvEq : BitVec.ofNat 64 (r5.getReg AbiReg.a0).toNat = r5.getReg AbiReg.a0 :=
        BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (r5.getReg AbiReg.a0).isLt])
      rw [hz]; dsimp only [evalBranch]; rw [← hbvEq, bitvec_slt_zero_iff _ (r5.getReg AbiReg.a0).isLt]
      simp [hlt2]
    rw [hev5False] at hbr5
    obtain ⟨kBr5, st5p, _, hrunBr5, hpc5p, hothBr5, _, hmBr5⟩ := hbr5
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc5p
    let p5p := pBr5 ++ [Asm.bge AbiReg.a0 AbiReg.zero drvDoneLabel]
    have hpc5p' : st5p.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p5p) := by
      rw [hpc5p]; exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (by
        dsimp only [p5p]
        simp only [Asm.bge, img.lkm.totalSize_append, img.lkm.totalSize_singleton]; rfl)
    have hlS5 : img.lkm.linkSpec (p5p ++ [Asm.slli AbiReg.s5 AbiReg.a0 1#6, Asm.srli AbiReg.s5 AbiReg.s5 1#6] ++
        (cmpDrvMode6Setup checkerTabMini ++ [Asm.call (fnLabel "check")] ++ cmpTail6 img)) =
        .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
      simpa only [p5p, List.append_assoc] using hlBr5
    obtain ⟨st60, hrunS5, hpc60, hs5_60, hothS5, hmS5⟩ :=
      cmp_slli_srli_rd_sim img AbiReg.s5 (by decide) (sig5.retVal.headD 0) hge5 p5p _ hlS5 st5p hpc5p'
        ((hothBr5 _ (by decide)).trans hra0_5)
    have hpc60' : st60.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize (cmpPreCall5 ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode5Post)) := by
      simpa only [p5p, pBr5, cmpDrvMode5Post, List.cons_append, List.nil_append, List.append_assoc] using hpc60
    exact ⟨hge5, k50 + k51 + kPost5 + kBr5 + 2, st60,
      by rw [run_add, run_add, hrunToR5]; dsimp only; rw [hrunBr5]; exact hrunS5,
      hpc60', (hothS5 _ (by decide)).trans ((hothBr5 _ (by decide)).trans hgpR5),
      hs5_60, by rw [hmS5, hmBr5]; exact hsavedR5, by rw [hmS5, hmBr5]; exact hmR5⟩
  · left
    have hlt2 : (r5.getReg AbiReg.a0).toNat < 2 ^ 63 := by rw [hra0_5]; exact Nat.lt_of_not_le hge5
    have hev5True : evalBranch .bge (r5.getReg AbiReg.a0) (r5.getReg AbiReg.zero) = true := by
      have hz : r5.getReg AbiReg.zero = 0#64 := rfl
      have hbvEq : BitVec.ofNat 64 (r5.getReg AbiReg.a0).toNat = r5.getReg AbiReg.a0 :=
        BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (r5.getReg AbiReg.a0).isLt])
      rw [hz]; dsimp only [evalBranch]; rw [← hbvEq, bitvec_slt_zero_iff _ (r5.getReg AbiReg.a0).isLt]
      simp [hlt2]
    rw [hev5True] at hbr5
    obtain ⟨kBr5, stDone5, _, hrunBr5, hpcDone5, hothBr5, _, hmDone5⟩ := hbr5
    simp only [↓reduceIte] at hpcDone5
    have hgpDone5 : stDone5.getReg AbiReg.gp = regionBase := (hothBr5 _ (by decide)).trans hgpR5
    have hsavedDone5 : DrvRegsSaved regionBase initSt stDone5.mem := by rw [hmDone5]; exact hsavedR5
    obtain ⟨mD5, rD5, hrunD5, hpcD5, hregsD5, hraD5, ha0D5, _, _⟩ :=
      linkedCmpDrvDone_returns img initSt regionBase halignSave stDone5 hpcDone5 hgpDone5 hsavedDone5
    have htot : RV64.run (linkedCmpEnv img).rom (k50 + k51 + kPost5 + kBr5 + mD5) initSt = .cont rD5 := by
      rw [run_add, run_add, hrunToR5]; dsimp only; rw [hrunBr5]; exact hrunD5
    have heqFin := run_ret_deterministic (linkedCmpEnv img).rom _ _ initSt hrun htot hret hpcD5 hRetOut
    refine ⟨UInt64.toBitVec_inj.mp (by rw [← hra0_5, ← hothBr5 _ (by decide), ← ha0D5, ← heqFin, ha0Out]), ?_⟩
    rw [heqFin]; exact ⟨hregsD5, hraD5⟩

private theorem cmp_mode6_step (img : LinkedCmpImage)
    (initSt : RV64.State)
    {solBase pinsBase regionBase : BitVec 64}
    {chalBytes solBytes pins : ByteArray}
    (hSol64 : solBase.toNat + solBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjSolPins : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjSolReg : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hStack6 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase6InitMem chalBytes solBytes pins) ≤ abiStack)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : img.rom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run img.rom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha0Out : finalSt.getReg AbiReg.a0 = acceptWord.toBitVec)
    (ha1Out : finalSt.getReg AbiReg.a1 = 0#64)
    {sig5 : _root_.L.Sig} {m5' : _root_.L.Mem}
    (hm5OutSz : (m5'.words (.t0 L.Arena.OUT)).size = abiWords)
    (hm6Init : cmpPhase6InitMem chalBytes solBytes pins = cmpPhase6Mem m5')
    {k60 : Nat} {st60 : RV64.State}
    (hrun60 : RV64.run (linkedCmpEnv img).rom k60 initSt = .cont st60)
    (hpc60 : st60.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize (cmpPreCall5 ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode5Post)))
    (hgp60 : st60.getReg AbiReg.gp = regionBase)
    (hs5_60 : st60.getReg AbiReg.s5 = (sig5.retVal.headD 0 - 9223372036854775808).toBitVec)
    (hsaved60 : DrvRegsSaved regionBase initSt st60.mem)
    (hMemRel_60 : ProgMemRel checkerTabMini (checkerLayoutA solBase pinsBase regionBase solBytes.size pins.size
      hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg) st60.mem m5') :
    ∃ (sig6 : _root_.L.Sig) (m6' : _root_.L.Mem) (b6' : Nat),
      runB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase6Mem m5') = .ok (sig6.retVal, m6', b6') ∧
      cmpRunMini (abiFuel - 1) checkerProgMini (cmpPhase6Mem m5') = .ok (sig6.retVal, m6') ∧
      (m6'.words (.t0 L.Arena.OUT)).size = abiWords ∧
      ((sig6.retVal.headD 0 = acceptWord ∧
        RegsRestored initSt finalSt ∧ finalSt.getReg AbiReg.ra = initSt.getReg AbiReg.ra) ∨
        (2 ^ 63 ≤ (sig6.retVal.headD 0).toNat ∧
         ∃ (k80 : Nat) (st80 : RV64.State),
           RV64.run (linkedCmpEnv img).rom k80 initSt = .cont st80 ∧
           st80.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize (cmpPreCall6 ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode6Post)) ∧
           st80.getReg AbiReg.gp = regionBase ∧
           st80.getReg AbiReg.s5 = (sig5.retVal.headD 0 - 9223372036854775808).toBitVec ∧
           st80.getReg AbiReg.s6 = (sig6.retVal.headD 0 - 9223372036854775808).toBitVec ∧
           DrvRegsSaved regionBase initSt st80.mem ∧
           ProgMemRel checkerTabMini (checkerLayoutA solBase pinsBase regionBase solBytes.size pins.size
             hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg) st80.mem m6')) := by
  let LA5 := checkerLayoutA solBase pinsBase regionBase solBytes.size pins.size
    hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg
  have halignSave : isAligned (regionBase + BitVec.ofInt 64 (checkerTabMini.saveBase 0)) 8 = true :=
    checkerTabMini_saveBase_align regionBase hRegAlign
  have hTabSave6 : checkerTabMini.saveBase 0 + 128 ≤ (LA5.tabBytes : Int) := by
    simp only [LA5, checkerLayoutA]; exact checkerTabMini_saveBase_le_abiSlot
  let p60 := cmpPreCall5 ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode5Post
  have hl6Setup : img.lkm.linkSpec (p60 ++ cmpDrvMode6Setup checkerTabMini ++
      ([Asm.call (fnLabel "check")] ++ cmpTail6 img)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p60, cmpPreCall5, cmpTail5, cmpTail4, cmpDrvMode4Post, cmpDrvMode5Post,
      List.cons_append, List.nil_append, List.append_assoc] using cmp_linkFull img
  obtain ⟨k61, st61, hrun61, hpc61, hgp61, hsp61, hs0_61, _, hs5_61, ht0_61, ht1_61,
      hout61, hTop6, hLim6⟩ :=
    cmpMode6Setup_sim img regionBase hRegAlign hReg64 p60 _ hl6Setup st60 hpc60 hgp60
  rcases hout61 with ⟨st6Mid, houtMid6, hm6Eq⟩
  have hsaved6Mid : DrvRegsSaved regionBase initSt st6Mid :=
    drvRegsSaved_of_memEqOutside_le_args (by omega)
      (by rw [checkerTabMini_args_eq, Int.toNat_natCast]; omega : 0 + 16 ≤ checkerTabMini.args.toNat)
      (by simpa only [BitVec.add_zero] using houtMid6) hsaved60
  have hsaved61 : DrvRegsSaved regionBase initSt st61.mem := by
    rw [hm6Eq]
    exact drvRegsSaved_of_writeWord64_lt_args (by omega)
      (by rw [globOff_eq_nat]; omega)
      (by rw [globOff_eq_nat, checkerTabMini_args_eq, checkerTabMini_resBase_eq, t_nxres]
          simp only [Int.toNat_natCast]
          have : modeGVar.id < 12 := by decide
          omega)
      6#64 hsaved6Mid
  have hMemRel6 : ProgMemRel checkerTabMini LA5 st61.mem (cmpPhase6Mem m5') :=
    cmpMode6_progMemRel hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg
      hMemRel_60 houtMid6 hm6Eq
  have hHdr6 : TabHeaderOk LA5 st61.mem := ⟨hTop6, hLim6⟩
  have hpc61' : st61.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize cmpPreCall6) := by
    simpa only [cmpPreCall6, p60, img.lkm.totalSize_append] using hpc61
  have hlCall6 : img.lkm.linkSpec (cmpPreCall6 ++ [Asm.call (fnLabel "check")] ++ cmpTail6 img) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [cmpPreCall6, p60, List.append_assoc] using hl6Setup
  have hrunTo61 : RV64.run (linkedCmpEnv img).rom (k60 + k61) initSt = .cont st61 := by
    rw [run_add, hrun60]; exact hrun61
  have hStack6' : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase6Mem m5') ≤ abiStack := by
    rw [← hm6Init]; exact hStack6
  obtain ⟨sig6, m6', b6', kPost6, r6, hrunB6, hMini6, hrunToR6, hpcR6, hgpR6, hra0_6, hcalR6, hsavedR6, hmR6, _⟩ :=
    linkedCmp_call_check_step img initSt hRegAlign hReg64 hRetOut hrun hret ha1Out
      LA5 rfl rfl rfl LA5.hTopAlign hTabSave6 cmpPreCall6 (cmpTail6 img) hlCall6
      (cmpPhase6Mem m5') hStack6' hrunTo61 hpc61' hgp61 hsp61 hs0_61 ht0_61 hsaved61 hMemRel6 hHdr6
  have hm6OutSz : (m6'.words (.t0 L.Arena.OUT)).size = abiWords := by
    rw [minil_run_words_size hMini6]; exact hm5OutSz
  refine ⟨sig6, m6', b6', hrunB6, hMini6, hm6OutSz, ?_⟩
  let pBr6 := cmpPreCall6 ++ [Asm.call (fnLabel "check")]
  have hlBr6 : img.lkm.linkSpec (pBr6 ++ [Asm.bge AbiReg.a0 AbiReg.zero drvDoneLabel] ++
      ([Asm.slli AbiReg.s6 AbiReg.a0 1#6, Asm.srli AbiReg.s6 AbiReg.s6 1#6] ++
       cmpDrvMode8Setup checkerTabMini ++ [Asm.call (fnLabel "check")] ++ cmpTail8 img)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [pBr6, cmpTail6, cmpDrvMode6Post, List.cons_append, List.nil_append, List.append_assoc] using hlCall6
  have hbr6 := run_br_step (linkedCmpEnv img) pBr6 _ .bge AbiReg.a0 AbiReg.zero drvDoneLabel _
    (checkerCmp_drvDone_lbl img) (by decide) hlBr6 r6 hpcR6
  by_cases hge6 : 2 ^ 63 ≤ (sig6.retVal.headD 0).toNat
  · right
    have hev6False : evalBranch .bge (r6.getReg AbiReg.a0) (r6.getReg AbiReg.zero) = false := by
      have hz : r6.getReg AbiReg.zero = 0#64 := rfl
      have hlt2 : 2 ^ 63 ≤ (r6.getReg AbiReg.a0).toNat := by rw [hra0_6]; exact hge6
      have hbvEq : BitVec.ofNat 64 (r6.getReg AbiReg.a0).toNat = r6.getReg AbiReg.a0 :=
        BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (r6.getReg AbiReg.a0).isLt])
      rw [hz]; dsimp only [evalBranch]; rw [← hbvEq, bitvec_slt_zero_iff _ (r6.getReg AbiReg.a0).isLt]
      simp [hlt2]
    rw [hev6False] at hbr6
    obtain ⟨kBr6, st6p, _, hrunBr6, hpc6p, hothBr6, _, hmBr6⟩ := hbr6
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc6p
    let p6p := pBr6 ++ [Asm.bge AbiReg.a0 AbiReg.zero drvDoneLabel]
    have hpc6p' : st6p.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p6p) := by
      rw [hpc6p]; exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (by
        dsimp only [p6p]
        simp only [Asm.bge, img.lkm.totalSize_append, img.lkm.totalSize_singleton]; rfl)
    have hlS6 : img.lkm.linkSpec (p6p ++ [Asm.slli AbiReg.s6 AbiReg.a0 1#6, Asm.srli AbiReg.s6 AbiReg.s6 1#6] ++
        (cmpDrvMode8Setup checkerTabMini ++ [Asm.call (fnLabel "check")] ++ cmpTail8 img)) =
        .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
      simpa only [p6p, List.append_assoc] using hlBr6
    obtain ⟨st80, hrunS6, hpc80, hs6_80, hothS6, hmS6⟩ :=
      cmp_slli_srli_rd_sim img AbiReg.s6 (by decide) (sig6.retVal.headD 0) hge6 p6p _ hlS6 st6p hpc6p'
        ((hothBr6 _ (by decide)).trans hra0_6)
    have hpc80' : st80.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize (cmpPreCall6 ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode6Post)) := by
      simpa only [p6p, pBr6, cmpDrvMode6Post, List.cons_append, List.nil_append, List.append_assoc] using hpc80
    have hs5_r6 : r6.getReg AbiReg.s5 = (sig5.retVal.headD 0 - 9223372036854775808).toBitVec :=
      (hcalR6 _ (by decide)).trans (hs5_61.trans hs5_60)
    exact ⟨hge6, k60 + k61 + kPost6 + kBr6 + 2, st80,
      by rw [run_add, run_add, hrunToR6]; dsimp only; rw [hrunBr6]; exact hrunS6,
      hpc80', (hothS6 _ (by decide)).trans ((hothBr6 _ (by decide)).trans hgpR6),
      (hothS6 _ (by decide)).trans ((hothBr6 _ (by decide)).trans hs5_r6),
      hs6_80, by rw [hmS6, hmBr6]; exact hsavedR6, by rw [hmS6, hmBr6]; exact hmR6⟩
  · left
    have hlt2 : (r6.getReg AbiReg.a0).toNat < 2 ^ 63 := by rw [hra0_6]; exact Nat.lt_of_not_le hge6
    have hev6True : evalBranch .bge (r6.getReg AbiReg.a0) (r6.getReg AbiReg.zero) = true := by
      have hz : r6.getReg AbiReg.zero = 0#64 := rfl
      have hbvEq : BitVec.ofNat 64 (r6.getReg AbiReg.a0).toNat = r6.getReg AbiReg.a0 :=
        BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (r6.getReg AbiReg.a0).isLt])
      rw [hz]; dsimp only [evalBranch]; rw [← hbvEq, bitvec_slt_zero_iff _ (r6.getReg AbiReg.a0).isLt]
      simp [hlt2]
    rw [hev6True] at hbr6
    obtain ⟨kBr6, stDone6, _, hrunBr6, hpcDone6, hothBr6, _, hmDone6⟩ := hbr6
    simp only [↓reduceIte] at hpcDone6
    have hgpDone6 : stDone6.getReg AbiReg.gp = regionBase := (hothBr6 _ (by decide)).trans hgpR6
    have hsavedDone6 : DrvRegsSaved regionBase initSt stDone6.mem := by rw [hmDone6]; exact hsavedR6
    obtain ⟨mD6, rD6, hrunD6, hpcD6, hregsD6, hraD6, ha0D6, _, _⟩ :=
      linkedCmpDrvDone_returns img initSt regionBase halignSave stDone6 hpcDone6 hgpDone6 hsavedDone6
    have htot : RV64.run (linkedCmpEnv img).rom (k60 + k61 + kPost6 + kBr6 + mD6) initSt = .cont rD6 := by
      rw [run_add, run_add, hrunToR6]; dsimp only; rw [hrunBr6]; exact hrunD6
    have heqFin := run_ret_deterministic (linkedCmpEnv img).rom _ _ initSt hrun htot hret hpcD6 hRetOut
    refine ⟨UInt64.toBitVec_inj.mp (by rw [← hra0_6, ← hothBr6 _ (by decide), ← ha0D6, ← heqFin, ha0Out]), ?_⟩
    rw [heqFin]; exact ⟨hregsD6, hraD6⟩

private theorem cmp_mode8_step (img : LinkedCmpImage)
    (initSt : RV64.State)
    {solBase pinsBase regionBase : BitVec 64}
    {chalBytes solBytes pins : ByteArray}
    (hSol64 : solBase.toNat + solBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjSolPins : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjSolReg : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hStack8 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase8InitMem chalBytes solBytes pins) ≤ abiStack)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : img.rom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run img.rom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha0Out : finalSt.getReg AbiReg.a0 = acceptWord.toBitVec)
    (ha1Out : finalSt.getReg AbiReg.a1 = 0#64)
    {sig5 sig6 : _root_.L.Sig} {m6' : _root_.L.Mem}
    (hge5 : 2 ^ 63 ≤ (sig5.retVal.headD 0).toNat)
    (hm6OutSz : (m6'.words (.t0 L.Arena.OUT)).size = abiWords)
    (hm8Init : cmpPhase8InitMem chalBytes solBytes pins = cmpPhase8Mem m6' (sig5.retVal.headD 0))
    {k80 : Nat} {st80 : RV64.State}
    (hrun80 : RV64.run (linkedCmpEnv img).rom k80 initSt = .cont st80)
    (hpc80 : st80.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize (cmpPreCall6 ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode6Post)))
    (hgp80 : st80.getReg AbiReg.gp = regionBase)
    (hs5_80 : st80.getReg AbiReg.s5 = (sig5.retVal.headD 0 - 9223372036854775808).toBitVec)
    (hs6_80 : st80.getReg AbiReg.s6 = (sig6.retVal.headD 0 - 9223372036854775808).toBitVec)
    (hsaved80 : DrvRegsSaved regionBase initSt st80.mem)
    (hMemRel_80 : ProgMemRel checkerTabMini (checkerLayoutA solBase pinsBase regionBase solBytes.size pins.size
      hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg) st80.mem m6') :
    ∃ (sig8 : _root_.L.Sig) (m8' : _root_.L.Mem) (b8' : Nat),
      runB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase8Mem m6' (sig5.retVal.headD 0)) = .ok (sig8.retVal, m8', b8') ∧
      cmpRunMini (abiFuel - 1) checkerProgMini (cmpPhase8Mem m6' (sig5.retVal.headD 0)) = .ok (sig8.retVal, m8') ∧
      sig8.retVal.headD 0 = acceptWord ∧
      ∃ (k90 : Nat) (st90 : RV64.State),
        RV64.run (linkedCmpEnv img).rom k90 initSt = .cont st90 ∧
        st90.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize (cmpPreCall8 ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode8Post)) ∧
        st90.getReg AbiReg.gp = regionBase ∧
        st90.getReg AbiReg.s6 = (sig6.retVal.headD 0 - 9223372036854775808).toBitVec ∧
        DrvRegsSaved regionBase initSt st90.mem ∧
        ProgMemRel checkerTabMini (checkerLayoutCmpB solBase pinsBase regionBase solBytes.size pins.size
          hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg) st90.mem m8' := by
  let LB8 := checkerLayoutCmpB solBase pinsBase regionBase solBytes.size pins.size
    hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg
  have halignSave : isAligned (regionBase + BitVec.ofInt 64 (checkerTabMini.saveBase 0)) 8 = true :=
    checkerTabMini_saveBase_align regionBase hRegAlign
  have hTabSave8 : checkerTabMini.saveBase 0 + 128 ≤ (LB8.tabBytes : Int) := by
    simp only [LB8, checkerLayoutCmpB, checkerLayoutBGen, checkerLayoutA]
    exact checkerTabMini_saveBase_le_abiSlot
  let p80 := cmpPreCall6 ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode6Post
  have hl8Setup : img.lkm.linkSpec (p80 ++ cmpDrvMode8Setup checkerTabMini ++
      ([Asm.call (fnLabel "check")] ++ cmpTail8 img)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p80, cmpPreCall6, cmpPreCall5, cmpTail6, cmpTail5, cmpTail4,
      cmpDrvMode4Post, cmpDrvMode5Post, cmpDrvMode6Post, List.cons_append, List.nil_append,
      List.append_assoc] using cmp_linkFull img
  obtain ⟨k81, st81, hrun81, hpc81, hgp81, hs0_81, hsp81, _, hs6_81, ht0_81, ht1_81,
      hout81, hTop8, hLim8, hPhi8, hPlo8, hMode8, h180B, h180L, h182B, h182L, h181B, h181L⟩ :=
    cmpMode8Setup_sim img regionBase hRegAlign hReg64 (sig5.retVal.headD 0) hge5 p80 _
      hl8Setup st80 hpc80 hgp80 hs5_80
  have hsaved81 : DrvRegsSaved regionBase initSt st81.mem :=
    drvRegsSaved_of_progMemOutside hout81 (phaseBWriteSpan_disj_callerSave regionBase hReg64) hsaved80
  have hMemRel8 : ProgMemRel checkerTabMini LB8 st81.mem (cmpPhase8Mem m6' (sig5.retVal.headD 0)) :=
    phaseB_progMemRel_gen hdrHw (by decide) (by decide) (by decide)
      hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg
      hMemRel_80 hm6OutSz (fun _ => rfl) rfl rfl rfl
      (fun s h1 h2 h3 => by simp [cmpPhase8Mem, h1, h2, h3])
      rfl (by simp [cmpPhase8Mem, (by decide : ploGVar ≠ phiGVar)])
      (by simp [cmpPhase8Mem, (by decide : modeGVar ≠ phiGVar), (by decide : modeGVar ≠ ploGVar)])
      (fun g h1 h2 h3 => by simp [cmpPhase8Mem, h1, h2, h3])
      hout81 hPhi8 hPlo8 hMode8 h180B h180L h182B h182L h181B h181L
  have hHdr8 : TabHeaderOk LB8 st81.mem := ⟨hTop8, hLim8⟩
  have hpc81' : st81.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize cmpPreCall8) := by
    simpa only [cmpPreCall8, p80, img.lkm.totalSize_append] using hpc81
  have hlCall8 : img.lkm.linkSpec (cmpPreCall8 ++ [Asm.call (fnLabel "check")] ++ cmpTail8 img) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [cmpPreCall8, p80, List.append_assoc] using hl8Setup
  have hrunTo81 : RV64.run (linkedCmpEnv img).rom (k80 + k81) initSt = .cont st81 := by
    rw [run_add, hrun80]; exact hrun81
  have hStack8' : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase8Mem m6' (sig5.retVal.headD 0)) ≤ abiStack := by
    rw [← hm8Init]; exact hStack8
  obtain ⟨sig8, m8', b8', kPost8, r8, hrunB8, hMini8, hrunToR8, hpcR8, hgpR8, hra0_8, hcalR8, hsavedR8, hmR8, _⟩ :=
    linkedCmp_call_check_step img initSt hRegAlign hReg64 hRetOut hrun hret ha1Out
      LB8 rfl rfl rfl LB8.hTopAlign hTabSave8 cmpPreCall8 (cmpTail8 img) hlCall8
      (cmpPhase8Mem m6' (sig5.retVal.headD 0)) hStack8' hrunTo81 hpc81' hgp81 hsp81 hs0_81 ht0_81 hsaved81 hMemRel8 hHdr8
  let pLi8 := cmpPreCall8 ++ [Asm.call (fnLabel "check")]
  have hlLi8 : img.lkm.linkSpec (pLi8 ++ li AbiReg.t1 acceptWord.toBitVec ++
      ([Asm.bne AbiReg.a0 AbiReg.t1 drvDoneLabel] ++
       cmpDrvMode9Setup checkerTabMini ++ [Asm.call (fnLabel "check")] ++ cmpTail9 img)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [pLi8, cmpTail8, cmpDrvMode8Post, List.append_assoc] using hlCall8
  have hpcLi8_64 := linkResolved_sub_pc64 (linkedCmpEnv img) pLi8 (li AbiReg.t1 acceptWord.toBitVec) _ hlLi8
  obtain ⟨s8t, hrunLi8, hothLi8, ht1_Li8, hmLi8, hpcLi8⟩ :=
    li_correct_lm img.lkm (linkedCmpEnv img).hrom pLi8 _ AbiReg.t1 (by decide)
      acceptWord.toBitVec hlLi8 hpcLi8_64 r8 hpcR8
  let pBr8 := pLi8 ++ li AbiReg.t1 acceptWord.toBitVec
  have hpcBr8' : s8t.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize pBr8) := by
    simpa only [pBr8, img.lkm.totalSize_append] using hpcLi8
  have hlBr8 : img.lkm.linkSpec (pBr8 ++ [Asm.bne AbiReg.a0 AbiReg.t1 drvDoneLabel] ++
      (cmpDrvMode9Setup checkerTabMini ++ [Asm.call (fnLabel "check")] ++ cmpTail9 img)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [pBr8, List.append_assoc] using hlLi8
  have hbr8 := run_br_step (linkedCmpEnv img) pBr8 _ .bne AbiReg.a0 AbiReg.t1 drvDoneLabel _
    (checkerCmp_drvDone_lbl img) (by decide) hlBr8 s8t hpcBr8'
  have hacc8 : sig8.retVal.headD 0 = acceptWord := by
    by_cases heq8 : sig8.retVal.headD 0 = acceptWord
    · exact heq8
    · have hev8True : evalBranch .bne (s8t.getReg AbiReg.a0) (s8t.getReg AbiReg.t1) = true := by
        rw [hothLi8 _ (by decide), hra0_8, ht1_Li8]
        have hneBv : (sig8.retVal.headD 0).toBitVec ≠ acceptWord.toBitVec :=
          fun h => heq8 (UInt64.toBitVec_inj.mp h)
        dsimp only [evalBranch]
        rw [bne_iff_ne.mpr hneBv]
      rw [hev8True] at hbr8
      obtain ⟨kBr8, stDone8, _, hrunBr8, hpcDone8, hothBr8, _, hmDone8⟩ := hbr8
      simp only [↓reduceIte] at hpcDone8
      have hgpDone8 : stDone8.getReg AbiReg.gp = regionBase :=
        (hothBr8 _ (by decide)).trans ((hothLi8 _ (by decide)).trans hgpR8)
      have hsavedDone8 : DrvRegsSaved regionBase initSt stDone8.mem := by
        rw [hmDone8, hmLi8]; exact hsavedR8
      obtain ⟨mD, rD, hrunD, hpcD, _, _, ha0D, _, _⟩ :=
        linkedCmpDrvDone_returns img initSt regionBase halignSave stDone8 hpcDone8 hgpDone8 hsavedDone8
      have htot : RV64.run (linkedCmpEnv img).rom
          (k80 + k81 + kPost8 + img.lkm.totalSize (li AbiReg.t1 acceptWord.toBitVec) + kBr8 + mD)
          initSt = .cont rD := by
        rw [run_add, run_add, run_add, hrunToR8]; dsimp only
        rw [hrunLi8]; dsimp only; rw [hrunBr8]; exact hrunD
      have heqFin := run_ret_deterministic (linkedCmpEnv img).rom _ _ initSt hrun htot hret hpcD hRetOut
      exact absurd (UInt64.toBitVec_inj.mp (by rw [← hra0_8, ← hothLi8 _ (by decide), ← hothBr8 _ (by decide), ← ha0D, ← heqFin, ha0Out])) heq8
  have hev8False : evalBranch .bne (s8t.getReg AbiReg.a0) (s8t.getReg AbiReg.t1) = false := by
    rw [hothLi8 _ (by decide), hra0_8, ht1_Li8, hacc8]
    simp [evalBranch]
  rw [hev8False] at hbr8
  obtain ⟨kBr8, st90, _, hrunBr8, hpc90, hothBr8, _, hmBr8⟩ := hbr8
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc90
  have hpc90' : st90.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize (cmpPreCall8 ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode8Post)) := by
    rw [hpc90, ← img.lkm.totalSize_append]
    exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (by
      simp only [pBr8, pLi8, cmpDrvMode8Post, Asm.bne, List.append_assoc]; rfl)
  have hs6_r8 : r8.getReg AbiReg.s6 = (sig6.retVal.headD 0 - 9223372036854775808).toBitVec :=
    (hcalR8 _ (by decide)).trans (hs6_81.trans hs6_80)
  refine ⟨sig8, m8', b8', hrunB8, hMini8, hacc8,
    k80 + k81 + kPost8 + img.lkm.totalSize (li AbiReg.t1 acceptWord.toBitVec) + kBr8,
    st90, by rw [run_add, run_add, hrunToR8]; dsimp only; rw [hrunLi8]; exact hrunBr8,
    hpc90', (hothBr8 _ (by decide)).trans ((hothLi8 _ (by decide)).trans hgpR8),
    (hothBr8 _ (by decide)).trans ((hothLi8 _ (by decide)).trans hs6_r8),
    by rw [hmBr8, hmLi8]; exact hsavedR8,
    by rw [hmBr8, hmLi8]; exact hmR8⟩

private theorem cmp_mode9_step (img : LinkedCmpImage)
    (initSt : RV64.State)
    {solBase pinsBase regionBase : BitVec 64}
    {chalBytes solBytes pins : ByteArray}
    (hSol64 : solBase.toNat + solBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjSolPins : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjSolReg : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hStack9 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase9InitMem chalBytes solBytes pins) ≤ abiStack)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : img.rom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run img.rom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha0Out : finalSt.getReg AbiReg.a0 = acceptWord.toBitVec)
    (ha1Out : finalSt.getReg AbiReg.a1 = 0#64)
    {sig6 : _root_.L.Sig} {m8' : _root_.L.Mem}
    (hm9Init : cmpPhase9InitMem chalBytes solBytes pins = cmpPhase9Mem m8' (sig6.retVal.headD 0))
    {k90 : Nat} {st90 : RV64.State}
    (hrun90 : RV64.run (linkedCmpEnv img).rom k90 initSt = .cont st90)
    (hpc90 : st90.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize (cmpPreCall8 ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode8Post)))
    (hgp90 : st90.getReg AbiReg.gp = regionBase)
    (hs6_90 : st90.getReg AbiReg.s6 = (sig6.retVal.headD 0 - 9223372036854775808).toBitVec)
    (hsaved90 : DrvRegsSaved regionBase initSt st90.mem)
    (hMemRel_90 : ProgMemRel checkerTabMini (checkerLayoutCmpB solBase pinsBase regionBase solBytes.size pins.size
      hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg) st90.mem m8') :
    ∃ (sig9 : _root_.L.Sig) (m9' : _root_.L.Mem),
      cmpRunMini (abiFuel - 1) checkerProgMini (cmpPhase9Mem m8' (sig6.retVal.headD 0)) = .ok (sig9.retVal, m9') ∧
      sig9.retVal.headD 0 = acceptWord ∧
      RegsRestored initSt finalSt ∧ finalSt.getReg AbiReg.ra = initSt.getReg AbiReg.ra := by
  let LB8 := checkerLayoutCmpB solBase pinsBase regionBase solBytes.size pins.size
    hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg
  have halignSave : isAligned (regionBase + BitVec.ofInt 64 (checkerTabMini.saveBase 0)) 8 = true :=
    checkerTabMini_saveBase_align regionBase hRegAlign
  have hTabSave9 : checkerTabMini.saveBase 0 + 128 ≤ (LB8.tabBytes : Int) := by
    simp only [LB8, checkerLayoutCmpB, checkerLayoutBGen, checkerLayoutA]
    exact checkerTabMini_saveBase_le_abiSlot
  let p90 := cmpPreCall8 ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode8Post
  have hl9Setup : img.lkm.linkSpec (p90 ++ cmpDrvMode9Setup checkerTabMini ++
      ([Asm.call (fnLabel "check")] ++ cmpTail9 img)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p90, cmpPreCall8, cmpPreCall6, cmpPreCall5, cmpTail8, cmpTail6, cmpTail5, cmpTail4,
      cmpDrvMode4Post, cmpDrvMode5Post, cmpDrvMode6Post, cmpDrvMode8Post,
      List.cons_append, List.nil_append, List.append_assoc] using cmp_linkFull img
  obtain ⟨k91, st91, hrun91, hpc91, hgp91, hs0_91, hsp91, _, ht0_91, ht1_91,
      hout91, hTop9, hLim9, hPhi9, hPlo9, hMode9⟩ :=
    cmpMode9Setup_sim img regionBase hRegAlign hReg64 (sig6.retVal.headD 0) p90 _
      hl9Setup st90 hpc90 hgp90 hs6_90
  have hsaved91 : DrvRegsSaved regionBase initSt st91.mem :=
    drvRegsSaved_of_progMemOutside hout91 (cmp9WriteSpan_disj_callerSave regionBase hReg64) hsaved90
  have hMemRel9 : ProgMemRel checkerTabMini LB8 st91.mem (cmpPhase9Mem m8' (sig6.retVal.headD 0)) :=
    cmpMode9_progMemRel hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg
      hMemRel_90 hout91 hPhi9 hPlo9 hMode9
  have hHdr9 : TabHeaderOk LB8 st91.mem := ⟨hTop9, hLim9⟩
  have hpc91' : st91.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize cmpPreCall9) := by
    simpa only [cmpPreCall9, p90, img.lkm.totalSize_append] using hpc91
  have hlCall9 : img.lkm.linkSpec (cmpPreCall9 ++ [Asm.call (fnLabel "check")] ++ cmpTail9 img) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [cmpPreCall9, p90, List.append_assoc] using hl9Setup
  have hrunTo91 : RV64.run (linkedCmpEnv img).rom (k90 + k91) initSt = .cont st91 := by
    rw [run_add, hrun90]; exact hrun91
  have hStack9' : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase9Mem m8' (sig6.retVal.headD 0)) ≤ abiStack := by
    rw [← hm9Init]; exact hStack9
  obtain ⟨sig9, m9', _, kPost9, r9, _, hMini9, hrunToR9, hpcR9, hgpR9, hrb0, _, hsavedR9, _, _⟩ :=
    linkedCmp_call_check_step img initSt hRegAlign hReg64 hRetOut hrun hret ha1Out
      LB8 rfl rfl rfl LB8.hTopAlign hTabSave9 cmpPreCall9 (cmpTail9 img) hlCall9
      (cmpPhase9Mem m8' (sig6.retVal.headD 0)) hStack9' hrunTo91 hpc91' hgp91 hsp91 hs0_91 ht0_91 hsaved91 hMemRel9 hHdr9
  let pJ9 := cmpPreCall9 ++ [Asm.call (fnLabel "check")]
  have hlJ9 : img.lkm.linkSpec (pJ9 ++ [Asm.j drvDoneLabel] ++ linkedCmpFnsAsm img) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [pJ9, cmpTail9, List.append_assoc] using hlCall9
  have h64J9 : 4 * (img.lkm.totalSize pJ9 + img.lkm.itemSize (.j drvDoneLabel)) < 2 ^ 64 := by
    simpa [Asm.j, img.lkm.totalSize_singleton] using
      linkResolved_sub_pc64 (linkedCmpEnv img) pJ9 [Asm.j drvDoneLabel] _ hlJ9
  obtain ⟨kJ9, stDone9, hrunJ9, hpcDone9, hothJ9, _, hmDone9⟩ :=
    prog_step_j (linkedCmpEnv img) pJ9 _ drvDoneLabel (img.lkm.totalSize (drvPreDone checkerTabMini))
      (checkerCmp_drvDone_lbl img) hlJ9 h64J9 r9 hpcR9
  have hgpDone9 : stDone9.getReg AbiReg.gp = regionBase := (hothJ9 _ (by decide)).trans hgpR9
  have hsavedDone9 : DrvRegsSaved regionBase initSt stDone9.mem := by rw [hmDone9]; exact hsavedR9
  obtain ⟨mD9, rD9, hrunD9, hpcD9, hregsD9, hraD9, ha0D9, _, _⟩ :=
    linkedCmpDrvDone_returns img initSt regionBase halignSave stDone9 hpcDone9 hgpDone9 hsavedDone9
  have htot : RV64.run (linkedCmpEnv img).rom (k90 + k91 + kPost9 + kJ9 + mD9) initSt = .cont rD9 := by
    rw [run_add, run_add, hrunToR9]; dsimp only; rw [hrunJ9]; exact hrunD9
  have heqFin := run_ret_deterministic (linkedCmpEnv img).rom _ _ initSt hrun htot hret hpcD9 hRetOut
  refine ⟨sig9, m9', hMini9,
    UInt64.toBitVec_inj.mp (by rw [← hrb0, ← hothJ9 _ (by decide), ← ha0D9, ← heqFin, ha0Out]), ?_⟩
  rw [heqFin]; exact ⟨hregsD9, hraD9⟩

private theorem cmp_mode89_bridge
    (m6' m8' m9' : _root_.L.Mem) (sig5 sig6 sig8 sig9 : _root_.L.Sig)
    (hMini8 : cmpRunMini (abiFuel - 1) checkerProgMini (cmpPhase8Mem m6' (sig5.retVal.headD 0)) = .ok (sig8.retVal, m8'))
    (hMini9 : cmpRunMini (abiFuel - 1) checkerProgMini (cmpPhase9Mem m8' (sig6.retVal.headD 0)) = .ok (sig9.retVal, m9')) :
    ∃ m8N' m9N',
      cmpRunMini (abiFuel - 1) checkerProgMini
        (seqMemWMini m6' modeGVar ploGVar phiGVar outArr hdrfArr ctlfArr hdrHw 8 0
          (sig5.retVal.getD 0 0 - 9223372036854775808)) = .ok (sig8.retVal, m8N') ∧
      cmpRunMini (abiFuel - 1) checkerProgMini
        (seqNextMini m8N' modeGVar ploGVar phiGVar 9 0
          (sig6.retVal.getD 0 0 - 9223372036854775808)) = .ok (sig9.retVal, m9N') := by
  have hret5Eq : sig5.retVal.headD 0 = sig5.retVal.getD 0 0 := by cases sig5.retVal <;> rfl
  have hret6Eq : sig6.retVal.headD 0 = sig6.retVal.getD 0 0 := by cases sig6.retVal <;> rfl
  let m8N_init := seqMemWMini m6' modeGVar ploGVar phiGVar outArr hdrfArr ctlfArr hdrHw
    8 0 (sig5.retVal.getD 0 0 - 9223372036854775808)
  have hAg8 : L.Agree L.Checker.phaseBPa (fun _ => false)
      (cmpPhase8Mem m6' (sig5.retVal.headD 0)) m8N_init := by
    refine ⟨fun a ha => ?_, fun _ h => absurd h (by simp), funext fun g => ?_⟩
    · simp only [L.Checker.phaseBPa, Bool.and_eq_true, bne_iff_ne, ne_eq] at ha
      have hne1 : a ≠ .t0 L.Arena.OUT := ha.1.1
      have hne2 : a ≠ .t0 L.Arena.HDRF := ha.1.2
      have hne3 : a ≠ .t0 L.Arena.CTLF := ha.2
      dsimp only [m8N_init, seqMemWMini, seqNextMini, seqMem0Mini, cmpPhase8Mem,
        _root_.L.Mem.arr64, _root_.L.Mem.setG, outArr, ctlfArr, hdrfArr]
      simp only [hne1, hne2, hne3, or_self, ↓reduceIte]
    · by_cases hgM : g = modeGVar
      · rw [hgM]
        simp only [m8N_init, seqMemWMini, seqNextMini, cmpPhase8Mem, _root_.L.Mem.setG,
          (by decide : modeGVar ≠ phiGVar), (by decide : modeGVar ≠ ploGVar), ↓reduceIte]
      · by_cases hgHi : g = phiGVar
        · rw [hgHi]
          dsimp only [m8N_init, seqMemWMini, seqNextMini, cmpPhase8Mem, _root_.L.Mem.setG]
          rw [← hret5Eq]
          simp only [(by decide : phiGVar ≠ modeGVar), ↓reduceIte]
        · by_cases hgLo : g = ploGVar
          · rw [hgLo]
            simp only [m8N_init, seqMemWMini, seqNextMini, cmpPhase8Mem, _root_.L.Mem.setG,
              (by decide : ploGVar ≠ modeGVar), (by decide : ploGVar ≠ phiGVar), ↓reduceIte]
          · simp only [m8N_init, seqMemWMini, seqNextMini, seqMem0Mini, cmpPhase8Mem, _root_.L.Mem.setG,
              hgM, hgHi, hgLo, ↓reduceIte]
  have hmode8 : (cmpPhase8Mem m6' (sig5.retVal.headD 0)).glob modeGVar = 8 := by
    simp [cmpPhase8Mem, (by decide : modeGVar ≠ phiGVar), (by decide : modeGVar ≠ ploGVar)]
  have hMini8' : _root_.L.run checkerProgMini ((abiFuel - 2) + 1) "check" []
      (cmpPhase8Mem m6' (sig5.retVal.headD 0)) = .ok (sig8.retVal, m8') := by
    simpa only [show abiFuel - 1 = (abiFuel - 2) + 1 from by simp [abiFuel]] using hMini8
  obtain ⟨m8N', hrun8N', hAg8'⟩ := run_check_mode89_agree_ok 8 (Or.inl rfl) hAg8 hmode8 hMini8'
  have hMini8N' : cmpRunMini (abiFuel - 1) checkerProgMini m8N_init = .ok (sig8.retVal, m8N') := by
    simpa only [show abiFuel - 1 = (abiFuel - 2) + 1 from by simp [abiFuel]] using hrun8N'
  let m9N_init := seqNextMini m8N' modeGVar ploGVar phiGVar 9 0 (sig6.retVal.getD 0 0 - 9223372036854775808)
  have hAg9 : L.Agree L.Checker.phaseBPa (fun _ => false)
      (cmpPhase9Mem m8' (sig6.retVal.headD 0)) m9N_init := by
    refine ⟨fun a ha => hAg8'.1 a ha, fun _ h => absurd h (by simp), funext fun g => ?_⟩
    by_cases hgM : g = modeGVar
    · rw [hgM]
      simp only [m9N_init, cmpPhase9Mem, seqNextMini, _root_.L.Mem.setG, ↓reduceIte]
    · by_cases hgHi : g = phiGVar
      · rw [hgHi]
        dsimp only [m9N_init, cmpPhase9Mem, seqNextMini, _root_.L.Mem.setG]
        rw [← hret6Eq]
        simp only [(by decide : phiGVar ≠ modeGVar), ↓reduceIte]
      · by_cases hgLo : g = ploGVar
        · rw [hgLo]
          simp only [m9N_init, cmpPhase9Mem, seqNextMini, _root_.L.Mem.setG,
            (by decide : ploGVar ≠ modeGVar), (by decide : ploGVar ≠ phiGVar), ↓reduceIte]
        · have hge := congrFun hAg8'.2.2 g
          simp only [m9N_init, cmpPhase9Mem, seqNextMini, _root_.L.Mem.setG, hgM, hgHi, hgLo, ↓reduceIte]
          exact hge
  have hmode9 : (cmpPhase9Mem m8' (sig6.retVal.headD 0)).glob modeGVar = 9 := by
    simp [cmpPhase9Mem, seqNextMini, _root_.L.Mem.setG]
  have hMini9' : _root_.L.run checkerProgMini ((abiFuel - 2) + 1) "check" []
      (cmpPhase9Mem m8' (sig6.retVal.headD 0)) = .ok (sig9.retVal, m9') := by
    simpa only [show abiFuel - 1 = (abiFuel - 2) + 1 from by simp [abiFuel]] using hMini9
  obtain ⟨m9N', hrun9N', _⟩ := run_check_mode89_agree_ok 9 (Or.inr rfl) hAg9 hmode9 hMini9'
  have hMini9N' : cmpRunMini (abiFuel - 1) checkerProgMini m9N_init = .ok (sig9.retVal, m9N') := by
    simpa only [show abiFuel - 1 = (abiFuel - 2) + 1 from by simp [abiFuel]] using hrun9N'
  exact ⟨m8N', m9N', hMini8N', hMini9N'⟩

private theorem cmp_hm5Init (chalBytes solBytes pins : ByteArray)
    {rs4 : List _root_.L.Word} {m4' : _root_.L.Mem} {b4' : Nat}
    (hrunB4 : runB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase4Mem chalBytes pins) = .ok (rs4, m4', b4')) :
    cmpPhase5InitMem chalBytes solBytes pins = cmpPhase5Mem m4' solBytes := by
  simp only [cmpPhase5InitMem, hrunB4]

private theorem cmp_hm6Init (chalBytes solBytes pins : ByteArray)
    {m4' m5' : _root_.L.Mem} {rs5 : List _root_.L.Word} {b5' : Nat}
    (hm5Init : cmpPhase5InitMem chalBytes solBytes pins = cmpPhase5Mem m4' solBytes)
    (hrunB5 : runB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase5Mem m4' solBytes) = .ok (rs5, m5', b5')) :
    cmpPhase6InitMem chalBytes solBytes pins = cmpPhase6Mem m5' := by
  simp only [cmpPhase6InitMem, hm5Init, hrunB5]

private theorem cmp_hm8Init (chalBytes solBytes pins : ByteArray)
    {m4' m5' m6' : _root_.L.Mem} {rs5 rs6 : List _root_.L.Word} {b5' b6' : Nat}
    (hm5Init : cmpPhase5InitMem chalBytes solBytes pins = cmpPhase5Mem m4' solBytes)
    (hrunB5 : runB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase5Mem m4' solBytes) = .ok (rs5, m5', b5'))
    (hm6Init : cmpPhase6InitMem chalBytes solBytes pins = cmpPhase6Mem m5')
    (hrunB6 : runB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase6Mem m5') = .ok (rs6, m6', b6')) :
    cmpPhase8InitMem chalBytes solBytes pins = cmpPhase8Mem m6' (rs5.headD 0) := by
  simp only [cmpPhase8InitMem, hm5Init, hrunB5, hm6Init, hrunB6]

private theorem cmp_hm9Init (chalBytes solBytes pins : ByteArray)
    {m5' m6' m8' : _root_.L.Mem} {rs5 rs6 rs8 : List _root_.L.Word} {b6' b8' : Nat}
    (hm6Init : cmpPhase6InitMem chalBytes solBytes pins = cmpPhase6Mem m5')
    (hrunB6 : runB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase6Mem m5') = .ok (rs6, m6', b6'))
    (hm8Init : cmpPhase8InitMem chalBytes solBytes pins = cmpPhase8Mem m6' (rs5.headD 0))
    (hrunB8 : runB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase8Mem m6' (rs5.headD 0)) = .ok (rs8, m8', b8')) :
    cmpPhase9InitMem chalBytes solBytes pins = cmpPhase9Mem m8' (rs6.headD 0) := by
  simp only [cmpPhase9InitMem, hm6Init, hrunB6, hm8Init, hrunB8]

private theorem cmp_acc_done4 {chalBytes solBytes pins : ByteArray}
    (hchal63 : chalBytes.size < 2 ^ 63) (hpins63 : pins.size < 2 ^ 63)
    {sig4 : _root_.L.Sig} {m4' : _root_.L.Mem}
    (hMini4 : cmpRunMini (abiFuel - 1) checkerProgMini (cmpPhase4Mem chalBytes pins) = .ok (sig4.retVal, m4'))
    (hacc4 : sig4.retVal.headD 0 = acceptWord) :
    CmpAccSSzMini (fun _ => abiWords) (abiFuel - 1) checkerProgMini chalBytes solBytes pins := by
  have hret4Eq : sig4.retVal.headD 0 = sig4.retVal.getD 0 0 := by cases sig4.retVal <;> rfl
  exact Or.inl ⟨hchal63, hpins63, sig4.retVal, m4', hMini4, Or.inl (hret4Eq ▸ hacc4)⟩

private theorem cmp_acc_done5 {chalBytes solBytes pins : ByteArray}
    (hchal63 : chalBytes.size < 2 ^ 63) (hpins63 : pins.size < 2 ^ 63) (hsol63 : solBytes.size < 2 ^ 63)
    {sig4 sig5 : _root_.L.Sig} {m4' m5' : _root_.L.Mem}
    (hMini4 : cmpRunMini (abiFuel - 1) checkerProgMini (cmpPhase4Mem chalBytes pins) = .ok (sig4.retVal, m4'))
    (hge4 : 2 ^ 63 ≤ (sig4.retVal.headD 0).toNat)
    (hMini5 : cmpRunMini (abiFuel - 1) checkerProgMini (cmpPhase5Mem m4' solBytes) = .ok (sig5.retVal, m5'))
    (hacc5 : sig5.retVal.headD 0 = acceptWord) :
    CmpAccSSzMini (fun _ => abiWords) (abiFuel - 1) checkerProgMini chalBytes solBytes pins := by
  have hret4Eq : sig4.retVal.headD 0 = sig4.retVal.getD 0 0 := by cases sig4.retVal <;> rfl
  have hret5Eq : sig5.retVal.headD 0 = sig5.retVal.getD 0 0 := by cases sig5.retVal <;> rfl
  exact Or.inl ⟨hchal63, hpins63, sig4.retVal, m4', hMini4,
    Or.inr ⟨hret4Eq ▸ hge4, hsol63, sig5.retVal, m5', hMini5, hret5Eq ▸ hacc5⟩⟩

private theorem cmp_acc_done6 {chalBytes solBytes pins : ByteArray}
    (hchal63 : chalBytes.size < 2 ^ 63) (hpins63 : pins.size < 2 ^ 63) (hsol63 : solBytes.size < 2 ^ 63)
    {sig4 sig5 sig6 : _root_.L.Sig} {m4' m5' m6' : _root_.L.Mem}
    (hMini4 : cmpRunMini (abiFuel - 1) checkerProgMini (cmpPhase4Mem chalBytes pins) = .ok (sig4.retVal, m4'))
    (hge4 : 2 ^ 63 ≤ (sig4.retVal.headD 0).toNat)
    (hMini5 : cmpRunMini (abiFuel - 1) checkerProgMini (cmpPhase5Mem m4' solBytes) = .ok (sig5.retVal, m5'))
    (hge5 : 2 ^ 63 ≤ (sig5.retVal.headD 0).toNat)
    (hMini6 : cmpRunMini (abiFuel - 1) checkerProgMini (cmpPhase6Mem m5') = .ok (sig6.retVal, m6'))
    (hacc6 : sig6.retVal.headD 0 = acceptWord) :
    CmpAccSSzMini (fun _ => abiWords) (abiFuel - 1) checkerProgMini chalBytes solBytes pins := by
  have hret4Eq : sig4.retVal.headD 0 = sig4.retVal.getD 0 0 := by cases sig4.retVal <;> rfl
  have hret5Eq : sig5.retVal.headD 0 = sig5.retVal.getD 0 0 := by cases sig5.retVal <;> rfl
  have hret6Eq : sig6.retVal.headD 0 = sig6.retVal.getD 0 0 := by cases sig6.retVal <;> rfl
  exact Or.inr ⟨sig5.retVal, m5',
    ⟨hchal63, hpins63, hsol63, sig4.retVal, m4', hMini4, hret4Eq ▸ hge4, hMini5, hret5Eq ▸ hge5⟩,
    sig6.retVal, m6', hMini6, Or.inl (hret6Eq ▸ hacc6)⟩

private theorem cmp_acc_done9 {chalBytes solBytes pins : ByteArray}
    (hchal63 : chalBytes.size < 2 ^ 63) (hpins63 : pins.size < 2 ^ 63) (hsol63 : solBytes.size < 2 ^ 63)
    {sig4 sig5 sig6 sig8 sig9 : _root_.L.Sig} {m4' m5' m6' m8N' m9N' : _root_.L.Mem}
    (hMini4 : cmpRunMini (abiFuel - 1) checkerProgMini (cmpPhase4Mem chalBytes pins) = .ok (sig4.retVal, m4'))
    (hge4 : 2 ^ 63 ≤ (sig4.retVal.headD 0).toNat)
    (hMini5 : cmpRunMini (abiFuel - 1) checkerProgMini (cmpPhase5Mem m4' solBytes) = .ok (sig5.retVal, m5'))
    (hge5 : 2 ^ 63 ≤ (sig5.retVal.headD 0).toNat)
    (hMini6 : cmpRunMini (abiFuel - 1) checkerProgMini (cmpPhase6Mem m5') = .ok (sig6.retVal, m6'))
    (hge6 : 2 ^ 63 ≤ (sig6.retVal.headD 0).toNat)
    (hMini8N' : cmpRunMini (abiFuel - 1) checkerProgMini
      (seqMemWMini m6' modeGVar ploGVar phiGVar outArr hdrfArr ctlfArr hdrHw 8 0
        (sig5.retVal.getD 0 0 - 9223372036854775808)) = .ok (sig8.retVal, m8N'))
    (hacc8 : sig8.retVal.headD 0 = acceptWord)
    (hMini9N' : cmpRunMini (abiFuel - 1) checkerProgMini
      (seqNextMini m8N' modeGVar ploGVar phiGVar 9 0
        (sig6.retVal.getD 0 0 - 9223372036854775808)) = .ok (sig9.retVal, m9N'))
    (hacc9 : sig9.retVal.headD 0 = acceptWord) :
    CmpAccSSzMini (fun _ => abiWords) (abiFuel - 1) checkerProgMini chalBytes solBytes pins := by
  have hret4Eq : sig4.retVal.headD 0 = sig4.retVal.getD 0 0 := by cases sig4.retVal <;> rfl
  have hret5Eq : sig5.retVal.headD 0 = sig5.retVal.getD 0 0 := by cases sig5.retVal <;> rfl
  have hret6Eq : sig6.retVal.headD 0 = sig6.retVal.getD 0 0 := by cases sig6.retVal <;> rfl
  have hret8Eq : sig8.retVal.headD 0 = sig8.retVal.getD 0 0 := by cases sig8.retVal <;> rfl
  have hret9Eq : sig9.retVal.headD 0 = sig9.retVal.getD 0 0 := by cases sig9.retVal <;> rfl
  exact Or.inr ⟨sig5.retVal, m5',
    ⟨hchal63, hpins63, hsol63, sig4.retVal, m4', hMini4, hret4Eq ▸ hge4, hMini5, hret5Eq ▸ hge5⟩,
    sig6.retVal, m6', hMini6,
    Or.inr ⟨hret6Eq ▸ hge6,
      sig8.retVal, m8N', hMini8N', hret8Eq ▸ hacc8,
      sig9.retVal, m9N', hMini9N', hret9Eq ▸ hacc9⟩⟩

private theorem linkedCmpRom_accept_cmpAccSSz_and_regs (img : LinkedCmpImage)
    (_hPlat : System.Platform.numBits = 64)
    (initSt : RV64.State) (hpc0 : initSt.pc = img.cmpEntryPc)
    {chalBase solBase pinsBase regionBase : BitVec 64}
    {chalBytes solBytes pins : ByteArray}
    (ha0 : initSt.getReg AbiReg.a0 = chalBase)
    (ha1 : initSt.getReg AbiReg.a1 = BitVec.ofNat 64 chalBytes.size)
    (ha2 : initSt.getReg AbiReg.a2 = pinsBase)
    (ha3 : initSt.getReg AbiReg.a3 = BitVec.ofNat 64 pins.size)
    (ha4 : initSt.getReg AbiReg.a4 = regionBase)
    (ha6 : initSt.getReg AbiReg.a6 = solBase)
    (ha7 : initSt.getReg AbiReg.a7 = BitVec.ofNat 64 solBytes.size)
    (hchal64 : chalBytes.size < 2 ^ 64) (hsol64 : solBytes.size < 2 ^ 64)
    (hpins64 : pins.size < 2 ^ 64)
    (hChal64 : chalBase.toNat + chalBytes.size ≤ 2 ^ 64)
    (hSol64 : solBase.toNat + solBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjChalPins : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjChalSol : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨solBase, solBytes.size⟩)
    (hDisjChalReg : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjSolPins : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjSolReg : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hChalMem : ∀ i, (hi : i < chalBytes.size) → initSt.mem (chalBase + BitVec.ofNat 64 i) = chalBytes[i].toBitVec)
    (hSolMem : ∀ i, (hi : i < solBytes.size) → initSt.mem (solBase + BitVec.ofNat 64 i) = solBytes[i].toBitVec)
    (hPinsMem : ∀ i, (hi : i < pins.size) → initSt.mem (pinsBase + BitVec.ofNat 64 i) = pins[i].toBitVec)
    (hRegZero : ∀ k, k < abiNeed checkerTabMini → initSt.mem (regionBase + BitVec.ofNat 64 k) = 0#8)
    (hStack4 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase4Mem chalBytes pins) ≤ abiStack)
    (hStack5 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase5InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack6 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase6InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack8 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase8InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack9 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase9InitMem chalBytes solBytes pins) ≤ abiStack)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : img.rom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run img.rom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha0Out : finalSt.getReg AbiReg.a0 = acceptWord.toBitVec)
    (ha1Out : finalSt.getReg AbiReg.a1 = 0#64) :
    CmpAccSSzMini (fun _ => abiWords) (abiFuel - 1) checkerProgMini chalBytes solBytes pins ∧
    RegsRestored initSt finalSt ∧ finalSt.getReg AbiReg.ra = initSt.getReg AbiReg.ra := by
  obtain ⟨hchal63, hpins63, hsol63, sig4, m4', b4', hrunB4, hMini4, hm4OutSz, hBr4⟩ :=
    cmp_mode4_step img initSt hpc0 ha0 ha1 ha2 ha3 ha4 ha6 ha7 hchal64 hsol64 hpins64
      hChal64 hSol64 hPins64 hRegAlign hReg64 hDisjChalPins hDisjChalSol hDisjChalReg
      hDisjSolPins hDisjSolReg hDisjPinsReg hChalMem hSolMem hPinsMem hRegZero hStack4
      hRetOut hrun hret ha0Out ha1Out
  rcases hBr4 with ⟨hacc4, hrest4⟩ | ⟨hge4, k50, st50, hrun50, hpc50, hgp50, hs3_50, hs4_50, hsaved50, hMemRel_50, hSolMem_50⟩
  · exact ⟨cmp_acc_done4 hchal63 hpins63 hMini4 hacc4, hrest4⟩
  · have hm5Init := cmp_hm5Init chalBytes solBytes pins hrunB4
    obtain ⟨sig5, m5', b5', hrunB5, hMini5, hm5OutSz, hBr5⟩ :=
      cmp_mode5_step img initSt hsol64 hChal64 hSol64 hPins64 hRegAlign hReg64
        hDisjChalPins hDisjChalReg hDisjSolPins hDisjSolReg hDisjPinsReg
        hStack5 hRetOut hrun hret ha0Out ha1Out hm4OutSz hm5Init hrun50 hpc50 hgp50 hs3_50 hs4_50 hsaved50 hMemRel_50 hSolMem_50
    rcases hBr5 with ⟨hacc5, hrest5⟩ | ⟨hge5, k60, st60, hrun60, hpc60, hgp60, hs5_60, hsaved60, hMemRel_60⟩
    · exact ⟨cmp_acc_done5 hchal63 hpins63 hsol63 hMini4 hge4 hMini5 hacc5, hrest5⟩
    · have hm6Init := cmp_hm6Init chalBytes solBytes pins hm5Init hrunB5
      obtain ⟨sig6, m6', b6', hrunB6, hMini6, hm6OutSz, hBr6⟩ :=
        cmp_mode6_step img initSt hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg
          hStack6 hRetOut hrun hret ha0Out ha1Out hm5OutSz hm6Init hrun60 hpc60 hgp60 hs5_60 hsaved60 hMemRel_60
      rcases hBr6 with ⟨hacc6, hrest6⟩ | ⟨hge6, k80, st80, hrun80, hpc80, hgp80, hs5_80, hs6_80, hsaved80, hMemRel_80⟩
      · exact ⟨cmp_acc_done6 hchal63 hpins63 hsol63 hMini4 hge4 hMini5 hge5 hMini6 hacc6, hrest6⟩
      · have hm8Init := cmp_hm8Init chalBytes solBytes pins hm5Init hrunB5 hm6Init hrunB6
        obtain ⟨sig8, m8', b8', hrunB8, hMini8, hacc8, k90, st90, hrun90, hpc90, hgp90, hs6_90, hsaved90, hMemRel_90⟩ :=
          cmp_mode8_step img initSt hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg
            hStack8 hRetOut hrun hret ha0Out ha1Out hge5 hm6OutSz hm8Init hrun80 hpc80 hgp80 hs5_80 hs6_80 hsaved80 hMemRel_80
        have hm9Init := cmp_hm9Init chalBytes solBytes pins hm6Init hrunB6 hm8Init hrunB8
        obtain ⟨sig9, m9', hMini9, hacc9, hrest9⟩ :=
          cmp_mode9_step img initSt hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg
            hStack9 hRetOut hrun hret ha0Out ha1Out hm9Init hrun90 hpc90 hgp90 hs6_90 hsaved90 hMemRel_90
        obtain ⟨m8N', m9N', hMini8N', hMini9N'⟩ := cmp_mode89_bridge m6' m8' m9' sig5 sig6 sig8 sig9 hMini8 hMini9
        exact ⟨cmp_acc_done9 hchal63 hpins63 hsol63 hMini4 hge4 hMini5 hge5 hMini6 hge6 hMini8N' hacc8 hMini9N' hacc9, hrest9⟩

/-- Any accepting return `(acceptWord, 0)` of a `LinkedCmpImage` `img.rom` from boot state
    `initSt` yields `CmpAccSSzMini (fun _ => abiWords) (abiFuel - 1) checkerProgMini chalBytes solBytes pins`. -/
theorem linkedCmpRom_accept_cmpAccSSz (img : LinkedCmpImage)
    (hPlat : System.Platform.numBits = 64)
    (initSt : RV64.State) (hpc0 : initSt.pc = img.cmpEntryPc)
    {chalBase solBase pinsBase regionBase : BitVec 64}
    {chalBytes solBytes pins : ByteArray}
    (ha0 : initSt.getReg AbiReg.a0 = chalBase)
    (ha1 : initSt.getReg AbiReg.a1 = BitVec.ofNat 64 chalBytes.size)
    (ha2 : initSt.getReg AbiReg.a2 = pinsBase)
    (ha3 : initSt.getReg AbiReg.a3 = BitVec.ofNat 64 pins.size)
    (ha4 : initSt.getReg AbiReg.a4 = regionBase)
    (ha6 : initSt.getReg AbiReg.a6 = solBase)
    (ha7 : initSt.getReg AbiReg.a7 = BitVec.ofNat 64 solBytes.size)
    (hchal64 : chalBytes.size < 2 ^ 64) (hsol64 : solBytes.size < 2 ^ 64)
    (hpins64 : pins.size < 2 ^ 64)
    (hChal64 : chalBase.toNat + chalBytes.size ≤ 2 ^ 64)
    (hSol64 : solBase.toNat + solBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjChalPins : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjChalSol : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨solBase, solBytes.size⟩)
    (hDisjChalReg : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjSolPins : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjSolReg : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hChalMem : ∀ i, (hi : i < chalBytes.size) → initSt.mem (chalBase + BitVec.ofNat 64 i) = chalBytes[i].toBitVec)
    (hSolMem : ∀ i, (hi : i < solBytes.size) → initSt.mem (solBase + BitVec.ofNat 64 i) = solBytes[i].toBitVec)
    (hPinsMem : ∀ i, (hi : i < pins.size) → initSt.mem (pinsBase + BitVec.ofNat 64 i) = pins[i].toBitVec)
    (hRegZero : ∀ k, k < abiNeed checkerTabMini → initSt.mem (regionBase + BitVec.ofNat 64 k) = 0#8)
    (hStack4 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase4Mem chalBytes pins) ≤ abiStack)
    (hStack5 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase5InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack6 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase6InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack8 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase8InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack9 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase9InitMem chalBytes solBytes pins) ≤ abiStack)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : img.rom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run img.rom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha0Out : finalSt.getReg AbiReg.a0 = acceptWord.toBitVec)
    (ha1Out : finalSt.getReg AbiReg.a1 = 0#64) :
    CmpAccSSzMini (fun _ => abiWords) (abiFuel - 1) checkerProgMini chalBytes solBytes pins :=
  (linkedCmpRom_accept_cmpAccSSz_and_regs img hPlat initSt hpc0 ha0 ha1 ha2 ha3 ha4 ha6 ha7 hchal64 hsol64 hpins64
    hChal64 hSol64 hPins64 hRegAlign hReg64 hDisjChalPins hDisjChalSol hDisjChalReg hDisjSolPins
    hDisjSolReg hDisjPinsReg hChalMem hSolMem hPinsMem hRegZero hStack4 hStack5 hStack6 hStack8 hStack9
    hRetOut hrun hret ha0Out ha1Out).1

/-- LP64 callee-saved register and `ra` restoration theorem for any `LinkedCmpImage`. -/
theorem linkedCmpRom_accept_regsRestored (img : LinkedCmpImage)
    (hPlat : System.Platform.numBits = 64)
    (initSt : RV64.State) (hpc0 : initSt.pc = img.cmpEntryPc)
    {chalBase solBase pinsBase regionBase : BitVec 64}
    {chalBytes solBytes pins : ByteArray}
    (ha0 : initSt.getReg AbiReg.a0 = chalBase)
    (ha1 : initSt.getReg AbiReg.a1 = BitVec.ofNat 64 chalBytes.size)
    (ha2 : initSt.getReg AbiReg.a2 = pinsBase)
    (ha3 : initSt.getReg AbiReg.a3 = BitVec.ofNat 64 pins.size)
    (ha4 : initSt.getReg AbiReg.a4 = regionBase)
    (ha6 : initSt.getReg AbiReg.a6 = solBase)
    (ha7 : initSt.getReg AbiReg.a7 = BitVec.ofNat 64 solBytes.size)
    (hchal64 : chalBytes.size < 2 ^ 64) (hsol64 : solBytes.size < 2 ^ 64)
    (hpins64 : pins.size < 2 ^ 64)
    (hChal64 : chalBase.toNat + chalBytes.size ≤ 2 ^ 64)
    (hSol64 : solBase.toNat + solBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjChalPins : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjChalSol : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨solBase, solBytes.size⟩)
    (hDisjChalReg : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjSolPins : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjSolReg : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hChalMem : ∀ i, (hi : i < chalBytes.size) → initSt.mem (chalBase + BitVec.ofNat 64 i) = chalBytes[i].toBitVec)
    (hSolMem : ∀ i, (hi : i < solBytes.size) → initSt.mem (solBase + BitVec.ofNat 64 i) = solBytes[i].toBitVec)
    (hPinsMem : ∀ i, (hi : i < pins.size) → initSt.mem (pinsBase + BitVec.ofNat 64 i) = pins[i].toBitVec)
    (hRegZero : ∀ k, k < abiNeed checkerTabMini → initSt.mem (regionBase + BitVec.ofNat 64 k) = 0#8)
    (hStack4 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase4Mem chalBytes pins) ≤ abiStack)
    (hStack5 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase5InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack6 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase6InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack8 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase8InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack9 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase9InitMem chalBytes solBytes pins) ≤ abiStack)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : img.rom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run img.rom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha0Out : finalSt.getReg AbiReg.a0 = acceptWord.toBitVec)
    (ha1Out : finalSt.getReg AbiReg.a1 = 0#64) :
    RegsRestored initSt finalSt ∧ finalSt.getReg AbiReg.ra = initSt.getReg AbiReg.ra :=
  (linkedCmpRom_accept_cmpAccSSz_and_regs img hPlat initSt hpc0 ha0 ha1 ha2 ha3 ha4 ha6 ha7 hchal64 hsol64 hpins64
    hChal64 hSol64 hPins64 hRegAlign hReg64 hDisjChalPins hDisjChalSol hDisjChalReg hDisjSolPins
    hDisjSolReg hDisjPinsReg hChalMem hSolMem hPinsMem hRegZero hStack4 hStack5 hStack6 hStack8 hStack9
    hRetOut hrun hret ha0Out ha1Out).2

/-- End-to-end backward soundness: an accepting RV64 execution of any `LinkedCmpImage`
    `img.rom` implies `ConAgua.Final.TwinComparesAccepts chalBytes solBytes`. -/
theorem linkedCmpRom_accept_twinComparesAccepts (img : LinkedCmpImage)
    (hPlat : System.Platform.numBits = 64)
    (initSt : RV64.State) (hpc0 : initSt.pc = img.cmpEntryPc)
    {chalBase solBase pinsBase regionBase : BitVec 64}
    {chalBytes solBytes pins : ByteArray}
    (ha0 : initSt.getReg AbiReg.a0 = chalBase)
    (ha1 : initSt.getReg AbiReg.a1 = BitVec.ofNat 64 chalBytes.size)
    (ha2 : initSt.getReg AbiReg.a2 = pinsBase)
    (ha3 : initSt.getReg AbiReg.a3 = BitVec.ofNat 64 pins.size)
    (ha4 : initSt.getReg AbiReg.a4 = regionBase)
    (ha6 : initSt.getReg AbiReg.a6 = solBase)
    (ha7 : initSt.getReg AbiReg.a7 = BitVec.ofNat 64 solBytes.size)
    (hchal64 : chalBytes.size < 2 ^ 64) (hsol64 : solBytes.size < 2 ^ 64)
    (hpins64 : pins.size < 2 ^ 64)
    (hChal64 : chalBase.toNat + chalBytes.size ≤ 2 ^ 64)
    (hSol64 : solBase.toNat + solBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjChalPins : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjChalSol : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨solBase, solBytes.size⟩)
    (hDisjChalReg : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjSolPins : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjSolReg : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hChalMem : ∀ i, (hi : i < chalBytes.size) → initSt.mem (chalBase + BitVec.ofNat 64 i) = chalBytes[i].toBitVec)
    (hSolMem : ∀ i, (hi : i < solBytes.size) → initSt.mem (solBase + BitVec.ofNat 64 i) = solBytes[i].toBitVec)
    (hPinsMem : ∀ i, (hi : i < pins.size) → initSt.mem (pinsBase + BitVec.ofNat 64 i) = pins[i].toBitVec)
    (hRegZero : ∀ k, k < abiNeed checkerTabMini → initSt.mem (regionBase + BitVec.ofNat 64 k) = 0#8)
    (hStack4 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase4Mem chalBytes pins) ≤ abiStack)
    (hStack5 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase5InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack6 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase6InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack8 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase8InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack9 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase9InitMem chalBytes solBytes pins) ≤ abiStack)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : img.rom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run img.rom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha0Out : finalSt.getReg AbiReg.a0 = acceptWord.toBitVec)
    (ha1Out : finalSt.getReg AbiReg.a1 = 0#64) :
    ConAgua.Final.TwinComparesAccepts chalBytes solBytes :=
  checkerProgMini_cmpSeq_twinAccepts (fun _ => abiWords) (fun _ => by simp [abiWords])
    (fun _ _ => ⟨rfl, rfl⟩) chalBytes solBytes pins hPlat (Nat.sub_le abiFuel 1)
    (linkedCmpRom_accept_cmpAccSSz img hPlat initSt hpc0 ha0 ha1 ha2 ha3 ha4 ha6 ha7 hchal64 hsol64 hpins64
      hChal64 hSol64 hPins64 hRegAlign hReg64 hDisjChalPins hDisjChalSol hDisjChalReg hDisjSolPins
      hDisjSolReg hDisjPinsReg hChalMem hSolMem hPinsMem hRegZero hStack4 hStack5 hStack6 hStack8 hStack9
      hRetOut hrun hret ha0Out ha1Out)

/-- End-to-end semantic soundness (`ChallengeHasModel`): an accepting RV64 execution of
    `img.rom` implies the challenge stream parses cleanly and has a `ConLeche.Model V`
    over any ZF/CZF universe `V`. -/
theorem linkedCmpRom_accept_model.{w_u} (V : Type w_u) [ConLeche.SetTheory V]
    (img : LinkedCmpImage)
    (hPlat : System.Platform.numBits = 64)
    (initSt : RV64.State) (hpc0 : initSt.pc = img.cmpEntryPc)
    {chalBase solBase pinsBase regionBase : BitVec 64}
    {chalBytes solBytes pins : ByteArray}
    (ha0 : initSt.getReg AbiReg.a0 = chalBase)
    (ha1 : initSt.getReg AbiReg.a1 = BitVec.ofNat 64 chalBytes.size)
    (ha2 : initSt.getReg AbiReg.a2 = pinsBase)
    (ha3 : initSt.getReg AbiReg.a3 = BitVec.ofNat 64 pins.size)
    (ha4 : initSt.getReg AbiReg.a4 = regionBase)
    (ha6 : initSt.getReg AbiReg.a6 = solBase)
    (ha7 : initSt.getReg AbiReg.a7 = BitVec.ofNat 64 solBytes.size)
    (hchal64 : chalBytes.size < 2 ^ 64) (hsol64 : solBytes.size < 2 ^ 64)
    (hpins64 : pins.size < 2 ^ 64)
    (hChal64 : chalBase.toNat + chalBytes.size ≤ 2 ^ 64)
    (hSol64 : solBase.toNat + solBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjChalPins : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjChalSol : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨solBase, solBytes.size⟩)
    (hDisjChalReg : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjSolPins : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjSolReg : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hChalMem : ∀ i, (hi : i < chalBytes.size) → initSt.mem (chalBase + BitVec.ofNat 64 i) = chalBytes[i].toBitVec)
    (hSolMem : ∀ i, (hi : i < solBytes.size) → initSt.mem (solBase + BitVec.ofNat 64 i) = solBytes[i].toBitVec)
    (hPinsMem : ∀ i, (hi : i < pins.size) → initSt.mem (pinsBase + BitVec.ofNat 64 i) = pins[i].toBitVec)
    (hRegZero : ∀ k, k < abiNeed checkerTabMini → initSt.mem (regionBase + BitVec.ofNat 64 k) = 0#8)
    (hStack4 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase4Mem chalBytes pins) ≤ abiStack)
    (hStack5 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase5InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack6 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase6InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack8 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase8InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack9 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase9InitMem chalBytes solBytes pins) ≤ abiStack)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : img.rom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run img.rom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha0Out : finalSt.getReg AbiReg.a0 = acceptWord.toBitVec)
    (ha1Out : finalSt.getReg AbiReg.a1 = 0#64) :
    ∃ (rcC : ConLeche.Frontend.ParseResultD) (preC : ConLeche.Frontend.PreludeIx),
      ConLeche.Frontend.parseChunks [chalBytes] = .ok rcC ∧
      Nonempty (ConLeche.Model V (ConLeche.streamEnv
        ((ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map ConLeche.Cached.sideRecord))) :=
  checkerProgMini_cmpSeq_model V (fun _ => abiWords) (fun _ => by simp [abiWords])
    (fun _ _ => ⟨rfl, rfl⟩) chalBytes solBytes pins hPlat (Nat.sub_le abiFuel 1)
    (linkedCmpRom_accept_cmpAccSSz img hPlat initSt hpc0 ha0 ha1 ha2 ha3 ha4 ha6 ha7 hchal64 hsol64 hpins64
      hChal64 hSol64 hPins64 hRegAlign hReg64 hDisjChalPins hDisjChalSol hDisjChalReg hDisjSolPins
      hDisjSolReg hDisjPinsReg hChalMem hSolMem hPinsMem hRegZero hStack4 hStack5 hStack6 hStack8 hStack9
      hRetOut hrun hret ha0Out ha1Out)

/-- End-to-end soundness (`NoFalse`): `img.rom` never accepts an input challenge
    declaring a theorem of type `False`. -/
theorem linkedCmpRom_accept_no_False.{w_u} (V : Type w_u) [ConLeche.SetTheory V]
    (img : LinkedCmpImage)
    (hPlat : System.Platform.numBits = 64)
    (initSt : RV64.State) (hpc0 : initSt.pc = img.cmpEntryPc)
    {chalBase solBase pinsBase regionBase : BitVec 64}
    {chalBytes solBytes pins : ByteArray}
    (hfalse : ConLeche.jsonWithTheoremFalse [chalBytes])
    (ha0 : initSt.getReg AbiReg.a0 = chalBase)
    (ha1 : initSt.getReg AbiReg.a1 = BitVec.ofNat 64 chalBytes.size)
    (ha2 : initSt.getReg AbiReg.a2 = pinsBase)
    (ha3 : initSt.getReg AbiReg.a3 = BitVec.ofNat 64 pins.size)
    (ha4 : initSt.getReg AbiReg.a4 = regionBase)
    (ha6 : initSt.getReg AbiReg.a6 = solBase)
    (ha7 : initSt.getReg AbiReg.a7 = BitVec.ofNat 64 solBytes.size)
    (hchal64 : chalBytes.size < 2 ^ 64) (hsol64 : solBytes.size < 2 ^ 64)
    (hpins64 : pins.size < 2 ^ 64)
    (hChal64 : chalBase.toNat + chalBytes.size ≤ 2 ^ 64)
    (hSol64 : solBase.toNat + solBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjChalPins : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjChalSol : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨solBase, solBytes.size⟩)
    (hDisjChalReg : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjSolPins : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjSolReg : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hChalMem : ∀ i, (hi : i < chalBytes.size) → initSt.mem (chalBase + BitVec.ofNat 64 i) = chalBytes[i].toBitVec)
    (hSolMem : ∀ i, (hi : i < solBytes.size) → initSt.mem (solBase + BitVec.ofNat 64 i) = solBytes[i].toBitVec)
    (hPinsMem : ∀ i, (hi : i < pins.size) → initSt.mem (pinsBase + BitVec.ofNat 64 i) = pins[i].toBitVec)
    (hRegZero : ∀ k, k < abiNeed checkerTabMini → initSt.mem (regionBase + BitVec.ofNat 64 k) = 0#8)
    (hStack4 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase4Mem chalBytes pins) ≤ abiStack)
    (hStack5 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase5InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack6 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase6InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack8 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase8InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack9 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase9InitMem chalBytes solBytes pins) ≤ abiStack)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : img.rom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run img.rom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha0Out : finalSt.getReg AbiReg.a0 = acceptWord.toBitVec)
    (ha1Out : finalSt.getReg AbiReg.a1 = 0#64) :
    False :=
  checkerProgMini_cmpSeq_no_False V (fun _ => abiWords) (fun _ => by simp [abiWords])
    (fun _ _ => ⟨rfl, rfl⟩) chalBytes solBytes pins hPlat hfalse (Nat.sub_le abiFuel 1)
    (linkedCmpRom_accept_cmpAccSSz img hPlat initSt hpc0 ha0 ha1 ha2 ha3 ha4 ha6 ha7 hchal64 hsol64 hpins64
      hChal64 hSol64 hPins64 hRegAlign hReg64 hDisjChalPins hDisjChalSol hDisjChalReg hDisjSolPins
      hDisjSolReg hDisjPinsReg hChalMem hSolMem hPinsMem hRegZero hStack4 hStack5 hStack6 hStack8 hStack9
      hRetOut hrun hret ha0Out ha1Out)

private theorem defaultCheckerCmpImage_cmpEntryPc :
    defaultCheckerCmpImage.cmpEntryPc = checkerCmpEntryPc := by
  dsimp only [defaultCheckerCmpImage, LinkedCmpImage.cmpEntryPc, LinkedCmpImage.cmpEntryWord,
    checkerCmpEntryPc, checkerCmpEntryWord]

private theorem defaultCheckerCmpImage_rom :
    defaultCheckerCmpImage.rom = checkerRom := by
  dsimp only [defaultCheckerCmpImage, LinkedCmpImage.rom, checkerRom]

/-- Any accepting return `(acceptWord, 0)` of `checkerRom` from boot state `initSt` yields
    `CmpAccSSzMini (fun _ => abiWords) (abiFuel - 1) checkerProgMini chalBytes solBytes pins`. -/
theorem checkerCmpRom_accept_cmpAccSSz
    (hPlat : System.Platform.numBits = 64)
    (initSt : RV64.State) (hpc0 : initSt.pc = checkerCmpEntryPc)
    {chalBase solBase pinsBase regionBase : BitVec 64}
    {chalBytes solBytes pins : ByteArray}
    (ha0 : initSt.getReg AbiReg.a0 = chalBase)
    (ha1 : initSt.getReg AbiReg.a1 = BitVec.ofNat 64 chalBytes.size)
    (ha2 : initSt.getReg AbiReg.a2 = pinsBase)
    (ha3 : initSt.getReg AbiReg.a3 = BitVec.ofNat 64 pins.size)
    (ha4 : initSt.getReg AbiReg.a4 = regionBase)
    (ha6 : initSt.getReg AbiReg.a6 = solBase)
    (ha7 : initSt.getReg AbiReg.a7 = BitVec.ofNat 64 solBytes.size)
    (hchal64 : chalBytes.size < 2 ^ 64) (hsol64 : solBytes.size < 2 ^ 64)
    (hpins64 : pins.size < 2 ^ 64)
    (hChal64 : chalBase.toNat + chalBytes.size ≤ 2 ^ 64)
    (hSol64 : solBase.toNat + solBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjChalPins : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjChalSol : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨solBase, solBytes.size⟩)
    (hDisjChalReg : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjSolPins : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjSolReg : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hChalMem : ∀ i, (hi : i < chalBytes.size) → initSt.mem (chalBase + BitVec.ofNat 64 i) = chalBytes[i].toBitVec)
    (hSolMem : ∀ i, (hi : i < solBytes.size) → initSt.mem (solBase + BitVec.ofNat 64 i) = solBytes[i].toBitVec)
    (hPinsMem : ∀ i, (hi : i < pins.size) → initSt.mem (pinsBase + BitVec.ofNat 64 i) = pins[i].toBitVec)
    (hRegZero : ∀ k, k < abiNeed checkerTabMini → initSt.mem (regionBase + BitVec.ofNat 64 k) = 0#8)
    (hStack4 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase4Mem chalBytes pins) ≤ abiStack)
    (hStack5 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase5InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack6 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase6InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack8 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase8InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack9 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase9InitMem chalBytes solBytes pins) ≤ abiStack)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : checkerRom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run checkerRom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha0Out : finalSt.getReg AbiReg.a0 = acceptWord.toBitVec)
    (ha1Out : finalSt.getReg AbiReg.a1 = 0#64) :
    CmpAccSSzMini (fun _ => abiWords) (abiFuel - 1) checkerProgMini chalBytes solBytes pins := by
  rw [← defaultCheckerCmpImage_cmpEntryPc] at hpc0
  rw [← defaultCheckerCmpImage_rom] at hRetOut hrun
  exact linkedCmpRom_accept_cmpAccSSz defaultCheckerCmpImage hPlat initSt hpc0 ha0 ha1 ha2 ha3 ha4 ha6 ha7
    hchal64 hsol64 hpins64 hChal64 hSol64 hPins64 hRegAlign hReg64 hDisjChalPins hDisjChalSol
    hDisjChalReg hDisjSolPins hDisjSolReg hDisjPinsReg hChalMem hSolMem hPinsMem hRegZero
    hStack4 hStack5 hStack6 hStack8 hStack9 hRetOut hrun hret ha0Out ha1Out

/-- LP64 callee-saved register and `ra` restoration theorem for `checkerRom`. -/
theorem checkerCmpRom_accept_regsRestored
    (hPlat : System.Platform.numBits = 64)
    (initSt : RV64.State) (hpc0 : initSt.pc = checkerCmpEntryPc)
    {chalBase solBase pinsBase regionBase : BitVec 64}
    {chalBytes solBytes pins : ByteArray}
    (ha0 : initSt.getReg AbiReg.a0 = chalBase)
    (ha1 : initSt.getReg AbiReg.a1 = BitVec.ofNat 64 chalBytes.size)
    (ha2 : initSt.getReg AbiReg.a2 = pinsBase)
    (ha3 : initSt.getReg AbiReg.a3 = BitVec.ofNat 64 pins.size)
    (ha4 : initSt.getReg AbiReg.a4 = regionBase)
    (ha6 : initSt.getReg AbiReg.a6 = solBase)
    (ha7 : initSt.getReg AbiReg.a7 = BitVec.ofNat 64 solBytes.size)
    (hchal64 : chalBytes.size < 2 ^ 64) (hsol64 : solBytes.size < 2 ^ 64)
    (hpins64 : pins.size < 2 ^ 64)
    (hChal64 : chalBase.toNat + chalBytes.size ≤ 2 ^ 64)
    (hSol64 : solBase.toNat + solBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjChalPins : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjChalSol : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨solBase, solBytes.size⟩)
    (hDisjChalReg : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjSolPins : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjSolReg : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hChalMem : ∀ i, (hi : i < chalBytes.size) → initSt.mem (chalBase + BitVec.ofNat 64 i) = chalBytes[i].toBitVec)
    (hSolMem : ∀ i, (hi : i < solBytes.size) → initSt.mem (solBase + BitVec.ofNat 64 i) = solBytes[i].toBitVec)
    (hPinsMem : ∀ i, (hi : i < pins.size) → initSt.mem (pinsBase + BitVec.ofNat 64 i) = pins[i].toBitVec)
    (hRegZero : ∀ k, k < abiNeed checkerTabMini → initSt.mem (regionBase + BitVec.ofNat 64 k) = 0#8)
    (hStack4 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase4Mem chalBytes pins) ≤ abiStack)
    (hStack5 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase5InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack6 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase6InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack8 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase8InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack9 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase9InitMem chalBytes solBytes pins) ≤ abiStack)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : checkerRom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run checkerRom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha0Out : finalSt.getReg AbiReg.a0 = acceptWord.toBitVec)
    (ha1Out : finalSt.getReg AbiReg.a1 = 0#64) :
    RegsRestored initSt finalSt ∧ finalSt.getReg AbiReg.ra = initSt.getReg AbiReg.ra := by
  rw [← defaultCheckerCmpImage_cmpEntryPc] at hpc0
  rw [← defaultCheckerCmpImage_rom] at hRetOut hrun
  exact linkedCmpRom_accept_regsRestored defaultCheckerCmpImage hPlat initSt hpc0 ha0 ha1 ha2 ha3 ha4 ha6 ha7
    hchal64 hsol64 hpins64 hChal64 hSol64 hPins64 hRegAlign hReg64 hDisjChalPins hDisjChalSol
    hDisjChalReg hDisjSolPins hDisjSolReg hDisjPinsReg hChalMem hSolMem hPinsMem hRegZero
    hStack4 hStack5 hStack6 hStack8 hStack9 hRetOut hrun hret ha0Out ha1Out

/-- End-to-end backward soundness: an accepting RV64 execution of the comparator
    firmware `checkerRom` implies `ConAgua.Final.TwinComparesAccepts chalBytes solBytes`. -/
theorem checkerCmpRom_accept_twinComparesAccepts
    (hPlat : System.Platform.numBits = 64)
    (initSt : RV64.State) (hpc0 : initSt.pc = checkerCmpEntryPc)
    {chalBase solBase pinsBase regionBase : BitVec 64}
    {chalBytes solBytes pins : ByteArray}
    (ha0 : initSt.getReg AbiReg.a0 = chalBase)
    (ha1 : initSt.getReg AbiReg.a1 = BitVec.ofNat 64 chalBytes.size)
    (ha2 : initSt.getReg AbiReg.a2 = pinsBase)
    (ha3 : initSt.getReg AbiReg.a3 = BitVec.ofNat 64 pins.size)
    (ha4 : initSt.getReg AbiReg.a4 = regionBase)
    (ha6 : initSt.getReg AbiReg.a6 = solBase)
    (ha7 : initSt.getReg AbiReg.a7 = BitVec.ofNat 64 solBytes.size)
    (hchal64 : chalBytes.size < 2 ^ 64) (hsol64 : solBytes.size < 2 ^ 64)
    (hpins64 : pins.size < 2 ^ 64)
    (hChal64 : chalBase.toNat + chalBytes.size ≤ 2 ^ 64)
    (hSol64 : solBase.toNat + solBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjChalPins : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjChalSol : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨solBase, solBytes.size⟩)
    (hDisjChalReg : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjSolPins : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjSolReg : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hChalMem : ∀ i, (hi : i < chalBytes.size) → initSt.mem (chalBase + BitVec.ofNat 64 i) = chalBytes[i].toBitVec)
    (hSolMem : ∀ i, (hi : i < solBytes.size) → initSt.mem (solBase + BitVec.ofNat 64 i) = solBytes[i].toBitVec)
    (hPinsMem : ∀ i, (hi : i < pins.size) → initSt.mem (pinsBase + BitVec.ofNat 64 i) = pins[i].toBitVec)
    (hRegZero : ∀ k, k < abiNeed checkerTabMini → initSt.mem (regionBase + BitVec.ofNat 64 k) = 0#8)
    (hStack4 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase4Mem chalBytes pins) ≤ abiStack)
    (hStack5 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase5InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack6 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase6InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack8 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase8InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack9 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase9InitMem chalBytes solBytes pins) ≤ abiStack)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : checkerRom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run checkerRom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha0Out : finalSt.getReg AbiReg.a0 = acceptWord.toBitVec)
    (ha1Out : finalSt.getReg AbiReg.a1 = 0#64) :
    ConAgua.Final.TwinComparesAccepts chalBytes solBytes :=
  checkerProgMini_cmpSeq_twinAccepts (fun _ => abiWords) (fun _ => by simp [abiWords])
    (fun _ _ => ⟨rfl, rfl⟩) chalBytes solBytes pins hPlat (Nat.sub_le abiFuel 1)
    (checkerCmpRom_accept_cmpAccSSz hPlat initSt hpc0 ha0 ha1 ha2 ha3 ha4 ha6 ha7 hchal64 hsol64 hpins64
      hChal64 hSol64 hPins64 hRegAlign hReg64 hDisjChalPins hDisjChalSol hDisjChalReg hDisjSolPins
      hDisjSolReg hDisjPinsReg hChalMem hSolMem hPinsMem hRegZero hStack4 hStack5 hStack6 hStack8 hStack9
      hRetOut hrun hret ha0Out ha1Out)

/-- End-to-end semantic soundness (`ChallengeHasModel`): an accepting RV64 execution of
    `checkerRom` implies the challenge stream parses cleanly and has a `ConLeche.Model V`
    over any ZF/CZF universe `V`. -/
theorem checkerCmpRom_accept_model.{w_u} (V : Type w_u) [ConLeche.SetTheory V]
    (hPlat : System.Platform.numBits = 64)
    (initSt : RV64.State) (hpc0 : initSt.pc = checkerCmpEntryPc)
    {chalBase solBase pinsBase regionBase : BitVec 64}
    {chalBytes solBytes pins : ByteArray}
    (ha0 : initSt.getReg AbiReg.a0 = chalBase)
    (ha1 : initSt.getReg AbiReg.a1 = BitVec.ofNat 64 chalBytes.size)
    (ha2 : initSt.getReg AbiReg.a2 = pinsBase)
    (ha3 : initSt.getReg AbiReg.a3 = BitVec.ofNat 64 pins.size)
    (ha4 : initSt.getReg AbiReg.a4 = regionBase)
    (ha6 : initSt.getReg AbiReg.a6 = solBase)
    (ha7 : initSt.getReg AbiReg.a7 = BitVec.ofNat 64 solBytes.size)
    (hchal64 : chalBytes.size < 2 ^ 64) (hsol64 : solBytes.size < 2 ^ 64)
    (hpins64 : pins.size < 2 ^ 64)
    (hChal64 : chalBase.toNat + chalBytes.size ≤ 2 ^ 64)
    (hSol64 : solBase.toNat + solBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjChalPins : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjChalSol : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨solBase, solBytes.size⟩)
    (hDisjChalReg : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjSolPins : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjSolReg : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hChalMem : ∀ i, (hi : i < chalBytes.size) → initSt.mem (chalBase + BitVec.ofNat 64 i) = chalBytes[i].toBitVec)
    (hSolMem : ∀ i, (hi : i < solBytes.size) → initSt.mem (solBase + BitVec.ofNat 64 i) = solBytes[i].toBitVec)
    (hPinsMem : ∀ i, (hi : i < pins.size) → initSt.mem (pinsBase + BitVec.ofNat 64 i) = pins[i].toBitVec)
    (hRegZero : ∀ k, k < abiNeed checkerTabMini → initSt.mem (regionBase + BitVec.ofNat 64 k) = 0#8)
    (hStack4 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase4Mem chalBytes pins) ≤ abiStack)
    (hStack5 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase5InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack6 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase6InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack8 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase8InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack9 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase9InitMem chalBytes solBytes pins) ≤ abiStack)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : checkerRom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run checkerRom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha0Out : finalSt.getReg AbiReg.a0 = acceptWord.toBitVec)
    (ha1Out : finalSt.getReg AbiReg.a1 = 0#64) :
    ∃ (rcC : ConLeche.Frontend.ParseResultD) (preC : ConLeche.Frontend.PreludeIx),
      ConLeche.Frontend.parseChunks [chalBytes] = .ok rcC ∧
      Nonempty (ConLeche.Model V (ConLeche.streamEnv
        ((ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map ConLeche.Cached.sideRecord))) :=
  checkerProgMini_cmpSeq_model V (fun _ => abiWords) (fun _ => by simp [abiWords])
    (fun _ _ => ⟨rfl, rfl⟩) chalBytes solBytes pins hPlat (Nat.sub_le abiFuel 1)
    (checkerCmpRom_accept_cmpAccSSz hPlat initSt hpc0 ha0 ha1 ha2 ha3 ha4 ha6 ha7 hchal64 hsol64 hpins64
      hChal64 hSol64 hPins64 hRegAlign hReg64 hDisjChalPins hDisjChalSol hDisjChalReg hDisjSolPins
      hDisjSolReg hDisjPinsReg hChalMem hSolMem hPinsMem hRegZero hStack4 hStack5 hStack6 hStack8 hStack9
      hRetOut hrun hret ha0Out ha1Out)

/-- End-to-end soundness (`NoFalse`): `checkerRom` never accepts an input challenge
    declaring a theorem of type `False`. -/
theorem checkerCmpRom_accept_no_False.{w_u} (V : Type w_u) [ConLeche.SetTheory V]
    (hPlat : System.Platform.numBits = 64)
    (initSt : RV64.State) (hpc0 : initSt.pc = checkerCmpEntryPc)
    {chalBase solBase pinsBase regionBase : BitVec 64}
    {chalBytes solBytes pins : ByteArray}
    (hfalse : ConLeche.jsonWithTheoremFalse [chalBytes])
    (ha0 : initSt.getReg AbiReg.a0 = chalBase)
    (ha1 : initSt.getReg AbiReg.a1 = BitVec.ofNat 64 chalBytes.size)
    (ha2 : initSt.getReg AbiReg.a2 = pinsBase)
    (ha3 : initSt.getReg AbiReg.a3 = BitVec.ofNat 64 pins.size)
    (ha4 : initSt.getReg AbiReg.a4 = regionBase)
    (ha6 : initSt.getReg AbiReg.a6 = solBase)
    (ha7 : initSt.getReg AbiReg.a7 = BitVec.ofNat 64 solBytes.size)
    (hchal64 : chalBytes.size < 2 ^ 64) (hsol64 : solBytes.size < 2 ^ 64)
    (hpins64 : pins.size < 2 ^ 64)
    (hChal64 : chalBase.toNat + chalBytes.size ≤ 2 ^ 64)
    (hSol64 : solBase.toNat + solBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjChalPins : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjChalSol : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨solBase, solBytes.size⟩)
    (hDisjChalReg : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjSolPins : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjSolReg : MemSpan.disjoint ⟨solBase, solBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hChalMem : ∀ i, (hi : i < chalBytes.size) → initSt.mem (chalBase + BitVec.ofNat 64 i) = chalBytes[i].toBitVec)
    (hSolMem : ∀ i, (hi : i < solBytes.size) → initSt.mem (solBase + BitVec.ofNat 64 i) = solBytes[i].toBitVec)
    (hPinsMem : ∀ i, (hi : i < pins.size) → initSt.mem (pinsBase + BitVec.ofNat 64 i) = pins[i].toBitVec)
    (hRegZero : ∀ k, k < abiNeed checkerTabMini → initSt.mem (regionBase + BitVec.ofNat 64 k) = 0#8)
    (hStack4 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase4Mem chalBytes pins) ≤ abiStack)
    (hStack5 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase5InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack6 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase6InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack8 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase8InitMem chalBytes solBytes pins) ≤ abiStack)
    (hStack9 : runStackNeedB checkerProgMini (abiFuel - 1) "check" [] (cmpPhase9InitMem chalBytes solBytes pins) ≤ abiStack)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : checkerRom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run checkerRom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha0Out : finalSt.getReg AbiReg.a0 = acceptWord.toBitVec)
    (ha1Out : finalSt.getReg AbiReg.a1 = 0#64) :
    False :=
  checkerProgMini_cmpSeq_no_False V (fun _ => abiWords) (fun _ => by simp [abiWords])
    (fun _ _ => ⟨rfl, rfl⟩) chalBytes solBytes pins hPlat hfalse (Nat.sub_le abiFuel 1)
    (checkerCmpRom_accept_cmpAccSSz hPlat initSt hpc0 ha0 ha1 ha2 ha3 ha4 ha6 ha7 hchal64 hsol64 hpins64
      hChal64 hSol64 hPins64 hRegAlign hReg64 hDisjChalPins hDisjChalSol hDisjChalReg hDisjSolPins
      hDisjSolReg hDisjPinsReg hChalMem hSolMem hPinsMem hRegZero hStack4 hStack5 hStack6 hStack8 hStack9
      hRetOut hrun hret ha0Out ha1Out)

/-- info: 'ConAgua.RISCV.Bridge.linkedCmpRom_accept_cmpAccSSz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms linkedCmpRom_accept_cmpAccSSz

/-- info: 'ConAgua.RISCV.Bridge.linkedCmpRom_accept_twinComparesAccepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms linkedCmpRom_accept_twinComparesAccepts

/-- info: 'ConAgua.RISCV.Bridge.linkedCmpRom_accept_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms linkedCmpRom_accept_model

/-- info: 'ConAgua.RISCV.Bridge.linkedCmpRom_accept_no_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms linkedCmpRom_accept_no_False

/-- info: 'ConAgua.RISCV.Bridge.linkedCmpRom_accept_regsRestored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms linkedCmpRom_accept_regsRestored

/-- info: 'ConAgua.RISCV.Bridge.checkerCmpRom_accept_cmpAccSSz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerCmpRom_accept_cmpAccSSz

/-- info: 'ConAgua.RISCV.Bridge.checkerCmpRom_accept_twinComparesAccepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms checkerCmpRom_accept_twinComparesAccepts

/-- info: 'ConAgua.RISCV.Bridge.checkerCmpRom_accept_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerCmpRom_accept_model

/-- info: 'ConAgua.RISCV.Bridge.checkerCmpRom_accept_no_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerCmpRom_accept_no_False

/-- info: 'ConAgua.RISCV.Bridge.checkerCmpRom_accept_regsRestored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerCmpRom_accept_regsRestored


end ConAgua.RISCV.Bridge
