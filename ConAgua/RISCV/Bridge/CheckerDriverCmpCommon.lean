import ConAgua.RISCV.Bridge.CheckerDriverSetup

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Comparator Driver Setup and Mode Simulation Helpers (`ConAgua.RISCV.Bridge.CheckerDriverCmpSetup`)

Label lemmas, mode 5/6/8/9 setup simulation, memory-relation transport, mode 8/9 agreement,
and assembly slice definitions for `checkerRom`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard Lean axioms only.
-/

namespace ConAgua.RISCV.Bridge

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Compiler
open ConAgua.RISCV.Linker

/-! ## 5. End-to-End Linked Comparator ROM Backward Soundness Theorems -/

theorem checkerCmp_exhausted_lbl (img : LinkedCmpImage) :
    lookupLabel (linkedCmpEnv img).labels exhaustedLabel =
      some (linkedCmpEnv img).exhaustedTarget :=
  (linkedCmpEnv img).hexhaustedLbl

theorem checkerCmp_drvDone_lbl (img : LinkedCmpImage) :
    lookupLabel (linkedCmpEnv img).labels drvDoneLabel =
      some (img.lkm.totalSize (drvPreDone checkerTabMini)) := by
  have h := linkedCmpChipAsm_linkSpec_decomp img
  have hsp : drvDoneStub = [Asm.lbl drvDoneLabel] ++
      [Asm.addi AbiReg.a1 AbiReg.zero 0#12, Asm.j retRestoreLabel] := rfl
  have hlinkD : img.lkm.linkSpec (drvPreDone checkerTabMini ++ [Asm.lbl drvDoneLabel] ++
      ([Asm.addi AbiReg.a1 AbiReg.zero 0#12, Asm.j retRestoreLabel] ++
       drvExhaustedStub ++ drvErrPrefix ++ drvAbortPrefix ++
       drvRetRestoreStub checkerTabMini ++ drvInitSubAsm checkerTabMini ++
       checkerCmpDriverAsm checkerTabMini ++ linkedCmpFnsAsm img)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    rw [hsp] at h
    simpa only [List.append_assoc] using h
  exact linkResolved_lbl_lm img.lkm _ drvDoneLabel _ hlinkD

theorem cmpDrvSetMode_sim (img : LinkedCmpImage) (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (_hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (m : Nat) (pre post : List AsmItem)
    (hlink : img.lkm.linkSpec (pre ++ cmpDrvSetMode m checkerTabMini ++ post) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase) :
    ∃ k st',
      RV64.run (linkedCmpEnv img).rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (img.lkm.totalSize pre +
        img.lkm.totalSize (cmpDrvSetMode m checkerTabMini))) ∧
      st'.getReg AbiReg.gp = regionBase ∧
      (∀ q, q ≠ AbiReg.t0 → q ≠ AbiReg.t1 → st'.getReg q = st.getReg q) ∧
      st'.mem = writeWord64 st.mem
        (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) (BitVec.ofNat 64 m) := by
  let cLi := li AbiReg.t1 (BitVec.ofNat 64 m)
  let cSt := storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (checkerTabMini.globOff modeGVar)
  have hl1 : img.lkm.linkSpec (pre ++ cLi ++ (cSt ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [cmpDrvSetMode, cLi, cSt, List.append_assoc] using hlink
  have hpc1_64 := linkResolved_sub_pc64 (linkedCmpEnv img) pre cLi _ hl1
  obtain ⟨s1, hrun1, hoth1, ht1_1, hm1, hpc1⟩ :=
    li_correct_lm img.lkm (linkedCmpEnv img).hrom pre _ AbiReg.t1 (by decide)
      (BitVec.ofNat 64 m) hl1 hpc1_64 st hpc
  let p1 := pre ++ cLi
  have hpc1' : s1.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p1) := by
    simpa only [p1, img.lkm.totalSize_append] using hpc1
  have hs1gp : s1.getReg AbiReg.gp = regionBase := (hoth1 _ (by decide)).trans hgp
  have hl2 : img.lkm.linkSpec (p1 ++ cSt ++ post) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p1, List.append_assoc] using hl1
  have hpc2_64 := linkResolved_sub_pc64 (linkedCmpEnv img) p1 cSt _ hl2
  have hNeedEq := checkerTabMini_abiNeed_eq
  have h211 : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; simp [abiSlot]
  have halMode : isAligned (s1.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) 8 = true := by
    rw [hs1gp, globOff_bitvec]
    refine isAligned8_add_nat_mul8 regionBase hRegAlign _ ?_
    have hrmNat : checkerTabMini.resBase.toNat = 16 + 24 * 205 + 8 * checkerTabMini.romWords := by
      rw [checkerTabMini_resBase_eq, Int.toNat_natCast]
    rw [hrmNat, t_nxres]; omega
  obtain ⟨s2, hrun2, hoth2, hm2, hpc2⟩ :=
    storeMemOff_sd_correct_lm img.lkm (linkedCmpEnv img).hrom p1 _ AbiReg.gp AbiReg.t1 AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.globOff modeGVar) hl2 hpc2_64 s1 hpc1' halMode
  refine ⟨img.lkm.totalSize cLi + img.lkm.totalSize cSt, s2, ?_, ?_,
    (hoth2 _ (by decide)).trans hs1gp, fun q hq0 hq1 => (hoth2 q hq0).trans (hoth1 q hq1), ?_⟩
  · rw [run_add, hrun1]; exact hrun2
  · rw [hpc2]
    exact congrArg (fun n => BitVec.ofNat 64 (4 * n))
      (by dsimp only [p1, cmpDrvSetMode, cLi, cSt]
          simp only [img.lkm.totalSize_append, Nat.add_assoc])
  · rw [hm2, hs1gp, ht1_1, hm1]

theorem cmp_slli_srli_rd_sim (img : LinkedCmpImage) (rd : Reg) (hrd : rd ≠ 0#5)
    (ret : _root_.L.Word) (hret : 2 ^ 63 ≤ ret.toNat)
    (pre post : List AsmItem)
    (hlink : img.lkm.linkSpec (pre ++ [Asm.slli rd AbiReg.a0 1#6, Asm.srli rd rd 1#6] ++ post) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize pre))
    (ha0 : st.getReg AbiReg.a0 = ret.toBitVec) :
    ∃ s2,
      RV64.run (linkedCmpEnv img).rom 2 st = .cont s2 ∧
      s2.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize
        (pre ++ [Asm.slli rd AbiReg.a0 1#6, Asm.srli rd rd 1#6])) ∧
      s2.getReg rd = (ret - 9223372036854775808).toBitVec ∧
      (∀ q, q ≠ rd → s2.getReg q = st.getReg q) ∧
      s2.mem = st.mem := by
  let cSlli := Asm.slli rd AbiReg.a0 1#6
  let cSrli := Asm.srli rd rd 1#6
  have hl1 : img.lkm.linkSpec (pre ++ [cSlli] ++ ([cSrli] ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [cSlli, cSrli, List.cons_append, List.nil_append, List.append_assoc] using hlink
  obtain ⟨hr1, hpc1, hrd1, hoth1, hm1⟩ :=
    run_shImm_rd_step (linkedCmpEnv img) pre ([cSrli] ++ post) .slli rd AbiReg.a0 1#6 hrd hl1 st hpc
  let s1 := stepReg st rd (evalShiftImm .slli (st.getReg AbiReg.a0) 1#6)
    (BitVec.ofNat 64 (4 * (img.lkm.totalSize pre + 1)))
  let p1 := pre ++ [cSlli]
  have hpc1' : s1.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p1) := by
    simpa only [p1, cSlli, Asm.slli, img.lkm.totalSize_append, img.lkm.totalSize_instr] using hpc1
  have hl2 : img.lkm.linkSpec (p1 ++ [cSrli] ++ post) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p1, List.append_assoc] using hl1
  obtain ⟨hr2, hpc2, hrd2, hoth2, hm2⟩ :=
    run_shImm_rd_step (linkedCmpEnv img) p1 post .srli rd rd 1#6 hrd hl2 s1 hpc1'
  let s2 := stepReg s1 rd (evalShiftImm .srli (s1.getReg rd) 1#6)
    (BitVec.ofNat 64 (4 * (img.lkm.totalSize p1 + 1)))
  refine ⟨s2, by rw [show (2 : Nat) = 1 + 1 from rfl, run_add, hr1]; exact hr2, ?_, ?_,
    fun q hq => (hoth2 q hq).trans (hoth1 q hq), hm2.trans hm1⟩
  · rw [hpc2]
    exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (by
      simp only [p1, cSlli, Asm.slli, Asm.srli, img.lkm.totalSize_append,
        img.lkm.totalSize_cons, img.lkm.totalSize_nil, img.lkm.itemSize_instr,
        Nat.add_zero, Nat.add_assoc])
  · rw [hrd2, hrd1, ha0]
    exact slli_srli_uint64 ret hret

theorem cmp_callWriteMask_not_sol
    {chalBase solBase pinsBase regionBase : BitVec 64}
    {chalLen solLen pinsLen : Nat}
    (hChal64 : chalBase.toNat + chalLen ≤ 2 ^ 64)
    (hSol64 : solBase.toNat + solLen ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pinsLen ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjChalPins : MemSpan.disjoint ⟨chalBase, chalLen⟩ ⟨pinsBase, pinsLen⟩)
    (hDisjChalReg : MemSpan.disjoint ⟨chalBase, chalLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pinsLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjChalSol : MemSpan.disjoint ⟨chalBase, chalLen⟩ ⟨solBase, solLen⟩)
    (hDisjSolPins : MemSpan.disjoint ⟨solBase, solLen⟩ ⟨pinsBase, pinsLen⟩)
    (hDisjSolReg : MemSpan.disjoint ⟨solBase, solLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩) :
    let LA := checkerLayoutA chalBase pinsBase regionBase chalLen pinsLen
      hChal64 hPins64 hRegAlign hReg64 hDisjChalPins hDisjChalReg hDisjPinsReg
    ∀ i, i < solLen → ¬ CallWriteMask LA LA.stackTop (solBase + BitVec.ofNat 64 i) := by
  intro LA i hi hm
  have hcSol : (⟨solBase, solLen⟩ : MemSpan).contains (solBase + BitVec.ofNat 64 i) := ⟨i, hi, rfl⟩
  have hNeedEq := checkerTabMini_abiNeed_eq
  have hRegV : (⟨regionBase, abiNeed checkerTabMini⟩ : MemSpan).valid := by
    dsimp only [MemSpan.valid]; omega
  rcases hm with ⟨hs, _⟩ | hres | ⟨idx, hidx, h8⟩ | ⟨s, hs, h64⟩
  · have hsub : LA.stackSpan.sub ⟨regionBase, abiNeed checkerTabMini⟩ := by
      intro a ⟨k, hk, ha⟩
      dsimp only [ProgLayout.stackSpan] at hk ha
      have hSt : abiStack = LA.stackTop.toNat - LA.stackLimit.toNat :=
        (checkerLayout_stack_diff regionBase hReg64).symm
      have hk' : k < abiStack := by rw [hSt]; exact hk
      have hTop : LA.stackLimit = regionBase + BitVec.ofNat 64 abiSlot := by simp [LA, checkerLayoutA]
      rw [hTop] at ha
      have h1 : abiSlot + abiStack ≤ 205 * abiSlot := by simp [abiSlot, abiStack]
      have hRegNat : regionBase.toNat + 205 * abiSlot < 2 ^ 64 := by rw [← hNeedEq]; exact hReg64
      have hklt : abiSlot + k < 205 * abiSlot := by omega
      refine ⟨abiSlot + k, by dsimp only; rw [hNeedEq]; exact hklt, ?_⟩
      rw [ha, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact @MemSpan.disjoint_to_memDisjoint ⟨solBase, solLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩
      hSol64 hRegV hDisjSolReg _ hcSol (hsub _ hs)
  · have hsub : LA.resGlobSpan.sub ⟨regionBase, abiNeed checkerTabMini⟩ := by
      intro a ⟨k, hk, ha⟩
      dsimp only [ProgLayout.resGlobSpan] at hk ha
      have hTEq : LA.T = regionBase := by simp [LA, checkerLayoutA]
      have hrb : 0 ≤ checkerTabMini.resBase := ProgLayout.resBase_nonneg checkerTabMini
      have harg := checkerTabMini_args_lt
      have haNat : checkerTabMini.args.toNat =
          checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + checkerTabMini.ng) := by
        rw [checkerTabMini_args_eq, checkerTabMini_resBase_eq, Int.toNat_natCast, Int.toNat_natCast, t_nxres, t_ng]
      have hbd : checkerTabMini.resBase.toNat + k < abiNeed checkerTabMini := by
        have h211 : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; simp [abiSlot]
        omega
      refine ⟨checkerTabMini.resBase.toNat + k, hbd, ?_⟩
      rw [ha, BitVec.add_assoc, ← BitVec.ofNat_add]; rfl
    exact @MemSpan.disjoint_to_memDisjoint ⟨solBase, solLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩
      hSol64 hRegV hDisjSolReg _ hcSol (hsub _ hres)
  · rcases checkerTabMini_bytePos_cases hidx with rfl | rfl
    · have hbase : LA.base8 inArr = chalBase := by simp [LA, checkerLayoutA]
      have hcap : LA.cap8 inArr = chalLen := by simp [LA, checkerLayoutA]
      dsimp only [ProgLayout.arr8Span] at h8
      rw [hbase, hcap] at h8
      exact @MemSpan.disjoint_to_memDisjoint ⟨chalBase, chalLen⟩ ⟨solBase, solLen⟩ hChal64 hSol64 hDisjChalSol _ h8 hcSol
    · have hne : pbArr ≠ inArr := by decide
      have hbase : LA.base8 pbArr = pinsBase := by simp [LA, checkerLayoutA, hne]
      have hcap : LA.cap8 pbArr = pinsLen := by simp [LA, checkerLayoutA, hne]
      dsimp only [ProgLayout.arr8Span] at h8
      rw [hbase, hcap] at h8
      exact @MemSpan.disjoint_to_memDisjoint ⟨solBase, solLen⟩ ⟨pinsBase, pinsLen⟩ hSol64 hPins64 hDisjSolPins _ hcSol h8
  · have hsub : (LA.arr64Span s).sub ⟨regionBase, abiNeed checkerTabMini⟩ := by
      intro a ⟨k, hk, ha⟩
      dsimp only [ProgLayout.arr64Span] at hk ha
      have hbase : LA.base64 s = regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.pos64 s) := by
        simp [LA, checkerLayoutA, hs]
      have hcap : LA.cap64 s = abiWords := by simp [LA, checkerLayoutA, hs]
      have hhi := (checkerTabMini_wordPos_bounds hs).2
      have h8w : 8 * abiWords = abiSlot := by simp [abiWords, abiSlot]
      have hm211 : abiSlot * checkerTabMini.pos64 s + abiSlot ≤ 205 * abiSlot := by
        have hm := Nat.mul_le_mul_left abiSlot (by omega : checkerTabMini.pos64 s + 1 ≤ 205)
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm abiSlot 205] at hm; exact hm
      rw [hbase] at ha; rw [hcap] at hk
      refine ⟨abiSlot * checkerTabMini.pos64 s + k, by dsimp only; rw [hNeedEq]; omega, ?_⟩
      rw [ha, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact @MemSpan.disjoint_to_memDisjoint ⟨solBase, solLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩
      hSol64 hRegV hDisjSolReg _ hcSol (hsub _ h64)

theorem cmp_prefix_sim (img : LinkedCmpImage)
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
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjChalPins : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjChalReg : MemSpan.disjoint ⟨chalBase, chalBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hChalMem : ∀ i, (hi : i < chalBytes.size) → initSt.mem (chalBase + BitVec.ofNat 64 i) = chalBytes[i].toBitVec)
    (hPinsMem : ∀ i, (hi : i < pins.size) → initSt.mem (pinsBase + BitVec.ofNat 64 i) = pins[i].toBitVec)
    (hRegZero : ∀ k, k < abiNeed checkerTabMini → initSt.mem (regionBase + BitVec.ofNat 64 k) = 0#8)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : img.rom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run img.rom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha1Out : finalSt.getReg AbiReg.a1 ≠ 1#64) :
    let LA4 := checkerLayoutA chalBase pinsBase regionBase chalBytes.size pins.size
      hChal64 hPins64 hRegAlign hReg64 hDisjChalPins hDisjChalReg hDisjPinsReg
    let preCall4 := checkerDriverAsm checkerTabMini ++ cmpDrvPfx ++ drvNeedLi checkerTabMini ++
      cmpDrvBootCheck checkerTabMini ++ [Asm.call drvInitLabel] ++ cmpDrvMode4Setup checkerTabMini
    chalBytes.size < 2 ^ 63 ∧ pins.size < 2 ^ 63 ∧ solBytes.size < 2 ^ 63 ∧
    ∃ k st,
      RV64.run (linkedCmpEnv img).rom k initSt = .cont st ∧
      st.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize preCall4) ∧
      st.getReg AbiReg.gp = regionBase ∧
      st.getReg AbiReg.sp = LA4.stackTop ∧
      st.getReg AbiReg.s0 = BitVec.ofNat 64 (abiFuel - 2) ∧
      st.getReg AbiReg.s3 = solBase ∧
      st.getReg AbiReg.s4 = BitVec.ofNat 64 solBytes.size ∧
      st.getReg AbiReg.t0 = regionBase + BitVec.ofInt 64 checkerTabMini.args ∧
      st.getReg AbiReg.t1 = 0#64 ∧
      DrvRegsSaved regionBase initSt st.mem ∧
      MemEqOutside ⟨regionBase, abiSlot⟩ initSt.mem st.mem ∧
      ProgMemRel checkerTabMini LA4 st.mem (cmpPhase4Mem chalBytes pins) ∧
      TabHeaderOk LA4 st.mem := by
  intro LA4 preCall4
  have hNeedEq := checkerTabMini_abiNeed_eq
  let tail4 := [Asm.call (fnLabel "check")] ++ cmpDrvMode4Post ++
    cmpDrvMode5Setup checkerTabMini ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode5Post ++
    cmpDrvMode6Setup checkerTabMini ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode6Post ++
    cmpDrvMode8Setup checkerTabMini ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode8Post ++
    cmpDrvMode9Setup checkerTabMini ++ [Asm.call (fnLabel "check")] ++
    [Asm.j drvDoneLabel] ++ linkedCmpFnsAsm img
  have hlinkFull : img.lkm.linkSpec (preCall4 ++ tail4) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    have h := img.hlink
    rw [linkedCmpChipAsm_eq img, checkerCmpDriverAsm_decomp] at h
    dsimp only [cmpDrvPreDone] at h
    change img.lkm.linkSpec _ = .ok (img.code, img.labels)
    simpa only [preCall4, tail4, List.append_assoc] using h
  have hpc0' : initSt.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize (checkerDriverAsm checkerTabMini)) := by
    simpa only [LinkedCmpImage.cmpEntryPc, LinkedCmpImage.cmpEntryWord] using hpc0
  have hlBoot : img.lkm.linkSpec (checkerDriverAsm checkerTabMini ++ cmpDrvPfx ++
      drvNeedLi checkerTabMini ++ cmpDrvBootCheck checkerTabMini ++
      ([Asm.call drvInitLabel] ++ cmpDrvMode4Setup checkerTabMini ++ tail4)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [preCall4, List.append_assoc] using hlinkFull
  obtain ⟨k0, s0, hrun0, hpc0_s, hs0_s3, hs0_s4, hs0_gp, hs0_a0, hs0_a1, hs0_a2, hs0_a3, hs0_a4,
      hs0_saved, hs0_m, _, ha1Lt63, ha3Lt63, ha7Lt63⟩ :=
    linkedCmpDrvBootCheck_sim img (checkerDriverAsm checkerTabMini) _ hlBoot initSt hpc0'
      (by rw [ha4]; exact hRegAlign) (by rw [ha4]; omega) hRetOut hrun hret ha1Out
  have hchal63 : chalBytes.size < 2 ^ 63 := by
    rw [ha1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hchal64] at ha1Lt63; exact ha1Lt63
  have hpins63 : pins.size < 2 ^ 63 := by
    rw [ha3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpins64] at ha3Lt63; exact ha3Lt63
  have hsol63 : solBytes.size < 2 ^ 63 := by
    rw [ha7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsol64] at ha7Lt63; exact ha7Lt63
  let pBoot := checkerDriverAsm checkerTabMini ++ cmpDrvPfx ++ drvNeedLi checkerTabMini ++ cmpDrvBootCheck checkerTabMini
  have hpc0'' : s0.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize pBoot) := by
    simpa only [pBoot, List.append_assoc] using hpc0_s
  have hlCallInit : img.lkm.linkSpec (pBoot ++ [Asm.call drvInitLabel] ++
      (cmpDrvMode4Setup checkerTabMini ++ tail4)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [pBoot, List.append_assoc] using hlBoot
  have hpcCallInit_64 := linkResolved_sub_pc64 (linkedCmpEnv img) pBoot [Asm.call drvInitLabel] _ hlCallInit
  have hltCallInit_64 : 4 * (img.lkm.totalSize pBoot + img.lkm.itemSize (.call drvInitLabel)) < 2 ^ 64 := by
    simpa only [Asm.call, img.lkm.totalSize_singleton] using hpcCallInit_64
  obtain ⟨tgtInit, kCallInit, sCallInit, _, hlkpInit, hrunCallInit, hpcCallInit, hregsCallInit, hmCallInit⟩ :=
    step_item_call_lm img.lkm (linkedCmpEnv img).hrom pBoot _ drvInitLabel hlCallInit hltCallInit_64 s0 hpc0''
  have htgtInit : tgtInit = img.lkm.totalSize (drvInitPre checkerTabMini) :=
    Option.some.inj (hlkpInit.symm.trans (linkedCmp_drvInit_lbl img))
  have hpcInit : sCallInit.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize (drvInitPre checkerTabMini)) := by
    rw [hpcCallInit, htgtInit]
  have hCallInitRa : sCallInit.getReg AbiReg.ra =
      BitVec.ofNat 64 (4 * (img.lkm.totalSize pBoot + img.lkm.itemSize (.call drvInitLabel))) :=
    (hregsCallInit.getReg_eq (by decide)).symm.trans (getReg_setReg_eq s0 AbiReg.ra _ (by decide))
  have hCallInitReg : ∀ q, q ≠ AbiReg.t6 → q ≠ AbiReg.s1 → q ≠ AbiReg.ra → sCallInit.getReg q = s0.getReg q :=
    fun q hqt6 hqs1 hqra => (hregsCallInit.getReg_eq ⟨hqt6, hqs1⟩).symm.trans (getReg_setReg_ne s0 AbiReg.ra q _ hqra)
  have hlInit : img.lkm.linkSpec (drvInitPre checkerTabMini ++ drvInitSubAsm checkerTabMini ++
      (checkerCmpDriverAsm checkerTabMini ++ linkedCmpFnsAsm img)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [drvInitPre, List.append_assoc] using linkedCmpChipAsm_linkSpec_decomp img
  obtain ⟨kInit, sInit, m1, m2, m3, m4, m5, hrunInit, hpcInitRet, hothInit,
      hout1, hHdrTop1, hHdrLim1, hout2, hBase2, hout3, hLen3, hout4, hout5, hRom5, hout6, hZero6⟩ :=
    drvInitSub_sim_gen (linkedCmpEnv img) regionBase chalBase pinsBase hRegAlign hReg64
      (drvInitPre checkerTabMini) (checkerCmpDriverAsm checkerTabMini ++ linkedCmpFnsAsm img) hlInit
      sCallInit hpcInit
      ((hCallInitReg _ (by decide) (by decide) (by decide)).trans (hs0_gp.trans ha4))
      ((hCallInitReg _ (by decide) (by decide) (by decide)).trans (hs0_a0.trans ha0))
      ((hCallInitReg _ (by decide) (by decide) (by decide)).trans (hs0_a1.trans ha1))
      ((hCallInitReg _ (by decide) (by decide) (by decide)).trans (hs0_a2.trans ha2))
      ((hCallInitReg _ (by decide) (by decide) (by decide)).trans (hs0_a3.trans ha3))
  let pInit := pBoot ++ [Asm.call drvInitLabel]
  have hpcInit' : sInit.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize pInit) := by
    rw [hpcInitRet, hCallInitRa, mul4_and_not1_cd _ hltCallInit_64]
    exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (by
      dsimp only [pInit]
      rw [img.lkm.totalSize_append pBoot [Asm.call drvInitLabel], Asm.call, img.lkm.totalSize_singleton])
  have hsInit_gp : sInit.getReg AbiReg.gp = regionBase :=
    (hothInit _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hCallInitReg _ (by decide) (by decide) (by decide)).trans (hs0_gp.trans ha4))
  have hsInit_s3 : sInit.getReg AbiReg.s3 = solBase :=
    (hothInit _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hCallInitReg _ (by decide) (by decide) (by decide)).trans (hs0_s3.trans ha6))
  have hsInit_s4 : sInit.getReg AbiReg.s4 = BitVec.ofNat 64 solBytes.size :=
    (hothInit _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hCallInitReg _ (by decide) (by decide) (by decide)).trans (hs0_s4.trans ha7))
  have hlMode4 : img.lkm.linkSpec (pInit ++ cmpDrvSetMode 4 checkerTabMini ++
      (cmpDrvCallPrep checkerTabMini ++ tail4)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [pInit, cmpDrvMode4Setup, List.append_assoc] using hlCallInit
  obtain ⟨k7a, s7a, hrun7a, hpc7a, hs7agp, hoth7a, hs7am⟩ :=
    cmpDrvSetMode_sim img regionBase hRegAlign hReg64 4 pInit _ hlMode4 sInit hpcInit' hsInit_gp
  let p7a := pInit ++ cmpDrvSetMode 4 checkerTabMini
  have hpc7a' : s7a.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p7a) := by
    simpa only [p7a, img.lkm.totalSize_append] using hpc7a
  have hlPrep4 : img.lkm.linkSpec (p7a ++ cmpDrvCallPrep checkerTabMini ++ tail4) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p7a, List.append_assoc] using hlMode4
  obtain ⟨k7b, s7b, hrun7b, hpc7b, hm7b, hs7bgp, hs7bsp, hs7bs0, hs7bt0, hs7bt1, hoth7b⟩ :=
    linkedCmpDrvCallPrep_sim img regionBase hRegAlign p7a tail4 hlPrep4
      (checkerCmp_exhausted_lbl img) s7a hpc7a' hs7agp
  have hs0_m' : MemEqOutside (callerSaveSpan regionBase (checkerTabMini.saveBase 0)) initSt.mem sCallInit.mem := by
    rw [hmCallInit, ← ha4]; exact hs0_m
  have hs0_saved' : DrvRegsSaved regionBase initSt sCallInit.mem := by
    rw [hmCallInit, ← ha4]; exact hs0_saved
  obtain ⟨houtSlot0, hs6Top, hHdr, hMemRel⟩ := phaseInit_hdr_and_rel 4
    initSt.mem sCallInit.mem m1 m2 m3 m4 m5 sInit.mem s7a.mem
    hchal63 hpins63 hChal64 hPins64 hRegAlign hReg64 hDisjChalPins hDisjChalReg hDisjPinsReg
    hChalMem hPinsMem hRegZero
    hs0_m' hout1 hHdrTop1 hHdrLim1 hout2 hBase2 hout3 hLen3 hout4 hout5 hRom5
    hout6 hZero6 hs7am
  have hs7aSaved := phaseInit_drvRegsSaved 4
    sCallInit.mem m1 m2 m3 m4 m5 sInit.mem s7a.mem
    (by omega) hs0_saved'
    hout1 hout2 hout3 hout4 hout5 hout6 hs7am
  have hreg_pres : ∀ r, r ≠ AbiReg.t0 → r ≠ AbiReg.t1 → r ≠ AbiReg.t2 → r ≠ AbiReg.t6 →
      r ≠ AbiReg.s0 → r ≠ AbiReg.sp → r ≠ AbiReg.s1 →
      s7b.getReg r = sInit.getReg r := by
    intro r hr0 hr1 hr2 hr6 hrs0 hrsp hrs1
    exact (hoth7b r hrs0 hrsp hr0 hr1 hr2 hr6 hrs1).trans (hoth7a r hr0 hr1)
  have hs7bMem : s7b.mem = s7a.mem := hm7b
  have hHdrB : TabHeaderOk LA4 s7b.mem := by rw [hs7bMem]; exact hHdr
  have hMemRelB : ProgMemRel checkerTabMini LA4 s7b.mem (cmpPhase4Mem chalBytes pins) := by
    rw [hs7bMem]; exact hMemRel
  have hs7bSaved : DrvRegsSaved regionBase initSt s7b.mem := by
    rw [hs7bMem]; exact hs7aSaved
  refine ⟨hchal63, hpins63, hsol63,
    k0 + kCallInit + kInit + k7a + k7b, s7b, ?_, ?_, hs7bgp,
    by rw [hs7bsp, hs7am]
       have hr := resBase_ge_16
       have hgb := globOff_bound (g := modeGVar) (by decide)
       have hmodeOff := globOff_eq_nat modeGVar
       have hmodeNn : 0 ≤ checkerTabMini.globOff modeGVar := by rw [hmodeOff]; omega
       have hmodeB : (checkerTabMini.globOff modeGVar).toNat + 8 ≤ abiSlot := by
         rw [hmodeOff, Int.toNat_natCast]; exact hgb
       have hd : (0 : Int).toNat + 8 ≤ (checkerTabMini.globOff modeGVar).toNat ∨
           (checkerTabMini.globOff modeGVar).toNat + 8 ≤ (0 : Int).toNat := by
         rw [hmodeOff, Int.toNat_natCast]; exact Or.inl (by omega)
       have hneed : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; simp [abiSlot]
       have hR : regionBase.toNat + abiSlot ≤ 2 ^ 64 := by omega
       have hrw := readWord64_writeWord64_tabOff hR (off1 := 0) (off2 := checkerTabMini.globOff modeGVar)
         (by omega) hmodeNn (by simp [abiSlot]) hmodeB hd 4#64 (m := sInit.mem)
       have hz : BitVec.ofInt 64 0 = 0#64 := rfl
       rw [hz, BitVec.add_zero] at hrw
       rw [hrw, hs6Top],
    hs7bs0,
    (hreg_pres _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsInit_s3,
    (hreg_pres _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsInit_s4,
    hs7bt0, hs7bt1, hs7bSaved, by rw [hs7bMem]; exact houtSlot0, hMemRelB, hHdrB⟩
  · rw [run_add, run_add, run_add, run_add, hrun0]
    dsimp only; rw [hrunCallInit]; dsimp only; rw [hrunInit]
    dsimp only; rw [hrun7a]; exact hrun7b
  · rw [hpc7b]; exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (by
      have e7a : img.lkm.totalSize p7a + img.lkm.totalSize (cmpDrvCallPrep checkerTabMini) =
          img.lkm.totalSize pInit + img.lkm.totalSize (cmpDrvMode4Setup checkerTabMini) := by
        dsimp only [p7a, cmpDrvMode4Setup]
        rw [img.lkm.totalSize_append pInit _, img.lkm.totalSize_append (cmpDrvSetMode 4 checkerTabMini) _, Nat.add_assoc]
      dsimp only [preCall4]
      rw [e7a]; dsimp only [pInit, pBoot]
      simp only [img.lkm.totalSize_append, Nat.add_assoc])


end ConAgua.RISCV.Bridge
