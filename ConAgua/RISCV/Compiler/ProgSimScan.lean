import ConAgua.RISCV.Compiler.ProgSimProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Byte-Source, `copy8w`, and `scan8` Forward Simulation (`ConAgua.RISCV.Compiler.ProgSimScan`)

Completes statement-level forward simulation for `_root_.L.BSrc`, `.copy8w`, and `.scan8`.
Split out of `ProgSimProof.lean` for fast incremental compilation.
-/

namespace ConAgua.RISCV.Compiler

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Linker

def bsrcSetup (tab : Tab) (baseReg tmpReg : Reg) : _root_.L.BSrc → List AsmItem
  | .arr a =>
    loadMemOff .ld AbiReg.t0 AbiReg.gp tmpReg (tab.len8 a) ++
    loadMemOff .ld baseReg AbiReg.gp tmpReg (tab.base8 a)
  | .rom bs =>
    li AbiReg.t0 (BitVec.ofNat 64 bs.length) ++
    addImmOff baseReg AbiReg.gp tmpReg (tab.romBase + (romIdx bs tab.rom : Int))

def bsrcAddr (tab : Tab) (L : ProgLayout tab) : _root_.L.BSrc → BitVec 64
  | .arr a => L.base8 a
  | .rom bs => L.T + BitVec.ofNat 64 (tab.romBase.toNat + romIdx bs tab.rom)

theorem bsrc_byte_at {tab : Tab} {L : ProgLayout tab} {rmem : ByteMem} {lm : _root_.L.Mem}
    (hrel : ProgMemRel tab L rmem lm) (src : _root_.L.BSrc) (hsrc : bsrcOkB tab src = true)
    (j : Nat) (hj : j < (lm.src8 src).size) :
    rmem (bsrcAddr tab L src + BitVec.ofNat 64 j) = (lm.src8 src)[j].toBitVec := by
  cases src with
  | arr a => exact (hrel.1 a hsrc).2.2.2.2 j hj
  | rom d =>
    have hromSpec := Tab.romSliceOk_spec hsrc
    simp only [_root_.L.Mem.src8, List.size_toArray] at hj ⊢
    rw [bsrcAddr, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc,
        hrel.2.2.1 (romIdx d tab.rom + j) (by omega)]
    have hrom_eq := hromSpec.2 j hj
    rw [List.getElem?_eq_getElem (by omega : romIdx d tab.rom + j < tab.rom.length),
        Option.some.injEq] at hrom_eq
    rw [hrom_eq]; simp [List.getElem_toArray]

theorem bsrc_setup_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab) (lm : _root_.L.Mem)
    (src : _root_.L.BSrc) (hsrc : bsrcOkB env.tab src = true)
    (baseReg tmpReg : Reg)
    (hnpB : baseReg ≠ AbiReg.zero ∧ baseReg ≠ AbiReg.gp ∧ baseReg ≠ AbiReg.sp ∧
      baseReg ≠ AbiReg.s0 ∧ baseReg ≠ AbiReg.s1 ∧ baseReg ≠ AbiReg.s2)
    (hnpT : tmpReg ≠ AbiReg.zero ∧ tmpReg ≠ AbiReg.gp ∧ tmpReg ≠ AbiReg.sp ∧
      tmpReg ≠ AbiReg.s0 ∧ tmpReg ≠ AbiReg.s1 ∧ tmpReg ≠ AbiReg.s2)
    (hbt0 : baseReg ≠ AbiReg.t0) (htt0 : tmpReg ≠ AbiReg.t0) (_hbt : baseReg ≠ tmpReg)
    (_hbgp : baseReg ≠ AbiReg.gp) (htgp : tmpReg ≠ AbiReg.gp)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ bsrcSetup env.tab baseReg tmpReg src ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hrel : ProgMemRel env.tab L st.mem lm) :
    ∃ k st', RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (bsrcSetup env.tab baseReg tmpReg src))) ∧
      st'.getReg AbiReg.t0 = BitVec.ofNat 64 (lm.src8 src).size ∧
      st'.getReg baseReg = bsrcAddr env.tab L src ∧
      (lm.src8 src).size < 2 ^ 64 ∧
      (∀ r, r ≠ AbiReg.t0 → r ≠ baseReg → r ≠ tmpReg → st'.getReg r = st.getReg r) ∧
      st'.mem = st.mem ∧
      PreservedRegs st st' := by
  cases src with
  | arr a =>
    dsimp only [bsrcOkB] at hsrc
    rcases hrel.1 a hsrc with ⟨_, hlt64, hlenR, hbaseR, _⟩
    let sL := loadMemOff .ld AbiReg.t0 AbiReg.gp tmpReg (env.tab.len8 a)
    let sB := loadMemOff .ld baseReg AbiReg.gp tmpReg (env.tab.base8 a)
    have hsDef : bsrcSetup env.tab baseReg tmpReg (.arr a) = sL ++ sB := rfl
    rw [hsDef] at hlink
    have hlink0 : lkm.linkSpec (pre ++ sL ++ (sB ++ post)) = .ok (env.code, env.labels) := by
      simpa [List.append_assoc] using hlink
    have halL : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.len8 a)) 8 = true := by
      rw [hgp, Tab.len8_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨stA, hrA, hoA, ht0A, hmA, hpcA⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom pre (sB ++ post) AbiReg.t0 AbiReg.gp tmpReg
        (by decide) hnpT.1 htgp.symm (env.tab.len8 a) hlink0
        (linkResolved_sub_pc64 env pre sL _ hlink0) st hpc halL
    have hpA : PreservedRegs st stA :=
      ⟨hoA _ (by decide) hnpT.2.1.symm, hoA _ (by decide) hnpT.2.2.1.symm,
       hoA _ (by decide) hnpT.2.2.2.1.symm, hoA _ (by decide) hnpT.2.2.2.2.2.symm⟩
    let preA := pre ++ sL
    have hpcA' : stA.pc = BitVec.ofNat 64 (4 * lkm.totalSize preA) := by rw [hpcA, lkm.totalSize_append pre sL]
    have hlink1 : lkm.linkSpec (preA ++ sB ++ post) = .ok (env.code, env.labels) := by
      simpa [preA, List.append_assoc] using hlink0
    have halB : isAligned (stA.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.base8 a)) 8 = true := by
      rw [hpA.gp.trans hgp, Tab.base8_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨stB, hrB, hoB, htB, hmB, hpcB⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom preA post baseReg AbiReg.gp tmpReg
        hnpB.1 hnpT.1 htgp.symm (env.tab.base8 a) hlink1
        (linkResolved_sub_pc64 env preA sB post hlink1) stA hpcA' halB
    have hpB : PreservedRegs stA stB :=
      ⟨hoB _ hnpB.2.1.symm hnpT.2.1.symm, hoB _ hnpB.2.2.1.symm hnpT.2.2.1.symm,
       hoB _ hnpB.2.2.2.1.symm hnpT.2.2.2.1.symm, hoB _ hnpB.2.2.2.2.2.symm hnpT.2.2.2.2.2.symm⟩
    refine ⟨lkm.totalSize sL + lkm.totalSize sB, stB, run_trans hrA hrB, ?_, ?_, ?_, hlt64, ?_, hmB.trans hmA, hpA.trans hpB⟩
    · rw [hpcB, lkm.totalSize_append pre sL, hsDef, lkm.totalSize_append sL sB, Nat.add_assoc]
    · rw [hoB AbiReg.t0 hbt0.symm htt0.symm, ht0A, hgp, hlenR]; simp [_root_.L.Mem.src8]
    · rw [htB, hmA, hpA.gp.trans hgp, hbaseR]; rfl
    · intro r hr0 hrb hrt; rw [hoB r hrb hrt, hoA r hr0 hrt]
  | rom d =>
    dsimp only [bsrcOkB] at hsrc
    have hromSpec := Tab.romSliceOk_spec hsrc
    have hrb := L.tab_rom_bound
    have hvT := L.hTValid
    have hdlt : d.length < 2 ^ 64 := by
      have hrb16 : 16 ≤ env.tab.romBase.toNat := by simp [Tab.romBase]; omega
      omega
    let sL := li AbiReg.t0 (BitVec.ofNat 64 d.length)
    let sB := addImmOff baseReg AbiReg.gp tmpReg (env.tab.romBase + (romIdx d env.tab.rom : Int))
    have hsDef : bsrcSetup env.tab baseReg tmpReg (.rom d) = sL ++ sB := rfl
    rw [hsDef] at hlink
    have hlink0 : lkm.linkSpec (pre ++ sL ++ (sB ++ post)) = .ok (env.code, env.labels) := by
      simpa [List.append_assoc] using hlink
    obtain ⟨stA, hrA, hoA, ht0A, hmA, hpcA⟩ :=
      li_correct_lm lkm env.hrom pre (sB ++ post) AbiReg.t0 (by decide) (BitVec.ofNat 64 d.length)
        hlink0 (linkResolved_sub_pc64 env pre sL _ hlink0) st hpc
    have hpA : PreservedRegs st stA :=
      ⟨hoA _ (by decide), hoA _ (by decide), hoA _ (by decide), hoA _ (by decide)⟩
    let preA := pre ++ sL
    have hpcA' : stA.pc = BitVec.ofNat 64 (4 * lkm.totalSize preA) := by rw [hpcA, lkm.totalSize_append pre sL]
    have hlink1 : lkm.linkSpec (preA ++ sB ++ post) = .ok (env.code, env.labels) := by
      simpa [preA, List.append_assoc] using hlink0
    obtain ⟨stB, hrB, hoB, htB, hmB, hpcB⟩ :=
      addImmOff_correct_lm lkm env.hrom preA post baseReg AbiReg.gp tmpReg hnpB.1 hnpT.1 htgp
        (env.tab.romBase + (romIdx d env.tab.rom : Int)) hlink1
        (linkResolved_sub_pc64 env preA sB post hlink1) stA hpcA'
    have hpB : PreservedRegs stA stB :=
      ⟨hoB _ hnpB.2.1.symm hnpT.2.1.symm, hoB _ hnpB.2.2.1.symm hnpT.2.2.1.symm,
       hoB _ hnpB.2.2.2.1.symm hnpT.2.2.2.1.symm, hoB _ hnpB.2.2.2.2.2.symm hnpT.2.2.2.2.2.symm⟩
    refine ⟨lkm.totalSize sL + lkm.totalSize sB, stB, run_trans hrA hrB, ?_, ?_, ?_, by simpa [_root_.L.Mem.src8] using hdlt, ?_, hmB.trans hmA, hpA.trans hpB⟩
    · rw [hpcB, lkm.totalSize_append pre sL, hsDef, lkm.totalSize_append sL sB, Nat.add_assoc]
    · rw [hoB AbiReg.t0 hbt0.symm htt0.symm, ht0A]; simp [_root_.L.Mem.src8]
    · have hrb_nn : 0 ≤ env.tab.romBase := ProgLayout.romBase_nonneg env.tab
      have hcoe : (env.tab.romBase + (romIdx d env.tab.rom : Int)) =
          ((env.tab.romBase.toNat + romIdx d env.tab.rom : Nat) : Int) := by
        rw [← Int.toNat_of_nonneg hrb_nn]; push_cast; rfl
      rw [htB, hpA.gp.trans hgp, hcoe]; rfl
    · intro r hr0 hrb hrt; rw [hoB r hrb hrt, hoA r hr0]

theorem copy8w_src_check_sim {lkm : LinkModel} (env : CodeEnvGen lkm) {sp : BitVec 64} {nl : Nat}
    (hal : isAligned sp 8 = true) (bytes : Array UInt8) (hlenLt : bytes.size < 2 ^ 64)
    (vsi vk : _root_.L.Word) (t1Val t5Val : BitVec 64)
    (pre codeCheck post : List AsmItem)
    (hcodeCheck : codeCheck =
      loadMemOff .ld AbiReg.t2 AbiReg.sp AbiReg.t6 (slotOff (nl + 3)) ++
      [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3,
       Asm.bltu AbiReg.t0 AbiReg.t2 errLabel, Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2])
    (hlink : lkm.linkSpec (pre ++ codeCheck ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hsp : st.getReg AbiReg.sp = sp)
    (ht0 : st.getReg AbiReg.t0 = BitVec.ofNat 64 bytes.size)
    (ht1 : st.getReg AbiReg.t1 = t1Val) (ht3 : st.getReg AbiReg.t3 = vk.toBitVec)
    (ht5 : st.getReg AbiReg.t5 = t5Val)
    (hslot3 : readWord64 st.mem (sp + BitVec.ofInt 64 (slotOff (nl + 3))) = vsi.toBitVec) :
    if vsi.toNat + vk.toNat ≤ bytes.size then
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize codeCheck)) ∧
        r'.getReg AbiReg.t1 = t1Val ∧
        r'.getReg AbiReg.t2 = t5Val + BitVec.ofNat 64 vsi.toNat ∧
        r'.getReg AbiReg.t3 = vk.toBitVec ∧
        r'.mem = st.mem ∧
        PreservedRegs st r'
    else
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st r' := by
  let cl := loadMemOff .ld AbiReg.t2 AbiReg.sp AbiReg.t6 (slotOff (nl + 3))
  let cb0 := [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel]
  let cs0 := [Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3]
  let cb1 := [Asm.bltu AbiReg.t0 AbiReg.t2 errLabel]
  let ca := [Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2]
  have hcEq : codeCheck = cl ++ cb0 ++ cs0 ++ cb1 ++ ca := by
    rw [hcodeCheck]; simp [cl, cb0, cs0, cb1, ca, List.append_assoc]
  rw [hcEq] at hlink
  have hlink0 : lkm.linkSpec (pre ++ cl ++ (cb0 ++ cs0 ++ cb1 ++ ca ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
  have hal3 : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff (nl + 3))) 8 = true := by
    rw [hsp]; exact isAligned8_add_int_mul8 sp hal (1 + (nl + 3))
  obtain ⟨st1, hrun0, hoth0, ht2_1, hmem0, hpc1⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre _ AbiReg.t2 AbiReg.sp AbiReg.t6
      (by decide) (by decide) (by decide) (slotOff (nl + 3)) hlink0
      (linkResolved_sub_pc64 env pre cl _ hlink0) st hpc hal3
  have hpres0 : PreservedRegs st st1 :=
    ⟨hoth0 _ (by decide) (by decide), hoth0 _ (by decide) (by decide),
     hoth0 _ (by decide) (by decide), hoth0 _ (by decide) (by decide)⟩
  let pre1 := pre ++ cl
  have htwPre1 : lkm.totalSize pre1 = lkm.totalSize pre + lkm.totalSize cl := lkm.totalSize_append pre cl
  have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by rw [hpc1, htwPre1]
  have hlink1 : lkm.linkSpec (pre1 ++ cb0 ++ (cs0 ++ cb1 ++ ca ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre1, List.append_assoc] using hlink0
  have ht0_1 : st1.getReg AbiReg.t0 = BitVec.ofNat 64 bytes.size := (hoth0 _ (by decide) (by decide)).trans ht0
  have ht1_1 : st1.getReg AbiReg.t1 = t1Val := (hoth0 _ (by decide) (by decide)).trans ht1
  have ht2Val : st1.getReg AbiReg.t2 = vsi.toBitVec := by rw [ht2_1, hsp, hslot3]
  have ht3_1 : st1.getReg AbiReg.t3 = vk.toBitVec := (hoth0 _ (by decide) (by decide)).trans ht3
  have ht5_1 : st1.getReg AbiReg.t5 = t5Val := (hoth0 _ (by decide) (by decide)).trans ht5
  have hbr0 := run_br_step env pre1 _ .bltu AbiReg.t0 AbiReg.t3 errLabel env.errTarget env.herrLbl (by decide) hlink1 st1 hpc1'
  have hcond0 : evalBranch .bltu (st1.getReg AbiReg.t0) (st1.getReg AbiReg.t3) =
      decide (bytes.size < vk.toNat) := by
    rw [ht0_1, ht3_1, u64_toBitVec_eq_ofNat]; exact evalBranch_bltu_nat hlenLt vk.toBitVec.isLt
  by_cases hkn : vk.toNat ≤ bytes.size
  · have hbr0F : evalBranch .bltu (st1.getReg AbiReg.t0) (st1.getReg AbiReg.t3) = false := by
      rw [hcond0, decide_eq_false_iff_not]; omega
    obtain ⟨_, st2, _, hrun1, hpc2Br, hoth1Br, hpres1Br, hmem1Br⟩ := hbr0
    let pre2 := pre1 ++ cb0
    have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) := by
      rw [hpc2Br, hbr0F]; simp only [Bool.false_eq_true, ↓reduceIte]
      exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (lkm.totalSize_append pre1 cb0).symm
    have hlink2 : lkm.linkSpec (pre2 ++ cs0 ++ (cb1 ++ ca ++ post)) =
        .ok (env.code, env.labels) := by simpa [pre2, List.append_assoc] using hlink1
    let st3 := stepReg st2 AbiReg.t0 (evalAlu .sub (st2.getReg AbiReg.t0) (st2.getReg AbiReg.t3))
      (BitVec.ofNat 64 (4 * (lkm.totalSize pre2 + 1)))
    obtain ⟨hrun2, hpc3, ht0_3, hoth2, hmem2, hpres2⟩ :=
      run_alu_step env pre2 _ .sub AbiReg.t0 AbiReg.t0 AbiReg.t3 nonPreserved_t0 hlink2 st2 hpc2'
    have ht0_3v : st3.getReg AbiReg.t0 = BitVec.ofNat 64 (bytes.size - vk.toNat) := by
      rw [ht0_3, evalAlu, hoth1Br _ (by decide), hoth1Br _ (by decide), ht0_1, ht3_1, u64_toBitVec_eq_ofNat]
      exact bitvec_sub_ofNat_eq hlenLt hkn
    let pre3 := pre2 ++ cs0
    have htwPre3 : lkm.totalSize pre3 = lkm.totalSize pre2 + 1 := by
      have htws : lkm.totalSize cs0 = 1 := by simp only [cs0, Asm.sub, lkm.totalSize_instr]
      rw [lkm.totalSize_append, htws]
    have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre3) := by rw [hpc3, htwPre3]
    have hlink3 : lkm.linkSpec (pre3 ++ cb1 ++ (ca ++ post)) =
        .ok (env.code, env.labels) := by simpa [pre3, List.append_assoc] using hlink2
    have hbr1 := run_br_step env pre3 _ .bltu AbiReg.t0 AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide) hlink3 st3 hpc3'
    have hcond1 : evalBranch .bltu (st3.getReg AbiReg.t0) (st3.getReg AbiReg.t2) =
        decide (bytes.size - vk.toNat < vsi.toNat) := by
      rw [ht0_3v, hoth2 _ (by decide), hoth1Br _ (by decide), ht2Val, u64_toBitVec_eq_ofNat]
      exact evalBranch_bltu_nat (by omega) vsi.toBitVec.isLt
    by_cases hdi : vsi.toNat ≤ bytes.size - vk.toNat
    · have hbound : vsi.toNat + vk.toNat ≤ bytes.size := by omega
      simp only [hbound, ↓reduceIte]
      have hbr1F : evalBranch .bltu (st3.getReg AbiReg.t0) (st3.getReg AbiReg.t2) = false := by
        rw [hcond1, decide_eq_false_iff_not]; omega
      obtain ⟨_, st4, _, hrun3, hpc4Br, hoth3Br, hpres3Br, hmem3Br⟩ := hbr1
      let pre4 := pre3 ++ cb1
      have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre4) := by
        rw [hpc4Br, hbr1F]; simp only [Bool.false_eq_true, ↓reduceIte]
        exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (lkm.totalSize_append pre3 cb1).symm
      have hlink4 : lkm.linkSpec (pre4 ++ ca ++ post) =
          .ok (env.code, env.labels) := by simpa [pre4, List.append_assoc] using hlink3
      let st5 := stepReg st4 AbiReg.t2 (evalAlu .add (st4.getReg AbiReg.t5) (st4.getReg AbiReg.t2))
        (BitVec.ofNat 64 (4 * (lkm.totalSize pre4 + 1)))
      obtain ⟨hrun4, hpc5, ht2_5, hoth4, hmem4, hpres4⟩ :=
        run_alu_step env pre4 _ .add AbiReg.t2 AbiReg.t5 AbiReg.t2 nonPreserved_t2 hlink4 st4 hpc4'
      have ht2_5v : st5.getReg AbiReg.t2 = t5Val + BitVec.ofNat 64 vsi.toNat := by
        rw [ht2_5, evalAlu, hoth3Br _ (by decide), hoth3Br _ (by decide),
            hoth2 _ (by decide), hoth2 _ (by decide),
            hoth1Br _ (by decide), hoth1Br _ (by decide), ht5_1, ht2Val, u64_toBitVec_eq_ofNat]
      have hpcEq : lkm.totalSize pre4 + 1 = lkm.totalSize pre + lkm.totalSize codeCheck := by
        have htws0 : lkm.totalSize cs0 = 1 := by simp only [cs0, Asm.sub, lkm.totalSize_instr]
        have htwa : lkm.totalSize ca = 1 := by simp only [ca, Asm.add, lkm.totalSize_instr]
        rw [show pre4 = pre3 ++ cb1 from rfl, lkm.totalSize_append, htwPre3,
            show pre2 = pre1 ++ cb0 from rfl, lkm.totalSize_append, htwPre1, hcEq,
            lkm.totalSize_append (((cl ++ cb0) ++ cs0) ++ cb1) ca,
            lkm.totalSize_append ((cl ++ cb0) ++ cs0) cb1,
            lkm.totalSize_append (cl ++ cb0) cs0, lkm.totalSize_append cl cb0, htws0, htwa]; omega
      refine ⟨_, st5, run_trans (run_trans (run_trans hrun0 hrun1) hrun2) (run_trans hrun3 hrun4),
        by rw [hpc5, hpcEq],
        (hoth4 _ (by decide)).trans ((hoth3Br _ (by decide)).trans ((hoth2 _ (by decide)).trans ((hoth1Br _ (by decide)).trans ht1_1))),
        ht2_5v,
        (hoth4 _ (by decide)).trans ((hoth3Br _ (by decide)).trans ((hoth2 _ (by decide)).trans ((hoth1Br _ (by decide)).trans ht3_1))),
        by rw [hmem4, hmem3Br, hmem2, hmem1Br, hmem0],
        hpres0.trans (hpres1Br.trans (hpres2.trans (hpres3Br.trans hpres4)))⟩
    · have hbound : ¬(vsi.toNat + vk.toNat ≤ bytes.size) := by omega
      simp only [hbound, ↓reduceIte]
      have hbr1T : evalBranch .bltu (st3.getReg AbiReg.t0) (st3.getReg AbiReg.t2) = true := by
        rw [hcond1, decide_eq_true_iff]; omega
      obtain ⟨_, st4, _, hrun3, hpc4Br, _, hpres3Br, _⟩ := hbr1
      have hpc4' : st4.pc = BitVec.ofNat 64 (4 * env.errTarget) := by rw [hpc4Br, hbr1T]; rfl
      exact ⟨_, st4, run_trans (run_trans (run_trans hrun0 hrun1) hrun2) hrun3, hpc4',
        hpres0.trans (hpres1Br.trans (hpres2.trans hpres3Br))⟩
  · have hbound : ¬(vsi.toNat + vk.toNat ≤ bytes.size) := by omega
    simp only [hbound, ↓reduceIte]
    have hbr0T : evalBranch .bltu (st1.getReg AbiReg.t0) (st1.getReg AbiReg.t3) = true := by
      rw [hcond0, decide_eq_true_iff]; omega
    obtain ⟨_, st2, _, hrun1, hpc2Br, _, hpres1Br, _⟩ := hbr0
    have hpc2' : st2.pc = BitVec.ofNat 64 (4 * env.errTarget) := by rw [hpc2Br, hbr0T]; rfl
    exact ⟨_, st2, run_trans hrun0 hrun1, hpc2', hpres0.trans hpres1Br⟩

theorem copy8w_loop_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (da : _root_.L.TieredArray) (hda : env.tab.wordPosOkB da = true)
    (src : _root_.L.BSrc) (hsrc : bsrcOkB env.tab src = true)
    (loopLbl doneLbl : String) (loopTarget doneTarget : Nat)
    (hloopLbl : lookupLabel env.labels loopLbl = some loopTarget)
    (hdoneLbl : lookupLabel env.labels doneLbl = some doneTarget)
    (pre post : List AsmItem)
    (hltLoop : loopTarget = lkm.totalSize pre)
    (hlink : lkm.linkSpec (pre ++ [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
      Asm.lbu AbiReg.t4 AbiReg.t2, Asm.sd AbiReg.t1 AbiReg.t4,
      Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 1#12,
      Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] ++ post) = .ok (env.code, env.labels)) :
    ∀ n (lm : _root_.L.Mem) (di si : _root_.L.Word) (st : State),
      st.pc = BitVec.ofNat 64 (4 * loopTarget) →
      st.getReg AbiReg.t1 = L.base64 da + BitVec.ofNat 64 (8 * di.toNat) →
      st.getReg AbiReg.t2 = bsrcAddr env.tab L src + BitVec.ofNat 64 si.toNat →
      st.getReg AbiReg.t3 = BitVec.ofNat 64 n →
      di.toNat + n ≤ (lm.arr64 da).size →
      si.toNat + n ≤ (lm.src8 src).size →
      (lm.src8 src).size < 2 ^ 64 →
      ProgMemRel env.tab L st.mem lm →
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * doneTarget) ∧
        PreservedRegs st r' ∧
        ProgMemRel env.tab L r'.mem (lm.copy8w da di (lm.src8 src) si n) ∧
        MemEqOutside (L.arr64Span da) st.mem r'.mem := by
  intro n
  induction n with
  | zero =>
    intro lm di si st hpc ht1 ht2 ht3 hdi hsi hsz hm
    have ⟨_, hl1⟩ := linkResolved_mid_split lkm pre [Asm.lbl loopLbl] _ post hlink
    have ⟨hlBeq, _⟩ := linkResolved_mid_split lkm (pre ++ [Asm.lbl loopLbl]) [Asm.beq AbiReg.t3 AbiReg.zero doneLbl] _ post hl1
    have hbr := run_br_step env (pre ++ [Asm.lbl loopLbl]) _ .beq AbiReg.t3 AbiReg.zero doneLbl doneTarget hdoneLbl (by decide)
      hlBeq st (by rw [lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero, ← hltLoop]; exact hpc)
    have hcond : evalBranch .beq (st.getReg AbiReg.t3) (st.getReg AbiReg.zero) = true := by
      rw [ht3, getReg_zero st]; decide
    obtain ⟨kBr, st', _, hrun, hpcBr, _, hpresBr, hmemBr⟩ := hbr
    have hpc' : st'.pc = BitVec.ofNat 64 (4 * doneTarget) := by rw [hpcBr, hcond]; rfl
    have hcopy : lm.copy8w da di (lm.src8 src) si 0 = lm := by simp [_root_.L.Mem.copy8w]
    rw [hcopy]
    exact ⟨kBr, st', hrun, hpc', hpresBr, by rw [hmemBr]; exact hm, fun _ _ => by rw [hmemBr]⟩
  | succ n ih =>
    intro lm di si st hpc ht1 ht2 ht3 hdi hsi hsz hm
    have hltLoopEq : lkm.totalSize (pre ++ [Asm.lbl loopLbl]) = loopTarget := by
      rw [lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero, hltLoop]
    have ⟨_, hlR0⟩ := linkResolved_mid_split lkm pre [Asm.lbl loopLbl] _ post hlink
    have ⟨hl1, hlR1⟩ := linkResolved_mid_split lkm (pre ++ [Asm.lbl loopLbl]) [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]
      [Asm.lbu AbiReg.t4 AbiReg.t2, Asm.sd AbiReg.t1 AbiReg.t4, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
       Asm.addi AbiReg.t2 AbiReg.t2 1#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] post hlR0
    have ⟨hl2, hlR2⟩ := linkResolved_mid_split lkm ((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl])
      [Asm.lbu AbiReg.t4 AbiReg.t2]
      [Asm.sd AbiReg.t1 AbiReg.t4, Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 1#12,
       Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] post hlR1
    have ⟨hl3, hlR3⟩ := linkResolved_mid_split lkm (((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.lbu AbiReg.t4 AbiReg.t2])
      [Asm.sd AbiReg.t1 AbiReg.t4]
      [Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 1#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] post hlR2
    have ⟨hl4, hlR4⟩ := linkResolved_mid_split lkm ((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.lbu AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4])
      [Asm.addi AbiReg.t1 AbiReg.t1 8#12]
      [Asm.addi AbiReg.t2 AbiReg.t2 1#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] post hlR3
    have ⟨hl5, hlR5⟩ := linkResolved_mid_split lkm (((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.lbu AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) ++ [Asm.addi AbiReg.t1 AbiReg.t1 8#12])
      [Asm.addi AbiReg.t2 AbiReg.t2 1#12] [Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] post hlR4
    have ⟨hl6, hlR6⟩ := linkResolved_mid_split lkm ((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.lbu AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) ++ [Asm.addi AbiReg.t1 AbiReg.t1 8#12]) ++ [Asm.addi AbiReg.t2 AbiReg.t2 1#12])
      [Asm.addi AbiReg.t3 AbiReg.t3 (-1#12)] [Asm.j loopLbl, Asm.lbl doneLbl] post hlR5
    have ⟨hl7, _⟩ := linkResolved_mid_split lkm (((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.lbu AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) ++ [Asm.addi AbiReg.t1 AbiReg.t1 8#12]) ++ [Asm.addi AbiReg.t2 AbiReg.t2 1#12]) ++ [Asm.addi AbiReg.t3 AbiReg.t3 (-1#12)])
      [Asm.j loopLbl] [Asm.lbl doneLbl] post hlR6
    rcases hm.2.1 da hda with ⟨hcapD, _, _, _, _⟩
    have hnBound : n + 1 < 2 ^ 64 := by omega
    have hbr := run_br_step env (pre ++ [Asm.lbl loopLbl]) _ .beq AbiReg.t3 AbiReg.zero doneLbl doneTarget hdoneLbl (by decide)
      hl1 st (by rw [hltLoopEq]; exact hpc)
    have hcond : evalBranch .beq (st.getReg AbiReg.t3) (st.getReg AbiReg.zero) = false := by
      rw [ht3, getReg_zero st, evalBranch]
      exact beq_false_of_ne (BitVec.ofNat_ne_zero_of_lt (Nat.succ_pos n) hnBound)
    obtain ⟨kBr, st1, _, hrun1, hpc1Br, hoth1, hpres1, hmem1⟩ := hbr
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize ((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl])) := by
      rw [hpc1Br, hcond]; simp only [Bool.false_eq_true, ↓reduceIte, lkm.totalSize_append, Asm.beq, Asm.br, lkm.totalSize_singleton]
    obtain ⟨hrun2, hpc2, ht4_2, hoth2, hmem2, hpres2⟩ :=
      run_lbu_zero_step env _ _ AbiReg.t4 AbiReg.t2 nonPreserved_t4 hl2 st1 hpc1'
    let st2 := stepReg st1 AbiReg.t4 (BitVec.zeroExtend 64 (st1.mem (st1.getReg AbiReg.t2)))
      (BitVec.ofNat 64 (4 * (lkm.totalSize ((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) + 1)))
    have halDst : isAligned (st2.getReg AbiReg.t1) 8 = true := by
      rw [hoth2 _ (by decide), hoth1 _ (by decide), ht1]
      exact isAligned8_add_mul8 _ (L.h64Align da) di.toNat
    have htwLbu : lkm.totalSize [Asm.lbu AbiReg.t4 AbiReg.t2] = 1 := by simp only [Asm.lbu, lkm.totalSize_instr]
    have hrun3 := step_sd_zero env _ _ AbiReg.t1 AbiReg.t4 hl3 st2
      (by rw [lkm.totalSize_append, htwLbu]; exact hpc2) halDst
    let st3 : State :=
      { pc := BitVec.ofNat 64 (4 * (lkm.totalSize (((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.lbu AbiReg.t4 AbiReg.t2]) + 1))
      , regs := st2.regs
      , mem := writeWord64 st2.mem (st2.getReg AbiReg.t1) (st2.getReg AbiReg.t4) }
    have htwSd : lkm.totalSize [Asm.sd AbiReg.t1 AbiReg.t4] = 1 := by simp only [Asm.sd, lkm.totalSize_instr]
    obtain ⟨hrun4, hpc4, ht1_4, hoth4, hmem4, hpres4⟩ :=
      run_aluImm_step env _ _ .addi AbiReg.t1 AbiReg.t1 8#12 nonPreserved_t1 hl4 st3
        (by rw [lkm.totalSize_append, htwSd])
    let st4 := stepReg st3 AbiReg.t1 (evalAluImm .addi (st3.getReg AbiReg.t1) 8#12)
      (BitVec.ofNat 64 (4 * (lkm.totalSize ((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.lbu AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) + 1)))
    have htwA1 : lkm.totalSize [Asm.addi AbiReg.t1 AbiReg.t1 8#12] = 1 := by simp only [Asm.addi, lkm.totalSize_instr]
    obtain ⟨hrun5, hpc5, ht2_5, hoth5, hmem5, hpres5⟩ :=
      run_aluImm_step env _ _ .addi AbiReg.t2 AbiReg.t2 1#12 nonPreserved_t2 hl5 st4
        (by rw [lkm.totalSize_append, htwA1]; exact hpc4)
    let st5 := stepReg st4 AbiReg.t2 (evalAluImm .addi (st4.getReg AbiReg.t2) 1#12)
      (BitVec.ofNat 64 (4 * (lkm.totalSize (((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.lbu AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) ++ [Asm.addi AbiReg.t1 AbiReg.t1 8#12]) + 1)))
    have htwA2 : lkm.totalSize [Asm.addi AbiReg.t2 AbiReg.t2 1#12] = 1 := by simp only [Asm.addi, lkm.totalSize_instr]
    obtain ⟨hrun6, hpc6, ht3_6, hoth6, hmem6, hpres6⟩ :=
      run_aluImm_step env _ _ .addi AbiReg.t3 AbiReg.t3 (-1#12) nonPreserved_t3 hl6 st5
        (by rw [lkm.totalSize_append, htwA2]; exact hpc5)
    let st6 := stepReg st5 AbiReg.t3 (evalAluImm .addi (st5.getReg AbiReg.t3) (-1#12))
      (BitVec.ofNat 64 (4 * (lkm.totalSize ((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.lbu AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) ++ [Asm.addi AbiReg.t1 AbiReg.t1 8#12]) ++ [Asm.addi AbiReg.t2 AbiReg.t2 1#12]) + 1)))
    have htwA3 : lkm.totalSize [Asm.addi AbiReg.t3 AbiReg.t3 (-1#12)] = 1 := by simp only [Asm.addi, lkm.totalSize_instr]
    have hpc64J : 4 * (lkm.totalSize (((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.lbu AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) ++ [Asm.addi AbiReg.t1 AbiReg.t1 8#12]) ++ [Asm.addi AbiReg.t2 AbiReg.t2 1#12]) ++ [Asm.addi AbiReg.t3 AbiReg.t3 (-1#12)]) + lkm.itemSize (.j loopLbl)) < 2 ^ 64 := by
      have h := linkResolved_sub_pc64 env _ [Asm.j loopLbl] _ hl7
      simpa [Asm.j, lkm.totalSize_singleton] using h
    obtain ⟨kJ, st7, hrun7, hpc7, hoth7, hpres7, hmem7⟩ :=
      prog_step_j env _ _ loopLbl loopTarget hloopLbl hl7 hpc64J st6
        (by rw [lkm.totalSize_append, htwA3]; exact hpc6)
    have ht4Val : st2.getReg AbiReg.t4 = (((lm.src8 src)[si.toNat]!).toUInt64).toBitVec := by
      have hget : (lm.src8 src)[si.toNat]! = (lm.src8 src)[si.toNat]'(by omega) := getElem!_pos _ _ (by omega)
      rw [ht4_2, hmem1]; change BitVec.zeroExtend 64 (st.mem (st1.getReg AbiReg.t2)) = _
      rw [hoth1 _ (by decide), ht2, bsrc_byte_at hm src hsrc si.toNat (by omega), hget]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.zeroExtend, BitVec.toNat_setWidth, UInt8.toNat_toBitVec, UInt64.toNat_toBitVec, UInt8.toNat_toUInt64,
          Nat.mod_eq_of_lt (Nat.lt_trans (UInt8.toNat_lt _) (by decide))]
    have ht1St2 : st2.getReg AbiReg.t1 = L.base64 da + BitVec.ofNat 64 (8 * di.toNat) := by
      rw [hoth2 _ (by decide), hoth1 _ (by decide)]; exact ht1
    have hst3Mem : st3.mem = writeWord64 st.mem (L.base64 da + BitVec.ofNat 64 (8 * di.toNat)) (((lm.src8 src)[si.toNat]!).toUInt64).toBitVec := by
      dsimp only [st3]; rw [hmem2, hmem1, ht1St2, ht4Val]
    have hst7Mem : st7.mem = st3.mem := by rw [hmem7, hmem6, hmem5, hmem4]
    have hdi1 : (di + 1).toNat = di.toNat + 1 := by
      have := L.h64Valid da
      simp [UInt64.toNat_add, Nat.mod_eq_of_lt (show di.toNat + 1 < 2 ^ 64 by omega)]
    have hsi1 : (si + 1).toNat = si.toNat + 1 := by
      simp [UInt64.toNat_add, Nat.mod_eq_of_lt (show si.toNat + 1 < 2 ^ 64 by omega)]
    have h8eq : sextImm12 8#12 = BitVec.ofNat 64 8 := by decide
    have h1eq : sextImm12 1#12 = BitVec.ofNat 64 1 := by decide
    have ht1_7 : st7.getReg AbiReg.t1 = L.base64 da + BitVec.ofNat 64 (8 * (di + 1).toNat) := by
      rw [hoth7 _ (by decide)]
      change st6.getReg AbiReg.t1 = _
      rw [hoth6 _ (by decide), hoth5 _ (by decide), ht1_4, evalAluImm]
      change st2.getReg AbiReg.t1 + sextImm12 8#12 = _
      rw [ht1St2, h8eq, BitVec.add_assoc, ← BitVec.ofNat_add, hdi1, show 8 * di.toNat + 8 = 8 * (di.toNat + 1) by omega]
    have ht2_7 : st7.getReg AbiReg.t2 = bsrcAddr env.tab L src + BitVec.ofNat 64 (si + 1).toNat := by
      rw [hoth7 _ (by decide)]
      change st6.getReg AbiReg.t2 = _
      rw [hoth6 _ (by decide), ht2_5, evalAluImm]
      change st4.getReg AbiReg.t2 + sextImm12 1#12 = _
      rw [hoth4 _ (by decide), show st3.getReg AbiReg.t2 = st2.getReg AbiReg.t2 from rfl,
          hoth2 _ (by decide), hoth1 _ (by decide),
          ht2, h1eq, BitVec.add_assoc, ← BitVec.ofNat_add, hsi1]
    have ht3_7 : st7.getReg AbiReg.t3 = BitVec.ofNat 64 n := by
      rw [hoth7 _ (by decide)]
      change st6.getReg AbiReg.t3 = _
      rw [ht3_6, evalAluImm]
      change st4.getReg AbiReg.t3 + sextImm12 (-1#12) = _
      rw [hoth4 _ (by decide), show st3.getReg AbiReg.t3 = st2.getReg AbiReg.t3 from rfl,
          hoth2 _ (by decide), hoth1 _ (by decide), ht3]
      exact BitVec.ofNat_sub_one_eq_add_neg1 hnBound
    let lm1 := lm.set64 da di ((lm.src8 src)[si.toNat]!).toUInt64
    have hm1 : ProgMemRel env.tab L st7.mem lm1 := by
      rw [hst7Mem, hst3Mem]; exact ProgMemRel.set64 hm da hda di _ (by omega)
    have hsrcEq : lm1.src8 src = lm.src8 src := by
      cases src <;> simp [lm1, _root_.L.Mem.src8, _root_.L.Mem.arr8, _root_.L.Mem.set64]
    have hdiSize : (di + 1).toNat + n ≤ (lm1.arr64 da).size := by
      rw [hdi1]; simp only [_root_.L.Mem.arr64] at hdi
      simp only [lm1, _root_.L.Mem.arr64, _root_.L.Mem.set64, ↓reduceIte, Array.size_set!]; omega
    have hsiSize : (si + 1).toNat + n ≤ (lm1.src8 src).size := by rw [hsrcEq, hsi1]; omega
    have hsz1 : (lm1.src8 src).size < 2 ^ 64 := by rw [hsrcEq]; exact hsz
    obtain ⟨kRest, stEnd, hrunRest, hpcEnd, hpresRest, hmEnd, hpmRest⟩ :=
      ih lm1 (di + 1) (si + 1) st7 hpc7
        ht1_7 ht2_7 ht3_7 hdiSize hsiSize hsz1 hm1
    have hpmStep : MemEqOutside (L.arr64Span da) st.mem st7.mem := by
      rw [hst7Mem, hst3Mem]
      exact memEqOutside_writeWord64_arr64 L da di.toNat (Nat.lt_of_lt_of_le (by omega) hcapD) st.mem _
    have hpresStep : PreservedRegs st st7 :=
      hpres1.trans (hpres2.trans ((preservedRegs_of_regs rfl : PreservedRegs st2 st3).trans
        (hpres4.trans (hpres5.trans (hpres6.trans hpres7)))))
    have hcopyEq : lm.copy8w da di (lm.src8 src) si (n + 1) = lm1.copy8w da (di + 1) (lm1.src8 src) (si + 1) n := by
      rw [hsrcEq]; rfl
    have hrunStep := run_trans (run_trans (run_trans (run_trans (run_trans (run_trans hrun1 hrun2) hrun3) hrun4) hrun5) hrun6) hrun7
    refine ⟨_, stEnd, run_trans hrunStep hrunRest, hpcEnd, hpresStep.trans hpresRest, ?_, hpmStep.trans hpmRest⟩
    · rw [hcopyEq]; exact hmEnd

theorem prog_copy8w_args_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (d : _root_.L.WArr) (di si n : _root_.L.Expr)
    (hdOk : warrOkB env.tab nl d = true) (hdiOk : exprOkB env.tab nl di = true)
    (hsiOk : exprOkB env.tab nl si = true) (hnOk : exprOkB env.tab nl n = true)
    (hnt : max (warrTemps d) (max (1 + maxTempsExpr di)
      (max (3 + maxTempsExpr si) (4 + max 1 (maxTempsExpr n)))) ≤ nt)
    (pre codeArgs post : List AsmItem)
    (hcodeArgs : codeArgs =
      (evalWArrTierToTemp env.tab nl 0 d).2 ++
      (compileE env.tab nl 1 di ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 1))) ++
      (compileE env.tab nl 3 si ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 3))) ++
      (compileE env.tab nl 4 n ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 4))))
    (hlink : lkm.linkSpec (pre ++ codeArgs ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOk L sp st.mem nl loc) :
    let dArr := (evalWArrTierToTemp env.tab nl 0 d).1
    match copy8wArgsEval d di si n { mem := lm, loc := loc } with
    | .ok ((da, vdi, vsi, vk), _) =>
      ∃ k st' du,
        RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize codeArgs)) ∧
        da = _root_.L.tierA dArr du ∧
        env.tab.wordPosOkB da = true ∧
        (L.T + (if (du &&& 1 == 0) = true then 0#64 else 8#64) + BitVec.ofInt 64 (env.tab.len64 (.t0 dArr)) =
          L.T + BitVec.ofInt 64 (env.tab.len64 da)) ∧
        (L.T + (if (du &&& 1 == 0) = true then 0#64 else 8#64) + BitVec.ofInt 64 (env.tab.base64 (.t0 dArr)) =
          L.T + BitVec.ofInt 64 (env.tab.base64 da)) ∧
        readWord64 st'.mem (sp + BitVec.ofInt 64 (slotOff nl)) = du.toBitVec ∧
        readWord64 st'.mem (sp + BitVec.ofInt 64 (slotOff (nl + 1))) = vdi.toBitVec ∧
        readWord64 st'.mem (sp + BitVec.ofInt 64 (slotOff (nl + 3))) = vsi.toBitVec ∧
        readWord64 st'.mem (sp + BitVec.ofInt 64 (slotOff (nl + 4))) = vk.toBitVec ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl 0 nt) st.mem st'.mem
    | .error _ =>
      ∃ k st',
        RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' := by
  let c0 := (evalWArrTierToTemp env.tab nl 0 d).2
  let c1 := compileE env.tab nl 1 di ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 1))
  let c3 := compileE env.tab nl 3 si ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 3))
  let c4 := compileE env.tab nl 4 n ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 4))
  have hcEq : codeArgs = c0 ++ c1 ++ c3 ++ c4 := by rw [hcodeArgs]
  rw [hcEq] at hlink
  have hlink0 : lkm.linkSpec (pre ++ c0 ++ (c1 ++ c3 ++ c4 ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
  have hw0 : 0 + max 1 (warrTemps d) ≤ nt := by
    have := Nat.le_trans (by omega : 4 + 1 ≤ 4 + max 1 (maxTempsExpr n)) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hnt)))
    have := Nat.le_trans (Nat.le_max_left _ _) hnt; omega
  have hsim0 := eval_warr_to_temp_sim env L lm loc hal hlim htop d hdOk hw0 pre _ hlink0 st hpc hgp hsp hm hf
  cases hdW : _root_.L.warr d { mem := lm, loc := loc } with
  | error err =>
    simp only [copy8wArgsEval, Bind.bind, StateT.bind, Except.bind, hdW] at hsim0 ⊢
    obtain ⟨k, st', hrun, hpc', hpres, _⟩ := hsim0; exact ⟨k, st', hrun, hpc', hpres⟩
  | ok r0 =>
    rcases r0 with ⟨da, st0'⟩
    have hst0' : st0' = { mem := lm, loc := loc } := by
      rcases warr_pure d { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
      · rw [hdW] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
      · rw [hdW] at herr; contradiction
    subst hst0'; rw [hdW] at hsim0
    obtain ⟨k0, st1, du, hrun0, hpc0, hdaEq, hdaOk, hdoLen, hdoBase, hslot0, hpres0, hout0⟩ := hsim0
    have hm1 := progMemRel_of_tempSpan env L hlim htop (Nat.zero_le nt) hout0 hm
    have hf1 := progFrameOk_of_tempSpan L htop (Nat.zero_le nt) hout0 hf
    let pre1 := pre ++ c0
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by rw [hpc0, lkm.totalSize_append pre c0]
    have hlink1 : lkm.linkSpec (pre1 ++ c1 ++ (c3 ++ c4 ++ post)) =
        .ok (env.code, env.labels) := by simpa [pre1, List.append_assoc] using hlink0
    have hw1 : 1 + max 1 (maxTempsExpr di) ≤ nt := by
      have h1 := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hnt)
      have h2 := Nat.le_trans (by omega : 4 + 1 ≤ 4 + max 1 (maxTempsExpr n)) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hnt)))
      omega
    have hsim1 := prog_evalToTemp_sim env L lm loc hal hlim htop di hdiOk hw1 pre1 _ hlink1 st1 hpc1' (hpres0.gp.trans hgp) (hpres0.sp.trans hsp) hm1 hf1
    cases hdiE : _root_.L.evalE di { mem := lm, loc := loc } with
    | error err =>
      simp only [copy8wArgsEval, Bind.bind, StateT.bind, Except.bind, hdW, hdiE] at hsim1 ⊢
      obtain ⟨k, st', hrun, hpc', hpres, _⟩ := hsim1
      exact ⟨_, st', run_trans hrun0 hrun, hpc', hpres0.trans hpres⟩
    | ok r1 =>
      rcases r1 with ⟨vdi, st1'⟩
      have hst1' : st1' = { mem := lm, loc := loc } := by
        rcases _root_.L.evalE_pure di { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
        · rw [hdiE] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
        · rw [hdiE] at herr; contradiction
      subst hst1'; rw [hdiE] at hsim1
      obtain ⟨k1, st2, hrun1, hpc1, hslot1, hpres1, hout1⟩ := hsim1
      have hm2 := progMemRel_of_tempSpan env L hlim htop (by omega : 1 ≤ nt) hout1 hm1
      have hf2 := progFrameOk_of_tempSpan L htop (by omega : 1 ≤ nt) hout1 hf1
      let pre2 := pre1 ++ c1
      have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) := by rw [hpc1, lkm.totalSize_append pre1 c1]
      have hlink2 : lkm.linkSpec (pre2 ++ c3 ++ (c4 ++ post)) =
          .ok (env.code, env.labels) := by simpa [pre2, List.append_assoc] using hlink1
      have hw3 : 3 + max 1 (maxTempsExpr si) ≤ nt := by
        have h1 := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hnt))
        have h2 := Nat.le_trans (by omega : 4 + 1 ≤ 4 + max 1 (maxTempsExpr n)) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hnt)))
        omega
      have hsim3 := prog_evalToTemp_sim env L lm loc hal hlim htop si hsiOk hw3 pre2 _ hlink2 st2 hpc2' ((hpres0.trans hpres1).gp.trans hgp) ((hpres0.trans hpres1).sp.trans hsp) hm2 hf2
      cases hsiE : _root_.L.evalE si { mem := lm, loc := loc } with
      | error err =>
        simp only [copy8wArgsEval, Bind.bind, StateT.bind, Except.bind, hdW, hdiE, hsiE] at hsim3 ⊢
        obtain ⟨k, st', hrun, hpc', hpres, _⟩ := hsim3
        exact ⟨_, st', run_trans (run_trans hrun0 hrun1) hrun, hpc', (hpres0.trans hpres1).trans hpres⟩
      | ok r3 =>
        rcases r3 with ⟨vsi, st3'⟩
        have hst3' : st3' = { mem := lm, loc := loc } := by
          rcases _root_.L.evalE_pure si { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
          · rw [hsiE] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
          · rw [hsiE] at herr; contradiction
        subst hst3'; rw [hsiE] at hsim3
        obtain ⟨k3, st3, hrun3, hpc3, hslot3, hpres3, hout3⟩ := hsim3
        have hm3 := progMemRel_of_tempSpan env L hlim htop (by omega : 3 ≤ nt) hout3 hm2
        have hf3 := progFrameOk_of_tempSpan L htop (by omega : 3 ≤ nt) hout3 hf2
        let pre3 := pre2 ++ c3
        have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre3) := by rw [hpc3, lkm.totalSize_append pre2 c3]
        have hlink3 : lkm.linkSpec (pre3 ++ c4 ++ post) =
            .ok (env.code, env.labels) := by simpa [pre3, List.append_assoc] using hlink2
        have hw4 : 4 + max 1 (maxTempsExpr n) ≤ nt :=
          Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hnt))
        have hsim4 := prog_evalToTemp_sim env L lm loc hal hlim htop n hnOk hw4 pre3 post hlink3 st3 hpc3' ((hpres0.trans (hpres1.trans hpres3)).gp.trans hgp) ((hpres0.trans (hpres1.trans hpres3)).sp.trans hsp) hm3 hf3
        cases hnE : _root_.L.evalE n { mem := lm, loc := loc } with
        | error err =>
          simp only [copy8wArgsEval, Bind.bind, StateT.bind, Except.bind, hdW, hdiE, hsiE, hnE] at hsim4 ⊢
          obtain ⟨k, st', hrun, hpc', hpres, _⟩ := hsim4
          exact ⟨_, st', run_trans (run_trans (run_trans hrun0 hrun1) hrun3) hrun, hpc',
            (hpres0.trans (hpres1.trans hpres3)).trans hpres⟩
        | ok r4 =>
          rcases r4 with ⟨vk, st4'⟩
          have hst4' : st4' = { mem := lm, loc := loc } := by
            rcases _root_.L.evalE_pure n { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
            · rw [hnE] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
            · rw [hnE] at herr; contradiction
          subst hst4'; rw [hnE] at hsim4
          obtain ⟨k4, st4, hrun4, hpc4, hslot4, hpres4, hout4⟩ := hsim4
          have hminiOk : copy8wArgsEval d di si n { mem := lm, loc := loc } =
              .ok ((da, vdi, vsi, vk), { mem := lm, loc := loc }) := by
            simp [copy8wArgsEval, Bind.bind, StateT.bind, Except.bind, hdW, hdiE, hsiE, hnE, Pure.pure, Except.pure, StateT.pure]
          rw [hminiOk]
          have hvalid : sp.toNat + 8 * (1 + nl + nt) ≤ 2 ^ 64 := Nat.le_trans htop L.hStackValid
          have hs0 : readWord64 st4.mem (sp + BitVec.ofInt 64 (slotOff nl)) = du.toBitVec := by
            have hz : nl + 0 = nl := Nat.add_zero nl
            rw [← hz, readWord64_slot_of_tempSpan (by omega : 0 < 4) (by omega) hvalid hout4,
                readWord64_slot_of_tempSpan (by omega : 0 < 3) (by omega) hvalid hout3,
                readWord64_slot_of_tempSpan (by omega : 0 < 1) (by omega) hvalid hout1, hz]
            exact hslot0
          have hs1 : readWord64 st4.mem (sp + BitVec.ofInt 64 (slotOff (nl + 1))) = vdi.toBitVec := by
            rw [readWord64_slot_of_tempSpan (by omega : 1 < 4) (by omega) hvalid hout4,
                readWord64_slot_of_tempSpan (by omega : 1 < 3) (by omega) hvalid hout3]
            exact hslot1
          have hs3 : readWord64 st4.mem (sp + BitVec.ofInt 64 (slotOff (nl + 3))) = vsi.toBitVec := by
            rw [readWord64_slot_of_tempSpan (by omega : 3 < 4) (by omega) hvalid hout4]
            exact hslot3
          have hout01 : MemEqOutside (tempSpan sp nl 0 nt) st.mem st2.mem :=
            hout0.trans (MemEqOutside.mono (tempSpan_mono (by omega : 0 ≤ 1) (by omega)) hout1)
          have hout03 : MemEqOutside (tempSpan sp nl 0 nt) st.mem st3.mem :=
            hout01.trans (MemEqOutside.mono (tempSpan_mono (by omega : 0 ≤ 3) (by omega)) hout3)
          have hout04 : MemEqOutside (tempSpan sp nl 0 nt) st.mem st4.mem :=
            hout03.trans (MemEqOutside.mono (tempSpan_mono (by omega : 0 ≤ 4) (by omega)) hout4)
          have hpcEq : lkm.totalSize pre3 + lkm.totalSize c4 = lkm.totalSize pre + lkm.totalSize codeArgs := by
            rw [lkm.totalSize_append pre2 c3, lkm.totalSize_append pre1 c1, lkm.totalSize_append pre c0,
                hcEq, lkm.totalSize_append ((c0 ++ c1) ++ c3) c4, lkm.totalSize_append (c0 ++ c1) c3,
                lkm.totalSize_append c0 c1]; omega
          refine ⟨_, st4, du, run_trans (run_trans (run_trans hrun0 hrun1) hrun3) hrun4,
            by rw [hpc4, hpcEq], hdaEq, hdaOk, hdoLen, hdoBase,
            hs0, hs1, hs3, hslot4, hpres0.trans (hpres1.trans (hpres3.trans hpres4)), hout04⟩

theorem prog_copy8w_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (d : _root_.L.WArr) (di : _root_.L.Expr) (src : _root_.L.BSrc) (si n : _root_.L.Expr)
    (hdOk : warrOkB env.tab nl d = true) (hdiOk : exprOkB env.tab nl di = true)
    (hsrcOk : bsrcOkB env.tab src = true) (hsiOk : exprOkB env.tab nl si = true)
    (hnOk : exprOkB env.tab nl n = true)
    (hnt : max (warrTemps d) (max (1 + maxTempsExpr di)
      (max (3 + maxTempsExpr si) (4 + max 1 (maxTempsExpr n)))) ≤ nt)
    (pfx : String) (lblId : Nat) (pre post : List AsmItem)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOk L sp st.mem nl loc)
    (hlink : lkm.linkSpec (pre ++ (compileS env.tab nl pfx lblId none "" (.copy8w d di src si n)).1 ++ post) =
      .ok (env.code, env.labels))
    (p : _root_.L.Prog) :
    let codeS := (compileS env.tab nl pfx lblId none "" (.copy8w d di src si n)).1
    match _root_.L.step p (fun _ => throw .outOfFuel) (.copy8w d di src si n) { mem := lm, loc := loc } with
    | .ok (_, st') =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize codeS)) ∧
        PreservedRegs st r' ∧
        ProgMemRel env.tab L r'.mem st'.mem ∧
        ProgFrameOk L sp r'.mem nl st'.loc ∧
        ProgMemOutside (FnWriteMask L sp nl nt) st.mem r'.mem
    | .error _ =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st r' := by
  let dArr := (evalWArrTierToTemp env.tab nl 0 d).1
  let loopLbl := s!"{pfx}_c8w_{lblId}"
  let doneLbl := s!"{pfx}_c8w_done_{lblId}"
  let codeArgs :=
    (evalWArrTierToTemp env.tab nl 0 d).2 ++
    (compileE env.tab nl 1 di ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 1))) ++
    (compileE env.tab nl 3 si ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 3))) ++
    (compileE env.tab nl 4 n ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 4)))
  let codeDst :=
    loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff nl) ++
    [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] ++
    loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (env.tab.len64 (.t0 dArr)) ++
    loadMemOff .ld AbiReg.t1 AbiReg.sp AbiReg.t6 (slotOff (nl + 1)) ++
    loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t6 (slotOff (nl + 4)) ++
    [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3, Asm.bltu AbiReg.t0 AbiReg.t1 errLabel] ++
    loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (env.tab.base64 (.t0 dArr)) ++
    [Asm.slli AbiReg.t1 AbiReg.t1 3#6, Asm.add AbiReg.t1 AbiReg.t5 AbiReg.t1]
  let srcSetup := bsrcSetup env.tab AbiReg.t5 AbiReg.t6 src
  let srcCheck :=
    loadMemOff .ld AbiReg.t2 AbiReg.sp AbiReg.t6 (slotOff (nl + 3)) ++
    [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3,
     Asm.bltu AbiReg.t0 AbiReg.t2 errLabel, Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2]
  let codeLoop :=
    [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl, Asm.lbu AbiReg.t4 AbiReg.t2 0#12,
     Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 1#12,
     Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl]
  have hcodeEq : (compileS env.tab nl pfx lblId none "" (.copy8w d di src si n)).1 =
      codeArgs ++ codeDst ++ srcSetup ++ srcCheck ++ codeLoop := by
    cases d <;> cases src <;>
      dsimp only [compileS, dArr, evalWArrTierToTemp, codeArgs, codeDst, srcSetup, bsrcSetup, srcCheck, codeLoop, loopLbl, doneLbl] <;>
      simp only [List.append_assoc] <;> rfl <;> rfl
  rw [hcodeEq] at hlink
  have hlink0 : lkm.linkSpec (pre ++ codeArgs ++ (codeDst ++ srcSetup ++ srcCheck ++ codeLoop ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
  have hargs := prog_copy8w_args_sim env L lm loc hal hlim htop d di si n hdOk hdiOk hsiOk hnOk hnt
    pre codeArgs (codeDst ++ srcSetup ++ srcCheck ++ codeLoop ++ post) rfl hlink0 st hpc hgp hsp hm hf
  cases hdaW : _root_.L.warr d { mem := lm, loc := loc } with
  | error err =>
    simp only [copy8wArgsEval, Bind.bind, StateT.bind, Except.bind, hdaW] at hargs
    have hstepErr : _root_.L.step p (fun _ => throw .outOfFuel) (.copy8w d di src si n) { mem := lm, loc := loc } = .error err := by
      simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hdaW]
    rw [hstepErr]; exact hargs
  | ok r0 =>
    rcases r0 with ⟨da, st0'⟩
    have hst0' : st0' = { mem := lm, loc := loc } := by
      rcases warr_pure d { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
      · rw [hdaW] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
      · rw [hdaW] at herr; cases herr
    rw [hst0'] at hdaW
    cases hdiE : _root_.L.evalE di { mem := lm, loc := loc } with
    | error err =>
      simp only [copy8wArgsEval, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE] at hargs
      have hstepErr : _root_.L.step p (fun _ => throw .outOfFuel) (.copy8w d di src si n) { mem := lm, loc := loc } = .error err := by
        simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE]
      rw [hstepErr]; exact hargs
    | ok r1 =>
      rcases r1 with ⟨vdi, st1'⟩
      have hst1' : st1' = { mem := lm, loc := loc } := by
        rcases _root_.L.evalE_pure di { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
        · rw [hdiE] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
        · rw [hdiE] at herr; cases herr
      rw [hst1'] at hdiE
      cases hsiE : _root_.L.evalE si { mem := lm, loc := loc } with
      | error err =>
        simp only [copy8wArgsEval, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE, hsiE] at hargs
        have hstepErr : _root_.L.step p (fun _ => throw .outOfFuel) (.copy8w d di src si n) { mem := lm, loc := loc } = .error err := by
          simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE, hsiE]
        rw [hstepErr]; exact hargs
      | ok r3 =>
        rcases r3 with ⟨vsi, st3'⟩
        have hst3' : st3' = { mem := lm, loc := loc } := by
          rcases _root_.L.evalE_pure si { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
          · rw [hsiE] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
          · rw [hsiE] at herr; cases herr
        rw [hst3'] at hsiE
        cases hnE : _root_.L.evalE n { mem := lm, loc := loc } with
        | error err =>
          simp only [copy8wArgsEval, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE, hsiE, hnE] at hargs
          have hstepErr : _root_.L.step p (fun _ => throw .outOfFuel) (.copy8w d di src si n) { mem := lm, loc := loc } = .error err := by
            simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE, hsiE, hnE]
          rw [hstepErr]; exact hargs
        | ok r4 =>
          rcases r4 with ⟨vk, st4'⟩
          have hst4' : st4' = { mem := lm, loc := loc } := by
            rcases _root_.L.evalE_pure n { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
            · rw [hnE] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
            · rw [hnE] at herr; cases herr
          rw [hst4'] at hnE
          have hargsEq : copy8wArgsEval d di si n { mem := lm, loc := loc } =
              .ok ((da, vdi, vsi, vk), { mem := lm, loc := loc }) := by
            simp [copy8wArgsEval, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE, hsiE, hnE, Pure.pure, Except.pure, StateT.pure]
          rw [hargsEq] at hargs
          obtain ⟨kA, st1, du, hrunA, hpc1, hdaEq, hdaOk, hdoLen, hdoBase,
            hs0, hs1, hs3, hs4, hpresA, houtA⟩ := hargs
          have hm1 := progMemRel_of_tempSpan env L hlim htop (Nat.zero_le nt) houtA hm
          have hf1 := progFrameOk_of_tempSpan L htop (Nat.zero_le nt) houtA hf
          have hpmA := progMemOutside_of_tempSpan L hlim htop (Nat.zero_le nt) houtA
          let pre1 := pre ++ codeArgs
          have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by rw [hpc1, lkm.totalSize_append pre codeArgs]
          have hlink1 : lkm.linkSpec (pre1 ++ codeDst ++ (srcSetup ++ srcCheck ++ codeLoop ++ post)) =
              .ok (env.code, env.labels) := by simpa [pre1, List.append_assoc] using hlink0
          have hdst := prog_warr_dst_setup_sim env L lm hal dArr du vdi vk da hdaOk
            (hdaEq ▸ hdoLen) (hdaEq ▸ hdoBase) pre1 codeDst (srcSetup ++ srcCheck ++ codeLoop ++ post) rfl
            st1 hpc1' (hpresA.gp.trans hgp) (hpresA.sp.trans hsp) hm1 hs0 hs1 hs4 hlink1
          have hstepOk : _root_.L.step p (fun _ => throw .outOfFuel) (.copy8w d di src si n) { mem := lm, loc := loc } =
              if vdi.toNat + vk.toNat ≤ (lm.arr64 da).size ∧ vsi.toNat + vk.toNat ≤ (lm.src8 src).size then
                .ok (Sig.normal, { mem := lm.copy8w da vdi (lm.src8 src) vsi vk.toNat, loc := loc })
              else .error .oob := by
            simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE, hsiE, hnE, get, getThe,
              MonadStateOf.get, StateT.get, set, MonadStateOf.set,
              throw, throwThe, MonadExceptOf.throw, Pure.pure, Except.pure]
            split <;> rfl
          rw [hstepOk]
          by_cases hbd : vdi.toNat + vk.toNat ≤ (lm.arr64 da).size
          · simp only [hbd, ↓reduceIte] at hdst
            obtain ⟨kD, st2, hrunD, hpc2, ht1_2, ht3_2, hmemD, hpresD⟩ := hdst
            let pre2 := pre1 ++ codeDst
            have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) := by rw [hpc2, lkm.totalSize_append pre1 codeDst]
            have hlink2 : lkm.linkSpec (pre2 ++ srcSetup ++ (srcCheck ++ codeLoop ++ post)) =
                .ok (env.code, env.labels) := by simpa [pre2, List.append_assoc] using hlink1
            obtain ⟨kB, st3, hrunB, hpc3, ht0_3, ht5_3, hlenLt, hothB, hmemB, hpresB⟩ :=
              bsrc_setup_sim env L lm src hsrcOk AbiReg.t5 AbiReg.t6 (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) (by decide)
                pre2 (srcCheck ++ codeLoop ++ post) hlink2 st2 hpc2' (hpresD.gp.trans (hpresA.gp.trans hgp)) (hmemD ▸ hm1)
            let pre3 := pre2 ++ srcSetup
            have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre3) := by rw [hpc3, lkm.totalSize_append pre2 srcSetup]
            have hlink3 : lkm.linkSpec (pre3 ++ srcCheck ++ (codeLoop ++ post)) =
                .ok (env.code, env.labels) := by simpa [pre3, List.append_assoc] using hlink2
            have ht1_3 : st3.getReg AbiReg.t1 = L.base64 da + BitVec.ofNat 64 (8 * vdi.toNat) :=
              (hothB _ (by decide) (by decide) (by decide)).trans ht1_2
            have ht3_3 : st3.getReg AbiReg.t3 = vk.toBitVec :=
              (hothB _ (by decide) (by decide) (by decide)).trans ht3_2
            have hchk := copy8w_src_check_sim env hal (lm.src8 src) hlenLt vsi vk
              (L.base64 da + BitVec.ofNat 64 (8 * vdi.toNat)) (bsrcAddr env.tab L src)
              pre3 srcCheck (codeLoop ++ post) rfl hlink3 st3 hpc3'
              (hpresB.sp.trans (hpresD.sp.trans (hpresA.sp.trans hsp))) ht0_3 ht1_3 ht3_3 ht5_3
              (by rw [hmemB, hmemD]; exact hs3)
            by_cases hbs : vsi.toNat + vk.toNat ≤ (lm.src8 src).size
            · simp only [hbd, hbs, and_self, ↓reduceIte] at hchk ⊢
              obtain ⟨kC, st4, hrunC, hpc4, ht1_4, ht2_4, ht3_4, hmemC, hpresC⟩ := hchk
              let pre4 := pre3 ++ srcCheck
              have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre4) := by rw [hpc4, lkm.totalSize_append pre3 srcCheck]
              have hlink4 : lkm.linkSpec (pre4 ++ codeLoop ++ post) =
                  .ok (env.code, env.labels) := by simpa [pre4, List.append_assoc] using hlink3
              have hloopLbl := lookupLabel_of_lbl_lm lkm pre4
                ([Asm.beq AbiReg.t3 AbiReg.zero doneLbl, Asm.lbu AbiReg.t4 AbiReg.t2 0#12,
                  Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
                  Asm.addi AbiReg.t2 AbiReg.t2 1#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12),
                  Asm.j loopLbl, Asm.lbl doneLbl] ++ post) loopLbl
                (by simpa [codeLoop, List.append_assoc] using hlink4)
              have hdoneLbl := lookupLabel_of_lbl_lm lkm
                (pre4 ++ [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl, Asm.lbu AbiReg.t4 AbiReg.t2 0#12,
                  Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
                  Asm.addi AbiReg.t2 AbiReg.t2 1#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl])
                post doneLbl (by simpa [codeLoop, List.append_assoc] using hlink4)
              have htwDone : lkm.totalSize codeLoop =
                  lkm.totalSize [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
                    Asm.lbu AbiReg.t4 AbiReg.t2 0#12, Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
                    Asm.addi AbiReg.t2 AbiReg.t2 1#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl] := by
                rw [show codeLoop = [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
                  Asm.lbu AbiReg.t4 AbiReg.t2 0#12, Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
                  Asm.addi AbiReg.t2 AbiReg.t2 1#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl] ++ [Asm.lbl doneLbl] by simp [codeLoop]]
                simp only [lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero]
              have hdoneTgt : lkm.totalSize (pre4 ++ [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
                  Asm.lbu AbiReg.t4 AbiReg.t2 0#12, Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
                  Asm.addi AbiReg.t2 AbiReg.t2 1#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl]) =
                  lkm.totalSize pre4 + lkm.totalSize codeLoop := by
                rw [lkm.totalSize_append, ← htwDone]
              have hlinkL : lkm.linkSpec (pre4 ++ [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
                  Asm.lbu AbiReg.t4 AbiReg.t2, Asm.sd AbiReg.t1 AbiReg.t4, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
                  Asm.addi AbiReg.t2 AbiReg.t2 1#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl,
                  Asm.lbl doneLbl] ++ post) = .ok (env.code, env.labels) := by
                simpa [codeLoop, Asm.lbu, Asm.sd, List.append_assoc] using hlink4
              have hloop := copy8w_loop_sim env L da hdaOk src hsrcOk loopLbl doneLbl
                (lkm.totalSize pre4) (lkm.totalSize pre4 + lkm.totalSize codeLoop) hloopLbl (by rw [← hdoneTgt]; exact hdoneLbl) pre4 post rfl hlinkL
                vk.toNat lm vdi vsi st4 hpc4' ht1_4 ht2_4 (by rw [ht3_4, u64_toBitVec_eq_ofNat]) hbd hbs hlenLt
                (hmemC ▸ hmemB ▸ hmemD ▸ hm1)
              obtain ⟨kL, r', hrunL, hpcR, hpresL, hmR, hmeqL⟩ := hloop
              have hmeqL' : MemEqOutside (L.arr64Span da) st1.mem r'.mem := by
                rw [← hmemD, ← hmemB, ← hmemC]; exact hmeqL
              have hpmL' : ProgMemOutside (FnWriteMask L sp nl nt) st1.mem r'.mem :=
                ProgMemOutside.of_memEqOutside (fun _ hc => Or.inr (Or.inr (Or.inr ⟨da, hdaOk, hc⟩))) hmeqL'
              have hfR := progFrameOk_of_disj_stack L hlim htop (L.arr64Span da) (L.arr64Span_valid da)
                (L.h64DisjStack da hdaOk) hmeqL' hf1
              have hpcEq : lkm.totalSize pre4 + lkm.totalSize codeLoop = lkm.totalSize pre + lkm.totalSize (codeArgs ++ codeDst ++ srcSetup ++ srcCheck ++ codeLoop) := by
                rw [lkm.totalSize_append pre3 srcCheck, lkm.totalSize_append pre2 srcSetup, lkm.totalSize_append pre1 codeDst,
                    lkm.totalSize_append pre codeArgs,
                    lkm.totalSize_append (((codeArgs ++ codeDst) ++ srcSetup) ++ srcCheck) codeLoop,
                    lkm.totalSize_append ((codeArgs ++ codeDst) ++ srcSetup) srcCheck,
                    lkm.totalSize_append (codeArgs ++ codeDst) srcSetup, lkm.totalSize_append codeArgs codeDst]; omega
              exact ⟨_, r', run_trans (run_trans (run_trans (run_trans hrunA hrunD) hrunB) hrunC) hrunL,
                by rw [hpcR, hpcEq, ← hcodeEq], hpresA.trans (hpresD.trans (hpresB.trans (hpresC.trans hpresL))), hmR, hfR, hpmA.trans hpmL'⟩
            · simp only [hbd, hbs, and_false, ↓reduceIte] at hchk ⊢
              obtain ⟨kC, r', hrunC, hpcR, hpresC⟩ := hchk
              exact ⟨_, r', run_trans (run_trans (run_trans hrunA hrunD) hrunB) hrunC, hpcR,
                hpresA.trans (hpresD.trans (hpresB.trans hpresC))⟩
          · simp only [hbd, false_and, ↓reduceIte] at hdst ⊢
            obtain ⟨kD, r', hrunD, hpcR, hpresD⟩ := hdst
            exact ⟨_, r', run_trans hrunA hrunD, hpcR, hpresA.trans hpresD⟩

theorem scanN_le_end (bs : Array UInt8) (c : List UInt8) (i e : Nat) (h : i ≤ e) :
    _root_.L.scanN bs c i e ≤ e := by
  unfold _root_.L.scanN
  split
  · split
    · exact h
    · exact scanN_le_end bs c (i + 1) e ‹_›
  · exact h
termination_by e - i

theorem scan8_loop_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (src : _root_.L.BSrc) (hsrc : bsrcOkB env.tab src = true)
    (c : List UInt8) (hcLen : 256 ≤ c.length) (hcOk : env.tab.romSliceOkB c = true)
    (ve : _root_.L.Word) (hveSize : ve.toNat ≤ (lm.src8 src).size) (hlenLt : (lm.src8 src).size < 2 ^ 64)
    (loopLbl doneLbl : String) (loopTarget doneTarget : Nat)
    (hloopLbl : lookupLabel env.labels loopLbl = some loopTarget)
    (hdoneLbl : lookupLabel env.labels doneLbl = some doneTarget)
    (pre post : List AsmItem)
    (hltLoop : loopTarget = lkm.totalSize pre)
    (hlink : lkm.linkSpec (pre ++ [Asm.lbl loopLbl, Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl,
      Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3, Asm.lbu AbiReg.t4 AbiReg.t4 0#12,
      Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4, Asm.lbu AbiReg.t5 AbiReg.t5 0#12,
      Asm.bne AbiReg.t5 AbiReg.zero doneLbl, Asm.addi AbiReg.t3 AbiReg.t3 1#12,
      Asm.j loopLbl, Asm.lbl doneLbl] ++ post) = .ok (env.code, env.labels)) :
    ∀ rem i (st : State),
      i + rem = ve.toNat →
      st.pc = BitVec.ofNat 64 (4 * loopTarget) →
      st.getReg AbiReg.a0 = ve.toBitVec →
      st.getReg AbiReg.t1 = bsrcAddr env.tab L src →
      st.getReg AbiReg.t2 = L.T + BitVec.ofNat 64 (env.tab.romBase.toNat + romIdx c env.tab.rom) →
      st.getReg AbiReg.t3 = BitVec.ofNat 64 i →
      ProgMemRel env.tab L st.mem lm →
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * doneTarget) ∧
        r'.getReg AbiReg.t3 = BitVec.ofNat 64 (_root_.L.scanN (lm.src8 src) c i ve.toNat) ∧
        r'.mem = st.mem ∧
        PreservedRegs st r' := by
  intro rem
  induction rem with
  | zero =>
    intro i st hiRem hpc ha0 ht1 ht2 ht3 hm
    have ⟨_, hl1⟩ := linkResolved_mid_split lkm pre [Asm.lbl loopLbl] _ post hlink
    have ⟨hlBge, _⟩ := linkResolved_mid_split lkm (pre ++ [Asm.lbl loopLbl]) [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl] _ post hl1
    have hbr := run_br_step env (pre ++ [Asm.lbl loopLbl]) _ .bgeu AbiReg.t3 AbiReg.a0 doneLbl doneTarget hdoneLbl (by decide)
      hlBge st (by rw [lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero, ← hltLoop]; exact hpc)
    have hcond : evalBranch .bgeu (st.getReg AbiReg.t3) (st.getReg AbiReg.a0) = true := by
      rw [ht3, ha0, u64_toBitVec_eq_ofNat]
      rw [evalBranch_bgeu_nat (a := i) (b := ve.toNat) (by omega) (by simpa using ve.toBitVec.isLt), decide_eq_true_iff]; omega
    obtain ⟨kBr, st', _, hrun, hpcBr, hothBr, hpresBr, hmemBr⟩ := hbr
    have hpc' : st'.pc = BitVec.ofNat 64 (4 * doneTarget) := by rw [hpcBr, hcond]; rfl
    have hscan : _root_.L.scanN (lm.src8 src) c i ve.toNat = i := by
      have hnot : ¬(i < ve.toNat) := by omega
      unfold _root_.L.scanN; simp only [hnot, ↓reduceIte]
    exact ⟨kBr, st', hrun, hpc', by rw [hscan, hothBr _ (by decide)]; exact ht3, hmemBr, hpresBr⟩
  | succ rem ih =>
    intro i st hiRem hpc ha0 ht1 ht2 ht3 hm
    have hltLoopEq : lkm.totalSize (pre ++ [Asm.lbl loopLbl]) = loopTarget := by
      rw [lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero, hltLoop]
    have ⟨_, hlR0⟩ := linkResolved_mid_split lkm pre [Asm.lbl loopLbl] _ post hlink
    have ⟨hl1, hlR1⟩ := linkResolved_mid_split lkm (pre ++ [Asm.lbl loopLbl]) [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl]
      [Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3, Asm.lbu AbiReg.t4 AbiReg.t4 0#12,
       Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4, Asm.lbu AbiReg.t5 AbiReg.t5 0#12,
       Asm.bne AbiReg.t5 AbiReg.zero doneLbl, Asm.addi AbiReg.t3 AbiReg.t3 1#12, Asm.j loopLbl, Asm.lbl doneLbl] post hlR0
    have ⟨hl2, hlR2⟩ := linkResolved_mid_split lkm ((pre ++ [Asm.lbl loopLbl]) ++ [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl])
      [Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3]
      [Asm.lbu AbiReg.t4 AbiReg.t4 0#12, Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4, Asm.lbu AbiReg.t5 AbiReg.t5 0#12,
       Asm.bne AbiReg.t5 AbiReg.zero doneLbl, Asm.addi AbiReg.t3 AbiReg.t3 1#12, Asm.j loopLbl, Asm.lbl doneLbl] post hlR1
    have ⟨hl3, hlR3⟩ := linkResolved_mid_split lkm (((pre ++ [Asm.lbl loopLbl]) ++ [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl]) ++ [Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3])
      [Asm.lbu AbiReg.t4 AbiReg.t4 0#12]
      [Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4, Asm.lbu AbiReg.t5 AbiReg.t5 0#12,
       Asm.bne AbiReg.t5 AbiReg.zero doneLbl, Asm.addi AbiReg.t3 AbiReg.t3 1#12, Asm.j loopLbl, Asm.lbl doneLbl] post hlR2
    have ⟨hl4, hlR4⟩ := linkResolved_mid_split lkm ((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl]) ++ [Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3]) ++ [Asm.lbu AbiReg.t4 AbiReg.t4 0#12])
      [Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4]
      [Asm.lbu AbiReg.t5 AbiReg.t5 0#12, Asm.bne AbiReg.t5 AbiReg.zero doneLbl, Asm.addi AbiReg.t3 AbiReg.t3 1#12, Asm.j loopLbl, Asm.lbl doneLbl] post hlR3
    have ⟨hl5, hlR5⟩ := linkResolved_mid_split lkm (((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl]) ++ [Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3]) ++ [Asm.lbu AbiReg.t4 AbiReg.t4 0#12]) ++ [Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4])
      [Asm.lbu AbiReg.t5 AbiReg.t5 0#12] [Asm.bne AbiReg.t5 AbiReg.zero doneLbl, Asm.addi AbiReg.t3 AbiReg.t3 1#12, Asm.j loopLbl, Asm.lbl doneLbl] post hlR4
    have ⟨hl6, hlR6⟩ := linkResolved_mid_split lkm ((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl]) ++ [Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3]) ++ [Asm.lbu AbiReg.t4 AbiReg.t4 0#12]) ++ [Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4]) ++ [Asm.lbu AbiReg.t5 AbiReg.t5 0#12])
      [Asm.bne AbiReg.t5 AbiReg.zero doneLbl] [Asm.addi AbiReg.t3 AbiReg.t3 1#12, Asm.j loopLbl, Asm.lbl doneLbl] post hlR5
    have ⟨hl7, hlR7⟩ := linkResolved_mid_split lkm (((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl]) ++ [Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3]) ++ [Asm.lbu AbiReg.t4 AbiReg.t4 0#12]) ++ [Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4]) ++ [Asm.lbu AbiReg.t5 AbiReg.t5 0#12]) ++ [Asm.bne AbiReg.t5 AbiReg.zero doneLbl])
      [Asm.addi AbiReg.t3 AbiReg.t3 1#12] [Asm.j loopLbl, Asm.lbl doneLbl] post hlR6
    have ⟨hl8, _⟩ := linkResolved_mid_split lkm ((((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl]) ++ [Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3]) ++ [Asm.lbu AbiReg.t4 AbiReg.t4 0#12]) ++ [Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4]) ++ [Asm.lbu AbiReg.t5 AbiReg.t5 0#12]) ++ [Asm.bne AbiReg.t5 AbiReg.zero doneLbl]) ++ [Asm.addi AbiReg.t3 AbiReg.t3 1#12])
      [Asm.j loopLbl] [Asm.lbl doneLbl] post hlR7
    have hbr := run_br_step env (pre ++ [Asm.lbl loopLbl]) _ .bgeu AbiReg.t3 AbiReg.a0 doneLbl doneTarget hdoneLbl (by decide)
      hl1 st (by rw [hltLoopEq]; exact hpc)
    have hcond : evalBranch .bgeu (st.getReg AbiReg.t3) (st.getReg AbiReg.a0) = false := by
      rw [ht3, ha0, u64_toBitVec_eq_ofNat]
      rw [evalBranch_bgeu_nat (a := i) (b := ve.toNat) (by omega) (by simpa using ve.toBitVec.isLt), decide_eq_false_iff_not]; omega
    obtain ⟨kBr, st1, _, hrun1, hpc1Br, hoth1, hpres1, hmem1⟩ := hbr
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize ((pre ++ [Asm.lbl loopLbl]) ++ [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl])) := by
      rw [hpc1Br, hcond]; simp only [Bool.false_eq_true, ↓reduceIte, lkm.totalSize_append, Asm.bgeu, Asm.br, lkm.totalSize_singleton]
    let st2 := stepReg st1 AbiReg.t4 (evalAlu .add (st1.getReg AbiReg.t1) (st1.getReg AbiReg.t3))
      (BitVec.ofNat 64 (4 * (lkm.totalSize ((pre ++ [Asm.lbl loopLbl]) ++ [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl]) + 1)))
    obtain ⟨hrun2, hpc2, ht4_2, hoth2, hmem2, hpres2⟩ :=
      run_alu_step env _ _ .add AbiReg.t4 AbiReg.t1 AbiReg.t3 nonPreserved_t4 hl2 st1 hpc1'
    have htwAdd1 : lkm.totalSize [Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3] = 1 := by simp only [Asm.add, lkm.totalSize_instr]
    obtain ⟨hrun3, hpc3, ht4_3, hoth3, hmem3, hpres3⟩ :=
      run_lbu_zero_step env _ _ AbiReg.t4 AbiReg.t4 nonPreserved_t4 hl3 st2
        (by rw [lkm.totalSize_append, htwAdd1]; exact hpc2)
    let st3 := stepReg st2 AbiReg.t4 (BitVec.zeroExtend 64 (st2.mem (st2.getReg AbiReg.t4)))
      (BitVec.ofNat 64 (4 * (lkm.totalSize (((pre ++ [Asm.lbl loopLbl]) ++ [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl]) ++ [Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3]) + 1)))
    have htwLbu1 : lkm.totalSize [Asm.lbu AbiReg.t4 AbiReg.t4 0#12] = 1 := by simp only [Asm.lbu, lkm.totalSize_instr]
    let st4 := stepReg st3 AbiReg.t5 (evalAlu .add (st3.getReg AbiReg.t2) (st3.getReg AbiReg.t4))
      (BitVec.ofNat 64 (4 * (lkm.totalSize ((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl]) ++ [Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3]) ++ [Asm.lbu AbiReg.t4 AbiReg.t4 0#12]) + 1)))
    obtain ⟨hrun4, hpc4, ht5_4, hoth4, hmem4, hpres4⟩ :=
      run_alu_step env _ _ .add AbiReg.t5 AbiReg.t2 AbiReg.t4 nonPreserved_t5 hl4 st3
        (by rw [lkm.totalSize_append, htwLbu1]; exact hpc3)
    have htwAdd2 : lkm.totalSize [Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4] = 1 := by simp only [Asm.add, lkm.totalSize_instr]
    obtain ⟨hrun5, hpc5, ht5_5, hoth5, hmem5, hpres5⟩ :=
      run_lbu_zero_step env _ _ AbiReg.t5 AbiReg.t5 nonPreserved_t5 hl5 st4
        (by rw [lkm.totalSize_append, htwAdd2]; exact hpc4)
    let st5 := stepReg st4 AbiReg.t5 (BitVec.zeroExtend 64 (st4.mem (st4.getReg AbiReg.t5)))
      (BitVec.ofNat 64 (4 * (lkm.totalSize (((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl]) ++ [Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3]) ++ [Asm.lbu AbiReg.t4 AbiReg.t4 0#12]) ++ [Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4]) + 1)))
    have htwLbu2 : lkm.totalSize [Asm.lbu AbiReg.t5 AbiReg.t5 0#12] = 1 := by simp only [Asm.lbu, lkm.totalSize_instr]
    have hpc5' : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize ((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl]) ++ [Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3]) ++ [Asm.lbu AbiReg.t4 AbiReg.t4 0#12]) ++ [Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4]) ++ [Asm.lbu AbiReg.t5 AbiReg.t5 0#12])) := by
      rw [lkm.totalSize_append, htwLbu2]; exact hpc5
    have hbr2 := run_br_step env _ _ .bne AbiReg.t5 AbiReg.zero doneLbl doneTarget hdoneLbl (by decide) hl6 st5 hpc5'
    let bval := (lm.src8 src)[i]!
    have hgetB : (lm.src8 src)[i]! = (lm.src8 src)[i]'(by omega) := getElem!_pos _ _ (by omega)
    have hbval : bval = (lm.src8 src)[i]'(by omega) := hgetB
    have ht4Val : st3.getReg AbiReg.t4 = BitVec.ofNat 64 bval.toNat := by
      have haddr : st2.getReg AbiReg.t4 = bsrcAddr env.tab L src + BitVec.ofNat 64 i := by
        rw [ht4_2, evalAlu]
        change st1.getReg AbiReg.t1 + st1.getReg AbiReg.t3 = _
        rw [hoth1 _ (by decide), hoth1 _ (by decide), ht1, ht3]
      rw [ht4_3, hmem2, hmem1]; change BitVec.zeroExtend 64 (st.mem (st2.getReg AbiReg.t4)) = _
      rw [haddr, bsrc_byte_at hm src hsrc i (by omega), ← hbval]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.zeroExtend, BitVec.toNat_setWidth, UInt8.toNat_toBitVec, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (Nat.lt_trans (UInt8.toNat_lt _) (by decide : 2 ^ 8 < 2 ^ 64))]
    have hromSpec := Tab.romSliceOk_spec hcOk
    let cval := c[bval.toNat]!
    have hbvLt : bval.toNat < c.length := Nat.lt_of_lt_of_le (UInt8.toNat_lt bval) hcLen
    have hgetC : c[bval.toNat]! = c[bval.toNat]'hbvLt := getElem!_pos c bval.toNat hbvLt
    have ht5Val : st5.getReg AbiReg.t5 = BitVec.zeroExtend 64 cval.toBitVec := by
      rw [ht5_5, hmem4, hmem3, hmem2, hmem1]; change BitVec.zeroExtend 64 (st.mem (st4.getReg AbiReg.t5)) = _
      rw [ht5_4, evalAlu, hoth3 _ (by decide), hoth2 _ (by decide), hoth1 _ (by decide),
          ht2, ht4Val, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc,
          hm.2.2.1 (romIdx c env.tab.rom + bval.toNat) (by omega)]
      have hrom_eq := hromSpec.2 bval.toNat hbvLt
      rw [List.getElem?_eq_getElem (by omega : romIdx c env.tab.rom + bval.toNat < env.tab.rom.length),
          Option.some.injEq] at hrom_eq
      dsimp only [cval]
      rw [hrom_eq, hgetC]
    have ht3_5 : st5.getReg AbiReg.t3 = BitVec.ofNat 64 i :=
      (hoth5 _ (by decide)).trans ((hoth4 _ (by decide)).trans ((hoth3 _ (by decide)).trans ((hoth2 _ (by decide)).trans ((hoth1 _ (by decide)).trans ht3))))
    have hmem5 : st5.mem = st.mem := hmem4.trans (hmem3.trans (hmem2.trans hmem1))
    have hpres05 : PreservedRegs st st5 :=
      hpres1.trans (hpres2.trans (hpres3.trans (hpres4.trans hpres5)))
    have hrun15 := run_trans (run_trans (run_trans hrun1 hrun2) hrun3) (run_trans hrun4 hrun5)
    by_cases hcz : cval ≠ 0
    · have hbneT : evalBranch .bne (st5.getReg AbiReg.t5) (st5.getReg AbiReg.zero) = true := by
        rw [ht5Val, getReg_zero]; simp only [evalBranch, bne_iff_ne, ne_eq]
        intro heq
        have hnat := congrArg BitVec.toNat heq
        rw [BitVec.zeroExtend, BitVec.toNat_setWidth, UInt8.toNat_toBitVec,
            Nat.mod_eq_of_lt (Nat.lt_trans (UInt8.toNat_lt _) (by decide : 2 ^ 8 < 2 ^ 64)),
            show (0#64 : BitVec 64).toNat = 0 from rfl] at hnat
        exact hcz (by rcases cval with ⟨bv⟩; congr; exact BitVec.eq_of_toNat_eq (by simpa using hnat))
      obtain ⟨_, st6, _, hrun6, hpc6Br, hoth6Br, hpres6Br, hmem6Br⟩ := hbr2
      have hpc6' : st6.pc = BitVec.ofNat 64 (4 * doneTarget) := by rw [hpc6Br, hbneT]; rfl
      have hscan : _root_.L.scanN (lm.src8 src) c i ve.toNat = i := by
        have hlt : i < ve.toNat := by omega
        dsimp only [cval, bval] at hcz
        unfold _root_.L.scanN; simp only [eq_true hlt, eq_true hcz, ↓reduceIte]
      refine ⟨_, st6, run_trans hrun15 hrun6, hpc6', by rw [hscan, hoth6Br _ (by decide)]; exact ht3_5,
        hmem6Br.trans hmem5, hpres05.trans hpres6Br⟩
    · have hc0 : cval = 0 := Classical.not_not.mp hcz
      have hbneF : evalBranch .bne (st5.getReg AbiReg.t5) (st5.getReg AbiReg.zero) = false := by
        rw [ht5Val, hc0, getReg_zero]; decide
      obtain ⟨_, st6, _, hrun6, hpc6Br, hoth6Br, hpres6Br, hmem6Br⟩ := hbr2
      have hpc6' : st6.pc = BitVec.ofNat 64 (4 * lkm.totalSize (((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl]) ++ [Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3]) ++ [Asm.lbu AbiReg.t4 AbiReg.t4 0#12]) ++ [Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4]) ++ [Asm.lbu AbiReg.t5 AbiReg.t5 0#12]) ++ [Asm.bne AbiReg.t5 AbiReg.zero doneLbl])) := by
        rw [hpc6Br, hbneF]; simp only [Bool.false_eq_true, ↓reduceIte, lkm.totalSize_append, Asm.bne, Asm.br, lkm.totalSize_singleton]
      obtain ⟨hrun7, hpc7, ht3_7, hoth7, hmem7, hpres7⟩ :=
        run_aluImm_step env _ _ .addi AbiReg.t3 AbiReg.t3 1#12 nonPreserved_t3 hl7 st6 hpc6'
      let st7 := stepReg st6 AbiReg.t3 (evalAluImm .addi (st6.getReg AbiReg.t3) 1#12)
        (BitVec.ofNat 64 (4 * (lkm.totalSize (((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl]) ++ [Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3]) ++ [Asm.lbu AbiReg.t4 AbiReg.t4 0#12]) ++ [Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4]) ++ [Asm.lbu AbiReg.t5 AbiReg.t5 0#12]) ++ [Asm.bne AbiReg.t5 AbiReg.zero doneLbl]) + 1)))
      have htwAddi : lkm.totalSize [Asm.addi AbiReg.t3 AbiReg.t3 1#12] = 1 := by simp only [Asm.addi, lkm.totalSize_instr]
      have hpc64J : 4 * (lkm.totalSize ((((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl]) ++ [Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3]) ++ [Asm.lbu AbiReg.t4 AbiReg.t4 0#12]) ++ [Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4]) ++ [Asm.lbu AbiReg.t5 AbiReg.t5 0#12]) ++ [Asm.bne AbiReg.t5 AbiReg.zero doneLbl]) ++ [Asm.addi AbiReg.t3 AbiReg.t3 1#12]) + lkm.itemSize (.j loopLbl)) < 2 ^ 64 := by
        have h := linkResolved_sub_pc64 env _ [Asm.j loopLbl] _ hl8
        simpa [Asm.j, lkm.totalSize_singleton] using h
      obtain ⟨kJ, st8, hrun8, hpc8, hoth8, hpres8, hmem8⟩ :=
        prog_step_j env _ _ loopLbl loopTarget hloopLbl hl8 hpc64J st7
          (by rw [lkm.totalSize_append, htwAddi]; exact hpc7)
      have ha0_8 : st8.getReg AbiReg.a0 = ve.toBitVec := by
        rw [hoth8 _ (by decide)]
        change st7.getReg AbiReg.a0 = _
        rw [hoth7 _ (by decide), hoth6Br _ (by decide)]
        change st5.getReg AbiReg.a0 = _
        rw [hoth5 _ (by decide), hoth4 _ (by decide), hoth3 _ (by decide), hoth2 _ (by decide), hoth1 _ (by decide)]
        exact ha0
      have ht1_8 : st8.getReg AbiReg.t1 = bsrcAddr env.tab L src := by
        rw [hoth8 _ (by decide)]
        change st7.getReg AbiReg.t1 = _
        rw [hoth7 _ (by decide), hoth6Br _ (by decide)]
        change st5.getReg AbiReg.t1 = _
        rw [hoth5 _ (by decide), hoth4 _ (by decide), hoth3 _ (by decide), hoth2 _ (by decide), hoth1 _ (by decide)]
        exact ht1
      have ht2_8 : st8.getReg AbiReg.t2 = L.T + BitVec.ofNat 64 (env.tab.romBase.toNat + romIdx c env.tab.rom) := by
        rw [hoth8 _ (by decide)]
        change st7.getReg AbiReg.t2 = _
        rw [hoth7 _ (by decide), hoth6Br _ (by decide)]
        change st5.getReg AbiReg.t2 = _
        rw [hoth5 _ (by decide), hoth4 _ (by decide), hoth3 _ (by decide), hoth2 _ (by decide), hoth1 _ (by decide)]
        exact ht2
      have ht3_8 : st8.getReg AbiReg.t3 = BitVec.ofNat 64 (i + 1) := by
        rw [hoth8 _ (by decide)]
        change st7.getReg AbiReg.t3 = _
        rw [ht3_7, evalAluImm, hoth6Br _ (by decide)]
        change st5.getReg AbiReg.t3 + sextImm12 1#12 = _
        rw [ht3_5, show sextImm12 1#12 = BitVec.ofNat 64 1 from by decide, ← BitVec.ofNat_add]
      have hmem08 : st8.mem = st.mem := hmem8.trans (hmem7.trans (hmem6Br.trans hmem5))
      obtain ⟨kRest, stEnd, hrunRest, hpcEnd, ht3End, hmemEnd, hpresRest⟩ :=
        ih (i + 1) st8 (by omega) hpc8 ha0_8 ht1_8 ht2_8 ht3_8 (hmem08 ▸ hm)
      have hscan : _root_.L.scanN (lm.src8 src) c i ve.toNat = _root_.L.scanN (lm.src8 src) c (i + 1) ve.toNat := by
        have hlt : i < ve.toNat := by omega
        dsimp only [cval, bval] at hcz
        conv => lhs; unfold _root_.L.scanN
        simp only [eq_true hlt, eq_false hcz, ↓reduceIte]
      have hrunStep := run_trans hrun15 (run_trans (run_trans hrun6 hrun7) hrun8)
      refine ⟨_, stEnd, run_trans hrunStep hrunRest, hpcEnd, by rw [hscan]; exact ht3End,
        hmemEnd.trans hmem08, (hpres05.trans (hpres6Br.trans (hpres7.trans hpres8))).trans hpresRest⟩

theorem prog_scan8_check_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (src : _root_.L.BSrc) (c : List UInt8) (_hcOk : env.tab.romSliceOkB c = true)
    (vi ve : _root_.L.Word) (hlenLt : (lm.src8 src).size < 2 ^ 64)
    (pre codeCheck post : List AsmItem)
    (hcodeCheck : codeCheck =
      [Asm.bltu AbiReg.a0 AbiReg.t3 errLabel, Asm.bltu AbiReg.t0 AbiReg.a0 errLabel] ++
      addImmOff AbiReg.t2 AbiReg.gp AbiReg.t5 (env.tab.romBase + (romIdx c env.tab.rom : Int)))
    (hlink : lkm.linkSpec (pre ++ codeCheck ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T)
    (ht0 : st.getReg AbiReg.t0 = BitVec.ofNat 64 (lm.src8 src).size)
    (ht1 : st.getReg AbiReg.t1 = bsrcAddr env.tab L src)
    (ht3 : st.getReg AbiReg.t3 = vi.toBitVec) (ha0 : st.getReg AbiReg.a0 = ve.toBitVec) :
    if vi ≤ ve ∧ ve.toNat ≤ (lm.src8 src).size then
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize codeCheck)) ∧
        r'.getReg AbiReg.a0 = ve.toBitVec ∧
        r'.getReg AbiReg.t1 = bsrcAddr env.tab L src ∧
        r'.getReg AbiReg.t2 = L.T + BitVec.ofNat 64 (env.tab.romBase.toNat + romIdx c env.tab.rom) ∧
        r'.getReg AbiReg.t3 = BitVec.ofNat 64 vi.toNat ∧
        r'.mem = st.mem ∧
        PreservedRegs st r'
    else
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st r' := by
  let cb0 := [Asm.bltu AbiReg.a0 AbiReg.t3 errLabel]
  let cb1 := [Asm.bltu AbiReg.t0 AbiReg.a0 errLabel]
  let sadd := addImmOff AbiReg.t2 AbiReg.gp AbiReg.t5 (env.tab.romBase + (romIdx c env.tab.rom : Int))
  have hcEq : codeCheck = cb0 ++ cb1 ++ sadd := by rw [hcodeCheck]; simp [cb0, cb1, sadd]
  rw [hcEq] at hlink
  have hlink0 : lkm.linkSpec (pre ++ cb0 ++ (cb1 ++ sadd ++ post)) = .ok (env.code, env.labels) := by
    simpa [List.append_assoc] using hlink
  have hbr0 := run_br_step env pre _ .bltu AbiReg.a0 AbiReg.t3 errLabel env.errTarget env.herrLbl (by decide) hlink0 st hpc
  have hcond0 : evalBranch .bltu (st.getReg AbiReg.a0) (st.getReg AbiReg.t3) =
      decide (ve.toNat < vi.toNat) := by
    rw [ha0, ht3, u64_toBitVec_eq_ofNat, u64_toBitVec_eq_ofNat]
    exact evalBranch_bltu_nat ve.toBitVec.isLt vi.toBitVec.isLt
  by_cases hvevi : vi ≤ ve
  · have hviNat : vi.toNat ≤ ve.toNat := hvevi
    have hbr0F : evalBranch .bltu (st.getReg AbiReg.a0) (st.getReg AbiReg.t3) = false := by
      rw [hcond0, decide_eq_false_iff_not]; omega
    obtain ⟨_, st1, _, hrun0, hpc1Br, hoth0Br, hpres0Br, hmem0Br⟩ := hbr0
    let pre1 := pre ++ cb0
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by
      rw [hpc1Br, hbr0F]; simp only [Bool.false_eq_true, ↓reduceIte]
      exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (lkm.totalSize_append pre cb0).symm
    have hlink1 : lkm.linkSpec (pre1 ++ cb1 ++ (sadd ++ post)) = .ok (env.code, env.labels) := by
      simpa [pre1, List.append_assoc] using hlink0
    have hbr1 := run_br_step env pre1 _ .bltu AbiReg.t0 AbiReg.a0 errLabel env.errTarget env.herrLbl (by decide) hlink1 st1 hpc1'
    have hcond1 : evalBranch .bltu (st1.getReg AbiReg.t0) (st1.getReg AbiReg.a0) =
        decide ((lm.src8 src).size < ve.toNat) := by
      rw [hoth0Br _ (by decide), hoth0Br _ (by decide), ht0, ha0, u64_toBitVec_eq_ofNat]
      exact evalBranch_bltu_nat hlenLt ve.toBitVec.isLt
    by_cases hvesz : ve.toNat ≤ (lm.src8 src).size
    · simp only [hvevi, hvesz, and_self, ↓reduceIte]
      have hbr1F : evalBranch .bltu (st1.getReg AbiReg.t0) (st1.getReg AbiReg.a0) = false := by
        rw [hcond1, decide_eq_false_iff_not]; omega
      obtain ⟨_, st2, _, hrun1, hpc2Br, hoth1Br, hpres1Br, hmem1Br⟩ := hbr1
      let pre2 := pre1 ++ cb1
      have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) := by
        rw [hpc2Br, hbr1F]; simp only [Bool.false_eq_true, ↓reduceIte]
        exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (lkm.totalSize_append pre1 cb1).symm
      have hlink2 : lkm.linkSpec (pre2 ++ sadd ++ post) = .ok (env.code, env.labels) := by
        simpa [pre2, List.append_assoc] using hlink1
      obtain ⟨st3, hrun2, hoth2, ht2_3, hmem2, hpc3⟩ :=
        addImmOff_correct_lm lkm env.hrom pre2 post AbiReg.t2 AbiReg.gp AbiReg.t5
          (by decide) (by decide) (by decide) (env.tab.romBase + (romIdx c env.tab.rom : Int))
          hlink2 (linkResolved_sub_pc64 env pre2 sadd post hlink2) st2 hpc2'
      have hpres2 : PreservedRegs st2 st3 :=
        ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
         hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide)⟩
      have hrb_nn : 0 ≤ env.tab.romBase := ProgLayout.romBase_nonneg env.tab
      have hcoe : (env.tab.romBase + (romIdx c env.tab.rom : Int)) =
          ((env.tab.romBase.toNat + romIdx c env.tab.rom : Nat) : Int) := by
        rw [← Int.toNat_of_nonneg hrb_nn]; push_cast; rfl
      have ht2Val : st3.getReg AbiReg.t2 = L.T + BitVec.ofNat 64 (env.tab.romBase.toNat + romIdx c env.tab.rom) := by
        rw [ht2_3, hoth1Br _ (by decide), hoth0Br _ (by decide), hgp, hcoe]; rfl
      have hpcEq : lkm.totalSize pre2 + lkm.totalSize sadd = lkm.totalSize pre + lkm.totalSize codeCheck := by
        rw [show pre2 = pre1 ++ cb1 from rfl, lkm.totalSize_append,
            show pre1 = pre ++ cb0 from rfl, lkm.totalSize_append, hcEq,
            lkm.totalSize_append (cb0 ++ cb1) sadd, lkm.totalSize_append cb0 cb1]; omega
      refine ⟨_, st3, run_trans (run_trans hrun0 hrun1) hrun2, by rw [hpc3, hpcEq],
        (hoth2 _ (by decide) (by decide)).trans ((hoth1Br _ (by decide)).trans ((hoth0Br _ (by decide)).trans ha0)),
        (hoth2 _ (by decide) (by decide)).trans ((hoth1Br _ (by decide)).trans ((hoth0Br _ (by decide)).trans ht1)),
        ht2Val,
        by rw [hoth2 _ (by decide) (by decide), hoth1Br _ (by decide), hoth0Br _ (by decide), ht3, u64_toBitVec_eq_ofNat],
        by rw [hmem2, hmem1Br, hmem0Br],
        hpres0Br.trans (hpres1Br.trans hpres2)⟩
    · simp only [hvevi, hvesz, and_false, ↓reduceIte]
      have hbr1T : evalBranch .bltu (st1.getReg AbiReg.t0) (st1.getReg AbiReg.a0) = true := by
        rw [hcond1, decide_eq_true_iff]; omega
      obtain ⟨_, st2, _, hrun1, hpc2Br, _, hpres1Br, _⟩ := hbr1
      have hpc2' : st2.pc = BitVec.ofNat 64 (4 * env.errTarget) := by rw [hpc2Br, hbr1T]; rfl
      exact ⟨_, st2, run_trans hrun0 hrun1, hpc2', hpres0Br.trans hpres1Br⟩
  · have hviNat : ¬(vi.toNat ≤ ve.toNat) := hvevi
    simp only [hvevi, false_and, ↓reduceIte]
    have hbr0T : evalBranch .bltu (st.getReg AbiReg.a0) (st.getReg AbiReg.t3) = true := by
      rw [hcond0, decide_eq_true_iff]; omega
    obtain ⟨_, st1, _, hrun0, hpc1Br, _, hpres0Br, _⟩ := hbr0
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * env.errTarget) := by rw [hpc1Br, hbr0T]; rfl
    exact ⟨_, st1, hrun0, hpc1', hpres0Br⟩

theorem prog_scan8_tail_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (x : _root_.L.Var) (hx : x < nl) (src : _root_.L.BSrc) (hsrcOk : bsrcOkB env.tab src = true)
    (c : List UInt8) (hcLen : 256 ≤ c.length) (hcOk : env.tab.romSliceOkB c = true)
    (vi ve : _root_.L.Word) (hcond : vi ≤ ve ∧ ve.toNat ≤ (lm.src8 src).size) (hlenLt : (lm.src8 src).size < 2 ^ 64)
    (pfx : String) (lblId : Nat) (pre5 post : List AsmItem)
    (st5 : State) (hpc5 : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre5))
    (hsp5 : st5.getReg AbiReg.sp = sp)
    (ha0_5 : st5.getReg AbiReg.a0 = ve.toBitVec) (ht1_5 : st5.getReg AbiReg.t1 = bsrcAddr env.tab L src)
    (ht2_5 : st5.getReg AbiReg.t2 = L.T + BitVec.ofNat 64 (env.tab.romBase.toNat + romIdx c env.tab.rom))
    (ht3_5 : st5.getReg AbiReg.t3 = BitVec.ofNat 64 vi.toNat)
    (hm5 : ProgMemRel env.tab L st5.mem lm) (hf5 : ProgFrameOk L sp st5.mem nl loc)
    (hlink5 : lkm.linkSpec (pre5 ++ ([Asm.lbl s!"{pfx}_scan_{lblId}",
      Asm.bgeu AbiReg.t3 AbiReg.a0 s!"{pfx}_scan_done_{lblId}",
      Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3, Asm.lbu AbiReg.t4 AbiReg.t4 0#12,
      Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4, Asm.lbu AbiReg.t5 AbiReg.t5 0#12,
      Asm.bne AbiReg.t5 AbiReg.zero s!"{pfx}_scan_done_{lblId}", Asm.addi AbiReg.t3 AbiReg.t3 1#12,
      Asm.j s!"{pfx}_scan_{lblId}", Asm.lbl s!"{pfx}_scan_done_{lblId}"] ++
      storeMemOff .sd AbiReg.sp AbiReg.t3 AbiReg.t5 (slotOff x)) ++ post) = .ok (env.code, env.labels)) :
    let codeTail := [Asm.lbl s!"{pfx}_scan_{lblId}",
      Asm.bgeu AbiReg.t3 AbiReg.a0 s!"{pfx}_scan_done_{lblId}",
      Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3, Asm.lbu AbiReg.t4 AbiReg.t4 0#12,
      Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4, Asm.lbu AbiReg.t5 AbiReg.t5 0#12,
      Asm.bne AbiReg.t5 AbiReg.zero s!"{pfx}_scan_done_{lblId}", Asm.addi AbiReg.t3 AbiReg.t3 1#12,
      Asm.j s!"{pfx}_scan_{lblId}", Asm.lbl s!"{pfx}_scan_done_{lblId}"] ++
      storeMemOff .sd AbiReg.sp AbiReg.t3 AbiReg.t5 (slotOff x)
    ∃ k r',
      RV64.run env.rom k st5 = .cont r' ∧
      r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre5 + lkm.totalSize codeTail)) ∧
      PreservedRegs st5 r' ∧
      ProgMemRel env.tab L r'.mem lm ∧
      ProgFrameOk L sp r'.mem nl
        (({ mem := lm, loc := loc } : _root_.L.St).setLoc x
          (UInt64.ofNat (_root_.L.scanN (lm.src8 src) c vi.toNat ve.toNat))).loc ∧
      ProgMemOutside (FnWriteMask L sp nl nt) st5.mem r'.mem := by
  let loopLbl := s!"{pfx}_scan_{lblId}"
  let doneLbl := s!"{pfx}_scan_done_{lblId}"
  let codeLoop := [Asm.lbl loopLbl, Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl,
    Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3, Asm.lbu AbiReg.t4 AbiReg.t4 0#12,
    Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4, Asm.lbu AbiReg.t5 AbiReg.t5 0#12,
    Asm.bne AbiReg.t5 AbiReg.zero doneLbl, Asm.addi AbiReg.t3 AbiReg.t3 1#12,
    Asm.j loopLbl, Asm.lbl doneLbl]
  let csX := storeMemOff .sd AbiReg.sp AbiReg.t3 AbiReg.t5 (slotOff x)
  have hlink5' : lkm.linkSpec (pre5 ++ codeLoop ++ (csX ++ post)) = .ok (env.code, env.labels) := by
    simpa [codeLoop, csX, loopLbl, doneLbl, List.append_assoc] using hlink5
  have hloopLbl := lookupLabel_of_lbl_lm lkm pre5
    ([Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl, Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3,
      Asm.lbu AbiReg.t4 AbiReg.t4 0#12, Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4,
      Asm.lbu AbiReg.t5 AbiReg.t5 0#12, Asm.bne AbiReg.t5 AbiReg.zero doneLbl,
      Asm.addi AbiReg.t3 AbiReg.t3 1#12, Asm.j loopLbl, Asm.lbl doneLbl] ++ (csX ++ post)) loopLbl
    (by simpa [codeLoop, List.append_assoc] using hlink5')
  have hdoneLbl := lookupLabel_of_lbl_lm lkm
    (pre5 ++ [Asm.lbl loopLbl, Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl, Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3,
      Asm.lbu AbiReg.t4 AbiReg.t4 0#12, Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4,
      Asm.lbu AbiReg.t5 AbiReg.t5 0#12, Asm.bne AbiReg.t5 AbiReg.zero doneLbl,
      Asm.addi AbiReg.t3 AbiReg.t3 1#12, Asm.j loopLbl]) (csX ++ post) doneLbl
    (by simpa [codeLoop, List.append_assoc] using hlink5')
  have htwDone : lkm.totalSize codeLoop = lkm.totalSize [Asm.lbl loopLbl, Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl,
      Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3, Asm.lbu AbiReg.t4 AbiReg.t4 0#12,
      Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4, Asm.lbu AbiReg.t5 AbiReg.t5 0#12,
      Asm.bne AbiReg.t5 AbiReg.zero doneLbl, Asm.addi AbiReg.t3 AbiReg.t3 1#12, Asm.j loopLbl] := by
    rw [show codeLoop = [Asm.lbl loopLbl, Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl,
      Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3, Asm.lbu AbiReg.t4 AbiReg.t4 0#12,
      Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4, Asm.lbu AbiReg.t5 AbiReg.t5 0#12,
      Asm.bne AbiReg.t5 AbiReg.zero doneLbl, Asm.addi AbiReg.t3 AbiReg.t3 1#12, Asm.j loopLbl] ++ [Asm.lbl doneLbl] by simp [codeLoop]]
    simp only [lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero]
  have hdoneTgt : lkm.totalSize (pre5 ++ [Asm.lbl loopLbl, Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl,
      Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3, Asm.lbu AbiReg.t4 AbiReg.t4 0#12,
      Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4, Asm.lbu AbiReg.t5 AbiReg.t5 0#12,
      Asm.bne AbiReg.t5 AbiReg.zero doneLbl, Asm.addi AbiReg.t3 AbiReg.t3 1#12, Asm.j loopLbl]) =
      lkm.totalSize pre5 + lkm.totalSize codeLoop := by
    rw [lkm.totalSize_append, ← htwDone]
  have hviLe : vi.toNat ≤ ve.toNat := hcond.1
  have hloop := scan8_loop_sim env L lm src hsrcOk c hcLen hcOk ve hcond.2 hlenLt
    loopLbl doneLbl (lkm.totalSize pre5) (lkm.totalSize pre5 + lkm.totalSize codeLoop) hloopLbl (by rw [← hdoneTgt]; exact hdoneLbl)
    pre5 (csX ++ post) rfl hlink5' (ve.toNat - vi.toNat) vi.toNat st5 (by omega) hpc5 ha0_5 ht1_5 ht2_5 ht3_5 hm5
  obtain ⟨kL, st6, hrunL, hpc6, ht3_6, hmemL, hpresL⟩ := hloop
  let pre6 := pre5 ++ codeLoop
  have hpc6' : st6.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre6) := by rw [hpc6, lkm.totalSize_append pre5 codeLoop]
  have hlink6 : lkm.linkSpec (pre6 ++ csX ++ post) = .ok (env.code, env.labels) := by
    simpa [pre6, List.append_assoc] using hlink5'
  have hsp6 : st6.getReg AbiReg.sp = sp := hpresL.sp.trans hsp5
  have halS : isAligned (st6.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff x)) 8 = true := by
    rw [hsp6]; exact isAligned8_add_int_mul8 sp hal (1 + x)
  obtain ⟨st7, hrunS, hothS, hmemS, hpc7⟩ :=
    storeMemOff_sd_correct_lm lkm env.hrom pre6 post AbiReg.sp AbiReg.t3 AbiReg.t5
      (by decide) (by decide) (by decide) (slotOff x) hlink6
      (linkResolved_sub_pc64 env pre6 csX post hlink6) st6 hpc6' halS
  have hpresS : PreservedRegs st6 st7 :=
    ⟨hothS _ (by decide), hothS _ (by decide), hothS _ (by decide), hothS _ (by decide)⟩
  have hsp6w : st7.mem = writeWord64 st6.mem (sp + BitVec.ofInt 64 (slotOff x))
      (UInt64.ofNat (_root_.L.scanN (lm.src8 src) c vi.toNat ve.toNat)).toBitVec := by
    rw [hmemS, hsp6, ht3_6]; rfl
  have hslotSub : (slotSpan sp (1 + x)).sub (frameSpan sp nl nt) :=
    slotSpan_sub_frame (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hx 1) (Nat.le_add_right _ _))
  have houtX : MemEqOutside (slotSpan sp (1 + x)) st6.mem st7.mem := by
    rw [hsp6w]; exact MemEqOutside.writeWord64 _ _ _ fun k hk => ⟨k, hk, by simp [slotSpan, slotAddr, slotOff_ofInt]⟩
  have hm7 : ProgMemRel env.tab L st7.mem lm :=
    ProgMemRel.of_stack_eqOutside (MemSpan.sub_trans hslotSub (L.frame_sub_stackSpan hlim htop)) houtX (hmemL ▸ hm5)
  have hf6 : ProgFrameOk L sp st6.mem nl loc := by rw [hmemL]; exact hf5
  have hf7 : ProgFrameOk L sp st7.mem nl
      (({ mem := lm, loc := loc } : _root_.L.St).setLoc x (UInt64.ofNat (_root_.L.scanN (lm.src8 src) c vi.toNat ve.toNat))).loc := by
    rw [hsp6w]
    exact ProgFrameOk.of_setLoc L (by simp only [MemSpan.valid, frameSpan]; exact Nat.le_trans htop L.hStackValid) x hx _ hf6
  have hpmS : ProgMemOutside (FnWriteMask L sp nl nt) st5.mem st7.mem := by
    rw [← hmemL]
    apply ProgMemOutside.of_memEqOutside _ houtX
    intro a ha
    refine Or.inl ⟨L.frame_sub_stackSpan hlim htop a (hslotSub a ha), Or.inr ?_⟩
    rcases ha with ⟨k, hk, rfl⟩
    dsimp only [slotSpan, slotAddr] at hk ⊢
    have hsp64 : sp.toNat + 8 * (1 + nl + nt) ≤ 2 ^ 64 := Nat.le_trans htop L.hStackValid
    have h8x : 8 * (1 + x) + k < 8 * (1 + nl + nt) := by
      have h1 : 8 * (1 + x) ≤ 8 * nl := by rw [Nat.add_comm]; exact Nat.mul_le_mul_left 8 (Nat.succ_le_of_lt hx)
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _) (Nat.le_trans (Nat.add_le_add_right h1 8) (by
        rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]; have := Nat.mul_le_mul_left 8 (Nat.le_add_right nl nt); omega))
    have h8x64 : 8 * (1 + x) + k < 2 ^ 64 := Nat.lt_of_lt_of_le h8x (by omega)
    have hsp8x64 : sp.toNat + (8 * (1 + x) + k) < 2 ^ 64 := Nat.lt_of_lt_of_le (Nat.add_lt_add_left h8x sp.toNat) hsp64
    have hadd : (sp + BitVec.ofNat 64 (8 * (1 + x) + k)).toNat = sp.toNat + 8 * (1 + x) + k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h8x64, Nat.mod_eq_of_lt hsp8x64]; omega
    rw [show sp + BitVec.ofNat 64 (8 * (1 + x)) + BitVec.ofNat 64 k = sp + BitVec.ofNat 64 (8 * (1 + x) + k) from by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add], hadd]
    have h8x_ge : 8 ≤ 8 * (1 + x) + k :=
      Nat.le_trans (by decide : 8 ≤ 8 * 1) (Nat.le_trans (Nat.mul_le_mul_left 8 (Nat.le_add_right 1 x)) (Nat.le_add_right _ k))
    rw [Nat.add_assoc]
    exact ⟨Nat.add_le_add_left h8x_ge sp.toNat, Nat.add_lt_add_left h8x sp.toNat⟩
  refine ⟨_, st7, run_trans hrunL hrunS, ?_, hpresL.trans hpresS, hm7, hf7, hpmS⟩
  rw [hpc7, lkm.totalSize_append pre5 codeLoop, lkm.totalSize_append codeLoop csX, Nat.add_assoc]

theorem prog_scan8_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (x : _root_.L.Var) (hx : x < nl) (src : _root_.L.BSrc) (hsrcOk : bsrcOkB env.tab src = true)
    (i e : _root_.L.Expr) (hiOk : exprOkB env.tab nl i = true) (heOk : exprOkB env.tab nl e = true)
    (c : List UInt8) (hcLen : 256 ≤ c.length) (hcOk : env.tab.romSliceOkB c = true)
    (hnt : max (maxTempsExpr i) (1 + maxTempsExpr e) ≤ nt)
    (pfx : String) (lblId : Nat) (pre post : List AsmItem)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOk L sp st.mem nl loc)
    (hlink : lkm.linkSpec (pre ++ (compileS env.tab nl pfx lblId none "" (.scan8 x src i e c)).1 ++ post) =
      .ok (env.code, env.labels))
    (p : _root_.L.Prog) :
    let codeS := (compileS env.tab nl pfx lblId none "" (.scan8 x src i e c)).1
    match _root_.L.step p (fun _ => throw .outOfFuel) (.scan8 x src i e c) { mem := lm, loc := loc } with
    | .ok (_, st') =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize codeS)) ∧
        PreservedRegs st r' ∧
        ProgMemRel env.tab L r'.mem st'.mem ∧
        ProgFrameOk L sp r'.mem nl st'.loc ∧
        ProgMemOutside (FnWriteMask L sp nl nt) st.mem r'.mem
    | .error _ =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st r' := by
  let loopLbl := s!"{pfx}_scan_{lblId}"
  let doneLbl := s!"{pfx}_scan_done_{lblId}"
  let ci := compileE env.tab nl 0 i ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff nl)
  let ce := compileE env.tab nl 1 e
  let clVi := loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t5 (slotOff nl)
  let srcSetup := bsrcSetup env.tab AbiReg.t1 AbiReg.t5 src
  let codeCheck := [Asm.bltu AbiReg.a0 AbiReg.t3 errLabel, Asm.bltu AbiReg.t0 AbiReg.a0 errLabel] ++
    addImmOff AbiReg.t2 AbiReg.gp AbiReg.t5 (env.tab.romBase + (romIdx c env.tab.rom : Int))
  let codeLoop := [Asm.lbl loopLbl, Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl,
    Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3, Asm.lbu AbiReg.t4 AbiReg.t4 0#12,
    Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4, Asm.lbu AbiReg.t5 AbiReg.t5 0#12,
    Asm.bne AbiReg.t5 AbiReg.zero doneLbl, Asm.addi AbiReg.t3 AbiReg.t3 1#12,
    Asm.j loopLbl, Asm.lbl doneLbl]
  let csX := storeMemOff .sd AbiReg.sp AbiReg.t3 AbiReg.t5 (slotOff x)
  have hcodeEq : (compileS env.tab nl pfx lblId none "" (.scan8 x src i e c)).1 =
      ci ++ ce ++ clVi ++ srcSetup ++ codeCheck ++ (codeLoop ++ csX) := by
    cases src <;> simp [compileS, ci, ce, clVi, srcSetup, bsrcSetup, codeCheck, codeLoop, csX, loopLbl, doneLbl, List.append_assoc]
  rw [hcodeEq] at hlink
  have hlink0 : lkm.linkSpec (pre ++ ci ++ (ce ++ clVi ++ srcSetup ++ codeCheck ++ (codeLoop ++ csX) ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
  have hsim0 := prog_evalToTemp_sim env L lm loc hal hlim htop i hiOk (by omega) pre _ hlink0 st hpc hgp hsp hm hf
  cases hiE : _root_.L.evalE i { mem := lm, loc := loc } with
  | error err =>
    simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hiE] at hsim0 ⊢
    obtain ⟨k, r', hrun, hpc', hpres, _⟩ := hsim0; exact ⟨k, r', hrun, hpc', hpres⟩
  | ok r0 =>
    rcases r0 with ⟨vi, st0'⟩
    have hst0' : st0' = { mem := lm, loc := loc } := by
      rcases _root_.L.evalE_pure i { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
      · rw [hiE] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
      · rw [hiE] at herr; contradiction
    subst hst0'; rw [hiE] at hsim0
    obtain ⟨k0, st1, hrun0, hpc0, hslot0, hpres0, hout0⟩ := hsim0
    have hm1 := progMemRel_of_tempSpan env L hlim htop (Nat.zero_le nt) hout0 hm
    have hf1 := progFrameOk_of_tempSpan L htop (Nat.zero_le nt) hout0 hf
    have hpm0 := progMemOutside_of_tempSpan L hlim htop (Nat.zero_le nt) hout0
    let pre1 := pre ++ ci
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by
      simpa [pre1, ci, Nat.add_zero, lkm.totalSize_append] using hpc0
    have hlink1 : lkm.linkSpec (pre1 ++ ce ++ (clVi ++ srcSetup ++ codeCheck ++ (codeLoop ++ csX) ++ post)) =
        .ok (env.code, env.labels) := by simpa [pre1, List.append_assoc] using hlink0
    have hpcE := linkResolved_sub_pc64 env pre1 ce _ hlink1
    have hsim1 := progEvalExpr_sim env L lm loc hal hlim htop e pre1 _ 1 heOk (by omega) hlink1 hpcE st1
      hpc1' (hpres0.gp.trans hgp) (hpres0.sp.trans hsp) hm1 hf1
    cases heE : _root_.L.evalE e { mem := lm, loc := loc } with
    | error err =>
      simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hiE, heE] at hsim1 ⊢
      obtain ⟨k, r', hrun, hpc', hpres, _⟩ := hsim1
      exact ⟨_, r', run_trans hrun0 hrun, hpc', hpres0.trans hpres⟩
    | ok r1 =>
      rcases r1 with ⟨ve, st1'⟩
      have hst1' : st1' = { mem := lm, loc := loc } := by
        rcases _root_.L.evalE_pure e { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
        · rw [heE] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
        · rw [heE] at herr; contradiction
      subst hst1'; rw [heE] at hsim1
      obtain ⟨k1, st2, hrun1, hpc1, ha0_2, hpres1, hout1⟩ := hsim1
      have hm2 := progMemRel_of_tempSpan env L hlim htop (by omega : 1 ≤ nt) hout1 hm1
      have hf2 := progFrameOk_of_tempSpan L htop (by omega : 1 ≤ nt) hout1 hf1
      have hpm1 := progMemOutside_of_tempSpan L hlim htop (by omega : 1 ≤ nt) hout1
      have hslot0_2 : readWord64 st2.mem (sp + BitVec.ofInt 64 (slotOff nl)) = vi.toBitVec := by
        have hvalid := Nat.le_trans htop L.hStackValid
        have hz : nl + 0 = nl := Nat.add_zero nl
        rw [← hz, readWord64_slot_of_tempSpan (by omega : 0 < 1) (by omega) hvalid hout1, hz]; exact hslot0
      let pre2 := pre1 ++ ce
      have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) := by rw [hpc1, lkm.totalSize_append pre1 ce]
      have hlink2 : lkm.linkSpec (pre2 ++ clVi ++ (srcSetup ++ codeCheck ++ (codeLoop ++ csX) ++ post)) =
          .ok (env.code, env.labels) := by simpa [pre2, List.append_assoc] using hlink1
      have halX : isAligned (st2.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff nl)) 8 = true := by
        rw [hpres1.sp.trans (hpres0.sp.trans hsp)]; exact isAligned8_add_int_mul8 sp hal (1 + nl)
      obtain ⟨st3, hrun2, hoth2, ht3_3, hmem2, hpc3⟩ :=
        loadMemOff_ld_correct_lm lkm env.hrom pre2 _ AbiReg.t3 AbiReg.sp AbiReg.t5
          (by decide) (by decide) (by decide) (slotOff nl) hlink2
          (linkResolved_sub_pc64 env pre2 clVi _ hlink2) st2 hpc2' halX
      have hpres2 : PreservedRegs st2 st3 :=
        ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
         hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide)⟩
      let pre3 := pre2 ++ clVi
      have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre3) := by rw [hpc3, lkm.totalSize_append pre2 clVi]
      have hlink3 : lkm.linkSpec (pre3 ++ srcSetup ++ (codeCheck ++ (codeLoop ++ csX) ++ post)) =
          .ok (env.code, env.labels) := by simpa [pre3, List.append_assoc] using hlink2
      obtain ⟨kB, st4, hrunB, hpc4, ht0_4, ht1_4, hlenLt, hothB, hmemB, hpresB⟩ :=
        bsrc_setup_sim env L lm src hsrcOk AbiReg.t1 AbiReg.t5 (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)
          pre3 (codeCheck ++ (codeLoop ++ csX) ++ post) hlink3 st3 hpc3'
          (hpres2.gp.trans (hpres1.gp.trans (hpres0.gp.trans hgp))) (hmem2 ▸ hm2)
      let pre4 := pre3 ++ srcSetup
      have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre4) := by rw [hpc4, lkm.totalSize_append pre3 srcSetup]
      have hlink4 : lkm.linkSpec (pre4 ++ codeCheck ++ ((codeLoop ++ csX) ++ post)) =
          .ok (env.code, env.labels) := by simpa [pre4, List.append_assoc] using hlink3
      have ht3_4 : st4.getReg AbiReg.t3 = vi.toBitVec := by
        rw [hothB _ (by decide) (by decide) (by decide), ht3_3, hpres1.sp.trans (hpres0.sp.trans hsp), hslot0_2]
      have ha0_4 : st4.getReg AbiReg.a0 = ve.toBitVec :=
        (hothB _ (by decide) (by decide) (by decide)).trans ((hoth2 _ (by decide) (by decide)).trans ha0_2)
      have hchk := prog_scan8_check_sim env L lm src c hcOk vi ve hlenLt pre4 codeCheck ((codeLoop ++ csX) ++ post) rfl
        hlink4 st4 hpc4' (hpresB.gp.trans (hpres2.gp.trans (hpres1.gp.trans (hpres0.gp.trans hgp))))
        ht0_4 ht1_4 ht3_4 ha0_4
      have hrun0_B := run_trans (run_trans hrun0 hrun1) (run_trans hrun2 hrunB)
      have hpres0_B := hpres0.trans (hpres1.trans (hpres2.trans hpresB))
      have hstepOk : _root_.L.step p (fun _ => throw .outOfFuel) (.scan8 x src i e c) { mem := lm, loc := loc } =
          if vi ≤ ve ∧ ve.toNat ≤ (lm.src8 src).size then
            .ok (Sig.normal, { mem := lm, loc := (({ mem := lm, loc := loc } : _root_.L.St).setLoc x
              (UInt64.ofNat (_root_.L.scanN (lm.src8 src) c vi.toNat ve.toNat))).loc })
          else .error .oob := by
        simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hiE, heE, get, getThe, MonadStateOf.get, StateT.get,
          _root_.L.setLoc, modify, throw, throwThe, MonadExceptOf.throw, Pure.pure, Except.pure]
        split <;> rfl
      rw [hstepOk]
      by_cases hcond : vi ≤ ve ∧ ve.toNat ≤ (lm.src8 src).size
      · simp only [eq_true hcond, ↓reduceIte] at hchk ⊢
        obtain ⟨kC, st5, hrunC, hpc5, ha0_5, ht1_5, ht2_5, ht3_5, hmemC, hpresC⟩ := hchk
        let pre5 := pre4 ++ codeCheck
        have hpc5' : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre5) := by rw [hpc5, lkm.totalSize_append pre4 codeCheck]
        have hlink5 : lkm.linkSpec (pre5 ++ (codeLoop ++ csX) ++ post) =
            .ok (env.code, env.labels) := by simpa [pre5, List.append_assoc] using hlink4
        have hmem25 : st5.mem = st2.mem := hmemC.trans (hmemB.trans hmem2)
        have hsp5 : st5.getReg AbiReg.sp = sp := hpresC.sp.trans (hpres0_B.sp.trans hsp)
        obtain ⟨kT, st7, hrunT, hpc7, hpresT, hm7, hf7, hpmT⟩ :=
          prog_scan8_tail_sim env L lm loc hal hlim htop x hx src hsrcOk c hcLen hcOk vi ve hcond hlenLt
            pfx lblId pre5 post st5 hpc5' hsp5 ha0_5 ht1_5 ht2_5 ht3_5
            (hmem25 ▸ hm2) (hmem25 ▸ hf2) hlink5
        have hpcEq : lkm.totalSize pre5 + lkm.totalSize (codeLoop ++ csX) =
            lkm.totalSize pre + lkm.totalSize (ci ++ ce ++ clVi ++ srcSetup ++ codeCheck ++ (codeLoop ++ csX)) := by
          rw [lkm.totalSize_append pre4 codeCheck, lkm.totalSize_append pre3 srcSetup,
              lkm.totalSize_append pre2 clVi, lkm.totalSize_append pre1 ce, lkm.totalSize_append pre ci,
              lkm.totalSize_append ((((ci ++ ce) ++ clVi) ++ srcSetup) ++ codeCheck) (codeLoop ++ csX),
              lkm.totalSize_append (((ci ++ ce) ++ clVi) ++ srcSetup) codeCheck,
              lkm.totalSize_append ((ci ++ ce) ++ clVi) srcSetup,
              lkm.totalSize_append (ci ++ ce) clVi, lkm.totalSize_append ci ce]; omega
        refine ⟨_, st7, run_trans (run_trans hrun0_B hrunC) hrunT,
          by rw [hpc7, hpcEq, ← hcodeEq], hpres0_B.trans (hpresC.trans hpresT), hm7, hf7, ?_⟩
        rw [hmem25] at hpmT; exact hpm0.trans (hpm1.trans hpmT)
      · simp only [eq_false hcond, ↓reduceIte] at hchk ⊢
        obtain ⟨kC, st5, hrunC, hpc5, hpresC⟩ := hchk
        exact ⟨_, st5, run_trans hrun0_B hrunC, hpc5, hpres0_B.trans hpresC⟩



/-- info: 'ConAgua.RISCV.Compiler.prog_copy8w_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prog_copy8w_sim

/-- info: 'ConAgua.RISCV.Compiler.prog_scan8_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prog_scan8_sim

end ConAgua.RISCV.Compiler
