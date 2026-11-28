import ConAgua.RISCV.Bridge.CheckerDriverCmpCommon

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ConAgua.RISCV.Bridge

open ConAgua.RISCV.RV64
open ConAgua.RISCV.Compiler
open ConAgua.RISCV.Linker
open _root_.L

theorem cmpMode8Setup_sim (img : LinkedCmpImage) (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (ret5 : _root_.L.Word) (_hret5 : 2 ^ 63 ≤ ret5.toNat)
    (pre post : List AsmItem)
    (hlink : img.lkm.linkSpec (pre ++ cmpDrvMode8Setup checkerTabMini ++ post) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase)
    (hs5 : st.getReg AbiReg.s5 = (ret5 - 9223372036854775808).toBitVec) :
    ∃ k st',
      RV64.run (linkedCmpEnv img).rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize (pre ++ cmpDrvMode8Setup checkerTabMini)) ∧
      st'.getReg AbiReg.gp = regionBase ∧
      st'.getReg AbiReg.s0 = BitVec.ofNat 64 (abiFuel - 2) ∧
      st'.getReg AbiReg.sp = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) ∧
      st'.getReg AbiReg.s2 = st.getReg AbiReg.s2 ∧
      st'.getReg AbiReg.s6 = st.getReg AbiReg.s6 ∧
      st'.getReg AbiReg.t0 = regionBase + BitVec.ofInt 64 checkerTabMini.args ∧
      st'.getReg AbiReg.t1 = 0#64 ∧
      ProgMemOutside (phaseBWriteSpan regionBase) st.mem st'.mem ∧
      readWord64 st'.mem regionBase = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) ∧
      readWord64 st'.mem (regionBase + 8#64) = regionBase + BitVec.ofNat 64 abiSlot ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff phiGVar)) =
        (ret5 - 9223372036854775808).toBitVec ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff ploGVar)) = 0#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) = 8#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 180)) = 0#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 180)) = 0#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 182)) = 0#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 182)) = 0#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 181)) =
        regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.slotOf 180) ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 181)) =
        BitVec.ofNat 64 hdrHw := by
  let cPhi := storeMemOff .sd AbiReg.gp AbiReg.s5 AbiReg.t0 (checkerTabMini.globOff phiGVar)
  let cPlo := storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (checkerTabMini.globOff ploGVar)
  let cMode := cmpDrvSetMode 8 checkerTabMini
  let cClrOut := drvClearDesc checkerTabMini 180
  let cClrCtl := drvClearDesc checkerTabMini 182
  let cHdrBaseLi := li AbiReg.t1 (BitVec.ofNat 64 (abiSlot * checkerTabMini.slotOf 180))
  let cHdrBaseAdd := [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1]
  let cHdrBaseSt := storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (checkerTabMini.dbase 181)
  let cHdrLenLi := li AbiReg.t1 (BitVec.ofNat 64 hdrHw)
  let cHdrLenSt := storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (checkerTabMini.dlen 181)
  let cHdrL32Li := li AbiReg.t1 (BitVec.ofNat 64 (2 * hdrHw))
  let cHdrL32St := storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (checkerTabMini.dlen32 181)
  have hNeedEq := checkerTabMini_abiNeed_eq
  have h211 : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; simp [abiSlot]
  have hR : regionBase.toNat + abiSlot ≤ 2 ^ 64 := by omega
  have hDecomp : cmpDrvMode8Setup checkerTabMini =
      cPhi ++ cPlo ++ cMode ++ drvResetStack ++ cClrOut ++ cClrCtl ++
      cHdrBaseLi ++ cHdrBaseAdd ++ cHdrBaseSt ++ cHdrLenLi ++ cHdrLenSt ++
      cHdrL32Li ++ cHdrL32St ++ cmpDrvCallPrep checkerTabMini := by
    dsimp only [cmpDrvMode8Setup, cPhi, cPlo, cMode, cClrOut, cClrCtl,
      cHdrBaseLi, cHdrBaseAdd, cHdrBaseSt, cHdrLenLi, cHdrLenSt, cHdrL32Li, cHdrL32St]
    rw [t_pos_out, t_pos_hdrf, t_pos_ctlf]
  rw [hDecomp] at hlink
  have hl1 : img.lkm.linkSpec (pre ++ cPhi ++ (cPlo ++ cMode ++ drvResetStack ++
      cClrOut ++ cClrCtl ++ cHdrBaseLi ++ cHdrBaseAdd ++ cHdrBaseSt ++
      cHdrLenLi ++ cHdrLenSt ++ cHdrL32Li ++ cHdrL32St ++ cmpDrvCallPrep checkerTabMini ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [List.append_assoc] using hlink
  have hpc1_64 := linkResolved_sub_pc64 (linkedCmpEnv img) pre cPhi _ hl1
  have halPhi : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.globOff phiGVar)) 8 = true := by
    rw [hgp, globOff_bitvec]; exact isAligned8_add_nat_mul8 regionBase hRegAlign _ (by
      rw [checkerTabMini_resBase_eq, Int.toNat_natCast, t_nxres]; omega)
  obtain ⟨s1, hrun1, hoth1, hm1, hpc1⟩ :=
    storeMemOff_sd_correct_lm img.lkm (linkedCmpEnv img).hrom pre _ AbiReg.gp AbiReg.s5 AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.globOff phiGVar) hl1 hpc1_64 st hpc halPhi
  let p1 := pre ++ cPhi
  have hpc1' : s1.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p1) := by
    simpa only [p1, img.lkm.totalSize_append] using hpc1
  have hs1gp : s1.getReg AbiReg.gp = regionBase := (hoth1 _ (by decide)).trans hgp
  have hl2 : img.lkm.linkSpec (p1 ++ cPlo ++ (cMode ++ drvResetStack ++
      cClrOut ++ cClrCtl ++ cHdrBaseLi ++ cHdrBaseAdd ++ cHdrBaseSt ++
      cHdrLenLi ++ cHdrLenSt ++ cHdrL32Li ++ cHdrL32St ++ cmpDrvCallPrep checkerTabMini ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p1, List.append_assoc] using hl1
  have hpc2_64 := linkResolved_sub_pc64 (linkedCmpEnv img) p1 cPlo _ hl2
  have halPlo : isAligned (s1.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.globOff ploGVar)) 8 = true := by
    rw [hs1gp, globOff_bitvec]; exact isAligned8_add_nat_mul8 regionBase hRegAlign _ (by
      rw [checkerTabMini_resBase_eq, Int.toNat_natCast, t_nxres]; omega)
  obtain ⟨s2, hrun2, hoth2, hm2, hpc2⟩ :=
    storeMemOff_sd_correct_lm img.lkm (linkedCmpEnv img).hrom p1 _ AbiReg.gp AbiReg.zero AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.globOff ploGVar) hl2 hpc2_64 s1 hpc1' halPlo
  let p2 := p1 ++ cPlo
  have hpc2' : s2.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p2) := by
    simpa only [p2, img.lkm.totalSize_append] using hpc2
  have hs2gp : s2.getReg AbiReg.gp = regionBase := (hoth2 _ (by decide)).trans hs1gp
  have hl3 : img.lkm.linkSpec (p2 ++ cMode ++ (drvResetStack ++
      cClrOut ++ cClrCtl ++ cHdrBaseLi ++ cHdrBaseAdd ++ cHdrBaseSt ++
      cHdrLenLi ++ cHdrLenSt ++ cHdrL32Li ++ cHdrL32St ++ cmpDrvCallPrep checkerTabMini ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p2, List.append_assoc] using hl2
  obtain ⟨k3, s3, hrun3, hpc3, hs3gp, hoth3, hm3⟩ :=
    cmpDrvSetMode_sim img regionBase hRegAlign hReg64 8 p2 _ hl3 s2 hpc2' hs2gp
  let p3 := p2 ++ cMode
  have hpc3' : s3.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p3) := by
    simpa only [p3, img.lkm.totalSize_append] using hpc3
  have hl4 : img.lkm.linkSpec (p3 ++ drvResetStack ++ (cClrOut ++ cClrCtl ++
      cHdrBaseLi ++ cHdrBaseAdd ++ cHdrBaseSt ++ cHdrLenLi ++ cHdrLenSt ++
      cHdrL32Li ++ cHdrL32St ++ cmpDrvCallPrep checkerTabMini ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p3, List.append_assoc] using hl3
  obtain ⟨k4, s4, hrun4, hpc4, hoth4, hout4, hTop4, hLim4⟩ :=
    drvResetStack_sim_gen (linkedCmpEnv img) regionBase hRegAlign p3 _ hl4 s3 hpc3' hs3gp
  let p4 := p3 ++ drvResetStack
  have hpc4' : s4.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p4) := by
    simpa only [p4, img.lkm.totalSize_append] using hpc4
  have hs4gp : s4.getReg AbiReg.gp = regionBase := (hoth4 _ (by decide)).trans hs3gp
  have hl5 : img.lkm.linkSpec (p4 ++ cClrOut ++ (cClrCtl ++ cHdrBaseLi ++ cHdrBaseAdd ++ cHdrBaseSt ++
      cHdrLenLi ++ cHdrLenSt ++ cHdrL32Li ++ cHdrL32St ++ cmpDrvCallPrep checkerTabMini ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p4, List.append_assoc] using hl4
  obtain ⟨k5, s5, hrun5, hpc5, hoth5, hm5⟩ :=
    drvClearDesc_sim_gen (linkedCmpEnv img) regionBase hRegAlign 180 (by omega) p4 _ hl5 s4 hpc4' hs4gp
  let p5 := p4 ++ cClrOut
  have hpc5' : s5.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p5) := by
    simpa only [p5, img.lkm.totalSize_append] using hpc5
  have hs5gp : s5.getReg AbiReg.gp = regionBase := (hoth5 _ (by decide)).trans hs4gp
  have hl6 : img.lkm.linkSpec (p5 ++ cClrCtl ++ (cHdrBaseLi ++ cHdrBaseAdd ++ cHdrBaseSt ++
      cHdrLenLi ++ cHdrLenSt ++ cHdrL32Li ++ cHdrL32St ++ cmpDrvCallPrep checkerTabMini ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p5, List.append_assoc] using hl5
  obtain ⟨k6, s6, hrun6, hpc6, hoth6, hm6⟩ :=
    drvClearDesc_sim_gen (linkedCmpEnv img) regionBase hRegAlign 182 (by omega) p5 _ hl6 s5 hpc5' hs5gp
  let p6 := p5 ++ cClrCtl
  have hpc6' : s6.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p6) := by
    simpa only [p6, img.lkm.totalSize_append] using hpc6
  have hs6gp : s6.getReg AbiReg.gp = regionBase := (hoth6 _ (by decide)).trans hs5gp
  have hl7a : img.lkm.linkSpec (p6 ++ cHdrBaseLi ++ (cHdrBaseAdd ++ cHdrBaseSt ++
      cHdrLenLi ++ cHdrLenSt ++ cHdrL32Li ++ cHdrL32St ++ cmpDrvCallPrep checkerTabMini ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p6, List.append_assoc] using hl6
  have hpc7a_64 := linkResolved_sub_pc64 (linkedCmpEnv img) p6 cHdrBaseLi _ hl7a
  obtain ⟨s7a, hrun7a, hoth7a, ht1_7a, hm7a, hpc7a⟩ :=
    li_correct_lm img.lkm (linkedCmpEnv img).hrom p6 _ AbiReg.t1 (by decide)
      (BitVec.ofNat 64 (abiSlot * checkerTabMini.slotOf 180)) hl7a hpc7a_64 s6 hpc6'
  let p7a := p6 ++ cHdrBaseLi
  have hpc7a' : s7a.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p7a) := by
    simpa only [p7a, img.lkm.totalSize_append] using hpc7a
  have hs7agp : s7a.getReg AbiReg.gp = regionBase := (hoth7a _ (by decide)).trans hs6gp
  have hl7b : img.lkm.linkSpec (p7a ++ [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1] ++
      (cHdrBaseSt ++ cHdrLenLi ++ cHdrLenSt ++ cHdrL32Li ++ cHdrL32St ++ cmpDrvCallPrep checkerTabMini ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p7a, cHdrBaseAdd, List.append_assoc] using hl7a
  obtain ⟨hr7b, hpc7b, ht1_7b, hoth7b, hm7b⟩ :=
    run_alu_rd_step (linkedCmpEnv img) p7a _ .add AbiReg.t1 AbiReg.gp AbiReg.t1 (by decide) hl7b s7a hpc7a'
  let s7b := stepReg s7a AbiReg.t1 (evalAlu .add (s7a.getReg AbiReg.gp) (s7a.getReg AbiReg.t1))
    (BitVec.ofNat 64 (4 * (img.lkm.totalSize p7a + 1)))
  let p7b := p7a ++ cHdrBaseAdd
  have hpc7b' : s7b.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p7b) := by
    simpa only [p7b, cHdrBaseAdd, img.lkm.totalSize_append, Asm.add, img.lkm.totalSize_instr] using hpc7b
  have hs7bgp : s7b.getReg AbiReg.gp = regionBase := (hoth7b _ (by decide)).trans hs7agp
  have hs7bt1 : s7b.getReg AbiReg.t1 = regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.slotOf 180) := by
    rw [ht1_7b]; change s7a.getReg AbiReg.gp + s7a.getReg AbiReg.t1 = _; rw [hs7agp, ht1_7a]
  have hl7c : img.lkm.linkSpec (p7b ++ cHdrBaseSt ++
      (cHdrLenLi ++ cHdrLenSt ++ cHdrL32Li ++ cHdrL32St ++ cmpDrvCallPrep checkerTabMini ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p7b, List.append_assoc] using hl7b
  have hpc7c_64 := linkResolved_sub_pc64 (linkedCmpEnv img) p7b cHdrBaseSt _ hl7c
  have hal7c : isAligned (s7b.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.dbase 181)) 8 = true := by
    rw [hs7bgp, dbase_bv]; exact isAligned8_add_nat_mul8 regionBase hRegAlign _ (by simp)
  obtain ⟨s7, hrun7c, hoth7c, hm7c, hpc7⟩ :=
    storeMemOff_sd_correct_lm img.lkm (linkedCmpEnv img).hrom p7b _ AbiReg.gp AbiReg.t1 AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.dbase 181) hl7c hpc7c_64 s7b hpc7b' hal7c
  let p7 := p7b ++ cHdrBaseSt
  have hpc7' : s7.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p7) := by
    simpa only [p7, img.lkm.totalSize_append] using hpc7
  have hs7gp : s7.getReg AbiReg.gp = regionBase := (hoth7c _ (by decide)).trans hs7bgp
  have hl8a : img.lkm.linkSpec (p7 ++ cHdrLenLi ++
      (cHdrLenSt ++ cHdrL32Li ++ cHdrL32St ++ cmpDrvCallPrep checkerTabMini ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p7, List.append_assoc] using hl7c
  have hpc8a_64 := linkResolved_sub_pc64 (linkedCmpEnv img) p7 cHdrLenLi _ hl8a
  obtain ⟨s8a, hrun8a, hoth8a, ht1_8a, hm8a, hpc8a⟩ :=
    li_correct_lm img.lkm (linkedCmpEnv img).hrom p7 _ AbiReg.t1 (by decide)
      (BitVec.ofNat 64 hdrHw) hl8a hpc8a_64 s7 hpc7'
  let p8a := p7 ++ cHdrLenLi
  have hpc8a' : s8a.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p8a) := by
    simpa only [p8a, img.lkm.totalSize_append] using hpc8a
  have hs8agp : s8a.getReg AbiReg.gp = regionBase := (hoth8a _ (by decide)).trans hs7gp
  have hl8b : img.lkm.linkSpec (p8a ++ cHdrLenSt ++
      (cHdrL32Li ++ cHdrL32St ++ cmpDrvCallPrep checkerTabMini ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p8a, List.append_assoc] using hl8a
  have hpc8b_64 := linkResolved_sub_pc64 (linkedCmpEnv img) p8a cHdrLenSt _ hl8b
  have hal8b : isAligned (s8a.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.dlen 181)) 8 = true := by
    rw [hs8agp, dlen_bv]; exact isAligned8_add_nat_mul8 regionBase hRegAlign _ (by simp)
  obtain ⟨s8, hrun8b, hoth8b, hm8b, hpc8⟩ :=
    storeMemOff_sd_correct_lm img.lkm (linkedCmpEnv img).hrom p8a _ AbiReg.gp AbiReg.t1 AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.dlen 181) hl8b hpc8b_64 s8a hpc8a' hal8b
  let p8 := p8a ++ cHdrLenSt
  have hpc8' : s8.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p8) := by
    simpa only [p8, img.lkm.totalSize_append] using hpc8
  have hs8gp : s8.getReg AbiReg.gp = regionBase := (hoth8b _ (by decide)).trans hs8agp
  have hl9a : img.lkm.linkSpec (p8 ++ cHdrL32Li ++ (cHdrL32St ++ cmpDrvCallPrep checkerTabMini ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p8, List.append_assoc] using hl8b
  have hpc9a_64 := linkResolved_sub_pc64 (linkedCmpEnv img) p8 cHdrL32Li _ hl9a
  obtain ⟨s9a, hrun9a, hoth9a, ht1_9a, hm9a, hpc9a⟩ :=
    li_correct_lm img.lkm (linkedCmpEnv img).hrom p8 _ AbiReg.t1 (by decide)
      (BitVec.ofNat 64 (2 * hdrHw)) hl9a hpc9a_64 s8 hpc8'
  let p9a := p8 ++ cHdrL32Li
  have hpc9a' : s9a.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p9a) := by
    simpa only [p9a, img.lkm.totalSize_append] using hpc9a
  have hs9agp : s9a.getReg AbiReg.gp = regionBase := (hoth9a _ (by decide)).trans hs8gp
  have hl9b : img.lkm.linkSpec (p9a ++ cHdrL32St ++ (cmpDrvCallPrep checkerTabMini ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p9a, List.append_assoc] using hl9a
  have hpc9b_64 := linkResolved_sub_pc64 (linkedCmpEnv img) p9a cHdrL32St _ hl9b
  have hal9b : isAligned (s9a.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.dlen32 181)) 8 = true := by
    rw [hs9agp, dlen32_bv]; exact isAligned8_add_nat_mul8 regionBase hRegAlign _ (by simp)
  obtain ⟨s9, hrun9b, hoth9b, hm9b, hpc9⟩ :=
    storeMemOff_sd_correct_lm img.lkm (linkedCmpEnv img).hrom p9a _ AbiReg.gp AbiReg.t1 AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.dlen32 181) hl9b hpc9b_64 s9a hpc9a' hal9b
  let p9 := p9a ++ cHdrL32St
  have hpc9' : s9.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p9) := by
    simpa only [p9, img.lkm.totalSize_append] using hpc9
  have hs9gp : s9.getReg AbiReg.gp = regionBase := (hoth9b _ (by decide)).trans hs9agp
  have hl10 : img.lkm.linkSpec (p9 ++ cmpDrvCallPrep checkerTabMini ++ post) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p9, List.append_assoc] using hl9b
  obtain ⟨k10, s10, hrun10, hpc10, hm10, hs10gp, hs10sp, hs10s0, hs10t0, hs10t1, hoth10⟩ :=
    linkedCmpDrvCallPrep_sim img regionBase hRegAlign p9 post hl10 (checkerCmp_exhausted_lbl img) s9 hpc9' hs9gp
  have hphiM : s1.mem = writeWord64 st.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff phiGVar))
      ((ret5 - 9223372036854775808).toBitVec) := by
    rw [hm1, hgp, hs5]
  have hploM : s2.mem = writeWord64 s1.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff ploGVar)) 0#64 := by
    rw [hm2, hs1gp]; rfl
  have hmodeM : s3.mem = writeWord64 s2.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) 8#64 :=
    hm3
  let ws03 : List (Int × BitVec 64) :=
    [(checkerTabMini.globOff phiGVar, (ret5 - 9223372036854775808).toBitVec),
     (checkerTabMini.globOff ploGVar, 0#64),
     (checkerTabMini.globOff modeGVar, 8#64)]
  have hs3Eq : s3.mem = applyTabWrites regionBase st.mem ws03 := by
    rw [hmodeM, hploM, hphiM]; simp only [ws03, applyTabWrites]
  let hdrBaseVal := regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.slotOf 180)
  let ws49 : List (Int × BitVec 64) :=
    [(checkerTabMini.dbase 180, 0#64),
     (checkerTabMini.dlen 180, 0#64),
     (checkerTabMini.dlen32 180, 0#64),
     (checkerTabMini.dbase 182, 0#64),
     (checkerTabMini.dlen 182, 0#64),
     (checkerTabMini.dlen32 182, 0#64),
     (checkerTabMini.dbase 181, hdrBaseVal),
     (checkerTabMini.dlen 181, BitVec.ofNat 64 hdrHw),
     (checkerTabMini.dlen32 181, BitVec.ofNat 64 (2 * hdrHw))]
  have hs5M : s5.mem = applyTabWrites regionBase s4.mem (ws49.take 3) := by
    rw [hm5]; simp only [ws49, List.take, applyTabWrites]
  have hs6M : s6.mem = applyTabWrites regionBase s5.mem (ws49.drop 3 |>.take 3) := by
    rw [hm6]; simp only [ws49, List.drop, List.take, applyTabWrites]
  have hs7M : s7.mem = writeWord64 s6.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 181)) hdrBaseVal := by
    rw [hm7c, hs7bgp, hm7b, hm7a, hs7bt1]
  have hs8M : s8.mem = writeWord64 s7.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 181)) (BitVec.ofNat 64 hdrHw) := by
    rw [hm8b, hs8agp, hm8a, ht1_8a]
  have hs9M : s9.mem = writeWord64 s8.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen32 181)) (BitVec.ofNat 64 (2 * hdrHw)) := by
    rw [hm9b, hs9agp, hm9a, ht1_9a]
  have hs9Eq : s9.mem = applyTabWrites regionBase s4.mem ws49 := by
    rw [hs9M, hs8M, hs7M, hm6, hm5]; simp only [ws49, applyTabWrites]
  have hout03 : ProgMemOutside (phaseBWriteSpan regionBase) st.mem s3.mem := by
    rw [hs3Eq]
    refine progMemOutside_applyTabWrites ws03 (fun e he k hk => ?_) st.mem
    simp only [ws03, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact Or.inr (Or.inr ⟨phiGVar, Or.inl rfl, ⟨k, hk, rfl⟩⟩)
    · exact Or.inr (Or.inr ⟨ploGVar, Or.inr (Or.inl rfl), ⟨k, hk, rfl⟩⟩)
    · exact Or.inr (Or.inr ⟨modeGVar, Or.inr (Or.inr rfl), ⟨k, hk, rfl⟩⟩)
  have hout34' : ProgMemOutside (phaseBWriteSpan regionBase) s3.mem s4.mem :=
    ProgMemOutside.of_memEqOutside (fun _ h => Or.inl h) hout4
  have hout49 : ProgMemOutside (phaseBWriteSpan regionBase) s4.mem s9.mem := by
    rw [hs9Eq]
    refine progMemOutside_applyTabWrites ws49 (fun e he k hk => ?_) s4.mem
    simp only [ws49, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl ⟨180, Or.inl rfl, Or.inl ⟨k, hk, rfl⟩⟩)
    · exact Or.inr (Or.inl ⟨180, Or.inl rfl, Or.inr (Or.inl ⟨k, hk, rfl⟩)⟩)
    · exact Or.inr (Or.inl ⟨180, Or.inl rfl, Or.inr (Or.inr ⟨k, hk, rfl⟩)⟩)
    · exact Or.inr (Or.inl ⟨182, Or.inr (Or.inr rfl), Or.inl ⟨k, hk, rfl⟩⟩)
    · exact Or.inr (Or.inl ⟨182, Or.inr (Or.inr rfl), Or.inr (Or.inl ⟨k, hk, rfl⟩)⟩)
    · exact Or.inr (Or.inl ⟨182, Or.inr (Or.inr rfl), Or.inr (Or.inr ⟨k, hk, rfl⟩)⟩)
    · exact Or.inr (Or.inl ⟨181, Or.inr (Or.inl rfl), Or.inl ⟨k, hk, rfl⟩⟩)
    · exact Or.inr (Or.inl ⟨181, Or.inr (Or.inl rfl), Or.inr (Or.inl ⟨k, hk, rfl⟩)⟩)
    · exact Or.inr (Or.inl ⟨181, Or.inr (Or.inl rfl), Or.inr (Or.inr ⟨k, hk, rfl⟩)⟩)
  have hout09 : ProgMemOutside (phaseBWriteSpan regionBase) st.mem s9.mem :=
    hout03.trans (hout34'.trans hout49)
  have hb180eq : checkerTabMini.dbase 180 = ((16 + 8 * 180 : Nat) : Int) := by simp [Tab.dbase]
  have hl180eq : checkerTabMini.dlen 180 = ((1656 + 8 * 180 : Nat) : Int) := by
    simp only [Tab.dlen, t_nb, t_nw]; omega
  have hd180eq : checkerTabMini.dlen32 180 = ((3296 + 8 * 180 : Nat) : Int) := by
    simp only [Tab.dlen32, t_nb, t_nw]; omega
  have hb181eq : checkerTabMini.dbase 181 = ((16 + 8 * 181 : Nat) : Int) := by simp [Tab.dbase]
  have hl181eq : checkerTabMini.dlen 181 = ((1656 + 8 * 181 : Nat) : Int) := by
    simp only [Tab.dlen, t_nb, t_nw]; omega
  have hd181eq : checkerTabMini.dlen32 181 = ((3296 + 8 * 181 : Nat) : Int) := by
    simp only [Tab.dlen32, t_nb, t_nw]; omega
  have hb182eq : checkerTabMini.dbase 182 = ((16 + 8 * 182 : Nat) : Int) := by simp [Tab.dbase]
  have hl182eq : checkerTabMini.dlen 182 = ((1656 + 8 * 182 : Nat) : Int) := by
    simp only [Tab.dlen, t_nb, t_nw]; omega
  have hd182eq : checkerTabMini.dlen32 182 = ((3296 + 8 * 182 : Nat) : Int) := by
    simp only [Tab.dlen32, t_nb, t_nw]; omega
  have hb180ok : tabOffOk (checkerTabMini.dbase 180) := ⟨by rw [hb180eq]; omega, by rw [hb180eq, Int.toNat_natCast]; simp [abiSlot]⟩
  have hl180ok : tabOffOk (checkerTabMini.dlen 180) := ⟨by rw [hl180eq]; omega, by rw [hl180eq, Int.toNat_natCast]; simp [abiSlot]⟩
  have hd180ok : tabOffOk (checkerTabMini.dlen32 180) := ⟨by rw [hd180eq]; omega, by rw [hd180eq, Int.toNat_natCast]; simp [abiSlot]⟩
  have hb181ok : tabOffOk (checkerTabMini.dbase 181) := ⟨by rw [hb181eq]; omega, by rw [hb181eq, Int.toNat_natCast]; simp [abiSlot]⟩
  have hl181ok : tabOffOk (checkerTabMini.dlen 181) := ⟨by rw [hl181eq]; omega, by rw [hl181eq, Int.toNat_natCast]; simp [abiSlot]⟩
  have hd181ok : tabOffOk (checkerTabMini.dlen32 181) := ⟨by rw [hd181eq]; omega, by rw [hd181eq, Int.toNat_natCast]; simp [abiSlot]⟩
  have hb182ok : tabOffOk (checkerTabMini.dbase 182) := ⟨by rw [hb182eq]; omega, by rw [hb182eq, Int.toNat_natCast]; simp [abiSlot]⟩
  have hl182ok : tabOffOk (checkerTabMini.dlen 182) := ⟨by rw [hl182eq]; omega, by rw [hl182eq, Int.toNat_natCast]; simp [abiSlot]⟩
  have hd182ok : tabOffOk (checkerTabMini.dlen32 182) := ⟨by rw [hd182eq]; omega, by rw [hd182eq, Int.toNat_natCast]; simp [abiSlot]⟩
  have hphiOff : checkerTabMini.globOff phiGVar = ((checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + phiGVar.id) : Nat) : Int) := globOff_eq_nat phiGVar
  have hploOff : checkerTabMini.globOff ploGVar = ((checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + ploGVar.id) : Nat) : Int) := globOff_eq_nat ploGVar
  have hmodeOff : checkerTabMini.globOff modeGVar = ((checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + modeGVar.id) : Nat) : Int) := globOff_eq_nat modeGVar
  have hphiN : checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + phiGVar.id) + 8 ≤ abiSlot := globOff_bound (by decide)
  have hploN : checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + ploGVar.id) + 8 ≤ abiSlot := globOff_bound (by decide)
  have hmodeN : checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + modeGVar.id) + 8 ≤ abiSlot := globOff_bound (by decide)
  have hphiOk : tabOffOk (checkerTabMini.globOff phiGVar) := ⟨by rw [hphiOff]; omega, by rw [hphiOff, Int.toNat_natCast]; exact hphiN⟩
  have hploOk : tabOffOk (checkerTabMini.globOff ploGVar) := ⟨by rw [hploOff]; omega, by rw [hploOff, Int.toNat_natCast]; exact hploN⟩
  have hmodeOk : tabOffOk (checkerTabMini.globOff modeGVar) := ⟨by rw [hmodeOff]; omega, by rw [hmodeOff, Int.toNat_natCast]; exact hmodeN⟩
  have hrGe := resBase_ge_16
  have hws49Ok : ∀ e ∈ ws49, tabOffOk e.1 ∧ 16 ≤ e.1.toNat ∧ e.1.toNat + 8 ≤ 16 + 24 * 205 := by
    intro e he
    simp only [ws49, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨hb180ok, by rw [hb180eq, Int.toNat_natCast]; omega, by rw [hb180eq, Int.toNat_natCast]; omega⟩
    · exact ⟨hl180ok, by rw [hl180eq, Int.toNat_natCast]; omega, by rw [hl180eq, Int.toNat_natCast]; omega⟩
    · exact ⟨hd180ok, by rw [hd180eq, Int.toNat_natCast]; omega, by rw [hd180eq, Int.toNat_natCast]; omega⟩
    · exact ⟨hb182ok, by rw [hb182eq, Int.toNat_natCast]; omega, by rw [hb182eq, Int.toNat_natCast]; omega⟩
    · exact ⟨hl182ok, by rw [hl182eq, Int.toNat_natCast]; omega, by rw [hl182eq, Int.toNat_natCast]; omega⟩
    · exact ⟨hd182ok, by rw [hd182eq, Int.toNat_natCast]; omega, by rw [hd182eq, Int.toNat_natCast]; omega⟩
    · exact ⟨hb181ok, by rw [hb181eq, Int.toNat_natCast]; omega, by rw [hb181eq, Int.toNat_natCast]; omega⟩
    · exact ⟨hl181ok, by rw [hl181eq, Int.toNat_natCast]; omega, by rw [hl181eq, Int.toNat_natCast]; omega⟩
    · exact ⟨hd181ok, by rw [hd181eq, Int.toNat_natCast]; omega, by rw [hd181eq, Int.toNat_natCast]; omega⟩
  have hPres49 : ∀ {off : Int} (hoff : tabOffOk off)
      (hdisj : off.toNat + 8 ≤ 16 ∨ 16 + 24 * 205 ≤ off.toNat),
      readWord64 s9.mem (regionBase + BitVec.ofInt 64 off) =
        readWord64 s4.mem (regionBase + BitVec.ofInt 64 off) := by
    intro off hoff hdisj
    rw [hs9Eq]
    exact readWord64_applyTabWrites_disj hR hoff ws49 (fun e he => by
      obtain ⟨heOk, heLo, heHi⟩ := hws49Ok e he
      exact ⟨heOk, by rcases hdisj with h | h <;> first | exact Or.inl (by omega) | exact Or.inr (by omega)⟩) _
  have hPhiVal : readWord64 s9.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff phiGVar)) =
      (ret5 - 9223372036854775808).toBitVec := by
    have e34 : readWord64 s4.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff phiGVar)) =
        readWord64 s3.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff phiGVar)) := by
      rw [hphiOff, BitVec.ofInt_natCast]
      exact MemEqOutside.readWord64_eq hout4 _ fun k hk hc =>
        memSpan_offset_disjoint_contains_false hR hphiN (by simp [abiSlot] : 0 + 16 ≤ abiSlot)
          (Or.inr (by omega)) ⟨k, hk, rfl⟩
          (by simpa only [BitVec.add_zero] using hc)
    have hs3tail : s3.mem = applyTabWrites regionBase s1.mem
        [(checkerTabMini.globOff ploGVar, 0#64), (checkerTabMini.globOff modeGVar, 8#64)] := by
      rw [hmodeM, hploM]; simp only [applyTabWrites]
    rw [hPres49 hphiOk (Or.inr (by rw [hphiOff, Int.toNat_natCast]; omega)), e34, hs3tail]
    rw [readWord64_applyTabWrites_disj hR hphiOk _ (fun e he => by
      have hne1 : phiGVar.id ≠ ploGVar.id := by decide
      have hne2 : phiGVar.id ≠ modeGVar.id := by decide
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact ⟨hploOk, by dsimp only [tabOffDisj]; rw [hphiOff, hploOff, Int.toNat_natCast, Int.toNat_natCast]; omega⟩
      · exact ⟨hmodeOk, by dsimp only [tabOffDisj]; rw [hphiOff, hmodeOff, Int.toNat_natCast, Int.toNat_natCast]; omega⟩) _]
    rw [hphiM, readWord64_writeWord64_self]
  have hPloVal : readWord64 s9.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff ploGVar)) = 0#64 := by
    have e34 : readWord64 s4.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff ploGVar)) =
        readWord64 s3.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff ploGVar)) := by
      rw [hploOff, BitVec.ofInt_natCast]
      exact MemEqOutside.readWord64_eq hout4 _ fun k hk hc =>
        memSpan_offset_disjoint_contains_false hR hploN (by simp [abiSlot] : 0 + 16 ≤ abiSlot)
          (Or.inr (by omega)) ⟨k, hk, rfl⟩
          (by simpa only [BitVec.add_zero] using hc)
    have hs3tail : s3.mem = applyTabWrites regionBase s2.mem [(checkerTabMini.globOff modeGVar, 8#64)] := by
      rw [hmodeM]; simp only [applyTabWrites]
    rw [hPres49 hploOk (Or.inr (by rw [hploOff, Int.toNat_natCast]; omega)), e34, hs3tail]
    rw [readWord64_applyTabWrites_disj hR hploOk _ (fun e he => by
      have hne : ploGVar.id ≠ modeGVar.id := by decide
      simp only [List.mem_singleton] at he; subst he
      exact ⟨hmodeOk, by dsimp only [tabOffDisj]; rw [hploOff, hmodeOff, Int.toNat_natCast, Int.toNat_natCast]; omega⟩) _]
    rw [hploM, readWord64_writeWord64_self]
  have hModeVal : readWord64 s9.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) = 8#64 := by
    have e34 : readWord64 s4.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) =
        readWord64 s3.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) := by
      rw [hmodeOff, BitVec.ofInt_natCast]
      exact MemEqOutside.readWord64_eq hout4 _ fun k hk hc =>
        memSpan_offset_disjoint_contains_false hR hmodeN (by simp [abiSlot] : 0 + 16 ≤ abiSlot)
          (Or.inr (by omega)) ⟨k, hk, rfl⟩
          (by simpa only [BitVec.add_zero] using hc)
    rw [hPres49 hmodeOk (Or.inr (by rw [hmodeOff, Int.toNat_natCast]; omega)), e34, hmodeM,
      readWord64_writeWord64_self]
  have hTop9 : readWord64 s9.mem regionBase = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) := by
    have hz : BitVec.ofInt 64 0 = 0#64 := rfl
    have e49 := hPres49 (off := 0) ⟨by omega, by simp [abiSlot]⟩ (Or.inl (by omega))
    rw [hz, BitVec.add_zero] at e49
    rw [e49, hTop4]
  have hLim9 : readWord64 s9.mem (regionBase + 8#64) = regionBase + BitVec.ofNat 64 abiSlot := by
    have h8 : BitVec.ofInt 64 8 = 8#64 := rfl
    have e49 := hPres49 (off := 8) ⟨by omega, by simp [abiSlot]⟩ (Or.inl (by omega))
    rw [h8] at e49
    rw [e49, hLim4]
  have applyTabWrites_append : ∀ (xs ys : List (Int × BitVec 64)) (m : ByteMem),
      applyTabWrites regionBase m (xs ++ ys) =
        applyTabWrites regionBase (applyTabWrites regionBase m xs) ys := by
    intro xs; induction xs with
    | nil => intro _ _; rfl
    | cons _ _ ih => intro ys m; exact ih ys _
  have hAt49 : ∀ (xs : List (Int × BitVec 64)) (off : Int) (w : BitVec 64) (ys : List (Int × BitVec 64)),
      ws49 = xs ++ (off, w) :: ys →
      tabOffOk off →
      (∀ e ∈ ys, tabOffOk e.1 ∧ tabOffDisj off e.1) →
      readWord64 s9.mem (regionBase + BitVec.ofInt 64 off) = w := by
    intro xs off w ys hws hoff hys
    rw [hs9Eq, hws, applyTabWrites_append]
    change readWord64 (applyTabWrites regionBase
      (writeWord64 (applyTabWrites regionBase s4.mem xs) (regionBase + BitVec.ofInt 64 off) w) ys) _ = w
    rw [readWord64_applyTabWrites_disj hR hoff ys hys, readWord64_writeWord64_self]
  have h180BVal : readWord64 s9.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 180)) = 0#64 :=
    hAt49 [] _ _
      [(checkerTabMini.dlen 180, 0#64), (checkerTabMini.dlen32 180, 0#64),
       (checkerTabMini.dbase 182, 0#64), (checkerTabMini.dlen 182, 0#64), (checkerTabMini.dlen32 182, 0#64),
       (checkerTabMini.dbase 181, hdrBaseVal),
       (checkerTabMini.dlen 181, BitVec.ofNat 64 hdrHw),
       (checkerTabMini.dlen32 181, BitVec.ofNat 64 (2 * hdrHw))]
      rfl hb180ok (fun e he => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hl180ok, Or.inl (by rw [hb180eq, hl180eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩
        · exact ⟨hd180ok, Or.inl (by rw [hb180eq, hd180eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩
        · exact ⟨hb182ok, Or.inl (by rw [hb180eq, hb182eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩
        · exact ⟨hl182ok, Or.inl (by rw [hb180eq, hl182eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩
        · exact ⟨hd182ok, Or.inl (by rw [hb180eq, hd182eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩
        · exact ⟨hb181ok, Or.inl (by rw [hb180eq, hb181eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩
        · exact ⟨hl181ok, Or.inl (by rw [hb180eq, hl181eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩
        · exact ⟨hd181ok, Or.inl (by rw [hb180eq, hd181eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩)
  have h180LVal : readWord64 s9.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 180)) = 0#64 :=
    hAt49 [(checkerTabMini.dbase 180, 0#64)] _ _
      [(checkerTabMini.dlen32 180, 0#64),
       (checkerTabMini.dbase 182, 0#64), (checkerTabMini.dlen 182, 0#64), (checkerTabMini.dlen32 182, 0#64),
       (checkerTabMini.dbase 181, hdrBaseVal),
       (checkerTabMini.dlen 181, BitVec.ofNat 64 hdrHw),
       (checkerTabMini.dlen32 181, BitVec.ofNat 64 (2 * hdrHw))]
      rfl hl180ok (fun e he => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hd180ok, Or.inl (by rw [hl180eq, hd180eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩
        · exact ⟨hb182ok, Or.inr (by rw [hl180eq, hb182eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩
        · exact ⟨hl182ok, Or.inl (by rw [hl180eq, hl182eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩
        · exact ⟨hd182ok, Or.inl (by rw [hl180eq, hd182eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩
        · exact ⟨hb181ok, Or.inr (by rw [hl180eq, hb181eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩
        · exact ⟨hl181ok, Or.inl (by rw [hl180eq, hl181eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩
        · exact ⟨hd181ok, Or.inl (by rw [hl180eq, hd181eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩)
  have h182BVal : readWord64 s9.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 182)) = 0#64 :=
    hAt49 [(checkerTabMini.dbase 180, 0#64), (checkerTabMini.dlen 180, 0#64), (checkerTabMini.dlen32 180, 0#64)] _ _
      [(checkerTabMini.dlen 182, 0#64), (checkerTabMini.dlen32 182, 0#64),
       (checkerTabMini.dbase 181, hdrBaseVal),
       (checkerTabMini.dlen 181, BitVec.ofNat 64 hdrHw),
       (checkerTabMini.dlen32 181, BitVec.ofNat 64 (2 * hdrHw))]
      rfl hb182ok (fun e he => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hl182ok, Or.inl (by rw [hb182eq, hl182eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩
        · exact ⟨hd182ok, Or.inl (by rw [hb182eq, hd182eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩
        · exact ⟨hb181ok, Or.inr (by rw [hb182eq, hb181eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩
        · exact ⟨hl181ok, Or.inl (by rw [hb182eq, hl181eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩
        · exact ⟨hd181ok, Or.inl (by rw [hb182eq, hd181eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩)
  have h182LVal : readWord64 s9.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 182)) = 0#64 :=
    hAt49 [(checkerTabMini.dbase 180, 0#64), (checkerTabMini.dlen 180, 0#64), (checkerTabMini.dlen32 180, 0#64),
       (checkerTabMini.dbase 182, 0#64)] _ _
      [(checkerTabMini.dlen32 182, 0#64),
       (checkerTabMini.dbase 181, hdrBaseVal),
       (checkerTabMini.dlen 181, BitVec.ofNat 64 hdrHw),
       (checkerTabMini.dlen32 181, BitVec.ofNat 64 (2 * hdrHw))]
      rfl hl182ok (fun e he => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl
        · exact ⟨hd182ok, Or.inl (by rw [hl182eq, hd182eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩
        · exact ⟨hb181ok, Or.inr (by rw [hl182eq, hb181eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩
        · exact ⟨hl181ok, Or.inr (by rw [hl182eq, hl181eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩
        · exact ⟨hd181ok, Or.inl (by rw [hl182eq, hd181eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩)
  have h181BVal : readWord64 s9.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 181)) = hdrBaseVal :=
    hAt49 [(checkerTabMini.dbase 180, 0#64), (checkerTabMini.dlen 180, 0#64), (checkerTabMini.dlen32 180, 0#64),
       (checkerTabMini.dbase 182, 0#64), (checkerTabMini.dlen 182, 0#64), (checkerTabMini.dlen32 182, 0#64)] _ _
      [(checkerTabMini.dlen 181, BitVec.ofNat 64 hdrHw),
       (checkerTabMini.dlen32 181, BitVec.ofNat 64 (2 * hdrHw))]
      rfl hb181ok (fun e he => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · exact ⟨hl181ok, Or.inl (by rw [hb181eq, hl181eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩
        · exact ⟨hd181ok, Or.inl (by rw [hb181eq, hd181eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩)
  have h181LVal : readWord64 s9.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 181)) =
      BitVec.ofNat 64 hdrHw :=
    hAt49 [(checkerTabMini.dbase 180, 0#64), (checkerTabMini.dlen 180, 0#64), (checkerTabMini.dlen32 180, 0#64),
       (checkerTabMini.dbase 182, 0#64), (checkerTabMini.dlen 182, 0#64), (checkerTabMini.dlen32 182, 0#64),
       (checkerTabMini.dbase 181, hdrBaseVal)] _ _
      [(checkerTabMini.dlen32 181, BitVec.ofNat 64 (2 * hdrHw))]
      rfl hl181ok (fun e he => by
        simp only [List.mem_singleton] at he; subst he
        exact ⟨hd181ok, Or.inl (by rw [hl181eq, hd181eq, Int.toNat_natCast, Int.toNat_natCast]; omega)⟩)
  have hregPres : ∀ r, r ≠ AbiReg.t0 → r ≠ AbiReg.t1 → r ≠ AbiReg.t2 → r ≠ AbiReg.t6 →
      r ≠ AbiReg.s0 → r ≠ AbiReg.sp → r ≠ AbiReg.s1 → s10.getReg r = st.getReg r := by
    intro r hr0 hr1 hr2 hr6 hrs0 hrsp hrs1
    have e10 := hoth10 r hrs0 hrsp hr0 hr1 hr2 hr6 hrs1
    have e9b := hoth9b r hr0
    have e9a := hoth9a r hr1
    have e8b := hoth8b r hr0
    have e8a := hoth8a r hr1
    have e7c := hoth7c r hr0
    have e7b := hoth7b r hr1
    have e7a := hoth7a r hr1
    have e6 := hoth6 r hr0
    have e5 := hoth5 r hr0
    have e4 := hoth4 r hr1
    have e3 := hoth3 r hr0 hr1
    have e2 := hoth2 r hr0
    have e1 := hoth1 r hr0
    rw [e10, e9b, e9a, e8b, e8a, e7c, e7b, e7a, e6, e5, e4, e3, e2, e1]
  refine ⟨img.lkm.totalSize cPhi + img.lkm.totalSize cPlo + k3 + k4 + k5 + k6 +
      img.lkm.totalSize cHdrBaseLi + 1 + img.lkm.totalSize cHdrBaseSt +
      img.lkm.totalSize cHdrLenLi + img.lkm.totalSize cHdrLenSt +
      img.lkm.totalSize cHdrL32Li + img.lkm.totalSize cHdrL32St + k10, s10, ?_, ?_,
    hs10gp, hs10s0, by rw [hs10sp]; exact hTop9,
    hregPres _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    hregPres _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    hs10t0, hs10t1, by rw [hm10]; exact hout09,
    by rw [hm10]; exact hTop9, by rw [hm10]; exact hLim9,
    by rw [hm10]; exact hPhiVal, by rw [hm10]; exact hPloVal, by rw [hm10]; exact hModeVal,
    by rw [hm10]; exact h180BVal, by rw [hm10]; exact h180LVal,
    by rw [hm10]; exact h182BVal, by rw [hm10]; exact h182LVal,
    by rw [hm10]; exact h181BVal, by rw [hm10]; exact h181LVal⟩
  · rw [run_add, run_add, run_add, run_add, run_add, run_add, run_add, run_add, run_add,
      run_add, run_add, run_add, run_add, hrun1]
    dsimp only; rw [hrun2]; dsimp only; rw [hrun3]; dsimp only; rw [hrun4]
    dsimp only; rw [hrun5]; dsimp only; rw [hrun6]; dsimp only; rw [hrun7a]
    dsimp only; rw [hr7b]; dsimp only; rw [hrun7c]; dsimp only; rw [hrun8a]
    dsimp only; rw [hrun8b]; dsimp only; rw [hrun9a]; dsimp only; rw [hrun9b]; exact hrun10
  · rw [hpc10, hDecomp]
    exact congrArg (fun n => BitVec.ofNat 64 (4 * n))
      (by dsimp only [p9, p9a, p8, p8a, p7, p7b, p7a, p6, p5, p4, p3, p2, p1]
          simp only [img.lkm.totalSize_append, Nat.add_assoc])


end ConAgua.RISCV.Bridge
