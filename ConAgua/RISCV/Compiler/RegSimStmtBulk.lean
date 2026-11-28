import ConAgua.RISCV.Compiler.RegSimStmtBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Bulk Array & Byte-Scan Simulation (`ConAgua.RISCV.Compiler.RegSimStmtBulk`)

Forward simulation of `.copy64`, `.copy8w`, `.scan8` in `compileSR`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard Lean axioms only.
-/

namespace ConAgua.RISCV.Compiler

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Linker

/-! ## 4. Bulk Array & Byte-Scan Simulations (`.copy64`, `.copy8w`, `.scan8`) -/

theorem PreservedFrameRegs.of_scratch3 {fl : FrameLayout} {excl : Reg → Prop} {s1 s2 : State}
    (r0 r1 r2 : Reg) (hr0 : r0 ∈ scratchRegs) (hr1 : r1 ∈ scratchRegs) (hr2 : r2 ∈ scratchRegs)
    (heq : ∀ r, r ≠ r0 → r ≠ r1 → r ≠ r2 → s2.getReg r = s1.getReg r) :
    PreservedFrameRegs fl excl s1 s2 := by
  have h0 := scratchRegs_ne_abi hr0
  have h1 := scratchRegs_ne_abi hr1
  have h2 := scratchRegs_ne_abi hr2
  refine ⟨⟨heq _ h0.1.symm h1.1.symm h2.1.symm, heq _ h0.2.1.symm h1.2.1.symm h2.2.1.symm,
      heq _ h0.2.2.1.symm h1.2.2.1.symm h2.2.2.1.symm,
      heq _ h0.2.2.2.2.1.symm h1.2.2.2.2.1.symm h2.2.2.2.2.1.symm⟩,
    fun _ => heq _ h0.2.2.2.2.2.1.symm h1.2.2.2.2.2.1.symm h2.2.2.2.2.2.1.symm,
    fun _ => heq _ h0.2.2.2.2.2.2.symm h1.2.2.2.2.2.2.symm h2.2.2.2.2.2.2.symm,
    fun r hr _ => heq r
      (allowedRegs_disj_reserved true hr (scratchRegs_sub_reserved hr0))
      (allowedRegs_disj_reserved true hr (scratchRegs_sub_reserved hr1))
      (allowedRegs_disj_reserved true hr (scratchRegs_sub_reserved hr2))⟩

private def copyScanScratchRegs : List Reg :=
  AbiReg.t5 :: scratchRegs

private theorem copyScanScratchRegs_sub_reserved {r : Reg} (h : r ∈ copyScanScratchRegs) :
    r ∈ reservedAbiRegs := by
  simp only [copyScanScratchRegs, List.mem_cons] at h
  rcases h with rfl | h
  · decide
  · exact scratchRegs_sub_reserved h

private theorem copyScanScratchRegs_ne_abi {r : Reg} (h : r ∈ copyScanScratchRegs) :
    r ≠ AbiReg.gp ∧ r ≠ AbiReg.sp ∧ r ≠ AbiReg.s0 ∧ r ≠ AbiReg.s1 ∧ r ≠ AbiReg.s2 ∧ r ≠ AbiReg.ra := by
  simp only [copyScanScratchRegs, List.mem_cons] at h
  rcases h with rfl | h
  · decide
  · have ha := scratchRegs_ne_abi h
    exact ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2.1, ha.2.2.2.2.2.1⟩

private theorem preservedFrameRegs_of_noT5_scratch1 {fl : FrameLayout} {excl : Reg → Prop} {s1 s2 : State}
    (hnoT5 : fl.useT5Gp = false) (r0 : Reg) (hr0 : r0 ∈ copyScanScratchRegs)
    (heq : ∀ r, r ≠ r0 → s2.getReg r = s1.getReg r) :
    PreservedFrameRegs fl excl s1 s2 := by
  have habi := copyScanScratchRegs_ne_abi hr0
  refine ⟨⟨heq _ habi.1.symm, heq _ habi.2.1.symm, heq _ habi.2.2.1.symm,
      heq _ habi.2.2.2.2.1.symm⟩,
    fun _ => heq _ habi.2.2.2.2.2.symm,
    (fun ht => by rw [hnoT5] at ht; cases ht),
    fun r hr _ => heq r (allowedRegs_disj_reserved true hr (copyScanScratchRegs_sub_reserved hr0))⟩

private theorem preservedFrameRegs_of_noT5_scratch2 {fl : FrameLayout} {excl : Reg → Prop} {s1 s2 : State}
    (hnoT5 : fl.useT5Gp = false) (r0 r1 : Reg)
    (hr0 : r0 ∈ copyScanScratchRegs) (hr1 : r1 ∈ copyScanScratchRegs)
    (heq : ∀ r, r ≠ r0 → r ≠ r1 → s2.getReg r = s1.getReg r) :
    PreservedFrameRegs fl excl s1 s2 := by
  have h0 := copyScanScratchRegs_ne_abi hr0
  have h1 := copyScanScratchRegs_ne_abi hr1
  refine ⟨⟨heq _ h0.1.symm h1.1.symm, heq _ h0.2.1.symm h1.2.1.symm,
      heq _ h0.2.2.1.symm h1.2.2.1.symm, heq _ h0.2.2.2.2.1.symm h1.2.2.2.2.1.symm⟩,
    fun _ => heq _ h0.2.2.2.2.2.symm h1.2.2.2.2.2.symm,
    (fun ht => by rw [hnoT5] at ht; cases ht),
    fun r hr _ => heq r
      (allowedRegs_disj_reserved true hr (copyScanScratchRegs_sub_reserved hr0))
      (allowedRegs_disj_reserved true hr (copyScanScratchRegs_sub_reserved hr1))⟩

private theorem preservedFrameRegs_of_noT5_scratch3 {fl : FrameLayout} {excl : Reg → Prop} {s1 s2 : State}
    (hnoT5 : fl.useT5Gp = false) (r0 r1 r2 : Reg)
    (hr0 : r0 ∈ copyScanScratchRegs) (hr1 : r1 ∈ copyScanScratchRegs) (hr2 : r2 ∈ copyScanScratchRegs)
    (heq : ∀ r, r ≠ r0 → r ≠ r1 → r ≠ r2 → s2.getReg r = s1.getReg r) :
    PreservedFrameRegs fl excl s1 s2 := by
  have h0 := copyScanScratchRegs_ne_abi hr0
  have h1 := copyScanScratchRegs_ne_abi hr1
  have h2 := copyScanScratchRegs_ne_abi hr2
  refine ⟨⟨heq _ h0.1.symm h1.1.symm h2.1.symm, heq _ h0.2.1.symm h1.2.1.symm h2.2.1.symm,
      heq _ h0.2.2.1.symm h1.2.2.1.symm h2.2.2.1.symm,
      heq _ h0.2.2.2.2.1.symm h1.2.2.2.2.1.symm h2.2.2.2.2.1.symm⟩,
    fun _ => heq _ h0.2.2.2.2.2.symm h1.2.2.2.2.2.symm h2.2.2.2.2.2.symm,
    (fun ht => by rw [hnoT5] at ht; cases ht),
    fun r hr _ => heq r
      (allowedRegs_disj_reserved true hr (copyScanScratchRegs_sub_reserved hr0))
      (allowedRegs_disj_reserved true hr (copyScanScratchRegs_sub_reserved hr1))
      (allowedRegs_disj_reserved true hr (copyScanScratchRegs_sub_reserved hr2))⟩

private theorem readWord64_tempSlotR_of_tempSpanR {fl : FrameLayout} {sp : BitVec 64}
    {j k : Nat} (hjk : j < k) (hk : k ≤ fl.usedTemps) (hvalid : (frameSpanR fl sp).valid)
    {m1 m2 : ByteMem} (hout : MemEqOutside (tempSpanR fl sp k) m1 m2) :
    readWord64 m2 (sp + BitVec.ofInt 64 (fl.tempSlotOff j)) =
      readWord64 m1 (sp + BitVec.ofInt 64 (fl.tempSlotOff j)) := by
  apply MemEqOutside.readWord64_eq hout
  intro o ho; rw [tempSlotOff_ofInt]
  exact (tempSpanR_disj_tempSlot fl sp hvalid hjk hk).symm _ ⟨o, ho, rfl⟩

private theorem reg_evalToTemp_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (tmp : Nat) (e : Expr) (heOk : exprOkB env.tab fl.nlocals e = true)
    (hVfE : ExprVarsInFrame fl e)
    (htmp : tmp + max 1 (usedTempsExpr e) ≤ fl.usedTemps)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ (compileETo env.tab fl tmp AbiReg.a0 e ++
      storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp)) ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOkR L fl sp st loc) :
    let codeT := compileETo env.tab fl tmp AbiReg.a0 e ++
      storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp)
    match _root_.L.evalE e ⟨lm, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize codeT)) ∧
        readWord64 st'.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff tmp)) = v.toBitVec ∧
        PreservedFrameRegs fl (fun _ => False) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (fun _ => False) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
  have hvalid : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  let ce := compileETo env.tab fl tmp AbiReg.a0 e
  let cs := storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp)
  have h64 := linkResolved_sub_pc64 env pre (ce ++ cs) post hlink
  have htw_all : lkm.totalSize (ce ++ cs) = lkm.totalSize ce + lkm.totalSize cs := lkm.totalSize_append ce cs
  have re := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi e pre (cs ++ post) tmp
    AbiReg.a0 (Or.inl rfl) heOk hVfE (by omega)
    (by simpa only [ce, cs, List.append_assoc] using hlink)
    (by rw [htw_all] at h64; dsimp only [ce] at h64; omega) st hpc hgp ht5 hsp hm hf
  rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨v, hv⟩ | hv
  · simp only [hv] at re ⊢
    obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := re
    have htw1 : lkm.totalSize (pre ++ ce) = lkm.totalSize pre + lkm.totalSize ce := lkm.totalSize_append pre ce
    have halS : isAligned (st1.getReg AbiReg.sp + BitVec.ofInt 64 (fl.tempSlotOff tmp)) 8 = true := by
      rw [hpres1.abi.sp.trans hsp, tempSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hspAlign _
    obtain ⟨st2, hrunS, hothS, hmemS, hpc2⟩ :=
      storeMemOff_sd_correct_lm lkm env.hrom (pre ++ ce) post AbiReg.sp AbiReg.a0 AbiReg.t0
        (by decide) (by decide) (by decide) (fl.tempSlotOff tmp)
        (by simpa only [ce, cs, List.append_assoc] using hlink)
        (by rw [htw1]; rw [htw_all] at h64; dsimp only [cs] at h64 ⊢; omega) st1 (by rw [htw1]; exact hpc1) halS
    have heqS : MemEqOutside (tempSpanR fl sp tmp) st1.mem st2.mem := by
      rw [hmemS, hpres1.abi.sp.trans hsp, tempSlotOff_ofInt]
      exact MemEqOutside.writeWord64 st1.mem _ _ fun k hk =>
        tempSlotSpanR_sub_tempSpanR fl sp hvalid (Nat.le_refl tmp) (by omega) _ ⟨k, hk, rfl⟩
    exact ⟨k1 + lkm.totalSize cs, st2,
      by rw [run_add, hrun1]; dsimp only; exact hrunS,
      by rw [hpc2, htw1, htw_all]; exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (by dsimp only [cs]; omega),
      by rw [hmemS, hpres1.abi.sp.trans hsp, ha0_1]; exact readWord64_writeWord64_self _ _ _,
      (PreservedFrameRegs.of_a0 hpres1).trans (PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hothS),
      heq1.trans heqS⟩
  · simp only [hv] at re ⊢
    obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := re
    exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩

private theorem tier_bit_shift3 (u : _root_.L.Word) :
    evalShiftImm .slli (evalAluImm .andi u.toBitVec 1#12) 3#6 =
      if (u &&& 1 == 0) = true then 0#64 else 8#64 := by
  simp only [evalShiftImm, evalAluImm, show sextImm12 1#12 = 1#64 from rfl, show (3#6 : BitVec 6).toNat = 3 from rfl]
  by_cases h0 : u &&& 1 = 0
  · simp only [beq_iff_eq, h0, ↓reduceIte]
    have hbit := (tierA_bit0 0 u).1 h0 |>.2
    have hz : u.toBitVec &&& 1#64 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hbit)
    rw [hz]; rfl
  · simp only [beq_iff_eq, h0, ↓reduceIte]
    have hbit := (tierA_bit0 0 u).2 h0 |>.2
    have ho : u.toBitVec &&& 1#64 = 1#64 := BitVec.eq_of_toNat_eq (by simpa using hbit)
    rw [ho]; rfl

private theorem reg_warr_dst_setup_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (lm : _root_.L.Mem) {sp : BitVec 64}
    (hal : isAligned sp 8 = true)
    (a : ArrId) (u vdi vk : _root_.L.Word) (da : TieredArray)
    (hdaOk : env.tab.wordPosOkB da = true)
    (hOffLen : L.T + (if (u &&& 1 == 0) = true then 0#64 else 8#64) +
        BitVec.ofInt 64 (env.tab.len64 (.t0 a)) = L.T + BitVec.ofInt 64 (env.tab.len64 da))
    (hOffBase : L.T + (if (u &&& 1 == 0) = true then 0#64 else 8#64) +
        BitVec.ofInt 64 (env.tab.base64 (.t0 a)) = L.T + BitVec.ofInt 64 (env.tab.base64 da))
    (pre codeDst post : List AsmItem)
    (hcodeDst : codeDst =
      loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 0) ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (env.tab.len64 (.t0 a)) ++
      loadMemOff .ld AbiReg.t1 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 1) ++
      loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 4) ++
      [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3, Asm.bltu AbiReg.t0 AbiReg.t1 errLabel] ++
      loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (env.tab.base64 (.t0 a)) ++
      [Asm.slli AbiReg.t1 AbiReg.t1 3#6, Asm.add AbiReg.t1 AbiReg.t5 AbiReg.t1])
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hnoT5 : fl.useT5Gp = false) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm)
    (hs0 : readWord64 st.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff 0)) = u.toBitVec)
    (hs1 : readWord64 st.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff 1)) = vdi.toBitVec)
    (hs4 : readWord64 st.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff 4)) = vk.toBitVec)
    (hlink : lkm.linkSpec (pre ++ codeDst ++ post) = .ok (env.code, env.labels)) :
    if vdi.toNat + vk.toNat ≤ (lm.arr64 da).size then
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize codeDst)) ∧
        r'.getReg AbiReg.t1 = L.base64 da + BitVec.ofNat 64 (8 * vdi.toNat) ∧
        r'.getReg AbiReg.t3 = vk.toBitVec ∧
        r'.mem = st.mem ∧
        PreservedFrameRegs fl (fun _ => False) st r'
    else
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        r'.mem = st.mem ∧
        PreservedFrameRegs fl (fun _ => False) st r' := by
  let cl0 := loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 0)
  let ctp := [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0]
  let clL := loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (env.tab.len64 (.t0 a))
  let cl1 := loadMemOff .ld AbiReg.t1 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 1)
  let cl4 := loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 4)
  let cb0 := [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel]
  let cs0 := [Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3]
  let cb1 := [Asm.bltu AbiReg.t0 AbiReg.t1 errLabel]
  let clB := loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (env.tab.base64 (.t0 a))
  let ct1 := [Asm.slli AbiReg.t1 AbiReg.t1 3#6]
  let ct2 := [Asm.add AbiReg.t1 AbiReg.t5 AbiReg.t1]
  have hcEq : codeDst = cl0 ++ ctp ++ clL ++ cl1 ++ cl4 ++ cb0 ++ cs0 ++ cb1 ++ clB ++ ct1 ++ ct2 := by
    rw [hcodeDst]; simp [cl0, ctp, clL, cl1, cl4, cb0, cs0, cb1, clB, ct1, ct2, List.append_assoc]
  rw [hcEq] at hlink
  have hlink0 : lkm.linkSpec (pre ++ cl0 ++ (ctp ++ clL ++ cl1 ++ cl4 ++ cb0 ++ cs0 ++ cb1 ++ clB ++ ct1 ++ ct2 ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
  have hal0 : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (fl.tempSlotOff 0)) 8 = true := by
    rw [hsp, tempSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hal _
  obtain ⟨st1, hrun0, hoth0, ht0_1, hmem0, hpc1⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre _ AbiReg.t0 AbiReg.sp AbiReg.t1
      (by decide) (by decide) (by decide) (fl.tempSlotOff 0) hlink0
      (linkResolved_sub_pc64 env pre cl0 _ hlink0) st hpc hal0
  have hp0 : PreservedFrameRegs fl (fun _ => False) st st1 :=
    PreservedFrameRegs.of_scratch2 AbiReg.t0 AbiReg.t1 (by decide) (by decide) hoth0
  let pre1 := pre ++ cl0
  have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by rw [hpc1, lkm.totalSize_append pre cl0]
  have hlink1 : lkm.linkSpec (pre1 ++ ctp ++ (clL ++ cl1 ++ cl4 ++ cb0 ++ cs0 ++ cb1 ++ clB ++ ct1 ++ ct2 ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre1, List.append_assoc] using hlink0
  have ⟨hlA, hlBC⟩ := linkResolved_mid_split lkm pre1 [Asm.andi AbiReg.t0 AbiReg.t0 1#12]
    [Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] _ hlink1
  have ⟨hlB, hlC⟩ := linkResolved_mid_split lkm (pre1 ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12])
    [Asm.slli AbiReg.t0 AbiReg.t0 3#6] [Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] _ hlBC
  obtain ⟨hrunA, hpcA, ht0A, hothA, hmemA, _⟩ :=
    run_aluImm_step env pre1 _ .andi AbiReg.t0 AbiReg.t0 1#12 nonPreserved_t0 hlA st1 hpc1'
  let st1a := stepReg st1 AbiReg.t0 (evalAluImm .andi (st1.getReg AbiReg.t0) 1#12)
    (BitVec.ofNat 64 (4 * (lkm.totalSize pre1 + 1)))
  have htwA : lkm.totalSize [Asm.andi AbiReg.t0 AbiReg.t0 1#12] = 1 := by simp only [Asm.andi, lkm.totalSize_instr]
  obtain ⟨hrunB, hpcB, ht0B, hothB, hmemB, _⟩ :=
    run_shImm_step env (pre1 ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12]) _ .slli AbiReg.t0 AbiReg.t0 3#6
      nonPreserved_t0 hlB st1a (by rw [lkm.totalSize_append, htwA]; exact hpcA)
  let st1b := stepReg st1a AbiReg.t0 (evalShiftImm .slli (st1a.getReg AbiReg.t0) 3#6)
    (BitVec.ofNat 64 (4 * (lkm.totalSize (pre1 ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12]) + 1)))
  have htwB : lkm.totalSize [Asm.slli AbiReg.t0 AbiReg.t0 3#6] = 1 := by simp only [Asm.slli, lkm.totalSize_instr]
  obtain ⟨hrunC, hpcC, ht5C, hothC, hmemC, _⟩ :=
    run_alu_step env ((pre1 ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12]) ++ [Asm.slli AbiReg.t0 AbiReg.t0 3#6]) _
      .add AbiReg.t5 AbiReg.gp AbiReg.t0 nonPreserved_t5 hlC st1b (by rw [lkm.totalSize_append, htwB]; exact hpcB)
  let st2 := stepReg st1b AbiReg.t5 (evalAlu .add (st1b.getReg AbiReg.gp) (st1b.getReg AbiReg.t0))
    (BitVec.ofNat 64 (4 * (lkm.totalSize ((pre1 ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12]) ++ [Asm.slli AbiReg.t0 AbiReg.t0 3#6]) + 1)))
  have htwTp : lkm.totalSize ctp = 3 := by
    simp [ctp, Asm.andi, Asm.slli, Asm.add, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
  have hpTp : PreservedFrameRegs fl (fun _ => False) st1 st2 :=
    (PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hothA).trans
      ((PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hothB).trans
        (preservedFrameRegs_of_noT5_scratch1 hnoT5 AbiReg.t5 (by decide) hothC))
  have ht5_2 : st2.getReg AbiReg.t5 = L.T + (if (u &&& 1 == 0) = true then 0#64 else 8#64) := by
    rw [ht5C, evalAlu, hothB _ (by decide), hothA _ (by decide), hp0.abi.gp.trans hgp, ht0B, ht0A, ht0_1, hsp, hs0]
    exact congrArg (L.T + ·) (tier_bit_shift3 u)
  let pre2 := pre1 ++ ctp
  have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) := by
    rw [hpcC]; exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (by
      rw [lkm.totalSize_append, htwB, lkm.totalSize_append, htwA,
          show lkm.totalSize pre2 = lkm.totalSize pre1 + 3 from by rw [lkm.totalSize_append pre1 ctp, htwTp]])
  have hmem02 : st2.mem = st.mem := hmemC.trans (hmemB.trans (hmemA.trans hmem0))
  have hp02 : PreservedFrameRegs fl (fun _ => False) st st2 := hp0.trans hpTp
  have hrun02 := run_trans hrun0 (run_trans (run_trans hrunA hrunB) hrunC)
  have hlink2 : lkm.linkSpec (pre2 ++ clL ++ (cl1 ++ cl4 ++ cb0 ++ cs0 ++ cb1 ++ clB ++ ct1 ++ ct2 ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre2, List.append_assoc] using hlink1
  have halL : isAligned (st2.getReg AbiReg.t5 + BitVec.ofInt 64 (env.tab.len64 (.t0 a))) 8 = true := by
    rw [ht5_2, hOffLen, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
  obtain ⟨st3, hrunL, hothL, ht0_3, hmemL, hpc3⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre2 _ AbiReg.t0 AbiReg.t5 AbiReg.t6
      (by decide) (by decide) (by decide) (env.tab.len64 (.t0 a)) hlink2
      (linkResolved_sub_pc64 env pre2 clL _ hlink2) st2 hpc2' halL
  have hpL : PreservedFrameRegs fl (fun _ => False) st2 st3 :=
    PreservedFrameRegs.of_scratch2 AbiReg.t0 AbiReg.t6 (by decide) (by decide) hothL
  let pre3 := pre2 ++ clL
  have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre3) := by rw [hpc3, lkm.totalSize_append pre2 clL]
  have hlink3 : lkm.linkSpec (pre3 ++ cl1 ++ (cl4 ++ cb0 ++ cs0 ++ cb1 ++ clB ++ ct1 ++ ct2 ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre3, List.append_assoc] using hlink2
  have hsp3 : st3.getReg AbiReg.sp = sp := hpL.abi.sp.trans (hp02.abi.sp.trans hsp)
  have hal1 : isAligned (st3.getReg AbiReg.sp + BitVec.ofInt 64 (fl.tempSlotOff 1)) 8 = true := by
    rw [hsp3, tempSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hal _
  obtain ⟨st4, hrun1, hoth1, ht1_4, hmem1, hpc4⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre3 _ AbiReg.t1 AbiReg.sp AbiReg.t6
      (by decide) (by decide) (by decide) (fl.tempSlotOff 1) hlink3
      (linkResolved_sub_pc64 env pre3 cl1 _ hlink3) st3 hpc3' hal1
  have hp1 : PreservedFrameRegs fl (fun _ => False) st3 st4 :=
    PreservedFrameRegs.of_scratch2 AbiReg.t1 AbiReg.t6 (by decide) (by decide) hoth1
  let pre4 := pre3 ++ cl1
  have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre4) := by rw [hpc4, lkm.totalSize_append pre3 cl1]
  have hlink4 : lkm.linkSpec (pre4 ++ cl4 ++ (cb0 ++ cs0 ++ cb1 ++ clB ++ ct1 ++ ct2 ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre4, List.append_assoc] using hlink3
  have hsp4 : st4.getReg AbiReg.sp = sp := hp1.abi.sp.trans hsp3
  have hal4 : isAligned (st4.getReg AbiReg.sp + BitVec.ofInt 64 (fl.tempSlotOff 4)) 8 = true := by
    rw [hsp4, tempSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hal _
  obtain ⟨st5, hrun4, hoth4, ht3_5, hmem4, hpc5⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre4 _ AbiReg.t3 AbiReg.sp AbiReg.t6
      (by decide) (by decide) (by decide) (fl.tempSlotOff 4) hlink4
      (linkResolved_sub_pc64 env pre4 cl4 _ hlink4) st4 hpc4' hal4
  have hp4 : PreservedFrameRegs fl (fun _ => False) st4 st5 :=
    PreservedFrameRegs.of_scratch2 AbiReg.t3 AbiReg.t6 (by decide) (by decide) hoth4
  let pre5 := pre4 ++ cl4
  have hpc5' : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre5) := by rw [hpc5, lkm.totalSize_append pre4 cl4]
  have hlink5 : lkm.linkSpec (pre5 ++ cb0 ++ (cs0 ++ cb1 ++ clB ++ ct1 ++ ct2 ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre5, List.append_assoc] using hlink4
  have hmem05 : st5.mem = st.mem := hmem4.trans (hmem1.trans (hmemL.trans hmem02))
  have hp05 : PreservedFrameRegs fl (fun _ => False) st st5 := hp02.trans (hpL.trans (hp1.trans hp4))
  have hrun05 := run_trans hrun02 (run_trans (run_trans hrunL hrun1) hrun4)
  rcases hm.2.1 da hdaOk with ⟨_, hlt61, hlen64, hbase64, _⟩
  have ht0_5 : st5.getReg AbiReg.t0 = BitVec.ofNat 64 (lm.arr64 da).size := by
    rw [hoth4 _ (by decide) (by decide), hoth1 _ (by decide) (by decide), ht0_3, hmem02, ht5_2, hOffLen, hlen64]
  have ht1_5 : st5.getReg AbiReg.t1 = vdi.toBitVec := by
    rw [hoth4 _ (by decide) (by decide), ht1_4, hmemL, hmem02, hsp3, hs1]
  have ht3_5v : st5.getReg AbiReg.t3 = vk.toBitVec := by
    rw [ht3_5, hmem1, hmemL, hmem02, hsp4, hs4]
  have ht5_5 : st5.getReg AbiReg.t5 = L.T + (if (u &&& 1 == 0) = true then 0#64 else 8#64) :=
    (hoth4 _ (by decide) (by decide)).trans ((hoth1 _ (by decide) (by decide)).trans ((hothL _ (by decide) (by decide)).trans ht5_2))
  have hbr0 := run_br_step env pre5 _ .bltu AbiReg.t0 AbiReg.t3 errLabel env.errTarget env.herrLbl (by decide) hlink5 st5 hpc5'
  have hcond0 : evalBranch .bltu (st5.getReg AbiReg.t0) (st5.getReg AbiReg.t3) =
      decide ((lm.arr64 da).size < vk.toNat) := by
    rw [ht0_5, ht3_5v, u64_toBitVec_eq_ofNat]; exact evalBranch_bltu_nat (by omega) vk.toBitVec.isLt
  obtain ⟨_, st6, _, hrunBr0, hpcBr0, hothBr0, _, hmemBr0⟩ := hbr0
  have hpBr0 : PreservedFrameRegs fl (fun _ => False) st5 st6 :=
    preservedFrameRegs_of_t6_s1 hothBr0
  by_cases hkn : vk.toNat ≤ (lm.arr64 da).size
  · have hbr0F : evalBranch .bltu (st5.getReg AbiReg.t0) (st5.getReg AbiReg.t3) = false := by
      rw [hcond0, decide_eq_false_iff_not]; omega
    let pre6 := pre5 ++ cb0
    have hpc6' : st6.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre6) := by
      rw [hpcBr0, hbr0F]; simp only [Bool.false_eq_true, ↓reduceIte]
      exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (lkm.totalSize_append pre5 cb0).symm
    have hlink6 : lkm.linkSpec (pre6 ++ cs0 ++ (cb1 ++ clB ++ ct1 ++ ct2 ++ post)) =
        .ok (env.code, env.labels) := by simpa [pre6, List.append_assoc] using hlink5
    let st7 := stepReg st6 AbiReg.t0 (evalAlu .sub (st6.getReg AbiReg.t0) (st6.getReg AbiReg.t3))
      (BitVec.ofNat 64 (4 * (lkm.totalSize pre6 + 1)))
    obtain ⟨hrunSub, hpc7, ht0_7, hothSub, hmemSub, _⟩ :=
      run_alu_step env pre6 _ .sub AbiReg.t0 AbiReg.t0 AbiReg.t3 nonPreserved_t0 hlink6 st6 hpc6'
    have hpSub : PreservedFrameRegs fl (fun _ => False) st6 st7 :=
      PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hothSub
    have ht0_7v : st7.getReg AbiReg.t0 = BitVec.ofNat 64 ((lm.arr64 da).size - vk.toNat) := by
      rw [ht0_7, evalAlu, hothBr0 _ (by decide), hothBr0 _ (by decide), ht0_5, ht3_5v, u64_toBitVec_eq_ofNat]
      exact bitvec_sub_ofNat_eq (by omega) hkn
    let pre7 := pre6 ++ cs0
    have htwSub : lkm.totalSize cs0 = 1 := by simp only [cs0, Asm.sub, lkm.totalSize_instr]
    have hpc7' : st7.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre7) := by rw [hpc7, show lkm.totalSize pre7 = lkm.totalSize pre6 + 1 from by rw [lkm.totalSize_append pre6 cs0, htwSub]]
    have hlink7 : lkm.linkSpec (pre7 ++ cb1 ++ (clB ++ ct1 ++ ct2 ++ post)) =
        .ok (env.code, env.labels) := by simpa [pre7, List.append_assoc] using hlink6
    have hbr1 := run_br_step env pre7 _ .bltu AbiReg.t0 AbiReg.t1 errLabel env.errTarget env.herrLbl (by decide) hlink7 st7 hpc7'
    have hcond1 : evalBranch .bltu (st7.getReg AbiReg.t0) (st7.getReg AbiReg.t1) =
        decide ((lm.arr64 da).size - vk.toNat < vdi.toNat) := by
      rw [ht0_7v, hothSub _ (by decide), hothBr0 _ (by decide), ht1_5, u64_toBitVec_eq_ofNat]
      exact evalBranch_bltu_nat (by omega) vdi.toBitVec.isLt
    obtain ⟨_, st8, _, hrunBr1, hpcBr1, hothBr1, _, hmemBr1⟩ := hbr1
    have hpBr1 : PreservedFrameRegs fl (fun _ => False) st7 st8 :=
      preservedFrameRegs_of_t6_s1 hothBr1
    by_cases hdi : vdi.toNat ≤ (lm.arr64 da).size - vk.toNat
    · have hbound : vdi.toNat + vk.toNat ≤ (lm.arr64 da).size := by omega
      simp only [hbound, ↓reduceIte]
      have hbr1F : evalBranch .bltu (st7.getReg AbiReg.t0) (st7.getReg AbiReg.t1) = false := by
        rw [hcond1, decide_eq_false_iff_not]; omega
      let pre8 := pre7 ++ cb1
      have hpc8' : st8.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre8) := by
        rw [hpcBr1, hbr1F]; simp only [Bool.false_eq_true, ↓reduceIte]
        exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (lkm.totalSize_append pre7 cb1).symm
      have hlink8 : lkm.linkSpec (pre8 ++ clB ++ (ct1 ++ ct2 ++ post)) =
          .ok (env.code, env.labels) := by simpa [pre8, List.append_assoc] using hlink7
      have ht5_8 : st8.getReg AbiReg.t5 = L.T + (if (u &&& 1 == 0) = true then 0#64 else 8#64) :=
        (hothBr1 _ (by decide)).trans ((hothSub _ (by decide)).trans ((hothBr0 _ (by decide)).trans ht5_5))
      have halB : isAligned (st8.getReg AbiReg.t5 + BitVec.ofInt 64 (env.tab.base64 (.t0 a))) 8 = true := by
        rw [ht5_8, hOffBase, Tab.base64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
      obtain ⟨st9, hrunB2, hothB2, ht5_9, hmemB2, hpc9⟩ :=
        loadMemOff_ld_correct_lm lkm env.hrom pre8 _ AbiReg.t5 AbiReg.t5 AbiReg.t6
          (by decide) (by decide) (by decide) (env.tab.base64 (.t0 a)) hlink8
          (linkResolved_sub_pc64 env pre8 clB _ hlink8) st8 hpc8' halB
      have hpB2 : PreservedFrameRegs fl (fun _ => False) st8 st9 :=
        preservedFrameRegs_of_noT5_scratch2 hnoT5 AbiReg.t5 AbiReg.t6 (by decide) (by decide) hothB2
      let pre9 := pre8 ++ clB
      have hpc9' : st9.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre9) := by rw [hpc9, lkm.totalSize_append pre8 clB]
      have hlink9 : lkm.linkSpec (pre9 ++ ct1 ++ (ct2 ++ post)) =
          .ok (env.code, env.labels) := by simpa [pre9, List.append_assoc] using hlink8
      let st10 := stepReg st9 AbiReg.t1 (evalShiftImm .slli (st9.getReg AbiReg.t1) 3#6)
        (BitVec.ofNat 64 (4 * (lkm.totalSize pre9 + 1)))
      obtain ⟨hrunSll, hpc10, ht1_10, hothSll, hmemSll, _⟩ :=
        run_shImm_step env pre9 _ .slli AbiReg.t1 AbiReg.t1 3#6 nonPreserved_t1 hlink9 st9 hpc9'
      have hpSll : PreservedFrameRegs fl (fun _ => False) st9 st10 :=
        PreservedFrameRegs.of_scratch1 AbiReg.t1 (by decide) hothSll
      let pre10 := pre9 ++ ct1
      have htwCt1 : lkm.totalSize ct1 = 1 := by simp only [ct1, Asm.slli, lkm.totalSize_instr]
      have hpc10' : st10.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre10) := by rw [hpc10, show lkm.totalSize pre10 = lkm.totalSize pre9 + 1 from by rw [lkm.totalSize_append pre9 ct1, htwCt1]]
      have hlink10 : lkm.linkSpec (pre10 ++ ct2 ++ post) =
          .ok (env.code, env.labels) := by simpa [pre10, List.append_assoc] using hlink9
      let st11 := stepReg st10 AbiReg.t1 (evalAlu .add (st10.getReg AbiReg.t5) (st10.getReg AbiReg.t1))
        (BitVec.ofNat 64 (4 * (lkm.totalSize pre10 + 1)))
      obtain ⟨hrunAdd, hpc11, ht1_11, hothAdd, hmemAdd, _⟩ :=
        run_alu_step env pre10 _ .add AbiReg.t1 AbiReg.t5 AbiReg.t1 nonPreserved_t1 hlink10 st10 hpc10'
      have hpAdd : PreservedFrameRegs fl (fun _ => False) st10 st11 :=
        PreservedFrameRegs.of_scratch1 AbiReg.t1 (by decide) hothAdd
      have hmem08 : st8.mem = st.mem := hmemBr1.trans (hmemSub.trans (hmemBr0.trans hmem05))
      have ht1_11v : st11.getReg AbiReg.t1 = L.base64 da + BitVec.ofNat 64 (8 * vdi.toNat) := by
        rw [ht1_11, evalAlu, hothSll _ (by decide), ht5_9, hmem08, ht5_8, hOffBase, hbase64,
            ht1_10, hothB2 _ (by decide) (by decide), hothBr1 _ (by decide), hothSub _ (by decide),
            hothBr0 _ (by decide), ht1_5, shl3_ofNat_eq vdi (by omega)]
      have ht3_11v : st11.getReg AbiReg.t3 = vk.toBitVec :=
        (hothAdd _ (by decide)).trans ((hothSll _ (by decide)).trans ((hothB2 _ (by decide) (by decide)).trans
          ((hothBr1 _ (by decide)).trans ((hothSub _ (by decide)).trans ((hothBr0 _ (by decide)).trans ht3_5v)))))
      have hpcEq : lkm.totalSize pre10 + 1 = lkm.totalSize pre + lkm.totalSize codeDst := by
        have htwCt2 : lkm.totalSize ct2 = 1 := by simp only [ct2, Asm.add, lkm.totalSize_instr]
        rw [hcEq]
        simp only [pre10, pre9, pre8, pre7, pre6, pre5, pre4, pre3, pre2, pre1, lkm.totalSize_append, htwCt1, htwCt2, htwSub]
        omega
      exact ⟨_, st11,
        run_trans hrun05 (run_trans (run_trans (run_trans hrunBr0 hrunSub) hrunBr1) (run_trans (run_trans hrunB2 hrunSll) hrunAdd)),
        by rw [hpc11, hpcEq], ht1_11v, ht3_11v,
        hmemAdd.trans (hmemSll.trans (hmemB2.trans hmem08)),
        hp05.trans (hpBr0.trans (hpSub.trans (hpBr1.trans (hpB2.trans (hpSll.trans hpAdd)))))⟩
    · have hbound : ¬(vdi.toNat + vk.toNat ≤ (lm.arr64 da).size) := by omega
      simp only [hbound, ↓reduceIte]
      have hbr1T : evalBranch .bltu (st7.getReg AbiReg.t0) (st7.getReg AbiReg.t1) = true := by
        rw [hcond1, decide_eq_true_iff]; omega
      exact ⟨_, st8, run_trans hrun05 (run_trans (run_trans hrunBr0 hrunSub) hrunBr1),
        by rw [hpcBr1, hbr1T]; rfl, hmemBr1.trans (hmemSub.trans (hmemBr0.trans hmem05)),
        hp05.trans (hpBr0.trans (hpSub.trans hpBr1))⟩
  · have hbound : ¬(vdi.toNat + vk.toNat ≤ (lm.arr64 da).size) := by omega
    simp only [hbound, ↓reduceIte]
    have hbr0T : evalBranch .bltu (st5.getReg AbiReg.t0) (st5.getReg AbiReg.t3) = true := by
      rw [hcond0, decide_eq_true_iff]; omega
    exact ⟨_, st6, run_trans hrun05 hrunBr0, by rw [hpcBr0, hbr0T]; rfl,
      hmemBr0.trans hmem05, hp05.trans hpBr0⟩

private theorem reg_warr_src_setup_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (lm : _root_.L.Mem) {sp : BitVec 64}
    (hal : isAligned sp 8 = true)
    (a : ArrId) (u vsi vk : _root_.L.Word) (sa : TieredArray)
    (hsaOk : env.tab.wordPosOkB sa = true) (t1Val : BitVec 64)
    (hOffLen : L.T + (if (u &&& 1 == 0) = true then 0#64 else 8#64) +
        BitVec.ofInt 64 (env.tab.len64 (.t0 a)) = L.T + BitVec.ofInt 64 (env.tab.len64 sa))
    (hOffBase : L.T + (if (u &&& 1 == 0) = true then 0#64 else 8#64) +
        BitVec.ofInt 64 (env.tab.base64 (.t0 a)) = L.T + BitVec.ofInt 64 (env.tab.base64 sa))
    (pre codeSrc post : List AsmItem)
    (hcodeSrc : codeSrc =
      loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t2 (fl.tempSlotOff 2) ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (env.tab.len64 (.t0 a)) ++
      loadMemOff .ld AbiReg.t2 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 3) ++
      [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3, Asm.bltu AbiReg.t0 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (env.tab.base64 (.t0 a)) ++
      [Asm.slli AbiReg.t2 AbiReg.t2 3#6, Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2])
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hnoT5 : fl.useT5Gp = false) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm)
    (ht1 : st.getReg AbiReg.t1 = t1Val) (ht3 : st.getReg AbiReg.t3 = vk.toBitVec)
    (hs2 : readWord64 st.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff 2)) = u.toBitVec)
    (hs3 : readWord64 st.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff 3)) = vsi.toBitVec)
    (hlink : lkm.linkSpec (pre ++ codeSrc ++ post) = .ok (env.code, env.labels)) :
    if vsi.toNat + vk.toNat ≤ (lm.arr64 sa).size then
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize codeSrc)) ∧
        r'.getReg AbiReg.t1 = t1Val ∧
        r'.getReg AbiReg.t2 = L.base64 sa + BitVec.ofNat 64 (8 * vsi.toNat) ∧
        r'.getReg AbiReg.t3 = vk.toBitVec ∧
        r'.mem = st.mem ∧
        PreservedFrameRegs fl (fun _ => False) st r'
    else
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        r'.mem = st.mem ∧
        PreservedFrameRegs fl (fun _ => False) st r' := by
  let cl0 := loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t2 (fl.tempSlotOff 2)
  let ctp := [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0]
  let clL := loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (env.tab.len64 (.t0 a))
  let cl3 := loadMemOff .ld AbiReg.t2 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 3)
  let cb0 := [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel]
  let cs0 := [Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3]
  let cb1 := [Asm.bltu AbiReg.t0 AbiReg.t2 errLabel]
  let clB := loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (env.tab.base64 (.t0 a))
  let ct1 := [Asm.slli AbiReg.t2 AbiReg.t2 3#6]
  let ct2 := [Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2]
  have hcEq : codeSrc = cl0 ++ ctp ++ clL ++ cl3 ++ cb0 ++ cs0 ++ cb1 ++ clB ++ ct1 ++ ct2 := by
    rw [hcodeSrc]; simp [cl0, ctp, clL, cl3, cb0, cs0, cb1, clB, ct1, ct2, List.append_assoc]
  rw [hcEq] at hlink
  have hlink0 : lkm.linkSpec (pre ++ cl0 ++ (ctp ++ clL ++ cl3 ++ cb0 ++ cs0 ++ cb1 ++ clB ++ ct1 ++ ct2 ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
  have hal2 : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (fl.tempSlotOff 2)) 8 = true := by
    rw [hsp, tempSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hal _
  obtain ⟨st1, hrun0, hoth0, ht0_1, hmem0, hpc1⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre _ AbiReg.t0 AbiReg.sp AbiReg.t2
      (by decide) (by decide) (by decide) (fl.tempSlotOff 2) hlink0
      (linkResolved_sub_pc64 env pre cl0 _ hlink0) st hpc hal2
  have hp0 : PreservedFrameRegs fl (fun _ => False) st st1 :=
    PreservedFrameRegs.of_scratch2 AbiReg.t0 AbiReg.t2 (by decide) (by decide) hoth0
  let pre1 := pre ++ cl0
  have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by rw [hpc1, lkm.totalSize_append pre cl0]
  have hlink1 : lkm.linkSpec (pre1 ++ ctp ++ (clL ++ cl3 ++ cb0 ++ cs0 ++ cb1 ++ clB ++ ct1 ++ ct2 ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre1, List.append_assoc] using hlink0
  have ⟨hlA, hlBC⟩ := linkResolved_mid_split lkm pre1 [Asm.andi AbiReg.t0 AbiReg.t0 1#12]
    [Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] _ hlink1
  have ⟨hlB, hlC⟩ := linkResolved_mid_split lkm (pre1 ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12])
    [Asm.slli AbiReg.t0 AbiReg.t0 3#6] [Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] _ hlBC
  obtain ⟨hrunA, hpcA, ht0A, hothA, hmemA, _⟩ :=
    run_aluImm_step env pre1 _ .andi AbiReg.t0 AbiReg.t0 1#12 nonPreserved_t0 hlA st1 hpc1'
  let st1a := stepReg st1 AbiReg.t0 (evalAluImm .andi (st1.getReg AbiReg.t0) 1#12)
    (BitVec.ofNat 64 (4 * (lkm.totalSize pre1 + 1)))
  have htwA : lkm.totalSize [Asm.andi AbiReg.t0 AbiReg.t0 1#12] = 1 := by simp only [Asm.andi, lkm.totalSize_instr]
  obtain ⟨hrunB, hpcB, ht0B, hothB, hmemB, _⟩ :=
    run_shImm_step env (pre1 ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12]) _ .slli AbiReg.t0 AbiReg.t0 3#6
      nonPreserved_t0 hlB st1a (by rw [lkm.totalSize_append, htwA]; exact hpcA)
  let st1b := stepReg st1a AbiReg.t0 (evalShiftImm .slli (st1a.getReg AbiReg.t0) 3#6)
    (BitVec.ofNat 64 (4 * (lkm.totalSize (pre1 ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12]) + 1)))
  have htwB : lkm.totalSize [Asm.slli AbiReg.t0 AbiReg.t0 3#6] = 1 := by simp only [Asm.slli, lkm.totalSize_instr]
  obtain ⟨hrunC, hpcC, ht5C, hothC, hmemC, _⟩ :=
    run_alu_step env ((pre1 ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12]) ++ [Asm.slli AbiReg.t0 AbiReg.t0 3#6]) _
      .add AbiReg.t5 AbiReg.gp AbiReg.t0 nonPreserved_t5 hlC st1b (by rw [lkm.totalSize_append, htwB]; exact hpcB)
  let st2 := stepReg st1b AbiReg.t5 (evalAlu .add (st1b.getReg AbiReg.gp) (st1b.getReg AbiReg.t0))
    (BitVec.ofNat 64 (4 * (lkm.totalSize ((pre1 ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12]) ++ [Asm.slli AbiReg.t0 AbiReg.t0 3#6]) + 1)))
  have htwTp : lkm.totalSize ctp = 3 := by
    simp [ctp, Asm.andi, Asm.slli, Asm.add, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
  have hpTp : PreservedFrameRegs fl (fun _ => False) st1 st2 :=
    (PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hothA).trans
      ((PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hothB).trans
        (preservedFrameRegs_of_noT5_scratch1 hnoT5 AbiReg.t5 (by decide) hothC))
  have ht5_2 : st2.getReg AbiReg.t5 = L.T + (if (u &&& 1 == 0) = true then 0#64 else 8#64) := by
    rw [ht5C, evalAlu, hothB _ (by decide), hothA _ (by decide), hp0.abi.gp.trans hgp, ht0B, ht0A, ht0_1, hsp, hs2]
    exact congrArg (L.T + ·) (tier_bit_shift3 u)
  let pre2 := pre1 ++ ctp
  have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) := by
    rw [hpcC]; exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (by
      rw [lkm.totalSize_append, htwB, lkm.totalSize_append, htwA,
          show lkm.totalSize pre2 = lkm.totalSize pre1 + 3 from by rw [lkm.totalSize_append pre1 ctp, htwTp]])
  have hmem02 : st2.mem = st.mem := hmemC.trans (hmemB.trans (hmemA.trans hmem0))
  have hp02 : PreservedFrameRegs fl (fun _ => False) st st2 := hp0.trans hpTp
  have hrun02 := run_trans hrun0 (run_trans (run_trans hrunA hrunB) hrunC)
  have ht1_2 : st2.getReg AbiReg.t1 = t1Val :=
    (hothC _ (by decide)).trans ((hothB _ (by decide)).trans ((hothA _ (by decide)).trans ((hoth0 _ (by decide) (by decide)).trans ht1)))
  have ht3_2 : st2.getReg AbiReg.t3 = vk.toBitVec :=
    (hothC _ (by decide)).trans ((hothB _ (by decide)).trans ((hothA _ (by decide)).trans ((hoth0 _ (by decide) (by decide)).trans ht3)))
  have hlink2 : lkm.linkSpec (pre2 ++ clL ++ (cl3 ++ cb0 ++ cs0 ++ cb1 ++ clB ++ ct1 ++ ct2 ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre2, List.append_assoc] using hlink1
  have halL : isAligned (st2.getReg AbiReg.t5 + BitVec.ofInt 64 (env.tab.len64 (.t0 a))) 8 = true := by
    rw [ht5_2, hOffLen, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
  obtain ⟨st3, hrunL, hothL, ht0_3, hmemL, hpc3⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre2 _ AbiReg.t0 AbiReg.t5 AbiReg.t6
      (by decide) (by decide) (by decide) (env.tab.len64 (.t0 a)) hlink2
      (linkResolved_sub_pc64 env pre2 clL _ hlink2) st2 hpc2' halL
  have hpL : PreservedFrameRegs fl (fun _ => False) st2 st3 :=
    PreservedFrameRegs.of_scratch2 AbiReg.t0 AbiReg.t6 (by decide) (by decide) hothL
  let pre3 := pre2 ++ clL
  have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre3) := by rw [hpc3, lkm.totalSize_append pre2 clL]
  have hlink3 : lkm.linkSpec (pre3 ++ cl3 ++ (cb0 ++ cs0 ++ cb1 ++ clB ++ ct1 ++ ct2 ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre3, List.append_assoc] using hlink2
  have hsp3 : st3.getReg AbiReg.sp = sp := hpL.abi.sp.trans (hp02.abi.sp.trans hsp)
  have hal3 : isAligned (st3.getReg AbiReg.sp + BitVec.ofInt 64 (fl.tempSlotOff 3)) 8 = true := by
    rw [hsp3, tempSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hal _
  obtain ⟨st4, hrun3, hoth3, ht2_4, hmem3, hpc4⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre3 _ AbiReg.t2 AbiReg.sp AbiReg.t6
      (by decide) (by decide) (by decide) (fl.tempSlotOff 3) hlink3
      (linkResolved_sub_pc64 env pre3 cl3 _ hlink3) st3 hpc3' hal3
  have hp3 : PreservedFrameRegs fl (fun _ => False) st3 st4 :=
    PreservedFrameRegs.of_scratch2 AbiReg.t2 AbiReg.t6 (by decide) (by decide) hoth3
  let pre4 := pre3 ++ cl3
  have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre4) := by rw [hpc4, lkm.totalSize_append pre3 cl3]
  have hlink4 : lkm.linkSpec (pre4 ++ cb0 ++ (cs0 ++ cb1 ++ clB ++ ct1 ++ ct2 ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre4, List.append_assoc] using hlink3
  have hmem04 : st4.mem = st.mem := hmem3.trans (hmemL.trans hmem02)
  have hp04 : PreservedFrameRegs fl (fun _ => False) st st4 := hp02.trans (hpL.trans hp3)
  have hrun04 := run_trans hrun02 (run_trans hrunL hrun3)
  rcases hm.2.1 sa hsaOk with ⟨_, hlt61, hlen64, hbase64, _⟩
  have ht0_4 : st4.getReg AbiReg.t0 = BitVec.ofNat 64 (lm.arr64 sa).size := by
    rw [hoth3 _ (by decide) (by decide), ht0_3, hmem02, ht5_2, hOffLen, hlen64]
  have ht1_4 : st4.getReg AbiReg.t1 = t1Val :=
    (hoth3 _ (by decide) (by decide)).trans ((hothL _ (by decide) (by decide)).trans ht1_2)
  have ht2_4v : st4.getReg AbiReg.t2 = vsi.toBitVec := by
    rw [ht2_4, hmemL, hmem02, hsp3, hs3]
  have ht3_4 : st4.getReg AbiReg.t3 = vk.toBitVec :=
    (hoth3 _ (by decide) (by decide)).trans ((hothL _ (by decide) (by decide)).trans ht3_2)
  have ht5_4 : st4.getReg AbiReg.t5 = L.T + (if (u &&& 1 == 0) = true then 0#64 else 8#64) :=
    (hoth3 _ (by decide) (by decide)).trans ((hothL _ (by decide) (by decide)).trans ht5_2)
  have hbr0 := run_br_step env pre4 _ .bltu AbiReg.t0 AbiReg.t3 errLabel env.errTarget env.herrLbl (by decide) hlink4 st4 hpc4'
  have hcond0 : evalBranch .bltu (st4.getReg AbiReg.t0) (st4.getReg AbiReg.t3) =
      decide ((lm.arr64 sa).size < vk.toNat) := by
    rw [ht0_4, ht3_4, u64_toBitVec_eq_ofNat]; exact evalBranch_bltu_nat (by omega) vk.toBitVec.isLt
  obtain ⟨_, st5, _, hrunBr0, hpcBr0, hothBr0, _, hmemBr0⟩ := hbr0
  have hpBr0 : PreservedFrameRegs fl (fun _ => False) st4 st5 :=
    preservedFrameRegs_of_t6_s1 hothBr0
  by_cases hkn : vk.toNat ≤ (lm.arr64 sa).size
  · have hbr0F : evalBranch .bltu (st4.getReg AbiReg.t0) (st4.getReg AbiReg.t3) = false := by
      rw [hcond0, decide_eq_false_iff_not]; omega
    let pre5 := pre4 ++ cb0
    have hpc5' : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre5) := by
      rw [hpcBr0, hbr0F]; simp only [Bool.false_eq_true, ↓reduceIte]
      exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (lkm.totalSize_append pre4 cb0).symm
    have hlink5 : lkm.linkSpec (pre5 ++ cs0 ++ (cb1 ++ clB ++ ct1 ++ ct2 ++ post)) =
        .ok (env.code, env.labels) := by simpa [pre5, List.append_assoc] using hlink4
    let st6 := stepReg st5 AbiReg.t0 (evalAlu .sub (st5.getReg AbiReg.t0) (st5.getReg AbiReg.t3))
      (BitVec.ofNat 64 (4 * (lkm.totalSize pre5 + 1)))
    obtain ⟨hrunSub, hpc6, ht0_6, hothSub, hmemSub, _⟩ :=
      run_alu_step env pre5 _ .sub AbiReg.t0 AbiReg.t0 AbiReg.t3 nonPreserved_t0 hlink5 st5 hpc5'
    have hpSub : PreservedFrameRegs fl (fun _ => False) st5 st6 :=
      PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hothSub
    have ht0_6v : st6.getReg AbiReg.t0 = BitVec.ofNat 64 ((lm.arr64 sa).size - vk.toNat) := by
      rw [ht0_6, evalAlu, hothBr0 _ (by decide), hothBr0 _ (by decide), ht0_4, ht3_4, u64_toBitVec_eq_ofNat]
      exact bitvec_sub_ofNat_eq (by omega) hkn
    let pre6 := pre5 ++ cs0
    have htwSub : lkm.totalSize cs0 = 1 := by simp only [cs0, Asm.sub, lkm.totalSize_instr]
    have hpc6' : st6.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre6) := by rw [hpc6, show lkm.totalSize pre6 = lkm.totalSize pre5 + 1 from by rw [lkm.totalSize_append pre5 cs0, htwSub]]
    have hlink6 : lkm.linkSpec (pre6 ++ cb1 ++ (clB ++ ct1 ++ ct2 ++ post)) =
        .ok (env.code, env.labels) := by simpa [pre6, List.append_assoc] using hlink5
    have hbr1 := run_br_step env pre6 _ .bltu AbiReg.t0 AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide) hlink6 st6 hpc6'
    have hcond1 : evalBranch .bltu (st6.getReg AbiReg.t0) (st6.getReg AbiReg.t2) =
        decide ((lm.arr64 sa).size - vk.toNat < vsi.toNat) := by
      rw [ht0_6v, hothSub _ (by decide), hothBr0 _ (by decide), ht2_4v, u64_toBitVec_eq_ofNat]
      exact evalBranch_bltu_nat (by omega) vsi.toBitVec.isLt
    obtain ⟨_, st7, _, hrunBr1, hpcBr1, hothBr1, _, hmemBr1⟩ := hbr1
    have hpBr1 : PreservedFrameRegs fl (fun _ => False) st6 st7 :=
      preservedFrameRegs_of_t6_s1 hothBr1
    by_cases hsi : vsi.toNat ≤ (lm.arr64 sa).size - vk.toNat
    · have hbound : vsi.toNat + vk.toNat ≤ (lm.arr64 sa).size := by omega
      simp only [hbound, ↓reduceIte]
      have hbr1F : evalBranch .bltu (st6.getReg AbiReg.t0) (st6.getReg AbiReg.t2) = false := by
        rw [hcond1, decide_eq_false_iff_not]; omega
      let pre7 := pre6 ++ cb1
      have hpc7' : st7.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre7) := by
        rw [hpcBr1, hbr1F]; simp only [Bool.false_eq_true, ↓reduceIte]
        exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (lkm.totalSize_append pre6 cb1).symm
      have hlink7 : lkm.linkSpec (pre7 ++ clB ++ (ct1 ++ ct2 ++ post)) =
          .ok (env.code, env.labels) := by simpa [pre7, List.append_assoc] using hlink6
      have ht5_7 : st7.getReg AbiReg.t5 = L.T + (if (u &&& 1 == 0) = true then 0#64 else 8#64) :=
        (hothBr1 _ (by decide)).trans ((hothSub _ (by decide)).trans ((hothBr0 _ (by decide)).trans ht5_4))
      have halB : isAligned (st7.getReg AbiReg.t5 + BitVec.ofInt 64 (env.tab.base64 (.t0 a))) 8 = true := by
        rw [ht5_7, hOffBase, Tab.base64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
      obtain ⟨st8, hrunB2, hothB2, ht5_8, hmemB2, hpc8⟩ :=
        loadMemOff_ld_correct_lm lkm env.hrom pre7 _ AbiReg.t5 AbiReg.t5 AbiReg.t6
          (by decide) (by decide) (by decide) (env.tab.base64 (.t0 a)) hlink7
          (linkResolved_sub_pc64 env pre7 clB _ hlink7) st7 hpc7' halB
      have hpB2 : PreservedFrameRegs fl (fun _ => False) st7 st8 :=
        preservedFrameRegs_of_noT5_scratch2 hnoT5 AbiReg.t5 AbiReg.t6 (by decide) (by decide) hothB2
      let pre8 := pre7 ++ clB
      have hpc8' : st8.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre8) := by rw [hpc8, lkm.totalSize_append pre7 clB]
      have hlink8 : lkm.linkSpec (pre8 ++ ct1 ++ (ct2 ++ post)) =
          .ok (env.code, env.labels) := by simpa [pre8, List.append_assoc] using hlink7
      let st9 := stepReg st8 AbiReg.t2 (evalShiftImm .slli (st8.getReg AbiReg.t2) 3#6)
        (BitVec.ofNat 64 (4 * (lkm.totalSize pre8 + 1)))
      obtain ⟨hrunSll, hpc9, ht2_9, hothSll, hmemSll, _⟩ :=
        run_shImm_step env pre8 _ .slli AbiReg.t2 AbiReg.t2 3#6 nonPreserved_t2 hlink8 st8 hpc8'
      have hpSll : PreservedFrameRegs fl (fun _ => False) st8 st9 :=
        PreservedFrameRegs.of_scratch1 AbiReg.t2 (by decide) hothSll
      let pre9 := pre8 ++ ct1
      have htwCt1 : lkm.totalSize ct1 = 1 := by simp only [ct1, Asm.slli, lkm.totalSize_instr]
      have hpc9' : st9.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre9) := by rw [hpc9, show lkm.totalSize pre9 = lkm.totalSize pre8 + 1 from by rw [lkm.totalSize_append pre8 ct1, htwCt1]]
      have hlink9 : lkm.linkSpec (pre9 ++ ct2 ++ post) =
          .ok (env.code, env.labels) := by simpa [pre9, List.append_assoc] using hlink8
      let st10 := stepReg st9 AbiReg.t2 (evalAlu .add (st9.getReg AbiReg.t5) (st9.getReg AbiReg.t2))
        (BitVec.ofNat 64 (4 * (lkm.totalSize pre9 + 1)))
      obtain ⟨hrunAdd, hpc10, ht2_10, hothAdd, hmemAdd, _⟩ :=
        run_alu_step env pre9 _ .add AbiReg.t2 AbiReg.t5 AbiReg.t2 nonPreserved_t2 hlink9 st9 hpc9'
      have hpAdd : PreservedFrameRegs fl (fun _ => False) st9 st10 :=
        PreservedFrameRegs.of_scratch1 AbiReg.t2 (by decide) hothAdd
      have hmem07 : st7.mem = st.mem := hmemBr1.trans (hmemSub.trans (hmemBr0.trans hmem04))
      have ht1_10 : st10.getReg AbiReg.t1 = t1Val :=
        (hothAdd _ (by decide)).trans ((hothSll _ (by decide)).trans ((hothB2 _ (by decide) (by decide)).trans
          ((hothBr1 _ (by decide)).trans ((hothSub _ (by decide)).trans ((hothBr0 _ (by decide)).trans ht1_4)))))
      have ht2_10v : st10.getReg AbiReg.t2 = L.base64 sa + BitVec.ofNat 64 (8 * vsi.toNat) := by
        rw [ht2_10, evalAlu, hothSll _ (by decide), ht5_8, hmem07, ht5_7, hOffBase, hbase64,
            ht2_9, hothB2 _ (by decide) (by decide), hothBr1 _ (by decide), hothSub _ (by decide),
            hothBr0 _ (by decide), ht2_4v, shl3_ofNat_eq vsi (by omega)]
      have ht3_10 : st10.getReg AbiReg.t3 = vk.toBitVec :=
        (hothAdd _ (by decide)).trans ((hothSll _ (by decide)).trans ((hothB2 _ (by decide) (by decide)).trans
          ((hothBr1 _ (by decide)).trans ((hothSub _ (by decide)).trans ((hothBr0 _ (by decide)).trans ht3_4)))))
      have hpcEq : lkm.totalSize pre9 + 1 = lkm.totalSize pre + lkm.totalSize codeSrc := by
        have htwCt2 : lkm.totalSize ct2 = 1 := by simp only [ct2, Asm.add, lkm.totalSize_instr]
        rw [hcEq]
        simp only [pre9, pre8, pre7, pre6, pre5, pre4, pre3, pre2, pre1, lkm.totalSize_append, htwCt1, htwCt2, htwSub]
        omega
      exact ⟨_, st10,
        run_trans hrun04 (run_trans (run_trans (run_trans hrunBr0 hrunSub) hrunBr1) (run_trans (run_trans hrunB2 hrunSll) hrunAdd)),
        by rw [hpc10, hpcEq], ht1_10, ht2_10v, ht3_10,
        hmemAdd.trans (hmemSll.trans (hmemB2.trans hmem07)),
        hp04.trans (hpBr0.trans (hpSub.trans (hpBr1.trans (hpB2.trans (hpSll.trans hpAdd)))))⟩
    · have hbound : ¬(vsi.toNat + vk.toNat ≤ (lm.arr64 sa).size) := by omega
      simp only [hbound, ↓reduceIte]
      have hbr1T : evalBranch .bltu (st6.getReg AbiReg.t0) (st6.getReg AbiReg.t2) = true := by
        rw [hcond1, decide_eq_true_iff]; omega
      exact ⟨_, st7, run_trans hrun04 (run_trans (run_trans hrunBr0 hrunSub) hrunBr1),
        by rw [hpcBr1, hbr1T]; rfl, hmemBr1.trans (hmemSub.trans (hmemBr0.trans hmem04)),
        hp04.trans (hpBr0.trans (hpSub.trans hpBr1))⟩
  · have hbound : ¬(vsi.toNat + vk.toNat ≤ (lm.arr64 sa).size) := by omega
    simp only [hbound, ↓reduceIte]
    have hbr0T : evalBranch .bltu (st4.getReg AbiReg.t0) (st4.getReg AbiReg.t3) = true := by
      rw [hcond0, decide_eq_true_iff]; omega
    exact ⟨_, st5, run_trans hrun04 hrunBr0, by rw [hpcBr0, hbr0T]; rfl,
      hmemBr0.trans hmem04, hp04.trans hpBr0⟩

private theorem reg_copy64_loop_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout)
    (da sa : TieredArray) (hda : env.tab.wordPosOkB da = true) (hsa : env.tab.wordPosOkB sa = true)
    (loopLbl doneLbl : String) (loopTarget doneTarget : Nat)
    (hloopLbl : lookupLabel env.labels loopLbl = some loopTarget)
    (hdoneLbl : lookupLabel env.labels doneLbl = some doneTarget)
    (pre post : List AsmItem)
    (hltLoop : loopTarget = lkm.totalSize pre)
    (hlink : lkm.linkSpec (pre ++ [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
      Asm.ld AbiReg.t4 AbiReg.t2, Asm.sd AbiReg.t1 AbiReg.t4,
      Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 8#12,
      Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] ++ post) = .ok (env.code, env.labels)) :
    ∀ n (lm : _root_.L.Mem) (di si : _root_.L.Word) (st : State),
      st.pc = BitVec.ofNat 64 (4 * loopTarget) →
      st.getReg AbiReg.t1 = L.base64 da + BitVec.ofNat 64 (8 * di.toNat) →
      st.getReg AbiReg.t2 = L.base64 sa + BitVec.ofNat 64 (8 * si.toNat) →
      st.getReg AbiReg.t3 = BitVec.ofNat 64 n →
      di.toNat + n ≤ (lm.arr64 da).size →
      si.toNat + n ≤ (lm.arr64 sa).size →
      ProgMemRel env.tab L st.mem lm →
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * doneTarget) ∧
        PreservedFrameRegs fl (fun _ => False) st r' ∧
        ProgMemRel env.tab L r'.mem (lm.copy64 da di sa si n) ∧
        MemEqOutside (L.arr64Span da) st.mem r'.mem := by
  intro n
  induction n with
  | zero =>
    intro lm di si st hpc ht1 ht2 ht3 _ _ hm
    have ⟨_, hl1⟩ := linkResolved_mid_split lkm pre [Asm.lbl loopLbl] _ post hlink
    have ⟨hlBeq, _⟩ := linkResolved_mid_split lkm (pre ++ [Asm.lbl loopLbl]) [Asm.beq AbiReg.t3 AbiReg.zero doneLbl] _ post hl1
    have hbr := run_br_step env (pre ++ [Asm.lbl loopLbl]) _ .beq AbiReg.t3 AbiReg.zero doneLbl doneTarget hdoneLbl (by decide)
      hlBeq st (by rw [lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero, ← hltLoop]; exact hpc)
    have hcond : evalBranch .beq (st.getReg AbiReg.t3) (st.getReg AbiReg.zero) = true := by
      rw [ht3, getReg_zero st]; decide
    obtain ⟨kBr, st', _, hrun, hpcBr, hothBr, _, hmemBr⟩ := hbr
    have hcopy : lm.copy64 da di sa si 0 = lm := by simp [_root_.L.Mem.copy64]
    rw [hcopy]
    exact ⟨kBr, st', hrun, by rw [hpcBr, hcond]; rfl,
      preservedFrameRegs_of_t6_s1 hothBr,
      by rw [hmemBr]; exact hm, fun _ _ => by rw [hmemBr]⟩
  | succ n ih =>
    intro lm di si st hpc ht1 ht2 ht3 hdi hsi hm
    have hltLoopEq : lkm.totalSize (pre ++ [Asm.lbl loopLbl]) = loopTarget := by
      rw [lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero, hltLoop]
    have ⟨_, hlR0⟩ := linkResolved_mid_split lkm pre [Asm.lbl loopLbl] _ post hlink
    have ⟨hl1, hlR1⟩ := linkResolved_mid_split lkm (pre ++ [Asm.lbl loopLbl]) [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]
      [Asm.ld AbiReg.t4 AbiReg.t2, Asm.sd AbiReg.t1 AbiReg.t4, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
       Asm.addi AbiReg.t2 AbiReg.t2 8#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] post hlR0
    have ⟨hl2, hlR2⟩ := linkResolved_mid_split lkm ((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl])
      [Asm.ld AbiReg.t4 AbiReg.t2]
      [Asm.sd AbiReg.t1 AbiReg.t4, Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 8#12,
       Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] post hlR1
    have ⟨hl3, hlR3⟩ := linkResolved_mid_split lkm (((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.ld AbiReg.t4 AbiReg.t2])
      [Asm.sd AbiReg.t1 AbiReg.t4]
      [Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 8#12,
       Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] post hlR2
    have ⟨hl4, hlR4⟩ := linkResolved_mid_split lkm ((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.ld AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4])
      [Asm.addi AbiReg.t1 AbiReg.t1 8#12]
      [Asm.addi AbiReg.t2 AbiReg.t2 8#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] post hlR3
    have ⟨hl5, hlR5⟩ := linkResolved_mid_split lkm (((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.ld AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) ++ [Asm.addi AbiReg.t1 AbiReg.t1 8#12])
      [Asm.addi AbiReg.t2 AbiReg.t2 8#12] [Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] post hlR4
    have ⟨hl6, hlR6⟩ := linkResolved_mid_split lkm ((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.ld AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) ++ [Asm.addi AbiReg.t1 AbiReg.t1 8#12]) ++ [Asm.addi AbiReg.t2 AbiReg.t2 8#12])
      [Asm.addi AbiReg.t3 AbiReg.t3 (-1#12)] [Asm.j loopLbl, Asm.lbl doneLbl] post hlR5
    have ⟨hl7, _⟩ := linkResolved_mid_split lkm (((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.ld AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) ++ [Asm.addi AbiReg.t1 AbiReg.t1 8#12]) ++ [Asm.addi AbiReg.t2 AbiReg.t2 8#12]) ++ [Asm.addi AbiReg.t3 AbiReg.t3 (-1#12)])
      [Asm.j loopLbl] [Asm.lbl doneLbl] post hlR6
    rcases hm.2.1 da hda with ⟨hcapD, _, _, _, _⟩
    rcases hm.2.1 sa hsa with ⟨_, hltS, _, _, hwordsS⟩
    have hnBound : n + 1 < 2 ^ 64 := by omega
    have hbr := run_br_step env (pre ++ [Asm.lbl loopLbl]) _ .beq AbiReg.t3 AbiReg.zero doneLbl doneTarget hdoneLbl (by decide)
      hl1 st (by rw [hltLoopEq]; exact hpc)
    have hcond : evalBranch .beq (st.getReg AbiReg.t3) (st.getReg AbiReg.zero) = false := by
      rw [ht3, getReg_zero st, evalBranch]
      exact beq_false_of_ne (BitVec.ofNat_ne_zero_of_lt (Nat.succ_pos n) hnBound)
    obtain ⟨_, st1, _, hrun1, hpc1Br, hoth1, _, hmem1⟩ := hbr
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize ((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl])) := by
      rw [hpc1Br, hcond]; simp only [Bool.false_eq_true, ↓reduceIte, lkm.totalSize_append, Asm.beq, Asm.br, lkm.totalSize_singleton]
    have halSrc : isAligned (st1.getReg AbiReg.t2) 8 = true := by
      rw [hoth1 _ (by decide), ht2]; exact isAligned8_add_mul8 _ (L.h64Align sa) si.toNat
    obtain ⟨hrun2, hpc2, ht4_2, hoth2, hmem2, _⟩ :=
      run_ld_zero_step env _ _ AbiReg.t4 AbiReg.t2 nonPreserved_t4 hl2 st1 hpc1' halSrc
    let st2 := stepReg st1 AbiReg.t4 (readWord64 st1.mem (st1.getReg AbiReg.t2))
      (BitVec.ofNat 64 (4 * (lkm.totalSize ((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) + 1)))
    have halDst : isAligned (st2.getReg AbiReg.t1) 8 = true := by
      rw [hoth2 _ (by decide), hoth1 _ (by decide), ht1]; exact isAligned8_add_mul8 _ (L.h64Align da) di.toNat
    have htwLd : lkm.totalSize [Asm.ld AbiReg.t4 AbiReg.t2] = 1 := by simp only [Asm.ld, lkm.totalSize_instr]
    have hrun3 := step_sd_zero env _ _ AbiReg.t1 AbiReg.t4 hl3 st2 (by rw [lkm.totalSize_append, htwLd]; exact hpc2) halDst
    let st3 : State :=
      { pc := BitVec.ofNat 64 (4 * (lkm.totalSize (((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.ld AbiReg.t4 AbiReg.t2]) + 1))
      , regs := st2.regs, mem := writeWord64 st2.mem (st2.getReg AbiReg.t1) (st2.getReg AbiReg.t4) }
    have htwSd : lkm.totalSize [Asm.sd AbiReg.t1 AbiReg.t4] = 1 := by simp only [Asm.sd, lkm.totalSize_instr]
    obtain ⟨hrun4, hpc4, ht1_4, hoth4, hmem4, _⟩ :=
      run_aluImm_step env _ _ .addi AbiReg.t1 AbiReg.t1 8#12 nonPreserved_t1 hl4 st3 (by rw [lkm.totalSize_append, htwSd])
    let st4 := stepReg st3 AbiReg.t1 (evalAluImm .addi (st3.getReg AbiReg.t1) 8#12)
      (BitVec.ofNat 64 (4 * (lkm.totalSize ((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.ld AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) + 1)))
    have htwA1 : lkm.totalSize [Asm.addi AbiReg.t1 AbiReg.t1 8#12] = 1 := by simp only [Asm.addi, lkm.totalSize_instr]
    obtain ⟨hrun5, hpc5, ht2_5, hoth5, hmem5, _⟩ :=
      run_aluImm_step env _ _ .addi AbiReg.t2 AbiReg.t2 8#12 nonPreserved_t2 hl5 st4 (by rw [lkm.totalSize_append, htwA1]; exact hpc4)
    let st5 := stepReg st4 AbiReg.t2 (evalAluImm .addi (st4.getReg AbiReg.t2) 8#12)
      (BitVec.ofNat 64 (4 * (lkm.totalSize (((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.ld AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) ++ [Asm.addi AbiReg.t1 AbiReg.t1 8#12]) + 1)))
    have htwA2 : lkm.totalSize [Asm.addi AbiReg.t2 AbiReg.t2 8#12] = 1 := by simp only [Asm.addi, lkm.totalSize_instr]
    obtain ⟨hrun6, hpc6, ht3_6, hoth6, hmem6, _⟩ :=
      run_aluImm_step env _ _ .addi AbiReg.t3 AbiReg.t3 (-1#12) nonPreserved_t3 hl6 st5 (by rw [lkm.totalSize_append, htwA2]; exact hpc5)
    let st6 := stepReg st5 AbiReg.t3 (evalAluImm .addi (st5.getReg AbiReg.t3) (-1#12))
      (BitVec.ofNat 64 (4 * (lkm.totalSize ((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.ld AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) ++ [Asm.addi AbiReg.t1 AbiReg.t1 8#12]) ++ [Asm.addi AbiReg.t2 AbiReg.t2 8#12]) + 1)))
    have htwA3 : lkm.totalSize [Asm.addi AbiReg.t3 AbiReg.t3 (-1#12)] = 1 := by simp only [Asm.addi, lkm.totalSize_instr]
    have hpc64J : 4 * (lkm.totalSize (((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.ld AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) ++ [Asm.addi AbiReg.t1 AbiReg.t1 8#12]) ++ [Asm.addi AbiReg.t2 AbiReg.t2 8#12]) ++ [Asm.addi AbiReg.t3 AbiReg.t3 (-1#12)]) + lkm.itemSize (.j loopLbl)) < 2 ^ 64 := by
      simpa [Asm.j, lkm.totalSize_singleton] using linkResolved_sub_pc64 env _ [Asm.j loopLbl] _ hl7
    obtain ⟨_, st7, hrun7, hpc7, hoth7, _, hmem7⟩ :=
      prog_step_j env _ _ loopLbl loopTarget hloopLbl hl7 hpc64J st6 (by rw [lkm.totalSize_append, htwA3]; exact hpc6)
    have ht4Val : st2.getReg AbiReg.t4 = (lm.arr64 sa)[si.toNat]!.toBitVec := by
      have hget : (lm.arr64 sa)[si.toNat]! = (lm.arr64 sa)[si.toNat]'(by omega) := getElem!_pos _ _ (by omega)
      rw [ht4_2, hget, hmem1]; change readWord64 st.mem (st1.getReg AbiReg.t2) = _
      rw [hoth1 _ (by decide), ht2]; exact hwordsS si.toNat (by omega)
    have ht1St2 : st2.getReg AbiReg.t1 = L.base64 da + BitVec.ofNat 64 (8 * di.toNat) := by
      rw [hoth2 _ (by decide), hoth1 _ (by decide)]; exact ht1
    have hst3Mem : st3.mem = writeWord64 st.mem (L.base64 da + BitVec.ofNat 64 (8 * di.toNat)) (lm.arr64 sa)[si.toNat]!.toBitVec := by
      dsimp only [st3]; rw [hmem2, hmem1, ht1St2, ht4Val]
    have hst7Mem : st7.mem = st3.mem := by rw [hmem7, hmem6, hmem5, hmem4]
    have hdi1 : (di + 1).toNat = di.toNat + 1 := by
      have := L.h64Valid da; simp [UInt64.toNat_add, Nat.mod_eq_of_lt (show di.toNat + 1 < 2 ^ 64 by omega)]
    have hsi1 : (si + 1).toNat = si.toNat + 1 := by
      simp [UInt64.toNat_add, Nat.mod_eq_of_lt (show si.toNat + 1 < 2 ^ 64 by omega)]
    have h8eq : sextImm12 8#12 = BitVec.ofNat 64 8 := by decide
    have ht1_7 : st7.getReg AbiReg.t1 = L.base64 da + BitVec.ofNat 64 (8 * (di + 1).toNat) := by
      rw [hoth7 _ (by decide)]; change st6.getReg AbiReg.t1 = _
      rw [hoth6 _ (by decide), hoth5 _ (by decide), ht1_4, evalAluImm]
      change st2.getReg AbiReg.t1 + sextImm12 8#12 = _
      rw [ht1St2, h8eq, BitVec.add_assoc, ← BitVec.ofNat_add, hdi1, show 8 * di.toNat + 8 = 8 * (di.toNat + 1) by omega]
    have ht2_7 : st7.getReg AbiReg.t2 = L.base64 sa + BitVec.ofNat 64 (8 * (si + 1).toNat) := by
      rw [hoth7 _ (by decide)]; change st6.getReg AbiReg.t2 = _
      rw [hoth6 _ (by decide), ht2_5, evalAluImm]
      change st4.getReg AbiReg.t2 + sextImm12 8#12 = _
      rw [hoth4 _ (by decide), show st3.getReg AbiReg.t2 = st2.getReg AbiReg.t2 from rfl,
          hoth2 _ (by decide), hoth1 _ (by decide), ht2, h8eq, BitVec.add_assoc, ← BitVec.ofNat_add, hsi1,
          show 8 * si.toNat + 8 = 8 * (si.toNat + 1) by omega]
    have ht3_7 : st7.getReg AbiReg.t3 = BitVec.ofNat 64 n := by
      rw [hoth7 _ (by decide)]; change st6.getReg AbiReg.t3 = _
      rw [ht3_6, evalAluImm]; change st4.getReg AbiReg.t3 + sextImm12 (-1#12) = _
      rw [hoth4 _ (by decide), show st3.getReg AbiReg.t3 = st2.getReg AbiReg.t3 from rfl,
          hoth2 _ (by decide), hoth1 _ (by decide), ht3]
      exact BitVec.ofNat_sub_one_eq_add_neg1 hnBound
    let lm1 := lm.set64 da di (lm.arr64 sa)[si.toNat]!
    have hm1 : ProgMemRel env.tab L st7.mem lm1 := by
      rw [hst7Mem, hst3Mem]; exact ProgMemRel.set64 hm da hda di _ (by omega)
    have hdiSize : (di + 1).toNat + n ≤ (lm1.arr64 da).size := by
      rw [hdi1]; simp only [_root_.L.Mem.arr64] at hdi
      simp only [lm1, _root_.L.Mem.arr64, _root_.L.Mem.set64, ↓reduceIte, Array.size_set!]; omega
    have hsiSize : (si + 1).toNat + n ≤ (lm1.arr64 sa).size := by
      rw [hsi1]; simp only [_root_.L.Mem.arr64] at hsi
      by_cases hds : sa = da
      · subst hds; simp only [lm1, _root_.L.Mem.arr64, _root_.L.Mem.set64, ↓reduceIte, Array.size_set!]; omega
      · simp only [lm1, _root_.L.Mem.arr64, _root_.L.Mem.set64, hds, ↓reduceIte]; omega
    obtain ⟨_, stEnd, hrunRest, hpcEnd, hpresRest, hmEnd, hpmRest⟩ :=
      ih lm1 (di + 1) (si + 1) st7 hpc7 ht1_7 ht2_7 ht3_7 hdiSize hsiSize hm1
    have hpmStep : MemEqOutside (L.arr64Span da) st.mem st7.mem := by
      rw [hst7Mem, hst3Mem]
      exact memEqOutside_writeWord64_arr64 L da di.toNat (Nat.lt_of_lt_of_le (by omega) hcapD) st.mem _
    have hpStep : PreservedFrameRegs fl (fun _ => False) st st7 :=
      (preservedFrameRegs_of_t6_s1 hoth1).trans
        ((PreservedFrameRegs.of_scratch1 AbiReg.t4 (by decide) hoth2).trans
          ((⟨⟨rfl, rfl, rfl, rfl⟩, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩ : PreservedFrameRegs fl (fun _ => False) st2 st3).trans
            ((PreservedFrameRegs.of_scratch1 AbiReg.t1 (by decide) hoth4).trans
              ((PreservedFrameRegs.of_scratch1 AbiReg.t2 (by decide) hoth5).trans
                ((PreservedFrameRegs.of_scratch1 AbiReg.t3 (by decide) hoth6).trans
                  (preservedFrameRegs_of_t6_s1 hoth7))))))
    have hrunStep := run_trans (run_trans (run_trans (run_trans (run_trans (run_trans hrun1 hrun2) hrun3) hrun4) hrun5) hrun6) hrun7
    exact ⟨_, stEnd, run_trans hrunStep hrunRest, hpcEnd, hpStep.trans hpresRest, hmEnd, hpmStep.trans hpmRest⟩

theorem reg_copy64_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hal : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (d : WArr) (di : Expr) (s : WArr) (si n : Expr)
    (hdOk : warrOkB env.tab fl.nlocals d = true) (hdiOk : exprOkB env.tab fl.nlocals di = true)
    (hsOk : warrOkB env.tab fl.nlocals s = true) (hsiOk : exprOkB env.tab fl.nlocals si = true)
    (hnOk : exprOkB env.tab fl.nlocals n = true)
    (hVfD : WArrVarsInFrame fl d) (hVfDI : ExprVarsInFrame fl di)
    (hVfS : WArrVarsInFrame fl s) (hVfSI : ExprVarsInFrame fl si) (hVfN : ExprVarsInFrame fl n)
    (hTmp : usedTempsStmt (.copy64 d di s si n) ≤ fl.usedTemps)
    (pfx : String) (lblId : Nat) (brkLbl : Option String) (retLbl : String) (isTail : Bool)
    (pre post : List AsmItem)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hnoT5 : fl.useT5Gp = false) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOkR L fl sp st loc)
    (hlink : lkm.linkSpec (pre ++ (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.copy64 d di s si n)).1 ++ post) =
      .ok (env.code, env.labels))
    (p : _root_.L.Prog) :
    let codeS := (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.copy64 d di s si n)).1
    match _root_.L.step p (fun _ => throw .outOfFuel) (.copy64 d di s si n) { mem := lm, loc := loc } with
    | .ok (_, st') =>
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize codeS)) ∧
        PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) st r' ∧
        ProgMemRel env.tab L r'.mem st'.mem ∧
        ProgFrameOkR L fl sp r' st'.loc ∧
        ProgMemOutside (FnWriteMaskR L fl sp) st.mem r'.mem
    | .error _ =>
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) st r' ∧
        ProgMemOutside (FnWriteMaskR L fl sp) st.mem r'.mem := by
  have hvalid : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  dsimp only [usedTempsStmt] at hTmp
  let dArr := (evalWArrTierToTempR env.tab fl 0 d).1
  let sArr := (evalWArrTierToTempR env.tab fl 2 s).1
  let loopLbl := s!"{pfx}_c64_{lblId}"
  let doneLbl := s!"{pfx}_c64_done_{lblId}"
  let c0 := (evalWArrTierToTempR env.tab fl 0 d).2
  let c1 := compileETo env.tab fl 1 AbiReg.a0 di ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 1)
  let c2 := (evalWArrTierToTempR env.tab fl 2 s).2
  let c3 := compileETo env.tab fl 3 AbiReg.a0 si ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 3)
  let c4 := compileETo env.tab fl 4 AbiReg.a0 n ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 4)
  let codeDst :=
    loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 0) ++
    [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] ++
    loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (env.tab.len64 (.t0 dArr)) ++
    loadMemOff .ld AbiReg.t1 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 1) ++
    loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 4) ++
    [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3, Asm.bltu AbiReg.t0 AbiReg.t1 errLabel] ++
    loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (env.tab.base64 (.t0 dArr)) ++
    [Asm.slli AbiReg.t1 AbiReg.t1 3#6, Asm.add AbiReg.t1 AbiReg.t5 AbiReg.t1]
  let codeSrc :=
    loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t2 (fl.tempSlotOff 2) ++
    [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] ++
    loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (env.tab.len64 (.t0 sArr)) ++
    loadMemOff .ld AbiReg.t2 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 3) ++
    [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3, Asm.bltu AbiReg.t0 AbiReg.t2 errLabel] ++
    loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (env.tab.base64 (.t0 sArr)) ++
    [Asm.slli AbiReg.t2 AbiReg.t2 3#6, Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2]
  let codeLoop :=
    [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl, Asm.ld AbiReg.t4 AbiReg.t2 0#12,
     Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 8#12,
     Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl]
  have hcodeEq : (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.copy64 d di s si n)).1 =
      c0 ++ c1 ++ c2 ++ c3 ++ c4 ++ codeDst ++ codeSrc ++ codeLoop := by
    cases d <;> cases s <;>
      dsimp only [compileSR, dArr, sArr, evalWArrTierToTempR, c0, c1, c2, c3, c4, codeDst, codeSrc, codeLoop, loopLbl, doneLbl] <;>
      simp only [List.append_assoc] <;> rfl
  rw [hcodeEq] at hlink
  have hlink0 : lkm.linkSpec (pre ++ c0 ++ (c1 ++ c2 ++ c3 ++ c4 ++ codeDst ++ codeSrc ++ codeLoop ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
  have hvacT5 : ∀ s, T5GpOk L fl s := fun _ h => by rw [hnoT5] at h; cases h
  have hw0 : 0 + max 1 (warrUsedTemps d) ≤ fl.usedTemps := by
    cases d <;> dsimp only [warrUsedTemps] at hTmp ⊢ <;> omega
  have hs0Sim := reg_evalWArrTierToTempR_sim env L fl hfl lm loc hal hlo hhi d hdOk hVfD 0 hw0 pre _ hlink0 st hpc hgp (hvacT5 _) hsp hm hf
  rcases warr_pure d ⟨lm, loc⟩ with ⟨da, hdaW⟩ | hdaW
  · rw [hdaW] at hs0Sim
    obtain ⟨k0, st1, du, hrun0, hpc0, hdaEq, hdaOk, hdoLen, hdoBase, hslot0, hp0, hout0⟩ := hs0Sim
    have hpm0 : ProgMemOutside (FnWriteMaskR L fl sp) st.mem st1.mem :=
      ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) hout0
    have hm1 := ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) hout0 hm
    have hf1 := ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) (hp0.mono (fun _ h => False.elim h)) hout0 hf
    let pre1 := pre ++ c0
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by rw [hpc0, lkm.totalSize_append pre c0]
    have hlink1 : lkm.linkSpec (pre1 ++ c1 ++ (c2 ++ c3 ++ c4 ++ codeDst ++ codeSrc ++ codeLoop ++ post)) =
        .ok (env.code, env.labels) := by simpa [pre1, List.append_assoc] using hlink0
    have hs1Sim := reg_evalToTemp_sim env L fl hfl lm loc hal hlo hhi 1 di hdiOk hVfDI (by omega) pre1 _ hlink1
      st1 hpc1' (hp0.abi.gp.trans hgp) (hvacT5 _) (hp0.abi.sp.trans hsp) hm1 hf1
    rcases _root_.L.evalE_pure di ⟨lm, loc⟩ with ⟨vdi, hdiE⟩ | hdiE
    · rw [hdiE] at hs1Sim
      obtain ⟨k1, st2, hrun1, hpc1, hslot1, hp1, hout1⟩ := hs1Sim
      have hpm1 : ProgMemOutside (FnWriteMaskR L fl sp) st1.mem st2.mem :=
        ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (by omega : 1 ≤ fl.usedTemps)) hout1
      have hm2 := ProgMemRel.of_tempSpanR hlo hhi (by omega : 1 ≤ fl.usedTemps) hout1 hm1
      have hf2 := ProgFrameOkR.of_preserved_temp hfl hvalid (by omega : 1 ≤ fl.usedTemps) (hp1.mono (fun _ h => False.elim h)) hout1 hf1
      let pre2 := pre1 ++ c1
      have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) := by rw [hpc1, lkm.totalSize_append pre1 c1]
      have hlink2 : lkm.linkSpec (pre2 ++ c2 ++ (c3 ++ c4 ++ codeDst ++ codeSrc ++ codeLoop ++ post)) =
          .ok (env.code, env.labels) := by simpa [pre2, List.append_assoc] using hlink1
      have hw2 : 2 + max 1 (warrUsedTemps s) ≤ fl.usedTemps := by
        cases s <;> dsimp only [warrUsedTemps] at hTmp ⊢ <;> omega
      have hs2Sim := reg_evalWArrTierToTempR_sim env L fl hfl lm loc hal hlo hhi s hsOk hVfS 2 hw2 pre2 _ hlink2
        st2 hpc2' ((hp0.trans hp1).abi.gp.trans hgp) (hvacT5 _) ((hp0.trans hp1).abi.sp.trans hsp) hm2 hf2
      rcases warr_pure s ⟨lm, loc⟩ with ⟨sa, hsaW⟩ | hsaW
      · rw [hsaW] at hs2Sim
        obtain ⟨k2, st3, su, hrun2, hpc2, hsaEq, hsaOk, hsoLen, hsoBase, hslot2, hp2, hout2⟩ := hs2Sim
        have hpm2 : ProgMemOutside (FnWriteMaskR L fl sp) st2.mem st3.mem :=
          ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (by omega : 2 ≤ fl.usedTemps)) hout2
        have hm3 := ProgMemRel.of_tempSpanR hlo hhi (by omega : 2 ≤ fl.usedTemps) hout2 hm2
        have hf3 := ProgFrameOkR.of_preserved_temp hfl hvalid (by omega : 2 ≤ fl.usedTemps) (hp2.mono (fun _ h => False.elim h)) hout2 hf2
        let pre3 := pre2 ++ c2
        have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre3) := by rw [hpc2, lkm.totalSize_append pre2 c2]
        have hlink3 : lkm.linkSpec (pre3 ++ c3 ++ (c4 ++ codeDst ++ codeSrc ++ codeLoop ++ post)) =
            .ok (env.code, env.labels) := by simpa [pre3, List.append_assoc] using hlink2
        have hs3Sim := reg_evalToTemp_sim env L fl hfl lm loc hal hlo hhi 3 si hsiOk hVfSI (by omega) pre3 _ hlink3
          st3 hpc3' ((hp0.trans (hp1.trans hp2)).abi.gp.trans hgp) (hvacT5 _) ((hp0.trans (hp1.trans hp2)).abi.sp.trans hsp) hm3 hf3
        rcases _root_.L.evalE_pure si ⟨lm, loc⟩ with ⟨vsi, hsiE⟩ | hsiE
        · rw [hsiE] at hs3Sim
          obtain ⟨k3, st4, hrun3, hpc3, hslot3, hp3, hout3⟩ := hs3Sim
          have hpm3 : ProgMemOutside (FnWriteMaskR L fl sp) st3.mem st4.mem :=
            ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (by omega : 3 ≤ fl.usedTemps)) hout3
          have hm4 := ProgMemRel.of_tempSpanR hlo hhi (by omega : 3 ≤ fl.usedTemps) hout3 hm3
          have hf4 := ProgFrameOkR.of_preserved_temp hfl hvalid (by omega : 3 ≤ fl.usedTemps) (hp3.mono (fun _ h => False.elim h)) hout3 hf3
          let pre4 := pre3 ++ c3
          have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre4) := by rw [hpc3, lkm.totalSize_append pre3 c3]
          have hlink4 : lkm.linkSpec (pre4 ++ c4 ++ (codeDst ++ codeSrc ++ codeLoop ++ post)) =
              .ok (env.code, env.labels) := by simpa [pre4, List.append_assoc] using hlink3
          have hs4Sim := reg_evalToTemp_sim env L fl hfl lm loc hal hlo hhi 4 n hnOk hVfN (by omega) pre4 _ hlink4
            st4 hpc4' ((hp0.trans (hp1.trans (hp2.trans hp3))).abi.gp.trans hgp) (hvacT5 _)
            ((hp0.trans (hp1.trans (hp2.trans hp3))).abi.sp.trans hsp) hm4 hf4
          rcases _root_.L.evalE_pure n ⟨lm, loc⟩ with ⟨vk, hnE⟩ | hnE
          · rw [hnE] at hs4Sim
            obtain ⟨k4, st5, hrun4, hpc4, hslot4, hp4, hout4⟩ := hs4Sim
            have hm5 := ProgMemRel.of_tempSpanR hlo hhi (by omega : 4 ≤ fl.usedTemps) hout4 hm4
            have hf5 := ProgFrameOkR.of_preserved_temp hfl hvalid (by omega : 4 ≤ fl.usedTemps) (hp4.mono (fun _ h => False.elim h)) hout4 hf4
            have hout04 : MemEqOutside (tempSpanR fl sp 0) st.mem st5.mem :=
              hout0.trans ((hout1.mono (tempSpanR_mono fl sp hvalid (by omega : 0 ≤ 1) (by omega))).trans
                ((hout2.mono (tempSpanR_mono fl sp hvalid (by omega : 0 ≤ 2) (by omega))).trans
                  ((hout3.mono (tempSpanR_mono fl sp hvalid (by omega : 0 ≤ 3) (by omega))).trans
                    (hout4.mono (tempSpanR_mono fl sp hvalid (by omega : 0 ≤ 4) (by omega))))))
            have hpmA : ProgMemOutside (FnWriteMaskR L fl sp) st.mem st5.mem :=
              ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) hout04
            have hpA : PreservedFrameRegs fl (fun _ => False) st st5 := hp0.trans (hp1.trans (hp2.trans (hp3.trans hp4)))
            have hrunA := run_trans (run_trans (run_trans (run_trans hrun0 hrun1) hrun2) hrun3) hrun4
            have hs0_5 : readWord64 st5.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff 0)) = du.toBitVec := by
              rw [readWord64_tempSlotR_of_tempSpanR (by omega : 0 < 4) (by omega) hvalid hout4,
                  readWord64_tempSlotR_of_tempSpanR (by omega : 0 < 3) (by omega) hvalid hout3,
                  readWord64_tempSlotR_of_tempSpanR (by omega : 0 < 2) (by omega) hvalid hout2,
                  readWord64_tempSlotR_of_tempSpanR (by omega : 0 < 1) (by omega) hvalid hout1]; exact hslot0
            have hs1_5 : readWord64 st5.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff 1)) = vdi.toBitVec := by
              rw [readWord64_tempSlotR_of_tempSpanR (by omega : 1 < 4) (by omega) hvalid hout4,
                  readWord64_tempSlotR_of_tempSpanR (by omega : 1 < 3) (by omega) hvalid hout3,
                  readWord64_tempSlotR_of_tempSpanR (by omega : 1 < 2) (by omega) hvalid hout2]; exact hslot1
            have hs2_5 : readWord64 st5.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff 2)) = su.toBitVec := by
              rw [readWord64_tempSlotR_of_tempSpanR (by omega : 2 < 4) (by omega) hvalid hout4,
                  readWord64_tempSlotR_of_tempSpanR (by omega : 2 < 3) (by omega) hvalid hout3]; exact hslot2
            have hs3_5 : readWord64 st5.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff 3)) = vsi.toBitVec := by
              rw [readWord64_tempSlotR_of_tempSpanR (by omega : 3 < 4) (by omega) hvalid hout4]; exact hslot3
            let pre5 := pre4 ++ c4
            have hpc5' : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre5) := by rw [hpc4, lkm.totalSize_append pre4 c4]
            have hlink5 : lkm.linkSpec (pre5 ++ codeDst ++ (codeSrc ++ codeLoop ++ post)) =
                .ok (env.code, env.labels) := by simpa [pre5, List.append_assoc] using hlink4
            have hdst := reg_warr_dst_setup_sim env L fl lm hal dArr du vdi vk da hdaOk
              hdoLen hdoBase pre5 codeDst (codeSrc ++ codeLoop ++ post) rfl st5 hpc5'
              (hpA.abi.gp.trans hgp) hnoT5 (hpA.abi.sp.trans hsp) hm5 hs0_5 hs1_5 hslot4 hlink5
            have hstepOk : _root_.L.step p (fun _ => throw .outOfFuel) (.copy64 d di s si n) { mem := lm, loc := loc } =
                if vdi.toNat + vk.toNat ≤ (lm.arr64 da).size ∧ vsi.toNat + vk.toNat ≤ (lm.arr64 sa).size then
                  .ok (Sig.normal, { mem := lm.copy64 da vdi sa vsi vk.toNat, loc := loc })
                else .error .oob := by
              simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE, hsaW, hsiE, hnE, get, getThe,
                MonadStateOf.get, StateT.get, set, MonadStateOf.set, throw, throwThe, MonadExceptOf.throw, Pure.pure, Except.pure]
              by_cases hb : vdi.toNat + vk.toNat ≤ (lm.arr64 da).size ∧ vsi.toNat + vk.toNat ≤ (lm.arr64 sa).size <;>
                simp only [hb, ↓reduceIte] <;> rfl
            rw [hstepOk]
            by_cases hbd : vdi.toNat + vk.toNat ≤ (lm.arr64 da).size
            · simp only [hbd, ↓reduceIte] at hdst
              obtain ⟨_, st6, hrunD, hpc6, ht1_6, ht3_6, hmemD, hpD⟩ := hdst
              let pre6 := pre5 ++ codeDst
              have hpc6' : st6.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre6) := by rw [hpc6, lkm.totalSize_append pre5 codeDst]
              have hlink6 : lkm.linkSpec (pre6 ++ codeSrc ++ (codeLoop ++ post)) =
                  .ok (env.code, env.labels) := by simpa [pre6, List.append_assoc] using hlink5
              have hsrc := reg_warr_src_setup_sim env L fl lm hal sArr su vsi vk sa hsaOk
                (L.base64 da + BitVec.ofNat 64 (8 * vdi.toNat)) hsoLen hsoBase pre6 codeSrc (codeLoop ++ post) rfl
                st6 hpc6' (hpD.abi.gp.trans (hpA.abi.gp.trans hgp)) hnoT5 (hpD.abi.sp.trans (hpA.abi.sp.trans hsp))
                (hmemD ▸ hm5) ht1_6 ht3_6 (hmemD ▸ hs2_5) (hmemD ▸ hs3_5) hlink6
              by_cases hbs : vsi.toNat + vk.toNat ≤ (lm.arr64 sa).size
              · simp only [hbd, hbs, and_self, ↓reduceIte] at hsrc ⊢
                obtain ⟨_, st7, hrunS, hpc7, ht1_7, ht2_7, ht3_7, hmemS, hpS⟩ := hsrc
                let pre7 := pre6 ++ codeSrc
                have hpc7' : st7.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre7) := by rw [hpc7, lkm.totalSize_append pre6 codeSrc]
                have hlink7 : lkm.linkSpec (pre7 ++ codeLoop ++ post) =
                    .ok (env.code, env.labels) := by simpa [pre7, List.append_assoc] using hlink6
                have hloopLbl := lookupLabel_of_lbl_lm lkm pre7
                  ([Asm.beq AbiReg.t3 AbiReg.zero doneLbl, Asm.ld AbiReg.t4 AbiReg.t2 0#12,
                    Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
                    Asm.addi AbiReg.t2 AbiReg.t2 8#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12),
                    Asm.j loopLbl, Asm.lbl doneLbl] ++ post) loopLbl (by simpa [codeLoop, List.append_assoc] using hlink7)
                have hdoneLbl := lookupLabel_of_lbl_lm lkm
                  (pre7 ++ [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl, Asm.ld AbiReg.t4 AbiReg.t2 0#12,
                    Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
                    Asm.addi AbiReg.t2 AbiReg.t2 8#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl])
                  post doneLbl (by simpa [codeLoop, List.append_assoc] using hlink7)
                have htwDone : lkm.totalSize codeLoop =
                    lkm.totalSize [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
                      Asm.ld AbiReg.t4 AbiReg.t2 0#12, Asm.sd AbiReg.t1 AbiReg.t4 0#12,
                      Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 8#12,
                      Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl] := by
                  rw [show codeLoop = [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
                    Asm.ld AbiReg.t4 AbiReg.t2 0#12, Asm.sd AbiReg.t1 AbiReg.t4 0#12,
                    Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 8#12,
                    Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl] ++ [Asm.lbl doneLbl] by simp [codeLoop]]
                  simp only [lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero]
                have hdoneTgt : lkm.totalSize (pre7 ++ [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
                    Asm.ld AbiReg.t4 AbiReg.t2 0#12, Asm.sd AbiReg.t1 AbiReg.t4 0#12,
                    Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 8#12,
                    Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl]) = lkm.totalSize pre7 + lkm.totalSize codeLoop := by
                  rw [lkm.totalSize_append, ← htwDone]
                have hlinkL : lkm.linkSpec (pre7 ++ [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
                    Asm.ld AbiReg.t4 AbiReg.t2, Asm.sd AbiReg.t1 AbiReg.t4, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
                    Asm.addi AbiReg.t2 AbiReg.t2 8#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl,
                    Asm.lbl doneLbl] ++ post) = .ok (env.code, env.labels) := by
                  simpa [codeLoop, Asm.ld, Asm.sd, List.append_assoc] using hlink7
                have hmem57 : st7.mem = st5.mem := hmemS.trans hmemD
                obtain ⟨_, r', hrunL, hpcR, hpL, hmR, hmeqL⟩ :=
                  reg_copy64_loop_sim env L fl da sa hdaOk hsaOk loopLbl doneLbl
                    (lkm.totalSize pre7) (lkm.totalSize pre7 + lkm.totalSize codeLoop)
                    hloopLbl (by rw [← hdoneTgt]; exact hdoneLbl) pre7 post rfl hlinkL
                    vk.toNat lm vdi vsi st7 hpc7' ht1_7 ht2_7 (by rw [ht3_7, u64_toBitVec_eq_ofNat]) hbd hbs (hmem57 ▸ hm5)
                have hmeq5R : MemEqOutside (L.arr64Span da) st5.mem r'.mem := by rw [← hmem57]; exact hmeqL
                have h64Disj : MemDisjoint (L.arr64Span da) L.stackSpan :=
                  MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid da) L.stackSpan_valid (L.h64DisjStack da hdaOk)
                have hpcEq : lkm.totalSize pre7 + lkm.totalSize codeLoop =
                    lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.copy64 d di s si n)).1 := by
                  rw [hcodeEq]
                  simp only [pre7, pre6, pre5, pre4, pre3, pre2, pre1, lkm.totalSize_append]; omega
                exact ⟨_, r', run_trans (run_trans (run_trans hrunA hrunD) hrunS) hrunL,
                  by rw [hpcR, hpcEq],
                  (hpA.trans (hpD.trans (hpS.trans hpL))).mono (fun _ h => False.elim h),
                  hmR,
                  ProgFrameOkR.of_mem_outside_stack hfl hlo hhi (L.arr64Span da) h64Disj (hpD.trans (hpS.trans hpL)) hmeq5R hf5,
                  hpmA.trans (ProgMemOutside.of_memEqOutside (fun _ ha => Or.inr (Or.inr (Or.inr ⟨da, hdaOk, ha⟩))) hmeq5R)⟩
              · simp only [hbd, hbs, and_false, ↓reduceIte] at hsrc ⊢
                obtain ⟨_, r', hrunS, hpcR, hmemS, hpS⟩ := hsrc
                exact ⟨_, r', run_trans (run_trans hrunA hrunD) hrunS, hpcR,
                  (hpA.trans (hpD.trans hpS)).mono (fun _ h => False.elim h),
                  by rw [hmemS, hmemD]; exact hpmA⟩
            · simp only [hbd, false_and, ↓reduceIte] at hdst ⊢
              obtain ⟨_, r', hrunD, hpcR, hmemD, hpD⟩ := hdst
              exact ⟨_, r', run_trans hrunA hrunD, hpcR, (hpA.trans hpD).mono (fun _ h => False.elim h),
                by rw [hmemD]; exact hpmA⟩
          · rw [hnE] at hs4Sim
            have hstepErr : _root_.L.step p (fun _ => throw .outOfFuel) (.copy64 d di s si n) ⟨lm, loc⟩ = .error .oob := by
              simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE, hsaW, hsiE, hnE]
            rw [hstepErr]; obtain ⟨_, st', hrun4, hpc4, hp4, hout4⟩ := hs4Sim
            exact ⟨_, st', run_trans (run_trans (run_trans (run_trans hrun0 hrun1) hrun2) hrun3) hrun4, hpc4,
              (hp0.trans (hp1.trans (hp2.trans (hp3.trans hp4)))).mono (fun _ h => False.elim h),
              hpm0.trans (hpm1.trans (hpm2.trans (hpm3.trans (ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (by omega : 4 ≤ fl.usedTemps)) hout4))))⟩
        · rw [hsiE] at hs3Sim
          have hstepErr : _root_.L.step p (fun _ => throw .outOfFuel) (.copy64 d di s si n) ⟨lm, loc⟩ = .error .oob := by
            simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE, hsaW, hsiE]
          rw [hstepErr]; obtain ⟨_, st', hrun3, hpc3, hp3, hout3⟩ := hs3Sim
          exact ⟨_, st', run_trans (run_trans (run_trans hrun0 hrun1) hrun2) hrun3, hpc3,
            (hp0.trans (hp1.trans (hp2.trans hp3))).mono (fun _ h => False.elim h),
            hpm0.trans (hpm1.trans (hpm2.trans (ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (by omega : 3 ≤ fl.usedTemps)) hout3)))⟩
      · rw [hsaW] at hs2Sim
        have hstepErr : _root_.L.step p (fun _ => throw .outOfFuel) (.copy64 d di s si n) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE, hsaW]
        rw [hstepErr]; obtain ⟨_, st', hrun2, hpc2, hp2, hout2⟩ := hs2Sim
        exact ⟨_, st', run_trans (run_trans hrun0 hrun1) hrun2, hpc2,
          (hp0.trans (hp1.trans hp2)).mono (fun _ h => False.elim h),
          hpm0.trans (hpm1.trans (ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (by omega : 2 ≤ fl.usedTemps)) hout2))⟩
    · rw [hdiE] at hs1Sim
      have hstepErr : _root_.L.step p (fun _ => throw .outOfFuel) (.copy64 d di s si n) ⟨lm, loc⟩ = .error .oob := by
        simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE]
      rw [hstepErr]; obtain ⟨_, st', hrun1, hpc1, hp1, hout1⟩ := hs1Sim
      exact ⟨_, st', run_trans hrun0 hrun1, hpc1, (hp0.trans hp1).mono (fun _ h => False.elim h),
        hpm0.trans (ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (by omega : 1 ≤ fl.usedTemps)) hout1)⟩
  · rw [hdaW] at hs0Sim
    have hstepErr : _root_.L.step p (fun _ => throw .outOfFuel) (.copy64 d di s si n) ⟨lm, loc⟩ = .error .oob := by
      simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hdaW]
    rw [hstepErr]; obtain ⟨_, st', hrun0, hpc0, hp0, hout0⟩ := hs0Sim
    exact ⟨_, st', hrun0, hpc0, hp0.mono (fun _ h => False.elim h),
      ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) hout0⟩

private theorem reg_copy8w_src_check_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (fl : FrameLayout) {sp : BitVec 64}
    (hal : isAligned sp 8 = true) (bytes : Array UInt8) (hlenLt : bytes.size < 2 ^ 64)
    (vsi vk : _root_.L.Word) (t1Val t5Val : BitVec 64)
    (pre codeCheck post : List AsmItem)
    (hcodeCheck : codeCheck =
      loadMemOff .ld AbiReg.t2 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 3) ++
      [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3,
       Asm.bltu AbiReg.t0 AbiReg.t2 errLabel, Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2])
    (hlink : lkm.linkSpec (pre ++ codeCheck ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hsp : st.getReg AbiReg.sp = sp)
    (ht0 : st.getReg AbiReg.t0 = BitVec.ofNat 64 bytes.size)
    (ht1 : st.getReg AbiReg.t1 = t1Val) (ht3 : st.getReg AbiReg.t3 = vk.toBitVec)
    (ht5 : st.getReg AbiReg.t5 = t5Val)
    (hslot3 : readWord64 st.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff 3)) = vsi.toBitVec) :
    if vsi.toNat + vk.toNat ≤ bytes.size then
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize codeCheck)) ∧
        r'.getReg AbiReg.t1 = t1Val ∧
        r'.getReg AbiReg.t2 = t5Val + BitVec.ofNat 64 vsi.toNat ∧
        r'.getReg AbiReg.t3 = vk.toBitVec ∧
        r'.mem = st.mem ∧
        PreservedFrameRegs fl (fun _ => False) st r'
    else
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        r'.mem = st.mem ∧
        PreservedFrameRegs fl (fun _ => False) st r' := by
  let cl := loadMemOff .ld AbiReg.t2 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 3)
  let cb0 := [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel]
  let cs0 := [Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3]
  let cb1 := [Asm.bltu AbiReg.t0 AbiReg.t2 errLabel]
  let ca := [Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2]
  have hcEq : codeCheck = cl ++ cb0 ++ cs0 ++ cb1 ++ ca := by
    rw [hcodeCheck]; simp [cl, cb0, cs0, cb1, ca, List.append_assoc]
  rw [hcEq] at hlink
  have hlink0 : lkm.linkSpec (pre ++ cl ++ (cb0 ++ cs0 ++ cb1 ++ ca ++ post)) = .ok (env.code, env.labels) := by
    simpa [List.append_assoc] using hlink
  have hal3 : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (fl.tempSlotOff 3)) 8 = true := by
    rw [hsp, tempSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hal _
  obtain ⟨st1, hrun0, hoth0, ht2_1, hmem0, hpc1⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre _ AbiReg.t2 AbiReg.sp AbiReg.t6
      (by decide) (by decide) (by decide) (fl.tempSlotOff 3) hlink0
      (linkResolved_sub_pc64 env pre cl _ hlink0) st hpc hal3
  have hp0 : PreservedFrameRegs fl (fun _ => False) st st1 :=
    PreservedFrameRegs.of_scratch2 AbiReg.t2 AbiReg.t6 (by decide) (by decide) hoth0
  let pre1 := pre ++ cl
  have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by rw [hpc1, lkm.totalSize_append pre cl]
  have hlink1 : lkm.linkSpec (pre1 ++ cb0 ++ (cs0 ++ cb1 ++ ca ++ post)) = .ok (env.code, env.labels) := by
    simpa [pre1, List.append_assoc] using hlink0
  have ht0_1 : st1.getReg AbiReg.t0 = BitVec.ofNat 64 bytes.size := (hoth0 _ (by decide) (by decide)).trans ht0
  have ht1_1 : st1.getReg AbiReg.t1 = t1Val := (hoth0 _ (by decide) (by decide)).trans ht1
  have ht2Val : st1.getReg AbiReg.t2 = vsi.toBitVec := by rw [ht2_1, hsp, hslot3]
  have ht3_1 : st1.getReg AbiReg.t3 = vk.toBitVec := (hoth0 _ (by decide) (by decide)).trans ht3
  have ht5_1 : st1.getReg AbiReg.t5 = t5Val := (hoth0 _ (by decide) (by decide)).trans ht5
  have hbr0 := run_br_step env pre1 _ .bltu AbiReg.t0 AbiReg.t3 errLabel env.errTarget env.herrLbl (by decide) hlink1 st1 hpc1'
  have hcond0 : evalBranch .bltu (st1.getReg AbiReg.t0) (st1.getReg AbiReg.t3) = decide (bytes.size < vk.toNat) := by
    rw [ht0_1, ht3_1, u64_toBitVec_eq_ofNat]; exact evalBranch_bltu_nat hlenLt vk.toBitVec.isLt
  obtain ⟨_, st2, _, hrun1, hpc2Br, hoth1Br, _, hmem1Br⟩ := hbr0
  have hp1Br : PreservedFrameRegs fl (fun _ => False) st1 st2 :=
    preservedFrameRegs_of_t6_s1 hoth1Br
  by_cases hkn : vk.toNat ≤ bytes.size
  · have hbr0F : evalBranch .bltu (st1.getReg AbiReg.t0) (st1.getReg AbiReg.t3) = false := by
      rw [hcond0, decide_eq_false_iff_not]; omega
    let pre2 := pre1 ++ cb0
    have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) := by
      rw [hpc2Br, hbr0F]; simp only [Bool.false_eq_true, ↓reduceIte]
      exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (lkm.totalSize_append pre1 cb0).symm
    have hlink2 : lkm.linkSpec (pre2 ++ cs0 ++ (cb1 ++ ca ++ post)) = .ok (env.code, env.labels) := by
      simpa [pre2, List.append_assoc] using hlink1
    let st3 := stepReg st2 AbiReg.t0 (evalAlu .sub (st2.getReg AbiReg.t0) (st2.getReg AbiReg.t3))
      (BitVec.ofNat 64 (4 * (lkm.totalSize pre2 + 1)))
    obtain ⟨hrun2, hpc3, ht0_3, hoth2, hmem2, _⟩ :=
      run_alu_step env pre2 _ .sub AbiReg.t0 AbiReg.t0 AbiReg.t3 nonPreserved_t0 hlink2 st2 hpc2'
    have hp2 : PreservedFrameRegs fl (fun _ => False) st2 st3 :=
      PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hoth2
    have ht0_3v : st3.getReg AbiReg.t0 = BitVec.ofNat 64 (bytes.size - vk.toNat) := by
      rw [ht0_3, evalAlu, hoth1Br _ (by decide), hoth1Br _ (by decide), ht0_1, ht3_1, u64_toBitVec_eq_ofNat]
      exact bitvec_sub_ofNat_eq hlenLt hkn
    let pre3 := pre2 ++ cs0
    have htws : lkm.totalSize cs0 = 1 := by simp only [cs0, Asm.sub, lkm.totalSize_instr]
    have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre3) := by rw [hpc3, show lkm.totalSize pre3 = lkm.totalSize pre2 + 1 from by rw [lkm.totalSize_append pre2 cs0, htws]]
    have hlink3 : lkm.linkSpec (pre3 ++ cb1 ++ (ca ++ post)) = .ok (env.code, env.labels) := by
      simpa [pre3, List.append_assoc] using hlink2
    have hbr1 := run_br_step env pre3 _ .bltu AbiReg.t0 AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide) hlink3 st3 hpc3'
    have hcond1 : evalBranch .bltu (st3.getReg AbiReg.t0) (st3.getReg AbiReg.t2) =
        decide (bytes.size - vk.toNat < vsi.toNat) := by
      rw [ht0_3v, hoth2 _ (by decide), hoth1Br _ (by decide), ht2Val, u64_toBitVec_eq_ofNat]
      exact evalBranch_bltu_nat (by omega) vsi.toBitVec.isLt
    obtain ⟨_, st4, _, hrun3, hpc4Br, hoth3Br, _, hmem3Br⟩ := hbr1
    have hp3Br : PreservedFrameRegs fl (fun _ => False) st3 st4 :=
      preservedFrameRegs_of_t6_s1 hoth3Br
    by_cases hdi : vsi.toNat ≤ bytes.size - vk.toNat
    · have hbound : vsi.toNat + vk.toNat ≤ bytes.size := by omega
      simp only [hbound, ↓reduceIte]
      have hbr1F : evalBranch .bltu (st3.getReg AbiReg.t0) (st3.getReg AbiReg.t2) = false := by
        rw [hcond1, decide_eq_false_iff_not]; omega
      let pre4 := pre3 ++ cb1
      have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre4) := by
        rw [hpc4Br, hbr1F]; simp only [Bool.false_eq_true, ↓reduceIte]
        exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (lkm.totalSize_append pre3 cb1).symm
      have hlink4 : lkm.linkSpec (pre4 ++ ca ++ post) = .ok (env.code, env.labels) := by
        simpa [pre4, List.append_assoc] using hlink3
      let st5 := stepReg st4 AbiReg.t2 (evalAlu .add (st4.getReg AbiReg.t5) (st4.getReg AbiReg.t2))
        (BitVec.ofNat 64 (4 * (lkm.totalSize pre4 + 1)))
      obtain ⟨hrun4, hpc5, ht2_5, hoth4, hmem4, _⟩ :=
        run_alu_step env pre4 _ .add AbiReg.t2 AbiReg.t5 AbiReg.t2 nonPreserved_t2 hlink4 st4 hpc4'
      have hp4 : PreservedFrameRegs fl (fun _ => False) st4 st5 :=
        PreservedFrameRegs.of_scratch1 AbiReg.t2 (by decide) hoth4
      have ht2_5v : st5.getReg AbiReg.t2 = t5Val + BitVec.ofNat 64 vsi.toNat := by
        rw [ht2_5, evalAlu, hoth3Br _ (by decide), hoth3Br _ (by decide),
            hoth2 _ (by decide), hoth2 _ (by decide),
            hoth1Br _ (by decide), hoth1Br _ (by decide), ht5_1, ht2Val, u64_toBitVec_eq_ofNat]
      have hpcEq : lkm.totalSize pre4 + 1 = lkm.totalSize pre + lkm.totalSize codeCheck := by
        have htwa : lkm.totalSize ca = 1 := by simp only [ca, Asm.add, lkm.totalSize_instr]
        rw [hcEq]; simp only [pre4, pre3, pre2, pre1, lkm.totalSize_append, htws, htwa]; omega
      exact ⟨_, st5, run_trans (run_trans (run_trans hrun0 hrun1) hrun2) (run_trans hrun3 hrun4),
        by rw [hpc5, hpcEq],
        (hoth4 _ (by decide)).trans ((hoth3Br _ (by decide)).trans ((hoth2 _ (by decide)).trans ((hoth1Br _ (by decide)).trans ht1_1))),
        ht2_5v,
        (hoth4 _ (by decide)).trans ((hoth3Br _ (by decide)).trans ((hoth2 _ (by decide)).trans ((hoth1Br _ (by decide)).trans ht3_1))),
        by rw [hmem4, hmem3Br, hmem2, hmem1Br, hmem0],
        hp0.trans (hp1Br.trans (hp2.trans (hp3Br.trans hp4)))⟩
    · have hbound : ¬(vsi.toNat + vk.toNat ≤ bytes.size) := by omega
      simp only [hbound, ↓reduceIte]
      have hbr1T : evalBranch .bltu (st3.getReg AbiReg.t0) (st3.getReg AbiReg.t2) = true := by
        rw [hcond1, decide_eq_true_iff]; omega
      exact ⟨_, st4, run_trans (run_trans (run_trans hrun0 hrun1) hrun2) hrun3,
        by rw [hpc4Br, hbr1T]; rfl, by rw [hmem3Br, hmem2, hmem1Br, hmem0],
        hp0.trans (hp1Br.trans (hp2.trans hp3Br))⟩
  · have hbound : ¬(vsi.toNat + vk.toNat ≤ bytes.size) := by omega
    simp only [hbound, ↓reduceIte]
    have hbr0T : evalBranch .bltu (st1.getReg AbiReg.t0) (st1.getReg AbiReg.t3) = true := by
      rw [hcond0, decide_eq_true_iff]; omega
    exact ⟨_, st2, run_trans hrun0 hrun1, by rw [hpc2Br, hbr0T]; rfl,
      by rw [hmem1Br, hmem0], hp0.trans hp1Br⟩

private theorem reg_copy8w_loop_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout)
    (da : TieredArray) (hda : env.tab.wordPosOkB da = true)
    (src : BSrc) (hsrc : bsrcOkB env.tab src = true)
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
        PreservedFrameRegs fl (fun _ => False) st r' ∧
        ProgMemRel env.tab L r'.mem (lm.copy8w da di (lm.src8 src) si n) ∧
        MemEqOutside (L.arr64Span da) st.mem r'.mem := by
  intro n
  induction n with
  | zero =>
    intro lm di si st hpc ht1 ht2 ht3 _ _ _ hm
    have ⟨_, hl1⟩ := linkResolved_mid_split lkm pre [Asm.lbl loopLbl] _ post hlink
    have ⟨hlBeq, _⟩ := linkResolved_mid_split lkm (pre ++ [Asm.lbl loopLbl]) [Asm.beq AbiReg.t3 AbiReg.zero doneLbl] _ post hl1
    have hbr := run_br_step env (pre ++ [Asm.lbl loopLbl]) _ .beq AbiReg.t3 AbiReg.zero doneLbl doneTarget hdoneLbl (by decide)
      hlBeq st (by rw [lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero, ← hltLoop]; exact hpc)
    have hcond : evalBranch .beq (st.getReg AbiReg.t3) (st.getReg AbiReg.zero) = true := by
      rw [ht3, getReg_zero st]; decide
    obtain ⟨kBr, st', _, hrun, hpcBr, hothBr, _, hmemBr⟩ := hbr
    have hcopy : lm.copy8w da di (lm.src8 src) si 0 = lm := by simp [_root_.L.Mem.copy8w]
    rw [hcopy]
    exact ⟨kBr, st', hrun, by rw [hpcBr, hcond]; rfl,
      preservedFrameRegs_of_t6_s1 hothBr,
      by rw [hmemBr]; exact hm, fun _ _ => by rw [hmemBr]⟩
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
    obtain ⟨_, st1, _, hrun1, hpc1Br, hoth1, _, hmem1⟩ := hbr
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize ((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl])) := by
      rw [hpc1Br, hcond]; simp only [Bool.false_eq_true, ↓reduceIte, lkm.totalSize_append, Asm.beq, Asm.br, lkm.totalSize_singleton]
    obtain ⟨hrun2, hpc2, ht4_2, hoth2, hmem2, _⟩ :=
      run_lbu_zero_step env _ _ AbiReg.t4 AbiReg.t2 nonPreserved_t4 hl2 st1 hpc1'
    let st2 := stepReg st1 AbiReg.t4 (BitVec.zeroExtend 64 (st1.mem (st1.getReg AbiReg.t2)))
      (BitVec.ofNat 64 (4 * (lkm.totalSize ((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) + 1)))
    have halDst : isAligned (st2.getReg AbiReg.t1) 8 = true := by
      rw [hoth2 _ (by decide), hoth1 _ (by decide), ht1]; exact isAligned8_add_mul8 _ (L.h64Align da) di.toNat
    have htwLbu : lkm.totalSize [Asm.lbu AbiReg.t4 AbiReg.t2] = 1 := by simp only [Asm.lbu, lkm.totalSize_instr]
    have hrun3 := step_sd_zero env _ _ AbiReg.t1 AbiReg.t4 hl3 st2 (by rw [lkm.totalSize_append, htwLbu]; exact hpc2) halDst
    let st3 : State :=
      { pc := BitVec.ofNat 64 (4 * (lkm.totalSize (((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.lbu AbiReg.t4 AbiReg.t2]) + 1))
      , regs := st2.regs, mem := writeWord64 st2.mem (st2.getReg AbiReg.t1) (st2.getReg AbiReg.t4) }
    have htwSd : lkm.totalSize [Asm.sd AbiReg.t1 AbiReg.t4] = 1 := by simp only [Asm.sd, lkm.totalSize_instr]
    obtain ⟨hrun4, hpc4, ht1_4, hoth4, hmem4, _⟩ :=
      run_aluImm_step env _ _ .addi AbiReg.t1 AbiReg.t1 8#12 nonPreserved_t1 hl4 st3 (by rw [lkm.totalSize_append, htwSd])
    let st4 := stepReg st3 AbiReg.t1 (evalAluImm .addi (st3.getReg AbiReg.t1) 8#12)
      (BitVec.ofNat 64 (4 * (lkm.totalSize ((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.lbu AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) + 1)))
    have htwA1 : lkm.totalSize [Asm.addi AbiReg.t1 AbiReg.t1 8#12] = 1 := by simp only [Asm.addi, lkm.totalSize_instr]
    obtain ⟨hrun5, hpc5, ht2_5, hoth5, hmem5, _⟩ :=
      run_aluImm_step env _ _ .addi AbiReg.t2 AbiReg.t2 1#12 nonPreserved_t2 hl5 st4 (by rw [lkm.totalSize_append, htwA1]; exact hpc4)
    let st5 := stepReg st4 AbiReg.t2 (evalAluImm .addi (st4.getReg AbiReg.t2) 1#12)
      (BitVec.ofNat 64 (4 * (lkm.totalSize (((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.lbu AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) ++ [Asm.addi AbiReg.t1 AbiReg.t1 8#12]) + 1)))
    have htwA2 : lkm.totalSize [Asm.addi AbiReg.t2 AbiReg.t2 1#12] = 1 := by simp only [Asm.addi, lkm.totalSize_instr]
    obtain ⟨hrun6, hpc6, ht3_6, hoth6, hmem6, _⟩ :=
      run_aluImm_step env _ _ .addi AbiReg.t3 AbiReg.t3 (-1#12) nonPreserved_t3 hl6 st5 (by rw [lkm.totalSize_append, htwA2]; exact hpc5)
    let st6 := stepReg st5 AbiReg.t3 (evalAluImm .addi (st5.getReg AbiReg.t3) (-1#12))
      (BitVec.ofNat 64 (4 * (lkm.totalSize ((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.lbu AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) ++ [Asm.addi AbiReg.t1 AbiReg.t1 8#12]) ++ [Asm.addi AbiReg.t2 AbiReg.t2 1#12]) + 1)))
    have htwA3 : lkm.totalSize [Asm.addi AbiReg.t3 AbiReg.t3 (-1#12)] = 1 := by simp only [Asm.addi, lkm.totalSize_instr]
    have hpc64J : 4 * (lkm.totalSize (((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.lbu AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) ++ [Asm.addi AbiReg.t1 AbiReg.t1 8#12]) ++ [Asm.addi AbiReg.t2 AbiReg.t2 1#12]) ++ [Asm.addi AbiReg.t3 AbiReg.t3 (-1#12)]) + lkm.itemSize (.j loopLbl)) < 2 ^ 64 := by
      simpa [Asm.j, lkm.totalSize_singleton] using linkResolved_sub_pc64 env _ [Asm.j loopLbl] _ hl7
    obtain ⟨_, st7, hrun7, hpc7, hoth7, _, hmem7⟩ :=
      prog_step_j env _ _ loopLbl loopTarget hloopLbl hl7 hpc64J st6 (by rw [lkm.totalSize_append, htwA3]; exact hpc6)
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
      have := L.h64Valid da; simp [UInt64.toNat_add, Nat.mod_eq_of_lt (show di.toNat + 1 < 2 ^ 64 by omega)]
    have hsi1 : (si + 1).toNat = si.toNat + 1 := by
      simp [UInt64.toNat_add, Nat.mod_eq_of_lt (show si.toNat + 1 < 2 ^ 64 by omega)]
    have h8eq : sextImm12 8#12 = BitVec.ofNat 64 8 := by decide
    have h1eq : sextImm12 1#12 = BitVec.ofNat 64 1 := by decide
    have ht1_7 : st7.getReg AbiReg.t1 = L.base64 da + BitVec.ofNat 64 (8 * (di + 1).toNat) := by
      rw [hoth7 _ (by decide)]; change st6.getReg AbiReg.t1 = _
      rw [hoth6 _ (by decide), hoth5 _ (by decide), ht1_4, evalAluImm]
      change st2.getReg AbiReg.t1 + sextImm12 8#12 = _
      rw [ht1St2, h8eq, BitVec.add_assoc, ← BitVec.ofNat_add, hdi1, show 8 * di.toNat + 8 = 8 * (di.toNat + 1) by omega]
    have ht2_7 : st7.getReg AbiReg.t2 = bsrcAddr env.tab L src + BitVec.ofNat 64 (si + 1).toNat := by
      rw [hoth7 _ (by decide)]; change st6.getReg AbiReg.t2 = _
      rw [hoth6 _ (by decide), ht2_5, evalAluImm]
      change st4.getReg AbiReg.t2 + sextImm12 1#12 = _
      rw [hoth4 _ (by decide), show st3.getReg AbiReg.t2 = st2.getReg AbiReg.t2 from rfl,
          hoth2 _ (by decide), hoth1 _ (by decide), ht2, h1eq, BitVec.add_assoc, ← BitVec.ofNat_add, hsi1]
    have ht3_7 : st7.getReg AbiReg.t3 = BitVec.ofNat 64 n := by
      rw [hoth7 _ (by decide)]; change st6.getReg AbiReg.t3 = _
      rw [ht3_6, evalAluImm]; change st4.getReg AbiReg.t3 + sextImm12 (-1#12) = _
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
    obtain ⟨_, stEnd, hrunRest, hpcEnd, hpresRest, hmEnd, hpmRest⟩ :=
      ih lm1 (di + 1) (si + 1) st7 hpc7 ht1_7 ht2_7 ht3_7 hdiSize hsiSize hsz1 hm1
    have hpmStep : MemEqOutside (L.arr64Span da) st.mem st7.mem := by
      rw [hst7Mem, hst3Mem]
      exact memEqOutside_writeWord64_arr64 L da di.toNat (Nat.lt_of_lt_of_le (by omega) hcapD) st.mem _
    have hpStep : PreservedFrameRegs fl (fun _ => False) st st7 :=
      (preservedFrameRegs_of_t6_s1 hoth1).trans
        ((PreservedFrameRegs.of_scratch1 AbiReg.t4 (by decide) hoth2).trans
          ((⟨⟨rfl, rfl, rfl, rfl⟩, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩ : PreservedFrameRegs fl (fun _ => False) st2 st3).trans
            ((PreservedFrameRegs.of_scratch1 AbiReg.t1 (by decide) hoth4).trans
              ((PreservedFrameRegs.of_scratch1 AbiReg.t2 (by decide) hoth5).trans
                ((PreservedFrameRegs.of_scratch1 AbiReg.t3 (by decide) hoth6).trans
                  (preservedFrameRegs_of_t6_s1 hoth7))))))
    have hcopyEq : lm.copy8w da di (lm.src8 src) si (n + 1) = lm1.copy8w da (di + 1) (lm1.src8 src) (si + 1) n := by
      rw [hsrcEq]; rfl
    have hrunStep := run_trans (run_trans (run_trans (run_trans (run_trans (run_trans hrun1 hrun2) hrun3) hrun4) hrun5) hrun6) hrun7
    exact ⟨_, stEnd, run_trans hrunStep hrunRest, hpcEnd, hpStep.trans hpresRest, by rw [hcopyEq]; exact hmEnd, hpmStep.trans hpmRest⟩

theorem reg_copy8w_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hal : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (d : WArr) (di : Expr) (src : BSrc) (si n : Expr)
    (hdOk : warrOkB env.tab fl.nlocals d = true) (hdiOk : exprOkB env.tab fl.nlocals di = true)
    (hsrcOk : bsrcOkB env.tab src = true) (hsiOk : exprOkB env.tab fl.nlocals si = true)
    (hnOk : exprOkB env.tab fl.nlocals n = true)
    (hVfD : WArrVarsInFrame fl d) (hVfDI : ExprVarsInFrame fl di)
    (hVfSI : ExprVarsInFrame fl si) (hVfN : ExprVarsInFrame fl n)
    (hTmp : usedTempsStmt (.copy8w d di src si n) ≤ fl.usedTemps)
    (pfx : String) (lblId : Nat) (brkLbl : Option String) (retLbl : String) (isTail : Bool)
    (pre post : List AsmItem)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hnoT5 : fl.useT5Gp = false) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOkR L fl sp st loc)
    (hlink : lkm.linkSpec (pre ++ (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.copy8w d di src si n)).1 ++ post) =
      .ok (env.code, env.labels))
    (p : _root_.L.Prog) :
    let codeS := (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.copy8w d di src si n)).1
    match _root_.L.step p (fun _ => throw .outOfFuel) (.copy8w d di src si n) { mem := lm, loc := loc } with
    | .ok (_, st') =>
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize codeS)) ∧
        PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) st r' ∧
        ProgMemRel env.tab L r'.mem st'.mem ∧
        ProgFrameOkR L fl sp r' st'.loc ∧
        ProgMemOutside (FnWriteMaskR L fl sp) st.mem r'.mem
    | .error _ =>
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) st r' ∧
        ProgMemOutside (FnWriteMaskR L fl sp) st.mem r'.mem := by
  have hvalid : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  dsimp only [usedTempsStmt] at hTmp
  let dArr := (evalWArrTierToTempR env.tab fl 0 d).1
  let loopLbl := s!"{pfx}_c8w_{lblId}"
  let doneLbl := s!"{pfx}_c8w_done_{lblId}"
  let c0 := (evalWArrTierToTempR env.tab fl 0 d).2
  let c1 := compileETo env.tab fl 1 AbiReg.a0 di ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 1)
  let c3 := compileETo env.tab fl 3 AbiReg.a0 si ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 3)
  let c4 := compileETo env.tab fl 4 AbiReg.a0 n ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 4)
  let codeDst :=
    loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 0) ++
    [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] ++
    loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (env.tab.len64 (.t0 dArr)) ++
    loadMemOff .ld AbiReg.t1 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 1) ++
    loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 4) ++
    [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3, Asm.bltu AbiReg.t0 AbiReg.t1 errLabel] ++
    loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (env.tab.base64 (.t0 dArr)) ++
    [Asm.slli AbiReg.t1 AbiReg.t1 3#6, Asm.add AbiReg.t1 AbiReg.t5 AbiReg.t1]
  let srcSetup := bsrcSetup env.tab AbiReg.t5 AbiReg.t6 src
  let srcCheck :=
    loadMemOff .ld AbiReg.t2 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 3) ++
    [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3,
     Asm.bltu AbiReg.t0 AbiReg.t2 errLabel, Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2]
  let codeLoop :=
    [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl, Asm.lbu AbiReg.t4 AbiReg.t2 0#12,
     Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 1#12,
     Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl]
  have hcodeEq : (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.copy8w d di src si n)).1 =
      c0 ++ c1 ++ c3 ++ c4 ++ codeDst ++ srcSetup ++ srcCheck ++ codeLoop := by
    cases d <;> cases src <;>
      dsimp only [compileSR, dArr, evalWArrTierToTempR, c0, c1, c3, c4, codeDst, srcSetup, bsrcSetup, srcCheck, codeLoop, loopLbl, doneLbl] <;>
      simp only [List.append_assoc] <;> rfl
  rw [hcodeEq] at hlink
  have hlink0 : lkm.linkSpec (pre ++ c0 ++ (c1 ++ c3 ++ c4 ++ codeDst ++ srcSetup ++ srcCheck ++ codeLoop ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
  have hvacT5 : ∀ s, T5GpOk L fl s := fun _ h => by rw [hnoT5] at h; cases h
  have hw0 : 0 + max 1 (warrUsedTemps d) ≤ fl.usedTemps := by
    cases d <;> dsimp only [warrUsedTemps] at hTmp ⊢ <;> omega
  have hs0Sim := reg_evalWArrTierToTempR_sim env L fl hfl lm loc hal hlo hhi d hdOk hVfD 0 hw0 pre _ hlink0 st hpc hgp (hvacT5 _) hsp hm hf
  rcases warr_pure d ⟨lm, loc⟩ with ⟨da, hdaW⟩ | hdaW
  · rw [hdaW] at hs0Sim
    obtain ⟨_, st1, du, hrun0, hpc0, hdaEq, hdaOk, hdoLen, hdoBase, hslot0, hp0, hout0⟩ := hs0Sim
    have hpm0 : ProgMemOutside (FnWriteMaskR L fl sp) st.mem st1.mem :=
      ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) hout0
    have hm1 := ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) hout0 hm
    have hf1 := ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) (hp0.mono (fun _ h => False.elim h)) hout0 hf
    let pre1 := pre ++ c0
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by rw [hpc0, lkm.totalSize_append pre c0]
    have hlink1 : lkm.linkSpec (pre1 ++ c1 ++ (c3 ++ c4 ++ codeDst ++ srcSetup ++ srcCheck ++ codeLoop ++ post)) =
        .ok (env.code, env.labels) := by simpa [pre1, List.append_assoc] using hlink0
    have hs1Sim := reg_evalToTemp_sim env L fl hfl lm loc hal hlo hhi 1 di hdiOk hVfDI (by omega) pre1 _ hlink1
      st1 hpc1' (hp0.abi.gp.trans hgp) (hvacT5 _) (hp0.abi.sp.trans hsp) hm1 hf1
    rcases _root_.L.evalE_pure di ⟨lm, loc⟩ with ⟨vdi, hdiE⟩ | hdiE
    · rw [hdiE] at hs1Sim
      obtain ⟨_, st2, hrun1, hpc1, hslot1, hp1, hout1⟩ := hs1Sim
      have hpm1 : ProgMemOutside (FnWriteMaskR L fl sp) st1.mem st2.mem :=
        ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (by omega : 1 ≤ fl.usedTemps)) hout1
      have hm2 := ProgMemRel.of_tempSpanR hlo hhi (by omega : 1 ≤ fl.usedTemps) hout1 hm1
      have hf2 := ProgFrameOkR.of_preserved_temp hfl hvalid (by omega : 1 ≤ fl.usedTemps) (hp1.mono (fun _ h => False.elim h)) hout1 hf1
      let pre2 := pre1 ++ c1
      have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) := by rw [hpc1, lkm.totalSize_append pre1 c1]
      have hlink2 : lkm.linkSpec (pre2 ++ c3 ++ (c4 ++ codeDst ++ srcSetup ++ srcCheck ++ codeLoop ++ post)) =
          .ok (env.code, env.labels) := by simpa [pre2, List.append_assoc] using hlink1
      have hs3Sim := reg_evalToTemp_sim env L fl hfl lm loc hal hlo hhi 3 si hsiOk hVfSI (by omega) pre2 _ hlink2
        st2 hpc2' ((hp0.trans hp1).abi.gp.trans hgp) (hvacT5 _) ((hp0.trans hp1).abi.sp.trans hsp) hm2 hf2
      rcases _root_.L.evalE_pure si ⟨lm, loc⟩ with ⟨vsi, hsiE⟩ | hsiE
      · rw [hsiE] at hs3Sim
        obtain ⟨_, st3, hrun3, hpc3, hslot3, hp3, hout3⟩ := hs3Sim
        have hpm3 : ProgMemOutside (FnWriteMaskR L fl sp) st2.mem st3.mem :=
          ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (by omega : 3 ≤ fl.usedTemps)) hout3
        have hm3 := ProgMemRel.of_tempSpanR hlo hhi (by omega : 3 ≤ fl.usedTemps) hout3 hm2
        have hf3 := ProgFrameOkR.of_preserved_temp hfl hvalid (by omega : 3 ≤ fl.usedTemps) (hp3.mono (fun _ h => False.elim h)) hout3 hf2
        let pre3 := pre2 ++ c3
        have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre3) := by rw [hpc3, lkm.totalSize_append pre2 c3]
        have hlink3 : lkm.linkSpec (pre3 ++ c4 ++ (codeDst ++ srcSetup ++ srcCheck ++ codeLoop ++ post)) =
            .ok (env.code, env.labels) := by simpa [pre3, List.append_assoc] using hlink2
        have hs4Sim := reg_evalToTemp_sim env L fl hfl lm loc hal hlo hhi 4 n hnOk hVfN (by omega) pre3 _ hlink3
          st3 hpc3' ((hp0.trans (hp1.trans hp3)).abi.gp.trans hgp) (hvacT5 _) ((hp0.trans (hp1.trans hp3)).abi.sp.trans hsp) hm3 hf3
        rcases _root_.L.evalE_pure n ⟨lm, loc⟩ with ⟨vk, hnE⟩ | hnE
        · rw [hnE] at hs4Sim
          obtain ⟨_, st4, hrun4, hpc4, hslot4, hp4, hout4⟩ := hs4Sim
          have hm4 := ProgMemRel.of_tempSpanR hlo hhi (by omega : 4 ≤ fl.usedTemps) hout4 hm3
          have hf4 := ProgFrameOkR.of_preserved_temp hfl hvalid (by omega : 4 ≤ fl.usedTemps) (hp4.mono (fun _ h => False.elim h)) hout4 hf3
          have hout04 : MemEqOutside (tempSpanR fl sp 0) st.mem st4.mem :=
            hout0.trans ((hout1.mono (tempSpanR_mono fl sp hvalid (by omega : 0 ≤ 1) (by omega))).trans
              ((hout3.mono (tempSpanR_mono fl sp hvalid (by omega : 0 ≤ 3) (by omega))).trans
                (hout4.mono (tempSpanR_mono fl sp hvalid (by omega : 0 ≤ 4) (by omega)))))
          have hpmA : ProgMemOutside (FnWriteMaskR L fl sp) st.mem st4.mem :=
            ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) hout04
          have hpA : PreservedFrameRegs fl (fun _ => False) st st4 := hp0.trans (hp1.trans (hp3.trans hp4))
          have hrunA := run_trans (run_trans (run_trans hrun0 hrun1) hrun3) hrun4
          have hs0_4 : readWord64 st4.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff 0)) = du.toBitVec := by
            rw [readWord64_tempSlotR_of_tempSpanR (by omega : 0 < 4) (by omega) hvalid hout4,
                readWord64_tempSlotR_of_tempSpanR (by omega : 0 < 3) (by omega) hvalid hout3,
                readWord64_tempSlotR_of_tempSpanR (by omega : 0 < 1) (by omega) hvalid hout1]; exact hslot0
          have hs1_4 : readWord64 st4.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff 1)) = vdi.toBitVec := by
            rw [readWord64_tempSlotR_of_tempSpanR (by omega : 1 < 4) (by omega) hvalid hout4,
                readWord64_tempSlotR_of_tempSpanR (by omega : 1 < 3) (by omega) hvalid hout3]; exact hslot1
          have hs3_4 : readWord64 st4.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff 3)) = vsi.toBitVec := by
            rw [readWord64_tempSlotR_of_tempSpanR (by omega : 3 < 4) (by omega) hvalid hout4]; exact hslot3
          let pre4 := pre3 ++ c4
          have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre4) := by rw [hpc4, lkm.totalSize_append pre3 c4]
          have hlink4 : lkm.linkSpec (pre4 ++ codeDst ++ (srcSetup ++ srcCheck ++ codeLoop ++ post)) =
              .ok (env.code, env.labels) := by simpa [pre4, List.append_assoc] using hlink3
          have hdst := reg_warr_dst_setup_sim env L fl lm hal dArr du vdi vk da hdaOk
            hdoLen hdoBase pre4 codeDst (srcSetup ++ srcCheck ++ codeLoop ++ post) rfl st4 hpc4'
            (hpA.abi.gp.trans hgp) hnoT5 (hpA.abi.sp.trans hsp) hm4 hs0_4 hs1_4 hslot4 hlink4
          have hstepOk : _root_.L.step p (fun _ => throw .outOfFuel) (.copy8w d di src si n) { mem := lm, loc := loc } =
              if vdi.toNat + vk.toNat ≤ (lm.arr64 da).size ∧ vsi.toNat + vk.toNat ≤ (lm.src8 src).size then
                .ok (Sig.normal, { mem := lm.copy8w da vdi (lm.src8 src) vsi vk.toNat, loc := loc })
              else .error .oob := by
            simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE, hsiE, hnE, get, getThe,
              MonadStateOf.get, StateT.get, set, MonadStateOf.set, throw, throwThe, MonadExceptOf.throw, Pure.pure, Except.pure]
            by_cases hb : vdi.toNat + vk.toNat ≤ (lm.arr64 da).size ∧ vsi.toNat + vk.toNat ≤ (lm.src8 src).size <;>
              simp only [hb, ↓reduceIte] <;> rfl
          rw [hstepOk]
          by_cases hbd : vdi.toNat + vk.toNat ≤ (lm.arr64 da).size
          · simp only [hbd, ↓reduceIte] at hdst
            obtain ⟨_, st5, hrunD, hpc5, ht1_5, ht3_5, hmemD, hpD⟩ := hdst
            let pre5 := pre4 ++ codeDst
            have hpc5' : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre5) := by rw [hpc5, lkm.totalSize_append pre4 codeDst]
            have hlink5 : lkm.linkSpec (pre5 ++ srcSetup ++ (srcCheck ++ codeLoop ++ post)) =
                .ok (env.code, env.labels) := by simpa [pre5, List.append_assoc] using hlink4
            obtain ⟨_, st6, hrunB, hpc6, ht0_6, ht5_6, hlenLt, hothB, hmemB, _⟩ :=
              bsrc_setup_sim env L lm src hsrcOk AbiReg.t5 AbiReg.t6 (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) (by decide)
                pre5 (srcCheck ++ codeLoop ++ post) hlink5 st5 hpc5' (hpD.abi.gp.trans (hpA.abi.gp.trans hgp)) (hmemD ▸ hm4)
            have hpB : PreservedFrameRegs fl (fun _ => False) st5 st6 :=
              preservedFrameRegs_of_noT5_scratch3 hnoT5 AbiReg.t0 AbiReg.t5 AbiReg.t6 (by decide) (by decide) (by decide) hothB
            let pre6 := pre5 ++ srcSetup
            have hpc6' : st6.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre6) := by rw [hpc6, lkm.totalSize_append pre5 srcSetup]
            have hlink6 : lkm.linkSpec (pre6 ++ srcCheck ++ (codeLoop ++ post)) =
                .ok (env.code, env.labels) := by simpa [pre6, List.append_assoc] using hlink5
            have ht1_6 : st6.getReg AbiReg.t1 = L.base64 da + BitVec.ofNat 64 (8 * vdi.toNat) :=
              (hothB _ (by decide) (by decide) (by decide)).trans ht1_5
            have ht3_6 : st6.getReg AbiReg.t3 = vk.toBitVec :=
              (hothB _ (by decide) (by decide) (by decide)).trans ht3_5
            have hchk := reg_copy8w_src_check_sim env fl hal (lm.src8 src) hlenLt vsi vk
              (L.base64 da + BitVec.ofNat 64 (8 * vdi.toNat)) (bsrcAddr env.tab L src)
              pre6 srcCheck (codeLoop ++ post) rfl hlink6 st6 hpc6'
              (hpB.abi.sp.trans (hpD.abi.sp.trans (hpA.abi.sp.trans hsp))) ht0_6 ht1_6 ht3_6 ht5_6
              (by rw [hmemB, hmemD]; exact hs3_4)
            by_cases hbs : vsi.toNat + vk.toNat ≤ (lm.src8 src).size
            · simp only [hbd, hbs, and_self, ↓reduceIte] at hchk ⊢
              obtain ⟨_, st7, hrunC, hpc7, ht1_7, ht2_7, ht3_7, hmemC, hpC⟩ := hchk
              let pre7 := pre6 ++ srcCheck
              have hpc7' : st7.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre7) := by rw [hpc7, lkm.totalSize_append pre6 srcCheck]
              have hlink7 : lkm.linkSpec (pre7 ++ codeLoop ++ post) = .ok (env.code, env.labels) := by
                simpa [pre7, List.append_assoc] using hlink6
              have hloopLbl := lookupLabel_of_lbl_lm lkm pre7
                ([Asm.beq AbiReg.t3 AbiReg.zero doneLbl, Asm.lbu AbiReg.t4 AbiReg.t2 0#12,
                  Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
                  Asm.addi AbiReg.t2 AbiReg.t2 1#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12),
                  Asm.j loopLbl, Asm.lbl doneLbl] ++ post) loopLbl (by simpa [codeLoop, List.append_assoc] using hlink7)
              have hdoneLbl := lookupLabel_of_lbl_lm lkm
                (pre7 ++ [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl, Asm.lbu AbiReg.t4 AbiReg.t2 0#12,
                  Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
                  Asm.addi AbiReg.t2 AbiReg.t2 1#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl])
                post doneLbl (by simpa [codeLoop, List.append_assoc] using hlink7)
              have htwDone : lkm.totalSize codeLoop =
                  lkm.totalSize [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
                    Asm.lbu AbiReg.t4 AbiReg.t2 0#12, Asm.sd AbiReg.t1 AbiReg.t4 0#12,
                    Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 1#12,
                    Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl] := by
                rw [show codeLoop = [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
                  Asm.lbu AbiReg.t4 AbiReg.t2 0#12, Asm.sd AbiReg.t1 AbiReg.t4 0#12,
                  Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 1#12,
                  Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl] ++ [Asm.lbl doneLbl] by simp [codeLoop]]
                simp only [lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero]
              have hdoneTgt : lkm.totalSize (pre7 ++ [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
                  Asm.lbu AbiReg.t4 AbiReg.t2 0#12, Asm.sd AbiReg.t1 AbiReg.t4 0#12,
                  Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 1#12,
                  Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl]) = lkm.totalSize pre7 + lkm.totalSize codeLoop := by
                rw [lkm.totalSize_append, ← htwDone]
              have hlinkL : lkm.linkSpec (pre7 ++ [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
                  Asm.lbu AbiReg.t4 AbiReg.t2, Asm.sd AbiReg.t1 AbiReg.t4, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
                  Asm.addi AbiReg.t2 AbiReg.t2 1#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl,
                  Asm.lbl doneLbl] ++ post) = .ok (env.code, env.labels) := by
                simpa [codeLoop, Asm.lbu, Asm.sd, List.append_assoc] using hlink7
              have hmem47 : st7.mem = st4.mem := hmemC.trans (hmemB.trans hmemD)
              obtain ⟨_, r', hrunL, hpcR, hpL, hmR, hmeqL⟩ :=
                reg_copy8w_loop_sim env L fl da hdaOk src hsrcOk loopLbl doneLbl
                  (lkm.totalSize pre7) (lkm.totalSize pre7 + lkm.totalSize codeLoop)
                  hloopLbl (by rw [← hdoneTgt]; exact hdoneLbl) pre7 post rfl hlinkL
                  vk.toNat lm vdi vsi st7 hpc7' ht1_7 ht2_7 (by rw [ht3_7, u64_toBitVec_eq_ofNat]) hbd hbs hlenLt (hmem47 ▸ hm4)
              have hmeq4R : MemEqOutside (L.arr64Span da) st4.mem r'.mem := by rw [← hmem47]; exact hmeqL
              have h64Disj : MemDisjoint (L.arr64Span da) L.stackSpan :=
                MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid da) L.stackSpan_valid (L.h64DisjStack da hdaOk)
              have hpcEq : lkm.totalSize pre7 + lkm.totalSize codeLoop =
                  lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.copy8w d di src si n)).1 := by
                rw [hcodeEq]
                simp only [pre7, pre6, pre5, pre4, pre3, pre2, pre1, lkm.totalSize_append]; omega
              exact ⟨_, r', run_trans (run_trans (run_trans (run_trans hrunA hrunD) hrunB) hrunC) hrunL,
                by rw [hpcR, hpcEq],
                (hpA.trans (hpD.trans (hpB.trans (hpC.trans hpL)))).mono (fun _ h => False.elim h),
                hmR,
                ProgFrameOkR.of_mem_outside_stack hfl hlo hhi (L.arr64Span da) h64Disj (hpD.trans (hpB.trans (hpC.trans hpL))) hmeq4R hf4,
                hpmA.trans (ProgMemOutside.of_memEqOutside (fun _ ha => Or.inr (Or.inr (Or.inr ⟨da, hdaOk, ha⟩))) hmeq4R)⟩
            · simp only [hbd, hbs, and_false, ↓reduceIte] at hchk ⊢
              obtain ⟨_, r', hrunC, hpcR, hmemC, hpC⟩ := hchk
              exact ⟨_, r', run_trans (run_trans (run_trans hrunA hrunD) hrunB) hrunC, hpcR,
                (hpA.trans (hpD.trans (hpB.trans hpC))).mono (fun _ h => False.elim h),
                by rw [hmemC, hmemB, hmemD]; exact hpmA⟩
          · simp only [hbd, false_and, ↓reduceIte] at hdst ⊢
            obtain ⟨_, r', hrunD, hpcR, hmemD, hpD⟩ := hdst
            exact ⟨_, r', run_trans hrunA hrunD, hpcR, (hpA.trans hpD).mono (fun _ h => False.elim h),
              by rw [hmemD]; exact hpmA⟩
        · rw [hnE] at hs4Sim
          have hstepErr : _root_.L.step p (fun _ => throw .outOfFuel) (.copy8w d di src si n) ⟨lm, loc⟩ = .error .oob := by
            simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE, hsiE, hnE]
          rw [hstepErr]; obtain ⟨_, st', hrun4, hpc4, hp4, hout4⟩ := hs4Sim
          exact ⟨_, st', run_trans (run_trans (run_trans hrun0 hrun1) hrun3) hrun4, hpc4,
            (hp0.trans (hp1.trans (hp3.trans hp4))).mono (fun _ h => False.elim h),
            hpm0.trans (hpm1.trans (hpm3.trans (ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (by omega : 4 ≤ fl.usedTemps)) hout4)))⟩
      · rw [hsiE] at hs3Sim
        have hstepErr : _root_.L.step p (fun _ => throw .outOfFuel) (.copy8w d di src si n) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE, hsiE]
        rw [hstepErr]; obtain ⟨_, st', hrun3, hpc3, hp3, hout3⟩ := hs3Sim
        exact ⟨_, st', run_trans (run_trans hrun0 hrun1) hrun3, hpc3,
          (hp0.trans (hp1.trans hp3)).mono (fun _ h => False.elim h),
          hpm0.trans (hpm1.trans (ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (by omega : 3 ≤ fl.usedTemps)) hout3))⟩
    · rw [hdiE] at hs1Sim
      have hstepErr : _root_.L.step p (fun _ => throw .outOfFuel) (.copy8w d di src si n) ⟨lm, loc⟩ = .error .oob := by
        simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE]
      rw [hstepErr]; obtain ⟨_, st', hrun1, hpc1, hp1, hout1⟩ := hs1Sim
      exact ⟨_, st', run_trans hrun0 hrun1, hpc1, (hp0.trans hp1).mono (fun _ h => False.elim h),
        hpm0.trans (ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (by omega : 1 ≤ fl.usedTemps)) hout1)⟩
  · rw [hdaW] at hs0Sim
    have hstepErr : _root_.L.step p (fun _ => throw .outOfFuel) (.copy8w d di src si n) ⟨lm, loc⟩ = .error .oob := by
      simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hdaW]
    rw [hstepErr]; obtain ⟨_, st', hrun0, hpc0, hp0, hout0⟩ := hs0Sim
    exact ⟨_, st', hrun0, hpc0, hp0.mono (fun _ h => False.elim h),
      ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) hout0⟩

private theorem reg_scan8_check_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (lm : _root_.L.Mem) (src : BSrc) (c : List UInt8)
    (vi ve : _root_.L.Word) (hlenLt : (lm.src8 src).size < 2 ^ 64)
    (pre codeCheck post : List AsmItem)
    (hcodeCheck : codeCheck =
      [Asm.bltu AbiReg.a0 AbiReg.t3 errLabel, Asm.bltu AbiReg.t0 AbiReg.a0 errLabel] ++
      addImmOff AbiReg.t2 AbiReg.gp AbiReg.t5 (env.tab.romBase + (romIdx c env.tab.rom : Int)))
    (hlink : lkm.linkSpec (pre ++ codeCheck ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hnoT5 : fl.useT5Gp = false)
    (ht0 : st.getReg AbiReg.t0 = BitVec.ofNat 64 (lm.src8 src).size)
    (ht1 : st.getReg AbiReg.t1 = bsrcAddr env.tab L src)
    (ht3 : st.getReg AbiReg.t3 = vi.toBitVec) (ha0 : st.getReg AbiReg.a0 = ve.toBitVec) :
    if vi ≤ ve ∧ ve.toNat ≤ (lm.src8 src).size then
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize codeCheck)) ∧
        r'.getReg AbiReg.a0 = ve.toBitVec ∧
        r'.getReg AbiReg.t1 = bsrcAddr env.tab L src ∧
        r'.getReg AbiReg.t2 = L.T + BitVec.ofNat 64 (env.tab.romBase.toNat + romIdx c env.tab.rom) ∧
        r'.getReg AbiReg.t3 = BitVec.ofNat 64 vi.toNat ∧
        r'.mem = st.mem ∧
        PreservedFrameRegs fl (fun _ => False) st r'
    else
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        r'.mem = st.mem ∧
        PreservedFrameRegs fl (fun _ => False) st r' := by
  let cb0 := [Asm.bltu AbiReg.a0 AbiReg.t3 errLabel]
  let cb1 := [Asm.bltu AbiReg.t0 AbiReg.a0 errLabel]
  let sadd := addImmOff AbiReg.t2 AbiReg.gp AbiReg.t5 (env.tab.romBase + (romIdx c env.tab.rom : Int))
  have hcEq : codeCheck = cb0 ++ cb1 ++ sadd := by rw [hcodeCheck]; simp [cb0, cb1, sadd]
  rw [hcEq] at hlink
  have hlink0 : lkm.linkSpec (pre ++ cb0 ++ (cb1 ++ sadd ++ post)) = .ok (env.code, env.labels) := by
    simpa [List.append_assoc] using hlink
  have hbr0 := run_br_step env pre _ .bltu AbiReg.a0 AbiReg.t3 errLabel env.errTarget env.herrLbl (by decide) hlink0 st hpc
  have hcond0 : evalBranch .bltu (st.getReg AbiReg.a0) (st.getReg AbiReg.t3) = decide (ve.toNat < vi.toNat) := by
    rw [ha0, ht3, u64_toBitVec_eq_ofNat, u64_toBitVec_eq_ofNat]
    exact evalBranch_bltu_nat ve.toBitVec.isLt vi.toBitVec.isLt
  obtain ⟨_, st1, _, hrun0, hpc1Br, hoth0Br, _, hmem0Br⟩ := hbr0
  have hp0Br : PreservedFrameRegs fl (fun _ => False) st st1 :=
    preservedFrameRegs_of_t6_s1 hoth0Br
  by_cases hvevi : vi ≤ ve
  · have hviNat : vi.toNat ≤ ve.toNat := hvevi
    have hbr0F : evalBranch .bltu (st.getReg AbiReg.a0) (st.getReg AbiReg.t3) = false := by
      rw [hcond0, decide_eq_false_iff_not]; omega
    let pre1 := pre ++ cb0
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by
      rw [hpc1Br, hbr0F]; simp only [Bool.false_eq_true, ↓reduceIte]
      exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (lkm.totalSize_append pre cb0).symm
    have hlink1 : lkm.linkSpec (pre1 ++ cb1 ++ (sadd ++ post)) = .ok (env.code, env.labels) := by
      simpa [pre1, List.append_assoc] using hlink0
    have hbr1 := run_br_step env pre1 _ .bltu AbiReg.t0 AbiReg.a0 errLabel env.errTarget env.herrLbl (by decide) hlink1 st1 hpc1'
    have hcond1 : evalBranch .bltu (st1.getReg AbiReg.t0) (st1.getReg AbiReg.a0) = decide ((lm.src8 src).size < ve.toNat) := by
      rw [hoth0Br _ (by decide), hoth0Br _ (by decide), ht0, ha0, u64_toBitVec_eq_ofNat]
      exact evalBranch_bltu_nat hlenLt ve.toBitVec.isLt
    obtain ⟨_, st2, _, hrun1, hpc2Br, hoth1Br, _, hmem1Br⟩ := hbr1
    have hp1Br : PreservedFrameRegs fl (fun _ => False) st1 st2 :=
      preservedFrameRegs_of_t6_s1 hoth1Br
    by_cases hvesz : ve.toNat ≤ (lm.src8 src).size
    · simp only [hvevi, hvesz, and_self, ↓reduceIte]
      have hbr1F : evalBranch .bltu (st1.getReg AbiReg.t0) (st1.getReg AbiReg.a0) = false := by
        rw [hcond1, decide_eq_false_iff_not]; omega
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
      have hp2 : PreservedFrameRegs fl (fun _ => False) st2 st3 :=
        preservedFrameRegs_of_noT5_scratch2 hnoT5 AbiReg.t2 AbiReg.t5 (by decide) (by decide) hoth2
      have hrb_nn : 0 ≤ env.tab.romBase := ProgLayout.romBase_nonneg env.tab
      have hcoe : (env.tab.romBase + (romIdx c env.tab.rom : Int)) = ((env.tab.romBase.toNat + romIdx c env.tab.rom : Nat) : Int) := by
        rw [← Int.toNat_of_nonneg hrb_nn]; push_cast; rfl
      have ht2Val : st3.getReg AbiReg.t2 = L.T + BitVec.ofNat 64 (env.tab.romBase.toNat + romIdx c env.tab.rom) := by
        rw [ht2_3, hoth1Br _ (by decide), hoth0Br _ (by decide), hgp, hcoe]; rfl
      have hpcEq : lkm.totalSize pre2 + lkm.totalSize sadd = lkm.totalSize pre + lkm.totalSize codeCheck := by
        rw [hcEq]; simp only [pre2, pre1, lkm.totalSize_append]; omega
      exact ⟨_, st3, run_trans (run_trans hrun0 hrun1) hrun2, by rw [hpc3, hpcEq],
        (hoth2 _ (by decide) (by decide)).trans ((hoth1Br _ (by decide)).trans ((hoth0Br _ (by decide)).trans ha0)),
        (hoth2 _ (by decide) (by decide)).trans ((hoth1Br _ (by decide)).trans ((hoth0Br _ (by decide)).trans ht1)),
        ht2Val,
        by rw [hoth2 _ (by decide) (by decide), hoth1Br _ (by decide), hoth0Br _ (by decide), ht3, u64_toBitVec_eq_ofNat],
        by rw [hmem2, hmem1Br, hmem0Br],
        hp0Br.trans (hp1Br.trans hp2)⟩
    · simp only [hvevi, hvesz, and_false, ↓reduceIte]
      have hbr1T : evalBranch .bltu (st1.getReg AbiReg.t0) (st1.getReg AbiReg.a0) = true := by
        rw [hcond1, decide_eq_true_iff]; omega
      exact ⟨_, st2, run_trans hrun0 hrun1, by rw [hpc2Br, hbr1T]; rfl,
        by rw [hmem1Br, hmem0Br], hp0Br.trans hp1Br⟩
  · have hviNat : ¬(vi.toNat ≤ ve.toNat) := hvevi
    simp only [hvevi, false_and, ↓reduceIte]
    have hbr0T : evalBranch .bltu (st.getReg AbiReg.a0) (st.getReg AbiReg.t3) = true := by
      rw [hcond0, decide_eq_true_iff]; omega
    exact ⟨_, st1, hrun0, by rw [hpc1Br, hbr0T]; rfl, hmem0Br, hp0Br⟩

private theorem reg_scan8_loop_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hnoT5 : fl.useT5Gp = false)
    (lm : _root_.L.Mem) (src : BSrc) (hsrc : bsrcOkB env.tab src = true)
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
        PreservedFrameRegs fl (fun _ => False) st r' := by
  intro rem
  induction rem with
  | zero =>
    intro i st hiRem hpc ha0 ht1 ht2 ht3 _
    have ⟨_, hl1⟩ := linkResolved_mid_split lkm pre [Asm.lbl loopLbl] _ post hlink
    have ⟨hlBge, _⟩ := linkResolved_mid_split lkm (pre ++ [Asm.lbl loopLbl]) [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl] _ post hl1
    have hbr := run_br_step env (pre ++ [Asm.lbl loopLbl]) _ .bgeu AbiReg.t3 AbiReg.a0 doneLbl doneTarget hdoneLbl (by decide)
      hlBge st (by rw [lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero, ← hltLoop]; exact hpc)
    have hcond : evalBranch .bgeu (st.getReg AbiReg.t3) (st.getReg AbiReg.a0) = true := by
      rw [ht3, ha0, u64_toBitVec_eq_ofNat]
      rw [evalBranch_bgeu_nat (a := i) (b := ve.toNat) (by omega) (by simpa using ve.toBitVec.isLt), decide_eq_true_iff]; omega
    obtain ⟨kBr, st', _, hrun, hpcBr, hothBr, _, hmemBr⟩ := hbr
    have hscan : _root_.L.scanN (lm.src8 src) c i ve.toNat = i := by
      have hnot : ¬(i < ve.toNat) := by omega
      unfold _root_.L.scanN; simp only [hnot, ↓reduceIte]
    exact ⟨kBr, st', hrun, by rw [hpcBr, hcond]; rfl, by rw [hscan, hothBr _ (by decide)]; exact ht3,
      hmemBr, preservedFrameRegs_of_t6_s1 hothBr⟩
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
    obtain ⟨_, st1, _, hrun1, hpc1Br, hoth1, _, hmem1⟩ := hbr
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize ((pre ++ [Asm.lbl loopLbl]) ++ [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl])) := by
      rw [hpc1Br, hcond]; simp only [Bool.false_eq_true, ↓reduceIte, lkm.totalSize_append, Asm.bgeu, Asm.br, lkm.totalSize_singleton]
    let st2 := stepReg st1 AbiReg.t4 (evalAlu .add (st1.getReg AbiReg.t1) (st1.getReg AbiReg.t3))
      (BitVec.ofNat 64 (4 * (lkm.totalSize ((pre ++ [Asm.lbl loopLbl]) ++ [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl]) + 1)))
    obtain ⟨hrun2, hpc2, ht4_2, hoth2, hmem2, _⟩ :=
      run_alu_step env _ _ .add AbiReg.t4 AbiReg.t1 AbiReg.t3 nonPreserved_t4 hl2 st1 hpc1'
    have htwAdd1 : lkm.totalSize [Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3] = 1 := by simp only [Asm.add, lkm.totalSize_instr]
    obtain ⟨hrun3, hpc3, ht4_3, hoth3, hmem3, _⟩ :=
      run_lbu_zero_step env _ _ AbiReg.t4 AbiReg.t4 nonPreserved_t4 hl3 st2 (by rw [lkm.totalSize_append, htwAdd1]; exact hpc2)
    let st3 := stepReg st2 AbiReg.t4 (BitVec.zeroExtend 64 (st2.mem (st2.getReg AbiReg.t4)))
      (BitVec.ofNat 64 (4 * (lkm.totalSize (((pre ++ [Asm.lbl loopLbl]) ++ [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl]) ++ [Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3]) + 1)))
    have htwLbu1 : lkm.totalSize [Asm.lbu AbiReg.t4 AbiReg.t4 0#12] = 1 := by simp only [Asm.lbu, lkm.totalSize_instr]
    let st4 := stepReg st3 AbiReg.t5 (evalAlu .add (st3.getReg AbiReg.t2) (st3.getReg AbiReg.t4))
      (BitVec.ofNat 64 (4 * (lkm.totalSize ((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl]) ++ [Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3]) ++ [Asm.lbu AbiReg.t4 AbiReg.t4 0#12]) + 1)))
    obtain ⟨hrun4, hpc4, ht5_4, hoth4, hmem4, _⟩ :=
      run_alu_step env _ _ .add AbiReg.t5 AbiReg.t2 AbiReg.t4 nonPreserved_t5 hl4 st3 (by rw [lkm.totalSize_append, htwLbu1]; exact hpc3)
    have htwAdd2 : lkm.totalSize [Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4] = 1 := by simp only [Asm.add, lkm.totalSize_instr]
    obtain ⟨hrun5, hpc5, ht5_5, hoth5, hmem5, _⟩ :=
      run_lbu_zero_step env _ _ AbiReg.t5 AbiReg.t5 nonPreserved_t5 hl5 st4 (by rw [lkm.totalSize_append, htwAdd2]; exact hpc4)
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
        rw [ht4_2, evalAlu]; change st1.getReg AbiReg.t1 + st1.getReg AbiReg.t3 = _
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
      dsimp only [cval]; rw [hrom_eq, hgetC]
    have ht3_5 : st5.getReg AbiReg.t3 = BitVec.ofNat 64 i :=
      (hoth5 _ (by decide)).trans ((hoth4 _ (by decide)).trans ((hoth3 _ (by decide)).trans ((hoth2 _ (by decide)).trans ((hoth1 _ (by decide)).trans ht3))))
    have hmem5 : st5.mem = st.mem := hmem4.trans (hmem3.trans (hmem2.trans hmem1))
    have hp05 : PreservedFrameRegs fl (fun _ => False) st st5 :=
      (preservedFrameRegs_of_t6_s1 hoth1).trans
        ((PreservedFrameRegs.of_scratch1 AbiReg.t4 (by decide) hoth2).trans
          ((PreservedFrameRegs.of_scratch1 AbiReg.t4 (by decide) hoth3).trans
            ((preservedFrameRegs_of_noT5_scratch1 hnoT5 AbiReg.t5 (by decide) hoth4).trans
              (preservedFrameRegs_of_noT5_scratch1 hnoT5 AbiReg.t5 (by decide) hoth5))))
    have hrun15 := run_trans (run_trans (run_trans hrun1 hrun2) hrun3) (run_trans hrun4 hrun5)
    obtain ⟨_, st6, _, hrun6, hpc6Br, hoth6Br, _, hmem6Br⟩ := hbr2
    have hp6Br : PreservedFrameRegs fl (fun _ => False) st5 st6 :=
      preservedFrameRegs_of_t6_s1 hoth6Br
    by_cases hcz : cval ≠ 0
    · have hbneT : evalBranch .bne (st5.getReg AbiReg.t5) (st5.getReg AbiReg.zero) = true := by
        rw [ht5Val, getReg_zero]; simp only [evalBranch, bne_iff_ne, ne_eq]
        intro heq
        have hnat := congrArg BitVec.toNat heq
        rw [BitVec.zeroExtend, BitVec.toNat_setWidth, UInt8.toNat_toBitVec,
            Nat.mod_eq_of_lt (Nat.lt_trans (UInt8.toNat_lt _) (by decide : 2 ^ 8 < 2 ^ 64)),
            show (0#64 : BitVec 64).toNat = 0 from rfl] at hnat
        exact hcz (by rcases cval with ⟨bv⟩; congr; exact BitVec.eq_of_toNat_eq (by simpa using hnat))
      have hscan : _root_.L.scanN (lm.src8 src) c i ve.toNat = i := by
        have hlt : i < ve.toNat := by omega
        dsimp only [cval, bval] at hcz; unfold _root_.L.scanN; simp only [eq_true hlt, eq_true hcz, ↓reduceIte]
      exact ⟨_, st6, run_trans hrun15 hrun6, by rw [hpc6Br, hbneT]; rfl,
        by rw [hscan, hoth6Br _ (by decide)]; exact ht3_5, hmem6Br.trans hmem5, hp05.trans hp6Br⟩
    · have hc0 : cval = 0 := Classical.not_not.mp hcz
      have hbneF : evalBranch .bne (st5.getReg AbiReg.t5) (st5.getReg AbiReg.zero) = false := by
        rw [ht5Val, hc0, getReg_zero]; decide
      have hpc6' : st6.pc = BitVec.ofNat 64 (4 * lkm.totalSize (((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl]) ++ [Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3]) ++ [Asm.lbu AbiReg.t4 AbiReg.t4 0#12]) ++ [Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4]) ++ [Asm.lbu AbiReg.t5 AbiReg.t5 0#12]) ++ [Asm.bne AbiReg.t5 AbiReg.zero doneLbl])) := by
        rw [hpc6Br, hbneF]; simp only [Bool.false_eq_true, ↓reduceIte, lkm.totalSize_append, Asm.bne, Asm.br, lkm.totalSize_singleton]
      obtain ⟨hrun7, hpc7, ht3_7, hoth7, hmem7, _⟩ :=
        run_aluImm_step env _ _ .addi AbiReg.t3 AbiReg.t3 1#12 nonPreserved_t3 hl7 st6 hpc6'
      let st7 := stepReg st6 AbiReg.t3 (evalAluImm .addi (st6.getReg AbiReg.t3) 1#12)
        (BitVec.ofNat 64 (4 * (lkm.totalSize (((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl]) ++ [Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3]) ++ [Asm.lbu AbiReg.t4 AbiReg.t4 0#12]) ++ [Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4]) ++ [Asm.lbu AbiReg.t5 AbiReg.t5 0#12]) ++ [Asm.bne AbiReg.t5 AbiReg.zero doneLbl]) + 1)))
      have htwAddi : lkm.totalSize [Asm.addi AbiReg.t3 AbiReg.t3 1#12] = 1 := by simp only [Asm.addi, lkm.totalSize_instr]
      have hpc64J : 4 * (lkm.totalSize ((((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl]) ++ [Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3]) ++ [Asm.lbu AbiReg.t4 AbiReg.t4 0#12]) ++ [Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4]) ++ [Asm.lbu AbiReg.t5 AbiReg.t5 0#12]) ++ [Asm.bne AbiReg.t5 AbiReg.zero doneLbl]) ++ [Asm.addi AbiReg.t3 AbiReg.t3 1#12]) + lkm.itemSize (.j loopLbl)) < 2 ^ 64 := by
        simpa [Asm.j, lkm.totalSize_singleton] using linkResolved_sub_pc64 env _ [Asm.j loopLbl] _ hl8
      obtain ⟨_, st8, hrun8, hpc8, hoth8, _, hmem8⟩ :=
        prog_step_j env _ _ loopLbl loopTarget hloopLbl hl8 hpc64J st7 (by rw [lkm.totalSize_append, htwAddi]; exact hpc7)
      have ha0_8 : st8.getReg AbiReg.a0 = ve.toBitVec := by
        rw [hoth8 _ (by decide)]; change st7.getReg AbiReg.a0 = _
        rw [hoth7 _ (by decide), hoth6Br _ (by decide)]; change st5.getReg AbiReg.a0 = _
        rw [hoth5 _ (by decide), hoth4 _ (by decide), hoth3 _ (by decide), hoth2 _ (by decide), hoth1 _ (by decide)]; exact ha0
      have ht1_8 : st8.getReg AbiReg.t1 = bsrcAddr env.tab L src := by
        rw [hoth8 _ (by decide)]; change st7.getReg AbiReg.t1 = _
        rw [hoth7 _ (by decide), hoth6Br _ (by decide)]; change st5.getReg AbiReg.t1 = _
        rw [hoth5 _ (by decide), hoth4 _ (by decide), hoth3 _ (by decide), hoth2 _ (by decide), hoth1 _ (by decide)]; exact ht1
      have ht2_8 : st8.getReg AbiReg.t2 = L.T + BitVec.ofNat 64 (env.tab.romBase.toNat + romIdx c env.tab.rom) := by
        rw [hoth8 _ (by decide)]; change st7.getReg AbiReg.t2 = _
        rw [hoth7 _ (by decide), hoth6Br _ (by decide)]; change st5.getReg AbiReg.t2 = _
        rw [hoth5 _ (by decide), hoth4 _ (by decide), hoth3 _ (by decide), hoth2 _ (by decide), hoth1 _ (by decide)]; exact ht2
      have ht3_8 : st8.getReg AbiReg.t3 = BitVec.ofNat 64 (i + 1) := by
        rw [hoth8 _ (by decide)]; change st7.getReg AbiReg.t3 = _
        rw [ht3_7, evalAluImm, hoth6Br _ (by decide)]; change st5.getReg AbiReg.t3 + sextImm12 1#12 = _
        rw [ht3_5, show sextImm12 1#12 = BitVec.ofNat 64 1 from by decide, ← BitVec.ofNat_add]
      have hmem08 : st8.mem = st.mem := hmem8.trans (hmem7.trans (hmem6Br.trans hmem5))
      obtain ⟨_, stEnd, hrunRest, hpcEnd, ht3End, hmemEnd, hpRest⟩ :=
        ih (i + 1) st8 (by omega) hpc8 ha0_8 ht1_8 ht2_8 ht3_8 (hmem08 ▸ hm)
      have hscan : _root_.L.scanN (lm.src8 src) c i ve.toNat = _root_.L.scanN (lm.src8 src) c (i + 1) ve.toNat := by
        have hlt : i < ve.toNat := by omega
        dsimp only [cval, bval] at hcz; conv => lhs; unfold _root_.L.scanN
        simp only [eq_true hlt, eq_false hcz, ↓reduceIte]
      have hpStep : PreservedFrameRegs fl (fun _ => False) st st8 :=
        hp05.trans (hp6Br.trans ((PreservedFrameRegs.of_scratch1 AbiReg.t3 (by decide) hoth7).trans
          (preservedFrameRegs_of_t6_s1 hoth8)))
      have hrunStep := run_trans hrun15 (run_trans (run_trans hrun6 hrun7) hrun8)
      exact ⟨_, stEnd, run_trans hrunStep hrunRest, hpcEnd, by rw [hscan]; exact ht3End,
        hmemEnd.trans hmem08, hpStep.trans hpRest⟩

theorem reg_scan8_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hal : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (x : Var) (_hx : x < fl.nlocals) (src : BSrc) (hsrcOk : bsrcOkB env.tab src = true)
    (i e : Expr) (hiOk : exprOkB env.tab fl.nlocals i = true) (heOk : exprOkB env.tab fl.nlocals e = true)
    (hVfI : ExprVarsInFrame fl i) (hVfE : ExprVarsInFrame fl e)
    (live2 : Var → Bool)
    (hnoClob : ∀ rx, fl.alloc.lookup x = some rx → ∀ y, y ≠ x → live2 y = true → fl.alloc.lookup y ≠ some rx)
    (c : List UInt8) (hcLen : 256 ≤ c.length) (hcOk : env.tab.romSliceOkB c = true)
    (hTmp : usedTempsStmt (.scan8 x src i e c) ≤ fl.usedTemps)
    (pfx : String) (lblId : Nat) (brkLbl : Option String) (retLbl : String) (isTail : Bool)
    (pre post : List AsmItem)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hnoT5 : fl.useT5Gp = false) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOkR L fl sp st loc)
    (hlink : lkm.linkSpec (pre ++ (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.scan8 x src i e c)).1 ++ post) =
      .ok (env.code, env.labels))
    (p : _root_.L.Prog) :
    let codeS := (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.scan8 x src i e c)).1
    match _root_.L.step p (fun _ => throw .outOfFuel) (.scan8 x src i e c) { mem := lm, loc := loc } with
    | .ok (_, st') =>
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize codeS)) ∧
        PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) st r' ∧
        ProgMemRel env.tab L r'.mem st'.mem ∧
        ProgFrameOkLive L fl sp r' st'.loc live2 ∧
        ProgMemOutside (FnWriteMaskR L fl sp) st.mem r'.mem
    | .error _ =>
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) st r' ∧
        ProgMemOutside (FnWriteMaskR L fl sp) st.mem r'.mem := by
  have hvalid : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  have hvacT5 : ∀ s, T5GpOk L fl s := fun _ h => by rw [hnoT5] at h; cases h
  dsimp only [usedTempsStmt] at hTmp
  let loopLbl := s!"{pfx}_scan_{lblId}"
  let doneLbl := s!"{pfx}_scan_done_{lblId}"
  let ieCode :=
    match emitSimpleExprR env.tab fl AbiReg.a0 AbiReg.t5 e with
    | some ce =>
      let ci := match exprReg? fl.alloc i with
        | some ri => [Asm.mv AbiReg.t3 ri]
        | none => compileETo env.tab fl 0 AbiReg.a0 i ++ [Asm.mv AbiReg.t3 AbiReg.a0]
      ci ++ ce
    | none =>
      compileETo env.tab fl 0 AbiReg.a0 i ++
      storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 0) ++
      compileETo env.tab fl 1 AbiReg.a0 e ++
      loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t5 (fl.tempSlotOff 0)
  let srcSetup := bsrcSetup env.tab AbiReg.t1 AbiReg.t5 src
  let codeCheck := [Asm.bltu AbiReg.a0 AbiReg.t3 errLabel, Asm.bltu AbiReg.t0 AbiReg.a0 errLabel] ++
    addImmOff AbiReg.t2 AbiReg.gp AbiReg.t5 (env.tab.romBase + (romIdx c env.tab.rom : Int))
  let codeLoop := [Asm.lbl loopLbl, Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl,
    Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3, Asm.lbu AbiReg.t4 AbiReg.t4 0#12,
    Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4, Asm.lbu AbiReg.t5 AbiReg.t5 0#12,
    Asm.bne AbiReg.t5 AbiReg.zero doneLbl, Asm.addi AbiReg.t3 AbiReg.t3 1#12,
    Asm.j loopLbl, Asm.lbl doneLbl]
  let storeX := match fl.alloc.lookup x with
    | some rx => [Asm.mv rx AbiReg.t3]
    | none => if !(x ∈ fl.spilledVars) then [] else storeMemOff .sd AbiReg.sp AbiReg.t3 AbiReg.t5 (fl.varSlotOff x)
  have hcodeEq : (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.scan8 x src i e c)).1 =
      ieCode ++ srcSetup ++ codeCheck ++ codeLoop ++ storeX := by
    cases src <;> cases hse : emitSimpleExprR env.tab fl AbiReg.a0 AbiReg.t5 e <;>
      cases hri : exprReg? fl.alloc i <;>
      simp [compileSR, ieCode, hse, hri, srcSetup, bsrcSetup, codeCheck, codeLoop, storeX, loopLbl, doneLbl, List.append_assoc] <;> rfl
  rw [hcodeEq] at hlink
  have hlinkIE : lkm.linkSpec (pre ++ ieCode ++ (srcSetup ++ codeCheck ++ codeLoop ++ storeX ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
  have hieSim : match _root_.L.evalE i ⟨lm, loc⟩, _root_.L.evalE e ⟨lm, loc⟩ with
      | .ok (vi, _), .ok (ve, _) =>
        ∃ k st3, RV64.run env.rom k st = .cont st3 ∧
          st3.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize ieCode)) ∧
          st3.getReg AbiReg.t3 = vi.toBitVec ∧
          st3.getReg AbiReg.a0 = ve.toBitVec ∧
          PreservedFrameRegs fl (fun _ => False) st st3 ∧
          ProgMemRel env.tab L st3.mem lm ∧
          ProgFrameOkR L fl sp st3 loc ∧
          ProgMemOutside (FnWriteMaskR L fl sp) st.mem st3.mem
      | _, _ =>
        ∃ k st3, RV64.run env.rom k st = .cont st3 ∧
          st3.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedFrameRegs fl (fun _ => False) st st3 ∧
          ProgMemOutside (FnWriteMaskR L fl sp) st.mem st3.mem := by
    cases hse : emitSimpleExprR env.tab fl AbiReg.a0 AbiReg.t5 e with
    | some ce =>
      have hseSimple : isSimpleExpr e = true := by
        cases e <;> simp [emitSimpleExprR, isSimpleExpr] at hse ⊢
      simp only [hseSimple, ↓reduceIte] at hTmp
      cases hri : exprReg? fl.alloc i with
      | some ri =>
        have hieEq : ieCode = [Asm.mv AbiReg.t3 ri] ++ ce := by simp only [ieCode, hse, hri]
        rw [hieEq] at hlinkIE ⊢
        obtain ⟨hriMem, _, vi, hvi, hgri⟩ := reg_exprReg_sim (lm := lm) hfl hf hiOk hri
        have h64 := linkResolved_sub_pc64 env pre ([Asm.mv AbiReg.t3 ri] ++ ce) _ hlinkIE
        have htw_all : lkm.totalSize ([Asm.mv AbiReg.t3 ri] ++ ce) = 1 + lkm.totalSize ce := by
          rw [lkm.totalSize_append, Asm.mv, lkm.totalSize_instr]
        have hsMv := step_item_instr_lm lkm env.hrom pre (ce ++ (srcSetup ++ codeCheck ++ codeLoop ++ storeX ++ post))
          (.aluImm .addi AbiReg.t3 ri 0#12)
          (by simpa only [Asm.mv, List.append_assoc] using hlinkIE)
          (by rw [htw_all] at h64; omega) st hpc
        let st1 := stepReg st AbiReg.t3 (st.getReg ri) (st.pc + 4#64)
        have hrun1 : RV64.run env.rom 1 st = .cont st1 :=
          run_one_cont _ _ st1 (by rw [hsMv]; simp only [execInstr, evalAluImm, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero]; rfl)
        have htw1 : lkm.totalSize (pre ++ [Asm.mv AbiReg.t3 ri]) = lkm.totalSize pre + 1 := by
          rw [lkm.totalSize_append, Asm.mv, lkm.totalSize_instr]
        have hpc1 : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ [Asm.mv AbiReg.t3 ri])) := by
          change st.pc + 4#64 = _; rw [pc_add_4_ofNat st.pc hpc, htw1]
        have hp1 : PreservedFrameRegs fl (fun _ => False) st st1 :=
          PreservedFrameRegs.of_scratch1 AbiReg.t3 (by decide) (fun r hr => getReg_stepReg_ne st AbiReg.t3 r hr _ _)
        have hmem1 : st1.mem = st.mem := mem_stepReg st _ _ _
        obtain ⟨ve, ke, st2, hve, hrun2, hpc2, ha0_2, hoth2, hmem2⟩ :=
          reg_emitSimpleExprR_sim env L fl hfl lm loc hal (pre ++ [Asm.mv AbiReg.t3 ri])
            (srcSetup ++ codeCheck ++ codeLoop ++ storeX ++ post)
            AbiReg.a0 AbiReg.t5 (by decide) (by decide) (by decide) (by decide)
            (fun h => by rw [hnoT5] at h; cases h) e ce hse heOk hVfE
            (by simpa only [List.append_assoc] using hlinkIE)
            (by rw [htw1]; rw [htw_all] at h64; omega) st1 hpc1
            (hp1.abi.gp.trans hgp) (hvacT5 _) (hp1.abi.sp.trans hsp)
            (by rw [hmem1]; exact hm)
            (ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) (hp1.mono (fun _ h => False.elim h))
              (by rw [hmem1]; exact MemEqOutside.refl _ _) hf)
        rw [hvi, hve]
        have hp2 : PreservedFrameRegs fl (fun _ => False) st1 st2 :=
          preservedFrameRegs_of_noT5_scratch2 hnoT5 AbiReg.a0 AbiReg.t5 (by decide) (by decide) hoth2
        have hmem02 : st2.mem = st.mem := hmem2.trans hmem1
        have hp02 : PreservedFrameRegs fl (fun _ => False) st st2 := hp1.trans hp2
        exact ⟨1 + ke, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
          by rw [hpc2, htw1, htw_all]; congr 2; omega,
          (hoth2 AbiReg.t3 (by decide) (by decide)).trans ((getReg_stepReg_eq st AbiReg.t3 (by decide) _ _).trans hgri),
          ha0_2, hp02, by rw [hmem02]; exact hm,
          ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) (hp02.mono (fun _ h => False.elim h))
            (by rw [hmem02]; exact MemEqOutside.refl _ _) hf,
          by rw [hmem02]; exact ProgMemOutside.refl _ _⟩
      | none =>
        have hieEq : ieCode = compileETo env.tab fl 0 AbiReg.a0 i ++ [Asm.mv AbiReg.t3 AbiReg.a0] ++ ce := by
          simp only [ieCode, hse, hri, List.append_assoc]
        rw [hieEq] at hlinkIE ⊢
        let ci := compileETo env.tab fl 0 AbiReg.a0 i
        have h64 := linkResolved_sub_pc64 env pre (ci ++ [Asm.mv AbiReg.t3 AbiReg.a0] ++ ce) _ hlinkIE
        have htw_all : lkm.totalSize (ci ++ [Asm.mv AbiReg.t3 AbiReg.a0] ++ ce) = lkm.totalSize ci + 1 + lkm.totalSize ce := by
          simp only [lkm.totalSize_append, Asm.mv, lkm.totalSize_instr]
        have riSim := reg_evalExpr_sim env L fl hfl lm loc hal hlo hhi i pre
          (([Asm.mv AbiReg.t3 AbiReg.a0] ++ ce) ++ (srcSetup ++ codeCheck ++ codeLoop ++ storeX ++ post))
          0 AbiReg.a0 (Or.inl rfl) hiOk hVfI (by omega)
          (by simpa only [ci, List.append_assoc] using hlinkIE)
          (by rw [htw_all] at h64; dsimp only [ci] at h64 ⊢; omega) st hpc hgp (hvacT5 _) hsp hm hf
        rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
        · simp only [hvi] at riSim ⊢
          obtain ⟨ki, st1, hrun1, hpc1, ha0_1, hp1a, hout1⟩ := riSim
          have htw1 : lkm.totalSize (pre ++ ci) = lkm.totalSize pre + lkm.totalSize ci := lkm.totalSize_append pre ci
          have hsMv := step_item_instr_lm lkm env.hrom (pre ++ ci)
            (ce ++ (srcSetup ++ codeCheck ++ codeLoop ++ storeX ++ post))
            (.aluImm .addi AbiReg.t3 AbiReg.a0 0#12)
            (by simpa only [ci, Asm.mv, List.append_assoc] using hlinkIE)
            (by rw [htw1]; rw [htw_all] at h64; omega) st1 (by rw [htw1]; exact hpc1)
          let st2 := stepReg st1 AbiReg.t3 (st1.getReg AbiReg.a0) (st1.pc + 4#64)
          have hrun2 : RV64.run env.rom 1 st1 = .cont st2 :=
            run_one_cont _ _ st2 (by rw [hsMv]; simp only [execInstr, evalAluImm, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero]; rfl)
          have htw2 : lkm.totalSize (pre ++ ci ++ [Asm.mv AbiReg.t3 AbiReg.a0]) = lkm.totalSize pre + lkm.totalSize ci + 1 := by
            rw [lkm.totalSize_append, htw1, Asm.mv, lkm.totalSize_instr]
          have hpc2 : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ci ++ [Asm.mv AbiReg.t3 AbiReg.a0])) := by
            change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1, htw2]
          have hp2 : PreservedFrameRegs fl (fun _ => False) st1 st2 :=
            PreservedFrameRegs.of_scratch1 AbiReg.t3 (by decide) (fun r hr => getReg_stepReg_ne st1 AbiReg.t3 r hr _ _)
          have hp02 : PreservedFrameRegs fl (fun _ => False) st st2 := (PreservedFrameRegs.of_a0 hp1a).trans hp2
          have hmem2 : st2.mem = st1.mem := mem_stepReg st1 _ _ _
          have hout2 : MemEqOutside (tempSpanR fl sp 0) st.mem st2.mem := by rw [hmem2]; exact hout1
          have hm2 := ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) hout2 hm
          have hf2 := ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) (hp02.mono (fun _ h => False.elim h))
            hout2 hf
          obtain ⟨ve, ke, st3, hve, hrun3, hpc3, ha0_3, hoth3, hmem3⟩ :=
            reg_emitSimpleExprR_sim env L fl hfl lm loc hal (pre ++ ci ++ [Asm.mv AbiReg.t3 AbiReg.a0])
              (srcSetup ++ codeCheck ++ codeLoop ++ storeX ++ post)
              AbiReg.a0 AbiReg.t5 (by decide) (by decide) (by decide) (by decide)
              (fun h => by rw [hnoT5] at h; cases h) e ce hse heOk hVfE
              (by simpa only [ci, List.append_assoc] using hlinkIE)
              (by rw [htw2]; rw [htw_all] at h64; omega) st2 hpc2
              (hp02.abi.gp.trans hgp) (hvacT5 _) (hp02.abi.sp.trans hsp) hm2 hf2
          rw [hve]
          have hp3 : PreservedFrameRegs fl (fun _ => False) st2 st3 :=
            preservedFrameRegs_of_noT5_scratch2 hnoT5 AbiReg.a0 AbiReg.t5 (by decide) (by decide) hoth3
          have hmem13 : st3.mem = st1.mem := hmem3.trans hmem2
          exact ⟨ki + (1 + ke), st3,
            by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
            by rw [hpc3, htw2, htw_all]; congr 2; omega,
            (hoth3 AbiReg.t3 (by decide) (by decide)).trans ((getReg_stepReg_eq st1 AbiReg.t3 (by decide) _ _).trans ha0_1),
            ha0_3, hp02.trans hp3, by rw [hmem3]; exact hm2,
            ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) (hp3.mono (fun _ h => False.elim h))
              (by rw [hmem3]; exact MemEqOutside.refl _ _) hf2,
            by rw [hmem13]; exact ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) hout1⟩
        · simp only [hvi] at riSim ⊢
          obtain ⟨ki, st1, hrun1, hpc1, hp1, hout1⟩ := riSim
          exact ⟨ki, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hp1,
            ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) hout1⟩
    | none =>
      have hseF : isSimpleExpr e = false := isSimpleExpr_false_of_emitSimple_none hse
      simp only [hseF, Bool.false_eq_true, ↓reduceIte] at hTmp
      let ci := compileETo env.tab fl 0 AbiReg.a0 i ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 0)
      let ce := compileETo env.tab fl 1 AbiReg.a0 e
      let clVi := loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t5 (fl.tempSlotOff 0)
      have hieEq : ieCode = ci ++ ce ++ clVi := by simp only [ieCode, hse, ci, ce, clVi, List.append_assoc]
      rw [hieEq] at hlinkIE ⊢
      have hlink0 : lkm.linkSpec (pre ++ ci ++ (ce ++ clVi ++ (srcSetup ++ codeCheck ++ codeLoop ++ storeX ++ post))) =
          .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlinkIE
      have hs0Sim := reg_evalToTemp_sim env L fl hfl lm loc hal hlo hhi 0 i hiOk hVfI (by omega) pre _ hlink0 st hpc hgp (hvacT5 _) hsp hm hf
      rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hiE⟩ | hiE
      · rw [hiE] at hs0Sim ⊢
        obtain ⟨_, st1, hrun0, hpc0, hslot0, hp0, hout0⟩ := hs0Sim
        have hm1 := ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) hout0 hm
        have hf1 := ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) (hp0.mono (fun _ h => False.elim h)) hout0 hf
        have hpm0 : ProgMemOutside (FnWriteMaskR L fl sp) st.mem st1.mem :=
          ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) hout0
        let pre1 := pre ++ ci
        have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by rw [hpc0, lkm.totalSize_append pre ci]
        have hlink1 : lkm.linkSpec (pre1 ++ ce ++ (clVi ++ (srcSetup ++ codeCheck ++ codeLoop ++ storeX ++ post))) =
            .ok (env.code, env.labels) := by simpa [pre1, List.append_assoc] using hlink0
        have hs1Sim := reg_evalExpr_sim env L fl hfl lm loc hal hlo hhi e pre1 _ 1 AbiReg.a0 (Or.inl rfl)
          heOk hVfE (by omega) hlink1 (linkResolved_sub_pc64 env pre1 ce _ hlink1) st1 hpc1'
          (hp0.abi.gp.trans hgp) (hvacT5 _) (hp0.abi.sp.trans hsp) hm1 hf1
        rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨ve, heE⟩ | heE
        · rw [heE] at hs1Sim ⊢
          obtain ⟨_, st2, hrun1, hpc1, ha0_2, hp1a, hout1⟩ := hs1Sim
          have hp1 : PreservedFrameRegs fl (fun _ => False) st1 st2 := PreservedFrameRegs.of_a0 hp1a
          have hm2 := ProgMemRel.of_tempSpanR hlo hhi (by omega : 1 ≤ fl.usedTemps) hout1 hm1
          have hf2 := ProgFrameOkR.of_preserved_temp hfl hvalid (by omega : 1 ≤ fl.usedTemps) hp1a hout1 hf1
          have hpm1 : ProgMemOutside (FnWriteMaskR L fl sp) st1.mem st2.mem :=
            ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (by omega : 1 ≤ fl.usedTemps)) hout1
          have hslot0_2 : readWord64 st2.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff 0)) = vi.toBitVec := by
            rw [readWord64_tempSlotR_of_tempSpanR (by omega : 0 < 1) (by omega) hvalid hout1]; exact hslot0
          let pre2 := pre1 ++ ce
          have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) := by rw [hpc1, lkm.totalSize_append pre1 ce]
          have hlink2 : lkm.linkSpec (pre2 ++ clVi ++ (srcSetup ++ codeCheck ++ codeLoop ++ storeX ++ post)) =
              .ok (env.code, env.labels) := by simpa [pre2, List.append_assoc] using hlink1
          have hsp2 : st2.getReg AbiReg.sp = sp := hp1.abi.sp.trans (hp0.abi.sp.trans hsp)
          have hal0 : isAligned (st2.getReg AbiReg.sp + BitVec.ofInt 64 (fl.tempSlotOff 0)) 8 = true := by
            rw [hsp2, tempSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hal _
          obtain ⟨st3, hrun2, hoth2, ht3_3, hmem2, hpc3⟩ :=
            loadMemOff_ld_correct_lm lkm env.hrom pre2 _ AbiReg.t3 AbiReg.sp AbiReg.t5
              (by decide) (by decide) (by decide) (fl.tempSlotOff 0) hlink2
              (linkResolved_sub_pc64 env pre2 clVi _ hlink2) st2 hpc2' hal0
          have hp2 : PreservedFrameRegs fl (fun _ => False) st2 st3 :=
            preservedFrameRegs_of_noT5_scratch2 hnoT5 AbiReg.t3 AbiReg.t5 (by decide) (by decide) hoth2
          exact ⟨_, st3, run_trans (run_trans hrun0 hrun1) hrun2,
            by rw [hpc3]; dsimp only [pre2, pre1, clVi]; simp only [lkm.totalSize_append, Nat.add_assoc],
            by rw [ht3_3, hsp2, hslot0_2],
            (hoth2 _ (by decide) (by decide)).trans ha0_2,
            hp0.trans (hp1.trans hp2),
            by rw [hmem2]; exact hm2,
            ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) (hp2.mono (fun _ h => False.elim h))
              (by rw [hmem2]; exact MemEqOutside.refl _ _) hf2,
            by rw [hmem2]; exact hpm0.trans hpm1⟩
        · rw [heE] at hs1Sim ⊢
          obtain ⟨_, st', hrun1, hpc1, hp1, hout1⟩ := hs1Sim
          exact ⟨_, st', run_trans hrun0 hrun1, hpc1, hp0.trans (PreservedFrameRegs.of_a0 hp1),
            hpm0.trans (ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (by omega : 1 ≤ fl.usedTemps)) hout1)⟩
      · rw [hiE] at hs0Sim ⊢
        obtain ⟨_, st', hrun0, hpc0, hp0, hout0⟩ := hs0Sim
        exact ⟨_, st', hrun0, hpc0, hp0,
          ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) hout0⟩
  rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hiE⟩ | hiE
  · rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨ve, heE⟩ | heE
    · simp only [hiE, heE] at hieSim
      obtain ⟨_, st3, hrunIE, hpc3, ht3_3, ha0_3, hpIE, hm3, hf3, hpmIE⟩ := hieSim
      let pre3 := pre ++ ieCode
      have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre3) := by rw [hpc3, lkm.totalSize_append pre ieCode]
      have hlink3 : lkm.linkSpec (pre3 ++ srcSetup ++ (codeCheck ++ codeLoop ++ storeX ++ post)) =
          .ok (env.code, env.labels) := by simpa [pre3, List.append_assoc] using hlinkIE
      obtain ⟨_, st4, hrunB, hpc4, ht0_4, ht1_4, hlenLt, hothB, hmemB, _⟩ :=
        bsrc_setup_sim env L lm src hsrcOk AbiReg.t1 AbiReg.t5 (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)
          pre3 (codeCheck ++ codeLoop ++ storeX ++ post) hlink3 st3 hpc3'
          (hpIE.abi.gp.trans hgp) hm3
      have hpB : PreservedFrameRegs fl (fun _ => False) st3 st4 :=
        preservedFrameRegs_of_noT5_scratch3 hnoT5 AbiReg.t0 AbiReg.t1 AbiReg.t5 (by decide) (by decide) (by decide) hothB
      let pre4 := pre3 ++ srcSetup
      have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre4) := by rw [hpc4, lkm.totalSize_append pre3 srcSetup]
      have hlink4 : lkm.linkSpec (pre4 ++ codeCheck ++ (codeLoop ++ storeX ++ post)) =
          .ok (env.code, env.labels) := by simpa [pre4, List.append_assoc] using hlink3
      have ht3_4 : st4.getReg AbiReg.t3 = vi.toBitVec :=
        (hothB _ (by decide) (by decide) (by decide)).trans ht3_3
      have ha0_4 : st4.getReg AbiReg.a0 = ve.toBitVec :=
        (hothB _ (by decide) (by decide) (by decide)).trans ha0_3
      have hchk := reg_scan8_check_sim env L fl lm src c vi ve hlenLt pre4 codeCheck (codeLoop ++ storeX ++ post) rfl
        hlink4 st4 hpc4' (hpB.abi.gp.trans (hpIE.abi.gp.trans hgp)) hnoT5
        ht0_4 ht1_4 ht3_4 ha0_4
      have hrun0B := run_trans hrunIE hrunB
      have hp0B : PreservedFrameRegs fl (fun _ => False) st st4 := hpIE.trans hpB
      have hstepOk : _root_.L.step p (fun _ => throw .outOfFuel) (.scan8 x src i e c) { mem := lm, loc := loc } =
          if vi ≤ ve ∧ ve.toNat ≤ (lm.src8 src).size then
            .ok (Sig.normal, { mem := lm, loc := (({ mem := lm, loc := loc } : _root_.L.St).setLoc x
              (UInt64.ofNat (_root_.L.scanN (lm.src8 src) c vi.toNat ve.toNat))).loc })
          else .error .oob := by
        simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hiE, heE, get, getThe, MonadStateOf.get, StateT.get,
          _root_.L.setLoc, modify, throw, throwThe, MonadExceptOf.throw, Pure.pure, Except.pure]
        by_cases hb : vi ≤ ve ∧ ve.toNat ≤ (lm.src8 src).size <;> simp only [hb, ↓reduceIte] <;> rfl
      rw [hstepOk]
      by_cases hcond : vi ≤ ve ∧ ve.toNat ≤ (lm.src8 src).size
      · simp only [eq_true hcond, ↓reduceIte] at hchk ⊢
        obtain ⟨_, st5, hrunC, hpc5, ha0_5, ht1_5, ht2_5, ht3_5, hmemC, hpC⟩ := hchk
        let pre5 := pre4 ++ codeCheck
        have hpc5' : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre5) := by rw [hpc5, lkm.totalSize_append pre4 codeCheck]
        have hlink5 : lkm.linkSpec (pre5 ++ codeLoop ++ (storeX ++ post)) =
            .ok (env.code, env.labels) := by simpa [pre5, List.append_assoc] using hlink4
        have hloopLbl := lookupLabel_of_lbl_lm lkm pre5
          ([Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl, Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3,
            Asm.lbu AbiReg.t4 AbiReg.t4 0#12, Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4,
            Asm.lbu AbiReg.t5 AbiReg.t5 0#12, Asm.bne AbiReg.t5 AbiReg.zero doneLbl,
            Asm.addi AbiReg.t3 AbiReg.t3 1#12, Asm.j loopLbl, Asm.lbl doneLbl] ++ (storeX ++ post)) loopLbl
          (by simpa [codeLoop, List.append_assoc] using hlink5)
        have hdoneLbl := lookupLabel_of_lbl_lm lkm
          (pre5 ++ [Asm.lbl loopLbl, Asm.bgeu AbiReg.t3 AbiReg.a0 doneLbl, Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3,
            Asm.lbu AbiReg.t4 AbiReg.t4 0#12, Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4,
            Asm.lbu AbiReg.t5 AbiReg.t5 0#12, Asm.bne AbiReg.t5 AbiReg.zero doneLbl,
            Asm.addi AbiReg.t3 AbiReg.t3 1#12, Asm.j loopLbl]) (storeX ++ post) doneLbl
          (by simpa [codeLoop, List.append_assoc] using hlink5)
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
            lkm.totalSize pre5 + lkm.totalSize codeLoop := by rw [lkm.totalSize_append, ← htwDone]
        have hmem35 : st5.mem = st3.mem := hmemC.trans hmemB
        have hviLe : vi.toNat ≤ ve.toNat := hcond.1
        obtain ⟨_, st6, hrunL, hpc6, ht3_6, hmemL, hpL⟩ :=
          reg_scan8_loop_sim env L fl hnoT5 lm src hsrcOk c hcLen hcOk ve hcond.2 hlenLt
            loopLbl doneLbl (lkm.totalSize pre5) (lkm.totalSize pre5 + lkm.totalSize codeLoop)
            hloopLbl (by rw [← hdoneTgt]; exact hdoneLbl) pre5 (storeX ++ post) rfl hlink5
            (ve.toNat - vi.toNat) vi.toNat st5 (by omega) hpc5' ha0_5 ht1_5 ht2_5 ht3_5 (hmem35 ▸ hm3)
        let pre6 := pre5 ++ codeLoop
        have hpc6' : st6.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre6) := by rw [hpc6, lkm.totalSize_append pre5 codeLoop]
        have hlink6 : lkm.linkSpec (pre6 ++ storeX ++ post) = .ok (env.code, env.labels) := by
          simpa [pre6, List.append_assoc] using hlink5
        have hmem36 : st6.mem = st3.mem := hmemL.trans hmem35
        have hp36 : PreservedFrameRegs fl (fun _ => False) st3 st6 := hpB.trans (hpC.trans hpL)
        have hf6 : ProgFrameOkR L fl sp st6 loc :=
          ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) (hp36.mono (fun _ h => False.elim h))
            (by rw [hmem36]; exact MemEqOutside.refl _ _) hf3
        have hpcEq : lkm.totalSize pre6 + lkm.totalSize storeX =
            lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.scan8 x src i e c)).1 := by
          rw [hcodeEq]; simp only [pre6, pre5, pre4, pre3, lkm.totalSize_append]; omega
        let resWord := UInt64.ofNat (_root_.L.scanN (lm.src8 src) c vi.toNat ve.toNat)
        have hresLoc : (({ mem := lm, loc := loc } : _root_.L.St).setLoc x resWord).loc =
            fun y => if y = x then resWord else loc y := rfl
        rw [hresLoc]
        cases hlx : fl.alloc.lookup x with
        | some rx =>
          have hrxMem := (regAllocValid_lookup hfl.valid hlx).2.1
          have hrxAlloc : rx ∈ fl.alloc.map Prod.snd := List.mem_map.mpr ⟨(x, rx), list_lookup_mem hlx, rfl⟩
          have hrxNe0 : rx ≠ 0#5 := allowedRegs_ne_zero hrxMem
          have hstX : storeX = [Asm.mv rx AbiReg.t3] := by simp only [storeX, hlx]
          rw [hstX] at hlink6
          have h64X := linkResolved_sub_pc64 env pre6 [Asm.mv rx AbiReg.t3] post hlink6
          have htwX : lkm.totalSize [Asm.mv rx AbiReg.t3] = 1 := by simp only [Asm.mv, lkm.totalSize_instr]
          have hsMv := step_item_instr_lm lkm env.hrom pre6 post (.aluImm .addi rx AbiReg.t3 0#12)
            (by simpa only [Asm.mv] using hlink6) (by rw [htwX] at h64X; omega) st6 hpc6'
          let st7 := stepReg st6 rx (st6.getReg AbiReg.t3) (st6.pc + 4#64)
          have hrun7 : RV64.run env.rom 1 st6 = .cont st7 :=
            run_one_cont _ _ st7 (by rw [hsMv]; simp only [execInstr, evalAluImm, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero]; rfl)
          have hp7 : PreservedFrameRegs fl (· = rx) st6 st7 :=
            PreservedFrameRegs.of_target1 rx (Or.inr (allowedRegs_sub_true hrxMem)) (fun _ => rfl) (fun r hr => getReg_stepReg_ne st6 rx r hr _ _)
          have hmem7 : st7.mem = st6.mem := mem_stepReg st6 _ _ _
          have hrx7 : st7.getReg rx = resWord.toBitVec := by
            change (stepReg st6 rx _ _).getReg rx = _
            rw [getReg_stepReg_eq st6 rx hrxNe0, ht3_6]; rfl
          exact ⟨_, st7, run_trans (run_trans (run_trans hrun0B hrunC) hrunL) hrun7,
            by change st6.pc + 4#64 = _; rw [pc_add_4_ofNat st6.pc hpc6', ← hpcEq, hstX, htwX],
            ((hp0B.trans (hpC.trans hpL)).mono (fun _ h => False.elim h)).trans (hp7.mono (fun r (hr : r = rx) => hr ▸ hrxAlloc)),
            by rw [hmem7, hmem36]; exact hm3,
            ProgFrameOkR.of_set_reg_live hfl hvalid hlx hp7 hrx7 (by rw [hmem7]; exact MemEqOutside.refl _ _) (hnoClob rx hlx) hf6,
            by rw [hmem7, hmem36]; exact hpmIE⟩
        | none =>
          by_cases hmx : x ∈ fl.spilledVars
          · have hstX : storeX = storeMemOff .sd AbiReg.sp AbiReg.t3 AbiReg.t5 (fl.varSlotOff x) := by
              simp only [storeX, hlx, hmx, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            rw [hstX] at hlink6
            have hsp6 : st6.getReg AbiReg.sp = sp := hpL.abi.sp.trans (hpC.abi.sp.trans (hp0B.abi.sp.trans hsp))
            have halX : isAligned (st6.getReg AbiReg.sp + BitVec.ofInt 64 (fl.varSlotOff x)) 8 = true := by
              rw [hsp6, varSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hal _
            obtain ⟨st7, hrun7, hoth7, hmem7, hpc7⟩ :=
              storeMemOff_sd_correct_lm lkm env.hrom pre6 post AbiReg.sp AbiReg.t3 AbiReg.t5
                (by decide) (by decide) (by decide) (fl.varSlotOff x) hlink6
                (linkResolved_sub_pc64 env pre6 _ post hlink6) st6 hpc6' halX
            have hp7 : PreservedFrameRegs fl (· = AbiReg.a0) st6 st7 :=
              preservedFrameRegs_of_noT5_scratch1 hnoT5 AbiReg.t5 (by decide) hoth7
            have heq7 : MemEqOutside (varSlotSpanR fl sp x) st6.mem st7.mem := by
              rw [hmem7, hsp6, varSlotOff_ofInt]
              exact MemEqOutside.writeWord64 st6.mem _ _ fun k hk => ⟨k, hk, rfl⟩
            have hvarSubStack : (varSlotSpanR fl sp x).sub L.stackSpan := by
              have hsi := hfl.spillIdx_lt hmx
              intro a ⟨k, hk, ha⟩; subst ha; apply frameSpanR_sub_stackSpan L hlo hhi
              refine ⟨8 * (fl.protectedSlots + fl.spillIdx x) + k, ?_, ?_⟩
              · dsimp only [varSlotSpanR, slotSpan, frameSpanR, FrameLayout.frameSlots] at hk ⊢; omega
              · dsimp only [varSlotSpanR, slotSpan, slotAddr, frameSpanR]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
            have hpm7 : ProgMemOutside (FnWriteMaskR L fl sp) st3.mem st7.mem := by
              rw [← hmem36]; exact ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_varSlot L hfl hlo hhi hmx) heq7
            exact ⟨_, st7, run_trans (run_trans (run_trans hrun0B hrunC) hrunL) hrun7,
              by rw [hpc7, ← hstX, hpcEq],
              ((hp0B.trans (hpC.trans hpL)).mono (fun _ h => False.elim h)).trans (PreservedFrameRegs.of_a0 hp7),
              ProgMemRel.of_stack_eqOutside hvarSubStack heq7 (hmem36 ▸ hm3),
              (ProgFrameOkR.of_set_spill hfl hvalid hmx hp7 (by rw [hmem7, hsp6, ht3_6]; rfl) hf6).toLive_self live2,
              hpmIE.trans hpm7⟩
          · have hstX : storeX = [] := by
              simp only [storeX, hlx, hmx, decide_false, Bool.not_false, ↓reduceIte]
            exact ⟨_, st6, run_trans (run_trans hrun0B hrunC) hrunL,
              by rw [hpc6', ← hpcEq, hstX, lkm.totalSize_nil, Nat.add_zero],
              (hp0B.trans (hpC.trans hpL)).mono (fun _ h => False.elim h),
              by rw [hmem36]; exact hm3,
              (ProgFrameOkR.of_set_dead hfl hvalid resWord hlx hmx (PreservedFrameRegs.refl _ _ _) (MemEqOutside.refl _ _) hf6).toLive_self live2,
              by rw [hmem36]; exact hpmIE⟩
      · simp only [eq_false hcond, ↓reduceIte] at hchk ⊢
        obtain ⟨_, st5, hrunC, hpc5, hmemC, hpC⟩ := hchk
        exact ⟨_, st5, run_trans hrun0B hrunC, hpc5, (hp0B.trans hpC).mono (fun _ h => False.elim h),
          by rw [hmemC, hmemB]; exact hpmIE⟩
    · simp only [hiE, heE] at hieSim
      have hstepErr : _root_.L.step p (fun _ => throw .outOfFuel) (.scan8 x src i e c) ⟨lm, loc⟩ = .error .oob := by
        simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hiE, heE]
      rw [hstepErr]; obtain ⟨_, st', hrun1, hpc1, hp1, hpm1⟩ := hieSim
      exact ⟨_, st', hrun1, hpc1, hp1.mono (fun _ h => False.elim h), hpm1⟩
  · simp only [hiE] at hieSim
    have hstepErr : _root_.L.step p (fun _ => throw .outOfFuel) (.scan8 x src i e c) ⟨lm, loc⟩ = .error .oob := by
      simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hiE]
    rw [hstepErr]; obtain ⟨_, st', hrun0, hpc0, hp0, hpm0⟩ := hieSim
    exact ⟨_, st', hrun0, hpc0, hp0.mono (fun _ h => False.elim h), hpm0⟩

end ConAgua.RISCV.Compiler
