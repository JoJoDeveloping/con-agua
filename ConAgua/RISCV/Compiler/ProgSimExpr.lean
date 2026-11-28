import ConAgua.RISCV.Compiler.ProgSimBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Program Expression, Argument & Condition Simulation (`ConAgua.RISCV.Compiler.ProgSimExpr`)

Forward simulation for `_root_.L.Expr`, argument lists, and `_root_.L.Cond` (`progEvalExpr_sim`,
`progEvalArgs_sim`, `progEvalCond_sim`).

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard Lean axioms only.
-/

namespace ConAgua.RISCV.Compiler

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Linker

/-! ## 5. Forward Simulation of Expressions, Arguments, & Conditions -/

theorem prog_stepReg_mem (st : State) (r : Reg) (v npc : RV64.Word) :
    (stepReg st r v npc).mem = st.mem := by
  unfold stepReg State.setReg; split <;> rfl

theorem tempSpan_sub_frameSpan (sp : BitVec 64) (nl tmp nt : Nat) (hle : tmp ≤ nt) :
    (tempSpan sp nl tmp nt).sub (frameSpan sp nl nt) := by
  intro a ⟨k, hk, ha⟩
  dsimp only [tempSpan] at hk
  subst ha
  refine ⟨8 * (1 + nl + tmp) + k, ?_, ?_⟩
  · dsimp only [frameSpan]; omega
  · dsimp only [tempSpan, frameSpan]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem prog_step_j {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (target : String) (tgt : Nat)
    (htgt : lookupLabel env.labels target = some tgt)
    (hlink : lkm.linkSpec (pre ++ [.j target] ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.itemSize (.j target)) < 2 ^ 64) (st : State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre)) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * tgt) ∧
      (∀ q, q ≠ AbiReg.t6 ∧ q ≠ AbiReg.s1 → st'.getReg q = st.getReg q) ∧
      PreservedRegs st st' ∧
      st'.mem = st.mem := by
  obtain ⟨tgt', k, st', _, hlook, hrun, hpc', hreg, hmem⟩ :=
    step_item_j_lm lkm env.hrom pre post target hlink h64 st hpc
  rw [htgt] at hlook; obtain rfl := Option.some.inj hlook
  exact ⟨k, st', hrun, hpc', fun _ hq => (hreg.getReg_eq hq).symm, PreservedRegs.of_regEqExceptT6 hreg, hmem⟩

theorem ProgMemRel.of_tempSpan {lkm : LinkModel} (env : CodeEnvGen lkm) {L : ProgLayout env.tab}
    {sp : BitVec 64} {nl tmp nt : Nat}
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (htmp : tmp ≤ nt) {m1 m2 : ByteMem} {lm : _root_.L.Mem}
    (heq : MemEqOutside (tempSpan sp nl tmp nt) m1 m2)
    (hrel : ProgMemRel env.tab L m1 lm) :
    ProgMemRel env.tab L m2 lm :=
  ProgMemRel.of_stack_eqOutside
    (MemSpan.sub_trans (tempSpan_sub_frameSpan sp nl tmp nt htmp) (L.frame_sub_stackSpan hlo hhi))
    heq hrel

def progBinTail : BinOp → List AsmItem
  | .add => [Asm.add AbiReg.a0 AbiReg.t0 AbiReg.a0]
  | .sub => [Asm.sub AbiReg.a0 AbiReg.t0 AbiReg.a0]
  | .and => [Asm.and AbiReg.a0 AbiReg.t0 AbiReg.a0]
  | .or  => [Asm.or AbiReg.a0 AbiReg.t0 AbiReg.a0]
  | .xor => [Asm.xor AbiReg.a0 AbiReg.t0 AbiReg.a0]
  | .shl => [Asm.sll AbiReg.a0 AbiReg.t0 AbiReg.a0]
  | .shr => [Asm.srl AbiReg.a0 AbiReg.t0 AbiReg.a0]
  | .mul   => [Asm.mul   AbiReg.a0 AbiReg.t0 AbiReg.a0]
  | .mulhi => [Asm.mulhu AbiReg.a0 AbiReg.t0 AbiReg.a0]

def progCmpTail : Cmp → List AsmItem
  | .eq  => [Asm.sub AbiReg.a0 AbiReg.t0 AbiReg.a0, Asm.sltiu AbiReg.a0 AbiReg.a0 1#12]
  | .ne  => [Asm.sub AbiReg.a0 AbiReg.t0 AbiReg.a0, Asm.sltu AbiReg.a0 AbiReg.zero AbiReg.a0]
  | .ult => [Asm.sltu AbiReg.a0 AbiReg.t0 AbiReg.a0]
  | .ule => [Asm.sltu AbiReg.a0 AbiReg.a0 AbiReg.t0, Asm.xori AbiReg.a0 AbiReg.a0 1#12]
  | .slt => [Asm.slt AbiReg.a0 AbiReg.t0 AbiReg.a0]
  | .sle => [Asm.slt AbiReg.a0 AbiReg.a0 AbiReg.t0, Asm.xori AbiReg.a0 AbiReg.a0 1#12]

theorem prog_two_exprs_pair_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (lm : _root_.L.Mem) (loc : _root_.L.Locals)
    {sp : BitVec 64} {nl nt : Nat}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (pre tail : List AsmItem) (tmp : Nat) (e1 e2 : Expr)
    (htmp_le : tmp + 1 ≤ nt)
    (iha : ∀ (pre post : List AsmItem) (tmp : Nat) (st : State),
      tmp + maxTempsExpr e1 ≤ nt →
      lkm.linkSpec (pre ++ compileE env.tab nl tmp e1 ++ post) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp e1)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → st.getReg AbiReg.sp = sp →
      ProgMemRel env.tab L st.mem lm → ProgFrameOk L sp st.mem nl loc →
      match _root_.L.evalE e1 ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp e1))) ∧
          st'.getReg AbiReg.a0 = v.toBitVec ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem)
    (ihb : ∀ (pre post : List AsmItem) (tmp : Nat) (st : State),
      tmp + maxTempsExpr e2 ≤ nt →
      lkm.linkSpec (pre ++ compileE env.tab nl tmp e2 ++ post) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp e2)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → st.getReg AbiReg.sp = sp →
      ProgMemRel env.tab L st.mem lm → ProgFrameOk L sp st.mem nl loc →
      match _root_.L.evalE e2 ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp e2))) ∧
          st'.getReg AbiReg.a0 = v.toBitVec ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem)
    (htmp1 : tmp + maxTempsExpr e1 ≤ nt)
    (htmp2 : tmp + 1 + maxTempsExpr e2 ≤ nt)
    (hlink : lkm.linkSpec (pre ++ (compileE env.tab nl tmp e1 ++
        storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + tmp)) ++
        compileE env.tab nl (tmp + 1) e2 ++
        loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nl + tmp))) ++ tail) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp e1 ++
        storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + tmp)) ++
        compileE env.tab nl (tmp + 1) e2 ++
        loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nl + tmp)))) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOk L sp st.mem nl loc) :
    match _root_.L.evalE e1 ⟨lm, loc⟩, _root_.L.evalE e2 ⟨lm, loc⟩ with
    | .ok (v1, _), .ok (v2, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp e1 ++
          storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + tmp)) ++
          compileE env.tab nl (tmp + 1) e2 ++
          loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nl + tmp))))) ∧
        st'.getReg AbiReg.t0 = v1.toBitVec ∧
        st'.getReg AbiReg.a0 = v2.toBitVec ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
    | _, _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem := by
  let c1 := compileE env.tab nl tmp e1
  let cs := storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + tmp))
  let c2 := compileE env.tab nl (tmp + 1) e2
  let cl := loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nl + tmp))
  have hf : (frameSpan sp nl nt).valid := by
    simp only [frameSpan, MemSpan.valid]; have := L.hStackValid; omega
  have htw_all : lkm.totalSize (compileE env.tab nl tmp e1 ++
      storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + tmp)) ++
      compileE env.tab nl (tmp + 1) e2 ++
      loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nl + tmp))) =
      lkm.totalSize (compileE env.tab nl tmp e1) + lkm.totalSize cs + lkm.totalSize c2 + lkm.totalSize cl := by
    dsimp only [cs, c2, cl]; simp only [lkm.totalSize_append]
  have hlist1 : pre ++ c1 ++ (cs ++ c2 ++ cl ++ tail) =
      pre ++ (c1 ++ cs ++ c2 ++ cl) ++ tail := by
    simp only [List.append_assoc]
  have hlink1 : lkm.linkSpec (pre ++ c1 ++ (cs ++ c2 ++ cl ++ tail)) = .ok (env.code, env.labels) := by
    rw [hlist1]; exact hlink
  have r1 := iha pre (cs ++ c2 ++ cl ++ tail) tmp st htmp1 hlink1
    (by rw [htw_all] at h64; dsimp only [cs, c2, cl] at h64 ⊢; omega)
    hpc hgp hsp hmemRel hframeOk
  rcases _root_.L.evalE_pure e1 ⟨lm, loc⟩ with ⟨v1, hv1⟩ | hv1
  · simp only [hv1] at r1
    obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := r1
    have htw1 : lkm.totalSize (pre ++ c1) = lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp e1) :=
      lkm.totalSize_append _ _
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ c1)) := by
      rw [htw1]; exact hpc1
    have hlistS : (pre ++ c1) ++ cs ++ (c2 ++ cl ++ tail) =
        pre ++ (c1 ++ cs ++ c2 ++ cl) ++ tail := by
      simp only [List.append_assoc]
    have hlinkS : lkm.linkSpec ((pre ++ c1) ++ cs ++ (c2 ++ cl ++ tail)) = .ok (env.code, env.labels) := by
      rw [hlistS]; exact hlink
    have h64S : 4 * (lkm.totalSize (pre ++ c1) + lkm.totalSize cs) < 2 ^ 64 := by
      rw [htw1]; rw [htw_all] at h64; dsimp only [cs, c2, cl] at h64 ⊢; omega
    have halS : isAligned (st1.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff (nl + tmp))) 8 = true := by
      rw [hpres1.sp.trans hsp, slotOff_ofInt]; exact isAligned8_add_int_mul8 sp hspAlign _
    obtain ⟨st2, hrunS, hothS, hmemS, hpc2⟩ :=
      storeMemOff_sd_correct_lm lkm env.hrom (pre ++ c1) (c2 ++ cl ++ tail) AbiReg.sp AbiReg.a0 AbiReg.t0
        (by decide) (by decide) (by decide) (slotOff (nl + tmp)) hlinkS h64S st1 hpc1' halS
    have hpresS : PreservedRegs st1 st2 :=
      ⟨hothS _ (by decide), hothS _ (by decide), hothS _ (by decide), hothS _ (by decide)⟩
    have heqS : MemEqOutside (tempSpan sp nl tmp nt) st1.mem st2.mem := by
      rw [hmemS, hpres1.sp.trans hsp, slotOff_ofInt]
      apply MemEqOutside.writeWord64
      intro k hk
      exact tempSpan_slot_sub (Nat.le_refl tmp) htmp_le k hk
    have heq02 : MemEqOutside (tempSpan sp nl tmp nt) st.mem st2.mem :=
      MemEqOutside.trans heq1 heqS
    have htw2 : lkm.totalSize (pre ++ c1 ++ cs) =
        lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp e1) + lkm.totalSize cs := by
      rw [lkm.totalSize_append, htw1]
    have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ c1 ++ cs)) := by
      rw [htw2, ← htw1]; exact hpc2
    have hlist2 : (pre ++ c1 ++ cs) ++ c2 ++ (cl ++ tail) =
        pre ++ (c1 ++ cs ++ c2 ++ cl) ++ tail := by
      simp only [List.append_assoc]
    have hlink2 : lkm.linkSpec ((pre ++ c1 ++ cs) ++ c2 ++ (cl ++ tail)) = .ok (env.code, env.labels) := by
      rw [hlist2]; exact hlink
    have r2 := ihb (pre ++ c1 ++ cs) (cl ++ tail) (tmp + 1) st2 htmp2 hlink2
      (by rw [htw2]; rw [htw_all] at h64; dsimp only [cs, c2, cl] at h64 ⊢; omega)
      hpc2' (hpresS.gp.trans (hpres1.gp.trans hgp)) (hpresS.sp.trans (hpres1.sp.trans hsp))
      (ProgMemRel.of_tempSpan env hlo hhi (by omega) heq02 hmemRel)
      (ProgFrameOk.of_tempSpan hf (by omega) heq02 hframeOk)
    rcases _root_.L.evalE_pure e2 ⟨lm, loc⟩ with ⟨v2, hv2⟩ | hv2
    · simp only [hv1, hv2] at r2 ⊢
      obtain ⟨k2, st3, hrun2, hpc3, ha0_3, hpres2, heq2⟩ := r2
      have htw3 : lkm.totalSize (pre ++ c1 ++ cs ++ c2) =
          lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp e1) + lkm.totalSize cs +
          lkm.totalSize (compileE env.tab nl (tmp + 1) e2) := by
        rw [lkm.totalSize_append, htw2]
      have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ c1 ++ cs ++ c2)) := by
        rw [htw3, ← htw2]; exact hpc3
      have hlistL : (pre ++ c1 ++ cs ++ c2) ++ cl ++ tail =
          pre ++ (c1 ++ cs ++ c2 ++ cl) ++ tail := by
        simp only [List.append_assoc]
      have hlinkL : lkm.linkSpec ((pre ++ c1 ++ cs ++ c2) ++ cl ++ tail) = .ok (env.code, env.labels) := by
        rw [hlistL]; exact hlink
      have h64L : 4 * (lkm.totalSize (pre ++ c1 ++ cs ++ c2) + lkm.totalSize cl) < 2 ^ 64 := by
        rw [htw3]; rw [htw_all] at h64; dsimp only [cs, c2, cl] at h64 ⊢; omega
      have hsp3 : st3.getReg AbiReg.sp = sp :=
        hpres2.sp.trans (hpresS.sp.trans (hpres1.sp.trans hsp))
      have hal3 : isAligned (st3.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff (nl + tmp))) 8 = true := by
        rw [hsp3]; exact isAligned8_add_int_mul8 sp hspAlign _
      obtain ⟨st4, hrunL, hothL, ht0_4, hmemL, hpc4⟩ :=
        loadMemOff_ld_correct_lm lkm env.hrom (pre ++ c1 ++ cs ++ c2) tail AbiReg.t0 AbiReg.sp AbiReg.t1
          (by decide) (by decide) (by decide) (slotOff (nl + tmp)) hlinkL h64L st3 hpc3' hal3
      have hpresL : PreservedRegs st3 st4 :=
        ⟨hothL _ (by decide) (by decide), hothL _ (by decide) (by decide),
         hothL _ (by decide) (by decide),
         hothL _ (by decide) (by decide)⟩
      have hslot2 : readWord64 st2.mem (sp + BitVec.ofInt 64 (slotOff (nl + tmp))) = v1.toBitVec := by
        rw [hmemS, hpres1.sp.trans hsp, ha0_1]
        exact readWord64_writeWord64_self st1.mem _ _
      have hslot3 : readWord64 st3.mem (sp + BitVec.ofInt 64 (slotOff (nl + tmp))) = v1.toBitVec := by
        rw [← hslot2]
        apply MemEqOutside.readWord64_eq heq2
        intro k hk
        rw [slotOff_ofInt]
        exact (slotSpan_memDisjoint_tempSpan hf (by omega) (by omega)) _ ⟨k, hk, rfl⟩
      have heq2' : MemEqOutside (tempSpan sp nl tmp nt) st2.mem st3.mem :=
        heq2.mono (tempSpan_mono (Nat.le_succ tmp) htmp_le)
      refine ⟨k1 + (lkm.totalSize cs + (k2 + lkm.totalSize cl)), st4, ?_, ?_, ?_, ?_,
        (hpres1.trans hpresS).trans (hpres2.trans hpresL), ?_⟩
      · rw [run_add, hrun1]; dsimp only
        rw [run_add, hrunS]; dsimp only
        rw [run_add, hrun2]; dsimp only
        exact hrunL
      · rw [hpc4, htw3, htw_all]
        dsimp only [cs, c2, cl]
        congr 2; omega
      · rw [ht0_4, hsp3, hslot3]
      · rw [hothL AbiReg.a0 (by decide) (by decide), ha0_3]
      · rw [hmemL]; exact heq02.trans heq2'
    · simp only [hv1, hv2] at r2 ⊢
      obtain ⟨k2, st3, hrun2, hpc3, hpres2, heq2⟩ := r2
      have heq2' : MemEqOutside (tempSpan sp nl tmp nt) st2.mem st3.mem :=
        heq2.mono (tempSpan_mono (Nat.le_succ tmp) htmp_le)
      refine ⟨k1 + (lkm.totalSize cs + k2), st3, ?_, hpc3,
        (hpres1.trans hpresS).trans hpres2, heq02.trans heq2'⟩
      rw [run_add, hrun1]; dsimp only
      rw [run_add, hrunS]; dsimp only
      exact hrun2
  · simp only [hv1] at r1 ⊢
    exact r1

theorem prog_ld8_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (lm : _root_.L.Mem) (loc : _root_.L.Locals)
    {sp : BitVec 64} {nl nt : Nat}
    (pre post : List AsmItem) (tmp : Nat) (a : ArrId) (i : Expr)
    (ha : env.tab.bytePosOkB a = true)
    (htmp : tmp + maxTempsExpr i ≤ nt)
    (ihi : ∀ (pre post : List AsmItem) (tmp : Nat) (st : State),
      tmp + maxTempsExpr i ≤ nt →
      lkm.linkSpec (pre ++ compileE env.tab nl tmp i ++ post) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → st.getReg AbiReg.sp = sp →
      ProgMemRel env.tab L st.mem lm → ProgFrameOk L sp st.mem nl loc →
      match _root_.L.evalE i ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i))) ∧
          st'.getReg AbiReg.a0 = v.toBitVec ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (hlink : lkm.linkSpec (pre ++ compileE env.tab nl tmp (.ld8 a i) ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp (.ld8 a i))) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOk L sp st.mem nl loc) :
    match _root_.L.evalE (.ld8 a i) ⟨lm, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp (.ld8 a i)))) ∧
        st'.getReg AbiReg.a0 = v.toBitVec ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem := by
  let ci := compileE env.tab nl tmp i
  let clen := loadMemOff .ld AbiReg.t0 AbiReg.gp AbiReg.t1 (env.tab.len8 a)
  let cbr := [Asm.bgeu AbiReg.a0 AbiReg.t0 errLabel]
  let cbase := loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base8 a)
  let ctail := [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.a0, Asm.lbu AbiReg.a0 AbiReg.t1 0#12]
  have hce : compileE env.tab nl tmp (.ld8 a i) = ci ++ clen ++ cbr ++ cbase ++ ctail := by
    simp only [compileE, ci, clen, cbr, cbase, ctail, List.append_assoc]
  have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.ld8 a i)) =
      lkm.totalSize (compileE env.tab nl tmp i) + lkm.totalSize clen + lkm.totalSize cbr + lkm.totalSize cbase + 2 := by
    rw [hce]; dsimp only [ci, ctail]; simp only [lkm.totalSize_append, lkm.totalSize_cons, lkm.totalSize_nil, Asm.add, Asm.lbu, lkm.itemSize_instr]
  have hlistI : pre ++ ci ++ ((clen ++ cbr ++ cbase ++ ctail) ++ post) =
      pre ++ compileE env.tab nl tmp (.ld8 a i) ++ post := by
    rw [hce]; simp only [List.append_assoc]
  have ri := ihi pre ((clen ++ cbr ++ cbase ++ ctail) ++ post) tmp st htmp
    (by rw [hlistI]; exact hlink) (by rw [htw_ce] at h64; omega) hpc hgp hsp hmemRel hframeOk
  rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
  · simp only [hvi] at ri
    obtain ⟨ki, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ri
    have hf : (frameSpan sp nl nt).valid := by
      simp only [frameSpan, MemSpan.valid]; have := L.hStackValid; omega
    have hrel1 := ProgMemRel.of_tempSpan env hlo hhi (by omega) heq1 hmemRel
    rcases hrel1.1 a ha with ⟨_, _, hlenR, hbaseR, hbytesR⟩
    have htw1 : lkm.totalSize (pre ++ ci) = lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i) :=
      lkm.totalSize_append _ _
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ci)) := by rw [htw1]; exact hpc1
    have halLen : isAligned (st1.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.len8 a)) 8 = true := by
      rw [hpres1.gp.trans hgp, Tab.len8_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    have hlistL : (pre ++ ci) ++ clen ++ ((cbr ++ cbase ++ ctail) ++ post) =
        pre ++ compileE env.tab nl tmp (.ld8 a i) ++ post := by
      rw [hce]; simp only [List.append_assoc]
    obtain ⟨st2, hrun2, hoth2, ht0_2, hmem2, hpc2⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom (pre ++ ci) ((cbr ++ cbase ++ ctail) ++ post)
        AbiReg.t0 AbiReg.gp AbiReg.t1 (by decide) (by decide) (by decide)
        (env.tab.len8 a) (by rw [hlistL]; exact hlink)
        (by rw [htw1]; rw [htw_ce] at h64; dsimp only [clen] at h64 ⊢; omega)
        st1 hpc1' halLen
    have hpres2 : PreservedRegs st1 st2 :=
      ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
       hoth2 _ (by decide) (by decide),
       hoth2 _ (by decide) (by decide)⟩
    have ha0_2 : st2.getReg AbiReg.a0 = vi.toBitVec := by
      rw [hoth2 AbiReg.a0 (by decide) (by decide), ha0_1]
    have ht0_2' : st2.getReg AbiReg.t0 = BitVec.ofNat 64 (lm.arr8 a).size := by
      rw [ht0_2, hpres1.gp.trans hgp, hlenR]
    have htw2 : lkm.totalSize (pre ++ ci ++ clen) =
        lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i) + lkm.totalSize clen := by
      rw [lkm.totalSize_append, htw1]
    have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ci ++ clen)) := by
      rw [htw2, ← htw1]; exact hpc2
    have hlistB : (pre ++ ci ++ clen) ++ [.br .bgeu AbiReg.a0 AbiReg.t0 errLabel] ++
        ((cbase ++ ctail) ++ post) = pre ++ compileE env.tab nl tmp (.ld8 a i) ++ post := by
      rw [hce]; simp only [cbr, Asm.bgeu, List.append_assoc]
    have hlt64 : (lm.arr8 a).size < 2 ^ 64 := (hrel1.1 a ha).2.1
    have h64Br : 4 * (lkm.totalSize (pre ++ ci ++ clen) + lkm.itemSize (.br .bgeu AbiReg.a0 AbiReg.t0 errLabel)) < 2 ^ 64 := by
      rw [htw2]; rw [htw_ce] at h64
      have hbrsz : lkm.itemSize (.br .bgeu AbiReg.a0 AbiReg.t0 errLabel) = lkm.totalSize cbr := by
        simp [cbr, Asm.bgeu, lkm.totalSize_singleton]
      omega
    by_cases hbound : vi.toNat < (lm.arr8 a).size
    · have hevalE : _root_.L.evalE (.ld8 a i) ⟨lm, loc⟩ = .ok ((lm.arr8 a)[vi.toNat].toUInt64, ⟨lm, loc⟩) := by
        change (_root_.L.evalE i >>= fun idx => _root_.L.ld8 a idx) ⟨lm, loc⟩ = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hvi]
        dsimp only [_root_.L.ld8, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
          Pure.pure, StateT.pure, Except.pure, Except.bind]
        simp [hbound]; rfl
      rw [hevalE]
      have hcondF : evalBranch .bgeu (st2.getReg AbiReg.a0) (st2.getReg AbiReg.t0) = false := by
        simp [evalBranch, ha0_2, ht0_2']
        rw [BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
            Nat.mod_eq_of_lt hlt64, decide_eq_true hbound]
      obtain ⟨kBr, st3, hrun3, hpc3', hoth3, hpres3, hmem3⟩ :=
        prog_step_br_fall env (pre ++ ci ++ clen) ((cbase ++ ctail) ++ post)
          .bgeu AbiReg.a0 AbiReg.t0 errLabel env.errTarget env.herrLbl (by decide)
          (by rw [hlistB]; exact hlink) h64Br st2 hpc2' hcondF
      have htw3 : lkm.totalSize (pre ++ ci ++ clen ++ cbr) =
          lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i) + lkm.totalSize clen + lkm.totalSize cbr := by
        rw [lkm.totalSize_append, htw2]
      have hpc3 : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ci ++ clen ++ cbr)) := by
        rw [hpc3', htw3, htw2, show cbr = [.br .bgeu AbiReg.a0 AbiReg.t0 errLabel] from rfl]
      have hlistBase : (pre ++ ci ++ clen ++ cbr) ++ cbase ++ (ctail ++ post) =
          pre ++ compileE env.tab nl tmp (.ld8 a i) ++ post := by
        rw [hce]; simp only [List.append_assoc]
      have halBase : isAligned (st3.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.base8 a)) 8 = true := by
        rw [hoth3 _ (by decide), hpres2.gp.trans (hpres1.gp.trans hgp), Tab.base8_eq_nat]
        exact isAligned8_add_int_mul8 L.T L.hTAlign _
      obtain ⟨st4, hrun4, hoth4, ht1_4, hmem4, hpc4⟩ :=
        loadMemOff_ld_correct_lm lkm env.hrom (pre ++ ci ++ clen ++ cbr) (ctail ++ post)
          AbiReg.t1 AbiReg.gp AbiReg.t2 (by decide) (by decide) (by decide)
          (env.tab.base8 a) (by rw [hlistBase]; exact hlink)
          (by rw [htw3]; rw [htw_ce] at h64; dsimp only [cbase] at h64 ⊢; omega)
          st3 hpc3 halBase
      have hpres4 : PreservedRegs st3 st4 :=
        ⟨hoth4 _ (by decide) (by decide), hoth4 _ (by decide) (by decide),
         hoth4 _ (by decide) (by decide),
         hoth4 _ (by decide) (by decide)⟩
      have htw4 : lkm.totalSize (pre ++ ci ++ clen ++ cbr ++ cbase) =
          lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i) + lkm.totalSize clen + lkm.totalSize cbr + lkm.totalSize cbase := by
        rw [lkm.totalSize_append, htw3]
      have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ci ++ clen ++ cbr ++ cbase)) := by
        rw [htw4, ← htw3]; exact hpc4
      have hlistAdd : (pre ++ ci ++ clen ++ cbr ++ cbase) ++ [AsmItem.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.a0)] ++
          ([Asm.lbu AbiReg.a0 AbiReg.t1 0#12] ++ post) =
          pre ++ compileE env.tab nl tmp (.ld8 a i) ++ post := by
        rw [hce]; simp only [ctail, Asm.add, List.append_assoc, List.cons_append, List.nil_append]
      have hsAdd := step_item_instr_lm lkm env.hrom (pre ++ ci ++ clen ++ cbr ++ cbase)
        ([Asm.lbu AbiReg.a0 AbiReg.t1 0#12] ++ post) (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.a0)
        (by rw [hlistAdd]; exact hlink)
        (by rw [htw4]; rw [htw_ce] at h64; omega) st4 hpc4'
      let st5 := stepReg st4 AbiReg.t1 (st4.getReg AbiReg.t1 + st4.getReg AbiReg.a0) (st4.pc + 4#64)
      have hpres5 : PreservedRegs st4 st5 :=
        ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _⟩
      have htw5 : lkm.totalSize (pre ++ ci ++ clen ++ cbr ++ cbase ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.a0]) =
          lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i) + lkm.totalSize clen + lkm.totalSize cbr + lkm.totalSize cbase + 1 := by
        rw [lkm.totalSize_append, htw4, Asm.add, lkm.totalSize_instr]
      have hpc5 : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ci ++ clen ++ cbr ++ cbase ++
          [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.a0])) := by
        change st4.pc + 4#64 = _; rw [pc_add_4_ofNat st4.pc hpc4', htw5, htw4]
      have hlistLbu : (pre ++ ci ++ clen ++ cbr ++ cbase ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.a0]) ++
          [Asm.lbu AbiReg.a0 AbiReg.t1 0#12] ++ post =
          pre ++ compileE env.tab nl tmp (.ld8 a i) ++ post := by
        rw [hce]; simp only [ctail, List.append_assoc, List.cons_append, List.nil_append]
      let st6 := stepReg st5 AbiReg.a0
        ((loadBytes st5.mem (st5.getReg AbiReg.t1 + sextImm12 0#12) 1).zeroExtend 64) (st5.pc + 4#64)
      obtain ⟨hrun6, hpc6, ha0_6, hoth6, hmem6⟩ :=
        step_lbu_off env (pre ++ ci ++ clen ++ cbr ++ cbase ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.a0]) post
          AbiReg.a0 AbiReg.t1 0#12 (by decide) (by rw [hlistLbu]; exact hlink)
          (by rw [htw5]; rw [htw_ce] at h64; omega) st5 hpc5
      have hpres6 : PreservedRegs st5 st6 :=
        ⟨hoth6 _ (by decide), hoth6 _ (by decide), hoth6 _ (by decide), hoth6 _ (by decide)⟩
      have ht1_5 : st5.getReg AbiReg.t1 = L.base8 a + BitVec.ofNat 64 vi.toNat := by
        have ht1' : st4.getReg AbiReg.t1 = L.base8 a := by
          rw [ht1_4]; change readWord64 st3.mem (st3.getReg AbiReg.gp + _) = _
          rw [hmem3, hoth3 _ (by decide), hpres2.gp.trans (hpres1.gp.trans hgp), hmem2, hbaseR]
        have ha0' : st4.getReg AbiReg.a0 = BitVec.ofNat 64 vi.toNat := by
          rw [hoth4 AbiReg.a0 (by decide) (by decide), hoth3 _ (by decide), ha0_2]
          apply BitVec.eq_of_toNat_eq; simp [UInt64.toNat_toBitVec]
        change (stepReg st4 AbiReg.t1 _ _).getReg AbiReg.t1 = _
        rw [getReg_stepReg_eq _ _ (by decide), ht1', ha0']
      have ha0_6' : st6.getReg AbiReg.a0 = (lm.arr8 a)[vi.toNat].toUInt64.toBitVec := by
        rw [ha0_6]
        have hmem5 : st5.mem = st1.mem := by
          dsimp only [st5]; rw [prog_stepReg_mem, hmem4, hmem3, hmem2]
        rw [hmem5, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero, ht1_5, ← loadBytes_one]
        exact loadBytes_one_uint8 _ _ _ (hbytesR vi.toNat hbound)
      refine ⟨ki + (lkm.totalSize clen + (kBr + (lkm.totalSize cbase + (1 + 1)))), st6, ?_, ?_, ha0_6',
        (hpres1.trans (hpres2.trans hpres3)).trans (hpres4.trans (hpres5.trans hpres6)), ?_⟩
      · rw [run_add, hrun1]; dsimp only
        rw [run_add, hrun2]; dsimp only
        rw [run_add, hrun3]; dsimp only
        rw [run_add, hrun4]; dsimp only
        rw [run_add, run_one_cont _ _ st5 (by rw [hsAdd]; rfl)]; dsimp only
        exact hrun6
      · rw [hpc6, htw5, htw_ce]; congr 2; omega
      · have hm : st6.mem = st1.mem := by
          rw [hmem6]; dsimp only [st5]; rw [prog_stepReg_mem, hmem4, hmem3, hmem2]
        rw [hm]; exact heq1
    · have hevalE : _root_.L.evalE (.ld8 a i) ⟨lm, loc⟩ = .error .oob := by
        change (_root_.L.evalE i >>= fun idx => _root_.L.ld8 a idx) ⟨lm, loc⟩ = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hvi]
        dsimp only [_root_.L.ld8, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
          Pure.pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.pure, Except.bind]
        simp [hbound]; rfl
      rw [hevalE]
      have hge : (lm.arr8 a).size ≤ vi.toNat := by omega
      have hcondT : evalBranch .bgeu (st2.getReg AbiReg.a0) (st2.getReg AbiReg.t0) = true := by
        simp [evalBranch, ha0_2, ht0_2']
        rw [BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec, Nat.mod_eq_of_lt hlt64,
            decide_eq_false (by omega)]
      obtain ⟨kBr, st3, hrun3, hpc3', _, hpres3, hmem3⟩ :=
        prog_step_br_taken env (pre ++ ci ++ clen) ((cbase ++ ctail) ++ post)
          .bgeu AbiReg.a0 AbiReg.t0 errLabel env.errTarget env.herrLbl (by decide)
          (by rw [hlistB]; exact hlink) h64Br st2 hpc2' hcondT
      refine ⟨ki + (lkm.totalSize clen + kBr), st3, ?_, hpc3',
        hpres1.trans (hpres2.trans hpres3), ?_⟩
      · rw [run_add, hrun1]; dsimp only
        rw [run_add, hrun2]; dsimp only
        exact hrun3
      · rw [hmem3, hmem2]; exact heq1
  · simp only [hvi] at ri
    have hevalE : _root_.L.evalE (.ld8 a i) ⟨lm, loc⟩ = .error .oob := by
      simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hvi]
    rw [hevalE]; exact ri

theorem prog_ld64_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (lm : _root_.L.Mem) (loc : _root_.L.Locals)
    {sp : BitVec 64} {nl nt : Nat}
    (pre post : List AsmItem) (tmp : Nat) (a : ArrId) (i : Expr)
    (ha : env.tab.wordPosOkB (TieredArray.t0 a) = true)
    (htmp : tmp + maxTempsExpr i ≤ nt)
    (ihi : ∀ (pre post : List AsmItem) (tmp : Nat) (st : State),
      tmp + maxTempsExpr i ≤ nt →
      lkm.linkSpec (pre ++ compileE env.tab nl tmp i ++ post) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → st.getReg AbiReg.sp = sp →
      ProgMemRel env.tab L st.mem lm → ProgFrameOk L sp st.mem nl loc →
      match _root_.L.evalE i ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i))) ∧
          st'.getReg AbiReg.a0 = v.toBitVec ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (hlink : lkm.linkSpec (pre ++ compileE env.tab nl tmp (.ld64 a i) ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp (.ld64 a i))) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOk L sp st.mem nl loc) :
    match _root_.L.evalE (.ld64 a i) ⟨lm, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp (.ld64 a i)))) ∧
        st'.getReg AbiReg.a0 = v.toBitVec ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem := by
  let ci := compileE env.tab nl tmp i
  let clen := loadMemOff .ld AbiReg.t0 AbiReg.gp AbiReg.t1 (env.tab.len64 (TieredArray.t0 a))
  let cbr := [Asm.bgeu AbiReg.a0 AbiReg.t0 errLabel]
  let cbase := loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base64 (TieredArray.t0 a))
  let ctail := [Asm.slli AbiReg.t2 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2,
                Asm.ld AbiReg.a0 AbiReg.t1 0#12]
  have hce : compileE env.tab nl tmp (.ld64 a i) = ci ++ clen ++ cbr ++ cbase ++ ctail := by
    simp only [compileE, ci, clen, cbr, cbase, ctail, List.append_assoc]
  have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.ld64 a i)) =
      lkm.totalSize (compileE env.tab nl tmp i) + lkm.totalSize clen + lkm.totalSize cbr + lkm.totalSize cbase + 3 := by
    rw [hce]; dsimp only [ci, ctail]; simp only [lkm.totalSize_append, lkm.totalSize_cons, lkm.totalSize_nil, Asm.slli, Asm.add, Asm.ld, lkm.itemSize_instr]
  have hlistI : pre ++ ci ++ ((clen ++ cbr ++ cbase ++ ctail) ++ post) =
      pre ++ compileE env.tab nl tmp (.ld64 a i) ++ post := by
    rw [hce]; simp only [List.append_assoc]
  have ri := ihi pre ((clen ++ cbr ++ cbase ++ ctail) ++ post) tmp st htmp
    (by rw [hlistI]; exact hlink) (by rw [htw_ce] at h64; omega) hpc hgp hsp hmemRel hframeOk
  rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
  · simp only [hvi] at ri
    obtain ⟨ki, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ri
    have hrel1 := ProgMemRel.of_tempSpan env hlo hhi (by omega) heq1 hmemRel
    rcases hrel1.2.1 (TieredArray.t0 a) ha with ⟨_, hlt61, hlenR, hbaseR, hwordsR⟩
    have htw1 : lkm.totalSize (pre ++ ci) = lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i) :=
      lkm.totalSize_append _ _
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ci)) := by rw [htw1]; exact hpc1
    have halLen : isAligned (st1.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.len64 (TieredArray.t0 a))) 8 = true := by
      rw [hpres1.gp.trans hgp, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    have hlistL : (pre ++ ci) ++ clen ++ ((cbr ++ cbase ++ ctail) ++ post) =
        pre ++ compileE env.tab nl tmp (.ld64 a i) ++ post := by
      rw [hce]; simp only [List.append_assoc]
    obtain ⟨st2, hrun2, hoth2, ht0_2, hmem2, hpc2⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom (pre ++ ci) ((cbr ++ cbase ++ ctail) ++ post)
        AbiReg.t0 AbiReg.gp AbiReg.t1 (by decide) (by decide) (by decide)
        (env.tab.len64 (TieredArray.t0 a)) (by rw [hlistL]; exact hlink)
        (by rw [htw1]; rw [htw_ce] at h64; dsimp only [clen] at h64 ⊢; omega) st1 hpc1' halLen
    have hpres2 : PreservedRegs st1 st2 :=
      ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
       hoth2 _ (by decide) (by decide),
       hoth2 _ (by decide) (by decide)⟩
    have ha0_2 : st2.getReg AbiReg.a0 = vi.toBitVec := by
      rw [hoth2 AbiReg.a0 (by decide) (by decide), ha0_1]
    have ht0_2' : st2.getReg AbiReg.t0 = BitVec.ofNat 64 (lm.arr64 (TieredArray.t0 a)).size := by
      rw [ht0_2, hpres1.gp.trans hgp, hlenR]
    have htw2 : lkm.totalSize (pre ++ ci ++ clen) =
        lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i) + lkm.totalSize clen := by
      rw [lkm.totalSize_append, htw1]
    have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ci ++ clen)) := by
      rw [htw2, ← htw1]; exact hpc2
    have hlistB : (pre ++ ci ++ clen) ++ [.br .bgeu AbiReg.a0 AbiReg.t0 errLabel] ++
        ((cbase ++ ctail) ++ post) = pre ++ compileE env.tab nl tmp (.ld64 a i) ++ post := by
      rw [hce]; simp only [cbr, Asm.bgeu, List.append_assoc]
    have h64Br : 4 * (lkm.totalSize (pre ++ ci ++ clen) + lkm.itemSize (.br .bgeu AbiReg.a0 AbiReg.t0 errLabel)) < 2 ^ 64 := by
      rw [htw2]; rw [htw_ce] at h64
      have hbrsz : lkm.itemSize (.br .bgeu AbiReg.a0 AbiReg.t0 errLabel) = lkm.totalSize cbr := by
        simp [cbr, Asm.bgeu, lkm.totalSize_singleton]
      omega
    by_cases hbound : vi.toNat < (lm.arr64 (TieredArray.t0 a)).size
    · have hevalE : _root_.L.evalE (.ld64 a i) ⟨lm, loc⟩ =
          .ok ((lm.arr64 (TieredArray.t0 a))[vi.toNat], ⟨lm, loc⟩) := by
        change (_root_.L.evalE i >>= fun idx => _root_.L.ld64 (TieredArray.t0 a) idx) ⟨lm, loc⟩ = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hvi]
        dsimp only [_root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
          Pure.pure, StateT.pure, Except.pure, Except.bind]
        simp [hbound]; rfl
      rw [hevalE]
      have hcondF : evalBranch .bgeu (st2.getReg AbiReg.a0) (st2.getReg AbiReg.t0) = false := by
        simp only [evalBranch, ha0_2, ht0_2', BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
          Nat.mod_eq_of_lt (by omega : (lm.arr64 (TieredArray.t0 a)).size < 2 ^ 64),
          decide_eq_true hbound]
        rfl
      obtain ⟨kBr, st3, hrun3, hpc3', hoth3, hpres3, hmem3⟩ :=
        prog_step_br_fall env (pre ++ ci ++ clen) ((cbase ++ ctail) ++ post)
          .bgeu AbiReg.a0 AbiReg.t0 errLabel env.errTarget env.herrLbl (by decide)
          (by rw [hlistB]; exact hlink) h64Br st2 hpc2' hcondF
      have htw3 : lkm.totalSize (pre ++ ci ++ clen ++ cbr) =
          lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i) + lkm.totalSize clen + lkm.totalSize cbr := by
        rw [lkm.totalSize_append, htw2]
      have hpc3 : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ci ++ clen ++ cbr)) := by
        rw [hpc3', htw3, htw2, show cbr = [.br .bgeu AbiReg.a0 AbiReg.t0 errLabel] from rfl]
      have hlistBase : (pre ++ ci ++ clen ++ cbr) ++ cbase ++ (ctail ++ post) =
          pre ++ compileE env.tab nl tmp (.ld64 a i) ++ post := by
        rw [hce]; simp only [List.append_assoc]
      have halBase : isAligned (st3.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.base64 (TieredArray.t0 a))) 8 = true := by
        rw [hoth3 _ (by decide), hpres2.gp.trans (hpres1.gp.trans hgp), Tab.base64_eq_nat]
        exact isAligned8_add_int_mul8 L.T L.hTAlign _
      obtain ⟨st4, hrun4, hoth4, ht1_4, hmem4, hpc4⟩ :=
        loadMemOff_ld_correct_lm lkm env.hrom (pre ++ ci ++ clen ++ cbr) (ctail ++ post)
          AbiReg.t1 AbiReg.gp AbiReg.t2 (by decide) (by decide) (by decide)
          (env.tab.base64 (TieredArray.t0 a)) (by rw [hlistBase]; exact hlink)
          (by rw [htw3]; rw [htw_ce] at h64; dsimp only [clen, cbase] at h64 ⊢; omega) st3 hpc3 halBase
      have hpres4 : PreservedRegs st3 st4 :=
        ⟨hoth4 _ (by decide) (by decide), hoth4 _ (by decide) (by decide),
         hoth4 _ (by decide) (by decide),
         hoth4 _ (by decide) (by decide)⟩
      have htw4 : lkm.totalSize (pre ++ ci ++ clen ++ cbr ++ cbase) =
          lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i) + lkm.totalSize clen + lkm.totalSize cbr + lkm.totalSize cbase := by
        rw [lkm.totalSize_append, htw3]
      have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ci ++ clen ++ cbr ++ cbase)) := by
        rw [htw4, ← htw3]; exact hpc4
      let p4 := pre ++ ci ++ clen ++ cbr ++ cbase
      have hsSll := step_item_instr_lm lkm env.hrom p4
        ([Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2, Asm.ld AbiReg.a0 AbiReg.t1 0#12] ++ post)
        (.shImm .slli AbiReg.t2 AbiReg.a0 3#6)
        (by rw [show p4 ++ [AsmItem.instr (.shImm .slli AbiReg.t2 AbiReg.a0 3#6)] ++
            ([Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2, Asm.ld AbiReg.a0 AbiReg.t1 0#12] ++ post) =
            pre ++ compileE env.tab nl tmp (.ld64 a i) ++ post from by
            rw [hce]; simp only [p4, ctail, Asm.slli, List.append_assoc, List.cons_append, List.nil_append]]; exact hlink)
        (by rw [htw4]; rw [htw_ce] at h64; dsimp only [clen, cbase] at h64 ⊢; omega) st4 hpc4'
      let st5 := stepReg st4 AbiReg.t2 (st4.getReg AbiReg.a0 <<< 3) (st4.pc + 4#64)
      have hpres5 : PreservedRegs st4 st5 :=
        ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _⟩
      have htw5 : lkm.totalSize (p4 ++ [Asm.slli AbiReg.t2 AbiReg.a0 3#6]) = lkm.totalSize p4 + 1 := by
        rw [lkm.totalSize_append, Asm.slli, lkm.totalSize_instr]
      have hpc5 : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p4 ++ [Asm.slli AbiReg.t2 AbiReg.a0 3#6])) := by
        change st4.pc + 4#64 = _; rw [pc_add_4_ofNat st4.pc hpc4', htw5]
      have hsAdd := step_item_instr_lm lkm env.hrom (p4 ++ [Asm.slli AbiReg.t2 AbiReg.a0 3#6])
        ([Asm.ld AbiReg.a0 AbiReg.t1 0#12] ++ post) (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.t2)
        (by rw [show (p4 ++ [Asm.slli AbiReg.t2 AbiReg.a0 3#6]) ++ [AsmItem.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.t2)] ++
            ([Asm.ld AbiReg.a0 AbiReg.t1 0#12] ++ post) =
            pre ++ compileE env.tab nl tmp (.ld64 a i) ++ post from by
            rw [hce]; simp only [p4, ctail, Asm.add, List.append_assoc, List.cons_append, List.nil_append]]; exact hlink)
        (by rw [htw5, htw4]; rw [htw_ce] at h64; dsimp only [clen, cbase] at h64 ⊢; omega) st5 hpc5
      let st6 := stepReg st5 AbiReg.t1 (st5.getReg AbiReg.t1 + st5.getReg AbiReg.t2) (st5.pc + 4#64)
      have hpres6 : PreservedRegs st5 st6 :=
        ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _⟩
      have htw6 : lkm.totalSize (p4 ++ [Asm.slli AbiReg.t2 AbiReg.a0 3#6] ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2]) =
          lkm.totalSize p4 + 2 := by
        rw [lkm.totalSize_append, htw5, Asm.add, lkm.totalSize_instr]
      have hpc6 : st6.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p4 ++ [Asm.slli AbiReg.t2 AbiReg.a0 3#6] ++
          [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2])) := by
        change st5.pc + 4#64 = _; rw [pc_add_4_ofNat st5.pc hpc5, htw6, htw5]
      have hsLd := step_item_instr_lm lkm env.hrom
        (p4 ++ [Asm.slli AbiReg.t2 AbiReg.a0 3#6] ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2])
        post (.load .ld AbiReg.a0 AbiReg.t1 0#12)
        (by rw [show (p4 ++ [Asm.slli AbiReg.t2 AbiReg.a0 3#6] ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2]) ++
            [AsmItem.instr (.load .ld AbiReg.a0 AbiReg.t1 0#12)] ++ post =
            pre ++ compileE env.tab nl tmp (.ld64 a i) ++ post from by
            rw [hce]; simp only [p4, ctail, Asm.ld, List.append_assoc, List.cons_append, List.nil_append]]; exact hlink)
        (by rw [htw6, htw4]; rw [htw_ce] at h64; dsimp only [clen, cbase] at h64 ⊢; omega) st6 hpc6
      have ht1_6 : st6.getReg AbiReg.t1 = L.base64 (TieredArray.t0 a) + BitVec.ofNat 64 (8 * vi.toNat) := by
        have ht1' : st4.getReg AbiReg.t1 = L.base64 (TieredArray.t0 a) := by
          rw [ht1_4]; change readWord64 st3.mem (st3.getReg AbiReg.gp + _) = _
          rw [hmem3, hoth3 _ (by decide), hpres2.gp.trans (hpres1.gp.trans hgp), hmem2, hbaseR]
        have ha0' : st4.getReg AbiReg.a0 = vi.toBitVec := by
          rw [hoth4 AbiReg.a0 (by decide) (by decide), hoth3 _ (by decide)]; rw [ha0_2]
        have ht2' : st5.getReg AbiReg.t2 = BitVec.ofNat 64 (8 * vi.toNat) := by
          change (stepReg st4 AbiReg.t2 _ _).getReg AbiReg.t2 = _
          rw [getReg_stepReg_eq _ _ (by decide), ha0']
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_shiftLeft, UInt64.toNat_toBitVec, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
          rw [show (2 ^ 3 : Nat) = 8 from rfl, Nat.mul_comm _ 8]
        change (stepReg st5 AbiReg.t1 _ _).getReg AbiReg.t1 = _
        rw [getReg_stepReg_eq _ _ (by decide)]
        have ht1_5 : st5.getReg AbiReg.t1 = st4.getReg AbiReg.t1 :=
          getReg_stepReg_ne st4 AbiReg.t2 AbiReg.t1 (by decide) _ _
        rw [ht1_5, ht1', ht2']
      have hal6 : isAligned (st6.getReg AbiReg.t1 + sextImm12 0#12) 8 = true := by
        rw [show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero, ht1_6]
        exact isAligned8_add_mul8 (L.base64 (TieredArray.t0 a)) (L.h64Align (TieredArray.t0 a)) vi.toNat
      let st7 := stepReg st6 AbiReg.a0 (loadBytes st6.mem (st6.getReg AbiReg.t1 + sextImm12 0#12) 8) (st6.pc + 4#64)
      have hpres7 : PreservedRegs st6 st7 :=
        ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _⟩
      have hmem7 : st7.mem = st1.mem := by
        dsimp only [st7, st6, st5]
        rw [prog_stepReg_mem, prog_stepReg_mem, prog_stepReg_mem, hmem4, hmem3, hmem2]
      refine ⟨ki + (lkm.totalSize clen + (kBr + (lkm.totalSize cbase + (1 + (1 + 1))))), st7, ?_, ?_, ?_,
        (hpres1.trans (hpres2.trans hpres3)).trans (hpres4.trans (hpres5.trans (hpres6.trans hpres7))), ?_⟩
      · rw [run_add, hrun1]; dsimp only
        rw [run_add, hrun2]; dsimp only
        rw [run_add, hrun3]; dsimp only
        rw [run_add, hrun4]; dsimp only
        rw [run_add, run_one_cont _ _ st5 (by rw [hsSll]; rfl)]; dsimp only
        rw [run_add, run_one_cont _ _ st6 (by rw [hsAdd]; rfl)]; dsimp only
        exact run_one_cont _ _ st7 (by rw [hsLd]; simp only [execInstr, hal6]; rfl)
      · change st6.pc + 4#64 = _
        rw [pc_add_4_ofNat st6.pc hpc6, htw6, htw4, htw_ce]; congr 2; omega
      · change (stepReg st6 AbiReg.a0 _ _).getReg AbiReg.a0 = _
        rw [getReg_stepReg_eq _ _ (by decide), show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero, ht1_6]
        have hm6 : st6.mem = st1.mem := by
          dsimp only [st6, st5]; rw [prog_stepReg_mem, prog_stepReg_mem, hmem4, hmem3, hmem2]
        rw [hm6]; exact hwordsR vi.toNat hbound
      · rw [hmem7]; exact heq1
    · have hevalE : _root_.L.evalE (.ld64 a i) ⟨lm, loc⟩ = .error .oob := by
        change (_root_.L.evalE i >>= fun idx => _root_.L.ld64 (TieredArray.t0 a) idx) ⟨lm, loc⟩ = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hvi]
        dsimp only [_root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
          Pure.pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.pure, Except.bind]
        simp [hbound]; rfl
      rw [hevalE]
      have hcondT : evalBranch .bgeu (st2.getReg AbiReg.a0) (st2.getReg AbiReg.t0) = true := by
        simp [evalBranch, ha0_2, ht0_2']
        rw [BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
            Nat.mod_eq_of_lt (by omega : (lm.arr64 (TieredArray.t0 a)).size < 2 ^ 64),
            decide_eq_false (by omega)]
      obtain ⟨kBr, st3, hrun3, hpc3', _, hpres3, hmem3⟩ :=
        prog_step_br_taken env (pre ++ ci ++ clen) ((cbase ++ ctail) ++ post)
          .bgeu AbiReg.a0 AbiReg.t0 errLabel env.errTarget env.herrLbl (by decide)
          (by rw [hlistB]; exact hlink) h64Br st2 hpc2' hcondT
      refine ⟨ki + (lkm.totalSize clen + kBr), st3, ?_, hpc3',
        hpres1.trans (hpres2.trans hpres3), ?_⟩
      · rw [run_add, hrun1]; dsimp only
        rw [run_add, hrun2]; dsimp only
        exact hrun3
      · rw [hmem3, hmem2]; exact heq1
  · simp only [hvi] at ri
    have hevalE : _root_.L.evalE (.ld64 a i) ⟨lm, loc⟩ = .error .oob := by
      simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hvi]
    rw [hevalE]; exact ri

theorem prog_ldc_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (lm : _root_.L.Mem) (loc : _root_.L.Locals)
    {sp : BitVec 64} {nl nt : Nat}
    (pre post : List AsmItem) (tmp : Nat) (d : List UInt8) (i : Expr)
    (hd : env.tab.romSliceOkB d = true)
    (htmp : tmp + maxTempsExpr i ≤ nt)
    (ihi : ∀ (pre post : List AsmItem) (tmp : Nat) (st : State),
      tmp + maxTempsExpr i ≤ nt →
      lkm.linkSpec (pre ++ compileE env.tab nl tmp i ++ post) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → st.getReg AbiReg.sp = sp →
      ProgMemRel env.tab L st.mem lm → ProgFrameOk L sp st.mem nl loc →
      match _root_.L.evalE i ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i))) ∧
          st'.getReg AbiReg.a0 = v.toBitVec ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (hlink : lkm.linkSpec (pre ++ compileE env.tab nl tmp (.ldc d i) ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp (.ldc d i))) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOk L sp st.mem nl loc) :
    match _root_.L.evalE (.ldc d i) ⟨lm, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp (.ldc d i)))) ∧
        st'.getReg AbiReg.a0 = v.toBitVec ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem := by
  let ci := compileE env.tab nl tmp i
  let clen := li AbiReg.t0 (BitVec.ofNat 64 d.length)
  let cbr := [Asm.bgeu AbiReg.a0 AbiReg.t0 errLabel]
  let cbase := addImmOff AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.romBase + (romIdx d env.tab.rom : Int))
  let ctail := [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.a0, Asm.lbu AbiReg.a0 AbiReg.t1 0#12]
  have hce : compileE env.tab nl tmp (.ldc d i) = ci ++ clen ++ cbr ++ cbase ++ ctail := by
    simp only [compileE, ci, clen, cbr, cbase, ctail, List.append_assoc]
  have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.ldc d i)) =
      lkm.totalSize (compileE env.tab nl tmp i) + lkm.totalSize clen + lkm.totalSize cbr + lkm.totalSize cbase + 2 := by
    rw [hce]; dsimp only [ci, ctail]; simp only [lkm.totalSize_append, lkm.totalSize_cons, lkm.totalSize_nil, Asm.add, Asm.lbu, lkm.itemSize_instr]
  have hlistI : pre ++ ci ++ ((clen ++ cbr ++ cbase ++ ctail) ++ post) =
      pre ++ compileE env.tab nl tmp (.ldc d i) ++ post := by
    rw [hce]; simp only [List.append_assoc]
  have ri := ihi pre ((clen ++ cbr ++ cbase ++ ctail) ++ post) tmp st htmp
    (by rw [hlistI]; exact hlink) (by rw [htw_ce] at h64; omega) hpc hgp hsp hmemRel hframeOk
  rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
  · simp only [hvi] at ri
    obtain ⟨ki, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ri
    have hrel1 := ProgMemRel.of_tempSpan env hlo hhi (by omega) heq1 hmemRel
    have hromSpec := Tab.romSliceOk_spec hd
    have hrb := L.tab_rom_bound
    have hvT := L.hTValid
    have hdlt : d.length < 2 ^ 64 := by
      have hrb16 : 16 ≤ env.tab.romBase.toNat := by simp [Tab.romBase]; omega
      omega
    have htw1 : lkm.totalSize (pre ++ ci) = lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i) :=
      lkm.totalSize_append _ _
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ci)) := by rw [htw1]; exact hpc1
    have hlistL : (pre ++ ci) ++ clen ++ ((cbr ++ cbase ++ ctail) ++ post) =
        pre ++ compileE env.tab nl tmp (.ldc d i) ++ post := by
      rw [hce]; simp only [List.append_assoc]
    obtain ⟨st2, hrun2, hoth2, ht0_2, hmem2, hpc2⟩ :=
      li_correct_lm lkm env.hrom (pre ++ ci) ((cbr ++ cbase ++ ctail) ++ post) AbiReg.t0 (by decide)
        (BitVec.ofNat 64 d.length) (by rw [hlistL]; exact hlink)
        (by rw [htw1]; rw [htw_ce] at h64; dsimp only [clen] at h64 ⊢; omega) st1 hpc1'
    have hpres2 : PreservedRegs st1 st2 :=
      ⟨hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide)⟩
    have ha0_2 : st2.getReg AbiReg.a0 = vi.toBitVec := by
      rw [hoth2 AbiReg.a0 (by decide), ha0_1]
    have htw2 : lkm.totalSize (pre ++ ci ++ clen) =
        lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i) + lkm.totalSize clen := by
      rw [lkm.totalSize_append, htw1]
    have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ci ++ clen)) := by
      rw [htw2, ← htw1]; exact hpc2
    have hlistB : (pre ++ ci ++ clen) ++ [.br .bgeu AbiReg.a0 AbiReg.t0 errLabel] ++
        ((cbase ++ ctail) ++ post) = pre ++ compileE env.tab nl tmp (.ldc d i) ++ post := by
      rw [hce]; simp only [cbr, Asm.bgeu, List.append_assoc]
    have h64Br : 4 * (lkm.totalSize (pre ++ ci ++ clen) + lkm.itemSize (.br .bgeu AbiReg.a0 AbiReg.t0 errLabel)) < 2 ^ 64 := by
      rw [htw2]; rw [htw_ce] at h64
      have hbrsz : lkm.itemSize (.br .bgeu AbiReg.a0 AbiReg.t0 errLabel) = lkm.totalSize cbr := by
        simp [cbr, Asm.bgeu, lkm.totalSize_singleton]
      omega
    by_cases hbound : vi.toNat < d.length
    · have hevalE : _root_.L.evalE (.ldc d i) ⟨lm, loc⟩ = .ok (d[vi.toNat].toUInt64, ⟨lm, loc⟩) := by
        change (_root_.L.evalE i >>= fun idx => _root_.L.ldc d idx) ⟨lm, loc⟩ = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hvi]
        dsimp only [_root_.L.ldc, Pure.pure, StateT.pure, Except.pure]
        simp [hbound]; rfl
      rw [hevalE]
      have hcondF : evalBranch .bgeu (st2.getReg AbiReg.a0) (st2.getReg AbiReg.t0) = false := by
        simp only [evalBranch, ha0_2, ht0_2, BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
          Nat.mod_eq_of_lt hdlt, decide_eq_true hbound]
        rfl
      obtain ⟨kBr, st3, hrun3, hpc3', hoth3, hpres3, hmem3⟩ :=
        prog_step_br_fall env (pre ++ ci ++ clen) ((cbase ++ ctail) ++ post)
          .bgeu AbiReg.a0 AbiReg.t0 errLabel env.errTarget env.herrLbl (by decide)
          (by rw [hlistB]; exact hlink) h64Br st2 hpc2' hcondF
      have htw3 : lkm.totalSize (pre ++ ci ++ clen ++ cbr) =
          lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i) + lkm.totalSize clen + lkm.totalSize cbr := by
        rw [lkm.totalSize_append, htw2]
      have hpc3 : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ci ++ clen ++ cbr)) := by
        rw [hpc3', htw3, htw2, show cbr = [.br .bgeu AbiReg.a0 AbiReg.t0 errLabel] from rfl]
      have hlistBase : (pre ++ ci ++ clen ++ cbr) ++ cbase ++ (ctail ++ post) =
          pre ++ compileE env.tab nl tmp (.ldc d i) ++ post := by
        rw [hce]; simp only [List.append_assoc]
      obtain ⟨st4, hrun4, hoth4, ht1_4, hmem4, hpc4⟩ :=
        addImmOff_correct_lm lkm env.hrom (pre ++ ci ++ clen ++ cbr) (ctail ++ post)
          AbiReg.t1 AbiReg.gp AbiReg.t2 (by decide) (by decide) (by decide)
          (env.tab.romBase + (romIdx d env.tab.rom : Int))
          (by rw [hlistBase]; exact hlink)
          (by rw [htw3]; rw [htw_ce] at h64; dsimp only [clen, cbase] at h64 ⊢; omega) st3 hpc3
      have hpres4 : PreservedRegs st3 st4 :=
        ⟨hoth4 _ (by decide) (by decide), hoth4 _ (by decide) (by decide),
         hoth4 _ (by decide) (by decide),
         hoth4 _ (by decide) (by decide)⟩
      have htw4 : lkm.totalSize (pre ++ ci ++ clen ++ cbr ++ cbase) =
          lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i) + lkm.totalSize clen + lkm.totalSize cbr + lkm.totalSize cbase := by
        rw [lkm.totalSize_append, htw3]
      have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ci ++ clen ++ cbr ++ cbase)) := by
        rw [htw4, ← htw3]; exact hpc4
      let p4 := pre ++ ci ++ clen ++ cbr ++ cbase
      have hsAdd := step_item_instr_lm lkm env.hrom p4
        ([Asm.lbu AbiReg.a0 AbiReg.t1 0#12] ++ post) (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.a0)
        (by rw [show p4 ++ [AsmItem.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.a0)] ++ ([Asm.lbu AbiReg.a0 AbiReg.t1 0#12] ++ post) =
            pre ++ compileE env.tab nl tmp (.ldc d i) ++ post from by
            rw [hce]; simp only [p4, ctail, Asm.add, List.append_assoc, List.cons_append, List.nil_append]]; exact hlink)
        (by rw [htw4]; rw [htw_ce] at h64; dsimp only [clen, cbase] at h64 ⊢; omega) st4 hpc4'
      let st5 := stepReg st4 AbiReg.t1 (st4.getReg AbiReg.t1 + st4.getReg AbiReg.a0) (st4.pc + 4#64)
      have hpres5 : PreservedRegs st4 st5 :=
        ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _⟩
      have htw5 : lkm.totalSize (p4 ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.a0]) = lkm.totalSize p4 + 1 := by
        rw [lkm.totalSize_append, Asm.add, lkm.totalSize_instr]
      have hpc5 : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p4 ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.a0])) := by
        change st4.pc + 4#64 = _; rw [pc_add_4_ofNat st4.pc hpc4', htw5]
      let st6 := stepReg st5 AbiReg.a0 ((loadBytes st5.mem (st5.getReg AbiReg.t1 + sextImm12 0#12) 1).zeroExtend 64)
        (st5.pc + 4#64)
      obtain ⟨hrun6, hpc6, ha0_6, hoth6, hmem6⟩ :=
        step_lbu_off env (p4 ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.a0]) post
          AbiReg.a0 AbiReg.t1 0#12 (by decide)
          (by rw [show (p4 ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.a0]) ++ [Asm.lbu AbiReg.a0 AbiReg.t1 0#12] ++ post =
              pre ++ compileE env.tab nl tmp (.ldc d i) ++ post from by
              rw [hce]; simp only [p4, ctail, List.append_assoc, List.cons_append, List.nil_append]]; exact hlink)
          (by rw [htw5, htw4]; rw [htw_ce] at h64; dsimp only [clen, cbase] at h64 ⊢; omega) st5 hpc5
      have hpres6 : PreservedRegs st5 st6 :=
        ⟨hoth6 _ (by decide), hoth6 _ (by decide), hoth6 _ (by decide), hoth6 _ (by decide)⟩
      have ht1_5 : st5.getReg AbiReg.t1 =
          L.T + BitVec.ofNat 64 (env.tab.romBase.toNat + (romIdx d env.tab.rom + vi.toNat)) := by
        have hrb_nn : 0 ≤ env.tab.romBase := ProgLayout.romBase_nonneg env.tab
        have hcoe : (env.tab.romBase + (romIdx d env.tab.rom : Int)) =
            ((env.tab.romBase.toNat + romIdx d env.tab.rom : Nat) : Int) := by
          rw [← Int.toNat_of_nonneg hrb_nn]; push_cast; rfl
        have ht1' : st4.getReg AbiReg.t1 =
            L.T + BitVec.ofNat 64 (env.tab.romBase.toNat + romIdx d env.tab.rom) := by
          rw [ht1_4]; change st3.getReg AbiReg.gp + _ = _
          rw [hoth3 _ (by decide), hpres2.gp.trans (hpres1.gp.trans hgp), hcoe]; rfl
        have ha0' : st4.getReg AbiReg.a0 = BitVec.ofNat 64 vi.toNat := by
          rw [hoth4 AbiReg.a0 (by decide) (by decide), hoth3 _ (by decide), ha0_2]
          apply BitVec.eq_of_toNat_eq; simp [UInt64.toNat_toBitVec]
        change (stepReg st4 AbiReg.t1 _ _).getReg AbiReg.t1 = _
        rw [getReg_stepReg_eq _ _ (by decide), ht1', ha0', BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
      have ha0_6' : st6.getReg AbiReg.a0 = d[vi.toNat].toUInt64.toBitVec := by
        rw [ha0_6]
        have hmem5 : st5.mem = st1.mem := by
          dsimp only [st5]; rw [prog_stepReg_mem, hmem4, hmem3, hmem2]
        rw [hmem5, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero, ht1_5, ← loadBytes_one]
        have hrom_eq := hromSpec.2 vi.toNat hbound
        rw [List.getElem?_eq_getElem (by omega : romIdx d env.tab.rom + vi.toNat < env.tab.rom.length),
            Option.some.injEq] at hrom_eq
        exact loadBytes_one_uint8 _ _ _ (by rw [hrel1.2.2.1 (romIdx d env.tab.rom + vi.toNat) (by omega), hrom_eq])
      refine ⟨ki + (lkm.totalSize clen + (kBr + (lkm.totalSize cbase + (1 + 1)))), st6, ?_, ?_, ha0_6',
        (hpres1.trans (hpres2.trans hpres3)).trans (hpres4.trans (hpres5.trans hpres6)), ?_⟩
      · rw [run_add, hrun1]; dsimp only
        rw [run_add, hrun2]; dsimp only
        rw [run_add, hrun3]; dsimp only
        rw [run_add, hrun4]; dsimp only
        rw [run_add, run_one_cont _ _ st5 (by rw [hsAdd]; rfl)]; dsimp only
        exact hrun6
      · rw [hpc6, htw5, htw4, htw_ce]; congr 2; omega
      · have hm : st6.mem = st1.mem := by
          rw [hmem6]; dsimp only [st5]; rw [prog_stepReg_mem, hmem4, hmem3, hmem2]
        rw [hm]; exact heq1
    · have hevalE : _root_.L.evalE (.ldc d i) ⟨lm, loc⟩ = .error .oob := by
        change (_root_.L.evalE i >>= fun idx => _root_.L.ldc d idx) ⟨lm, loc⟩ = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hvi]
        dsimp only [_root_.L.ldc, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.pure]
        simp [hbound]; rfl
      rw [hevalE]
      have hcondT : evalBranch .bgeu (st2.getReg AbiReg.a0) (st2.getReg AbiReg.t0) = true := by
        simp [evalBranch, ha0_2, ht0_2]
        rw [BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec, Nat.mod_eq_of_lt hdlt,
            decide_eq_false (by omega)]
      obtain ⟨kBr, st3, hrun3, hpc3', _, hpres3, hmem3⟩ :=
        prog_step_br_taken env (pre ++ ci ++ clen) ((cbase ++ ctail) ++ post)
          .bgeu AbiReg.a0 AbiReg.t0 errLabel env.errTarget env.herrLbl (by decide)
          (by rw [hlistB]; exact hlink) h64Br st2 hpc2' hcondT
      refine ⟨ki + (lkm.totalSize clen + kBr), st3, ?_, hpc3',
        hpres1.trans (hpres2.trans hpres3), ?_⟩
      · rw [run_add, hrun1]; dsimp only
        rw [run_add, hrun2]; dsimp only
        exact hrun3
      · rw [hmem3, hmem2]; exact heq1
  · simp only [hvi] at ri
    have hevalE : _root_.L.evalE (.ldc d i) ⟨lm, loc⟩ = .error .oob := by
      simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hvi]
    rw [hevalE]; exact ri

theorem prog_emitSimpleExpr_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (lm : _root_.L.Mem) (loc : _root_.L.Locals)
    {sp : BitVec 64} {nl : Nat}
    (hspAlign : isAligned sp 8 = true)
    (pre post : List AsmItem) (rd tmp : Reg)
    (hrd0 : rd ≠ 0#5) (htmp0 : tmp ≠ 0#5) (_hne : tmp ≠ rd)
    (htmpSp : tmp ≠ AbiReg.sp) (htmpGp : tmp ≠ AbiReg.gp)
    (e : Expr) (ce : List AsmItem)
    (hsimp : emitSimpleExpr env.tab rd tmp e = some ce)
    (heOk : exprOkB env.tab nl e = true)
    (hlink : lkm.linkSpec (pre ++ ce ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize ce) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOk L sp st.mem nl loc) :
    ∃ v k st', _root_.L.evalE e ⟨lm, loc⟩ = .ok (v, ⟨lm, loc⟩) ∧
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize ce)) ∧
      st'.getReg rd = v.toBitVec ∧
      (∀ r, r ≠ rd → r ≠ tmp → st'.getReg r = st.getReg r) ∧
      st'.mem = st.mem := by
  cases e with
  | const w =>
    simp only [emitSimpleExpr, Option.some.injEq] at hsimp; subst hsimp
    obtain ⟨st', hrun, hoth, hrd, hmem, hpc'⟩ :=
      li_correct_lm lkm env.hrom pre post rd hrd0 (BitVec.ofNat 64 w.toNat) hlink h64 st hpc
    refine ⟨w, lkm.totalSize (li rd (BitVec.ofNat 64 w.toNat)), st', rfl, hrun, hpc', ?_,
      fun r hr _ => hoth r hr, hmem⟩
    rw [hrd]; apply BitVec.eq_of_toNat_eq; simp [UInt64.toNat_toBitVec]
  | var x =>
    simp only [emitSimpleExpr, Option.some.injEq] at hsimp; subst hsimp
    simp only [exprOkB, decide_eq_true_eq] at heOk
    have hal : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff x)) 8 = true := by
      rw [hsp, slotOff_ofInt]; exact isAligned8_add_int_mul8 sp hspAlign _
    obtain ⟨st', hrun, hoth, hrd, hmem, hpc'⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom pre post rd AbiReg.sp tmp hrd0 htmp0 htmpSp.symm
        (slotOff x) hlink h64 st hpc hal
    exact ⟨loc x, lkm.totalSize _, st', rfl, hrun, hpc', by rw [hrd, hsp, hframeOk x heOk], hoth, hmem⟩
  | len8 a =>
    simp only [emitSimpleExpr, Option.some.injEq] at hsimp; subst hsimp
    simp only [exprOkB] at heOk
    have hal : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.len8 a)) 8 = true := by
      rw [hgp, Tab.len8_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨st', hrun, hoth, hrd, hmem, hpc'⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom pre post rd AbiReg.gp tmp hrd0 htmp0 htmpGp.symm
        (env.tab.len8 a) hlink h64 st hpc hal
    refine ⟨lm.len8 a, lkm.totalSize _, st', rfl, hrun, hpc', ?_, hoth, hmem⟩
    rw [hrd, hgp, (hmemRel.1 a heOk).2.2.1]; rfl
  | len64 a =>
    simp only [emitSimpleExpr, Option.some.injEq] at hsimp; subst hsimp
    simp only [exprOkB] at heOk
    have hal : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.len64 (TieredArray.t0 a))) 8 = true := by
      rw [hgp, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨st', hrun, hoth, hrd, hmem, hpc'⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom pre post rd AbiReg.gp tmp hrd0 htmp0 htmpGp.symm
        (env.tab.len64 (TieredArray.t0 a)) hlink h64 st hpc hal
    refine ⟨lm.len64 (TieredArray.t0 a), lkm.totalSize _, st', rfl, hrun, hpc', ?_, hoth, hmem⟩
    rw [hrd, hgp, (hmemRel.2.1 (TieredArray.t0 a) heOk).2.2.1]; rfl
  | glob g =>
    simp only [emitSimpleExpr, Option.some.injEq] at hsimp; subst hsimp
    simp only [exprOkB, decide_eq_true_eq] at heOk
    have hal : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.globOff g)) 8 = true := by
      rw [hgp, Tab.globOff_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨st', hrun, hoth, hrd, hmem, hpc'⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom pre post rd AbiReg.gp tmp hrd0 htmp0 htmpGp.symm
        (env.tab.globOff g) hlink h64 st hpc hal
    exact ⟨lm.glob g, lkm.totalSize _, st', rfl, hrun, hpc',
      by rw [hrd, hgp, hmemRel.2.2.2 g heOk], hoth, hmem⟩
  | _ => simp [emitSimpleExpr] at hsimp

def tieredHead (tab : Tab) (nl tmp : Nat) (t i : Expr) : List AsmItem :=
  match emitSimpleExpr tab AbiReg.t0 AbiReg.t1 t with
  | some ct => compileE tab nl tmp i ++ ct
  | none =>
    compileE tab nl tmp t ++
    storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + tmp)) ++
    compileE tab nl (tmp + 1) i ++
    loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nl + tmp))

theorem prog_tiered_head_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (lm : _root_.L.Mem) (loc : _root_.L.Locals)
    {sp : BitVec 64} {nl nt : Nat}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (pre tail : List AsmItem) (tmp : Nat) (t i : Expr)
    (htOk : exprOkB env.tab nl t = true)
    (htmp_le : tmp + 1 ≤ nt)
    (htmp1 : tmp + maxTempsExpr t ≤ nt)
    (htmp2 : tmp + 1 + maxTempsExpr i ≤ nt)
    (iht : ∀ (pre post : List AsmItem) (tmp : Nat) (st : State),
      tmp + maxTempsExpr t ≤ nt →
      lkm.linkSpec (pre ++ compileE env.tab nl tmp t ++ post) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp t)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → st.getReg AbiReg.sp = sp →
      ProgMemRel env.tab L st.mem lm → ProgFrameOk L sp st.mem nl loc →
      match _root_.L.evalE t ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp t))) ∧
          st'.getReg AbiReg.a0 = v.toBitVec ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem)
    (ihi : ∀ (pre post : List AsmItem) (tmp : Nat) (st : State),
      tmp + maxTempsExpr i ≤ nt →
      lkm.linkSpec (pre ++ compileE env.tab nl tmp i ++ post) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → st.getReg AbiReg.sp = sp →
      ProgMemRel env.tab L st.mem lm → ProgFrameOk L sp st.mem nl loc →
      match _root_.L.evalE i ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i))) ∧
          st'.getReg AbiReg.a0 = v.toBitVec ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem)
    (hlink : lkm.linkSpec (pre ++ tieredHead env.tab nl tmp t i ++ tail) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (tieredHead env.tab nl tmp t i)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOk L sp st.mem nl loc) :
    match _root_.L.evalE t ⟨lm, loc⟩, _root_.L.evalE i ⟨lm, loc⟩ with
    | .ok (u, _), .ok (vi, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (tieredHead env.tab nl tmp t i))) ∧
        st'.getReg AbiReg.t0 = u.toBitVec ∧
        st'.getReg AbiReg.a0 = vi.toBitVec ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
    | _, _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem := by
  cases hs : emitSimpleExpr env.tab AbiReg.t0 AbiReg.t1 t with
  | some ct =>
    have hdef : tieredHead env.tab nl tmp t i = compileE env.tab nl tmp i ++ ct := by
      simp only [tieredHead, hs]
    rw [hdef] at hlink h64 ⊢
    have htw : lkm.totalSize (compileE env.tab nl tmp i ++ ct) =
        lkm.totalSize (compileE env.tab nl tmp i) + lkm.totalSize ct := lkm.totalSize_append _ _
    have hlinkI : lkm.linkSpec (pre ++ compileE env.tab nl tmp i ++ (ct ++ tail)) = .ok (env.code, env.labels) := by
      simpa only [List.append_assoc] using hlink
    have ri := ihi pre (ct ++ tail) tmp st (by omega) hlinkI (by rw [htw] at h64; omega) hpc hgp hsp hmemRel hframeOk
    rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
    · simp only [hvi] at ri
      obtain ⟨ki, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ri
      have hf : (frameSpan sp nl nt).valid := by
        simp only [frameSpan, MemSpan.valid]; have := L.hStackValid; omega
      have htw1 : lkm.totalSize (pre ++ compileE env.tab nl tmp i) =
          lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i) := lkm.totalSize_append _ _
      have hlinkT : lkm.linkSpec ((pre ++ compileE env.tab nl tmp i) ++ ct ++ tail) = .ok (env.code, env.labels) := by
        simpa only [List.append_assoc] using hlink
      obtain ⟨u, kt, st2, htu, hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
        prog_emitSimpleExpr_sim env L lm loc hspAlign (pre ++ compileE env.tab nl tmp i) tail
          AbiReg.t0 AbiReg.t1 (by decide) (by decide) (by decide) (by decide) (by decide)
          t ct hs htOk hlinkT (by rw [htw1]; rw [htw] at h64; omega) st1 (by rw [htw1]; exact hpc1)
          (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
          (ProgMemRel.of_tempSpan env hlo hhi (by omega) heq1 hmemRel)
          (ProgFrameOk.of_tempSpan hf (by omega) heq1 hframeOk)
      simp only [htu, hvi]
      have hpres2 : PreservedRegs st1 st2 :=
        ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
         hoth2 _ (by decide) (by decide),
         hoth2 _ (by decide) (by decide)⟩
      exact ⟨ki + kt, st2, by rw [run_add, hrun1]; exact hrun2,
        by rw [hpc2, htw1, htw, Nat.add_assoc], ht0_2,
        (hoth2 _ (by decide) (by decide)).trans ha0_1,
        hpres1.trans hpres2, by rw [hmem2]; exact heq1⟩
    · simp only [hvi] at ri
      have hPure : ∃ u, _root_.L.evalE t ⟨lm, loc⟩ = .ok (u, ⟨lm, loc⟩) := by
        cases t <;> simp [emitSimpleExpr] at hs <;> exact ⟨_, rfl⟩
      obtain ⟨u, htu⟩ := hPure
      simp only [htu, hvi]; exact ri
  | none =>
    have hdef : tieredHead env.tab nl tmp t i = compileE env.tab nl tmp t ++
        storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + tmp)) ++
        compileE env.tab nl (tmp + 1) i ++
        loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nl + tmp)) := by
      simp only [tieredHead, hs]
    rw [hdef] at hlink h64 ⊢
    exact prog_two_exprs_pair_sim env L lm loc hspAlign hlo hhi pre tail tmp t i
      htmp_le iht ihi htmp1 htmp2 hlink h64 st hpc hgp hsp hmemRel hframeOk

theorem prog_tiered_idx_bounds_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (lm : _root_.L.Mem) (loc : _root_.L.Locals)
    {sp : BitVec 64} {nl nt : Nat}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (pre tail : List AsmItem) (tmp : Nat) (a : ArrId) (t i : Expr)
    (ha : tier32OkB env.tab a t = true)
    (htOk : exprOkB env.tab nl t = true)
    (htmp_le : tmp + 1 ≤ nt)
    (htmp1 : tmp + maxTempsExpr t ≤ nt)
    (htmp2 : tmp + 1 + maxTempsExpr i ≤ nt)
    (iht : ∀ (pre post : List AsmItem) (tmp : Nat) (st : State),
      tmp + maxTempsExpr t ≤ nt →
      lkm.linkSpec (pre ++ compileE env.tab nl tmp t ++ post) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp t)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → st.getReg AbiReg.sp = sp →
      ProgMemRel env.tab L st.mem lm → ProgFrameOk L sp st.mem nl loc →
      match _root_.L.evalE t ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp t))) ∧
          st'.getReg AbiReg.a0 = v.toBitVec ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem)
    (ihi : ∀ (pre post : List AsmItem) (tmp : Nat) (st : State),
      tmp + maxTempsExpr i ≤ nt →
      lkm.linkSpec (pre ++ compileE env.tab nl tmp i ++ post) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → st.getReg AbiReg.sp = sp →
      ProgMemRel env.tab L st.mem lm → ProgFrameOk L sp st.mem nl loc →
      match _root_.L.evalE i ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i))) ∧
          st'.getReg AbiReg.a0 = v.toBitVec ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem)
    (hlink : lkm.linkSpec (pre ++ (tieredHead env.tab nl tmp t i ++
        [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
         Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
        loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (env.tab.len64 (TieredArray.t0 a))) ++ tail) =
        .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (tieredHead env.tab nl tmp t i ++
        [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
         Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
        loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (env.tab.len64 (TieredArray.t0 a)))) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOk L sp st.mem nl loc) :
    match _root_.L.evalE t ⟨lm, loc⟩, _root_.L.evalE i ⟨lm, loc⟩ with
    | .ok (u, _), .ok (vi, _) =>
      let off := if (u &&& 1) == 0 then 0#64 else 8#64
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (tieredHead env.tab nl tmp t i ++
          [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
           Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
          loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (env.tab.len64 (TieredArray.t0 a))))) ∧
        st'.getReg AbiReg.t1 = L.T + off ∧
        st'.getReg AbiReg.t2 = BitVec.ofNat 64 (lm.arr64 (tierA a u)).size ∧
        st'.getReg AbiReg.a0 = vi.toBitVec ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
    | _, _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem := by
  let cpair := tieredHead env.tab nl tmp t i
  let chdr := [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
    Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0]
  let clen := loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (env.tab.len64 (TieredArray.t0 a))
  have htw_all : lkm.totalSize (tieredHead env.tab nl tmp t i ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
       Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (env.tab.len64 (TieredArray.t0 a))) =
      lkm.totalSize cpair + 3 + lkm.totalSize clen := by
    dsimp only [cpair, chdr, clen]; simp only [lkm.totalSize_append, lkm.totalSize_cons, lkm.totalSize_nil, Asm.andi, Asm.slli, Asm.add, lkm.itemSize_instr]
  have rpair := prog_tiered_head_sim env L lm loc hspAlign hlo hhi pre (chdr ++ clen ++ tail)
    tmp t i htOk htmp_le htmp1 htmp2 iht ihi
    (by rw [show pre ++ cpair ++ (chdr ++ clen ++ tail) =
        pre ++ (cpair ++ chdr ++ clen) ++ tail from by simp only [List.append_assoc]]; exact hlink)
    (by rw [htw_all] at h64; dsimp only [cpair] at h64 ⊢; omega)
    st hpc hgp hsp hmemRel hframeOk
  rcases _root_.L.evalE_pure t ⟨lm, loc⟩ with ⟨u, hu⟩ | hu
  · rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
    · simp only [hu, hvi] at rpair ⊢
      obtain ⟨kp, st1, hrun1, hpc1, ht0_1, ha0_1, hpres1, heq1⟩ := rpair
      have hrel1 := ProgMemRel.of_tempSpan env hlo hhi (by omega) heq1 hmemRel
      have hta := tierAddrOk_len64_addr_T L.T a u (tier32Ok_to_tierAddrOk ha hu)
      rcases hrel1.2.1 (tierA a u) hta.1 with ⟨_, _, hlenR, _, _⟩
      have htw1 : lkm.totalSize (pre ++ cpair) = lkm.totalSize pre + lkm.totalSize cpair := lkm.totalSize_append _ _
      have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ cpair)) := by rw [htw1]; exact hpc1
      obtain ⟨st2, hrun2, hpc2, ht1_2, hmem2, hpres2, hoth2⟩ :=
        step_tierHdr env (pre ++ cpair) (clen ++ tail) AbiReg.t0 u
          (by rw [show (pre ++ cpair) ++ chdr ++ (clen ++ tail) =
              pre ++ (cpair ++ chdr ++ clen) ++ tail from by simp only [List.append_assoc]]; exact hlink)
          (by rw [htw1]; rw [htw_all] at h64; omega)
          st1 hpc1' (hpres1.gp.trans hgp) ht0_1
      have htw2 : lkm.totalSize (pre ++ cpair ++ chdr) = lkm.totalSize pre + lkm.totalSize cpair + 3 := by
        rw [lkm.totalSize_append, htw1]; dsimp only [chdr]
        simp only [lkm.totalSize_cons, lkm.totalSize_nil, Asm.andi, Asm.slli, Asm.add, lkm.itemSize_instr]
      have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ cpair ++ chdr)) := by
        rw [htw2, ← htw1]; exact hpc2
      have halLen : isAligned (st2.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.len64 (TieredArray.t0 a))) 8 = true := by
        rw [ht1_2, hta.2.1, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
      obtain ⟨st3, hrun3, hoth3, ht2_3, hmem3, hpc3⟩ :=
        loadMemOff_ld_correct_lm lkm env.hrom (pre ++ cpair ++ chdr) tail
          AbiReg.t2 AbiReg.t1 AbiReg.t3 (by decide) (by decide) (by decide)
          (env.tab.len64 (TieredArray.t0 a))
          (by rw [show (pre ++ cpair ++ chdr) ++ clen ++ tail =
              pre ++ (cpair ++ chdr ++ clen) ++ tail from by simp only [List.append_assoc]]; exact hlink)
          (by rw [htw2]; rw [htw_all] at h64; dsimp only [clen] at h64 ⊢; omega)
          st2 hpc2' halLen
      have hpres3 : PreservedRegs st2 st3 :=
        ⟨hoth3 _ (by decide) (by decide), hoth3 _ (by decide) (by decide),
         hoth3 _ (by decide) (by decide),
         hoth3 _ (by decide) (by decide)⟩
      refine ⟨kp + (3 + lkm.totalSize clen), st3, ?_, ?_, ?_, ?_, ?_,
        hpres1.trans (hpres2.trans hpres3), ?_⟩
      · rw [run_add, hrun1]; dsimp only
        rw [run_add, hrun2]; dsimp only
        exact hrun3
      · rw [hpc3, htw2, htw_all]; dsimp only [cpair, clen]; congr 2; omega
      · rw [hoth3 AbiReg.t1 (by decide) (by decide), ht1_2]
      · rw [ht2_3, hmem2, ht1_2, hta.2.1, hlenR]
      · rw [hoth3 AbiReg.a0 (by decide) (by decide), hoth2 AbiReg.a0 (by decide) (by decide), ha0_1]
      · rw [hmem3, hmem2]; exact heq1
    · simp only [hu, hvi] at rpair ⊢; exact rpair
  · simp only [hu] at rpair ⊢; exact rpair

theorem prog_tiered_addr8_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (lm : _root_.L.Mem) (loc : _root_.L.Locals)
    {sp : BitVec 64} {nl nt : Nat}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (pre tail : List AsmItem) (tmp : Nat) (a : ArrId) (t i : Expr)
    (ha : env.tab.tieredOkB a = true)
    (htOk : exprOkB env.tab nl t = true)
    (htmp_le : tmp + 1 ≤ nt)
    (htmp1 : tmp + maxTempsExpr t ≤ nt)
    (htmp2 : tmp + 1 + maxTempsExpr i ≤ nt)
    (iht : ∀ (pre post : List AsmItem) (tmp : Nat) (st : State),
      tmp + maxTempsExpr t ≤ nt →
      lkm.linkSpec (pre ++ compileE env.tab nl tmp t ++ post) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp t)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → st.getReg AbiReg.sp = sp →
      ProgMemRel env.tab L st.mem lm → ProgFrameOk L sp st.mem nl loc →
      match _root_.L.evalE t ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp t))) ∧
          st'.getReg AbiReg.a0 = v.toBitVec ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem)
    (ihi : ∀ (pre post : List AsmItem) (tmp : Nat) (st : State),
      tmp + maxTempsExpr i ≤ nt →
      lkm.linkSpec (pre ++ compileE env.tab nl tmp i ++ post) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → st.getReg AbiReg.sp = sp →
      ProgMemRel env.tab L st.mem lm → ProgFrameOk L sp st.mem nl loc →
      match _root_.L.evalE i ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i))) ∧
          st'.getReg AbiReg.a0 = v.toBitVec ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem)
    (hlink : lkm.linkSpec (pre ++ (tieredHead env.tab nl tmp t i ++
        [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
         Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
        loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (env.tab.len64 (TieredArray.t0 a)) ++
        [Asm.bgeu AbiReg.a0 AbiReg.t2 errLabel] ++
        loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t3 (env.tab.base64 (TieredArray.t0 a)) ++
        [Asm.slli AbiReg.t3 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3]) ++ tail) =
        .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (tieredHead env.tab nl tmp t i ++
        [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
         Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
        loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (env.tab.len64 (TieredArray.t0 a)) ++
        [Asm.bgeu AbiReg.a0 AbiReg.t2 errLabel] ++
        loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t3 (env.tab.base64 (TieredArray.t0 a)) ++
        [Asm.slli AbiReg.t3 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3])) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOk L sp st.mem nl loc) :
    match _root_.L.evalE t ⟨lm, loc⟩, _root_.L.evalE i ⟨lm, loc⟩ with
    | .ok (u, _), .ok (vi, _) =>
      let s := tierA a u
      if vi.toNat < (lm.arr64 s).size then
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (tieredHead env.tab nl tmp t i ++
            [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
             Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
            loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (env.tab.len64 (TieredArray.t0 a)) ++
            [Asm.bgeu AbiReg.a0 AbiReg.t2 errLabel] ++
            loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t3 (env.tab.base64 (TieredArray.t0 a)) ++
            [Asm.slli AbiReg.t3 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3]))) ∧
          st'.getReg AbiReg.t1 = L.base64 s + BitVec.ofNat 64 (8 * vi.toNat) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
      else
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
    | _, _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem := by
  let cpre := tieredHead env.tab nl tmp t i ++
    [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
     Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
    loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (env.tab.len64 (TieredArray.t0 a))
  let cbr := [Asm.bgeu AbiReg.a0 AbiReg.t2 errLabel]
  let cbase := loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t3 (env.tab.base64 (TieredArray.t0 a))
  let csh := [Asm.slli AbiReg.t3 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3]
  have htw_all : lkm.totalSize (cpre ++ cbr ++ cbase ++ csh) =
      lkm.totalSize cpre + lkm.totalSize cbr + lkm.totalSize cbase + 2 := by
    dsimp only [csh]; simp only [lkm.totalSize_append, lkm.totalSize_cons, lkm.totalSize_nil, Asm.slli, Asm.add, lkm.itemSize_instr]
  have hassoc : cpre ++ cbr ++ cbase ++ csh = tieredHead env.tab nl tmp t i ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
       Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (env.tab.len64 (TieredArray.t0 a)) ++
      [Asm.bgeu AbiReg.a0 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t3 (env.tab.base64 (TieredArray.t0 a)) ++
      [Asm.slli AbiReg.t3 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3] := by
    simp only [cpre, cbr, cbase, csh, List.append_assoc]
  rw [← hassoc] at hlink h64 ⊢
  have rb := prog_tiered_idx_bounds_sim env L lm loc hspAlign hlo hhi pre (cbr ++ cbase ++ csh ++ tail)
    tmp a t i (tieredOk_implies_tier32Ok env.tab a t ha) htOk htmp_le htmp1 htmp2 iht ihi
    (by rw [show pre ++ cpre ++ (cbr ++ cbase ++ csh ++ tail) = pre ++ (cpre ++ cbr ++ cbase ++ csh) ++ tail from by simp only [List.append_assoc]]; exact hlink)
    (by rw [htw_all] at h64; dsimp only [cpre] at h64 ⊢; exact by omega)
    st hpc hgp hsp hmemRel hframeOk
  rcases _root_.L.evalE_pure t ⟨lm, loc⟩ with ⟨u, hu⟩ | hu
  · rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
    · simp only [hu, hvi] at rb ⊢
      obtain ⟨kp, st1, hrun1, hpc1, ht1_1, ht2_1, ha0_1, hpres1, heq1⟩ := rb
      have hrel1 := ProgMemRel.of_tempSpan env hlo hhi (by omega) heq1 hmemRel
      have hta := tieredOk_len64_addr_T L.T a u ha
      rcases hrel1.2.1 (tierA a u) hta.1 with ⟨_, hlt61, _, hbaseR, _⟩
      have htw1 : lkm.totalSize (pre ++ cpre) = lkm.totalSize pre + lkm.totalSize cpre := lkm.totalSize_append _ _
      have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ cpre)) := by
        rw [htw1]; dsimp only [cpre] at hpc1 ⊢; exact hpc1
      have hlinkBr : lkm.linkSpec ((pre ++ cpre) ++ [.br .bgeu AbiReg.a0 AbiReg.t2 errLabel] ++ ((cbase ++ csh) ++ tail)) =
          .ok (env.code, env.labels) := by
        rw [show (pre ++ cpre) ++ [.br .bgeu AbiReg.a0 AbiReg.t2 errLabel] ++ ((cbase ++ csh) ++ tail) =
            pre ++ (cpre ++ cbr ++ cbase ++ csh) ++ tail from by simp only [cbr, Asm.bgeu, List.append_assoc]]; exact hlink
      have h64Br : 4 * (lkm.totalSize (pre ++ cpre) + lkm.itemSize (.br .bgeu AbiReg.a0 AbiReg.t2 errLabel)) < 2 ^ 64 := by
        rw [htw1]; rw [htw_all] at h64; dsimp only [cpre] at h64 ⊢
        have hbrsz : lkm.itemSize (.br .bgeu AbiReg.a0 AbiReg.t2 errLabel) = lkm.totalSize cbr := by
          simp [cbr, Asm.bgeu, lkm.totalSize_singleton]
        omega
      by_cases hbound : vi.toNat < (lm.arr64 (tierA a u)).size
      · simp only [hbound, ↓reduceIte]
        have hcondF : evalBranch .bgeu (st1.getReg AbiReg.a0) (st1.getReg AbiReg.t2) = false := by
          simp [evalBranch, ha0_1, ht2_1]
          rw [BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
              Nat.mod_eq_of_lt (by omega : (lm.arr64 (tierA a u)).size < 2 ^ 64),
              decide_eq_true hbound]
        obtain ⟨kBr, st2, hrun2, hpc2', hoth2, hpres2, hmem2⟩ :=
          prog_step_br_fall env (pre ++ cpre) ((cbase ++ csh) ++ tail)
            .bgeu AbiReg.a0 AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide)
            hlinkBr h64Br st1 hpc1' hcondF
        have htw2 : lkm.totalSize (pre ++ cpre ++ cbr) = lkm.totalSize pre + lkm.totalSize cpre + lkm.totalSize cbr := by
          rw [lkm.totalSize_append, htw1]
        have hpc2 : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ cpre ++ cbr)) := by
          rw [hpc2', htw2, htw1, show cbr = [.br .bgeu AbiReg.a0 AbiReg.t2 errLabel] from rfl]
        have halBase : isAligned (st2.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.base64 (TieredArray.t0 a))) 8 = true := by
          rw [hoth2 _ (by decide), ht1_1, hta.2.2, Tab.base64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
        obtain ⟨st3, hrun3, hoth3, ht1_3, hmem3, hpc3⟩ :=
          loadMemOff_ld_correct_lm lkm env.hrom (pre ++ cpre ++ cbr) (csh ++ tail)
            AbiReg.t1 AbiReg.t1 AbiReg.t3 (by decide) (by decide) (by decide)
            (env.tab.base64 (TieredArray.t0 a))
            (by rw [show (pre ++ cpre ++ cbr) ++ cbase ++ (csh ++ tail) =
                pre ++ (cpre ++ cbr ++ cbase ++ csh) ++ tail from by simp only [List.append_assoc]]; exact hlink)
            (by rw [htw2]; rw [htw_all] at h64; dsimp only [cbase] at h64 ⊢; omega) st2 hpc2 halBase
        have hpres3 : PreservedRegs st2 st3 :=
          ⟨hoth3 _ (by decide) (by decide), hoth3 _ (by decide) (by decide),
           hoth3 _ (by decide) (by decide),
           hoth3 _ (by decide) (by decide)⟩
        have htw3 : lkm.totalSize (pre ++ cpre ++ cbr ++ cbase) =
            lkm.totalSize pre + lkm.totalSize cpre + lkm.totalSize cbr + lkm.totalSize cbase := by
          rw [lkm.totalSize_append, htw2]
        have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ cpre ++ cbr ++ cbase)) := by
          rw [htw3, ← htw2]; exact hpc3
        let p3 := pre ++ cpre ++ cbr ++ cbase
        have hsSll := step_item_instr_lm lkm env.hrom p3
          ([Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3] ++ tail) (.shImm .slli AbiReg.t3 AbiReg.a0 3#6)
          (by rw [show p3 ++ [AsmItem.instr (.shImm .slli AbiReg.t3 AbiReg.a0 3#6)] ++ ([Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3] ++ tail) =
              pre ++ (cpre ++ cbr ++ cbase ++ csh) ++ tail from by
              simp only [p3, csh, Asm.slli, List.append_assoc, List.cons_append, List.nil_append]]; exact hlink)
          (by rw [htw3]; rw [htw_all] at h64; omega) st3 hpc3'
        let st4 := stepReg st3 AbiReg.t3 (st3.getReg AbiReg.a0 <<< 3) (st3.pc + 4#64)
        have hpres4 : PreservedRegs st3 st4 :=
          ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
           getReg_stepReg_ne _ _ _ (by decide) _ _,
           getReg_stepReg_ne _ _ _ (by decide) _ _⟩
        have htw4 : lkm.totalSize (p3 ++ [Asm.slli AbiReg.t3 AbiReg.a0 3#6]) = lkm.totalSize p3 + 1 := by
          rw [lkm.totalSize_append, Asm.slli, lkm.totalSize_instr]
        have hpc4 : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p3 ++ [Asm.slli AbiReg.t3 AbiReg.a0 3#6])) := by
          change st3.pc + 4#64 = _; rw [pc_add_4_ofNat st3.pc hpc3', htw4]
        have hsAdd := step_item_instr_lm lkm env.hrom (p3 ++ [Asm.slli AbiReg.t3 AbiReg.a0 3#6]) tail
          (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.t3)
          (by rw [show (p3 ++ [Asm.slli AbiReg.t3 AbiReg.a0 3#6]) ++ [AsmItem.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.t3)] ++ tail =
              pre ++ (cpre ++ cbr ++ cbase ++ csh) ++ tail from by
              simp only [p3, csh, Asm.add, List.append_assoc, List.cons_append, List.nil_append]]; exact hlink)
          (by rw [htw4, htw3]; rw [htw_all] at h64; omega) st4 hpc4
        let st5 := stepReg st4 AbiReg.t1 (st4.getReg AbiReg.t1 + st4.getReg AbiReg.t3) (st4.pc + 4#64)
        have hpres5 : PreservedRegs st4 st5 :=
          ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
           getReg_stepReg_ne _ _ _ (by decide) _ _,
           getReg_stepReg_ne _ _ _ (by decide) _ _⟩
        refine ⟨kp + (kBr + (lkm.totalSize cbase + (1 + 1))), st5, ?_, ?_, ?_,
          (hpres1.trans hpres2).trans (hpres3.trans (hpres4.trans hpres5)), ?_⟩
        · rw [run_add, hrun1]; dsimp only
          rw [run_add, hrun2]; dsimp only
          rw [run_add, hrun3]; dsimp only
          rw [run_add, run_one_cont _ _ st4 (by rw [hsSll]; rfl)]; dsimp only
          exact run_one_cont _ _ st5 (by rw [hsAdd]; rfl)
        · change st4.pc + 4#64 = _
          rw [pc_add_4_ofNat st4.pc hpc4, htw4, htw3, htw_all]; dsimp only [cpre]; congr 2; omega
        · have ht1_3' : st3.getReg AbiReg.t1 = L.base64 (tierA a u) := by
            rw [ht1_3]; change readWord64 st2.mem (st2.getReg AbiReg.t1 + _) = _
            rw [hmem2, hoth2 _ (by decide), ht1_1, hta.2.2]; exact hbaseR
          have ha0_3' : st3.getReg AbiReg.a0 = vi.toBitVec := by
            rw [hoth3 AbiReg.a0 (by decide) (by decide), hoth2 _ (by decide)]; exact ha0_1
          have ht3_4 : st4.getReg AbiReg.t3 = BitVec.ofNat 64 (8 * vi.toNat) := by
            change (stepReg st3 AbiReg.t3 _ _).getReg AbiReg.t3 = _
            rw [getReg_stepReg_eq _ _ (by decide), ha0_3']
            apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_shiftLeft, UInt64.toNat_toBitVec, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
            rw [show (2 ^ 3 : Nat) = 8 from rfl, Nat.mul_comm _ 8, Nat.mod_eq_of_lt (by omega)]
          have ht1_4 : st4.getReg AbiReg.t1 = st3.getReg AbiReg.t1 :=
            getReg_stepReg_ne st3 AbiReg.t3 AbiReg.t1 (by decide) _ _
          change (stepReg st4 AbiReg.t1 _ _).getReg AbiReg.t1 = _
          rw [getReg_stepReg_eq _ _ (by decide), ht1_4, ht1_3', ht3_4]
        · dsimp only [st5, st4]
          rw [prog_stepReg_mem, prog_stepReg_mem, hmem3, hmem2]; exact heq1
      · simp only [hbound, ↓reduceIte]
        have hcondT : evalBranch .bgeu (st1.getReg AbiReg.a0) (st1.getReg AbiReg.t2) = true := by
          simp [evalBranch, ha0_1, ht2_1]
          rw [BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
              Nat.mod_eq_of_lt (by omega : (lm.arr64 (tierA a u)).size < 2 ^ 64),
              decide_eq_false (by omega)]
        obtain ⟨kBr, st2, hrun2, hpc2', _, hpres2, hmem2⟩ :=
          prog_step_br_taken env (pre ++ cpre) ((cbase ++ csh) ++ tail)
            .bgeu AbiReg.a0 AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide)
            hlinkBr h64Br st1 hpc1' hcondT
        refine ⟨kp + kBr, st2, ?_, hpc2', hpres1.trans hpres2, by rw [hmem2]; exact heq1⟩
        rw [run_add, hrun1]; dsimp only; exact hrun2
    · simp only [hu, hvi] at rb ⊢; exact rb
  · simp only [hu] at rb ⊢; exact rb

theorem prog_tiered_const_addr8_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (lm : _root_.L.Mem) (loc : _root_.L.Locals)
    {sp : BitVec 64} {nl nt : Nat}
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (pre tail : List AsmItem) (tmp : Nat) (s : TieredArray) (i : Expr)
    (hs : env.tab.wordPosOkB s = true)
    (htmpi : tmp + maxTempsExpr i ≤ nt)
    (ihi : ∀ (pre post : List AsmItem) (tmp : Nat) (st : State),
      tmp + maxTempsExpr i ≤ nt →
      lkm.linkSpec (pre ++ compileE env.tab nl tmp i ++ post) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → st.getReg AbiReg.sp = sp →
      ProgMemRel env.tab L st.mem lm → ProgFrameOk L sp st.mem nl loc →
      match _root_.L.evalE i ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i))) ∧
          st'.getReg AbiReg.a0 = v.toBitVec ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem)
    (hlink : lkm.linkSpec (pre ++ (compileE env.tab nl tmp i ++
        loadMemOff .ld AbiReg.t2 AbiReg.gp AbiReg.t3 (env.tab.len64 s) ++
        [Asm.bgeu AbiReg.a0 AbiReg.t2 errLabel] ++
        loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t3 (env.tab.base64 s) ++
        [Asm.slli AbiReg.t3 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3]) ++ tail) =
        .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i ++
        loadMemOff .ld AbiReg.t2 AbiReg.gp AbiReg.t3 (env.tab.len64 s) ++
        [Asm.bgeu AbiReg.a0 AbiReg.t2 errLabel] ++
        loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t3 (env.tab.base64 s) ++
        [Asm.slli AbiReg.t3 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3])) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOk L sp st.mem nl loc) :
    match _root_.L.evalE i ⟨lm, loc⟩ with
    | .ok (vi, _) =>
      if vi.toNat < (lm.arr64 s).size then
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i ++
            loadMemOff .ld AbiReg.t2 AbiReg.gp AbiReg.t3 (env.tab.len64 s) ++
            [Asm.bgeu AbiReg.a0 AbiReg.t2 errLabel] ++
            loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t3 (env.tab.base64 s) ++
            [Asm.slli AbiReg.t3 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3]))) ∧
          st'.getReg AbiReg.t1 = L.base64 s + BitVec.ofNat 64 (8 * vi.toNat) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
      else
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem := by
  let ci := compileE env.tab nl tmp i
  let clen := loadMemOff .ld AbiReg.t2 AbiReg.gp AbiReg.t3 (env.tab.len64 s)
  let cbr := [Asm.bgeu AbiReg.a0 AbiReg.t2 errLabel]
  let cbase := loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t3 (env.tab.base64 s)
  let csh := [Asm.slli AbiReg.t3 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3]
  have htw_all : lkm.totalSize (ci ++ clen ++ cbr ++ cbase ++ csh) =
      lkm.totalSize ci + lkm.totalSize clen + lkm.totalSize cbr + lkm.totalSize cbase + 2 := by
    dsimp only [csh]; simp only [lkm.totalSize_append, lkm.totalSize_cons, lkm.totalSize_nil, Asm.slli, Asm.add, lkm.itemSize_instr]
  have ri := ihi pre ((clen ++ cbr ++ cbase ++ csh) ++ tail) tmp st htmpi
    (by simpa only [ci, clen, cbr, cbase, csh, List.append_assoc] using hlink)
    (by rw [show lkm.totalSize ci = lkm.totalSize (compileE env.tab nl tmp i) from rfl] at htw_all; rw [htw_all] at h64; omega)
    hpc hgp hsp hmemRel hframeOk
  rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
  · simp only [hvi] at ri ⊢
    obtain ⟨ki, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ri
    have hrel1 := ProgMemRel.of_tempSpan env hlo hhi (by omega) heq1 hmemRel
    rcases hrel1.2.1 s hs with ⟨_, hlt61, hlenR, hbaseR, _⟩
    have htw1 : lkm.totalSize (pre ++ ci) = lkm.totalSize pre + lkm.totalSize ci := lkm.totalSize_append _ _
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ci)) := by rw [htw1]; exact hpc1
    have halLen : isAligned (st1.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.len64 s)) 8 = true := by
      rw [hpres1.gp.trans hgp, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨st2, hrun2, hoth2, ht2_2, hmem2, hpc2⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom (pre ++ ci) (cbr ++ cbase ++ csh ++ tail)
        AbiReg.t2 AbiReg.gp AbiReg.t3 (by decide) (by decide) (by decide) (env.tab.len64 s)
        (by simpa only [ci, clen, cbr, cbase, csh, List.append_assoc] using hlink)
        (by rw [htw1]; rw [htw_all] at h64; dsimp only [ci, clen, cbr, cbase, csh] at h64 ⊢; omega) st1 hpc1' halLen
    have hpres2 : PreservedRegs st1 st2 :=
      ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
       hoth2 _ (by decide) (by decide),
       hoth2 _ (by decide) (by decide)⟩
    have htw2 : lkm.totalSize (pre ++ ci ++ clen) = lkm.totalSize pre + lkm.totalSize ci + lkm.totalSize clen := by
      rw [lkm.totalSize_append, htw1]
    have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ci ++ clen)) := by
      rw [htw2, ← htw1]; exact hpc2
    have ha0_2 : st2.getReg AbiReg.a0 = vi.toBitVec := (hoth2 _ (by decide) (by decide)).trans ha0_1
    have ht2_2' : st2.getReg AbiReg.t2 = BitVec.ofNat 64 (lm.arr64 s).size := by
      rw [ht2_2, hpres1.gp.trans hgp, hlenR]
    have hlinkBr : lkm.linkSpec ((pre ++ ci ++ clen) ++ [.br .bgeu AbiReg.a0 AbiReg.t2 errLabel] ++ ((cbase ++ csh) ++ tail)) =
        .ok (env.code, env.labels) := by
      simpa only [ci, clen, cbr, cbase, csh, Asm.bgeu, List.append_assoc] using hlink
    have h64Br : 4 * (lkm.totalSize (pre ++ ci ++ clen) + lkm.itemSize (.br .bgeu AbiReg.a0 AbiReg.t2 errLabel)) < 2 ^ 64 := by
      rw [htw2]; rw [htw_all] at h64
      have hbrsz : lkm.itemSize (.br .bgeu AbiReg.a0 AbiReg.t2 errLabel) = lkm.totalSize cbr := by
        simp [cbr, Asm.bgeu, lkm.totalSize_singleton]
      omega
    by_cases hbound : vi.toNat < (lm.arr64 s).size
    · simp only [hbound, ↓reduceIte]
      have hcondF : evalBranch .bgeu (st2.getReg AbiReg.a0) (st2.getReg AbiReg.t2) = false := by
        simp [evalBranch, ha0_2, ht2_2']
        rw [BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
            Nat.mod_eq_of_lt (by omega : (lm.arr64 s).size < 2 ^ 64), decide_eq_true hbound]
      obtain ⟨kBr, st3, hrun3, hpc3', hoth3, hpres3, hmem3⟩ :=
        prog_step_br_fall env (pre ++ ci ++ clen) ((cbase ++ csh) ++ tail)
          .bgeu AbiReg.a0 AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide)
          hlinkBr h64Br st2 hpc2' hcondF
      have htw3 : lkm.totalSize (pre ++ ci ++ clen ++ cbr) = lkm.totalSize pre + lkm.totalSize ci + lkm.totalSize clen + lkm.totalSize cbr := by
        rw [lkm.totalSize_append, htw2]
      have hpc3 : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ci ++ clen ++ cbr)) := by
        rw [hpc3', htw3, htw2, show cbr = [.br .bgeu AbiReg.a0 AbiReg.t2 errLabel] from rfl]
      have halBase : isAligned (st3.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.base64 s)) 8 = true := by
        rw [hpres3.gp.trans (hpres2.gp.trans (hpres1.gp.trans hgp)), Tab.base64_eq_nat]
        exact isAligned8_add_int_mul8 L.T L.hTAlign _
      obtain ⟨st4, hrun4, hoth4, ht1_4, hmem4, hpc4⟩ :=
        loadMemOff_ld_correct_lm lkm env.hrom (pre ++ ci ++ clen ++ cbr) (csh ++ tail)
          AbiReg.t1 AbiReg.gp AbiReg.t3 (by decide) (by decide) (by decide) (env.tab.base64 s)
          (by simpa only [ci, clen, cbr, cbase, csh, List.append_assoc] using hlink)
          (by rw [htw3]; rw [htw_all] at h64; dsimp only [ci, clen, cbr, cbase, csh] at h64 ⊢; omega) st3 hpc3 halBase
      have hpres4 : PreservedRegs st3 st4 :=
        ⟨hoth4 _ (by decide) (by decide), hoth4 _ (by decide) (by decide),
         hoth4 _ (by decide) (by decide),
         hoth4 _ (by decide) (by decide)⟩
      let p4 := pre ++ ci ++ clen ++ cbr ++ cbase
      have htw4 : lkm.totalSize p4 = lkm.totalSize pre + lkm.totalSize ci + lkm.totalSize clen + lkm.totalSize cbr + lkm.totalSize cbase := by
        dsimp only [p4]; rw [lkm.totalSize_append, htw3]
      have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize p4) := by rw [htw4, ← htw3]; exact hpc4
      have hsSll := step_item_instr_lm lkm env.hrom p4 ([Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3] ++ tail)
        (.shImm .slli AbiReg.t3 AbiReg.a0 3#6)
        (by simpa only [p4, ci, clen, cbr, cbase, csh, Asm.slli, List.append_assoc, List.cons_append, List.nil_append] using hlink)
        (by rw [htw4]; rw [htw_all] at h64; omega) st4 hpc4'
      let st5 := stepReg st4 AbiReg.t3 (st4.getReg AbiReg.a0 <<< 3) (st4.pc + 4#64)
      have hpres5 : PreservedRegs st4 st5 :=
        ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _⟩
      have htw5 : lkm.totalSize (p4 ++ [Asm.slli AbiReg.t3 AbiReg.a0 3#6]) = lkm.totalSize p4 + 1 := by
        rw [lkm.totalSize_append, Asm.slli, lkm.totalSize_instr]
      have hpc5 : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p4 ++ [Asm.slli AbiReg.t3 AbiReg.a0 3#6])) := by
        change st4.pc + 4#64 = _; rw [pc_add_4_ofNat st4.pc hpc4', htw5]
      have hsAdd := step_item_instr_lm lkm env.hrom (p4 ++ [Asm.slli AbiReg.t3 AbiReg.a0 3#6]) tail
        (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.t3)
        (by simpa only [p4, ci, clen, cbr, cbase, csh, Asm.add, Asm.slli, List.append_assoc, List.cons_append, List.nil_append] using hlink)
        (by rw [htw5, htw4]; rw [htw_all] at h64; omega) st5 hpc5
      let st6 := stepReg st5 AbiReg.t1 (st5.getReg AbiReg.t1 + st5.getReg AbiReg.t3) (st5.pc + 4#64)
      have hpres6 : PreservedRegs st5 st6 :=
        ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _⟩
      refine ⟨ki + (lkm.totalSize clen + (kBr + (lkm.totalSize cbase + (1 + 1)))), st6, ?_, ?_, ?_,
        (hpres1.trans hpres2).trans (hpres3.trans (hpres4.trans (hpres5.trans hpres6))), ?_⟩
      · rw [run_add, hrun1]; dsimp only
        rw [run_add, hrun2]; dsimp only
        rw [run_add, hrun3]; dsimp only
        rw [run_add, hrun4]; dsimp only
        rw [run_add, run_one_cont _ _ st5 (by rw [hsSll]; rfl)]; dsimp only
        exact run_one_cont _ _ st6 (by rw [hsAdd]; rfl)
      · change st5.pc + 4#64 = _
        rw [pc_add_4_ofNat st5.pc hpc5, htw5, htw4, htw_all]; congr 2; omega
      · have ht1_4' : st4.getReg AbiReg.t1 = L.base64 s := by
          rw [ht1_4, hmem3, hmem2, hpres3.gp.trans (hpres2.gp.trans (hpres1.gp.trans hgp))]; exact hbaseR
        have ha0_4' : st4.getReg AbiReg.a0 = vi.toBitVec :=
          (hoth4 _ (by decide) (by decide)).trans ((hoth3 _ (by decide)).trans ha0_2)
        have ht3_5 : st5.getReg AbiReg.t3 = BitVec.ofNat 64 (8 * vi.toNat) := by
          change (stepReg st4 AbiReg.t3 _ _).getReg AbiReg.t3 = _
          rw [getReg_stepReg_eq _ _ (by decide), ha0_4']
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_shiftLeft, UInt64.toNat_toBitVec, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
          rw [show (2 ^ 3 : Nat) = 8 from rfl, Nat.mul_comm _ 8, Nat.mod_eq_of_lt (by omega)]
        change (stepReg st5 AbiReg.t1 _ _).getReg AbiReg.t1 = _
        rw [getReg_stepReg_eq _ _ (by decide),
            getReg_stepReg_ne st4 AbiReg.t3 AbiReg.t1 (by decide) _ _, ht1_4', ht3_5]
      · dsimp only [st6, st5]; rw [prog_stepReg_mem, prog_stepReg_mem, hmem4, hmem3, hmem2]; exact heq1
    · simp only [hbound, ↓reduceIte]
      have hcondT : evalBranch .bgeu (st2.getReg AbiReg.a0) (st2.getReg AbiReg.t2) = true := by
        simp [evalBranch, ha0_2, ht2_2']
        rw [BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
            Nat.mod_eq_of_lt (by omega : (lm.arr64 s).size < 2 ^ 64), decide_eq_false (by omega)]
      obtain ⟨kBr, st3, hrun3, hpc3', _, hpres3, hmem3⟩ :=
        prog_step_br_taken env (pre ++ ci ++ clen) ((cbase ++ csh) ++ tail)
          .bgeu AbiReg.a0 AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide)
          hlinkBr h64Br st2 hpc2' hcondT
      refine ⟨ki + (lkm.totalSize clen + kBr), st3, ?_, hpc3',
        (hpres1.trans hpres2).trans hpres3, by rw [hmem3, hmem2]; exact heq1⟩
      rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3
  · simp only [hvi] at ri ⊢; exact ri

theorem prog_ld32t_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (lm : _root_.L.Mem) (loc : _root_.L.Locals)
    {sp : BitVec 64} {nl nt : Nat}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (pre post : List AsmItem) (tmp : Nat) (a : ArrId) (t i : Expr)
    (ha : tier32OkB env.tab a t = true)
    (htOk : exprOkB env.tab nl t = true)
    (htmp : tmp + maxTempsExpr (.ld32t a t i) ≤ nt)
    (iht : ∀ (pre post : List AsmItem) (tmp : Nat) (st : State),
      tmp + maxTempsExpr t ≤ nt →
      lkm.linkSpec (pre ++ compileE env.tab nl tmp t ++ post) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp t)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → st.getReg AbiReg.sp = sp →
      ProgMemRel env.tab L st.mem lm → ProgFrameOk L sp st.mem nl loc →
      match _root_.L.evalE t ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp t))) ∧
          st'.getReg AbiReg.a0 = v.toBitVec ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem)
    (ihi : ∀ (pre post : List AsmItem) (tmp : Nat) (st : State),
      tmp + maxTempsExpr i ≤ nt →
      lkm.linkSpec (pre ++ compileE env.tab nl tmp i ++ post) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → st.getReg AbiReg.sp = sp →
      ProgMemRel env.tab L st.mem lm → ProgFrameOk L sp st.mem nl loc →
      match _root_.L.evalE i ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i))) ∧
          st'.getReg AbiReg.a0 = v.toBitVec ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem)
    (hlink : lkm.linkSpec (pre ++ compileE env.tab nl tmp (.ld32t a t i) ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp (.ld32t a t i))) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOk L sp st.mem nl loc) :
    match _root_.L.evalE (.ld32t a t i) ⟨lm, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp (.ld32t a t i)))) ∧
        st'.getReg AbiReg.a0 = v.toBitVec ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem := by
  dsimp only [maxTempsExpr] at htmp
  let csrl := [Asm.srli AbiReg.t3 AbiReg.a0 1#6]
  let cbr := [Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel]
  let ctail := [Asm.slli AbiReg.t3 AbiReg.a0 2#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3,
                Asm.lwu AbiReg.a0 AbiReg.t1 0#12]
  have runTail : ∀ (pHead : List AsmItem) (baseReg : Reg) (off : Int) (u vi : _root_.L.Word) (st1 : State)
      (hbr3 : baseReg ≠ AbiReg.t3) (hbr6 : baseReg ≠ AbiReg.t6 ∧ baseReg ≠ AbiReg.s1)
      (hu : _root_.L.evalE t ⟨lm, loc⟩ = .ok (u, ⟨lm, loc⟩))
      (hvi : _root_.L.evalE i ⟨lm, loc⟩ = .ok (vi, ⟨lm, loc⟩))
      (hrel1 : ProgMemRel env.tab L st1.mem lm)
      (hwordOk : env.tab.wordPosOkB (tierA a u) = true)
      (haddrEq : st1.getReg baseReg + BitVec.ofInt 64 off =
        L.T + BitVec.ofInt 64 (env.tab.base64 (tierA a u)))
      (hpc1 : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pHead))
      (ht2_1 : st1.getReg AbiReg.t2 = BitVec.ofNat 64 (lm.arr64 (tierA a u)).size)
      (ha0_1 : st1.getReg AbiReg.a0 = vi.toBitVec)
      (hlinkT : lkm.linkSpec (pHead ++ csrl ++ cbr ++
        loadMemOff .ld AbiReg.t1 baseReg AbiReg.t3 off ++ ctail ++ post) = .ok (env.code, env.labels))
      (h64T : 4 * (lkm.totalSize pHead + (1 + lkm.totalSize cbr +
        lkm.totalSize (loadMemOff .ld AbiReg.t1 baseReg AbiReg.t3 off) + 3)) < 2 ^ 64),
      match _root_.L.evalE (.ld32t a t i) ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st1 = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pHead + (1 + lkm.totalSize cbr +
            lkm.totalSize (loadMemOff .ld AbiReg.t1 baseReg AbiReg.t3 off) + 3))) ∧
          st'.getReg AbiReg.a0 = v.toBitVec ∧
          PreservedRegs st1 st' ∧ st'.mem = st1.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st1 = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st1 st' ∧ st'.mem = st1.mem := by
    intro pHead baseReg off u vi st1 hbr3 hbr6 hu hvi hrel1 hwordOk haddrEq hpc1 ht2_1 ha0_1 hlinkT h64T
    let cbase := loadMemOff .ld AbiReg.t1 baseReg AbiReg.t3 off
    rcases hrel1.2.1 (tierA a u) hwordOk with ⟨_, hlt61, _, hbaseR, hwordsR⟩
    have hsSrl := step_item_instr_lm lkm env.hrom pHead ((cbr ++ cbase ++ ctail) ++ post)
      (.shImm .srli AbiReg.t3 AbiReg.a0 1#6)
      (by simpa only [csrl, Asm.srli, List.append_assoc, List.cons_append, List.nil_append] using hlinkT)
      (by omega) st1 hpc1
    let st2 := stepReg st1 AbiReg.t3 (st1.getReg AbiReg.a0 >>> 1) (st1.pc + 4#64)
    have hpres2 : PreservedRegs st1 st2 :=
      ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
       getReg_stepReg_ne _ _ _ (by decide) _ _,
       getReg_stepReg_ne _ _ _ (by decide) _ _⟩
    have htw2 : lkm.totalSize (pHead ++ csrl) = lkm.totalSize pHead + 1 := by
      rw [lkm.totalSize_append]; dsimp only [csrl]; simp only [Asm.srli, lkm.totalSize_instr]
    have hpc2 : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pHead ++ csrl)) := by
      change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1, htw2]
    have ht3_2 : st2.getReg AbiReg.t3 = BitVec.ofNat 64 (vi / 2).toNat := by
      change (stepReg st1 AbiReg.t3 _ _).getReg AbiReg.t3 = _
      rw [getReg_stepReg_eq _ _ (by decide), ha0_1]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, UInt64.toNat_toBitVec]
      change vi.toNat >>> 1 = _
      rw [Nat.shiftRight_eq_div_pow]; simp only [Nat.pow_one]
      have hvit : vi.toNat < 2 ^ 64 := vi.toBitVec.isLt
      rw [BitVec.toNat_ofNat, show (vi / 2).toNat = vi.toNat / 2 from rfl,
          Nat.mod_eq_of_lt (by omega : vi.toNat / 2 < 2 ^ 64)]
    have ht2_2 : st2.getReg AbiReg.t2 = BitVec.ofNat 64 (lm.arr64 (tierA a u)).size := by
      change (stepReg st1 AbiReg.t3 _ _).getReg AbiReg.t2 = _
      rw [getReg_stepReg_ne _ _ _ (by decide) _ _, ht2_1]
    have hlinkBr : lkm.linkSpec ((pHead ++ csrl) ++ [.br .bgeu AbiReg.t3 AbiReg.t2 errLabel] ++ ((cbase ++ ctail) ++ post)) =
        .ok (env.code, env.labels) := by
      simpa only [cbr, cbase, Asm.bgeu, List.append_assoc, List.cons_append, List.nil_append] using hlinkT
    have h64Br : 4 * (lkm.totalSize (pHead ++ csrl) + lkm.itemSize (.br .bgeu AbiReg.t3 AbiReg.t2 errLabel)) < 2 ^ 64 := by
      rw [htw2]
      have hbrsz : lkm.itemSize (.br .bgeu AbiReg.t3 AbiReg.t2 errLabel) = lkm.totalSize cbr := by
        simp [cbr, Asm.bgeu, lkm.totalSize_singleton]
      omega
    by_cases hbound : (vi / 2).toNat < (lm.arr64 (tierA a u)).size
    · have hbound' : vi.toNat / 2 < (lm.arr64 (tierA a u)).size := hbound
      have hevalE : _root_.L.evalE (.ld32t a t i) ⟨lm, loc⟩ =
          .ok (half32 ((lm.arr64 (tierA a u))[(vi / 2).toNat]) vi, ⟨lm, loc⟩) := by
        change (_root_.L.evalE t >>= fun u' => _root_.L.evalE i >>= fun idx => _root_.L.ld32 (tierA a u') idx) ⟨lm, loc⟩ = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hu]; dsimp only; rw [hvi]
        dsimp only [_root_.L.ld32, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind]
        simp [hbound', Pure.pure, Except.pure, Except.bind]; rfl
      rw [hevalE]
      have hcondF : evalBranch .bgeu (st2.getReg AbiReg.t3) (st2.getReg AbiReg.t2) = false := by
        have hdvlt : vi.toNat / 2 < 2 ^ 64 := by have := vi.toBitVec.isLt; omega
        simp [evalBranch, ht3_2, ht2_2]
        rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt hdvlt,
            Nat.mod_eq_of_lt (by omega : (lm.arr64 (tierA a u)).size < 2 ^ 64),
            decide_eq_true hbound']
      obtain ⟨kBr, st3, hrun3, hpc3', hoth3, hpres3, hmem3⟩ :=
        prog_step_br_fall env (pHead ++ csrl) ((cbase ++ ctail) ++ post)
          .bgeu AbiReg.t3 AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide)
          hlinkBr h64Br st2 hpc2 hcondF
      have htw3 : lkm.totalSize (pHead ++ csrl ++ cbr) = lkm.totalSize pHead + 1 + lkm.totalSize cbr := by
        rw [lkm.totalSize_append, htw2]
      have hpc3 : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pHead ++ csrl ++ cbr)) := by
        rw [hpc3', htw3, htw2, show cbr = [.br .bgeu AbiReg.t3 AbiReg.t2 errLabel] from rfl]
      have hbrEq : st3.getReg baseReg = st1.getReg baseReg := by
        rw [hoth3 baseReg hbr6]
        change (stepReg st1 AbiReg.t3 _ _).getReg baseReg = _
        exact getReg_stepReg_ne st1 AbiReg.t3 baseReg hbr3 _ _
      have halBase : isAligned (st3.getReg baseReg + BitVec.ofInt 64 off) 8 = true := by
        rw [hbrEq, haddrEq, Tab.base64_eq_nat]
        exact isAligned8_add_int_mul8 L.T L.hTAlign _
      obtain ⟨st4, hrun4, hoth4, ht1_4, hmem4, hpc4⟩ :=
        loadMemOff_ld_correct_lm lkm env.hrom (pHead ++ csrl ++ cbr) (ctail ++ post)
          AbiReg.t1 baseReg AbiReg.t3 (by decide) (by decide) hbr3 off
          (by simpa only [cbase, List.append_assoc] using hlinkT)
          (by rw [htw3]; change 4 * (lkm.totalSize pHead + 1 + lkm.totalSize cbr + lkm.totalSize cbase) < 2 ^ 64; change 4 * (lkm.totalSize pHead + (1 + lkm.totalSize cbr + lkm.totalSize cbase + 3)) < 2 ^ 64 at h64T; omega) st3 hpc3 halBase
      have hpres4 : PreservedRegs st3 st4 :=
        ⟨hoth4 _ (by decide) (by decide), hoth4 _ (by decide) (by decide),
         hoth4 _ (by decide) (by decide),
         hoth4 _ (by decide) (by decide)⟩
      let p4 := pHead ++ csrl ++ cbr ++ cbase
      have htw4 : lkm.totalSize p4 = lkm.totalSize pHead + 1 + lkm.totalSize cbr + lkm.totalSize cbase := by
        dsimp only [p4]; rw [lkm.totalSize_append, htw3]
      have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize p4) := by rw [htw4, ← htw3]; exact hpc4
      have hsSll := step_item_instr_lm lkm env.hrom p4
        ([Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3, Asm.lwu AbiReg.a0 AbiReg.t1 0#12] ++ post)
        (.shImm .slli AbiReg.t3 AbiReg.a0 2#6)
        (by simpa only [p4, ctail, cbase, Asm.slli, List.append_assoc, List.cons_append, List.nil_append] using hlinkT)
        (by rw [htw4]; change 4 * (lkm.totalSize pHead + (1 + lkm.totalSize cbr + lkm.totalSize cbase + 3)) < 2 ^ 64 at h64T; omega) st4 hpc4'
      let st5 := stepReg st4 AbiReg.t3 (st4.getReg AbiReg.a0 <<< 2) (st4.pc + 4#64)
      have hpres5 : PreservedRegs st4 st5 :=
        ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _⟩
      have htw5 : lkm.totalSize (p4 ++ [Asm.slli AbiReg.t3 AbiReg.a0 2#6]) = lkm.totalSize p4 + 1 := by
        rw [lkm.totalSize_append, Asm.slli, lkm.totalSize_instr]
      have hpc5 : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p4 ++ [Asm.slli AbiReg.t3 AbiReg.a0 2#6])) := by
        change st4.pc + 4#64 = _; rw [pc_add_4_ofNat st4.pc hpc4', htw5]
      have hsAdd := step_item_instr_lm lkm env.hrom (p4 ++ [Asm.slli AbiReg.t3 AbiReg.a0 2#6])
        ([Asm.lwu AbiReg.a0 AbiReg.t1 0#12] ++ post) (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.t3)
        (by simpa only [p4, ctail, cbase, Asm.add, Asm.slli, List.append_assoc, List.cons_append, List.nil_append] using hlinkT)
        (by rw [htw5, htw4]; change 4 * (lkm.totalSize pHead + (1 + lkm.totalSize cbr + lkm.totalSize cbase + 3)) < 2 ^ 64 at h64T; omega) st5 hpc5
      let st6 := stepReg st5 AbiReg.t1 (st5.getReg AbiReg.t1 + st5.getReg AbiReg.t3) (st5.pc + 4#64)
      have hpres6 : PreservedRegs st5 st6 :=
        ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _⟩
      have htw6 : lkm.totalSize (p4 ++ [Asm.slli AbiReg.t3 AbiReg.a0 2#6] ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3]) =
          lkm.totalSize p4 + 2 := by
        rw [lkm.totalSize_append, htw5, Asm.add, lkm.totalSize_instr]
      have hpc6 : st6.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p4 ++ [Asm.slli AbiReg.t3 AbiReg.a0 2#6] ++
          [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3])) := by
        change st5.pc + 4#64 = _; rw [pc_add_4_ofNat st5.pc hpc5, htw6, htw5]
      have ht1_6 : st6.getReg AbiReg.t1 = L.base64 (tierA a u) + BitVec.ofNat 64 (4 * vi.toNat) := by
        have ht1' : st4.getReg AbiReg.t1 = L.base64 (tierA a u) := by
          rw [ht1_4, hmem3, hbrEq, haddrEq]
          change readWord64 (stepReg st1 AbiReg.t3 _ _).mem _ = _
          rw [prog_stepReg_mem]; exact hbaseR
        have ha0' : st4.getReg AbiReg.a0 = vi.toBitVec := by
          rw [hoth4 AbiReg.a0 (by decide) (by decide), hoth3 _ (by decide)]
          change (stepReg st1 AbiReg.t3 _ _).getReg AbiReg.a0 = _
          rw [getReg_stepReg_ne _ _ _ (by decide) _ _, ha0_1]
        have hvi_lt : 4 * vi.toNat < 2 ^ 64 := by
          have : (vi / 2).toNat = vi.toNat / 2 := rfl; omega
        have ht3_5 : st5.getReg AbiReg.t3 = BitVec.ofNat 64 (4 * vi.toNat) := by
          change (stepReg st4 AbiReg.t3 _ _).getReg AbiReg.t3 = _
          rw [getReg_stepReg_eq _ _ (by decide), ha0']
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_shiftLeft, UInt64.toNat_toBitVec, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
          rw [show (2 ^ 2 : Nat) = 4 from rfl, Nat.mul_comm _ 4, Nat.mod_eq_of_lt hvi_lt]
        have ht1_5 : st5.getReg AbiReg.t1 = st4.getReg AbiReg.t1 :=
          getReg_stepReg_ne st4 AbiReg.t3 AbiReg.t1 (by decide) _ _
        change (stepReg st5 AbiReg.t1 _ _).getReg AbiReg.t1 = _
        rw [getReg_stepReg_eq _ _ (by decide), ht1_5, ht1', ht3_5]
      have hal6 : isAligned (st6.getReg AbiReg.t1 + sextImm12 0#12) 4 = true := by
        rw [show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero, ht1_6]
        exact isAligned4_add_mul4 (L.base64 (tierA a u)) (L.h64Align (tierA a u)) vi.toNat
      let st7 := stepReg st6 AbiReg.a0
        ((loadBytes st6.mem (st6.getReg AbiReg.t1 + sextImm12 0#12) 4).zeroExtend 64) (st6.pc + 4#64)
      obtain ⟨hrun7, hpc7, ha0_7, hoth7, hmem7⟩ :=
        step_lwu_off env (p4 ++ [Asm.slli AbiReg.t3 AbiReg.a0 2#6] ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3])
          post AbiReg.a0 AbiReg.t1 0#12 (by decide)
          (by simpa only [p4, ctail, cbase, Asm.lwu, Asm.raw, Asm.add, Asm.slli, List.append_assoc, List.cons_append, List.nil_append] using hlinkT)
          (by rw [htw6, htw4]; change 4 * (lkm.totalSize pHead + (1 + lkm.totalSize cbr + lkm.totalSize cbase + 3)) < 2 ^ 64 at h64T; omega) st6 hpc6 hal6
      have hpres7 : PreservedRegs st6 st7 :=
        ⟨hoth7 _ (by decide), hoth7 _ (by decide), hoth7 _ (by decide), hoth7 _ (by decide)⟩
      have hm6 : st6.mem = st1.mem := by
        dsimp only [st6, st5]; rw [prog_stepReg_mem, prog_stepReg_mem, hmem4, hmem3, prog_stepReg_mem]
      have ha0_7' : st7.getReg AbiReg.a0 =
          (half32 ((lm.arr64 (tierA a u))[(vi / 2).toNat]) vi).toBitVec := by
        rw [ha0_7, hm6, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero, ht1_6]
        have hw := hwordsR (vi / 2).toNat hbound
        have him : (vi % 2).toNat = vi.toNat % 2 := by
          rw [UInt64.toNat_mod, show (2 : UInt64).toNat = 2 from rfl]
        have hvi_lt : 4 * vi.toNat < 2 ^ 64 := by
          have : (vi / 2).toNat = vi.toNat / 2 := rfl; omega
        by_cases hmod : vi.toNat % 2 = 0
        · have heq0 : vi % 2 = 0 := uint64_eq_of_toNat (by simpa [him] using hmod)
          have h4eq : L.base64 (tierA a u) + BitVec.ofNat 64 (4 * vi.toNat) =
              L.base64 (tierA a u) + BitVec.ofNat 64 (8 * (vi / 2).toNat) := by
            congr 1; congr 1; have : (vi / 2).toNat = vi.toNat / 2 := rfl; omega
          rw [h4eq, loadBytes_zeroExtend32_lo _ _, hw]
          simp only [_root_.L.half32, heq0, ↓reduceIte]
          apply BitVec.eq_of_toNat_eq
          have hltw : ((lm.arr64 (tierA a u))[(vi / 2).toNat]).toNat < 2 ^ 64 :=
            ((lm.arr64 (tierA a u))[(vi / 2).toNat]).toBitVec.isLt
          simp only [UInt64.toNat_toBitVec]
          rw [UInt64.toNat_mod, UInt64.toNat_ofNat', UInt64.toNat_mod,
              show (4294967296 : UInt64).toNat = 2 ^ 32 from rfl, Nat.mod_eq_of_lt hltw]
        · have hmod1 : vi.toNat % 2 = 1 := by omega
          have hne0 : vi % 2 ≠ 0 := fun h0 => by
            have := congrArg UInt64.toNat h0
            rw [him, show (0 : UInt64).toNat = 0 from rfl] at this; omega
          have h4eq : L.base64 (tierA a u) + BitVec.ofNat 64 (4 * vi.toNat) =
              L.base64 (tierA a u) + BitVec.ofNat 64 (8 * (vi / 2).toNat) + 4#64 := by
            rw [BitVec.add_assoc]; congr 1
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (by omega : 8 * (vi / 2).toNat < 2 ^ 64),
                Nat.mod_eq_of_lt (by decide : 4 < 2 ^ 64), Nat.mod_eq_of_lt hvi_lt,
                Nat.mod_eq_of_lt (by omega)]
            have : (vi / 2).toNat = vi.toNat / 2 := rfl; omega
          rw [h4eq, loadBytes_zeroExtend32_hi _ _, hw]
          simp only [_root_.L.half32, hne0, ↓reduceIte]
          apply BitVec.eq_of_toNat_eq
          let w := (lm.arr64 (tierA a u))[(vi / 2).toNat]
          have hltw : w.toNat < 2 ^ 64 := w.toBitVec.isLt
          simp only [UInt64.toNat_toBitVec]
          change (UInt64.ofNat w.toNat).toNat >>> (UInt64.toNat 32 % 64) = (w / 4294967296).toNat
          rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hltw,
              show (32 : UInt64).toNat % 64 = 32 from rfl, Nat.shiftRight_eq_div_pow,
              UInt64.toNat_div, show (4294967296 : UInt64).toNat = 2 ^ 32 from rfl]
      refine ⟨1 + (kBr + (lkm.totalSize cbase + (1 + (1 + 1)))), st7, ?_, ?_, ha0_7',
        (hpres2.trans hpres3).trans (hpres4.trans (hpres5.trans (hpres6.trans hpres7))), ?_⟩
      · rw [run_add, run_one_cont _ _ st2 (by rw [hsSrl]; rfl)]; dsimp only
        rw [run_add, hrun3]; dsimp only
        rw [run_add, hrun4]; dsimp only
        rw [run_add, run_one_cont _ _ st5 (by rw [hsSll]; rfl)]; dsimp only
        rw [run_add, run_one_cont _ _ st6 (by rw [hsAdd]; rfl)]; dsimp only
        exact hrun7
      · rw [hpc7, htw6, htw4]; dsimp only [cbase]; congr 2; omega
      · rw [hmem7, hm6]
    · have hbound' : ¬(vi.toNat / 2 < (lm.arr64 (tierA a u)).size) := hbound
      have hevalE : _root_.L.evalE (.ld32t a t i) ⟨lm, loc⟩ = .error .oob := by
        change (_root_.L.evalE t >>= fun u' => _root_.L.evalE i >>= fun idx => _root_.L.ld32 (tierA a u') idx) ⟨lm, loc⟩ = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hu]; dsimp only; rw [hvi]
        dsimp only [_root_.L.ld32, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind]
        simp [hbound', Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Except.bind]; rfl
      rw [hevalE]
      have hcondT : evalBranch .bgeu (st2.getReg AbiReg.t3) (st2.getReg AbiReg.t2) = true := by
        have hdvlt : (vi / 2).toNat < 2 ^ 64 := by
          rw [← UInt64.toNat_toBitVec]; exact (vi / 2).toBitVec.isLt
        simp [evalBranch, ht3_2, ht2_2]
        rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            show vi.toNat / 2 = (vi / 2).toNat from rfl,
            Nat.mod_eq_of_lt hdvlt,
            Nat.mod_eq_of_lt (by omega : (lm.arr64 (tierA a u)).size < 2 ^ 64),
            decide_eq_false (by omega)]
      obtain ⟨kBr, st3, hrun3, hpc3', _, hpres3, hmem3⟩ :=
        prog_step_br_taken env (pHead ++ csrl) ((cbase ++ ctail) ++ post)
          .bgeu AbiReg.t3 AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide)
          hlinkBr h64Br st2 hpc2 hcondT
      refine ⟨1 + kBr, st3, ?_, hpc3', hpres2.trans hpres3, ?_⟩
      · rw [run_add, run_one_cont _ _ st2 (by rw [hsSrl]; rfl)]; dsimp only; exact hrun3
      · rw [hmem3]; dsimp only [st2]; exact prog_stepReg_mem st1 _ _ _
  cases htc : t.constVal? with
  | some w =>
    have hteq : t = .const w := expr_constVal_eq_some htc
    have hu : _root_.L.evalE t ⟨lm, loc⟩ = .ok (w, ⟨lm, loc⟩) := by rw [hteq]; rfl
    let s := tierA a w
    let ci := compileE env.tab nl tmp i
    let clen := loadMemOff .ld AbiReg.t2 AbiReg.gp AbiReg.t3 (env.tab.len64 s)
    let cbase := loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t3 (env.tab.base64 s)
    have hce : compileE env.tab nl tmp (.ld32t a t i) = ci ++ clen ++ csrl ++ cbr ++ cbase ++ ctail := by
      simp only [compileE, htc, s, ci, clen, csrl, cbr, cbase, ctail, List.append_assoc, List.cons_append, List.nil_append]
    have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.ld32t a t i)) =
        lkm.totalSize ci + lkm.totalSize clen + (1 + lkm.totalSize cbr + lkm.totalSize cbase + 3) := by
      rw [hce]; dsimp only [csrl, ctail]
      simp only [lkm.totalSize_append, lkm.totalSize_cons, lkm.totalSize_nil,
        Asm.srli, Asm.slli, Asm.add, Asm.lwu, lkm.itemSize_instr]; omega
    have ri := ihi pre ((clen ++ csrl ++ cbr ++ cbase ++ ctail) ++ post) tmp st (by omega)
      (by rw [show pre ++ ci ++ ((clen ++ csrl ++ cbr ++ cbase ++ ctail) ++ post) =
          pre ++ compileE env.tab nl tmp (.ld32t a t i) ++ post from by rw [hce]; simp only [List.append_assoc]]; exact hlink)
      (by rw [htw_ce] at h64; dsimp only [ci] at h64; omega) hpc hgp hsp hmemRel hframeOk
    rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
    · simp only [hvi] at ri
      obtain ⟨ki, st0, hrun0, hpc0, ha0_0, hpres0, heq0⟩ := ri
      have hrel0 := ProgMemRel.of_tempSpan env hlo hhi (by omega) heq0 hmemRel
      have hta := tierAddrOk_len64_addr_T L.T a w (tier32Ok_to_tierAddrOk ha hu)
      have htw0 : lkm.totalSize (pre ++ ci) = lkm.totalSize pre + lkm.totalSize ci := lkm.totalSize_append _ _
      have halLen : isAligned (st0.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.len64 s)) 8 = true := by
        rw [hpres0.gp.trans hgp, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
      obtain ⟨st1, hrunL, hothL, ht2_1, hmemL, hpc1⟩ :=
        loadMemOff_ld_correct_lm lkm env.hrom (pre ++ ci) ((csrl ++ cbr ++ cbase ++ ctail) ++ post)
          AbiReg.t2 AbiReg.gp AbiReg.t3 (by decide) (by decide) (by decide) (env.tab.len64 s)
          (by rw [show (pre ++ ci) ++ clen ++ ((csrl ++ cbr ++ cbase ++ ctail) ++ post) =
              pre ++ compileE env.tab nl tmp (.ld32t a t i) ++ post from by rw [hce]; simp only [List.append_assoc]]; exact hlink)
          (by rw [htw0]; rw [htw_ce] at h64; dsimp only [ci, clen] at h64 ⊢; omega) st0 (by rw [htw0]; exact hpc0) halLen
      have hpresL : PreservedRegs st0 st1 :=
        ⟨hothL _ (by decide) (by decide), hothL _ (by decide) (by decide),
         hothL _ (by decide) (by decide),
         hothL _ (by decide) (by decide)⟩
      have htw1 : lkm.totalSize (pre ++ ci ++ clen) = lkm.totalSize pre + lkm.totalSize ci + lkm.totalSize clen := by
        rw [lkm.totalSize_append, htw0]
      have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ci ++ clen)) := by
        rw [htw1, ← htw0]; exact hpc1
      have hrel1 : ProgMemRel env.tab L st1.mem lm := by rw [hmemL]; exact hrel0
      have rt := runTail (pre ++ ci ++ clen) AbiReg.gp (env.tab.base64 s) w vi st1
        (by decide) (by decide) hu hvi hrel1 hta.1
        (by rw [hpresL.gp.trans (hpres0.gp.trans hgp)])
        hpc1'
        (by rw [ht2_1, hpres0.gp.trans hgp, (hrel0.2.1 s hta.1).2.2.1])
        ((hothL _ (by decide) (by decide)).trans ha0_0)
        (by rw [show (pre ++ ci ++ clen) ++ csrl ++ cbr ++ cbase ++ ctail ++ post =
            pre ++ compileE env.tab nl tmp (.ld32t a t i) ++ post from by rw [hce]; simp only [List.append_assoc]]; exact hlink)
        (by rw [htw1]; rw [htw_ce] at h64; dsimp only [ci, clen, cbase] at h64 ⊢; omega)
      cases hev : _root_.L.evalE (.ld32t a t i) ⟨lm, loc⟩ with
      | ok res =>
        rw [hev] at rt; obtain ⟨kt, st', hrunT, hpc', ha0', hpresT, hmemT⟩ := rt
        exact ⟨ki + (lkm.totalSize clen + kt), st',
          by rw [run_add, hrun0]; dsimp only; rw [run_add, hrunL]; dsimp only; exact hrunT,
          by rw [hpc', htw1, htw_ce]; dsimp only [ci, clen, cbase]; congr 2; omega, ha0',
          (hpres0.trans hpresL).trans hpresT, by rw [hmemT, hmemL]; exact heq0⟩
      | error err =>
        rw [hev] at rt; obtain ⟨kt, st', hrunT, hpc', hpresT, hmemT⟩ := rt
        exact ⟨ki + (lkm.totalSize clen + kt), st',
          by rw [run_add, hrun0]; dsimp only; rw [run_add, hrunL]; dsimp only; exact hrunT,
          hpc', (hpres0.trans hpresL).trans hpresT, by rw [hmemT, hmemL]; exact heq0⟩
    · simp only [hvi] at ri
      have hevalE : _root_.L.evalE (.ld32t a t i) ⟨lm, loc⟩ = .error .oob := by
        simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hu, hvi]
      rw [hevalE]; exact ri
  | none =>
    let cpre := tieredHead env.tab nl tmp t i ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
       Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (env.tab.len64 (TieredArray.t0 a))
    let cbase := loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t3 (env.tab.base64 (TieredArray.t0 a))
    have hce : compileE env.tab nl tmp (.ld32t a t i) = cpre ++ csrl ++ cbr ++ cbase ++ ctail := by
      dsimp only [compileE]; rw [htc]
      cases hs : emitSimpleExpr env.tab AbiReg.t0 AbiReg.t1 t <;>
        simp only [cpre, tieredHead, hs, csrl, cbr, cbase, ctail, List.append_assoc, List.cons_append, List.nil_append]
    have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.ld32t a t i)) =
        lkm.totalSize cpre + (1 + lkm.totalSize cbr + lkm.totalSize cbase + 3) := by
      rw [hce]; dsimp only [csrl, ctail]
      simp only [lkm.totalSize_append, lkm.totalSize_cons, lkm.totalSize_nil,
        Asm.srli, Asm.slli, Asm.add, Asm.lwu, lkm.itemSize_instr]; omega
    have rb := prog_tiered_idx_bounds_sim env L lm loc hspAlign hlo hhi pre (csrl ++ cbr ++ cbase ++ ctail ++ post)
      tmp a t i ha htOk (by omega) (by omega) (by omega) iht ihi
      (by rw [show pre ++ cpre ++ (csrl ++ cbr ++ cbase ++ ctail ++ post) =
          pre ++ compileE env.tab nl tmp (.ld32t a t i) ++ post from by rw [hce]; simp only [List.append_assoc]]; exact hlink)
      (by rw [htw_ce] at h64; dsimp only [cpre] at h64 ⊢; omega) st hpc hgp hsp hmemRel hframeOk
    rcases _root_.L.evalE_pure t ⟨lm, loc⟩ with ⟨u, hu⟩ | hu
    · rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
      · simp only [hu, hvi] at rb
        obtain ⟨kp, st1, hrun1, hpc1, ht1_1, ht2_1, ha0_1, hpres1, heq1⟩ := rb
        have hrel1 := ProgMemRel.of_tempSpan env hlo hhi (by omega) heq1 hmemRel
        have hta := tierAddrOk_len64_addr_T L.T a u (tier32Ok_to_tierAddrOk ha hu)
        have htw1 : lkm.totalSize (pre ++ cpre) = lkm.totalSize pre + lkm.totalSize cpre := lkm.totalSize_append _ _
        have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ cpre)) := by
          rw [htw1]; dsimp only [cpre] at hpc1 ⊢; exact hpc1
        have rt := runTail (pre ++ cpre) AbiReg.t1 (env.tab.base64 (TieredArray.t0 a)) u vi st1
          (by decide) (by decide) hu hvi hrel1 hta.1 (by rw [ht1_1, hta.2.2]) hpc1' ht2_1 ha0_1
          (by rw [show (pre ++ cpre) ++ csrl ++ cbr ++ cbase ++ ctail ++ post =
              pre ++ compileE env.tab nl tmp (.ld32t a t i) ++ post from by rw [hce]; simp only [List.append_assoc]]; exact hlink)
          (by rw [htw1]; rw [htw_ce] at h64; dsimp only [cbase] at h64 ⊢; omega)
        cases hev : _root_.L.evalE (.ld32t a t i) ⟨lm, loc⟩ with
        | ok res =>
          rw [hev] at rt; obtain ⟨kt, st', hrunT, hpc', ha0', hpresT, hmemT⟩ := rt
          exact ⟨kp + kt, st', by rw [run_add, hrun1]; dsimp only; exact hrunT,
            by rw [hpc', htw1, htw_ce]; dsimp only [cbase]; congr 2; omega, ha0',
            hpres1.trans hpresT, by rw [hmemT]; exact heq1⟩
        | error err =>
          rw [hev] at rt; obtain ⟨kt, st', hrunT, hpc', hpresT, hmemT⟩ := rt
          exact ⟨kp + kt, st', by rw [run_add, hrun1]; dsimp only; exact hrunT,
            hpc', hpres1.trans hpresT, by rw [hmemT]; exact heq1⟩
      · simp only [hu, hvi] at rb
        have hevalE : _root_.L.evalE (.ld32t a t i) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hu, hvi]
        rw [hevalE]; exact rb
    · simp only [hu] at rb
      have hevalE : _root_.L.evalE (.ld32t a t i) ⟨lm, loc⟩ = .error .oob := by
        simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hu]
      rw [hevalE]; exact rb

def ld8x8SetupSrc (tab : Tab) (src : BSrc) : List AsmItem :=
  match src with
  | .arr a =>
    loadMemOff .ld AbiReg.t0 AbiReg.gp AbiReg.t2 (tab.len8 a) ++
    loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (tab.base8 a)
  | .rom d =>
    li AbiReg.t0 (BitVec.ofNat 64 d.length) ++
    addImmOff AbiReg.t1 AbiReg.gp AbiReg.t2 (tab.romBase + (romIdx d tab.rom : Int))

theorem prog_ld8x8_setup_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (p1 post1 : List AsmItem) (src : BSrc) (vi : _root_.L.Word)
    (hsrc : bsrcOkB env.tab src = true)
    (hlink : lkm.linkSpec (p1 ++ ld8x8SetupSrc env.tab src ++ post1) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize p1 + lkm.totalSize (ld8x8SetupSrc env.tab src)) < 2 ^ 64)
    (st1 : State) (hpc1 : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize p1))
    (hgp1 : st1.getReg AbiReg.gp = L.T) (ha0_1 : st1.getReg AbiReg.a0 = vi.toBitVec)
    (hrel1 : ProgMemRel env.tab L st1.mem lm) :
    ∃ k2 st2, RV64.run env.rom k2 st1 = .cont st2 ∧
      st2.pc = BitVec.ofNat 64 (4 * (lkm.totalSize p1 + lkm.totalSize (ld8x8SetupSrc env.tab src))) ∧
      st2.getReg AbiReg.t0 = BitVec.ofNat 64 (lm.src8 src).size ∧
      st2.getReg AbiReg.a0 = vi.toBitVec ∧
      (lm.src8 src).size < 2 ^ 64 ∧
      (∀ j (hj : j < (lm.src8 src).size),
        st2.mem (st2.getReg AbiReg.t1 + BitVec.ofNat 64 j) = (lm.src8 src)[j].toBitVec) ∧
      st2.mem = st1.mem ∧
      PreservedRegs st1 st2 := by
  cases src with
  | arr a =>
    dsimp only [bsrcOkB] at hsrc
    rcases hrel1.1 a hsrc with ⟨_, hlt64, hlenR, hbaseR, hbytesR⟩
    let sL := loadMemOff .ld AbiReg.t0 AbiReg.gp AbiReg.t2 (env.tab.len8 a)
    let sB := loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base8 a)
    have hsDef : ld8x8SetupSrc env.tab (.arr a) = sL ++ sB := rfl
    have htwS : lkm.totalSize (ld8x8SetupSrc env.tab (.arr a)) = lkm.totalSize sL + lkm.totalSize sB := by
      rw [hsDef, lkm.totalSize_append]
    have halL : isAligned (st1.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.len8 a)) 8 = true := by
      rw [hgp1, Tab.len8_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨stA, hrA, hoA, ht0A, hmA, hpcA⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom p1 (sB ++ post1)
        AbiReg.t0 AbiReg.gp AbiReg.t2 (by decide) (by decide) (by decide) (env.tab.len8 a)
        (by rw [show p1 ++ sL ++ (sB ++ post1) = p1 ++ ld8x8SetupSrc env.tab (.arr a) ++ post1 from by
            rw [hsDef]; simp only [List.append_assoc]]; exact hlink)
        (by dsimp only [sL] at htwS; rw [htwS] at h64; omega) st1 hpc1 halL
    have hpA : PreservedRegs st1 stA :=
      ⟨hoA _ (by decide) (by decide), hoA _ (by decide) (by decide),
       hoA _ (by decide) (by decide),
       hoA _ (by decide) (by decide)⟩
    have htwA : lkm.totalSize (p1 ++ sL) = lkm.totalSize p1 + lkm.totalSize sL := lkm.totalSize_append _ _
    have hpcA' : stA.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p1 ++ sL)) := by rw [htwA]; exact hpcA
    have halB : isAligned (stA.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.base8 a)) 8 = true := by
      rw [hpA.gp.trans hgp1, Tab.base8_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨stB, hrB, hoB, ht1B, hmB, hpcB⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom (p1 ++ sL) post1
        AbiReg.t1 AbiReg.gp AbiReg.t2 (by decide) (by decide) (by decide) (env.tab.base8 a)
        (by rw [show (p1 ++ sL) ++ sB ++ post1 = p1 ++ ld8x8SetupSrc env.tab (.arr a) ++ post1 from by
            rw [hsDef]; simp only [List.append_assoc]]; exact hlink)
        (by dsimp only [sL, sB] at htwS htwA ⊢; rw [htwA]; rw [htwS] at h64; omega) stA hpcA' halB
    have hpB : PreservedRegs stA stB :=
      ⟨hoB _ (by decide) (by decide), hoB _ (by decide) (by decide),
       hoB _ (by decide) (by decide),
       hoB _ (by decide) (by decide)⟩
    refine ⟨lkm.totalSize sL + lkm.totalSize sB, stB, ?_, ?_, ?_, ?_, hlt64, ?_, hmB.trans hmA, hpA.trans hpB⟩
    · rw [run_add, hrA]; exact hrB
    · rw [hpcB, htwA, htwS]; dsimp only [sL, sB]; congr 2; omega
    · rw [hoB AbiReg.t0 (by decide) (by decide), ht0A, hgp1, hlenR]; simp [_root_.L.Mem.src8]
    · rw [hoB AbiReg.a0 (by decide) (by decide), hoA AbiReg.a0 (by decide) (by decide), ha0_1]
    · intro j hj
      rw [hmB, hmA, ht1B, hmA, hpA.gp.trans hgp1, hbaseR]
      exact hbytesR j hj
  | rom d =>
    dsimp only [bsrcOkB] at hsrc
    have hromSpec := Tab.romSliceOk_spec hsrc
    have hrb := L.tab_rom_bound
    have hvT := L.hTValid
    have hdlt : d.length < 2 ^ 64 := by
      have hrb16 : 16 ≤ env.tab.romBase.toNat := by simp [Tab.romBase]; omega
      omega
    let sL := li AbiReg.t0 (BitVec.ofNat 64 d.length)
    let sB := addImmOff AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.romBase + (romIdx d env.tab.rom : Int))
    have hsDef : ld8x8SetupSrc env.tab (.rom d) = sL ++ sB := rfl
    have htwS : lkm.totalSize (ld8x8SetupSrc env.tab (.rom d)) = lkm.totalSize sL + lkm.totalSize sB := by
      rw [hsDef, lkm.totalSize_append]
    obtain ⟨stA, hrA, hoA, ht0A, hmA, hpcA⟩ :=
      li_correct_lm lkm env.hrom p1 (sB ++ post1) AbiReg.t0 (by decide) (BitVec.ofNat 64 d.length)
        (by rw [show p1 ++ sL ++ (sB ++ post1) = p1 ++ ld8x8SetupSrc env.tab (.rom d) ++ post1 from by
            rw [hsDef]; simp only [List.append_assoc]]; exact hlink)
        (by dsimp only [sL] at htwS; rw [htwS] at h64; omega) st1 hpc1
    have hpA : PreservedRegs st1 stA :=
      ⟨hoA _ (by decide), hoA _ (by decide), hoA _ (by decide), hoA _ (by decide)⟩
    have htwA : lkm.totalSize (p1 ++ sL) = lkm.totalSize p1 + lkm.totalSize sL := lkm.totalSize_append _ _
    have hpcA' : stA.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p1 ++ sL)) := by rw [htwA]; exact hpcA
    obtain ⟨stB, hrB, hoB, ht1B, hmB, hpcB⟩ :=
      addImmOff_correct_lm lkm env.hrom (p1 ++ sL) post1
        AbiReg.t1 AbiReg.gp AbiReg.t2 (by decide) (by decide) (by decide)
        (env.tab.romBase + (romIdx d env.tab.rom : Int))
        (by rw [show (p1 ++ sL) ++ sB ++ post1 = p1 ++ ld8x8SetupSrc env.tab (.rom d) ++ post1 from by
            rw [hsDef]; simp only [List.append_assoc]]; exact hlink)
        (by dsimp only [sL, sB] at htwS htwA ⊢; rw [htwA]; rw [htwS] at h64; omega) stA hpcA'
    have hpB : PreservedRegs stA stB :=
      ⟨hoB _ (by decide) (by decide), hoB _ (by decide) (by decide),
       hoB _ (by decide) (by decide),
       hoB _ (by decide) (by decide)⟩
    refine ⟨lkm.totalSize sL + lkm.totalSize sB, stB, ?_, ?_, ?_, ?_, by simpa [_root_.L.Mem.src8] using hdlt, ?_, hmB.trans hmA, hpA.trans hpB⟩
    · rw [run_add, hrA]; exact hrB
    · rw [hpcB, htwA, htwS]; dsimp only [sL, sB]; congr 2; omega
    · rw [hoB AbiReg.t0 (by decide) (by decide), ht0A]; simp [_root_.L.Mem.src8]
    · rw [hoB AbiReg.a0 (by decide) (by decide), hoA AbiReg.a0 (by decide), ha0_1]
    · intro j hj
      simp only [_root_.L.Mem.src8, List.size_toArray] at hj ⊢
      have hrb_nn : 0 ≤ env.tab.romBase := ProgLayout.romBase_nonneg env.tab
      have hcoe : (env.tab.romBase + (romIdx d env.tab.rom : Int)) =
          ((env.tab.romBase.toNat + romIdx d env.tab.rom : Nat) : Int) := by
        rw [← Int.toNat_of_nonneg hrb_nn]; push_cast; rfl
      rw [hmB, hmA, ht1B, hpA.gp.trans hgp1, hcoe]
      change st1.mem (L.T + BitVec.ofNat 64 (env.tab.romBase.toNat + romIdx d env.tab.rom) + BitVec.ofNat 64 j) = _
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc,
          hrel1.2.2.1 (romIdx d env.tab.rom + j) (by omega)]
      have hrom_eq := hromSpec.2 j hj
      rw [List.getElem?_eq_getElem (by omega : romIdx d env.tab.rom + j < env.tab.rom.length),
          Option.some.injEq] at hrom_eq
      rw [hrom_eq]; simp [List.getElem_toArray]

def ld8x8Mid : List AsmItem :=
  [Asm.addi AbiReg.t2 AbiReg.zero 8#12,
   Asm.bltu AbiReg.t0 AbiReg.t2 errLabel,
   Asm.addi AbiReg.t0 AbiReg.t0 (-8#12),
   Asm.bltu AbiReg.t0 AbiReg.a0 errLabel,
   Asm.add AbiReg.t1 AbiReg.t1 AbiReg.a0]

def ld8x8ReadBytes : List AsmItem :=
  [Asm.lbu AbiReg.a0 AbiReg.t1 7#12] ++
  ([6, 5, 4, 3, 2, 1, 0].flatMap fun k =>
    [Asm.lbu AbiReg.t2 AbiReg.t1 (BitVec.ofInt 12 (k : Int)),
     Asm.slli AbiReg.a0 AbiReg.a0 8#6,
     Asm.or AbiReg.a0 AbiReg.a0 AbiReg.t2])

theorem prog_ld8x8_tail_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (p2 post : List AsmItem) (bytes : Array UInt8) (vi : _root_.L.Word)
    (hlink : lkm.linkSpec (p2 ++ ld8x8Mid ++ ld8x8ReadBytes ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize p2 + (lkm.totalSize ld8x8Mid + 22)) < 2 ^ 64)
    (hlt64 : bytes.size < 2 ^ 64)
    (st2 : State) (hpc2 : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize p2))
    (ht0_2 : st2.getReg AbiReg.t0 = BitVec.ofNat 64 bytes.size)
    (ha0_2 : st2.getReg AbiReg.a0 = vi.toBitVec)
    (hbytes2 : ∀ j (hj : j < bytes.size),
      st2.mem (st2.getReg AbiReg.t1 + BitVec.ofNat 64 j) = bytes[j].toBitVec) :
    if _ : vi.toNat + 8 ≤ bytes.size then
      ∃ k st9, RV64.run env.rom k st2 = .cont st9 ∧
        st9.pc = BitVec.ofNat 64 (4 * (lkm.totalSize p2 + (lkm.totalSize ld8x8Mid + 22))) ∧
        st9.getReg AbiReg.a0 = (le64 bytes vi.toNat).toBitVec ∧
        PreservedRegs st2 st9 ∧ st9.mem = st2.mem
    else
      ∃ k st', RV64.run env.rom k st2 = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st2 st' ∧ st'.mem = st2.mem := by
  let i0 := Asm.addi AbiReg.t2 AbiReg.zero 8#12
  let i1 := Asm.bltu AbiReg.t0 AbiReg.t2 errLabel
  let i2 := Asm.addi AbiReg.t0 AbiReg.t0 (-8#12)
  let i3 := Asm.bltu AbiReg.t0 AbiReg.a0 errLabel
  let i4 := Asm.add AbiReg.t1 AbiReg.t1 AbiReg.a0
  have hcmid : ld8x8Mid = [i0, i1, i2, i3, i4] := rfl
  have hs0 := step_item_instr_lm lkm env.hrom p2 ([i1, i2, i3, i4] ++ ld8x8ReadBytes ++ post)
    (.aluImm .addi AbiReg.t2 AbiReg.zero 8#12)
    (by rw [show p2 ++ [AsmItem.instr (.aluImm .addi AbiReg.t2 AbiReg.zero 8#12)] ++
        ([i1, i2, i3, i4] ++ ld8x8ReadBytes ++ post) =
        p2 ++ ld8x8Mid ++ ld8x8ReadBytes ++ post from by
        rw [hcmid]; simp only [i0, Asm.addi, List.append_assoc, List.cons_append, List.nil_append]]; exact hlink)
    (by omega) st2 hpc2
  let st3 := stepReg st2 AbiReg.t2 (st2.getReg AbiReg.zero + sextImm12 8#12) (st2.pc + 4#64)
  have hpres3 : PreservedRegs st2 st3 :=
    ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
     getReg_stepReg_ne _ _ _ (by decide) _ _,
     getReg_stepReg_ne _ _ _ (by decide) _ _⟩
  have htw3 : lkm.totalSize (p2 ++ [i0]) = lkm.totalSize p2 + 1 := by
    rw [lkm.totalSize_append]; dsimp only [i0, Asm.addi]; rw [lkm.totalSize_instr]
  have hpc3 : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p2 ++ [i0])) := by
    change st2.pc + 4#64 = _; rw [pc_add_4_ofNat st2.pc hpc2, htw3]
  have ht2_3 : st3.getReg AbiReg.t2 = 8#64 := by
    change (stepReg st2 AbiReg.t2 _ _).getReg AbiReg.t2 = _
    rw [getReg_stepReg_eq _ _ (by decide), show st2.getReg AbiReg.zero = 0#64 from rfl, BitVec.zero_add]; rfl
  have ht0_3 : st3.getReg AbiReg.t0 = BitVec.ofNat 64 bytes.size := by
    change (stepReg st2 AbiReg.t2 _ _).getReg AbiReg.t0 = _
    rw [getReg_stepReg_ne _ _ _ (by decide) _ _, ht0_2]
  have ha0_3 : st3.getReg AbiReg.a0 = vi.toBitVec := by
    change (stepReg st2 AbiReg.t2 _ _).getReg AbiReg.a0 = _
    rw [getReg_stepReg_ne _ _ _ (by decide) _ _, ha0_2]
  have hlinkBr1 : lkm.linkSpec ((p2 ++ [i0]) ++ [.br .bltu AbiReg.t0 AbiReg.t2 errLabel] ++ ([i2, i3, i4] ++ ld8x8ReadBytes ++ post)) =
      .ok (env.code, env.labels) := by
    rw [show (p2 ++ [i0]) ++ [.br .bltu AbiReg.t0 AbiReg.t2 errLabel] ++ ([i2, i3, i4] ++ ld8x8ReadBytes ++ post) =
        p2 ++ ld8x8Mid ++ ld8x8ReadBytes ++ post from by
        rw [hcmid]; simp only [i1, Asm.bltu, List.append_assoc, List.cons_append, List.nil_append]]; exact hlink
  have hmidSz : lkm.totalSize ld8x8Mid = 3 + lkm.itemSize (.br .bltu AbiReg.t0 AbiReg.t2 errLabel) + lkm.itemSize (.br .bltu AbiReg.t0 AbiReg.a0 errLabel) := by
    rw [hcmid]; simp only [i0, i1, i2, i3, i4, Asm.addi, Asm.bltu, Asm.add,
      lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]; omega
  have h64Br1 : 4 * (lkm.totalSize (p2 ++ [i0]) + lkm.itemSize (.br .bltu AbiReg.t0 AbiReg.t2 errLabel)) < 2 ^ 64 := by
    rw [htw3]; omega
  by_cases hsz8 : 8 ≤ bytes.size
  · have hcond1F : evalBranch .bltu (st3.getReg AbiReg.t0) (st3.getReg AbiReg.t2) = false := by
      simp only [evalBranch, ht0_3, ht2_3, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64,
                 show (8 : Nat) % 2 ^ 64 = 8 from rfl, decide_eq_false_iff_not]; omega
    obtain ⟨kBr1, st4, hrunBr1, hpc4', hoth4, hpres4, hmem4⟩ :=
      prog_step_br_fall env (p2 ++ [i0]) ([i2, i3, i4] ++ ld8x8ReadBytes ++ post)
        .bltu AbiReg.t0 AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide)
        hlinkBr1 h64Br1 st3 hpc3 hcond1F
    have htw4 : lkm.totalSize (p2 ++ [i0, i1]) = lkm.totalSize (p2 ++ [i0]) + lkm.totalSize [i1] := by
      rw [show p2 ++ [i0, i1] = p2 ++ [i0] ++ [i1] from by simp, lkm.totalSize_append]
    have hpc4 : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p2 ++ [i0, i1])) := by
      rw [hpc4', htw4, show [i1] = [.br .bltu AbiReg.t0 AbiReg.t2 errLabel] from rfl]
    have hs2 := step_item_instr_lm lkm env.hrom (p2 ++ [i0, i1]) ([i3, i4] ++ ld8x8ReadBytes ++ post)
      (.aluImm .addi AbiReg.t0 AbiReg.t0 (-8#12))
      (by rw [show (p2 ++ [i0, i1]) ++ [AsmItem.instr (.aluImm .addi AbiReg.t0 AbiReg.t0 (-8#12))] ++
          ([i3, i4] ++ ld8x8ReadBytes ++ post) =
          p2 ++ ld8x8Mid ++ ld8x8ReadBytes ++ post from by
          rw [hcmid]; simp only [i2, Asm.addi, List.append_assoc, List.cons_append, List.nil_append]]; exact hlink)
      (by rw [htw4, htw3, show [i1] = [.br .bltu AbiReg.t0 AbiReg.t2 errLabel] from rfl, lkm.totalSize_singleton]; omega) st4 hpc4
    let st5 := stepReg st4 AbiReg.t0 (st4.getReg AbiReg.t0 + sextImm12 (-8#12)) (st4.pc + 4#64)
    have hpres5 : PreservedRegs st4 st5 :=
      ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
       getReg_stepReg_ne _ _ _ (by decide) _ _,
       getReg_stepReg_ne _ _ _ (by decide) _ _⟩
    have htw5 : lkm.totalSize (p2 ++ [i0, i1, i2]) = lkm.totalSize (p2 ++ [i0, i1]) + 1 := by
      rw [show p2 ++ [i0, i1, i2] = p2 ++ [i0, i1] ++ [i2] from by simp, lkm.totalSize_append]
      dsimp only [i2, Asm.addi]; rw [lkm.totalSize_instr]
    have hpc5 : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p2 ++ [i0, i1, i2])) := by
      change st4.pc + 4#64 = _; rw [pc_add_4_ofNat st4.pc hpc4, htw5]
    have ht0_5 : st5.getReg AbiReg.t0 = BitVec.ofNat 64 (bytes.size - 8) := by
      change (stepReg st4 AbiReg.t0 _ _).getReg AbiReg.t0 = _
      rw [getReg_stepReg_eq _ _ (by decide), hoth4 _ (by decide), ht0_3]
      apply BitVec.eq_of_toNat_eq
      have hneg8 : (sextImm12 (-8#12)).toNat = 2 ^ 64 - 8 := by decide
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hneg8,
          Nat.mod_eq_of_lt hlt64, Nat.mod_eq_of_lt (by omega : bytes.size - 8 < 2 ^ 64)]; omega
    have ha0_5 : st5.getReg AbiReg.a0 = vi.toBitVec := by
      change (stepReg st4 AbiReg.t0 _ _).getReg AbiReg.a0 = _
      rw [getReg_stepReg_ne _ _ _ (by decide) _ _, hoth4 _ (by decide)]; exact ha0_3
    have hlinkBr2 : lkm.linkSpec ((p2 ++ [i0, i1, i2]) ++ [.br .bltu AbiReg.t0 AbiReg.a0 errLabel] ++
        ([i4] ++ ld8x8ReadBytes ++ post)) = .ok (env.code, env.labels) := by
      rw [show (p2 ++ [i0, i1, i2]) ++ [.br .bltu AbiReg.t0 AbiReg.a0 errLabel] ++
          ([i4] ++ ld8x8ReadBytes ++ post) =
          p2 ++ ld8x8Mid ++ ld8x8ReadBytes ++ post from by
          rw [hcmid]; simp only [i3, Asm.bltu, List.append_assoc, List.cons_append, List.nil_append]]; exact hlink
    have h64Br2 : 4 * (lkm.totalSize (p2 ++ [i0, i1, i2]) + lkm.itemSize (.br .bltu AbiReg.t0 AbiReg.a0 errLabel)) < 2 ^ 64 := by
      rw [htw5, htw4, htw3, show [i1] = [.br .bltu AbiReg.t0 AbiReg.t2 errLabel] from rfl, lkm.totalSize_singleton]; omega
    by_cases hbound : vi.toNat + 8 ≤ bytes.size
    · simp only [hbound, ↓reduceDIte]
      have hcond2F : evalBranch .bltu (st5.getReg AbiReg.t0) (st5.getReg AbiReg.a0) = false := by
        simp only [evalBranch, ht0_5, ha0_5, BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
                   Nat.mod_eq_of_lt (by omega : bytes.size - 8 < 2 ^ 64), decide_eq_false_iff_not]; omega
      obtain ⟨kBr2, st6, hrunBr2, hpc6', hoth6, hpres6, hmem6⟩ :=
        prog_step_br_fall env (p2 ++ [i0, i1, i2]) ([i4] ++ ld8x8ReadBytes ++ post)
          .bltu AbiReg.t0 AbiReg.a0 errLabel env.errTarget env.herrLbl (by decide)
          hlinkBr2 h64Br2 st5 hpc5 hcond2F
      have htw6 : lkm.totalSize (p2 ++ [i0, i1, i2, i3]) = lkm.totalSize (p2 ++ [i0, i1, i2]) + lkm.totalSize [i3] := by
        rw [show p2 ++ [i0, i1, i2, i3] = p2 ++ [i0, i1, i2] ++ [i3] from by simp, lkm.totalSize_append]
      have hpc6 : st6.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p2 ++ [i0, i1, i2, i3])) := by
        rw [hpc6', htw6, show [i3] = [.br .bltu AbiReg.t0 AbiReg.a0 errLabel] from rfl]
      have hs4 := step_item_instr_lm lkm env.hrom (p2 ++ [i0, i1, i2, i3]) (ld8x8ReadBytes ++ post)
        (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.a0)
        (by rw [show (p2 ++ [i0, i1, i2, i3]) ++ [AsmItem.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.a0)] ++
            (ld8x8ReadBytes ++ post) =
            p2 ++ ld8x8Mid ++ ld8x8ReadBytes ++ post from by
            rw [hcmid]; simp only [i4, Asm.add, List.append_assoc, List.cons_append, List.nil_append]]; exact hlink)
        (by rw [htw6, htw5, htw4, htw3, show [i1] = [.br .bltu AbiReg.t0 AbiReg.t2 errLabel] from rfl,
                show [i3] = [.br .bltu AbiReg.t0 AbiReg.a0 errLabel] from rfl,
                lkm.totalSize_singleton, lkm.totalSize_singleton]; omega) st6 hpc6
      let st7 := stepReg st6 AbiReg.t1 (st6.getReg AbiReg.t1 + st6.getReg AbiReg.a0) (st6.pc + 4#64)
      have hpres7 : PreservedRegs st6 st7 :=
        ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _⟩
      have htw7 : lkm.totalSize (p2 ++ ld8x8Mid) = lkm.totalSize (p2 ++ [i0, i1, i2, i3]) + 1 := by
        rw [show p2 ++ ld8x8Mid = p2 ++ [i0, i1, i2, i3] ++ [i4] from by rw [hcmid]; simp, lkm.totalSize_append]
        dsimp only [i4, Asm.add]; rw [lkm.totalSize_instr]
      have htw7_eq : lkm.totalSize (p2 ++ ld8x8Mid) = lkm.totalSize p2 + lkm.totalSize ld8x8Mid :=
        lkm.totalSize_append p2 ld8x8Mid
      have h64_read : 4 * (lkm.totalSize (p2 ++ ld8x8Mid) + 22) < 2 ^ 64 := by
        rw [htw7_eq]; exact h64
      have hpc7 : st7.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p2 ++ ld8x8Mid)) := by
        change st6.pc + 4#64 = _; rw [pc_add_4_ofNat st6.pc hpc6, htw7]
      have ht1_7 : st7.getReg AbiReg.t1 = st2.getReg AbiReg.t1 + BitVec.ofNat 64 vi.toNat := by
        change (stepReg st6 AbiReg.t1 _ _).getReg AbiReg.t1 = _
        rw [getReg_stepReg_eq _ _ (by decide)]
        have ht1_6 : st6.getReg AbiReg.t1 = st2.getReg AbiReg.t1 := by
          rw [hoth6 _ (by decide)]
          change (stepReg st4 AbiReg.t0 _ _).getReg AbiReg.t1 = _
          rw [getReg_stepReg_ne _ _ _ (by decide) _ _, hoth4 _ (by decide)]
          change st3.getReg AbiReg.t1 = _
          change (stepReg st2 AbiReg.t2 _ _).getReg AbiReg.t1 = _
          rw [getReg_stepReg_ne _ _ _ (by decide) _ _]
        have ha0_6 : st6.getReg AbiReg.a0 = BitVec.ofNat 64 vi.toNat := by
          rw [hoth6 _ (by decide), ha0_5]
          apply BitVec.eq_of_toNat_eq; simp [UInt64.toNat_toBitVec]
        rw [ht1_6, ha0_6]
      have hmem7 : st7.mem = st2.mem := by
        dsimp only [st7]
        rw [prog_stepReg_mem, hmem6]; dsimp only [st5]
        rw [prog_stepReg_mem, hmem4]; dsimp only [st3]; rw [prog_stepReg_mem]
      have hmem_rb : ∀ j (hj : j < 8),
          st7.mem (st7.getReg AbiReg.t1 + BitVec.ofNat 64 j) = (bytes[vi.toNat + j]'(by omega)).toBitVec := by
        intro j hj
        rw [hmem7, ht1_7, BitVec.add_assoc, ← BitVec.ofNat_add]
        exact hbytes2 (vi.toNat + j) (by omega)
      obtain ⟨st9, hrun9, hpc9, ha0_9, hmem9, hpres9⟩ :=
        le64_8bytes_sim env (p2 ++ ld8x8Mid) post bytes vi.toNat hbound
          (by simpa only [ld8x8ReadBytes, List.append_assoc] using hlink)
          h64_read st7 hpc7 hmem_rb
      refine ⟨1 + (kBr1 + (1 + (kBr2 + (1 + 22)))), st9, ?_, ?_, ha0_9,
        (hpres3.trans hpres4).trans (hpres5.trans (hpres6.trans (hpres7.trans hpres9))), ?_⟩
      · rw [run_add, run_one_cont _ _ st3 (by rw [hs0]; rfl)]; dsimp only
        rw [run_add, hrunBr1]; dsimp only
        rw [run_add, run_one_cont _ _ st5 (by rw [hs2]; rfl)]; dsimp only
        rw [run_add, hrunBr2]; dsimp only
        rw [run_add, run_one_cont _ _ st7 (by rw [hs4]; rfl)]; dsimp only
        exact hrun9
      · rw [hpc9, htw7_eq, Nat.add_assoc]
      · rw [hmem9, hmem7]
    · simp only [hbound, ↓reduceDIte]
      have hcond2T : evalBranch .bltu (st5.getReg AbiReg.t0) (st5.getReg AbiReg.a0) = true := by
        simp only [evalBranch, ht0_5, ha0_5, BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
                   Nat.mod_eq_of_lt (by omega : bytes.size - 8 < 2 ^ 64), decide_eq_true_eq]; omega
      obtain ⟨kBr2, st6, hrunBr2, hpc6', _, hpres6, hmem6⟩ :=
        prog_step_br_taken env (p2 ++ [i0, i1, i2]) ([i4] ++ ld8x8ReadBytes ++ post)
          .bltu AbiReg.t0 AbiReg.a0 errLabel env.errTarget env.herrLbl (by decide)
          hlinkBr2 h64Br2 st5 hpc5 hcond2T
      refine ⟨1 + (kBr1 + (1 + kBr2)), st6, ?_, hpc6',
        ((hpres3.trans hpres4).trans hpres5).trans hpres6, ?_⟩
      · rw [run_add, run_one_cont _ _ st3 (by rw [hs0]; rfl)]; dsimp only
        rw [run_add, hrunBr1]; dsimp only
        rw [run_add, run_one_cont _ _ st5 (by rw [hs2]; rfl)]; dsimp only
        exact hrunBr2
      · rw [hmem6]; dsimp only [st5]; rw [prog_stepReg_mem, hmem4]; dsimp only [st3]; exact prog_stepReg_mem st2 _ _ _
  · have hbound : ¬(vi.toNat + 8 ≤ bytes.size) := by omega
    simp only [hbound, ↓reduceDIte]
    have hcond1T : evalBranch .bltu (st3.getReg AbiReg.t0) (st3.getReg AbiReg.t2) = true := by
      simp only [evalBranch, ht0_3, ht2_3, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64,
                 show (8 : Nat) % 2 ^ 64 = 8 from rfl, decide_eq_true_eq]; omega
    obtain ⟨kBr1, st4, hrunBr1, hpc4', _, hpres4, hmem4⟩ :=
      prog_step_br_taken env (p2 ++ [i0]) ([i2, i3, i4] ++ ld8x8ReadBytes ++ post)
        .bltu AbiReg.t0 AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide)
        hlinkBr1 h64Br1 st3 hpc3 hcond1T
    refine ⟨1 + kBr1, st4, ?_, hpc4', hpres3.trans hpres4, ?_⟩
    · rw [run_add, run_one_cont _ _ st3 (by rw [hs0]; rfl)]; dsimp only
      exact hrunBr1
    · rw [hmem4]; dsimp only [st3]; exact prog_stepReg_mem st2 _ _ _

theorem prog_ld8x8_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (lm : _root_.L.Mem) (loc : _root_.L.Locals)
    {sp : BitVec 64} {nl nt : Nat}
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (pre post : List AsmItem) (tmp : Nat) (src : BSrc) (i : Expr)
    (hsrc : bsrcOkB env.tab src = true)
    (htmp : tmp + maxTempsExpr i ≤ nt)
    (ihi : ∀ (pre post : List AsmItem) (tmp : Nat) (st : State),
      tmp + maxTempsExpr i ≤ nt →
      lkm.linkSpec (pre ++ compileE env.tab nl tmp i ++ post) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → st.getReg AbiReg.sp = sp →
      ProgMemRel env.tab L st.mem lm → ProgFrameOk L sp st.mem nl loc →
      match _root_.L.evalE i ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i))) ∧
          st'.getReg AbiReg.a0 = v.toBitVec ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem)
    (hlink : lkm.linkSpec (pre ++ compileE env.tab nl tmp (.ld8x8 src i) ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp (.ld8x8 src i))) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOk L sp st.mem nl loc) :
    match _root_.L.evalE (.ld8x8 src i) ⟨lm, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp (.ld8x8 src i)))) ∧
        st'.getReg AbiReg.a0 = v.toBitVec ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem := by
  let setupSrc := ld8x8SetupSrc env.tab src
  let ci := compileE env.tab nl tmp i
  have hce : compileE env.tab nl tmp (.ld8x8 src i) = ci ++ setupSrc ++ ld8x8Mid ++ ld8x8ReadBytes := by
    cases src <;> simp only [compileE, ci, setupSrc, ld8x8SetupSrc, ld8x8Mid, ld8x8ReadBytes, List.append_assoc] <;> rfl
  have htw_rb : lkm.totalSize ld8x8ReadBytes = 22 := by
    simp only [ld8x8ReadBytes, lkm.totalSize_append, Asm.lbu, lkm.totalSize_instr,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    simp only [lkm.totalSize_cons, lkm.totalSize_nil, Asm.slli, Asm.or, lkm.itemSize_instr]
  have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.ld8x8 src i)) =
      lkm.totalSize (compileE env.tab nl tmp i) + lkm.totalSize setupSrc + (lkm.totalSize ld8x8Mid + 22) := by
    rw [hce]; dsimp only [ci]; simp only [lkm.totalSize_append, htw_rb]; omega
  have ri := ihi pre ((setupSrc ++ ld8x8Mid ++ ld8x8ReadBytes) ++ post) tmp st htmp
    (by rw [show pre ++ ci ++ ((setupSrc ++ ld8x8Mid ++ ld8x8ReadBytes) ++ post) =
        pre ++ compileE env.tab nl tmp (.ld8x8 src i) ++ post from by rw [hce]; simp only [List.append_assoc]]; exact hlink)
    (by rw [htw_ce] at h64; omega) hpc hgp hsp hmemRel hframeOk
  rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
  · simp only [hvi] at ri
    obtain ⟨ki, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ri
    have hrel1 := ProgMemRel.of_tempSpan env hlo hhi (by omega) heq1 hmemRel
    have htw1 : lkm.totalSize (pre ++ ci) = lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i) :=
      lkm.totalSize_append _ _
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ci)) := by rw [htw1]; exact hpc1
    obtain ⟨k2, st2, hrun2, hpc2, ht0_2, ha0_2, hlt64, hbytes2, hmem2, hpres2⟩ :=
      prog_ld8x8_setup_sim env L lm (pre ++ ci) ((ld8x8Mid ++ ld8x8ReadBytes) ++ post) src vi hsrc
        (by rw [show (pre ++ ci) ++ ld8x8SetupSrc env.tab src ++ ((ld8x8Mid ++ ld8x8ReadBytes) ++ post) =
            pre ++ compileE env.tab nl tmp (.ld8x8 src i) ++ post from by
            rw [hce]; simp only [setupSrc, List.append_assoc]]; exact hlink)
        (by rw [htw1]; rw [htw_ce] at h64; dsimp only [setupSrc] at h64; omega)
        st1 hpc1' (hpres1.gp.trans hgp) ha0_1 hrel1
    have htw2 : lkm.totalSize (pre ++ ci ++ setupSrc) =
        lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp i) + lkm.totalSize setupSrc := by
      rw [lkm.totalSize_append, htw1]
    have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ci ++ setupSrc)) := by
      rw [htw2, ← htw1]; exact hpc2
    let p2 := pre ++ ci ++ setupSrc
    have rtail := prog_ld8x8_tail_sim env p2 post (lm.src8 src) vi
      (by rw [show p2 ++ ld8x8Mid ++ ld8x8ReadBytes ++ post =
          pre ++ compileE env.tab nl tmp (.ld8x8 src i) ++ post from by
          rw [hce]; simp only [p2, List.append_assoc]]; exact hlink)
      (by rw [htw2]; rw [htw_ce] at h64; omega) hlt64 st2 hpc2' ht0_2 ha0_2 hbytes2
    by_cases hbound : vi.toNat + 8 ≤ (lm.src8 src).size
    · simp only [hbound, ↓reduceDIte] at rtail
      obtain ⟨k3, st9, hrun3, hpc9, ha0_9, hpres3, hmem9⟩ := rtail
      have hevalE : _root_.L.evalE (.ld8x8 src i) ⟨lm, loc⟩ =
          .ok (le64 (lm.src8 src) vi.toNat, ⟨lm, loc⟩) := by
        change (_root_.L.evalE i >>= fun idx => _root_.L.ld8x8 src idx) ⟨lm, loc⟩ = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hvi]
        dsimp only [_root_.L.ld8x8, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
          Pure.pure, StateT.pure, Except.pure, Except.bind]
        simp [hbound]; rfl
      rw [hevalE]
      refine ⟨ki + (k2 + k3), st9, ?_, ?_, ha0_9, hpres1.trans (hpres2.trans hpres3), ?_⟩
      · rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3
      · rw [hpc9, htw2, htw_ce]; rw [Nat.add_assoc (lkm.totalSize pre), Nat.add_assoc (lkm.totalSize pre)]
      · rw [hmem9, hmem2]; exact heq1
    · simp only [hbound, ↓reduceDIte] at rtail
      obtain ⟨k3, st3, hrun3, hpc3, hpres3, hmem3⟩ := rtail
      have hevalE : _root_.L.evalE (.ld8x8 src i) ⟨lm, loc⟩ = .error .oob := by
        change (_root_.L.evalE i >>= fun idx => _root_.L.ld8x8 src idx) ⟨lm, loc⟩ = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hvi]
        dsimp only [_root_.L.ld8x8, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
          Pure.pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.pure, Except.bind]
        simp [hbound]; rfl
      rw [hevalE]
      refine ⟨ki + (k2 + k3), st3, ?_, hpc3, hpres1.trans (hpres2.trans hpres3), ?_⟩
      · rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3
      · rw [hmem3, hmem2]; exact heq1
  · simp only [hvi] at ri
    have hevalE : _root_.L.evalE (.ld8x8 src i) ⟨lm, loc⟩ = .error .oob := by
      simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hvi]
    rw [hevalE]; exact ri

/-- General forward simulation for ALL 15 `_root_.L.Expr` constructors. -/
theorem progEvalExpr_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals)
    {sp : BitVec 64} {nl nt : Nat}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (e : Expr) (pre post : List AsmItem) (tmp : Nat)
    (heOk : exprOkB env.tab nl e = true) (hTmp : tmp + maxTempsExpr e ≤ nt)
    (hlink : lkm.linkSpec (pre ++ compileE env.tab nl tmp e ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp e)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOk L sp st.mem nl loc) :
    match _root_.L.evalE e ⟨lm, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp e))) ∧
        st'.getReg AbiReg.a0 = v.toBitVec ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem := by
  induction e generalizing pre post tmp st with
  | const w =>
    simp only [_root_.L.evalE, Pure.pure, StateT.pure, Except.pure, compileE]
    obtain ⟨st', hrun, hoth, ha0, hmem, hpc'⟩ :=
      li_correct_lm lkm env.hrom pre post AbiReg.a0 (by decide) (BitVec.ofNat 64 w.toNat) hlink h64 st hpc
    refine ⟨lkm.totalSize (li AbiReg.a0 (BitVec.ofNat 64 w.toNat)), st', hrun, hpc', ?_,
      ⟨hoth _ (by decide), hoth _ (by decide), hoth _ (by decide), hoth _ (by decide)⟩,
      by rw [hmem]; exact MemEqOutside.refl _ _⟩
    rw [ha0]; apply BitVec.eq_of_toNat_eq; simp [UInt64.toNat_toBitVec]
  | var x =>
    simp only [exprOkB, decide_eq_true_eq] at heOk
    simp only [_root_.L.evalE, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
      Pure.pure, StateT.pure, Except.bind, Except.pure, compileE]
    have hal : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff x)) 8 = true := by
      rw [hsp, slotOff_ofInt]; exact isAligned8_add_int_mul8 sp hspAlign _
    obtain ⟨st', hrun, hoth, ha0, hmem, hpc'⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom pre post AbiReg.a0 AbiReg.sp AbiReg.t0
        (by decide) (by decide) (by decide) (slotOff x) hlink h64 st hpc hal
    refine ⟨lkm.totalSize (loadMemOff .ld AbiReg.a0 AbiReg.sp AbiReg.t0 (slotOff x)), st',
      hrun, hpc', ?_,
      ⟨hoth _ (by decide) (by decide), hoth _ (by decide) (by decide),
       hoth _ (by decide) (by decide),
       hoth _ (by decide) (by decide)⟩,
      by rw [hmem]; exact MemEqOutside.refl _ _⟩
    rw [ha0, hsp, hframeOk x heOk]
  | len8 a =>
    simp only [exprOkB] at heOk
    simp only [_root_.L.evalE, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
      Pure.pure, StateT.pure, Except.bind, Except.pure, compileE]
    have hal : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.len8 a)) 8 = true := by
      rw [hgp, Tab.len8_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨st', hrun, hoth, ha0, hmem, hpc'⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom pre post AbiReg.a0 AbiReg.gp AbiReg.t0
        (by decide) (by decide) (by decide) (env.tab.len8 a) hlink h64 st hpc hal
    refine ⟨lkm.totalSize (loadMemOff .ld AbiReg.a0 AbiReg.gp AbiReg.t0 (env.tab.len8 a)), st',
      hrun, hpc', ?_,
      ⟨hoth _ (by decide) (by decide), hoth _ (by decide) (by decide),
       hoth _ (by decide) (by decide),
       hoth _ (by decide) (by decide)⟩,
      by rw [hmem]; exact MemEqOutside.refl _ _⟩
    rw [ha0, hgp, (hmemRel.1 a heOk).2.2.1]; rfl
  | len64 a =>
    simp only [exprOkB] at heOk
    simp only [_root_.L.evalE, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
      Pure.pure, StateT.pure, Except.bind, Except.pure, compileE]
    have hal : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.len64 (TieredArray.t0 a))) 8 = true := by
      rw [hgp, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨st', hrun, hoth, ha0, hmem, hpc'⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom pre post AbiReg.a0 AbiReg.gp AbiReg.t0
        (by decide) (by decide) (by decide) (env.tab.len64 (TieredArray.t0 a)) hlink h64 st hpc hal
    refine ⟨lkm.totalSize (loadMemOff .ld AbiReg.a0 AbiReg.gp AbiReg.t0 (env.tab.len64 (TieredArray.t0 a))), st',
      hrun, hpc', ?_,
      ⟨hoth _ (by decide) (by decide), hoth _ (by decide) (by decide),
       hoth _ (by decide) (by decide),
       hoth _ (by decide) (by decide)⟩,
      by rw [hmem]; exact MemEqOutside.refl _ _⟩
    rw [ha0, hgp, (hmemRel.2.1 (TieredArray.t0 a) heOk).2.2.1]; rfl
  | glob g =>
    simp only [exprOkB, decide_eq_true_eq] at heOk
    simp only [_root_.L.evalE, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
      Pure.pure, StateT.pure, Except.bind, Except.pure, compileE]
    have hal : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.globOff g)) 8 = true := by
      rw [hgp, Tab.globOff_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨st', hrun, hoth, ha0, hmem, hpc'⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom pre post AbiReg.a0 AbiReg.gp AbiReg.t0
        (by decide) (by decide) (by decide) (env.tab.globOff g) hlink h64 st hpc hal
    refine ⟨lkm.totalSize (loadMemOff .ld AbiReg.a0 AbiReg.gp AbiReg.t0 (env.tab.globOff g)), st',
      hrun, hpc', ?_,
      ⟨hoth _ (by decide) (by decide), hoth _ (by decide) (by decide),
       hoth _ (by decide) (by decide),
       hoth _ (by decide) (by decide)⟩,
      by rw [hmem]; exact MemEqOutside.refl _ _⟩
    rw [ha0, hgp, hmemRel.2.2.2 g heOk]
  | bin op a b iha ihb =>
    simp only [exprOkB, Bool.and_eq_true] at heOk
    dsimp only [maxTempsExpr] at hTmp
    have hcomm : ∀ (va vb : _root_.L.Word),
        (op = .add ∨ op = .and ∨ op = .or ∨ op = .xor ∨ op = .mul ∨ op = .mulhi) →
        op.eval va vb = op.eval vb va := by
      intro va vb hop
      rcases hop with rfl | rfl | rfl | rfl | rfl | rfl
      · exact UInt64.add_comm va vb
      · apply UInt64.eq_of_toBitVec_eq; simp only [BinOp.eval, UInt64.toBitVec_and, BitVec.and_comm]
      · apply UInt64.eq_of_toBitVec_eq; simp only [BinOp.eval, UInt64.toBitVec_or, BitVec.or_comm]
      · apply UInt64.eq_of_toBitVec_eq; simp only [BinOp.eval, UInt64.toBitVec_xor, BitVec.xor_comm]
      · exact UInt64.mul_comm va vb
      · apply UInt64.eq_of_toBitVec_eq
        rw [← (mul_lo_hi_toNat va vb).2, ← (mul_lo_hi_toNat vb va).2, Nat.mul_comm va.toBitVec.toNat vb.toBitVec.toNat]
    cases hbc : b.constVal? with
    | some w =>
      have hbeq : b = .const w := expr_constVal_eq_some hbc
      have hce : compileE env.tab nl tmp (.bin op a b) = compileE env.tab nl tmp a ++ emitBinConstRhs op w := by
        simp only [compileE, hbc]
      have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.bin op a b)) =
          lkm.totalSize (compileE env.tab nl tmp a) + lkm.totalSize (emitBinConstRhs op w) := by
        rw [hce, lkm.totalSize_append]
      have ra := iha pre (emitBinConstRhs op w ++ post) tmp heOk.1 (by omega)
        (by rw [show pre ++ compileE env.tab nl tmp a ++ (emitBinConstRhs op w ++ post) =
            pre ++ compileE env.tab nl tmp (.bin op a b) ++ post from by rw [hce]; simp only [List.append_assoc]]; exact hlink)
        (by rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
      rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va, hva⟩ | hva
      · simp only [hva] at ra
        obtain ⟨ka, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ra
        have hvb : _root_.L.evalE b ⟨lm, loc⟩ = .ok (w, ⟨lm, loc⟩) := by rw [hbeq]; rfl
        have heval : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .ok (op.eval va w, ⟨lm, loc⟩) := by
          simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
        rw [heval]
        have htw1 : lkm.totalSize (pre ++ compileE env.tab nl tmp a) =
            lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp a) := lkm.totalSize_append _ _
        obtain ⟨k2, st2, hrun2, hpc2, ha0_2, hpres2, hmem2⟩ :=
          emitBinConstRhs_sim_lm lkm env (pre ++ compileE env.tab nl tmp a) post op w va st1
            (by rw [show (pre ++ compileE env.tab nl tmp a) ++ emitBinConstRhs op w ++ post =
                pre ++ compileE env.tab nl tmp (.bin op a b) ++ post from by rw [hce]; simp only [List.append_assoc]]; exact hlink)
            (by rw [htw1, Nat.add_assoc, ← htw_ce]; exact h64)
            (by rw [htw1]; exact hpc1) ha0_1
        exact ⟨ka + k2, st2, by rw [run_add, hrun1]; exact hrun2,
          by rw [hpc2, htw1, Nat.add_assoc, ← htw_ce], ha0_2, hpres1.trans hpres2,
          by rw [hmem2]; exact heq1⟩
      · simp only [hva] at ra
        have heval : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva]
        rw [heval]; exact ra
    | none =>
      cases hac : a.constVal? with
      | some w =>
        have haeq : a = .const w := expr_constVal_eq_some hac
        have hva : _root_.L.evalE a ⟨lm, loc⟩ = .ok (w, ⟨lm, loc⟩) := by rw [haeq]; rfl
        have runComm : (hop : op = .add ∨ op = .and ∨ op = .or ∨ op = .xor ∨ op = .mul ∨ op = .mulhi) →
            (hce : compileE env.tab nl tmp (.bin op a b) = compileE env.tab nl tmp b ++ emitBinConstRhs op w) →
            match _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ with
            | .ok (v, _) =>
              ∃ k st', RV64.run env.rom k st = .cont st' ∧
                st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp (.bin op a b)))) ∧
                st'.getReg AbiReg.a0 = v.toBitVec ∧ PreservedRegs st st' ∧
                MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
            | .error _ =>
              ∃ k st', RV64.run env.rom k st = .cont st' ∧
                st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧ PreservedRegs st st' ∧
                MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem := by
          intro hop hce
          have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.bin op a b)) =
              lkm.totalSize (compileE env.tab nl tmp b) + lkm.totalSize (emitBinConstRhs op w) := by
            rw [hce, lkm.totalSize_append]
          have rb := ihb pre (emitBinConstRhs op w ++ post) tmp heOk.2 (by omega)
            (by rw [show pre ++ compileE env.tab nl tmp b ++ (emitBinConstRhs op w ++ post) =
                pre ++ compileE env.tab nl tmp (.bin op a b) ++ post from by rw [hce]; simp only [List.append_assoc]]; exact hlink)
            (by rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
          rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
          · simp only [hvb] at rb
            obtain ⟨kb, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := rb
            have heval : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .ok (op.eval w vb, ⟨lm, loc⟩) := by
              simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
            rw [heval]
            have htw1 : lkm.totalSize (pre ++ compileE env.tab nl tmp b) =
                lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp b) := lkm.totalSize_append _ _
            obtain ⟨k2, st2, hrun2, hpc2, ha0_2, hpres2, hmem2⟩ :=
              emitBinConstRhs_sim_lm lkm env (pre ++ compileE env.tab nl tmp b) post op w vb st1
                (by rw [show (pre ++ compileE env.tab nl tmp b) ++ emitBinConstRhs op w ++ post =
                    pre ++ compileE env.tab nl tmp (.bin op a b) ++ post from by rw [hce]; simp only [List.append_assoc]]; exact hlink)
                (by rw [htw1, Nat.add_assoc, ← htw_ce]; exact h64)
                (by rw [htw1]; exact hpc1) ha0_1
            exact ⟨kb + k2, st2, by rw [run_add, hrun1]; exact hrun2,
              by rw [hpc2, htw1, Nat.add_assoc, ← htw_ce],
              by rw [ha0_2, hcomm vb w hop], hpres1.trans hpres2, by rw [hmem2]; exact heq1⟩
          · simp only [hvb] at rb
            have heval : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .error .oob := by
              simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb]
            rw [heval]; exact rb
        have runLiBin : (hce : compileE env.tab nl tmp (.bin op a b) =
              compileE env.tab nl tmp b ++ li AbiReg.t0 w.toBitVec ++ [emitBinOp op AbiReg.a0 AbiReg.t0 AbiReg.a0]) →
            match _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ with
            | .ok (v, _) =>
              ∃ k st', RV64.run env.rom k st = .cont st' ∧
                st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp (.bin op a b)))) ∧
                st'.getReg AbiReg.a0 = v.toBitVec ∧ PreservedRegs st st' ∧
                MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
            | .error _ =>
              ∃ k st', RV64.run env.rom k st = .cont st' ∧
                st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧ PreservedRegs st st' ∧
                MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem := by
          intro hce
          have htw_op : lkm.totalSize [emitBinOp op AbiReg.a0 AbiReg.t0 AbiReg.a0] = 1 := by
            cases op <;> simp only [emitBinOp, Asm.add, Asm.sub, Asm.and, Asm.or, Asm.xor, Asm.sll, Asm.srl, Asm.mul, Asm.mulhu, lkm.totalSize_instr]
          have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.bin op a b)) =
              lkm.totalSize (compileE env.tab nl tmp b) + lkm.totalSize (li AbiReg.t0 w.toBitVec) + 1 := by
            rw [hce, lkm.totalSize_append, lkm.totalSize_append, htw_op]
          have rb := ihb pre (li AbiReg.t0 w.toBitVec ++ [emitBinOp op AbiReg.a0 AbiReg.t0 AbiReg.a0] ++ post)
            tmp heOk.2 (by omega)
            (by simpa only [hce, List.append_assoc] using hlink)
            (by rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
          rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
          · simp only [hvb] at rb
            obtain ⟨kb, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := rb
            have heval : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .ok (op.eval w vb, ⟨lm, loc⟩) := by
              simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
            rw [heval]
            have htw1 : lkm.totalSize (pre ++ compileE env.tab nl tmp b) =
                lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp b) := lkm.totalSize_append _ _
            obtain ⟨st2, hrun2, hoth2, ht0_2, hmem2, hpc2⟩ :=
              li_correct_lm lkm env.hrom (pre ++ compileE env.tab nl tmp b)
                ([emitBinOp op AbiReg.a0 AbiReg.t0 AbiReg.a0] ++ post)
                AbiReg.t0 (by decide) w.toBitVec
                (by simpa only [hce, List.append_assoc] using hlink)
                (by rw [htw1]; rw [htw_ce] at h64; omega) st1 (by rw [htw1]; exact hpc1)
            have hpres2 : PreservedRegs st1 st2 :=
              ⟨hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide)⟩
            have htw2 : lkm.totalSize (pre ++ compileE env.tab nl tmp b ++ li AbiReg.t0 w.toBitVec) =
                lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp b) + lkm.totalSize (li AbiReg.t0 w.toBitVec) := by
              rw [lkm.totalSize_append, htw1]
            obtain ⟨st3, hrun3, hpc3, ha0_3, hoth3, hmem3⟩ :=
              emitBinOp_step_lm lkm env (pre ++ compileE env.tab nl tmp b ++ li AbiReg.t0 w.toBitVec) post
                op AbiReg.a0 AbiReg.t0 AbiReg.a0 (by decide) w vb st2
                (by simpa only [hce, List.append_assoc] using hlink)
                (by rw [htw2]; rw [htw_ce] at h64; omega)
                (by rw [htw2, ← htw1]; exact hpc2) ht0_2 ((hoth2 _ (by decide)).trans ha0_1)
            have hpres3 : PreservedRegs st2 st3 :=
              ⟨hoth3 _ (by decide), hoth3 _ (by decide), hoth3 _ (by decide), hoth3 _ (by decide)⟩
            exact ⟨kb + (lkm.totalSize (li AbiReg.t0 w.toBitVec) + 1), st3,
              by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
              by rw [hpc3, htw2, htw_ce]; congr 2; omega, ha0_3,
              (hpres1.trans hpres2).trans hpres3, by rw [hmem3, hmem2]; exact heq1⟩
          · simp only [hvb] at rb
            have heval : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .error .oob := by
              simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb]
            rw [heval]; exact rb
        cases op with
        | add => exact runComm (Or.inl rfl) (by simp only [compileE, hbc, hac])
        | and => exact runComm (Or.inr (Or.inl rfl)) (by simp only [compileE, hbc, hac])
        | or  => exact runComm (Or.inr (Or.inr (Or.inl rfl))) (by simp only [compileE, hbc, hac])
        | xor => exact runComm (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by simp only [compileE, hbc, hac])
        | mul => exact runComm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (by simp only [compileE, hbc, hac])
        | mulhi => exact runComm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) (by simp only [compileE, hbc, hac])
        | sub =>
          by_cases hw0 : w = 0
          · subst hw0
            have hce : compileE env.tab nl tmp (.bin .sub a b) =
                compileE env.tab nl tmp b ++ [Asm.sub AbiReg.a0 AbiReg.zero AbiReg.a0] := by
              simp only [compileE, hbc, hac, beq_self_eq_true, ↓reduceIte]
            have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.bin .sub a b)) =
                lkm.totalSize (compileE env.tab nl tmp b) + 1 := by
              rw [hce, lkm.totalSize_append, Asm.sub, lkm.totalSize_instr]
            have rb := ihb pre ([Asm.sub AbiReg.a0 AbiReg.zero AbiReg.a0] ++ post) tmp heOk.2 (by omega)
              (by simpa only [hce, List.append_assoc] using hlink)
              (by rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
            rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
            · simp only [hvb] at rb
              obtain ⟨kb, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := rb
              have heval : _root_.L.evalE (.bin .sub a b) ⟨lm, loc⟩ = .ok ((0 : UInt64) - vb, ⟨lm, loc⟩) := by
                simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure, BinOp.eval]
              rw [heval]
              have htw1 : lkm.totalSize (pre ++ compileE env.tab nl tmp b) =
                  lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp b) := lkm.totalSize_append _ _
              obtain ⟨st2, hrun2, hpc2, ha0_2, hoth2, hmem2⟩ :=
                emitBinOp_step_lm lkm env (pre ++ compileE env.tab nl tmp b) post .sub
                  AbiReg.a0 AbiReg.zero AbiReg.a0 (by decide) 0 vb st1
                  (by simpa only [hce, emitBinOp, List.append_assoc] using hlink)
                  (by rw [htw1]; rw [htw_ce] at h64; omega)
                  (by rw [htw1]; exact hpc1) rfl ha0_1
              exact ⟨kb + 1, st2, by rw [run_add, hrun1]; exact hrun2,
                by rw [hpc2, htw1, htw_ce, Nat.add_assoc], ha0_2,
                hpres1.trans ⟨hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide)⟩,
                by rw [hmem2]; exact heq1⟩
            · simp only [hvb] at rb
              have heval : _root_.L.evalE (.bin .sub a b) ⟨lm, loc⟩ = .error .oob := by
                simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb]
              rw [heval]; exact rb
          · have hneq : (w == 0) = false := beq_false_of_ne hw0
            exact runLiBin (by simp only [compileE, hbc, hac, hneq, Bool.false_eq_true, ↓reduceIte, emitBinOp, List.append_assoc])
        | shl => exact runLiBin (by simp only [compileE, hbc, hac, emitBinOp, List.append_assoc])
        | shr => exact runLiBin (by simp only [compileE, hbc, hac, emitBinOp, List.append_assoc])
      | none =>
        have htw_op : ∀ rL rR, lkm.totalSize [emitBinOp op AbiReg.a0 rL rR] = 1 := fun _ _ => by
          cases op <;> simp only [emitBinOp, Asm.add, Asm.sub, Asm.and, Asm.or, Asm.xor, Asm.sll, Asm.srl, Asm.mul, Asm.mulhu, lkm.totalSize_instr]
        cases hsb : emitSimpleExpr env.tab AbiReg.t0 AbiReg.t1 b with
        | some cb =>
          have hce : compileE env.tab nl tmp (.bin op a b) =
              compileE env.tab nl tmp a ++ cb ++ [emitBinOp op AbiReg.a0 AbiReg.a0 AbiReg.t0] := by
            simp only [compileE, hbc, hac, hsb, List.append_assoc]
          have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.bin op a b)) =
              lkm.totalSize (compileE env.tab nl tmp a) + lkm.totalSize cb + 1 := by
            rw [hce, lkm.totalSize_append, lkm.totalSize_append, htw_op]
          have ra := iha pre (cb ++ [emitBinOp op AbiReg.a0 AbiReg.a0 AbiReg.t0] ++ post) tmp heOk.1 (by omega)
            (by simpa only [hce, List.append_assoc] using hlink)
            (by rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
          rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va, hva⟩ | hva
          · simp only [hva] at ra
            obtain ⟨ka, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ra
            have hf : (frameSpan sp nl nt).valid := by
              simp only [frameSpan, MemSpan.valid]; have := L.hStackValid; omega
            have htw1 : lkm.totalSize (pre ++ compileE env.tab nl tmp a) =
                lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp a) := lkm.totalSize_append _ _
            obtain ⟨vb, kb, st2, hvb, hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
              prog_emitSimpleExpr_sim env L lm loc hspAlign (pre ++ compileE env.tab nl tmp a)
                ([emitBinOp op AbiReg.a0 AbiReg.a0 AbiReg.t0] ++ post)
                AbiReg.t0 AbiReg.t1 (by decide) (by decide) (by decide) (by decide) (by decide)
                b cb hsb heOk.2
                (by simpa only [hce, List.append_assoc] using hlink)
                (by rw [htw1]; rw [htw_ce] at h64; omega) st1 (by rw [htw1]; exact hpc1)
                (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
                (ProgMemRel.of_tempSpan env hlo hhi (by omega) heq1 hmemRel)
                (ProgFrameOk.of_tempSpan hf (by omega) heq1 hframeOk)
            have heval : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .ok (op.eval va vb, ⟨lm, loc⟩) := by
              simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
            rw [heval]
            have hpres2 : PreservedRegs st1 st2 :=
              ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
               hoth2 _ (by decide) (by decide),
               hoth2 _ (by decide) (by decide)⟩
            have htw2 : lkm.totalSize (pre ++ compileE env.tab nl tmp a ++ cb) =
                lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp a) + lkm.totalSize cb := by
              rw [lkm.totalSize_append, htw1]
            obtain ⟨st3, hrun3, hpc3, ha0_3, hoth3, hmem3⟩ :=
              emitBinOp_step_lm lkm env (pre ++ compileE env.tab nl tmp a ++ cb) post
                op AbiReg.a0 AbiReg.a0 AbiReg.t0 (by decide) va vb st2
                (by simpa only [hce, List.append_assoc] using hlink)
                (by rw [htw2]; rw [htw_ce] at h64; omega)
                (by rw [htw2, ← htw1]; exact hpc2)
                ((hoth2 _ (by decide) (by decide)).trans ha0_1) ht0_2
            exact ⟨ka + (kb + 1), st3,
              by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
              by rw [hpc3, htw2, htw_ce]; congr 2; omega, ha0_3,
              (hpres1.trans hpres2).trans ⟨hoth3 _ (by decide), hoth3 _ (by decide), hoth3 _ (by decide), hoth3 _ (by decide)⟩,
              by rw [hmem3, hmem2]; exact heq1⟩
          · simp only [hva] at ra
            have heval : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .error .oob := by
              simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva]
            rw [heval]; exact ra
        | none =>
          cases hsa : emitSimpleExpr env.tab AbiReg.t0 AbiReg.t1 a with
          | some ca =>
            have hce : compileE env.tab nl tmp (.bin op a b) =
                compileE env.tab nl tmp b ++ ca ++ [emitBinOp op AbiReg.a0 AbiReg.t0 AbiReg.a0] := by
              simp only [compileE, hbc, hac, hsb, hsa, List.append_assoc]
            have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.bin op a b)) =
                lkm.totalSize (compileE env.tab nl tmp b) + lkm.totalSize ca + 1 := by
              rw [hce, lkm.totalSize_append, lkm.totalSize_append, htw_op]
            have rb := ihb pre (ca ++ [emitBinOp op AbiReg.a0 AbiReg.t0 AbiReg.a0] ++ post) tmp heOk.2 (by omega)
              (by simpa only [hce, List.append_assoc] using hlink)
              (by rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
            rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
            · simp only [hvb] at rb
              obtain ⟨kb, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := rb
              have hf : (frameSpan sp nl nt).valid := by
                simp only [frameSpan, MemSpan.valid]; have := L.hStackValid; omega
              have htw1 : lkm.totalSize (pre ++ compileE env.tab nl tmp b) =
                  lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp b) := lkm.totalSize_append _ _
              obtain ⟨va, ka, st2, hva, hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
                prog_emitSimpleExpr_sim env L lm loc hspAlign (pre ++ compileE env.tab nl tmp b)
                  ([emitBinOp op AbiReg.a0 AbiReg.t0 AbiReg.a0] ++ post)
                  AbiReg.t0 AbiReg.t1 (by decide) (by decide) (by decide) (by decide) (by decide)
                  a ca hsa heOk.1
                  (by simpa only [hce, List.append_assoc] using hlink)
                  (by rw [htw1]; rw [htw_ce] at h64; omega) st1 (by rw [htw1]; exact hpc1)
                  (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
                  (ProgMemRel.of_tempSpan env hlo hhi (by omega) heq1 hmemRel)
                  (ProgFrameOk.of_tempSpan hf (by omega) heq1 hframeOk)
              have heval : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .ok (op.eval va vb, ⟨lm, loc⟩) := by
                simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
              rw [heval]
              have hpres2 : PreservedRegs st1 st2 :=
                ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
                 hoth2 _ (by decide) (by decide),
                 hoth2 _ (by decide) (by decide)⟩
              have htw2 : lkm.totalSize (pre ++ compileE env.tab nl tmp b ++ ca) =
                  lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp b) + lkm.totalSize ca := by
                rw [lkm.totalSize_append, htw1]
              obtain ⟨st3, hrun3, hpc3, ha0_3, hoth3, hmem3⟩ :=
                emitBinOp_step_lm lkm env (pre ++ compileE env.tab nl tmp b ++ ca) post
                  op AbiReg.a0 AbiReg.t0 AbiReg.a0 (by decide) va vb st2
                  (by simpa only [hce, List.append_assoc] using hlink)
                  (by rw [htw2]; rw [htw_ce] at h64; omega)
                  (by rw [htw2, ← htw1]; exact hpc2) ht0_2
                  ((hoth2 _ (by decide) (by decide)).trans ha0_1)
              exact ⟨kb + (ka + 1), st3,
                by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
                by rw [hpc3, htw2, htw_ce]; congr 2; omega, ha0_3,
                (hpres1.trans hpres2).trans ⟨hoth3 _ (by decide), hoth3 _ (by decide), hoth3 _ (by decide), hoth3 _ (by decide)⟩,
                by rw [hmem3, hmem2]; exact heq1⟩
            · simp only [hvb] at rb
              have hPureA : ∃ va, _root_.L.evalE a ⟨lm, loc⟩ = .ok (va, ⟨lm, loc⟩) := by
                cases a <;> simp [emitSimpleExpr] at hsa <;> exact ⟨_, rfl⟩
              obtain ⟨va, hva⟩ := hPureA
              have heval : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .error .oob := by
                simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb]
              rw [heval]; exact rb
          | none =>
            let seq := compileE env.tab nl tmp a ++
              storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + tmp)) ++
              compileE env.tab nl (tmp + 1) b ++
              loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nl + tmp))
            have hce : compileE env.tab nl tmp (.bin op a b) =
                seq ++ [emitBinOp op AbiReg.a0 AbiReg.t0 AbiReg.a0] := by
              simp only [compileE, hbc, hac, hsb, hsa, seq, List.append_assoc]
            have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.bin op a b)) =
                lkm.totalSize seq + 1 := by rw [hce, lkm.totalSize_append, htw_op]
            have hlinkSeq : lkm.linkSpec (pre ++ seq ++ ([emitBinOp op AbiReg.a0 AbiReg.t0 AbiReg.a0] ++ post)) =
                .ok (env.code, env.labels) := by
              simpa only [hce, List.append_assoc] using hlink
            have rseq := prog_two_exprs_pair_sim env L lm loc hspAlign hlo hhi pre
              ([emitBinOp op AbiReg.a0 AbiReg.t0 AbiReg.a0] ++ post) tmp a b (by omega)
              (fun p q t s ht hl h6 hpc' hgp' hsp' hm hf => iha p q t heOk.1 ht hl h6 s hpc' hgp' hsp' hm hf)
              (fun p q t s ht hl h6 hpc' hgp' hsp' hm hf => ihb p q t heOk.2 ht hl h6 s hpc' hgp' hsp' hm hf)
              (by omega) (by omega) hlinkSeq (by dsimp only [seq] at htw_ce; rw [htw_ce] at h64; omega)
              st hpc hgp hsp hmemRel hframeOk
            rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va, hva⟩ | hva
            · rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
              · simp only [hva, hvb] at rseq
                obtain ⟨kseq, st1, hrun1, hpc1, ht0_1, ha0_1, hpres1, heq1⟩ := rseq
                have heval : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .ok (op.eval va vb, ⟨lm, loc⟩) := by
                  simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
                rw [heval]
                have htw_ps : lkm.totalSize (pre ++ seq) = lkm.totalSize pre + lkm.totalSize seq :=
                  lkm.totalSize_append _ _
                obtain ⟨st2, hrun2, hpc2, ha0_2, hoth2, hmem2⟩ :=
                  emitBinOp_step_lm lkm env (pre ++ seq) post op AbiReg.a0 AbiReg.t0 AbiReg.a0 (by decide)
                    va vb st1 (by simpa only [hce, List.append_assoc] using hlink)
                    (by rw [htw_ps, Nat.add_assoc, ← htw_ce]; exact h64)
                    (by rw [htw_ps]; exact hpc1) ht0_1 ha0_1
                exact ⟨kseq + 1, st2, by rw [run_add, hrun1]; exact hrun2,
                  by rw [hpc2, htw_ps, Nat.add_assoc, ← htw_ce], ha0_2,
                  hpres1.trans ⟨hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide)⟩,
                  by rw [hmem2]; exact heq1⟩
              · simp only [hva, hvb] at rseq
                have heval : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .error .oob := by
                  simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb]
                rw [heval]; exact rseq
            · simp only [hva] at rseq
              have heval : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .error .oob := by
                simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva]
              rw [heval]; exact rseq
  | cmpw c a b iha ihb =>
    simp only [exprOkB, Bool.and_eq_true] at heOk
    dsimp only [maxTempsExpr] at hTmp
    by_cases h1 : c = .eq ∧ b.constVal? = some 0
    · rcases h1 with ⟨rfl, hbc⟩
      have hbeq : b = .const 0 := expr_constVal_eq_some hbc
      have hce : compileE env.tab nl tmp (.cmpw .eq a b) =
          compileE env.tab nl tmp a ++ [Asm.sltiu AbiReg.a0 AbiReg.a0 1#12] := by
        simp only [compileE, hbc, beq_self_eq_true, Bool.true_and, ↓reduceIte]
      have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.cmpw .eq a b)) =
          lkm.totalSize (compileE env.tab nl tmp a) + 1 := by
        rw [hce, lkm.totalSize_append, Asm.sltiu, lkm.totalSize_instr]
      have ra := iha pre ([Asm.sltiu AbiReg.a0 AbiReg.a0 1#12] ++ post) tmp heOk.1 (by omega)
        (by simpa only [hce, List.append_assoc] using hlink)
        (by rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
      rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va, hva⟩ | hva
      · simp only [hva] at ra
        obtain ⟨ka, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ra
        have hvb : _root_.L.evalE b ⟨lm, loc⟩ = .ok (0, ⟨lm, loc⟩) := by rw [hbeq]; rfl
        have heval : _root_.L.evalE (.cmpw .eq a b) ⟨lm, loc⟩ = .ok (Cmp.eq.evalW va 0, ⟨lm, loc⟩) := by
          simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
        rw [heval]
        have htw1 : lkm.totalSize (pre ++ compileE env.tab nl tmp a) =
            lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp a) := lkm.totalSize_append _ _
        have hs := step_item_instr_lm lkm env.hrom (pre ++ compileE env.tab nl tmp a) post
          (.aluImm .sltiu AbiReg.a0 AbiReg.a0 1#12)
          (by simpa only [hce, Asm.sltiu, Asm.raw, List.append_assoc] using hlink)
          (by rw [htw1]; rw [htw_ce] at h64; omega) st1 (by rw [htw1]; exact hpc1)
        let st2 := stepReg st1 AbiReg.a0 (if va.toBitVec.ult 1#64 then 1#64 else 0#64) (st1.pc + 4#64)
        have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ compileE env.tab nl tmp a)) := by rw [htw1]; exact hpc1
        refine ⟨ka + 1, st2, by rw [run_add, hrun1]; exact run_one_cont _ _ st2 (by
            rw [hs]; simp only [execInstr, evalAluImm, ha0_1, show sextImm12 1#12 = 1#64 from rfl]; rfl),
          by change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1', htw1, htw_ce, Nat.add_assoc],
          ?_,
          hpres1.trans ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
            getReg_stepReg_ne _ _ _ (by decide) _ _,
            getReg_stepReg_ne _ _ _ (by decide) _ _⟩,
          by dsimp only [st2]; rw [prog_stepReg_mem]; exact heq1⟩
        change (stepReg st1 AbiReg.a0 _ _).getReg AbiReg.a0 = _
        rw [getReg_stepReg_eq _ _ (by decide)]
        have hsub : va.toBitVec - (0 : UInt64).toBitVec = va.toBitVec := BitVec.sub_zero _
        rw [← hsub, bv_sub_ult1_eq, ← uint64_cmp_eq, Cmp.evalW, Cmp.eval]
        cases (va == 0) <;> rfl
      · simp only [hva] at ra
        have heval : _root_.L.evalE (.cmpw .eq a b) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva]
        rw [heval]; exact ra
    · have hf1 : (c == .eq && b.constVal? == some 0) = false := by
        cases hceq : (c == .eq) <;> cases hbeq : (b.constVal? == some 0) <;> simp_all
      by_cases h2 : c = .eq ∧ a.constVal? = some 0
      · rcases h2 with ⟨rfl, hac⟩
        have haeq : a = .const 0 := expr_constVal_eq_some hac
        have hce : compileE env.tab nl tmp (.cmpw .eq a b) =
            compileE env.tab nl tmp b ++ [Asm.sltiu AbiReg.a0 AbiReg.a0 1#12] := by
          have hbf : (b.constVal? == some 0) = false := by
            cases hb : b.constVal? == some 0 <;> simp_all
          simp only [compileE, hbf, beq_self_eq_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte, hac]
        have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.cmpw .eq a b)) =
            lkm.totalSize (compileE env.tab nl tmp b) + 1 := by
          rw [hce, lkm.totalSize_append, Asm.sltiu, lkm.totalSize_instr]
        have hva : _root_.L.evalE a ⟨lm, loc⟩ = .ok (0, ⟨lm, loc⟩) := by rw [haeq]; rfl
        have rb := ihb pre ([Asm.sltiu AbiReg.a0 AbiReg.a0 1#12] ++ post) tmp heOk.2 (by omega)
          (by simpa only [hce, List.append_assoc] using hlink)
          (by rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
        rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
        · simp only [hvb] at rb
          obtain ⟨kb, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := rb
          have heval : _root_.L.evalE (.cmpw .eq a b) ⟨lm, loc⟩ = .ok (Cmp.eq.evalW 0 vb, ⟨lm, loc⟩) := by
            simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
          rw [heval]
          have htw1 : lkm.totalSize (pre ++ compileE env.tab nl tmp b) =
              lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp b) := lkm.totalSize_append _ _
          have hs := step_item_instr_lm lkm env.hrom (pre ++ compileE env.tab nl tmp b) post
            (.aluImm .sltiu AbiReg.a0 AbiReg.a0 1#12)
            (by simpa only [hce, Asm.sltiu, Asm.raw, List.append_assoc] using hlink)
            (by rw [htw1]; rw [htw_ce] at h64; omega) st1 (by rw [htw1]; exact hpc1)
          let st2 := stepReg st1 AbiReg.a0 (if vb.toBitVec.ult 1#64 then 1#64 else 0#64) (st1.pc + 4#64)
          have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ compileE env.tab nl tmp b)) := by rw [htw1]; exact hpc1
          refine ⟨kb + 1, st2, by rw [run_add, hrun1]; exact run_one_cont _ _ st2 (by
              rw [hs]; simp only [execInstr, evalAluImm, ha0_1, show sextImm12 1#12 = 1#64 from rfl]; rfl),
            by change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1', htw1, htw_ce, Nat.add_assoc],
            ?_,
            hpres1.trans ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
              getReg_stepReg_ne _ _ _ (by decide) _ _,
              getReg_stepReg_ne _ _ _ (by decide) _ _⟩,
            by dsimp only [st2]; rw [prog_stepReg_mem]; exact heq1⟩
          change (stepReg st1 AbiReg.a0 _ _).getReg AbiReg.a0 = _
          rw [getReg_stepReg_eq _ _ (by decide)]
          have hsub : vb.toBitVec - (0 : UInt64).toBitVec = vb.toBitVec := BitVec.sub_zero _
          rw [← hsub, bv_sub_ult1_eq, ← uint64_cmp_eq, show (vb == 0) = (0 == vb) from by
            by_cases h : vb = 0
            · subst h; rfl
            · simp [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (Ne.symm h)]]
          rw [Cmp.evalW, Cmp.eval]; cases (0 == vb) <;> rfl
        · simp only [hvb] at rb
          have heval : _root_.L.evalE (.cmpw .eq a b) ⟨lm, loc⟩ = .error .oob := by
            simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb]
          rw [heval]; exact rb
      · have hf2 : (c == .eq && a.constVal? == some 0) = false := by
          cases hceq : (c == .eq) <;> cases haeq : (a.constVal? == some 0) <;> simp_all
        by_cases h3 : c = .ne ∧ b.constVal? = some 0
        · rcases h3 with ⟨rfl, hbc⟩
          have hbeq : b = .const 0 := expr_constVal_eq_some hbc
          have hce : compileE env.tab nl tmp (.cmpw .ne a b) =
              compileE env.tab nl tmp a ++ [Asm.sltu AbiReg.a0 AbiReg.zero AbiReg.a0] := by
            have hne : (Cmp.ne == Cmp.eq) = false := rfl
            simp only [compileE, hne, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hbc, beq_self_eq_true, Bool.true_and]
          have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.cmpw .ne a b)) =
              lkm.totalSize (compileE env.tab nl tmp a) + 1 := by
            rw [hce, lkm.totalSize_append, Asm.sltu, lkm.totalSize_instr]
          have ra := iha pre ([Asm.sltu AbiReg.a0 AbiReg.zero AbiReg.a0] ++ post) tmp heOk.1 (by omega)
            (by simpa only [hce, List.append_assoc] using hlink)
            (by rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
          rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va, hva⟩ | hva
          · simp only [hva] at ra
            obtain ⟨ka, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ra
            have hvb : _root_.L.evalE b ⟨lm, loc⟩ = .ok (0, ⟨lm, loc⟩) := by rw [hbeq]; rfl
            have heval : _root_.L.evalE (.cmpw .ne a b) ⟨lm, loc⟩ = .ok (Cmp.ne.evalW va 0, ⟨lm, loc⟩) := by
              simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
            rw [heval]
            have htw1 : lkm.totalSize (pre ++ compileE env.tab nl tmp a) =
                lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp a) := lkm.totalSize_append _ _
            have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ compileE env.tab nl tmp a)) := by
              rw [htw1]; exact hpc1
            have hs := step_item_instr_lm lkm env.hrom (pre ++ compileE env.tab nl tmp a) post
              (.alu .sltu AbiReg.a0 AbiReg.zero AbiReg.a0)
              (by simpa only [hce, Asm.sltu, Asm.raw, List.append_assoc] using hlink)
              (by rw [htw1]; rw [htw_ce] at h64; omega) st1 hpc1'
            let st2 := stepReg st1 AbiReg.a0 (if (0#64 : RV64.Word).ult va.toBitVec then 1#64 else 0#64) (st1.pc + 4#64)
            refine ⟨ka + 1, st2, by rw [run_add, hrun1]; exact run_one_cont _ _ st2 (by
                rw [hs]; simp only [execInstr, evalAlu, show st1.getReg AbiReg.zero = 0#64 from rfl, ha0_1]; rfl),
              by change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1', htw1, htw_ce, Nat.add_assoc],
              ?_,
              hpres1.trans ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
                getReg_stepReg_ne _ _ _ (by decide) _ _,
                getReg_stepReg_ne _ _ _ (by decide) _ _⟩,
              by dsimp only [st2]; rw [prog_stepReg_mem]; exact heq1⟩
            change (stepReg st1 AbiReg.a0 _ _).getReg AbiReg.a0 = _
            rw [getReg_stepReg_eq _ _ (by decide)]
            have hsub : va.toBitVec - (0 : UInt64).toBitVec = va.toBitVec := BitVec.sub_zero _
            rw [← hsub, bv_zero_ult_sub_eq, ← uint64_cmp_ne, Cmp.evalW, Cmp.eval]
            cases (va != 0) <;> rfl
          · simp only [hva] at ra
            have heval : _root_.L.evalE (.cmpw .ne a b) ⟨lm, loc⟩ = .error .oob := by
              simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva]
            rw [heval]; exact ra
        · have hf3 : (c == .ne && b.constVal? == some 0) = false := by
            cases hcne : (c == .ne) <;> cases hbeq : (b.constVal? == some 0) <;> simp_all
          by_cases h4 : c = .ne ∧ a.constVal? = some 0
          · rcases h4 with ⟨rfl, hac⟩
            have haeq : a = .const 0 := expr_constVal_eq_some hac
            have hce : compileE env.tab nl tmp (.cmpw .ne a b) =
                compileE env.tab nl tmp b ++ [Asm.sltu AbiReg.a0 AbiReg.zero AbiReg.a0] := by
              have hne : (Cmp.ne == Cmp.eq) = false := rfl
              have hbf : (b.constVal? == some 0) = false := by
                cases hb : b.constVal? == some 0 <;> simp_all
              simp only [compileE, hne, hbf, Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte, hac, beq_self_eq_true]
            have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.cmpw .ne a b)) =
                lkm.totalSize (compileE env.tab nl tmp b) + 1 := by
              rw [hce, lkm.totalSize_append, Asm.sltu, lkm.totalSize_instr]
            have hva : _root_.L.evalE a ⟨lm, loc⟩ = .ok (0, ⟨lm, loc⟩) := by rw [haeq]; rfl
            have rb := ihb pre ([Asm.sltu AbiReg.a0 AbiReg.zero AbiReg.a0] ++ post) tmp heOk.2 (by omega)
              (by simpa only [hce, List.append_assoc] using hlink)
              (by rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
            rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
            · simp only [hvb] at rb
              obtain ⟨kb, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := rb
              have heval : _root_.L.evalE (.cmpw .ne a b) ⟨lm, loc⟩ = .ok (Cmp.ne.evalW 0 vb, ⟨lm, loc⟩) := by
                simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
              rw [heval]
              have htw1 : lkm.totalSize (pre ++ compileE env.tab nl tmp b) =
                  lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp b) := lkm.totalSize_append _ _
              have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ compileE env.tab nl tmp b)) := by
                rw [htw1]; exact hpc1
              have hs := step_item_instr_lm lkm env.hrom (pre ++ compileE env.tab nl tmp b) post
                (.alu .sltu AbiReg.a0 AbiReg.zero AbiReg.a0)
                (by simpa only [hce, Asm.sltu, Asm.raw, List.append_assoc] using hlink)
                (by rw [htw1]; rw [htw_ce] at h64; omega) st1 hpc1'
              let st2 := stepReg st1 AbiReg.a0 (if (0#64 : RV64.Word).ult vb.toBitVec then 1#64 else 0#64) (st1.pc + 4#64)
              refine ⟨kb + 1, st2, by rw [run_add, hrun1]; exact run_one_cont _ _ st2 (by
                  rw [hs]; simp only [execInstr, evalAlu, show st1.getReg AbiReg.zero = 0#64 from rfl, ha0_1]; rfl),
                by change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1', htw1, htw_ce, Nat.add_assoc],
                ?_,
                hpres1.trans ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
                  getReg_stepReg_ne _ _ _ (by decide) _ _,
                  getReg_stepReg_ne _ _ _ (by decide) _ _⟩,
                by dsimp only [st2]; rw [prog_stepReg_mem]; exact heq1⟩
              change (stepReg st1 AbiReg.a0 _ _).getReg AbiReg.a0 = _
              rw [getReg_stepReg_eq _ _ (by decide)]
              have hsub : vb.toBitVec - (0 : UInt64).toBitVec = vb.toBitVec := BitVec.sub_zero _
              rw [← hsub, bv_zero_ult_sub_eq, ← uint64_cmp_ne, show (vb != 0) = (0 != vb) from by
                by_cases h : vb = 0
                · subst h; rfl
                · simp [bne, beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (Ne.symm h)]]
              rw [Cmp.evalW, Cmp.eval]; cases (0 != vb) <;> rfl
            · simp only [hvb] at rb
              have heval : _root_.L.evalE (.cmpw .ne a b) ⟨lm, loc⟩ = .error .oob := by
                simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb]
              rw [heval]; exact rb
          · have hf4 : (c == .ne && a.constVal? == some 0) = false := by
              cases hcne : (c == .ne) <;> cases haeq : (a.constVal? == some 0) <;> simp_all
            cases hsb : emitSimpleExpr env.tab AbiReg.t0 AbiReg.t1 b with
            | some cb =>
              have hce : compileE env.tab nl tmp (.cmpw c a b) =
                  compileE env.tab nl tmp a ++ cb ++ emitCmpw c AbiReg.a0 AbiReg.t0 := by
                simp only [compileE, hf1, hf2, hf3, hf4, Bool.false_eq_true, ↓reduceIte, hsb, List.append_assoc]
              have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.cmpw c a b)) =
                  lkm.totalSize (compileE env.tab nl tmp a) + lkm.totalSize cb + lkm.totalSize (emitCmpw c AbiReg.a0 AbiReg.t0) := by
                rw [hce, lkm.totalSize_append, lkm.totalSize_append]
              have ra := iha pre (cb ++ emitCmpw c AbiReg.a0 AbiReg.t0 ++ post) tmp heOk.1 (by omega)
                (by simpa only [hce, List.append_assoc] using hlink)
                (by rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
              rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va, hva⟩ | hva
              · simp only [hva] at ra
                obtain ⟨ka, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ra
                have hf : (frameSpan sp nl nt).valid := by
                  simp only [frameSpan, MemSpan.valid]; have := L.hStackValid; omega
                have htw1 : lkm.totalSize (pre ++ compileE env.tab nl tmp a) =
                    lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp a) := lkm.totalSize_append _ _
                obtain ⟨vb, kb, st2, hvb, hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
                  prog_emitSimpleExpr_sim env L lm loc hspAlign (pre ++ compileE env.tab nl tmp a)
                    (emitCmpw c AbiReg.a0 AbiReg.t0 ++ post)
                    AbiReg.t0 AbiReg.t1 (by decide) (by decide) (by decide) (by decide) (by decide)
                    b cb hsb heOk.2 (by simpa only [hce, List.append_assoc] using hlink)
                    (by rw [htw1]; rw [htw_ce] at h64; omega) st1 (by rw [htw1]; exact hpc1)
                    (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
                    (ProgMemRel.of_tempSpan env hlo hhi (by omega) heq1 hmemRel)
                    (ProgFrameOk.of_tempSpan hf (by omega) heq1 hframeOk)
                have heval : _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .ok (c.evalW va vb, ⟨lm, loc⟩) := by
                  simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
                rw [heval]
                have hpres2 : PreservedRegs st1 st2 :=
                  ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
                   hoth2 _ (by decide) (by decide),
                   hoth2 _ (by decide) (by decide)⟩
                have htw2 : lkm.totalSize (pre ++ compileE env.tab nl tmp a ++ cb) =
                    lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp a) + lkm.totalSize cb := by
                  rw [lkm.totalSize_append, htw1]
                obtain ⟨kc, st3, hrun3, hpc3, ha0_3, hpres3, hmem3⟩ :=
                  emitCmpw_sim_lm lkm env (pre ++ compileE env.tab nl tmp a ++ cb) post c AbiReg.a0 AbiReg.t0 va vb st2
                    (by simpa only [hce, List.append_assoc] using hlink)
                    (by rw [htw2]; rw [htw_ce] at h64; omega)
                    (by rw [htw2, ← htw1]; exact hpc2)
                    ((hoth2 _ (by decide) (by decide)).trans ha0_1) ht0_2
                exact ⟨ka + (kb + kc), st3,
                  by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
                  by rw [hpc3, htw2, htw_ce]; congr 2; omega, ha0_3,
                  (hpres1.trans hpres2).trans hpres3, by rw [hmem3, hmem2]; exact heq1⟩
              · simp only [hva] at ra
                have heval : _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .error .oob := by
                  simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva]
                rw [heval]; exact ra
            | none =>
              cases hsa : emitSimpleExpr env.tab AbiReg.t0 AbiReg.t1 a with
              | some ca =>
                have hce : compileE env.tab nl tmp (.cmpw c a b) =
                    compileE env.tab nl tmp b ++ ca ++ emitCmpw c AbiReg.t0 AbiReg.a0 := by
                  simp only [compileE, hf1, hf2, hf3, hf4, Bool.false_eq_true, ↓reduceIte, hsb, hsa, List.append_assoc]
                have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.cmpw c a b)) =
                    lkm.totalSize (compileE env.tab nl tmp b) + lkm.totalSize ca + lkm.totalSize (emitCmpw c AbiReg.t0 AbiReg.a0) := by
                  rw [hce, lkm.totalSize_append, lkm.totalSize_append]
                have rb := ihb pre (ca ++ emitCmpw c AbiReg.t0 AbiReg.a0 ++ post) tmp heOk.2 (by omega)
                  (by simpa only [hce, List.append_assoc] using hlink)
                  (by rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
                rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
                · simp only [hvb] at rb
                  obtain ⟨kb, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := rb
                  have hf : (frameSpan sp nl nt).valid := by
                    simp only [frameSpan, MemSpan.valid]; have := L.hStackValid; omega
                  have htw1 : lkm.totalSize (pre ++ compileE env.tab nl tmp b) =
                      lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp b) := lkm.totalSize_append _ _
                  obtain ⟨va, ka, st2, hva, hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
                    prog_emitSimpleExpr_sim env L lm loc hspAlign (pre ++ compileE env.tab nl tmp b)
                      (emitCmpw c AbiReg.t0 AbiReg.a0 ++ post)
                      AbiReg.t0 AbiReg.t1 (by decide) (by decide) (by decide) (by decide) (by decide)
                      a ca hsa heOk.1 (by simpa only [hce, List.append_assoc] using hlink)
                      (by rw [htw1]; rw [htw_ce] at h64; omega) st1 (by rw [htw1]; exact hpc1)
                      (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
                      (ProgMemRel.of_tempSpan env hlo hhi (by omega) heq1 hmemRel)
                      (ProgFrameOk.of_tempSpan hf (by omega) heq1 hframeOk)
                  have heval : _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .ok (c.evalW va vb, ⟨lm, loc⟩) := by
                    simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
                  rw [heval]
                  have hpres2 : PreservedRegs st1 st2 :=
                    ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
                     hoth2 _ (by decide) (by decide),
                     hoth2 _ (by decide) (by decide)⟩
                  have htw2 : lkm.totalSize (pre ++ compileE env.tab nl tmp b ++ ca) =
                      lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp b) + lkm.totalSize ca := by
                    rw [lkm.totalSize_append, htw1]
                  obtain ⟨kc, st3, hrun3, hpc3, ha0_3, hpres3, hmem3⟩ :=
                    emitCmpw_sim_lm lkm env (pre ++ compileE env.tab nl tmp b ++ ca) post c AbiReg.t0 AbiReg.a0 va vb st2
                      (by simpa only [hce, List.append_assoc] using hlink)
                      (by rw [htw2]; rw [htw_ce] at h64; omega)
                      (by rw [htw2, ← htw1]; exact hpc2)
                      ht0_2 ((hoth2 _ (by decide) (by decide)).trans ha0_1)
                  exact ⟨kb + (ka + kc), st3,
                    by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
                    by rw [hpc3, htw2, htw_ce]; congr 2; omega, ha0_3,
                    (hpres1.trans hpres2).trans hpres3, by rw [hmem3, hmem2]; exact heq1⟩
                · simp only [hvb] at rb
                  have hPureA : ∃ va, _root_.L.evalE a ⟨lm, loc⟩ = .ok (va, ⟨lm, loc⟩) := by
                    cases a <;> simp [emitSimpleExpr] at hsa <;> exact ⟨_, rfl⟩
                  obtain ⟨va, hva⟩ := hPureA
                  have heval : _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .error .oob := by
                    simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb]
                  rw [heval]; exact rb
              | none =>
                let seq := compileE env.tab nl tmp a ++
                  storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + tmp)) ++
                  compileE env.tab nl (tmp + 1) b ++
                  loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nl + tmp))
                have hce : compileE env.tab nl tmp (.cmpw c a b) = seq ++ emitCmpw c AbiReg.t0 AbiReg.a0 := by
                  simp only [compileE, hf1, hf2, hf3, hf4, Bool.false_eq_true, ↓reduceIte, hsb, hsa, seq, List.append_assoc]
                have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.cmpw c a b)) =
                    lkm.totalSize seq + lkm.totalSize (emitCmpw c AbiReg.t0 AbiReg.a0) := by
                  rw [hce, lkm.totalSize_append]
                have rseq := prog_two_exprs_pair_sim env L lm loc hspAlign hlo hhi pre
                  (emitCmpw c AbiReg.t0 AbiReg.a0 ++ post) tmp a b (by omega)
                  (fun p q t s ht hl h6 hpc' hgp' hsp' hm hf => iha p q t heOk.1 ht hl h6 s hpc' hgp' hsp' hm hf)
                  (fun p q t s ht hl h6 hpc' hgp' hsp' hm hf => ihb p q t heOk.2 ht hl h6 s hpc' hgp' hsp' hm hf)
                  (by omega) (by omega)
                  (by rw [show pre ++ (compileE env.tab nl tmp a ++
                      storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + tmp)) ++
                      compileE env.tab nl (tmp + 1) b ++
                      loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nl + tmp))) ++
                      (emitCmpw c AbiReg.t0 AbiReg.a0 ++ post) =
                      pre ++ compileE env.tab nl tmp (.cmpw c a b) ++ post from by
                      rw [hce]; dsimp only [seq]; simp only [List.append_assoc]]; exact hlink)
                  (by dsimp only [seq] at htw_ce; rw [htw_ce] at h64; omega)
                  st hpc hgp hsp hmemRel hframeOk
                rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va, hva⟩ | hva
                · rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
                  · simp only [hva, hvb] at rseq
                    obtain ⟨kseq, st1, hrun1, hpc1, ht0_1, ha0_1, hpres1, heq1⟩ := rseq
                    have heval : _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .ok (c.evalW va vb, ⟨lm, loc⟩) := by
                      simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
                    rw [heval]
                    have htw_ps : lkm.totalSize (pre ++ seq) = lkm.totalSize pre + lkm.totalSize seq :=
                      lkm.totalSize_append _ _
                    obtain ⟨kc, st2, hrun2, hpc2, ha0_2, hpres2, hmem2⟩ :=
                      emitCmpw_sim_lm lkm env (pre ++ seq) post c AbiReg.t0 AbiReg.a0 va vb st1
                        (by simpa only [hce, List.append_assoc] using hlink)
                        (by rw [htw_ps, Nat.add_assoc, ← htw_ce]; exact h64)
                        (by rw [htw_ps]; exact hpc1) ht0_1 ha0_1
                    exact ⟨kseq + kc, st2, by rw [run_add, hrun1]; exact hrun2,
                      by rw [hpc2, htw_ps, Nat.add_assoc, ← htw_ce], ha0_2,
                      hpres1.trans hpres2, by rw [hmem2]; exact heq1⟩
                  · simp only [hva, hvb] at rseq
                    have heval : _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .error .oob := by
                      simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb]
                    rw [heval]; exact rseq
                · simp only [hva] at rseq
                  have heval : _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .error .oob := by
                    simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hva]
                  rw [heval]; exact rseq
  | ld8 a i ihi =>
    simp only [exprOkB, Bool.and_eq_true] at heOk
    exact prog_ld8_sim env L lm loc pre post tmp a i heOk.1 hTmp
      (fun p q t s ht hl h6 hpc' hgp' hsp' hm hf => ihi p q t heOk.2 ht hl h6 s hpc' hgp' hsp' hm hf)
      hlo hhi hlink h64 st hpc hgp hsp hmemRel hframeOk
  | ld64 a i ihi =>
    simp only [exprOkB, Bool.and_eq_true] at heOk
    exact prog_ld64_sim env L lm loc pre post tmp a i heOk.1 hTmp
      (fun p q t s ht hl h6 hpc' hgp' hsp' hm hf => ihi p q t heOk.2 ht hl h6 s hpc' hgp' hsp' hm hf)
      hlo hhi hlink h64 st hpc hgp hsp hmemRel hframeOk
  | ldc d i ihi =>
    simp only [exprOkB, Bool.and_eq_true] at heOk
    exact prog_ldc_sim env L lm loc pre post tmp d i heOk.1 hTmp
      (fun p q t s ht hl h6 hpc' hgp' hsp' hm hf => ihi p q t heOk.2 ht hl h6 s hpc' hgp' hsp' hm hf)
      hlo hhi hlink h64 st hpc hgp hsp hmemRel hframeOk
  | ld64t a t i iht ihi =>
    simp only [exprOkB, Bool.and_eq_true] at heOk
    dsimp only [maxTempsExpr] at hTmp
    cases htc : t.constVal? with
    | some w =>
      have hteq : t = .const w := expr_constVal_eq_some htc
      have hu : _root_.L.evalE t ⟨lm, loc⟩ = .ok (w, ⟨lm, loc⟩) := by rw [hteq]; rfl
      have hta := tieredOk_len64_addr_T L.T a w heOk.1.1
      let s := tierA a w
      let caddr := compileE env.tab nl tmp i ++
        loadMemOff .ld AbiReg.t2 AbiReg.gp AbiReg.t3 (env.tab.len64 s) ++
        [Asm.bgeu AbiReg.a0 AbiReg.t2 errLabel] ++
        loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t3 (env.tab.base64 s) ++
        [Asm.slli AbiReg.t3 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3]
      have hce : compileE env.tab nl tmp (.ld64t a t i) = caddr ++ [Asm.ld AbiReg.a0 AbiReg.t1 0#12] := by
        simp only [compileE, htc, s, caddr, List.append_assoc, List.cons_append, List.nil_append]
      have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.ld64t a t i)) = lkm.totalSize caddr + 1 := by
        rw [hce, lkm.totalSize_append, Asm.ld, lkm.totalSize_instr]
      have raddr := prog_tiered_const_addr8_sim env L lm loc hlo hhi pre
        ([Asm.ld AbiReg.a0 AbiReg.t1 0#12] ++ post) tmp s i hta.1 (by omega)
        (fun p q t' s' ht hl h6 hpc' hgp' hsp' hm hf => ihi p q t' heOk.2 ht hl h6 s' hpc' hgp' hsp' hm hf)
        (by rw [show pre ++ caddr ++ ([Asm.ld AbiReg.a0 AbiReg.t1 0#12] ++ post) =
            pre ++ compileE env.tab nl tmp (.ld64t a t i) ++ post from by rw [hce]; simp only [List.append_assoc]]; exact hlink)
        (by rw [htw_ce] at h64; dsimp only [caddr] at h64; omega) st hpc hgp hsp hmemRel hframeOk
      rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
      · simp only [hvi] at raddr
        by_cases hbound : vi.toNat < (lm.arr64 s).size
        · simp only [hbound, ↓reduceIte] at raddr
          obtain ⟨k1, st1, hrun1, hpc1, ht1_1, hpres1, heq1⟩ := raddr
          have hevalE : _root_.L.evalE (.ld64t a t i) ⟨lm, loc⟩ =
              .ok ((lm.arr64 s)[vi.toNat], ⟨lm, loc⟩) := by
            change (_root_.L.evalE t >>= fun u' => _root_.L.evalE i >>= fun idx => _root_.L.ld64 (tierA a u') idx) ⟨lm, loc⟩ = _
            dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hu]; dsimp only; rw [hvi]
            dsimp only [_root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
              Pure.pure, StateT.pure, Except.pure, Except.bind]
            simp [s, hbound]; rfl
          rw [hevalE]
          have hrel1 := ProgMemRel.of_tempSpan env hlo hhi (by omega) heq1 hmemRel
          have hw := (hrel1.2.1 s hta.1).2.2.2.2 vi.toNat hbound
          have htw1 : lkm.totalSize (pre ++ caddr) = lkm.totalSize pre + lkm.totalSize caddr := lkm.totalSize_append _ _
          have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ caddr)) := by rw [htw1]; exact hpc1
          have hsLd := step_item_instr_lm lkm env.hrom (pre ++ caddr) post (.load .ld AbiReg.a0 AbiReg.t1 0#12)
            (by rw [show (pre ++ caddr) ++ [AsmItem.instr (.load .ld AbiReg.a0 AbiReg.t1 0#12)] ++ post =
                pre ++ compileE env.tab nl tmp (.ld64t a t i) ++ post from by rw [hce]; simp only [Asm.ld, List.append_assoc]]; exact hlink)
            (by rw [htw1]; rw [htw_ce] at h64; omega) st1 hpc1'
          have hal1 : isAligned (st1.getReg AbiReg.t1 + sextImm12 0#12) 8 = true := by
            rw [show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero, ht1_1]
            exact isAligned8_add_mul8 (L.base64 s) (L.h64Align s) vi.toNat
          let st2 := stepReg st1 AbiReg.a0 (loadBytes st1.mem (st1.getReg AbiReg.t1 + sextImm12 0#12) 8) (st1.pc + 4#64)
          refine ⟨k1 + 1, st2, by rw [run_add, hrun1]; exact run_one_cont _ _ st2 (by rw [hsLd]; simp only [execInstr, hal1]; rfl),
            by change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1', htw1, htw_ce]; congr 2; try omega,
            by change (stepReg st1 AbiReg.a0 _ _).getReg AbiReg.a0 = _
               rw [getReg_stepReg_eq _ _ (by decide), show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero, ht1_1]; exact hw,
            hpres1.trans ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
              getReg_stepReg_ne _ _ _ (by decide) _ _,
              getReg_stepReg_ne _ _ _ (by decide) _ _⟩,
            by dsimp only [st2]; rw [prog_stepReg_mem]; exact heq1⟩
        · simp only [hbound, ↓reduceIte] at raddr
          have hevalE : _root_.L.evalE (.ld64t a t i) ⟨lm, loc⟩ = .error .oob := by
            change (_root_.L.evalE t >>= fun u' => _root_.L.evalE i >>= fun idx => _root_.L.ld64 (tierA a u') idx) ⟨lm, loc⟩ = _
            dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hu]; dsimp only; rw [hvi]
            dsimp only [_root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
              Pure.pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.pure, Except.bind]
            simp [s, hbound]; rfl
          rw [hevalE]; exact raddr
      · simp only [hvi] at raddr
        have hevalE : _root_.L.evalE (.ld64t a t i) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hu, hvi]
        rw [hevalE]; exact raddr
    | none =>
      let caddr := tieredHead env.tab nl tmp t i ++
        [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
         Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
        loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (env.tab.len64 (TieredArray.t0 a)) ++
        [Asm.bgeu AbiReg.a0 AbiReg.t2 errLabel] ++
        loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t3 (env.tab.base64 (TieredArray.t0 a)) ++
        [Asm.slli AbiReg.t3 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3]
      have hce : compileE env.tab nl tmp (.ld64t a t i) = caddr ++ [Asm.ld AbiReg.a0 AbiReg.t1 0#12] := by
        dsimp only [compileE]; rw [htc]
        cases hs : emitSimpleExpr env.tab AbiReg.t0 AbiReg.t1 t <;>
          simp only [caddr, tieredHead, hs, List.append_assoc, List.cons_append, List.nil_append]
      have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.ld64t a t i)) = lkm.totalSize caddr + 1 := by
        rw [hce, lkm.totalSize_append, Asm.ld, lkm.totalSize_instr]
      have raddr := prog_tiered_addr8_sim env L lm loc hspAlign hlo hhi pre
        ([Asm.ld AbiReg.a0 AbiReg.t1 0#12] ++ post) tmp a t i heOk.1.1 heOk.1.2 (by omega) (by omega) (by omega)
        (fun p q t' s ht hl h6 hpc' hgp' hsp' hm hf => iht p q t' heOk.1.2 ht hl h6 s hpc' hgp' hsp' hm hf)
        (fun p q t' s ht hl h6 hpc' hgp' hsp' hm hf => ihi p q t' heOk.2 ht hl h6 s hpc' hgp' hsp' hm hf)
        (by rw [show pre ++ caddr ++ ([Asm.ld AbiReg.a0 AbiReg.t1 0#12] ++ post) =
            pre ++ compileE env.tab nl tmp (.ld64t a t i) ++ post from by rw [hce]; simp only [List.append_assoc]]; exact hlink)
        (by rw [htw_ce] at h64; dsimp only [caddr] at h64 ⊢; omega) st hpc hgp hsp hmemRel hframeOk
      rcases _root_.L.evalE_pure t ⟨lm, loc⟩ with ⟨u, hu⟩ | hu
      · rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
        · simp only [hu, hvi] at raddr ⊢
          by_cases hbound : vi.toNat < (lm.arr64 (tierA a u)).size
          · simp only [hbound, ↓reduceIte] at raddr
            obtain ⟨k1, st1, hrun1, hpc1, ht1_1, hpres1, heq1⟩ := raddr
            have hevalE : _root_.L.evalE (.ld64t a t i) ⟨lm, loc⟩ =
                .ok ((lm.arr64 (tierA a u))[vi.toNat], ⟨lm, loc⟩) := by
              change (_root_.L.evalE t >>= fun u' => _root_.L.evalE i >>= fun idx => _root_.L.ld64 (tierA a u') idx) ⟨lm, loc⟩ = _
              dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hu]; dsimp only; rw [hvi]
              dsimp only [_root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
                Pure.pure, StateT.pure, Except.pure, Except.bind]
              simp [hbound]; rfl
            rw [hevalE]
            have hrel1 := ProgMemRel.of_tempSpan env hlo hhi (by omega) heq1 hmemRel
            have hta := tieredOk_len64_addr_T L.T a u heOk.1.1
            have hw := (hrel1.2.1 (tierA a u) hta.1).2.2.2.2 vi.toNat hbound
            have htw1 : lkm.totalSize (pre ++ caddr) = lkm.totalSize pre + lkm.totalSize caddr := lkm.totalSize_append _ _
            have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ caddr)) := by
              rw [htw1]; dsimp only [caddr] at hpc1 ⊢; exact hpc1
            have hsLd := step_item_instr_lm lkm env.hrom (pre ++ caddr) post (.load .ld AbiReg.a0 AbiReg.t1 0#12)
              (by rw [show (pre ++ caddr) ++ [AsmItem.instr (.load .ld AbiReg.a0 AbiReg.t1 0#12)] ++ post =
                  pre ++ compileE env.tab nl tmp (.ld64t a t i) ++ post from by
                  rw [hce]; simp only [Asm.ld, List.append_assoc]]; exact hlink)
              (by rw [htw1]; rw [htw_ce] at h64; omega) st1 hpc1'
            have hal1 : isAligned (st1.getReg AbiReg.t1 + sextImm12 0#12) 8 = true := by
              rw [show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero, ht1_1]
              exact isAligned8_add_mul8 (L.base64 (tierA a u)) (L.h64Align (tierA a u)) vi.toNat
            let st2 := stepReg st1 AbiReg.a0 (loadBytes st1.mem (st1.getReg AbiReg.t1 + sextImm12 0#12) 8) (st1.pc + 4#64)
            refine ⟨k1 + 1, st2, ?_, ?_, ?_, hpres1.trans
              ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
               getReg_stepReg_ne _ _ _ (by decide) _ _,
               getReg_stepReg_ne _ _ _ (by decide) _ _⟩,
              by dsimp only [st2]; rw [prog_stepReg_mem]; exact heq1⟩
            · rw [run_add, hrun1]; exact run_one_cont _ _ st2 (by rw [hsLd]; simp only [execInstr, hal1]; rfl)
            · change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1', htw1, htw_ce]; congr 2; try omega
            · change (stepReg st1 AbiReg.a0 _ _).getReg AbiReg.a0 = _
              rw [getReg_stepReg_eq _ _ (by decide), show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero, ht1_1]; exact hw
          · simp only [hbound, ↓reduceIte] at raddr
            have hevalE : _root_.L.evalE (.ld64t a t i) ⟨lm, loc⟩ = .error .oob := by
              change (_root_.L.evalE t >>= fun u' => _root_.L.evalE i >>= fun idx => _root_.L.ld64 (tierA a u') idx) ⟨lm, loc⟩ = _
              dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hu]; dsimp only; rw [hvi]
              dsimp only [_root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
                Pure.pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.pure, Except.bind]
              simp [hbound]; rfl
            rw [hevalE]; exact raddr
        · simp only [hu, hvi] at raddr ⊢
          have hevalE : _root_.L.evalE (.ld64t a t i) ⟨lm, loc⟩ = .error .oob := by
            simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hu, hvi]
          rw [hevalE]; exact raddr
      · simp only [hu] at raddr ⊢
        have hevalE : _root_.L.evalE (.ld64t a t i) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hu]
        rw [hevalE]; exact raddr
  | len64t a t iht =>
    simp only [exprOkB, Bool.and_eq_true] at heOk
    dsimp only [maxTempsExpr] at hTmp
    cases htc : t.constVal? with
    | some w =>
      have hteq : t = .const w := expr_constVal_eq_some htc
      have hu : _root_.L.evalE t ⟨lm, loc⟩ = .ok (w, ⟨lm, loc⟩) := by rw [hteq]; rfl
      have hta := tieredOk_len64_addr_T L.T a w heOk.1
      have hce : compileE env.tab nl tmp (.len64t a t) =
          loadMemOff .ld AbiReg.a0 AbiReg.gp AbiReg.t2 (env.tab.len64 (tierA a w)) := by
        simp only [compileE, htc]
      have hevalE : _root_.L.evalE (.len64t a t) ⟨lm, loc⟩ = .ok (lm.len64 (tierA a w), ⟨lm, loc⟩) := by
        change (_root_.L.evalE t >>= fun u' => do return (← get).mem.len64 (tierA a u')) ⟨lm, loc⟩ = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hu]
        dsimp only [get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind, Pure.pure, StateT.pure,
          Except.pure, Except.bind]
      rw [hevalE]
      have hal : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.len64 (tierA a w))) 8 = true := by
        rw [hgp, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
      obtain ⟨st', hrun, hoth, ha0, hmem, hpc'⟩ :=
        loadMemOff_ld_correct_lm lkm env.hrom pre post AbiReg.a0 AbiReg.gp AbiReg.t2
          (by decide) (by decide) (by decide) (env.tab.len64 (tierA a w))
          (by rw [← hce]; exact hlink) (by rw [← hce]; exact h64) st hpc hal
      refine ⟨lkm.totalSize _, st', hrun, by rw [hce]; exact hpc', ?_,
        ⟨hoth _ (by decide) (by decide), hoth _ (by decide) (by decide),
         hoth _ (by decide) (by decide),
         hoth _ (by decide) (by decide)⟩,
        by rw [hmem]; exact MemEqOutside.refl _ _⟩
      rw [ha0, hgp, (hmemRel.2.1 (tierA a w) hta.1).2.2.1]; rfl
    | none =>
      let ct := compileE env.tab nl tmp t
      let chdr := [Asm.andi AbiReg.t0 AbiReg.a0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
                   Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0]
      let clen := loadMemOff .ld AbiReg.a0 AbiReg.t1 AbiReg.t2 (env.tab.len64 (TieredArray.t0 a))
      have hce : compileE env.tab nl tmp (.len64t a t) = ct ++ chdr ++ clen := by
        simp only [compileE, htc, ct, chdr, clen, List.append_assoc]
      have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.len64t a t)) =
          lkm.totalSize (compileE env.tab nl tmp t) + 3 + lkm.totalSize clen := by
        rw [hce]; dsimp only [ct, chdr]
        simp only [lkm.totalSize_append, lkm.totalSize_cons, lkm.totalSize_nil, Asm.andi, Asm.slli, Asm.add, lkm.itemSize_instr]
      have rt := iht pre ((chdr ++ clen) ++ post) tmp heOk.2 hTmp
        (by rw [show pre ++ ct ++ ((chdr ++ clen) ++ post) = pre ++ compileE env.tab nl tmp (.len64t a t) ++ post from by
            rw [hce]; simp only [List.append_assoc]]; exact hlink)
        (by rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
      rcases _root_.L.evalE_pure t ⟨lm, loc⟩ with ⟨u, hu⟩ | hu
      · simp only [hu] at rt
        obtain ⟨kt, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := rt
        have hevalE : _root_.L.evalE (.len64t a t) ⟨lm, loc⟩ = .ok (lm.len64 (tierA a u), ⟨lm, loc⟩) := by
          change (_root_.L.evalE t >>= fun u' => do return (← get).mem.len64 (tierA a u')) ⟨lm, loc⟩ = _
          dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hu]
          dsimp only [get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind, Pure.pure, StateT.pure,
            Except.pure, Except.bind]
        rw [hevalE]
        have hrel1 := ProgMemRel.of_tempSpan env hlo hhi (by omega) heq1 hmemRel
        have hta := tieredOk_len64_addr_T L.T a u heOk.1
        have hlenR := (hrel1.2.1 (tierA a u) hta.1).2.2.1
        have htw1 : lkm.totalSize (pre ++ ct) = lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp t) :=
          lkm.totalSize_append _ _
        have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ct)) := by rw [htw1]; exact hpc1
        obtain ⟨st2, hrun2, hpc2, ht1_2, hmem2, hpres2, _⟩ :=
          step_tierHdr env (pre ++ ct) (clen ++ post) AbiReg.a0 u
            (by rw [show (pre ++ ct) ++ chdr ++ (clen ++ post) = pre ++ compileE env.tab nl tmp (.len64t a t) ++ post from by
                rw [hce]; simp only [List.append_assoc]]; exact hlink)
            (by rw [htw1]; rw [htw_ce] at h64; omega) st1 hpc1' (hpres1.gp.trans hgp) ha0_1
        have htw2 : lkm.totalSize (pre ++ ct ++ chdr) =
            lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp t) + 3 := by
          rw [lkm.totalSize_append, htw1]; dsimp only [chdr]
          simp only [lkm.totalSize_cons, lkm.totalSize_nil, Asm.andi, Asm.slli, Asm.add, lkm.itemSize_instr]
        have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ct ++ chdr)) := by
          rw [htw2, ← htw1]; exact hpc2
        have halLen : isAligned (st2.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.len64 (TieredArray.t0 a))) 8 = true := by
          rw [ht1_2, hta.2.1, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
        obtain ⟨st3, hrun3, hoth3, ha0_3, hmem3, hpc3⟩ :=
          loadMemOff_ld_correct_lm lkm env.hrom (pre ++ ct ++ chdr) post AbiReg.a0 AbiReg.t1 AbiReg.t2
            (by decide) (by decide) (by decide) (env.tab.len64 (TieredArray.t0 a))
            (by rw [show (pre ++ ct ++ chdr) ++ clen ++ post = pre ++ compileE env.tab nl tmp (.len64t a t) ++ post from by
                rw [hce]; simp only [List.append_assoc]]; exact hlink)
            (by rw [htw2]; rw [htw_ce] at h64; dsimp only [clen] at h64 ⊢; omega) st2 hpc2' halLen
        have hpres3 : PreservedRegs st2 st3 :=
          ⟨hoth3 _ (by decide) (by decide), hoth3 _ (by decide) (by decide),
           hoth3 _ (by decide) (by decide),
           hoth3 _ (by decide) (by decide)⟩
        refine ⟨kt + (3 + lkm.totalSize clen), st3, ?_, ?_, ?_, hpres1.trans (hpres2.trans hpres3), ?_⟩
        · rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3
        · rw [hpc3, htw2, htw_ce]; dsimp only [clen]; congr 2; omega
        · rw [ha0_3, hmem2, ht1_2, hta.2.1, hlenR]; rfl
        · rw [hmem3, hmem2]; exact heq1
      · simp only [hu] at rt
        have hevalE : _root_.L.evalE (.len64t a t) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hu]
        rw [hevalE]; exact rt
  | ld8x8 src i ihi =>
    dsimp only [maxTempsExpr] at hTmp
    have hsrcOk : bsrcOkB env.tab src = true := by
      cases src <;> simp only [exprOkB, Bool.and_eq_true] at heOk <;> exact heOk.1
    have hiOk : exprOkB env.tab nl i = true := by
      cases src <;> simp only [exprOkB, Bool.and_eq_true] at heOk <;> exact heOk.2
    exact prog_ld8x8_sim env L lm loc hlo hhi pre post tmp src i hsrcOk hTmp
      (fun p q t s ht hl h6 hpc' hgp' hsp' hm hf => ihi p q t hiOk ht hl h6 s hpc' hgp' hsp' hm hf)
      hlink h64 st hpc hgp hsp hmemRel hframeOk
  | ld32t a t i iht ihi =>
    simp only [exprOkB, Bool.and_eq_true] at heOk
    exact prog_ld32t_sim env L lm loc hspAlign hlo hhi pre post tmp a t i heOk.1.1 heOk.1.2 hTmp
      (fun p q t' s ht hl h6 hpc' hgp' hsp' hm hf => iht p q t' heOk.1.2 ht hl h6 s hpc' hgp' hsp' hm hf)
      (fun p q t' s ht hl h6 hpc' hgp' hsp' hm hf => ihi p q t' heOk.2 ht hl h6 s hpc' hgp' hsp' hm hf)
      hlink h64 st hpc hgp hsp hmemRel hframeOk
  | ld32h a t i hi iht ihi =>
    simp only [exprOkB, Bool.and_eq_true] at heOk
    dsimp only [maxTempsExpr] at hTmp
    let lwuItem := Asm.lwu AbiReg.a0 AbiReg.t1 (if hi then 4#12 else 0#12)
    have runLwu : ∀ (caddr : List AsmItem) (u vi : _root_.L.Word) (k1 : Nat) (st1 : State)
        (hce : compileE env.tab nl tmp (.ld32h a t i hi) = caddr ++ [lwuItem])
        (hu : _root_.L.evalE t ⟨lm, loc⟩ = .ok (u, ⟨lm, loc⟩))
        (hvi : _root_.L.evalE i ⟨lm, loc⟩ = .ok (vi, ⟨lm, loc⟩))
        (hbound : vi.toNat < (lm.arr64 (tierA a u)).size)
        (hrun1 : RV64.run env.rom k1 st = .cont st1)
        (hpc1 : st1.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize caddr)))
        (ht1_1 : st1.getReg AbiReg.t1 = L.base64 (tierA a u) + BitVec.ofNat 64 (8 * vi.toNat))
        (hpres1 : PreservedRegs st st1)
        (heq1 : MemEqOutside (tempSpan sp nl tmp nt) st.mem st1.mem),
        match _root_.L.evalE (.ld32h a t i hi) ⟨lm, loc⟩ with
        | .ok (v, _) =>
          ∃ k st', RV64.run env.rom k st = .cont st' ∧
            st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp (.ld32h a t i hi)))) ∧
            st'.getReg AbiReg.a0 = v.toBitVec ∧ PreservedRegs st st' ∧
            MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
        | .error _ =>
          ∃ k st', RV64.run env.rom k st = .cont st' ∧
            st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧ PreservedRegs st st' ∧
            MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem := by
      intro caddr u vi k1 st1 hce hu hvi hbound hrun1 hpc1 ht1_1 hpres1 heq1
      have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.ld32h a t i hi)) = lkm.totalSize caddr + 1 := by
        rw [hce, lkm.totalSize_append]; dsimp only [lwuItem]; rw [Asm.lwu, lkm.totalSize_instr]
      have hevalE : _root_.L.evalE (.ld32h a t i hi) ⟨lm, loc⟩ =
          .ok (half32b hi ((lm.arr64 (tierA a u))[vi.toNat]), ⟨lm, loc⟩) := by
        change (_root_.L.evalE t >>= fun u' => _root_.L.evalE i >>= fun idx => do
          let w ← _root_.L.ld64 (tierA a u') idx; return half32b hi w) ⟨lm, loc⟩ = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hu]; dsimp only; rw [hvi]
        dsimp only [_root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
          Pure.pure, StateT.pure, Except.pure, Except.bind]
        simp [hbound]; rfl
      rw [hevalE]
      have hrel1 := ProgMemRel.of_tempSpan env hlo hhi (by omega) heq1 hmemRel
      have hta := tieredOk_len64_addr_T L.T a u heOk.1.1
      have hw := (hrel1.2.1 (tierA a u) hta.1).2.2.2.2 vi.toNat hbound
      have htw1 : lkm.totalSize (pre ++ caddr) = lkm.totalSize pre + lkm.totalSize caddr := lkm.totalSize_append _ _
      have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ caddr)) := by rw [htw1]; exact hpc1
      have hal1 : isAligned (st1.getReg AbiReg.t1 + sextImm12 (if hi then 4#12 else 0#12)) 4 = true := by
        rw [ht1_1]; cases hi
        · rw [show sextImm12 (if false then 4#12 else 0#12) = 0#64 from rfl, BitVec.add_zero]
          exact isAligned4_of_isAligned8 _ (isAligned8_add_mul8 _ (L.h64Align (tierA a u)) vi.toNat)
        · rw [show sextImm12 (if true then 4#12 else 0#12) = 4#64 from rfl]
          exact isAligned4_add_mul4 _ (isAligned8_add_mul8 _ (L.h64Align (tierA a u)) vi.toNat) 1
      let st2 := stepReg st1 AbiReg.a0
        ((loadBytes st1.mem (st1.getReg AbiReg.t1 + sextImm12 (if hi then 4#12 else 0#12)) 4).zeroExtend 64)
        (st1.pc + 4#64)
      obtain ⟨hrun2, hpc2, ha0_2, hoth2, hmem2⟩ :=
        step_lwu_off env (pre ++ caddr) post AbiReg.a0 AbiReg.t1 (if hi then 4#12 else 0#12) (by decide)
          (by rw [show (pre ++ caddr) ++ [Asm.raw (.load .lwu AbiReg.a0 AbiReg.t1 (if hi then 4#12 else 0#12))] ++ post =
              pre ++ compileE env.tab nl tmp (.ld32h a t i hi) ++ post from by
              rw [hce]; simp only [lwuItem, Asm.lwu, Asm.raw, List.append_assoc]]; exact hlink)
          (by rw [htw1]; rw [htw_ce] at h64; omega) st1 hpc1' hal1
      refine ⟨k1 + 1, st2, by rw [run_add, hrun1]; exact hrun2,
        by rw [hpc2, htw1, htw_ce, Nat.add_assoc], ?_,
        hpres1.trans ⟨hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide)⟩,
        by rw [hmem2]; exact heq1⟩
      rw [ha0_2, ht1_1]
      cases hi
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero, loadBytes_zeroExtend32_lo _ _, hw]
        simp only [half32b, Bool.false_eq_true, ↓reduceIte]
        apply BitVec.eq_of_toNat_eq; simp only [UInt64.toNat_toBitVec]
        have hlt64 : ((lm.arr64 (tierA a u))[vi.toNat]).toNat < 2 ^ 64 := ((lm.arr64 (tierA a u))[vi.toNat]).toBitVec.isLt
        rw [UInt64.toNat_mod, UInt64.toNat_ofNat', UInt64.toNat_and,
            show (4294967296 : UInt64).toNat = 2 ^ 32 from rfl,
            show (4294967295 : UInt64).toNat = 2 ^ 32 - 1 from rfl,
            Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt64]
      · simp only [↓reduceIte]
        rw [show sextImm12 4#12 = 4#64 from rfl, loadBytes_zeroExtend32_hi _ _, hw]
        simp only [half32b, ↓reduceIte]
        apply BitVec.eq_of_toNat_eq; simp only [UInt64.toNat_toBitVec]
        have hlt64 : ((lm.arr64 (tierA a u))[vi.toNat]).toNat < 2 ^ 64 := ((lm.arr64 (tierA a u))[vi.toNat]).toBitVec.isLt
        rw [UInt64.toNat_shiftRight, UInt64.toNat_shiftRight, UInt64.toNat_ofNat',
            show (32 : UInt64).toNat % 64 = 32 from rfl, Nat.mod_eq_of_lt hlt64]
    cases htc : t.constVal? with
    | some w =>
      have hteq : t = .const w := expr_constVal_eq_some htc
      have hu : _root_.L.evalE t ⟨lm, loc⟩ = .ok (w, ⟨lm, loc⟩) := by rw [hteq]; rfl
      have hta := tieredOk_len64_addr_T L.T a w heOk.1.1
      let s := tierA a w
      let caddr := compileE env.tab nl tmp i ++
        loadMemOff .ld AbiReg.t2 AbiReg.gp AbiReg.t3 (env.tab.len64 s) ++
        [Asm.bgeu AbiReg.a0 AbiReg.t2 errLabel] ++
        loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t3 (env.tab.base64 s) ++
        [Asm.slli AbiReg.t3 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3]
      have hce : compileE env.tab nl tmp (.ld32h a t i hi) = caddr ++ [lwuItem] := by
        simp only [compileE, htc, s, caddr, lwuItem, List.append_assoc, List.cons_append, List.nil_append]
      have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.ld32h a t i hi)) = lkm.totalSize caddr + 1 := by
        rw [hce, lkm.totalSize_append]; dsimp only [lwuItem]; rw [Asm.lwu, lkm.totalSize_instr]
      have raddr := prog_tiered_const_addr8_sim env L lm loc hlo hhi pre ([lwuItem] ++ post)
        tmp s i hta.1 (by omega)
        (fun p q t' s' ht hl h6 hpc' hgp' hsp' hm hf => ihi p q t' heOk.2 ht hl h6 s' hpc' hgp' hsp' hm hf)
        (by rw [show pre ++ caddr ++ ([lwuItem] ++ post) = pre ++ compileE env.tab nl tmp (.ld32h a t i hi) ++ post from by
            rw [hce]; simp only [List.append_assoc]]; exact hlink)
        (by rw [htw_ce] at h64; dsimp only [caddr] at h64; omega) st hpc hgp hsp hmemRel hframeOk
      rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
      · simp only [hvi] at raddr
        by_cases hbound : vi.toNat < (lm.arr64 s).size
        · simp only [hbound, ↓reduceIte] at raddr
          obtain ⟨k1, st1, hrun1, hpc1, ht1_1, hpres1, heq1⟩ := raddr
          exact runLwu caddr w vi k1 st1 hce hu hvi hbound hrun1 hpc1 ht1_1 hpres1 heq1
        · simp only [hbound, ↓reduceIte] at raddr
          have hevalE : _root_.L.evalE (.ld32h a t i hi) ⟨lm, loc⟩ = .error .oob := by
            change (_root_.L.evalE t >>= fun u' => _root_.L.evalE i >>= fun idx => do
              let w ← _root_.L.ld64 (tierA a u') idx; return half32b hi w) ⟨lm, loc⟩ = _
            dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hu]; dsimp only; rw [hvi]
            dsimp only [_root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
              Pure.pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.pure, Except.bind]
            simp [s, hbound]; rfl
          rw [hevalE]; exact raddr
      · simp only [hvi] at raddr
        have hevalE : _root_.L.evalE (.ld32h a t i hi) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hu, hvi]
        rw [hevalE]; exact raddr
    | none =>
      let caddr := tieredHead env.tab nl tmp t i ++
        [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
         Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
        loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (env.tab.len64 (TieredArray.t0 a)) ++
        [Asm.bgeu AbiReg.a0 AbiReg.t2 errLabel] ++
        loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t3 (env.tab.base64 (TieredArray.t0 a)) ++
        [Asm.slli AbiReg.t3 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3]
      have hce : compileE env.tab nl tmp (.ld32h a t i hi) = caddr ++ [lwuItem] := by
        dsimp only [compileE]; rw [htc]
        cases hs : emitSimpleExpr env.tab AbiReg.t0 AbiReg.t1 t <;>
          simp only [caddr, tieredHead, hs, lwuItem, List.append_assoc, List.cons_append, List.nil_append]
      have htw_ce : lkm.totalSize (compileE env.tab nl tmp (.ld32h a t i hi)) = lkm.totalSize caddr + 1 := by
        rw [hce, lkm.totalSize_append]; dsimp only [lwuItem]; rw [Asm.lwu, lkm.totalSize_instr]
      have raddr := prog_tiered_addr8_sim env L lm loc hspAlign hlo hhi pre ([lwuItem] ++ post)
        tmp a t i heOk.1.1 heOk.1.2 (by omega) (by omega) (by omega)
        (fun p q t' s ht hl h6 hpc' hgp' hsp' hm hf => iht p q t' heOk.1.2 ht hl h6 s hpc' hgp' hsp' hm hf)
        (fun p q t' s ht hl h6 hpc' hgp' hsp' hm hf => ihi p q t' heOk.2 ht hl h6 s hpc' hgp' hsp' hm hf)
        (by rw [show pre ++ caddr ++ ([lwuItem] ++ post) = pre ++ compileE env.tab nl tmp (.ld32h a t i hi) ++ post from by
            rw [hce]; simp only [List.append_assoc]]; exact hlink)
        (by rw [htw_ce] at h64; dsimp only [caddr] at h64 ⊢; omega) st hpc hgp hsp hmemRel hframeOk
      rcases _root_.L.evalE_pure t ⟨lm, loc⟩ with ⟨u, hu⟩ | hu
      · rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
        · simp only [hu, hvi] at raddr ⊢
          by_cases hbound : vi.toNat < (lm.arr64 (tierA a u)).size
          · simp only [hbound, ↓reduceIte] at raddr
            obtain ⟨k1, st1, hrun1, hpc1, ht1_1, hpres1, heq1⟩ := raddr
            exact runLwu caddr u vi k1 st1 hce hu hvi hbound hrun1 hpc1 ht1_1 hpres1 heq1
          · simp only [hbound, ↓reduceIte] at raddr
            have hevalE : _root_.L.evalE (.ld32h a t i hi) ⟨lm, loc⟩ = .error .oob := by
              change (_root_.L.evalE t >>= fun u' => _root_.L.evalE i >>= fun idx => do
                let w ← _root_.L.ld64 (tierA a u') idx; return half32b hi w) ⟨lm, loc⟩ = _
              dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hu]; dsimp only; rw [hvi]
              dsimp only [_root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
                Pure.pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.pure, Except.bind]
              simp [hbound]; rfl
            rw [hevalE]; exact raddr
        · simp only [hu, hvi] at raddr ⊢
          have hevalE : _root_.L.evalE (.ld32h a t i hi) ⟨lm, loc⟩ = .error .oob := by
            simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hu, hvi]
          rw [hevalE]; exact raddr
      · simp only [hu] at raddr ⊢
        have hevalE : _root_.L.evalE (.ld32h a t i hi) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, hu]
        rw [hevalE]; exact raddr

theorem progEvalArgs_sim_aux {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals)
    {sp : BitVec 64} {nl nt : Nat}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (es : List Expr) (pre post : List AsmItem) (tmp : Nat)
    (hesOk : es.all (exprOkB env.tab nl) = true)
    (hTmp : ∀ e idx, (e, idx) ∈ es.zipIdx → tmp + idx + max 1 (maxTempsExpr e) ≤ nt)
    (hlink : lkm.linkSpec (pre ++ compileEvalExprsToTemps env.tab nl tmp es ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (compileEvalExprsToTemps env.tab nl tmp es)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOk L sp st.mem nl loc) :
    match _root_.L.evalArgs es ⟨lm, loc⟩ with
    | .ok (vs, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileEvalExprsToTemps env.tab nl tmp es))) ∧
        vs.length = es.length ∧
        (∀ idx (hidx : idx < vs.length),
          readWord64 st'.mem (sp + BitVec.ofInt 64 (slotOff (nl + tmp + idx))) = vs[idx].toBitVec) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem := by
  induction es generalizing pre post tmp st with
  | nil =>
    simp only [_root_.L.evalArgs, Pure.pure, StateT.pure, Except.pure, compileEvalExprsToTemps,
      lkm.totalSize_nil, Nat.add_zero, List.length_nil]
    exact ⟨0, st, rfl, hpc, trivial, fun _ h => absurd h (Nat.not_lt_zero _), ⟨rfl, rfl, rfl, rfl⟩,
      MemEqOutside.refl _ _⟩
  | cons e es ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hesOk
    have hmem0 : (e, 0) ∈ (e :: es).zipIdx := by simp [List.zipIdx]
    have hTmpE := hTmp e 0 hmem0
    have hTmpRest : ∀ e' idx, (e', idx) ∈ es.zipIdx → (tmp + 1) + idx + max 1 (maxTempsExpr e') ≤ nt := by
      intro e' idx hm
      have hm' : (e', idx + 1) ∈ (e :: es).zipIdx := (mem_zipIdx_cons_succ e e' es idx).mpr hm
      have h := hTmp e' (idx + 1) hm'; omega
    let crest := compileEvalExprsToTemps env.tab nl (tmp + 1) es
    have hf : (frameSpan sp nl nt).valid := by
      simp only [frameSpan, MemSpan.valid]; have := L.hStackValid; omega
    by_cases he0 : e.constVal? = some 0
    · have heeq : e = .const 0 := expr_constVal_eq_some he0
      have hv : _root_.L.evalE e ⟨lm, loc⟩ = .ok (0, ⟨lm, loc⟩) := by rw [heeq]; rfl
      let cs0 := storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t0 (slotOff (nl + tmp))
      have hdef : compileEvalExprsToTemps env.tab nl tmp (e :: es) = cs0 ++ crest := by
        simp only [compileEvalExprsToTemps, he0, beq_self_eq_true, ↓reduceIte, cs0, crest]
      have htw_all : lkm.totalSize (compileEvalExprsToTemps env.tab nl tmp (e :: es)) =
          lkm.totalSize cs0 + lkm.totalSize (compileEvalExprsToTemps env.tab nl (tmp + 1) es) := by
        rw [hdef]; dsimp only [crest]; exact lkm.totalSize_append _ _
      have halS : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff (nl + tmp))) 8 = true := by
        rw [hsp, slotOff_ofInt]; exact isAligned8_add_int_mul8 sp hspAlign _
      obtain ⟨st2, hrunS, hothS, hmemS, hpc2⟩ :=
        storeMemOff_sd_correct_lm lkm env.hrom pre (crest ++ post) AbiReg.sp AbiReg.zero AbiReg.t0
          (by decide) (by decide) (by decide) (slotOff (nl + tmp))
          (by rw [show pre ++ cs0 ++ (crest ++ post) = pre ++ compileEvalExprsToTemps env.tab nl tmp (e :: es) ++ post from by
              rw [hdef]; simp only [List.append_assoc]]; exact hlink)
          (by rw [htw_all] at h64; dsimp only [cs0] at h64 ⊢; omega) st hpc halS
      have hpresS : PreservedRegs st st2 :=
        ⟨hothS _ (by decide), hothS _ (by decide), hothS _ (by decide), hothS _ (by decide)⟩
      have heq02 : MemEqOutside (tempSpan sp nl tmp nt) st.mem st2.mem := by
        rw [hmemS, hsp, slotOff_ofInt]
        apply MemEqOutside.writeWord64
        intro k hk; exact tempSpan_slot_sub (Nat.le_refl tmp) (by omega) k hk
      have htw2 : lkm.totalSize (pre ++ cs0) = lkm.totalSize pre + lkm.totalSize cs0 := lkm.totalSize_append _ _
      have rrest := ih (pre ++ cs0) post (tmp + 1) hesOk.2 hTmpRest
        (by rw [show (pre ++ cs0) ++ crest ++ post = pre ++ compileEvalExprsToTemps env.tab nl tmp (e :: es) ++ post from by
            rw [hdef]; simp only [List.append_assoc]]; exact hlink)
        (by rw [htw2]; rw [htw_all] at h64; omega) st2 (by rw [htw2]; exact hpc2)
        (hpresS.gp.trans hgp) (hpresS.sp.trans hsp)
        (ProgMemRel.of_tempSpan env hlo hhi (by omega) heq02 hmemRel)
        (ProgFrameOk.of_tempSpan hf (by omega) heq02 hframeOk)
      rcases _root_.L.evalArgs_pure es ⟨lm, loc⟩ with ⟨vs, hvs⟩ | hvs
      · simp only [hvs] at rrest
        obtain ⟨k2, st3, hrun2, hpc3, hlen, hslots, hpres2, heq2⟩ := rrest
        have heval : _root_.L.evalArgs (e :: es) ⟨lm, loc⟩ = .ok ((0 : _root_.L.Word) :: vs, ⟨lm, loc⟩) := by
          change (_root_.L.evalE e >>= fun v' => _root_.L.evalArgs es >>= fun vs' => pure (v' :: vs')) ⟨lm, loc⟩ = _
          dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hv]; dsimp only; rw [hvs]; rfl
        rw [heval]
        have heq2' : MemEqOutside (tempSpan sp nl tmp nt) st2.mem st3.mem :=
          heq2.mono (tempSpan_mono (Nat.le_succ tmp) (by omega))
        refine ⟨lkm.totalSize cs0 + k2, st3,
          by rw [run_add, hrunS]; dsimp only; exact hrun2,
          by rw [hpc3, htw2, htw_all]; congr 2; omega,
          by simp [hlen], ?_, hpresS.trans hpres2, heq02.trans heq2'⟩
        intro idx hidx
        cases idx with
        | zero =>
          simp only [Nat.add_zero, List.getElem_cons_zero]
          have h2 : readWord64 st2.mem (sp + BitVec.ofInt 64 (slotOff (nl + tmp))) = (0 : _root_.L.Word).toBitVec := by
            rw [hmemS, hsp, show st.getReg AbiReg.zero = 0#64 from rfl]
            exact readWord64_writeWord64_self st.mem _ _
          rw [← h2]
          apply MemEqOutside.readWord64_eq heq2
          intro k hk; rw [slotOff_ofInt]
          exact (slotSpan_memDisjoint_tempSpan hf (by omega) (by omega)) _ ⟨k, hk, rfl⟩
        | succ idx' =>
          simp only [List.getElem_cons_succ]
          rw [show nl + tmp + (idx' + 1) = nl + (tmp + 1) + idx' by omega]
          exact hslots idx' (by simpa using hidx)
      · simp only [hvs] at rrest
        obtain ⟨k2, st3, hrun2, hpc3, hpres2, heq2⟩ := rrest
        have heval : _root_.L.evalArgs (e :: es) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.evalArgs, Bind.bind, StateT.bind, Except.bind, hv, hvs]
        rw [heval]
        have heq2' : MemEqOutside (tempSpan sp nl tmp nt) st2.mem st3.mem :=
          heq2.mono (tempSpan_mono (Nat.le_succ tmp) (by omega))
        exact ⟨lkm.totalSize cs0 + k2, st3,
          by rw [run_add, hrunS]; dsimp only; exact hrun2,
          hpc3, hpresS.trans hpres2, heq02.trans heq2'⟩
    · have hne0 : (e.constVal? == some 0) = false := beq_false_of_ne he0
      let ce := compileE env.tab nl tmp e
      let cs := storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + tmp))
      have hdef : compileEvalExprsToTemps env.tab nl tmp (e :: es) = ce ++ cs ++ crest := by
        simp only [compileEvalExprsToTemps, hne0, Bool.false_eq_true, ↓reduceIte, ce, cs, crest, List.append_assoc]
      have htw_all : lkm.totalSize (compileEvalExprsToTemps env.tab nl tmp (e :: es)) =
          lkm.totalSize (compileE env.tab nl tmp e) + lkm.totalSize cs + lkm.totalSize (compileEvalExprsToTemps env.tab nl (tmp + 1) es) := by
        rw [hdef]; dsimp only [ce, crest]; simp only [lkm.totalSize_append]
      have re := progEvalExpr_sim env L lm loc hspAlign hlo hhi e pre ((cs ++ crest) ++ post) tmp
        hesOk.1 (by omega)
        (by rw [show pre ++ ce ++ ((cs ++ crest) ++ post) = pre ++ compileEvalExprsToTemps env.tab nl tmp (e :: es) ++ post from by
            rw [hdef]; simp only [List.append_assoc]]; exact hlink)
        (by rw [htw_all] at h64; omega) st hpc hgp hsp hmemRel hframeOk
      rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨v, hv⟩ | hv
      · simp only [hv] at re
        obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := re
        have htw1 : lkm.totalSize (pre ++ ce) = lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp e) :=
          lkm.totalSize_append _ _
        have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ce)) := by rw [htw1]; exact hpc1
        have halS : isAligned (st1.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff (nl + tmp))) 8 = true := by
          rw [hpres1.sp.trans hsp, slotOff_ofInt]; exact isAligned8_add_int_mul8 sp hspAlign _
        obtain ⟨st2, hrunS, hothS, hmemS, hpc2⟩ :=
          storeMemOff_sd_correct_lm lkm env.hrom (pre ++ ce) (crest ++ post) AbiReg.sp AbiReg.a0 AbiReg.t0
            (by decide) (by decide) (by decide) (slotOff (nl + tmp))
            (by rw [show (pre ++ ce) ++ cs ++ (crest ++ post) = pre ++ compileEvalExprsToTemps env.tab nl tmp (e :: es) ++ post from by
                rw [hdef]; simp only [List.append_assoc]]; exact hlink)
            (by rw [htw1]; rw [htw_all] at h64; dsimp only [cs] at h64 ⊢; omega) st1 hpc1' halS
        have hpresS : PreservedRegs st1 st2 :=
          ⟨hothS _ (by decide), hothS _ (by decide), hothS _ (by decide), hothS _ (by decide)⟩
        have heqS : MemEqOutside (tempSpan sp nl tmp nt) st1.mem st2.mem := by
          rw [hmemS, hpres1.sp.trans hsp, slotOff_ofInt]
          apply MemEqOutside.writeWord64
          intro k hk
          exact tempSpan_slot_sub (Nat.le_refl tmp) (by omega) k hk
        have heq02 : MemEqOutside (tempSpan sp nl tmp nt) st.mem st2.mem := heq1.trans heqS
        have htw2 : lkm.totalSize (pre ++ ce ++ cs) =
            lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp e) + lkm.totalSize cs := by
          rw [lkm.totalSize_append, htw1]
        have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ ce ++ cs)) := by
          rw [htw2, ← htw1]; exact hpc2
        have rrest := ih (pre ++ ce ++ cs) post (tmp + 1) hesOk.2 hTmpRest
          (by rw [show (pre ++ ce ++ cs) ++ crest ++ post = pre ++ compileEvalExprsToTemps env.tab nl tmp (e :: es) ++ post from by
              rw [hdef]; simp only [List.append_assoc]]; exact hlink)
          (by rw [htw2]; rw [htw_all] at h64; omega) st2 hpc2'
          (hpresS.gp.trans (hpres1.gp.trans hgp)) (hpresS.sp.trans (hpres1.sp.trans hsp))
          (ProgMemRel.of_tempSpan env hlo hhi (by omega) heq02 hmemRel)
          (ProgFrameOk.of_tempSpan hf (by omega) heq02 hframeOk)
        rcases _root_.L.evalArgs_pure es ⟨lm, loc⟩ with ⟨vs, hvs⟩ | hvs
        · simp only [hvs] at rrest
          obtain ⟨k2, st3, hrun2, hpc3, hlen, hslots, hpres2, heq2⟩ := rrest
          have heval : _root_.L.evalArgs (e :: es) ⟨lm, loc⟩ = .ok (v :: vs, ⟨lm, loc⟩) := by
            change (_root_.L.evalE e >>= fun v' => _root_.L.evalArgs es >>= fun vs' => pure (v' :: vs')) ⟨lm, loc⟩ = _
            dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hv]; dsimp only; rw [hvs]
            rfl
          rw [heval]
          have heq2' : MemEqOutside (tempSpan sp nl tmp nt) st2.mem st3.mem :=
            heq2.mono (tempSpan_mono (Nat.le_succ tmp) (by omega))
          refine ⟨k1 + (lkm.totalSize cs + k2), st3, ?_, ?_, by simp [hlen], ?_,
            (hpres1.trans hpresS).trans hpres2, heq02.trans heq2'⟩
          · rw [run_add, hrun1]; dsimp only; rw [run_add, hrunS]; dsimp only; exact hrun2
          · rw [hpc3, htw2, htw_all]; dsimp only [cs]; congr 2; omega
          · intro idx hidx
            cases idx with
            | zero =>
              simp only [Nat.add_zero, List.getElem_cons_zero]
              have h2 : readWord64 st2.mem (sp + BitVec.ofInt 64 (slotOff (nl + tmp))) = v.toBitVec := by
                rw [hmemS, hpres1.sp.trans hsp, ha0_1]; exact readWord64_writeWord64_self st1.mem _ _
              rw [← h2]
              apply MemEqOutside.readWord64_eq heq2
              intro k hk
              rw [slotOff_ofInt]
              exact (slotSpan_memDisjoint_tempSpan hf (by omega) (by omega)) _ ⟨k, hk, rfl⟩
            | succ idx' =>
              simp only [List.getElem_cons_succ]
              rw [show nl + tmp + (idx' + 1) = nl + (tmp + 1) + idx' by omega]
              exact hslots idx' (by simpa using hidx)
        · simp only [hvs] at rrest
          obtain ⟨k2, st3, hrun2, hpc3, hpres2, heq2⟩ := rrest
          have heval : _root_.L.evalArgs (e :: es) ⟨lm, loc⟩ = .error .oob := by
            simp [_root_.L.evalArgs, Bind.bind, StateT.bind, Except.bind, hv, hvs]
          rw [heval]
          have heq2' : MemEqOutside (tempSpan sp nl tmp nt) st2.mem st3.mem :=
            heq2.mono (tempSpan_mono (Nat.le_succ tmp) (by omega))
          exact ⟨k1 + (lkm.totalSize cs + k2), st3,
            by rw [run_add, hrun1]; dsimp only; rw [run_add, hrunS]; dsimp only; exact hrun2,
            hpc3, (hpres1.trans hpresS).trans hpres2, heq02.trans heq2'⟩
      · simp only [hv] at re
        have heval : _root_.L.evalArgs (e :: es) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.evalArgs, Bind.bind, StateT.bind, Except.bind, hv]
        rw [heval]; exact re

theorem progEvalArgs_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals)
    {sp : BitVec 64} {nl nt : Nat}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (es : List Expr) (pre post : List AsmItem) (tmp : Nat)
    (hesOk : es.all (exprOkB env.tab nl) = true)
    (hTmp : tmp + maxTempsExprs es ≤ nt)
    (hlink : lkm.linkSpec (pre ++ compileEvalExprsToTemps env.tab nl tmp es ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (compileEvalExprsToTemps env.tab nl tmp es)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOk L sp st.mem nl loc) :
    match _root_.L.evalArgs es ⟨lm, loc⟩ with
    | .ok (vs, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileEvalExprsToTemps env.tab nl tmp es))) ∧
        vs.length = es.length ∧
        (∀ idx (hidx : idx < vs.length),
          readWord64 st'.mem (sp + BitVec.ofInt 64 (slotOff (nl + tmp + idx))) = vs[idx].toBitVec) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem := by
  apply progEvalArgs_sim_aux env L lm loc hspAlign hlo hhi es pre post tmp hesOk
    _ hlink h64 st hpc hgp hsp hmemRel hframeOk
  intro e idx hmem
  have hm := foldl_max_mem (f := fun (p : Expr × Nat) => p.2 + max 1 (maxTempsExpr p.1))
    (xs := es.zipIdx) (init := 0) (x := (e, idx)) hmem
  dsimp only [maxTempsExprs] at hTmp
  dsimp only at hm
  omega

def progCmpBrItem (op : Cmp) (want : Bool) (target : String) : AsmItem :=
  match op, want with
  | .eq, true   | .ne, false  => Asm.beq AbiReg.t0 AbiReg.a0 target
  | .ne, true   | .eq, false  => Asm.bne AbiReg.t0 AbiReg.a0 target
  | .ult, true  => Asm.bltu AbiReg.t0 AbiReg.a0 target
  | .ult, false => Asm.bgeu AbiReg.t0 AbiReg.a0 target
  | .ule, true  => Asm.bgeu AbiReg.a0 AbiReg.t0 target
  | .ule, false => Asm.bltu AbiReg.a0 AbiReg.t0 target
  | .slt, true  => Asm.blt AbiReg.t0 AbiReg.a0 target
  | .slt, false => Asm.bge AbiReg.t0 AbiReg.a0 target
  | .sle, true  => Asm.bge AbiReg.a0 AbiReg.t0 target
  | .sle, false => Asm.blt AbiReg.a0 AbiReg.t0 target

theorem progCmpBrItem_step {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (op : Cmp) (want : Bool) (target : String) (tgt : Nat)
    (va vb : _root_.L.Word) (st1 : State)
    (htgt : lookupLabel env.labels target = some tgt)
    (hlink : lkm.linkSpec (pre ++ [progCmpBrItem op want target] ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize [progCmpBrItem op want target]) < 2 ^ 64)
    (hpc1 : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (ht0 : st1.getReg AbiReg.t0 = va.toBitVec)
    (ha0 : st1.getReg AbiReg.a0 = vb.toBitVec) :
    ∃ k st2,
      RV64.run env.rom k st1 = .cont st2 ∧
      st2.pc = BitVec.ofNat 64
        (4 * (if op.eval va vb == want then tgt else lkm.totalSize pre + lkm.totalSize [progCmpBrItem op want target])) ∧
      PreservedRegs st1 st2 ∧
      st2.mem = st1.mem := by
  have stepAux : ∀ (bop : BranchOp) (rs1 rs2 : Reg)
      (hbr : progCmpBrItem op want target = .br bop rs1 rs2 target)
      (hrs : rs1 ≠ AbiReg.t6 ∧ rs2 ≠ AbiReg.t6)
      (hev : evalBranch bop (st1.getReg rs1) (st1.getReg rs2) = (op.eval va vb == want)),
      ∃ k st2,
        RV64.run env.rom k st1 = .cont st2 ∧
        st2.pc = BitVec.ofNat 64
          (4 * (if op.eval va vb == want then tgt else lkm.totalSize pre + lkm.totalSize [progCmpBrItem op want target])) ∧
        PreservedRegs st1 st2 ∧
        st2.mem = st1.mem := by
    intro bop rs1 rs2 hbr hrs hev
    rw [hbr] at hlink h64 ⊢
    rw [lkm.totalSize_singleton] at h64 ⊢
    obtain ⟨k, st2, _, hrun, hpc2, _, hpres, hmem⟩ :=
      prog_step_br env pre post bop rs1 rs2 target tgt htgt hrs hlink h64 st1 hpc1
    refine ⟨k, st2, hrun, ?_, hpres, hmem⟩
    rw [hpc2, hev]
    cases (op.eval va vb == want) <;> rfl
  cases op <;> cases want
  · exact stepAux .bne AbiReg.t0 AbiReg.a0 rfl (by decide)
      (by simp [evalBranch, ht0, ha0, Cmp.eval, uint64_cmp_eq, bne])
  · exact stepAux .beq AbiReg.t0 AbiReg.a0 rfl (by decide)
      (by simp [evalBranch, ht0, ha0, Cmp.eval, uint64_cmp_eq])
  · exact stepAux .beq AbiReg.t0 AbiReg.a0 rfl (by decide)
      (by simp [evalBranch, ht0, ha0, Cmp.eval, bne, uint64_cmp_eq])
  · exact stepAux .bne AbiReg.t0 AbiReg.a0 rfl (by decide)
      (by simp [evalBranch, ht0, ha0, Cmp.eval, uint64_cmp_eq, bne])
  · exact stepAux .bgeu AbiReg.t0 AbiReg.a0 rfl (by decide)
      (by simp [evalBranch, ht0, ha0, Cmp.eval, ← uint64_cmp_ult])
  · exact stepAux .bltu AbiReg.t0 AbiReg.a0 rfl (by decide)
      (by simp [evalBranch, ht0, ha0, Cmp.eval, ← uint64_cmp_ult])
  · exact stepAux .bltu AbiReg.a0 AbiReg.t0 rfl (by decide)
      (by simp [evalBranch, ht0, ha0, Cmp.eval, uint64_cmp_ule])
  · exact stepAux .bgeu AbiReg.a0 AbiReg.t0 rfl (by decide)
      (by simp [evalBranch, ht0, ha0, Cmp.eval, uint64_cmp_ule])
  · exact stepAux .bge AbiReg.t0 AbiReg.a0 rfl (by decide)
      (by simp [evalBranch, ht0, ha0, Cmp.eval, ← uint64_cmp_slt])
  · exact stepAux .blt AbiReg.t0 AbiReg.a0 rfl (by decide)
      (by simp [evalBranch, ht0, ha0, Cmp.eval, ← uint64_cmp_slt])
  · exact stepAux .blt AbiReg.a0 AbiReg.t0 rfl (by decide)
      (by simp [evalBranch, ht0, ha0, Cmp.eval, uint64_cmp_sle])
  · exact stepAux .bge AbiReg.a0 AbiReg.t0 rfl (by decide)
      (by simp [evalBranch, ht0, ha0, Cmp.eval, uint64_cmp_sle])

theorem progEvalCond_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals)
    {sp : BitVec 64} {nl nt : Nat}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (c : Cond) (pre post : List AsmItem) (tmp : Nat) (pfx : String) (lblId : Nat)
    (want : Bool) (target : String) (tgt : Nat)
    (hcOk : condOkB env.tab nl c = true) (hTmp : tmp + maxTempsCond c ≤ nt)
    (htgt : lookupLabel env.labels target = some tgt)
    (hlink : lkm.linkSpec (pre ++ (compileC env.tab nl tmp pfx lblId c want target).1 ++ post) =
      .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (compileC env.tab nl tmp pfx lblId c want target).1) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOk L sp st.mem nl loc) :
    match _root_.L.evalC c ⟨lm, loc⟩ with
    | .ok (b, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (if b == want then tgt else
          lkm.totalSize pre + lkm.totalSize (compileC env.tab nl tmp pfx lblId c want target).1)) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem := by
  induction c generalizing pre post tmp pfx lblId want target tgt st with
  | cmp op a b =>
    simp only [condOkB, Bool.and_eq_true] at hcOk
    dsimp only [maxTempsCond] at hTmp
    by_cases hb0 : b.constVal? = some 0
    · have hbeq : b = .const 0 := expr_constVal_eq_some hb0
      have hvb : _root_.L.evalE b ⟨lm, loc⟩ = .ok (0, ⟨lm, loc⟩) := by rw [hbeq]; rfl
      have hcc : (compileC env.tab nl tmp pfx lblId (.cmp op a b) want target).1 =
          compileE env.tab nl tmp a ++ [brCmp op want AbiReg.a0 AbiReg.zero target] := by
        simp only [compileC, hb0, beq_self_eq_true, ↓reduceIte]
      have htw_cc : lkm.totalSize (compileC env.tab nl tmp pfx lblId (.cmp op a b) want target).1 =
          lkm.totalSize (compileE env.tab nl tmp a) + lkm.itemSize (brCmp op want AbiReg.a0 AbiReg.zero target) := by
        rw [hcc, lkm.totalSize_append, lkm.totalSize_singleton]
      have ra := progEvalExpr_sim env L lm loc hspAlign hlo hhi a pre
        ([brCmp op want AbiReg.a0 AbiReg.zero target] ++ post) tmp hcOk.1 (by omega)
        (by simpa only [hcc, List.append_assoc] using hlink)
        (by rw [htw_cc] at h64; omega) st hpc hgp hsp hmemRel hframeOk
      rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va, hva⟩ | hva
      · simp only [hva] at ra
        obtain ⟨ka, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ra
        have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .ok (op.eval va 0, ⟨lm, loc⟩) := by
          simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
        rw [heval]
        have htw1 : lkm.totalSize (pre ++ compileE env.tab nl tmp a) =
            lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp a) := lkm.totalSize_append _ _
        obtain ⟨kbr, st2, _, hrunBr, hpc2, hpres2, hmem2⟩ :=
          brCmp_step_lm lkm env (pre ++ compileE env.tab nl tmp a) post op want
            AbiReg.a0 AbiReg.zero (by decide) (by decide) target tgt va 0 st1 htgt
            (by simpa only [hcc, List.append_assoc] using hlink)
            (by rw [htw1, Nat.add_assoc, ← htw_cc]; exact h64)
            (by rw [htw1]; exact hpc1) ha0_1 rfl
        exact ⟨ka + kbr, st2, by rw [run_add, hrun1]; exact hrunBr,
          by rw [hpc2, htw1, Nat.add_assoc, ← htw_cc], hpres1.trans hpres2,
          by rw [hmem2]; exact heq1⟩
      · simp only [hva] at ra
        have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva]
        rw [heval]; exact ra
    · have hfb0 : (b.constVal? == some 0) = false := beq_false_of_ne hb0
      by_cases ha0 : a.constVal? = some 0
      · have haeq : a = .const 0 := expr_constVal_eq_some ha0
        have hva : _root_.L.evalE a ⟨lm, loc⟩ = .ok (0, ⟨lm, loc⟩) := by rw [haeq]; rfl
        have hcc : (compileC env.tab nl tmp pfx lblId (.cmp op a b) want target).1 =
            compileE env.tab nl tmp b ++ [brCmp op want AbiReg.zero AbiReg.a0 target] := by
          simp only [compileC, hfb0, Bool.false_eq_true, ↓reduceIte, ha0, beq_self_eq_true]
        have htw_cc : lkm.totalSize (compileC env.tab nl tmp pfx lblId (.cmp op a b) want target).1 =
            lkm.totalSize (compileE env.tab nl tmp b) + lkm.itemSize (brCmp op want AbiReg.zero AbiReg.a0 target) := by
          rw [hcc, lkm.totalSize_append, lkm.totalSize_singleton]
        have rb := progEvalExpr_sim env L lm loc hspAlign hlo hhi b pre
          ([brCmp op want AbiReg.zero AbiReg.a0 target] ++ post) tmp hcOk.2 (by omega)
          (by simpa only [hcc, List.append_assoc] using hlink)
          (by rw [htw_cc] at h64; omega) st hpc hgp hsp hmemRel hframeOk
        rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
        · simp only [hvb] at rb
          obtain ⟨kb, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := rb
          have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .ok (op.eval 0 vb, ⟨lm, loc⟩) := by
            simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
          rw [heval]
          have htw1 : lkm.totalSize (pre ++ compileE env.tab nl tmp b) =
              lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp b) := lkm.totalSize_append _ _
          obtain ⟨kbr, st2, _, hrunBr, hpc2, hpres2, hmem2⟩ :=
            brCmp_step_lm lkm env (pre ++ compileE env.tab nl tmp b) post op want
              AbiReg.zero AbiReg.a0 (by decide) (by decide) target tgt 0 vb st1 htgt
              (by simpa only [hcc, List.append_assoc] using hlink)
              (by rw [htw1, Nat.add_assoc, ← htw_cc]; exact h64)
              (by rw [htw1]; exact hpc1) rfl ha0_1
          exact ⟨kb + kbr, st2, by rw [run_add, hrun1]; exact hrunBr,
            by rw [hpc2, htw1, Nat.add_assoc, ← htw_cc], hpres1.trans hpres2,
            by rw [hmem2]; exact heq1⟩
        · simp only [hvb] at rb
          have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .error .oob := by
            simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb]
          rw [heval]; exact rb
      · have hfa0 : (a.constVal? == some 0) = false := beq_false_of_ne ha0
        cases hsb : emitSimpleExpr env.tab AbiReg.t0 AbiReg.t1 b with
        | some cb =>
          have hcc : (compileC env.tab nl tmp pfx lblId (.cmp op a b) want target).1 =
              compileE env.tab nl tmp a ++ cb ++ [brCmp op want AbiReg.a0 AbiReg.t0 target] := by
            simp only [compileC, hfb0, hfa0, Bool.false_eq_true, ↓reduceIte, hsb, List.append_assoc]
          have htw_cc : lkm.totalSize (compileC env.tab nl tmp pfx lblId (.cmp op a b) want target).1 =
              lkm.totalSize (compileE env.tab nl tmp a) + lkm.totalSize cb +
                lkm.itemSize (brCmp op want AbiReg.a0 AbiReg.t0 target) := by
            rw [hcc, lkm.totalSize_append, lkm.totalSize_append, lkm.totalSize_singleton]
          have ra := progEvalExpr_sim env L lm loc hspAlign hlo hhi a pre
            (cb ++ [brCmp op want AbiReg.a0 AbiReg.t0 target] ++ post) tmp hcOk.1 (by omega)
            (by simpa only [hcc, List.append_assoc] using hlink)
            (by rw [htw_cc] at h64; omega) st hpc hgp hsp hmemRel hframeOk
          rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va, hva⟩ | hva
          · simp only [hva] at ra
            obtain ⟨ka, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ra
            have hf : (frameSpan sp nl nt).valid := by
              simp only [frameSpan, MemSpan.valid]; have := L.hStackValid; omega
            have htw1 : lkm.totalSize (pre ++ compileE env.tab nl tmp a) =
                lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp a) := lkm.totalSize_append _ _
            obtain ⟨vb, kb, st2, hvb, hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
              prog_emitSimpleExpr_sim env L lm loc hspAlign (pre ++ compileE env.tab nl tmp a)
                ([brCmp op want AbiReg.a0 AbiReg.t0 target] ++ post)
                AbiReg.t0 AbiReg.t1 (by decide) (by decide) (by decide) (by decide) (by decide)
                b cb hsb hcOk.2 (by simpa only [hcc, List.append_assoc] using hlink)
                (by rw [htw1]; rw [htw_cc] at h64; omega) st1 (by rw [htw1]; exact hpc1)
                (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
                (ProgMemRel.of_tempSpan env hlo hhi (by omega) heq1 hmemRel)
                (ProgFrameOk.of_tempSpan hf (by omega) heq1 hframeOk)
            have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .ok (op.eval va vb, ⟨lm, loc⟩) := by
              simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
            rw [heval]
            have hpres2 : PreservedRegs st1 st2 :=
              ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
               hoth2 _ (by decide) (by decide),
               hoth2 _ (by decide) (by decide)⟩
            have htw2 : lkm.totalSize (pre ++ compileE env.tab nl tmp a ++ cb) =
                lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp a) + lkm.totalSize cb := by
              rw [lkm.totalSize_append, htw1]
            obtain ⟨kbr, st3, _, hrunBr, hpc3, hpres3, hmem3⟩ :=
              brCmp_step_lm lkm env (pre ++ compileE env.tab nl tmp a ++ cb) post op want
                AbiReg.a0 AbiReg.t0 (by decide) (by decide) target tgt va vb st2 htgt
                (by simpa only [hcc, List.append_assoc] using hlink)
                (by rw [htw2]; rw [htw_cc] at h64; omega)
                (by rw [htw2, ← htw1]; exact hpc2)
                ((hoth2 _ (by decide) (by decide)).trans ha0_1) ht0_2
            exact ⟨ka + (kb + kbr), st3,
              by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrunBr,
              by rw [hpc3, htw2, htw_cc]; cases (op.eval va vb == want) <;> simp [Nat.add_assoc],
              (hpres1.trans hpres2).trans hpres3, by rw [hmem3, hmem2]; exact heq1⟩
          · simp only [hva] at ra
            have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .error .oob := by
              simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva]
            rw [heval]; exact ra
        | none =>
          cases hsa : emitSimpleExpr env.tab AbiReg.t0 AbiReg.t1 a with
          | some ca =>
            have hcc : (compileC env.tab nl tmp pfx lblId (.cmp op a b) want target).1 =
                compileE env.tab nl tmp b ++ ca ++ [brCmp op want AbiReg.t0 AbiReg.a0 target] := by
              simp only [compileC, hfb0, hfa0, Bool.false_eq_true, ↓reduceIte, hsb, hsa, List.append_assoc]
            have htw_cc : lkm.totalSize (compileC env.tab nl tmp pfx lblId (.cmp op a b) want target).1 =
                lkm.totalSize (compileE env.tab nl tmp b) + lkm.totalSize ca +
                  lkm.itemSize (brCmp op want AbiReg.t0 AbiReg.a0 target) := by
              rw [hcc, lkm.totalSize_append, lkm.totalSize_append, lkm.totalSize_singleton]
            have rb := progEvalExpr_sim env L lm loc hspAlign hlo hhi b pre
              (ca ++ [brCmp op want AbiReg.t0 AbiReg.a0 target] ++ post) tmp hcOk.2 (by omega)
              (by simpa only [hcc, List.append_assoc] using hlink)
              (by rw [htw_cc] at h64; omega) st hpc hgp hsp hmemRel hframeOk
            rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
            · simp only [hvb] at rb
              obtain ⟨kb, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := rb
              have hf : (frameSpan sp nl nt).valid := by
                simp only [frameSpan, MemSpan.valid]; have := L.hStackValid; omega
              have htw1 : lkm.totalSize (pre ++ compileE env.tab nl tmp b) =
                  lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp b) := lkm.totalSize_append _ _
              obtain ⟨va, ka, st2, hva, hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
                prog_emitSimpleExpr_sim env L lm loc hspAlign (pre ++ compileE env.tab nl tmp b)
                  ([brCmp op want AbiReg.t0 AbiReg.a0 target] ++ post)
                  AbiReg.t0 AbiReg.t1 (by decide) (by decide) (by decide) (by decide) (by decide)
                  a ca hsa hcOk.1 (by simpa only [hcc, List.append_assoc] using hlink)
                  (by rw [htw1]; rw [htw_cc] at h64; omega) st1 (by rw [htw1]; exact hpc1)
                  (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
                  (ProgMemRel.of_tempSpan env hlo hhi (by omega) heq1 hmemRel)
                  (ProgFrameOk.of_tempSpan hf (by omega) heq1 hframeOk)
              have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .ok (op.eval va vb, ⟨lm, loc⟩) := by
                simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
              rw [heval]
              have hpres2 : PreservedRegs st1 st2 :=
                ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
                 hoth2 _ (by decide) (by decide),
                 hoth2 _ (by decide) (by decide)⟩
              have htw2 : lkm.totalSize (pre ++ compileE env.tab nl tmp b ++ ca) =
                  lkm.totalSize pre + lkm.totalSize (compileE env.tab nl tmp b) + lkm.totalSize ca := by
                rw [lkm.totalSize_append, htw1]
              obtain ⟨kbr, st3, _, hrunBr, hpc3, hpres3, hmem3⟩ :=
                brCmp_step_lm lkm env (pre ++ compileE env.tab nl tmp b ++ ca) post op want
                  AbiReg.t0 AbiReg.a0 (by decide) (by decide) target tgt va vb st2 htgt
                  (by simpa only [hcc, List.append_assoc] using hlink)
                  (by rw [htw2]; rw [htw_cc] at h64; omega)
                  (by rw [htw2, ← htw1]; exact hpc2)
                  ht0_2 ((hoth2 _ (by decide) (by decide)).trans ha0_1)
              exact ⟨kb + (ka + kbr), st3,
                by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrunBr,
                by rw [hpc3, htw2, htw_cc]; cases (op.eval va vb == want) <;> simp [Nat.add_assoc],
                (hpres1.trans hpres2).trans hpres3, by rw [hmem3, hmem2]; exact heq1⟩
            · simp only [hvb] at rb
              have hPureA : ∃ va, _root_.L.evalE a ⟨lm, loc⟩ = .ok (va, ⟨lm, loc⟩) := by
                cases a <;> simp [emitSimpleExpr] at hsa <;> exact ⟨_, rfl⟩
              obtain ⟨va, hva⟩ := hPureA
              have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .error .oob := by
                simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb]
              rw [heval]; exact rb
          | none =>
            let seq := compileE env.tab nl tmp a ++
              storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + tmp)) ++
              compileE env.tab nl (tmp + 1) b ++
              loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nl + tmp))
            have hcc : (compileC env.tab nl tmp pfx lblId (.cmp op a b) want target).1 =
                seq ++ [brCmp op want AbiReg.t0 AbiReg.a0 target] := by
              simp only [compileC, hfb0, hfa0, Bool.false_eq_true, ↓reduceIte, hsb, hsa, seq, List.append_assoc]
            have htw_cc : lkm.totalSize (compileC env.tab nl tmp pfx lblId (.cmp op a b) want target).1 =
                lkm.totalSize seq + lkm.itemSize (brCmp op want AbiReg.t0 AbiReg.a0 target) := by
              rw [hcc, lkm.totalSize_append, lkm.totalSize_singleton]
            have rseq := prog_two_exprs_pair_sim env L lm loc hspAlign hlo hhi pre
              ([brCmp op want AbiReg.t0 AbiReg.a0 target] ++ post) tmp a b (by omega)
              (fun p q t s ht hl h6 hpc' hgp' hsp' hm hf =>
                progEvalExpr_sim env L lm loc hspAlign hlo hhi a p q t hcOk.1 ht hl h6 s hpc' hgp' hsp' hm hf)
              (fun p q t s ht hl h6 hpc' hgp' hsp' hm hf =>
                progEvalExpr_sim env L lm loc hspAlign hlo hhi b p q t hcOk.2 ht hl h6 s hpc' hgp' hsp' hm hf)
              (by omega) (by omega)
              (by rw [show pre ++ (compileE env.tab nl tmp a ++
                  storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + tmp)) ++
                  compileE env.tab nl (tmp + 1) b ++
                  loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nl + tmp))) ++
                  ([brCmp op want AbiReg.t0 AbiReg.a0 target] ++ post) =
                  pre ++ (compileC env.tab nl tmp pfx lblId (.cmp op a b) want target).1 ++ post from by
                  rw [hcc]; dsimp only [seq]; simp only [List.append_assoc]]; exact hlink)
              (by dsimp only [seq] at htw_cc; rw [htw_cc] at h64; omega) st hpc hgp hsp hmemRel hframeOk
            rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va, hva⟩ | hva
            · rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
              · simp only [hva, hvb] at rseq
                obtain ⟨kseq, st1, hrun1, hpc1, ht0_1, ha0_1, hpres1, heq1⟩ := rseq
                have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .ok (op.eval va vb, ⟨lm, loc⟩) := by
                  simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
                rw [heval]
                have htw_ps : lkm.totalSize (pre ++ seq) = lkm.totalSize pre + lkm.totalSize seq :=
                  lkm.totalSize_append _ _
                obtain ⟨kbr, st2, _, hrunBr, hpc2, hpres2, hmem2⟩ :=
                  brCmp_step_lm lkm env (pre ++ seq) post op want AbiReg.t0 AbiReg.a0 (by decide) (by decide)
                    target tgt va vb st1 htgt
                    (by simpa only [hcc, List.append_assoc] using hlink)
                    (by rw [htw_ps, Nat.add_assoc, ← htw_cc]; exact h64)
                    (by rw [htw_ps]; exact hpc1) ht0_1 ha0_1
                refine ⟨kseq + kbr, st2, by rw [run_add, hrun1]; exact hrunBr, ?_,
                  hpres1.trans hpres2, by rw [hmem2]; exact heq1⟩
                rw [hpc2, htw_ps, htw_cc, Nat.add_assoc]
              · simp only [hva, hvb] at rseq
                have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .error .oob := by
                  simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb]
                rw [heval]; exact rseq
            · simp only [hva] at rseq
              have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .error .oob := by
                simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva]
              rw [heval]; exact rseq
  | not p ihp =>
    simp only [condOkB] at hcOk
    dsimp only [maxTempsCond] at hTmp
    have rp := ihp pre post tmp pfx lblId (!want) target tgt hcOk hTmp htgt hlink h64 st hpc hgp hsp hmemRel hframeOk
    rcases _root_.L.evalC_pure p ⟨lm, loc⟩ with ⟨bp, hbp⟩ | hbp
    · simp only [hbp] at rp
      have heval : _root_.L.evalC (.not p) ⟨lm, loc⟩ = .ok (!bp, ⟨lm, loc⟩) := by
        simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, Pure.pure, StateT.pure, Except.pure]
      rw [heval]; cases bp <;> cases want <;> exact rp
    · simp only [hbp] at rp
      have heval : _root_.L.evalC (.not p) ⟨lm, loc⟩ = .error .oob := by
        simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp]
      rw [heval]; exact rp
  | and p q ihp ihq =>
    simp only [condOkB, Bool.and_eq_true] at hcOk
    dsimp only [maxTempsCond] at hTmp
    have hf : (frameSpan sp nl nt).valid := by
      simp only [frameSpan, MemSpan.valid]; have := L.hStackValid; omega
    cases want
    · let cp := (compileC env.tab nl tmp pfx lblId p false target).1
      let id1 := (compileC env.tab nl tmp pfx lblId p false target).2
      let cq := (compileC env.tab nl tmp pfx id1 q false target).1
      have hcp_def : (compileC env.tab nl tmp pfx lblId (.and p q) false target).1 = cp ++ cq := rfl
      have htw_cc : lkm.totalSize (compileC env.tab nl tmp pfx lblId (.and p q) false target).1 =
          lkm.totalSize cp + lkm.totalSize cq := by rw [hcp_def, lkm.totalSize_append]
      have rp := ihp pre (cq ++ post) tmp pfx lblId false target tgt hcOk.1 (by omega) htgt
        (by rw [show pre ++ cp ++ (cq ++ post) = pre ++ (compileC env.tab nl tmp pfx lblId (.and p q) false target).1 ++ post from by
            rw [hcp_def]; simp only [List.append_assoc]]; exact hlink)
        (by rw [htw_cc] at h64; dsimp only [cp, cq] at h64 ⊢; omega) st hpc hgp hsp hmemRel hframeOk
      rcases _root_.L.evalC_pure p ⟨lm, loc⟩ with ⟨bp, hbp⟩ | hbp
      · cases bp
        · simp only [hbp] at rp
          have heval : _root_.L.evalC (.and p q) ⟨lm, loc⟩ = .ok (false, ⟨lm, loc⟩) := by
            simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, Pure.pure, StateT.pure, Except.pure]
          rw [heval]; exact rp
        · simp only [hbp] at rp
          obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := rp
          have htw1 : lkm.totalSize (pre ++ cp) = lkm.totalSize pre + lkm.totalSize cp := lkm.totalSize_append _ _
          have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ cp)) := by rw [htw1]; exact hpc1
          have rq := ihq (pre ++ cp) post tmp pfx id1 false target tgt hcOk.2 (by omega) htgt
            (by rw [show (pre ++ cp) ++ cq ++ post = pre ++ (compileC env.tab nl tmp pfx lblId (.and p q) false target).1 ++ post from by
                rw [hcp_def]; simp only [List.append_assoc]]; exact hlink)
            (by rw [htw1]; rw [htw_cc] at h64; dsimp only [cp, cq] at h64 ⊢; omega) st1 hpc1'
            (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
            (ProgMemRel.of_tempSpan env hlo hhi (by omega) heq1 hmemRel)
            (ProgFrameOk.of_tempSpan hf (by omega) heq1 hframeOk)
          rcases _root_.L.evalC_pure q ⟨lm, loc⟩ with ⟨bq, hbq⟩ | hbq
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : _root_.L.evalC (.and p q) ⟨lm, loc⟩ = .ok (bq, ⟨lm, loc⟩) := by
              simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            exact ⟨kp + kq, st2, by rw [run_add, hrun1]; exact hrun2,
              by rw [hpc2, htw1, htw_cc, Nat.add_assoc], hpres1.trans hpres2, heq1.trans heq2⟩
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : _root_.L.evalC (.and p q) ⟨lm, loc⟩ = .error .oob := by
              simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            exact ⟨kp + kq, st2, by rw [run_add, hrun1]; exact hrun2, hpc2, hpres1.trans hpres2, heq1.trans heq2⟩
      · simp only [hbp] at rp
        have heval : _root_.L.evalC (.and p q) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp]
        rw [heval]; exact rp
    · let skipLbl := s!"{pfx}_and_{lblId}"
      let cp := (compileC env.tab nl tmp pfx (lblId + 1) p false skipLbl).1
      let id1 := (compileC env.tab nl tmp pfx (lblId + 1) p false skipLbl).2
      let cq := (compileC env.tab nl tmp pfx id1 q true target).1
      have hcp_def : (compileC env.tab nl tmp pfx lblId (.and p q) true target).1 =
          cp ++ cq ++ [Asm.lbl skipLbl] := rfl
      have htw_cc : lkm.totalSize (compileC env.tab nl tmp pfx lblId (.and p q) true target).1 =
          lkm.totalSize cp + lkm.totalSize cq := by
        rw [hcp_def, lkm.totalSize_append, lkm.totalSize_append, Asm.lbl, lkm.totalSize_label]; omega
      have hskip : lookupLabel env.labels skipLbl = some (lkm.totalSize (pre ++ cp ++ cq)) :=
        lookupLabel_of_lbl_lm lkm (pre ++ cp ++ cq) post skipLbl (by
          rw [show (pre ++ cp ++ cq) ++ [Asm.lbl skipLbl] ++ post =
              pre ++ (compileC env.tab nl tmp pfx lblId (.and p q) true target).1 ++ post from by
              rw [hcp_def]; simp only [List.append_assoc]]; exact hlink)
      have rp := ihp pre (cq ++ [Asm.lbl skipLbl] ++ post) tmp pfx (lblId + 1) false skipLbl
        (lkm.totalSize (pre ++ cp ++ cq)) hcOk.1 (by omega) hskip
        (by rw [show pre ++ cp ++ (cq ++ [Asm.lbl skipLbl] ++ post) =
            pre ++ (compileC env.tab nl tmp pfx lblId (.and p q) true target).1 ++ post from by
            rw [hcp_def]; simp only [List.append_assoc]]; exact hlink)
        (by rw [htw_cc] at h64; dsimp only [cp, cq] at h64 ⊢; omega) st hpc hgp hsp hmemRel hframeOk
      rcases _root_.L.evalC_pure p ⟨lm, loc⟩ with ⟨bp, hbp⟩ | hbp
      · cases bp
        · simp only [hbp] at rp
          obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := rp
          have heval : _root_.L.evalC (.and p q) ⟨lm, loc⟩ = .ok (false, ⟨lm, loc⟩) := by
            simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, Pure.pure, StateT.pure, Except.pure]
          rw [heval]
          refine ⟨kp, st1, hrun1, ?_, hpres1, heq1⟩
          rw [hpc1]; simp [htw_cc, lkm.totalSize_append]
        · simp only [hbp] at rp
          obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := rp
          have htw1 : lkm.totalSize (pre ++ cp) = lkm.totalSize pre + lkm.totalSize cp := lkm.totalSize_append _ _
          have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ cp)) := by rw [htw1]; exact hpc1
          have rq := ihq (pre ++ cp) ([Asm.lbl skipLbl] ++ post) tmp pfx id1 true target tgt
            hcOk.2 (by omega) htgt
            (by rw [show (pre ++ cp) ++ cq ++ ([Asm.lbl skipLbl] ++ post) =
                pre ++ (compileC env.tab nl tmp pfx lblId (.and p q) true target).1 ++ post from by
                rw [hcp_def]; simp only [List.append_assoc]]; exact hlink)
            (by rw [htw1]; rw [htw_cc] at h64; dsimp only [cp, cq] at h64 ⊢; omega) st1 hpc1'
            (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
            (ProgMemRel.of_tempSpan env hlo hhi (by omega) heq1 hmemRel)
            (ProgFrameOk.of_tempSpan hf (by omega) heq1 hframeOk)
          rcases _root_.L.evalC_pure q ⟨lm, loc⟩ with ⟨bq, hbq⟩ | hbq
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : _root_.L.evalC (.and p q) ⟨lm, loc⟩ = .ok (bq, ⟨lm, loc⟩) := by
              simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            exact ⟨kp + kq, st2, by rw [run_add, hrun1]; exact hrun2,
              by rw [hpc2, htw1, htw_cc, Nat.add_assoc], hpres1.trans hpres2, heq1.trans heq2⟩
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : _root_.L.evalC (.and p q) ⟨lm, loc⟩ = .error .oob := by
              simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            exact ⟨kp + kq, st2, by rw [run_add, hrun1]; exact hrun2, hpc2, hpres1.trans hpres2, heq1.trans heq2⟩
      · simp only [hbp] at rp
        have heval : _root_.L.evalC (.and p q) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp]
        rw [heval]; exact rp
  | or p q ihp ihq =>
    simp only [condOkB, Bool.and_eq_true] at hcOk
    dsimp only [maxTempsCond] at hTmp
    have hf : (frameSpan sp nl nt).valid := by
      simp only [frameSpan, MemSpan.valid]; have := L.hStackValid; omega
    cases want
    · let skipLbl := s!"{pfx}_or_{lblId}"
      let cp := (compileC env.tab nl tmp pfx (lblId + 1) p true skipLbl).1
      let id1 := (compileC env.tab nl tmp pfx (lblId + 1) p true skipLbl).2
      let cq := (compileC env.tab nl tmp pfx id1 q false target).1
      have hcp_def : (compileC env.tab nl tmp pfx lblId (.or p q) false target).1 =
          cp ++ cq ++ [Asm.lbl skipLbl] := rfl
      have htw_cc : lkm.totalSize (compileC env.tab nl tmp pfx lblId (.or p q) false target).1 =
          lkm.totalSize cp + lkm.totalSize cq := by
        rw [hcp_def, lkm.totalSize_append, lkm.totalSize_append, Asm.lbl, lkm.totalSize_label]; omega
      have hskip : lookupLabel env.labels skipLbl = some (lkm.totalSize (pre ++ cp ++ cq)) :=
        lookupLabel_of_lbl_lm lkm (pre ++ cp ++ cq) post skipLbl (by
          rw [show (pre ++ cp ++ cq) ++ [Asm.lbl skipLbl] ++ post =
              pre ++ (compileC env.tab nl tmp pfx lblId (.or p q) false target).1 ++ post from by
              rw [hcp_def]; simp only [List.append_assoc]]; exact hlink)
      have rp := ihp pre (cq ++ [Asm.lbl skipLbl] ++ post) tmp pfx (lblId + 1) true skipLbl
        (lkm.totalSize (pre ++ cp ++ cq)) hcOk.1 (by omega) hskip
        (by rw [show pre ++ cp ++ (cq ++ [Asm.lbl skipLbl] ++ post) =
            pre ++ (compileC env.tab nl tmp pfx lblId (.or p q) false target).1 ++ post from by
            rw [hcp_def]; simp only [List.append_assoc]]; exact hlink)
        (by rw [htw_cc] at h64; dsimp only [cp, cq] at h64 ⊢; omega) st hpc hgp hsp hmemRel hframeOk
      rcases _root_.L.evalC_pure p ⟨lm, loc⟩ with ⟨bp, hbp⟩ | hbp
      · cases bp
        · simp only [hbp] at rp
          obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := rp
          have htw1 : lkm.totalSize (pre ++ cp) = lkm.totalSize pre + lkm.totalSize cp := lkm.totalSize_append _ _
          have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ cp)) := by rw [htw1]; exact hpc1
          have rq := ihq (pre ++ cp) ([Asm.lbl skipLbl] ++ post) tmp pfx id1 false target tgt
            hcOk.2 (by omega) htgt
            (by rw [show (pre ++ cp) ++ cq ++ ([Asm.lbl skipLbl] ++ post) =
                pre ++ (compileC env.tab nl tmp pfx lblId (.or p q) false target).1 ++ post from by
                rw [hcp_def]; simp only [List.append_assoc]]; exact hlink)
            (by rw [htw1]; rw [htw_cc] at h64; dsimp only [cp, cq] at h64 ⊢; omega) st1 hpc1'
            (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
            (ProgMemRel.of_tempSpan env hlo hhi (by omega) heq1 hmemRel)
            (ProgFrameOk.of_tempSpan hf (by omega) heq1 hframeOk)
          rcases _root_.L.evalC_pure q ⟨lm, loc⟩ with ⟨bq, hbq⟩ | hbq
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : _root_.L.evalC (.or p q) ⟨lm, loc⟩ = .ok (bq, ⟨lm, loc⟩) := by
              simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            exact ⟨kp + kq, st2, by rw [run_add, hrun1]; exact hrun2,
              by rw [hpc2, htw1, htw_cc, Nat.add_assoc], hpres1.trans hpres2, heq1.trans heq2⟩
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : _root_.L.evalC (.or p q) ⟨lm, loc⟩ = .error .oob := by
              simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            exact ⟨kp + kq, st2, by rw [run_add, hrun1]; exact hrun2, hpc2, hpres1.trans hpres2, heq1.trans heq2⟩
        · simp only [hbp] at rp
          obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := rp
          have heval : _root_.L.evalC (.or p q) ⟨lm, loc⟩ = .ok (true, ⟨lm, loc⟩) := by
            simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, Pure.pure, StateT.pure, Except.pure]
          rw [heval]
          refine ⟨kp, st1, hrun1, ?_, hpres1, heq1⟩
          rw [hpc1]; simp [htw_cc, lkm.totalSize_append]
      · simp only [hbp] at rp
        have heval : _root_.L.evalC (.or p q) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp]
        rw [heval]; exact rp
    · let cp := (compileC env.tab nl tmp pfx lblId p true target).1
      let id1 := (compileC env.tab nl tmp pfx lblId p true target).2
      let cq := (compileC env.tab nl tmp pfx id1 q true target).1
      have hcp_def : (compileC env.tab nl tmp pfx lblId (.or p q) true target).1 = cp ++ cq := rfl
      have htw_cc : lkm.totalSize (compileC env.tab nl tmp pfx lblId (.or p q) true target).1 =
          lkm.totalSize cp + lkm.totalSize cq := by rw [hcp_def, lkm.totalSize_append]
      have rp := ihp pre (cq ++ post) tmp pfx lblId true target tgt hcOk.1 (by omega) htgt
        (by rw [show pre ++ cp ++ (cq ++ post) = pre ++ (compileC env.tab nl tmp pfx lblId (.or p q) true target).1 ++ post from by
            rw [hcp_def]; simp only [List.append_assoc]]; exact hlink)
        (by rw [htw_cc] at h64; dsimp only [cp, cq] at h64 ⊢; omega) st hpc hgp hsp hmemRel hframeOk
      rcases _root_.L.evalC_pure p ⟨lm, loc⟩ with ⟨bp, hbp⟩ | hbp
      · cases bp
        · simp only [hbp] at rp
          obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := rp
          have htw1 : lkm.totalSize (pre ++ cp) = lkm.totalSize pre + lkm.totalSize cp := lkm.totalSize_append _ _
          have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ cp)) := by rw [htw1]; exact hpc1
          have rq := ihq (pre ++ cp) post tmp pfx id1 true target tgt hcOk.2 (by omega) htgt
            (by rw [show (pre ++ cp) ++ cq ++ post = pre ++ (compileC env.tab nl tmp pfx lblId (.or p q) true target).1 ++ post from by
                rw [hcp_def]; simp only [List.append_assoc]]; exact hlink)
            (by rw [htw1]; rw [htw_cc] at h64; dsimp only [cp, cq] at h64 ⊢; omega) st1 hpc1'
            (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
            (ProgMemRel.of_tempSpan env hlo hhi (by omega) heq1 hmemRel)
            (ProgFrameOk.of_tempSpan hf (by omega) heq1 hframeOk)
          rcases _root_.L.evalC_pure q ⟨lm, loc⟩ with ⟨bq, hbq⟩ | hbq
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : _root_.L.evalC (.or p q) ⟨lm, loc⟩ = .ok (bq, ⟨lm, loc⟩) := by
              simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            exact ⟨kp + kq, st2, by rw [run_add, hrun1]; exact hrun2,
              by rw [hpc2, htw1, htw_cc, Nat.add_assoc], hpres1.trans hpres2, heq1.trans heq2⟩
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : _root_.L.evalC (.or p q) ⟨lm, loc⟩ = .error .oob := by
              simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            exact ⟨kp + kq, st2, by rw [run_add, hrun1]; exact hrun2, hpc2, hpres1.trans hpres2, heq1.trans heq2⟩
        · simp only [hbp] at rp
          have heval : _root_.L.evalC (.or p q) ⟨lm, loc⟩ = .ok (true, ⟨lm, loc⟩) := by
            simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, Pure.pure, StateT.pure, Except.pure]
          rw [heval]; exact rp
      · simp only [hbp] at rp
        have heval : _root_.L.evalC (.or p q) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp]
        rw [heval]; exact rp


end ConAgua.RISCV.Compiler
