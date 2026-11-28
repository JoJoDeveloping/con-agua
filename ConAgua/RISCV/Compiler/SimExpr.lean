import ConAgua.RISCV.Compiler.SimBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Forward Simulation of Expressions & Conditions (`ConAgua.RISCV.Compiler.SimExpr`)

Proves semantic forward simulation of `MiniL` expressions (`evalExpr_sim_gen`) and
conditions (`evalCond_sim_gen`) against `ConAgua.RISCV.RV64.Semantics.run`.
-/

namespace ConAgua.RISCV.Compiler

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Linker

/-! ## 5. Forward Simulation of Expressions (`evalExpr_sim`) -/

theorem mul_lo_hi_toNat (x y : UInt64) :
    BitVec.ofNat 64 (x.toBitVec.toNat * y.toBitVec.toNat % 2 ^ 64) = (x * y).toBitVec ∧
    BitVec.ofNat 64 (x.toBitVec.toNat * y.toBitVec.toNat / 2 ^ 64) = (BinOp.mulhi.eval x y).toBitVec := by
  constructor
  · rw [UInt64.toBitVec_mul]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_mod]
  · rw [BinOp.eval, UInt64.toBitVec_ofNat', UInt64.toNat_toBitVec, UInt64.toNat_toBitVec]

theorem expr_constVal_eq_some {e : Expr} {w : UInt64} (h : e.constVal? = some w) :
    e = .const w := by
  cases e <;> simp [Expr.constVal?] at h; subst h; rfl

theorem emitBinOp_step_lm (lm : LinkModel) (env : CodeEnvGen lm) (pre post : List AsmItem)
    (op : BinOp) (rd rs1 rs2 : Reg) (hrd : rd ≠ 0#5)
    (va vb : _root_.L.Word) (st : State)
    (hlink : lm.linkSpec (pre ++ [emitBinOp op rd rs1 rs2] ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lm.totalSize pre + 1) < 2 ^ 64)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (h1 : st.getReg rs1 = va.toBitVec) (h2 : st.getReg rs2 = vb.toBitVec) :
    ∃ st', RV64.run env.rom 1 st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + 1)) ∧
      st'.getReg rd = (op.eval va vb).toBitVec ∧
      (∀ r, r ≠ rd → st'.getReg r = st.getReg r) ∧
      st'.mem = st.mem := by
  have aux : ∀ (aop : AluOp) (ht : emitBinOp op rd rs1 rs2 = .instr (.alu aop rd rs1 rs2))
      (hop : evalAlu aop va.toBitVec vb.toBitVec = (op.eval va vb).toBitVec),
      ∃ st', RV64.run env.rom 1 st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + 1)) ∧
        st'.getReg rd = (op.eval va vb).toBitVec ∧
        (∀ r, r ≠ rd → st'.getReg r = st.getReg r) ∧
        st'.mem = st.mem := by
    intro aop ht hop
    rw [ht] at hlink
    have hs := step_item_instr_lm lm env.hrom pre post (.alu aop rd rs1 rs2) hlink (by omega) st hpc
    refine ⟨stepReg st rd (evalAlu aop (st.getReg rs1) (st.getReg rs2)) (st.pc + 4#64),
      run_one_cont _ _ _ (by rw [hs]; rfl),
      pc_add_4_ofNat st.pc hpc,
      by rw [getReg_stepReg_eq _ _ hrd, h1, h2, hop],
      fun r hr => getReg_stepReg_ne st rd r hr _ _, mem_stepReg _ _ _ _⟩
  cases op with
  | add   => exact aux .add rfl (uint64_binop_toBitVec .add va vb).symm
  | sub   => exact aux .sub rfl (uint64_binop_toBitVec .sub va vb).symm
  | and   => exact aux .and rfl (uint64_binop_toBitVec .and va vb).symm
  | or    => exact aux .or  rfl (uint64_binop_toBitVec .or va vb).symm
  | xor   => exact aux .xor rfl (uint64_binop_toBitVec .xor va vb).symm
  | shl   => exact aux .sll rfl (uint64_binop_toBitVec .shl va vb).symm
  | shr   => exact aux .srl rfl (uint64_binop_toBitVec .shr va vb).symm
  | mul   => exact aux .mul rfl (by simp only [BinOp.eval, UInt64.toBitVec_mul, evalAlu_mul_eq])
  | mulhi => exact aux .mulhu rfl ((evalAlu_mulhu_eq va.toBitVec vb.toBitVec).trans (mul_lo_hi_toNat va vb).2)

private theorem bv_shl_eq_mul_pow2 (x : BitVec 64) (k : Nat) (hk : k < 64) :
    x <<< k = x * (1#64 <<< k) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1#64 <<< k).toNat = 2 ^ k := by
    rw [BitVec.toNat_shiftLeft, show (1#64).toNat = 1 from rfl, Nat.shiftLeft_eq, Nat.one_mul,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hk)]
  rw [BitVec.toNat_mul, h1, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

private theorem bv_mul_add_shl (x : BitVec 64) (k : Nat) (hk : k < 64) :
    x + (x <<< k) = x * BitVec.ofNat 64 (2 ^ k + 1) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : 2 ^ k + 1 < 2 ^ 64 := by
    have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : k ≤ 63)
    omega
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_mul,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1]
  have : (x.toNat + x.toNat * 2 ^ k % 2 ^ 64) % 2 ^ 64 = (x.toNat + x.toNat * 2 ^ k) % 2 ^ 64 := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [this, Nat.mul_add, Nat.mul_one, Nat.add_comm]

private theorem bv_mul_sub_shl (x : BitVec 64) (k : Nat) (_hk0 : 1 ≤ k) (hk : k < 64) :
    (x <<< k) - x = x * BitVec.ofNat 64 (2 ^ k - 1) := by
  have hp : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
  have hlt : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hk
  have hpow : (1#64 <<< k : BitVec 64) = BitVec.ofNat 64 (2 ^ k) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, show (1#64).toNat = 1 from rfl, Nat.shiftLeft_eq, Nat.one_mul,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  calc (x <<< k) - x
      = x * BitVec.ofNat 64 (2 ^ k) - x * 1#64 := by rw [bv_shl_eq_mul_pow2 x k hk, hpow, BitVec.mul_one]
    _ = x * (BitVec.ofNat 64 (2 ^ k) - 1#64) := by rw [BitVec.mul_sub]
    _ = x * BitVec.ofNat 64 (2 ^ k - 1) := by
        congr 1; apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : 2 ^ k - 1 < 2 ^ 64)]
        have hsum : 2 ^ 64 - 1 + 2 ^ k = 2 ^ 64 + (2 ^ k - 1) := by omega
        rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : 2 ^ k - 1 < 2 ^ 64)]

theorem emitMulConstTo_sim_lm (lm : LinkModel) (env : CodeEnvGen lm) (pre post : List AsmItem)
    (rd rs tmp : Reg) (hrd : rd ≠ 0#5) (htmp : tmp ≠ 0#5) (_hne : tmp ≠ rd) (hners : tmp ≠ rs)
    (w : UInt64) (x : UInt64) (st : State)
    (hlink : lm.linkSpec (pre ++ emitMulConstTo rd rs tmp w ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (emitMulConstTo rd rs tmp w)) < 2 ^ 64)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (hrsx : st.getReg rs = x.toBitVec) :
    ∃ k st', RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (emitMulConstTo rd rs tmp w))) ∧
      st'.getReg rd = (x * w).toBitVec ∧
      (∀ r, r ≠ rd → r ≠ tmp → st'.getReg r = st.getReg r) ∧
      st'.mem = st.mem := by
  have stepShiftAdd : ∀ (sh : BitVec 6) (hsh : sh.toNat < 64)
      (hcode : emitMulConstTo rd rs tmp w = [Asm.slli tmp rs sh, Asm.add rd rs tmp])
      (hw : w.toBitVec = BitVec.ofNat 64 (2 ^ sh.toNat + 1)),
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (emitMulConstTo rd rs tmp w))) ∧
        st'.getReg rd = (x * w).toBitVec ∧
        (∀ r, r ≠ rd → r ≠ tmp → st'.getReg r = st.getReg r) ∧
        st'.mem = st.mem := by
    intro sh hsh hcode hw
    rw [hcode] at hlink h64 ⊢
    have htw : lm.totalSize [Asm.slli tmp rs sh, Asm.add rd rs tmp] = 2 := by
      simp [Asm.slli, Asm.add, lm.itemSize_instr]
    rw [htw] at h64 ⊢
    have hl1 : lm.linkSpec (pre ++ [Asm.slli tmp rs sh] ++ ([Asm.add rd rs tmp] ++ post)) =
        .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
    have hs1 := step_item_instr_lm lm env.hrom pre ([Asm.add rd rs tmp] ++ post)
      (.shImm .slli tmp rs sh) hl1 (by omega) st hpc
    let st1 := stepReg st tmp (x.toBitVec <<< sh.toNat) (st.pc + 4#64)
    have hr1 : RV64.step env.rom st = .cont st1 := by
      rw [hs1]; dsimp only [execInstr, evalShiftImm]; rw [hrsx]; rfl
    have hpc1 : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ [Asm.slli tmp rs sh])) := by
      rw [lm.totalSize_append, show lm.totalSize [Asm.slli tmp rs sh] = 1 by simp [Asm.slli, lm.itemSize_instr]]
      exact pc_add_4_ofNat st.pc hpc
    have hl2 : lm.linkSpec ((pre ++ [Asm.slli tmp rs sh]) ++ [Asm.add rd rs tmp] ++ post) =
        .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
    have hs2 := step_item_instr_lm lm env.hrom (pre ++ [Asm.slli tmp rs sh]) post
      (.alu .add rd rs tmp) hl2
      (by rw [lm.totalSize_append, show lm.totalSize [Asm.slli tmp rs sh] = 1 by simp [Asm.slli, lm.itemSize_instr]]; omega)
      st1 hpc1
    let st2 := stepReg st1 rd (x.toBitVec + (x.toBitVec <<< sh.toNat)) (st1.pc + 4#64)
    have hr2 : RV64.step env.rom st1 = .cont st2 := by
      rw [hs2]; dsimp only [execInstr, evalAlu]
      rw [getReg_stepReg_eq _ _ htmp, getReg_stepReg_ne _ _ _ hners.symm, hrsx]; rfl
    refine ⟨2, st2, by rw [show (2 : Nat) = 1 + 1 from rfl, run_add, run_one_cont _ _ _ hr1]; exact run_one_cont _ _ _ hr2,
      ?_, ?_, ?_, (mem_stepReg _ _ _ _).trans (mem_stepReg _ _ _ _)⟩
    · change st1.pc + 4#64 = _
      rw [pc_add_4_ofNat st1.pc hpc1, lm.totalSize_append,
        show lm.totalSize [Asm.slli tmp rs sh] = 1 by simp [Asm.slli, lm.itemSize_instr], Nat.add_assoc]
    · rw [getReg_stepReg_eq _ _ hrd, bv_mul_add_shl x.toBitVec sh.toNat hsh, ← hw, UInt64.toBitVec_mul]
    · intro r hrr hrt
      exact (getReg_stepReg_ne st1 rd r hrr _ _).trans (getReg_stepReg_ne st tmp r hrt _ _)
  have stepShiftSub : ∀ (sh : BitVec 6) (hsh0 : 1 ≤ sh.toNat) (hsh : sh.toNat < 64)
      (hcode : emitMulConstTo rd rs tmp w = [Asm.slli tmp rs sh, Asm.sub rd tmp rs])
      (hw : w.toBitVec = BitVec.ofNat 64 (2 ^ sh.toNat - 1)),
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (emitMulConstTo rd rs tmp w))) ∧
        st'.getReg rd = (x * w).toBitVec ∧
        (∀ r, r ≠ rd → r ≠ tmp → st'.getReg r = st.getReg r) ∧
        st'.mem = st.mem := by
    intro sh hsh0 hsh hcode hw
    rw [hcode] at hlink h64 ⊢
    have htw : lm.totalSize [Asm.slli tmp rs sh, Asm.sub rd tmp rs] = 2 := by
      simp [Asm.slli, Asm.sub, lm.itemSize_instr]
    rw [htw] at h64 ⊢
    have hl1 : lm.linkSpec (pre ++ [Asm.slli tmp rs sh] ++ ([Asm.sub rd tmp rs] ++ post)) =
        .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
    have hs1 := step_item_instr_lm lm env.hrom pre ([Asm.sub rd tmp rs] ++ post)
      (.shImm .slli tmp rs sh) hl1 (by omega) st hpc
    let st1 := stepReg st tmp (x.toBitVec <<< sh.toNat) (st.pc + 4#64)
    have hr1 : RV64.step env.rom st = .cont st1 := by
      rw [hs1]; dsimp only [execInstr, evalShiftImm]; rw [hrsx]; rfl
    have hpc1 : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ [Asm.slli tmp rs sh])) := by
      rw [lm.totalSize_append, show lm.totalSize [Asm.slli tmp rs sh] = 1 by simp [Asm.slli, lm.itemSize_instr]]
      exact pc_add_4_ofNat st.pc hpc
    have hl2 : lm.linkSpec ((pre ++ [Asm.slli tmp rs sh]) ++ [Asm.sub rd tmp rs] ++ post) =
        .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
    have hs2 := step_item_instr_lm lm env.hrom (pre ++ [Asm.slli tmp rs sh]) post
      (.alu .sub rd tmp rs) hl2
      (by rw [lm.totalSize_append, show lm.totalSize [Asm.slli tmp rs sh] = 1 by simp [Asm.slli, lm.itemSize_instr]]; omega)
      st1 hpc1
    let st2 := stepReg st1 rd ((x.toBitVec <<< sh.toNat) - x.toBitVec) (st1.pc + 4#64)
    have hr2 : RV64.step env.rom st1 = .cont st2 := by
      rw [hs2]; dsimp only [execInstr, evalAlu]
      rw [getReg_stepReg_eq _ _ htmp, getReg_stepReg_ne _ _ _ hners.symm, hrsx]; rfl
    refine ⟨2, st2, by rw [show (2 : Nat) = 1 + 1 from rfl, run_add, run_one_cont _ _ _ hr1]; exact run_one_cont _ _ _ hr2,
      ?_, ?_, ?_, (mem_stepReg _ _ _ _).trans (mem_stepReg _ _ _ _)⟩
    · change st1.pc + 4#64 = _
      rw [pc_add_4_ofNat st1.pc hpc1, lm.totalSize_append,
        show lm.totalSize [Asm.slli tmp rs sh] = 1 by simp [Asm.slli, lm.itemSize_instr], Nat.add_assoc]
    · rw [getReg_stepReg_eq _ _ hrd, bv_mul_sub_shl x.toBitVec sh.toNat hsh0 hsh, ← hw, UInt64.toBitVec_mul]
    · intro r hrr hrt
      exact (getReg_stepReg_ne st1 rd r hrr _ _).trans (getReg_stepReg_ne st tmp r hrt _ _)
  have hw_of_nat : ∀ k, w.toNat = k → w.toBitVec = BitVec.ofNat 64 k := fun k hk => by
    rw [← hk, ← UInt64.toBitVec_ofNat' w.toNat, UInt64.ofNat_toNat]
  by_cases h0 : w.toNat = 0
  · have hc : emitMulConstTo rd rs tmp w = [Asm.addi rd AbiReg.zero 0#12] := by simp [emitMulConstTo, h0]
    rw [hc] at hlink h64 ⊢
    have htw1 : lm.totalSize [Asm.addi rd AbiReg.zero 0#12] = 1 := by simp [Asm.addi, lm.itemSize_instr]
    rw [htw1] at h64 ⊢
    have hs := step_item_instr_lm lm env.hrom pre post (.aluImm .addi rd AbiReg.zero 0#12) hlink (by omega) st hpc
    refine ⟨1, stepReg st rd 0#64 (st.pc + 4#64), run_one_cont _ _ _ (by rw [hs]; rfl),
      pc_add_4_ofNat st.pc hpc, ?_, fun r hr _ => getReg_stepReg_ne st rd r hr _ _, mem_stepReg _ _ _ _⟩
    rw [getReg_stepReg_eq _ _ hrd, UInt64.toBitVec_mul, hw_of_nat 0 h0, BitVec.mul_zero]
  · by_cases h1 : w.toNat = 1
    · by_cases heq : rd = rs
      · subst heq
        have hc : emitMulConstTo rd rd tmp w = [] := by simp [emitMulConstTo, h1]
        rw [hc]
        refine ⟨0, st, rfl, by simpa using hpc, ?_, fun _ _ _ => rfl, rfl⟩
        rw [hrsx, UInt64.toBitVec_mul, hw_of_nat 1 h1, BitVec.mul_one]
      · have hc : emitMulConstTo rd rs tmp w = [Asm.mv rd rs] := by simp [emitMulConstTo, h1, heq]
        rw [hc] at hlink h64 ⊢
        have htw1 : lm.totalSize [Asm.mv rd rs] = 1 := by simp [Asm.mv, lm.itemSize_instr]
        rw [htw1] at h64 ⊢
        have hs := step_item_instr_lm lm env.hrom pre post (.aluImm .addi rd rs 0#12)
          (by simpa [Asm.mv, Asm.addi] using hlink) (by omega) st hpc
        refine ⟨1, stepReg st rd x.toBitVec (st.pc + 4#64),
          run_one_cont _ _ _ (by rw [hs]; simp only [execInstr, evalAluImm, hrsx, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero]; rfl),
          pc_add_4_ofNat st.pc hpc, ?_, fun r hr _ => getReg_stepReg_ne st rd r hr _ _, mem_stepReg _ _ _ _⟩
        rw [getReg_stepReg_eq _ _ hrd, UInt64.toBitVec_mul, hw_of_nat 1 h1, BitVec.mul_one]
    · cases hpow : isPow2Shift64 w with
      | some sh =>
        have hc : emitMulConstTo rd rs tmp w = [Asm.slli rd rs sh] := by
          simp [emitMulConstTo, h0, h1, hpow]
        dsimp only [isPow2Shift64] at hpow
        by_cases hcond : (ctz64 w.toBitVec < 64 && w.toBitVec == (1#64 <<< ctz64 w.toBitVec)) = true
        · next =>
          rw [ite_eq_left_of_eq_true _ _ (eq_true hcond)] at hpow
          simp only [Option.some.injEq] at hpow
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond
          have hsh : sh.toNat = ctz64 w.toBitVec := by
            rw [← hpow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcond.1]
          rw [hc] at hlink h64 ⊢
          have htw1 : lm.totalSize [Asm.slli rd rs sh] = 1 := by simp [Asm.slli, lm.itemSize_instr]
          rw [htw1] at h64 ⊢
          have hs := step_item_instr_lm lm env.hrom pre post (.shImm .slli rd rs sh) hlink (by omega) st hpc
          refine ⟨1, stepReg st rd (x.toBitVec <<< sh.toNat) (st.pc + 4#64),
            run_one_cont _ _ _ (by rw [hs]; dsimp only [execInstr, evalShiftImm]; rw [hrsx]; rfl),
            pc_add_4_ofNat st.pc hpc, ?_, fun r hr _ => getReg_stepReg_ne st rd r hr _ _, mem_stepReg _ _ _ _⟩
          rw [getReg_stepReg_eq _ _ hrd, hsh, UInt64.toBitVec_mul, bv_shl_eq_mul_pow2 _ _ hcond.1]
          exact congrArg (x.toBitVec * ·) hcond.2.symm
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hcond)] at hpow; cases hpow
      | none =>
        by_cases h3 : w.toNat = 3
        · exact stepShiftAdd 1#6 (by decide) (by simp [emitMulConstTo, hpow, h3]) (hw_of_nat 3 h3)
        · by_cases h5 : w.toNat = 5
          · exact stepShiftAdd 2#6 (by decide) (by simp [emitMulConstTo, hpow, h5]) (hw_of_nat 5 h5)
          · by_cases h7 : w.toNat = 7
            · exact stepShiftSub 3#6 (by decide) (by decide) (by simp [emitMulConstTo, hpow, h7]) (hw_of_nat 7 h7)
            · by_cases h9 : w.toNat = 9
              · exact stepShiftAdd 3#6 (by decide) (by simp [emitMulConstTo, hpow, h9]) (hw_of_nat 9 h9)
              · by_cases h15 : w.toNat = 15
                · exact stepShiftSub 4#6 (by decide) (by decide) (by simp [emitMulConstTo, hpow, h15]) (hw_of_nat 15 h15)
                · by_cases h17 : w.toNat = 17
                  · exact stepShiftAdd 4#6 (by decide) (by simp [emitMulConstTo, hpow, h17]) (hw_of_nat 17 h17)
                  · by_cases h255 : w.toNat = 255
                    · exact stepShiftSub 8#6 (by decide) (by decide) (by simp [emitMulConstTo, hpow, h255]) (hw_of_nat 255 h255)
                    · by_cases h257 : w.toNat = 257
                      · exact stepShiftAdd 8#6 (by decide) (by simp [emitMulConstTo, hpow, h257]) (hw_of_nat 257 h257)
                      · have hc : emitMulConstTo rd rs tmp w = li tmp (BitVec.ofNat 64 w.toNat) ++ [Asm.mul rd rs tmp] := by
                          simp [emitMulConstTo, h0, h1, hpow, h3, h5, h7, h9, h15, h17, h255, h257]
                        rw [hc] at hlink h64 ⊢
                        have htwMul : lm.totalSize (li tmp (BitVec.ofNat 64 w.toNat) ++ [Asm.mul rd rs tmp]) =
                            lm.totalSize (li tmp (BitVec.ofNat 64 w.toNat)) + 1 := by
                          rw [lm.totalSize_append]; simp [Asm.mul, lm.itemSize_instr]
                        have hl1 : lm.linkSpec (pre ++ li tmp (BitVec.ofNat 64 w.toNat) ++ ([Asm.mul rd rs tmp] ++ post)) =
                            .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
                        obtain ⟨st1, hrun1, hoth1, htmp1, hmem1, hpc1⟩ :=
                          li_correct_lm lm env.hrom pre ([Asm.mul rd rs tmp] ++ post) tmp htmp
                            (BitVec.ofNat 64 w.toNat) hl1 (by rw [htwMul] at h64; omega) st hpc
                        have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ li tmp (BitVec.ofNat 64 w.toNat))) := by
                          rw [lm.totalSize_append]; exact hpc1
                        have hl2 : lm.linkSpec ((pre ++ li tmp (BitVec.ofNat 64 w.toNat)) ++ [Asm.mul rd rs tmp] ++ post) =
                            .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
                        have hs2 := step_item_instr_lm lm env.hrom (pre ++ li tmp (BitVec.ofNat 64 w.toNat)) post
                          (.alu .mul rd rs tmp) hl2 (by rw [lm.totalSize_append]; rw [htwMul] at h64; omega) st1 hpc1'
                        have hwv : BitVec.ofNat 64 w.toNat = w.toBitVec := hw_of_nat w.toNat rfl |>.symm
                        let st2 := stepReg st1 rd (evalAlu .mul (st1.getReg rs) (st1.getReg tmp)) (st1.pc + 4#64)
                        refine ⟨lm.totalSize (li tmp (BitVec.ofNat 64 w.toNat)) + 1, st2,
                          by rw [run_add, hrun1]; exact run_one_cont _ _ _ (by rw [hs2]; rfl),
                          ?_, ?_, ?_, (mem_stepReg _ _ _ _).trans hmem1⟩
                        · change st1.pc + 4#64 = _
                          rw [pc_add_4_ofNat st1.pc hpc1', lm.totalSize_append, htwMul, Nat.add_assoc]
                        · rw [getReg_stepReg_eq _ _ hrd, evalAlu_mul_eq, hoth1 rs hners.symm, hrsx, htmp1, hwv, UInt64.toBitVec_mul]
                        · intro r hrr hrt
                          exact (getReg_stepReg_ne st1 rd r hrr _ _).trans (hoth1 r hrt)

theorem emitMulConst_sim_lm (lm : LinkModel) (env : CodeEnvGen lm) (pre post : List AsmItem)
    (rd tmp : Reg) (hrd : rd ≠ 0#5) (htmp : tmp ≠ 0#5) (hne : rd ≠ tmp)
    (w : UInt64) (x : UInt64) (st : State)
    (hlink : lm.linkSpec (pre ++ emitMulConst rd tmp w ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (emitMulConst rd tmp w)) < 2 ^ 64)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (hrdx : st.getReg rd = x.toBitVec) :
    ∃ k st', RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (emitMulConst rd tmp w))) ∧
      st'.getReg rd = (x * w).toBitVec ∧
      (∀ r, r ≠ rd → r ≠ tmp → st'.getReg r = st.getReg r) ∧
      st'.mem = st.mem :=
  emitMulConstTo_sim_lm lm env pre post rd rd tmp hrd htmp hne.symm hne.symm w x st hlink h64 hpc hrdx

private theorem slli_srli_eq_and_lowMask (x : BitVec 64) {k : Nat} (hk64 : k < 64) :
    (x <<< (64 - k)) >>> (64 - k) = x &&& ((1#64 <<< k) - 1#64) := by
  apply BitVec.eq_of_toNat_eq
  have hlt : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hk64
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
  have hpow : (1#64 <<< k).toNat = 2 ^ k := by
    rw [BitVec.toNat_shiftLeft, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt hlt]
  have hmask : ((1#64 <<< k) - 1#64).toNat = 2 ^ k - 1 := by
    rw [BitVec.toNat_sub_of_le (by
      change (1#64 : BitVec 64).toNat ≤ (1#64 <<< k).toNat
      rw [hpow]; exact h1), hpow]; rfl
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_and, hmask,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]
  have hmul : 2 ^ 64 = 2 ^ k * 2 ^ (64 - k) := by rw [← Nat.pow_add]; congr 1; omega
  rw [hmul, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (Nat.pow_pos (by omega))]

private theorem lowMaskShift_spec {w : UInt64} {sh : BitVec 6}
    (h : lowMaskShift? w = some sh) :
    ∃ k, 12 ≤ k ∧ k < 64 ∧ sh = BitVec.ofNat 6 (64 - k) ∧ w.toBitVec = (1#64 <<< k) - 1#64 := by
  unfold lowMaskShift? at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond
      cases h
      exact ⟨ctz64 (w.toBitVec + 1#64), hcond.1.1, hcond.1.2, rfl, hcond.2⟩
    · cases h

theorem emitBinConstRhsTo_sim_lm (lm : LinkModel) (env : CodeEnvGen lm) (pre post : List AsmItem)
    (rd rs : Reg) (hrd : rd ≠ 0#5) (hrdt0 : rd ≠ AbiReg.t0) (hrst0 : rs ≠ AbiReg.t0)
    (op : BinOp) (w : UInt64) (x : UInt64) (st : State)
    (hlink : lm.linkSpec (pre ++ emitBinConstRhsTo rd rs op w ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (emitBinConstRhsTo rd rs op w)) < 2 ^ 64)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (hrs : st.getReg rs = x.toBitVec) :
    ∃ k st', RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (emitBinConstRhsTo rd rs op w))) ∧
      st'.getReg rd = (op.eval x w).toBitVec ∧
      (∀ r, r ≠ rd → r ≠ AbiReg.t0 → st'.getReg r = st.getReg r) ∧
      st'.mem = st.mem := by
  have stepMvIf : ∀ (hcode : emitBinConstRhsTo rd rs op w = if rd == rs then [] else [Asm.mv rd rs])
      (hv : x.toBitVec = (op.eval x w).toBitVec),
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (emitBinConstRhsTo rd rs op w))) ∧
        st'.getReg rd = (op.eval x w).toBitVec ∧
        (∀ r, r ≠ rd → r ≠ AbiReg.t0 → st'.getReg r = st.getReg r) ∧
        st'.mem = st.mem := by
    intro hcode hv
    rw [hcode] at hlink h64 ⊢
    by_cases heq : rd = rs
    · subst heq; simp only [beq_self_eq_true, ↓reduceIte, lm.totalSize_nil, Nat.add_zero]
      exact ⟨0, st, rfl, hpc, hrs.trans hv, fun _ _ _ => rfl, rfl⟩
    · simp only [beq_false_of_ne heq, Bool.false_eq_true, ↓reduceIte] at hlink h64 ⊢
      have htw1 : lm.totalSize [Asm.mv rd rs] = 1 := by simp [Asm.mv, lm.itemSize_instr]
      rw [htw1] at h64 ⊢
      have hs := step_item_instr_lm lm env.hrom pre post (.aluImm .addi rd rs 0#12)
        (by simpa [Asm.mv, Asm.addi] using hlink) (by omega) st hpc
      refine ⟨1, stepReg st rd x.toBitVec (st.pc + 4#64),
        run_one_cont _ _ _ (by rw [hs]; simp only [execInstr, evalAluImm, hrs, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero]; rfl),
        pc_add_4_ofNat st.pc hpc, by rw [getReg_stepReg_eq _ _ hrd, hv],
        fun r hr _ => getReg_stepReg_ne st rd r hr _ _, mem_stepReg _ _ _ _⟩
  have stepLiBin : ∀ (hcode : emitBinConstRhsTo rd rs op w = li AbiReg.t0 w.toBitVec ++ [emitBinOp op rd rs AbiReg.t0]),
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (emitBinConstRhsTo rd rs op w))) ∧
        st'.getReg rd = (op.eval x w).toBitVec ∧
        (∀ r, r ≠ rd → r ≠ AbiReg.t0 → st'.getReg r = st.getReg r) ∧
        st'.mem = st.mem := by
    intro hcode
    rw [hcode] at hlink h64 ⊢
    have htw : lm.totalSize (li AbiReg.t0 w.toBitVec ++ [emitBinOp op rd rs AbiReg.t0]) =
        lm.totalSize (li AbiReg.t0 w.toBitVec) + 1 := by
      rw [lm.totalSize_append]; cases op <;> simp [emitBinOp, Asm.add, Asm.sub, Asm.and, Asm.or,
        Asm.xor, Asm.sll, Asm.srl, Asm.mul, Asm.mulhu, lm.itemSize_instr]
    obtain ⟨st1, hrun1, hoth1, ht0_1, hmem1, hpc1⟩ :=
      li_correct_lm lm env.hrom pre ([emitBinOp op rd rs AbiReg.t0] ++ post)
        AbiReg.t0 (by decide) w.toBitVec (by simpa [List.append_assoc] using hlink)
        (by rw [htw] at h64; omega) st hpc
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ li AbiReg.t0 w.toBitVec)) := by
      rw [lm.totalSize_append]; exact hpc1
    obtain ⟨st2, hrun2, hpc2, hrd_2, hoth2, hmem2⟩ :=
      emitBinOp_step_lm lm env (pre ++ li AbiReg.t0 w.toBitVec) post op rd rs AbiReg.t0
        hrd x w st1 (by simpa [List.append_assoc] using hlink)
        (by rw [lm.totalSize_append]; rw [htw] at h64; omega) hpc1'
        ((hoth1 rs hrst0).trans hrs) ht0_1
    refine ⟨_, st2, by rw [run_add, hrun1]; exact hrun2,
      by rw [hpc2, lm.totalSize_append, htw, Nat.add_assoc], hrd_2,
      fun r hr1 hr2 => (hoth2 r hr1).trans (hoth1 r hr2), hmem2.trans hmem1⟩
  have stepAluImm : ∀ (iop : AluImmOp) (imm : BitVec 12)
      (hcode : emitBinConstRhsTo rd rs op w = [.instr (.aluImm iop rd rs imm)])
      (hv : evalAluImm iop x.toBitVec imm = (op.eval x w).toBitVec),
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (emitBinConstRhsTo rd rs op w))) ∧
        st'.getReg rd = (op.eval x w).toBitVec ∧
        (∀ r, r ≠ rd → r ≠ AbiReg.t0 → st'.getReg r = st.getReg r) ∧
        st'.mem = st.mem := by
    intro iop imm hcode hv
    rw [hcode] at hlink h64 ⊢
    have htw1 : lm.totalSize [.instr (.aluImm iop rd rs imm)] = 1 := by simp [lm.itemSize_instr]
    rw [htw1] at h64 ⊢
    have hs := step_item_instr_lm lm env.hrom pre post (.aluImm iop rd rs imm) hlink (by omega) st hpc
    let st1 := stepReg st rd (evalAluImm iop (st.getReg rs) imm) (st.pc + 4#64)
    refine ⟨1, st1, run_one_cont _ _ _ (by rw [hs]; rfl), pc_add_4_ofNat st.pc hpc,
      by rw [getReg_stepReg_eq _ _ hrd, hrs, hv],
      fun r hr1 _ => getReg_stepReg_ne st rd r hr1 _ _, mem_stepReg _ _ _ _⟩
  have fits_sext : ∀ (bv : BitVec 64), fitsImm12 bv = true → sextImm12 (bv.extractLsb' 0 12) = bv := fun bv h =>
    beq_iff_eq.mp h
  cases op with
  | add =>
    by_cases hw0 : w = 0
    · exact stepMvIf (by simp [emitBinConstRhsTo, hw0]) (by subst hw0; simp [BinOp.eval])
    · by_cases hfit : fitsImm12 w.toBitVec = true
      · exact stepAluImm .addi (w.toBitVec.extractLsb' 0 12) (by simp [emitBinConstRhsTo, hw0, hfit, Asm.addi])
          (by simp [evalAluImm, fits_sext _ hfit, BinOp.eval, UInt64.toBitVec_add])
      · exact stepLiBin (by simp [emitBinConstRhsTo, emitBinOp, hw0, hfit])
  | sub =>
    by_cases hw0 : w = 0
    · exact stepMvIf (by simp [emitBinConstRhsTo, hw0]) (by subst hw0; simp [BinOp.eval])
    · by_cases hfit : fitsImm12 (-w.toBitVec) = true
      · exact stepAluImm .addi ((-w.toBitVec).extractLsb' 0 12) (by simp [emitBinConstRhsTo, hw0, hfit, Asm.addi])
          (by simp [evalAluImm, fits_sext _ hfit, BinOp.eval, UInt64.toBitVec_sub, BitVec.sub_eq_add_neg])
      · exact stepLiBin (by simp [emitBinConstRhsTo, emitBinOp, hw0, hfit])
  | and =>
    by_cases hw0 : w = 0
    · have hc : emitBinConstRhsTo rd rs .and w = [Asm.addi rd AbiReg.zero 0#12] := by simp [emitBinConstRhsTo, hw0]
      rw [hc] at hlink h64 ⊢
      have htw1 : lm.totalSize [Asm.addi rd AbiReg.zero 0#12] = 1 := by simp [Asm.addi, lm.itemSize_instr]
      rw [htw1] at h64 ⊢
      have hs := step_item_instr_lm lm env.hrom pre post (.aluImm .addi rd AbiReg.zero 0#12) hlink (by omega) st hpc
      subst hw0
      refine ⟨1, stepReg st rd 0#64 (st.pc + 4#64), run_one_cont _ _ _ (by rw [hs]; rfl),
        pc_add_4_ofNat st.pc hpc, by rw [getReg_stepReg_eq _ _ hrd]; simp [BinOp.eval],
        fun r hr1 _ => getReg_stepReg_ne st rd r hr1 _ _, mem_stepReg _ _ _ _⟩
    · by_cases hwAll : w = 0xffffffffffffffff
      · refine stepMvIf (by subst hwAll; simp [emitBinConstRhsTo]) ?_
        subst hwAll
        rw [BinOp.eval, UInt64.toBitVec_and, show (0xffffffffffffffff : UInt64).toBitVec = BitVec.allOnes 64 from rfl, BitVec.and_allOnes]
      · by_cases hfit : fitsImm12 w.toBitVec = true
        · exact stepAluImm .andi (w.toBitVec.extractLsb' 0 12) (by simp [emitBinConstRhsTo, hw0, hwAll, hfit, Asm.andi])
            (by simp [evalAluImm, fits_sext _ hfit, BinOp.eval, UInt64.toBitVec_and])
        · cases hmask : lowMaskShift? w with
          | none => exact stepLiBin (by simp [emitBinConstRhsTo, emitBinOp, hw0, hwAll, hfit, hmask])
          | some sh =>
            obtain ⟨k, hk12, hk64, rfl, hwk⟩ := lowMaskShift_spec hmask
            have hc : emitBinConstRhsTo rd rs .and w =
                [Asm.slli rd rs (BitVec.ofNat 6 (64 - k)), Asm.srli rd rd (BitVec.ofNat 6 (64 - k))] := by
              simp [emitBinConstRhsTo, hw0, hwAll, hfit, hmask]
            rw [hc] at hlink h64 ⊢
            have htw2 : lm.totalSize [Asm.slli rd rs (BitVec.ofNat 6 (64 - k)),
                Asm.srli rd rd (BitVec.ofNat 6 (64 - k))] = 2 := by
              simp [Asm.slli, Asm.srli, lm.totalSize_cons, lm.totalSize_nil, lm.itemSize_instr]
            rw [htw2] at h64 ⊢
            have hlink1 : lm.linkSpec (pre ++ [Asm.slli rd rs (BitVec.ofNat 6 (64 - k))] ++
                ([Asm.srli rd rd (BitVec.ofNat 6 (64 - k))] ++ post)) = .ok (env.code, env.labels) := by
              simpa [List.append_assoc] using hlink
            have hlink2 : lm.linkSpec ((pre ++ [Asm.slli rd rs (BitVec.ofNat 6 (64 - k))]) ++
                [Asm.srli rd rd (BitVec.ofNat 6 (64 - k))] ++ post) = .ok (env.code, env.labels) := by
              simpa [List.append_assoc] using hlink
            have hs1 := step_item_instr_lm lm env.hrom pre _ (.shImm .slli rd rs (BitVec.ofNat 6 (64 - k)))
              hlink1 (by omega) st hpc
            let st1 := stepReg st rd (x.toBitVec <<< (64 - k)) (st.pc + 4#64)
            have hsz1 : lm.totalSize (pre ++ [Asm.slli rd rs (BitVec.ofNat 6 (64 - k))]) = lm.totalSize pre + 1 := by
              rw [lm.totalSize_append, Asm.slli, lm.totalSize_instr]
            have hpc1 : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ [Asm.slli rd rs (BitVec.ofNat 6 (64 - k))])) := by
              rw [hsz1]; exact pc_add_4_ofNat st.pc hpc
            have hrun1 : RV64.run env.rom 1 st = .cont st1 := run_one_cont _ _ _ (by
              rw [hs1]; dsimp only [execInstr, evalShiftImm]
              rw [hrs, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; rfl)
            have hs2 := step_item_instr_lm lm env.hrom (pre ++ [Asm.slli rd rs (BitVec.ofNat 6 (64 - k))]) post
              (.shImm .srli rd rd (BitVec.ofNat 6 (64 - k))) hlink2 (by rw [hsz1]; omega) st1 hpc1
            let st2 := stepReg st1 rd ((x.toBitVec <<< (64 - k)) >>> (64 - k)) (st1.pc + 4#64)
            have hrun2 : RV64.run env.rom 1 st1 = .cont st2 := run_one_cont _ _ _ (by
              rw [hs2]; dsimp only [execInstr, evalShiftImm]
              rw [getReg_stepReg_eq _ _ hrd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; rfl)
            have hpc2 : st2.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + 2)) := by
              rw [hsz1] at hpc1
              change st1.pc + 4#64 = _
              rw [pc_add_4_ofNat st1.pc hpc1]
            refine ⟨1 + 1, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2, hpc2, ?_, ?_,
              (mem_stepReg st1 _ _ _).trans (mem_stepReg st _ _ _)⟩
            · rw [getReg_stepReg_eq _ _ hrd, slli_srli_eq_and_lowMask x.toBitVec hk64, ← hwk,
                BinOp.eval, UInt64.toBitVec_and]
            · intro r hr1 _
              rw [getReg_stepReg_ne st1 rd r hr1, getReg_stepReg_ne st rd r hr1]
  | or =>
    by_cases hw0 : w = 0
    · exact stepMvIf (by simp [emitBinConstRhsTo, hw0]) (by subst hw0; simp [BinOp.eval])
    · by_cases hfit : fitsImm12 w.toBitVec = true
      · exact stepAluImm .ori (w.toBitVec.extractLsb' 0 12) (by simp [emitBinConstRhsTo, hw0, hfit, Asm.ori])
          (by simp [evalAluImm, fits_sext _ hfit, BinOp.eval, UInt64.toBitVec_or])
      · exact stepLiBin (by simp [emitBinConstRhsTo, emitBinOp, hw0, hfit])
  | xor =>
    by_cases hw0 : w = 0
    · exact stepMvIf (by simp [emitBinConstRhsTo, hw0]) (by subst hw0; simp [BinOp.eval])
    · by_cases hfit : fitsImm12 w.toBitVec = true
      · exact stepAluImm .xori (w.toBitVec.extractLsb' 0 12) (by simp [emitBinConstRhsTo, hw0, hfit, Asm.xori])
          (by simp [evalAluImm, fits_sext _ hfit, BinOp.eval, UInt64.toBitVec_xor])
      · exact stepLiBin (by simp [emitBinConstRhsTo, emitBinOp, hw0, hfit])
  | shl =>
    have hshEq : (w.toBitVec.extractLsb' 0 6).toNat = w.toNat % 64 := by
      rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, UInt64.toNat_toBitVec]
    by_cases h0 : w.toNat % 64 = 0
    · refine stepMvIf (by simp [emitBinConstRhsTo, h0]) ?_
      rw [uint64_binop_toBitVec .shl, hshEq, h0]; simp
    · have hc : emitBinConstRhsTo rd rs .shl w = [Asm.slli rd rs (BitVec.ofNat 6 (w.toNat % 64))] := by
        simp [emitBinConstRhsTo, h0]
      rw [hc] at hlink h64 ⊢
      have htw1 : lm.totalSize [Asm.slli rd rs (BitVec.ofNat 6 (w.toNat % 64))] = 1 := by
        simp [Asm.slli, lm.itemSize_instr]
      rw [htw1] at h64 ⊢
      have hs := step_item_instr_lm lm env.hrom pre post
        (.shImm .slli rd rs (BitVec.ofNat 6 (w.toNat % 64))) hlink (by omega) st hpc
      refine ⟨1, stepReg st rd (x.toBitVec <<< (w.toNat % 64)) (st.pc + 4#64),
        run_one_cont _ _ _ (by rw [hs]; dsimp only [execInstr, evalShiftImm]; rw [hrs, BitVec.toNat_ofNat, Nat.mod_mod]; rfl),
        pc_add_4_ofNat st.pc hpc, ?_,
        fun r hr1 _ => getReg_stepReg_ne st rd r hr1 _ _, mem_stepReg _ _ _ _⟩
      rw [getReg_stepReg_eq _ _ hrd, uint64_binop_toBitVec .shl, hshEq]
  | shr =>
    have hshEq : (w.toBitVec.extractLsb' 0 6).toNat = w.toNat % 64 := by
      rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, UInt64.toNat_toBitVec]
    by_cases h0 : w.toNat % 64 = 0
    · refine stepMvIf (by simp [emitBinConstRhsTo, h0]) ?_
      rw [uint64_binop_toBitVec .shr, hshEq, h0]; simp
    · have hc : emitBinConstRhsTo rd rs .shr w = [Asm.srli rd rs (BitVec.ofNat 6 (w.toNat % 64))] := by
        simp [emitBinConstRhsTo, h0]
      rw [hc] at hlink h64 ⊢
      have htw1 : lm.totalSize [Asm.srli rd rs (BitVec.ofNat 6 (w.toNat % 64))] = 1 := by
        simp [Asm.srli, lm.itemSize_instr]
      rw [htw1] at h64 ⊢
      have hs := step_item_instr_lm lm env.hrom pre post
        (.shImm .srli rd rs (BitVec.ofNat 6 (w.toNat % 64))) hlink (by omega) st hpc
      refine ⟨1, stepReg st rd (x.toBitVec >>> (w.toNat % 64)) (st.pc + 4#64),
        run_one_cont _ _ _ (by rw [hs]; dsimp only [execInstr, evalShiftImm]; rw [hrs, BitVec.toNat_ofNat, Nat.mod_mod]; rfl),
        pc_add_4_ofNat st.pc hpc, ?_,
        fun r hr1 _ => getReg_stepReg_ne st rd r hr1 _ _, mem_stepReg _ _ _ _⟩
      rw [getReg_stepReg_eq _ _ hrd, uint64_binop_toBitVec .shr, hshEq]
  | mul =>
    exact emitMulConstTo_sim_lm lm env pre post rd rs AbiReg.t0 hrd (by decide) hrdt0.symm hrst0.symm w x st hlink h64 hpc hrs
  | mulhi =>
    by_cases hw0 : w = 0
    · have hc : emitBinConstRhsTo rd rs .mulhi w = [Asm.addi rd AbiReg.zero 0#12] := by simp [emitBinConstRhsTo, hw0]
      rw [hc] at hlink h64 ⊢
      have htw1 : lm.totalSize [Asm.addi rd AbiReg.zero 0#12] = 1 := by simp [Asm.addi, lm.itemSize_instr]
      rw [htw1] at h64 ⊢
      have hs := step_item_instr_lm lm env.hrom pre post (.aluImm .addi rd AbiReg.zero 0#12) hlink (by omega) st hpc
      subst hw0
      refine ⟨1, stepReg st rd 0#64 (st.pc + 4#64), run_one_cont _ _ _ (by rw [hs]; rfl),
        pc_add_4_ofNat st.pc hpc, by rw [getReg_stepReg_eq _ _ hrd]; simp [BinOp.eval],
        fun r hr1 _ => getReg_stepReg_ne st rd r hr1 _ _, mem_stepReg _ _ _ _⟩
    · exact stepLiBin (by simp [emitBinConstRhsTo, emitBinOp, hw0])

theorem emitBinConstRhs_sim_lm (lm : LinkModel) (env : CodeEnvGen lm) (pre post : List AsmItem)
    (op : BinOp) (w : UInt64) (x : UInt64) (st : State)
    (hlink : lm.linkSpec (pre ++ emitBinConstRhs op w ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (emitBinConstRhs op w)) < 2 ^ 64)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (ha0 : st.getReg AbiReg.a0 = x.toBitVec) :
    ∃ k st', RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (emitBinConstRhs op w))) ∧
      st'.getReg AbiReg.a0 = (op.eval x w).toBitVec ∧
      PreservedRegs st st' ∧ st'.mem = st.mem := by
  obtain ⟨k, st', hrun, hpc', ha0', hoth, hmem⟩ :=
    emitBinConstRhsTo_sim_lm lm env pre post AbiReg.a0 AbiReg.a0 (by decide) (by decide) (by decide)
      op w x st hlink h64 hpc ha0
  exact ⟨k, st', hrun, hpc', ha0',
    ⟨hoth _ (by decide) (by decide), hoth _ (by decide) (by decide), hoth _ (by decide) (by decide), hoth _ (by decide) (by decide)⟩, hmem⟩

theorem emitCmpwTo_sim_lm (lm : LinkModel) (env : CodeEnvGen lm) (pre post : List AsmItem)
    (rd : Reg) (hrd : rd ≠ 0#5) (c : Cmp) (rL rR : Reg) (va vb : _root_.L.Word) (st1 : State)
    (hlink : lm.linkSpec (pre ++ emitCmpwTo rd c rL rR ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (emitCmpwTo rd c rL rR)) < 2 ^ 64)
    (hpc : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (hL : st1.getReg rL = va.toBitVec) (hR : st1.getReg rR = vb.toBitVec) :
    ∃ k st', RV64.run env.rom k st1 = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (emitCmpwTo rd c rL rR))) ∧
      st'.getReg rd = (c.evalW va vb).toBitVec ∧
      (∀ r, r ≠ rd → st'.getReg r = st1.getReg r) ∧ st'.mem = st1.mem := by
  have step1 : ∀ (i1 : Instr) (w1 : RV64.Word)
      (ht : emitCmpwTo rd c rL rR = [.instr i1])
      (hstep : execInstr st1 i1 = .cont (stepReg st1 rd w1 (st1.pc + 4#64)))
      (hw : w1 = (c.evalW va vb).toBitVec),
      ∃ k st', RV64.run env.rom k st1 = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (emitCmpwTo rd c rL rR))) ∧
        st'.getReg rd = (c.evalW va vb).toBitVec ∧
        (∀ r, r ≠ rd → st'.getReg r = st1.getReg r) ∧ st'.mem = st1.mem := by
    intro i1 w1 ht hstep hw
    rw [ht] at hlink h64 ⊢
    have htw1 : lm.totalSize [.instr i1] = 1 := by simp [lm.itemSize_instr]
    rw [htw1] at h64 ⊢
    have hs := step_item_instr_lm lm env.hrom pre post i1 hlink (by omega) st1 hpc
    refine ⟨1, stepReg st1 rd w1 (st1.pc + 4#64), run_one_cont _ _ _ (by rw [hs, hstep]),
      pc_add_4_ofNat st1.pc hpc, by rw [getReg_stepReg_eq st1 rd hrd, hw],
      fun r hr => getReg_stepReg_ne st1 rd r hr _ _, mem_stepReg _ _ _ _⟩
  have step2 : ∀ (i1 i2 : Instr) (w1 w2 : RV64.Word)
      (ht : emitCmpwTo rd c rL rR = [.instr i1, .instr i2])
      (hstep1 : execInstr st1 i1 = .cont (stepReg st1 rd w1 (st1.pc + 4#64)))
      (hstep2 : execInstr (stepReg st1 rd w1 (st1.pc + 4#64)) i2 =
        .cont (stepReg (stepReg st1 rd w1 (st1.pc + 4#64)) rd w2 ((stepReg st1 rd w1 (st1.pc + 4#64)).pc + 4#64)))
      (hw : w2 = (c.evalW va vb).toBitVec),
      ∃ k st', RV64.run env.rom k st1 = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (emitCmpwTo rd c rL rR))) ∧
        st'.getReg rd = (c.evalW va vb).toBitVec ∧
        (∀ r, r ≠ rd → st'.getReg r = st1.getReg r) ∧ st'.mem = st1.mem := by
    intro i1 i2 w1 w2 ht hstep1 hstep2 hw
    rw [ht] at hlink h64 ⊢
    have htw12 : lm.totalSize [.instr i1, .instr i2] = 2 := by simp [lm.itemSize_instr]
    rw [htw12] at h64 ⊢
    have hs1 := step_item_instr_lm lm env.hrom pre ([.instr i2] ++ post) i1
      (by simpa [List.append_assoc] using hlink) (by omega) st1 hpc
    let st2 := stepReg st1 rd w1 (st1.pc + 4#64)
    have hpc2 : st2.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ [.instr i1])) := by
      rw [lm.totalSize_append, lm.totalSize_instr]; exact pc_add_4_ofNat st1.pc hpc
    have hs2 := step_item_instr_lm lm env.hrom (pre ++ [.instr i1]) post i2
      (by simpa [List.append_assoc] using hlink)
      (by rw [lm.totalSize_append, lm.totalSize_instr]; omega) st2 hpc2
    let st3 := stepReg st2 rd w2 (st2.pc + 4#64)
    refine ⟨2, st3, by rw [show (2 : Nat) = 1 + 1 from rfl, run_add, run_one_cont _ _ _ (by rw [hs1, hstep1])]; exact run_one_cont _ _ _ (by rw [hs2, hstep2]),
      by change st2.pc + 4#64 = _; rw [pc_add_4_ofNat st2.pc hpc2, lm.totalSize_append, lm.totalSize_instr, Nat.add_assoc],
      by rw [getReg_stepReg_eq st2 rd hrd, hw],
      fun r hr => (getReg_stepReg_ne st2 rd r hr _ _).trans (getReg_stepReg_ne st1 rd r hr _ _),
      (mem_stepReg _ _ _ _).trans (mem_stepReg _ _ _ _)⟩
  cases c with
  | eq =>
    refine step2 (.alu .sub rd rL rR) (.aluImm .sltiu rd rd 1#12)
      (va.toBitVec - vb.toBitVec) (if (va.toBitVec - vb.toBitVec).ult 1#64 then 1#64 else 0#64)
      rfl (by simp [execInstr, evalAlu, hL, hR, stepReg])
      (by simp only [execInstr, evalAluImm, getReg_stepReg_eq st1 rd hrd, show sextImm12 1#12 = 1#64 from rfl]; rfl) ?_
    rw [bv_sub_ult1_eq, ← uint64_cmp_eq, Cmp.evalW, Cmp.eval]; cases va == vb <;> decide
  | ne =>
    refine step2 (.alu .sub rd rL rR) (.alu .sltu rd AbiReg.zero rd)
      (va.toBitVec - vb.toBitVec) (if (0#64).ult (va.toBitVec - vb.toBitVec) then 1#64 else 0#64)
      rfl (by simp [execInstr, evalAlu, hL, hR, stepReg])
      (by simp only [execInstr, evalAlu, getReg_zero, getReg_stepReg_eq st1 rd hrd]; rfl) ?_
    rw [bv_zero_ult_sub_eq, ← uint64_cmp_ne, Cmp.evalW, Cmp.eval]; cases va != vb <;> decide
  | ult =>
    refine step1 (.alu .sltu rd rL rR) (if va.toBitVec.ult vb.toBitVec then 1#64 else 0#64)
      rfl (by simp [execInstr, evalAlu, hL, hR, stepReg]) ?_
    rw [← uint64_cmp_ult, Cmp.evalW, Cmp.eval]; cases decide (va < vb) <;> decide
  | ule =>
    refine step2 (.alu .sltu rd rR rL) (.aluImm .xori rd rd 1#12)
      (if vb.toBitVec.ult va.toBitVec then 1#64 else 0#64)
      ((if vb.toBitVec.ult va.toBitVec then 1#64 else 0#64) ^^^ 1#64)
      rfl (by simp [execInstr, evalAlu, hL, hR, stepReg])
      (by simp only [execInstr, evalAluImm, getReg_stepReg_eq st1 rd hrd, show sextImm12 1#12 = 1#64 from rfl]; rfl) ?_
    rw [Cmp.evalW, Cmp.eval, uint64_cmp_ule]; cases vb.toBitVec.ult va.toBitVec <;> decide
  | slt =>
    refine step1 (.alu .slt rd rL rR) (if va.toBitVec.slt vb.toBitVec then 1#64 else 0#64)
      rfl (by simp [execInstr, evalAlu, hL, hR, stepReg]) ?_
    rw [← uint64_cmp_slt, Cmp.evalW, Cmp.eval]; cases decide (va.toInt64 < vb.toInt64) <;> decide
  | sle =>
    refine step2 (.alu .slt rd rR rL) (.aluImm .xori rd rd 1#12)
      (if vb.toBitVec.slt va.toBitVec then 1#64 else 0#64)
      ((if vb.toBitVec.slt va.toBitVec then 1#64 else 0#64) ^^^ 1#64)
      rfl (by simp [execInstr, evalAlu, hL, hR, stepReg])
      (by simp only [execInstr, evalAluImm, getReg_stepReg_eq st1 rd hrd, show sextImm12 1#12 = 1#64 from rfl]; rfl) ?_
    rw [Cmp.evalW, Cmp.eval, uint64_cmp_sle]; cases vb.toBitVec.slt va.toBitVec <;> decide

theorem emitCmpw_sim_lm (lm : LinkModel) (env : CodeEnvGen lm) (pre post : List AsmItem)
    (c : Cmp) (rL rR : Reg) (va vb : _root_.L.Word) (st1 : State)
    (hlink : lm.linkSpec (pre ++ emitCmpw c rL rR ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (emitCmpw c rL rR)) < 2 ^ 64)
    (hpc : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (hL : st1.getReg rL = va.toBitVec) (hR : st1.getReg rR = vb.toBitVec) :
    ∃ k st', RV64.run env.rom k st1 = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (emitCmpw c rL rR))) ∧
      st'.getReg AbiReg.a0 = (c.evalW va vb).toBitVec ∧
      PreservedRegs st1 st' ∧ st'.mem = st1.mem := by
  obtain ⟨k, st', hrun, hpc', ha0', hoth, hmem⟩ :=
    emitCmpwTo_sim_lm lm env pre post AbiReg.a0 (by decide) c rL rR va vb st1 hlink h64 hpc hL hR
  exact ⟨k, st', hrun, hpc', ha0',
    ⟨hoth _ (by decide), hoth _ (by decide), hoth _ (by decide), hoth _ (by decide)⟩, hmem⟩

theorem brCmp_step_reg_lm (lm : LinkModel) (env : CodeEnvGen lm) (pre post : List AsmItem)
    (op : Cmp) (want : Bool) (rL rR : Reg) (hLt6 : rL ≠ AbiReg.t6) (hRt6 : rR ≠ AbiReg.t6)
    (target : String) (tgt : Nat) (va vb : _root_.L.Word) (st1 : State)
    (htgt : lookupLabel env.labels target = some tgt)
    (hlink : lm.linkSpec (pre ++ [brCmp op want rL rR target] ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lm.totalSize pre + lm.itemSize (brCmp op want rL rR target)) < 2 ^ 64)
    (hpc1 : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (hL : st1.getReg rL = va.toBitVec) (hR : st1.getReg rR = vb.toBitVec) :
    ∃ k st2, 1 ≤ k ∧ RV64.run env.rom k st1 = .cont st2 ∧
      st2.pc = BitVec.ofNat 64
        (4 * (if op.eval va vb == want then tgt
              else lm.totalSize pre + lm.itemSize (brCmp op want rL rR target))) ∧
      RegEqExceptT6 st1.regs st2.regs ∧ st2.mem = st1.mem := by
  have stepAux : ∀ (bop : BranchOp) (rs1 rs2 : Reg)
      (hne : rs1 ≠ AbiReg.t6 ∧ rs2 ≠ AbiReg.t6)
      (hbr : brCmp op want rL rR target = .br bop rs1 rs2 target)
      (heval : evalBranch bop (st1.getReg rs1) (st1.getReg rs2) = (op.eval va vb == want)),
      ∃ k st2, 1 ≤ k ∧ RV64.run env.rom k st1 = .cont st2 ∧
        st2.pc = BitVec.ofNat 64
          (4 * (if op.eval va vb == want then tgt
                else lm.totalSize pre + lm.itemSize (brCmp op want rL rR target))) ∧
        RegEqExceptT6 st1.regs st2.regs ∧ st2.mem = st1.mem := by
    intro bop rs1 rs2 hne hbr heval
    rw [hbr] at hlink h64 ⊢
    obtain ⟨tgt', k, st2, hk, hlook, hrun, hpc2, hreg2, hmem2⟩ :=
      step_item_br_lm lm env.hrom pre post bop rs1 rs2 target hlink hne h64 st1 hpc1
    have htgt' : tgt' = tgt := by rw [htgt] at hlook; cases hlook; rfl
    subst htgt'; rw [heval] at hpc2
    refine ⟨k, st2, hk, hrun, ?_, hreg2, hmem2⟩
    rw [hpc2]; cases op.eval va vb == want <;> rfl
  cases op <;> cases want
  · exact stepAux .bne rL rR ⟨hLt6, hRt6⟩ rfl (by rw [evalBranch, hL, hR, Cmp.eval, uint64_cmp_eq]; simp [bne])
  · exact stepAux .beq rL rR ⟨hLt6, hRt6⟩ rfl (by rw [evalBranch, hL, hR, Cmp.eval, uint64_cmp_eq]; cases va.toBitVec == vb.toBitVec <;> rfl)
  · exact stepAux .beq rL rR ⟨hLt6, hRt6⟩ rfl (by rw [evalBranch, hL, hR, Cmp.eval, uint64_cmp_ne]; simp [bne])
  · exact stepAux .bne rL rR ⟨hLt6, hRt6⟩ rfl (by rw [evalBranch, hL, hR, Cmp.eval, uint64_cmp_ne]; simp [bne])
  · exact stepAux .bgeu rL rR ⟨hLt6, hRt6⟩ rfl (by rw [evalBranch, hL, hR, Cmp.eval, uint64_cmp_ult]; cases va.toBitVec.ult vb.toBitVec <;> rfl)
  · exact stepAux .bltu rL rR ⟨hLt6, hRt6⟩ rfl (by rw [evalBranch, hL, hR, Cmp.eval, uint64_cmp_ult]; cases va.toBitVec.ult vb.toBitVec <;> rfl)
  · exact stepAux .bltu rR rL ⟨hRt6, hLt6⟩ rfl (by rw [evalBranch, hL, hR, Cmp.eval, uint64_cmp_ule]; cases vb.toBitVec.ult va.toBitVec <;> rfl)
  · exact stepAux .bgeu rR rL ⟨hRt6, hLt6⟩ rfl (by rw [evalBranch, hL, hR, Cmp.eval, uint64_cmp_ule]; cases vb.toBitVec.ult va.toBitVec <;> rfl)
  · exact stepAux .bge rL rR ⟨hLt6, hRt6⟩ rfl (by rw [evalBranch, hL, hR, Cmp.eval, uint64_cmp_slt]; cases va.toBitVec.slt vb.toBitVec <;> rfl)
  · exact stepAux .blt rL rR ⟨hLt6, hRt6⟩ rfl (by rw [evalBranch, hL, hR, Cmp.eval, uint64_cmp_slt]; cases va.toBitVec.slt vb.toBitVec <;> rfl)
  · exact stepAux .blt rR rL ⟨hRt6, hLt6⟩ rfl (by rw [evalBranch, hL, hR, Cmp.eval, uint64_cmp_sle]; cases vb.toBitVec.slt va.toBitVec <;> rfl)
  · exact stepAux .bge rR rL ⟨hRt6, hLt6⟩ rfl (by rw [evalBranch, hL, hR, Cmp.eval, uint64_cmp_sle]; cases vb.toBitVec.slt va.toBitVec <;> rfl)

theorem brCmp_step_lm (lm : LinkModel) (env : CodeEnvGen lm) (pre post : List AsmItem)
    (op : Cmp) (want : Bool) (rL rR : Reg) (hLt6 : rL ≠ AbiReg.t6) (hRt6 : rR ≠ AbiReg.t6)
    (target : String) (tgt : Nat) (va vb : _root_.L.Word) (st1 : State)
    (htgt : lookupLabel env.labels target = some tgt)
    (hlink : lm.linkSpec (pre ++ [brCmp op want rL rR target] ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lm.totalSize pre + lm.itemSize (brCmp op want rL rR target)) < 2 ^ 64)
    (hpc1 : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (hL : st1.getReg rL = va.toBitVec) (hR : st1.getReg rR = vb.toBitVec) :
    ∃ k st2, 1 ≤ k ∧ RV64.run env.rom k st1 = .cont st2 ∧
      st2.pc = BitVec.ofNat 64
        (4 * (if op.eval va vb == want then tgt
              else lm.totalSize pre + lm.itemSize (brCmp op want rL rR target))) ∧
      PreservedRegs st1 st2 ∧ st2.mem = st1.mem := by
  obtain ⟨k, st2, hk, hrun, hpc2, hreg2, hmem2⟩ :=
    brCmp_step_reg_lm lm env pre post op want rL rR hLt6 hRt6 target tgt va vb st1 htgt hlink h64 hpc1 hL hR
  exact ⟨k, st2, hk, hrun, hpc2, PreservedRegs.of_regEqExceptT6 hreg2, hmem2⟩

theorem emitSimpleExpr_sim_gen (lm : LinkModel) (env : CodeEnvGen lm)
    {nlocals ntemps : Nat} (L : Layout env.tab nlocals ntemps)
    (m : _root_.L.Mem) (loc : _root_.L.Locals)
    (pre post : List AsmItem) (rd tmp : Reg)
    (hrd0 : rd ≠ 0#5) (htmp0 : tmp ≠ 0#5) (_hrdtmp : tmp ≠ rd)
    (htmpSp : tmp ≠ AbiReg.sp) (htmpGp : tmp ≠ AbiReg.gp)
    (e : Expr) (ce : List AsmItem)
    (hsimp : emitSimpleExpr env.tab rd tmp e = some ce)
    (he : CoreExpr env.tab e) (hvars : exprVarsLt nlocals e)
    (hlink : lm.linkSpec (pre ++ ce ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize ce) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = L.sp)
    (hmemRel : MemRel env.tab L st.mem m) (hframeOk : FrameOk L st.mem nlocals loc) :
    ∃ v k st', evalE e ⟨m, loc⟩ = .ok (v, ⟨m, loc⟩) ∧
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize ce)) ∧
      st'.getReg rd = v.toBitVec ∧
      (∀ r, r ≠ rd → r ≠ tmp → st'.getReg r = st.getReg r) ∧
      st'.mem = st.mem := by
  cases e with
  | const w =>
    simp only [emitSimpleExpr, Option.some.injEq] at hsimp; subst hsimp
    obtain ⟨st', hrun, hoth, hrd', hmem, hpc'⟩ :=
      li_correct_lm lm env.hrom pre post rd hrd0 (BitVec.ofNat 64 w.toNat) hlink h64 st hpc
    have hw : BitVec.ofNat 64 w.toNat = w.toBitVec := by
      rw [← UInt64.toBitVec_ofNat' w.toNat, UInt64.ofNat_toNat]
    exact ⟨w, _, st', rfl, hrun, hpc', hrd'.trans hw, fun r hr _ => hoth r hr, hmem⟩
  | var x =>
    simp only [emitSimpleExpr, Option.some.injEq] at hsimp; subst hsimp
    have hal : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff x)) 8 = true := by
      rw [hsp, slotOff_ofInt]; exact isAligned8_add_mul8 L.sp L.hSpAlign (1 + x)
    obtain ⟨st', hrun, hoth, hrd', hmem, hpc'⟩ :=
      loadMemOff_ld_correct_lm lm env.hrom pre post rd AbiReg.sp tmp hrd0 htmp0 htmpSp.symm (slotOff x) hlink h64 st hpc hal
    exact ⟨loc x, _, st', rfl, hrun, hpc', by rw [hrd', hsp, hframeOk x hvars], hoth, hmem⟩
  | len8 a =>
    simp only [emitSimpleExpr, Option.some.injEq] at hsimp; subst hsimp
    cases he with
    | len8 _ ha =>
      have hal : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.len8 a)) 8 = true := by
        rw [hgp, Tab.len8_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
      obtain ⟨st', hrun, hoth, hrd', hmem, hpc'⟩ :=
        loadMemOff_ld_correct_lm lm env.hrom pre post rd AbiReg.gp tmp hrd0 htmp0 htmpGp.symm (env.tab.len8 a) hlink h64 st hpc hal
      rcases hmemRel.1 a ha with ⟨_, _, hlenR, _, _⟩
      exact ⟨m.len8 a, _, st', rfl, hrun, hpc', by rw [hrd', hgp, hlenR]; simp [Mem.len8, UInt64.toBitVec_ofNat'], hoth, hmem⟩
  | len64 a =>
    simp only [emitSimpleExpr, Option.some.injEq] at hsimp; subst hsimp
    cases he with
    | len64 _ ha =>
      have hal : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.len64 (TieredArray.t0 a))) 8 = true := by
        rw [hgp, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
      obtain ⟨st', hrun, hoth, hrd', hmem, hpc'⟩ :=
        loadMemOff_ld_correct_lm lm env.hrom pre post rd AbiReg.gp tmp hrd0 htmp0 htmpGp.symm (env.tab.len64 (TieredArray.t0 a)) hlink h64 st hpc hal
      rcases hmemRel.2.1 (TieredArray.t0 a) ha with ⟨_, _, hlenR, _, _⟩
      exact ⟨m.len64 (TieredArray.t0 a), _, st', rfl, hrun, hpc', by rw [hrd', hgp, hlenR]; simp [Mem.len64, UInt64.toBitVec_ofNat'], hoth, hmem⟩
  | glob g =>
    simp only [emitSimpleExpr, Option.some.injEq] at hsimp; subst hsimp
    cases he with
    | glob _ hg =>
      have hal : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.globOff g)) 8 = true := by
        rw [hgp, Tab.globOff_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
      obtain ⟨st', hrun, hoth, hrd', hmem, hpc'⟩ :=
        loadMemOff_ld_correct_lm lm env.hrom pre post rd AbiReg.gp tmp hrd0 htmp0 htmpGp.symm (env.tab.globOff g) hlink h64 st hpc hal
      exact ⟨m.glob g, _, st', rfl, hrun, hpc', by rw [hrd', hgp, hmemRel.2.2 g hg], hoth, hmem⟩
  | _ => cases hsimp

theorem two_exprs_pair_sim_gen (lm : LinkModel) (env : CodeEnvGen lm) (hm : TabMapOk env.tab)
    {nlocals ntemps : Nat} (L : Layout env.tab nlocals ntemps)
    (m : _root_.L.Mem) (loc : _root_.L.Locals)
    (pre tail : List AsmItem) (tmp : Nat) (e1 e2 : Expr)
    (he1 : CoreExpr env.tab e1) (he2 : CoreExpr env.tab e2)
    (htmp_le : tmp + 1 ≤ ntemps)
    (iha : ∀ (pre post : List AsmItem) (tmp : Nat) (st : State),
      tmp + maxTempsExpr e1 ≤ ntemps →
      lm.linkSpec (pre ++ compileE env.tab nlocals tmp e1 ++ post) = .ok (env.code, env.labels) →
      4 * (lm.totalSize pre + lm.totalSize (compileE env.tab nlocals tmp e1)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → st.getReg AbiReg.sp = L.sp →
      MemRel env.tab L st.mem m → FrameOk L st.mem nlocals loc →
      match evalE e1 ⟨m, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (compileE env.tab nlocals tmp e1))) ∧
          st'.getReg AbiReg.a0 = v.toBitVec ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem)
    (ihb : ∀ (pre post : List AsmItem) (tmp : Nat) (st : State),
      tmp + maxTempsExpr e2 ≤ ntemps →
      lm.linkSpec (pre ++ compileE env.tab nlocals tmp e2 ++ post) = .ok (env.code, env.labels) →
      4 * (lm.totalSize pre + lm.totalSize (compileE env.tab nlocals tmp e2)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → st.getReg AbiReg.sp = L.sp →
      MemRel env.tab L st.mem m → FrameOk L st.mem nlocals loc →
      match evalE e2 ⟨m, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (compileE env.tab nlocals tmp e2))) ∧
          st'.getReg AbiReg.a0 = v.toBitVec ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem)
    (htmp1 : tmp + maxTempsExpr e1 ≤ ntemps)
    (htmp2 : tmp + 1 + maxTempsExpr e2 ≤ ntemps)
    (hlink : lm.linkSpec (pre ++
        (compileE env.tab nlocals tmp e1 ++
         storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + tmp)) ++
         compileE env.tab nlocals (tmp + 1) e2 ++
         loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nlocals + tmp))) ++ tail) =
        .ok (env.code, env.labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize
        (compileE env.tab nlocals tmp e1 ++
         storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + tmp)) ++
         compileE env.tab nlocals (tmp + 1) e2 ++
         loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nlocals + tmp)))) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = L.sp)
    (hmemRel : MemRel env.tab L st.mem m) (hframeOk : FrameOk L st.mem nlocals loc) :
    let seq := compileE env.tab nlocals tmp e1 ++
               storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + tmp)) ++
               compileE env.tab nlocals (tmp + 1) e2 ++
               loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nlocals + tmp))
    match evalE e1 ⟨m, loc⟩, evalE e2 ⟨m, loc⟩ with
    | .ok (v1, _), .ok (v2, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize seq)) ∧
        st'.getReg AbiReg.t0 = v1.toBitVec ∧
        st'.getReg AbiReg.a0 = v2.toBitVec ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem
    | .error _, _ | .ok _, .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem := by
  let c1 := compileE env.tab nlocals tmp e1
  let cs := storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + tmp))
  let c2 := compileE env.tab nlocals (tmp + 1) e2
  let cl := loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nlocals + tmp))
  have htw_all : lm.totalSize (c1 ++ cs ++ c2 ++ cl) =
      lm.totalSize c1 + lm.totalSize cs + lm.totalSize c2 + lm.totalSize cl := by
    simp only [(lm.totalSize_append)]
  have hlist1 : pre ++ c1 ++ (cs ++ c2 ++ cl ++ tail) = pre ++ (c1 ++ cs ++ c2 ++ cl) ++ tail := by
    simp only [List.append_assoc]
  have hlink1 : lm.linkSpec (pre ++ c1 ++ (cs ++ c2 ++ cl ++ tail)) = .ok (env.code, env.labels) := by
    rw [hlist1]; exact hlink
  have h64_1 : 4 * (lm.totalSize pre + lm.totalSize c1) < 2 ^ 64 := by
    rw [htw_all] at h64; omega
  have r1 := iha pre (cs ++ c2 ++ cl ++ tail) tmp st htmp1 hlink1 h64_1 hpc hgp hsp hmemRel hframeOk
  rcases he1.evalE_pure ⟨m, loc⟩ with ⟨v1, hv1⟩ | hv1
  · simp only [hv1] at r1
    obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := r1
    have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.gp.trans hgp
    have hsp1 : st1.getReg AbiReg.sp = L.sp := hpres1.sp.trans hsp
    have htw_p1 : lm.totalSize (pre ++ c1) = lm.totalSize pre + lm.totalSize c1 := (lm.totalSize_append) _ _
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ c1)) := by
      rw [htw_p1]; exact hpc1
    have hlistS : (pre ++ c1) ++ cs ++ (c2 ++ cl ++ tail) = pre ++ (c1 ++ cs ++ c2 ++ cl) ++ tail := by
      simp only [List.append_assoc]
    have hlinkS : lm.linkSpec ((pre ++ c1) ++ cs ++ (c2 ++ cl ++ tail)) = .ok (env.code, env.labels) := by
      rw [hlistS]; exact hlink
    have h64_S : 4 * (lm.totalSize (pre ++ c1) + lm.totalSize cs) < 2 ^ 64 := by
      rw [htw_p1]; rw [htw_all] at h64; omega
    have halS : isAligned (st1.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff (nlocals + tmp))) 8 = true := by
      rw [hsp1, slotOff_ofInt]; exact isAligned8_add_mul8 L.sp L.hSpAlign (1 + (nlocals + tmp))
    obtain ⟨st2, hrunS, hothS, hmem2, hpc2⟩ :=
      storeMemOff_sd_correct_lm lm env.hrom (pre ++ c1) (c2 ++ cl ++ tail) AbiReg.sp AbiReg.a0 AbiReg.t0
        (by decide) (by decide) (by decide) (slotOff (nlocals + tmp)) hlinkS h64_S st1 hpc1' halS
    have hpresS : PreservedRegs st1 st2 :=
      ⟨hothS _ (by decide), hothS _ (by decide), hothS _ (by decide), hothS _ (by decide)⟩
    have hgp2 : st2.getReg AbiReg.gp = L.T := hpresS.gp.trans hgp1
    have hsp2 : st2.getReg AbiReg.sp = L.sp := hpresS.sp.trans hsp1
    have heqS : MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st1.mem st2.mem := by
      rw [hmem2, hsp1, slotOff_ofInt]
      exact MemEqOutside.writeWord64 _ _ _ (tempSpan_slot_sub (Nat.le_refl tmp) (by omega))
    have heq02 : MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st2.mem := heq1.trans heqS
    have htmp0_le : tmp ≤ ntemps := by omega
    have hmemRel2 := memRel_of_eqOutside_temp hm htmp0_le heq02 hmemRel
    have hframeOk2 := frameOk_of_eqOutside_temp htmp0_le heq02 hframeOk
    have hslot2 : readWord64 st2.mem (L.sp + BitVec.ofInt 64 (slotOff (nlocals + tmp))) = v1.toBitVec := by
      rw [hmem2, hsp1, ← ha0_1, readWord64_writeWord64_self]
    have htw_p2 : lm.totalSize (pre ++ c1 ++ cs) = lm.totalSize pre + lm.totalSize c1 + lm.totalSize cs := by
      rw [(lm.totalSize_append), htw_p1]
    have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ c1 ++ cs)) := by
      rw [htw_p2, ← htw_p1]; exact hpc2
    have hlist2 : (pre ++ c1 ++ cs) ++ c2 ++ (cl ++ tail) = pre ++ (c1 ++ cs ++ c2 ++ cl) ++ tail := by
      simp only [List.append_assoc]
    have hlink2 : lm.linkSpec ((pre ++ c1 ++ cs) ++ c2 ++ (cl ++ tail)) = .ok (env.code, env.labels) := by
      rw [hlist2]; exact hlink
    have h64_2 : 4 * (lm.totalSize (pre ++ c1 ++ cs) + lm.totalSize c2) < 2 ^ 64 := by
      rw [htw_p2]; rw [htw_all] at h64; omega
    have r2 := ihb (pre ++ c1 ++ cs) (cl ++ tail) (tmp + 1) st2 htmp2 hlink2 h64_2
      hpc2' hgp2 hsp2 hmemRel2 hframeOk2
    rcases he2.evalE_pure ⟨m, loc⟩ with ⟨v2, hv2⟩ | hv2
    · simp only [hv1, hv2] at r2 ⊢
      obtain ⟨k2, st3, hrun2, hpc3, ha0_3, hpres2, heq2⟩ := r2
      have heq2' : MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st2.mem st3.mem :=
        heq2.mono (tempSpan_mono (Nat.le_succ tmp) htmp_le)
      have heq03 : MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st3.mem := heq02.trans heq2'
      have hsp3 : st3.getReg AbiReg.sp = L.sp := hpres2.sp.trans hsp2
      have hslot3 : readWord64 st3.mem (L.sp + BitVec.ofInt 64 (slotOff (nlocals + tmp))) = v1.toBitVec := by
        rw [← hslot2]
        apply MemEqOutside.readWord64_eq heq2
        intro k hk
        rw [slotOff_ofInt]
        exact (slotSpan_memDisjoint_tempSpan L.hFrameValid htmp_le (by omega)) _ ⟨k, hk, rfl⟩
      have htw_p3 : lm.totalSize (pre ++ c1 ++ cs ++ c2) =
          lm.totalSize pre + lm.totalSize c1 + lm.totalSize cs + lm.totalSize c2 := by
        rw [(lm.totalSize_append), htw_p2]
      have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ c1 ++ cs ++ c2)) := by
        rw [htw_p3, ← htw_p2]; exact hpc3
      have hlistL : (pre ++ c1 ++ cs ++ c2) ++ cl ++ tail = pre ++ (c1 ++ cs ++ c2 ++ cl) ++ tail := by
        simp only [List.append_assoc]
      have hlinkL : lm.linkSpec ((pre ++ c1 ++ cs ++ c2) ++ cl ++ tail) = .ok (env.code, env.labels) := by
        rw [hlistL]; exact hlink
      have h64_L : 4 * (lm.totalSize (pre ++ c1 ++ cs ++ c2) + lm.totalSize cl) < 2 ^ 64 := by
        rw [htw_p3]; rw [htw_all] at h64; omega
      have halL : isAligned (st3.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff (nlocals + tmp))) 8 = true := by
        rw [hsp3, slotOff_ofInt]; exact isAligned8_add_mul8 L.sp L.hSpAlign (1 + (nlocals + tmp))
      obtain ⟨st4, hrunL, hothL, ht0_4, hmem4, hpc4⟩ :=
        loadMemOff_ld_correct_lm lm env.hrom (pre ++ c1 ++ cs ++ c2) tail AbiReg.t0 AbiReg.sp AbiReg.t1
          (by decide) (by decide) (by decide) (slotOff (nlocals + tmp)) hlinkL h64_L st3 hpc3' halL
      have hpresL : PreservedRegs st3 st4 :=
        ⟨hothL _ (by decide) (by decide), hothL _ (by decide) (by decide),
         hothL _ (by decide) (by decide), hothL _ (by decide) (by decide)⟩
      refine ⟨k1 + (lm.totalSize cs + (k2 + lm.totalSize cl)), st4, ?_, ?_, ?_, ?_,
        (hpres1.trans hpresS).trans (hpres2.trans hpresL), hmem4 ▸ heq03⟩
      · rw [run_add, hrun1]; dsimp only
        rw [run_add, hrunS]; dsimp only
        rw [run_add, hrun2]; dsimp only
        exact hrunL
      · rw [hpc4]
        congr 2
        dsimp only [c1, cs, c2, cl]
        simp only [(lm.totalSize_append), Nat.add_assoc]
      · rw [ht0_4, hsp3, hslot3]
      · rw [hothL AbiReg.a0 (by decide) (by decide), ha0_3]
    · simp only [hv1, hv2] at r2 ⊢
      obtain ⟨k2, st3, hrun2, hpc3, hpres2, heq2⟩ := r2
      have heq2' : MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st2.mem st3.mem :=
        heq2.mono (tempSpan_mono (Nat.le_succ tmp) htmp_le)
      refine ⟨k1 + (lm.totalSize cs + k2), st3, ?_, hpc3,
        (hpres1.trans hpresS).trans hpres2, heq02.trans heq2'⟩
      rw [run_add, hrun1]; dsimp only
      rw [run_add, hrunS]; dsimp only
      exact hrun2
  · simp only [hv1] at r1 ⊢
    exact r1

private theorem ld8_sim_gen (lm : LinkModel) (env : CodeEnvGen lm) (hm : TabMapOk env.tab)
    {nlocals ntemps : Nat} (L : Layout env.tab nlocals ntemps)
    (m : _root_.L.Mem) (loc : _root_.L.Locals)
    (pre post : List AsmItem) (tmp : Nat) (a : ArrId) (i : Expr)
    (ha : (TieredArray.t0 a) ∈ env.tab.arrAt) (hiExpr : CoreExpr env.tab i)
    (htmp : tmp + maxTempsExpr i ≤ ntemps)
    (ihi : ∀ (pre post : List AsmItem) (tmp : Nat) (st : State),
      tmp + maxTempsExpr i ≤ ntemps →
      lm.linkSpec (pre ++ compileE env.tab nlocals tmp i ++ post) = .ok (env.code, env.labels) →
      4 * (lm.totalSize pre + lm.totalSize (compileE env.tab nlocals tmp i)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → st.getReg AbiReg.sp = L.sp →
      MemRel env.tab L st.mem m → FrameOk L st.mem nlocals loc →
      match evalE i ⟨m, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (compileE env.tab nlocals tmp i))) ∧
          st'.getReg AbiReg.a0 = v.toBitVec ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem)
    (hlink : lm.linkSpec (pre ++ compileE env.tab nlocals tmp (.ld8 a i) ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (compileE env.tab nlocals tmp (.ld8 a i))) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = L.sp)
    (hmemRel : MemRel env.tab L st.mem m) (hframeOk : FrameOk L st.mem nlocals loc) :
    match evalE (.ld8 a i) ⟨m, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (compileE env.tab nlocals tmp (.ld8 a i)))) ∧
        st'.getReg AbiReg.a0 = v.toBitVec ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem := by
  let ci := compileE env.tab nlocals tmp i
  let clen := loadMemOff .ld AbiReg.t0 AbiReg.gp AbiReg.t1 (env.tab.len8 a)
  let cbr := [Asm.bgeu AbiReg.a0 AbiReg.t0 errLabel]
  let cbase := loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base8 a)
  let cld := [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.a0, Asm.lbu AbiReg.a0 AbiReg.t1 0#12]
  have hce : compileE env.tab nlocals tmp (.ld8 a i) = ci ++ clen ++ cbr ++ cbase ++ cld := by
    simp [ci, clen, cbr, cbase, cld, compileE, List.append_assoc]
  let brSz := lm.itemSize (.br .bgeu AbiReg.a0 AbiReg.t0 errLabel)
  have htw_ce : lm.totalSize (compileE env.tab nlocals tmp (.ld8 a i)) =
      lm.totalSize ci + lm.totalSize clen + brSz + lm.totalSize cbase + 2 := by
    rw [hce]; simp only [lm.totalSize_append]
    have h1 : lm.totalSize cbr = brSz := by simp [cbr, Asm.bgeu, brSz]
    have h2 : lm.totalSize cld = 2 := by simp [cld, Asm.add, Asm.lbu, lm.itemSize_instr]
    omega
  have htw_ci : lm.totalSize (compileE env.tab nlocals tmp i) = lm.totalSize ci := rfl
  have hlistI : pre ++ ci ++ (clen ++ cbr ++ cbase ++ cld ++ post) =
      pre ++ (ci ++ clen ++ cbr ++ cbase ++ cld) ++ post := by
    simp only [List.append_assoc]
  have hlinkI : lm.linkSpec (pre ++ ci ++ (clen ++ cbr ++ cbase ++ cld ++ post)) = .ok (env.code, env.labels) := by
    rw [hlistI, ← hce]; exact hlink
  have ri := ihi pre (clen ++ cbr ++ cbase ++ cld ++ post) tmp st htmp hlinkI
    (by rw [htw_ci]; rw [htw_ce] at h64; omega) hpc hgp hsp hmemRel hframeOk
  rcases hiExpr.evalE_pure ⟨m, loc⟩ with ⟨vi, hvi⟩ | hvi
  · simp only [hvi] at ri
    obtain ⟨ki, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ri
    have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.gp.trans hgp
    have hmemRel1 := memRel_of_eqOutside_temp hm (by omega) heq1 hmemRel
    rcases hmemRel1.1 a ha with ⟨_, hlt64, hlenR, hbaseR, hbytesR⟩
    have htw_p1 : lm.totalSize (pre ++ ci) = lm.totalSize pre + lm.totalSize ci := (lm.totalSize_append) _ _
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ ci)) := by
      rw [htw_p1, ← htw_ci]; exact hpc1
    have hlistLen : (pre ++ ci) ++ clen ++ (cbr ++ cbase ++ cld ++ post) =
        pre ++ (ci ++ clen ++ cbr ++ cbase ++ cld) ++ post := by
      simp only [List.append_assoc]
    have hlinkLen : lm.linkSpec ((pre ++ ci) ++ clen ++ (cbr ++ cbase ++ cld ++ post)) =
        .ok (env.code, env.labels) := by
      rw [hlistLen, ← hce]; exact hlink
    have halLen : isAligned (st1.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.len8 a)) 8 = true := by
      rw [hgp1, Tab.len8_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    have htw_clen : lm.totalSize (loadMemOff .ld AbiReg.t0 AbiReg.gp AbiReg.t1 (env.tab.len8 a)) = lm.totalSize clen := rfl
    obtain ⟨st2, hrun2, hoth2, ht0_2, hmem2, hpc2⟩ :=
      loadMemOff_ld_correct_lm lm env.hrom (pre ++ ci) (cbr ++ cbase ++ cld ++ post)
        AbiReg.t0 AbiReg.gp AbiReg.t1 (by decide) (by decide) (by decide) (env.tab.len8 a)
        hlinkLen (by rw [htw_clen, htw_p1]; rw [htw_ce] at h64; omega) st1 hpc1' halLen
    have hpres12 : PreservedRegs st1 st2 :=
      ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
       hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide)⟩
    have hgp2 : st2.getReg AbiReg.gp = L.T := hpres12.gp.trans hgp1
    have ha0_2 : st2.getReg AbiReg.a0 = vi.toBitVec := by
      rw [hoth2 AbiReg.a0 (by decide) (by decide), ha0_1]
    have ht0_2' : st2.getReg AbiReg.t0 = BitVec.ofNat 64 (m.arr8 a).size := by
      rw [ht0_2, hgp1, hlenR]
    have htw2 : lm.totalSize (pre ++ ci ++ clen) = lm.totalSize pre + lm.totalSize ci + lm.totalSize clen := by
      rw [(lm.totalSize_append), htw_p1]
    have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ ci ++ clen)) := by
      rw [htw2, ← htw_p1, ← htw_clen]; exact hpc2
    have hlistBr : (pre ++ ci ++ clen) ++ [Asm.bgeu AbiReg.a0 AbiReg.t0 errLabel] ++ (cbase ++ cld ++ post) =
        pre ++ (ci ++ clen ++ cbr ++ cbase ++ cld) ++ post := by
      simp only [cbr, List.append_assoc]
    have hlinkBr : lm.linkSpec ((pre ++ ci ++ clen) ++ [Asm.bgeu AbiReg.a0 AbiReg.t0 errLabel] ++
        (cbase ++ cld ++ post)) = .ok (env.code, env.labels) := by
      rw [hlistBr, ← hce]; exact hlink
    obtain ⟨tgt, kbr, st3, _, hlook, hrunBr, hpc3_raw, hreg3, hmem3⟩ :=
      step_item_br_lm lm env.hrom (pre ++ ci ++ clen) (cbase ++ cld ++ post) .bgeu AbiReg.a0 AbiReg.t0 errLabel
        hlinkBr (by decide) (by rw [htw2]; rw [htw_ce] at h64; simp only [Asm.bgeu, brSz] at *; omega) st2 hpc2'
    have htgt : tgt = env.errTarget := by rw [env.herrLbl] at hlook; cases hlook; rfl
    subst htgt
    by_cases hbound : vi.toNat < (m.arr8 a).size
    · have heval : evalE (.ld8 a i) ⟨m, loc⟩ = .ok ((m.arr8 a)[vi.toNat].toUInt64, ⟨m, loc⟩) := by
        change (evalE i >>= fun idx => _root_.L.ld8 a idx) ⟨m, loc⟩ = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]
        rw [hvi]
        dsimp only [_root_.L.ld8, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
          Pure.pure, StateT.pure, Except.pure, Except.bind]
        simp [hbound]; rfl
      rw [heval]
      have hbrF : evalBranch .bgeu (st2.getReg AbiReg.a0) (st2.getReg AbiReg.t0) = false := by
        rw [ha0_2, ht0_2', evalBranch, BitVec.ult]
        have h1 : (BitVec.ofNat 64 (m.arr8 a).size).toNat = (m.arr8 a).size := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
        simp [UInt64.toNat_toBitVec, h1, hbound]
      have hpres23 : PreservedRegs st2 st3 := PreservedRegs.of_regEqExceptT6 hreg3
      rw [hbrF] at hpc3_raw
      simp only [Bool.false_eq_true, ↓reduceIte] at hpc3_raw
      have htw3 : lm.totalSize (pre ++ ci ++ clen ++ cbr) = lm.totalSize pre + lm.totalSize ci + lm.totalSize clen + brSz := by
        rw [lm.totalSize_append, htw2]; simp [cbr, Asm.bgeu, brSz]
      have hpc3 : st3.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ ci ++ clen ++ cbr)) := by
        rw [hpc3_raw, htw3, htw2]
      have hgp3 : st3.getReg AbiReg.gp = L.T := (hreg3.getReg_eq (by decide)).symm.trans hgp2
      have ha0_3 : st3.getReg AbiReg.a0 = vi.toBitVec := (hreg3.getReg_eq (by decide)).symm.trans ha0_2
      have hlistBase : (pre ++ ci ++ clen ++ cbr) ++ cbase ++ (cld ++ post) =
          pre ++ (ci ++ clen ++ cbr ++ cbase ++ cld) ++ post := by
        simp only [List.append_assoc]
      have hlinkBase : lm.linkSpec ((pre ++ ci ++ clen ++ cbr) ++ cbase ++ (cld ++ post)) =
          .ok (env.code, env.labels) := by
        rw [hlistBase, ← hce]; exact hlink
      have halBase : isAligned (st3.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.base8 a)) 8 = true := by
        rw [hgp3, Tab.base8_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
      have htw_cbase : lm.totalSize (loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base8 a)) = lm.totalSize cbase := rfl
      obtain ⟨st4, hrun4, hoth4, ht1_4, hmem4, hpc4⟩ :=
        loadMemOff_ld_correct_lm lm env.hrom (pre ++ ci ++ clen ++ cbr) (cld ++ post)
          AbiReg.t1 AbiReg.gp AbiReg.t2 (by decide) (by decide) (by decide) (env.tab.base8 a)
          hlinkBase (by rw [htw_cbase, htw3]; rw [htw_ce] at h64; omega) st3 hpc3 halBase
      have hpres34 : PreservedRegs st3 st4 :=
        ⟨hoth4 _ (by decide) (by decide), hoth4 _ (by decide) (by decide),
         hoth4 _ (by decide) (by decide), hoth4 _ (by decide) (by decide)⟩
      have ht1_4' : st4.getReg AbiReg.t1 = L.base8 a := by
        rw [ht1_4, hmem3, hmem2, hgp3, hbaseR]
      have ha0_4 : st4.getReg AbiReg.a0 = vi.toBitVec := by
        rw [hoth4 AbiReg.a0 (by decide) (by decide)]; exact ha0_3
      have htw4 : lm.totalSize (pre ++ ci ++ clen ++ cbr ++ cbase) =
          lm.totalSize pre + lm.totalSize ci + lm.totalSize clen + brSz + lm.totalSize cbase := by
        rw [(lm.totalSize_append), htw3]
      have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ ci ++ clen ++ cbr ++ cbase)) := by
        rw [htw4, ← htw3, ← htw_cbase]; exact hpc4
      have hlistAdd : (pre ++ ci ++ clen ++ cbr ++ cbase) ++
          [.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.a0)] ++
          ([Asm.lbu AbiReg.a0 AbiReg.t1 0#12] ++ post) =
          pre ++ (ci ++ clen ++ cbr ++ cbase ++ cld) ++ post := by
        simp only [cld, Asm.add, Asm.lbu, List.append_assoc, List.cons_append, List.nil_append]
      have hlinkAdd : lm.linkSpec ((pre ++ ci ++ clen ++ cbr ++ cbase) ++
          [.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.a0)] ++
          ([Asm.lbu AbiReg.a0 AbiReg.t1 0#12] ++ post)) = .ok (env.code, env.labels) := by
        rw [hlistAdd, ← hce]; exact hlink
      have hs5 := step_item_instr_lm lm env.hrom (pre ++ ci ++ clen ++ cbr ++ cbase)
        ([Asm.lbu AbiReg.a0 AbiReg.t1 0#12] ++ post) (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.a0)
        hlinkAdd (by rw [htw4]; rw [htw_ce] at h64; omega) st4 hpc4'
      let st5 := stepReg st4 AbiReg.t1 (st4.getReg AbiReg.t1 + st4.getReg AbiReg.a0) (st4.pc + 4#64)
      have hpres45 : PreservedRegs st4 st5 :=
        ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _⟩
      have htw5 : lm.totalSize (pre ++ ci ++ clen ++ cbr ++ cbase ++ [.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.a0)]) =
          lm.totalSize pre + lm.totalSize ci + lm.totalSize clen + brSz + lm.totalSize cbase + 1 := by
        rw [lm.totalSize_append, htw4, lm.totalSize_instr]
      have hpc5 : st5.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ ci ++ clen ++ cbr ++ cbase ++
          [.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.a0)])) := by
        change st4.pc + 4#64 = _; rw [htw5, ← htw4]; exact pc_add_4_ofNat st4.pc hpc4'
      have hlistLd : (pre ++ ci ++ clen ++ cbr ++ cbase ++ [.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.a0)]) ++
          [.instr (.load .lbu AbiReg.a0 AbiReg.t1 0#12)] ++ post =
          pre ++ (ci ++ clen ++ cbr ++ cbase ++ cld) ++ post := by
        simp only [cld, Asm.add, Asm.lbu, List.append_assoc, List.cons_append, List.nil_append]
      have hlinkLd : lm.linkSpec ((pre ++ ci ++ clen ++ cbr ++ cbase ++ [.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.a0)]) ++
          [.instr (.load .lbu AbiReg.a0 AbiReg.t1 0#12)] ++ post) = .ok (env.code, env.labels) := by
        rw [hlistLd, ← hce]; exact hlink
      have hs6 := step_item_instr_lm lm env.hrom
        (pre ++ ci ++ clen ++ cbr ++ cbase ++ [.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.a0)])
        post (.load .lbu AbiReg.a0 AbiReg.t1 0#12) hlinkLd
        (by rw [htw5]; rw [htw_ce] at h64; omega) st5 hpc5
      let st6 := stepReg st5 AbiReg.a0
        ((loadBytes st5.mem (st5.getReg AbiReg.t1 + sextImm12 0#12) 1).zeroExtend 64) (st5.pc + 4#64)
      have hpres56 : PreservedRegs st5 st6 :=
        ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _,
         getReg_stepReg_ne _ _ _ (by decide) _ _⟩
      have haddr5 : st5.getReg AbiReg.t1 + sextImm12 0#12 = L.base8 a + BitVec.ofNat 64 vi.toNat := by
        have hz : sextImm12 0#12 = 0#64 := rfl
        have hvi_bv : vi.toBitVec = BitVec.ofNat 64 vi.toNat := by
          apply BitVec.eq_of_toNat_eq; simp [UInt64.toNat_toBitVec]
        change (stepReg st4 AbiReg.t1 _ _).getReg AbiReg.t1 + sextImm12 0#12 = _
        rw [hz, BitVec.add_zero, getReg_stepReg_eq _ _ (by decide), ht1_4', ha0_4, hvi_bv]
      refine ⟨ki + (lm.totalSize clen + (kbr + (lm.totalSize cbase + (1 + 1)))), st6, ?_, ?_, ?_,
        hpres1.trans (hpres12.trans (hpres23.trans (hpres34.trans (hpres45.trans hpres56)))), ?_⟩
      · rw [run_add, hrun1]; dsimp only
        rw [run_add, hrun2]; dsimp only
        rw [run_add, hrunBr]; dsimp only
        rw [run_add, hrun4]; dsimp only
        rw [run_add, run_one_cont _ _ st5 (by rw [hs5]; rfl)]; dsimp only
        exact run_one_cont _ _ st6 (by rw [hs6]; rfl)
      · change st5.pc + 4#64 = _
        rw [pc_add_4_ofNat st5.pc hpc5, htw5, htw_ce]
        congr 2; omega
      · change (stepReg st5 AbiReg.a0 _ _).getReg AbiReg.a0 = _
        rw [getReg_stepReg_eq _ _ (by decide), haddr5]
        have hmem5 : st5.mem = st1.mem := by
          change st4.mem = _; rw [hmem4, hmem3]; exact hmem2
        rw [hmem5]
        exact loadBytes_one_uint8 _ _ _ (hbytesR vi.toNat hbound)
      · change MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st5.mem
        have hmem5 : st5.mem = st1.mem := by
          change st4.mem = _; rw [hmem4, hmem3]; exact hmem2
        rw [hmem5]; exact heq1
    · have heval : evalE (.ld8 a i) ⟨m, loc⟩ = .error .oob := by
        change (evalE i >>= fun idx => _root_.L.ld8 a idx) ⟨m, loc⟩ = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]
        rw [hvi]
        dsimp only [_root_.L.ld8, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
          Pure.pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, Except.pure]
        simp [hbound]; rfl
      rw [heval]
      have hbrT : evalBranch .bgeu (st2.getReg AbiReg.a0) (st2.getReg AbiReg.t0) = true := by
        rw [ha0_2, ht0_2', evalBranch, BitVec.ult]
        have h1 : (BitVec.ofNat 64 (m.arr8 a).size).toNat = (m.arr8 a).size := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
        simp [UInt64.toNat_toBitVec, h1, hbound]
      have hpres23 : PreservedRegs st2 st3 := PreservedRegs.of_regEqExceptT6 hreg3
      rw [hbrT] at hpc3_raw; simp only [↓reduceIte] at hpc3_raw
      refine ⟨ki + (lm.totalSize clen + kbr), st3, ?_, hpc3_raw, hpres1.trans (hpres12.trans hpres23), ?_⟩
      · rw [run_add, hrun1]; dsimp only
        rw [run_add, hrun2]; dsimp only
        exact hrunBr
      · rw [hmem3, hmem2]; exact heq1
  · have heval : evalE (.ld8 a i) ⟨m, loc⟩ = .error .oob := by
      simp [evalE, Bind.bind, StateT.bind, Except.bind, hvi]
    rw [heval]; simp only [hvi] at ri; exact ri

private theorem ld64_ok_tail_gen (lm : LinkModel) (env : CodeEnvGen lm) {nlocals ntemps : Nat} (L : Layout env.tab nlocals ntemps)
    (m : _root_.L.Mem) (pre3 post : List AsmItem) (a : ArrId) (vi : _root_.L.Word) (st3 : State)
    (hlink3 : lm.linkSpec (pre3 ++
      (loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base64 (TieredArray.t0 a)) ++
        [Asm.slli AbiReg.t2 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2, Asm.ld AbiReg.a0 AbiReg.t1 0#12]) ++
      post) = .ok (env.code, env.labels))
    (h64_3 : 4 * (lm.totalSize pre3 +
      lm.totalSize (loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base64 (TieredArray.t0 a))) + 3) < 2 ^ 64)
    (hpc3 : st3.pc = BitVec.ofNat 64 (4 * lm.totalSize pre3))
    (hgp3 : st3.getReg AbiReg.gp = L.T) (ha0_3 : st3.getReg AbiReg.a0 = vi.toBitVec)
    (hbaseR3 : readWord64 st3.mem (L.T + BitVec.ofInt 64 (env.tab.base64 (TieredArray.t0 a))) = L.base64 (TieredArray.t0 a))
    (hbound : vi.toNat < (m.arr64 (TieredArray.t0 a)).size)
    (hwordsR3 : ∀ j (hj : j < (m.arr64 (TieredArray.t0 a)).size),
      readWord64 st3.mem (L.base64 (TieredArray.t0 a) + BitVec.ofNat 64 (8 * j)) =
        ((m.arr64 (TieredArray.t0 a))[j]).toBitVec) :
    ∃ k st', RV64.run env.rom k st3 = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre3 +
        lm.totalSize (loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base64 (TieredArray.t0 a))) + 3)) ∧
      st'.getReg AbiReg.a0 = ((m.arr64 (TieredArray.t0 a))[vi.toNat]).toBitVec ∧
      PreservedRegs st3 st' ∧ st'.mem = st3.mem := by
  let cbase := loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base64 (TieredArray.t0 a))
  have htw_cb : lm.totalSize (loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base64 (TieredArray.t0 a))) =
      lm.totalSize cbase := rfl
  let cld : List AsmItem :=
    [Asm.slli AbiReg.t2 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2, Asm.ld AbiReg.a0 AbiReg.t1 0#12]
  have hlistBase : pre3 ++ cbase ++ (cld ++ post) = pre3 ++ (cbase ++ cld) ++ post := by
    simp only [List.append_assoc]
  have hlinkBase : lm.linkSpec (pre3 ++ cbase ++ (cld ++ post)) = .ok (env.code, env.labels) := by
    rw [hlistBase]; exact hlink3
  have halBase : isAligned (st3.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.base64 (TieredArray.t0 a))) 8 = true := by
    rw [hgp3, Tab.base64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
  obtain ⟨st4, hrun4, hoth4, ht1_4, hmem4, hpc4⟩ :=
    loadMemOff_ld_correct_lm lm env.hrom pre3 (cld ++ post)
      AbiReg.t1 AbiReg.gp AbiReg.t2 (by decide) (by decide) (by decide)
      (env.tab.base64 (TieredArray.t0 a)) hlinkBase (by omega) st3 hpc3 halBase
  have hpres34 : PreservedRegs st3 st4 :=
    ⟨hoth4 _ (by decide) (by decide), hoth4 _ (by decide) (by decide),
     hoth4 _ (by decide) (by decide), hoth4 _ (by decide) (by decide)⟩
  have ht1_4' : st4.getReg AbiReg.t1 = L.base64 (TieredArray.t0 a) := by
    rw [ht1_4, hgp3, hbaseR3]
  have ha0_4 : st4.getReg AbiReg.a0 = vi.toBitVec := by
    rw [hoth4 AbiReg.a0 (by decide) (by decide), ha0_3]
  have htw4 : lm.totalSize (pre3 ++ cbase) = lm.totalSize pre3 + lm.totalSize cbase := (lm.totalSize_append) _ _
  have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre3 ++ cbase)) := by
    rw [htw4]; exact hpc4
  have hlistSll : (pre3 ++ cbase) ++ [.instr (.shImm .slli AbiReg.t2 AbiReg.a0 3#6)] ++
      ([Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2, Asm.ld AbiReg.a0 AbiReg.t1 0#12] ++ post) =
      pre3 ++ (cbase ++ cld) ++ post := by
    simp only [cld, Asm.slli, Asm.add, Asm.ld, List.append_assoc, List.cons_append, List.nil_append]
  have hlinkSll : lm.linkSpec ((pre3 ++ cbase) ++ [.instr (.shImm .slli AbiReg.t2 AbiReg.a0 3#6)] ++
      ([Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2, Asm.ld AbiReg.a0 AbiReg.t1 0#12] ++ post)) =
      .ok (env.code, env.labels) := by
    rw [hlistSll]; exact hlink3
  have hs5 := step_item_instr_lm lm env.hrom (pre3 ++ cbase)
    ([Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2, Asm.ld AbiReg.a0 AbiReg.t1 0#12] ++ post)
    (.shImm .slli AbiReg.t2 AbiReg.a0 3#6) hlinkSll
    (by rw [htw4, htw_cb]; omega) st4 hpc4'
  let st5 := stepReg st4 AbiReg.t2 (st4.getReg AbiReg.a0 <<< 3) (st4.pc + 4#64)
  have hpres45 : PreservedRegs st4 st5 :=
    ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
     getReg_stepReg_ne _ _ _ (by decide) _ _,
     getReg_stepReg_ne _ _ _ (by decide) _ _⟩
  have htw5 : lm.totalSize (pre3 ++ cbase ++ [.instr (.shImm .slli AbiReg.t2 AbiReg.a0 3#6)]) =
      lm.totalSize (pre3 ++ cbase) + 1 := by
    rw [lm.totalSize_append, lm.totalSize_instr]
  have hpc5 : st5.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre3 ++ cbase ++
      [.instr (.shImm .slli AbiReg.t2 AbiReg.a0 3#6)])) := by
    change st4.pc + 4#64 = _; rw [pc_add_4_ofNat st4.pc hpc4', htw5]
  have hlistAdd : (pre3 ++ cbase ++ [.instr (.shImm .slli AbiReg.t2 AbiReg.a0 3#6)]) ++
      [.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.t2)] ++
      ([Asm.ld AbiReg.a0 AbiReg.t1 0#12] ++ post) = pre3 ++ (cbase ++ cld) ++ post := by
    simp only [cld, Asm.slli, Asm.add, Asm.ld, List.append_assoc, List.cons_append, List.nil_append]
  have hlinkAdd : lm.linkSpec ((pre3 ++ cbase ++ [.instr (.shImm .slli AbiReg.t2 AbiReg.a0 3#6)]) ++
      [.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.t2)] ++
      ([Asm.ld AbiReg.a0 AbiReg.t1 0#12] ++ post)) = .ok (env.code, env.labels) := by
    rw [hlistAdd]; exact hlink3
  have hs6 := step_item_instr_lm lm env.hrom
    (pre3 ++ cbase ++ [.instr (.shImm .slli AbiReg.t2 AbiReg.a0 3#6)])
    ([Asm.ld AbiReg.a0 AbiReg.t1 0#12] ++ post) (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.t2) hlinkAdd
    (by rw [htw5, htw4, htw_cb]; omega) st5 hpc5
  let st6 := stepReg st5 AbiReg.t1 (st5.getReg AbiReg.t1 + st5.getReg AbiReg.t2) (st5.pc + 4#64)
  have hpres56 : PreservedRegs st5 st6 :=
    ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
     getReg_stepReg_ne _ _ _ (by decide) _ _,
     getReg_stepReg_ne _ _ _ (by decide) _ _⟩
  have htw6 : lm.totalSize (pre3 ++ cbase ++ [.instr (.shImm .slli AbiReg.t2 AbiReg.a0 3#6)] ++
      [.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.t2)]) = lm.totalSize (pre3 ++ cbase) + 2 := by
    rw [lm.totalSize_append, htw5, lm.totalSize_instr]
  have hpc6 : st6.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre3 ++ cbase ++
      [.instr (.shImm .slli AbiReg.t2 AbiReg.a0 3#6)] ++ [.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.t2)])) := by
    change st5.pc + 4#64 = _; rw [pc_add_4_ofNat st5.pc hpc5, htw6, htw5]
  have hlistLd : (pre3 ++ cbase ++ [.instr (.shImm .slli AbiReg.t2 AbiReg.a0 3#6)] ++
      [.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.t2)]) ++
      [.instr (.load .ld AbiReg.a0 AbiReg.t1 0#12)] ++ post = pre3 ++ (cbase ++ cld) ++ post := by
    simp only [cld, Asm.slli, Asm.add, Asm.ld, List.append_assoc, List.cons_append, List.nil_append]
  have hlinkLd : lm.linkSpec ((pre3 ++ cbase ++ [.instr (.shImm .slli AbiReg.t2 AbiReg.a0 3#6)] ++
      [.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.t2)]) ++
      [.instr (.load .ld AbiReg.a0 AbiReg.t1 0#12)] ++ post) = .ok (env.code, env.labels) := by
    rw [hlistLd]; exact hlink3
  have hs7 := step_item_instr_lm lm env.hrom
    (pre3 ++ cbase ++ [.instr (.shImm .slli AbiReg.t2 AbiReg.a0 3#6)] ++
      [.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.t2)])
    post (.load .ld AbiReg.a0 AbiReg.t1 0#12) hlinkLd
    (by rw [htw6, htw4, htw_cb]; omega) st6 hpc6
  have hshift : vi.toBitVec <<< 3 = BitVec.ofNat 64 (8 * vi.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, UInt64.toNat_toBitVec, Nat.shiftLeft_eq,
        show (2 ^ 3 : Nat) = 8 by decide, Nat.mul_comm]
  have ht1_5 : st5.getReg AbiReg.t1 = L.base64 (TieredArray.t0 a) := by
    change (stepReg st4 AbiReg.t2 _ _).getReg AbiReg.t1 = _
    rw [getReg_stepReg_ne st4 AbiReg.t2 AbiReg.t1 (by decide) _ _, ht1_4']
  have ht2_5 : st5.getReg AbiReg.t2 = BitVec.ofNat 64 (8 * vi.toNat) := by
    change (stepReg st4 AbiReg.t2 _ _).getReg AbiReg.t2 = _
    rw [getReg_stepReg_eq st4 AbiReg.t2 (by decide) _ _, ha0_4, hshift]
  have haddr6 : st6.getReg AbiReg.t1 + sextImm12 0#12 =
      L.base64 (TieredArray.t0 a) + BitVec.ofNat 64 (8 * vi.toNat) := by
    have hz : sextImm12 0#12 = 0#64 := rfl
    change (stepReg st5 AbiReg.t1 _ _).getReg AbiReg.t1 + sextImm12 0#12 = _
    rw [hz, BitVec.add_zero, getReg_stepReg_eq st5 AbiReg.t1 (by decide) _ _, ht1_5, ht2_5]
  have hal6 : isAligned (st6.getReg AbiReg.t1 + sextImm12 0#12) 8 = true := by
    rw [haddr6]; exact isAligned8_add_mul8 _ (L.h64Align _) _
  let st7 := stepReg st6 AbiReg.a0 (loadBytes st6.mem (st6.getReg AbiReg.t1 + sextImm12 0#12) 8) (st6.pc + 4#64)
  have hpres67 : PreservedRegs st6 st7 :=
    ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
     getReg_stepReg_ne _ _ _ (by decide) _ _,
     getReg_stepReg_ne _ _ _ (by decide) _ _⟩
  refine ⟨lm.totalSize cbase + 3, st7, ?_, ?_, ?_,
    hpres34.trans (hpres45.trans (hpres56.trans hpres67)), ?_⟩
  · change RV64.run env.rom (lm.totalSize cbase + (1 + (1 + 1))) st3 = _
    rw [run_add, hrun4]; dsimp only
    rw [run_add, run_one_cont _ _ st5 (by rw [hs5]; simp only [execInstr, evalShiftImm]; rfl)]; dsimp only
    rw [run_add, run_one_cont _ _ st6 (by rw [hs6]; rfl)]; dsimp only
    exact run_one_cont _ _ st7 (by rw [hs7]; simp only [execInstr, hal6, ↓reduceIte]; rfl)
  · change st6.pc + 4#64 = _
    rw [pc_add_4_ofNat st6.pc hpc6, htw6, htw4]
  · change (stepReg st6 AbiReg.a0 _ _).getReg AbiReg.a0 = _
    rw [getReg_stepReg_eq st6 AbiReg.a0 (by decide) _ _, haddr6]
    have hmem6 : st6.mem = st3.mem := by
      change st5.mem = _; change st4.mem = _; exact hmem4
    rw [hmem6]
    exact hwordsR3 vi.toNat hbound
  · change st6.mem = _; change st5.mem = _; change st4.mem = _; exact hmem4

private theorem ld64_sim_gen (lm : LinkModel) (env : CodeEnvGen lm) (hm : TabMapOk env.tab)
    {nlocals ntemps : Nat} (L : Layout env.tab nlocals ntemps)
    (m : _root_.L.Mem) (loc : _root_.L.Locals)
    (pre post : List AsmItem) (tmp : Nat) (a : ArrId) (i : Expr)
    (ha : (TieredArray.t0 a) ∈ env.tab.arrAt) (hiExpr : CoreExpr env.tab i)
    (htmp : tmp + maxTempsExpr i ≤ ntemps)
    (ihi : ∀ (pre post : List AsmItem) (tmp : Nat) (st : State),
      tmp + maxTempsExpr i ≤ ntemps →
      lm.linkSpec (pre ++ compileE env.tab nlocals tmp i ++ post) = .ok (env.code, env.labels) →
      4 * (lm.totalSize pre + lm.totalSize (compileE env.tab nlocals tmp i)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → st.getReg AbiReg.sp = L.sp →
      MemRel env.tab L st.mem m → FrameOk L st.mem nlocals loc →
      match evalE i ⟨m, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (compileE env.tab nlocals tmp i))) ∧
          st'.getReg AbiReg.a0 = v.toBitVec ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem)
    (hlink : lm.linkSpec (pre ++ compileE env.tab nlocals tmp (.ld64 a i) ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (compileE env.tab nlocals tmp (.ld64 a i))) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = L.sp)
    (hmemRel : MemRel env.tab L st.mem m) (hframeOk : FrameOk L st.mem nlocals loc) :
    match evalE (.ld64 a i) ⟨m, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (compileE env.tab nlocals tmp (.ld64 a i)))) ∧
        st'.getReg AbiReg.a0 = v.toBitVec ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem := by
  let ci := compileE env.tab nlocals tmp i
  let clen := loadMemOff .ld AbiReg.t0 AbiReg.gp AbiReg.t1 (env.tab.len64 (TieredArray.t0 a))
  let cbr := [Asm.bgeu AbiReg.a0 AbiReg.t0 errLabel]
  let cbase := loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base64 (TieredArray.t0 a))
  let cld := [Asm.slli AbiReg.t2 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2, Asm.ld AbiReg.a0 AbiReg.t1 0#12]
  have hce : compileE env.tab nlocals tmp (.ld64 a i) = ci ++ clen ++ cbr ++ cbase ++ cld := by
    dsimp only [ci, clen, cbr, cbase, cld, compileE]
  let brSz := lm.itemSize (.br .bgeu AbiReg.a0 AbiReg.t0 errLabel)
  have htw_ce : lm.totalSize (compileE env.tab nlocals tmp (.ld64 a i)) =
      lm.totalSize ci + lm.totalSize clen + brSz + lm.totalSize cbase + 3 := by
    rw [hce]; simp only [lm.totalSize_append]
    have h1 : lm.totalSize cbr = brSz := by simp [cbr, Asm.bgeu, brSz]
    have h2 : lm.totalSize cld = 3 := by simp [cld, Asm.slli, Asm.add, Asm.ld, lm.itemSize_instr]
    omega
  have h64_ld64 : 4 * (lm.totalSize pre + lm.totalSize ci + lm.totalSize clen + brSz + lm.totalSize cbase + 3) < 2 ^ 64 := by
    rw [htw_ce] at h64; omega
  have htw_ci : lm.totalSize (compileE env.tab nlocals tmp i) = lm.totalSize ci := rfl
  have hlistI : pre ++ ci ++ (clen ++ cbr ++ cbase ++ cld ++ post) =
      pre ++ (ci ++ clen ++ cbr ++ cbase ++ cld) ++ post := by
    simp only [List.append_assoc]
  have hlinkI : lm.linkSpec (pre ++ ci ++ (clen ++ cbr ++ cbase ++ cld ++ post)) = .ok (env.code, env.labels) := by
    rw [hlistI, ← hce]; exact hlink
  have ri := ihi pre (clen ++ cbr ++ cbase ++ cld ++ post) tmp st htmp hlinkI
    (by rw [htw_ci]; rw [htw_ce] at h64; omega) hpc hgp hsp hmemRel hframeOk
  rcases hiExpr.evalE_pure ⟨m, loc⟩ with ⟨vi, hvi⟩ | hvi
  · simp only [hvi] at ri
    obtain ⟨ki, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ri
    have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.gp.trans hgp
    have hmemRel1 := memRel_of_eqOutside_temp hm (by omega) heq1 hmemRel
    rcases hmemRel1.2.1 (TieredArray.t0 a) ha with ⟨_, hlt64, hlenR, hbaseR, hwordsR⟩
    have htw_p1 : lm.totalSize (pre ++ ci) = lm.totalSize pre + lm.totalSize ci := (lm.totalSize_append) _ _
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ ci)) := by
      rw [htw_p1, ← htw_ci]; exact hpc1
    have hlistLen : (pre ++ ci) ++ clen ++ (cbr ++ cbase ++ cld ++ post) =
        pre ++ (ci ++ clen ++ cbr ++ cbase ++ cld) ++ post := by
      simp only [List.append_assoc]
    have hlinkLen : lm.linkSpec ((pre ++ ci) ++ clen ++ (cbr ++ cbase ++ cld ++ post)) =
        .ok (env.code, env.labels) := by
      rw [hlistLen, ← hce]; exact hlink
    have halLen : isAligned (st1.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.len64 (TieredArray.t0 a))) 8 = true := by
      rw [hgp1, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    have htw_clen : lm.totalSize (loadMemOff .ld AbiReg.t0 AbiReg.gp AbiReg.t1 (env.tab.len64 (TieredArray.t0 a))) = lm.totalSize clen := rfl
    obtain ⟨st2, hrun2, hoth2, ht0_2, hmem2, hpc2⟩ :=
      loadMemOff_ld_correct_lm lm env.hrom (pre ++ ci) (cbr ++ cbase ++ cld ++ post)
        AbiReg.t0 AbiReg.gp AbiReg.t1 (by decide) (by decide) (by decide)
        (env.tab.len64 (TieredArray.t0 a)) hlinkLen (by rw [htw_clen, htw_p1]; rw [htw_ce] at h64; omega) st1 hpc1' halLen
    have hpres12 : PreservedRegs st1 st2 :=
      ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
       hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide)⟩
    have hgp2 : st2.getReg AbiReg.gp = L.T := hpres12.gp.trans hgp1
    have ha0_2 : st2.getReg AbiReg.a0 = vi.toBitVec := by
      rw [hoth2 AbiReg.a0 (by decide) (by decide), ha0_1]
    have ht0_2' : st2.getReg AbiReg.t0 = BitVec.ofNat 64 (m.arr64 (TieredArray.t0 a)).size := by
      rw [ht0_2, hgp1, hlenR]
    have htw2 : lm.totalSize (pre ++ ci ++ clen) = lm.totalSize pre + lm.totalSize ci + lm.totalSize clen := by
      rw [(lm.totalSize_append), htw_p1]
    have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ ci ++ clen)) := by
      rw [htw2, ← htw_p1, ← htw_clen]; exact hpc2
    have hlistBr : (pre ++ ci ++ clen) ++ [Asm.bgeu AbiReg.a0 AbiReg.t0 errLabel] ++ (cbase ++ cld ++ post) =
        pre ++ (ci ++ clen ++ cbr ++ cbase ++ cld) ++ post := by
      simp only [cbr, List.append_assoc]
    have hlinkBr : lm.linkSpec ((pre ++ ci ++ clen) ++ [Asm.bgeu AbiReg.a0 AbiReg.t0 errLabel] ++
        (cbase ++ cld ++ post)) = .ok (env.code, env.labels) := by
      rw [hlistBr, ← hce]; exact hlink
    obtain ⟨tgt, kbr, st3, _, hlook, hrunBr, hpc3_raw, hreg3, hmem3⟩ :=
      step_item_br_lm lm env.hrom (pre ++ ci ++ clen) (cbase ++ cld ++ post) .bgeu AbiReg.a0 AbiReg.t0 errLabel
        hlinkBr (by decide) (by rw [htw2]; rw [htw_ce] at h64; simp only [Asm.bgeu, brSz] at *; omega) st2 hpc2'
    have htgt : tgt = env.errTarget := by rw [env.herrLbl] at hlook; cases hlook; rfl
    subst htgt
    by_cases hbound : vi.toNat < (m.arr64 (TieredArray.t0 a)).size
    · have heval : evalE (.ld64 a i) ⟨m, loc⟩ = .ok ((m.arr64 (TieredArray.t0 a))[vi.toNat], ⟨m, loc⟩) := by
        change (evalE i >>= fun idx => _root_.L.ld64 (TieredArray.t0 a) idx) ⟨m, loc⟩ = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]
        rw [hvi]
        dsimp only [_root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
          Pure.pure, StateT.pure, Except.pure, Except.bind]
        simp only [hbound]; rfl
      rw [heval]
      have hbrF : evalBranch .bgeu (st2.getReg AbiReg.a0) (st2.getReg AbiReg.t0) = false := by
        rw [ha0_2, ht0_2', evalBranch, BitVec.ult]
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64, UInt64.toNat_toBitVec,
          decide_eq_true hbound, Bool.not_true]
      have hpres23 : PreservedRegs st2 st3 := PreservedRegs.of_regEqExceptT6 hreg3
      rw [hbrF] at hpc3_raw
      simp only [Bool.false_eq_true, ↓reduceIte] at hpc3_raw
      have htw3 : lm.totalSize (pre ++ ci ++ clen ++ cbr) = lm.totalSize pre + lm.totalSize ci + lm.totalSize clen + brSz := by
        rw [lm.totalSize_append, htw2]; simp [cbr, Asm.bgeu, brSz]
      have hpc3 : st3.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ ci ++ clen ++ cbr)) := by
        rw [hpc3_raw, htw3, htw2]
      have hgp3 : st3.getReg AbiReg.gp = L.T := (hreg3.getReg_eq (by decide)).symm.trans hgp2
      have ha0_3 : st3.getReg AbiReg.a0 = vi.toBitVec := (hreg3.getReg_eq (by decide)).symm.trans ha0_2
      have hlistTail : (pre ++ ci ++ clen ++ cbr) ++ (cbase ++ cld) ++ post =
          pre ++ (ci ++ clen ++ cbr ++ cbase ++ cld) ++ post := by
        simp only [List.append_assoc]
      have hlinkTail : lm.linkSpec ((pre ++ ci ++ clen ++ cbr) ++ (cbase ++ cld) ++ post) =
          .ok (env.code, env.labels) := by
        rw [hlistTail, ← hce]; exact hlink
      have hmem3' : st3.mem = st1.mem := hmem3.trans hmem2
      have htw_cbase : lm.totalSize (loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base64 (TieredArray.t0 a))) = lm.totalSize cbase := rfl
      obtain ⟨kt, st7, hrunT, hpc7, ha0_7, hpres37, hmem7⟩ :=
        ld64_ok_tail_gen lm env L m (pre ++ ci ++ clen ++ cbr) post a vi st3 hlinkTail
          (by rw [htw3, htw_cbase]; omega) hpc3 hgp3 ha0_3 (by rw [hmem3']; exact hbaseR)
          hbound (fun j hj => by rw [hmem3']; exact hwordsR j hj)
      refine ⟨ki + (lm.totalSize clen + (kbr + kt)), st7, ?_, ?_, ha0_7,
        hpres1.trans (hpres12.trans (hpres23.trans hpres37)), ?_⟩
      · rw [run_add, hrun1]; dsimp only
        rw [run_add, hrun2]; dsimp only
        rw [run_add, hrunBr]; dsimp only
        exact hrunT
      · rw [hpc7, htw3, htw_cbase, htw_ce]
        congr 2; omega
      · change MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st7.mem
        rw [hmem7, hmem3']; exact heq1
    · have heval : evalE (.ld64 a i) ⟨m, loc⟩ = .error .oob := by
        change (evalE i >>= fun idx => _root_.L.ld64 (TieredArray.t0 a) idx) ⟨m, loc⟩ = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]
        rw [hvi]
        dsimp only [_root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
          Pure.pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, Except.pure]
        simp [hbound]; rfl
      rw [heval]
      have hbrT : evalBranch .bgeu (st2.getReg AbiReg.a0) (st2.getReg AbiReg.t0) = true := by
        rw [ha0_2, ht0_2', evalBranch, BitVec.ult]
        have h1 : (BitVec.ofNat 64 (m.arr64 (TieredArray.t0 a)).size).toNat =
            (m.arr64 (TieredArray.t0 a)).size := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
        simp [UInt64.toNat_toBitVec, h1, hbound]
      have hpres23 : PreservedRegs st2 st3 := PreservedRegs.of_regEqExceptT6 hreg3
      rw [hbrT] at hpc3_raw; simp only [↓reduceIte] at hpc3_raw
      refine ⟨ki + (lm.totalSize clen + kbr), st3, ?_, hpc3_raw, hpres1.trans (hpres12.trans hpres23), ?_⟩
      · rw [run_add, hrun1]; dsimp only
        rw [run_add, hrun2]; dsimp only
        exact hrunBr
      · rw [hmem3, hmem2]; exact heq1
  · have heval : evalE (.ld64 a i) ⟨m, loc⟩ = .error .oob := by
      simp [evalE, Bind.bind, StateT.bind, Except.bind, hvi]
    rw [heval]; simp only [hvi] at ri; exact ri

theorem evalExpr_sim_gen (lm : LinkModel) (env : CodeEnvGen lm) (hm : TabMapOk env.tab)
    {nlocals ntemps : Nat} (L : Layout env.tab nlocals ntemps)
    (m : _root_.L.Mem) (loc : _root_.L.Locals)
    (pre post : List AsmItem) (tmp : Nat) (e : Expr)
    (he : CoreExpr env.tab e) (hvars : exprVarsLt nlocals e)
    (htmp : tmp + maxTempsExpr e ≤ ntemps)
    (hlink : lm.linkSpec (pre ++ compileE env.tab nlocals tmp e ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (compileE env.tab nlocals tmp e)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = L.sp)
    (hmemRel : MemRel env.tab L st.mem m) (hframeOk : FrameOk L st.mem nlocals loc) :
    match evalE e ⟨m, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (compileE env.tab nlocals tmp e))) ∧
        st'.getReg AbiReg.a0 = v.toBitVec ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem := by
  induction he generalizing pre post tmp st with
  | const w =>
    have hce : compileE env.tab nlocals tmp (.const w) = li AbiReg.a0 (BitVec.ofNat 64 w.toNat) := rfl
    rw [hce] at hlink h64 ⊢
    obtain ⟨st', hrun, hoth, ha0, hmem, hpc'⟩ :=
      li_correct_lm lm env.hrom pre post AbiReg.a0 (by decide) (BitVec.ofNat 64 w.toNat) hlink h64 st hpc
    have hw : BitVec.ofNat 64 w.toNat = w.toBitVec := by
      rw [← UInt64.toBitVec_ofNat' w.toNat, UInt64.ofNat_toNat]
    refine ⟨_, st', hrun, hpc', ha0.trans hw,
      ⟨hoth _ (by decide), hoth _ (by decide), hoth _ (by decide), hoth _ (by decide)⟩,
      hmem ▸ MemEqOutside.refl _ _⟩
  | var x =>
    have hx : x < nlocals := hvars
    have hce : compileE env.tab nlocals tmp (.var x) = loadMemOff .ld AbiReg.a0 AbiReg.sp AbiReg.t0 (slotOff x) := rfl
    rw [hce] at hlink h64 ⊢
    have hal : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff x)) 8 = true := by
      rw [hsp, slotOff_ofInt]; exact isAligned8_add_mul8 L.sp L.hSpAlign (1 + x)
    obtain ⟨st', hrun, hoth, ha0, hmem, hpc'⟩ :=
      loadMemOff_ld_correct_lm lm env.hrom pre post AbiReg.a0 AbiReg.sp AbiReg.t0
        (by decide) (by decide) (by decide) (slotOff x) hlink h64 st hpc hal
    refine ⟨_, st', hrun, hpc', ?_,
      ⟨hoth _ (by decide) (by decide), hoth _ (by decide) (by decide),
       hoth _ (by decide) (by decide), hoth _ (by decide) (by decide)⟩,
      hmem ▸ MemEqOutside.refl _ _⟩
    rw [ha0, hsp, hframeOk x hx]
  | len8 a ha =>
    have hce : compileE env.tab nlocals tmp (.len8 a) =
        loadMemOff .ld AbiReg.a0 AbiReg.gp AbiReg.t0 (env.tab.len8 a) := rfl
    rw [hce] at hlink h64 ⊢
    have hal : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.len8 a)) 8 = true := by
      rw [hgp, Tab.len8_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨st', hrun, hoth, ha0, hmem, hpc'⟩ :=
      loadMemOff_ld_correct_lm lm env.hrom pre post AbiReg.a0 AbiReg.gp AbiReg.t0
        (by decide) (by decide) (by decide) (env.tab.len8 a) hlink h64 st hpc hal
    rcases hmemRel.1 a ha with ⟨_, _, hlenR, _, _⟩
    refine ⟨_, st', hrun, hpc', ?_,
      ⟨hoth _ (by decide) (by decide), hoth _ (by decide) (by decide),
       hoth _ (by decide) (by decide), hoth _ (by decide) (by decide)⟩,
      hmem ▸ MemEqOutside.refl _ _⟩
    rw [ha0, hgp, hlenR]; simp [Mem.len8, UInt64.toBitVec_ofNat']
  | len64 a ha =>
    have hce : compileE env.tab nlocals tmp (.len64 a) =
        loadMemOff .ld AbiReg.a0 AbiReg.gp AbiReg.t0 (env.tab.len64 (TieredArray.t0 a)) := rfl
    rw [hce] at hlink h64 ⊢
    have hal : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.len64 (TieredArray.t0 a))) 8 = true := by
      rw [hgp, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨st', hrun, hoth, ha0, hmem, hpc'⟩ :=
      loadMemOff_ld_correct_lm lm env.hrom pre post AbiReg.a0 AbiReg.gp AbiReg.t0
        (by decide) (by decide) (by decide) (env.tab.len64 (TieredArray.t0 a)) hlink h64 st hpc hal
    rcases hmemRel.2.1 (TieredArray.t0 a) ha with ⟨_, _, hlenR, _, _⟩
    refine ⟨_, st', hrun, hpc', ?_,
      ⟨hoth _ (by decide) (by decide), hoth _ (by decide) (by decide),
       hoth _ (by decide) (by decide), hoth _ (by decide) (by decide)⟩,
      hmem ▸ MemEqOutside.refl _ _⟩
    rw [ha0, hgp, hlenR]; simp [Mem.len64, UInt64.toBitVec_ofNat']
  | glob g hg =>
    have hce : compileE env.tab nlocals tmp (.glob g) =
        loadMemOff .ld AbiReg.a0 AbiReg.gp AbiReg.t0 (env.tab.globOff g) := rfl
    rw [hce] at hlink h64 ⊢
    have hal : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.globOff g)) 8 = true := by
      rw [hgp, Tab.globOff_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨st', hrun, hoth, ha0, hmem, hpc'⟩ :=
      loadMemOff_ld_correct_lm lm env.hrom pre post AbiReg.a0 AbiReg.gp AbiReg.t0
        (by decide) (by decide) (by decide) (env.tab.globOff g) hlink h64 st hpc hal
    refine ⟨_, st', hrun, hpc', ?_,
      ⟨hoth _ (by decide) (by decide), hoth _ (by decide) (by decide),
       hoth _ (by decide) (by decide), hoth _ (by decide) (by decide)⟩,
      hmem ▸ MemEqOutside.refl _ _⟩
    rw [ha0, hgp, hmemRel.2.2 g hg]
  | bin op a b haExpr hbExpr iha ihb =>
    have hmt : maxTempsExpr (.bin op a b) = max (maxTempsExpr a) (1 + maxTempsExpr b) := rfl
    have hcomm : ∀ (w x : UInt64),
        (match op with | .add | .and | .or | .xor | .mul | .mulhi => op.eval w x = op.eval x w | _ => True) := by
      intro w x; cases op
      · exact UInt64.add_comm w x
      · trivial
      · exact UInt64.mul_comm w x
      · apply UInt64.toBitVec_inj.mp; simpa [BinOp.eval, UInt64.toBitVec_and] using BitVec.and_comm w.toBitVec x.toBitVec
      · apply UInt64.toBitVec_inj.mp; simpa [BinOp.eval, UInt64.toBitVec_or] using BitVec.or_comm w.toBitVec x.toBitVec
      · apply UInt64.toBitVec_inj.mp; simpa [BinOp.eval, UInt64.toBitVec_xor] using BitVec.xor_comm w.toBitVec x.toBitVec
      · trivial
      · trivial
      · dsimp only [BinOp.eval]; rw [Nat.mul_comm]
    cases hb_c : b.constVal? with
    | some w =>
      have hbeq : b = .const w := expr_constVal_eq_some hb_c
      subst hbeq
      have hce : compileE env.tab nlocals tmp (.bin op a (.const w)) =
          compileE env.tab nlocals tmp a ++ emitBinConstRhs op w := by
        simp [compileE, hb_c]
      have htw_ce : lm.totalSize (compileE env.tab nlocals tmp (.bin op a (.const w))) =
          lm.totalSize (compileE env.tab nlocals tmp a) + lm.totalSize (emitBinConstRhs op w) := by
        rw [hce, lm.totalSize_append]
      have ra := iha pre (emitBinConstRhs op w ++ post) tmp hvars.1 (by omega)
        (by rw [show pre ++ compileE env.tab nlocals tmp a ++ (emitBinConstRhs op w ++ post) =
            pre ++ compileE env.tab nlocals tmp (.bin op a (.const w)) ++ post by rw [hce]; simp [List.append_assoc]]; exact hlink)
        (by rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
      rcases haExpr.evalE_pure ⟨m, loc⟩ with ⟨va, hva⟩ | hva
      · simp only [hva] at ra
        obtain ⟨ka, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ra
        have heval : evalE (.bin op a (.const w)) ⟨m, loc⟩ = .ok (op.eval va w, ⟨m, loc⟩) := by
          simp [evalE, Bind.bind, StateT.bind, Except.bind, hva, Pure.pure, StateT.pure, Except.pure]
        rw [heval]
        obtain ⟨kb, st2, hrun2, hpc2, ha0_2, hpres2, hmem2⟩ :=
          emitBinConstRhs_sim_lm lm env (pre ++ compileE env.tab nlocals tmp a) post op w va st1
            (by simpa only [hce, List.append_assoc] using hlink)
            (by rw [lm.totalSize_append, Nat.add_assoc, ← htw_ce]; exact h64)
            (by rw [lm.totalSize_append]; exact hpc1) ha0_1
        exact ⟨ka + kb, st2, by rw [run_add, hrun1]; exact hrun2,
          by rw [hpc2, lm.totalSize_append, Nat.add_assoc, ← htw_ce],
          ha0_2, hpres1.trans hpres2, hmem2 ▸ heq1⟩
      · simp only [hva] at ra
        rw [show evalE (.bin op a (.const w)) ⟨m, loc⟩ = .error .oob by
          simp [evalE, Bind.bind, StateT.bind, Except.bind, hva]]
        exact ra
    | none =>
      cases ha_c : a.constVal? with
      | some w =>
        have haeq : a = .const w := expr_constVal_eq_some ha_c
        subst haeq
        have runLhsTail : ∀ (tail : List AsmItem)
            (hce : compileE env.tab nlocals tmp (.bin op (.const w) b) = compileE env.tab nlocals tmp b ++ tail)
            (htail : ∀ (vb : UInt64) (st1 : State),
              lm.linkSpec ((pre ++ compileE env.tab nlocals tmp b) ++ tail ++ post) = .ok (env.code, env.labels) →
              4 * (lm.totalSize (pre ++ compileE env.tab nlocals tmp b) + lm.totalSize tail) < 2 ^ 64 →
              st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ compileE env.tab nlocals tmp b)) →
              st1.getReg AbiReg.a0 = vb.toBitVec →
              ∃ k st2, RV64.run env.rom k st1 = .cont st2 ∧
                st2.pc = BitVec.ofNat 64 (4 * (lm.totalSize (pre ++ compileE env.tab nlocals tmp b) + lm.totalSize tail)) ∧
                st2.getReg AbiReg.a0 = (op.eval w vb).toBitVec ∧ PreservedRegs st1 st2 ∧ st2.mem = st1.mem),
            match evalE (.bin op (.const w) b) ⟨m, loc⟩ with
            | .ok (v, _) =>
              ∃ k st', RV64.run env.rom k st = .cont st' ∧
                st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (compileE env.tab nlocals tmp (.bin op (.const w) b)))) ∧
                st'.getReg AbiReg.a0 = v.toBitVec ∧ PreservedRegs st st' ∧
                MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem
            | .error _ =>
              ∃ k st', RV64.run env.rom k st = .cont st' ∧
                st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧ PreservedRegs st st' ∧
                MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem := by
          intro tail hce htail
          have htw_ce : lm.totalSize (compileE env.tab nlocals tmp (.bin op (.const w) b)) =
              lm.totalSize (compileE env.tab nlocals tmp b) + lm.totalSize tail := by rw [hce, lm.totalSize_append]
          have rb := ihb pre (tail ++ post) tmp hvars.2 (by omega)
            (by simpa only [hce, List.append_assoc] using hlink)
            (by rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
          rcases hbExpr.evalE_pure ⟨m, loc⟩ with ⟨vb, hvb⟩ | hvb
          · simp only [hvb] at rb
            obtain ⟨kb, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := rb
            have heval : evalE (.bin op (.const w) b) ⟨m, loc⟩ = .ok (op.eval w vb, ⟨m, loc⟩) := by
              simp [evalE, Bind.bind, StateT.bind, Except.bind, hvb, Pure.pure, StateT.pure, Except.pure]
            rw [heval]
            obtain ⟨kt, st2, hrun2, hpc2, ha0_2, hpres2, hmem2⟩ :=
              htail vb st1 (by simpa only [hce, List.append_assoc] using hlink)
                (by rw [lm.totalSize_append, Nat.add_assoc, ← htw_ce]; exact h64)
                (by rw [lm.totalSize_append]; exact hpc1) ha0_1
            exact ⟨kb + kt, st2, by rw [run_add, hrun1]; exact hrun2,
              by rw [hpc2, lm.totalSize_append, Nat.add_assoc, ← htw_ce],
              ha0_2, hpres1.trans hpres2, hmem2 ▸ heq1⟩
          · simp only [hvb] at rb
            rw [show evalE (.bin op (.const w) b) ⟨m, loc⟩ = .error .oob by
              simp [evalE, Bind.bind, StateT.bind, Except.bind, hvb, Pure.pure, StateT.pure, Except.pure]]
            exact rb
        have liBinLhs : ∀ (op' : BinOp) (heq : op = op') (vb : UInt64) (st1 : State) (p' : List AsmItem),
            lm.linkSpec (p' ++ (li AbiReg.t0 w.toBitVec ++ [emitBinOp op' AbiReg.a0 AbiReg.t0 AbiReg.a0]) ++ post) = .ok (env.code, env.labels) →
            4 * (lm.totalSize p' + lm.totalSize (li AbiReg.t0 w.toBitVec ++ [emitBinOp op' AbiReg.a0 AbiReg.t0 AbiReg.a0])) < 2 ^ 64 →
            st1.pc = BitVec.ofNat 64 (4 * lm.totalSize p') →
            st1.getReg AbiReg.a0 = vb.toBitVec →
            ∃ k st2, RV64.run env.rom k st1 = .cont st2 ∧
              st2.pc = BitVec.ofNat 64 (4 * (lm.totalSize p' + lm.totalSize (li AbiReg.t0 w.toBitVec ++ [emitBinOp op' AbiReg.a0 AbiReg.t0 AbiReg.a0]))) ∧
              st2.getReg AbiReg.a0 = (op'.eval w vb).toBitVec ∧ PreservedRegs st1 st2 ∧ st2.mem = st1.mem := by
          intro op' _ vb st1 p' hl' h64' hpc1 ha0_1
          have htw_t : lm.totalSize (li AbiReg.t0 w.toBitVec ++ [emitBinOp op' AbiReg.a0 AbiReg.t0 AbiReg.a0]) =
              lm.totalSize (li AbiReg.t0 w.toBitVec) + 1 := by
            rw [lm.totalSize_append]; cases op' <;> simp [emitBinOp, Asm.add, Asm.sub, Asm.and, Asm.or,
              Asm.xor, Asm.sll, Asm.srl, Asm.mul, Asm.mulhu, lm.itemSize_instr]
          obtain ⟨st2, hrun2, hoth2, ht0_2, hmem2, hpc2⟩ :=
            li_correct_lm lm env.hrom p' ([emitBinOp op' AbiReg.a0 AbiReg.t0 AbiReg.a0] ++ post)
              AbiReg.t0 (by decide) w.toBitVec (by simpa [List.append_assoc] using hl')
              (by rw [htw_t] at h64'; omega) st1 hpc1
          obtain ⟨st3, hrun3, hpc3, ha0_3, hoth3, hmem3⟩ :=
            emitBinOp_step_lm lm env (p' ++ li AbiReg.t0 w.toBitVec) post op' AbiReg.a0 AbiReg.t0 AbiReg.a0
              (by decide) w vb st2 (by simpa [List.append_assoc] using hl')
              (by rw [lm.totalSize_append]; rw [htw_t] at h64'; omega)
              (by rw [lm.totalSize_append]; exact hpc2) ht0_2 ((hoth2 _ (by decide)).trans ha0_1)
          refine ⟨_, st3, by rw [run_add, hrun2]; exact hrun3,
            by rw [hpc3, lm.totalSize_append, htw_t, Nat.add_assoc], ha0_3, ?_, hmem3.trans hmem2⟩
          exact ⟨(hoth3 _ (by decide)).trans (hoth2 _ (by decide)),
                 (hoth3 _ (by decide)).trans (hoth2 _ (by decide)),
                 (hoth3 _ (by decide)).trans (hoth2 _ (by decide)),
                 (hoth3 _ (by decide)).trans (hoth2 _ (by decide))⟩
        cases op with
        | add | and | or | xor | mul | mulhi =>
          refine runLhsTail (emitBinConstRhs _ w) (by rw [compileE, hb_c]; rfl) fun vb st1 hl' h64' hpc1 ha0_1 => by
            obtain ⟨k, st2, hrun, hpc2, ha0_2, hp, hm'⟩ := emitBinConstRhs_sim_lm lm env _ post _ w vb st1 hl' h64' hpc1 ha0_1
            exact ⟨k, st2, hrun, hpc2, ha0_2.trans (by have hc' := hcomm w vb; dsimp only at hc'; rw [hc']), hp, hm'⟩
        | sub =>
          by_cases hw0 : w = 0
          · subst hw0
            refine runLhsTail [Asm.sub AbiReg.a0 AbiReg.zero AbiReg.a0]
              (by simp [compileE, hb_c, ha_c]) fun vb st1 hl' h64' hpc1 ha0_1 => ?_
            have htw1 : lm.totalSize [Asm.sub AbiReg.a0 AbiReg.zero AbiReg.a0] = 1 := by simp [Asm.sub, lm.itemSize_instr]
            obtain ⟨st2, hrun, hpc2, ha0_2, hoth, hm'⟩ :=
              emitBinOp_step_lm lm env _ post .sub AbiReg.a0 AbiReg.zero AbiReg.a0 (by decide) 0 vb st1
                (by simpa [emitBinOp] using hl') (by rw [htw1] at h64'; exact h64') hpc1 rfl ha0_1
            exact ⟨1, st2, hrun, by rw [htw1]; exact hpc2, ha0_2,
              ⟨hoth _ (by decide), hoth _ (by decide), hoth _ (by decide), hoth _ (by decide)⟩, hm'⟩
          · refine runLhsTail (li AbiReg.t0 w.toBitVec ++ [Asm.sub AbiReg.a0 AbiReg.t0 AbiReg.a0])
              (by simp [compileE, hb_c, ha_c, hw0, List.append_assoc]) fun vb st1 hl' h64' hpc1 ha0_1 =>
                liBinLhs .sub rfl vb st1 _ (by simpa [emitBinOp] using hl') (by simpa [emitBinOp] using h64') hpc1 ha0_1
        | shl =>
          refine runLhsTail (li AbiReg.t0 w.toBitVec ++ [Asm.sll AbiReg.a0 AbiReg.t0 AbiReg.a0])
            (by simp [compileE, hb_c, ha_c, List.append_assoc]) fun vb st1 hl' h64' hpc1 ha0_1 =>
              liBinLhs .shl rfl vb st1 _ (by simpa [emitBinOp] using hl') (by simpa [emitBinOp] using h64') hpc1 ha0_1
        | shr =>
          refine runLhsTail (li AbiReg.t0 w.toBitVec ++ [Asm.srl AbiReg.a0 AbiReg.t0 AbiReg.a0])
            (by simp [compileE, hb_c, ha_c, List.append_assoc]) fun vb st1 hl' h64' hpc1 ha0_1 =>
              liBinLhs .shr rfl vb st1 _ (by simpa [emitBinOp] using hl') (by simpa [emitBinOp] using h64') hpc1 ha0_1
      | none =>
        cases hsb : emitSimpleExpr env.tab AbiReg.t0 AbiReg.t1 b with
        | some cb =>
          have hce : compileE env.tab nlocals tmp (.bin op a b) =
              compileE env.tab nlocals tmp a ++ cb ++ [emitBinOp op AbiReg.a0 AbiReg.a0 AbiReg.t0] := by
            simp [compileE, hb_c, ha_c, hsb]
          have htw_op : lm.totalSize [emitBinOp op AbiReg.a0 AbiReg.a0 AbiReg.t0] = 1 := by
            cases op <;> simp [emitBinOp, Asm.add, Asm.sub, Asm.and, Asm.or,
              Asm.xor, Asm.sll, Asm.srl, Asm.mul, Asm.mulhu, lm.itemSize_instr]
          have htw_ce : lm.totalSize (compileE env.tab nlocals tmp (.bin op a b)) =
              lm.totalSize (compileE env.tab nlocals tmp a) + lm.totalSize cb + 1 := by
            rw [hce, lm.totalSize_append, lm.totalSize_append, htw_op]
          have ra := iha pre (cb ++ [emitBinOp op AbiReg.a0 AbiReg.a0 AbiReg.t0] ++ post) tmp hvars.1 (by omega)
            (by simpa only [hce, List.append_assoc] using hlink)
            (by rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
          rcases haExpr.evalE_pure ⟨m, loc⟩ with ⟨va, hva⟩ | hva
          · simp only [hva] at ra
            obtain ⟨ka, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ra
            have hmr1 := memRel_of_eqOutside_temp hm (by omega : tmp ≤ ntemps) heq1 hmemRel
            have hfr1 := frameOk_of_eqOutside_temp (by omega : tmp ≤ ntemps) heq1 hframeOk
            obtain ⟨vb, kb, st2, hvb, hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
              emitSimpleExpr_sim_gen lm env L m loc (pre ++ compileE env.tab nlocals tmp a)
                ([emitBinOp op AbiReg.a0 AbiReg.a0 AbiReg.t0] ++ post) AbiReg.t0 AbiReg.t1
                (by decide) (by decide) (by decide) (by decide) (by decide) b cb hsb hbExpr hvars.2
                (by simpa only [hce, List.append_assoc] using hlink)
                (by rw [lm.totalSize_append]; rw [htw_ce] at h64; omega)
                st1 (show st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ _)) from by rw [lm.totalSize_append]; exact hpc1)
                (hpres1.gp.trans hgp) (hpres1.sp.trans hsp) hmr1 hfr1
            have heval : evalE (.bin op a b) ⟨m, loc⟩ = .ok (op.eval va vb, ⟨m, loc⟩) := by
              simp [evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
            rw [heval]
            have hpres12 : PreservedRegs st1 st2 :=
              ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
               hoth2 _ (by decide) (by decide),
               hoth2 _ (by decide) (by decide)⟩
            obtain ⟨st3, hrun3, hpc3, ha0_3, hoth3, hmem3⟩ :=
              emitBinOp_step_lm lm env (pre ++ compileE env.tab nlocals tmp a ++ cb) post op
                AbiReg.a0 AbiReg.a0 AbiReg.t0 (by decide) va vb st2
                (by simpa only [hce, List.append_assoc] using hlink)
                (by rw [lm.totalSize_append, lm.totalSize_append]; rw [htw_ce] at h64; omega)
                (by rw [lm.totalSize_append, lm.totalSize_append] at *; simpa [Nat.add_assoc] using hpc2)
                ((hoth2 _ (by decide) (by decide)).trans ha0_1) ht0_2
            refine ⟨ka + kb + 1, st3,
              by rw [Nat.add_assoc, run_add, hrun1]; dsimp only; rw [run_add, hrun2]; exact hrun3,
              by rw [hpc3, lm.totalSize_append, lm.totalSize_append, htw_ce]; congr 2; omega,
              ha0_3, hpres1.trans (hpres12.trans ⟨hoth3 _ (by decide), hoth3 _ (by decide),
                hoth3 _ (by decide), hoth3 _ (by decide)⟩),
              (hmem3.trans hmem2) ▸ heq1⟩
          · simp only [hva] at ra
            rw [show evalE (.bin op a b) ⟨m, loc⟩ = .error .oob by simp [evalE, Bind.bind, StateT.bind, Except.bind, hva]]
            exact ra
        | none =>
          cases hsa : emitSimpleExpr env.tab AbiReg.t0 AbiReg.t1 a with
          | some ca =>
            have hce : compileE env.tab nlocals tmp (.bin op a b) =
                compileE env.tab nlocals tmp b ++ ca ++ [emitBinOp op AbiReg.a0 AbiReg.t0 AbiReg.a0] := by
              simp [compileE, hb_c, ha_c, hsb, hsa]
            have htw_op : lm.totalSize [emitBinOp op AbiReg.a0 AbiReg.t0 AbiReg.a0] = 1 := by
              cases op <;> simp [emitBinOp, Asm.add, Asm.sub, Asm.and, Asm.or,
                Asm.xor, Asm.sll, Asm.srl, Asm.mul, Asm.mulhu, lm.itemSize_instr]
            have htw_ce : lm.totalSize (compileE env.tab nlocals tmp (.bin op a b)) =
                lm.totalSize (compileE env.tab nlocals tmp b) + lm.totalSize ca + 1 := by
              rw [hce, lm.totalSize_append, lm.totalSize_append, htw_op]
            have rb := ihb pre (ca ++ [emitBinOp op AbiReg.a0 AbiReg.t0 AbiReg.a0] ++ post) tmp hvars.2 (by omega)
              (by simpa only [hce, List.append_assoc] using hlink)
              (by rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
            have haOk : ∃ va, evalE a ⟨m, loc⟩ = .ok (va, ⟨m, loc⟩) := by
              cases a <;> simp [emitSimpleExpr] at hsa
              · exact ⟨_, rfl⟩
              · exact ⟨_, rfl⟩
              · exact ⟨_, rfl⟩
              · exact ⟨_, rfl⟩
              · exact ⟨_, rfl⟩
            rcases haOk with ⟨va0, hva0⟩
            rcases hbExpr.evalE_pure ⟨m, loc⟩ with ⟨vb, hvb⟩ | hvb
            · simp only [hvb] at rb
              obtain ⟨kb, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := rb
              have hmr1 := memRel_of_eqOutside_temp hm (by omega : tmp ≤ ntemps) heq1 hmemRel
              have hfr1 := frameOk_of_eqOutside_temp (by omega : tmp ≤ ntemps) heq1 hframeOk
              obtain ⟨va, ka, st2, hva, hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
                emitSimpleExpr_sim_gen lm env L m loc (pre ++ compileE env.tab nlocals tmp b)
                  ([emitBinOp op AbiReg.a0 AbiReg.t0 AbiReg.a0] ++ post) AbiReg.t0 AbiReg.t1
                  (by decide) (by decide) (by decide) (by decide) (by decide) a ca hsa haExpr hvars.1
                  (by simpa only [hce, List.append_assoc] using hlink)
                  (by rw [lm.totalSize_append]; rw [htw_ce] at h64; omega)
                  st1 (show st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ _)) from by rw [lm.totalSize_append]; exact hpc1)
                  (hpres1.gp.trans hgp) (hpres1.sp.trans hsp) hmr1 hfr1
              have heval : evalE (.bin op a b) ⟨m, loc⟩ = .ok (op.eval va vb, ⟨m, loc⟩) := by
                simp [evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
              rw [heval]
              have hpres12 : PreservedRegs st1 st2 :=
                ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
                 hoth2 _ (by decide) (by decide),
                 hoth2 _ (by decide) (by decide)⟩
              obtain ⟨st3, hrun3, hpc3, ha0_3, hoth3, hmem3⟩ :=
                emitBinOp_step_lm lm env (pre ++ compileE env.tab nlocals tmp b ++ ca) post op
                  AbiReg.a0 AbiReg.t0 AbiReg.a0 (by decide) va vb st2
                  (by simpa only [hce, List.append_assoc] using hlink)
                  (by rw [lm.totalSize_append, lm.totalSize_append]; rw [htw_ce] at h64; omega)
                  (by rw [lm.totalSize_append, lm.totalSize_append] at *; simpa [Nat.add_assoc] using hpc2)
                  ht0_2 ((hoth2 _ (by decide) (by decide)).trans ha0_1)
              refine ⟨kb + ka + 1, st3,
                by rw [Nat.add_assoc, run_add, hrun1]; dsimp only; rw [run_add, hrun2]; exact hrun3,
                by rw [hpc3, lm.totalSize_append, lm.totalSize_append, htw_ce]; congr 2; omega,
                ha0_3, hpres1.trans (hpres12.trans ⟨hoth3 _ (by decide), hoth3 _ (by decide),
                  hoth3 _ (by decide), hoth3 _ (by decide)⟩),
                (hmem3.trans hmem2) ▸ heq1⟩
            · simp only [hvb] at rb
              rw [show evalE (.bin op a b) ⟨m, loc⟩ = .error .oob by
                simp [evalE, Bind.bind, StateT.bind, Except.bind, hva0, hvb]]
              exact rb
          | none =>
            let seq := compileE env.tab nlocals tmp a ++
                       storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + tmp)) ++
                       compileE env.tab nlocals (tmp + 1) b ++
                       loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nlocals + tmp))
            have hce : compileE env.tab nlocals tmp (.bin op a b) =
                seq ++ [emitBinOp op AbiReg.a0 AbiReg.t0 AbiReg.a0] := by
              simp [compileE, hb_c, ha_c, hsb, hsa, seq, List.append_assoc]
            have htw_op : lm.totalSize [emitBinOp op AbiReg.a0 AbiReg.t0 AbiReg.a0] = 1 := by
              cases op <;> simp [emitBinOp, Asm.add, Asm.sub, Asm.and, Asm.or,
                Asm.xor, Asm.sll, Asm.srl, Asm.mul, Asm.mulhu, lm.itemSize_instr]
            have htw_ce : lm.totalSize (compileE env.tab nlocals tmp (.bin op a b)) =
                lm.totalSize seq + 1 := by rw [hce, lm.totalSize_append, htw_op]
            have rseq := two_exprs_pair_sim_gen lm env hm L m loc pre
              ([emitBinOp op AbiReg.a0 AbiReg.t0 AbiReg.a0] ++ post) tmp a b haExpr hbExpr (by omega)
              (fun p q t s h1 h2 h3 h4 h5 h6 h7 h8 => iha p q t hvars.1 h1 h2 h3 s h4 h5 h6 h7 h8)
              (fun p q t s h1 h2 h3 h4 h5 h6 h7 h8 => ihb p q t hvars.2 h1 h2 h3 s h4 h5 h6 h7 h8)
              (by omega) (by omega) (by simpa only [hce, seq, List.append_assoc] using hlink)
              (by dsimp only [seq] at htw_ce; rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
            rcases haExpr.evalE_pure ⟨m, loc⟩ with ⟨va, hva⟩ | hva
            · rcases hbExpr.evalE_pure ⟨m, loc⟩ with ⟨vb, hvb⟩ | hvb
              · simp only [hva, hvb] at rseq
                obtain ⟨kseq, st1, hrun1, hpc1, ht0_1, ha0_1, hpres1, heq1⟩ := rseq
                rw [show evalE (.bin op a b) ⟨m, loc⟩ = .ok (op.eval va vb, ⟨m, loc⟩) by
                  simp [evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]]
                obtain ⟨st2, hrun2, hpc2, ha0_2, hoth2, hmem2⟩ :=
                  emitBinOp_step_lm lm env (pre ++ seq) post op AbiReg.a0 AbiReg.t0 AbiReg.a0 (by decide) va vb st1
                    (by simpa only [hce, List.append_assoc] using hlink)
                    (by rw [lm.totalSize_append]; rw [htw_ce] at h64; omega)
                    (by rw [lm.totalSize_append]; exact hpc1) ht0_1 ha0_1
                exact ⟨kseq + 1, st2, by rw [run_add, hrun1]; exact hrun2,
                  by rw [hpc2, lm.totalSize_append, htw_ce, Nat.add_assoc], ha0_2,
                  hpres1.trans ⟨hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide)⟩, hmem2 ▸ heq1⟩
              · simp only [hva, hvb] at rseq
                rw [show evalE (.bin op a b) ⟨m, loc⟩ = .error .oob by
                  simp [evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb]]
                exact rseq
            · simp only [hva] at rseq
              rw [show evalE (.bin op a b) ⟨m, loc⟩ = .error .oob by
                simp [evalE, Bind.bind, StateT.bind, Except.bind, hva]]
              exact rseq
  | cmpw c a b haExpr hbExpr iha ihb =>
    have hmt : maxTempsExpr (.cmpw c a b) = max (maxTempsExpr a) (1 + maxTempsExpr b) := rfl
    by_cases h1 : (c == .eq && b.constVal? == some 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h1
      rcases h1 with ⟨rfl, hb0⟩; obtain rfl := expr_constVal_eq_some hb0
      have hce : compileE env.tab nlocals tmp (.cmpw .eq a (.const 0)) =
          compileE env.tab nlocals tmp a ++ [Asm.sltiu AbiReg.a0 AbiReg.a0 1#12] := by
        simp [compileE, Expr.constVal?]
      have htw1 : lm.totalSize [Asm.sltiu AbiReg.a0 AbiReg.a0 1#12] = 1 := by simp [Asm.sltiu, lm.itemSize_instr]
      have htw_ce : lm.totalSize (compileE env.tab nlocals tmp (.cmpw .eq a (.const 0))) =
          lm.totalSize (compileE env.tab nlocals tmp a) + 1 := by rw [hce, lm.totalSize_append, htw1]
      have ra := iha pre ([Asm.sltiu AbiReg.a0 AbiReg.a0 1#12] ++ post) tmp hvars.1 (by omega)
        (by simpa only [hce, List.append_assoc] using hlink) (by rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
      rcases haExpr.evalE_pure ⟨m, loc⟩ with ⟨va, hva⟩ | hva
      · simp only [hva] at ra; obtain ⟨ka, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ra
        rw [show evalE (.cmpw .eq a (.const 0)) ⟨m, loc⟩ = .ok (Cmp.eq.evalW va 0, ⟨m, loc⟩) by
          simp [evalE, Bind.bind, StateT.bind, Except.bind, hva, Pure.pure, StateT.pure, Except.pure]]
        have hs := step_item_instr_lm lm env.hrom (pre ++ compileE env.tab nlocals tmp a) post
          (.aluImm .sltiu AbiReg.a0 AbiReg.a0 1#12) (by simpa only [hce, Asm.sltiu, List.append_assoc] using hlink)
          (by rw [lm.totalSize_append]; rw [htw_ce] at h64; omega) st1 (show st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ _)) from by rw [lm.totalSize_append]; exact hpc1)
        let st2 := stepReg st1 AbiReg.a0 (if va.toBitVec.ult 1#64 then 1#64 else 0#64) (st1.pc + 4#64)
        refine ⟨ka + 1, st2, by rw [run_add, hrun1]; exact run_one_cont _ _ _ (by rw [hs]; simp [execInstr, evalAluImm, ha0_1, show sextImm12 1#12 = 1#64 from rfl, stepReg, st2]),
          by change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1, htw_ce, Nat.add_assoc],
          ?_, hpres1.trans ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
            getReg_stepReg_ne _ _ _ (by decide) _ _,
            getReg_stepReg_ne _ _ _ (by decide) _ _⟩, heq1⟩
        rw [getReg_stepReg_eq _ _ (by decide)]
        have hsub := bv_sub_ult1_eq va.toBitVec 0#64; rw [BitVec.sub_zero] at hsub
        rw [hsub, show (0#64 : BitVec 64) = (0 : UInt64).toBitVec from rfl, ← uint64_cmp_eq, Cmp.evalW, Cmp.eval]
        cases va == 0 <;> decide
      · simp only [hva] at ra
        rw [show evalE (.cmpw .eq a (.const 0)) ⟨m, loc⟩ = .error .oob by simp [evalE, Bind.bind, StateT.bind, Except.bind, hva]]
        exact ra
    · by_cases h2 : (c == .eq && a.constVal? == some 0) = true
      · simp only [Bool.and_eq_true, beq_iff_eq] at h2
        rcases h2 with ⟨rfl, ha0⟩; obtain rfl := expr_constVal_eq_some ha0
        have hce : compileE env.tab nlocals tmp (.cmpw .eq (.const 0) b) =
            compileE env.tab nlocals tmp b ++ [Asm.sltiu AbiReg.a0 AbiReg.a0 1#12] := by
          have hne0 : (b.constVal? == some 0) = false := by
            cases hbx : b.constVal? == some 0 <;> simp_all
          change (if (Cmp.eq == .eq && b.constVal? == some 0) = true then _ else _) = _
          rw [hne0]; rfl
        have htw1 : lm.totalSize [Asm.sltiu AbiReg.a0 AbiReg.a0 1#12] = 1 := by simp [Asm.sltiu, lm.itemSize_instr]
        have htw_ce : lm.totalSize (compileE env.tab nlocals tmp (.cmpw .eq (.const 0) b)) =
            lm.totalSize (compileE env.tab nlocals tmp b) + 1 := by rw [hce, lm.totalSize_append, htw1]
        have rb := ihb pre ([Asm.sltiu AbiReg.a0 AbiReg.a0 1#12] ++ post) tmp hvars.2 (by omega)
          (by simpa only [hce, List.append_assoc] using hlink) (by rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
        rcases hbExpr.evalE_pure ⟨m, loc⟩ with ⟨vb, hvb⟩ | hvb
        · simp only [hvb] at rb; obtain ⟨kb, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := rb
          rw [show evalE (.cmpw .eq (.const 0) b) ⟨m, loc⟩ = .ok (Cmp.eq.evalW 0 vb, ⟨m, loc⟩) by
            simp [evalE, Bind.bind, StateT.bind, Except.bind, hvb, Pure.pure, StateT.pure, Except.pure]]
          have hs := step_item_instr_lm lm env.hrom (pre ++ compileE env.tab nlocals tmp b) post
            (.aluImm .sltiu AbiReg.a0 AbiReg.a0 1#12) (by simpa only [hce, Asm.sltiu, List.append_assoc] using hlink)
            (by rw [lm.totalSize_append]; rw [htw_ce] at h64; omega) st1 (show st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ _)) from by rw [lm.totalSize_append]; exact hpc1)
          let st2 := stepReg st1 AbiReg.a0 (if vb.toBitVec.ult 1#64 then 1#64 else 0#64) (st1.pc + 4#64)
          refine ⟨kb + 1, st2, by rw [run_add, hrun1]; exact run_one_cont _ _ _ (by rw [hs]; simp [execInstr, evalAluImm, ha0_1, show sextImm12 1#12 = 1#64 from rfl, stepReg, st2]),
            by change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1, htw_ce, Nat.add_assoc],
            ?_, hpres1.trans ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
              getReg_stepReg_ne _ _ _ (by decide) _ _,
              getReg_stepReg_ne _ _ _ (by decide) _ _⟩, heq1⟩
          rw [getReg_stepReg_eq _ _ (by decide)]
          have hsub := bv_sub_ult1_eq vb.toBitVec 0#64; rw [BitVec.sub_zero] at hsub
          have hcomm0 : (vb == (0 : UInt64)) = ((0 : UInt64) == vb) := Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq]; exact eq_comm)
          rw [hsub, show (0#64 : BitVec 64) = (0 : UInt64).toBitVec from rfl, ← uint64_cmp_eq, hcomm0, Cmp.evalW, Cmp.eval]
          cases (0 : UInt64) == vb <;> decide
        · simp only [hvb] at rb
          rw [show evalE (.cmpw .eq (.const 0) b) ⟨m, loc⟩ = .error .oob by
            simp [evalE, Bind.bind, StateT.bind, Except.bind, hvb, Pure.pure, StateT.pure, Except.pure]]
          exact rb
      · by_cases h3 : (c == .ne && b.constVal? == some 0) = true
        · simp only [Bool.and_eq_true, beq_iff_eq] at h3
          rcases h3 with ⟨rfl, hb0⟩; obtain rfl := expr_constVal_eq_some hb0
          have hce : compileE env.tab nlocals tmp (.cmpw .ne a (.const 0)) =
              compileE env.tab nlocals tmp a ++ [Asm.sltu AbiReg.a0 AbiReg.zero AbiReg.a0] := by
            simp [compileE, Expr.constVal?]
          have htw1 : lm.totalSize [Asm.sltu AbiReg.a0 AbiReg.zero AbiReg.a0] = 1 := by simp [Asm.sltu, lm.itemSize_instr]
          have htw_ce : lm.totalSize (compileE env.tab nlocals tmp (.cmpw .ne a (.const 0))) =
              lm.totalSize (compileE env.tab nlocals tmp a) + 1 := by rw [hce, lm.totalSize_append, htw1]
          have ra := iha pre ([Asm.sltu AbiReg.a0 AbiReg.zero AbiReg.a0] ++ post) tmp hvars.1 (by omega)
            (by simpa only [hce, List.append_assoc] using hlink) (by rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
          rcases haExpr.evalE_pure ⟨m, loc⟩ with ⟨va, hva⟩ | hva
          · simp only [hva] at ra; obtain ⟨ka, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ra
            rw [show evalE (.cmpw .ne a (.const 0)) ⟨m, loc⟩ = .ok (Cmp.ne.evalW va 0, ⟨m, loc⟩) by
              simp [evalE, Bind.bind, StateT.bind, Except.bind, hva, Pure.pure, StateT.pure, Except.pure]]
            have hs := step_item_instr_lm lm env.hrom (pre ++ compileE env.tab nlocals tmp a) post
              (.alu .sltu AbiReg.a0 AbiReg.zero AbiReg.a0) (by simpa only [hce, Asm.sltu, List.append_assoc] using hlink)
              (by rw [lm.totalSize_append]; rw [htw_ce] at h64; omega) st1 (show st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ _)) from by rw [lm.totalSize_append]; exact hpc1)
            let st2 := stepReg st1 AbiReg.a0 (if (0#64).ult va.toBitVec then 1#64 else 0#64) (st1.pc + 4#64)
            refine ⟨ka + 1, st2, by rw [run_add, hrun1]; exact run_one_cont _ _ _ (by rw [hs]; simp [execInstr, evalAlu, getReg_zero, ha0_1, stepReg, st2]),
              by change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1, htw_ce, Nat.add_assoc],
              ?_, hpres1.trans ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
                getReg_stepReg_ne _ _ _ (by decide) _ _,
                getReg_stepReg_ne _ _ _ (by decide) _ _⟩, heq1⟩
            rw [getReg_stepReg_eq _ _ (by decide)]
            have hsub := bv_zero_ult_sub_eq va.toBitVec 0#64; rw [BitVec.sub_zero] at hsub
            rw [hsub, show (0#64 : BitVec 64) = (0 : UInt64).toBitVec from rfl, ← uint64_cmp_ne, Cmp.evalW, Cmp.eval]
            cases va != 0 <;> decide
          · simp only [hva] at ra
            rw [show evalE (.cmpw .ne a (.const 0)) ⟨m, loc⟩ = .error .oob by simp [evalE, Bind.bind, StateT.bind, Except.bind, hva]]
            exact ra
        · by_cases h4 : (c == .ne && a.constVal? == some 0) = true
          · simp only [Bool.and_eq_true, beq_iff_eq] at h4
            rcases h4 with ⟨rfl, ha0⟩; obtain rfl := expr_constVal_eq_some ha0
            have hce : compileE env.tab nlocals tmp (.cmpw .ne (.const 0) b) =
                compileE env.tab nlocals tmp b ++ [Asm.sltu AbiReg.a0 AbiReg.zero AbiReg.a0] := by
              have hne0 : (b.constVal? == some 0) = false := by
                cases hbx : b.constVal? == some 0 <;> simp_all
              change (if _ then _ else if _ then _ else if (Cmp.ne == Cmp.ne && b.constVal? == some 0) = true then _ else _) = _
              rw [hne0]; rfl
            have htw1 : lm.totalSize [Asm.sltu AbiReg.a0 AbiReg.zero AbiReg.a0] = 1 := by simp [Asm.sltu, lm.itemSize_instr]
            have htw_ce : lm.totalSize (compileE env.tab nlocals tmp (.cmpw .ne (.const 0) b)) =
                lm.totalSize (compileE env.tab nlocals tmp b) + 1 := by rw [hce, lm.totalSize_append, htw1]
            have rb := ihb pre ([Asm.sltu AbiReg.a0 AbiReg.zero AbiReg.a0] ++ post) tmp hvars.2 (by omega)
              (by simpa only [hce, List.append_assoc] using hlink) (by rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
            rcases hbExpr.evalE_pure ⟨m, loc⟩ with ⟨vb, hvb⟩ | hvb
            · simp only [hvb] at rb; obtain ⟨kb, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := rb
              rw [show evalE (.cmpw .ne (.const 0) b) ⟨m, loc⟩ = .ok (Cmp.ne.evalW 0 vb, ⟨m, loc⟩) by
                simp [evalE, Bind.bind, StateT.bind, Except.bind, hvb, Pure.pure, StateT.pure, Except.pure]]
              have hs := step_item_instr_lm lm env.hrom (pre ++ compileE env.tab nlocals tmp b) post
                (.alu .sltu AbiReg.a0 AbiReg.zero AbiReg.a0) (by simpa only [hce, Asm.sltu, List.append_assoc] using hlink)
                (by rw [lm.totalSize_append]; rw [htw_ce] at h64; omega) st1 (show st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ _)) from by rw [lm.totalSize_append]; exact hpc1)
              let st2 := stepReg st1 AbiReg.a0 (if (0#64).ult vb.toBitVec then 1#64 else 0#64) (st1.pc + 4#64)
              refine ⟨kb + 1, st2, by rw [run_add, hrun1]; exact run_one_cont _ _ _ (by rw [hs]; simp [execInstr, evalAlu, getReg_zero, ha0_1, stepReg, st2]),
                by change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1, htw_ce, Nat.add_assoc],
                ?_, hpres1.trans ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
                  getReg_stepReg_ne _ _ _ (by decide) _ _,
                  getReg_stepReg_ne _ _ _ (by decide) _ _⟩, heq1⟩
              rw [getReg_stepReg_eq _ _ (by decide)]
              have hsub := bv_zero_ult_sub_eq vb.toBitVec 0#64; rw [BitVec.sub_zero] at hsub
              rw [hsub, show (0#64 : BitVec 64) = (0 : UInt64).toBitVec from rfl, ← uint64_cmp_ne,
                show (vb != (0 : UInt64)) = ((0 : UInt64) != vb) from Bool.eq_iff_iff.mpr (by simp only [bne_iff_ne, ne_eq]; exact ne_comm), Cmp.evalW, Cmp.eval]
              cases (0 : UInt64) != vb <;> decide
            · simp only [hvb] at rb
              rw [show evalE (.cmpw .ne (.const 0) b) ⟨m, loc⟩ = .error .oob by
                simp [evalE, Bind.bind, StateT.bind, Except.bind, hvb, Pure.pure, StateT.pure, Except.pure]]
              exact rb
          · cases hsb : emitSimpleExpr env.tab AbiReg.t0 AbiReg.t1 b with
            | some cb =>
              have hce : compileE env.tab nlocals tmp (.cmpw c a b) =
                  compileE env.tab nlocals tmp a ++ cb ++ emitCmpw c AbiReg.a0 AbiReg.t0 := by
                simp [compileE, h1, h2, h3, h4, hsb]
              have htw_ce : lm.totalSize (compileE env.tab nlocals tmp (.cmpw c a b)) =
                  lm.totalSize (compileE env.tab nlocals tmp a) + lm.totalSize cb + lm.totalSize (emitCmpw c AbiReg.a0 AbiReg.t0) := by
                rw [hce, lm.totalSize_append, lm.totalSize_append]
              have ra := iha pre (cb ++ emitCmpw c AbiReg.a0 AbiReg.t0 ++ post) tmp hvars.1 (by omega)
                (by simpa only [hce, List.append_assoc] using hlink) (by rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
              rcases haExpr.evalE_pure ⟨m, loc⟩ with ⟨va, hva⟩ | hva
              · simp only [hva] at ra; obtain ⟨ka, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ra
                obtain ⟨vb, kb, st2, hvb, hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
                  emitSimpleExpr_sim_gen lm env L m loc (pre ++ compileE env.tab nlocals tmp a)
                    (emitCmpw c AbiReg.a0 AbiReg.t0 ++ post) AbiReg.t0 AbiReg.t1
                    (by decide) (by decide) (by decide) (by decide) (by decide) b cb hsb hbExpr hvars.2
                    (by simpa only [hce, List.append_assoc] using hlink)
                    (by rw [lm.totalSize_append]; rw [htw_ce] at h64; omega)
                    st1 (show st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ _)) from by rw [lm.totalSize_append]; exact hpc1)
                    (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
                    (memRel_of_eqOutside_temp hm (by omega : tmp ≤ ntemps) heq1 hmemRel)
                    (frameOk_of_eqOutside_temp (by omega : tmp ≤ ntemps) heq1 hframeOk)
                rw [show evalE (.cmpw c a b) ⟨m, loc⟩ = .ok (c.evalW va vb, ⟨m, loc⟩) by
                  simp [evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]]
                obtain ⟨kc, st3, hrun3, hpc3, ha0_3, hpres3, hmem3⟩ :=
                  emitCmpw_sim_lm lm env (pre ++ compileE env.tab nlocals tmp a ++ cb) post c AbiReg.a0 AbiReg.t0 va vb st2
                    (by simpa only [hce, List.append_assoc] using hlink)
                    (by rw [lm.totalSize_append, lm.totalSize_append]; rw [htw_ce] at h64; omega)
                    (by rw [lm.totalSize_append, lm.totalSize_append]; simpa [Nat.add_assoc] using hpc2)
                    ((hoth2 _ (by decide) (by decide)).trans ha0_1) ht0_2
                have hp12 : PreservedRegs st1 st2 :=
                  ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
                   hoth2 _ (by decide) (by decide),
                   hoth2 _ (by decide) (by decide)⟩
                exact ⟨ka + kb + kc, st3, by rw [Nat.add_assoc, run_add, hrun1]; dsimp only; rw [run_add, hrun2]; exact hrun3,
                  by rw [hpc3, lm.totalSize_append, lm.totalSize_append, htw_ce]; congr 2; omega,
                  ha0_3, hpres1.trans (hp12.trans hpres3), (hmem3.trans hmem2) ▸ heq1⟩
              · simp only [hva] at ra
                rw [show evalE (.cmpw c a b) ⟨m, loc⟩ = .error .oob by simp [evalE, Bind.bind, StateT.bind, Except.bind, hva]]
                exact ra
            | none =>
              cases hsa : emitSimpleExpr env.tab AbiReg.t0 AbiReg.t1 a with
              | some ca =>
                have hce : compileE env.tab nlocals tmp (.cmpw c a b) =
                    compileE env.tab nlocals tmp b ++ ca ++ emitCmpw c AbiReg.t0 AbiReg.a0 := by
                  simp [compileE, h1, h2, h3, h4, hsb, hsa]
                have htw_ce : lm.totalSize (compileE env.tab nlocals tmp (.cmpw c a b)) =
                    lm.totalSize (compileE env.tab nlocals tmp b) + lm.totalSize ca + lm.totalSize (emitCmpw c AbiReg.t0 AbiReg.a0) := by
                  rw [hce, lm.totalSize_append, lm.totalSize_append]
                have rb := ihb pre (ca ++ emitCmpw c AbiReg.t0 AbiReg.a0 ++ post) tmp hvars.2 (by omega)
                  (by simpa only [hce, List.append_assoc] using hlink) (by rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
                have haOk : ∃ va, evalE a ⟨m, loc⟩ = .ok (va, ⟨m, loc⟩) := by
                  cases a <;> simp [emitSimpleExpr] at hsa <;> exact ⟨_, rfl⟩
                rcases haOk with ⟨va0, hva0⟩
                rcases hbExpr.evalE_pure ⟨m, loc⟩ with ⟨vb, hvb⟩ | hvb
                · simp only [hvb] at rb; obtain ⟨kb, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := rb
                  obtain ⟨va, ka, st2, hva, hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
                    emitSimpleExpr_sim_gen lm env L m loc (pre ++ compileE env.tab nlocals tmp b)
                      (emitCmpw c AbiReg.t0 AbiReg.a0 ++ post) AbiReg.t0 AbiReg.t1
                      (by decide) (by decide) (by decide) (by decide) (by decide) a ca hsa haExpr hvars.1
                      (by simpa only [hce, List.append_assoc] using hlink)
                      (by rw [lm.totalSize_append]; rw [htw_ce] at h64; omega)
                      st1 (show st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ _)) from by rw [lm.totalSize_append]; exact hpc1)
                      (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
                      (memRel_of_eqOutside_temp hm (by omega : tmp ≤ ntemps) heq1 hmemRel)
                      (frameOk_of_eqOutside_temp (by omega : tmp ≤ ntemps) heq1 hframeOk)
                  rw [show evalE (.cmpw c a b) ⟨m, loc⟩ = .ok (c.evalW va vb, ⟨m, loc⟩) by
                    simp [evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]]
                  obtain ⟨kc, st3, hrun3, hpc3, ha0_3, hpres3, hmem3⟩ :=
                    emitCmpw_sim_lm lm env (pre ++ compileE env.tab nlocals tmp b ++ ca) post c AbiReg.t0 AbiReg.a0 va vb st2
                      (by simpa only [hce, List.append_assoc] using hlink)
                      (by rw [lm.totalSize_append, lm.totalSize_append]; rw [htw_ce] at h64; omega)
                      (by rw [lm.totalSize_append, lm.totalSize_append]; simpa [Nat.add_assoc] using hpc2)
                      ht0_2 ((hoth2 _ (by decide) (by decide)).trans ha0_1)
                  have hp12 : PreservedRegs st1 st2 :=
                    ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
                     hoth2 _ (by decide) (by decide),
                     hoth2 _ (by decide) (by decide)⟩
                  exact ⟨kb + ka + kc, st3, by rw [Nat.add_assoc, run_add, hrun1]; dsimp only; rw [run_add, hrun2]; exact hrun3,
                    by rw [hpc3, lm.totalSize_append, lm.totalSize_append, htw_ce]; congr 2; omega,
                    ha0_3, hpres1.trans (hp12.trans hpres3), (hmem3.trans hmem2) ▸ heq1⟩
                · simp only [hvb] at rb
                  rw [show evalE (.cmpw c a b) ⟨m, loc⟩ = .error .oob by
                    simp [evalE, Bind.bind, StateT.bind, Except.bind, hva0, hvb]]
                  exact rb
              | none =>
                let seq := compileE env.tab nlocals tmp a ++
                           storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + tmp)) ++
                           compileE env.tab nlocals (tmp + 1) b ++
                           loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nlocals + tmp))
                have hce : compileE env.tab nlocals tmp (.cmpw c a b) =
                    seq ++ emitCmpw c AbiReg.t0 AbiReg.a0 := by
                  simp [compileE, h1, h2, h3, h4, hsb, hsa, seq, List.append_assoc]
                have htw_ce : lm.totalSize (compileE env.tab nlocals tmp (.cmpw c a b)) =
                    lm.totalSize seq + lm.totalSize (emitCmpw c AbiReg.t0 AbiReg.a0) := by
                  rw [hce, lm.totalSize_append]
                have rseq := two_exprs_pair_sim_gen lm env hm L m loc pre
                  (emitCmpw c AbiReg.t0 AbiReg.a0 ++ post) tmp a b haExpr hbExpr (by omega)
                  (fun p q t s h1 h2 h3 h4 h5 h6 h7 h8 => iha p q t hvars.1 h1 h2 h3 s h4 h5 h6 h7 h8)
                  (fun p q t s h1 h2 h3 h4 h5 h6 h7 h8 => ihb p q t hvars.2 h1 h2 h3 s h4 h5 h6 h7 h8)
                  (by omega) (by omega) (by simpa only [hce, seq, List.append_assoc] using hlink)
                  (by dsimp only [seq] at htw_ce; rw [htw_ce] at h64; omega) st hpc hgp hsp hmemRel hframeOk
                rcases haExpr.evalE_pure ⟨m, loc⟩ with ⟨va, hva⟩ | hva
                · rcases hbExpr.evalE_pure ⟨m, loc⟩ with ⟨vb, hvb⟩ | hvb
                  · simp only [hva, hvb] at rseq
                    obtain ⟨kseq, st1, hrun1, hpc1, ht0_1, ha0_1, hpres1, heq1⟩ := rseq
                    rw [show evalE (.cmpw c a b) ⟨m, loc⟩ = .ok (c.evalW va vb, ⟨m, loc⟩) by
                      simp [evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]]
                    obtain ⟨kc, st2, hrun2, hpc2, ha0_2, hpres2, hmem2⟩ :=
                      emitCmpw_sim_lm lm env (pre ++ seq) post c AbiReg.t0 AbiReg.a0 va vb st1
                        (by simpa only [hce, List.append_assoc] using hlink)
                        (by rw [lm.totalSize_append, Nat.add_assoc, ← htw_ce]; exact h64)
                        (by rw [lm.totalSize_append]; exact hpc1) ht0_1 ha0_1
                    exact ⟨kseq + kc, st2, by rw [run_add, hrun1]; exact hrun2,
                      by rw [hpc2, lm.totalSize_append, Nat.add_assoc, ← htw_ce], ha0_2,
                      hpres1.trans hpres2, hmem2 ▸ heq1⟩
                  · simp only [hva, hvb] at rseq
                    rw [show evalE (.cmpw c a b) ⟨m, loc⟩ = .error .oob by
                      simp [evalE, Bind.bind, StateT.bind, Except.bind, hva, hvb]]
                    exact rseq
                · simp only [hva] at rseq
                  rw [show evalE (.cmpw c a b) ⟨m, loc⟩ = .error .oob by
                    simp [evalE, Bind.bind, StateT.bind, Except.bind, hva]]
                  exact rseq
  | ld8 a i ha hiExpr ihi =>
    exact ld8_sim_gen lm env hm L m loc pre post tmp a i ha hiExpr htmp
      (fun p q t s h1 h2 h3 h4 h5 h6 h7 h8 => ihi p q t hvars h1 h2 h3 s h4 h5 h6 h7 h8)
      hlink h64 st hpc hgp hsp hmemRel hframeOk
  | ld64 a i ha hiExpr ihi =>
    exact ld64_sim_gen lm env hm L m loc pre post tmp a i ha hiExpr htmp
      (fun p q t s h1 h2 h3 h4 h5 h6 h7 h8 => ihi p q t hvars h1 h2 h3 s h4 h5 h6 h7 h8)
      hlink h64 st hpc hgp hsp hmemRel hframeOk


/-! ## 6. Forward Simulation of Conditions (`evalCond_sim_gen`) -/

theorem lookupLabel_of_lbl_lm (lm : LinkModel) {code : Array (BitVec 32)} {labels : LabelMap}
    (pre post : List AsmItem) (name : String)
    (hlink : lm.linkSpec (pre ++ [Asm.lbl name] ++ post) = .ok (code, labels)) :
    lookupLabel labels name = some (lm.totalSize pre) :=
  lm.lookup_label_at hlink

private def cmpBrItem (op : Cmp) (want : Bool) (target : String) : AsmItem :=
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

private theorem cmpBrItem_step_gen (lm : LinkModel) (env : CodeEnvGen lm) (pre post : List AsmItem)
    (op : Cmp) (want : Bool) (target : String) (tgt : Nat)
    (va vb : _root_.L.Word) (st1 : State)
    (htgt : lookupLabel env.labels target = some tgt)
    (hlink : lm.linkSpec (pre ++ [cmpBrItem op want target] ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lm.totalSize pre + lm.itemSize (cmpBrItem op want target)) < 2 ^ 64)
    (hpc1 : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (ht0 : st1.getReg AbiReg.t0 = va.toBitVec)
    (ha0 : st1.getReg AbiReg.a0 = vb.toBitVec) :
    ∃ k st2, 1 ≤ k ∧ RV64.run env.rom k st1 = .cont st2 ∧
      st2.pc = BitVec.ofNat 64
        (4 * (if op.eval va vb == want then tgt
              else lm.totalSize pre + lm.itemSize (cmpBrItem op want target))) ∧
      PreservedRegs st1 st2 ∧ st2.mem = st1.mem := by
  have stepAux : ∀ (bop : BranchOp) (rs1 rs2 : Reg)
      (hne : rs1 ≠ AbiReg.t6 ∧ rs2 ≠ AbiReg.t6)
      (hbr : cmpBrItem op want target = .br bop rs1 rs2 target)
      (heval : evalBranch bop (st1.getReg rs1) (st1.getReg rs2) = (op.eval va vb == want)),
      ∃ k st2, 1 ≤ k ∧ RV64.run env.rom k st1 = .cont st2 ∧
        st2.pc = BitVec.ofNat 64
          (4 * (if op.eval va vb == want then tgt
                else lm.totalSize pre + lm.itemSize (cmpBrItem op want target))) ∧
        PreservedRegs st1 st2 ∧ st2.mem = st1.mem := by
    intro bop rs1 rs2 hne hbr heval
    rw [hbr] at hlink h64 ⊢
    obtain ⟨tgt', k, st2, hk, hlook, hrun, hpc2, hreg2, hmem2⟩ :=
      step_item_br_lm lm env.hrom pre post bop rs1 rs2 target hlink hne h64 st1 hpc1
    have htgt' : tgt' = tgt := by rw [htgt] at hlook; cases hlook; rfl
    subst htgt'
    rw [heval] at hpc2
    refine ⟨k, st2, hk, hrun, ?_, PreservedRegs.of_regEqExceptT6 hreg2, hmem2⟩
    rw [hpc2]; cases op.eval va vb == want <;> rfl
  cases op <;> cases want
  · refine stepAux .bne AbiReg.t0 AbiReg.a0 (by decide) rfl ?_
    rw [evalBranch, ht0, ha0, Cmp.eval, uint64_cmp_eq]; simp [bne]
  · exact stepAux .beq AbiReg.t0 AbiReg.a0 (by decide) rfl
      (by rw [evalBranch, ht0, ha0, Cmp.eval, uint64_cmp_eq]; cases va.toBitVec == vb.toBitVec <;> rfl)
  · refine stepAux .beq AbiReg.t0 AbiReg.a0 (by decide) rfl ?_
    rw [evalBranch, ht0, ha0, Cmp.eval, uint64_cmp_ne]; simp [bne]
  · exact stepAux .bne AbiReg.t0 AbiReg.a0 (by decide) rfl
      (by rw [evalBranch, ht0, ha0, Cmp.eval, uint64_cmp_ne]; simp [bne])
  · refine stepAux .bgeu AbiReg.t0 AbiReg.a0 (by decide) rfl ?_
    rw [evalBranch, ht0, ha0, Cmp.eval, uint64_cmp_ult]; cases va.toBitVec.ult vb.toBitVec <;> rfl
  · refine stepAux .bltu AbiReg.t0 AbiReg.a0 (by decide) rfl ?_
    rw [evalBranch, ht0, ha0, Cmp.eval, uint64_cmp_ult]; cases va.toBitVec.ult vb.toBitVec <;> rfl
  · refine stepAux .bltu AbiReg.a0 AbiReg.t0 (by decide) rfl ?_
    rw [evalBranch, ht0, ha0, Cmp.eval, uint64_cmp_ule]; cases vb.toBitVec.ult va.toBitVec <;> rfl
  · refine stepAux .bgeu AbiReg.a0 AbiReg.t0 (by decide) rfl ?_
    rw [evalBranch, ht0, ha0, Cmp.eval, uint64_cmp_ule]; cases vb.toBitVec.ult va.toBitVec <;> rfl
  · refine stepAux .bge AbiReg.t0 AbiReg.a0 (by decide) rfl ?_
    rw [evalBranch, ht0, ha0, Cmp.eval, uint64_cmp_slt]; cases va.toBitVec.slt vb.toBitVec <;> rfl
  · refine stepAux .blt AbiReg.t0 AbiReg.a0 (by decide) rfl ?_
    rw [evalBranch, ht0, ha0, Cmp.eval, uint64_cmp_slt]; cases va.toBitVec.slt vb.toBitVec <;> rfl
  · refine stepAux .blt AbiReg.a0 AbiReg.t0 (by decide) rfl ?_
    rw [evalBranch, ht0, ha0, Cmp.eval, uint64_cmp_sle]; cases vb.toBitVec.slt va.toBitVec <;> rfl
  · refine stepAux .bge AbiReg.a0 AbiReg.t0 (by decide) rfl ?_
    rw [evalBranch, ht0, ha0, Cmp.eval, uint64_cmp_sle]; cases vb.toBitVec.slt va.toBitVec <;> rfl

theorem evalCond_sim_gen (lm : LinkModel) (env : CodeEnvGen lm) (hm : TabMapOk env.tab)
    {nlocals ntemps : Nat} (L : Layout env.tab nlocals ntemps)
    (m : _root_.L.Mem) (loc : _root_.L.Locals)
    (pre post : List AsmItem) (tmp : Nat) (pfx : String) (lblId : Nat)
    (c : Cond) (want : Bool) (target : String) (tgt : Nat)
    (hc : CoreCond env.tab c) (hvars : condVarsLt nlocals c)
    (htmp : tmp + maxTempsCond c ≤ ntemps)
    (htgt : lookupLabel env.labels target = some tgt)
    (hlink : lm.linkSpec (pre ++ (compileC env.tab nlocals tmp pfx lblId c want target).1 ++ post) =
        .ok (env.code, env.labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (compileC env.tab nlocals tmp pfx lblId c want target).1) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = L.sp)
    (hmemRel : MemRel env.tab L st.mem m) (hframeOk : FrameOk L st.mem nlocals loc) :
    match evalC c ⟨m, loc⟩ with
    | .ok (b, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (if b == want then tgt else
          lm.totalSize pre + lm.totalSize (compileC env.tab nlocals tmp pfx lblId c want target).1)) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem := by
  induction hc generalizing tmp pfx lblId want target tgt pre post st with
  | cmp op a b haExpr hbExpr =>
    have hmt : maxTempsCond (.cmp op a b) = max (maxTempsExpr a) (1 + maxTempsExpr b) := rfl
    by_cases hb0 : (b.constVal? == some 0) = true
    · have hbEq : b = .const 0 := expr_constVal_eq_some (beq_iff_eq.mp hb0)
      subst hbEq
      have hcc : (compileC env.tab nlocals tmp pfx lblId (.cmp op a (.const 0)) want target).1 =
          compileE env.tab nlocals tmp a ++ [brCmp op want AbiReg.a0 AbiReg.zero target] := by
        simp [compileC, Expr.constVal?]
      have htw_cc : lm.totalSize (compileC env.tab nlocals tmp pfx lblId (.cmp op a (.const 0)) want target).1 =
          lm.totalSize (compileE env.tab nlocals tmp a) + lm.itemSize (brCmp op want AbiReg.a0 AbiReg.zero target) := by
        rw [hcc, lm.totalSize_append, lm.totalSize_singleton]
      have ra := evalExpr_sim_gen lm env hm L m loc pre ([brCmp op want AbiReg.a0 AbiReg.zero target] ++ post) tmp a
        haExpr hvars.1 (by omega) (by simpa only [hcc, List.append_assoc] using hlink)
        (by rw [htw_cc] at h64; omega) st hpc hgp hsp hmemRel hframeOk
      rcases haExpr.evalE_pure ⟨m, loc⟩ with ⟨va, hva⟩ | hva
      · simp only [hva] at ra; obtain ⟨ka, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ra
        rw [show evalC (.cmp op a (.const 0)) ⟨m, loc⟩ = .ok (op.eval va 0, ⟨m, loc⟩) by
          simp [evalC, evalE, Bind.bind, StateT.bind, Except.bind, hva, Pure.pure, StateT.pure, Except.pure]]
        obtain ⟨kbr, st2, _, hrun2, hpc2, hpres2, hmem2⟩ :=
          brCmp_step_lm lm env (pre ++ compileE env.tab nlocals tmp a) post op want AbiReg.a0 AbiReg.zero
            (by decide) (by decide) target tgt va 0 st1 htgt
            (by simpa only [hcc, List.append_assoc] using hlink)
            (by rw [lm.totalSize_append, Nat.add_assoc, ← htw_cc]; exact h64)
            (by rw [lm.totalSize_append]; exact hpc1) ha0_1 rfl
        exact ⟨ka + kbr, st2, by rw [run_add, hrun1]; exact hrun2,
          by rw [hpc2, lm.totalSize_append, htw_cc, Nat.add_assoc], hpres1.trans hpres2, hmem2 ▸ heq1⟩
      · simp only [hva] at ra
        rw [show evalC (.cmp op a (.const 0)) ⟨m, loc⟩ = .error .oob by
          simp [evalC, Bind.bind, StateT.bind, Except.bind, hva]]
        exact ra
    · by_cases ha0 : (a.constVal? == some 0) = true
      · have haEq : a = .const 0 := expr_constVal_eq_some (beq_iff_eq.mp ha0)
        subst haEq
        have hcc : (compileC env.tab nlocals tmp pfx lblId (.cmp op (.const 0) b) want target).1 =
            compileE env.tab nlocals tmp b ++ [brCmp op want AbiReg.zero AbiReg.a0 target] := by
          have hbf : (b.constVal? == some 0) = false := Bool.eq_false_iff.mpr hb0
          change (if (b.constVal? == some 0) = true then _ else _) = _
          rw [hbf]; rfl
        have htw_cc : lm.totalSize (compileC env.tab nlocals tmp pfx lblId (.cmp op (.const 0) b) want target).1 =
            lm.totalSize (compileE env.tab nlocals tmp b) + lm.itemSize (brCmp op want AbiReg.zero AbiReg.a0 target) := by
          rw [hcc, lm.totalSize_append, lm.totalSize_singleton]
        have rb := evalExpr_sim_gen lm env hm L m loc pre ([brCmp op want AbiReg.zero AbiReg.a0 target] ++ post) tmp b
          hbExpr hvars.2 (by omega) (by simpa only [hcc, List.append_assoc] using hlink)
          (by rw [htw_cc] at h64; omega) st hpc hgp hsp hmemRel hframeOk
        rcases hbExpr.evalE_pure ⟨m, loc⟩ with ⟨vb, hvb⟩ | hvb
        · simp only [hvb] at rb; obtain ⟨kb, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := rb
          rw [show evalC (.cmp op (.const 0) b) ⟨m, loc⟩ = .ok (op.eval 0 vb, ⟨m, loc⟩) by
            simp [evalC, evalE, Bind.bind, StateT.bind, Except.bind, hvb, Pure.pure, StateT.pure, Except.pure]]
          obtain ⟨kbr, st2, _, hrun2, hpc2, hpres2, hmem2⟩ :=
            brCmp_step_lm lm env (pre ++ compileE env.tab nlocals tmp b) post op want AbiReg.zero AbiReg.a0
              (by decide) (by decide) target tgt 0 vb st1 htgt
              (by simpa only [hcc, List.append_assoc] using hlink)
              (by rw [lm.totalSize_append, Nat.add_assoc, ← htw_cc]; exact h64)
              (by rw [lm.totalSize_append]; exact hpc1) rfl ha0_1
          exact ⟨kb + kbr, st2, by rw [run_add, hrun1]; exact hrun2,
            by rw [hpc2, lm.totalSize_append, htw_cc, Nat.add_assoc], hpres1.trans hpres2, hmem2 ▸ heq1⟩
        · simp only [hvb] at rb
          rw [show evalC (.cmp op (.const 0) b) ⟨m, loc⟩ = .error .oob by
            simp [evalC, evalE, Bind.bind, StateT.bind, Except.bind, hvb, Pure.pure, StateT.pure, Except.pure]]
          exact rb
      · cases hsb : emitSimpleExpr env.tab AbiReg.t0 AbiReg.t1 b with
        | some cb =>
          have hcc : (compileC env.tab nlocals tmp pfx lblId (.cmp op a b) want target).1 =
              compileE env.tab nlocals tmp a ++ cb ++ [brCmp op want AbiReg.a0 AbiReg.t0 target] := by
            simp [compileC, hb0, ha0, hsb]
          have htw_cc : lm.totalSize (compileC env.tab nlocals tmp pfx lblId (.cmp op a b) want target).1 =
              lm.totalSize (compileE env.tab nlocals tmp a) + lm.totalSize cb +
                lm.itemSize (brCmp op want AbiReg.a0 AbiReg.t0 target) := by
            rw [hcc, lm.totalSize_append, lm.totalSize_append, lm.totalSize_singleton]
          have ra := evalExpr_sim_gen lm env hm L m loc pre
            (cb ++ [brCmp op want AbiReg.a0 AbiReg.t0 target] ++ post) tmp a
            haExpr hvars.1 (by omega) (by simpa only [hcc, List.append_assoc] using hlink)
            (by rw [htw_cc] at h64; omega) st hpc hgp hsp hmemRel hframeOk
          rcases haExpr.evalE_pure ⟨m, loc⟩ with ⟨va, hva⟩ | hva
          · simp only [hva] at ra; obtain ⟨ka, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ra
            obtain ⟨vb, kb, st2, hvb, hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
              emitSimpleExpr_sim_gen lm env L m loc (pre ++ compileE env.tab nlocals tmp a)
                ([brCmp op want AbiReg.a0 AbiReg.t0 target] ++ post) AbiReg.t0 AbiReg.t1
                (by decide) (by decide) (by decide) (by decide) (by decide) b cb hsb hbExpr hvars.2
                (by simpa only [hcc, List.append_assoc] using hlink)
                (by rw [lm.totalSize_append]; rw [htw_cc] at h64; omega)
                st1 (show st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ _)) from by rw [lm.totalSize_append]; exact hpc1)
                (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
                (memRel_of_eqOutside_temp hm (by omega : tmp ≤ ntemps) heq1 hmemRel)
                (frameOk_of_eqOutside_temp (by omega : tmp ≤ ntemps) heq1 hframeOk)
            rw [show evalC (.cmp op a b) ⟨m, loc⟩ = .ok (op.eval va vb, ⟨m, loc⟩) by
              simp [evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]]
            have hp12 : PreservedRegs st1 st2 :=
              ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
               hoth2 _ (by decide) (by decide),
               hoth2 _ (by decide) (by decide)⟩
            obtain ⟨kbr, st3, _, hrun3, hpc3, hpres3, hmem3⟩ :=
              brCmp_step_lm lm env (pre ++ compileE env.tab nlocals tmp a ++ cb) post op want
                AbiReg.a0 AbiReg.t0 (by decide) (by decide) target tgt va vb st2 htgt
                (by simpa only [hcc, List.append_assoc] using hlink)
                (by rw [lm.totalSize_append, lm.totalSize_append]; rw [htw_cc] at h64; omega)
                (by rw [lm.totalSize_append, lm.totalSize_append]; simpa [Nat.add_assoc] using hpc2)
                ((hoth2 _ (by decide) (by decide)).trans ha0_1) ht0_2
            exact ⟨ka + kb + kbr, st3, by rw [Nat.add_assoc, run_add, hrun1]; dsimp only; rw [run_add, hrun2]; exact hrun3,
              by rw [hpc3, lm.totalSize_append, lm.totalSize_append, htw_cc]; congr 2; split <;> omega,
              hpres1.trans (hp12.trans hpres3), (hmem3.trans hmem2) ▸ heq1⟩
          · simp only [hva] at ra
            rw [show evalC (.cmp op a b) ⟨m, loc⟩ = .error .oob by
              simp [evalC, Bind.bind, StateT.bind, Except.bind, hva]]
            exact ra
        | none =>
          cases hsa : emitSimpleExpr env.tab AbiReg.t0 AbiReg.t1 a with
          | some ca =>
            have hcc : (compileC env.tab nlocals tmp pfx lblId (.cmp op a b) want target).1 =
                compileE env.tab nlocals tmp b ++ ca ++ [brCmp op want AbiReg.t0 AbiReg.a0 target] := by
              simp [compileC, hb0, ha0, hsb, hsa]
            have htw_cc : lm.totalSize (compileC env.tab nlocals tmp pfx lblId (.cmp op a b) want target).1 =
                lm.totalSize (compileE env.tab nlocals tmp b) + lm.totalSize ca +
                  lm.itemSize (brCmp op want AbiReg.t0 AbiReg.a0 target) := by
              rw [hcc, lm.totalSize_append, lm.totalSize_append, lm.totalSize_singleton]
            have rb := evalExpr_sim_gen lm env hm L m loc pre
              (ca ++ [brCmp op want AbiReg.t0 AbiReg.a0 target] ++ post) tmp b
              hbExpr hvars.2 (by omega) (by simpa only [hcc, List.append_assoc] using hlink)
              (by rw [htw_cc] at h64; omega) st hpc hgp hsp hmemRel hframeOk
            have haOk : ∃ va, evalE a ⟨m, loc⟩ = .ok (va, ⟨m, loc⟩) := by
              cases a <;> simp [emitSimpleExpr] at hsa <;> exact ⟨_, rfl⟩
            rcases haOk with ⟨va0, hva0⟩
            rcases hbExpr.evalE_pure ⟨m, loc⟩ with ⟨vb, hvb⟩ | hvb
            · simp only [hvb] at rb; obtain ⟨kb, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := rb
              obtain ⟨va, ka, st2, hva, hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
                emitSimpleExpr_sim_gen lm env L m loc (pre ++ compileE env.tab nlocals tmp b)
                  ([brCmp op want AbiReg.t0 AbiReg.a0 target] ++ post) AbiReg.t0 AbiReg.t1
                  (by decide) (by decide) (by decide) (by decide) (by decide) a ca hsa haExpr hvars.1
                  (by simpa only [hcc, List.append_assoc] using hlink)
                  (by rw [lm.totalSize_append]; rw [htw_cc] at h64; omega)
                  st1 (show st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ _)) from by rw [lm.totalSize_append]; exact hpc1)
                  (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
                  (memRel_of_eqOutside_temp hm (by omega : tmp ≤ ntemps) heq1 hmemRel)
                  (frameOk_of_eqOutside_temp (by omega : tmp ≤ ntemps) heq1 hframeOk)
              rw [show evalC (.cmp op a b) ⟨m, loc⟩ = .ok (op.eval va vb, ⟨m, loc⟩) by
                simp [evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]]
              have hp12 : PreservedRegs st1 st2 :=
                ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
                 hoth2 _ (by decide) (by decide),
                 hoth2 _ (by decide) (by decide)⟩
              obtain ⟨kbr, st3, _, hrun3, hpc3, hpres3, hmem3⟩ :=
                brCmp_step_lm lm env (pre ++ compileE env.tab nlocals tmp b ++ ca) post op want
                  AbiReg.t0 AbiReg.a0 (by decide) (by decide) target tgt va vb st2 htgt
                  (by simpa only [hcc, List.append_assoc] using hlink)
                  (by rw [lm.totalSize_append, lm.totalSize_append]; rw [htw_cc] at h64; omega)
                  (by rw [lm.totalSize_append, lm.totalSize_append]; simpa [Nat.add_assoc] using hpc2)
                  ht0_2 ((hoth2 _ (by decide) (by decide)).trans ha0_1)
              exact ⟨kb + ka + kbr, st3, by rw [Nat.add_assoc, run_add, hrun1]; dsimp only; rw [run_add, hrun2]; exact hrun3,
                by rw [hpc3, lm.totalSize_append, lm.totalSize_append, htw_cc]; congr 2; split <;> omega,
                hpres1.trans (hp12.trans hpres3), (hmem3.trans hmem2) ▸ heq1⟩
            · simp only [hvb] at rb
              rw [show evalC (.cmp op a b) ⟨m, loc⟩ = .error .oob by
                simp [evalC, Bind.bind, StateT.bind, Except.bind, hva0, hvb]]
              exact rb
          | none =>
            let seq := compileE env.tab nlocals tmp a ++
                       storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + tmp)) ++
                       compileE env.tab nlocals (tmp + 1) b ++
                       loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nlocals + tmp))
            have hcc : (compileC env.tab nlocals tmp pfx lblId (.cmp op a b) want target).1 =
                seq ++ [brCmp op want AbiReg.t0 AbiReg.a0 target] := by
              simp [compileC, hb0, ha0, hsb, hsa, seq, List.append_assoc]
            have htw_cc : lm.totalSize (compileC env.tab nlocals tmp pfx lblId (.cmp op a b) want target).1 =
                lm.totalSize seq + lm.itemSize (brCmp op want AbiReg.t0 AbiReg.a0 target) := by
              rw [hcc, lm.totalSize_append, lm.totalSize_singleton]
            have rseq := two_exprs_pair_sim_gen lm env hm L m loc pre
              ([brCmp op want AbiReg.t0 AbiReg.a0 target] ++ post) tmp a b
              haExpr hbExpr (by omega)
              (fun p q t s h1 h2 h3 h4 h5 h6 h7 h8 =>
                evalExpr_sim_gen lm env hm L m loc p q t a haExpr hvars.1 h1 h2 h3 s h4 h5 h6 h7 h8)
              (fun p q t s h1 h2 h3 h4 h5 h6 h7 h8 =>
                evalExpr_sim_gen lm env hm L m loc p q t b hbExpr hvars.2 h1 h2 h3 s h4 h5 h6 h7 h8)
              (by omega) (by omega) (by simpa only [hcc, seq, List.append_assoc] using hlink)
              (by dsimp only [seq] at htw_cc; rw [htw_cc] at h64; omega) st hpc hgp hsp hmemRel hframeOk
            rcases haExpr.evalE_pure ⟨m, loc⟩ with ⟨va, hva⟩ | hva
            · rcases hbExpr.evalE_pure ⟨m, loc⟩ with ⟨vb, hvb⟩ | hvb
              · simp only [hva, hvb] at rseq
                obtain ⟨kseq, st1, hrun1, hpc1, ht0_1, ha0_1, hpres1, heq1⟩ := rseq
                rw [show evalC (.cmp op a b) ⟨m, loc⟩ = .ok (op.eval va vb, ⟨m, loc⟩) by
                  simp [evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]]
                obtain ⟨kbr, st2, _, hrun2, hpc2, hpres2, hmem2⟩ :=
                  brCmp_step_lm lm env (pre ++ seq) post op want AbiReg.t0 AbiReg.a0
                    (by decide) (by decide) target tgt va vb st1 htgt
                    (by simpa only [hcc, List.append_assoc] using hlink)
                    (by rw [lm.totalSize_append, Nat.add_assoc, ← htw_cc]; exact h64)
                    (by rw [lm.totalSize_append]; exact hpc1) ht0_1 ha0_1
                exact ⟨kseq + kbr, st2, by rw [run_add, hrun1]; exact hrun2,
                  by rw [hpc2, lm.totalSize_append, htw_cc, Nat.add_assoc], hpres1.trans hpres2, hmem2 ▸ heq1⟩
              · simp only [hva, hvb] at rseq
                rw [show evalC (.cmp op a b) ⟨m, loc⟩ = .error .oob by
                  simp [evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb]]
                exact rseq
            · simp only [hva] at rseq
              rw [show evalC (.cmp op a b) ⟨m, loc⟩ = .error .oob by
                simp [evalC, Bind.bind, StateT.bind, Except.bind, hva]]
              exact rseq
  | not p hp ihp =>
    have hcc : (compileC env.tab nlocals tmp pfx lblId (.not p) want target).1 =
        (compileC env.tab nlocals tmp pfx lblId p (!want) target).1 := rfl
    rw [hcc] at hlink h64 ⊢
    have r := ihp pre post tmp pfx lblId (!want) target tgt hvars htmp htgt hlink h64
      st hpc hgp hsp hmemRel hframeOk
    rcases hp.evalC_pure ⟨m, loc⟩ with ⟨bp, hbp⟩ | hbp
    · simp only [hbp] at r
      have heval : evalC (.not p) ⟨m, loc⟩ = .ok (!bp, ⟨m, loc⟩) := by
        simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, Pure.pure, StateT.pure, Except.pure]
      rw [heval]
      have hbeq : ((!bp) == want) = (bp == !want) := by cases bp <;> cases want <;> rfl
      simpa [hbeq] using r
    · simp only [hbp] at r
      have heval : evalC (.not p) ⟨m, loc⟩ = .error .oob := by
        simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp]
      rw [heval]; exact r
  | and p q hp hq ihp ihq =>
    dsimp only [maxTempsCond] at htmp
    cases want
    · have hcp_def : (compileC env.tab nlocals tmp pfx lblId (.and p q) false target).1 =
          (compileC env.tab nlocals tmp pfx lblId p false target).1 ++
          (compileC env.tab nlocals tmp pfx
            (compileC env.tab nlocals tmp pfx lblId p false target).2 q false target).1 := rfl
      let cp := (compileC env.tab nlocals tmp pfx lblId p false target).1
      let id1 := (compileC env.tab nlocals tmp pfx lblId p false target).2
      let cq := (compileC env.tab nlocals tmp pfx id1 q false target).1
      have htw_cc : lm.totalSize (compileC env.tab nlocals tmp pfx lblId (.and p q) false target).1 =
          lm.totalSize cp + lm.totalSize cq := by
        rw [hcp_def, (lm.totalSize_append)]
      have hlistP : pre ++ cp ++ (cq ++ post) =
          pre ++ (compileC env.tab nlocals tmp pfx lblId (.and p q) false target).1 ++ post := by
        dsimp only [cp, id1, cq]; rw [hcp_def]; simp only [List.append_assoc]
      have hlinkP : lm.linkSpec (pre ++ cp ++ (cq ++ post)) = .ok (env.code, env.labels) := by
        rw [hlistP]; exact hlink
      have rp := ihp pre (cq ++ post) tmp pfx lblId false target tgt hvars.1 (by omega) htgt hlinkP
        (by dsimp only [cp, cq] at htw_cc; rw [htw_cc] at h64; omega) st hpc hgp hsp hmemRel hframeOk
      rcases hp.evalC_pure ⟨m, loc⟩ with ⟨bp, hbp⟩ | hbp
      · cases bp
        · simp only [hbp] at rp
          have heval : evalC (.and p q) ⟨m, loc⟩ = .ok (false, ⟨m, loc⟩) := by
            simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, Pure.pure, StateT.pure, Except.pure]
          rw [heval]; exact rp
        · simp only [hbp] at rp
          obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := rp
          have htw1 : lm.totalSize (pre ++ cp) = lm.totalSize pre + lm.totalSize cp := (lm.totalSize_append) _ _
          have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ cp)) := by
            rw [htw1]; exact hpc1
          have hlistQ : (pre ++ cp) ++ cq ++ post =
              pre ++ (compileC env.tab nlocals tmp pfx lblId (.and p q) false target).1 ++ post := by
            dsimp only [cp, id1, cq]; rw [hcp_def]; simp only [List.append_assoc]
          have hlinkQ : lm.linkSpec ((pre ++ cp) ++ cq ++ post) = .ok (env.code, env.labels) := by
            rw [hlistQ]; exact hlink
          have rq := ihq (pre ++ cp) post tmp pfx id1 false target tgt hvars.2 (by omega) htgt hlinkQ
            (by rw [htw1]; dsimp only [cp, id1, cq] at htw_cc ⊢; rw [htw_cc] at h64; omega)
            st1 hpc1' (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
            (memRel_of_eqOutside_temp hm (by omega) heq1 hmemRel)
            (frameOk_of_eqOutside_temp (by omega) heq1 hframeOk)
          rcases hq.evalC_pure ⟨m, loc⟩ with ⟨bq, hbq⟩ | hbq
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : evalC (.and p q) ⟨m, loc⟩ = .ok (bq, ⟨m, loc⟩) := by
              simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            refine ⟨kp + kq, st2, ?_, ?_, hpres1.trans hpres2, MemEqOutside.trans heq1 heq2⟩
            · rw [run_add, hrun1]; exact hrun2
            · rw [hpc2, htw1, htw_cc, Nat.add_assoc]
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : evalC (.and p q) ⟨m, loc⟩ = .error .oob := by
              simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            exact ⟨kp + kq, st2, by rw [run_add, hrun1]; exact hrun2, hpc2,
              hpres1.trans hpres2, MemEqOutside.trans heq1 heq2⟩
      · simp only [hbp] at rp
        have heval : evalC (.and p q) ⟨m, loc⟩ = .error .oob := by
          simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp]
        rw [heval]; exact rp
    · let skipLbl := s!"{pfx}_and_{lblId}"
      let cp := (compileC env.tab nlocals tmp pfx (lblId + 1) p false skipLbl).1
      let id1 := (compileC env.tab nlocals tmp pfx (lblId + 1) p false skipLbl).2
      let cq := (compileC env.tab nlocals tmp pfx id1 q true target).1
      have hcp_def : (compileC env.tab nlocals tmp pfx lblId (.and p q) true target).1 =
          cp ++ cq ++ [Asm.lbl skipLbl] := rfl
      have htw_cc : lm.totalSize (compileC env.tab nlocals tmp pfx lblId (.and p q) true target).1 =
          lm.totalSize cp + lm.totalSize cq := by
        rw [hcp_def, (lm.totalSize_append), (lm.totalSize_append)]
        have h0 : lm.totalSize [Asm.lbl skipLbl] = 0 := by simp [Asm.lbl, lm.itemSize_label]
        omega
      have hlistSkip : (pre ++ cp ++ cq) ++ [Asm.lbl skipLbl] ++ post =
          pre ++ (compileC env.tab nlocals tmp pfx lblId (.and p q) true target).1 ++ post := by
        rw [hcp_def]; simp only [List.append_assoc]
      have hlinkSkip : lm.linkSpec ((pre ++ cp ++ cq) ++ [Asm.lbl skipLbl] ++ post) =
          .ok (env.code, env.labels) := by
        rw [hlistSkip]; exact hlink
      have hskip := lookupLabel_of_lbl_lm lm (pre ++ cp ++ cq) post skipLbl hlinkSkip
      have hlistP : pre ++ cp ++ (cq ++ [Asm.lbl skipLbl] ++ post) =
          pre ++ (compileC env.tab nlocals tmp pfx lblId (.and p q) true target).1 ++ post := by
        rw [hcp_def]; simp only [List.append_assoc]
      have hlinkP : lm.linkSpec (pre ++ cp ++ (cq ++ [Asm.lbl skipLbl] ++ post)) =
          .ok (env.code, env.labels) := by
        rw [hlistP]; exact hlink
      have rp := ihp pre (cq ++ [Asm.lbl skipLbl] ++ post) tmp pfx (lblId + 1) false skipLbl
        (lm.totalSize (pre ++ cp ++ cq)) hvars.1 (by omega) hskip hlinkP
        (by dsimp only [cp, cq] at htw_cc; rw [htw_cc] at h64; omega) st hpc hgp hsp hmemRel hframeOk
      rcases hp.evalC_pure ⟨m, loc⟩ with ⟨bp, hbp⟩ | hbp
      · cases bp
        · simp only [hbp] at rp
          obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := rp
          have heval : evalC (.and p q) ⟨m, loc⟩ = .ok (false, ⟨m, loc⟩) := by
            simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, Pure.pure, StateT.pure, Except.pure]
          rw [heval]
          refine ⟨kp, st1, hrun1, ?_, hpres1, heq1⟩
          rw [hpc1, (lm.totalSize_append), (lm.totalSize_append), htw_cc, Nat.add_assoc]
          simp only [show ((false == false) = true) = True from by decide,
            show ((false == true) = true) = False from by decide, ↓reduceIte]
        · simp only [hbp] at rp
          obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := rp
          have htw1 : lm.totalSize (pre ++ cp) = lm.totalSize pre + lm.totalSize cp := (lm.totalSize_append) _ _
          have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ cp)) := by
            rw [htw1]; exact hpc1
          have hlistQ : (pre ++ cp) ++ cq ++ ([Asm.lbl skipLbl] ++ post) =
              pre ++ (compileC env.tab nlocals tmp pfx lblId (.and p q) true target).1 ++ post := by
            rw [hcp_def]; simp only [List.append_assoc]
          have hlinkQ : lm.linkSpec ((pre ++ cp) ++ cq ++ ([Asm.lbl skipLbl] ++ post)) =
              .ok (env.code, env.labels) := by
            rw [hlistQ]; exact hlink
          have rq := ihq (pre ++ cp) ([Asm.lbl skipLbl] ++ post) tmp pfx id1 true target tgt
            hvars.2 (by omega) htgt hlinkQ
            (by rw [htw1]; dsimp only [cp, id1, cq] at htw_cc ⊢; rw [htw_cc] at h64; omega)
            st1 hpc1' (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
            (memRel_of_eqOutside_temp hm (by omega) heq1 hmemRel)
            (frameOk_of_eqOutside_temp (by omega) heq1 hframeOk)
          rcases hq.evalC_pure ⟨m, loc⟩ with ⟨bq, hbq⟩ | hbq
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : evalC (.and p q) ⟨m, loc⟩ = .ok (bq, ⟨m, loc⟩) := by
              simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            refine ⟨kp + kq, st2, ?_, ?_, hpres1.trans hpres2, MemEqOutside.trans heq1 heq2⟩
            · rw [run_add, hrun1]; exact hrun2
            · rw [hpc2, htw1, htw_cc, Nat.add_assoc]
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : evalC (.and p q) ⟨m, loc⟩ = .error .oob := by
              simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            exact ⟨kp + kq, st2, by rw [run_add, hrun1]; exact hrun2, hpc2,
              hpres1.trans hpres2, MemEqOutside.trans heq1 heq2⟩
      · simp only [hbp] at rp
        have heval : evalC (.and p q) ⟨m, loc⟩ = .error .oob := by
          simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp]
        rw [heval]; exact rp
  | or p q hp hq ihp ihq =>
    dsimp only [maxTempsCond] at htmp
    cases want
    · let skipLbl := s!"{pfx}_or_{lblId}"
      let cp := (compileC env.tab nlocals tmp pfx (lblId + 1) p true skipLbl).1
      let id1 := (compileC env.tab nlocals tmp pfx (lblId + 1) p true skipLbl).2
      let cq := (compileC env.tab nlocals tmp pfx id1 q false target).1
      have hcp_def : (compileC env.tab nlocals tmp pfx lblId (.or p q) false target).1 =
          cp ++ cq ++ [Asm.lbl skipLbl] := rfl
      have htw_cc : lm.totalSize (compileC env.tab nlocals tmp pfx lblId (.or p q) false target).1 =
          lm.totalSize cp + lm.totalSize cq := by
        rw [hcp_def, (lm.totalSize_append), (lm.totalSize_append)]
        have h0 : lm.totalSize [Asm.lbl skipLbl] = 0 := by simp [Asm.lbl, lm.itemSize_label]
        omega
      have hlistSkip : (pre ++ cp ++ cq) ++ [Asm.lbl skipLbl] ++ post =
          pre ++ (compileC env.tab nlocals tmp pfx lblId (.or p q) false target).1 ++ post := by
        rw [hcp_def]; simp only [List.append_assoc]
      have hlinkSkip : lm.linkSpec ((pre ++ cp ++ cq) ++ [Asm.lbl skipLbl] ++ post) =
          .ok (env.code, env.labels) := by
        rw [hlistSkip]; exact hlink
      have hskip := lookupLabel_of_lbl_lm lm (pre ++ cp ++ cq) post skipLbl hlinkSkip
      have hlistP : pre ++ cp ++ (cq ++ [Asm.lbl skipLbl] ++ post) =
          pre ++ (compileC env.tab nlocals tmp pfx lblId (.or p q) false target).1 ++ post := by
        rw [hcp_def]; simp only [List.append_assoc]
      have hlinkP : lm.linkSpec (pre ++ cp ++ (cq ++ [Asm.lbl skipLbl] ++ post)) =
          .ok (env.code, env.labels) := by
        rw [hlistP]; exact hlink
      have rp := ihp pre (cq ++ [Asm.lbl skipLbl] ++ post) tmp pfx (lblId + 1) true skipLbl
        (lm.totalSize (pre ++ cp ++ cq)) hvars.1 (by omega) hskip hlinkP
        (by dsimp only [cp, cq] at htw_cc; rw [htw_cc] at h64; omega) st hpc hgp hsp hmemRel hframeOk
      rcases hp.evalC_pure ⟨m, loc⟩ with ⟨bp, hbp⟩ | hbp
      · cases bp
        · simp only [hbp] at rp
          obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := rp
          have htw1 : lm.totalSize (pre ++ cp) = lm.totalSize pre + lm.totalSize cp := (lm.totalSize_append) _ _
          have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ cp)) := by
            rw [htw1]; exact hpc1
          have hlistQ : (pre ++ cp) ++ cq ++ ([Asm.lbl skipLbl] ++ post) =
              pre ++ (compileC env.tab nlocals tmp pfx lblId (.or p q) false target).1 ++ post := by
            rw [hcp_def]; simp only [List.append_assoc]
          have hlinkQ : lm.linkSpec ((pre ++ cp) ++ cq ++ ([Asm.lbl skipLbl] ++ post)) =
              .ok (env.code, env.labels) := by
            rw [hlistQ]; exact hlink
          have rq := ihq (pre ++ cp) ([Asm.lbl skipLbl] ++ post) tmp pfx id1 false target tgt
            hvars.2 (by omega) htgt hlinkQ
            (by rw [htw1]; dsimp only [cp, id1, cq] at htw_cc ⊢; rw [htw_cc] at h64; omega)
            st1 hpc1' (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
            (memRel_of_eqOutside_temp hm (by omega) heq1 hmemRel)
            (frameOk_of_eqOutside_temp (by omega) heq1 hframeOk)
          rcases hq.evalC_pure ⟨m, loc⟩ with ⟨bq, hbq⟩ | hbq
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : evalC (.or p q) ⟨m, loc⟩ = .ok (bq, ⟨m, loc⟩) := by
              simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            refine ⟨kp + kq, st2, ?_, ?_, hpres1.trans hpres2, MemEqOutside.trans heq1 heq2⟩
            · rw [run_add, hrun1]; exact hrun2
            · rw [hpc2, htw1, htw_cc, Nat.add_assoc]
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : evalC (.or p q) ⟨m, loc⟩ = .error .oob := by
              simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            exact ⟨kp + kq, st2, by rw [run_add, hrun1]; exact hrun2, hpc2,
              hpres1.trans hpres2, MemEqOutside.trans heq1 heq2⟩
        · simp only [hbp] at rp
          obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := rp
          have heval : evalC (.or p q) ⟨m, loc⟩ = .ok (true, ⟨m, loc⟩) := by
            simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, Pure.pure, StateT.pure, Except.pure]
          rw [heval]
          refine ⟨kp, st1, hrun1, ?_, hpres1, heq1⟩
          rw [hpc1, (lm.totalSize_append), (lm.totalSize_append), htw_cc, Nat.add_assoc]
          simp only [beq_self_eq_true, Bool.true_beq, Bool.false_eq_true, ↓reduceIte]
      · simp only [hbp] at rp
        have heval : evalC (.or p q) ⟨m, loc⟩ = .error .oob := by
          simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp]
        rw [heval]; exact rp
    · have hcp_def : (compileC env.tab nlocals tmp pfx lblId (.or p q) true target).1 =
          (compileC env.tab nlocals tmp pfx lblId p true target).1 ++
          (compileC env.tab nlocals tmp pfx
            (compileC env.tab nlocals tmp pfx lblId p true target).2 q true target).1 := rfl
      let cp := (compileC env.tab nlocals tmp pfx lblId p true target).1
      let id1 := (compileC env.tab nlocals tmp pfx lblId p true target).2
      let cq := (compileC env.tab nlocals tmp pfx id1 q true target).1
      have htw_cc : lm.totalSize (compileC env.tab nlocals tmp pfx lblId (.or p q) true target).1 =
          lm.totalSize cp + lm.totalSize cq := by
        rw [hcp_def, (lm.totalSize_append)]
      have hlistP : pre ++ cp ++ (cq ++ post) =
          pre ++ (compileC env.tab nlocals tmp pfx lblId (.or p q) true target).1 ++ post := by
        dsimp only [cp, id1, cq]; rw [hcp_def]; simp only [List.append_assoc]
      have hlinkP : lm.linkSpec (pre ++ cp ++ (cq ++ post)) = .ok (env.code, env.labels) := by
        rw [hlistP]; exact hlink
      have rp := ihp pre (cq ++ post) tmp pfx lblId true target tgt hvars.1 (by omega) htgt hlinkP
        (by dsimp only [cp, cq] at htw_cc; rw [htw_cc] at h64; omega) st hpc hgp hsp hmemRel hframeOk
      rcases hp.evalC_pure ⟨m, loc⟩ with ⟨bp, hbp⟩ | hbp
      · cases bp
        · simp only [hbp] at rp
          obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := rp
          have htw1 : lm.totalSize (pre ++ cp) = lm.totalSize pre + lm.totalSize cp := (lm.totalSize_append) _ _
          have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ cp)) := by
            rw [htw1]; exact hpc1
          have hlistQ : (pre ++ cp) ++ cq ++ post =
              pre ++ (compileC env.tab nlocals tmp pfx lblId (.or p q) true target).1 ++ post := by
            dsimp only [cp, id1, cq]; rw [hcp_def]; simp only [List.append_assoc]
          have hlinkQ : lm.linkSpec ((pre ++ cp) ++ cq ++ post) = .ok (env.code, env.labels) := by
            rw [hlistQ]; exact hlink
          have rq := ihq (pre ++ cp) post tmp pfx id1 true target tgt hvars.2 (by omega) htgt hlinkQ
            (by rw [htw1]; dsimp only [cp, id1, cq] at htw_cc ⊢; rw [htw_cc] at h64; omega)
            st1 hpc1' (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
            (memRel_of_eqOutside_temp hm (by omega) heq1 hmemRel)
            (frameOk_of_eqOutside_temp (by omega) heq1 hframeOk)
          rcases hq.evalC_pure ⟨m, loc⟩ with ⟨bq, hbq⟩ | hbq
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : evalC (.or p q) ⟨m, loc⟩ = .ok (bq, ⟨m, loc⟩) := by
              simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            refine ⟨kp + kq, st2, ?_, ?_, hpres1.trans hpres2, MemEqOutside.trans heq1 heq2⟩
            · rw [run_add, hrun1]; exact hrun2
            · rw [hpc2, htw1, htw_cc, Nat.add_assoc]
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : evalC (.or p q) ⟨m, loc⟩ = .error .oob := by
              simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            exact ⟨kp + kq, st2, by rw [run_add, hrun1]; exact hrun2, hpc2,
              hpres1.trans hpres2, MemEqOutside.trans heq1 heq2⟩
        · simp only [hbp] at rp
          have heval : evalC (.or p q) ⟨m, loc⟩ = .ok (true, ⟨m, loc⟩) := by
            simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, Pure.pure, StateT.pure, Except.pure]
          rw [heval]; exact rp
      · simp only [hbp] at rp
        have heval : evalC (.or p q) ⟨m, loc⟩ = .error .oob := by
          simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp]
        rw [heval]; exact rp

end ConAgua.RISCV.Compiler
