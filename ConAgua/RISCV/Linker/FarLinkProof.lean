import ConAgua.RISCV.RV64.Roundtrip
import ConAgua.RISCV.Compiler.AsmProof
import ConAgua.RISCV.Linker.FarLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Far Linker Verification Proofs (`ConAgua.RISCV.Linker.FarLinkProof`)

Pure kernel-checked proofs (zero `sorry`, zero `native_decide`, zero `bv_decide`,
standard axioms `[propext, Classical.choice, Quot.sound]` only) for `ConAgua.RISCV.Linker.FarLink`:

1. **`jal + lui + add + jalr` BitVec arithmetic (`splitFarOffWords_val`, `pc_add_splitFarOffWords`):**
   for any `pc tgt : Nat` with `farInRange ((tgt : Int) - (pc : Int)) = true` (`±2 GiB`),
   `pc64 + sextImmU hi20 + sextImm12 lo12` (masked with `~~~1#64`) equals `BitVec.ofNat 64 (4 * tgt)`.
2. **Operational multi-cycle execution lemmas under `ConAgua.RISCV.RV64.Semantics.step`/`run`:**
   `step_far_jalr` (4 cycles), `step_far_branch_taken` (5 cycles), `step_far_branch_not_taken` (1 cycle).
3. **Full `linkFar` decode & step theorems (`linkFar_size`, `linkFar_item_spec`,
   `linkFar_word_decode`, `linkFar_step_j`, `linkFar_step_call`, `linkFar_step_br_taken`,
   `linkFar_step_br_not_taken`):** connects the fast O(N) `Std.HashMap` `linkFar` executable
   directly to `RV64.Semantics.run` via `linkFar_ok_spec`.
-/

namespace ConAgua.RISCV.Linker

open ConAgua.RISCV.RV64
open ConAgua.RISCV.Compiler

/-! ## 1. `jal + lui + add + jalr` BitVec Offset Arithmetic -/

private theorem toInt_ofInt_eq {n : Nat} (hn : 0 < n) (z : Int)
    (hlo : -(2 ^ (n - 1) : Int) ≤ z) (hhi : z < (2 ^ (n - 1) : Int)) :
    (BitVec.ofInt n z).toInt = z := by
  rw [BitVec.toInt_ofInt]
  have hpow : (2 : Int) ^ n = 2 * (2 ^ (n - 1) : Int) := by
    cases n with
    | zero => omega
    | succ m => simp [Int.pow_succ, Int.mul_comm]
  rw [Int.bmod_def]
  push_cast
  have hmod : z % ((2 : Int) ^ n) = if 0 ≤ z then z else z + (2 : Int) ^ n := by
    split
    · next h0 => exact Int.emod_eq_of_lt h0 (by omega)
    · next h0 =>
      have h1 : 0 ≤ z + (2 : Int) ^ n := by omega
      have h2 : z + (2 : Int) ^ n < (2 : Int) ^ n := by omega
      have heq : (z + (2 : Int) ^ n) % ((2 : Int) ^ n) = z % ((2 : Int) ^ n) := by
        rw [Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]
      rw [← heq, Int.emod_eq_of_lt h1 h2]
  rw [hmod]
  split <;> split <;> omega

private theorem sextImmU_eq_ofInt (imm : BitVec 20) :
    sextImmU imm = BitVec.ofInt 64 (4096 * imm.toInt) := by
  unfold sextImmU
  apply BitVec.eq_of_toInt_eq
  have h1 : (imm ++ 0#12).toInt = 4096 * imm.toInt := by
    rw [BitVec.toInt_append]; simp
  have hlo : -(2 ^ 19 : Int) ≤ imm.toInt := BitVec.le_toInt imm
  have hhi : imm.toInt < (2 ^ 19 : Int) := BitVec.toInt_lt
  rw [BitVec.toInt_signExtend]
  have hmin : min 64 (20 + 12) = 32 := by decide
  rw [hmin, h1, ← BitVec.toInt_ofInt (n := 32) (4096 * imm.toInt)]
  rw [toInt_ofInt_eq (by omega) (4096 * imm.toInt) (by omega) (by omega)]
  rw [toInt_ofInt_eq (by omega) (4096 * imm.toInt) (by omega) (by omega)]

private theorem sextImm12_eq_ofInt (imm : BitVec 12) :
    sextImm12 imm = BitVec.ofInt 64 imm.toInt := by
  unfold sextImm12
  apply BitVec.eq_of_toInt_eq
  have hlo : -(2 ^ 11 : Int) ≤ imm.toInt := BitVec.le_toInt imm
  have hhi : imm.toInt < (2 ^ 11 : Int) := BitVec.toInt_lt
  rw [BitVec.toInt_signExtend]
  have hmin : min 64 12 = 12 := by decide
  rw [hmin, ← BitVec.toInt_ofInt (n := 12) imm.toInt]
  rw [toInt_ofInt_eq (by omega) imm.toInt (by omega) (by omega)]
  rw [toInt_ofInt_eq (by omega) imm.toInt (by omega) (by omega)]

private theorem extract0_12_ofInt32 (z : Int) :
    (BitVec.ofInt 32 z).extractLsb' 0 12 = BitVec.ofInt 12 z := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_ofInt]
  have hmod : (z % (2 ^ 32 : Int)).toNat % 2 ^ 12 = (z % (2 ^ 12 : Int)).toNat := by
    have h1 : (0 : Int) ≤ z % (2 ^ 32 : Int) := Int.emod_nonneg z (by decide)
    have h2 : (0 : Int) ≤ z % (2 ^ 12 : Int) := Int.emod_nonneg z (by decide)
    have hdvd : (2 ^ 12 : Int) ∣ (2 ^ 32 : Int) := by decide
    have he : (z % (2 ^ 32 : Int)) % (2 ^ 12 : Int) = z % (2 ^ 12 : Int) :=
      Int.emod_emod_of_dvd z hdvd
    omega
  simpa using hmod

private theorem extract12_20_ofInt32 (h r : Int)
    (hhlo : -(2 ^ 19 : Int) ≤ h) (hhhi : h < (2 ^ 19 : Int))
    (hrlo : 0 ≤ r) (hrhi : r < 4096) :
    (BitVec.ofInt 32 (4096 * h + r)).extractLsb' 12 20 = BitVec.ofInt 20 h := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofInt]
  have hdiv : ((4096 * h + r) % (2 ^ 32 : Int)).toNat >>> 12 % 2 ^ 20 = (h % (2 ^ 20 : Int)).toNat := by
    rw [Nat.shiftRight_eq_div_pow]
    have hnn : (0 : Int) ≤ (4096 * h + r) % (2 ^ 32 : Int) := Int.emod_nonneg _ (by decide)
    have hlt : (4096 * h + r) % (2 ^ 32 : Int) < (2 ^ 32 : Int) := Int.emod_lt_of_pos _ (by decide)
    by_cases hh0 : 0 ≤ h
    · have hmod1 : (4096 * h + r) % (2 ^ 32 : Int) = 4096 * h + r :=
        Int.emod_eq_of_lt (by omega) (by omega)
      have hmod2 : h % (2 ^ 20 : Int) = h := Int.emod_eq_of_lt hh0 (by omega)
      rw [hmod1, hmod2]
      omega
    · have hmod1 : (4096 * h + r) % (2 ^ 32 : Int) = 4096 * (h + 2 ^ 20) + r := by
        have h1 : 0 ≤ 4096 * (h + 2 ^ 20) + r := by omega
        have h2 : 4096 * (h + 2 ^ 20) + r < 2 ^ 32 := by omega
        have heq : (4096 * (h + 2 ^ 20) + r) % (2 ^ 32 : Int) = (4096 * h + r) % (2 ^ 32 : Int) := by
          have : 4096 * (h + (2 ^ 20 : Int)) + r = (4096 * h + r) + (2 ^ 32 : Int) := by omega
          rw [this, Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]
        rw [← heq, Int.emod_eq_of_lt h1 h2]
      have hmod2 : h % (2 ^ 20 : Int) = h + 2 ^ 20 := by
        have h1 : 0 ≤ h + (2 ^ 20 : Int) := by omega
        have h2 : h + (2 ^ 20 : Int) < (2 ^ 20 : Int) := by omega
        have heq : (h + (2 ^ 20 : Int)) % (2 ^ 20 : Int) = h % (2 ^ 20 : Int) := by
          rw [Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]
        rw [← heq, Int.emod_eq_of_lt h1 h2]
      rw [hmod1, hmod2]
      omega
  simpa using hdiv

/-- Exact signed 32-bit `lui + jalr` offset decomposition theorem over `±2 GiB`. -/
theorem splitFarOffWords_val {diffWords : Int} (hrange : farInRange diffWords = true) :
    let (hi20, lo12) := splitFarOffWords diffWords
    sextImmU hi20 + sextImm12 lo12 = BitVec.ofInt 64 (4 * diffWords) := by
  simp only [farInRange, Bool.and_eq_true, decide_eq_true_eq] at hrange
  let off : Int := 4 * diffWords
  have hoff_lo : -(2 ^ 31 : Int) ≤ off := by omega
  have hoff_hi : off < (2 ^ 31 - 2048 : Int) := by omega
  let h : Int := (off + 2048) / 4096
  let r : Int := (off + 2048) % 4096
  let l : Int := r - 2048
  have hdiv : 4096 * h + r = off + 2048 := Int.mul_ediv_add_emod (off + 2048) 4096
  have hr_lo : 0 ≤ r := Int.emod_nonneg _ (by decide)
  have hr_hi : r < 4096 := Int.emod_lt_of_pos _ (by decide)
  have hl_lo : -2048 ≤ l := by omega
  have hl_hi : l < 2048 := by omega
  have hh_lo : -(2 ^ 19 : Int) ≤ h := by omega
  have hh_hi : h < (2 ^ 19 : Int) := by omega
  have hoff_eq : off = 4096 * h + l := by omega
  have hlo12 : (BitVec.ofInt 32 off).extractLsb' 0 12 = BitVec.ofInt 12 l := by
    rw [extract0_12_ofInt32]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt]
    have hmod_eq : off % ((2 ^ 12 : Nat) : Int) = l % ((2 ^ 12 : Nat) : Int) := by
      have : off = l + ((2 ^ 12 : Nat) : Int) * h := by omega
      rw [this, Int.add_emod, Int.mul_emod_right, Int.add_zero, Int.emod_emod]
    rw [hmod_eq]
  have hhi20 : (BitVec.ofInt 32 off + 0x800#32).extractLsb' 12 20 = BitVec.ofInt 20 h := by
    have hadd : BitVec.ofInt 32 off + 0x800#32 = BitVec.ofInt 32 (4096 * h + r) := by
      rw [show (0x800#32 : BitVec 32) = BitVec.ofInt 32 2048 by decide, ← BitVec.ofInt_add]
      congr 1; omega
    rw [hadd]
    exact extract12_20_ofInt32 h r hh_lo hh_hi hr_lo hr_hi
  dsimp only [splitFarOffWords]
  change sextImmU ((BitVec.ofInt 32 off + 0x800#32).extractLsb' 12 20) +
    sextImm12 ((BitVec.ofInt 32 off).extractLsb' 0 12) = BitVec.ofInt 64 off
  rw [hhi20, hlo12, sextImmU_eq_ofInt, sextImm12_eq_ofInt]
  rw [toInt_ofInt_eq (by omega) h hh_lo hh_hi, toInt_ofInt_eq (by omega) l hl_lo hl_hi]
  rw [← BitVec.ofInt_add]
  congr 1; omega

private theorem and_not_one_of_mul4 (n : Nat) :
    (BitVec.ofNat 64 (4 * n)) &&& ~~~1#64 = BitVec.ofNat 64 (4 * n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not]
  cases i with
  | zero =>
    simp only [BitVec.getLsbD_ofNat, Nat.zero_lt_succ, decide_true, Bool.true_and, Nat.testBit_zero]
    simp [show (4 * n) % 2 = 0 by omega]
  | succ i' =>
    simp [hi]

/-- Exact PC + `lui + jalr` target computation for word indices `pc` and `tgt`. -/
theorem pc_add_splitFarOffWords {pc tgt : Nat}
    (h : farInRange ((tgt : Int) - (pc : Int)) = true) :
    let (hi20, lo12) := splitFarOffWords ((tgt : Int) - (pc : Int))
    ((BitVec.ofNat 64 (4 * pc) + sextImmU hi20 + sextImm12 lo12) &&& ~~~1#64) =
      BitVec.ofNat 64 (4 * tgt) := by
  dsimp only
  have hval := splitFarOffWords_val h
  dsimp only at hval
  rw [BitVec.add_assoc, hval]
  rw [show BitVec.ofNat 64 (4 * pc) = BitVec.ofInt 64 (4 * (pc : Int)) from rfl]
  rw [← BitVec.ofInt_add]
  have hsum : (4 * (pc : Int) + 4 * ((tgt : Int) - (pc : Int))) = 4 * (tgt : Int) := by omega
  rw [hsum]
  exact and_not_one_of_mul4 tgt

/-! ## 2. Operational Multi-Step Execution Lemmas (`RV64.Semantics.step` / `run`) -/

private theorem pc_mul4_props {k : Nat} (hk : 4 * k < 2 ^ 64) :
    (BitVec.ofNat 64 (4 * k)).toNat / 4 = k ∧
    isAligned (BitVec.ofNat 64 (4 * k)) 4 = true ∧
    BitVec.ofNat 64 (4 * k) + 4#64 = BitVec.ofNat 64 (4 * (k + 1)) := by
  have hto : (BitVec.ofNat 64 (4 * k)).toNat = 4 * k := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  refine ⟨by rw [hto]; omega, ?_, ?_⟩
  · simp only [isAligned, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, hto, BitVec.toNat_ofNat]
    omega
  · apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, hto, Nat.mul_add]

private theorem getReg_setReg_eq {st : State} {r : Reg} (hr : r ≠ AbiReg.zero) (v : Word) :
    (st.setReg r v).getReg r = v := by
  have h0 : (r == 0#5) = false := Bool.eq_false_iff.mpr (fun h => hr (beq_iff_eq.mp h))
  simp [State.setReg, State.getReg, h0]

private theorem getReg_setReg_ne {st : State} {r q : Reg} (hrq : r ≠ q) (v : Word) :
    (st.setReg r v).getReg q = st.getReg q := by
  by_cases hr : r == 0#5
  · simp [State.setReg, hr]
  · have hqr : q ≠ r := fun h => hrq h.symm
    by_cases hq : q == 0#5
    · simp [State.getReg, hq]
    · simp [State.setReg, State.getReg, hr, hq, hqr]

/-- Execute a 4-instruction `jal t6, +4; lui s1, hi20; add t6, t6, s1; jalr rd, t6, lo12` veneer
    over `RV64.Semantics.step`/`run`. Jumps to `4 * tgt`, sets `rd := 4 * (pc + 4)` (when `rd ≠ zero`),
    clobbers only `{t6, s1}` (assuming `rd ∉ {t6, s1}`), and leaves all other registers and memory unchanged. -/
theorem step_far_jalr {rom : Rom} {st : State} {pc tgt : Nat} {rd : Reg}
    (_hrd_t6 : rd ≠ AbiReg.t6)
    (_hrd_s1 : rd ≠ AbiReg.s1)
    (hpc_lt : 4 * (pc + 3) < 2 ^ 64)
    (hst_pc : st.pc = BitVec.ofNat 64 (4 * pc))
    (hrange : farInRange ((tgt : Int) - ((pc + 1 : Nat) : Int)) = true)
    (hrom0 : (rom pc).bind decode = some (.jal AbiReg.t6 (mkJimm 1)))
    (hrom1 : (rom (pc + 1)).bind decode = some (.lui AbiReg.s1 (splitFarOffWords ((tgt : Int) - ((pc + 1 : Nat) : Int))).1))
    (hrom2 : (rom (pc + 2)).bind decode = some (.alu .add AbiReg.t6 AbiReg.t6 AbiReg.s1))
    (hrom3 : (rom (pc + 3)).bind decode = some (.jalr rd AbiReg.t6 (splitFarOffWords ((tgt : Int) - ((pc + 1 : Nat) : Int))).2)) :
    ∃ st1 st2 st3 st4,
      step rom st = .cont st1 ∧
      step rom st1 = .cont st2 ∧
      step rom st2 = .cont st3 ∧
      step rom st3 = .cont st4 ∧
      run rom 4 st = .cont st4 ∧
      st4.pc = BitVec.ofNat 64 (4 * tgt) ∧
      (rd ≠ AbiReg.zero → st4.getReg rd = BitVec.ofNat 64 (4 * (pc + 4))) ∧
      (∀ r, r ≠ rd → r ≠ AbiReg.t6 → r ≠ AbiReg.s1 → st4.getReg r = st.getReg r) ∧
      st4.mem = st.mem := by
  obtain ⟨hd0, ha0, hadd0⟩ := pc_mul4_props (k := pc) (by omega)
  obtain ⟨hd1, ha1, hadd1⟩ := pc_mul4_props (k := pc + 1) (by omega)
  obtain ⟨hd2, ha2, hadd2⟩ := pc_mul4_props (k := pc + 2) (by omega)
  obtain ⟨hd3, ha3, hadd3⟩ := pc_mul4_props (k := pc + 3) hpc_lt
  have h1r : jalInRange (((pc + 1 : Nat) : Int) - (pc : Int)) = true := by
    simp [jalInRange]; omega
  have h1eq : mkJimm 1 = mkJimm (((pc + 1 : Nat) : Int) - (pc : Int)) := by
    congr 1; omega
  let hi20 := (splitFarOffWords ((tgt : Int) - ((pc + 1 : Nat) : Int))).1
  let lo12 := (splitFarOffWords ((tgt : Int) - ((pc + 1 : Nat) : Int))).2
  let st1 : State := { (st.setReg AbiReg.t6 (BitVec.ofNat 64 (4 * (pc + 1)))) with pc := BitVec.ofNat 64 (4 * (pc + 1)) }
  have hs0 : step rom st = .cont st1 := by
    dsimp only [step]
    rw [hst_pc, ha0]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hd0]
    cases hr0 : rom pc with
    | none => rw [hr0] at hrom0; cases hrom0
    | some w0 =>
      rw [hr0] at hrom0
      simp only [Option.bind_some] at hrom0
      simp only [hrom0, execInstr, hst_pc, hadd0, h1eq, pc_add_sextImmJ h1r, st1]
  let st2 : State := { (st1.setReg AbiReg.s1 (sextImmU hi20)) with pc := BitVec.ofNat 64 (4 * (pc + 2)) }
  have hs1 : step rom st1 = .cont st2 := by
    dsimp only [step]
    have hpc1 : st1.pc = BitVec.ofNat 64 (4 * (pc + 1)) := rfl
    rw [hpc1, ha1]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hd1]
    cases hr1 : rom (pc + 1) with
    | none => rw [hr1] at hrom1; cases hrom1
    | some w1 =>
      rw [hr1] at hrom1
      simp only [Option.bind_some] at hrom1
      simp only [hrom1, execInstr, hpc1, hadd1, show pc + 1 + 1 = pc + 2 by omega, st2, hi20]
  have ht6_2 : st2.getReg AbiReg.t6 = BitVec.ofNat 64 (4 * (pc + 1)) := by
    dsimp only [st2]
    change (st1.setReg AbiReg.s1 (sextImmU hi20)).getReg AbiReg.t6 = _
    rw [getReg_setReg_ne (by decide)]
    dsimp only [st1]
    change (st.setReg AbiReg.t6 (BitVec.ofNat 64 (4 * (pc + 1)))).getReg AbiReg.t6 = _
    exact getReg_setReg_eq (by decide) _
  have hs1_2 : st2.getReg AbiReg.s1 = sextImmU hi20 := by
    dsimp only [st2]
    change (st1.setReg AbiReg.s1 (sextImmU hi20)).getReg AbiReg.s1 = _
    exact getReg_setReg_eq (by decide) _
  let st3 : State := { (st2.setReg AbiReg.t6 (BitVec.ofNat 64 (4 * (pc + 1)) + sextImmU hi20)) with pc := BitVec.ofNat 64 (4 * (pc + 3)) }
  have hs2 : step rom st2 = .cont st3 := by
    dsimp only [step]
    have hpc2 : st2.pc = BitVec.ofNat 64 (4 * (pc + 2)) := rfl
    rw [hpc2, ha2]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hd2]
    cases hr2 : rom (pc + 2) with
    | none => rw [hr2] at hrom2; cases hrom2
    | some w2 =>
      rw [hr2] at hrom2
      simp only [Option.bind_some] at hrom2
      simp only [hrom2, execInstr, evalAlu, hpc2, ht6_2, hs1_2, hadd2, show pc + 2 + 1 = pc + 3 by omega, st3]
  have ht6_3 : st3.getReg AbiReg.t6 = BitVec.ofNat 64 (4 * (pc + 1)) + sextImmU hi20 := by
    dsimp only [st3]
    change (st2.setReg AbiReg.t6 _).getReg AbiReg.t6 = _
    exact getReg_setReg_eq (by decide) _
  have htgt_eq : ((BitVec.ofNat 64 (4 * (pc + 1)) + sextImmU hi20 + sextImm12 lo12) &&& ~~~1#64) =
      BitVec.ofNat 64 (4 * tgt) :=
    pc_add_splitFarOffWords (pc := pc + 1) (tgt := tgt) hrange
  let st4 : State := { (st3.setReg rd (st3.pc + 4#64)) with pc := BitVec.ofNat 64 (4 * tgt) }
  have hs3 : step rom st3 = .cont st4 := by
    dsimp only [step]
    have hpc3 : st3.pc = BitVec.ofNat 64 (4 * (pc + 3)) := rfl
    rw [hpc3, ha3]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hd3]
    cases hr3 : rom (pc + 3) with
    | none => rw [hr3] at hrom3; cases hrom3
    | some w3 =>
      rw [hr3] at hrom3
      simp only [Option.bind_some] at hrom3
      simp only [hrom3, execInstr]
      dsimp only [st4]
      rw [ht6_3, show (splitFarOffWords ((tgt : Int) - ((pc + 1 : Nat) : Int))).2 = lo12 from rfl, htgt_eq, hpc3]
  have hmem_eq : st4.mem = st.mem := by
    dsimp only [st4, st3, st2, st1, State.setReg]
    by_cases hrd0 : rd == 0#5 <;> simp [hrd0, AbiReg.t6, AbiReg.s1]
  refine ⟨st1, st2, st3, st4, hs0, hs1, hs2, hs3, ?_, rfl, ?_, ?_, hmem_eq⟩
  · dsimp only [run]; rw [hs0]; dsimp only [run]; rw [hs1]; dsimp only [run]; rw [hs2]; dsimp only [run]; rw [hs3]
  · intro hrd0
    dsimp only [st4]
    change (st3.setReg rd (st3.pc + 4#64)).getReg rd = _
    rw [getReg_setReg_eq hrd0]
    dsimp only [st3]
    rw [hadd3, show pc + 3 + 1 = pc + 4 by omega]
  · intro r hrrd hrt6 hrs1
    dsimp only [st4]
    change (st3.setReg rd _).getReg r = st.getReg r
    rw [getReg_setReg_ne hrrd.symm]
    dsimp only [st3]
    change (st2.setReg AbiReg.t6 _).getReg r = st.getReg r
    rw [getReg_setReg_ne hrt6.symm]
    dsimp only [st2]
    change (st1.setReg AbiReg.s1 _).getReg r = st.getReg r
    rw [getReg_setReg_ne hrs1.symm]
    dsimp only [st1]
    change (st.setReg AbiReg.t6 _).getReg r = st.getReg r
    exact getReg_setReg_ne hrt6.symm _

/-- Execute a not-taken 5-word far branch in 1 cycle (`pc ↦ pc + 5`), touching zero registers or memory. -/
theorem step_far_branch_not_taken {rom : Rom} {st : State} {pc : Nat}
    {op : BranchOp} {rs1 rs2 : Reg}
    (hpc_lt : 4 * (pc + 5) < 2 ^ 64)
    (hst_pc : st.pc = BitVec.ofNat 64 (4 * pc))
    (hcond : evalBranch op (st.getReg rs1) (st.getReg rs2) = false)
    (hrom0 : (rom pc).bind decode = some (.branch (invertBranch op) rs1 rs2 (mkBimm 5))) :
    ∃ st1,
      step rom st = .cont st1 ∧
      run rom 1 st = .cont st1 ∧
      st1.pc = BitVec.ofNat 64 (4 * (pc + 5)) ∧
      st1.regs = st.regs ∧
      st1.mem = st.mem := by
  obtain ⟨hd0, ha0, _⟩ := pc_mul4_props (k := pc) (by omega)
  have hinv : evalBranch (invertBranch op) (st.getReg rs1) (st.getReg rs2) = true := by
    rw [evalBranch_invert, hcond]; rfl
  have h5r : branchInRange (((pc + 5 : Nat) : Int) - (pc : Int)) = true := by
    simp [branchInRange]; omega
  have h5eq : mkBimm 5 = mkBimm (((pc + 5 : Nat) : Int) - (pc : Int)) := by
    congr 1; omega
  have hs0 : step rom st = .cont { st with pc := BitVec.ofNat 64 (4 * (pc + 5)) } := by
    dsimp only [step]
    rw [hst_pc, ha0]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hd0]
    cases hr0 : rom pc with
    | none => rw [hr0] at hrom0; cases hrom0
    | some w0 =>
      rw [hr0] at hrom0
      simp only [Option.bind_some] at hrom0
      simp only [hrom0, execInstr, hinv, ↓reduceIte, hst_pc, h5eq, pc_add_sextImmB h5r]
  exact ⟨_, hs0, by simp [run, hs0], rfl, rfl, rfl⟩

/-- Execute a taken 5-word far branch in 5 cycles (`pc ↦ tgt`), touching only scratch `{t6, s1}`. -/
theorem step_far_branch_taken {rom : Rom} {st : State} {pc tgt : Nat}
    {op : BranchOp} {rs1 rs2 : Reg}
    (hpc_lt : 4 * (pc + 4) < 2 ^ 64)
    (hst_pc : st.pc = BitVec.ofNat 64 (4 * pc))
    (hrange : farInRange ((tgt : Int) - ((pc + 2 : Nat) : Int)) = true)
    (hcond : evalBranch op (st.getReg rs1) (st.getReg rs2) = true)
    (hrom0 : (rom pc).bind decode = some (.branch (invertBranch op) rs1 rs2 (mkBimm 5)))
    (hrom1 : (rom (pc + 1)).bind decode = some (.jal AbiReg.t6 (mkJimm 1)))
    (hrom2 : (rom (pc + 2)).bind decode = some (.lui AbiReg.s1 (splitFarOffWords ((tgt : Int) - ((pc + 2 : Nat) : Int))).1))
    (hrom3 : (rom (pc + 3)).bind decode = some (.alu .add AbiReg.t6 AbiReg.t6 AbiReg.s1))
    (hrom4 : (rom (pc + 4)).bind decode = some (.jalr AbiReg.zero AbiReg.t6 (splitFarOffWords ((tgt : Int) - ((pc + 2 : Nat) : Int))).2)) :
    ∃ st5,
      run rom 5 st = .cont st5 ∧
      st5.pc = BitVec.ofNat 64 (4 * tgt) ∧
      (∀ r, r ≠ AbiReg.t6 → r ≠ AbiReg.s1 → st5.getReg r = st.getReg r) ∧
      st5.mem = st.mem := by
  obtain ⟨hd0, ha0, hadd0⟩ := pc_mul4_props (k := pc) (by omega)
  have hinv : evalBranch (invertBranch op) (st.getReg rs1) (st.getReg rs2) = false := by
    rw [evalBranch_invert, hcond]; rfl
  let st1 : State := { st with pc := BitVec.ofNat 64 (4 * (pc + 1)) }
  have hs0 : step rom st = .cont st1 := by
    dsimp only [step]
    rw [hst_pc, ha0]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hd0]
    cases hr0 : rom pc with
    | none => rw [hr0] at hrom0; cases hrom0
    | some w0 =>
      rw [hr0] at hrom0
      simp only [Option.bind_some] at hrom0
      simp only [hrom0, execInstr, hinv, Bool.false_eq_true, ↓reduceIte, hst_pc, hadd0]
      rfl
  obtain ⟨_, _, _, st5, _, _, _, _, hrun4, hpc5, _, hregs5, hmem5⟩ :=
    step_far_jalr (st := st1) (pc := pc + 1) (tgt := tgt) (rd := AbiReg.zero) (by decide) (by decide)
      (by omega) rfl hrange hrom1 hrom2 hrom3 hrom4
  refine ⟨st5, ?_, hpc5, ?_, hmem5⟩
  · dsimp only [run]; rw [hs0]; exact hrun4
  · intro r hrt6 hrs1
    by_cases hr0 : r = AbiReg.zero
    · subst hr0; simp [State.getReg, AbiReg.zero]
    · exact hregs5 r hr0 hrt6 hrs1

/-! ## 3. Linker Structural & Decode Correctness (`linkFar_word_decode`) -/

theorem farTotalWords_nil : farTotalWords [] = 0 := rfl

private theorem foldl_farWordSize_add (xs : List AsmItem) (n : Nat) :
    xs.foldl (fun acc item => acc + farWordSize item) n = n + farTotalWords xs := by
  induction xs generalizing n with
  | nil => simp [farTotalWords]
  | cons x xs ih =>
    simp only [List.foldl_cons, farTotalWords] at *
    rw [ih (n + farWordSize x), ih (0 + farWordSize x)]
    omega

theorem farTotalWords_cons (x : AsmItem) (xs : List AsmItem) :
    farTotalWords (x :: xs) = farWordSize x + farTotalWords xs := by
  unfold farTotalWords
  simp only [List.foldl_cons, Nat.zero_add]
  exact foldl_farWordSize_add xs (farWordSize x)

theorem farTotalWords_append (xs ys : List AsmItem) :
    farTotalWords (xs ++ ys) = farTotalWords xs + farTotalWords ys := by
  induction xs with
  | nil => simp [farTotalWords_nil]
  | cons x xs ih => simp [farTotalWords_cons, ih, Nat.add_assoc]

private theorem collectFarLabelsGo_preserved (items : List AsmItem) (pc : Nat)
    (acc lm : LabelMap) (h : collectFarLabelsGo items pc acc = .ok lm)
    (name : String) (v : Nat) (hacc : lookupLabel acc name = some v) :
    lookupLabel lm name = some v := by
  induction items generalizing pc acc with
  | nil =>
    simp only [collectFarLabelsGo, Except.ok.injEq] at h
    subst h; exact hacc
  | cons item rest ih =>
    cases item with
    | label n =>
      simp only [collectFarLabelsGo] at h
      cases hlook : lookupLabel acc n with
      | some _ => rw [hlook] at h; cases h
      | none =>
        rw [hlook] at h
        apply ih pc ((n, pc) :: acc) h
        simp only [lookupLabel]
        split
        · next heq =>
          have : n = name := beq_iff_eq.mp heq
          subst this; rw [hlook] at hacc; cases hacc
        · exact hacc
    | _ => exact ih (pc + _) acc h hacc

private theorem collectFarLabelsGo_append (xs ys : List AsmItem) (pc : Nat) (acc lm : LabelMap)
    (h : collectFarLabelsGo (xs ++ ys) pc acc = .ok lm) :
    ∃ mid, collectFarLabelsGo xs pc acc = .ok mid ∧
           collectFarLabelsGo ys (pc + farTotalWords xs) mid = .ok lm := by
  induction xs generalizing pc acc with
  | nil =>
    simp only [List.nil_append, collectFarLabelsGo, farTotalWords_nil, Nat.add_zero] at *
    exact ⟨acc, rfl, h⟩
  | cons x xs ih =>
    cases x with
    | label n =>
      simp only [List.cons_append, collectFarLabelsGo, farTotalWords_cons, farWordSize,
        Nat.zero_add] at *
      cases hlook : lookupLabel acc n with
      | some _ => rw [hlook] at h; cases h
      | none =>
        rw [hlook] at h
        exact ih pc ((n, pc) :: acc) h
    | _ =>
      simp only [List.cons_append, collectFarLabelsGo, farTotalWords_cons] at *
      obtain ⟨mid, h1, h2⟩ := ih (pc + _) acc h
      refine ⟨mid, h1, ?_⟩
      simpa [Nat.add_assoc] using h2

theorem collectFarLabels_label_at (pre post : List AsmItem) (name : String) (lm : LabelMap)
    (h : collectFarLabels (pre ++ [.label name] ++ post) = .ok lm) :
    lookupLabel lm name = some (farTotalWords pre) := by
  unfold collectFarLabels at h
  rw [List.append_assoc] at h
  obtain ⟨mid, _, hpost⟩ := collectFarLabelsGo_append pre ([.label name] ++ post) 0 [] lm h
  simp only [Nat.zero_add, List.singleton_append, collectFarLabelsGo] at hpost
  cases hlook : lookupLabel mid name with
  | some _ => rw [hlook] at hpost; cases hpost
  | none =>
    rw [hlook] at hpost
    apply collectFarLabelsGo_preserved post (farTotalWords pre) ((name, farTotalWords pre) :: mid) lm hpost
    simp [lookupLabel]

theorem resolveFarItem_length {lm : LabelMap} {pc : Nat} {item : AsmItem} {is : List Instr}
    (h : resolveFarItem lm pc item = .ok is) : is.length = farWordSize item := by
  cases item <;> simp only [resolveFarItem, farWordSize] at h ⊢
  · cases h; rfl
  · cases h; rfl
  · rename_i target
    cases hlook : lookupLabel lm target <;> simp [hlook] at h
    split at h <;> cases h; simp [farInstrsFor]
  · rename_i target
    cases hlook : lookupLabel lm target <;> simp [hlook] at h
    split at h <;> cases h; simp [farInstrsFor]
  · rename_i op rs1 rs2 target
    cases hlook : lookupLabel lm target <;> simp [hlook] at h
    split at h <;> cases h; simp [farInstrsFor]
  · rename_i op rs1 rs2 target
    cases hlook : lookupLabel lm target <;> simp [hlook] at h
    split at h <;> cases h; simp [farInstrsFor]

private theorem pushEncoded_eq_append (acc : Array (BitVec 32)) (is : List Instr) :
    pushEncoded acc is = acc ++ (is.map encode).toArray := by
  induction is generalizing acc with
  | nil => simp [pushEncoded]
  | cons i is ih =>
    dsimp only [pushEncoded]
    rw [ih, List.map_cons, Array.push_eq_append, Array.append_assoc, ← List.toArray_cons]

private theorem resolveFarWordsGo_append_acc (lm : LabelMap) (pc : Nat) (items : List AsmItem)
    (acc arr : Array (BitVec 32)) :
    resolveFarWordsGo lm pc items acc = .ok arr ↔
      ∃ tail, resolveFarWordsGo lm pc items #[] = .ok tail ∧ arr = acc ++ tail := by
  induction items generalizing pc acc arr with
  | nil =>
    simp only [resolveFarWordsGo, Except.ok.injEq]
    constructor
    · intro h; exact ⟨#[], rfl, by simp [h]⟩
    · rintro ⟨tail, h1, h2⟩; cases h1; simp [h2]
  | cons item rest ih =>
    simp only [resolveFarWordsGo]
    cases hitem : resolveFarItem lm pc item with
    | error e =>
      simp only []
      constructor
      · intro h; cases h
      · rintro ⟨tail, h1, _⟩; cases h1
    | ok is =>
      simp only []
      rw [ih (pc + farWordSize item) (pushEncoded acc is) arr]
      constructor
      · rintro ⟨tail, h1, h2⟩
        have hres : resolveFarWordsGo lm (pc + farWordSize item) rest (pushEncoded #[] is) =
            .ok (pushEncoded #[] is ++ tail) :=
          (ih (pc + farWordSize item) (pushEncoded #[] is) (pushEncoded #[] is ++ tail)).mpr ⟨tail, h1, rfl⟩
        refine ⟨pushEncoded #[] is ++ tail, by simpa using hres, ?_⟩
        rw [h2, pushEncoded_eq_append, pushEncoded_eq_append, Array.empty_append, Array.append_assoc]
      · rintro ⟨tail, h1, h2⟩
        obtain ⟨tail', h1', htail⟩ := (ih (pc + farWordSize item) (pushEncoded #[] is) tail).mp (by simpa using h1)
        refine ⟨tail', h1', ?_⟩
        rw [h2, htail, pushEncoded_eq_append, pushEncoded_eq_append, Array.empty_append, Array.append_assoc]

private theorem resolveFarWordsGo_size (lm : LabelMap) (pc : Nat) (items : List AsmItem)
    (acc arr : Array (BitVec 32)) (h : resolveFarWordsGo lm pc items acc = .ok arr) :
    arr.size = acc.size + farTotalWords items := by
  induction items generalizing pc acc with
  | nil =>
    simp only [resolveFarWordsGo, Except.ok.injEq] at h
    subst h; simp [farTotalWords_nil]
  | cons item rest ih =>
    simp only [resolveFarWordsGo] at h
    cases hitem : resolveFarItem lm pc item with
    | error e => rw [hitem] at h; cases h
    | ok is =>
      rw [hitem] at h
      have hlen := resolveFarItem_length hitem
      have ih' := ih (pc + farWordSize item) (pushEncoded acc is) h
      rw [pushEncoded_eq_append, Array.size_append] at ih'
      have hsz : (is.map encode).toArray.size = is.length := by simp
      rw [hsz, hlen] at ih'
      rw [farTotalWords_cons]
      omega

private theorem resolveFarWordsGo_split (lm : LabelMap) (pc : Nat) (xs ys : List AsmItem)
    (acc arr : Array (BitVec 32)) (h : resolveFarWordsGo lm pc (xs ++ ys) acc = .ok arr) :
    ∃ a1 a2, resolveFarWordsGo lm pc xs #[] = .ok a1 ∧
             resolveFarWordsGo lm (pc + farTotalWords xs) ys #[] = .ok a2 ∧
             a1.size = farTotalWords xs ∧
             arr = acc ++ a1 ++ a2 := by
  induction xs generalizing pc acc with
  | nil =>
    simp only [List.nil_append, farTotalWords_nil, Nat.add_zero] at *
    rw [resolveFarWordsGo_append_acc] at h
    obtain ⟨a2, ha2, harr⟩ := h
    exact ⟨#[], a2, rfl, ha2, rfl, by simpa using harr⟩
  | cons x xs ih =>
    simp only [List.cons_append, resolveFarWordsGo, farTotalWords_cons] at h ⊢
    cases hx : resolveFarItem lm pc x with
    | error e => rw [hx] at h; cases h
    | ok is =>
      rw [hx] at h
      obtain ⟨a1, a2, h1, h2, hsz, harr⟩ := ih (pc + farWordSize x) (pushEncoded acc is) h
      have hlen := resolveFarItem_length hx
      refine ⟨pushEncoded #[] is ++ a1, a2,
        (resolveFarWordsGo_append_acc lm (pc + farWordSize x) xs (pushEncoded #[] is) (pushEncoded #[] is ++ a1)).mpr ⟨a1, h1, rfl⟩,
        ?_, ?_, ?_⟩
      · simpa [Nat.add_assoc] using h2
      · rw [pushEncoded_eq_append, Array.empty_append, Array.size_append]
        simp [hlen, hsz]
      · rw [harr, pushEncoded_eq_append, pushEncoded_eq_append, Array.empty_append]
        simp [Array.append_assoc]

private theorem resolveFarWordsGo_singleton (lm : LabelMap) (pc : Nat) (it : AsmItem)
    (a : Array (BitVec 32)) (h : resolveFarWordsGo lm pc [it] #[] = .ok a) :
    ∃ is, resolveFarItem lm pc it = .ok is ∧ a = (is.map encode).toArray := by
  simp only [resolveFarWordsGo] at h
  cases hit : resolveFarItem lm pc it with
  | error e => rw [hit] at h; cases h
  | ok is =>
    rw [hit] at h
    simp only [Except.ok.injEq] at h
    rw [pushEncoded_eq_append, Array.empty_append] at h
    exact ⟨is, rfl, h.symm⟩

/-- Decoded specification of one lowered `AsmItem` at word offset `pc` inside `linkFar` output. -/
def FarItemDecodedAt (code : Array (BitVec 32)) (labels : LabelMap) (pc : Nat) : AsmItem → Prop
  | .label name =>
    lookupLabel labels name = some pc
  | .instr inst =>
    (code[pc]?).bind decode = some inst
  | .j target =>
    ∃ tgt, lookupLabel labels target = some tgt ∧
      farInRange ((tgt : Int) - ((pc + 1 : Nat) : Int)) = true ∧
      let (hi20, lo12) := splitFarOffWords ((tgt : Int) - ((pc + 1 : Nat) : Int))
      (code[pc]?).bind decode = some (.jal AbiReg.t6 (mkJimm 1)) ∧
      (code[pc + 1]?).bind decode = some (.lui AbiReg.s1 hi20) ∧
      (code[pc + 2]?).bind decode = some (.alu .add AbiReg.t6 AbiReg.t6 AbiReg.s1) ∧
      (code[pc + 3]?).bind decode = some (.jalr AbiReg.zero AbiReg.t6 lo12)
  | .call target =>
    ∃ tgt, lookupLabel labels target = some tgt ∧
      farInRange ((tgt : Int) - ((pc + 1 : Nat) : Int)) = true ∧
      let (hi20, lo12) := splitFarOffWords ((tgt : Int) - ((pc + 1 : Nat) : Int))
      (code[pc]?).bind decode = some (.jal AbiReg.t6 (mkJimm 1)) ∧
      (code[pc + 1]?).bind decode = some (.lui AbiReg.s1 hi20) ∧
      (code[pc + 2]?).bind decode = some (.alu .add AbiReg.t6 AbiReg.t6 AbiReg.s1) ∧
      (code[pc + 3]?).bind decode = some (.jalr AbiReg.ra AbiReg.t6 lo12)
  | .br op rs1 rs2 target =>
    ∃ tgt, lookupLabel labels target = some tgt ∧
      farInRange ((tgt : Int) - ((pc + 2 : Nat) : Int)) = true ∧
      let (hi20, lo12) := splitFarOffWords ((tgt : Int) - ((pc + 2 : Nat) : Int))
      (code[pc]?).bind decode = some (.branch (invertBranch op) rs1 rs2 (mkBimm 5)) ∧
      (code[pc + 1]?).bind decode = some (.jal AbiReg.t6 (mkJimm 1)) ∧
      (code[pc + 2]?).bind decode = some (.lui AbiReg.s1 hi20) ∧
      (code[pc + 3]?).bind decode = some (.alu .add AbiReg.t6 AbiReg.t6 AbiReg.s1) ∧
      (code[pc + 4]?).bind decode = some (.jalr AbiReg.zero AbiReg.t6 lo12)
  | .brLong op rs1 rs2 target =>
    ∃ tgt, lookupLabel labels target = some tgt ∧
      farInRange ((tgt : Int) - ((pc + 2 : Nat) : Int)) = true ∧
      let (hi20, lo12) := splitFarOffWords ((tgt : Int) - ((pc + 2 : Nat) : Int))
      (code[pc]?).bind decode = some (.branch (invertBranch op) rs1 rs2 (mkBimm 5)) ∧
      (code[pc + 1]?).bind decode = some (.jal AbiReg.t6 (mkJimm 1)) ∧
      (code[pc + 2]?).bind decode = some (.lui AbiReg.s1 hi20) ∧
      (code[pc + 3]?).bind decode = some (.alu .add AbiReg.t6 AbiReg.t6 AbiReg.s1) ∧
      (code[pc + 4]?).bind decode = some (.jalr AbiReg.zero AbiReg.t6 lo12)

private theorem array_getElem?_append_middle {α : Type} (a b c : Array α) (i : Nat)
    (hi : i < b.size) :
    (a ++ b ++ c)[a.size + i]? = some b[i] := by
  have h1 : a.size + i < (a ++ b).size := by simp [hi]
  rw [Array.getElem?_append_left h1, Array.getElem?_append_right (by omega)]
  simp [hi]

theorem linkFarSpec_size {items : List AsmItem} {code : Array (BitVec 32)} {labels : LabelMap}
    (hlink : linkFarSpec items = .ok (code, labels)) :
    code.size = farTotalWords items := by
  simp only [linkFarSpec, bind, Except.bind] at hlink
  cases hcol : collectFarLabels items with
  | error e => rw [hcol] at hlink; cases hlink
  | ok lm =>
    rw [hcol] at hlink; dsimp only at hlink
    cases hres : resolveFarWordsGo lm 0 items #[] with
    | error e => rw [hres] at hlink; cases hlink
    | ok ws =>
      rw [hres] at hlink; dsimp only at hlink
      simp only [Except.pure, pure, Except.ok.injEq, Prod.mk.injEq] at hlink
      rcases hlink with ⟨hweq, _⟩
      subst ws
      simpa using resolveFarWordsGo_size lm 0 items #[] code hres

theorem linkFar_size {items : List AsmItem} {code : Array (BitVec 32)}
    (hlink : linkFar items = .ok code) :
    code.size = farTotalWords items := by
  obtain ⟨_, hspec⟩ := linkFar_ok_spec hlink
  exact linkFarSpec_size hspec

theorem linkFarSpec_item_spec (pre : List AsmItem) (it : AsmItem) (post : List AsmItem)
    (code : Array (BitVec 32)) (labels : LabelMap)
    (hlink : linkFarSpec (pre ++ [it] ++ post) = .ok (code, labels)) :
    FarItemDecodedAt code labels (farTotalWords pre) it := by
  simp only [linkFarSpec, bind, Except.bind] at hlink
  cases hcol : collectFarLabels (pre ++ [it] ++ post) with
  | error e => rw [hcol] at hlink; cases hlink
  | ok lm =>
    rw [hcol] at hlink; dsimp only at hlink
    cases hres : resolveFarWordsGo lm 0 (pre ++ [it] ++ post) #[] with
    | error e => rw [hres] at hlink; cases hlink
    | ok ws =>
      rw [hres] at hlink; dsimp only at hlink
      simp only [Except.pure, pure, Except.ok.injEq, Prod.mk.injEq] at hlink
      rcases hlink with ⟨hweq, hleq⟩
      subst ws; subst lm
      rw [List.append_assoc] at hres
      obtain ⟨a1, a23, _, h23, ha1sz, hws⟩ :=
        resolveFarWordsGo_split labels 0 pre ([it] ++ post) #[] code hres
      simp only [Nat.zero_add] at h23
      obtain ⟨a2, a3, h2, _, _, ha23⟩ :=
        resolveFarWordsGo_split labels (farTotalWords pre) [it] post #[] a23 h23
      have hfull : code = a1 ++ a2 ++ a3 := by
        rw [hws, ha23]; simp [Array.append_assoc]
      have hget : ∀ (j : Nat) (hj : j < a2.size),
          code[farTotalWords pre + j]? = some a2[j] := by
        intro j hj
        rw [hfull, ← ha1sz]
        exact array_getElem?_append_middle a1 a2 a3 j hj
      obtain ⟨is, his, rfl⟩ := resolveFarWordsGo_singleton labels (farTotalWords pre) it a2 h2
      cases it with
      | label name =>
        exact collectFarLabels_label_at pre post name labels hcol
      | instr inst =>
        simp only [resolveFarItem, Except.ok.injEq] at his
        subst his
        have hw := hget 0 (by simp)
        simp only [Nat.add_zero] at hw
        simp only [FarItemDecodedAt, hw, Option.bind_some, List.map_cons,
          List.getElem_toArray, List.getElem_cons_zero, decode_encode]
      | j target =>
        simp only [resolveFarItem] at his
        cases hlook : lookupLabel labels target with
        | none => rw [hlook] at his; cases his
        | some tgt =>
          rw [hlook] at his
          by_cases hrange : farInRange ((tgt : Int) - ((farTotalWords pre + 1 : Nat) : Int)) = true
          · simp only [hrange, ↓reduceIte, Except.ok.injEq] at his
            subst his
            have hw0 := hget 0 (by simp [farInstrsFor])
            have hw1 := hget 1 (by simp [farInstrsFor])
            have hw2 := hget 2 (by simp [farInstrsFor])
            have hw3 := hget 3 (by simp [farInstrsFor])
            simp only [Nat.add_zero] at hw0
            refine ⟨tgt, hlook, hrange, ?_, ?_, ?_, ?_⟩
            · simp only [hw0, Option.bind_some, farInstrsFor, List.map_cons, List.getElem_toArray,
                List.getElem_cons_zero, decode_encode]
            · simp only [hw1, Option.bind_some, farInstrsFor, List.map_cons, List.getElem_toArray,
                List.getElem_cons_succ, List.getElem_cons_zero, decode_encode]; rfl
            · simp only [hw2, Option.bind_some, farInstrsFor, List.map_cons, List.getElem_toArray,
                List.getElem_cons_succ, List.getElem_cons_zero, decode_encode]
            · simp only [hw3, Option.bind_some, farInstrsFor, List.map_cons, List.getElem_toArray,
                List.getElem_cons_succ, List.getElem_cons_zero, decode_encode]; rfl
          · simp only [hrange] at his; cases his
      | call target =>
        simp only [resolveFarItem] at his
        cases hlook : lookupLabel labels target with
        | none => rw [hlook] at his; cases his
        | some tgt =>
          rw [hlook] at his
          by_cases hrange : farInRange ((tgt : Int) - ((farTotalWords pre + 1 : Nat) : Int)) = true
          · simp only [hrange, ↓reduceIte, Except.ok.injEq] at his
            subst his
            have hw0 := hget 0 (by simp [farInstrsFor])
            have hw1 := hget 1 (by simp [farInstrsFor])
            have hw2 := hget 2 (by simp [farInstrsFor])
            have hw3 := hget 3 (by simp [farInstrsFor])
            simp only [Nat.add_zero] at hw0
            refine ⟨tgt, hlook, hrange, ?_, ?_, ?_, ?_⟩
            · simp only [hw0, Option.bind_some, farInstrsFor, List.map_cons, List.getElem_toArray,
                List.getElem_cons_zero, decode_encode]
            · simp only [hw1, Option.bind_some, farInstrsFor, List.map_cons, List.getElem_toArray,
                List.getElem_cons_succ, List.getElem_cons_zero, decode_encode]; rfl
            · simp only [hw2, Option.bind_some, farInstrsFor, List.map_cons, List.getElem_toArray,
                List.getElem_cons_succ, List.getElem_cons_zero, decode_encode]
            · simp only [hw3, Option.bind_some, farInstrsFor, List.map_cons, List.getElem_toArray,
                List.getElem_cons_succ, List.getElem_cons_zero, decode_encode]; rfl
          · simp only [hrange] at his; cases his
      | br op rs1 rs2 target =>
        simp only [resolveFarItem] at his
        cases hlook : lookupLabel labels target with
        | none => rw [hlook] at his; cases his
        | some tgt =>
          rw [hlook] at his
          by_cases hrange : farInRange ((tgt : Int) - ((farTotalWords pre + 2 : Nat) : Int)) = true
          · simp only [hrange, ↓reduceIte, Except.ok.injEq] at his
            subst his
            have hw0 := hget 0 (by simp [farInstrsFor])
            have hw1 := hget 1 (by simp [farInstrsFor])
            have hw2 := hget 2 (by simp [farInstrsFor])
            have hw3 := hget 3 (by simp [farInstrsFor])
            have hw4 := hget 4 (by simp [farInstrsFor])
            simp only [Nat.add_zero] at hw0
            refine ⟨tgt, hlook, hrange, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [hw0, Option.bind_some, farInstrsFor, List.map_cons, List.getElem_toArray,
                List.getElem_cons_zero, decode_encode]
            · simp only [hw1, Option.bind_some, farInstrsFor, List.map_cons, List.getElem_toArray,
                List.getElem_cons_succ, List.getElem_cons_zero, decode_encode]
            · simp only [hw2, Option.bind_some, farInstrsFor, List.map_cons, List.getElem_toArray,
                List.getElem_cons_succ, List.getElem_cons_zero, decode_encode]; rfl
            · simp only [hw3, Option.bind_some, farInstrsFor, List.map_cons, List.getElem_toArray,
                List.getElem_cons_succ, List.getElem_cons_zero, decode_encode]
            · simp only [hw4, Option.bind_some, farInstrsFor, List.map_cons, List.getElem_toArray,
                List.getElem_cons_succ, List.getElem_cons_zero, decode_encode]; rfl
          · simp only [hrange] at his; cases his
      | brLong op rs1 rs2 target =>
        simp only [resolveFarItem] at his
        cases hlook : lookupLabel labels target with
        | none => rw [hlook] at his; cases his
        | some tgt =>
          rw [hlook] at his
          by_cases hrange : farInRange ((tgt : Int) - ((farTotalWords pre + 2 : Nat) : Int)) = true
          · simp only [hrange, ↓reduceIte, Except.ok.injEq] at his
            subst his
            have hw0 := hget 0 (by simp [farInstrsFor])
            have hw1 := hget 1 (by simp [farInstrsFor])
            have hw2 := hget 2 (by simp [farInstrsFor])
            have hw3 := hget 3 (by simp [farInstrsFor])
            have hw4 := hget 4 (by simp [farInstrsFor])
            simp only [Nat.add_zero] at hw0
            refine ⟨tgt, hlook, hrange, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [hw0, Option.bind_some, farInstrsFor, List.map_cons, List.getElem_toArray,
                List.getElem_cons_zero, decode_encode]
            · simp only [hw1, Option.bind_some, farInstrsFor, List.map_cons, List.getElem_toArray,
                List.getElem_cons_succ, List.getElem_cons_zero, decode_encode]
            · simp only [hw2, Option.bind_some, farInstrsFor, List.map_cons, List.getElem_toArray,
                List.getElem_cons_succ, List.getElem_cons_zero, decode_encode]; rfl
            · simp only [hw3, Option.bind_some, farInstrsFor, List.map_cons, List.getElem_toArray,
                List.getElem_cons_succ, List.getElem_cons_zero, decode_encode]
            · simp only [hw4, Option.bind_some, farInstrsFor, List.map_cons, List.getElem_toArray,
                List.getElem_cons_succ, List.getElem_cons_zero, decode_encode]; rfl
          · simp only [hrange] at his; cases his

theorem exists_far_split_at_word (items : List AsmItem) (k : Nat) (hk : k < farTotalWords items) :
    ∃ pre it post, items = pre ++ [it] ++ post ∧
      farTotalWords pre ≤ k ∧ k < farTotalWords pre + farWordSize it := by
  induction items generalizing k with
  | nil => simp [farTotalWords_nil] at hk
  | cons x xs ih =>
    rw [farTotalWords_cons] at hk
    by_cases hlt : k < farWordSize x
    · exact ⟨[], x, xs, rfl, by simp [farTotalWords_nil], by simp [farTotalWords_nil, hlt]⟩
    · have hge : farWordSize x ≤ k := by omega
      obtain ⟨pre, it, post, hsplit, hlo, hhi⟩ := ih (k - farWordSize x) (by omega)
      refine ⟨x :: pre, it, post, ?_, ?_, ?_⟩
      · simp [hsplit]
      · rw [farTotalWords_cons]; omega
      · rw [farTotalWords_cons]; omega

/-- Universal word-level theorem for fast `linkFar`: every word `k < code.size` is owned by an
    `AsmItem` in `items` at `pre ++ [it] ++ post` satisfying `FarItemDecodedAt code labels`. -/
theorem linkFar_word_decode (items : List AsmItem) (code : Array (BitVec 32))
    (hlink : linkFar items = .ok code) :
    ∃ labels, linkFarSpec items = .ok (code, labels) ∧
      code.size = farTotalWords items ∧
      (∀ k, k < code.size →
        ∃ pre it post, items = pre ++ [it] ++ post ∧
          farTotalWords pre ≤ k ∧ k < farTotalWords pre + farWordSize it ∧
          FarItemDecodedAt code labels (farTotalWords pre) it) := by
  obtain ⟨labels, hspec⟩ := linkFar_ok_spec hlink
  have hsz := linkFarSpec_size hspec
  refine ⟨labels, hspec, hsz, fun k hk => ?_⟩
  rw [hsz] at hk
  obtain ⟨pre, it, post, hsplit, hlo, hhi⟩ := exists_far_split_at_word items k hk
  refine ⟨pre, it, post, hsplit, hlo, hhi, ?_⟩
  rw [hsplit] at hspec
  exact linkFarSpec_item_spec pre it post code labels hspec

/-! ## 4. Direct Item Execution Lemmas From Linked `code` (`romOfArray code`) -/

theorem linkFar_step_j (pre : List AsmItem) (target : String) (post : List AsmItem)
    (code : Array (BitVec 32)) (hlink : linkFar (pre ++ [.j target] ++ post) = .ok code)
    (st : State) (hpc_lt : 4 * (farTotalWords pre + 3) < 2 ^ 64)
    (hst_pc : st.pc = BitVec.ofNat 64 (4 * farTotalWords pre)) :
    ∃ labels tgt st4,
      lookupLabel labels target = some tgt ∧
      run (romOfArray code) 4 st = .cont st4 ∧
      st4.pc = BitVec.ofNat 64 (4 * tgt) ∧
      (∀ r, r ≠ AbiReg.t6 → r ≠ AbiReg.s1 → st4.getReg r = st.getReg r) ∧
      st4.mem = st.mem := by
  obtain ⟨labels, hspec⟩ := linkFar_ok_spec hlink
  obtain ⟨tgt, hlook, hrange, hd0, hd1, hd2, hd3⟩ :=
    linkFarSpec_item_spec pre (.j target) post code labels hspec
  obtain ⟨_, _, _, st4, _, _, _, _, hrun, hpc4, _, hregs4, hmem4⟩ :=
    step_far_jalr (rom := romOfArray code) (st := st) (pc := farTotalWords pre) (tgt := tgt)
      (rd := AbiReg.zero) (by decide) (by decide) hpc_lt hst_pc hrange hd0 hd1 hd2 hd3
  refine ⟨labels, tgt, st4, hlook, hrun, hpc4, ?_, hmem4⟩
  intro r hrt6 hrs1
  by_cases hrz : r = AbiReg.zero
  · subst hrz; simp [State.getReg, AbiReg.zero]
  · exact hregs4 r hrz hrt6 hrs1

theorem linkFar_step_call (pre : List AsmItem) (target : String) (post : List AsmItem)
    (code : Array (BitVec 32)) (hlink : linkFar (pre ++ [.call target] ++ post) = .ok code)
    (st : State) (hpc_lt : 4 * (farTotalWords pre + 3) < 2 ^ 64)
    (hst_pc : st.pc = BitVec.ofNat 64 (4 * farTotalWords pre)) :
    ∃ labels tgt st4,
      lookupLabel labels target = some tgt ∧
      run (romOfArray code) 4 st = .cont st4 ∧
      st4.pc = BitVec.ofNat 64 (4 * tgt) ∧
      st4.getReg AbiReg.ra = BitVec.ofNat 64 (4 * (farTotalWords pre + 4)) ∧
      (∀ r, r ≠ AbiReg.ra → r ≠ AbiReg.t6 → r ≠ AbiReg.s1 → st4.getReg r = st.getReg r) ∧
      st4.mem = st.mem := by
  obtain ⟨labels, hspec⟩ := linkFar_ok_spec hlink
  obtain ⟨tgt, hlook, hrange, hd0, hd1, hd2, hd3⟩ :=
    linkFarSpec_item_spec pre (.call target) post code labels hspec
  obtain ⟨_, _, _, st4, _, _, _, _, hrun, hpc4, hra, hregs4, hmem4⟩ :=
    step_far_jalr (rom := romOfArray code) (st := st) (pc := farTotalWords pre) (tgt := tgt)
      (rd := AbiReg.ra) (by decide) (by decide) hpc_lt hst_pc hrange hd0 hd1 hd2 hd3
  exact ⟨labels, tgt, st4, hlook, hrun, hpc4, hra (by decide), hregs4, hmem4⟩

theorem linkFar_step_br_taken (pre : List AsmItem) (op : BranchOp) (rs1 rs2 : Reg)
    (target : String) (post : List AsmItem)
    (code : Array (BitVec 32)) (hlink : linkFar (pre ++ [.br op rs1 rs2 target] ++ post) = .ok code)
    (st : State) (hpc_lt : 4 * (farTotalWords pre + 4) < 2 ^ 64)
    (hst_pc : st.pc = BitVec.ofNat 64 (4 * farTotalWords pre))
    (hcond : evalBranch op (st.getReg rs1) (st.getReg rs2) = true) :
    ∃ labels tgt st5,
      lookupLabel labels target = some tgt ∧
      run (romOfArray code) 5 st = .cont st5 ∧
      st5.pc = BitVec.ofNat 64 (4 * tgt) ∧
      (∀ r, r ≠ AbiReg.t6 → r ≠ AbiReg.s1 → st5.getReg r = st.getReg r) ∧
      st5.mem = st.mem := by
  obtain ⟨labels, hspec⟩ := linkFar_ok_spec hlink
  obtain ⟨tgt, hlook, hrange, hd0, hd1, hd2, hd3, hd4⟩ :=
    linkFarSpec_item_spec pre (.br op rs1 rs2 target) post code labels hspec
  obtain ⟨st5, hrun, hpc5, hregs5, hmem5⟩ :=
    step_far_branch_taken (rom := romOfArray code) (st := st) (pc := farTotalWords pre) (tgt := tgt)
      (op := op) (rs1 := rs1) (rs2 := rs2) hpc_lt hst_pc hrange hcond hd0 hd1 hd2 hd3 hd4
  exact ⟨labels, tgt, st5, hlook, hrun, hpc5, hregs5, hmem5⟩

theorem linkFar_step_br_not_taken (pre : List AsmItem) (op : BranchOp) (rs1 rs2 : Reg)
    (target : String) (post : List AsmItem)
    (code : Array (BitVec 32)) (hlink : linkFar (pre ++ [.br op rs1 rs2 target] ++ post) = .ok code)
    (st : State) (hpc_lt : 4 * (farTotalWords pre + 5) < 2 ^ 64)
    (hst_pc : st.pc = BitVec.ofNat 64 (4 * farTotalWords pre))
    (hcond : evalBranch op (st.getReg rs1) (st.getReg rs2) = false) :
    ∃ st1,
      step (romOfArray code) st = .cont st1 ∧
      run (romOfArray code) 1 st = .cont st1 ∧
      st1.pc = BitVec.ofNat 64 (4 * (farTotalWords pre + 5)) ∧
      st1.regs = st.regs ∧
      st1.mem = st.mem := by
  obtain ⟨labels, hspec⟩ := linkFar_ok_spec hlink
  obtain ⟨_, _, _, hd0, _, _, _, _⟩ :=
    linkFarSpec_item_spec pre (.br op rs1 rs2 target) post code labels hspec
  exact step_far_branch_not_taken (rom := romOfArray code) (st := st) (pc := farTotalWords pre)
    hpc_lt hst_pc hcond hd0

theorem linkFar_step_brLong_taken (pre : List AsmItem) (op : BranchOp) (rs1 rs2 : Reg)
    (target : String) (post : List AsmItem)
    (code : Array (BitVec 32)) (hlink : linkFar (pre ++ [.brLong op rs1 rs2 target] ++ post) = .ok code)
    (st : State) (hpc_lt : 4 * (farTotalWords pre + 4) < 2 ^ 64)
    (hst_pc : st.pc = BitVec.ofNat 64 (4 * farTotalWords pre))
    (hcond : evalBranch op (st.getReg rs1) (st.getReg rs2) = true) :
    ∃ labels tgt st5,
      lookupLabel labels target = some tgt ∧
      run (romOfArray code) 5 st = .cont st5 ∧
      st5.pc = BitVec.ofNat 64 (4 * tgt) ∧
      (∀ r, r ≠ AbiReg.t6 → r ≠ AbiReg.s1 → st5.getReg r = st.getReg r) ∧
      st5.mem = st.mem := by
  obtain ⟨labels, hspec⟩ := linkFar_ok_spec hlink
  obtain ⟨tgt, hlook, hrange, hd0, hd1, hd2, hd3, hd4⟩ :=
    linkFarSpec_item_spec pre (.brLong op rs1 rs2 target) post code labels hspec
  obtain ⟨st5, hrun, hpc5, hregs5, hmem5⟩ :=
    step_far_branch_taken (rom := romOfArray code) (st := st) (pc := farTotalWords pre) (tgt := tgt)
      (op := op) (rs1 := rs1) (rs2 := rs2) hpc_lt hst_pc hrange hcond hd0 hd1 hd2 hd3 hd4
  exact ⟨labels, tgt, st5, hlook, hrun, hpc5, hregs5, hmem5⟩

theorem linkFar_step_brLong_not_taken (pre : List AsmItem) (op : BranchOp) (rs1 rs2 : Reg)
    (target : String) (post : List AsmItem)
    (code : Array (BitVec 32)) (hlink : linkFar (pre ++ [.brLong op rs1 rs2 target] ++ post) = .ok code)
    (st : State) (hpc_lt : 4 * (farTotalWords pre + 5) < 2 ^ 64)
    (hst_pc : st.pc = BitVec.ofNat 64 (4 * farTotalWords pre))
    (hcond : evalBranch op (st.getReg rs1) (st.getReg rs2) = false) :
    ∃ st1,
      step (romOfArray code) st = .cont st1 ∧
      run (romOfArray code) 1 st = .cont st1 ∧
      st1.pc = BitVec.ofNat 64 (4 * (farTotalWords pre + 5)) ∧
      st1.regs = st.regs ∧
      st1.mem = st.mem := by
  obtain ⟨labels, hspec⟩ := linkFar_ok_spec hlink
  obtain ⟨_, _, _, hd0, _, _, _, _⟩ :=
    linkFarSpec_item_spec pre (.brLong op rs1 rs2 target) post code labels hspec
  exact step_far_branch_not_taken (rom := romOfArray code) (st := st) (pc := farTotalWords pre)
    hpc_lt hst_pc hcond hd0

theorem linkFar_step_instr (pre : List AsmItem) (inst : Instr) (post : List AsmItem)
    (code : Array (BitVec 32)) (hlink : linkFar (pre ++ [.instr inst] ++ post) = .ok code)
    (st : State) (hpc_lt : 4 * farTotalWords pre < 2 ^ 64)
    (hst_pc : st.pc = BitVec.ofNat 64 (4 * farTotalWords pre)) :
    step (romOfArray code) st = execInstr st inst := by
  obtain ⟨labels, hspec⟩ := linkFar_ok_spec hlink
  have hd0 := linkFarSpec_item_spec pre (.instr inst) post code labels hspec
  dsimp only [FarItemDecodedAt] at hd0
  obtain ⟨hd, ha, _⟩ := pc_mul4_props (k := farTotalWords pre) hpc_lt
  dsimp only [step]
  rw [hst_pc, ha]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hd]
  change (romOfArray code (farTotalWords pre)).bind decode = some inst at hd0
  cases hr : romOfArray code (farTotalWords pre) with
  | none => rw [hr] at hd0; cases hd0
  | some w =>
    rw [hr] at hd0
    simp only [Option.bind_some] at hd0
    simp [hd0]

/--
info: 'ConAgua.RISCV.Linker.linkFar_eq_linkFarSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms linkFar_eq_linkFarSpec

/--
info: 'ConAgua.RISCV.Linker.pc_add_splitFarOffWords' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pc_add_splitFarOffWords

/--
info: 'ConAgua.RISCV.Linker.step_far_jalr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms step_far_jalr

/--
info: 'ConAgua.RISCV.Linker.step_far_branch_taken' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms step_far_branch_taken

/--
info: 'ConAgua.RISCV.Linker.step_far_branch_not_taken' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms step_far_branch_not_taken

/--
info: 'ConAgua.RISCV.Linker.linkFar_word_decode' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms linkFar_word_decode

/--
info: 'ConAgua.RISCV.Linker.linkFar_step_j' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms linkFar_step_j

/--
info: 'ConAgua.RISCV.Linker.linkFar_step_call' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms linkFar_step_call

/--
info: 'ConAgua.RISCV.Linker.linkFar_step_br_taken' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms linkFar_step_br_taken

/--
info: 'ConAgua.RISCV.Linker.linkFar_step_br_not_taken' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms linkFar_step_br_not_taken

/--
info: 'ConAgua.RISCV.Linker.linkFar_step_brLong_taken' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms linkFar_step_brLong_taken

/--
info: 'ConAgua.RISCV.Linker.linkFar_step_brLong_not_taken' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms linkFar_step_brLong_not_taken

/--
info: 'ConAgua.RISCV.Linker.linkFar_step_instr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms linkFar_step_instr

end ConAgua.RISCV.Linker
