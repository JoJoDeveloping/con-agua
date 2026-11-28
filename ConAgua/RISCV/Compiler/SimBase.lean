import ConAgua.RISCV.Compiler.CompileProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Forward Simulation Base (`ConAgua.RISCV.Compiler.SimBase`)

BitVec/UInt64/alignment helpers, memory spans & framing, `CodeEnv`,
`MemRel`/frame relation, and core subset & purity lemmas.
-/

namespace ConAgua.RISCV.Compiler

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Linker

abbrev ByteMem := RV64.Word → RV64.Byte

/-! ## 1. BitVec / UInt64 / Alignment / Memory Span Helpers -/

theorem pc_add_4_ofNat (pc : RV64.Word) {k : Nat} (hpc : pc = BitVec.ofNat 64 (4 * k)) :
    pc + 4#64 = BitVec.ofNat 64 (4 * (k + 1)) := by
  have h4 : (4#64).toNat = 4 := rfl
  rw [hpc]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, h4, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mul_add, Nat.mul_one, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

theorem run_one_cont (rom : Rom) (st st' : State) (h : step rom st = .cont st') :
    RV64.run rom 1 st = .cont st' := by
  dsimp only [RV64.run]; rw [h]

theorem run_one_add (rom : Rom) (n : Nat) (st st1 : State) (h : step rom st = .cont st1) :
    RV64.run rom (1 + n) st = RV64.run rom n st1 := by
  rw [run_add, run_one_cont rom st st1 h]

theorem mul4_and_not1 (k : Nat) :
    (BitVec.ofNat 64 (4 * k)) &&& (~~~1#64) = BitVec.ofNat 64 (4 * k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases i with
  | zero =>
    have h0 : (BitVec.ofNat 64 (4 * k)).getLsbD 0 = false := by
      rw [BitVec.getLsbD_ofNat]; simp [Nat.testBit_zero, show (4 * k) % 2 = 0 by omega]
    rw [h0]; rfl
  | succ i' =>
    have h1 : (1#64).getLsbD (i' + 1) = false := by
      rw [BitVec.getLsbD_ofNat]; simp [Nat.testBit_succ, Nat.div_eq_of_lt (by decide : 1 < 2)]
    rw [h1]; simp

theorem isAligned8_iff (addr : BitVec 64) :
    isAligned addr 8 = true ↔ addr.toNat % 8 = 0 := by
  simp only [isAligned, beq_iff_eq]
  constructor
  · intro h
    have hnat : (addr.extractLsb' 0 3).toNat = (0#3).toNat := by rw [h]
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero] at hnat
    simpa [show (2 ^ 3 : Nat) = 8 by decide] using hnat
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, show (2 ^ 3 : Nat) = 8 by decide, h]
    rfl

theorem isAligned8_add_mul8 (base : BitVec 64) (hb : isAligned base 8 = true) (k : Nat) :
    isAligned (base + BitVec.ofNat 64 (8 * k)) 8 = true := by
  rw [isAligned8_iff] at hb ⊢
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hdvd : 8 ∣ 2 ^ 64 := by decide
  rw [Nat.mod_mod_of_dvd _ hdvd, Nat.add_mod, hb, Nat.zero_add, Nat.mod_mod_of_dvd _ hdvd]
  omega

theorem int_mul8_ofInt (k : Nat) :
    BitVec.ofInt 64 ((8 * k : Nat) : Int) = BitVec.ofNat 64 (8 * k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  rw [Int.toNat_emod (by omega) (by decide)]
  rfl

theorem isAligned8_add_int_mul8 (base : BitVec 64) (hb : isAligned base 8 = true) (k : Nat) :
    isAligned (base + BitVec.ofInt 64 (8 * (k : Int))) 8 = true := by
  rw [show (8 * (k : Int)) = ((8 * k : Nat) : Int) by omega, int_mul8_ofInt]
  exact isAligned8_add_mul8 base hb k

theorem slotOff_ofInt (k : Nat) :
    BitVec.ofInt 64 (slotOff k) = BitVec.ofNat 64 (8 * (1 + k)) := by
  rw [show slotOff k = ((8 * (1 + k) : Nat) : Int) from rfl, int_mul8_ofInt (1 + k)]

theorem loadBytes_one (m : ByteMem) (addr : BitVec 64) :
    (loadBytes m addr 1).zeroExtend 64 = (m addr).zeroExtend 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [loadBytes, BitVec.toNat_setWidth, BitVec.toNat_cast, BitVec.toNat_append, BitVec.toNat_ofNat]
  rw [Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]

theorem loadBytes_one_uint8 (m : ByteMem) (addr : BitVec 64) (b : UInt8)
    (hm : m addr = b.toBitVec) :
    (loadBytes m addr 1).zeroExtend 64 = b.toUInt64.toBitVec := by
  rw [loadBytes_one, hm, UInt8.toBitVec_toUInt64]

theorem uint64_toUInt8_toBitVec (v : UInt64) :
    v.toUInt8.toBitVec = v.toBitVec.extractLsb' 0 8 := by
  apply BitVec.eq_of_toNat_eq
  rw [UInt8.toNat_toBitVec, UInt64.toNat_toUInt8, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
      UInt64.toNat_toBitVec]

private theorem shift_nat_mod64 (b : UInt64) :
    (b.toBitVec % 64).toNat = (b.toBitVec.extractLsb' 0 6).toNat := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  have h64 : (64 : BitVec 64).toNat = 64 := by decide
  rw [BitVec.toNat_umod, h64]

theorem uint64_binop_toBitVec (op : BinOp) (x y : UInt64) :
    (op.eval x y).toBitVec = match op with
      | .add => x.toBitVec + y.toBitVec
      | .sub => x.toBitVec - y.toBitVec
      | .mul => x.toBitVec * y.toBitVec
      | .and => x.toBitVec &&& y.toBitVec
      | .or  => x.toBitVec ||| y.toBitVec
      | .xor => x.toBitVec ^^^ y.toBitVec
      | .shl => x.toBitVec <<< (y.toBitVec.extractLsb' 0 6).toNat
      | .shr => x.toBitVec >>> (y.toBitVec.extractLsb' 0 6).toNat
      | .mulhi => BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64) := by
  cases op
  · exact UInt64.toBitVec_add
  · exact UInt64.toBitVec_sub
  · exact UInt64.toBitVec_mul
  · exact UInt64.toBitVec_and x y
  · exact UInt64.toBitVec_or x y
  · exact UInt64.toBitVec_xor x y
  · rw [BinOp.eval, UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', shift_nat_mod64]
  · rw [BinOp.eval, UInt64.toBitVec_shiftRight, BitVec.ushiftRight_eq', shift_nat_mod64]
  · exact UInt64.toBitVec_ofNat' _

theorem uint64_cmp_slt (x y : UInt64) :
    decide (x.toInt64 < y.toInt64) = x.toBitVec.slt y.toBitVec := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff, Int64.lt_iff_toBitVec_slt, UInt64.toBitVec_toInt64, UInt64.toBitVec_toInt64]

theorem uint64_cmp_sle (x y : UInt64) :
    decide (x.toInt64 ≤ y.toInt64) = !(y.toBitVec.slt x.toBitVec) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff, Int64.le_iff_toBitVec_sle, UInt64.toBitVec_toInt64, UInt64.toBitVec_toInt64,
      BitVec.sle_eq_not_slt]

theorem uint64_cmp_ult (x y : UInt64) :
    decide (x < y) = x.toBitVec.ult y.toBitVec := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff, UInt64.lt_iff_toBitVec_lt, BitVec.ult_iff_toNat_lt]
  rfl

theorem uint64_cmp_ule (x y : UInt64) :
    decide (x ≤ y) = !(y.toBitVec.ult x.toBitVec) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff, UInt64.le_iff_toBitVec_le, BitVec.le_def, Bool.not_eq_true',
      BitVec.ult, decide_eq_false_iff_not, Nat.not_lt]

theorem uint64_cmp_eq (x y : UInt64) :
    (x == y) = (x.toBitVec == y.toBitVec) := by
  apply Bool.eq_iff_iff.mpr
  simp [beq_iff_eq, UInt64.toBitVec_inj]

theorem uint64_cmp_ne (x y : UInt64) :
    (x != y) = (x.toBitVec != y.toBitVec) := by
  simp only [bne, uint64_cmp_eq]

theorem bv_sub_ult1_eq (x y : BitVec 64) :
    (x - y).ult 1#64 = (x == y) := by
  apply Bool.eq_iff_iff.mpr
  rw [BitVec.ult_iff_toNat_lt, show (1#64).toNat = 1 by decide, Nat.lt_one_iff]
  constructor
  · intro h
    have hz : x - y = 0#64 := BitVec.eq_of_toNat_eq (by simpa using h)
    have hxy : x = y := by
      calc x = (x - y) + y := by rw [BitVec.sub_add_cancel]
        _ = 0#64 + y := by rw [hz]
        _ = y := BitVec.zero_add y
    exact beq_iff_eq.mpr hxy
  · intro h
    have hxy : x = y := beq_iff_eq.mp h
    subst hxy
    rw [BitVec.sub_self]; rfl

theorem bv_zero_ult_sub_eq (x y : BitVec 64) :
    (0#64).ult (x - y) = (x != y) := by
  apply Bool.eq_iff_iff.mpr
  rw [BitVec.ult_iff_toNat_lt, show (0#64).toNat = 0 by decide, Nat.pos_iff_ne_zero]
  simp only [bne_iff_ne]
  constructor
  · intro h heq; subst heq; rw [BitVec.sub_self] at h; exact h rfl
  · intro h heq; apply h
    have hz : x - y = 0#64 := BitVec.eq_of_toNat_eq (by simpa using heq)
    calc x = (x - y) + y := by rw [BitVec.sub_add_cancel]
      _ = 0#64 + y := by rw [hz]
      _ = y := BitVec.zero_add y

/-! ## 2. Memory Spans & Disjointness Framing -/

structure MemSpan where
  base : BitVec 64
  size : Nat

def MemSpan.valid (s : MemSpan) : Prop :=
  s.base.toNat + s.size ≤ 2 ^ 64

def MemSpan.contains (s : MemSpan) (addr : BitVec 64) : Prop :=
  ∃ k, k < s.size ∧ addr = s.base + BitVec.ofNat 64 k

def MemSpan.disjoint (s1 s2 : MemSpan) : Prop :=
  s1.base.toNat + s1.size ≤ s2.base.toNat ∨ s2.base.toNat + s2.size ≤ s1.base.toNat

def MemDisjoint (s1 s2 : MemSpan) : Prop :=
  ∀ a, s1.contains a → ¬s2.contains a

def MemSpan.sub (s1 s2 : MemSpan) : Prop :=
  ∀ a, s1.contains a → s2.contains a

theorem MemSpan.disjoint_symm {s1 s2 : MemSpan} (h : s1.disjoint s2) : s2.disjoint s1 := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem MemDisjoint.symm {s1 s2 : MemSpan} (h : MemDisjoint s1 s2) : MemDisjoint s2 s1 :=
  fun a h2 h1 => h a h1 h2

theorem MemDisjoint.of_sub_left {s1 s2 s3 : MemSpan} (h12 : s1.sub s2) (hd : MemDisjoint s2 s3) :
    MemDisjoint s1 s3 :=
  fun a h1 => hd a (h12 a h1)

theorem MemSpan.contains_toNat {s : MemSpan} (hv : s.valid) {a : BitVec 64}
    (hc : s.contains a) :
    s.base.toNat ≤ a.toNat ∧ a.toNat < s.base.toNat + s.size := by
  rcases hc with ⟨k, hk, rfl⟩
  have hlt : s.base.toNat + k < 2 ^ 64 := by
    have := hv; simp only [MemSpan.valid] at this; omega
  have hadd : (s.base + BitVec.ofNat 64 k).toNat = s.base.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hk64 : k < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hk64, Nat.mod_eq_of_lt hlt]
  omega

theorem MemSpan.disjoint_to_memDisjoint {s1 s2 : MemSpan} (hv1 : s1.valid) (hv2 : s2.valid)
    (hd : s1.disjoint s2) : MemDisjoint s1 s2 := by
  intro a h1 h2
  have hb1 := MemSpan.contains_toNat hv1 h1
  have hb2 := MemSpan.contains_toNat hv2 h2
  rcases hd with h | h <;> omega

theorem MemSpan.sub_range {s : MemSpan} (off n : Nat)
    (hle : off + n ≤ s.size) :
    ∀ k, k < n → s.contains (s.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) := by
  intro k hk
  refine ⟨off + k, by omega, ?_⟩
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem MemSpan.sub_trans {s1 s2 s3 : MemSpan} (h12 : s1.sub s2) (h23 : s2.sub s3) : s1.sub s3 :=
  fun a ha => h23 a (h12 a ha)

def MemEqOutside (s : MemSpan) (m1 m2 : ByteMem) : Prop :=
  ∀ a, ¬s.contains a → m2 a = m1 a

theorem MemEqOutside.refl (s : MemSpan) (m : ByteMem) : MemEqOutside s m m :=
  fun _ _ => rfl

theorem MemEqOutside.trans {s : MemSpan} {m1 m2 m3 : ByteMem}
    (h12 : MemEqOutside s m1 m2) (h23 : MemEqOutside s m2 m3) : MemEqOutside s m1 m3 := by
  intro a ha
  exact (h23 a ha).trans (h12 a ha)

theorem MemEqOutside.mono {s1 s2 : MemSpan} {m1 m2 : ByteMem}
    (hsub : s1.sub s2) (h : MemEqOutside s1 m1 m2) : MemEqOutside s2 m1 m2 := by
  intro a ha
  exact h a (fun h1 => ha (hsub a h1))

private theorem add_ofNat_succ (addr : BitVec 64) (k : Nat) :
    addr + 1#64 + BitVec.ofNat 64 k = addr + BitVec.ofNat 64 (k + 1) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64), Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_comm 1 k]

theorem MemEqOutside.storeBytes {s : MemSpan} (m : ByteMem) (addr : BitVec 64) (n : Nat)
    (v : BitVec (8 * n))
    (hcov : ∀ k, k < n → s.contains (addr + BitVec.ofNat 64 k)) :
    MemEqOutside s m (storeBytes m addr n v) := by
  induction n generalizing addr m with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro a ha
    have hcov' : ∀ k, k < n → s.contains ((addr + 1#64) + BitVec.ofNat 64 k) := by
      intro k hk
      rw [add_ofNat_succ]
      exact hcov (k + 1) (by omega)
    have h1 := ih (fun x => if x == addr then v.extractLsb' 0 8 else m x)
      (addr + 1#64) (v.extractLsb' 8 (8 * n)) hcov' a ha
    have hneq : (a == addr) = false := by
      apply beq_false_of_ne
      intro heq; apply ha
      rw [heq]
      simpa using hcov 0 (Nat.zero_lt_succ n)
    change RV64.storeBytes (fun x => if x == addr then v.extractLsb' 0 8 else m x)
      (addr + 1#64) n (v.extractLsb' 8 (8 * n)) a = m a
    rw [h1]
    simp [hneq]

theorem MemEqOutside.writeWord64 {s : MemSpan} (m : ByteMem) (addr w : BitVec 64)
    (hcov : ∀ k, k < 8 → s.contains (addr + BitVec.ofNat 64 k)) :
    MemEqOutside s m (writeWord64 m addr w) :=
  MemEqOutside.storeBytes m addr 8 w hcov

theorem MemEqOutside.loadBytes_eq {s1 : MemSpan} {m1 m2 : ByteMem}
    (heq : MemEqOutside s1 m1 m2) (addr : BitVec 64) (n : Nat)
    (hdisj : ∀ k, k < n → ¬s1.contains (addr + BitVec.ofNat 64 k)) :
    loadBytes m2 addr n = loadBytes m1 addr n := by
  apply loadBytes_congr
  intro k hk
  exact heq (addr + BitVec.ofNat 64 k) (hdisj k hk)

theorem MemEqOutside.readWord64_eq {s1 : MemSpan} {m1 m2 : ByteMem}
    (heq : MemEqOutside s1 m1 m2) (addr : BitVec 64)
    (hdisj : ∀ k, k < 8 → ¬s1.contains (addr + BitVec.ofNat 64 k)) :
    readWord64 m2 addr = readWord64 m1 addr :=
  MemEqOutside.loadBytes_eq heq addr 8 hdisj

def slotAddr (sp : BitVec 64) (j : Nat) : BitVec 64 :=
  sp + BitVec.ofNat 64 (8 * j)

def slotSpan (sp : BitVec 64) (j : Nat) : MemSpan :=
  ⟨slotAddr sp j, 8⟩

def frameSpan (sp : BitVec 64) (nlocals ntemps : Nat) : MemSpan :=
  ⟨sp, 8 * (1 + nlocals + ntemps)⟩

def tempSpan (sp : BitVec 64) (nlocals tmp ntemps : Nat) : MemSpan :=
  ⟨sp + BitVec.ofNat 64 (8 * (1 + nlocals + tmp)), 8 * (ntemps - tmp)⟩

theorem tempSpan_valid {sp : BitVec 64} {nlocals tmp ntemps : Nat}
    (hf : (frameSpan sp nlocals ntemps).valid) (hle : tmp ≤ ntemps) :
    (tempSpan sp nlocals tmp ntemps).valid := by
  simp only [MemSpan.valid, frameSpan, tempSpan] at *
  by_cases hlt : tmp < ntemps
  · have h1 : sp.toNat + 8 * (1 + nlocals + tmp) < 2 ^ 64 := by omega
    have hmul_lt : 8 * (1 + nlocals + tmp) < 2 ^ 64 := by omega
    have hadd : (sp + BitVec.ofNat 64 (8 * (1 + nlocals + tmp))).toNat =
        sp.toNat + 8 * (1 + nlocals + tmp) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmul_lt, Nat.mod_eq_of_lt h1]
    omega
  · have heq : ntemps - tmp = 0 := by omega
    rw [heq, Nat.mul_zero, Nat.add_zero]
    exact Nat.le_of_lt (BitVec.isLt _)

theorem tempSpan_sub_frame {sp : BitVec 64} {nlocals tmp ntemps : Nat}
    (hle : tmp ≤ ntemps) :
    (tempSpan sp nlocals tmp ntemps).sub (frameSpan sp nlocals ntemps) := by
  intro a ⟨k, hk, ha⟩
  subst ha
  refine ⟨8 * (1 + nlocals + tmp) + k, ?_, ?_⟩
  · simp only [tempSpan] at hk; simp only [frameSpan]; omega
  · simp only [tempSpan, frameSpan, BitVec.add_assoc, BitVec.ofNat_add]

theorem slotSpan_sub_frame {sp : BitVec 64} {nlocals ntemps j : Nat}
    (hj : j < 1 + nlocals + ntemps) :
    (slotSpan sp j).sub (frameSpan sp nlocals ntemps) := by
  intro a ⟨k, hk, ha⟩
  subst ha
  refine ⟨8 * j + k, ?_, ?_⟩
  · simp only [slotSpan] at hk; simp only [frameSpan]; omega
  · simp only [slotSpan, slotAddr, frameSpan, BitVec.add_assoc, BitVec.ofNat_add]

theorem tempSpan_mono {sp : BitVec 64} {nlocals tmp1 tmp2 ntemps : Nat}
    (h12 : tmp1 ≤ tmp2) (h2n : tmp2 ≤ ntemps) :
    (tempSpan sp nlocals tmp2 ntemps).sub (tempSpan sp nlocals tmp1 ntemps) := by
  intro a ⟨k, hk, ha⟩
  subst ha
  dsimp only [tempSpan] at hk
  dsimp only [MemSpan.contains, tempSpan]
  refine ⟨8 * (tmp2 - tmp1) + k, by omega, ?_⟩
  rw [BitVec.add_assoc sp, BitVec.add_assoc sp]
  congr 1
  rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 1
  omega

theorem tempSpan_slot_sub {sp : BitVec 64} {nlocals tmp j ntemps : Nat}
    (hle : tmp ≤ j) (hj : j < ntemps) :
    ∀ k, k < 8 → (tempSpan sp nlocals tmp ntemps).contains
      (sp + BitVec.ofNat 64 (8 * (1 + (nlocals + j))) + BitVec.ofNat 64 k) := by
  intro k hk
  dsimp only [MemSpan.contains, tempSpan]
  refine ⟨8 * (j - tmp) + k, by omega, ?_⟩
  rw [BitVec.add_assoc sp, BitVec.add_assoc sp]
  congr 1
  rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 1
  omega

theorem slotSpan_memDisjoint_tempSpan {sp : BitVec 64} {nlocals tmp ntemps x : Nat}
    (hf : (frameSpan sp nlocals ntemps).valid) (hle : tmp ≤ ntemps) (hx : x < 1 + nlocals + tmp) :
    MemDisjoint (slotSpan sp x) (tempSpan sp nlocals tmp ntemps) := by
  by_cases hlt : tmp < ntemps
  · refine MemSpan.disjoint_to_memDisjoint (by
      simp only [MemSpan.valid, frameSpan, slotSpan, slotAddr] at *
      have hx64 : 8 * x < 2 ^ 64 := by omega
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx64, Nat.mod_eq_of_lt (by omega)]
      omega) (tempSpan_valid hf hle) ?_
    simp only [MemSpan.valid, frameSpan] at hf
    have h1 : 8 * x < 2 ^ 64 := by omega
    have h2 : 8 * (1 + nlocals + tmp) < 2 ^ 64 := by omega
    have ha : (slotAddr sp x).toNat = sp.toNat + 8 * x := by
      simp only [slotAddr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1]
      exact Nat.mod_eq_of_lt (by omega)
    have hb : (tempSpan sp nlocals tmp ntemps).base.toNat = sp.toNat + 8 * (1 + nlocals + tmp) := by
      simp only [tempSpan, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2]
      exact Nat.mod_eq_of_lt (by omega)
    left; simp only [slotSpan, ha, hb]; omega
  · intro a _ ⟨k, hk, _⟩
    simp only [tempSpan] at hk; omega

theorem slotSpan_valid {sp : BitVec 64} {nlocals ntemps x : Nat}
    (hf : (frameSpan sp nlocals ntemps).valid) (hx : x < 1 + nlocals + ntemps) :
    (slotSpan sp x).valid := by
  simp only [MemSpan.valid, frameSpan, slotSpan, slotAddr] at *
  have hx64 : 8 * x < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx64, Nat.mod_eq_of_lt (by omega)]
  omega

theorem slotSpan_disjoint_of_ne {sp : BitVec 64} {nlocals ntemps x y : Nat}
    (hf : (frameSpan sp nlocals ntemps).valid)
    (hx : x < 1 + nlocals + ntemps) (hy : y < 1 + nlocals + ntemps) (hne : x ≠ y) :
    (slotSpan sp x).disjoint (slotSpan sp y) := by
  simp only [MemSpan.valid, frameSpan] at hf
  have hx64 : 8 * x < 2 ^ 64 := by omega
  have hy64 : 8 * y < 2 ^ 64 := by omega
  have ha : (slotSpan sp x).base.toNat = sp.toNat + 8 * x := by
    simp only [slotSpan, slotAddr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx64]
    exact Nat.mod_eq_of_lt (by omega)
  have hb : (slotSpan sp y).base.toNat = sp.toNat + 8 * y := by
    simp only [slotSpan, slotAddr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hy64]
    exact Nat.mod_eq_of_lt (by omega)
  dsimp only [MemSpan.disjoint, slotSpan]
  dsimp only [slotSpan] at ha hb
  rw [ha, hb]
  omega

/-! ## 3. Code Environment and Memory/Frame Relation -/

structure CodeEnv where
  tab : Tab
  code : Array (BitVec 32)
  labels : LabelMap
  rom : Rom
  hrom : RomMatchesCode rom code
  hcode64 : 4 * code.size < 2 ^ 64
  errTarget : Nat
  herrLbl : lookupLabel labels errLabel = some errTarget
  abortTarget : Nat
  habortLbl : lookupLabel labels abortLabel = some abortTarget
  exhaustedTarget : Nat
  hexhaustedLbl : lookupLabel labels exhaustedLabel = some exhaustedTarget

structure PreservedRegs (st0 st1 : State) : Prop where
  gp : st1.getReg AbiReg.gp = st0.getReg AbiReg.gp
  sp : st1.getReg AbiReg.sp = st0.getReg AbiReg.sp
  s0 : st1.getReg AbiReg.s0 = st0.getReg AbiReg.s0
  s2 : st1.getReg AbiReg.s2 = st0.getReg AbiReg.s2

theorem PreservedRegs.refl (st : State) : PreservedRegs st st :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem PreservedRegs.trans {st0 st1 st2 : State}
    (h01 : PreservedRegs st0 st1) (h12 : PreservedRegs st1 st2) : PreservedRegs st0 st2 :=
  ⟨h12.gp.trans h01.gp, h12.sp.trans h01.sp, h12.s0.trans h01.s0,
   h12.s2.trans h01.s2⟩

structure CodeEnvGen (lm : LinkModel) where
  tab : Tab
  code : Array (BitVec 32)
  labels : LabelMap
  rom : Rom
  hrom : RomMatchesCode rom code
  hcode64 : 4 * code.size < 2 ^ 64
  errTarget : Nat
  herrLbl : lookupLabel labels errLabel = some errTarget
  abortTarget : Nat
  habortLbl : lookupLabel labels abortLabel = some abortTarget
  exhaustedTarget : Nat
  hexhaustedLbl : lookupLabel labels exhaustedLabel = some exhaustedTarget

theorem PreservedRegs.of_regEqExceptT6 {st1 st2 : State}
    (h : RegEqExceptT6 st1.regs st2.regs) : PreservedRegs st1 st2 :=
  ⟨(h.getReg_eq (by decide)).symm, (h.getReg_eq (by decide)).symm,
   (h.getReg_eq (by decide)).symm, (h.getReg_eq (by decide)).symm⟩

def CodeEnv.toGen (env : CodeEnv) : CodeEnvGen nearLinkModel where
  tab := env.tab
  code := env.code
  labels := env.labels
  rom := env.rom
  hrom := env.hrom
  hcode64 := env.hcode64
  errTarget := env.errTarget
  herrLbl := env.herrLbl
  abortTarget := env.abortTarget
  habortLbl := env.habortLbl
  exhaustedTarget := env.exhaustedTarget
  hexhaustedLbl := env.hexhaustedLbl

structure TabMapOk (tab : Tab) : Prop where
  pos8_lt : ∀ a, (TieredArray.t0 a) ∈ tab.arrAt → tab.pos8 a < tab.nb + tab.nw
  pos64_lt : ∀ s, s ∈ tab.arrAt → tab.pos64 s < tab.nb + tab.nw
  pos8_inj : ∀ a1 a2, (TieredArray.t0 a1) ∈ tab.arrAt → (TieredArray.t0 a2) ∈ tab.arrAt →
    tab.pos8 a1 = tab.pos8 a2 → a1 = a2
  pos64_inj : ∀ s1 s2, s1 ∈ tab.arrAt → s2 ∈ tab.arrAt →
    tab.pos64 s1 = tab.pos64 s2 → s1 = s2
  pos8_pos64_eq : ∀ a, (TieredArray.t0 a) ∈ tab.arrAt →
    tab.pos8 a = tab.pos64 (TieredArray.t0 a)

structure Layout (tab : Tab) (nlocals ntemps : Nat) where
  T : BitVec 64
  hTAlign : isAligned T 8 = true
  tabBytes : Nat
  hTabMin : tab.globBase + 8 * (tab.ng : Int) ≤ (tabBytes : Int)
  hTValid : T.toNat + tabBytes ≤ 2 ^ 64
  sp : BitVec 64
  hSpAlign : isAligned sp 8 = true
  hFrameValid : sp.toNat + 8 * (1 + nlocals + ntemps) ≤ 2 ^ 64
  base8 : ArrId → BitVec 64
  cap8 : ArrId → Nat
  h8Valid : ∀ a, (base8 a).toNat + cap8 a ≤ 2 ^ 64
  base64 : TieredArray → BitVec 64
  cap64 : TieredArray → Nat
  h64Align : ∀ s, isAligned (base64 s) 8 = true
  h64Valid : ∀ s, (base64 s).toNat + 8 * cap64 s ≤ 2 ^ 64
  htabDisjFrame : MemSpan.disjoint ⟨T, tabBytes⟩ (frameSpan sp nlocals ntemps)
  h8DisjFrame : ∀ a, MemSpan.disjoint ⟨base8 a, cap8 a⟩ (frameSpan sp nlocals ntemps)
  h8DisjTab : ∀ a, MemSpan.disjoint ⟨base8 a, cap8 a⟩ ⟨T, tabBytes⟩
  h64DisjFrame : ∀ s, MemSpan.disjoint ⟨base64 s, 8 * cap64 s⟩ (frameSpan sp nlocals ntemps)
  h64DisjTab : ∀ s, MemSpan.disjoint ⟨base64 s, 8 * cap64 s⟩ ⟨T, tabBytes⟩
  h8Disj8 : ∀ a1 a2, a1 ≠ a2 → MemSpan.disjoint ⟨base8 a1, cap8 a1⟩ ⟨base8 a2, cap8 a2⟩
  h64Disj64 : ∀ s1 s2, s1 ≠ s2 → MemSpan.disjoint ⟨base64 s1, 8 * cap64 s1⟩ ⟨base64 s2, 8 * cap64 s2⟩
  h8Disj64 : ∀ a s, MemSpan.disjoint ⟨base8 a, cap8 a⟩ ⟨base64 s, 8 * cap64 s⟩

def Layout.tabSpan {tab : Tab} {nl nt : Nat} (L : Layout tab nl nt) : MemSpan :=
  ⟨L.T, L.tabBytes⟩

def Layout.arr8Span {tab : Tab} {nl nt : Nat} (L : Layout tab nl nt) (a : ArrId) : MemSpan :=
  ⟨L.base8 a, L.cap8 a⟩

def Layout.arr64Span {tab : Tab} {nl nt : Nat} (L : Layout tab nl nt) (s : TieredArray) : MemSpan :=
  ⟨L.base64 s, 8 * L.cap64 s⟩

theorem Tab.len8_eq_nat (tab : Tab) (a : ArrId) :
    tab.len8 a = ((8 * (2 + (tab.nb + tab.nw) + tab.pos8 a) : Nat) : Int) := by
  simp only [Tab.len8, Tab.dlen]; omega

theorem Tab.base8_eq_nat (tab : Tab) (a : ArrId) :
    tab.base8 a = ((8 * (2 + tab.pos8 a) : Nat) : Int) := by
  simp only [Tab.base8, Tab.dbase]; omega

theorem Tab.len64_eq_nat (tab : Tab) (s : TieredArray) :
    tab.len64 s = ((8 * (2 + (tab.nb + tab.nw) + tab.pos64 s) : Nat) : Int) := by
  simp only [Tab.len64, Tab.dlen]; omega

theorem Tab.base64_eq_nat (tab : Tab) (s : TieredArray) :
    tab.base64 s = ((8 * (2 + tab.pos64 s) : Nat) : Int) := by
  simp only [Tab.base64, Tab.dbase]; omega

theorem Tab.globOff_eq_nat (tab : Tab) (g : GVar) :
    tab.globOff g = ((8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres + g.id) : Nat) : Int) := by
  simp only [Tab.globOff, Tab.globBase, Tab.resBase, Tab.romBase]; omega

theorem Tab.len8_bound {tab : Tab} {nl nt : Nat} (L : Layout tab nl nt) (hm : TabMapOk tab)
    (a : ArrId) (ha : (TieredArray.t0 a) ∈ tab.arrAt) :
    8 * (2 + (tab.nb + tab.nw) + tab.pos8 a) + 8 ≤ L.tabBytes := by
  have h1 := L.hTabMin
  have h2 := hm.pos8_lt a ha
  simp only [Tab.globBase, Tab.resBase, Tab.romBase] at h1
  omega

theorem Tab.base8_bound {tab : Tab} {nl nt : Nat} (L : Layout tab nl nt) (hm : TabMapOk tab)
    (a : ArrId) (ha : (TieredArray.t0 a) ∈ tab.arrAt) :
    8 * (2 + tab.pos8 a) + 8 ≤ L.tabBytes := by
  have h1 := L.hTabMin
  have h2 := hm.pos8_lt a ha
  simp only [Tab.globBase, Tab.resBase, Tab.romBase] at h1
  omega

theorem Tab.len64_bound {tab : Tab} {nl nt : Nat} (L : Layout tab nl nt) (hm : TabMapOk tab)
    (s : TieredArray) (hs : s ∈ tab.arrAt) :
    8 * (2 + (tab.nb + tab.nw) + tab.pos64 s) + 8 ≤ L.tabBytes := by
  have h1 := L.hTabMin
  have h2 := hm.pos64_lt s hs
  simp only [Tab.globBase, Tab.resBase, Tab.romBase] at h1
  omega

theorem Tab.base64_bound {tab : Tab} {nl nt : Nat} (L : Layout tab nl nt) (hm : TabMapOk tab)
    (s : TieredArray) (hs : s ∈ tab.arrAt) :
    8 * (2 + tab.pos64 s) + 8 ≤ L.tabBytes := by
  have h1 := L.hTabMin
  have h2 := hm.pos64_lt s hs
  simp only [Tab.globBase, Tab.resBase, Tab.romBase] at h1
  omega

theorem Tab.globOff_bound_nat {tab : Tab} {nl nt : Nat} (L : Layout tab nl nt)
    (g : GVar) (hg : g.id < tab.ng) :
    8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres + g.id) + 8 ≤ L.tabBytes := by
  have h1 := L.hTabMin
  simp only [Tab.globBase, Tab.resBase, Tab.romBase] at h1
  omega

def MemRel (tab : Tab) {nl nt : Nat} (L : Layout tab nl nt)
    (rmem : ByteMem) (m : _root_.L.Mem) : Prop :=
  (∀ a, (TieredArray.t0 a) ∈ tab.arrAt →
    (m.arr8 a).size ≤ L.cap8 a ∧
    (m.arr8 a).size < 2 ^ 64 ∧
    readWord64 rmem (L.T + BitVec.ofInt 64 (tab.len8 a)) = BitVec.ofNat 64 (m.arr8 a).size ∧
    readWord64 rmem (L.T + BitVec.ofInt 64 (tab.base8 a)) = L.base8 a ∧
    (∀ i, (hi : i < (m.arr8 a).size) →
      rmem (L.base8 a + BitVec.ofNat 64 i) = (m.arr8 a)[i].toBitVec)) ∧
  (∀ s, s ∈ tab.arrAt →
    (m.arr64 s).size ≤ L.cap64 s ∧
    (m.arr64 s).size < 2 ^ 64 ∧
    readWord64 rmem (L.T + BitVec.ofInt 64 (tab.len64 s)) = BitVec.ofNat 64 (m.arr64 s).size ∧
    readWord64 rmem (L.T + BitVec.ofInt 64 (tab.base64 s)) = L.base64 s ∧
    (∀ i, (hi : i < (m.arr64 s).size) →
      readWord64 rmem (L.base64 s + BitVec.ofNat 64 (8 * i)) = (m.arr64 s)[i].toBitVec)) ∧
  (∀ g : GVar, g.id < tab.ng →
    readWord64 rmem (L.T + BitVec.ofInt 64 (tab.globOff g)) = (m.glob g).toBitVec)

def FrameOk {tab : Tab} {nl nt : Nat} (L : Layout tab nl nt)
    (rmem : ByteMem) (nlocals : Nat) (loc : _root_.L.Locals) : Prop :=
  ∀ x, x < nlocals → readWord64 rmem (L.sp + BitVec.ofInt 64 (slotOff x)) = (loc x).toBitVec

theorem MemRel.of_eqOutside {tab : Tab} {nl nt : Nat} {L : Layout tab nl nt} (hm : TabMapOk tab)
    {m1 m2 : ByteMem} {lm : _root_.L.Mem} {s : MemSpan}
    (hT : MemDisjoint s L.tabSpan) (h8 : ∀ a, MemDisjoint s (L.arr8Span a))
    (h64 : ∀ a, MemDisjoint s (L.arr64Span a))
    (heq : MemEqOutside s m1 m2) (hrel : MemRel tab L m1 lm) :
    MemRel tab L m2 lm := by
  rcases hrel with ⟨ha, hs64, hg⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a haMem
    rcases ha a haMem with ⟨hcap, hlt, hlen, hbase, hbytes⟩
    refine ⟨hcap, hlt, ?_, ?_, ?_⟩
    · rw [← hlen]
      apply MemEqOutside.readWord64_eq heq
      intro k hk
      rw [Tab.len8_eq_nat, int_mul8_ofInt]
      exact hT.symm _ (MemSpan.sub_range _ 8 (Tab.len8_bound L hm a haMem) k hk)
    · rw [← hbase]
      apply MemEqOutside.readWord64_eq heq
      intro k hk
      rw [Tab.base8_eq_nat, int_mul8_ofInt]
      exact hT.symm _ (MemSpan.sub_range _ 8 (Tab.base8_bound L hm a haMem) k hk)
    · intro i hi
      rw [← hbytes i hi]
      apply heq
      exact (h8 a).symm _ ⟨i, by dsimp only [Layout.arr8Span]; omega, rfl⟩
  · intro s64 hsMem
    rcases hs64 s64 hsMem with ⟨hcap, hlt, hlen, hbase, hwords⟩
    refine ⟨hcap, hlt, ?_, ?_, ?_⟩
    · rw [← hlen]
      apply MemEqOutside.readWord64_eq heq
      intro k hk
      rw [Tab.len64_eq_nat, int_mul8_ofInt]
      exact hT.symm _ (MemSpan.sub_range _ 8 (Tab.len64_bound L hm s64 hsMem) k hk)
    · rw [← hbase]
      apply MemEqOutside.readWord64_eq heq
      intro k hk
      rw [Tab.base64_eq_nat, int_mul8_ofInt]
      exact hT.symm _ (MemSpan.sub_range _ 8 (Tab.base64_bound L hm s64 hsMem) k hk)
    · intro i hi
      rw [← hwords i hi]
      apply MemEqOutside.readWord64_eq heq
      intro k hk
      exact (h64 s64).symm _
        (MemSpan.sub_range (s := L.arr64Span s64) (8 * i) 8 (by simp only [Layout.arr64Span]; omega) k hk)
  · intro g hgBound
    rw [← hg g hgBound]
    apply MemEqOutside.readWord64_eq heq
    intro k hk
    rw [Tab.globOff_eq_nat, int_mul8_ofInt]
    exact hT.symm _ (MemSpan.sub_range _ 8 (Tab.globOff_bound_nat L g hgBound) k hk)

theorem FrameOk.of_eqOutside {tab : Tab} {nl nt : Nat} {L : Layout tab nl nt}
    {m1 m2 : ByteMem} {loc : _root_.L.Locals} {s : MemSpan}
    (hdisj : ∀ x, x < nl → MemDisjoint s (slotSpan L.sp (1 + x)))
    (heq : MemEqOutside s m1 m2) (hfr : FrameOk L m1 nl loc) :
    FrameOk L m2 nl loc := by
  intro x hx
  rw [← hfr x hx]
  apply MemEqOutside.readWord64_eq heq
  intro k hk
  rw [slotOff_ofInt]
  exact (hdisj x hx).symm _ ⟨k, hk, rfl⟩

theorem memRel_frame_sub_trans {tab : Tab} {nl nt : Nat} {L : Layout tab nl nt} (hm : TabMapOk tab)
    {s : MemSpan} (hsub : s.sub (frameSpan L.sp nl nt))
    {m1 m2 : ByteMem} {lm : _root_.L.Mem}
    (heq : MemEqOutside s m1 m2) (hrel : MemRel tab L m1 lm) :
    MemRel tab L m2 lm := by
  refine MemRel.of_eqOutside hm ?_ ?_ ?_ heq hrel
  · exact MemDisjoint.of_sub_left hsub
      (MemSpan.disjoint_to_memDisjoint L.hFrameValid L.hTValid L.htabDisjFrame.symm)
  · intro a
    exact MemDisjoint.of_sub_left hsub
      (MemSpan.disjoint_to_memDisjoint L.hFrameValid (L.h8Valid a) (L.h8DisjFrame a).symm)
  · intro s64
    exact MemDisjoint.of_sub_left hsub
      (MemSpan.disjoint_to_memDisjoint L.hFrameValid (L.h64Valid s64) (L.h64DisjFrame s64).symm)

theorem frameOk_of_eqOutside_temp {tab : Tab} {nl nt : Nat} {L : Layout tab nl nt}
    {tmp : Nat} (hle : tmp ≤ nt) {m1 m2 : ByteMem} {loc : _root_.L.Locals}
    (heq : MemEqOutside (tempSpan L.sp nl tmp nt) m1 m2) (hfr : FrameOk L m1 nl loc) :
    FrameOk L m2 nl loc := by
  refine FrameOk.of_eqOutside ?_ heq hfr
  intro x hx
  exact (slotSpan_memDisjoint_tempSpan L.hFrameValid hle (by omega)).symm

theorem memRel_of_eqOutside_temp {tab : Tab} {nl nt : Nat} {L : Layout tab nl nt} (hm : TabMapOk tab)
    {tmp : Nat} (hle : tmp ≤ nt) {m1 m2 : ByteMem} {lm : _root_.L.Mem}
    (heq : MemEqOutside (tempSpan L.sp nl tmp nt) m1 m2) (hrel : MemRel tab L m1 lm) :
    MemRel tab L m2 lm :=
  memRel_frame_sub_trans hm (tempSpan_sub_frame hle) heq hrel

/-! ## 4. Core Subset & Purity Lemmas -/

inductive CoreExpr (tab : Tab) : Expr → Prop where
  | const (w : _root_.L.Word) : CoreExpr tab (.const w)
  | var (x : Var) : CoreExpr tab (.var x)
  | len8 (a : ArrId) (ha : (TieredArray.t0 a) ∈ tab.arrAt) : CoreExpr tab (.len8 a)
  | len64 (a : ArrId) (ha : (TieredArray.t0 a) ∈ tab.arrAt) : CoreExpr tab (.len64 a)
  | glob (g : GVar) (hg : g.id < tab.ng) : CoreExpr tab (.glob g)
  | bin (op : BinOp) (a b : Expr) : CoreExpr tab a → CoreExpr tab b → CoreExpr tab (.bin op a b)
  | cmpw (c : Cmp) (a b : Expr) : CoreExpr tab a → CoreExpr tab b → CoreExpr tab (.cmpw c a b)
  | ld8 (a : ArrId) (i : Expr) (ha : (TieredArray.t0 a) ∈ tab.arrAt) :
      CoreExpr tab i → CoreExpr tab (.ld8 a i)
  | ld64 (a : ArrId) (i : Expr) (ha : (TieredArray.t0 a) ∈ tab.arrAt) :
      CoreExpr tab i → CoreExpr tab (.ld64 a i)

inductive CoreCond (tab : Tab) : Cond → Prop where
  | cmp (c : Cmp) (a b : Expr) : CoreExpr tab a → CoreExpr tab b → CoreCond tab (.cmp c a b)
  | and (p q : Cond) : CoreCond tab p → CoreCond tab q → CoreCond tab (.and p q)
  | or (p q : Cond) : CoreCond tab p → CoreCond tab q → CoreCond tab (.or p q)
  | not (p : Cond) : CoreCond tab p → CoreCond tab (.not p)

inductive CoreStmt (tab : Tab) (nlocals : Nat) : Stmt → Prop where
  | skip : CoreStmt tab nlocals .skip
  | set (x : Var) (e : Expr) (hx : x < nlocals) : CoreExpr tab e → CoreStmt tab nlocals (.set x e)
  | gset (g : GVar) (e : Expr) (hg : g.id < tab.ng) : CoreExpr tab e → CoreStmt tab nlocals (.gset g e)
  | st64 (a : ArrId) (i e : Expr) (ha : (TieredArray.t0 a) ∈ tab.arrAt) :
      CoreExpr tab i → CoreExpr tab e → CoreStmt tab nlocals (.st64 a i e)
  | seq (s1 s2 : Stmt) : CoreStmt tab nlocals s1 → CoreStmt tab nlocals s2 → CoreStmt tab nlocals (.seq s1 s2)
  | ite (c : Cond) (s1 s2 : Stmt) :
      CoreCond tab c → CoreStmt tab nlocals s1 → CoreStmt tab nlocals s2 → CoreStmt tab nlocals (.ite c s1 s2)
  | ret (es : List Expr) (hes : ∀ e ∈ es, CoreExpr tab e) : CoreStmt tab nlocals (.ret es)
  | abort (e : Expr) : CoreExpr tab e → CoreStmt tab nlocals (.abort e)

def exprVarsLt (nlocals : Nat) : Expr → Prop
  | .const _ | .len8 _ | .len64 _ | .glob _ => True
  | .var x => x < nlocals
  | .bin _ a b | .cmpw _ a b | .ld64t _ a b | .ld32t _ a b | .ld32h _ a b _ =>
      exprVarsLt nlocals a ∧ exprVarsLt nlocals b
  | .ld8 _ i | .ld64 _ i | .ldc _ i | .len64t _ i | .ld8x8 _ i => exprVarsLt nlocals i

def condVarsLt (nlocals : Nat) : Cond → Prop
  | .cmp _ a b => exprVarsLt nlocals a ∧ exprVarsLt nlocals b
  | .and p q | .or p q => condVarsLt nlocals p ∧ condVarsLt nlocals q
  | .not p => condVarsLt nlocals p

def stmtVarsLt (nlocals : Nat) : Stmt → Prop
  | .skip | .brk => True
  | .set x e => x < nlocals ∧ exprVarsLt nlocals e
  | .gset _ e | .abort e => exprVarsLt nlocals e
  | .st8 _ i e | .st64 _ i e => exprVarsLt nlocals i ∧ exprVarsLt nlocals e
  | .seq s1 s2 => stmtVarsLt nlocals s1 ∧ stmtVarsLt nlocals s2
  | .ite c s1 s2 => condVarsLt nlocals c ∧ stmtVarsLt nlocals s1 ∧ stmtVarsLt nlocals s2
  | .while c s => condVarsLt nlocals c ∧ stmtVarsLt nlocals s
  | .ret es => ∀ e ∈ es, exprVarsLt nlocals e
  | _ => False

theorem CoreExpr.evalE_pure {tab : Tab} {e : Expr} (he : CoreExpr tab e) (st : St) :
    (∃ v, evalE e st = .ok (v, st)) ∨ evalE e st = .error .oob := by
  induction he with
  | const w => exact Or.inl ⟨w, rfl⟩
  | var x => exact Or.inl ⟨st.loc x, rfl⟩
  | len8 a _ => exact Or.inl ⟨st.mem.len8 a, rfl⟩
  | len64 a _ => exact Or.inl ⟨st.mem.len64 a, rfl⟩
  | glob g _ => exact Or.inl ⟨st.mem.glob g, rfl⟩
  | bin op a b _ _ iha ihb =>
    rcases iha with ⟨va, ha⟩ | ha
    · rcases ihb with ⟨vb, hb⟩ | hb
      · exact Or.inl ⟨op.eval va vb,
          by simp [evalE, Bind.bind, StateT.bind, Except.bind, ha, hb, Pure.pure, StateT.pure, Except.pure]⟩
      · exact Or.inr (by simp [evalE, Bind.bind, StateT.bind, Except.bind, ha, hb])
    · exact Or.inr (by simp [evalE, Bind.bind, StateT.bind, Except.bind, ha])
  | cmpw c a b _ _ iha ihb =>
    rcases iha with ⟨va, ha⟩ | ha
    · rcases ihb with ⟨vb, hb⟩ | hb
      · exact Or.inl ⟨c.evalW va vb,
          by simp [evalE, Bind.bind, StateT.bind, Except.bind, ha, hb, Pure.pure, StateT.pure, Except.pure]⟩
      · exact Or.inr (by simp [evalE, Bind.bind, StateT.bind, Except.bind, ha, hb])
    · exact Or.inr (by simp [evalE, Bind.bind, StateT.bind, Except.bind, ha])
  | ld8 a i _ _ ihi =>
    rcases ihi with ⟨vi, hi⟩ | hi
    · by_cases hb : vi.toNat < (st.mem.arr8 a).size
      · refine Or.inl ⟨(st.mem.arr8 a)[vi.toNat].toUInt64, ?_⟩
        change (evalE i >>= fun idx => _root_.L.ld8 a idx) st = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]
        rw [hi]
        dsimp only [_root_.L.ld8, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
          Pure.pure, StateT.pure, Except.pure, Except.bind]
        simp [hb]; rfl
      · refine Or.inr ?_
        change (evalE i >>= fun idx => _root_.L.ld8 a idx) st = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]
        rw [hi]
        dsimp only [_root_.L.ld8, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
          Pure.pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, Except.pure]
        simp [hb]; rfl
    · exact Or.inr (by simp [evalE, Bind.bind, StateT.bind, Except.bind, hi])
  | ld64 a i _ _ ihi =>
    rcases ihi with ⟨vi, hi⟩ | hi
    · by_cases hb : vi.toNat < (st.mem.arr64 (TieredArray.t0 a)).size
      · refine Or.inl ⟨(st.mem.arr64 (TieredArray.t0 a))[vi.toNat], ?_⟩
        change (evalE i >>= fun idx => _root_.L.ld64 (TieredArray.t0 a) idx) st = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]
        rw [hi]
        dsimp only [_root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
          Pure.pure, StateT.pure, Except.pure, Except.bind]
        simp [hb]; rfl
      · refine Or.inr ?_
        change (evalE i >>= fun idx => _root_.L.ld64 (TieredArray.t0 a) idx) st = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]
        rw [hi]
        dsimp only [_root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
          Pure.pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, Except.pure]
        simp [hb]; rfl
    · exact Or.inr (by simp [evalE, Bind.bind, StateT.bind, Except.bind, hi])

theorem CoreCond.evalC_pure {tab : Tab} {c : Cond} (hc : CoreCond tab c) (st : St) :
    (∃ b, evalC c st = .ok (b, st)) ∨ evalC c st = .error .oob := by
  induction hc with
  | cmp c a b ha hb =>
    rcases ha.evalE_pure st with ⟨va, hva⟩ | hva
    · rcases hb.evalE_pure st with ⟨vb, hvb⟩ | hvb
      · exact Or.inl ⟨c.eval va vb,
          by simp [evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]⟩
      · exact Or.inr (by simp [evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb])
    · exact Or.inr (by simp [evalC, Bind.bind, StateT.bind, Except.bind, hva])
  | and p q _ _ ihp ihq =>
    rcases ihp with ⟨bp, hbp⟩ | hbp
    · cases bp
      · exact Or.inl ⟨false,
          by simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, Pure.pure, StateT.pure, Except.pure]⟩
      · rcases ihq with ⟨bq, hbq⟩ | hbq
        · exact Or.inl ⟨bq, by simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]⟩
        · exact Or.inr (by simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq])
    · exact Or.inr (by simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp])
  | or p q _ _ ihp ihq =>
    rcases ihp with ⟨bp, hbp⟩ | hbp
    · cases bp
      · rcases ihq with ⟨bq, hbq⟩ | hbq
        · exact Or.inl ⟨bq, by simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]⟩
        · exact Or.inr (by simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq])
      · exact Or.inl ⟨true,
          by simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, Pure.pure, StateT.pure, Except.pure]⟩
    · exact Or.inr (by simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp])
  | not p _ ihp =>
    rcases ihp with ⟨bp, hbp⟩ | hbp
    · exact Or.inl ⟨!bp,
        by simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, Pure.pure, StateT.pure, Except.pure]⟩
    · exact Or.inr (by simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp])

end ConAgua.RISCV.Compiler
