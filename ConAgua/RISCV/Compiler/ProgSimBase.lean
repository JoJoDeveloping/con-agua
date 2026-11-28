import ConAgua.RISCV.Compiler.SimProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Program Simulation Base (`ConAgua.RISCV.Compiler.ProgSimBase`)

Shared alignment, program table/layout, `ProgMemRel`, purity lemmas, mutation lemmas,
and small self-contained helpers split out of `ProgSimProof`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard Lean axioms only.
-/

namespace ConAgua.RISCV.Compiler

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Linker

/-! ## 1. Extended Single-Instruction, Alignment, & 32/64-bit Memory Helpers -/

theorem step_item_ret_lm (lkm : LinkModel) {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ [Asm.ret] ++ post) = .ok (code, labels))
    (h64 : 4 * lkm.totalSize pre < 2 ^ 64) (st : State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre)) :
    RV64.step rom st = .cont { st with pc := st.getReg AbiReg.ra &&& ~~~1#64 } := by
  have hs := step_item_instr_lm lkm hrom pre post (.jalr AbiReg.zero AbiReg.ra 0#12) hlink h64 st hpc
  rw [hs]
  simp only [execInstr, setReg_zero]
  have hz : sextImm12 0#12 = 0#64 := rfl
  rw [hz, BitVec.add_zero]

theorem step_item_ret {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (hlink : linkResolved (pre ++ [Asm.ret] ++ post) = .ok (code, labels))
    (h64 : 4 * totalWords pre < 2 ^ 64) (st : State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * totalWords pre)) :
    RV64.step rom st = .cont { st with pc := st.getReg AbiReg.ra &&& ~~~1#64 } :=
  step_item_ret_lm nearLinkModel hrom pre post hlink (by rw [near_totalSize_eq]; exact h64) st (by rw [near_totalSize_eq]; exact hpc)

theorem isAligned4_of_isAligned8 (addr : BitVec 64) (h8 : isAligned addr 8 = true) :
    isAligned addr 4 = true := by
  rw [isAligned8_iff] at h8
  unfold isAligned
  simp only [beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_ofNat]
  omega

theorem isAligned4_add_mul4 (base : BitVec 64) (hb : isAligned base 8 = true) (k : Nat) :
    isAligned (base + BitVec.ofNat 64 (4 * k)) 4 = true := by
  rw [isAligned8_iff] at hb
  unfold isAligned
  simp only [beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_add, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
  have hdvd : 4 ∣ 2 ^ 64 := by decide
  rw [Nat.mod_mod_of_dvd _ hdvd, Nat.add_mod,
      show base.toNat % 4 = 0 by omega, Nat.zero_add,
      Nat.mod_mod_of_dvd _ hdvd]
  omega

theorem bitvec_sub_mul8_toNat (base : BitVec 64) (k : Nat) (hk : 8 * k ≤ base.toNat) :
    (base - BitVec.ofNat 64 (8 * k)).toNat = base.toNat - 8 * k := by
  have hklt : 8 * k < 2 ^ 64 := Nat.lt_of_le_of_lt hk base.isLt
  have hsub : 2 ^ 64 - 8 * k + base.toNat = 2 ^ 64 + (base.toNat - 8 * k) := by omega
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hklt, hsub,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

theorem isAligned8_sub_mul8 (base : BitVec 64) (hb : isAligned base 8 = true)
    (k : Nat) (hk : 8 * k ≤ base.toNat) :
    isAligned (base - BitVec.ofNat 64 (8 * k)) 8 = true := by
  rw [isAligned8_iff] at hb ⊢
  rw [bitvec_sub_mul8_toNat base k hk]
  omega

theorem loadBytes_one_eq_byte (m : ByteMem) (addr : BitVec 64) :
    loadBytes m addr 1 = m addr := by
  apply BitVec.eq_of_toNat_eq
  simp [loadBytes]

theorem sextImm12_of_lt2048_nat (x : Nat) (hx : x < 2 ^ 11) :
    sextImm12 (BitVec.ofNat 12 x) = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toInt_eq
  rw [sextImm12, BitVec.toInt_signExtend, show min 64 12 = 12 from rfl]
  have h12 : (BitVec.ofNat 12 x).toNat = x := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h64 : (BitVec.ofNat 64 x).toNat = x := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond, h12, h64]
  have c1 : 2 * x < 2 ^ 12 := by omega
  have c2 : 2 * x < 2 ^ 64 := by omega
  simp only [c1, c2, ↓reduceIte, Int.bmod_def]
  have hm : (x : Int) % ((2 ^ 12 : Nat) : Int) = (x : Int) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)
  rw [hm]
  split <;> omega

private theorem add_ofNat_left_succ (addr : BitVec 64) (k : Nat) :
    addr + 1#64 + BitVec.ofNat 64 k = addr + BitVec.ofNat 64 (k + 1) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64), Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
      Nat.add_comm 1 k]

private theorem add_ofNat_add (addr : BitVec 64) (p q : Nat) :
    addr + BitVec.ofNat 64 p + BitVec.ofNat 64 q = addr + BitVec.ofNat 64 (p + q) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

private theorem loadBytes_toNat_cast {m : ByteMem} {addr : BitVec 64} {a b : Nat} (h : a = b) :
    (loadBytes m addr a).toNat = (loadBytes m addr b).toNat := by
  subst h; rfl

theorem loadBytes_toNat_succ (m : ByteMem) (addr : BitVec 64) (n : Nat) :
    (loadBytes m addr (n + 1)).toNat =
      (loadBytes m (addr + 1#64) n).toNat * 256 + (m addr).toNat := by
  have hc : (loadBytes m addr (n + 1)).toNat =
      ((loadBytes m (addr + 1#64) n ++ m addr).cast (by omega) : BitVec (8 * (n + 1))).toNat := rfl
  rw [hc, BitVec.toNat_cast, BitVec.toNat_append]
  have hmlt : (m addr).toNat < 256 := (m addr).isLt
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by simpa using hmlt), Nat.shiftLeft_eq]

theorem loadBytes_split_toNat (m : ByteMem) (addr : BitVec 64) (p q : Nat) :
    (loadBytes m addr (p + q)).toNat =
      (loadBytes m (addr + BitVec.ofNat 64 p) q).toNat * 2 ^ (8 * p) +
        (loadBytes m addr p).toNat := by
  induction p generalizing addr with
  | zero =>
    rw [loadBytes_toNat_cast (Nat.zero_add q)]
    have hb : addr + BitVec.ofNat 64 0 = addr := BitVec.add_zero addr
    rw [hb, show loadBytes m addr 0 = 0#0 from rfl]
    simp
  | succ p ih =>
    have hc : (loadBytes m addr (p + 1 + q)).toNat = (loadBytes m addr ((p + q) + 1)).toNat :=
      loadBytes_toNat_cast (by omega)
    rw [hc, loadBytes_toNat_succ, loadBytes_toNat_succ (addr := addr) (n := p)]
    rw [ih (addr + 1#64), add_ofNat_left_succ]
    have hpow : 2 ^ (8 * (p + 1)) = 2 ^ (8 * p) * 256 := by
      rw [Nat.mul_add, Nat.pow_add]
    rw [hpow, Nat.add_mul, Nat.mul_assoc]
    omega

theorem loadBytes_zeroExtend32_lo (m : ByteMem) (addr : BitVec 64) :
    (loadBytes m addr 4).zeroExtend 64 =
      (UInt64.ofNat (readWord64 m addr).toNat % 4294967296).toBitVec := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.zeroExtend, BitVec.toNat_setWidth, UInt64.toNat_toBitVec, UInt64.toNat_mod,
      show (4294967296 : UInt64).toNat = 2 ^ 32 from rfl, UInt64.toNat_ofNat']
  have h8 : readWord64 m addr = loadBytes m addr (4 + 4) := rfl
  rw [h8, loadBytes_split_toNat]
  have hlt4 : (loadBytes m addr 4).toNat < 2 ^ 32 := (loadBytes m addr 4).isLt
  have hlt4b : (loadBytes m (addr + BitVec.ofNat 64 4) 4).toNat < 2 ^ 32 :=
    (loadBytes m (addr + BitVec.ofNat 64 4) 4).isLt
  have hlt8 : (loadBytes m (addr + BitVec.ofNat 64 4) 4).toNat * 2 ^ 32 +
      (loadBytes m addr 4).toNat < 2 ^ 64 := by omega
  have h32 : 2 ^ (8 * 4) = 2 ^ 32 := rfl
  rw [h32]
  rw [Nat.mod_eq_of_lt (Nat.lt_trans hlt4 (by decide)), Nat.mod_eq_of_lt hlt8,
      Nat.add_comm _ (loadBytes m addr 4).toNat, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt4]

theorem loadBytes_zeroExtend32_hi (m : ByteMem) (addr : BitVec 64) :
    (loadBytes m (addr + 4#64) 4).zeroExtend 64 =
      (UInt64.ofNat (readWord64 m addr).toNat >>> 32).toBitVec := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.zeroExtend, BitVec.toNat_setWidth, UInt64.toNat_toBitVec,
      UInt64.toNat_shiftRight, show (32 : UInt64).toNat % 64 = 32 from rfl, UInt64.toNat_ofNat']
  have h8 : (readWord64 m addr).toNat = (loadBytes m addr (4 + 4)).toNat := rfl
  have h32 : 2 ^ (8 * 4) = 2 ^ 32 := rfl
  rw [h8, loadBytes_split_toNat, h32]
  have hlt4a : (loadBytes m addr 4).toNat < 2 ^ 32 := (loadBytes m addr 4).isLt
  have hlt4b : (loadBytes m (addr + BitVec.ofNat 64 4) 4).toNat < 2 ^ 32 :=
    (loadBytes m (addr + BitVec.ofNat 64 4) 4).isLt
  have hlt8 : (loadBytes m (addr + BitVec.ofNat 64 4) 4).toNat * 2 ^ 32 +
      (loadBytes m addr 4).toNat < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt (Nat.lt_trans hlt4b (by decide)), Nat.mod_eq_of_lt hlt8,
      Nat.shiftRight_eq_div_pow, Nat.add_comm _ (loadBytes m addr 4).toNat,
      Nat.add_mul_div_right _ _ (by decide : 0 < 2 ^ 32),
      Nat.div_eq_of_lt hlt4a, Nat.zero_add]

private theorem loadBytes_4_write4_self (m : ByteMem) (addr : BitVec 64) (v : BitVec 32) :
    loadBytes (storeBytes m addr 4 v) addr 4 = v :=
  loadBytes_storeBytes_self m addr 4 (by decide) v

private theorem writeWord64_apply_lt (m : ByteMem) (addr : BitVec 64) (w : BitVec 64) (k : Nat)
    (hk : k < 8) :
    writeWord64 m addr w (addr + BitVec.ofNat 64 k) = (w.extractLsb' (8 * k) 8) := by
  have hk_step : ∀ (n : Nat) (mem : ByteMem) (a : BitVec 64) (v : BitVec (8 * n)) (j : Nat),
      j < n → n < 2 ^ 64 →
      storeBytes mem a n v (a + BitVec.ofNat 64 j) = v.extractLsb' (8 * j) 8 := by
    intro n
    induction n with
    | zero => intro _ _ _ j hj; omega
    | succ n ih =>
      intro mem a v j hj hn
      cases j with
      | zero =>
        rw [BitVec.add_zero]
        have hne : ∀ i, i < n → a ≠ (a + 1#64) + BitVec.ofNat 64 i := by
          intro i hi heq
          rw [add_ofNat_left_succ] at heq
          have hdn := congrArg (fun x => (x - a).toNat) heq
          have hza : (a - a).toNat = 0 := by rw [BitVec.sub_self]; rfl
          have hda : (a + BitVec.ofNat 64 (i + 1) - a).toNat = i + 1 := by
            rw [BitVec.add_comm, BitVec.add_sub_cancel]
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          rw [hza, hda] at hdn
          omega
        change storeBytes (fun x => if x == a then v.extractLsb' 0 8 else mem x) (a + 1#64) n
          (v.extractLsb' 8 (8 * n)) a = _
        rw [storeBytes_apply_ne _ _ _ _ _ hne]
        simp
      | succ j' =>
        rw [← add_ofNat_left_succ]
        have h1 := ih (fun x => if x == a then v.extractLsb' 0 8 else mem x)
          (a + 1#64) (v.extractLsb' 8 (8 * n)) j' (by omega) (by omega)
        change storeBytes (fun x => if x == a then v.extractLsb' 0 8 else mem x) (a + 1#64) n
          (v.extractLsb' 8 (8 * n)) (a + 1#64 + BitVec.ofNat 64 j') = _
        rw [h1]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat]
        have hlt_sh : v.toNat >>> 8 < 2 ^ (8 * n) := by
          rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 8)]
          rw [← Nat.pow_add, show 8 * n + 8 = 8 * (n + 1) from by omega]
          exact v.isLt
        rw [Nat.mod_eq_of_lt hlt_sh]
        simp only [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add]
        have heq1 : 8 + 8 * j' = 8 * (j' + 1) := by omega
        rw [heq1]
  exact hk_step 8 m addr w k hk (by decide)

theorem storeBytes_4_to_writeWord64 (m : ByteMem) (addr : BitVec 64) (v : BitVec 32) (hi : Bool) :
    let offAddr := if hi then addr + 4#64 else addr
    let old := UInt64.ofNat (readWord64 m addr).toNat
    let newW := setHalf32 old (if hi then 1 else 0) (UInt64.ofNat v.toNat)
    storeBytes m offAddr 4 v = writeWord64 m addr newW.toBitVec := by
  intro offAddr old newW
  funext a
  have hself : ∀ (n : Nat) (mem : ByteMem) (b : BitVec 64) (w : BitVec (8 * n)) (k : Nat),
      k < n → n < 2 ^ 64 →
      storeBytes mem b n w (b + BitVec.ofNat 64 k) = w.extractLsb' (8 * k) 8 := by
    intro n
    induction n with
    | zero => intro _ _ _ k hk; omega
    | succ n ih =>
      intro mem b w k hk hn
      cases k with
      | zero =>
        rw [BitVec.add_zero]
        have hne : ∀ i, i < n → b ≠ (b + 1#64) + BitVec.ofNat 64 i := by
          intro i hi' heq
          rw [add_ofNat_left_succ] at heq
          have hdn := congrArg (fun x => (x - b).toNat) heq
          have hzb : (b - b).toNat = 0 := by rw [BitVec.sub_self]; rfl
          have hdb : (b + BitVec.ofNat 64 (i + 1) - b).toNat = i + 1 := by
            rw [BitVec.add_comm, BitVec.add_sub_cancel]
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          rw [hzb, hdb] at hdn
          omega
        change storeBytes (fun x => if x == b then w.extractLsb' 0 8 else mem x) (b + 1#64) n
          (w.extractLsb' 8 (8 * n)) b = _
        rw [storeBytes_apply_ne _ _ _ _ _ hne]
        simp
      | succ k' =>
        rw [← add_ofNat_left_succ]
        have h1 := ih (fun x => if x == b then w.extractLsb' 0 8 else mem x)
          (b + 1#64) (w.extractLsb' 8 (8 * n)) k' (by omega) (by omega)
        change storeBytes (fun x => if x == b then w.extractLsb' 0 8 else mem x) (b + 1#64) n
          (w.extractLsb' 8 (8 * n)) (b + 1#64 + BitVec.ofNat 64 k') = _
        rw [h1]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat]
        have hlt_sh : w.toNat >>> 8 < 2 ^ (8 * n) := by
          rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 8)]
          rw [← Nat.pow_add, show 8 * n + 8 = 8 * (n + 1) from by omega]
          exact w.isLt
        rw [Nat.mod_eq_of_lt hlt_sh]
        simp only [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add]
        have heq1 : 8 + 8 * k' = 8 * (k' + 1) := by omega
        rw [heq1]
  have hbyte_read : ∀ (mem : ByteMem) (b : BitVec 64) (k : Nat), k < 8 →
      mem (b + BitVec.ofNat 64 k) = (readWord64 mem b).extractLsb' (8 * k) 8 := by
    intro mem b k hk
    have hsplit : (readWord64 mem b).toNat = (loadBytes mem b (k + (8 - k))).toNat :=
      loadBytes_toNat_cast (by omega)
    rw [loadBytes_split_toNat] at hsplit
    have hs1 : (loadBytes mem (b + BitVec.ofNat 64 k) (8 - k)).toNat =
        (loadBytes mem (b + BitVec.ofNat 64 k) (1 + (7 - k))).toNat :=
      loadBytes_toNat_cast (by omega)
    rw [loadBytes_split_toNat, add_ofNat_add, loadBytes_one_eq_byte] at hs1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat]
    change (mem (b + BitVec.ofNat 64 k)).toNat = (readWord64 mem b).toNat >>> (8 * k) % 2 ^ 8
    rw [Nat.shiftRight_eq_div_pow, hsplit]
    have hlk : (loadBytes mem b k).toNat < 2 ^ (8 * k) := (loadBytes mem b k).isLt
    have h256 : 2 ^ (8 * 1) = 2 ^ 8 := rfl
    rw [Nat.add_comm _ (loadBytes mem b k).toNat,
        Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide : 0 < 2)),
        Nat.div_eq_of_lt hlk, Nat.zero_add, hs1, h256]
    have hm8 : (mem (b + BitVec.ofNat 64 k)).toNat < 2 ^ 8 := (mem (b + BitVec.ofNat 64 k)).isLt
    rw [Nat.add_comm _ (mem (b + BitVec.ofNat 64 k)).toNat, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt hm8]
  have hnewNat : newW.toBitVec.toNat =
      if hi then v.toNat * 2 ^ 32 + (readWord64 m addr).toNat % 2 ^ 32
      else (readWord64 m addr).toNat / 2 ^ 32 * 2 ^ 32 + v.toNat := by
    have hv32 : v.toNat < 2 ^ 32 := v.isLt
    have hr64 : (readWord64 m addr).toNat < 2 ^ 64 := (readWord64 m addr).isLt
    cases hi
    · change (setHalf32 old 0 (UInt64.ofNat v.toNat)).toBitVec.toNat =
          (readWord64 m addr).toNat / 2 ^ 32 * 2 ^ 32 + v.toNat
      dsimp only [old, setHalf32]
      simp only [show ((0 : UInt64) % 2 = 0) ↔ True from by decide, ↓reduceIte,
        UInt64.toNat_toBitVec, UInt64.toNat_add, UInt64.toNat_mul,
        UInt64.toNat_div, UInt64.toNat_mod, show (4294967296 : UInt64).toNat = 2 ^ 32 from rfl,
        UInt64.toNat_ofNat']
      rw [Nat.mod_eq_of_lt hr64, Nat.mod_eq_of_lt (Nat.lt_trans hv32 (by decide)),
          Nat.mod_eq_of_lt hv32, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    · have hm := Nat.mod_lt (readWord64 m addr).toNat (by decide : 0 < 2 ^ 32)
      change (setHalf32 old 1 (UInt64.ofNat v.toNat)).toBitVec.toNat =
          v.toNat * 2 ^ 32 + (readWord64 m addr).toNat % 2 ^ 32
      dsimp only [old, setHalf32]
      simp only [show ((1 : UInt64) % 2 = 0) ↔ False from by decide, ↓reduceIte,
        UInt64.toNat_toBitVec, UInt64.toNat_add, UInt64.toNat_mul,
        UInt64.toNat_mod, show (4294967296 : UInt64).toNat = 2 ^ 32 from rfl,
        UInt64.toNat_ofNat']
      rw [Nat.mod_eq_of_lt hr64, Nat.mod_eq_of_lt (Nat.lt_trans hv32 (by decide)),
          Nat.mod_eq_of_lt hv32, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  by_cases ha : ∃ k, k < 8 ∧ a = addr + BitVec.ofNat 64 k
  · rcases ha with ⟨k, hk, rfl⟩
    rw [writeWord64_apply_lt m addr newW.toBitVec k hk]
    cases hi
    · by_cases hk4 : k < 4
      · have hs := hself 4 m addr v k hk4 (by decide)
        dsimp only [offAddr]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [hs]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, hnewNat]
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.shiftRight_eq_div_pow]
        have hpow32 : 2 ^ 32 = 2 ^ (32 - 8 * k) * 2 ^ (8 * k) := by
          rw [← Nat.pow_add]; congr 1; omega
        have hdiv : ((readWord64 m addr).toNat / 2 ^ 32 * 2 ^ 32 + v.toNat) / 2 ^ (8 * k) =
            (readWord64 m addr).toNat / 2 ^ 32 * 2 ^ (32 - 8 * k) + v.toNat / 2 ^ (8 * k) := by
          rw [hpow32, ← Nat.mul_assoc, Nat.add_comm,
              Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide : 0 < 2)), Nat.add_comm]
        rw [hdiv]
        have hpow8 : 2 ^ 8 ∣ 2 ^ (32 - 8 * k) := Nat.pow_dvd_pow 2 (by omega)
        have hm0 : ((readWord64 m addr).toNat / 2 ^ 32 * 2 ^ (32 - 8 * k)) % 2 ^ 8 = 0 := by
          rw [Nat.mul_mod, Nat.dvd_iff_mod_eq_zero.mp hpow8, Nat.mul_zero, Nat.zero_mod]
        rw [Nat.add_mod, hm0, Nat.zero_add, Nat.mod_mod]
      · have hk4' : 4 ≤ k := by omega
        have hne : ∀ i, i < 4 → addr + BitVec.ofNat 64 k ≠ addr + BitVec.ofNat 64 i := by
          intro i hi' heq
          have hd := congrArg (fun x => (x - addr).toNat) heq
          simp only [BitVec.add_comm addr, BitVec.add_sub_cancel, BitVec.toNat_ofNat] at hd
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hd
          omega
        dsimp only [offAddr]; simp only [Bool.false_eq_true, ↓reduceIte]
        rw [storeBytes_apply_ne _ _ _ _ _ hne, hbyte_read m addr k hk]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, hnewNat]
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.shiftRight_eq_div_pow]
        have hvlt : v.toNat < 2 ^ 32 := v.isLt
        have hpowk : 2 ^ (8 * k) = 2 ^ 32 * 2 ^ (8 * k - 32) := by
          rw [← Nat.pow_add]; congr 1; omega
        have hstep : ((readWord64 m addr).toNat / 2 ^ 32 * 2 ^ 32 + v.toNat) /
            (2 ^ 32 * 2 ^ (8 * k - 32)) =
            (readWord64 m addr).toNat / 2 ^ 32 / 2 ^ (8 * k - 32) := by
          rw [← Nat.div_div_eq_div_mul, Nat.add_comm,
              Nat.add_mul_div_right _ _ (by decide : 0 < 2 ^ 32),
              Nat.div_eq_of_lt hvlt, Nat.zero_add]
        rw [hpowk, hstep, Nat.div_div_eq_div_mul, ← Nat.pow_add,
            show 32 + (8 * k - 32) = 8 * k by omega]
    · by_cases hk4 : 4 ≤ k
      · have haddr_k : addr + BitVec.ofNat 64 k = (addr + 4#64) + BitVec.ofNat 64 (k - 4) := by
          rw [add_ofNat_add]; congr 1; congr 1; omega
        dsimp only [offAddr]; simp only [↓reduceIte]
        rw [haddr_k, hself 4 m (addr + 4#64) v (k - 4) (by omega) (by decide)]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, hnewNat]
        simp only [↓reduceIte, Nat.shiftRight_eq_div_pow]
        have hrm : (readWord64 m addr).toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
        have hpowk : 2 ^ (8 * k) = 2 ^ 32 * 2 ^ (8 * (k - 4)) := by
          rw [← Nat.pow_add]; congr 1; omega
        rw [hpowk, ← Nat.div_div_eq_div_mul, Nat.add_comm _ ((readWord64 m addr).toNat % 2 ^ 32),
            Nat.add_mul_div_right _ _ (by decide : 0 < 2 ^ 32),
            Nat.div_eq_of_lt hrm, Nat.zero_add]
      · have hne : ∀ i, i < 4 → addr + BitVec.ofNat 64 k ≠ (addr + 4#64) + BitVec.ofNat 64 i := by
          intro i hi' heq
          rw [add_ofNat_add] at heq
          have hd := congrArg (fun x => (x - addr).toNat) heq
          simp only [BitVec.add_comm addr, BitVec.add_sub_cancel, BitVec.toNat_ofNat] at hd
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hd
          omega
        dsimp only [offAddr]; simp only [↓reduceIte]
        rw [storeBytes_apply_ne _ _ _ _ _ hne, hbyte_read m addr k hk]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, hnewNat]
        simp only [↓reduceIte, Nat.shiftRight_eq_div_pow]
        have hpow32 : 2 ^ 32 = 2 ^ (8 * k) * 2 ^ (32 - 8 * k) := by
          rw [← Nat.pow_add]; congr 1; omega
        have hmod32 : (readWord64 m addr).toNat =
            (readWord64 m addr).toNat / 2 ^ 32 * 2 ^ 32 + (readWord64 m addr).toNat % 2 ^ 32 := by
          have := (Nat.div_add_mod (readWord64 m addr).toNat (2 ^ 32)).symm; omega
        have hpow8 : 2 ^ 8 ∣ 2 ^ (32 - 8 * k) := Nat.pow_dvd_pow 2 (by omega)
        have h1 : (v.toNat * 2 ^ 32 + (readWord64 m addr).toNat % 2 ^ 32) / 2 ^ (8 * k) =
            v.toNat * 2 ^ (32 - 8 * k) + ((readWord64 m addr).toNat % 2 ^ 32) / 2 ^ (8 * k) := by
          rw [hpow32, Nat.mul_left_comm, Nat.add_comm,
              Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide : 0 < 2)), Nat.add_comm]
        have h2 : (readWord64 m addr).toNat / 2 ^ (8 * k) =
            (readWord64 m addr).toNat / 2 ^ 32 * 2 ^ (32 - 8 * k) +
              ((readWord64 m addr).toNat % 2 ^ 32) / 2 ^ (8 * k) := by
          conv => lhs; rw [hmod32, hpow32, Nat.mul_left_comm, Nat.add_comm,
            Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide : 0 < 2)), Nat.add_comm]
          rw [← hpow32]
        have hm1 : (v.toNat * 2 ^ (32 - 8 * k)) % 2 ^ 8 = 0 := by
          rw [Nat.mul_mod, Nat.dvd_iff_mod_eq_zero.mp hpow8, Nat.mul_zero, Nat.zero_mod]
        have hm2 : ((readWord64 m addr).toNat / 2 ^ 32 * 2 ^ (32 - 8 * k)) % 2 ^ 8 = 0 := by
          rw [Nat.mul_mod, Nat.dvd_iff_mod_eq_zero.mp hpow8, Nat.mul_zero, Nat.zero_mod]
        have hl : ((readWord64 m addr).toNat / 2 ^ 32 * 2 ^ (32 - 8 * k) +
              ((readWord64 m addr).toNat % 2 ^ 32) / 2 ^ (8 * k)) % 2 ^ 8 =
            (((readWord64 m addr).toNat % 2 ^ 32) / 2 ^ (8 * k)) % 2 ^ 8 := by
          rw [Nat.add_mod, hm2, Nat.zero_add, Nat.mod_mod]
        have hr : (v.toNat * 2 ^ (32 - 8 * k) +
              ((readWord64 m addr).toNat % 2 ^ 32) / 2 ^ (8 * k)) % 2 ^ 8 =
            (((readWord64 m addr).toNat % 2 ^ 32) / 2 ^ (8 * k)) % 2 ^ 8 := by
          rw [Nat.add_mod, hm1, Nat.zero_add, Nat.mod_mod]
        rw [h1, h2, hl, hr]
  · have hne8 : ∀ k, k < 8 → a ≠ addr + BitVec.ofNat 64 k := fun k hk heq => ha ⟨k, hk, heq⟩
    have hne4 : ∀ i, i < 4 → a ≠ offAddr + BitVec.ofNat 64 i := by
      intro i hi' heq
      cases hi
      · exact ha ⟨i, by omega, by simpa [offAddr] using heq⟩
      · exact ha ⟨4 + i, by omega, by
          dsimp only [offAddr] at heq; simp only [↓reduceIte] at heq
          rwa [add_ofNat_add] at heq⟩
    change storeBytes m offAddr 4 v a = storeBytes m addr 8 newW.toBitVec a
    rw [storeBytes_apply_ne _ _ _ _ _ hne4, storeBytes_apply_ne _ _ _ _ _ hne8]

/-! ## 2. General Program Table, Layout, Memory Relation, & Resource Accounting -/

def Tab.bytePosOkB (tab : Tab) (a : ArrId) : Bool :=
  let p := tab.pos8 a
  (p < tab.nb) &&
  (tab.lmap.find (TieredArray.t0 a).code == some p) &&
  (tab.arrAt[p]? == some (TieredArray.t0 a))

def Tab.wordPosOkB (tab : Tab) (s : TieredArray) : Bool :=
  let p := tab.pos64 s
  (tab.nb ≤ p) && (p < tab.nb + tab.nw) &&
  (tab.lmap.find s.code == some p) &&
  (tab.arrAt[p]? == some s)

def Tab.tieredOkB (tab : Tab) (a : ArrId) : Bool :=
  tab.wordPosOkB (TieredArray.t0 a) &&
  tab.wordPosOkB (tier1 a) &&
  (tab.pos64 (tier1 a) == tab.pos64 (TieredArray.t0 a) + 1)

def Tab.romSliceOkB (tab : Tab) (d : List UInt8) : Bool :=
  let off := romIdx d tab.rom
  (off + d.length ≤ tab.rom.length) &&
  ((List.range d.length).all fun j => tab.rom[off + j]? == d[j]?)

def Tab.arrAtOkB (tab : Tab) : Bool :=
  (tab.arrAt.length == tab.nb + tab.nw) &&
  ((List.range tab.nb).all fun p =>
    match tab.arrAt[p]? with
    | some s => !s.hi && tab.bytePosOkB s.arr
    | none => false) &&
  ((List.range tab.nw).all fun j =>
    let p := tab.nb + j
    match tab.arrAt[p]? with
    | some s => tab.wordPosOkB s
    | none => false)

def tier32OkB (tab : Tab) (a : ArrId) (t : Expr) : Bool :=
  match t with
  | .const w => if w.toNat % 2 == 0 then tab.wordPosOkB (.t0 a) else tab.tieredOkB a
  | _ => tab.tieredOkB a

def exprOkB (tab : Tab) (nl : Nat) : Expr → Bool
  | .const _ => true
  | .var x => x < nl
  | .bin _ a b | .cmpw _ a b => exprOkB tab nl a && exprOkB tab nl b
  | .ld8 a i => tab.bytePosOkB a && exprOkB tab nl i
  | .ld64 a i => tab.wordPosOkB (TieredArray.t0 a) && exprOkB tab nl i
  | .len8 a => tab.bytePosOkB a
  | .len64 a => tab.wordPosOkB (TieredArray.t0 a)
  | .ldc d i => tab.romSliceOkB d && exprOkB tab nl i
  | .glob g => g.id < tab.ng
  | .ld64t a t i | .ld32h a t i _ =>
    tab.tieredOkB a && exprOkB tab nl t && exprOkB tab nl i
  | .ld32t a t i =>
    tier32OkB tab a t && exprOkB tab nl t && exprOkB tab nl i
  | .len64t a t => tab.tieredOkB a && exprOkB tab nl t
  | .ld8x8 (.arr a) i => tab.bytePosOkB a && exprOkB tab nl i
  | .ld8x8 (.rom d) i => tab.romSliceOkB d && exprOkB tab nl i

def condOkB (tab : Tab) (nl : Nat) : Cond → Bool
  | .cmp _ a b => exprOkB tab nl a && exprOkB tab nl b
  | .and p q | .or p q => condOkB tab nl p && condOkB tab nl q
  | .not p => condOkB tab nl p

def warrOkB (tab : Tab) (nl : Nat) : WArr → Bool
  | .plain a => tab.wordPosOkB (TieredArray.t0 a)
  | .tier a t => tab.tieredOkB a && exprOkB tab nl t

def bsrcOkB (tab : Tab) : BSrc → Bool
  | .arr a => tab.bytePosOkB a
  | .rom d => tab.romSliceOkB d

def stmtOkB (tab : Tab) (p : Prog) (nl : Nat) (inLoop : Bool) : Stmt → Bool
  | .skip => true
  | .brk => inLoop
  | .set x e => (x < nl) && exprOkB tab nl e
  | .st8 _ _ _ => false
  | .st64 a i e => tab.wordPosOkB (TieredArray.t0 a) && exprOkB tab nl i && exprOkB tab nl e
  | .seq s1 s2 => stmtOkB tab p nl inLoop s1 && stmtOkB tab p nl inLoop s2
  | .ite c s1 s2 => condOkB tab nl c && stmtOkB tab p nl inLoop s1 && stmtOkB tab p nl inLoop s2
  | .while c s => condOkB tab nl c && stmtOkB tab p nl true s
  | .ret es => (es.length ≤ tab.nres) && es.all (exprOkB tab nl)
  | .call xs f args =>
    (p.lookup f).isSome && (xs.all (· < nl)) && args.all (exprOkB tab nl)
  | .abort e => exprOkB tab nl e
  | .gset g e => (g.id < tab.ng) && exprOkB tab nl e
  | .st64t a t i e =>
    tab.tieredOkB a && exprOkB tab nl t && exprOkB tab nl i && exprOkB tab nl e
  | .st32t a t i e =>
    tier32OkB tab a t && exprOkB tab nl t && exprOkB tab nl i && exprOkB tab nl e
  | .copy64 d di s si n =>
    warrOkB tab nl d && exprOkB tab nl di && warrOkB tab nl s &&
    exprOkB tab nl si && exprOkB tab nl n
  | .copy8w d di s si n =>
    warrOkB tab nl d && exprOkB tab nl di && bsrcOkB tab s &&
    exprOkB tab nl si && exprOkB tab nl n
  | .scan8 x s i e c =>
    (x < nl) && bsrcOkB tab s && exprOkB tab nl i && exprOkB tab nl e &&
    (256 ≤ c.length) && tab.romSliceOkB c

def fnFrameBytes (fd : FunDecl) : Nat :=
  8 * (1 + numLocalsFn fd + maxTempsStmt fd.body)

def progOkB (tab : Tab) (p : Prog) : Bool :=
  tab.arrAtOkB &&
  (1 ≤ tab.nres) &&
  (p.map Prod.fst).Nodup &&
  p.all fun (_, fd) => stmtOkB tab p (numLocalsFn fd) false fd.body

theorem Tab.bytePosOk_lt {tab : Tab} {a : ArrId} (h : tab.bytePosOkB a = true) :
    tab.pos8 a < tab.nb ∧ tab.pos8 a < tab.nb + tab.nw ∧
    tab.lmap.find (TieredArray.t0 a).code = some (tab.pos8 a) ∧
    tab.arrAt[tab.pos8 a]? = some (TieredArray.t0 a) := by
  simp only [Tab.bytePosOkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1, by omega, h.1.2, h.2⟩

theorem Tab.wordPosOk_lt {tab : Tab} {s : TieredArray} (h : tab.wordPosOkB s = true) :
    tab.nb ≤ tab.pos64 s ∧ tab.pos64 s < tab.nb + tab.nw ∧
    tab.lmap.find s.code = some (tab.pos64 s) ∧
    tab.arrAt[tab.pos64 s]? = some s := by
  simp only [Tab.wordPosOkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem Tab.bytePosOk_inj {tab : Tab} {a1 a2 : ArrId}
    (h1 : tab.bytePosOkB a1 = true) (h2 : tab.bytePosOkB a2 = true)
    (heq : tab.pos8 a1 = tab.pos8 a2) : a1 = a2 := by
  have k1 := (Tab.bytePosOk_lt h1).2.2.2
  have k2 := (Tab.bytePosOk_lt h2).2.2.2
  rw [heq, k2] at k1
  cases k1
  rfl

theorem Tab.wordPosOk_inj {tab : Tab} {s1 s2 : TieredArray}
    (h1 : tab.wordPosOkB s1 = true) (h2 : tab.wordPosOkB s2 = true)
    (heq : tab.pos64 s1 = tab.pos64 s2) : s1 = s2 := by
  have k1 := (Tab.wordPosOk_lt h1).2.2.2
  have k2 := (Tab.wordPosOk_lt h2).2.2.2
  rw [heq, k2] at k1
  cases k1
  rfl

theorem Tab.byte_ne_word_pos {tab : Tab} {a : ArrId} {s : TieredArray}
    (hb : tab.bytePosOkB a = true) (hw : tab.wordPosOkB s = true) :
    tab.pos8 a ≠ tab.pos64 s := by
  have k1 := (Tab.bytePosOk_lt hb).1
  have k2 := (Tab.wordPosOk_lt hw).1
  omega

theorem Tab.romSliceOk_spec {tab : Tab} {d : List UInt8} (h : tab.romSliceOkB d = true) :
    romIdx d tab.rom + d.length ≤ tab.rom.length ∧
    ∀ j (hj : j < d.length), tab.rom[romIdx d tab.rom + j]? = some d[j] := by
  simp only [Tab.romSliceOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, beq_iff_eq] at h
  refine ⟨h.1, fun j hj => ?_⟩
  have he := h.2 j hj
  rw [he]; simp [hj]

structure ProgLayout (tab : Tab) where
  T : BitVec 64
  hTAlign : isAligned T 8 = true
  tabBytes : Nat
  hTabMin : tab.args + 8 * 1 ≤ (tabBytes : Int)
  hTValid : T.toNat + tabBytes ≤ 2 ^ 64
  stackLimit : BitVec 64
  stackTop : BitVec 64
  hLimAlign : isAligned stackLimit 8 = true
  hTopAlign : isAligned stackTop 8 = true
  hStackLe : stackLimit.toNat ≤ stackTop.toNat
  hStackValid : stackTop.toNat ≤ 2 ^ 64
  base8 : ArrId → BitVec 64
  cap8 : ArrId → Nat
  h8Valid : ∀ a, (base8 a).toNat + cap8 a ≤ 2 ^ 64
  base64 : TieredArray → BitVec 64
  cap64 : TieredArray → Nat
  h64Align : ∀ s, isAligned (base64 s) 8 = true
  h64Valid : ∀ s, (base64 s).toNat + 8 * cap64 s ≤ 2 ^ 64
  htabDisjStack : MemSpan.disjoint ⟨T, tabBytes⟩ ⟨stackLimit, stackTop.toNat - stackLimit.toNat⟩
  h8DisjStack : ∀ a, tab.bytePosOkB a = true →
    MemSpan.disjoint ⟨base8 a, cap8 a⟩ ⟨stackLimit, stackTop.toNat - stackLimit.toNat⟩
  h8DisjTab : ∀ a, tab.bytePosOkB a = true → MemSpan.disjoint ⟨base8 a, cap8 a⟩ ⟨T, tabBytes⟩
  h64DisjStack : ∀ s, tab.wordPosOkB s = true →
    MemSpan.disjoint ⟨base64 s, 8 * cap64 s⟩ ⟨stackLimit, stackTop.toNat - stackLimit.toNat⟩
  h64DisjTab : ∀ s, tab.wordPosOkB s = true →
    MemSpan.disjoint ⟨base64 s, 8 * cap64 s⟩ ⟨T, tabBytes⟩
  h8Disj8 : ∀ a1 a2, tab.bytePosOkB a1 = true → tab.bytePosOkB a2 = true → a1 ≠ a2 →
    MemSpan.disjoint ⟨base8 a1, cap8 a1⟩ ⟨base8 a2, cap8 a2⟩
  h64Disj64 : ∀ s1 s2, tab.wordPosOkB s1 = true → tab.wordPosOkB s2 = true → s1 ≠ s2 →
    MemSpan.disjoint ⟨base64 s1, 8 * cap64 s1⟩ ⟨base64 s2, 8 * cap64 s2⟩
  h8Disj64 : ∀ a s, tab.bytePosOkB a = true → tab.wordPosOkB s = true →
    MemSpan.disjoint ⟨base8 a, cap8 a⟩ ⟨base64 s, 8 * cap64 s⟩

def ProgLayout.tabSpan {tab : Tab} (L : ProgLayout tab) : MemSpan :=
  ⟨L.T, L.tabBytes⟩

def ProgLayout.stackSpan {tab : Tab} (L : ProgLayout tab) : MemSpan :=
  ⟨L.stackLimit, L.stackTop.toNat - L.stackLimit.toNat⟩

def ProgLayout.arr8Span {tab : Tab} (L : ProgLayout tab) (a : ArrId) : MemSpan :=
  ⟨L.base8 a, L.cap8 a⟩

def ProgLayout.arr64Span {tab : Tab} (L : ProgLayout tab) (s : TieredArray) : MemSpan :=
  ⟨L.base64 s, 8 * L.cap64 s⟩

def ProgLayout.resGlobSpan {tab : Tab} (L : ProgLayout tab) : MemSpan :=
  ⟨L.T + BitVec.ofNat 64 tab.resBase.toNat, 8 * (tab.nxres + tab.ng)⟩

theorem ProgLayout.tabSpan_valid {tab : Tab} (L : ProgLayout tab) : L.tabSpan.valid :=
  L.hTValid

theorem ProgLayout.arr8Span_valid {tab : Tab} (L : ProgLayout tab) (a : ArrId) :
    (L.arr8Span a).valid := L.h8Valid a

theorem ProgLayout.arr64Span_valid {tab : Tab} (L : ProgLayout tab) (s : TieredArray) :
    (L.arr64Span s).valid := L.h64Valid s

theorem ProgLayout.stackSpan_valid {tab : Tab} (L : ProgLayout tab) : L.stackSpan.valid := by
  simp only [MemSpan.valid, ProgLayout.stackSpan]
  have hle := L.hStackLe
  have hv := L.hStackValid
  omega

theorem ProgLayout.tabMin_strong {tab : Tab} (L : ProgLayout tab) :
    tab.globBase + 8 * (tab.ng : Int) ≤ (L.tabBytes : Int) := by
  have h := L.hTabMin
  simp only [Tab.args] at h
  omega

theorem ProgLayout.romBase_nonneg (tab : Tab) : 0 ≤ tab.romBase := by
  simp [Tab.romBase]; omega

theorem ProgLayout.resBase_nonneg (tab : Tab) : 0 ≤ tab.resBase := by
  simp [Tab.resBase, Tab.romBase]; omega

theorem ProgLayout.resGlob_sub_tab {tab : Tab} (L : ProgLayout tab) :
    L.resGlobSpan.sub L.tabSpan := by
  intro a ⟨k, hk, ha⟩
  subst ha
  dsimp only [ProgLayout.resGlobSpan] at hk ⊢
  refine ⟨tab.resBase.toNat + k, ?_, ?_⟩
  · have hmin := L.tabMin_strong
    have hnn := ProgLayout.resBase_nonneg tab
    have hcoe : ((tab.resBase.toNat : Nat) : Int) = tab.resBase := Int.toNat_of_nonneg hnn
    simp only [Tab.globBase] at hmin
    dsimp only [ProgLayout.tabSpan]
    omega
  · simp only [ProgLayout.tabSpan, BitVec.add_assoc, BitVec.ofNat_add]

theorem ProgLayout.tab_len8_bound {tab : Tab} (L : ProgLayout tab) {a : ArrId}
    (ha : tab.bytePosOkB a = true) :
    8 * (2 + (tab.nb + tab.nw) + tab.pos8 a) + 8 ≤ L.tabBytes := by
  have h1 := L.tabMin_strong
  have h2 := (Tab.bytePosOk_lt ha).2.1
  simp only [Tab.globBase, Tab.resBase, Tab.romBase] at h1
  omega

theorem ProgLayout.tab_base8_bound {tab : Tab} (L : ProgLayout tab) {a : ArrId}
    (ha : tab.bytePosOkB a = true) :
    8 * (2 + tab.pos8 a) + 8 ≤ L.tabBytes := by
  have h1 := L.tabMin_strong
  have h2 := (Tab.bytePosOk_lt ha).2.1
  simp only [Tab.globBase, Tab.resBase, Tab.romBase] at h1
  omega

theorem ProgLayout.tab_len64_bound {tab : Tab} (L : ProgLayout tab) {s : TieredArray}
    (hs : tab.wordPosOkB s = true) :
    8 * (2 + (tab.nb + tab.nw) + tab.pos64 s) + 8 ≤ L.tabBytes := by
  have h1 := L.tabMin_strong
  have h2 := (Tab.wordPosOk_lt hs).2.1
  simp only [Tab.globBase, Tab.resBase, Tab.romBase] at h1
  omega

theorem ProgLayout.tab_base64_bound {tab : Tab} (L : ProgLayout tab) {s : TieredArray}
    (hs : tab.wordPosOkB s = true) :
    8 * (2 + tab.pos64 s) + 8 ≤ L.tabBytes := by
  have h1 := L.tabMin_strong
  have h2 := (Tab.wordPosOk_lt hs).2.1
  simp only [Tab.globBase, Tab.resBase, Tab.romBase] at h1
  omega

theorem ProgLayout.tab_globOff_bound {tab : Tab} (L : ProgLayout tab) (g : GVar)
    (hg : g.id < tab.ng) :
    8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres + g.id) + 8 ≤ L.tabBytes := by
  have h1 := L.tabMin_strong
  simp only [Tab.globBase, Tab.resBase, Tab.romBase] at h1
  omega

theorem ProgLayout.tab_rom_bound {tab : Tab} (L : ProgLayout tab) :
    tab.romBase.toNat + tab.rom.length ≤ L.tabBytes := by
  have h1 := L.tabMin_strong
  simp only [Tab.globBase, Tab.resBase, Tab.romBase, Tab.romWords] at h1 ⊢
  have hnn : 0 ≤ tab.romBase := by simp [Tab.romBase]; omega
  omega

theorem ProgLayout.tab_resOff_bound {tab : Tab} (L : ProgLayout tab) {i : Nat}
    (h1 : maxRes ≤ i) (h2 : i < tab.nres) :
    tab.resBase.toNat + 8 * (i - maxRes) + 8 ≤ L.tabBytes := by
  have hm := L.tabMin_strong
  simp only [Tab.globBase, Tab.resBase, Tab.romBase, Tab.nxres] at hm ⊢
  have hnn : 0 ≤ tab.resBase := by simp [Tab.resBase, Tab.romBase]; omega
  omega

def ProgMemRel (tab : Tab) (L : ProgLayout tab) (rmem : ByteMem) (m : _root_.L.Mem) : Prop :=
  (∀ a, tab.bytePosOkB a = true →
    (m.arr8 a).size ≤ L.cap8 a ∧
    (m.arr8 a).size < 2 ^ 64 ∧
    readWord64 rmem (L.T + BitVec.ofInt 64 (tab.len8 a)) = BitVec.ofNat 64 (m.arr8 a).size ∧
    readWord64 rmem (L.T + BitVec.ofInt 64 (tab.base8 a)) = L.base8 a ∧
    (∀ i, (hi : i < (m.arr8 a).size) →
      rmem (L.base8 a + BitVec.ofNat 64 i) = (m.arr8 a)[i].toBitVec)) ∧
  (∀ s, tab.wordPosOkB s = true →
    (m.arr64 s).size ≤ L.cap64 s ∧
    (m.arr64 s).size < 2 ^ 61 ∧
    readWord64 rmem (L.T + BitVec.ofInt 64 (tab.len64 s)) = BitVec.ofNat 64 (m.arr64 s).size ∧
    readWord64 rmem (L.T + BitVec.ofInt 64 (tab.base64 s)) = L.base64 s ∧
    (∀ i, (hi : i < (m.arr64 s).size) →
      readWord64 rmem (L.base64 s + BitVec.ofNat 64 (8 * i)) = (m.arr64 s)[i].toBitVec)) ∧
  (∀ k, (hk : k < tab.rom.length) →
    rmem (L.T + BitVec.ofNat 64 (tab.romBase.toNat + k)) = tab.rom[k].toBitVec) ∧
  (∀ g : GVar, g.id < tab.ng →
    readWord64 rmem (L.T + BitVec.ofInt 64 (tab.globOff g)) = (m.glob g).toBitVec)

def ProgFrameOk {tab : Tab} (_L : ProgLayout tab) (sp : BitVec 64)
    (rmem : ByteMem) (nlocals : Nat) (loc : _root_.L.Locals) : Prop :=
  ∀ x, x < nlocals → readWord64 rmem (sp + BitVec.ofInt 64 (slotOff x)) = (loc x).toBitVec

/-- Predicate capturing every memory address a function at stack pointer `sp` (owning
    `[L.stackLimit, sp + 8 * (1 + nl + nt))` except its saved `ra` at `[sp, sp + 8)`)
    is permitted to modify, together with `resGlobSpan`, byte arrays, and word arrays. -/
def FnWriteMask {tab : Tab} (L : ProgLayout tab) (sp : BitVec 64) (nl nt : Nat)
    (a : BitVec 64) : Prop :=
  (L.stackSpan.contains a ∧
    (a.toNat < sp.toNat ∨ (sp.toNat + 8 ≤ a.toNat ∧ a.toNat < sp.toNat + 8 * (1 + nl + nt)))) ∨
  L.resGlobSpan.contains a ∨
  (∃ idx, tab.bytePosOkB idx = true ∧ (L.arr8Span idx).contains a) ∨
  (∃ s, tab.wordPosOkB s = true ∧ (L.arr64Span s).contains a)

def ProgMemOutside (S : BitVec 64 → Prop) (m1 m2 : ByteMem) : Prop :=
  ∀ a, ¬S a → m2 a = m1 a

theorem ProgMemOutside.refl (S : BitVec 64 → Prop) (m : ByteMem) : ProgMemOutside S m m :=
  fun _ _ => rfl

theorem ProgMemOutside.trans {S : BitVec 64 → Prop} {m1 m2 m3 : ByteMem}
    (h12 : ProgMemOutside S m1 m2) (h23 : ProgMemOutside S m2 m3) :
    ProgMemOutside S m1 m3 :=
  fun a ha => (h23 a ha).trans (h12 a ha)

theorem ProgMemOutside.mono {S1 S2 : BitVec 64 → Prop} {m1 m2 : ByteMem}
    (hsub : ∀ a, S1 a → S2 a) (h : ProgMemOutside S1 m1 m2) : ProgMemOutside S2 m1 m2 :=
  fun a ha => h a (fun h1 => ha (hsub a h1))

theorem ProgMemOutside.of_memEqOutside {s : MemSpan} {S : BitVec 64 → Prop} {m1 m2 : ByteMem}
    (hsub : ∀ a, s.contains a → S a) (h : MemEqOutside s m1 m2) : ProgMemOutside S m1 m2 :=
  fun a ha => h a (fun hs => ha (hsub a hs))

theorem ProgMemOutside.readWord64_eq {S : BitVec 64 → Prop} {m1 m2 : ByteMem}
    (heq : ProgMemOutside S m1 m2) (addr : BitVec 64)
    (hdisj : ∀ k, k < 8 → ¬S (addr + BitVec.ofNat 64 k)) :
    readWord64 m2 addr = readWord64 m1 addr := by
  apply loadBytes_congr
  intro k hk
  exact heq (addr + BitVec.ofNat 64 k) (hdisj k hk)

theorem ProgFrameOk.of_memEqOutside {tab : Tab} {L : ProgLayout tab} {sp : BitVec 64}
    {m1 m2 : ByteMem} {nl _nt : Nat} {loc : _root_.L.Locals} {s : MemSpan}
    (hdisj : ∀ x, x < nl → MemDisjoint s (slotSpan sp (1 + x)))
    (heq : MemEqOutside s m1 m2) (hfr : ProgFrameOk L sp m1 nl loc) :
    ProgFrameOk L sp m2 nl loc := by
  intro x hx
  rw [← hfr x hx]
  apply MemEqOutside.readWord64_eq heq
  intro k hk
  rw [slotOff_ofInt]
  exact (hdisj x hx).symm _ ⟨k, hk, rfl⟩

theorem ProgFrameOk.of_tempSpan {tab : Tab} {L : ProgLayout tab} {sp : BitVec 64}
    {nl tmp nt : Nat} (hf : (frameSpan sp nl nt).valid) (hle : tmp ≤ nt)
    {m1 m2 : ByteMem} {loc : _root_.L.Locals}
    (heq : MemEqOutside (tempSpan sp nl tmp nt) m1 m2)
    (hfr : ProgFrameOk L sp m1 nl loc) :
    ProgFrameOk L sp m2 nl loc :=
  ProgFrameOk.of_memEqOutside (_nt := nt)
    (fun _ hx => (slotSpan_memDisjoint_tempSpan hf hle (by omega)).symm)
    heq hfr

theorem ProgMemRel.of_stack_eqOutside {tab : Tab} {L : ProgLayout tab}
    {m1 m2 : ByteMem} {lm : _root_.L.Mem} {s : MemSpan}
    (hsub : s.sub L.stackSpan) (heq : MemEqOutside s m1 m2) (hrel : ProgMemRel tab L m1 lm) :
    ProgMemRel tab L m2 lm := by
  rcases hrel with ⟨ha, hs64, hrom, hg⟩
  have hdisjT : MemDisjoint s L.tabSpan :=
    MemDisjoint.of_sub_left hsub
      (MemSpan.disjoint_to_memDisjoint L.stackSpan_valid L.tabSpan_valid L.htabDisjStack.symm)
  have hdisj8 : ∀ a, tab.bytePosOkB a = true → MemDisjoint s (L.arr8Span a) := fun a haOk =>
    MemDisjoint.of_sub_left hsub
      (MemSpan.disjoint_to_memDisjoint L.stackSpan_valid (L.arr8Span_valid a) (L.h8DisjStack a haOk).symm)
  have hdisj64 : ∀ s64, tab.wordPosOkB s64 = true → MemDisjoint s (L.arr64Span s64) := fun s64 hsOk =>
    MemDisjoint.of_sub_left hsub
      (MemSpan.disjoint_to_memDisjoint L.stackSpan_valid (L.arr64Span_valid s64) (L.h64DisjStack s64 hsOk).symm)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a haOk
    rcases ha a haOk with ⟨hcap, hlt, hlen, hbase, hbytes⟩
    refine ⟨hcap, hlt, ?_, ?_, ?_⟩
    · rw [← hlen]
      apply MemEqOutside.readWord64_eq heq
      intro k hk
      rw [Tab.len8_eq_nat, int_mul8_ofInt]
      exact hdisjT.symm _ (MemSpan.sub_range _ 8 (L.tab_len8_bound haOk) k hk)
    · rw [← hbase]
      apply MemEqOutside.readWord64_eq heq
      intro k hk
      rw [Tab.base8_eq_nat, int_mul8_ofInt]
      exact hdisjT.symm _ (MemSpan.sub_range _ 8 (L.tab_base8_bound haOk) k hk)
    · intro i hi
      rw [← hbytes i hi]
      exact heq _ ((hdisj8 a haOk).symm _ ⟨i, by dsimp only [ProgLayout.arr8Span]; omega, rfl⟩)
  · intro s64 hsOk
    rcases hs64 s64 hsOk with ⟨hcap, hlt, hlen, hbase, hwords⟩
    refine ⟨hcap, hlt, ?_, ?_, ?_⟩
    · rw [← hlen]
      apply MemEqOutside.readWord64_eq heq
      intro k hk
      rw [Tab.len64_eq_nat, int_mul8_ofInt]
      exact hdisjT.symm _ (MemSpan.sub_range _ 8 (L.tab_len64_bound hsOk) k hk)
    · rw [← hbase]
      apply MemEqOutside.readWord64_eq heq
      intro k hk
      rw [Tab.base64_eq_nat, int_mul8_ofInt]
      exact hdisjT.symm _ (MemSpan.sub_range _ 8 (L.tab_base64_bound hsOk) k hk)
    · intro i hi
      rw [← hwords i hi]
      apply MemEqOutside.readWord64_eq heq
      intro k hk
      exact (hdisj64 s64 hsOk).symm _
        (MemSpan.sub_range (s := L.arr64Span s64) (8 * i) 8 (by simp only [ProgLayout.arr64Span]; omega) k hk)
  · intro k hk
    rw [← hrom k hk]
    refine heq _ (hdisjT.symm _ ⟨tab.romBase.toNat + k, ?_, ?_⟩)
    · have hrb := L.tab_rom_bound; dsimp only [ProgLayout.tabSpan]; omega
    · simp only [ProgLayout.tabSpan, BitVec.ofNat_add]
  · intro g hgBound
    rw [← hg g hgBound]
    apply MemEqOutside.readWord64_eq heq
    intro k hk
    rw [Tab.globOff_eq_nat, int_mul8_ofInt]
    exact hdisjT.symm _ (MemSpan.sub_range _ 8 (L.tab_globOff_bound g hgBound) k hk)

theorem ProgLayout.frame_sub_stackSpan {tab : Tab} (L : ProgLayout tab)
    {sp : BitVec 64} {nl nt : Nat}
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat) :
    (frameSpan sp nl nt).sub L.stackSpan := by
  intro a ⟨k, hk, ha⟩
  subst ha
  dsimp only [frameSpan, MemSpan.contains, ProgLayout.stackSpan] at hk ⊢
  refine ⟨sp.toNat - L.stackLimit.toNat + k, by omega, ?_⟩
  have hbase : L.stackLimit + BitVec.ofNat 64 (sp.toNat - L.stackLimit.toNat) = sp := by
    apply BitVec.eq_of_toNat_eq
    have h1 : L.stackLimit.toNat < 2 ^ 64 := L.stackLimit.isLt
    have h2 : sp.toNat - L.stackLimit.toNat < 2 ^ 64 := by omega
    have hlt : L.stackLimit.toNat + (sp.toNat - L.stackLimit.toNat) < 2 ^ 64 := by
      have := L.hStackValid; omega
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt hlt]
    omega
  conv => lhs; rw [← hbase]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem ProgLayout.fnWriteMask_mono_callee {tab : Tab} (L : ProgLayout tab)
    {sp sp' : BitVec 64} {nl nt nl' nt' : Nat}
    (_hlo : L.stackLimit.toNat ≤ sp'.toNat)
    (hsub : sp'.toNat + 8 * (1 + nl' + nt') ≤ sp.toNat)
    (_hle : sp.toNat ≤ L.stackTop.toNat) :
    ∀ a, FnWriteMask L sp' nl' nt' a → FnWriteMask L sp nl nt a := by
  intro a ha
  rcases ha with ⟨hs, hcase⟩ | hres | h8 | h64
  · left
    refine ⟨hs, Or.inl ?_⟩
    rcases hcase with hlt | ⟨_, hlt⟩
    · omega
    · omega
  · exact Or.inr (Or.inl hres)
  · exact Or.inr (Or.inr (Or.inl h8))
  · exact Or.inr (Or.inr (Or.inr h64))

theorem ProgLayout.fnWriteMask_of_slot {tab : Tab} (L : ProgLayout tab)
    {sp : BitVec 64} {nl nt j : Nat}
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (hj1 : 1 ≤ j) (hj2 : j < 1 + nl + nt) :
    ∀ k, k < 8 → FnWriteMask L sp nl nt (sp + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 k) := by
  intro k hk
  left
  have hsub := L.frame_sub_stackSpan hlo hhi
  have hcont : (frameSpan sp nl nt).contains (sp + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 k) :=
    ⟨8 * j + k, by simp only [frameSpan]; omega,
     by dsimp only [frameSpan]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]⟩
  refine ⟨hsub _ hcont, Or.inr ?_⟩
  have hlt64 : sp.toNat + (8 * j + k) < 2 ^ 64 := by
    have := L.hStackValid; omega
  have haNat : (sp + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 k).toNat = sp.toNat + 8 * j + k := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show 8 * j + k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hlt64, Nat.add_assoc]
  omega

theorem ProgLayout.fnWriteMask_of_tempSpan {tab : Tab} (L : ProgLayout tab)
    {sp : BitVec 64} {nl tmp nt : Nat}
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (hle : tmp ≤ nt) :
    ∀ a, (tempSpan sp nl tmp nt).contains a → FnWriteMask L sp nl nt a := by
  intro a ⟨k, hk, ha⟩
  subst ha
  dsimp only [tempSpan] at hk ⊢
  left
  have hsub := L.frame_sub_stackSpan hlo hhi
  have hcont : (frameSpan sp nl nt).contains
      (sp + BitVec.ofNat 64 (8 * (1 + nl + tmp)) + BitVec.ofNat 64 k) :=
    ⟨8 * (1 + nl + tmp) + k, by simp only [frameSpan]; omega,
     by dsimp only [frameSpan]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]⟩
  refine ⟨hsub _ hcont, Or.inr ?_⟩
  have hlt64 : sp.toNat + (8 * (1 + nl + tmp) + k) < 2 ^ 64 := by
    have := L.hStackValid; omega
  have haNat : (sp + BitVec.ofNat 64 (8 * (1 + nl + tmp)) + BitVec.ofNat 64 k).toNat =
      sp.toNat + 8 * (1 + nl + tmp) + k := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show 8 * (1 + nl + tmp) + k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hlt64]
    omega
  omega

theorem ProgLayout.tabResBase_disj_fnWriteMask {tab : Tab} (L : ProgLayout tab)
    {sp : BitVec 64} {nl nt : Nat}
    (hk_lt : ∀ k, k < tab.resBase.toNat → (L.tabSpan).contains (L.T + BitVec.ofNat 64 k)) :
    ∀ (off : Nat), off < tab.resBase.toNat →
      ¬FnWriteMask L sp nl nt (L.T + BitVec.ofNat 64 off) := by
  intro off hoff hm
  have htc := hk_lt off hoff
  rcases hm with ⟨hs, _⟩ | hres | ⟨a, haOk, ha⟩ | ⟨s, hsOk, hs64⟩
  · exact (MemSpan.disjoint_to_memDisjoint L.tabSpan_valid L.stackSpan_valid L.htabDisjStack) _ htc hs
  · rcases hres with ⟨k, hk, heq⟩
    have hmn := L.tabMin_strong
    have hv := L.hTValid
    have hnn := ProgLayout.resBase_nonneg tab
    have hcoe : ((tab.resBase.toNat : Nat) : Int) = tab.resBase := Int.toNat_of_nonneg hnn
    simp only [Tab.globBase] at hmn
    have hoff_lt : off < L.tabBytes := by omega
    have hk_lt2 : tab.resBase.toNat + k < L.tabBytes := by
      dsimp only [ProgLayout.resGlobSpan] at hk; omega
    have h1 : (L.T + BitVec.ofNat 64 off).toNat = L.T.toNat + off := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)]
    have h2 : (L.resGlobSpan.base + BitVec.ofNat 64 k).toNat =
        L.T.toNat + tab.resBase.toNat + k := by
      dsimp only [ProgLayout.resGlobSpan]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    have heqNat := congrArg BitVec.toNat heq
    rw [h1, h2] at heqNat
    omega
  · exact (MemSpan.disjoint_to_memDisjoint (L.arr8Span_valid a) L.tabSpan_valid (L.h8DisjTab a haOk)) _ ha htc
  · exact (MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid s) L.tabSpan_valid (L.h64DisjTab s hsOk)) _ hs64 htc

theorem ProgLayout.tabHeader_not_fnWriteMask {tab : Tab} (L : ProgLayout tab)
    {sp : BitVec 64} {nl nt : Nat} {off : Nat} (hoff : off < tab.resBase.toNat) :
    ¬FnWriteMask L sp nl nt (L.T + BitVec.ofNat 64 off) := by
  apply L.tabResBase_disj_fnWriteMask
  · intro k hk
    refine ⟨k, ?_, rfl⟩
    have hmn := L.tabMin_strong
    have hnn := ProgLayout.resBase_nonneg tab
    have hcoe : ((tab.resBase.toNat : Nat) : Int) = tab.resBase := Int.toNat_of_nonneg hnn
    simp only [Tab.globBase] at hmn
    dsimp only [ProgLayout.tabSpan]
    omega
  · exact hoff

theorem ProgLayout.outerStack_not_fnWriteMask {tab : Tab} (L : ProgLayout tab)
    {sp : BitVec 64} {nl nt : Nat} {addr : BitVec 64}
    (hStack : L.stackSpan.contains addr)
    (h1 : sp.toNat ≤ addr.toNat)
    (h2 : ¬(sp.toNat + 8 ≤ addr.toNat ∧ addr.toNat < sp.toNat + 8 * (1 + nl + nt))) :
    ¬FnWriteMask L sp nl nt addr := by
  intro hm
  rcases hm with ⟨hs, hcase⟩ | hres | ⟨idx, hOk, ha⟩ | ⟨s, hOk, hs64⟩
  · rcases hcase with hlt | hmid
    · omega
    · exact h2 hmid
  · exact (MemSpan.disjoint_to_memDisjoint L.tabSpan_valid L.stackSpan_valid L.htabDisjStack)
      _ (L.resGlob_sub_tab _ hres) hStack
  · exact (MemSpan.disjoint_to_memDisjoint (L.arr8Span_valid idx) L.stackSpan_valid (L.h8DisjStack idx hOk))
      _ ha hStack
  · exact (MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid s) L.stackSpan_valid (L.h64DisjStack s hOk))
      _ hs64 hStack

/-! ## 3. General Purity Lemmas & Expression/Condition Helpers -/

theorem _root_.L.evalE_pure (e : Expr) (st : St) :
    (∃ v, evalE e st = .ok (v, st)) ∨ evalE e st = .error .oob := by
  induction e with
  | const w => exact Or.inl ⟨w, rfl⟩
  | var x => exact Or.inl ⟨st.loc x, rfl⟩
  | len8 a => exact Or.inl ⟨st.mem.len8 a, rfl⟩
  | len64 a => exact Or.inl ⟨st.mem.len64 a, rfl⟩
  | glob g => exact Or.inl ⟨st.mem.glob g, rfl⟩
  | bin op a b iha ihb =>
    rcases iha with ⟨va, ha⟩ | ha
    · rcases ihb with ⟨vb, hb⟩ | hb
      · exact Or.inl ⟨op.eval va vb,
          by simp [evalE, Bind.bind, StateT.bind, Except.bind, ha, hb, Pure.pure, StateT.pure, Except.pure]⟩
      · exact Or.inr (by simp [evalE, Bind.bind, StateT.bind, Except.bind, ha, hb])
    · exact Or.inr (by simp [evalE, Bind.bind, StateT.bind, Except.bind, ha])
  | cmpw c a b iha ihb =>
    rcases iha with ⟨va, ha⟩ | ha
    · rcases ihb with ⟨vb, hb⟩ | hb
      · exact Or.inl ⟨c.evalW va vb,
          by simp [evalE, Bind.bind, StateT.bind, Except.bind, ha, hb, Pure.pure, StateT.pure, Except.pure]⟩
      · exact Or.inr (by simp [evalE, Bind.bind, StateT.bind, Except.bind, ha, hb])
    · exact Or.inr (by simp [evalE, Bind.bind, StateT.bind, Except.bind, ha])
  | ld8 a i ihi =>
    rcases ihi with ⟨vi, hi⟩ | hi
    · by_cases hb : vi.toNat < (st.mem.arr8 a).size
      · refine Or.inl ⟨(st.mem.arr8 a)[vi.toNat].toUInt64, ?_⟩
        change (evalE i >>= fun idx => _root_.L.ld8 a idx) st = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hi]
        dsimp only [_root_.L.ld8, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
          Pure.pure, StateT.pure, Except.pure, Except.bind]
        simp [hb]; rfl
      · refine Or.inr ?_
        change (evalE i >>= fun idx => _root_.L.ld8 a idx) st = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hi]
        dsimp only [_root_.L.ld8, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
          Pure.pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, Except.pure]
        simp [hb]; rfl
    · exact Or.inr (by simp [evalE, Bind.bind, StateT.bind, Except.bind, hi])
  | ld64 a i ihi =>
    rcases ihi with ⟨vi, hi⟩ | hi
    · by_cases hb : vi.toNat < (st.mem.arr64 (TieredArray.t0 a)).size
      · refine Or.inl ⟨(st.mem.arr64 (TieredArray.t0 a))[vi.toNat], ?_⟩
        change (evalE i >>= fun idx => _root_.L.ld64 (TieredArray.t0 a) idx) st = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hi]
        dsimp only [_root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
          Pure.pure, StateT.pure, Except.pure, Except.bind]
        simp [hb]; rfl
      · refine Or.inr ?_
        change (evalE i >>= fun idx => _root_.L.ld64 (TieredArray.t0 a) idx) st = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hi]
        dsimp only [_root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
          Pure.pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, Except.pure]
        simp [hb]; rfl
    · exact Or.inr (by simp [evalE, Bind.bind, StateT.bind, Except.bind, hi])
  | ldc d i ihi =>
    rcases ihi with ⟨vi, hi⟩ | hi
    · by_cases hb : vi.toNat < d.length
      · refine Or.inl ⟨d[vi.toNat].toUInt64, ?_⟩
        change (evalE i >>= fun idx => _root_.L.ldc d idx) st = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hi]
        dsimp only [_root_.L.ldc, Pure.pure, StateT.pure, Except.pure]
        simp [hb]; rfl
      · refine Or.inr ?_
        change (evalE i >>= fun idx => _root_.L.ldc d idx) st = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hi]
        dsimp only [_root_.L.ldc, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.pure]
        simp [hb]; rfl
    · exact Or.inr (by simp [evalE, Bind.bind, StateT.bind, Except.bind, hi])
  | ld64t a t i iht ihi =>
    rcases iht with ⟨u, ht⟩ | ht
    · rcases ihi with ⟨vi, hi⟩ | hi
      · by_cases hb : vi.toNat < (st.mem.arr64 (tierA a u)).size
        · refine Or.inl ⟨(st.mem.arr64 (tierA a u))[vi.toNat], ?_⟩
          change (evalE t >>= fun u' => evalE i >>= fun idx => _root_.L.ld64 (tierA a u') idx) st = _
          dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [ht]; dsimp only; rw [hi]
          dsimp only [_root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
            Pure.pure, StateT.pure, Except.pure, Except.bind]
          simp [hb]; rfl
        · refine Or.inr ?_
          change (evalE t >>= fun u' => evalE i >>= fun idx => _root_.L.ld64 (tierA a u') idx) st = _
          dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [ht]; dsimp only; rw [hi]
          dsimp only [_root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
            Pure.pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, Except.pure]
          simp [hb]; rfl
      · exact Or.inr (by simp [evalE, Bind.bind, StateT.bind, Except.bind, ht, hi])
    · exact Or.inr (by simp [evalE, Bind.bind, StateT.bind, Except.bind, ht])
  | len64t a t iht =>
    rcases iht with ⟨u, ht⟩ | ht
    · exact Or.inl ⟨st.mem.len64 (tierA a u),
        by simp [evalE, Bind.bind, StateT.bind, Except.bind, ht, get, getThe, MonadStateOf.get,
          StateT.get, Pure.pure, StateT.pure, Except.pure]⟩
    · exact Or.inr (by simp [evalE, Bind.bind, StateT.bind, Except.bind, ht])
  | ld8x8 s i ihi =>
    rcases ihi with ⟨vi, hi⟩ | hi
    · by_cases hb : vi.toNat + 8 ≤ (st.mem.src8 s).size
      · refine Or.inl ⟨le64 (st.mem.src8 s) vi.toNat, ?_⟩
        change (evalE i >>= fun idx => _root_.L.ld8x8 s idx) st = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hi]
        dsimp only [_root_.L.ld8x8, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
          Pure.pure, StateT.pure, Except.pure, Except.bind]
        simp [hb]; rfl
      · refine Or.inr ?_
        change (evalE i >>= fun idx => _root_.L.ld8x8 s idx) st = _
        dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hi]
        dsimp only [_root_.L.ld8x8, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
          Pure.pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, Except.pure]
        simp [hb]; rfl
    · exact Or.inr (by simp [evalE, Bind.bind, StateT.bind, Except.bind, hi])
  | ld32t a t i iht ihi =>
    rcases iht with ⟨u, ht⟩ | ht
    · rcases ihi with ⟨vi, hi⟩ | hi
      · by_cases hb : (vi / 2).toNat < (st.mem.arr64 (tierA a u)).size
        · refine Or.inl ⟨half32 (st.mem.arr64 (tierA a u))[(vi / 2).toNat] vi, ?_⟩
          change (evalE t >>= fun u' => evalE i >>= fun idx => _root_.L.ld32 (tierA a u') idx) st = _
          dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [ht]; dsimp only; rw [hi]
          dsimp only [_root_.L.ld32, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
            Pure.pure, StateT.pure, Except.pure, Except.bind]
          split
          case isTrue _ => rfl
          case isFalse hn => exfalso; exact hn hb
        · refine Or.inr ?_
          change (evalE t >>= fun u' => evalE i >>= fun idx => _root_.L.ld32 (tierA a u') idx) st = _
          dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [ht]; dsimp only; rw [hi]
          dsimp only [_root_.L.ld32, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
            Pure.pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, Except.pure]
          split
          case isTrue hy => exfalso; exact hb hy
          case isFalse _ => rfl
      · exact Or.inr (by simp [evalE, Bind.bind, StateT.bind, Except.bind, ht, hi])
    · exact Or.inr (by simp [evalE, Bind.bind, StateT.bind, Except.bind, ht])
  | ld32h a t i hiFlag iht ihi =>
    rcases iht with ⟨u, ht⟩ | ht
    · rcases ihi with ⟨vi, hi⟩ | hi
      · by_cases hb : (vi).toNat < (st.mem.arr64 (tierA a u)).size
        · refine Or.inl ⟨half32b hiFlag (st.mem.arr64 (tierA a u))[vi.toNat], ?_⟩
          change (evalE t >>= fun u' => evalE i >>= fun idx => do
            let w ← _root_.L.ld64 (tierA a u') idx; return half32b hiFlag w) st = _
          dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [ht]; dsimp only; rw [hi]
          dsimp only [_root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
            Pure.pure, StateT.pure, Except.pure, Except.bind]
          simp [hb]; rfl
        · refine Or.inr ?_
          change (evalE t >>= fun u' => evalE i >>= fun idx => do
            let w ← _root_.L.ld64 (tierA a u') idx; return half32b hiFlag w) st = _
          dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [ht]; dsimp only; rw [hi]
          dsimp only [_root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
            Pure.pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, Except.pure]
          simp [hb]; rfl
      · exact Or.inr (by simp [evalE, Bind.bind, StateT.bind, Except.bind, ht, hi])
    · exact Or.inr (by simp [evalE, Bind.bind, StateT.bind, Except.bind, ht])

theorem _root_.L.evalC_pure (c : Cond) (st : St) :
    (∃ b, evalC c st = .ok (b, st)) ∨ evalC c st = .error .oob := by
  induction c with
  | cmp op a b =>
    rcases _root_.L.evalE_pure a st with ⟨va, hva⟩ | hva
    · rcases _root_.L.evalE_pure b st with ⟨vb, hvb⟩ | hvb
      · exact Or.inl ⟨op.eval va vb,
          by simp [evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]⟩
      · exact Or.inr (by simp [evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb])
    · exact Or.inr (by simp [evalC, Bind.bind, StateT.bind, Except.bind, hva])
  | and p q ihp ihq =>
    rcases ihp with ⟨bp, hbp⟩ | hbp
    · cases bp
      · exact Or.inl ⟨false,
          by simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, Pure.pure, StateT.pure, Except.pure]⟩
      · rcases ihq with ⟨bq, hbq⟩ | hbq
        · exact Or.inl ⟨bq, by simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]⟩
        · exact Or.inr (by simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq])
    · exact Or.inr (by simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp])
  | or p q ihp ihq =>
    rcases ihp with ⟨bp, hbp⟩ | hbp
    · cases bp
      · rcases ihq with ⟨bq, hbq⟩ | hbq
        · exact Or.inl ⟨bq, by simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]⟩
        · exact Or.inr (by simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq])
      · exact Or.inl ⟨true,
          by simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, Pure.pure, StateT.pure, Except.pure]⟩
    · exact Or.inr (by simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp])
  | not p ihp =>
    rcases ihp with ⟨bp, hbp⟩ | hbp
    · exact Or.inl ⟨!bp,
        by simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp, Pure.pure, StateT.pure, Except.pure]⟩
    · exact Or.inr (by simp [evalC, Bind.bind, StateT.bind, Except.bind, hbp])

theorem _root_.L.evalArgs_pure (es : List Expr) (st : St) :
    (∃ vs, evalArgs es st = .ok (vs, st)) ∨ evalArgs es st = .error .oob := by
  induction es with
  | nil => exact Or.inl ⟨[], rfl⟩
  | cons e es ih =>
    rcases _root_.L.evalE_pure e st with ⟨v, hv⟩ | hv
    · rcases ih with ⟨vs, hvs⟩ | hvs
      · exact Or.inl ⟨v :: vs,
          by simp [evalArgs, Bind.bind, StateT.bind, Except.bind, hv, hvs, Pure.pure, StateT.pure, Except.pure]⟩
      · exact Or.inr (by simp [evalArgs, Bind.bind, StateT.bind, Except.bind, hv, hvs])
    · exact Or.inr (by simp [evalArgs, Bind.bind, StateT.bind, Except.bind, hv])

theorem _root_.L.warr_pure (w : WArr) (st : St) :
    (∃ a, _root_.L.warr w st = .ok (a, st)) ∨ _root_.L.warr w st = .error .oob := by
  cases w with
  | plain a => exact Or.inl ⟨a, rfl⟩
  | tier a t =>
    rcases _root_.L.evalE_pure t st with ⟨u, ht⟩ | ht
    · exact Or.inl ⟨tierA a u,
        by simp [_root_.L.warr, Bind.bind, StateT.bind, Except.bind, ht, Pure.pure, StateT.pure, Except.pure]⟩
    · exact Or.inr (by simp [_root_.L.warr, Bind.bind, StateT.bind, Except.bind, ht])

theorem uint64_eq_of_toNat {x y : UInt64} (h : x.toNat = y.toNat) : x = y :=
  UInt64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (by simpa [UInt64.toNat_toBitVec] using h))

private theorem isAligned_one (addr : BitVec 64) : isAligned addr 1 = true := rfl

/-- Tiered index `u`: bit 0 decides `.t0 a` (`u &&& 1 = 0`) vs `tier1 a` (`u &&& 1 ≠ 0`). -/
theorem tierA_bit0 (a : ArrId) (u : _root_.L.Word) :
    ((u &&& 1 = 0) → tierA a u = TieredArray.t0 a ∧ (u.toBitVec &&& 1#64).toNat = 0) ∧
    ((u &&& 1 ≠ 0) → tierA a u = tier1 a ∧ (u.toBitVec &&& 1#64).toNat = 1) := by
  have hb : (u.toBitVec &&& 1#64) = (u &&& 1).toBitVec := (UInt64.toBitVec_and u 1).symm
  have hm : (u &&& 1).toNat = u.toNat % 2 := by
    rw [← UInt64.toNat_toBitVec, ← hb, BitVec.toNat_and, BitVec.toNat_ofNat,
        show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.and_one_is_mod, UInt64.toNat_toBitVec]
  constructor
  · intro h0
    refine ⟨?_, ?_⟩
    · have hbf : (u &&& 1 != 0) = false := by rw [h0]; decide
      dsimp only [tierA]; rw [hbf]
    · rw [hb, h0]; rfl
  · intro hne
    have h1 : u &&& 1 = 1 := by
      have hm2 : (u &&& 1).toNat = 1 := by
        have hlt : (u &&& 1).toNat < 2 := by omega
        have hnz : (u &&& 1).toNat ≠ 0 := fun hz => hne (uint64_eq_of_toNat hz)
        omega
      exact uint64_eq_of_toNat hm2
    refine ⟨?_, ?_⟩
    · have hbt : (u &&& 1 != 0) = true := by rw [h1]; decide
      dsimp only [tierA]; rw [hbt]
    · rw [hb, h1]; rfl

theorem tieredOk_len64_addr {tab : Tab} (a : ArrId) (u : _root_.L.Word)
    (ht : tab.tieredOkB a = true) :
    let off := if (u &&& 1) == 0 then 0#64 else 8#64
    tab.wordPosOkB (tierA a u) = true ∧
    (BitVec.ofNat 64 0 + off) + BitVec.ofInt 64 (tab.len64 (TieredArray.t0 a)) =
      BitVec.ofInt 64 (tab.len64 (tierA a u)) ∧
    (BitVec.ofNat 64 0 + off) + BitVec.ofInt 64 (tab.base64 (TieredArray.t0 a)) =
      BitVec.ofInt 64 (tab.base64 (tierA a u)) := by
  simp only [Tab.tieredOkB, Bool.and_eq_true, beq_iff_eq] at ht
  have hw0 : tab.wordPosOkB (TieredArray.t0 a) = true := ht.1.1
  have hw1 : tab.wordPosOkB (tier1 a) = true := ht.1.2
  have hpos1 : tab.pos64 (tier1 a) = tab.pos64 (TieredArray.t0 a) + 1 := ht.2
  by_cases h0 : u &&& 1 = 0
  · simp only [beq_iff_eq, h0, ↓reduceIte, BitVec.add_zero]
    rw [(tierA_bit0 a u).1 h0 |>.1]
    exact ⟨hw0, BitVec.zero_add _, BitVec.zero_add _⟩
  · simp only [beq_iff_eq, h0, ↓reduceIte]
    rw [(tierA_bit0 a u).2 h0 |>.1]
    refine ⟨hw1, ?_, ?_⟩
    · rw [Tab.len64_eq_nat, Tab.len64_eq_nat, int_mul8_ofInt, int_mul8_ofInt, hpos1]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_add]
      simp only [BitVec.toNat_ofNat]
      have h1 : 8 * (2 + (tab.nb + tab.nw) + (tab.pos64 (TieredArray.t0 a) + 1)) =
          8 + 8 * (2 + (tab.nb + tab.nw) + tab.pos64 (TieredArray.t0 a)) := by omega
      rw [h1, ← Nat.add_mod]
    · rw [Tab.base64_eq_nat, Tab.base64_eq_nat, int_mul8_ofInt, int_mul8_ofInt, hpos1]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_add]
      simp only [BitVec.toNat_ofNat]
      have h1 : 8 * (2 + (tab.pos64 (TieredArray.t0 a) + 1)) =
          8 + 8 * (2 + tab.pos64 (TieredArray.t0 a)) := by omega
      rw [h1, ← Nat.add_mod]

def TierAddrOk (tab : Tab) (a : ArrId) (u : _root_.L.Word) : Prop :=
  tab.tieredOkB a = true ∨ (u &&& 1 = 0 ∧ tab.wordPosOkB (.t0 a) = true)

theorem tieredOk_implies_tier32Ok (tab : Tab) (a : ArrId) (t : Expr)
    (h : tab.tieredOkB a = true) : tier32OkB tab a t = true := by
  cases t with
  | const w =>
    dsimp only [tier32OkB]
    split
    · simp only [Tab.tieredOkB, Bool.and_eq_true] at h; exact h.1.1
    · exact h
  | _ => exact h

theorem tier32Ok_to_tierAddrOk {tab : Tab} {a : ArrId} {t : Expr} {st st' : _root_.L.St} {u : _root_.L.Word}
    (ht : tier32OkB tab a t = true) (hu : _root_.L.evalE t st = .ok (u, st')) :
    TierAddrOk tab a u := by
  cases t with
  | const w =>
    dsimp only [tier32OkB] at ht
    by_cases hm : (w.toNat % 2 == 0) = true
    · simp only [hm, ↓reduceIte] at ht
      have hw : u = w := by
        simp [_root_.L.evalE, Pure.pure, StateT.pure, Except.pure] at hu
        exact hu.1.symm
      have hev : w &&& 1 = 0 := by
        have hm0 : w.toNat % 2 = 0 := beq_iff_eq.mp hm
        apply uint64_eq_of_toNat
        rw [← UInt64.toNat_toBitVec, UInt64.toBitVec_and, BitVec.toNat_and,
            show (1 : UInt64).toBitVec = 1#64 from rfl, BitVec.toNat_ofNat,
            show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.and_one_is_mod, UInt64.toNat_toBitVec]
        exact hm0
      exact Or.inr ⟨hw ▸ hev, ht⟩
    · simp only [hm, Bool.false_eq_true, ↓reduceIte] at ht
      exact Or.inl ht
  | _ => exact Or.inl ht

theorem tierAddrOk_len64_addr {tab : Tab} (a : ArrId) (u : _root_.L.Word)
    (ht : TierAddrOk tab a u) :
    let off := if (u &&& 1) == 0 then 0#64 else 8#64
    tab.wordPosOkB (tierA a u) = true ∧
    (BitVec.ofNat 64 0 + off) + BitVec.ofInt 64 (tab.len64 (TieredArray.t0 a)) =
      BitVec.ofInt 64 (tab.len64 (tierA a u)) ∧
    (BitVec.ofNat 64 0 + off) + BitVec.ofInt 64 (tab.base64 (TieredArray.t0 a)) =
      BitVec.ofInt 64 (tab.base64 (tierA a u)) := by
  rcases ht with hfull | ⟨h0, hw0⟩
  · exact tieredOk_len64_addr a u hfull
  · simp only [beq_iff_eq, h0, ↓reduceIte, BitVec.add_zero]
    rw [(tierA_bit0 a u).1 h0 |>.1]
    exact ⟨hw0, BitVec.zero_add _, BitVec.zero_add _⟩

theorem step_tierHdr {lkm : LinkModel} (env : CodeEnvGen lkm) {T : BitVec 64}
    (pre post : List AsmItem) (rsrc : Reg) (u : _root_.L.Word)
    (hlink : lkm.linkSpec (pre ++
        [Asm.andi AbiReg.t0 rsrc 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
         Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + 3) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = T) (hsrc : st.getReg rsrc = u.toBitVec) :
    let off := if (u &&& 1) == 0 then 0#64 else 8#64
    ∃ st', RV64.run env.rom 3 st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 3)) ∧
      st'.getReg AbiReg.t1 = T + off ∧
      st'.mem = st.mem ∧
      PreservedRegs st st' ∧
      (∀ r, r ≠ AbiReg.t0 → r ≠ AbiReg.t1 → st'.getReg r = st.getReg r) := by
  intro off
  let i1 : Instr := .aluImm .andi AbiReg.t0 rsrc 1#12
  let i2 : Instr := .shImm .slli AbiReg.t0 AbiReg.t0 3#6
  let i3 : Instr := .alu .add AbiReg.t1 AbiReg.gp AbiReg.t0
  have hl1 : lkm.linkSpec (pre ++ [Asm.raw i1] ++ ([Asm.raw i2, Asm.raw i3] ++ post)) =
      .ok (env.code, env.labels) := by
    simpa [i1, i2, i3, Asm.andi, Asm.slli, Asm.add, Asm.raw, List.append_assoc] using hlink
  have hs1 := step_item_instr_lm lkm env.hrom pre ([Asm.raw i2, Asm.raw i3] ++ post) i1 hl1
    (by omega) st hpc
  let v1 : BitVec 64 := u.toBitVec &&& sextImm12 1#12
  let st1 := stepReg st AbiReg.t0 v1 (st.pc + 4#64)
  have ht0_1 : st1.getReg AbiReg.t0 = u.toBitVec &&& 1#64 := by
    change (stepReg st AbiReg.t0 v1 _).getReg AbiReg.t0 = _
    rw [getReg_stepReg_eq _ _ (by decide)]
    dsimp only [v1]
    rw [show sextImm12 1#12 = 1#64 from rfl]
  have htw1 : lkm.totalSize (pre ++ [Asm.raw i1]) = lkm.totalSize pre + 1 := by
    rw [lkm.totalSize_append, Asm.raw, lkm.totalSize_instr]
  have hpc1 : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ [Asm.raw i1])) := by
    change st.pc + 4#64 = _; rw [pc_add_4_ofNat st.pc hpc, htw1]
  have hl2 : lkm.linkSpec ((pre ++ [Asm.raw i1]) ++ [Asm.raw i2] ++ ([Asm.raw i3] ++ post)) =
      .ok (env.code, env.labels) := by
    simpa [i1, i2, i3, Asm.andi, Asm.slli, Asm.add, Asm.raw, List.append_assoc] using hlink
  have hs2 := step_item_instr_lm lkm env.hrom (pre ++ [Asm.raw i1]) ([Asm.raw i3] ++ post) i2 hl2
    (by rw [htw1]; omega) st1 hpc1
  let v2 : BitVec 64 := st1.getReg AbiReg.t0 <<< 3
  let st2 := stepReg st1 AbiReg.t0 v2 (st1.pc + 4#64)
  have ht0_2 : st2.getReg AbiReg.t0 = off := by
    change (stepReg st1 AbiReg.t0 v2 _).getReg AbiReg.t0 = _
    rw [getReg_stepReg_eq _ _ (by decide)]
    dsimp only [v2]; rw [ht0_1]
    by_cases h0 : u &&& 1 = 0
    · simp only [off, beq_iff_eq, h0, ↓reduceIte]
      have hbit := (tierA_bit0 0 u).1 h0 |>.2
      have hz : u.toBitVec &&& 1#64 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hbit)
      rw [hz]; rfl
    · simp only [off, beq_iff_eq, h0, ↓reduceIte]
      have hbit := (tierA_bit0 0 u).2 h0 |>.2
      have ho : u.toBitVec &&& 1#64 = 1#64 := BitVec.eq_of_toNat_eq (by simpa using hbit)
      rw [ho]; rfl
  have htw2 : lkm.totalSize (pre ++ [Asm.raw i1] ++ [Asm.raw i2]) = lkm.totalSize pre + 2 := by
    rw [lkm.totalSize_append, htw1, Asm.raw, lkm.totalSize_instr]
  have hpc2 : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ [Asm.raw i1] ++ [Asm.raw i2])) := by
    change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1, htw2, htw1]
  have hl3 : lkm.linkSpec ((pre ++ [Asm.raw i1] ++ [Asm.raw i2]) ++ [Asm.raw i3] ++ post) =
      .ok (env.code, env.labels) := by
    simpa [i1, i2, i3, Asm.andi, Asm.slli, Asm.add, Asm.raw, List.append_assoc] using hlink
  have hs3 := step_item_instr_lm lkm env.hrom (pre ++ [Asm.raw i1] ++ [Asm.raw i2]) post i3 hl3
    (by rw [htw2]; omega) st2 hpc2
  let v3 : BitVec 64 := st2.getReg AbiReg.gp + st2.getReg AbiReg.t0
  let st3 := stepReg st2 AbiReg.t1 v3 (st2.pc + 4#64)
  have hgp2 : st2.getReg AbiReg.gp = T := by
    change (stepReg st1 AbiReg.t0 _ _).getReg AbiReg.gp = T
    rw [getReg_stepReg_ne _ _ _ (by decide),
        getReg_stepReg_ne _ _ _ (by decide), hgp]
  refine ⟨st3, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · rw [show (3 : Nat) = 1 + (1 + 1) from rfl]
    rw [run_add, run_one_cont _ _ st1 (by rw [hs1]; simp only [execInstr, evalAluImm, hsrc, i1]; rfl)]
    dsimp only
    rw [run_add, run_one_cont _ _ st2 (by rw [hs2]; simp only [execInstr, i2]; rfl)]
    dsimp only
    exact run_one_cont _ _ st3 (by rw [hs3]; simp only [execInstr, evalAlu, i3]; rfl)
  · change st2.pc + 4#64 = _; rw [pc_add_4_ofNat st2.pc hpc2, htw2]
  · change (stepReg st2 AbiReg.t1 v3 _).getReg AbiReg.t1 = T + off
    rw [getReg_stepReg_eq _ _ (by decide)]
    dsimp only [v3]; rw [hgp2, ht0_2]
  · exact ⟨by rw [getReg_stepReg_ne _ _ _ (by decide), hgp2, hgp],
           by rw [getReg_stepReg_ne _ _ _ (by decide), getReg_stepReg_ne _ _ _ (by decide),
                  getReg_stepReg_ne _ _ _ (by decide)],
           by rw [getReg_stepReg_ne _ _ _ (by decide), getReg_stepReg_ne _ _ _ (by decide),
                  getReg_stepReg_ne _ _ _ (by decide)],
           by rw [getReg_stepReg_ne _ _ _ (by decide), getReg_stepReg_ne _ _ _ (by decide),
                  getReg_stepReg_ne _ _ _ (by decide)]⟩
  · intro r hr0 hr1
    change (stepReg st2 AbiReg.t1 _ _).getReg r = st.getReg r
    rw [getReg_stepReg_ne st2 AbiReg.t1 r hr1,
        getReg_stepReg_ne st1 AbiReg.t0 r hr0,
        getReg_stepReg_ne st AbiReg.t0 r hr0]

theorem step_lwu_off {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (rd base : Reg) (off : BitVec 12) (hrd : rd ≠ AbiReg.zero)
    (hlink : lkm.linkSpec (pre ++ [Asm.raw (.load .lwu rd base off)] ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + 1) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hal : isAligned (st.getReg base + sextImm12 off) 4 = true) :
    let addr := st.getReg base + sextImm12 off
    let st' := stepReg st rd ((loadBytes st.mem addr 4).zeroExtend 64) (st.pc + 4#64)
    RV64.run env.rom 1 st = .cont st' ∧
    st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)) ∧
    st'.getReg rd = (loadBytes st.mem addr 4).zeroExtend 64 ∧
    (∀ r, r ≠ rd → st'.getReg r = st.getReg r) ∧
    st'.mem = st.mem := by
  intro addr st'
  have hs := step_item_instr_lm lkm env.hrom pre post (.load .lwu rd base off) hlink (by omega) st hpc
  refine ⟨run_one_cont _ _ st' (by rw [hs]; simp only [execInstr, hal]; rfl),
          pc_add_4_ofNat st.pc hpc,
          getReg_stepReg_eq st rd hrd _ _,
          fun r hr => getReg_stepReg_ne st rd r hr _ _, (by dsimp only [st', stepReg, RV64.State.setReg]; split <;> rfl)⟩

private theorem step_sw_off {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (base rs : Reg) (off : BitVec 12)
    (hlink : lkm.linkSpec (pre ++ [Asm.raw (.store .sw base rs off)] ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + 1) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hal : isAligned (st.getReg base + sextImm12 off) 4 = true) :
    let addr := st.getReg base + sextImm12 off
    let st' := { st with pc := st.pc + 4#64, mem := RV64.storeBytes st.mem addr 4 ((st.getReg rs).extractLsb' 0 32) }
    RV64.run env.rom 1 st = .cont st' ∧
    st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)) ∧
    PreservedRegs st st' := by
  intro addr st'
  have hs := step_item_instr_lm lkm env.hrom pre post (.store .sw base rs off) hlink (by omega) st hpc
  exact ⟨run_one_cont _ _ st' (by rw [hs]; simp only [execInstr, hal]; rfl),
         pc_add_4_ofNat st.pc hpc, ⟨rfl, rfl, rfl, rfl⟩⟩

theorem step_lbu_off {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (rd base : Reg) (off : BitVec 12) (hrd : rd ≠ AbiReg.zero)
    (hlink : lkm.linkSpec (pre ++ [Asm.lbu rd base off] ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + 1) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre)) :
    let addr := st.getReg base + sextImm12 off
    let st' := stepReg st rd ((loadBytes st.mem addr 1).zeroExtend 64) (st.pc + 4#64)
    RV64.run env.rom 1 st = .cont st' ∧
    st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)) ∧
    st'.getReg rd = (st.mem addr).zeroExtend 64 ∧
    (∀ r, r ≠ rd → st'.getReg r = st.getReg r) ∧
    st'.mem = st.mem := by
  intro addr st'
  have hs := step_item_instr_lm lkm env.hrom pre post (.load .lbu rd base off) hlink (by omega) st hpc
  have hal : isAligned addr 1 = true := isAligned_one addr
  refine ⟨run_one_cont _ _ st' (by rw [hs]; simp only [execInstr]; rfl),
          pc_add_4_ofNat st.pc hpc, ?_,
          fun r hr => getReg_stepReg_ne st rd r hr _ _, (by dsimp only [st', stepReg, RV64.State.setReg]; split <;> rfl)⟩
  rw [getReg_stepReg_eq st rd hrd _ _, loadBytes_one]

private theorem le64_byte_step_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (off : BitVec 12)
    (hlink : lkm.linkSpec (pre ++
        [Asm.lbu AbiReg.t2 AbiReg.t1 off,
         Asm.slli AbiReg.a0 AbiReg.a0 8#6,
         Asm.or AbiReg.a0 AbiReg.a0 AbiReg.t2] ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + 3) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre)) :
    let addr := st.getReg AbiReg.t1 + sextImm12 off
    let bval := (st.mem addr).zeroExtend 64
    let a0new := (st.getReg AbiReg.a0 <<< 8) ||| bval
    ∃ st', RV64.run env.rom 3 st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 3)) ∧
      st'.getReg AbiReg.a0 = a0new ∧
      st'.getReg AbiReg.t1 = st.getReg AbiReg.t1 ∧
      st'.mem = st.mem ∧
      PreservedRegs st st' := by
  intro addr bval a0new
  have hl1 : lkm.linkSpec (pre ++ [Asm.lbu AbiReg.t2 AbiReg.t1 off] ++
      ([Asm.slli AbiReg.a0 AbiReg.a0 8#6, Asm.or AbiReg.a0 AbiReg.a0 AbiReg.t2] ++ post)) =
      .ok (env.code, env.labels) := by
    simpa [List.append_assoc] using hlink
  obtain ⟨hr1, hpc1, ht2_1, hoth1, hmem1⟩ :=
    step_lbu_off env pre ([Asm.slli AbiReg.a0 AbiReg.a0 8#6, Asm.or AbiReg.a0 AbiReg.a0 AbiReg.t2] ++ post)
      AbiReg.t2 AbiReg.t1 off (by decide) hl1 (by omega) st hpc
  let st1 := stepReg st AbiReg.t2 ((loadBytes st.mem addr 1).zeroExtend 64) (st.pc + 4#64)
  have htw1 : lkm.totalSize (pre ++ [Asm.lbu AbiReg.t2 AbiReg.t1 off]) = lkm.totalSize pre + 1 := by
    rw [lkm.totalSize_append, Asm.lbu, lkm.totalSize_instr]
  have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ [Asm.lbu AbiReg.t2 AbiReg.t1 off])) := by
    rw [htw1]; exact hpc1
  have hl2 : lkm.linkSpec ((pre ++ [Asm.lbu AbiReg.t2 AbiReg.t1 off]) ++
      [Asm.raw (.shImm .slli AbiReg.a0 AbiReg.a0 8#6)] ++
      ([Asm.or AbiReg.a0 AbiReg.a0 AbiReg.t2] ++ post)) = .ok (env.code, env.labels) := by
    simpa [Asm.slli, Asm.raw, List.append_assoc] using hlink
  have hs2 := step_item_instr_lm lkm env.hrom (pre ++ [Asm.lbu AbiReg.t2 AbiReg.t1 off])
    ([Asm.or AbiReg.a0 AbiReg.a0 AbiReg.t2] ++ post) (.shImm .slli AbiReg.a0 AbiReg.a0 8#6)
    hl2 (by rw [htw1]; omega) st1 hpc1'
  let v2 : BitVec 64 := st1.getReg AbiReg.a0 <<< 8
  let st2 := stepReg st1 AbiReg.a0 v2 (st1.pc + 4#64)
  have htw2 : lkm.totalSize (pre ++ [Asm.lbu AbiReg.t2 AbiReg.t1 off] ++ [Asm.slli AbiReg.a0 AbiReg.a0 8#6]) =
      lkm.totalSize pre + 2 := by
    rw [lkm.totalSize_append, htw1, Asm.slli, lkm.totalSize_instr]
  have hpc2 : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ [Asm.lbu AbiReg.t2 AbiReg.t1 off] ++
      [Asm.slli AbiReg.a0 AbiReg.a0 8#6])) := by
    change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1', htw2, htw1]
  have hl3 : lkm.linkSpec ((pre ++ [Asm.lbu AbiReg.t2 AbiReg.t1 off] ++ [Asm.slli AbiReg.a0 AbiReg.a0 8#6]) ++
      [Asm.raw (.alu .or AbiReg.a0 AbiReg.a0 AbiReg.t2)] ++ post) = .ok (env.code, env.labels) := by
    simpa [Asm.or, Asm.slli, Asm.raw, List.append_assoc] using hlink
  have hs3 := step_item_instr_lm lkm env.hrom
    (pre ++ [Asm.lbu AbiReg.t2 AbiReg.t1 off] ++ [Asm.slli AbiReg.a0 AbiReg.a0 8#6])
    post (.alu .or AbiReg.a0 AbiReg.a0 AbiReg.t2) hl3 (by rw [htw2]; omega) st2 hpc2
  let v3 : BitVec 64 := st2.getReg AbiReg.a0 ||| st2.getReg AbiReg.t2
  let st3 := stepReg st2 AbiReg.a0 v3 (st2.pc + 4#64)
  have ha0_1 : st1.getReg AbiReg.a0 = st.getReg AbiReg.a0 := hoth1 AbiReg.a0 (by decide)
  have ha0_2 : st2.getReg AbiReg.a0 = st.getReg AbiReg.a0 <<< 8 := by
    change (stepReg st1 AbiReg.a0 v2 _).getReg AbiReg.a0 = _
    rw [getReg_stepReg_eq _ _ (by decide)]; dsimp only [v2]; rw [ha0_1]
  have ht2_2 : st2.getReg AbiReg.t2 = bval := by
    change (stepReg st1 AbiReg.a0 v2 _).getReg AbiReg.t2 = _
    rw [getReg_stepReg_ne _ _ _ (by decide)]; exact ht2_1
  refine ⟨st3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (3 : Nat) = 1 + (1 + 1) from rfl, run_add, hr1]; dsimp only
    rw [run_add, run_one_cont _ _ st2 (by rw [hs2]; simp only [execInstr]; rfl)]; dsimp only
    exact run_one_cont _ _ st3 (by rw [hs3]; simp only [execInstr, evalAlu]; rfl)
  · change st2.pc + 4#64 = _; rw [pc_add_4_ofNat st2.pc hpc2, htw2]
  · change (stepReg st2 AbiReg.a0 v3 _).getReg AbiReg.a0 = _
    rw [getReg_stepReg_eq _ _ (by decide)]
    dsimp only [v3]; rw [ha0_2, ht2_2]
  · change (stepReg st2 AbiReg.a0 _ _).getReg AbiReg.t1 = st.getReg AbiReg.t1
    rw [getReg_stepReg_ne _ _ _ (by decide), getReg_stepReg_ne _ _ _ (by decide), hoth1 AbiReg.t1 (by decide)]
  · change st2.mem = st.mem; exact hmem1
  · exact ⟨by rw [getReg_stepReg_ne _ _ _ (by decide), getReg_stepReg_ne _ _ _ (by decide), hoth1 AbiReg.gp (by decide)],
           by rw [getReg_stepReg_ne _ _ _ (by decide), getReg_stepReg_ne _ _ _ (by decide), hoth1 AbiReg.sp (by decide)],
           by rw [getReg_stepReg_ne _ _ _ (by decide), getReg_stepReg_ne _ _ _ (by decide), hoth1 AbiReg.s0 (by decide)],
           by rw [getReg_stepReg_ne _ _ _ (by decide), getReg_stepReg_ne _ _ _ (by decide), hoth1 AbiReg.s2 (by decide)]⟩

private theorem le64_byte_eq (b : Array UInt8) (idx : Nat) (hib : idx + 8 ≤ b.size) :
    let v : Nat → Nat := fun k => if hk : idx + k < b.size then b[idx + k].toNat else 0
    (le64 b idx).toBitVec =
      ((((((((0#64 <<< 8 ||| BitVec.ofNat 64 (v 7)) <<< 8 ||| BitVec.ofNat 64 (v 6))
        <<< 8 ||| BitVec.ofNat 64 (v 5)) <<< 8 ||| BitVec.ofNat 64 (v 4))
        <<< 8 ||| BitVec.ofNat 64 (v 3)) <<< 8 ||| BitVec.ofNat 64 (v 2))
        <<< 8 ||| BitVec.ofNat 64 (v 1)) <<< 8 ||| BitVec.ofNat 64 (v 0)) := by
  intro v
  have hlt : ∀ k, k < 8 → v k < 256 := fun k hk => by
    have hik : idx + k < b.size := by omega
    simp only [v, hik, ↓reduceDIte]
    exact UInt8.toNat_lt (b[idx + k])
  have hstep : ∀ (acc : BitVec 64) (d : Nat), d < 256 →
      (acc <<< 8 ||| BitVec.ofNat 64 d).toNat = (acc.toNat * 256 + d) % 2 ^ 64 := by
    intro acc d hd
    have hlt64 : d < 2 ^ 64 := by omega
    rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64,
        Nat.shiftLeft_eq]
    have hdiv : acc.toNat * 256 % 2 ^ 64 = (acc.toNat % 2 ^ 56) * 256 := by
      have hp : (2 ^ 64 : Nat) = 2 ^ 56 * 256 := by decide
      rw [hp, Nat.mul_mod_mul_right]
    have hbound : acc.toNat * 256 % 2 ^ 64 + d < 2 ^ 64 := by
      rw [hdiv]; have := Nat.mod_lt acc.toNat (by decide : 0 < 2 ^ 56); omega
    have hmod_or : (acc.toNat * 256 % 2 ^ 64) ||| d = (acc.toNat * 256 % 2 ^ 64) + d := by
      rw [hdiv, ← Nat.shiftLeft_eq _ 8, ← Nat.shiftLeft_add_eq_or_of_lt hd, Nat.shiftLeft_eq]
    rw [hmod_or, ← Nat.mod_eq_of_lt hbound, Nat.mod_add_mod]
  apply BitVec.eq_of_toNat_eq
  rw [hstep _ _ (hlt 0 (by decide)), hstep _ _ (hlt 1 (by decide)), hstep _ _ (hlt 2 (by decide)),
      hstep _ _ (hlt 3 (by decide)), hstep _ _ (hlt 4 (by decide)), hstep _ _ (hlt 5 (by decide)),
      hstep _ _ (hlt 6 (by decide)), hstep _ _ (hlt 7 (by decide))]
  have hzero : (0#64 : BitVec 64).toNat = 0 := rfl
  rw [hzero, Nat.zero_mul, Nat.zero_add]
  have hf : ∀ (a b : Nat), (a % 2 ^ 64 * 256 + b) % 2 ^ 64 = (a * 256 + b) % 2 ^ 64 := by
    intro a b
    rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
  rw [Nat.mod_eq_of_lt (show v 7 < 2 ^ 64 from Nat.lt_trans (hlt 7 (by decide)) (by decide)),
      hf _ (v 5), hf _ (v 4), hf _ (v 3), hf _ (v 2), hf _ (v 1), hf _ (v 0)]
  dsimp only [le64]
  rw [UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
  simp only [List.range, List.range.loop, List.map, List.foldr]
  have hb0 : idx + 0 < b.size := by omega
  have hb1 : idx + 1 < b.size := by omega
  have hb2 : idx + 2 < b.size := by omega
  have hb3 : idx + 3 < b.size := by omega
  have hb4 : idx + 4 < b.size := by omega
  have hb5 : idx + 5 < b.size := by omega
  have hb6 : idx + 6 < b.size := by omega
  have hb7 : idx + 7 < b.size := by omega
  simp only [v, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, ↓reduceDIte,
    getElem!_pos b (idx + 0) hb0, getElem!_pos b (idx + 1) hb1,
    getElem!_pos b (idx + 2) hb2, getElem!_pos b (idx + 3) hb3,
    getElem!_pos b (idx + 4) hb4, getElem!_pos b (idx + 5) hb5,
    getElem!_pos b (idx + 6) hb6, getElem!_pos b (idx + 7) hb7]
  have hlt_all :
      (((((((b[idx + 7].toNat * 256 + b[idx + 6].toNat) * 256 + b[idx + 5].toNat) * 256 +
        b[idx + 4].toNat) * 256 + b[idx + 3].toNat) * 256 + b[idx + 2].toNat) * 256 +
        b[idx + 1].toNat) * 256 + b[idx + 0].toNat) < 2 ^ 64 := by
    have x0 := UInt8.toNat_lt (b[idx + 0]); have x1 := UInt8.toNat_lt (b[idx + 1])
    have x2 := UInt8.toNat_lt (b[idx + 2]); have x3 := UInt8.toNat_lt (b[idx + 3])
    have x4 := UInt8.toNat_lt (b[idx + 4]); have x5 := UInt8.toNat_lt (b[idx + 5])
    have x6 := UInt8.toNat_lt (b[idx + 6]); have x7 := UInt8.toNat_lt (b[idx + 7])
    omega
  rw [Nat.mod_eq_of_lt hlt_all]
  omega

private theorem sextImm12_nat_lt8 (k : Nat) (hk : k < 8) :
    sextImm12 (BitVec.ofInt 12 (k : Int)) = BitVec.ofNat 64 k := by
  have hk12 : BitVec.ofInt 12 (k : Int) = BitVec.ofNat 12 k := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    have hm : (k : Int) % (2 ^ 12 : Nat) = (k : Int) := Int.emod_eq_of_lt (by omega) (by omega)
    rw [← Int.natCast_emod, Int.toNat_natCast]
  rw [hk12]
  exact sextImm12_of_lt2048_nat k (by omega)

theorem le64_8bytes_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (bytes : Array UInt8) (idx : Nat) (hib : idx + 8 ≤ bytes.size)
    (hlink : lkm.linkSpec (pre ++ ([Asm.lbu AbiReg.a0 AbiReg.t1 7#12] ++
        ([6, 5, 4, 3, 2, 1, 0].flatMap fun k =>
          [Asm.lbu AbiReg.t2 AbiReg.t1 (BitVec.ofInt 12 (k : Int)),
           Asm.slli AbiReg.a0 AbiReg.a0 8#6,
           Asm.or AbiReg.a0 AbiReg.a0 AbiReg.t2])) ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + 22) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hmem : ∀ j (hj : j < 8),
      st.mem (st.getReg AbiReg.t1 + BitVec.ofNat 64 j) = (bytes[idx + j]'(by omega)).toBitVec) :
    ∃ st', RV64.run env.rom 22 st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 22)) ∧
      st'.getReg AbiReg.a0 = (le64 bytes idx).toBitVec ∧
      st'.mem = st.mem ∧
      PreservedRegs st st' := by
  let blk := fun (k : Nat) =>
    [Asm.lbu AbiReg.t2 AbiReg.t1 (BitVec.ofInt 12 (k : Int)),
     Asm.slli AbiReg.a0 AbiReg.a0 8#6,
     Asm.or AbiReg.a0 AbiReg.a0 AbiReg.t2]
  have stepOne : ∀ (k : Nat) (hk : k < 8) (p1 p2 : List AsmItem) (s : State),
      lkm.linkSpec (p1 ++ blk k ++ p2) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize p1 + 3) < 2 ^ 64 →
      s.pc = BitVec.ofNat 64 (4 * lkm.totalSize p1) →
      s.getReg AbiReg.t1 = st.getReg AbiReg.t1 →
      s.mem = st.mem →
      ∃ s', RV64.run env.rom 3 s = .cont s' ∧
        s'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize p1 + 3)) ∧
        s'.getReg AbiReg.a0 = ((s.getReg AbiReg.a0 <<< 8) ||| BitVec.ofNat 64 (bytes[idx + k]'(by omega)).toNat) ∧
        s'.getReg AbiReg.t1 = st.getReg AbiReg.t1 ∧
        s'.mem = st.mem ∧
        PreservedRegs s s' := by
    intro k hk p1 p2 s hl hk64 hsp ht1 hsmen
    obtain ⟨s', hr, hspc, hsa0, hst1, hsm', hpres⟩ :=
      le64_byte_step_sim env p1 p2 (BitVec.ofInt 12 (k : Int)) hl hk64 s hsp
    have hbyte : (s.mem (s.getReg AbiReg.t1 + sextImm12 (BitVec.ofInt 12 (k : Int)))).zeroExtend 64 =
        BitVec.ofNat 64 (bytes[idx + k]'(by omega)).toNat := by
      rw [hsmen, ht1, sextImm12_nat_lt8 k hk, hmem k hk]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.zeroExtend, BitVec.toNat_setWidth, UInt8.toNat_toBitVec, BitVec.toNat_ofNat]
    refine ⟨s', hr, hspc, ?_, hst1.trans ht1, hsm'.trans hsmen, hpres⟩
    rw [hsa0, hbyte]
  let b7 := [Asm.lbu AbiReg.a0 AbiReg.t1 7#12]
  have hflat : ([6, 5, 4, 3, 2, 1, 0].flatMap blk) =
      blk 6 ++ blk 5 ++ blk 4 ++ blk 3 ++ blk 2 ++ blk 1 ++ blk 0 := rfl
  change lkm.linkSpec (pre ++ (b7 ++ ([6, 5, 4, 3, 2, 1, 0].flatMap blk)) ++ post) = .ok (env.code, env.labels) at hlink
  rw [hflat] at hlink
  have hl7 : lkm.linkSpec (pre ++ [Asm.lbu AbiReg.a0 AbiReg.t1 7#12] ++
      (blk 6 ++ blk 5 ++ blk 4 ++ blk 3 ++ blk 2 ++ blk 1 ++ blk 0 ++ post)) =
      .ok (env.code, env.labels) := by simpa only [b7, List.append_assoc] using hlink
  obtain ⟨hr7, hpc7, ha7_0, hoth7, hm7⟩ :=
    step_lbu_off env pre (blk 6 ++ blk 5 ++ blk 4 ++ blk 3 ++ blk 2 ++ blk 1 ++ blk 0 ++ post)
      AbiReg.a0 AbiReg.t1 7#12 (by decide) hl7 (by omega) st hpc
  let s7 := stepReg st AbiReg.a0
    ((loadBytes st.mem (st.getReg AbiReg.t1 + sextImm12 7#12) 1).zeroExtend 64) (st.pc + 4#64)
  have ha7 : s7.getReg AbiReg.a0 = ((0#64 <<< 8) ||| BitVec.ofNat 64 (bytes[idx + 7]'(by omega)).toNat) := by
    rw [ha7_0, show sextImm12 7#12 = BitVec.ofNat 64 7 from rfl,
        hmem 7 (by decide), show (0#64 : BitVec 64) <<< 8 = 0#64 from rfl, BitVec.zero_or]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.zeroExtend, BitVec.toNat_setWidth, UInt8.toNat_toBitVec, BitVec.toNat_ofNat]
  have ht7 : s7.getReg AbiReg.t1 = st.getReg AbiReg.t1 := hoth7 _ (by decide)
  have hp7 : PreservedRegs st s7 :=
    ⟨hoth7 _ (by decide), hoth7 _ (by decide), hoth7 _ (by decide), hoth7 _ (by decide)⟩
  have hblkSz : ∀ k, lkm.totalSize (blk k) = 3 := fun _ => by
    simp [blk, Asm.lbu, Asm.slli, Asm.or, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
  have tw7 : lkm.totalSize (pre ++ b7) = lkm.totalSize pre + 1 := by
    rw [lkm.totalSize_append]; simp only [b7, Asm.lbu, lkm.totalSize_instr]
  have hl6 : lkm.linkSpec ((pre ++ b7) ++ blk 6 ++ (blk 5 ++ blk 4 ++ blk 3 ++ blk 2 ++ blk 1 ++ blk 0 ++ post)) =
      .ok (env.code, env.labels) := by simpa only [List.append_assoc] using hlink
  obtain ⟨s6, hr6, hpc6, ha6, ht6, hm6, hp6⟩ := stepOne 6 (by decide) (pre ++ b7) _ s7 hl6 (by rw [tw7]; omega)
    (by rw [tw7]; exact hpc7) ht7 hm7
  have tw6 : lkm.totalSize (pre ++ b7 ++ blk 6) = lkm.totalSize pre + 4 := by
    rw [lkm.totalSize_append, tw7, hblkSz]
  have hl5 : lkm.linkSpec ((pre ++ b7 ++ blk 6) ++ blk 5 ++ (blk 4 ++ blk 3 ++ blk 2 ++ blk 1 ++ blk 0 ++ post)) =
      .ok (env.code, env.labels) := by simpa only [List.append_assoc] using hlink
  obtain ⟨s5, hr5, hpc5, ha5, ht5, hm5, hp5⟩ := stepOne 5 (by decide) (pre ++ b7 ++ blk 6) _ s6 hl5
    (by rw [tw6]; omega) (by rw [hpc6, tw7, tw6]) ht6 hm6
  have tw5 : lkm.totalSize (pre ++ b7 ++ blk 6 ++ blk 5) = lkm.totalSize pre + 7 := by
    rw [lkm.totalSize_append, tw6, hblkSz]
  have hl4 : lkm.linkSpec ((pre ++ b7 ++ blk 6 ++ blk 5) ++ blk 4 ++ (blk 3 ++ blk 2 ++ blk 1 ++ blk 0 ++ post)) =
      .ok (env.code, env.labels) := by simpa only [List.append_assoc] using hlink
  obtain ⟨s4, hr4, hpc4, ha4, ht4, hm4, hp4⟩ := stepOne 4 (by decide) (pre ++ b7 ++ blk 6 ++ blk 5) _ s5 hl4
    (by rw [tw5]; omega) (by rw [hpc5, tw6, tw5]) ht5 hm5
  have tw4 : lkm.totalSize (pre ++ b7 ++ blk 6 ++ blk 5 ++ blk 4) = lkm.totalSize pre + 10 := by
    rw [lkm.totalSize_append, tw5, hblkSz]
  have hl3 : lkm.linkSpec ((pre ++ b7 ++ blk 6 ++ blk 5 ++ blk 4) ++ blk 3 ++ (blk 2 ++ blk 1 ++ blk 0 ++ post)) =
      .ok (env.code, env.labels) := by simpa only [List.append_assoc] using hlink
  obtain ⟨s3, hr3, hpc3, ha3, ht3, hm3, hp3⟩ := stepOne 3 (by decide) (pre ++ b7 ++ blk 6 ++ blk 5 ++ blk 4) _ s4 hl3
    (by rw [tw4]; omega) (by rw [hpc4, tw5, tw4]) ht4 hm4
  have tw3 : lkm.totalSize (pre ++ b7 ++ blk 6 ++ blk 5 ++ blk 4 ++ blk 3) = lkm.totalSize pre + 13 := by
    rw [lkm.totalSize_append, tw4, hblkSz]
  have hl2 : lkm.linkSpec ((pre ++ b7 ++ blk 6 ++ blk 5 ++ blk 4 ++ blk 3) ++ blk 2 ++ (blk 1 ++ blk 0 ++ post)) =
      .ok (env.code, env.labels) := by simpa only [List.append_assoc] using hlink
  obtain ⟨s2, hr2, hpc2, ha2, ht2, hm2, hp2⟩ := stepOne 2 (by decide) (pre ++ b7 ++ blk 6 ++ blk 5 ++ blk 4 ++ blk 3) _ s3 hl2
    (by rw [tw3]; omega) (by rw [hpc3, tw4, tw3]) ht3 hm3
  have tw2 : lkm.totalSize (pre ++ b7 ++ blk 6 ++ blk 5 ++ blk 4 ++ blk 3 ++ blk 2) = lkm.totalSize pre + 16 := by
    rw [lkm.totalSize_append, tw3, hblkSz]
  have hl1 : lkm.linkSpec ((pre ++ b7 ++ blk 6 ++ blk 5 ++ blk 4 ++ blk 3 ++ blk 2) ++ blk 1 ++ (blk 0 ++ post)) =
      .ok (env.code, env.labels) := by simpa only [List.append_assoc] using hlink
  obtain ⟨s1, hr1, hpc1, ha1, ht1, hm1, hp1⟩ := stepOne 1 (by decide) (pre ++ b7 ++ blk 6 ++ blk 5 ++ blk 4 ++ blk 3 ++ blk 2) _ s2 hl1
    (by rw [tw2]; omega) (by rw [hpc2, tw3, tw2]) ht2 hm2
  have tw1 : lkm.totalSize (pre ++ b7 ++ blk 6 ++ blk 5 ++ blk 4 ++ blk 3 ++ blk 2 ++ blk 1) = lkm.totalSize pre + 19 := by
    rw [lkm.totalSize_append, tw2, hblkSz]
  have hl0 : lkm.linkSpec ((pre ++ b7 ++ blk 6 ++ blk 5 ++ blk 4 ++ blk 3 ++ blk 2 ++ blk 1) ++ blk 0 ++ post) =
      .ok (env.code, env.labels) := by simpa only [List.append_assoc] using hlink
  obtain ⟨s0, hr0, hpc0, ha0', ht0, hm0, hp0⟩ := stepOne 0 (by decide) (pre ++ b7 ++ blk 6 ++ blk 5 ++ blk 4 ++ blk 3 ++ blk 2 ++ blk 1) _ s1 hl0
    (by rw [tw1]; omega) (by rw [hpc1, tw2, tw1]) ht1 hm1
  refine ⟨s0, ?_, ?_, ?_, hm0, hp7.trans (hp6.trans (hp5.trans (hp4.trans (hp3.trans (hp2.trans (hp1.trans hp0))))))⟩
  · rw [show (22 : Nat) = 1 + (3 + (3 + (3 + (3 + (3 + (3 + 3)))))) from rfl]
    rw [run_add, hr7]; dsimp only
    rw [run_add, hr6]; dsimp only
    rw [run_add, hr5]; dsimp only
    rw [run_add, hr4]; dsimp only
    rw [run_add, hr3]; dsimp only
    rw [run_add, hr2]; dsimp only
    rw [run_add, hr1]; dsimp only
    exact hr0
  · rw [hpc0, tw1]
  · rw [ha0', ha1, ha2, ha3, ha4, ha5, ha6, ha7]
    have hle := le64_byte_eq bytes idx hib
    dsimp only at hle
    have hb0 : idx + 0 < bytes.size := by omega
    have hb1 : idx + 1 < bytes.size := by omega
    have hb2 : idx + 2 < bytes.size := by omega
    have hb3 : idx + 3 < bytes.size := by omega
    have hb4 : idx + 4 < bytes.size := by omega
    have hb5 : idx + 5 < bytes.size := by omega
    have hb6 : idx + 6 < bytes.size := by omega
    have hb7 : idx + 7 < bytes.size := by omega
    simp only [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, ↓reduceDIte] at hle
    rw [← hle]

/-! ## 4. General `ProgMemRel` Mutation Lemmas -/

theorem ProgMemRel.set8 {tab : Tab} {L : ProgLayout tab} {rmem : ByteMem} {lm : _root_.L.Mem}
    (hrel : ProgMemRel tab L rmem lm) (a : ArrId) (ha : tab.bytePosOkB a = true)
    (i v : _root_.L.Word) (hi : i.toNat < (lm.arr8 a).size) :
    let addr := L.base8 a + BitVec.ofNat 64 i.toNat
    ProgMemRel tab L (storeBytes rmem addr 1 (v.toBitVec.extractLsb' 0 8)) (lm.set8 a i v) := by
  intro addr
  have heqOut : MemEqOutside (L.arr8Span a) rmem (storeBytes rmem addr 1 (v.toBitVec.extractLsb' 0 8)) := by
    apply MemEqOutside.storeBytes
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    have hcap := (hrel.1 a ha).1
    exact ⟨i.toNat, by dsimp only [ProgLayout.arr8Span]; omega, by simp [addr, ProgLayout.arr8Span]⟩
  have hdisjT : MemDisjoint (L.arr8Span a) L.tabSpan :=
    MemSpan.disjoint_to_memDisjoint (L.arr8Span_valid a) L.tabSpan_valid (L.h8DisjTab a ha)
  have hdisj8 : ∀ a', tab.bytePosOkB a' = true → a' ≠ a → MemDisjoint (L.arr8Span a) (L.arr8Span a') :=
    fun a' ha' hne => MemSpan.disjoint_to_memDisjoint (L.arr8Span_valid a) (L.arr8Span_valid a') (L.h8Disj8 a a' ha ha' hne.symm)
  have hdisj64 : ∀ s, tab.wordPosOkB s = true → MemDisjoint (L.arr8Span a) (L.arr64Span s) :=
    fun s hs => MemSpan.disjoint_to_memDisjoint (L.arr8Span_valid a) (L.arr64Span_valid s) (L.h8Disj64 a s ha hs)
  rcases hrel with ⟨haR, hs64R, hromR, hgR⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a' ha'
    by_cases heq : a' = a
    · rcases heq with rfl
      rcases haR a' ha' with ⟨hcap, hlt, hlen, hbase, hbytes⟩
      have hsz : ((lm.set8 a' i v).arr8 a').size = (lm.arr8 a').size := by
        simp [_root_.L.Mem.arr8, _root_.L.Mem.set8]
      refine ⟨by omega, by omega, ?_, ?_, ?_⟩
      · rw [hsz, ← hlen]
        apply MemEqOutside.readWord64_eq heqOut
        intro k hk
        rw [Tab.len8_eq_nat, int_mul8_ofInt]
        exact hdisjT.symm _ (MemSpan.sub_range _ 8 (L.tab_len8_bound ha') k hk)
      · rw [← hbase]
        apply MemEqOutside.readWord64_eq heqOut
        intro k hk
        rw [Tab.base8_eq_nat, int_mul8_ofInt]
        exact hdisjT.symm _ (MemSpan.sub_range _ 8 (L.tab_base8_bound ha') k hk)
      · intro j hj
        rw [hsz] at hj
        simp only [_root_.L.Mem.arr8, _root_.L.Mem.set8, ↓reduceIte]
        by_cases hji : i.toNat = j
        · subst hji
          have h1 : storeBytes rmem (L.base8 a' + BitVec.ofNat 64 i.toNat) 1
              (v.toBitVec.extractLsb' 0 8) (L.base8 a' + BitVec.ofNat 64 i.toNat) =
              v.toBitVec.extractLsb' 0 8 := by
            have hlb := loadBytes_storeBytes_self rmem addr 1 (by decide) (v.toBitVec.extractLsb' 0 8)
            rw [loadBytes_one_eq_byte] at hlb
            exact hlb
          rw [h1, ← uint64_toUInt8_toBitVec]
          congr 1
          have hsz' : ((lm.arr8 a').set! i.toNat v.toUInt8).size = (lm.arr8 a').size := by simp [Array.set!]
          have hi'' : i.toNat < ((lm.arr8 a').set! i.toNat v.toUInt8).size := by rw [hsz']; exact hi
          have hget : ((lm.arr8 a').set! i.toNat v.toUInt8)[i.toNat]'hi'' = v.toUInt8 := by
            simp [Array.set!, Array.setIfInBounds, hi]
          exact hget.symm
        · have hne : L.base8 a' + BitVec.ofNat 64 j ≠ addr := by
            intro heqa
            have hd := congrArg (fun x => (x - L.base8 a').toNat) heqa
            simp only [addr, BitVec.add_comm (L.base8 a'), BitVec.add_sub_cancel, BitVec.toNat_ofNat] at hd
            have := hlt
            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hd
            exact hji hd.symm
          have hsb : storeBytes rmem addr 1 (v.toBitVec.extractLsb' 0 8) (L.base8 a' + BitVec.ofNat 64 j) =
              rmem (L.base8 a' + BitVec.ofNat 64 j) := by
            apply storeBytes_apply_ne
            intro k hk heqk
            have hk0 : k = 0 := by omega
            subst hk0; apply hne; simpa using heqk
          rw [hsb, hbytes j hj]
          congr 1
          have hj' : j < (lm.arr8 a').size := hj
          have hsz' : ((lm.arr8 a').set! i.toNat v.toUInt8).size = (lm.arr8 a').size := by simp [Array.set!]
          have hj'' : j < ((lm.arr8 a').set! i.toNat v.toUInt8).size := by rw [hsz']; exact hj'
          have hget : ((lm.arr8 a').set! i.toNat v.toUInt8)[j]'hj'' = (lm.arr8 a')[j]'hj' := by
            simp only [Array.set!, Array.setIfInBounds, hi, ↓reduceDIte]
            exact Array.getElem_set_ne hi hj' hji
          exact hget.symm
    · have harr : (lm.set8 a i v).arr8 a' = lm.arr8 a' := by simp [_root_.L.Mem.arr8, _root_.L.Mem.set8, heq]
      rcases haR a' ha' with ⟨hcap, hlt, hlen, hbase, hbytes⟩
      rw [harr]
      refine ⟨hcap, hlt, ?_, ?_, ?_⟩
      · rw [← hlen]
        apply MemEqOutside.readWord64_eq heqOut
        intro k hk
        rw [Tab.len8_eq_nat, int_mul8_ofInt]
        exact hdisjT.symm _ (MemSpan.sub_range _ 8 (L.tab_len8_bound ha') k hk)
      · rw [← hbase]
        apply MemEqOutside.readWord64_eq heqOut
        intro k hk
        rw [Tab.base8_eq_nat, int_mul8_ofInt]
        exact hdisjT.symm _ (MemSpan.sub_range _ 8 (L.tab_base8_bound ha') k hk)
      · intro j hj
        rw [← hbytes j hj]
        exact heqOut _ ((hdisj8 a' ha' heq).symm _ ⟨j, by dsimp only [ProgLayout.arr8Span]; omega, rfl⟩)
  · intro s hs
    have harr : (lm.set8 a i v).arr64 s = lm.arr64 s := rfl
    rcases hs64R s hs with ⟨hcap, hlt, hlen, hbase, hwords⟩
    rw [harr]
    refine ⟨hcap, hlt, ?_, ?_, ?_⟩
    · rw [← hlen]
      apply MemEqOutside.readWord64_eq heqOut
      intro k hk
      rw [Tab.len64_eq_nat, int_mul8_ofInt]
      exact hdisjT.symm _ (MemSpan.sub_range _ 8 (L.tab_len64_bound hs) k hk)
    · rw [← hbase]
      apply MemEqOutside.readWord64_eq heqOut
      intro k hk
      rw [Tab.base64_eq_nat, int_mul8_ofInt]
      exact hdisjT.symm _ (MemSpan.sub_range _ 8 (L.tab_base64_bound hs) k hk)
    · intro j hj
      rw [← hwords j hj]
      apply MemEqOutside.readWord64_eq heqOut
      intro k hk
      exact (hdisj64 s hs).symm _
        (MemSpan.sub_range (s := L.arr64Span s) (8 * j) 8 (by dsimp only [ProgLayout.arr64Span]; omega) k hk)
  · intro k hk
    rw [← hromR k hk]
    refine heqOut _ (hdisjT.symm _ ⟨tab.romBase.toNat + k, ?_, ?_⟩)
    · have hrb := L.tab_rom_bound; dsimp only [ProgLayout.tabSpan]; omega
    · simp only [ProgLayout.tabSpan, BitVec.ofNat_add]
  · intro g hgBound
    have hg : (lm.set8 a i v).glob g = lm.glob g := rfl
    rw [hg, ← hgR g hgBound]
    apply MemEqOutside.readWord64_eq heqOut
    intro k hk
    rw [Tab.globOff_eq_nat, int_mul8_ofInt]
    exact hdisjT.symm _ (MemSpan.sub_range _ 8 (L.tab_globOff_bound g hgBound) k hk)

theorem ProgMemRel.set64 {tab : Tab} {L : ProgLayout tab} {rmem : ByteMem} {lm : _root_.L.Mem}
    (hrel : ProgMemRel tab L rmem lm) (s : TieredArray) (hs : tab.wordPosOkB s = true)
    (i v : _root_.L.Word) (hi : i.toNat < (lm.arr64 s).size) :
    let addr := L.base64 s + BitVec.ofNat 64 (8 * i.toNat)
    ProgMemRel tab L (writeWord64 rmem addr v.toBitVec) (lm.set64 s i v) := by
  intro addr
  have hcapS := (hrel.2.1 s hs).1
  have hltS := (hrel.2.1 s hs).2.1
  have heqOut : MemEqOutside (L.arr64Span s) rmem (writeWord64 rmem addr v.toBitVec) := by
    apply MemEqOutside.writeWord64
    intro k hk
    exact MemSpan.sub_range (s := L.arr64Span s) (8 * i.toNat) 8
      (by dsimp only [ProgLayout.arr64Span]; omega) k hk
  have hdisjT : MemDisjoint (L.arr64Span s) L.tabSpan :=
    MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid s) L.tabSpan_valid (L.h64DisjTab s hs)
  have hdisj8 : ∀ a, tab.bytePosOkB a = true → MemDisjoint (L.arr64Span s) (L.arr8Span a) :=
    fun a ha => MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid s) (L.arr8Span_valid a) (L.h8Disj64 a s ha hs).symm
  have hdisj64 : ∀ s', tab.wordPosOkB s' = true → s' ≠ s → MemDisjoint (L.arr64Span s) (L.arr64Span s') :=
    fun s' hs' hne => MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid s) (L.arr64Span_valid s') (L.h64Disj64 s s' hs hs' hne.symm)
  rcases hrel with ⟨haR, hs64R, hromR, hgR⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    have harr : (lm.set64 s i v).arr8 a = lm.arr8 a := rfl
    rcases haR a ha with ⟨hcap, hlt, hlen, hbase, hbytes⟩
    rw [harr]
    refine ⟨hcap, hlt, ?_, ?_, ?_⟩
    · rw [← hlen]
      apply MemEqOutside.readWord64_eq heqOut
      intro k hk
      rw [Tab.len8_eq_nat, int_mul8_ofInt]
      exact hdisjT.symm _ (MemSpan.sub_range _ 8 (L.tab_len8_bound ha) k hk)
    · rw [← hbase]
      apply MemEqOutside.readWord64_eq heqOut
      intro k hk
      rw [Tab.base8_eq_nat, int_mul8_ofInt]
      exact hdisjT.symm _ (MemSpan.sub_range _ 8 (L.tab_base8_bound ha) k hk)
    · intro j hj
      rw [← hbytes j hj]
      exact heqOut _ ((hdisj8 a ha).symm _ ⟨j, by dsimp only [ProgLayout.arr8Span]; omega, rfl⟩)
  · intro s' hs'
    by_cases heq : s' = s
    · rcases heq with rfl
      rcases hs64R s' hs' with ⟨hcap, hlt, hlen, hbase, hwords⟩
      have hsz : ((lm.set64 s' i v).arr64 s').size = (lm.arr64 s').size := by
        simp [_root_.L.Mem.arr64, _root_.L.Mem.set64]
      refine ⟨by omega, by omega, ?_, ?_, ?_⟩
      · rw [hsz, ← hlen]
        apply MemEqOutside.readWord64_eq heqOut
        intro k hk
        rw [Tab.len64_eq_nat, int_mul8_ofInt]
        exact hdisjT.symm _ (MemSpan.sub_range _ 8 (L.tab_len64_bound hs') k hk)
      · rw [← hbase]
        apply MemEqOutside.readWord64_eq heqOut
        intro k hk
        rw [Tab.base64_eq_nat, int_mul8_ofInt]
        exact hdisjT.symm _ (MemSpan.sub_range _ 8 (L.tab_base64_bound hs') k hk)
      · intro j hj
        rw [hsz] at hj
        by_cases hji : i.toNat = j
        · subst hji
          simp only [_root_.L.Mem.arr64, _root_.L.Mem.set64, ↓reduceIte]
          have hself : readWord64 (writeWord64 rmem addr v.toBitVec) addr = v.toBitVec :=
            loadBytes_storeBytes_self rmem addr 8 (by decide) v.toBitVec
          rw [hself]
          congr 1
          have hsz' : ((lm.arr64 s').set! i.toNat v).size = (lm.arr64 s').size := by simp [Array.set!]
          have hi'' : i.toNat < ((lm.arr64 s').set! i.toNat v).size := by rw [hsz']; exact hi
          have hget : ((lm.arr64 s').set! i.toNat v)[i.toNat]'hi'' = v := by
            simp [Array.set!, Array.setIfInBounds, hi]
          exact hget.symm
        · have hdisjW : ∀ k, k < 8 → ¬(slotSpan addr 0).contains (L.base64 s' + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 k) := by
            intro k hk ⟨k', hk', heqk⟩
            dsimp only [slotSpan, slotAddr] at hk' heqk
            rw [BitVec.add_zero] at heqk
            have hlt1 : 8 * j + k < 2 ^ 64 := by omega
            have hlt2 : 8 * i.toNat + k' < 2 ^ 64 := by omega
            have hd := congrArg (fun x => (x - L.base64 s').toNat) heqk
            have hsub (m : Nat) : (L.base64 s' + BitVec.ofNat 64 m - L.base64 s').toNat = m % 2 ^ 64 := by
              rw [BitVec.add_comm (L.base64 s'), BitVec.add_sub_cancel, BitVec.toNat_ofNat]
            rw [BitVec.add_assoc, ← BitVec.ofNat_add, hsub] at hd
            dsimp only [addr] at hd
            rw [BitVec.add_assoc, ← BitVec.ofNat_add, hsub] at hd
            rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hd
            omega
          have heqw : readWord64 (writeWord64 rmem addr v.toBitVec) (L.base64 s' + BitVec.ofNat 64 (8 * j)) =
              readWord64 rmem (L.base64 s' + BitVec.ofNat 64 (8 * j)) := by
            apply loadBytes_congr
            intro k hk
            apply storeBytes_apply_ne
            intro k' hk' heqk
            apply hdisjW k hk
            exact ⟨k', hk', by simpa [slotSpan, slotAddr, BitVec.add_zero] using heqk⟩
          rw [heqw, hwords j hj]
          simp only [_root_.L.Mem.arr64, _root_.L.Mem.set64, ↓reduceIte]
          congr 1
          have hj' : j < (lm.arr64 s').size := hj
          have hsz' : ((lm.arr64 s').set! i.toNat v).size = (lm.arr64 s').size := by simp [Array.set!]
          have hj'' : j < ((lm.arr64 s').set! i.toNat v).size := by rw [hsz']; exact hj'
          have hget : ((lm.arr64 s').set! i.toNat v)[j]'hj'' = (lm.arr64 s')[j]'hj' := by
            simp only [Array.set!, Array.setIfInBounds, hi, ↓reduceDIte]
            exact Array.getElem_set_ne hi hj' hji
          exact hget.symm
    · have harr : (lm.set64 s i v).arr64 s' = lm.arr64 s' := by simp [_root_.L.Mem.arr64, _root_.L.Mem.set64, heq]
      rcases hs64R s' hs' with ⟨hcap, hlt, hlen, hbase, hwords⟩
      rw [harr]
      refine ⟨hcap, hlt, ?_, ?_, ?_⟩
      · rw [← hlen]
        apply MemEqOutside.readWord64_eq heqOut
        intro k hk
        rw [Tab.len64_eq_nat, int_mul8_ofInt]
        exact hdisjT.symm _ (MemSpan.sub_range _ 8 (L.tab_len64_bound hs') k hk)
      · rw [← hbase]
        apply MemEqOutside.readWord64_eq heqOut
        intro k hk
        rw [Tab.base64_eq_nat, int_mul8_ofInt]
        exact hdisjT.symm _ (MemSpan.sub_range _ 8 (L.tab_base64_bound hs') k hk)
      · intro j hj
        rw [← hwords j hj]
        apply MemEqOutside.readWord64_eq heqOut
        intro k hk
        exact (hdisj64 s' hs' heq).symm _
          (MemSpan.sub_range (s := L.arr64Span s') (8 * j) 8 (by dsimp only [ProgLayout.arr64Span]; omega) k hk)
  · intro k hk
    rw [← hromR k hk]
    refine heqOut _ (hdisjT.symm _ ⟨tab.romBase.toNat + k, ?_, ?_⟩)
    · have hrb := L.tab_rom_bound; dsimp only [ProgLayout.tabSpan]; omega
    · simp only [ProgLayout.tabSpan, BitVec.ofNat_add]
  · intro g hgBound
    have hg : (lm.set64 s i v).glob g = lm.glob g := rfl
    rw [hg, ← hgR g hgBound]
    apply MemEqOutside.readWord64_eq heqOut
    intro k hk
    rw [Tab.globOff_eq_nat, int_mul8_ofInt]
    exact hdisjT.symm _ (MemSpan.sub_range _ 8 (L.tab_globOff_bound g hgBound) k hk)

theorem ProgMemRel.setG {tab : Tab} {L : ProgLayout tab} {rmem : ByteMem} {lm : _root_.L.Mem}
    (hrel : ProgMemRel tab L rmem lm) (g : GVar) (hg : g.id < tab.ng) (v : _root_.L.Word) :
    let addr := L.T + BitVec.ofInt 64 (tab.globOff g)
    ProgMemRel tab L (writeWord64 rmem addr v.toBitVec) (lm.setG g v) := by
  intro addr
  let gSpan : MemSpan := ⟨addr, 8⟩
  have hgb_nat : tab.globBase.toNat = 8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres) := by
    have hnn : 0 ≤ tab.globBase := by simp [Tab.globBase, Tab.resBase, Tab.romBase]; omega
    rw [← Int.ofNat_inj, Int.toNat_of_nonneg hnn]
    simp only [Tab.globBase, Tab.resBase, Tab.romBase]; push_cast; omega
  have hgSub : gSpan.sub L.tabSpan := by
    intro a ⟨k, hk, ha⟩
    have hk8 : k < 8 := hk
    subst ha
    refine ⟨(tab.globOff g).toNat + k, ?_, ?_⟩
    · have hm := L.tabMin_strong
      have hb := L.tab_globOff_bound g hg
      have hgn : tab.globOff g = ((8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres + g.id) : Nat) : Int) :=
        Tab.globOff_eq_nat tab g
      rw [hgn]; simp only [Int.toNat_natCast, ProgLayout.tabSpan]; omega
    · dsimp only [gSpan, ProgLayout.tabSpan, addr]
      rw [Tab.globOff_eq_nat, int_mul8_ofInt, BitVec.add_assoc, ← BitVec.ofNat_add, Int.toNat_natCast]
  have heqOut : MemEqOutside gSpan rmem (writeWord64 rmem addr v.toBitVec) := by
    apply MemEqOutside.writeWord64
    intro k hk; exact ⟨k, hk, rfl⟩
  have hdisj8 : ∀ a, tab.bytePosOkB a = true → MemDisjoint gSpan (L.arr8Span a) := fun a ha =>
    MemDisjoint.of_sub_left hgSub
      (MemSpan.disjoint_to_memDisjoint L.tabSpan_valid (L.arr8Span_valid a) (L.h8DisjTab a ha).symm)
  have hdisj64 : ∀ s, tab.wordPosOkB s = true → MemDisjoint gSpan (L.arr64Span s) := fun s hs =>
    MemDisjoint.of_sub_left hgSub
      (MemSpan.disjoint_to_memDisjoint L.tabSpan_valid (L.arr64Span_valid s) (L.h64DisjTab s hs).symm)
  have htabOff_disj : ∀ off : Nat, off + 8 ≤ tab.globBase.toNat + 8 * g.id →
      MemDisjoint gSpan ⟨L.T + BitVec.ofNat 64 off, 8⟩ := by
    intro off hoff x ⟨k, hk, heqk⟩ ⟨k', hk', heqx⟩
    have hk8 : k < 8 := hk
    have hk'8 : k' < 8 := hk'
    have hb := L.tab_globOff_bound g hg
    have hv := L.hTValid
    have hgn : 8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres + g.id) =
        tab.globBase.toNat + 8 * g.id := by rw [hgb_nat]; omega
    have h1 : x.toNat = L.T.toNat + tab.globBase.toNat + 8 * g.id + k := by
      rw [heqk]; dsimp only [gSpan, addr]; rw [Tab.globOff_eq_nat, int_mul8_ofInt, hgn]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show tab.globBase.toNat + 8 * g.id + k < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show L.T.toNat + (tab.globBase.toNat + 8 * g.id + k) < 2 ^ 64 by omega)]
      omega
    have h2 : x.toNat = L.T.toNat + off + k' := by
      rw [heqx, BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show off + k' < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show L.T.toNat + (off + k') < 2 ^ 64 by omega)]
      omega
    omega
  rcases hrel with ⟨haR, hs64R, hromR, hgR⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    have harr : (lm.setG g v).arr8 a = lm.arr8 a := rfl
    rcases haR a ha with ⟨hcap, hlt, hlen, hbase, hbytes⟩
    rw [harr]
    refine ⟨hcap, hlt, ?_, ?_, ?_⟩
    · rw [← hlen]
      apply MemEqOutside.readWord64_eq heqOut
      intro k hk
      rw [Tab.len8_eq_nat, int_mul8_ofInt]
      have hd := htabOff_disj (8 * (2 + (tab.nb + tab.nw) + tab.pos8 a))
        (by rw [hgb_nat]; have := (Tab.bytePosOk_lt ha).2.1; omega)
      exact hd.symm _ ⟨k, hk, rfl⟩
    · rw [← hbase]
      apply MemEqOutside.readWord64_eq heqOut
      intro k hk
      rw [Tab.base8_eq_nat, int_mul8_ofInt]
      have hd := htabOff_disj (8 * (2 + tab.pos8 a))
        (by rw [hgb_nat]; have := (Tab.bytePosOk_lt ha).2.1; omega)
      exact hd.symm _ ⟨k, hk, rfl⟩
    · intro j hj
      rw [← hbytes j hj]
      exact heqOut _ ((hdisj8 a ha).symm _ ⟨j, by dsimp only [ProgLayout.arr8Span]; omega, rfl⟩)
  · intro s hs
    have harr : (lm.setG g v).arr64 s = lm.arr64 s := rfl
    rcases hs64R s hs with ⟨hcap, hlt, hlen, hbase, hwords⟩
    rw [harr]
    refine ⟨hcap, hlt, ?_, ?_, ?_⟩
    · rw [← hlen]
      apply MemEqOutside.readWord64_eq heqOut
      intro k hk
      rw [Tab.len64_eq_nat, int_mul8_ofInt]
      have hd := htabOff_disj (8 * (2 + (tab.nb + tab.nw) + tab.pos64 s))
        (by rw [hgb_nat]; have := (Tab.wordPosOk_lt hs).2.1; omega)
      exact hd.symm _ ⟨k, hk, rfl⟩
    · rw [← hbase]
      apply MemEqOutside.readWord64_eq heqOut
      intro k hk
      rw [Tab.base64_eq_nat, int_mul8_ofInt]
      have hd := htabOff_disj (8 * (2 + tab.pos64 s))
        (by rw [hgb_nat]; have := (Tab.wordPosOk_lt hs).2.1; omega)
      exact hd.symm _ ⟨k, hk, rfl⟩
    · intro j hj
      rw [← hwords j hj]
      apply MemEqOutside.readWord64_eq heqOut
      intro k hk
      exact (hdisj64 s hs).symm _
        (MemSpan.sub_range (s := L.arr64Span s) (8 * j) 8 (by dsimp only [ProgLayout.arr64Span]; omega) k hk)
  · intro k hk
    rw [← hromR k hk]
    apply heqOut
    intro ⟨j, hj, heqx⟩
    have hj8 : j < 8 := hj
    have hb := L.tab_globOff_bound g hg
    have hv := L.hTValid
    have hrb := L.tab_rom_bound
    have hgn : 8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres + g.id) =
        tab.globBase.toNat + 8 * g.id := by
      simp only [Tab.globBase, Tab.resBase, Tab.romBase]; omega
    have hrn : tab.romBase.toNat + k < tab.globBase.toNat + 8 * g.id := by
      simp only [Tab.globBase, Tab.resBase, Tab.romBase, Tab.romWords] at hrb ⊢; omega
    have h1 : (L.T + BitVec.ofNat 64 (tab.romBase.toNat + k)).toNat = L.T.toNat + (tab.romBase.toNat + k) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have h2 : (addr + BitVec.ofNat 64 j).toNat = L.T.toNat + (tab.globBase.toNat + 8 * g.id) + j := by
      dsimp only [addr]; rw [Tab.globOff_eq_nat, int_mul8_ofInt, hgn, BitVec.add_assoc, ← BitVec.ofNat_add,
        BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    have hnat := congrArg BitVec.toNat heqx
    rw [h1, h2] at hnat
    omega
  · intro g' hg'
    by_cases heq : g' = g
    · subst heq
      have hself : readWord64 (writeWord64 rmem addr v.toBitVec) addr = v.toBitVec :=
        loadBytes_storeBytes_self rmem addr 8 (by decide) v.toBitVec
      rw [hself]
      simp [_root_.L.Mem.setG]
    · have hne : g'.id ≠ g.id := fun hi => heq (by cases g'; cases g; simp at hi; subst hi; rfl)
      have heqv : (lm.setG g v).glob g' = lm.glob g' := by simp [_root_.L.Mem.setG, heq]
      rw [heqv, ← hgR g' hg']
      apply MemEqOutside.readWord64_eq heqOut
      intro k hk ⟨j, hj, heqx⟩
      have hj8 : j < 8 := hj
      have hb1 := L.tab_globOff_bound g hg
      have hb2 := L.tab_globOff_bound g' hg'
      have hv := L.hTValid
      have h1 : (L.T + BitVec.ofInt 64 (tab.globOff g') + BitVec.ofNat 64 k).toNat =
          L.T.toNat + 8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres + g'.id) + k := by
        rw [Tab.globOff_eq_nat, int_mul8_ofInt, BitVec.add_assoc, ← BitVec.ofNat_add,
            BitVec.toNat_add, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (show 8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres + g'.id) + k < 2 ^ 64 by omega),
            Nat.mod_eq_of_lt (show L.T.toNat + (8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres + g'.id) + k) < 2 ^ 64 by omega)]
        omega
      have h2 : (addr + BitVec.ofNat 64 j).toNat =
          L.T.toNat + 8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres + g.id) + j := by
        dsimp only [addr]; rw [Tab.globOff_eq_nat, int_mul8_ofInt, BitVec.add_assoc, ← BitVec.ofNat_add,
          BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show 8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres + g.id) + j < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show L.T.toNat + (8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres + g.id) + j) < 2 ^ 64 by omega)]
        omega
      have hnat := congrArg BitVec.toNat heqx
      rw [h1, h2] at hnat
      omega

theorem ProgMemRel.set32 {tab : Tab} {L : ProgLayout tab} {rmem : ByteMem} {lm : _root_.L.Mem}
    (hrel : ProgMemRel tab L rmem lm) (s : TieredArray) (hs : tab.wordPosOkB s = true)
    (i v : _root_.L.Word) (hi : (i / 2).toNat < (lm.arr64 s).size) :
    let addr4 := L.base64 s + BitVec.ofNat 64 (4 * i.toNat)
    ProgMemRel tab L (storeBytes rmem addr4 4 (v.toBitVec.extractLsb' 0 32)) (lm.set32 s i v) := by
  intro addr4
  have hword_rel := hrel.2.1 s hs
  have hlt61 := hword_rel.2.1
  have hi' : i.toNat / 2 < (lm.arr64 s).size := hi
  have hw := hword_rel.2.2.2.2 (i / 2).toNat hi
  have h4eq : addr4 = if decide (i.toNat % 2 = 1) then
      (L.base64 s + BitVec.ofNat 64 (8 * (i / 2).toNat)) + 4#64
      else (L.base64 s + BitVec.ofNat 64 (8 * (i / 2).toNat)) := by
    dsimp only [addr4]
    have hdiv2 : (i / 2).toNat = i.toNat / 2 := rfl
    rw [hdiv2]
    by_cases hmod : i.toNat % 2 = 1
    · simp only [hmod, decide_true, ↓reduceIte, BitVec.add_assoc]
      congr 1; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by decide : 4 < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · simp only [hmod, decide_false, Bool.false_eq_true, ↓reduceIte]
      congr 1; congr 1; omega
  have hsb := storeBytes_4_to_writeWord64 rmem (L.base64 s + BitVec.ofNat 64 (8 * (i / 2).toNat))
    (v.toBitVec.extractLsb' 0 32) (decide (i.toNat % 2 = 1))
  dsimp only at hsb
  rw [← h4eq] at hsb
  rw [hsb]
  have hnew_eq : (let old := UInt64.ofNat (readWord64 rmem (L.base64 s + BitVec.ofNat 64 (8 * (i / 2).toNat))).toNat
      setHalf32 old (if decide (i.toNat % 2 = 1) = true then 1 else 0)
        (UInt64.ofNat (v.toBitVec.extractLsb' 0 32).toNat)).toBitVec =
      (setHalf32 ((lm.arr64 s).getD (i / 2).toNat 0) i v).toBitVec := by
    have hold_eq : UInt64.ofNat (readWord64 rmem (L.base64 s + BitVec.ofNat 64 (8 * (i / 2).toNat))).toNat =
        (lm.arr64 s).getD (i / 2).toNat 0 := by
      rw [hw, UInt64.toNat_toBitVec, UInt64.ofNat_toNat]
      simp [Array.getD, show (i / 2).toNat = i.toNat / 2 from rfl, hi']
    have hv_eq : UInt64.ofNat (v.toBitVec.extractLsb' 0 32).toNat = v % 4294967296 := by
      apply uint64_eq_of_toNat
      rw [UInt64.toNat_ofNat', BitVec.extractLsb'_toNat, Nat.shiftRight_zero, UInt64.toNat_toBitVec,
          UInt64.toNat_mod, show (4294967296 : UInt64).toNat = 2 ^ 32 from rfl,
          Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))]
    dsimp only; rw [hold_eq]
    dsimp only [_root_.L.setHalf32]
    have him : (i % 2).toNat = i.toNat % 2 := by
      rw [UInt64.toNat_mod, show (2 : UInt64).toNat = 2 from rfl]
    by_cases hmod : i.toNat % 2 = 1
    · have hne0 : i % 2 ≠ 0 := fun h0 => by
        have := congrArg UInt64.toNat h0
        rw [him, show (0 : UInt64).toNat = 0 from rfl] at this
        omega
      simp only [hmod, decide_true, ↓reduceIte]
      rw [hv_eq]
      have hm : (v % 4294967296) % 4294967296 = v % 4294967296 := by
        apply uint64_eq_of_toNat; simp [UInt64.toNat_mod]
      rw [hm]
      split
      case isTrue hz => exfalso; exact (by decide : ¬((1 : UInt64) % 2 = 0)) hz
      case isFalse _ => rfl
    · have hmod0 : i.toNat % 2 = 0 := by omega
      have heq0 : i % 2 = 0 := uint64_eq_of_toNat (by simpa [him] using hmod0)
      simp only [hmod, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [hv_eq]
      have hm : (v % 4294967296) % 4294967296 = v % 4294967296 := by
        apply uint64_eq_of_toNat; simp [UInt64.toNat_mod]
      rw [hm]
      split
      case isTrue _ => rfl
      case isFalse hne => exfalso; exact hne (by decide)
  rw [hnew_eq]
  exact ProgMemRel.set64 hrel s hs (i / 2) (setHalf32 ((lm.arr64 s).getD (i / 2).toNat 0) i v) hi


/-! ## 4b. Shared Helper Lemmas -/

theorem prog_step_br {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem) (op : BranchOp)
    (rs1 rs2 : Reg) (target : String) (tgt : Nat)
    (htgt : lookupLabel env.labels target = some tgt)
    (hrs : rs1 ≠ AbiReg.t6 ∧ rs2 ≠ AbiReg.t6)
    (hlink : lkm.linkSpec (pre ++ [.br op rs1 rs2 target] ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.itemSize (.br op rs1 rs2 target)) < 2 ^ 64) (st : State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre)) :
    ∃ k st', 1 ≤ k ∧
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = (if evalBranch op (st.getReg rs1) (st.getReg rs2)
                then BitVec.ofNat 64 (4 * tgt)
                else BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.itemSize (.br op rs1 rs2 target)))) ∧
      (∀ q, q ≠ AbiReg.t6 ∧ q ≠ AbiReg.s1 → st'.getReg q = st.getReg q) ∧
      PreservedRegs st st' ∧
      st'.mem = st.mem := by
  obtain ⟨tgt', k, st', hk, hlook, hrun, hpc', hreg, hmem⟩ :=
    step_item_br_lm lkm env.hrom pre post op rs1 rs2 target hlink hrs h64 st hpc
  rw [htgt] at hlook; obtain rfl := Option.some.inj hlook
  exact ⟨k, st', hk, hrun, hpc', fun _ hq => (hreg.getReg_eq hq).symm, PreservedRegs.of_regEqExceptT6 hreg, hmem⟩

theorem prog_step_br_fall {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem) (op : BranchOp)
    (rs1 rs2 : Reg) (target : String) (tgt : Nat)
    (htgt : lookupLabel env.labels target = some tgt)
    (hrs : rs1 ≠ AbiReg.t6 ∧ rs2 ≠ AbiReg.t6)
    (hlink : lkm.linkSpec (pre ++ [.br op rs1 rs2 target] ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.itemSize (.br op rs1 rs2 target)) < 2 ^ 64) (st : State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hcond : evalBranch op (st.getReg rs1) (st.getReg rs2) = false) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize [.br op rs1 rs2 target])) ∧
      (∀ q, q ≠ AbiReg.t6 ∧ q ≠ AbiReg.s1 → st'.getReg q = st.getReg q) ∧
      PreservedRegs st st' ∧
      st'.mem = st.mem := by
  obtain ⟨k, st', _, hrun, hpc', hoth, hpres, hmem⟩ :=
    prog_step_br env pre post op rs1 rs2 target tgt htgt hrs hlink h64 st hpc
  simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hpc'
  exact ⟨k, st', hrun, by simpa [lkm.totalSize_singleton] using hpc', hoth, hpres, hmem⟩

theorem prog_step_br_taken {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem) (op : BranchOp)
    (rs1 rs2 : Reg) (target : String) (tgt : Nat)
    (htgt : lookupLabel env.labels target = some tgt)
    (hrs : rs1 ≠ AbiReg.t6 ∧ rs2 ≠ AbiReg.t6)
    (hlink : lkm.linkSpec (pre ++ [.br op rs1 rs2 target] ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.itemSize (.br op rs1 rs2 target)) < 2 ^ 64) (st : State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hcond : evalBranch op (st.getReg rs1) (st.getReg rs2) = true) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * tgt) ∧
      (∀ q, q ≠ AbiReg.t6 ∧ q ≠ AbiReg.s1 → st'.getReg q = st.getReg q) ∧
      PreservedRegs st st' ∧
      st'.mem = st.mem := by
  obtain ⟨k, st', _, hrun, hpc', hoth, hpres, hmem⟩ :=
    prog_step_br env pre post op rs1 rs2 target tgt htgt hrs hlink h64 st hpc
  simp only [hcond, ↓reduceIte] at hpc'
  exact ⟨k, st', hrun, hpc', hoth, hpres, hmem⟩

theorem tierAddrOk_len64_addr_T {tab : Tab} (T : BitVec 64) (a : ArrId) (u : _root_.L.Word)
    (ht : TierAddrOk tab a u) :
    let off := if (u &&& 1) == 0 then 0#64 else 8#64
    tab.wordPosOkB (tierA a u) = true ∧
    (T + off) + BitVec.ofInt 64 (tab.len64 (TieredArray.t0 a)) =
      T + BitVec.ofInt 64 (tab.len64 (tierA a u)) ∧
    (T + off) + BitVec.ofInt 64 (tab.base64 (TieredArray.t0 a)) =
      T + BitVec.ofInt 64 (tab.base64 (tierA a u)) := by
  have h0 := tierAddrOk_len64_addr a u ht
  dsimp only at h0 ⊢
  refine ⟨h0.1, ?_, ?_⟩
  · rw [BitVec.add_assoc, ← BitVec.zero_add (if (u &&& 1) == 0 then 0#64 else 8#64), h0.2.1]
  · rw [BitVec.add_assoc, ← BitVec.zero_add (if (u &&& 1) == 0 then 0#64 else 8#64), h0.2.2]

theorem tieredOk_len64_addr_T {tab : Tab} (T : BitVec 64) (a : ArrId) (u : _root_.L.Word)
    (ht : tab.tieredOkB a = true) :
    let off := if (u &&& 1) == 0 then 0#64 else 8#64
    tab.wordPosOkB (tierA a u) = true ∧
    (T + off) + BitVec.ofInt 64 (tab.len64 (TieredArray.t0 a)) =
      T + BitVec.ofInt 64 (tab.len64 (tierA a u)) ∧
    (T + off) + BitVec.ofInt 64 (tab.base64 (TieredArray.t0 a)) =
      T + BitVec.ofInt 64 (tab.base64 (tierA a u)) :=
  tierAddrOk_len64_addr_T T a u (Or.inl ht)

theorem prog_mul_lo_hi_toNat (x y : UInt64) :
    BitVec.ofNat 64 (x.toBitVec.toNat * y.toBitVec.toNat % 2 ^ 64) = (x * y).toBitVec ∧
    BitVec.ofNat 64 (x.toBitVec.toNat * y.toBitVec.toNat / 2 ^ 64) = (BinOp.mulhi.eval x y).toBitVec := by
  constructor
  · rw [UInt64.toBitVec_mul]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_mod]
  · rw [BinOp.eval, UInt64.toBitVec_ofNat', UInt64.toNat_toBitVec, UInt64.toNat_toBitVec]

theorem foldl_max_ge {α : Type} (f : α → Nat) (xs : List α) (init : Nat) :
    init ≤ xs.foldl (fun acc x => max acc (f x)) init := by
  induction xs generalizing init with
  | nil => exact Nat.le_refl init
  | cons x xs ih => exact Nat.le_trans (Nat.le_max_left init (f x)) (ih (max init (f x)))

theorem foldl_max_mem {α : Type} {f : α → Nat} {xs : List α} {init : Nat} {x : α} (hx : x ∈ xs) :
    f x ≤ xs.foldl (fun acc y => max acc (f y)) init := by
  induction xs generalizing init with
  | nil => cases hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hy
    · exact Nat.le_trans (Nat.le_max_right init (f x)) (foldl_max_ge f ys (max init (f x)))
    · exact ih hy

theorem mem_zipIdx_succ {α : Type} (x : α) (xs : List α) (k idx : Nat) :
    (x, idx + 1) ∈ xs.zipIdx (k + 1) ↔ (x, idx) ∈ xs.zipIdx k := by
  induction xs generalizing k with
  | nil => simp [List.zipIdx]
  | cons y ys ih =>
    simp only [List.zipIdx, List.mem_cons, Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, h⟩ | h)
      · exact Or.inl ⟨rfl, by omega⟩
      · exact Or.inr ((ih (k + 1)).mp h)
    · rintro (⟨rfl, rfl⟩ | h)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ((ih (k + 1)).mpr h)

theorem mem_zipIdx_cons_succ {α : Type} (e x : α) (es : List α) (idx : Nat) :
    (x, idx + 1) ∈ (e :: es).zipIdx ↔ (x, idx) ∈ es.zipIdx := by
  simp only [List.zipIdx, List.mem_cons, Prod.mk.injEq]
  constructor
  · rintro (⟨_, h⟩ | h)
    · omega
    · exact (mem_zipIdx_succ x es 0 idx).mp h
  · intro h; exact Or.inr ((mem_zipIdx_succ x es 0 idx).mpr h)

theorem u64_toBitVec_eq_ofNat (v : _root_.L.Word) :
    v.toBitVec = BitVec.ofNat 64 v.toNat := by
  apply BitVec.eq_of_toNat_eq; simp

end ConAgua.RISCV.Compiler
