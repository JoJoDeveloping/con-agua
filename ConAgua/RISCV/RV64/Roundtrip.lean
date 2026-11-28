import ConAgua.RISCV.RV64.Encode
import ConAgua.RISCV.RV64.Decode

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Encode/Decode Bijection Theorems (`ConAgua.RISCV.RV64.Roundtrip`)

Pure kernel-checked proof (zero `sorry`, zero `native_decide`, zero `bv_decide`, standard
Lean axioms only) that `encode` and `decode` form an exact bijection between `Instr` and
the accepted 32-bit machine words:
- `decode_encode`: `decode (encode inst) = some inst` (every `Instr` decodes back cleanly).
- `encode_decode`: `decode w = some inst → encode inst = w` (`decode` ignores zero bits and
  accepts no alias / non-canonical encodings).
- `decode_eq_some_iff`: `decode w = some inst ↔ encode inst = w`.
- `encode_injective`: `encode a = encode b → a = b`.
-/

namespace ConAgua.RISCV.RV64

private theorem append_extract_lo {n m : Nat} (a : BitVec n) (b : BitVec m) :
    (a ++ b).extractLsb' 0 m = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.getLsbD_append, hi]

private theorem append_extract_hi {n m k lo : Nat} (a : BitVec n) (b : BitVec m)
    (hm : m ≤ lo) :
    (a ++ b).extractLsb' lo k = a.extractLsb' (lo - m) k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, BitVec.getLsbD_append]
  have h1 : ¬ (lo + i < m) := by omega
  simp [h1, show lo + i - m = (lo - m) + i by omega]

private theorem extract_self {n : Nat} (a : BitVec n) : a.extractLsb' 0 n = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

macro "bit_eq" : tactic =>
  `(tactic| (
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
    try grind))

/-! ## Field Extraction After Encoding (`get* (encode* ...)`, §§2.2, 2.3 Format Order) -/

@[simp] theorem getOpcode_encodeR (f7 : BitVec 7) (rs2 rs1 : Reg) (f3 : BitVec 3)
    (rd : Reg) (opc : BitVec 7) :
    getOpcode (encodeR f7 rs2 rs1 f3 rd opc) = opc := append_extract_lo _ _
@[simp] theorem getRd_encodeR (f7 : BitVec 7) (rs2 rs1 : Reg) (f3 : BitVec 3)
    (rd : Reg) (opc : BitVec 7) :
    getRd (encodeR f7 rs2 rs1 f3 rd opc) = rd := by
  unfold getRd encodeR; rw [append_extract_hi _ _ (by omega)]; exact append_extract_lo _ _
@[simp] theorem getFunct3_encodeR (f7 : BitVec 7) (rs2 rs1 : Reg) (f3 : BitVec 3)
    (rd : Reg) (opc : BitVec 7) :
    getFunct3 (encodeR f7 rs2 rs1 f3 rd opc) = f3 := by
  unfold getFunct3 encodeR
  rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega)]
  exact append_extract_lo _ _
@[simp] theorem getRs1_encodeR (f7 : BitVec 7) (rs2 rs1 : Reg) (f3 : BitVec 3)
    (rd : Reg) (opc : BitVec 7) :
    getRs1 (encodeR f7 rs2 rs1 f3 rd opc) = rs1 := by
  unfold getRs1 encodeR
  rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
      append_extract_hi _ _ (by omega)]
  exact append_extract_lo _ _
@[simp] theorem getRs2_encodeR (f7 : BitVec 7) (rs2 rs1 : Reg) (f3 : BitVec 3)
    (rd : Reg) (opc : BitVec 7) :
    getRs2 (encodeR f7 rs2 rs1 f3 rd opc) = rs2 := by
  unfold getRs2 encodeR
  rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
      append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega)]
  exact append_extract_lo _ _
@[simp] theorem getFunct7_encodeR (f7 : BitVec 7) (rs2 rs1 : Reg) (f3 : BitVec 3)
    (rd : Reg) (opc : BitVec 7) :
    getFunct7 (encodeR f7 rs2 rs1 f3 rd opc) = f7 := by
  unfold getFunct7 encodeR
  rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
      append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
      append_extract_hi _ _ (by omega)]
  exact extract_self _

@[simp] theorem getOpcode_encodeI (imm : BitVec 12) (rs1 : Reg) (f3 : BitVec 3)
    (rd : Reg) (opc : BitVec 7) :
    getOpcode (encodeI imm rs1 f3 rd opc) = opc := append_extract_lo _ _
@[simp] theorem getRd_encodeI (imm : BitVec 12) (rs1 : Reg) (f3 : BitVec 3)
    (rd : Reg) (opc : BitVec 7) :
    getRd (encodeI imm rs1 f3 rd opc) = rd := by
  unfold getRd encodeI; rw [append_extract_hi _ _ (by omega)]; exact append_extract_lo _ _
@[simp] theorem getFunct3_encodeI (imm : BitVec 12) (rs1 : Reg) (f3 : BitVec 3)
    (rd : Reg) (opc : BitVec 7) :
    getFunct3 (encodeI imm rs1 f3 rd opc) = f3 := by
  unfold getFunct3 encodeI
  rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega)]
  exact append_extract_lo _ _
@[simp] theorem getRs1_encodeI (imm : BitVec 12) (rs1 : Reg) (f3 : BitVec 3)
    (rd : Reg) (opc : BitVec 7) :
    getRs1 (encodeI imm rs1 f3 rd opc) = rs1 := by
  unfold getRs1 encodeI
  rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
      append_extract_hi _ _ (by omega)]
  exact append_extract_lo _ _
@[simp] theorem getImmI_encodeI (imm : BitVec 12) (rs1 : Reg) (f3 : BitVec 3)
    (rd : Reg) (opc : BitVec 7) :
    getImmI (encodeI imm rs1 f3 rd opc) = imm := by
  unfold getImmI encodeI
  rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
      append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega)]
  exact extract_self _
@[simp] theorem getFunct6_encodeI (f6 sh : BitVec 6) (rs1 : Reg) (f3 : BitVec 3)
    (rd : Reg) (opc : BitVec 7) :
    getFunct6 (encodeI (f6 ++ sh) rs1 f3 rd opc) = f6 := by
  unfold getFunct6 encodeI
  rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
      append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
      append_extract_hi _ _ (by omega)]
  exact extract_self _
@[simp] theorem getShamt6_encodeI (f6 sh : BitVec 6) (rs1 : Reg) (f3 : BitVec 3)
    (rd : Reg) (opc : BitVec 7) :
    getShamt6 (encodeI (f6 ++ sh) rs1 f3 rd opc) = sh := by
  unfold getShamt6 encodeI
  rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
      append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega)]
  exact append_extract_lo _ _

@[simp] theorem getOpcode_encodeS (imm : BitVec 12) (rs2 rs1 : Reg) (f3 : BitVec 3)
    (opc : BitVec 7) :
    getOpcode (encodeS imm rs2 rs1 f3 opc) = opc := append_extract_lo _ _
@[simp] theorem getFunct3_encodeS (imm : BitVec 12) (rs2 rs1 : Reg) (f3 : BitVec 3)
    (opc : BitVec 7) :
    getFunct3 (encodeS imm rs2 rs1 f3 opc) = f3 := by
  unfold getFunct3 encodeS
  rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega)]
  exact append_extract_lo _ _
@[simp] theorem getRs1_encodeS (imm : BitVec 12) (rs2 rs1 : Reg) (f3 : BitVec 3)
    (opc : BitVec 7) :
    getRs1 (encodeS imm rs2 rs1 f3 opc) = rs1 := by
  unfold getRs1 encodeS
  rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
      append_extract_hi _ _ (by omega)]
  exact append_extract_lo _ _
@[simp] theorem getRs2_encodeS (imm : BitVec 12) (rs2 rs1 : Reg) (f3 : BitVec 3)
    (opc : BitVec 7) :
    getRs2 (encodeS imm rs2 rs1 f3 opc) = rs2 := by
  unfold getRs2 encodeS
  rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
      append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega)]
  exact append_extract_lo _ _
@[simp] theorem getImmS_encodeS (imm : BitVec 12) (rs2 rs1 : Reg) (f3 : BitVec 3)
    (opc : BitVec 7) :
    getImmS (encodeS imm rs2 rs1 f3 opc) = imm := by
  unfold getImmS encodeS
  dsimp only
  have h1 : (imm.extractLsb' 5 7 ++ rs2 ++ rs1 ++ f3 ++ imm.extractLsb' 0 5 ++ opc).extractLsb' 25 7 =
      imm.extractLsb' 5 7 := by
    rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
        append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
        append_extract_hi _ _ (by omega)]
    exact extract_self _
  have h2 : (imm.extractLsb' 5 7 ++ rs2 ++ rs1 ++ f3 ++ imm.extractLsb' 0 5 ++ opc).extractLsb' 7 5 =
      imm.extractLsb' 0 5 := by
    rw [append_extract_hi _ _ (by omega)]
    exact append_extract_lo _ _
  rw [h1, h2]
  bit_eq

@[simp] theorem getOpcode_encodeB (bimm : BitVec 12) (rs2 rs1 : Reg) (f3 : BitVec 3)
    (opc : BitVec 7) :
    getOpcode (encodeB bimm rs2 rs1 f3 opc) = opc := append_extract_lo _ _
@[simp] theorem getFunct3_encodeB (bimm : BitVec 12) (rs2 rs1 : Reg) (f3 : BitVec 3)
    (opc : BitVec 7) :
    getFunct3 (encodeB bimm rs2 rs1 f3 opc) = f3 := by
  unfold getFunct3 encodeB
  dsimp only
  rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
      append_extract_hi _ _ (by omega)]
  exact append_extract_lo _ _
@[simp] theorem getRs1_encodeB (bimm : BitVec 12) (rs2 rs1 : Reg) (f3 : BitVec 3)
    (opc : BitVec 7) :
    getRs1 (encodeB bimm rs2 rs1 f3 opc) = rs1 := by
  unfold getRs1 encodeB
  dsimp only
  rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
      append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega)]
  exact append_extract_lo _ _
@[simp] theorem getRs2_encodeB (bimm : BitVec 12) (rs2 rs1 : Reg) (f3 : BitVec 3)
    (opc : BitVec 7) :
    getRs2 (encodeB bimm rs2 rs1 f3 opc) = rs2 := by
  unfold getRs2 encodeB
  dsimp only
  rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
      append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
      append_extract_hi _ _ (by omega)]
  exact append_extract_lo _ _
@[simp] theorem getImmB_encodeB (bimm : BitVec 12) (rs2 rs1 : Reg) (f3 : BitVec 3)
    (opc : BitVec 7) :
    getImmB (encodeB bimm rs2 rs1 f3 opc) = bimm := by
  unfold getImmB encodeB
  dsimp only
  have h31 : (bimm.extractLsb' 11 1 ++ bimm.extractLsb' 4 6 ++ rs2 ++ rs1 ++ f3 ++
      bimm.extractLsb' 0 4 ++ bimm.extractLsb' 10 1 ++ opc).extractLsb' 31 1 =
      bimm.extractLsb' 11 1 := by
    rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
        append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
        append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
        append_extract_hi _ _ (by omega)]
    exact extract_self _
  have h7 : (bimm.extractLsb' 11 1 ++ bimm.extractLsb' 4 6 ++ rs2 ++ rs1 ++ f3 ++
      bimm.extractLsb' 0 4 ++ bimm.extractLsb' 10 1 ++ opc).extractLsb' 7 1 =
      bimm.extractLsb' 10 1 := by
    rw [append_extract_hi _ _ (by omega)]
    exact append_extract_lo _ _
  have h25 : (bimm.extractLsb' 11 1 ++ bimm.extractLsb' 4 6 ++ rs2 ++ rs1 ++ f3 ++
      bimm.extractLsb' 0 4 ++ bimm.extractLsb' 10 1 ++ opc).extractLsb' 25 6 =
      bimm.extractLsb' 4 6 := by
    rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
        append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
        append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega)]
    exact append_extract_lo _ _
  have h8 : (bimm.extractLsb' 11 1 ++ bimm.extractLsb' 4 6 ++ rs2 ++ rs1 ++ f3 ++
      bimm.extractLsb' 0 4 ++ bimm.extractLsb' 10 1 ++ opc).extractLsb' 8 4 =
      bimm.extractLsb' 0 4 := by
    rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega)]
    exact append_extract_lo _ _
  rw [h31, h7, h25, h8]
  bit_eq

@[simp] theorem getOpcode_encodeU (imm : BitVec 20) (rd : Reg) (opc : BitVec 7) :
    getOpcode (encodeU imm rd opc) = opc := append_extract_lo _ _
@[simp] theorem getRd_encodeU (imm : BitVec 20) (rd : Reg) (opc : BitVec 7) :
    getRd (encodeU imm rd opc) = rd := by
  unfold getRd encodeU; rw [append_extract_hi _ _ (by omega)]; exact append_extract_lo _ _
@[simp] theorem getImmU_encodeU (imm : BitVec 20) (rd : Reg) (opc : BitVec 7) :
    getImmU (encodeU imm rd opc) = imm := by
  unfold getImmU encodeU
  rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega)]; exact extract_self _

@[simp] theorem getOpcode_encodeJ (jimm : BitVec 20) (rd : Reg) (opc : BitVec 7) :
    getOpcode (encodeJ jimm rd opc) = opc := append_extract_lo _ _
@[simp] theorem getRd_encodeJ (jimm : BitVec 20) (rd : Reg) (opc : BitVec 7) :
    getRd (encodeJ jimm rd opc) = rd := by
  unfold getRd encodeJ; dsimp only
  rw [append_extract_hi _ _ (by omega)]; exact append_extract_lo _ _
@[simp] theorem getImmJ_encodeJ (jimm : BitVec 20) (rd : Reg) (opc : BitVec 7) :
    getImmJ (encodeJ jimm rd opc) = jimm := by
  unfold getImmJ encodeJ
  dsimp only
  have h31 : (jimm.extractLsb' 19 1 ++ jimm.extractLsb' 0 10 ++ jimm.extractLsb' 10 1 ++
      jimm.extractLsb' 11 8 ++ rd ++ opc).extractLsb' 31 1 = jimm.extractLsb' 19 1 := by
    rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
        append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
        append_extract_hi _ _ (by omega)]
    exact extract_self _
  have h12 : (jimm.extractLsb' 19 1 ++ jimm.extractLsb' 0 10 ++ jimm.extractLsb' 10 1 ++
      jimm.extractLsb' 11 8 ++ rd ++ opc).extractLsb' 12 8 = jimm.extractLsb' 11 8 := by
    rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega)]
    exact append_extract_lo _ _
  have h20 : (jimm.extractLsb' 19 1 ++ jimm.extractLsb' 0 10 ++ jimm.extractLsb' 10 1 ++
      jimm.extractLsb' 11 8 ++ rd ++ opc).extractLsb' 20 1 = jimm.extractLsb' 10 1 := by
    rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
        append_extract_hi _ _ (by omega)]
    exact append_extract_lo _ _
  have h21 : (jimm.extractLsb' 19 1 ++ jimm.extractLsb' 0 10 ++ jimm.extractLsb' 10 1 ++
      jimm.extractLsb' 11 8 ++ rd ++ opc).extractLsb' 21 10 = jimm.extractLsb' 0 10 := by
    rw [append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega),
        append_extract_hi _ _ (by omega), append_extract_hi _ _ (by omega)]
    exact append_extract_lo _ _
  rw [h31, h12, h20, h21]
  bit_eq

/-! ## Word Reconstruction From Extracted Fields (`encode* (get* w) = w`) -/

private theorem encodeR_get (w : BitVec 32) :
    encodeR (getFunct7 w) (getRs2 w) (getRs1 w) (getFunct3 w) (getRd w) (getOpcode w) = w := by
  unfold encodeR getFunct7 getRs2 getRs1 getFunct3 getRd getOpcode; bit_eq

private theorem encodeI_get (w : BitVec 32) :
    encodeI (getImmI w) (getRs1 w) (getFunct3 w) (getRd w) (getOpcode w) = w := by
  unfold encodeI getImmI getRs1 getFunct3 getRd getOpcode; bit_eq

private theorem encodeI_sh_get (w : BitVec 32) :
    encodeI (getFunct6 w ++ getShamt6 w) (getRs1 w) (getFunct3 w) (getRd w) (getOpcode w) = w := by
  unfold encodeI getFunct6 getShamt6 getRs1 getFunct3 getRd getOpcode; bit_eq

private theorem encodeS_get (w : BitVec 32) :
    encodeS (getImmS w) (getRs2 w) (getRs1 w) (getFunct3 w) (getOpcode w) = w := by
  unfold encodeS getImmS getRs2 getRs1 getFunct3 getOpcode; dsimp only; bit_eq

private theorem encodeB_get (w : BitVec 32) :
    encodeB (getImmB w) (getRs2 w) (getRs1 w) (getFunct3 w) (getOpcode w) = w := by
  unfold encodeB getImmB getRs2 getRs1 getFunct3 getOpcode; dsimp only; bit_eq

private theorem encodeU_get (w : BitVec 32) :
    encodeU (getImmU w) (getRd w) (getOpcode w) = w := by
  unfold encodeU getImmU getRd getOpcode; bit_eq

private theorem encodeJ_get (w : BitVec 32) :
    encodeJ (getImmJ w) (getRd w) (getOpcode w) = w := by
  unfold encodeJ getImmJ getRd getOpcode; dsimp only; bit_eq

/-! ## Main Bijection Theorems -/

/-- Every `Instr` round-trips identically through `encode` and `decode`. -/
theorem decode_encode (inst : Instr) : decode (encode inst) = some inst := by
  cases inst with
  | lui rd imm20 =>
    simp [encode, decode]
  | jal rd jimm =>
    simp [encode, decode, Opcode.jal, Opcode.lui]
  | jalr rd rs1 imm12 =>
    simp [encode, decode, Opcode.jalr, Opcode.jal, Opcode.lui]
  | branch op rs1 rs2 bimm =>
    cases op <;> simp [encode, decode, BranchOp.funct3,
      Opcode.branch, Opcode.jalr, Opcode.jal, Opcode.lui]
  | load op rd rs1 imm12 =>
    cases op <;> simp [encode, decode, LoadOp.funct3,
      Opcode.load, Opcode.branch, Opcode.jalr, Opcode.jal, Opcode.lui]
  | store op rs1 rs2 imm12 =>
    cases op <;> simp [encode, decode, StoreOp.funct3,
      Opcode.store, Opcode.load, Opcode.branch, Opcode.jalr, Opcode.jal, Opcode.lui]
  | aluImm op rd rs1 imm12 =>
    cases op <;> simp [encode, decode, AluImmOp.funct3,
      Opcode.opImm, Opcode.store, Opcode.load, Opcode.branch,
      Opcode.jalr, Opcode.jal, Opcode.lui]
  | shImm op rd rs1 shamt =>
    cases op <;> simp [encode, decode, ShiftImmOp.funct3, ShiftImmOp.funct6,
      Opcode.opImm, Opcode.store, Opcode.load, Opcode.branch,
      Opcode.jalr, Opcode.jal, Opcode.lui]
  | alu op rd rs1 rs2 =>
    cases op <;> simp [encode, decode, AluOp.funct3, AluOp.funct7,
      Opcode.op, Opcode.opImm, Opcode.store, Opcode.load, Opcode.branch,
      Opcode.jalr, Opcode.jal, Opcode.lui]

/-- Converse roundtrip: if `decode w = some inst`, then `encode inst = w`.
    Establishes that `decode` checks every bit of `w` and admits no alias encodings. -/
theorem encode_decode {w : BitVec 32} {inst : Instr} (h : decode w = some inst) :
    encode inst = w := by
  dsimp only [decode] at h
  by_cases h1 : (getOpcode w == Opcode.lui) = true
  · simp only [h1, ↓reduceIte, Option.some.injEq] at h
    subst h; rw [beq_iff_eq] at h1
    dsimp only [encode]; rw [← h1]; exact encodeU_get w
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    by_cases h2 : (getOpcode w == Opcode.jal) = true
    · simp only [h2, ↓reduceIte, Option.some.injEq] at h
      subst h; rw [beq_iff_eq] at h2
      dsimp only [encode]; rw [← h2]; exact encodeJ_get w
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
      by_cases h3 : (getOpcode w == Opcode.jalr) = true
      · simp only [h3, ↓reduceIte] at h
        by_cases hf3 : (getFunct3 w == 0b000#3) = true
        · simp only [hf3, ↓reduceIte, Option.some.injEq] at h
          subst h; rw [beq_iff_eq] at h3 hf3
          dsimp only [encode]; rw [← h3, ← hf3]; exact encodeI_get w
        · simp only [hf3, Bool.false_eq_true, ↓reduceIte] at h; cases h
      · simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h4 : (getOpcode w == Opcode.branch) = true
        · simp only [h4, ↓reduceIte] at h
          rw [beq_iff_eq] at h4
          split at h <;> first
            | (cases h; done)
            | (rename_i _ hf3; injection h with hi; subst hi;
               dsimp only [encode, BranchOp.funct3]; rw [← h4, ← hf3]; exact encodeB_get w)
        · simp only [h4, Bool.false_eq_true, ↓reduceIte] at h
          by_cases h5 : (getOpcode w == Opcode.load) = true
          · simp only [h5, ↓reduceIte] at h
            rw [beq_iff_eq] at h5
            split at h <;> first
              | (cases h; done)
              | (rename_i _ hf3; injection h with hi; subst hi;
                 dsimp only [encode, LoadOp.funct3]; rw [← h5, ← hf3]; exact encodeI_get w)
          · simp only [h5, Bool.false_eq_true, ↓reduceIte] at h
            by_cases h6 : (getOpcode w == Opcode.store) = true
            · simp only [h6, ↓reduceIte] at h
              rw [beq_iff_eq] at h6
              split at h <;> first
                | (cases h; done)
                | (rename_i _ hf3; injection h with hi; subst hi;
                   dsimp only [encode, StoreOp.funct3]; rw [← h6, ← hf3]; exact encodeS_get w)
            · simp only [h6, Bool.false_eq_true, ↓reduceIte] at h
              by_cases h7 : (getOpcode w == Opcode.opImm) = true
              · simp only [h7, ↓reduceIte] at h
                rw [beq_iff_eq] at h7
                split at h <;> first
                  | (cases h; done)
                  | (rename_i _ hf3; injection h with hi; subst hi;
                     dsimp only [encode, AluImmOp.funct3]; rw [← h7, ← hf3]; exact encodeI_get w)
                  | (rename_i _ hf3;
                     by_cases hf6 : (getFunct6 w == 0b000000#6) = true
                     · simp only [hf6, ↓reduceIte, Option.some.injEq] at h
                       subst h; rw [beq_iff_eq] at hf6
                       dsimp only [encode, ShiftImmOp.funct3, ShiftImmOp.funct6]
                       rw [← h7, ← hf3, ← hf6]; exact encodeI_sh_get w
                     · simp only [hf6, Bool.false_eq_true, ↓reduceIte] at h; cases h)
              · simp only [h7, Bool.false_eq_true, ↓reduceIte] at h
                by_cases h8 : (getOpcode w == Opcode.op) = true
                · simp only [h8, ↓reduceIte] at h
                  rw [beq_iff_eq] at h8
                  by_cases hf7a : (getFunct7 w == 0b0000000#7) = true
                  · simp only [hf7a, ↓reduceIte] at h; rw [beq_iff_eq] at hf7a
                    split at h <;> first
                      | (cases h; done)
                      | (rename_i _ hf3; injection h with hi; subst hi;
                         dsimp only [encode, AluOp.funct3, AluOp.funct7]
                         rw [← h8, ← hf7a, ← hf3]; exact encodeR_get w)
                  · simp only [hf7a, Bool.false_eq_true, ↓reduceIte] at h
                    by_cases hf7b : (getFunct7 w == 0b0100000#7) = true
                    · simp only [hf7b, ↓reduceIte] at h; rw [beq_iff_eq] at hf7b
                      split at h <;> first
                        | (cases h; done)
                        | (rename_i _ hf3; injection h with hi; subst hi;
                           dsimp only [encode, AluOp.funct3, AluOp.funct7]
                           rw [← h8, ← hf7b, ← hf3]; exact encodeR_get w)
                    · simp only [hf7b, Bool.false_eq_true, ↓reduceIte] at h
                      by_cases hf7c : (getFunct7 w == 0b0000001#7) = true
                      · simp only [hf7c, ↓reduceIte] at h; rw [beq_iff_eq] at hf7c
                        split at h <;> first
                          | (cases h; done)
                          | (rename_i _ hf3; injection h with hi; subst hi;
                             dsimp only [encode, AluOp.funct3, AluOp.funct7]
                             rw [← h8, ← hf7c, ← hf3]; exact encodeR_get w)
                      · simp only [hf7c, Bool.false_eq_true, ↓reduceIte] at h; cases h
                · simp only [h8, Bool.false_eq_true, ↓reduceIte] at h; cases h

/-- Exact characterization: `w` decodes to `inst` iff `w` is the canonical encoding of `inst`. -/
theorem decode_eq_some_iff (w : BitVec 32) (inst : Instr) :
    decode w = some inst ↔ encode inst = w :=
  ⟨encode_decode, fun h => h ▸ decode_encode inst⟩

/-- Encoding is injective on `Instr`. -/
theorem encode_injective {a b : Instr} (h : encode a = encode b) : a = b := by
  have := congrArg decode h
  rw [decode_encode, decode_encode] at this
  injection this

/-- info: 'ConAgua.RISCV.RV64.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decode_encode

/-- info: 'ConAgua.RISCV.RV64.encode_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms encode_decode

end ConAgua.RISCV.RV64
