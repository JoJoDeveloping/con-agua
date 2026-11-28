import ConAgua.RISCV.RV64.Syntax

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RV64 32-Bit Binary Encoder (`ConAgua.RISCV.RV64.Encode`)

**Outside the TCB:** `Semantics.step` executes raw `BitVec 32` words via `Decode.decode`, so
soundness does not depend on `encode`. `Roundtrip.lean` proves `encode` and `decode` are
exact mutual inverses (`decode (encode inst) = some inst` and `decode w = some inst → encode inst = w`).

Because we emit raw `BitVec 32` words inside Lean (`.word 0x...` in `riscv/checker.s`),
no external assembler mnemonic parser sits inside the trusted computing base.

In Lean's `BitVec`, `a ++ b` places `a` in the more-significant bits and `b` in the
less-significant bits, and `x.extractLsb' lo len` extracts `x[lo + len - 1 : lo]`.
-/

namespace ConAgua.RISCV.RV64

/-! ## Format Packers (§2.2, §2.3; MSB on left, LSB on right; widths sum to 32) -/

/-- R-type (§2.2): `funct7[31:25] | rs2[24:20] | rs1[19:15] | funct3[14:12] | rd[11:7] | opcode[6:0]`. -/
def encodeR (funct7 : BitVec 7) (rs2 rs1 : Reg) (funct3 : BitVec 3)
    (rd : Reg) (opcode : BitVec 7) : BitVec 32 :=
  funct7 ++ rs2 ++ rs1 ++ funct3 ++ rd ++ opcode

/-- I-type (§2.2): `imm[31:20] | rs1[19:15] | funct3[14:12] | rd[11:7] | opcode[6:0]`. -/
def encodeI (imm12 : BitVec 12) (rs1 : Reg) (funct3 : BitVec 3)
    (rd : Reg) (opcode : BitVec 7) : BitVec 32 :=
  imm12 ++ rs1 ++ funct3 ++ rd ++ opcode

/-- S-type (§2.2): `imm[11:5] | rs2 | rs1 | funct3 | imm[4:0] | opcode`. -/
def encodeS (imm12 : BitVec 12) (rs2 rs1 : Reg) (funct3 : BitVec 3)
    (opcode : BitVec 7) : BitVec 32 :=
  let hi : BitVec 7 := imm12.extractLsb' 5 7  -- imm[11:5] → w[31:25]
  let lo : BitVec 5 := imm12.extractLsb' 0 5  -- imm[4:0]  → w[11:7]
  hi ++ rs2 ++ rs1 ++ funct3 ++ lo ++ opcode

/-- B-type (§2.3): `imm[12] | imm[10:5] | rs2 | rs1 | funct3 | imm[4:1] | imm[11] | opcode`.
    `bimm : BitVec 12` holds signed offset bits `[12:1]`, so `bimm[k]` is architectural `imm[k + 1]`. -/
def encodeB (bimm : BitVec 12) (rs2 rs1 : Reg) (funct3 : BitVec 3)
    (opcode : BitVec 7) : BitVec 32 :=
  let b12   : BitVec 1 := bimm.extractLsb' 11 1  -- imm[12]   → w[31]
  let b11   : BitVec 1 := bimm.extractLsb' 10 1  -- imm[11]   → w[7]
  let b10_5 : BitVec 6 := bimm.extractLsb' 4 6   -- imm[10:5] → w[30:25]
  let b4_1  : BitVec 4 := bimm.extractLsb' 0 4   -- imm[4:1]  → w[11:8]
  b12 ++ b10_5 ++ rs2 ++ rs1 ++ funct3 ++ b4_1 ++ b11 ++ opcode

/-- U-type (§2.2): `imm[31:12] | rd[11:7] | opcode[6:0]`. -/
def encodeU (imm20 : BitVec 20) (rd : Reg) (opcode : BitVec 7) : BitVec 32 :=
  imm20 ++ rd ++ opcode

/-- J-type (§2.3): `imm[20] | imm[10:1] | imm[11] | imm[19:12] | rd | opcode`.
    `jimm : BitVec 20` holds signed offset bits `[20:1]`, so `jimm[k]` is architectural `imm[k + 1]`. -/
def encodeJ (jimm : BitVec 20) (rd : Reg) (opcode : BitVec 7) : BitVec 32 :=
  let b20    : BitVec 1  := jimm.extractLsb' 19 1  -- imm[20]    → w[31]
  let b19_12 : BitVec 8  := jimm.extractLsb' 11 8  -- imm[19:12] → w[19:12]
  let b11    : BitVec 1  := jimm.extractLsb' 10 1  -- imm[11]    → w[20]
  let b10_1  : BitVec 10 := jimm.extractLsb' 0 10  -- imm[10:1]  → w[30:21]
  b20 ++ b10_1 ++ b11 ++ b19_12 ++ rd ++ opcode

/-! ## Sub-Opcode Tables (`funct3`, `funct6`, `funct7`, Ch. 36 Listing Order pp. 585-588) -/

def BranchOp.funct3 : BranchOp → BitVec 3
  | .beq  => 0b000#3
  | .bne  => 0b001#3
  | .blt  => 0b100#3
  | .bge  => 0b101#3
  | .bltu => 0b110#3
  | .bgeu => 0b111#3

def LoadOp.funct3 : LoadOp → BitVec 3
  | .lbu => 0b100#3
  | .lwu => 0b110#3
  | .ld  => 0b011#3

def StoreOp.funct3 : StoreOp → BitVec 3
  | .sw => 0b010#3
  | .sd => 0b011#3

def AluImmOp.funct3 : AluImmOp → BitVec 3
  | .addi  => 0b000#3
  | .slti  => 0b010#3
  | .sltiu => 0b011#3
  | .xori  => 0b100#3
  | .ori   => 0b110#3
  | .andi  => 0b111#3

def ShiftImmOp.funct6 : ShiftImmOp → BitVec 6
  | .slli => 0b000000#6
  | .srli => 0b000000#6

def ShiftImmOp.funct3 : ShiftImmOp → BitVec 3
  | .slli => 0b001#3
  | .srli => 0b101#3

def AluOp.funct7 : AluOp → BitVec 7
  | .sub          => 0b0100000#7
  | .mul | .mulhu => 0b0000001#7
  | _             => 0b0000000#7

def AluOp.funct3 : AluOp → BitVec 3
  | .add    => 0b000#3
  | .sub    => 0b000#3
  | .sll    => 0b001#3
  | .slt    => 0b010#3
  | .sltu   => 0b011#3
  | .xor    => 0b100#3
  | .srl    => 0b101#3
  | .or     => 0b110#3
  | .and    => 0b111#3
  | .mul    => 0b000#3
  | .mulhu  => 0b011#3

/-! ## Total Instruction Encoder -/

/-- Encode an RV64 instruction into its canonical 32-bit machine word (no preconditions),
    ordered to follow the Chapter 36 Instruction Set Listings (spec pp. 585-588, PDF pp. 604ff). -/
def encode : Instr → BitVec 32
  | .lui rd imm20          => encodeU imm20 rd Opcode.lui
  | .jal rd jimm           => encodeJ jimm rd Opcode.jal
  | .jalr rd rs1 imm12     => encodeI imm12 rs1 0b000#3 rd Opcode.jalr
  | .branch op rs1 rs2 imm => encodeB imm rs2 rs1 op.funct3 Opcode.branch
  | .load op rd rs1 imm    => encodeI imm rs1 op.funct3 rd Opcode.load
  | .store op rs1 rs2 imm  => encodeS imm rs2 rs1 op.funct3 Opcode.store
  | .aluImm op rd rs1 imm  => encodeI imm rs1 op.funct3 rd Opcode.opImm
  | .shImm op rd rs1 shamt => encodeI (op.funct6 ++ shamt) rs1 op.funct3 rd Opcode.opImm
  | .alu op rd rs1 rs2     => encodeR op.funct7 rs2 rs1 op.funct3 rd Opcode.op

end ConAgua.RISCV.RV64
