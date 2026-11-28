import ConAgua.RISCV.RV64.Syntax

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RV64 32-Bit Binary Decoder (`ConAgua.RISCV.RV64.Decode`)

**Trusted Computing Base (2 of 3):** Imports only `Syntax.lean` (zero proofs, zero external
dependencies). Maps every raw 32-bit machine word `w : BitVec 32` to `Option Instr` with
no preconditions. Any illegal, reserved, or out-of-subset bit pattern returns `none`, which
`Semantics.step` turns into `.trap`.

## Bit-Extraction Convention

In Lean's `BitVec`, `w.extractLsb' lo len` extracts `len` bits starting at LSB index `lo`,
corresponding to `w[lo + len - 1 : lo]` in the RISC-V Unprivileged ISA Specification.
Concatenation `a ++ b` places `a` in the more-significant bits and `b` in the less-significant bits.

## RISC-V 32-Bit Instruction Formats (ISA Spec §§2.2, 2.3, 4.2.1)

```
 31          25 24   20 19   15 14    12 11         7 6      0
+--------------+-------+-------+--------+------------+--------+
|    funct7    |  rs2  |  rs1  | funct3 |     rd     | opcode |  R-type (§2.2)
+--------------+-------+-------+--------+------------+--------+
|      imm[11:0]       |  rs1  | funct3 |     rd     | opcode |  I-type (§2.2)
+------------+---------+-------+--------+------------+--------+
|   funct6   | shamt6  |  rs1  | funct3 |     rd     | opcode |  I-type (RV64 shifts, §4.2.1)
+------------+---------+-------+--------+------------+--------+
|   imm[11:5]  |  rs2  |  rs1  | funct3 |  imm[4:0]  | opcode |  S-type (§2.2)
+-+------------+-------+-------+--------+----------+-+--------+
|a| imm[10:5]  |  rs2  |  rs1  | funct3 | imm[4:1] |b| opcode |  B-type (§2.3: a = imm[12], b = imm[11])
+-+------------+-------+-------+--------+----------+-+--------+
|              imm[31:12]               |     rd     | opcode |  U-type (§2.2)
+-+--------------------+--+-------------+------------+--------+
|c|     imm[10:1]      |d | imm[19:12]  |     rd     | opcode |  J-type (§2.3: c = imm[20], d = imm[11])
+-+--------------------+--+-------------+------------+--------+
```

`Roundtrip.lean` proves both `decode (encode inst) = some inst` and the converse
`decode w = some inst → encode inst = w`, confirming that `decode` leaves zero bits
unchecked and admits no alias encodings.
-/

namespace ConAgua.RISCV.RV64

/-! ## Fixed-Position Bit-Field Extractors -/

def getOpcode (w : BitVec 32) : BitVec 7 := w.extractLsb' 0 7   -- w[6:0]
def getRd     (w : BitVec 32) : Reg      := w.extractLsb' 7 5   -- w[11:7]
def getFunct3 (w : BitVec 32) : BitVec 3 := w.extractLsb' 12 3  -- w[14:12]
def getRs1    (w : BitVec 32) : Reg      := w.extractLsb' 15 5  -- w[19:15]
def getRs2    (w : BitVec 32) : Reg      := w.extractLsb' 20 5  -- w[24:20]
def getShamt6 (w : BitVec 32) : BitVec 6 := w.extractLsb' 20 6  -- w[25:20] (RV64 shift-imm)
def getFunct7 (w : BitVec 32) : BitVec 7 := w.extractLsb' 25 7  -- w[31:25]
def getFunct6 (w : BitVec 32) : BitVec 6 := w.extractLsb' 26 6  -- w[31:26] (RV64 shift-imm)

/-! ## Immediate Reassembly (§2.3 Figure 1; `BitVec` widths omit implicit zero LSBs) -/

/-- I-type `imm[11:0]` = `w[31:20]`. -/
def getImmI (w : BitVec 32) : BitVec 12 := w.extractLsb' 20 12

/-- S-type `imm[11:0]` = `w[31:25] ++ w[11:7]`. -/
def getImmS (w : BitVec 32) : BitVec 12 :=
  w.extractLsb' 25 7 ++ w.extractLsb' 7 5

/-- B-type `imm[12:1]` = `w[31] ++ w[7] ++ w[30:25] ++ w[11:8]` (implicit `imm[0] = 0`). -/
def getImmB (w : BitVec 32) : BitVec 12 :=
  w.extractLsb' 31 1 ++ w.extractLsb' 7 1 ++ w.extractLsb' 25 6 ++ w.extractLsb' 8 4

/-- U-type `imm[31:12]` = `w[31:12]` (implicit `imm[11:0] = 0`). -/
def getImmU (w : BitVec 32) : BitVec 20 := w.extractLsb' 12 20

/-- J-type `imm[20:1]` = `w[31] ++ w[19:12] ++ w[20] ++ w[30:21]` (implicit `imm[0] = 0`). -/
def getImmJ (w : BitVec 32) : BitVec 20 :=
  w.extractLsb' 31 1 ++ w.extractLsb' 12 8 ++ w.extractLsb' 20 1 ++ w.extractLsb' 21 10

/-! ## Total Instruction Decoder -/

/-- Decode a raw 32-bit little-endian RISC-V instruction word into `Option Instr`,
    ordered to follow the Chapter 36 Instruction Set Listings (spec pp. 585-588, PDF pp. 604ff).
    Returns `none` for every encoding outside our 33-instruction RV64 subset, including
    `AUIPC`, nonzero `funct3` on `JALR`, branch `funct3 ∈ {010, 011}`,
    signed/subword loads (`LB`/`LH`/`LW`/`LHU`), byte/halfword stores (`SB`/`SH`),
    nonzero `funct6` on `SLLI`/`SRLI` (rejecting `SRAI`), and unimplemented `OP`
    `funct7`/`funct3` pairs. -/
def decode (w : BitVec 32) : Option Instr :=
  let opc := getOpcode w
  let rd  := getRd w
  let f3  := getFunct3 w
  let rs1 := getRs1 w
  let rs2 := getRs2 w
  let f7  := getFunct7 w
  if opc == Opcode.lui then
    some (.lui rd (getImmU w))
  else if opc == Opcode.jal then
    some (.jal rd (getImmJ w))
  else if opc == Opcode.jalr then
    -- RV64I requires funct3 = 000 for JALR; all other funct3 values are reserved/illegal.
    if f3 == 0b000#3 then some (.jalr rd rs1 (getImmI w)) else none
  else if opc == Opcode.branch then
    let bimm := getImmB w
    match f3 with
    | 0b000#3 => some (.branch .beq  rs1 rs2 bimm)
    | 0b001#3 => some (.branch .bne  rs1 rs2 bimm)
    | 0b100#3 => some (.branch .blt  rs1 rs2 bimm)
    | 0b101#3 => some (.branch .bge  rs1 rs2 bimm)
    | 0b110#3 => some (.branch .bltu rs1 rs2 bimm)
    | 0b111#3 => some (.branch .bgeu rs1 rs2 bimm)
    | _       => none
  else if opc == Opcode.load then
    let imm := getImmI w
    match f3 with
    | 0b100#3 => some (.load .lbu rd rs1 imm)  -- RV32I listing (p. 585)
    | 0b110#3 => some (.load .lwu rd rs1 imm)  -- RV64I listing (p. 587)
    | 0b011#3 => some (.load .ld  rd rs1 imm)  -- RV64I listing (p. 587)
    | _       => none
  else if opc == Opcode.store then
    let imm := getImmS w
    match f3 with
    | 0b010#3 => some (.store .sw rs1 rs2 imm)  -- RV32I listing (p. 585)
    | 0b011#3 => some (.store .sd rs1 rs2 imm)  -- RV64I listing (p. 587)
    | _       => none
  else if opc == Opcode.opImm then
    let imm := getImmI w
    let f6  := getFunct6 w
    let sh  := getShamt6 w
    match f3 with
    | 0b000#3 => some (.aluImm .addi  rd rs1 imm)
    | 0b010#3 => some (.aluImm .slti  rd rs1 imm)
    | 0b011#3 => some (.aluImm .sltiu rd rs1 imm)
    | 0b100#3 => some (.aluImm .xori  rd rs1 imm)
    | 0b110#3 => some (.aluImm .ori   rd rs1 imm)
    | 0b111#3 => some (.aluImm .andi  rd rs1 imm)
    -- RV64I shift-immediate uses 6-bit shamt = w[25:20] and 6-bit funct6 = w[31:26] = 000000.
    | 0b001#3 => if f6 == 0b000000#6 then some (.shImm .slli rd rs1 sh) else none
    | 0b101#3 => if f6 == 0b000000#6 then some (.shImm .srli rd rs1 sh) else none
    | _ => none
  else if opc == Opcode.op then
    if f7 == 0b0000000#7 then
      match f3 with
      | 0b000#3 => some (.alu .add  rd rs1 rs2)
      | 0b001#3 => some (.alu .sll  rd rs1 rs2)
      | 0b010#3 => some (.alu .slt  rd rs1 rs2)
      | 0b011#3 => some (.alu .sltu rd rs1 rs2)
      | 0b100#3 => some (.alu .xor  rd rs1 rs2)
      | 0b101#3 => some (.alu .srl  rd rs1 rs2)
      | 0b110#3 => some (.alu .or   rd rs1 rs2)
      | 0b111#3 => some (.alu .and  rd rs1 rs2)
      | _ => none
    else if f7 == 0b0100000#7 then
      match f3 with
      | 0b000#3 => some (.alu .sub rd rs1 rs2)
      | _ => none
    else if f7 == 0b0000001#7 then
      -- RV32M / Zmmul multiply instructions (p. 587; only MUL and MULHU are included).
      match f3 with
      | 0b000#3 => some (.alu .mul   rd rs1 rs2)
      | 0b011#3 => some (.alu .mulhu rd rs1 rs2)
      | _ => none
    else
      none
  else
    none

end ConAgua.RISCV.RV64
