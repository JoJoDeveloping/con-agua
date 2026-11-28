set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Minimal RV64 33-Instruction Subset (`ConAgua.RISCV.RV64.Syntax`)

**Trusted Computing Base (1 of 3):** This file has **zero** imports outside Lean's core `Init`
library, no proofs, and no ABI/compiler dependencies. Together with `Decode.lean` and
`Semantics.lean`, it forms the entire trusted RV64 architectural specification.
Calling-convention names (`AbiReg`, `RegsRestored`) live separately in `Abi.lean`;
`Encode.lean` and `Roundtrip.lean` are outside the TCB (`step` executes via `decode`).

## Design for Precondition-Free Auditing

Every operand field uses its exact architectural bit-width so every value of type `Instr`
denotes a syntactically valid instruction with **no** side conditions or range invariants:
- `Reg := BitVec 5` -- general-purpose registers `x0..x31` (no `< 32` precondition; §2.1, §4.1).
- `imm12 : BitVec 12` -- I/S-type signed two's-complement immediate in `[-2048, +2047]` (§2.3).
- `bimm : BitVec 12` -- B-type signed branch offset bits `[12:1]` (implicit bit `0 = 0`,
  representing even byte offsets in `[-4096, +4094]`; §2.3).
- `imm20 : BitVec 20` -- U-type upper immediate bits `[31:12]` (implicit bits `[11:0] = 0`; §2.3).
- `jimm : BitVec 20` -- J-type signed jump offset bits `[20:1]` (implicit bit `0 = 0`,
  representing even byte offsets in `[-1048576, +1048574]`; §2.3).
- `shamt : BitVec 6` -- RV64 6-bit shift amount in `[0, 63]` (no `< 64` precondition; §4.2.1).

## Complete 33-Instruction Table (RV64I + Zmmul/M subset, Spec Order)

| Group        | Mnemonic                | Format   | `opcode` `[6:0]` |    `funct3` `[14:12]` | `funct6`/`funct7` | Spec             |
|--------------|-------------------------|----------|-----------------:|----------------------:|------------------:|------------------|
| `OP-IMM` (6) | `ADDI`                  | I        |        `0010011` |                 `000` |                 - | RV32I §2.4.1     |
|              | `SLTI` / `SLTIU`        | I        |        `0010011` |         `010` / `011` |                 - | RV32I §2.4.1     |
|              | `ANDI` / `ORI` / `XORI` | I        |        `0010011` | `111` / `110` / `100` |                 - | RV32I §2.4.1     |
| Shifts (2)   | `SLLI` / `SRLI`         | I (RV64) |        `0010011` |         `001` / `101` |     `f6 = 000000` | RV64I §4.2.1     |
| Upper (1)    | `LUI`                   | U        |        `0110111` |                     - |                 - | RV32I §2.4.1/4.2 |
| `OP` (9)     | `ADD`                   | R        |        `0110011` |                 `000` |    `f7 = 0000000` | RV32I §2.4.2     |
|              | `SUB`                   | R        |        `0110011` |                 `000` |    `f7 = 0100000` | RV32I §2.4.2     |
|              | `SLT` / `SLTU`          | R        |        `0110011` |         `010` / `011` |    `f7 = 0000000` | RV32I §2.4.2     |
|              | `AND` / `OR` / `XOR`    | R        |        `0110011` | `111` / `110` / `100` |    `f7 = 0000000` | RV32I §2.4.2     |
|              | `SLL` / `SRL`           | R        |        `0110011` |         `001` / `101` |    `f7 = 0000000` | RV32I §2.4.2/4.2 |
| Mul (2)      | `MUL` / `MULHU`         | R        |        `0110011` |         `000` / `011` |    `f7 = 0000001` | M/Zmmul §12.1    |
| Jumps (2)    | `JAL`                   | J        |        `1101111` |                     - |                 - | RV32I §2.5.1     |
|              | `JALR`                  | I        |        `1100111` |                 `000` |                 - | RV32I §2.5.1     |
| Branch (6)   | `BEQ` / `BNE`           | B        |        `1100011` |         `000` / `001` |                 - | RV32I §2.5.2     |
|              | `BLT` / `BLTU`          | B        |        `1100011` |         `100` / `110` |                 - | RV32I §2.5.2     |
|              | `BGE` / `BGEU`          | B        |        `1100011` |         `101` / `111` |                 - | RV32I §2.5.2     |
| Loads (3)    | `LD` / `LWU` / `LBU`    | I        |        `0000011` | `011` / `110` / `100` |                 - | RV64I §4.3/2.6   |
| Stores (2)   | `SD` / `SW`             | S        |        `0100011` |         `011` / `010` |                 - | RV64I §4.3/2.6   |

Everything outside these 33 instructions decodes to `none` and traps (`AUIPC`, `SB`, `ECALL`/system,
`FENCE`, `SRA`/`SRAI`, `MULH`/`MULHSU`, `DIV*`/`REM*`, `LB`/`LH`/`LW`/`LHU`/`SH`,
`OP-32`/`OP-IMM-32`, `F`/`D`/`A`/`C`/`V`, CSRs, interrupts, and privilege modes).
-/

namespace ConAgua.RISCV.RV64

/-- 5-bit architectural general-purpose register index (`0..31`; `x0` is hardwired to zero
    in `State.getReg` and `State.setReg`; RV32I §2.1, RV64I §4.1). -/
abbrev Reg := BitVec 5

/-- Register-immediate 64-bit integer computational operations (`OP-IMM`, opcode `0010011`; §2.4.1). -/
inductive AluImmOp where
  | addi | slti | sltiu | andi | ori | xori
  deriving Repr, DecidableEq, Inhabited

/-- 64-bit logical shift-by-immediate operations (`OP-IMM`, RV64 6-bit `shamt` in `0..63`,
    `funct6 = 000000`; §2.4.1, §4.2.1). Arithmetic shift `SRAI` is excluded. -/
inductive ShiftImmOp where
  | slli | srli
  deriving Repr, DecidableEq, Inhabited

/-- Register-register 64-bit integer computational (`OP`, §2.4.2, §4.2.2) and unsigned multiply
    (`M`/`Zmmul`, §12.1, §12.3) operations (opcode `0110011`). -/
inductive AluOp where
  | add | sub | slt | sltu | and | or | xor | sll | srl
  | mul | mulhu
  deriving Repr, DecidableEq, Inhabited

/-- Conditional branch comparisons (`BRANCH`, opcode `1100011`; §2.5.2). -/
inductive BranchOp where
  | beq | bne | blt | bltu | bge | bgeu
  deriving Repr, DecidableEq, Inhabited

/-- Unsigned `{64, 32, 8}`-bit loads (`LOAD`, opcode `0000011`; §2.6, §4.3).
    Natural alignment enforced. -/
inductive LoadOp where
  | ld | lwu | lbu
  deriving Repr, DecidableEq, Inhabited

/-- `{64, 32}`-bit stores (`STORE`, opcode `0100011`; §2.6, §4.3).
    Natural alignment enforced. -/
inductive StoreOp where
  | sd | sw
  deriving Repr, DecidableEq, Inhabited

/-- Minimal RV64 instruction AST (33 instructions total; no side conditions on operands),
    ordered to follow the RISC-V Unprivileged ISA Specification (§2.4, §2.5, §2.6, §4.2, §4.3, §12.1). -/
inductive Instr where
  /-- `<op>I rd, rs1, imm12` (§2.4.1): 64-bit ALU op with sign-extended 12-bit immediate. -/
  | aluImm (op : AluImmOp) (rd rs1 : Reg) (imm12 : BitVec 12)
  /-- `SLLI`/`SRLI rd, rs1, shamt` (§2.4.1, §4.2.1): 64-bit logical shift by `shamt ∈ [0, 63]`. -/
  | shImm  (op : ShiftImmOp) (rd rs1 : Reg) (shamt : BitVec 6)
  /-- `LUI rd, imm20` (§2.4.1, §4.2.1): `rd ← signExtend₆₄(imm20 ++ 0#12)`. -/
  | lui    (rd : Reg) (imm20 : BitVec 20)
  /-- `<op> rd, rs1, rs2` (§2.4.2, §4.2.2, §12.1): 64-bit register-register ALU or multiply (`MUL`/`MULHU`). -/
  | alu    (op : AluOp) (rd rs1 rs2 : Reg)
  /-- `JAL rd, jimm` (§2.5.1): `rd ← pc + 4; pc ← pc + signExtend₆₄(jimm ++ 0#1)`. -/
  | jal    (rd : Reg) (jimm : BitVec 20)
  /-- `JALR rd, rs1, imm12` (§2.5.1): `t ← (rs1 + signExtend₆₄(imm12)) & ~1; rd ← pc + 4; pc ← t`. -/
  | jalr   (rd : Reg) (rs1 : Reg) (imm12 : BitVec 12)
  /-- `B<op> rs1, rs2, bimm` (§2.5.2): branch to `pc + signExtend₆₄(bimm ++ 0#1)` if `op(rs1, rs2)`. -/
  | branch (op : BranchOp) (rs1 rs2 : Reg) (bimm : BitVec 12)
  /-- `LD`/`LWU`/`LBU rd, imm12(rs1)` (§2.6, §4.3): zero-extending little-endian load. -/
  | load   (op : LoadOp) (rd rs1 : Reg) (imm12 : BitVec 12)
  /-- `SD`/`SW rs2, imm12(rs1)` (§2.6, §4.3): little-endian store of low 64 or 32 bits of `rs2`. -/
  | store  (op : StoreOp) (rs1 rs2 : Reg) (imm12 : BitVec 12)
  deriving Repr, DecidableEq, Inhabited

/-! ## Standard RISC-V Major Opcodes (`instr[6:0]`)

Matches the Unprivileged ISA Spec "RV32/64G Opcode Map" (Chapter 36, Table 72).
All 8 values have low two bits `11` (standard 32-bit uncompressed encoding). -/
namespace Opcode
def load   : BitVec 7 := 0b0000011#7  -- 0x03
def opImm  : BitVec 7 := 0b0010011#7  -- 0x13
def store  : BitVec 7 := 0b0100011#7  -- 0x23
def op     : BitVec 7 := 0b0110011#7  -- 0x33
def lui    : BitVec 7 := 0b0110111#7  -- 0x37
def branch : BitVec 7 := 0b1100011#7  -- 0x63
def jalr   : BitVec 7 := 0b1100111#7  -- 0x67
def jal    : BitVec 7 := 0b1101111#7  -- 0x6F
end Opcode

end ConAgua.RISCV.RV64
