import ConAgua.RISCV.RV64.Decode

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RV64 Architectural Semantics (`ConAgua.RISCV.RV64.Semantics`)

**Trusted Computing Base (3 of 3):** Imports only `Decode.lean` (which imports only `Syntax.lean`,
zero external dependencies). Contains **only** architectural machine definitions — no proof helper
lemmas and no LP64 calling-convention definitions (see `Abi.lean`).

## Reviewer Checklist & Modeling Choices

Every function in this file is **total, deterministic, and precondition-free**:

1. **Harvard instruction memory (`Rom`):** Instructions live in an external read-only map
   `Rom := Nat → Option (BitVec 32)` indexed by `st.pc.toNat / 4`. There is no self-modifying code,
   and because `step` requires `isAligned st.pc 4` (`pc % 4 = 0`), `st.pc.toNat / 4` uniquely
   identifies every 4-byte-aligned 64-bit address (`0 ≤ wordIdx < 2⁶²`) with no aliasing.
2. **Flat little-endian byte memory (`Word → Byte`):** Total over the entire 64-bit address space
   (modulo `2⁶⁴` wraparound). Because `execInstr` enforces natural alignment (`4` for `LWU`/`SW`,
   `8` for `LD`/`SD`), multi-byte loads and stores never wrap across `2⁶⁴ - 1 → 0`.
3. **Hardwired `x0 = 0` without state invariants:** Both `State.getReg` and `State.setReg` check
   `r == 0#5`, so callers do **not** need a `st.regs 0#5 = 0#64` precondition on `State`.
4. **Immediate sign-extension (RV32I §2.3, RV64I §4.2):**
   - `sextImm12`: sign-extends `imm[11:0]` to 64 bits (including for `SLTIU`, where RV64I
     sign-extends the immediate *before* performing the unsigned comparison, as described in the spec §2.4.1).
   - `sextImmB`: appends implicit bit `0` (`imm[0] = 0`) and sign-extends to 64 bits.
   - `sextImmU` (`LUI`): appends 12 zero LSBs and **sign-extends bit 31** into bits `[63:32]`,
     matching RV64I §4.2.
   - `sextImmJ`: appends implicit bit `0` (`imm[0] = 0`) and sign-extends to 64 bits.
5. **Shifts (RV64I §4.2):** `SLL`, `SRL`, `SLLI`, and `SRLI` use **6-bit** shift amounts (`0..63`),
   not 5-bit RV32 shift amounts. On Lean's `BitVec`, `>>>` is `BitVec.ushiftRight` (zero-filling
   logical right shift); arithmetic shifts `SRA`/`SRAI` are excluded.
6. **Multiplication (RV64M / Zmmul §13.1):** `MUL` returns the low 64 bits of `a * b`;
   `MULHU` returns bits `[127:64]` of the unsigned `64 × 64 → 128` product.
7. **`JALR` operand ordering and LSB clearing (RV64I §2.5):** `target` is computed from
   `st.getReg rs1` *before* writing `pc + 4` to `rd` (relevant when `rd = rs1`), and bit `0` of
   `target` is cleared (`&&& ~~~1#64`).
8. **Subtlety — delayed misaligned-target trap on `JAL`/`JALR`/`BRANCH`:** In unprivileged RV64I
   without the `C` extension, jumping or branching to a `2 (mod 4)` address raises an
   instruction-address-misaligned exception *on* the jump/branch before updating `rd`. Here,
   `execInstr` updates `rd` and sets `pc := target`, and `step` traps at the start of the *next*
   cycle (`!isAligned st.pc 4 → .trap`). Because `.trap` is absorbing (no trap handler exists),
   any subsequent `step` traps immediately; only a run that stops with `fuel = 0` right at a
   misaligned target (e.g., an unmapped return address `ra` checked in the top-level theorem)
   exposes the intermediate `State`.
9. **Strict natural alignment:** Misaligned `LWU`/`SW` (not 4-byte aligned) and `LD`/`SD`
   (not 8-byte aligned) trap deterministically. This is stricter than RV64 implementations that
   support misaligned accesses in hardware/firmware, never more permissive.
-/

namespace ConAgua.RISCV.RV64

abbrev Word := BitVec 64
abbrev Byte := BitVec 8

/-- Architectural machine state (Harvard split: instruction ROM is external and read-only).
    No invariant on `regs 0#5` is required because `getReg` and `setReg` enforce `x0 = 0`. -/
structure State where
  pc   : Word
  regs : Reg → Word
  mem  : Word → Byte

/-- Read general-purpose register `r`, unconditionally returning `0` for `x0` (`0#5`). -/
def State.getReg (st : State) (r : Reg) : Word :=
  if r == 0#5 then 0#64 else st.regs r

/-- Write `v` to general-purpose register `r`, silently discarding writes to `x0` (`0#5`). -/
def State.setReg (st : State) (r : Reg) (v : Word) : State :=
  if r == 0#5 then st
  else { st with regs := fun q => if q == r then v else st.regs q }

/-- I-type / S-type signed 12-bit immediate → 64 bits (`[-2048, +2047]`; §2.3 Figure 1). -/
def sextImm12 (imm : BitVec 12) : Word := imm.signExtend 64
/-- B-type signed 13-bit even offset (`bimm` = `imm[12:1]`, implicit `imm[0] = 0`) → 64 bits (§2.3 Figure 1). -/
def sextImmB  (bimm : BitVec 12) : Word := (bimm ++ 0#1).signExtend 64
/-- U-type (`LUI`) upper 20-bit immediate → 64 bits, sign-extending bit 31 into bits `[63:32]` (§2.3, §4.2.1). -/
def sextImmU  (uimm : BitVec 20) : Word := (uimm ++ 0#12).signExtend 64
/-- J-type signed 21-bit even offset (`jimm` = `imm[20:1]`, implicit `imm[0] = 0`) → 64 bits (§2.3 Figure 1). -/
def sextImmJ  (jimm : BitVec 20) : Word := (jimm ++ 0#1).signExtend 64

/-- Evaluate a register-immediate 64-bit `OP-IMM` instruction (§2.4.1).
    `imm` is sign-extended to 64 bits *before* all ops, including unsigned `SLTIU`
    (as described in the spec). -/
def evalAluImm (op : AluImmOp) (a : Word) (imm : BitVec 12) : Word :=
  let b := sextImm12 imm
  match op with
  | .addi  => a + b
  | .slti  => if a.slt b then 1#64 else 0#64
  | .sltiu => if a.ult b then 1#64 else 0#64
  | .andi  => a &&& b
  | .ori   => a ||| b
  | .xori  => a ^^^ b

/-- Evaluate a 64-bit logical shift-by-immediate instruction (`shamt ∈ [0, 63]`; §2.4.1, §4.2.1). -/
def evalShiftImm (op : ShiftImmOp) (a : Word) (shamt : BitVec 6) : Word :=
  let sh := shamt.toNat
  match op with
  | .slli => a <<< sh
  | .srli => a >>> sh

/-- Evaluate a register-register 64-bit `OP` instruction (§2.4.2, §4.2.2, `M`/`Zmmul` §12.1).
    Shift amounts use the low 6 bits of `b` (`0..63`); `>>>` is zero-filling logical right shift. -/
def evalAlu (op : AluOp) (a b : Word) : Word :=
  let sh := (b.extractLsb' 0 6).toNat
  match op with
  | .add    => a + b
  | .sub    => a - b
  | .slt    => if a.slt b then 1#64 else 0#64
  | .sltu   => if a.ult b then 1#64 else 0#64
  | .and    => a &&& b
  | .or     => a ||| b
  | .xor    => a ^^^ b
  | .sll    => a <<< sh
  | .srl    => a >>> sh
  | .mul    => a * b
  | .mulhu  => ((a.zeroExtend 128) * (b.zeroExtend 128)).extractLsb' 64 64

/-- Evaluate a 64-bit conditional branch comparison (`!slt` = signed `≥`, `!ult` = unsigned `≥`; §2.5.2). -/
def evalBranch (op : BranchOp) (a b : Word) : Bool :=
  match op with
  | .beq  => a == b
  | .bne  => a != b
  | .blt  => a.slt b
  | .bltu => a.ult b
  | .bge  => !a.slt b
  | .bgeu => !a.ult b

/-- Little-endian multi-byte read: `mem (addr + k)` supplies bits `[8*k + 7 : 8*k]` (§2.6).
    Total for all `addr` and `n`; addresses wrap modulo `2⁶⁴`. -/
def loadBytes (mem : Word → Byte) (addr : Word) : (n : Nat) → BitVec (8 * n)
  | 0 => 0#0
  | n + 1 =>
    let lo : BitVec 8 := mem addr
    let hi : BitVec (8 * n) := loadBytes mem (addr + 1#64) n
    (hi ++ lo).cast (by omega)

/-- Little-endian multi-byte write: bits `[8*k + 7 : 8*k]` of `v` are written to `addr + k` (§2.6).
    Total for all `addr`, `n`, and `v`; addresses wrap modulo `2⁶⁴`. -/
def storeBytes (mem : Word → Byte) (addr : Word) : (n : Nat) → BitVec (8 * n) → (Word → Byte)
  | 0, _ => mem
  | n + 1, v =>
    let b : Byte := v.extractLsb' 0 8
    let rest : BitVec (8 * n) := v.extractLsb' 8 (8 * n)
    let mem' := fun a => if a == addr then b else mem a
    storeBytes mem' (addr + 1#64) n rest

/-- Natural alignment check for the supported access widths `{1, 4, 8}` bytes (`false` otherwise; §2.6). -/
def isAligned (addr : Word) (n : Nat) : Bool :=
  match n with
  | 1 => true
  | 4 => addr.extractLsb' 0 2 == 0#2
  | 8 => addr.extractLsb' 0 3 == 0#3
  | _ => false

/-- Outcome of one or more architectural steps (`.trap` is absorbing and never accepts). -/
inductive StepResult where
  | cont (st : State)
  | trap

/-- Read-only instruction ROM indexed by 32-bit word index `pc.toNat / 4`. -/
abbrev Rom := Nat → Option (BitVec 32)

/-- Execute a single decoded instruction on `st` in spec order
    (§§2.4, 2.5, 2.6, 4.2, 4.3, 12.1; see header note #8 on misaligned jump targets). -/
def execInstr (st : State) (inst : Instr) : StepResult :=
  let pc4 := st.pc + 4#64
  match inst with
  | .aluImm op rd rs1 imm12 =>
    .cont { (st.setReg rd (evalAluImm op (st.getReg rs1) imm12)) with pc := pc4 }
  | .shImm op rd rs1 shamt =>
    .cont { (st.setReg rd (evalShiftImm op (st.getReg rs1) shamt)) with pc := pc4 }
  | .lui rd imm20 =>
    .cont { (st.setReg rd (sextImmU imm20)) with pc := pc4 }
  | .alu op rd rs1 rs2 =>
    .cont { (st.setReg rd (evalAlu op (st.getReg rs1) (st.getReg rs2))) with pc := pc4 }
  | .jal rd jimm =>
    .cont { (st.setReg rd pc4) with pc := st.pc + sextImmJ jimm }
  | .jalr rd rs1 imm12 =>
    -- Read `rs1` before writing `rd` (matters when `rd = rs1`), then clear bit 0 per RV64I §2.5.
    let target := (st.getReg rs1 + sextImm12 imm12) &&& (~~~1#64)
    .cont { (st.setReg rd pc4) with pc := target }
  | .branch op rs1 rs2 bimm =>
    let nextPc := if evalBranch op (st.getReg rs1) (st.getReg rs2)
                  then st.pc + sextImmB bimm else pc4
    .cont { st with pc := nextPc }
  | .load op rd rs1 imm12 =>
    let addr := st.getReg rs1 + sextImm12 imm12
    match op with
    | .ld =>
      if isAligned addr 8 then
        .cont { (st.setReg rd (loadBytes st.mem addr 8)) with pc := pc4 }
      else .trap
    | .lwu =>
      if isAligned addr 4 then
        .cont { (st.setReg rd ((loadBytes st.mem addr 4).zeroExtend 64)) with pc := pc4 }
      else .trap
    | .lbu =>
      .cont { (st.setReg rd ((loadBytes st.mem addr 1).zeroExtend 64)) with pc := pc4 }
  | .store op rs1 rs2 imm12 =>
    let addr := st.getReg rs1 + sextImm12 imm12
    let v := st.getReg rs2
    match op with
    | .sd =>
      if isAligned addr 8 then
        .cont { st with pc := pc4, mem := storeBytes st.mem addr 8 v }
      else .trap
    | .sw =>
      if isAligned addr 4 then
        .cont { st with pc := pc4, mem := storeBytes st.mem addr 4 (v.extractLsb' 0 32) }
      else .trap

/-- Fetch, decode, and execute one architectural instruction from `rom`.
    Traps if `st.pc` is not 4-byte aligned, unmapped in `rom`, or decodes to `none`. -/
def step (rom : Rom) (st : State) : StepResult :=
  if !isAligned st.pc 4 then .trap
  else
    match rom (st.pc.toNat / 4) with
    | none => .trap
    | some word =>
      match decode word with
      | none => .trap
      | some inst => execInstr st inst

/-- Bounded multi-step execution for `n` instructions, stopping immediately on `.trap`. -/
def run (rom : Rom) : Nat → State → StepResult
  | 0, st => .cont st
  | n + 1, st =>
    match step rom st with
    | .cont st' => run rom n st'
    | res => res

/-- Construct a total `Rom` from a contiguous `Array (BitVec 32)` starting at address `0`
    (`none` for out-of-bounds indices). -/
def romOfArray (code : Array (BitVec 32)) : Rom := fun i => code[i]?

end ConAgua.RISCV.RV64
