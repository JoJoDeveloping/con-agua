# RISC-V (RV64) Specification & Trusted Computing Base

This directory contains the stand-alone 33-instruction RV64 architectural specification used by the RISC-V backend of `con-agua`. None of the files here import anything outside Lean's core `Init` library, and every definition is total, deterministic, and precondition-free.

> Note: This document is AI-generated to guide a human audit against the *RISC-V Unprivileged ISA Specification* (RV64I + Zmmul/M).

## Files in This Directory

### Trusted Computing Base (539 lines + 68 lines ABI)

| File                                 | Lines | Role                                                                                                                                                                                      |
|--------------------------------------|------:|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| [`Syntax.lean`](./Syntax.lean)       |   133 | 33-instruction AST (`Instr` and op enums in spec order) and major opcodes (`instr[6:0]`). Zero imports.                                                                                   |
| [`Decode.lean`](./Decode.lean)       |   167 | Total binary decoder `decode : BitVec 32 → Option Instr`. Illegal/reserved/unsupported encodings return `none`.                                                                           |
| [`Semantics.lean`](./Semantics.lean) |   239 | Architectural `State`, `getReg`/`setReg`, immediate sign-extension, ALU/branch evaluation, little-endian `loadBytes`/`storeBytes`, `isAligned`, `execInstr`, `step`, `run`, `romOfArray`. |
| [`Abi.lean`](./Abi.lean)             |    68 | Standard RISC-V LP64 psABI register nicknames (`AbiReg.zero..t6`) and `RegsRestored`, needed only to read the top-level theorem statements.                                               |

### Outside the TCB (in this directory for convenience)

`Encode.lean` is outside the TCB both because `Semantics.step` executes raw `BitVec 32` words via `Decode.decode` and because `Roundtrip.lean` proves `encode` and `decode` are exact mutual inverses (`decode (encode inst) = some inst` and `decode w = some inst → encode inst = w`). In fact, because of that bijection, a reviewer only needs to audit *either* `Decode.lean` or `Encode.lean` against the RISC-V encoding tables:

| File                                 | Lines | Role                                                                                                                                                                                                                                                                                    |
|--------------------------------------|------:|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| [`Encode.lean`](./Encode.lean)       |   132 | `encode : Instr → BitVec 32` used by the compiler and linker.                                                                                                                                                                                                                           |
| [`Roundtrip.lean`](./Roundtrip.lean) |   444 | Kernel-checked bijection proofs (`decode_encode : decode (encode inst) = some inst` and `encode_decode : decode w = some inst → encode inst = w`), showing `decode` checks all 32 bits and admits no alias encodings. Standard axioms only (`[propext, Classical.choice, Quot.sound]`). |

### Checking Stand-Alone (Zero Workspace Dependencies)

From the repository root, the spec files compile directly with bare `lean`:

```sh
mkdir -p /tmp/rv64/ConAgua/RISCV/RV64
for m in Syntax Decode Encode Semantics Abi; do
  LEAN_PATH=/tmp/rv64 lean ConAgua/RISCV/RV64/$m.lean -o /tmp/rv64/ConAgua/RISCV/RV64/$m.olean
done
```

Or via Lake (including `Roundtrip.lean`):

```sh
lake build ConAgua.RISCV.RV64.Semantics ConAgua.RISCV.RV64.Abi ConAgua.RISCV.RV64.Roundtrip
```

## Key Points to Review Against the RISC-V Spec

1. **Harvard instruction ROM (`Rom := Nat → Option (BitVec 32)`):** Instruction memory is external and read-only (no self-modifying code). `step` checks `isAligned st.pc 4` and indexes `rom (st.pc.toNat / 4)`, which uniquely maps every 4-byte-aligned 64-bit address (`0 ≤ wordIdx < 2⁶²`).
2. **Flat little-endian byte memory (`Word → Byte`):** Total over all `BitVec 64` addresses modulo `2⁶⁴`. Natural alignment (`4` for `LWU`/`SW`, `8` for `LD`/`SD`) prevents multi-byte accesses from wrapping across `2⁶⁴ - 1 → 0`.
3. **Hardwired `x0 = 0` without state invariants:** Both `State.getReg` and `State.setReg` guard on `r == 0#5`, so `State` carries no `regs 0#5 = 0#64` precondition.
4. **Immediate widths & sign extension (RV32I §2.3, RV64I §4.2):**
   - `imm12 : BitVec 12` is sign-extended to 64 bits for all `OP-IMM` ops, including `SLTIU` (sign-extended *before* unsigned comparison, as described in the spec §2.4.1).
   - `bimm : BitVec 12` (`imm[12:1]`) appends an implicit `0` LSB before sign-extending to 64 bits.
   - `LUI` (`sextImmU`, `imm20 : BitVec 20`) places `imm20` in bits `[31:12]`, zeroes `[11:0]`, and **sign-extends bit 31** into bits `[63:32]`.
   - `jimm : BitVec 20` (`imm[20:1]`) appends an implicit `0` LSB before sign-extending to 64 bits.
5. **Shifts & multiply:** `SLL`/`SRL`/`SLLI`/`SRLI` use **6-bit** RV64 shift amounts (`0..63`); `>>>` on Lean's `BitVec` is zero-filling logical right shift (`BitVec.ushiftRight`). `SLLI`/`SRLI` require `funct6 = 000000` (rejecting `SRAI`). `MUL` returns the low 64 bits; `MULHU` returns bits `[127:64]` of the unsigned `64 × 64 → 128` product.
6. **`JALR` semantics (RV64I §2.5):** Reads `rs1` *before* writing `pc + 4` to `rd` (relevant when `rd = rs1`), and clears bit 0 of the target (`&&& ~~~1#64`). `decode` rejects any `JALR` with `funct3 ≠ 000`.
7. **Subtlety — delayed misaligned-target trap:** In unprivileged RV64I without `C`, jumping or branching to a `2 (mod 4)` address traps *on* the jump/branch before updating `rd`. Here, `execInstr` updates `rd` and sets `pc := target`, and `step` traps at the start of the *next* step (`!isAligned st.pc 4 → .trap`). Because `.trap` is terminal (no trap handler), any further execution traps immediately; only a run stopping with `fuel = 0` right at a misaligned target (such as an unmapped return address `ra`) observes the intermediate state.
8. **Strict alignment:** Misaligned `LWU`/`SW`/`LD`/`SD` trap deterministically (stricter than RV64 hardware that handles misaligned accesses, never more permissive).
9. **Excluded instructions:** Everything outside the 33 instructions listed in [`Syntax.lean`](./Syntax.lean) (`AUIPC`, `SB`, `ECALL`/system, `FENCE`, `SRA`/`SRAI`, `MULH`/`MULHSU`, `DIV*`/`REM*`, `LB`/`LH`/`LW`/`LHU`/`SH`, `OP-32`/`OP-IMM-32`, `F`/`D`/`A`/`C`/`V`, CSRs, interrupts, privilege modes) decodes to `none` and traps.

## Rest of the RISC-V-Specific TCB (Outside This Folder)

In addition to the shared TCB (Lean's kernel, `con-leche`'s specification, and `pins.bin`), trusting the compiled `./riscv/checker` binary also relies on:

1. **Top-level theorem statements** (not their proofs) in [`../Bridge/CheckerDriverFlat.lean`](../Bridge/CheckerDriverFlat.lean) (`checkerRom_accept_model`, `checkerRom_accept_no_False`, starting at `pc = 0#64` / `ca_start`) and [`../Bridge/CheckerDriverCmp.lean`](../Bridge/CheckerDriverCmp.lean) (`checkerCmpRom_accept_model`, `checkerCmpRom_accept_no_False`, starting at `pc = checkerCmpEntryPc` / `ca_start_c`), together with the definitions appearing in their types:
   - `checkerRom`, `checkerCmpEntryWord`, and `checkerCmpEntryPc` in [`../Bridge/CheckerDriverCore.lean`](../Bridge/CheckerDriverCore.lean)
   - `MemSpan.disjoint` in [`../Compiler/SimBase.lean`](../Compiler/SimBase.lean)
   - `acceptWord` in [`../Bridge/CheckerDefs.lean`](../Bridge/CheckerDefs.lean) (with `acceptWord_eq : acceptWord = ConAgua.Final.ACCEPT` in [`../Bridge/CheckerIso.lean`](../Bridge/CheckerIso.lean))
   - The stack-depth hypotheses (`hStackA`/`hStackB`, `runStackNeedB ≤ abiStack`) assumed on the input proof in those theorem statements.
2. **Machine-word emission:** [`../Bridge/EmitChecker.lean`](../Bridge/EmitChecker.lean) (600 lines) links the single unified `checkerCode` image (`ca_start` at word `0`, `ca_start_c` at `checkerCmpEntryWord`, compiled functions emitted once) and writes it as raw `.word 0x...` directives into [`../../../riscv/checker.s`](../../../riscv/checker.s). Unlike the x86 backend's `ConAguaAsm`, `riscv/checker.s` is not parsed back into Lean, so `EmitChecker` is trusted to emit the exact array named in `checkerRom` and place `ca_start_c` at `checkerCmpEntryWord`.
3. **C harness & linker script:**
   - [`../../../commons/main.c`](../../../commons/main.c) (348 lines) — `riscv/Makefile` generates `riscv/main.c` from `commons/main.c` by inserting `#ifdef CA_NOLIBC` / `#ifndef CA_NO_THREADS`; reads inputs/pins (`commons/pins.bin`), allocates and zeroes the 8-byte-aligned region, populates argument registers, calls `ca_start` or `ca_start_c`, and checks `a0 == ACCEPT && a1 == 0`.
   - For cross-compiled x86-64 builds (`-DCA_NOLIBC`): [`../../../riscv/nolibc_rv64.h`](../../../riscv/nolibc_rv64.h) (320 lines) and [`../../../riscv/rv64_linux.ld`](../../../riscv/rv64_linux.ld) (29 lines), plus the C compiler/linker (and `qemu-riscv64` if emulated; mnemonic assembly is bypassed since `checker.s` uses raw `.word`s).
