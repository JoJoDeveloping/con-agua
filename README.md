# con-agua – A Lean checker verified at the assembly level

This is a reimplementation of the external Lean checker [con-leche](
https://github.com/leanprover/con-leche), verified at the (x86) assembly level.

This was written by AI under supervision from Joachim Breitner at the [Lean FRO](https://lean-fro.org/). This README is genuinely human written; the rest of the repository is not. The file [`OVERVIEW.md`](./OVERVIEW.md) contains a much more detailed, AI written exposition of the project.

## Goal

The `con-agua` checker joins [`con-ron`](https://github.com/leanprover/con-ron/) in providing extra assurance by reimplementing `con-leche` in a different setting. All three are proven to implement essentially the same consistent checking algorithm. But any such verification work leaves something left to be trusted:

* `con-leche`, written in Lean, in particular requires the Lean compiler and the Lean runtime with its bignum implementation to be correct.
* `con-ron`, written in Rust, in particular requires the Rust compiler as well as the Aeneas verification tool to be correct.
* `con-agua`, verified at the assembly level. We currently target two architectures:
    + For `x86-64` we in particular require the Kraken x86 semantics to be correct.
    + For `RISC-V` we hand-roll [our own semantics](./ConAgua/RISCV/RV64/README.md).

A bug in any of these trusted components threatens the validity of that checker's result. But if you check your proof with all three of them, the likelihood of bugs existing in all three settings that can be exploited together diminishes.

## Usage

Run [`make`](./Makefile) and call `./x86/checker FILE.ndjson`. Pass `--jobs=n` if you want parallel checking. Use `./x86/checker --compare CHALLENGE.ndjson SOLUTION.ndjson` for comparator mode. Unlike `con-leche` and `con-ron`, reading of `.olean` files is not supported. The `./riscv/checker` binary works the same way. See [`OVERVIEW.md`](./OVERVIEW.md) for more details.

## Architecture

The assembly is produced from code written in our own little ad-hoc low-level language [L](./ConAgua/L/), lowered to assembly by verified compilers. The L code is proven to simulate `con-leche` (via [`con-ron`’s Lean model](./vendor/con-ron/ConRon/Arena/), which already handles hash-consing and caching).

The small, trusted [`main.c`](./commons/main.c) file reads the input and invokes the entry point of the assembly function. With `--jobs=n`, after parsing the input (using the verified assembly for that), it spawns threads and invokes the verified assembly once for each declaration group.

The RISC-V backend tries to optimize the code a bit, by e.g. performing register allocation. It helps keep the binary small (smaller than the x86 one) and fast in `qemu`. This of course makes the correctness proof more complicated.

Again, more detail to be found in [`OVERVIEW.md`](./OVERVIEW.md).

### X86

The [compiler](./ConAgua/X86/Compiler/) is verified against the [Kraken](https://github.com/AeneasVerif/kraken) x86 semantics, proving that if the type checker in the assembly file [`checker.s`](./x86/checker.s) accepts, then `con-leche` and `con-ron` accept too (up to resource limits). See [`EndToEnd.lean`](./ConAgua/X86/Final/EndToEnd.lean) for the main theorems of this development.

### RISC-V

Here, the compiler is verified against a [hand-rolled semantics](./ConAgua/RISCV/RV64/). This semantics only models a tiny subset of RISC-V, which makes it easy to e.g. build a verified CPU. The semantics is currently not validated against anything, but since RISC-V is so extremely simple, it can be reviewed by a human in ~15 minutes.

The `main.c` file is generated from [the common one](./commons/main.c). It is identitcal, but it can be build with the [`nolibc_rv64.h`](./riscv/nolibc_rv64.h) header, which performs raw Linux syscalls. This is useful for testing (e.g. in `qemu`) or in case one is paranoid about bugs in `libc`.


## Contributions

Unsolicited PRs against this repo are unlikely to be useful; well-written issues with bug reports or feature requests are welcome.
