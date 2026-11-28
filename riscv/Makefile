# Minimal RV64 checker binary built from:
#   main.c                generated from ../commons/main.c by inserting #ifdef CA_NOLIBC / #ifndef CA_NO_THREADS
#   nolibc_rv64.h         Linux RV64 freestanding syscall shim for bare-metal cross-toolchain builds
#   checker.s             verified RV64 machine words (.word 0x...) emitted by ConAgua.RISCV.Bridge.EmitChecker
#   ../commons/pins.bin   pin data, embedded via --embed-dir=../commons
#   ../commons/reasons.h  abort reason messages, included via -I../commons
#
# Builds natively on RISC-V Linux (`cc -std=gnu23 -O2`) or cross-compiles on x86-64
# via `riscv64-unknown-elf-gcc -DCA_NOLIBC` and runs under `qemu-riscv64`.

HOST_ARCH := $(shell uname -m)
CFLAGS ?= -O2
PRELUDE = ../vendor/con-leche/pins/leanprover-lean4-v4.36.0.prelude.ndjson

main.c: ../commons/main.c Makefile
	python3 -c 'import sys; s = open(sys.argv[1]).read(); \
	reps = [ \
	  ("#include <errno.h>\n", "#ifdef CA_NOLIBC\n#include \"nolibc_rv64.h\"\n#else\n#include <errno.h>\n"), \
	  ("#include <pthread.h>\n", "#ifndef CA_NO_THREADS\n#include <pthread.h>\n#endif\n"), \
	  ("#include <unistd.h>\n", "#include <unistd.h>\n#endif\n"), \
	  ("static const uint64_t *g_buf;", "#ifndef CA_NO_THREADS\nstatic const uint64_t *g_buf;"), \
	  ("static int run_compare(const char *prog, int jobs, int argc, char **argv);", \
	   "#else\nstatic int run_jobs(int jobs, uint8_t *in, uint64_t in_len, uint8_t *s, uint64_t s_len, uint8_t *base) {\n  (void)jobs; (void)in; (void)in_len; (void)s; (void)s_len; (void)base;\n  fprintf(stderr, \"--jobs > 1 is not supported on RV64 (use --jobs=1)\\n\");\n  return 3;\n}\n#endif\n\nstatic int run_compare(const char *prog, int jobs, int argc, char **argv);"), \
	]; \
	[sys.exit(f"missing/ambiguous anchor: {a!r}") for a, _ in reps if s.count(a) != 1]; \
	[s := s.replace(a, b, 1) for a, b in reps]; \
	open(sys.argv[2], "w").write("/* Generated from ../commons/main.c by riscv/Makefile; do not edit. */\n" + s)' $< $@.tmp
	mv $@.tmp $@

ifeq ($(HOST_ARCH),riscv64)
CC ?= cc
RUN ?=
checker: main.c checker.s ../commons/pins.bin ../commons/reasons.h
	$(CC) -DCA_NO_THREADS -std=gnu23 $(CFLAGS) -I../commons --embed-dir=../commons -o $@ main.c checker.s
else
RV_CC ?= /usr/bin/riscv64-unknown-elf-gcc
QEMU ?= /usr/bin/qemu-riscv64
RUN ?= $(QEMU)
checker: main.c nolibc_rv64.h rv64_linux.ld checker.s ../commons/pins.bin ../commons/reasons.h
	$(RV_CC) -DCA_NOLIBC -DCA_NO_THREADS -std=gnu23 $(CFLAGS) -nostdlib -mno-relax -march=rv64ima -mabi=lp64 -mcmodel=medany -T rv64_linux.ld -I../commons --embed-dir=../commons -o $@ main.c checker.s
endif

check: checker
	out=$$($(RUN) ./checker $(PRELUDE)); echo "$$out"; test "$$out" = "accept"
	printf 'not json\n' > checker-smoke.ndjson
	out=$$($(RUN) ./checker checker-smoke.ndjson); rc=$$?; echo "$$out"; test $$rc = 3 && test "$$out" = "ok 1"
	cp $(PRELUDE) checker-cmp-sol.ndjson
	out=$$($(RUN) ./checker --compare $(PRELUDE) checker-cmp-sol.ndjson); echo "$$out"; test "$$out" = "accept"
	rm -f checker-smoke.ndjson checker-cmp-sol.ndjson
	@echo "make check: ok"

ELAN_LAKE ?= $(HOME)/.elan/bin/lake
LAKE_CACHE ?= $(CURDIR)/../_tmp/lake-cache-v2

regen:
	cd .. && LAKE_ARTIFACT_CACHE=true LAKE_CACHE_DIR=$(LAKE_CACHE) $(ELAN_LAKE) exe emit-checker --asm riscv/checker.s

clean:
	rm -f checker main.c main.c.tmp checker-smoke.ndjson checker-cmp-sol.ndjson

.PHONY: check regen clean
