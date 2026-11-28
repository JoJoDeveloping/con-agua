.PHONY: all checker L X86 RISCV lean check check-x86 check-riscv clean regen regen-check

all:
	$(MAKE) -C x86
	$(MAKE) -C riscv

checker:
	$(MAKE) -C x86 checker

L:
	scripts/lake build ConAgua ConLeche ConRonArena ConRonBridge

X86:
	scripts/lake build ConAguaX86 ConAguaAsm

RISCV:
	scripts/lake build ConAguaRISCV emit-checker

lean:
	scripts/lake build

check-x86:
	$(MAKE) -C x86 check

check-riscv:
	$(MAKE) -C riscv check

check: check-x86 check-riscv

regen:
	python3 scripts/reasons.py
	python3 scripts/asm_file.py
	$(MAKE) -C riscv regen

regen-check:
	python3 scripts/reasons.py --check
	python3 scripts/asm_file.py --check

clean:
	$(MAKE) -C x86 clean
	$(MAKE) -C riscv clean
