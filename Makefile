.PHONY: all checker L X86 lean check check-x86 clean regen regen-check

all:
	$(MAKE) -C x86

checker:
	$(MAKE) -C x86 checker

L:
	scripts/lake build ConAgua ConLeche ConRonArena ConRonBridge

X86:
	scripts/lake build ConAguaX86 ConAguaAsm

lean:
	scripts/lake build

check-x86:
	$(MAKE) -C x86 check

check: check-x86

regen:
	python3 scripts/reasons.py
	python3 scripts/asm_file.py

regen-check:
	python3 scripts/reasons.py --check
	python3 scripts/asm_file.py --check

clean:
	$(MAKE) -C x86 clean
