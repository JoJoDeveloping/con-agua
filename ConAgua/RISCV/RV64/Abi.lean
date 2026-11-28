import ConAgua.RISCV.RV64.Semantics

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RISC-V LP64 psABI Register & Calling-Convention Definitions (`ConAgua.RISCV.RV64.Abi`)

Separated from `Syntax.lean` and `Semantics.lean` so the core ISA specification stays purely
architectural. Defines standard RISC-V psABI register nicknames (`x0..x31` → `zero..t6`) and
the LP64 callee-saved register preservation predicate (`RegsRestored`) used by the C harness
interface theorems.
-/

namespace ConAgua.RISCV.RV64

-- Standard RISC-V integer psABI register names (`x0..x31`).
namespace AbiReg
def zero : Reg := 0#5   -- x0: hardwired zero
def ra   : Reg := 1#5   -- x1: return address (caller-saved)
def sp   : Reg := 2#5   -- x2: stack pointer (callee-saved)
def gp   : Reg := 3#5   -- x3: global pointer (unallocatable; preserved)
def tp   : Reg := 4#5   -- x4: thread pointer (unallocatable; preserved)
def t0   : Reg := 5#5   -- x5: temporary (caller-saved)
def t1   : Reg := 6#5   -- x6: temporary (caller-saved)
def t2   : Reg := 7#5   -- x7: temporary (caller-saved)
def s0   : Reg := 8#5   -- x8: saved register / frame pointer (callee-saved)
def s1   : Reg := 9#5   -- x9: saved register (callee-saved)
def a0   : Reg := 10#5  -- x10: arg 0 / return value 0 (caller-saved)
def a1   : Reg := 11#5  -- x11: arg 1 / return value 1 (caller-saved)
def a2   : Reg := 12#5  -- x12: arg 2 (caller-saved)
def a3   : Reg := 13#5  -- x13: arg 3 (caller-saved)
def a4   : Reg := 14#5  -- x14: arg 4 (caller-saved)
def a5   : Reg := 15#5  -- x15: arg 5 (caller-saved)
def a6   : Reg := 16#5  -- x16: arg 6 (caller-saved)
def a7   : Reg := 17#5  -- x17: arg 7 (caller-saved)
def s2   : Reg := 18#5  -- x18..x27: saved registers (callee-saved)
def s3   : Reg := 19#5
def s4   : Reg := 20#5
def s5   : Reg := 21#5
def s6   : Reg := 22#5
def s7   : Reg := 23#5
def s8   : Reg := 24#5
def s9   : Reg := 25#5
def s10  : Reg := 26#5
def s11  : Reg := 27#5
def t3   : Reg := 28#5  -- x28..x31: temporaries (caller-saved)
def t4   : Reg := 29#5
def t5   : Reg := 30#5
def t6   : Reg := 31#5
end AbiReg

/-- Registers preserved across a call under the RISC-V LP64 psABI (`sp, gp, tp, s0..s11`). -/
def lp64CalleeSaved : List Reg :=
  [2#5, 3#5, 4#5, 8#5, 9#5, 18#5, 19#5, 20#5, 21#5, 22#5, 23#5, 24#5, 25#5, 26#5, 27#5]

/-- Every register in `lp64CalleeSaved` has the same value in `finalSt` as in `initSt`. -/
def RegsRestored (initSt finalSt : State) : Prop :=
  ∀ r ∈ lp64CalleeSaved, finalSt.getReg r = initSt.getReg r

theorem RegsRestored.refl (st : State) : RegsRestored st st :=
  fun _ _ => rfl

theorem RegsRestored.trans {st0 st1 st2 : State}
    (h01 : RegsRestored st0 st1) (h12 : RegsRestored st1 st2) : RegsRestored st0 st2 :=
  fun r hr => (h12 r hr).trans (h01 r hr)

end ConAgua.RISCV.RV64
