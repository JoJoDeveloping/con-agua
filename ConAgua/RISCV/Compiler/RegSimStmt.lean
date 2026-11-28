import ConAgua.RISCV.Compiler.RegSimStmtCore
import ConAgua.RISCV.Compiler.RegSimStmtBulk

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Register-Allocated Liveness & Base-Statement Simulation (`ConAgua.RISCV.Compiler.RegSimStmt`)

Proves:
1. Pure `MiniL` liveness soundness (`stmtVarLive`): skipping zero-initialization of
   dead locals (`varNeedsZeroInit fd x = false`) preserves both `execB` and `stackNeedB`.
2. Register-allocated store-operand & tiered-array helpers (`evalWArrTierToTempR`,
   `compileStorePairR`, `compileTierStoreTripleR`).
3. Forward simulation of all base statements in `compileSR`: `.set`, `.gset`, `.st8`,
   `.st64`, `.st64t`, `.st32t`, `.copy64`, `.copy8w`, `.scan8`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard Lean axioms only.
-/

namespace ConAgua.RISCV.Compiler

/-- info: 'ConAgua.RISCV.Compiler.execB_stackNeedB_dead_vars_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms execB_stackNeedB_dead_vars_eq
/-- info: 'ConAgua.RISCV.Compiler.reg_set_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms reg_set_sim
/-- info: 'ConAgua.RISCV.Compiler.reg_st32t_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms reg_st32t_sim
/-- info: 'ConAgua.RISCV.Compiler.reg_copy64_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms reg_copy64_sim
/-- info: 'ConAgua.RISCV.Compiler.reg_copy8w_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms reg_copy8w_sim
/-- info: 'ConAgua.RISCV.Compiler.reg_scan8_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms reg_scan8_sim

end ConAgua.RISCV.Compiler
