import ConAgua.RISCV.Bridge.CheckerDriverFlat
import ConAgua.RISCV.Bridge.CheckerDriverCmp

/-!
# End-to-End Backward Soundness of Linked Checker ROM (`ConAgua.RISCV.Bridge.CheckerDriverProof`)

Thin re-export barrel combining the flat checker proof (`CheckerDriverFlat`) and the
comparator proof (`CheckerDriverCmp`), which share `CheckerDriverSetup` and compile in parallel.
-/
