import ConAgua.Checker.ProgTab
import ConAgua.RISCV.Compiler.Compile

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Lightweight Data Definitions for the RV64 Checker Emitter (`ConAgua.RISCV.Bridge.CheckerDefs`)

Holds only the data definitions needed by `EmitChecker` (`toRiscvTab`, `checkerTabMini`,
`checkerProgMini`, ABI constants, and array/global aliases) without importing
`ConAgua.Final.*` or `ConAgua.L.ModelGen`, so `lake build emit-checker` does not
compile and link `.c.o` object files for the soundness-proof stack.
-/

namespace ConAgua.RISCV.Bridge

def toRiscvNTree : L.Compiler.NTree → ConAgua.RISCV.Compiler.NTree
  | .leaf => .leaf
  | .node l k v r => .node (toRiscvNTree l) k v (toRiscvNTree r)

theorem toRiscvNTree_find (k : Nat) (t : L.Compiler.NTree) :
    (toRiscvNTree t).find k = t.find k := by
  induction t with
  | leaf => rfl
  | node l k' v r ihl ihr =>
    dsimp [toRiscvNTree, ConAgua.RISCV.Compiler.NTree.find, L.Compiler.NTree.find]
    split
    · exact ihl
    · split
      · rfl
      · exact ihr

/-- Convert an `L.Compiler.Tab` (`maxRes = 6` on x86-64) to an RV64 `Tab` (`maxRes = 8`). -/
def toRiscvTab (t : L.Compiler.Tab) : ConAgua.RISCV.Compiler.Tab :=
  { nb := t.nb
    nw := t.nw
    arrAt := t.arrAt
    lmap := toRiscvNTree t.lmap
    rom := t.rom
    nres := t.nres
    ng := t.ng }

abbrev checkerProgMini : L.Prog := L.Checker.checkerProg

def checkerTabMini : ConAgua.RISCV.Compiler.Tab :=
  toRiscvTab L.Checker.checkerTab

abbrev modeGVar : L.GVar := L.Arena.MODE
abbrev ploGVar : L.GVar := L.Arena.PLO
abbrev phiGVar : L.GVar := L.Arena.PHI
abbrev outArr : L.ArrId := L.Arena.OUT
abbrev hdrfArr : L.ArrId := L.Arena.HDRF
abbrev ctlfArr : L.ArrId := L.Arena.CTLF
abbrev inArr : L.ArrId := L.IN
abbrev pbArr : L.ArrId := L.Rom.PB

def acceptWord : L.Word := 0x4143_4345_5054
def inlineSlack : Nat := 1
def hdrHw : Nat := 156
def abiFuel : Nat := 2 ^ 62 - 1

end ConAgua.RISCV.Bridge
