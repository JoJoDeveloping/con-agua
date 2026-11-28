import ConAgua.RISCV.RV64.Encode
import ConAgua.RISCV.RV64.Semantics
import ConAgua.RISCV.RV64.Abi

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Symbolic RV64 Assembler & Two-Pass Deterministic Linker (`ConAgua.RISCV.Compiler.Asm`)

Provides a symbolic assembly AST (`AsmItem`) with labels, jumps, calls, conditional
branches (with automatic long-branch veneer relaxation when a branch exceeds ±4 KiB),
and `li` 64-bit constant materialization macros, plus a deterministic two-pass linker
producing `Array (BitVec 32)`.
-/

namespace ConAgua.RISCV.Compiler

open ConAgua.RISCV.RV64

/-- Negate a conditional branch opcode. -/
def invertBranch : BranchOp → BranchOp
  | .beq  => .bne
  | .bne  => .beq
  | .blt  => .bge
  | .bge  => .blt
  | .bltu => .bgeu
  | .bgeu => .bltu

/-- Symbolic RV64 assembly items. -/
inductive AsmItem where
  | label (name : String)
  | instr (inst : Instr)
  | j (target : String)
  | call (target : String)
  | br (op : BranchOp) (rs1 rs2 : Reg) (target : String)
  /-- Long-branch veneer: inverted short branch (+8 bytes) followed by `jal zero target`. -/
  | brLong (op : BranchOp) (rs1 rs2 : Reg) (target : String)
  deriving Repr, DecidableEq, Inhabited

/-- Number of 32-bit machine words emitted for one `AsmItem`. -/
def AsmItem.wordSize : AsmItem → Nat
  | .label _     => 0
  | .instr _     => 1
  | .j _         => 1
  | .call _      => 1
  | .br ..       => 1
  | .brLong ..   => 2

/-- True iff `w` equals the 64-bit sign-extension of its low 12 bits (`[-2048, 2047]`). -/
def fitsImm12 (w : BitVec 64) : Bool :=
  (w.extractLsb' 0 12).signExtend 64 == w

/-- Materialize `w32.signExtend 64` into `rd` using only `LUI` and `ADDI` (`rd ≠ zero`). -/
def li32Instrs (rd : Reg) (w32 : BitVec 32) : List Instr :=
  let w64 := w32.signExtend 64
  if fitsImm12 w64 then
    [.aluImm .addi rd AbiReg.zero (w32.extractLsb' 0 12)]
  else
    let lo12 := w32.extractLsb' 0 12
    let hi20 := w32.extractLsb' 12 20
    if lo12 == 0#12 then
      [.lui rd hi20]
    else if !lo12.msb then
      [.lui rd hi20, .aluImm .addi rd rd lo12]
    else if hi20 != 0x7ffff#20 then
      [.lui rd (hi20 + 1#20), .aluImm .addi rd rd lo12]
    else
      -- `w32 ∈ [0x7ffff800, 0x7fffffff]`: `hi20 + 1 = 0x80000` would sign-extend negatively in RV64.
      let rem := lo12 - 2048#12
      [.lui rd hi20, .aluImm .addi rd rd 1024#12, .aluImm .addi rd rd 1024#12] ++
        (if rem == 0#12 then [] else [.aluImm .addi rd rd rem])

/-- Trailing-zero bit count of a 64-bit word (`64` for `0`). -/
def ctz64 (w : BitVec 64) : Nat :=
  let rec go (x acc : Nat) : Nat → Nat
    | 0 => acc
    | fuel + 1 => if x % 2 == 1 then acc else go (x / 2) (acc + 1) fuel
  if w == 0#64 then 64 else go w.toNat 0 64

/-- If `w = (-1#64) >>> sh` (`0 < sh < 64`), return `some sh` for a 2-insn `addi -1; srli sh`. -/
def liLowMask? (w : BitVec 64) : Option (BitVec 6) :=
  let v := w.toNat
  if v == 0 then none
  else
    let sh := 64 - Nat.log2 v - 1
    if 0 < sh && sh < 64 then
      let sh6 := BitVec.ofNat 6 sh
      if ((BitVec.ofInt 64 (-1)) >>> sh6.toNat) == w then some sh6 else none
    else none

/-- If `w = (hi32.signExtend 64 <<< sh) + lo.signExtend 64` for `0 < sh < 64`,
    return `(hi32, sh, lo)` so `li` can emit `li32Instrs rd hi32; slli sh [; addi lo]`. -/
def liShiftAdd? (w : BitVec 64) : Option (BitVec 32 × BitVec 6 × BitVec 12) :=
  let tryLo (lo : BitVec 12) : Option (BitVec 32 × BitVec 6 × BitVec 12) :=
    let w' := w - lo.signExtend 64
    let tz := ctz64 w'
    if 0 < tz && tz < 64 then
      let sh := BitVec.ofNat 6 tz
      let hi32 := (w' >>> tz).extractLsb' 0 32
      if (hi32.signExtend 64 <<< sh.toNat) + lo.signExtend 64 == w then
        some (hi32, sh, lo)
      else none
    else none
  match tryLo 0#12 with
  | some p => some p
  | none => tryLo (w.extractLsb' 0 12)

/-- Materialize an arbitrary 64-bit constant `w` into `rd` using `LUI`/`ADDI`/`SLLI`/`SRLI`. -/
def li (rd : Reg) (w : BitVec 64) : List AsmItem :=
  if rd == AbiReg.zero then []
  else if fitsImm12 w then
    [.instr (.aluImm .addi rd AbiReg.zero (w.extractLsb' 0 12))]
  else match liLowMask? w with
  | some sh =>
    [.instr (.aluImm .addi rd AbiReg.zero (-1#12)),
     .instr (.shImm .srli rd rd sh)]
  | none =>
    if (w.extractLsb' 0 32).signExtend 64 == w then
      (li32Instrs rd (w.extractLsb' 0 32)).map .instr
    else match liShiftAdd? w with
    | some (hi32, sh, lo) =>
      let tail : List Instr := if lo == 0#12 then [] else [.aluImm .addi rd rd lo]
      (li32Instrs rd hi32 ++ [Instr.shImm .slli rd rd sh] ++ tail).map .instr
    | none =>
      let hi32 := w.extractLsb' 32 32
      if hi32 == 0#32 then
        let lo32 := w.extractLsb' 0 32
        (li32Instrs rd lo32 ++ [Instr.shImm .slli rd rd 32#6, Instr.shImm .srli rd rd 32#6]).map .instr
      else
        let c1 : BitVec 12 := (w.extractLsb' 21 11).zeroExtend 12
        let c2 : BitVec 12 := (w.extractLsb' 10 11).zeroExtend 12
        let c3 : BitVec 12 := (w.extractLsb' 0 10).zeroExtend 12
        let step (bits : BitVec 6) (c : BitVec 12) : List Instr :=
          [.shImm .slli rd rd bits] ++ (if c == 0#12 then [] else [.aluImm .addi rd rd c])
        (li32Instrs rd hi32 ++ step 11#6 c1 ++ step 11#6 c2 ++ step 10#6 c3).map .instr

-- Convenience instruction helpers.
namespace Asm

def lbl (name : String) : AsmItem := .label name
def raw (i : Instr) : AsmItem := .instr i
def j (target : String) : AsmItem := .j target
def call (target : String) : AsmItem := .call target
def br (op : BranchOp) (rs1 rs2 : Reg) (target : String) : AsmItem := .br op rs1 rs2 target
def beq (rs1 rs2 : Reg) (target : String) : AsmItem := .br .beq rs1 rs2 target
def bne (rs1 rs2 : Reg) (target : String) : AsmItem := .br .bne rs1 rs2 target
def blt (rs1 rs2 : Reg) (target : String) : AsmItem := .br .blt rs1 rs2 target
def bge (rs1 rs2 : Reg) (target : String) : AsmItem := .br .bge rs1 rs2 target
def bltu (rs1 rs2 : Reg) (target : String) : AsmItem := .br .bltu rs1 rs2 target
def bgeu (rs1 rs2 : Reg) (target : String) : AsmItem := .br .bgeu rs1 rs2 target

def mv (rd rs : Reg) : AsmItem := .instr (.aluImm .addi rd rs 0#12)
def nop : AsmItem := .instr (.aluImm .addi AbiReg.zero AbiReg.zero 0#12)
def ret : AsmItem := .instr (.jalr AbiReg.zero AbiReg.ra 0#12)
def jalr (rd rs1 : Reg) (imm : BitVec 12 := 0#12) : AsmItem := .instr (.jalr rd rs1 imm)

def add (rd rs1 rs2 : Reg) : AsmItem := .instr (.alu .add rd rs1 rs2)
def sub (rd rs1 rs2 : Reg) : AsmItem := .instr (.alu .sub rd rs1 rs2)
def sll (rd rs1 rs2 : Reg) : AsmItem := .instr (.alu .sll rd rs1 rs2)
def slt (rd rs1 rs2 : Reg) : AsmItem := .instr (.alu .slt rd rs1 rs2)
def sltu (rd rs1 rs2 : Reg) : AsmItem := .instr (.alu .sltu rd rs1 rs2)
def xor (rd rs1 rs2 : Reg) : AsmItem := .instr (.alu .xor rd rs1 rs2)
def srl (rd rs1 rs2 : Reg) : AsmItem := .instr (.alu .srl rd rs1 rs2)
def or (rd rs1 rs2 : Reg) : AsmItem := .instr (.alu .or rd rs1 rs2)
def and (rd rs1 rs2 : Reg) : AsmItem := .instr (.alu .and rd rs1 rs2)
def mul (rd rs1 rs2 : Reg) : AsmItem := .instr (.alu .mul rd rs1 rs2)
def mulhu (rd rs1 rs2 : Reg) : AsmItem := .instr (.alu .mulhu rd rs1 rs2)

def addi (rd rs1 : Reg) (imm : BitVec 12) : AsmItem := .instr (.aluImm .addi rd rs1 imm)
def slti (rd rs1 : Reg) (imm : BitVec 12) : AsmItem := .instr (.aluImm .slti rd rs1 imm)
def sltiu (rd rs1 : Reg) (imm : BitVec 12) : AsmItem := .instr (.aluImm .sltiu rd rs1 imm)
def xori (rd rs1 : Reg) (imm : BitVec 12) : AsmItem := .instr (.aluImm .xori rd rs1 imm)
def ori (rd rs1 : Reg) (imm : BitVec 12) : AsmItem := .instr (.aluImm .ori rd rs1 imm)
def andi (rd rs1 : Reg) (imm : BitVec 12) : AsmItem := .instr (.aluImm .andi rd rs1 imm)

def slli (rd rs1 : Reg) (sh : BitVec 6) : AsmItem := .instr (.shImm .slli rd rs1 sh)
def srli (rd rs1 : Reg) (sh : BitVec 6) : AsmItem := .instr (.shImm .srli rd rs1 sh)

def lbu (rd rs1 : Reg) (imm : BitVec 12 := 0#12) : AsmItem := .instr (.load .lbu rd rs1 imm)
def lwu (rd rs1 : Reg) (imm : BitVec 12 := 0#12) : AsmItem := .instr (.load .lwu rd rs1 imm)
def ld (rd rs1 : Reg) (imm : BitVec 12 := 0#12) : AsmItem := .instr (.load .ld rd rs1 imm)

def sw (rs1 rs2 : Reg) (imm : BitVec 12 := 0#12) : AsmItem := .instr (.store .sw rs1 rs2 imm)
def sd (rs1 rs2 : Reg) (imm : BitVec 12 := 0#12) : AsmItem := .instr (.store .sd rs1 rs2 imm)

end Asm

/-! ## Two-Pass Deterministic Linker -/

/-- Association list mapping label names to 32-bit word indices. -/
abbrev LabelMap := List (String × Nat)

def lookupLabel : LabelMap → String → Option Nat
  | [], _ => none
  | (k, v) :: rest, name => if k == name then some v else lookupLabel rest name

/-- Pass 1: collect all label word offsets, failing on duplicate label definitions. -/
def collectLabelsGo (items : List AsmItem) (pc : Nat) (acc : LabelMap) :
    Except String LabelMap :=
  match items with
  | [] => .ok acc
  | item :: rest =>
    match item with
    | .label name =>
      match lookupLabel acc name with
      | some _ => .error s!"duplicate label: {name}"
      | none => collectLabelsGo rest pc ((name, pc) :: acc)
    | _ => collectLabelsGo rest (pc + item.wordSize) acc

def collectLabels (items : List AsmItem) : Except String LabelMap :=
  collectLabelsGo items 0 []

/-- Total emitted words in `items`. -/
def totalWords (items : List AsmItem) : Nat :=
  items.foldl (fun acc item => acc + item.wordSize) 0

/-- Check whether word difference `diffWords` fits in a B-type branch offset (`[-1024, 1023]` words = `[-4096, 4092]` bytes). -/
def branchInRange (diffWords : Int) : Bool :=
  (-1024 ≤ diffWords) && (diffWords ≤ 1023)

/-- Check whether word difference `diffWords` fits in a J-type offset (`[-262144, 262143]` words = `±1 MiB`). -/
def jalInRange (diffWords : Int) : Bool :=
  (-262144 ≤ diffWords) && (diffWords ≤ 262143)

/-- Compute packed 12-bit B-type immediate (`imm[12:1]`) from a signed word difference. -/
def mkBimm (diffWords : Int) : BitVec 12 :=
  BitVec.ofInt 12 (2 * diffWords)

/-- Compute packed 20-bit J-type immediate (`imm[20:1]`) from a signed word difference. -/
def mkJimm (diffWords : Int) : BitVec 20 :=
  BitVec.ofInt 20 (2 * diffWords)

/-- Resolve one `AsmItem` at word index `pc` into concrete `Instr`s. -/
def resolveItem (labels : LabelMap) (pc : Nat) (item : AsmItem) : Except String (List Instr) :=
  match item with
  | .label _ => .ok []
  | .instr inst => .ok [inst]
  | .j target =>
    match lookupLabel labels target with
    | none => .error s!"undefined label: {target}"
    | some tgt =>
      let diff : Int := (tgt : Int) - (pc : Int)
      if jalInRange diff then
        .ok [.jal AbiReg.zero (mkJimm diff)]
      else
        .error s!"jump target out of ±1 MiB range: {target}"
  | .call target =>
    match lookupLabel labels target with
    | none => .error s!"undefined label: {target}"
    | some tgt =>
      let diff : Int := (tgt : Int) - (pc : Int)
      if jalInRange diff then
        .ok [.jal AbiReg.ra (mkJimm diff)]
      else
        .error s!"call target out of ±1 MiB range: {target}"
  | .br op rs1 rs2 target =>
    match lookupLabel labels target with
    | none => .error s!"undefined label: {target}"
    | some tgt =>
      let diff : Int := (tgt : Int) - (pc : Int)
      if branchInRange diff then
        .ok [.branch op rs1 rs2 (mkBimm diff)]
      else
        .error s!"branch target out of ±4 KiB range (unrelaxed): {target}"
  | .brLong op rs1 rs2 target =>
    match lookupLabel labels target with
    | none => .error s!"undefined label: {target}"
    | some tgt =>
      let diff : Int := (tgt : Int) - ((pc + 1 : Nat) : Int)
      if jalInRange diff then
        -- Skip +2 words (+8 bytes) if `!op`, else `jal zero target` from `pc + 1`.
        .ok [.branch (invertBranch op) rs1 rs2 (mkBimm 2), .jal AbiReg.zero (mkJimm diff)]
      else
        .error s!"long-branch target out of ±1 MiB range: {target}"

/-- Pass 2: resolve all `AsmItem`s into an array of `Instr`s. -/
def resolveItemsGo (labels : LabelMap) (pc : Nat) (items : List AsmItem)
    (acc : Array Instr) : Except String (Array Instr) :=
  match items with
  | [] => .ok acc
  | item :: rest => do
    let is ← resolveItem labels pc item
    resolveItemsGo labels (pc + item.wordSize) rest (acc ++ is.toArray)

def resolveItems (labels : LabelMap) (items : List AsmItem) : Except String (Array Instr) :=
  resolveItemsGo labels 0 items #[]

/-- Link an already-relaxed program using two deterministic passes (no veneer insertion). -/
def linkResolved (items : List AsmItem) : Except String (Array (BitVec 32) × LabelMap) := do
  let labels ← collectLabels items
  let instrs ← resolveItems labels items
  return (instrs.map encode, labels)

/-- Single relaxation pass: promote any out-of-range `.br` to `.brLong`.
    Returns `(newItems, changed)`. -/
def relaxStepGo (labels : LabelMap) (pc : Nat) (items : List AsmItem)
    (acc : List AsmItem) (changed : Bool) : Except String (List AsmItem × Bool) :=
  match items with
  | [] => .ok (acc.reverse, changed)
  | item :: rest =>
    match item with
    | .br op rs1 rs2 target =>
      match lookupLabel labels target with
      | none => .error s!"undefined label: {target}"
      | some tgt =>
        let diff : Int := (tgt : Int) - (pc : Int)
        if branchInRange diff then
          relaxStepGo labels (pc + 1) rest (item :: acc) changed
        else
          relaxStepGo labels (pc + 1) rest (.brLong op rs1 rs2 target :: acc) true
    | _ => relaxStepGo labels (pc + item.wordSize) rest (item :: acc) changed

def isShortBr : AsmItem → Bool
  | .br .. => true
  | _ => false

/-- Iteratively relax out-of-range branches to long-branch veneers (`brLong`). -/
def relaxGo (fuel : Nat) (items : List AsmItem) : Except String (List AsmItem) :=
  match fuel with
  | 0 => .ok items
  | fuel + 1 => do
    let labels ← collectLabels items
    let (items', changed) ← relaxStepGo labels 0 items [] false
    if changed then relaxGo fuel items' else .ok items'

def relax (items : List AsmItem) : Except String (List AsmItem) :=
  relaxGo (items.length + 1) items

/-- Full linker: relax out-of-range branches, then run the two-pass deterministic linker. -/
def linkWithLabels (items : List AsmItem) : Except String (Array (BitVec 32) × LabelMap) := do
  let relaxed ← relax items
  linkResolved relaxed

def link (items : List AsmItem) : Except String (Array (BitVec 32)) :=
  (linkWithLabels items).map Prod.fst

end ConAgua.RISCV.Compiler
