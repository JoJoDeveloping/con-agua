import Std.Data.HashMap
import ConAgua.RISCV.RV64.Encode
import ConAgua.RISCV.RV64.Semantics
import ConAgua.RISCV.Compiler.Asm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Fast Single-Pass `±2 GiB` Far Linker (`ConAgua.RISCV.Linker.FarLink`)

Provides a constant-size, O(N) tail-recursive symbolic linker (`linkFar`) for
`List ConAgua.RISCV.Compiler.AsmItem` supporting up to `±2 GiB` (`[-2^29, 2^29 - 513]` words)
jumps, calls, and conditional branches without `AUIPC`, via
`jal t6, +4; lui s1, hi20; add t6, t6, s1; jalr rd, t6, lo12`.

- **Zero modification** to `ConAgua.RISCV.Compiler.Asm` (`AsmItem`).
- **ABI safety:** `ConAgua.RISCV.Compiler.Compile` never keeps `AbiReg.t6` (`x31`)
  or `AbiReg.s1` (`x9`) live across `.j`, `.call`, `.br`, or `.brLong` (and `s1` is saved/restored
  at entry/exit by `callerSaveAsm` / `callerRestoreRetAsm`). On branches,
  `branch (invertBranch op) rs1 rs2 (+20)` reads `rs1`/`rs2` *before* `jal t6` runs (and untaken
  branches do not touch `t6` or `s1`).
- **Dual Layer (Spec + Fast Execution):**
  - `linkFarSpec` / `collectFarLabels` / `resolveFarItems` use `LabelMap` (`List (String × Nat)`),
    matching `AsmProof.lean` cleanly.
  - `linkFar` / `linkFarWithMap` use `Std.HashMap String Nat` and `Array.push` in strict
    tail recursion, running in well under 1s on 600,000+ `AsmItem`s and 35,000+ labels,
    proven extensionally equivalent to `linkFarSpec` (`linkFar_eq_linkFarSpec`).
-/

namespace ConAgua.RISCV.Linker

open ConAgua.RISCV.RV64
open ConAgua.RISCV.Compiler

/-! ## 1. Fixed Word Sizes & `±2 GiB` Offset Splitting -/

/-- Fixed number of 32-bit machine words emitted by `linkFar` for one `AsmItem`. -/
def farWordSize : AsmItem → Nat
  | .label _   => 0
  | .instr _   => 1
  | .j _       => 4
  | .call _    => 4
  | .br ..     => 5
  | .brLong .. => 5

/-- Total emitted 32-bit words under `linkFar`. -/
def farTotalWords (items : List AsmItem) : Nat :=
  items.foldl (fun acc item => acc + farWordSize item) 0

/-- Check whether word difference `diffWords` fits in signed 32-bit `lui + jalr` range
    (`[-2^29, 2^29 - 513]` words = `[-2^31, 2^31 - 2052]` bytes, avoiding `hi20` sign wrap at `+2^31 - 2048`). -/
def farInRange (diffWords : Int) : Bool :=
  (-(2 ^ 29 : Int) ≤ diffWords) && (diffWords ≤ 2 ^ 29 - 513)

/-- Split a word offset `diffWords` into `(hi20, lo12)` for `jal t6, +4; lui s1, hi20; add t6, t6, s1; jalr rd, t6, lo12`. -/
def splitFarOffWords (diffWords : Int) : BitVec 20 × BitVec 12 :=
  let off32 : BitVec 32 := BitVec.ofInt 32 (4 * diffWords)
  let lo12 : BitVec 12 := off32.extractLsb' 0 12
  let hi20 : BitVec 20 := (off32 + 0x800#32).extractLsb' 12 20
  (hi20, lo12)

/-- Lower `.j` / `.call` / `.br` / `.brLong` or raw `.instr` given resolved `tgt` word index. -/
def farInstrsFor (pc tgt : Nat) : AsmItem → List Instr
  | .label _ => []
  | .instr inst => [inst]
  | .j _ =>
    let (hi20, lo12) := splitFarOffWords ((tgt : Int) - ((pc + 1 : Nat) : Int))
    [.jal AbiReg.t6 (mkJimm 1),
     .lui AbiReg.s1 hi20,
     .alu .add AbiReg.t6 AbiReg.t6 AbiReg.s1,
     .jalr AbiReg.zero AbiReg.t6 lo12]
  | .call _ =>
    let (hi20, lo12) := splitFarOffWords ((tgt : Int) - ((pc + 1 : Nat) : Int))
    [.jal AbiReg.t6 (mkJimm 1),
     .lui AbiReg.s1 hi20,
     .alu .add AbiReg.t6 AbiReg.t6 AbiReg.s1,
     .jalr AbiReg.ra AbiReg.t6 lo12]
  | .br op rs1 rs2 _ =>
    let (hi20, lo12) := splitFarOffWords ((tgt : Int) - ((pc + 2 : Nat) : Int))
    [.branch (invertBranch op) rs1 rs2 (mkBimm 5),
     .jal AbiReg.t6 (mkJimm 1),
     .lui AbiReg.s1 hi20,
     .alu .add AbiReg.t6 AbiReg.t6 AbiReg.s1,
     .jalr AbiReg.zero AbiReg.t6 lo12]
  | .brLong op rs1 rs2 _ =>
    let (hi20, lo12) := splitFarOffWords ((tgt : Int) - ((pc + 2 : Nat) : Int))
    [.branch (invertBranch op) rs1 rs2 (mkBimm 5),
     .jal AbiReg.t6 (mkJimm 1),
     .lui AbiReg.s1 hi20,
     .alu .add AbiReg.t6 AbiReg.t6 AbiReg.s1,
     .jalr AbiReg.zero AbiReg.t6 lo12]

/-! ## 2. Pure `LabelMap` Specification (`collectFarLabels` / `resolveFarItems` / `linkFarSpec`) -/

def collectFarLabelsGo (items : List AsmItem) (pc : Nat) (acc : LabelMap) :
    Except String LabelMap :=
  match items with
  | [] => .ok acc
  | item :: rest =>
    match item with
    | .label name =>
      match lookupLabel acc name with
      | some _ => .error s!"duplicate label: {name}"
      | none => collectFarLabelsGo rest pc ((name, pc) :: acc)
    | _ => collectFarLabelsGo rest (pc + farWordSize item) acc

def collectFarLabels (items : List AsmItem) : Except String LabelMap :=
  collectFarLabelsGo items 0 []

def resolveFarItem (labels : LabelMap) (pc : Nat) (item : AsmItem) : Except String (List Instr) :=
  match item with
  | .label _ => .ok []
  | .instr inst => .ok [inst]
  | .j target =>
    match lookupLabel labels target with
    | none => .error s!"undefined label: {target}"
    | some tgt =>
      let diff : Int := (tgt : Int) - ((pc + 1 : Nat) : Int)
      if farInRange diff then .ok (farInstrsFor pc tgt (.j target))
      else .error s!"far jump target out of ±2 GiB range: {target}"
  | .call target =>
    match lookupLabel labels target with
    | none => .error s!"undefined label: {target}"
    | some tgt =>
      let diff : Int := (tgt : Int) - ((pc + 1 : Nat) : Int)
      if farInRange diff then .ok (farInstrsFor pc tgt (.call target))
      else .error s!"far call target out of ±2 GiB range: {target}"
  | .br op rs1 rs2 target =>
    match lookupLabel labels target with
    | none => .error s!"undefined label: {target}"
    | some tgt =>
      let diff : Int := (tgt : Int) - ((pc + 2 : Nat) : Int)
      if farInRange diff then .ok (farInstrsFor pc tgt (.br op rs1 rs2 target))
      else .error s!"far branch target out of ±2 GiB range: {target}"
  | .brLong op rs1 rs2 target =>
    match lookupLabel labels target with
    | none => .error s!"undefined label: {target}"
    | some tgt =>
      let diff : Int := (tgt : Int) - ((pc + 2 : Nat) : Int)
      if farInRange diff then .ok (farInstrsFor pc tgt (.brLong op rs1 rs2 target))
      else .error s!"far long-branch target out of ±2 GiB range: {target}"

@[inline] def pushEncoded (acc : Array (BitVec 32)) : List Instr → Array (BitVec 32)
  | [] => acc
  | i :: is => pushEncoded (acc.push (encode i)) is

def resolveFarWordsGo (labels : LabelMap) (pc : Nat) (items : List AsmItem)
    (acc : Array (BitVec 32)) : Except String (Array (BitVec 32)) :=
  match items with
  | [] => .ok acc
  | item :: rest =>
    match resolveFarItem labels pc item with
    | .error e => .error e
    | .ok is => resolveFarWordsGo labels (pc + farWordSize item) rest (pushEncoded acc is)

def toFarItemsGo (labels : LabelMap) (pc : Nat) (items : List AsmItem)
    (acc : Array Instr) : Except String (Array Instr) :=
  match items with
  | [] => .ok acc
  | item :: rest =>
    match resolveFarItem labels pc item with
    | .error e => .error e
    | .ok is => toFarItemsGo labels (pc + farWordSize item) rest (is.foldl Array.push acc)

def toFarItems (items : List AsmItem) : Except String (Array Instr) := do
  let labels ← collectFarLabels items
  toFarItemsGo labels 0 items #[]

def linkFarSpec (items : List AsmItem) : Except String (Array (BitVec 32) × LabelMap) := do
  let labels ← collectFarLabels items
  let words ← resolveFarWordsGo labels 0 items #[]
  return (words, labels)

/-! ## 3. Fast O(N) Tail-Recursive `Std.HashMap` Execution Linker (`linkFar`) -/

def collectFarLabelsFastGo (items : List AsmItem) (pc : Nat)
    (acc : Std.HashMap String Nat) : Except String (Std.HashMap String Nat) :=
  match items with
  | [] => .ok acc
  | item :: rest =>
    match item with
    | .label name =>
      match acc[name]? with
      | some _ => .error s!"duplicate label: {name}"
      | none => collectFarLabelsFastGo rest pc (acc.insert name pc)
    | _ => collectFarLabelsFastGo rest (pc + farWordSize item) acc

def collectFarLabelsFast (items : List AsmItem) : Except String (Std.HashMap String Nat) :=
  collectFarLabelsFastGo items 0 ∅

def resolveFarItemFast (labels : Std.HashMap String Nat) (pc : Nat) (item : AsmItem) :
    Except String (List Instr) :=
  match item with
  | .label _ => .ok []
  | .instr inst => .ok [inst]
  | .j target =>
    match labels[target]? with
    | none => .error s!"undefined label: {target}"
    | some tgt =>
      let diff : Int := (tgt : Int) - ((pc + 1 : Nat) : Int)
      if farInRange diff then .ok (farInstrsFor pc tgt (.j target))
      else .error s!"far jump target out of ±2 GiB range: {target}"
  | .call target =>
    match labels[target]? with
    | none => .error s!"undefined label: {target}"
    | some tgt =>
      let diff : Int := (tgt : Int) - ((pc + 1 : Nat) : Int)
      if farInRange diff then .ok (farInstrsFor pc tgt (.call target))
      else .error s!"far call target out of ±2 GiB range: {target}"
  | .br op rs1 rs2 target =>
    match labels[target]? with
    | none => .error s!"undefined label: {target}"
    | some tgt =>
      let diff : Int := (tgt : Int) - ((pc + 2 : Nat) : Int)
      if farInRange diff then .ok (farInstrsFor pc tgt (.br op rs1 rs2 target))
      else .error s!"far branch target out of ±2 GiB range: {target}"
  | .brLong op rs1 rs2 target =>
    match labels[target]? with
    | none => .error s!"undefined label: {target}"
    | some tgt =>
      let diff : Int := (tgt : Int) - ((pc + 2 : Nat) : Int)
      if farInRange diff then .ok (farInstrsFor pc tgt (.brLong op rs1 rs2 target))
      else .error s!"far long-branch target out of ±2 GiB range: {target}"

def resolveFarWordsFastGo (labels : Std.HashMap String Nat) (pc : Nat) (items : List AsmItem)
    (acc : Array (BitVec 32)) : Except String (Array (BitVec 32)) :=
  match items with
  | [] => .ok acc
  | item :: rest =>
    match resolveFarItemFast labels pc item with
    | .error e => .error e
    | .ok is => resolveFarWordsFastGo labels (pc + farWordSize item) rest (pushEncoded acc is)

/-- Link `items` with the fast O(N) `Std.HashMap` pass, returning words and label map. -/
def linkFarWithMap (items : List AsmItem) :
    Except String (Array (BitVec 32) × Std.HashMap String Nat) := do
  let labels ← collectFarLabelsFast items
  let words ← resolveFarWordsFastGo labels 0 items #[]
  return (words, labels)

/-- Fast single-pass `±2 GiB` linker replacing `ConAgua.RISCV.Compiler.link` for large programs. -/
def linkFar (items : List AsmItem) : Except String (Array (BitVec 32)) := do
  let (words, _) ← linkFarWithMap items
  return words

/-! ## 4. Extensional Equivalence Between Fast `Std.HashMap` and `LabelMap` Spec -/

def MapAgree (hm : Std.HashMap String Nat) (lm : LabelMap) : Prop :=
  ∀ s, hm[s]? = lookupLabel lm s

private theorem mapAgree_empty : MapAgree (∅ : Std.HashMap String Nat) [] := by
  intro s
  simp [lookupLabel]

private theorem mapAgree_insert {hm : Std.HashMap String Nat} {lm : LabelMap}
    (h : MapAgree hm lm) (k : String) (v : Nat) :
    MapAgree (hm.insert k v) ((k, v) :: lm) := by
  intro s
  rw [Std.HashMap.getElem?_insert]
  simp only [lookupLabel, h s]

private theorem collectFarLabelsFastGo_eq (items : List AsmItem) (pc : Nat)
    (hm : Std.HashMap String Nat) (lm : LabelMap) (hag : MapAgree hm lm) :
    (∀ hm', collectFarLabelsFastGo items pc hm = .ok hm' →
      ∃ lm', collectFarLabelsGo items pc lm = .ok lm' ∧ MapAgree hm' lm') ∧
    (∀ e, collectFarLabelsFastGo items pc hm = .error e →
      collectFarLabelsGo items pc lm = .error e) := by
  induction items generalizing pc hm lm with
  | nil =>
    simp only [collectFarLabelsFastGo, collectFarLabelsGo, Except.ok.injEq]
    constructor
    · intro hm' h; subst h; exact ⟨lm, rfl, hag⟩
    · intro e h; cases h
  | cons item rest ih =>
    cases item with
    | label name =>
      simp only [collectFarLabelsFastGo, collectFarLabelsGo]
      have hlook : hm[name]? = lookupLabel lm name := hag name
      cases hl : lookupLabel lm name with
      | some v =>
        have hf : hm[name]? = some v := hlook.trans hl
        simp only [hf]
        exact ⟨(fun hm' h => by cases h), (fun e h => by cases h; rfl)⟩
      | none =>
        have hf : hm[name]? = none := hlook.trans hl
        simp only [hf]
        exact ih pc (hm.insert name pc) ((name, pc) :: lm) (mapAgree_insert hag name pc)
    | _ => exact ih (pc + farWordSize _) hm lm hag

private theorem resolveFarItemFast_eq {hm : Std.HashMap String Nat} {lm : LabelMap}
    (hag : MapAgree hm lm) (pc : Nat) (item : AsmItem) :
    resolveFarItemFast hm pc item = resolveFarItem lm pc item := by
  cases item <;> simp only [resolveFarItemFast, resolveFarItem]
  all_goals
    rename_i target
    rw [hag target]

private theorem resolveFarWordsFastGo_eq {hm : Std.HashMap String Nat} {lm : LabelMap}
    (hag : MapAgree hm lm) (pc : Nat) (items : List AsmItem) (acc : Array (BitVec 32)) :
    resolveFarWordsFastGo hm pc items acc = resolveFarWordsGo lm pc items acc := by
  induction items generalizing pc acc with
  | nil => rfl
  | cons item rest ih =>
    simp only [resolveFarWordsFastGo, resolveFarWordsGo, resolveFarItemFast_eq hag pc item]
    cases resolveFarItem lm pc item with
    | error e => rfl
    | ok is => exact ih (pc + farWordSize item) (pushEncoded acc is)

/-- Exact functional equivalence: fast `Std.HashMap` `linkFarWithMap` succeeds iff `linkFarSpec`
    succeeds, producing the exact same `Array (BitVec 32)`, error, and point-wise equivalent label maps. -/
theorem linkFarWithMap_eq_linkFarSpec (items : List AsmItem) :
    (∀ words hm, linkFarWithMap items = .ok (words, hm) →
      ∃ lm, linkFarSpec items = .ok (words, lm) ∧ MapAgree hm lm) ∧
    (∀ e, linkFarWithMap items = .error e →
      linkFarSpec items = .error e) := by
  simp only [linkFarWithMap, linkFarSpec, bind, Except.bind, collectFarLabelsFast, collectFarLabels]
  have hcol := collectFarLabelsFastGo_eq items 0 ∅ [] mapAgree_empty
  constructor
  · intro words hm h
    cases hf : collectFarLabelsFastGo items 0 ∅ with
    | error e => rw [hf] at h; cases h
    | ok hm' =>
      rw [hf] at h
      dsimp only at h
      obtain ⟨lm', hlm', hag⟩ := hcol.1 hm' hf
      rw [resolveFarWordsFastGo_eq hag] at h
      rw [hlm']
      dsimp only
      cases hr : resolveFarWordsGo lm' 0 items #[] with
      | error e => rw [hr] at h; cases h
      | ok ws =>
        rw [hr] at h
        simp only [Except.pure, pure, Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact ⟨lm', rfl, hag⟩
  · intro e h
    cases hf : collectFarLabelsFastGo items 0 ∅ with
    | error e1 =>
      rw [hf] at h
      rw [hcol.2 e1 hf]
      dsimp only at h ⊢
      cases h; rfl
    | ok hm' =>
      rw [hf] at h
      dsimp only at h
      obtain ⟨lm', hlm', hag⟩ := hcol.1 hm' hf
      rw [resolveFarWordsFastGo_eq hag] at h
      rw [hlm']
      dsimp only
      cases hr : resolveFarWordsGo lm' 0 items #[] with
      | error e2 => simp only [hr] at h ⊢; cases h; rfl
      | ok ws => rw [hr] at h; cases h

/-- If fast `linkFar items = .ok words`, then pure `linkFarSpec items = .ok (words, lm)`. -/
theorem linkFar_ok_spec {items : List AsmItem} {words : Array (BitVec 32)}
    (h : linkFar items = .ok words) :
    ∃ lm, linkFarSpec items = .ok (words, lm) := by
  simp only [linkFar, bind, Except.bind] at h
  cases hw : linkFarWithMap items with
  | error e => rw [hw] at h; cases h
  | ok p =>
    rw [hw] at h
    simp only [Except.pure, pure, Except.ok.injEq] at h
    subst h
    obtain ⟨lm, hspec, _⟩ := (linkFarWithMap_eq_linkFarSpec items).1 p.1 p.2 hw
    exact ⟨lm, hspec⟩

/-- Fast `linkFar` equals pure `(linkFarSpec items).map Prod.fst`. -/
theorem linkFar_eq_linkFarSpec (items : List AsmItem) :
    linkFar items = (linkFarSpec items).map Prod.fst := by
  simp only [linkFar, bind, Except.bind, Except.map]
  cases hw : linkFarWithMap items with
  | ok p =>
    obtain ⟨lm, hspec, _⟩ := (linkFarWithMap_eq_linkFarSpec items).1 p.1 p.2 hw
    rw [hspec]; rfl
  | error e =>
    have hspec := (linkFarWithMap_eq_linkFarSpec items).2 e hw
    rw [hspec]

end ConAgua.RISCV.Linker
