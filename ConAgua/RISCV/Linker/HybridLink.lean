import Std.Data.HashMap
import ConAgua.RISCV.RV64.Roundtrip
import ConAgua.RISCV.Compiler.AsmProof
import ConAgua.RISCV.Linker.FarLink
import ConAgua.RISCV.Linker.FarLinkProof
import ConAgua.RISCV.Linker.LinkModel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Translation-Validated Hybrid Near/Mid/Far Linker (`ConAgua.RISCV.Linker.HybridLink`)

Selects the shortest legal RV64 encoding for every jump/call/branch in a `List AsmItem`
per target label so that `itemSize : AsmItem → Nat` remains purely context-free and drops
directly behind `ConAgua.RISCV.Linker.LinkModel`:

- `.j target`:
  - `1` word: `jal x0, imm20` (`±1 MiB`, `jalInRange`)
  - `4` words: `jal t6, +4; lui s1, hi20; add t6, t6, s1; jalr x0, t6, lo12` (`±2 GiB`, `farInRange`)
- `.call target`:
  - `1` word: `jal ra, imm20` (`±1 MiB`, `jalInRange`)
  - `4` words: `jal t6, +4; lui s1, hi20; add t6, t6, s1; jalr ra, t6, lo12` (`±2 GiB`, `farInRange`)
- `.br` / `.brLong`:
  - `1` word (`w1`): `b<op> rs1, rs2, imm12` (`±4 KiB`, `branchInRange`)
  - `2` words (`w2`): `b<!op> rs1, rs2, +8; jal x0, imm20` (`±1 MiB`, `jalInRange`)
  - `5` words (`w3`): `b<!op> rs1, rs2, +20; jal t6, +4; lui s1, hi20; add t6, t6, s1; jalr x0, t6, lo12` (`±2 GiB`, `farInRange`)

An unverified optimistic relaxation loop (`relaxGo`) computes a candidate width table
`HybridWidths`, which is then checked by a simple boolean validator `validateHybridGo`.
If validation fails for any reason, it falls back to `HybridWidths.allFar`, which is
definitionally equal to `FarLink.linkFar`. Hence kernel soundness holds symbolically
for **every** well-formed program without evaluating `relaxGo` inside the Lean kernel.

All proofs use strictly `[propext, Classical.choice, Quot.sound]` — zero `sorry`,
zero `native_decide`, zero `bv_decide`.
-/

namespace ConAgua.RISCV.Linker

open ConAgua.RISCV.RV64
open ConAgua.RISCV.Compiler

/-! ## 1. Per-Target Width Table & Lowering -/

inductive BrWidth where
  | w1 | w2 | w3
  deriving DecidableEq, Repr

/-- Per-target width assignment for `linkHybridWith`. When `allFar = true`, every
    item uses its worst-case `farWordSize` (`j=4, call=4, br=5`), identical to `linkFar`. -/
structure HybridWidths where
  allFar : Bool := false
  jFar   : Std.HashMap String Unit := ∅
  cFar   : Std.HashMap String Unit := ∅
  /-- Missing ⇒ `w1` (`1w Bcc`), `some false` ⇒ `w2` (`2w B!cc+JAL`), `some true` ⇒ `w3` (`5w`). -/
  bKind  : Std.HashMap String Bool := ∅

def HybridWidths.allNear : HybridWidths := {}

def HybridWidths.mkAllFar : HybridWidths := { allFar := true }

@[inline] def HybridWidths.getJ (hw : HybridWidths) (t : String) : Bool :=
  hw.allFar || hw.jFar.contains t

@[inline] def HybridWidths.getC (hw : HybridWidths) (t : String) : Bool :=
  hw.allFar || hw.cFar.contains t

@[inline] def HybridWidths.getB (hw : HybridWidths) (t : String) : BrWidth :=
  if hw.allFar then .w3
  else match hw.bKind[t]? with
    | none       => .w1
    | some false => .w2
    | some true  => .w3

/-- Word count emitted for one `AsmItem` under width assignment `hw`. -/
def hybridWordSize (hw : HybridWidths) : AsmItem → Nat
  | .label _          => 0
  | .instr _          => 1
  | .j t              => if hw.getJ t then 4 else 1
  | .call t           => if hw.getC t then 4 else 1
  | .br _ _ _ t       => match hw.getB t with | .w1 => 1 | .w2 => 2 | .w3 => 5
  | .brLong _ _ _ t   => match hw.getB t with | .w1 => 1 | .w2 => 2 | .w3 => 5

theorem hybridWordSize_le_far (hw : HybridWidths) (item : AsmItem) :
    hybridWordSize hw item ≤ farWordSize item := by
  cases item with
  | label _ => simp [hybridWordSize, farWordSize]
  | instr _ => simp [hybridWordSize, farWordSize]
  | j t => dsimp [hybridWordSize, farWordSize]; split <;> omega
  | «call» t => dsimp [hybridWordSize, farWordSize]; split <;> omega
  | br _ _ _ t => dsimp [hybridWordSize, farWordSize]; split <;> omega
  | brLong _ _ _ t => dsimp [hybridWordSize, farWordSize]; split <;> omega

theorem hybridWordSize_allFar (item : AsmItem) :
    hybridWordSize HybridWidths.mkAllFar item = farWordSize item := by
  cases item <;> simp [hybridWordSize, farWordSize, HybridWidths.mkAllFar,
    HybridWidths.getJ, HybridWidths.getC, HybridWidths.getB]

/-- Tail-recursive total word count under `hw`. -/
def hybridTotalWords (hw : HybridWidths) (items : List AsmItem) : Nat :=
  items.foldl (fun acc item => acc + hybridWordSize hw item) 0

private theorem foldl_hybrid_add (hw : HybridWidths) (xs : List AsmItem) (n : Nat) :
    xs.foldl (fun acc item => acc + hybridWordSize hw item) n =
      n + xs.foldl (fun acc item => acc + hybridWordSize hw item) 0 := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (n + hybridWordSize hw x), ih (hybridWordSize hw x), Nat.add_assoc]

theorem hybridTotalWords_nil (hw : HybridWidths) : hybridTotalWords hw [] = 0 := rfl

theorem hybridTotalWords_cons (hw : HybridWidths) (x : AsmItem) (xs : List AsmItem) :
    hybridTotalWords hw (x :: xs) = hybridWordSize hw x + hybridTotalWords hw xs := by
  unfold hybridTotalWords
  simp only [List.foldl_cons, Nat.zero_add]
  exact foldl_hybrid_add hw xs (hybridWordSize hw x)

theorem hybridTotalWords_append (hw : HybridWidths) (xs ys : List AsmItem) :
    hybridTotalWords hw (xs ++ ys) = hybridTotalWords hw xs + hybridTotalWords hw ys := by
  induction xs with
  | nil => simp [hybridTotalWords_nil]
  | cons x xs ih =>
    simp only [List.cons_append, hybridTotalWords_cons, ih, Nat.add_assoc]

theorem totalSizeWith_hybrid_eq (hw : HybridWidths) (xs : List AsmItem) :
    totalSizeWith (hybridWordSize hw) xs = hybridTotalWords hw xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [totalSizeWith, List.map_cons, List.sum_cons, hybridTotalWords_cons] at ih ⊢
    rw [ih]

theorem hybridTotalWords_le_far (hw : HybridWidths) (xs : List AsmItem) :
    hybridTotalWords hw xs ≤ farTotalWords xs := by
  induction xs with
  | nil => simp [hybridTotalWords_nil, farTotalWords]
  | cons x xs ih =>
    rw [hybridTotalWords_cons, farTotalWords_cons]
    have h := hybridWordSize_le_far hw x
    omega

theorem hybridTotalWords_allFar (xs : List AsmItem) :
    hybridTotalWords HybridWidths.mkAllFar xs = farTotalWords xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [hybridTotalWords_cons, farTotalWords_cons, hybridWordSize_allFar, ih]

private def branchInstrsFor (bw : BrWidth) (op : BranchOp) (rs1 rs2 : Reg) (pc tgt : Nat) :
    List Instr :=
  match bw with
  | .w1 =>
    [.branch op rs1 rs2 (mkBimm ((tgt : Int) - (pc : Int)))]
  | .w2 =>
    [.branch (invertBranch op) rs1 rs2 (mkBimm 2),
     .jal AbiReg.zero (mkJimm ((tgt : Int) - ((pc + 1 : Nat) : Int)))]
  | .w3 =>
    let (hi20, lo12) := splitFarOffWords ((tgt : Int) - ((pc + 2 : Nat) : Int))
    [.branch (invertBranch op) rs1 rs2 (mkBimm 5),
     .jal AbiReg.t6 (mkJimm 1),
     .lui AbiReg.s1 hi20,
     .alu .add AbiReg.t6 AbiReg.t6 AbiReg.s1,
     .jalr AbiReg.zero AbiReg.t6 lo12]

private def resolveBrWith (bw : BrWidth) (op : BranchOp) (rs1 rs2 : Reg) (target : String)
    (pc tgt : Nat) : Except String (List Instr) :=
  match bw with
  | .w1 =>
    if branchInRange ((tgt : Int) - (pc : Int)) then
      .ok (branchInstrsFor .w1 op rs1 rs2 pc tgt)
    else .error s!"hybrid branch out of ±4 KiB range: {target}"
  | .w2 =>
    if jalInRange ((tgt : Int) - ((pc + 1 : Nat) : Int)) then
      .ok (branchInstrsFor .w2 op rs1 rs2 pc tgt)
    else .error s!"hybrid mid-branch out of ±1 MiB range: {target}"
  | .w3 =>
    if farInRange ((tgt : Int) - ((pc + 2 : Nat) : Int)) then
      .ok (branchInstrsFor .w3 op rs1 rs2 pc tgt)
    else .error s!"hybrid far-branch out of ±2 GiB range: {target}"

/-! ## 2. Pure `LabelMap` Spec Layer -/

def collectHybridLabelsGo (hw : HybridWidths) (items : List AsmItem) (pc : Nat) (acc : LabelMap) :
    Except String LabelMap :=
  match items with
  | [] => .ok acc
  | item :: rest =>
    match item with
    | .label name =>
      match lookupLabel acc name with
      | some _ => .error s!"duplicate label: {name}"
      | none => collectHybridLabelsGo hw rest pc ((name, pc) :: acc)
    | _ => collectHybridLabelsGo hw rest (pc + hybridWordSize hw item) acc

def collectHybridLabels (hw : HybridWidths) (items : List AsmItem) : Except String LabelMap :=
  collectHybridLabelsGo hw items 0 []

def resolveHybridItem (hw : HybridWidths) (labels : LabelMap) (pc : Nat) (item : AsmItem) :
    Except String (List Instr) :=
  match item with
  | .label _ => .ok []
  | .instr inst => .ok [inst]
  | .j target =>
    match lookupLabel labels target with
    | none => .error s!"undefined label: {target}"
    | some tgt =>
      if hw.getJ target then
        let diff : Int := (tgt : Int) - ((pc + 1 : Nat) : Int)
        if farInRange diff then
          let (hi20, lo12) := splitFarOffWords diff
          .ok [.jal AbiReg.t6 (mkJimm 1),
               .lui AbiReg.s1 hi20,
               .alu .add AbiReg.t6 AbiReg.t6 AbiReg.s1,
               .jalr AbiReg.zero AbiReg.t6 lo12]
        else .error s!"far jump target out of ±2 GiB range: {target}"
      else
        let diff : Int := (tgt : Int) - (pc : Int)
        if jalInRange diff then .ok [.jal AbiReg.zero (mkJimm diff)]
        else .error s!"near jump target out of ±1 MiB range: {target}"
  | .call target =>
    match lookupLabel labels target with
    | none => .error s!"undefined label: {target}"
    | some tgt =>
      if hw.getC target then
        let diff : Int := (tgt : Int) - ((pc + 1 : Nat) : Int)
        if farInRange diff then
          let (hi20, lo12) := splitFarOffWords diff
          .ok [.jal AbiReg.t6 (mkJimm 1),
               .lui AbiReg.s1 hi20,
               .alu .add AbiReg.t6 AbiReg.t6 AbiReg.s1,
               .jalr AbiReg.ra AbiReg.t6 lo12]
        else .error s!"far call target out of ±2 GiB range: {target}"
      else
        let diff : Int := (tgt : Int) - (pc : Int)
        if jalInRange diff then .ok [.jal AbiReg.ra (mkJimm diff)]
        else .error s!"near call target out of ±1 MiB range: {target}"
  | .br op rs1 rs2 target =>
    match lookupLabel labels target with
    | none => .error s!"undefined label: {target}"
    | some tgt => resolveBrWith (hw.getB target) op rs1 rs2 target pc tgt
  | .brLong op rs1 rs2 target =>
    match lookupLabel labels target with
    | none => .error s!"undefined label: {target}"
    | some tgt => resolveBrWith (hw.getB target) op rs1 rs2 target pc tgt

def resolveHybridWordsGo (hw : HybridWidths) (labels : LabelMap) (pc : Nat)
    (items : List AsmItem) (acc : Array (BitVec 32)) : Except String (Array (BitVec 32)) :=
  match items with
  | [] => .ok acc
  | item :: rest =>
    match resolveHybridItem hw labels pc item with
    | .error e => .error e
    | .ok is =>
      resolveHybridWordsGo hw labels (pc + hybridWordSize hw item) rest (pushEncoded acc is)

def linkHybridWithSpec (hw : HybridWidths) (items : List AsmItem) :
    Except String (Array (BitVec 32) × LabelMap) := do
  let labels ← collectHybridLabels hw items
  let words ← resolveHybridWordsGo hw labels 0 items #[]
  return (words, labels)

/-! ## 3. Fast O(N) `Std.HashMap` Execution Layer -/

def collectHybridLabelsFastGo (hw : HybridWidths) (items : List AsmItem) (pc : Nat)
    (acc : Std.HashMap String Nat) : Except String (Std.HashMap String Nat) :=
  match items with
  | [] => .ok acc
  | item :: rest =>
    match item with
    | .label name =>
      match acc[name]? with
      | some _ => .error s!"duplicate label: {name}"
      | none => collectHybridLabelsFastGo hw rest pc (acc.insert name pc)
    | _ => collectHybridLabelsFastGo hw rest (pc + hybridWordSize hw item) acc

def collectHybridLabelsFast (hw : HybridWidths) (items : List AsmItem) :
    Except String (Std.HashMap String Nat) :=
  collectHybridLabelsFastGo hw items 0 ∅

def resolveHybridItemFast (hw : HybridWidths) (labels : Std.HashMap String Nat) (pc : Nat)
    (item : AsmItem) : Except String (List Instr) :=
  match item with
  | .label _ => .ok []
  | .instr inst => .ok [inst]
  | .j target =>
    match labels[target]? with
    | none => .error s!"undefined label: {target}"
    | some tgt =>
      if hw.getJ target then
        let diff : Int := (tgt : Int) - ((pc + 1 : Nat) : Int)
        if farInRange diff then
          let (hi20, lo12) := splitFarOffWords diff
          .ok [.jal AbiReg.t6 (mkJimm 1),
               .lui AbiReg.s1 hi20,
               .alu .add AbiReg.t6 AbiReg.t6 AbiReg.s1,
               .jalr AbiReg.zero AbiReg.t6 lo12]
        else .error s!"far jump target out of ±2 GiB range: {target}"
      else
        let diff : Int := (tgt : Int) - (pc : Int)
        if jalInRange diff then .ok [.jal AbiReg.zero (mkJimm diff)]
        else .error s!"near jump target out of ±1 MiB range: {target}"
  | .call target =>
    match labels[target]? with
    | none => .error s!"undefined label: {target}"
    | some tgt =>
      if hw.getC target then
        let diff : Int := (tgt : Int) - ((pc + 1 : Nat) : Int)
        if farInRange diff then
          let (hi20, lo12) := splitFarOffWords diff
          .ok [.jal AbiReg.t6 (mkJimm 1),
               .lui AbiReg.s1 hi20,
               .alu .add AbiReg.t6 AbiReg.t6 AbiReg.s1,
               .jalr AbiReg.ra AbiReg.t6 lo12]
        else .error s!"far call target out of ±2 GiB range: {target}"
      else
        let diff : Int := (tgt : Int) - (pc : Int)
        if jalInRange diff then .ok [.jal AbiReg.ra (mkJimm diff)]
        else .error s!"near call target out of ±1 MiB range: {target}"
  | .br op rs1 rs2 target =>
    match labels[target]? with
    | none => .error s!"undefined label: {target}"
    | some tgt => resolveBrWith (hw.getB target) op rs1 rs2 target pc tgt
  | .brLong op rs1 rs2 target =>
    match labels[target]? with
    | none => .error s!"undefined label: {target}"
    | some tgt => resolveBrWith (hw.getB target) op rs1 rs2 target pc tgt

def resolveHybridWordsFastGo (hw : HybridWidths) (labels : Std.HashMap String Nat) (pc : Nat)
    (items : List AsmItem) (acc : Array (BitVec 32)) : Except String (Array (BitVec 32)) :=
  match items with
  | [] => .ok acc
  | item :: rest =>
    match resolveHybridItemFast hw labels pc item with
    | .error e => .error e
    | .ok is =>
      resolveHybridWordsFastGo hw labels (pc + hybridWordSize hw item) rest (pushEncoded acc is)

def linkHybridWithMap (hw : HybridWidths) (items : List AsmItem) :
    Except String (Array (BitVec 32) × Std.HashMap String Nat) := do
  let labels ← collectHybridLabelsFast hw items
  let words ← resolveHybridWordsFastGo hw labels 0 items #[]
  return (words, labels)

def linkHybridWith (hw : HybridWidths) (items : List AsmItem) :
    Except String (Array (BitVec 32)) := do
  let (words, _) ← linkHybridWithMap hw items
  return words

/-! ## 4. Translation-Validated Width Oracle (`computeHybridWidths` / `linkHybrid`) -/

private def relaxUpdatePass (hw0 : HybridWidths) (labels : Std.HashMap String Nat) (pc : Nat)
    (items : List AsmItem) (hw : HybridWidths) (changed : Bool) : HybridWidths × Bool :=
  match items with
  | [] => (hw, changed)
  | item :: rest =>
    let step := hybridWordSize hw0 item
    match item with
    | .label _ | .instr _ => relaxUpdatePass hw0 labels (pc + step) rest hw changed
    | .j target =>
      match labels[target]? with
      | none => relaxUpdatePass hw0 labels (pc + step) rest hw changed
      | some tgt =>
        if !hw.getJ target && !jalInRange ((tgt : Int) - (pc : Int)) then
          relaxUpdatePass hw0 labels (pc + step) rest { hw with jFar := hw.jFar.insert target () } true
        else
          relaxUpdatePass hw0 labels (pc + step) rest hw changed
    | .call target =>
      match labels[target]? with
      | none => relaxUpdatePass hw0 labels (pc + step) rest hw changed
      | some tgt =>
        if !hw.getC target && !jalInRange ((tgt : Int) - (pc : Int)) then
          relaxUpdatePass hw0 labels (pc + step) rest { hw with cFar := hw.cFar.insert target () } true
        else
          relaxUpdatePass hw0 labels (pc + step) rest hw changed
    | .br _ _ _ target | .brLong _ _ _ target =>
      match labels[target]? with
      | none => relaxUpdatePass hw0 labels (pc + step) rest hw changed
      | some tgt =>
        let cur := hw.getB target
        let need3 := !jalInRange ((tgt : Int) - ((pc + 1 : Nat) : Int))
        let need2 := !branchInRange ((tgt : Int) - (pc : Int))
        match cur with
        | .w1 =>
          if need2 then
            relaxUpdatePass hw0 labels (pc + step) rest
              { hw with bKind := hw.bKind.insert target need3 } true
          else relaxUpdatePass hw0 labels (pc + step) rest hw changed
        | .w2 =>
          if need3 then
            relaxUpdatePass hw0 labels (pc + step) rest
              { hw with bKind := hw.bKind.insert target true } true
          else relaxUpdatePass hw0 labels (pc + step) rest hw changed
        | .w3 => relaxUpdatePass hw0 labels (pc + step) rest hw changed

private def relaxCandidateGo (fuel : Nat) (items : List AsmItem) (hw : HybridWidths) : HybridWidths :=
  match fuel with
  | 0 => hw
  | fuel' + 1 =>
    match collectHybridLabelsFast hw items with
    | .error _ => hw
    | .ok labs =>
      let (hw', changed) := relaxUpdatePass hw labs 0 items hw false
      if changed then relaxCandidateGo fuel' items hw' else hw'

/-- Boolean validator checking every jump/call/branch in `items` fits its assigned width in `hw`. -/
def validateHybridItem (hw : HybridWidths) (labels : Std.HashMap String Nat) (pc : Nat)
    (item : AsmItem) : Bool :=
  match item with
  | .label _ | .instr _ => true
  | .j target =>
    match labels[target]? with
    | none => false
    | some tgt =>
      if hw.getJ target then farInRange ((tgt : Int) - ((pc + 1 : Nat) : Int))
      else jalInRange ((tgt : Int) - (pc : Int))
  | .call target =>
    match labels[target]? with
    | none => false
    | some tgt =>
      if hw.getC target then farInRange ((tgt : Int) - ((pc + 1 : Nat) : Int))
      else jalInRange ((tgt : Int) - (pc : Int))
  | .br _ _ _ target | .brLong _ _ _ target =>
    match labels[target]? with
    | none => false
    | some tgt =>
      match hw.getB target with
      | .w1 => branchInRange ((tgt : Int) - (pc : Int))
      | .w2 => jalInRange ((tgt : Int) - ((pc + 1 : Nat) : Int))
      | .w3 => farInRange ((tgt : Int) - ((pc + 2 : Nat) : Int))

def validateHybridGo (hw : HybridWidths) (labels : Std.HashMap String Nat) (pc : Nat)
    (items : List AsmItem) : Bool :=
  match items with
  | [] => true
  | item :: rest =>
    if validateHybridItem hw labels pc item then
      validateHybridGo hw labels (pc + hybridWordSize hw item) rest
    else false

/-- Run unverified iterative relaxation and validate; fall back to `allFar` (`linkFar`) if
    validation does not pass. -/
def computeHybridWidths (items : List AsmItem) : HybridWidths :=
  let cand := relaxCandidateGo 8 items HybridWidths.allNear
  match collectHybridLabelsFast cand items with
  | .ok labs =>
    if validateHybridGo cand labs 0 items then cand else HybridWidths.mkAllFar
  | .error _ => HybridWidths.mkAllFar

/-- Fast hybrid near/mid/far symbolic linker. Falls back to `linkFar` if unvalidated. -/
def linkHybrid (items : List AsmItem) : Except String (Array (BitVec 32)) :=
  linkHybridWith (computeHybridWidths items) items

/-! ## 5. Fast ↔ Spec Equivalence (`MapAgree`) -/

private theorem hmapAgree_empty : MapAgree (∅ : Std.HashMap String Nat) [] := by
  intro s; simp [lookupLabel]

private theorem hmapAgree_insert {hm : Std.HashMap String Nat} {lm : LabelMap}
    (h : MapAgree hm lm) (k : String) (v : Nat) :
    MapAgree (hm.insert k v) ((k, v) :: lm) := by
  intro s
  rw [Std.HashMap.getElem?_insert]
  simp only [lookupLabel, h s]

private theorem collectHybridLabelsFastGo_eq (hw : HybridWidths) (items : List AsmItem) (pc : Nat)
    (hm : Std.HashMap String Nat) (lm : LabelMap) (hag : MapAgree hm lm) :
    (∀ hm', collectHybridLabelsFastGo hw items pc hm = .ok hm' →
      ∃ lm', collectHybridLabelsGo hw items pc lm = .ok lm' ∧ MapAgree hm' lm') ∧
    (∀ e, collectHybridLabelsFastGo hw items pc hm = .error e →
      collectHybridLabelsGo hw items pc lm = .error e) := by
  induction items generalizing pc hm lm with
  | nil =>
    simp only [collectHybridLabelsFastGo, collectHybridLabelsGo, Except.ok.injEq]
    constructor
    · intro hm' h; subst h; exact ⟨lm, rfl, hag⟩
    · intro e h; cases h
  | cons item rest ih =>
    cases item with
    | label name =>
      simp only [collectHybridLabelsFastGo, collectHybridLabelsGo]
      have hlook : hm[name]? = lookupLabel lm name := hag name
      cases hl : lookupLabel lm name with
      | some v =>
        have hf : hm[name]? = some v := hlook.trans hl
        simp only [hf]
        exact ⟨(fun _ h => by cases h), (fun _ h => by cases h; rfl)⟩
      | none =>
        have hf : hm[name]? = none := hlook.trans hl
        simp only [hf]
        exact ih pc (hm.insert name pc) ((name, pc) :: lm) (hmapAgree_insert hag name pc)
    | _ => exact ih (pc + hybridWordSize hw _) hm lm hag

private theorem resolveHybridItemFast_eq (hw : HybridWidths)
    {hm : Std.HashMap String Nat} {lm : LabelMap}
    (hag : MapAgree hm lm) (pc : Nat) (item : AsmItem) :
    resolveHybridItemFast hw hm pc item = resolveHybridItem hw lm pc item := by
  cases item <;> simp only [resolveHybridItemFast, resolveHybridItem]
  all_goals rename_i target; rw [hag target]

private theorem resolveHybridWordsFastGo_eq (hw : HybridWidths)
    {hm : Std.HashMap String Nat} {lm : LabelMap}
    (hag : MapAgree hm lm) (pc : Nat) (items : List AsmItem) (acc : Array (BitVec 32)) :
    resolveHybridWordsFastGo hw hm pc items acc = resolveHybridWordsGo hw lm pc items acc := by
  induction items generalizing pc acc with
  | nil => rfl
  | cons item rest ih =>
    simp only [resolveHybridWordsFastGo, resolveHybridWordsGo,
      resolveHybridItemFast_eq hw hag pc item]
    cases resolveHybridItem hw lm pc item with
    | error _ => rfl
    | ok is => exact ih (pc + hybridWordSize hw item) (pushEncoded acc is)

theorem linkHybridWithMap_eq_spec (hw : HybridWidths) (items : List AsmItem) :
    (∀ words hm, linkHybridWithMap hw items = .ok (words, hm) →
      ∃ lm, linkHybridWithSpec hw items = .ok (words, lm) ∧ MapAgree hm lm) ∧
    (∀ e, linkHybridWithMap hw items = .error e →
      linkHybridWithSpec hw items = .error e) := by
  simp only [linkHybridWithMap, linkHybridWithSpec, bind, Except.bind,
    collectHybridLabelsFast, collectHybridLabels]
  have hcol := collectHybridLabelsFastGo_eq hw items 0 ∅ [] hmapAgree_empty
  constructor
  · intro words hm h
    cases hf : collectHybridLabelsFastGo hw items 0 ∅ with
    | error e => rw [hf] at h; cases h
    | ok hm' =>
      rw [hf] at h; dsimp only at h
      obtain ⟨lm', hlm', hag⟩ := hcol.1 hm' hf
      rw [resolveHybridWordsFastGo_eq hw hag] at h
      rw [hlm']; dsimp only
      cases hr : resolveHybridWordsGo hw lm' 0 items #[] with
      | error e => rw [hr] at h; cases h
      | ok ws =>
        rw [hr] at h
        simp only [Except.pure, pure, Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact ⟨lm', rfl, hag⟩
  · intro e h
    cases hf : collectHybridLabelsFastGo hw items 0 ∅ with
    | error e1 =>
      rw [hf] at h; rw [hcol.2 e1 hf]; dsimp only at h ⊢; cases h; rfl
    | ok hm' =>
      rw [hf] at h; dsimp only at h
      obtain ⟨lm', hlm', hag⟩ := hcol.1 hm' hf
      rw [resolveHybridWordsFastGo_eq hw hag] at h
      rw [hlm']; dsimp only
      cases hr : resolveHybridWordsGo hw lm' 0 items #[] with
      | error e2 => simp only [hr] at h ⊢; cases h; rfl
      | ok ws => rw [hr] at h; cases h

theorem linkHybridWith_ok_spec {hw : HybridWidths} {items : List AsmItem}
    {words : Array (BitVec 32)} (h : linkHybridWith hw items = .ok words) :
    ∃ lm, linkHybridWithSpec hw items = .ok (words, lm) := by
  simp only [linkHybridWith, bind, Except.bind] at h
  cases hm : linkHybridWithMap hw items with
  | error e => rw [hm] at h; cases h
  | ok p =>
    rw [hm] at h
    simp only [Except.pure, pure, Except.ok.injEq] at h; subst h
    exact ⟨_, (linkHybridWithMap_eq_spec hw items).1 p.1 p.2 hm |>.choose_spec.1⟩

theorem linkHybridWith_eq_spec (hw : HybridWidths) (items : List AsmItem) :
    linkHybridWith hw items = (linkHybridWithSpec hw items).map Prod.fst := by
  simp only [linkHybridWith, bind, Except.bind, Except.map]
  cases hm : linkHybridWithMap hw items with
  | ok p =>
    obtain ⟨lm, hspec, _⟩ := (linkHybridWithMap_eq_spec hw items).1 p.1 p.2 hm
    rw [hspec]; rfl
  | error e =>
    have hspec := (linkHybridWithMap_eq_spec hw items).2 e hm
    rw [hspec]

/-! ## 6. Equivalence of `allFar` Fallback with `linkFarSpec` -/

private theorem collectHybridLabelsGo_allFar (items : List AsmItem) (pc : Nat) (acc : LabelMap) :
    collectHybridLabelsGo HybridWidths.mkAllFar items pc acc = collectFarLabelsGo items pc acc := by
  induction items generalizing pc acc with
  | nil => rfl
  | cons item rest ih =>
    cases item with
    | label name =>
      simp only [collectHybridLabelsGo, collectFarLabelsGo]
      cases lookupLabel acc name with
      | some _ => rfl
      | none => exact ih pc ((name, pc) :: acc)
    | _ =>
      simp only [collectHybridLabelsGo, collectFarLabelsGo, hybridWordSize_allFar]
      exact ih (pc + farWordSize _) acc

private theorem resolveHybridItem_allFar_ok (labels : LabelMap) (pc : Nat) (item : AsmItem)
    (is : List Instr) (h : resolveFarItem labels pc item = .ok is) :
    resolveHybridItem HybridWidths.mkAllFar labels pc item = .ok is := by
  cases item with
  | label _ => exact h
  | instr _ => exact h
  | j target =>
    simp only [resolveFarItem] at h
    simp only [resolveHybridItem, HybridWidths.getJ, HybridWidths.mkAllFar, Bool.true_or, ↓reduceIte]
    cases hl : lookupLabel labels target with
    | none => rw [hl] at h; cases h
    | some tgt =>
      rw [hl] at h; dsimp only at h ⊢
      split at h
      · next hrg => rw [hrg]; simpa [farInstrsFor] using h
      · cases h
  | «call» target =>
    simp only [resolveFarItem] at h
    simp only [resolveHybridItem, HybridWidths.getC, HybridWidths.mkAllFar, Bool.true_or, ↓reduceIte]
    cases hl : lookupLabel labels target with
    | none => rw [hl] at h; cases h
    | some tgt =>
      rw [hl] at h; dsimp only at h ⊢
      split at h
      · next hrg => rw [hrg]; simpa [farInstrsFor] using h
      · cases h
  | br op rs1 rs2 target =>
    simp only [resolveFarItem] at h
    simp only [resolveHybridItem, HybridWidths.getB, HybridWidths.mkAllFar, ↓reduceIte,
      resolveBrWith, branchInstrsFor]
    cases hl : lookupLabel labels target with
    | none => rw [hl] at h; cases h
    | some tgt =>
      rw [hl] at h; dsimp only at h ⊢
      split at h
      · next hrg => rw [hrg]; simpa [farInstrsFor] using h
      · cases h
  | brLong op rs1 rs2 target =>
    simp only [resolveFarItem] at h
    simp only [resolveHybridItem, HybridWidths.getB, HybridWidths.mkAllFar, ↓reduceIte,
      resolveBrWith, branchInstrsFor]
    cases hl : lookupLabel labels target with
    | none => rw [hl] at h; cases h
    | some tgt =>
      rw [hl] at h; dsimp only at h ⊢
      split at h
      · next hrg => rw [hrg]; simpa [farInstrsFor] using h
      · cases h

private theorem resolveHybridWordsGo_allFar_ok (labels : LabelMap) (pc : Nat)
    (items : List AsmItem) (acc : Array (BitVec 32)) (ws : Array (BitVec 32))
    (h : resolveFarWordsGo labels pc items acc = .ok ws) :
    resolveHybridWordsGo HybridWidths.mkAllFar labels pc items acc = .ok ws := by
  induction items generalizing pc acc with
  | nil => exact h
  | cons item rest ih =>
    simp only [resolveFarWordsGo] at h
    cases hr : resolveFarItem labels pc item with
    | error e => rw [hr] at h; cases h
    | ok is =>
      rw [hr] at h
      simp only [resolveHybridWordsGo, resolveHybridItem_allFar_ok labels pc item is hr,
        hybridWordSize_allFar]
      exact ih (pc + farWordSize item) (pushEncoded acc is) h

theorem linkHybridWithSpec_allFar_of_far {items : List AsmItem} {code : Array (BitVec 32)}
    {labels : LabelMap} (h : linkFarSpec items = .ok (code, labels)) :
    linkHybridWithSpec HybridWidths.mkAllFar items = .ok (code, labels) := by
  simp only [linkFarSpec, bind, Except.bind, collectFarLabels] at h
  cases hc : collectFarLabelsGo items 0 [] with
  | error e => rw [hc] at h; cases h
  | ok lm =>
    rw [hc] at h; dsimp only at h
    cases hr : resolveFarWordsGo lm 0 items #[] with
    | error e => rw [hr] at h; cases h
    | ok ws =>
      rw [hr] at h
      simp only [Except.pure, pure, Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp only [linkHybridWithSpec, bind, Except.bind, collectHybridLabels,
        collectHybridLabelsGo_allFar, hc, resolveHybridWordsGo_allFar_ok lm 0 items #[] ws hr,
        pure, Except.pure]

/-! ## 7. Label Lookup, Size, & Item Decode Theorems -/

private theorem lookupLabel_hybrid_append_fresh {hw : HybridWidths}
    {items : List AsmItem} {pc : Nat} {acc lm : LabelMap}
    (h : collectHybridLabelsGo hw items pc acc = .ok lm)
    (name : String) (v : Nat) (hacc : lookupLabel acc name = some v) :
    lookupLabel lm name = some v := by
  induction items generalizing pc acc with
  | nil =>
    simp only [collectHybridLabelsGo, Except.ok.injEq] at h; subst h; exact hacc
  | cons item rest ih =>
    cases item with
    | label nm =>
      simp only [collectHybridLabelsGo] at h
      cases hl : lookupLabel acc nm with
      | some _ => rw [hl] at h; cases h
      | none =>
        rw [hl] at h
        have hne : (nm == name) = false := by
          cases heq : (nm == name) with
          | false => rfl
          | true =>
            have : nm = name := beq_iff_eq.mp heq
            subst this; rw [hl] at hacc; cases hacc
        exact ih h (by simp [lookupLabel, hne, hacc])
    | _ => exact ih h hacc

private theorem collectHybridLabelsGo_append (hw : HybridWidths) (xs ys : List AsmItem)
    (pc : Nat) (acc : LabelMap) :
    collectHybridLabelsGo hw (xs ++ ys) pc acc =
      (do
        let acc1 ← collectHybridLabelsGo hw xs pc acc
        collectHybridLabelsGo hw ys (pc + hybridTotalWords hw xs) acc1) := by
  induction xs generalizing pc acc with
  | nil => simp [collectHybridLabelsGo, hybridTotalWords_nil, bind, Except.bind]
  | cons x xs ih =>
    cases x with
    | label nm =>
      simp only [List.cons_append, collectHybridLabelsGo, hybridTotalWords_cons,
        hybridWordSize, Nat.zero_add]
      cases hl : lookupLabel acc nm with
      | some _ => rfl
      | none => exact ih pc ((nm, pc) :: acc)
    | _ =>
      simp only [List.cons_append, collectHybridLabelsGo, hybridTotalWords_cons]
      rw [ih (pc + hybridWordSize hw _) acc, Nat.add_assoc]

theorem collectHybridLabels_label_at (hw : HybridWidths) (pre post : List AsmItem)
    (name : String) (lm : LabelMap)
    (h : collectHybridLabels hw (pre ++ [.label name] ++ post) = .ok lm) :
    lookupLabel lm name = some (hybridTotalWords hw pre) := by
  unfold collectHybridLabels at h
  rw [List.append_assoc, collectHybridLabelsGo_append] at h
  simp only [bind, Except.bind] at h
  cases hpre : collectHybridLabelsGo hw pre 0 [] with
  | error e => rw [hpre] at h; cases h
  | ok acc1 =>
    rw [hpre] at h
    dsimp only [List.cons_append, List.nil_append, Nat.zero_add, collectHybridLabelsGo] at h
    cases hl : lookupLabel acc1 name with
    | some _ => rw [hl] at h; cases h
    | none =>
      rw [hl] at h
      exact lookupLabel_hybrid_append_fresh h name (hybridTotalWords hw pre)
        (by simp [lookupLabel])

theorem resolveHybridItem_length {hw : HybridWidths} {lm : LabelMap} {pc : Nat}
    {item : AsmItem} {is : List Instr}
    (h : resolveHybridItem hw lm pc item = .ok is) :
    is.length = hybridWordSize hw item := by
  cases item with
  | label _ => simp [resolveHybridItem] at h; subst h; rfl
  | instr _ => simp [resolveHybridItem] at h; subst h; rfl
  | j target =>
    simp only [resolveHybridItem] at h
    cases hl : lookupLabel lm target with
    | none => rw [hl] at h; cases h
    | some tgt =>
      rw [hl] at h; dsimp only [hybridWordSize] at h ⊢
      cases hgj : hw.getJ target <;> rw [hgj] at h <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      · split at h <;> cases h; rfl
      · split at h <;> cases h; rfl
  | «call» target =>
    simp only [resolveHybridItem] at h
    cases hl : lookupLabel lm target with
    | none => rw [hl] at h; cases h
    | some tgt =>
      rw [hl] at h; dsimp only [hybridWordSize] at h ⊢
      cases hgc : hw.getC target <;> rw [hgc] at h <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      · split at h <;> cases h; rfl
      · split at h <;> cases h; rfl
  | br op r1 r2 target =>
    simp only [resolveHybridItem] at h
    cases hl : lookupLabel lm target with
    | none => rw [hl] at h; cases h
    | some tgt =>
      rw [hl] at h; dsimp only [resolveBrWith, hybridWordSize] at h ⊢
      cases hbw : hw.getB target <;> rw [hbw] at h <;> dsimp only at h
      all_goals (split at h; (cases h; rfl); cases h)
  | brLong op r1 r2 target =>
    simp only [resolveHybridItem] at h
    cases hl : lookupLabel lm target with
    | none => rw [hl] at h; cases h
    | some tgt =>
      rw [hl] at h; dsimp only [resolveBrWith, hybridWordSize] at h ⊢
      cases hbw : hw.getB target <;> rw [hbw] at h <;> dsimp only at h
      all_goals (split at h; (cases h; rfl); cases h)

private theorem pushEncoded_size_eq (acc : Array (BitVec 32)) (is : List Instr) :
    (pushEncoded acc is).size = acc.size + is.length := by
  induction is generalizing acc with
  | nil => simp [pushEncoded]
  | cons i is ih =>
    simp only [pushEncoded, List.length_cons]
    rw [ih (acc.push (encode i)), Array.size_push]
    omega

private theorem pushEncoded_getElem?_old (acc : Array (BitVec 32)) (is : List Instr)
    {k : Nat} (hk : k < acc.size) :
    (pushEncoded acc is)[k]? = acc[k]? := by
  induction is generalizing acc with
  | nil => rfl
  | cons i is ih =>
    simp only [pushEncoded]
    have hlt : k < (acc.push (encode i)).size := by simp; omega
    rw [ih (acc.push (encode i)) hlt, Array.getElem?_push]
    simp [Nat.ne_of_lt hk]

private theorem pushEncoded_getElem?_new (acc : Array (BitVec 32)) (is : List Instr)
    {j : Nat} (hj : j < is.length) :
    (pushEncoded acc is)[acc.size + j]? = some (encode is[j]) := by
  induction is generalizing acc j with
  | nil => simp at hj
  | cons i is ih =>
    simp only [pushEncoded]
    cases j with
    | zero =>
      have hk : acc.size < (acc.push (encode i)).size := by simp
      rw [Nat.add_zero, pushEncoded_getElem?_old (acc.push (encode i)) is hk, Array.getElem?_push]
      simp
    | succ j' =>
      have hj' : j' < is.length := by simp at hj; omega
      have hpos : acc.size + (j' + 1) = (acc.push (encode i)).size + j' := by
        simp; omega
      rw [hpos, ih (acc.push (encode i)) hj']
      rfl

private theorem resolveHybridWordsGo_size {hw : HybridWidths} {lm : LabelMap}
    {pc : Nat} {items : List AsmItem} {acc words : Array (BitVec 32)}
    (h : resolveHybridWordsGo hw lm pc items acc = .ok words) :
    words.size = acc.size + hybridTotalWords hw items := by
  induction items generalizing pc acc with
  | nil =>
    simp only [resolveHybridWordsGo, Except.ok.injEq] at h
    subst h; simp [hybridTotalWords_nil]
  | cons item rest ih =>
    simp only [resolveHybridWordsGo] at h
    cases hr : resolveHybridItem hw lm pc item with
    | error e => rw [hr] at h; cases h
    | ok is =>
      rw [hr] at h
      have hsz := ih h
      have hlen := resolveHybridItem_length hr
      rw [hsz, pushEncoded_size_eq, hlen, hybridTotalWords_cons]
      omega

private theorem resolveHybridWordsGo_prefix_getElem? {hw : HybridWidths} {lm : LabelMap}
    {pc : Nat} {items : List AsmItem} {acc words : Array (BitVec 32)}
    (h : resolveHybridWordsGo hw lm pc items acc = .ok words)
    {k : Nat} (hk : k < acc.size) :
    words[k]? = acc[k]? := by
  induction items generalizing pc acc with
  | nil =>
    simp only [resolveHybridWordsGo, Except.ok.injEq] at h; subst h; rfl
  | cons item rest ih =>
    simp only [resolveHybridWordsGo] at h
    cases hr : resolveHybridItem hw lm pc item with
    | error e => rw [hr] at h; cases h
    | ok is =>
      rw [hr] at h
      have hlt : k < (pushEncoded acc is).size := by
        rw [pushEncoded_size_eq]; omega
      rw [ih h hlt, pushEncoded_getElem?_old acc is hk]

private theorem resolveHybridWordsGo_append (hw : HybridWidths) (lm : LabelMap) (pc : Nat)
    (xs ys : List AsmItem) (acc : Array (BitVec 32)) :
    resolveHybridWordsGo hw lm pc (xs ++ ys) acc =
      (do
        let acc1 ← resolveHybridWordsGo hw lm pc xs acc
        resolveHybridWordsGo hw lm (pc + hybridTotalWords hw xs) ys acc1) := by
  induction xs generalizing pc acc with
  | nil => simp [resolveHybridWordsGo, hybridTotalWords_nil, bind, Except.bind]
  | cons x xs ih =>
    simp only [List.cons_append, resolveHybridWordsGo, hybridTotalWords_cons]
    cases hr : resolveHybridItem hw lm pc x with
    | error e => rfl
    | ok is =>
      have h := ih (pc + hybridWordSize hw x) (pushEncoded acc is)
      rw [Nat.add_assoc] at h
      exact h

theorem linkHybridWithSpec_size {hw : HybridWidths} {items : List AsmItem}
    {code : Array (BitVec 32)} {labels : LabelMap}
    (h : linkHybridWithSpec hw items = .ok (code, labels)) :
    code.size = hybridTotalWords hw items := by
  simp only [linkHybridWithSpec, bind, Except.bind] at h
  cases hc : collectHybridLabels hw items with
  | error e => rw [hc] at h; cases h
  | ok lm =>
    rw [hc] at h; dsimp only at h
    cases hr : resolveHybridWordsGo hw lm 0 items #[] with
    | error e => rw [hr] at h; cases h
    | ok ws =>
      rw [hr] at h
      simp only [Except.pure, pure, Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simpa using resolveHybridWordsGo_size hr

private theorem linkHybridWithSpec_item_instrs {hw : HybridWidths}
    (pre : List AsmItem) (it : AsmItem) (post : List AsmItem)
    {code : Array (BitVec 32)} {labels : LabelMap}
    (h : linkHybridWithSpec hw (pre ++ [it] ++ post) = .ok (code, labels)) :
    ∃ is, resolveHybridItem hw labels (hybridTotalWords hw pre) it = .ok is ∧
      is.length = hybridWordSize hw it ∧
      ∀ j, (hj : j < is.length) →
        (code[hybridTotalWords hw pre + j]?).bind decode = some is[j] := by
  simp only [linkHybridWithSpec, bind, Except.bind] at h
  cases hc : collectHybridLabels hw (pre ++ [it] ++ post) with
  | error e => rw [hc] at h; cases h
  | ok lm =>
    rw [hc] at h; dsimp only at h
    cases hr : resolveHybridWordsGo hw lm 0 (pre ++ [it] ++ post) #[] with
    | error e => rw [hr] at h; cases h
    | ok ws =>
      rw [hr] at h
      simp only [Except.pure, pure, Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rw [List.append_assoc, resolveHybridWordsGo_append] at hr
      simp only [bind, Except.bind] at hr
      cases hpre : resolveHybridWordsGo hw lm 0 pre #[] with
      | error e => rw [hpre] at hr; cases hr
      | ok acc1 =>
        rw [hpre] at hr; simp only [Nat.zero_add, List.cons_append, List.nil_append, resolveHybridWordsGo] at hr
        cases hit : resolveHybridItem hw lm (hybridTotalWords hw pre) it with
        | error e => rw [hit] at hr; cases hr
        | ok is =>
          rw [hit] at hr
          have hsz1 : acc1.size = hybridTotalWords hw pre := by
            simpa using resolveHybridWordsGo_size hpre
          refine ⟨is, rfl, resolveHybridItem_length hit, fun j hj => ?_⟩
          have hlt : hybridTotalWords hw pre + j < (pushEncoded acc1 is).size := by
            rw [pushEncoded_size_eq, hsz1]; omega
          rw [resolveHybridWordsGo_prefix_getElem? hr hlt, ← hsz1,
            pushEncoded_getElem?_new acc1 is hj]
          simp only [Option.bind_some, decode_encode]

/-! ## 8. Soundness of Boolean Validator `validateHybridGo` -/

private theorem resolveHybridItemFast_of_validate (hw : HybridWidths)
    (labs : Std.HashMap String Nat) (pc : Nat) (item : AsmItem)
    (hv : validateHybridItem hw labs pc item = true) :
    ∃ is, resolveHybridItemFast hw labs pc item = .ok is ∧ is.length = hybridWordSize hw item := by
  cases item with
  | label _ => exact ⟨[], rfl, rfl⟩
  | instr i => exact ⟨[i], rfl, rfl⟩
  | j target =>
    simp only [validateHybridItem] at hv
    simp only [resolveHybridItemFast, hybridWordSize]
    cases hl : labs[target]? with
    | none => rw [hl] at hv; simp at hv
    | some tgt =>
      rw [hl] at hv; dsimp only at hv ⊢
      cases hgj : hw.getJ target with
      | true =>
        rw [hgj] at hv; simp only [↓reduceIte] at hv ⊢
        rw [hv]; exact ⟨_, rfl, rfl⟩
      | false =>
        rw [hgj] at hv; simp only [Bool.false_eq_true, ↓reduceIte] at hv ⊢
        rw [hv]; exact ⟨_, rfl, rfl⟩
  | «call» target =>
    simp only [validateHybridItem] at hv
    simp only [resolveHybridItemFast, hybridWordSize]
    cases hl : labs[target]? with
    | none => rw [hl] at hv; simp at hv
    | some tgt =>
      rw [hl] at hv; dsimp only at hv ⊢
      cases hgc : hw.getC target with
      | true =>
        rw [hgc] at hv; simp only [↓reduceIte] at hv ⊢
        rw [hv]; exact ⟨_, rfl, rfl⟩
      | false =>
        rw [hgc] at hv; simp only [Bool.false_eq_true, ↓reduceIte] at hv ⊢
        rw [hv]; exact ⟨_, rfl, rfl⟩
  | br op r1 r2 target =>
    simp only [validateHybridItem] at hv
    simp only [resolveHybridItemFast, hybridWordSize, resolveBrWith]
    cases hl : labs[target]? with
    | none => rw [hl] at hv; simp at hv
    | some tgt =>
      rw [hl] at hv; dsimp only at hv ⊢
      cases hgb : hw.getB target with
      | w1 => rw [hgb] at hv; simp only [hv, ↓reduceIte]; exact ⟨_, rfl, rfl⟩
      | w2 => rw [hgb] at hv; simp only [hv, ↓reduceIte]; exact ⟨_, rfl, rfl⟩
      | w3 => rw [hgb] at hv; simp only [hv, ↓reduceIte]; exact ⟨_, rfl, rfl⟩
  | brLong op r1 r2 target =>
    simp only [validateHybridItem] at hv
    simp only [resolveHybridItemFast, hybridWordSize, resolveBrWith]
    cases hl : labs[target]? with
    | none => rw [hl] at hv; simp at hv
    | some tgt =>
      rw [hl] at hv; dsimp only at hv ⊢
      cases hgb : hw.getB target with
      | w1 => rw [hgb] at hv; simp only [hv, ↓reduceIte]; exact ⟨_, rfl, rfl⟩
      | w2 => rw [hgb] at hv; simp only [hv, ↓reduceIte]; exact ⟨_, rfl, rfl⟩
      | w3 => rw [hgb] at hv; simp only [hv, ↓reduceIte]; exact ⟨_, rfl, rfl⟩

private theorem resolveHybridWordsFastGo_of_validate (hw : HybridWidths)
    (labs : Std.HashMap String Nat) (pc : Nat) (items : List AsmItem)
    (acc : Array (BitVec 32)) (hv : validateHybridGo hw labs pc items = true) :
    ∃ ws, resolveHybridWordsFastGo hw labs pc items acc = .ok ws ∧
      ws.size = acc.size + hybridTotalWords hw items := by
  induction items generalizing pc acc with
  | nil => exact ⟨acc, rfl, by simp [hybridTotalWords_nil]⟩
  | cons item rest ih =>
    simp only [validateHybridGo] at hv
    split at hv
    · next hv1 =>
      obtain ⟨is, hres, hlen⟩ := resolveHybridItemFast_of_validate hw labs pc item hv1
      obtain ⟨ws, hgo, hsz⟩ := ih (pc + hybridWordSize hw item) (pushEncoded acc is) hv
      refine ⟨ws, ?_, ?_⟩
      · simp only [resolveHybridWordsFastGo, hres]; exact hgo
      · rw [hsz, pushEncoded_size_eq, hlen, hybridTotalWords_cons]; omega
    · cases hv

/-! ## 9. Operational `LinkModel` Instance (`hybridLinkModel`) -/

private theorem hpc_add_4 {pc : Nat} (stPc : Word) (h : stPc = BitVec.ofNat 64 (4 * pc)) :
    stPc + 4#64 = BitVec.ofNat 64 (4 * (pc + 1)) := by
  rw [h]; apply BitVec.eq_of_toNat_eq; simp [BitVec.add_def]; omega

private theorem hybrid_step_instr_aux (hw : HybridWidths)
    {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    {pre post : List AsmItem} {inst : Instr} {st : State}
    (hrom : RomMatches rom code)
    (hlink : linkHybridWithSpec hw (pre ++ [.instr inst] ++ post) = .ok (code, labels))
    (h64 : 4 * totalSizeWith (hybridWordSize hw) pre < 2 ^ 64)
    (hpc : st.pc = BitVec.ofNat 64 (4 * totalSizeWith (hybridWordSize hw) pre)) :
    RV64.step rom st = execInstr st inst := by
  rw [totalSizeWith_hybrid_eq] at h64 hpc
  obtain ⟨is, hres, _, hdec⟩ := linkHybridWithSpec_item_instrs pre (.instr inst) post hlink
  simp only [resolveHybridItem, Except.ok.injEq] at hres; subst hres
  have hd0 := hdec 0 (by simp)
  simp only [Nat.add_zero, List.getElem_cons_zero] at hd0
  exact step_at_decoded_rom h64 (rom_decode_of_matches hrom hd0) st hpc

private theorem hybrid_step_j_aux (hw : HybridWidths)
    {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    {pre post : List AsmItem} {target : String} {st : State}
    (hrom : RomMatches rom code)
    (hlink : linkHybridWithSpec hw (pre ++ [.j target] ++ post) = .ok (code, labels))
    (h64 : 4 * (totalSizeWith (hybridWordSize hw) pre + hybridWordSize hw (.j target)) < 2 ^ 64)
    (hpc : st.pc = BitVec.ofNat 64 (4 * totalSizeWith (hybridWordSize hw) pre)) :
    ∃ tgt k st', 1 ≤ k ∧
      lookupLabel labels target = some tgt ∧
      RV64.run rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * tgt) ∧
      RegEqExceptT6 st.regs st'.regs ∧
      st'.mem = st.mem := by
  rw [totalSizeWith_hybrid_eq] at h64 hpc
  obtain ⟨is, hres, _, hdec⟩ := linkHybridWithSpec_item_instrs pre (.j target) post hlink
  simp only [resolveHybridItem] at hres
  cases hlook : lookupLabel labels target with
  | none => rw [hlook] at hres; cases hres
  | some tgt =>
    rw [hlook] at hres; dsimp only at hres
    cases hgj : hw.getJ target with
    | false =>
      rw [hgj] at hres; simp only [Bool.false_eq_true, ↓reduceIte] at hres
      cases hrg : jalInRange ((tgt : Int) - (hybridTotalWords hw pre : Int)) with
      | false => rw [hrg] at hres; cases hres
      | true =>
        rw [hrg] at hres; simp only [↓reduceIte, Except.ok.injEq] at hres; subst hres
        have hd0 : (code[hybridTotalWords hw pre]?).bind decode =
            some (.jal AbiReg.zero (mkJimm ((tgt : Int) - (hybridTotalWords hw pre : Int)))) := by
          simpa using hdec 0 (by simp)
        have hlt : 4 * hybridTotalWords hw pre < 2 ^ 64 := by
          simp only [hybridWordSize, hgj, Bool.false_eq_true, ↓reduceIte] at h64; omega
        let st' : State := { st with pc := BitVec.ofNat 64 (4 * tgt) }
        have hs : RV64.step rom st = .cont st' := by
          rw [step_at_decoded_rom hlt (rom_decode_of_matches hrom hd0) st hpc]
          simp only [execInstr, State.setReg, AbiReg.zero, beq_self_eq_true, ↓reduceIte, st']
          rw [hpc, pc_add_sextImmJ hrg]
        exact ⟨tgt, 1, st', Nat.le_refl 1, rfl, by simp [RV64.run, hs], rfl,
          RegEqExceptT6.refl _, rfl⟩
    | true =>
      rw [hgj] at hres; simp only [↓reduceIte] at hres
      cases hrg : farInRange ((tgt : Int) - ((hybridTotalWords hw pre + 1 : Nat) : Int)) with
      | false => rw [hrg] at hres; cases hres
      | true =>
        rw [hrg] at hres; simp only [↓reduceIte, Except.ok.injEq] at hres; subst hres
        have hd0 := hdec 0 (by simp)
        have hd1 := hdec 1 (by simp)
        have hd2 := hdec 2 (by simp)
        have hd3 := hdec 3 (by simp)
        simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at hd0 hd1 hd2 hd3
        have hlt : 4 * (hybridTotalWords hw pre + 4) < 2 ^ 64 := by
          simpa [hybridWordSize, hgj] using h64
        obtain ⟨_, _, _, st', _, _, _, _, hrun, hpc', _, hget, hmem⟩ :=
          step_far_jalr (rom := rom) (st := st) (pc := hybridTotalWords hw pre) (tgt := tgt)
            (rd := AbiReg.zero) (by decide) (by decide) (by omega) hpc hrg
            (rom_decode_of_matches hrom hd0) (rom_decode_of_matches hrom hd1)
            (rom_decode_of_matches hrom hd2) (rom_decode_of_matches hrom hd3)
        have hzero : st'.regs 0#5 = st.regs 0#5 := run_regs_zero hrun
        have hregEq : RegEqExceptT6 st.regs st'.regs := by
          refine RegEqExceptT6.of_getReg_zero_eq hzero.symm ?_
          intro r hr
          by_cases hr0 : r = AbiReg.zero
          · subst hr0; simp [State.getReg, AbiReg.zero]
          · exact (hget r hr0 hr.1 hr.2).symm
        exact ⟨tgt, 4, st', by omega, rfl, hrun, hpc', hregEq, hmem⟩

private theorem getReg_setReg_self' (st : State) (r : Reg) (hr : r ≠ 0#5) (v : Word) :
    (st.setReg r v).getReg r = v := by
  simp [State.getReg, State.setReg, beq_false_of_ne hr]

private theorem getReg_setReg_other' (st : State) (r q : Reg) (hne : q ≠ r) (v : Word) :
    (st.setReg r v).getReg q = st.getReg q := by
  unfold State.getReg State.setReg
  split
  · rfl
  · split
    · simp
    · simp [beq_false_of_ne hne]

private theorem setReg_regs_zero' (st : State) (r : Reg) (v : Word) :
    (st.setReg r v).regs 0#5 = st.regs 0#5 := by
  unfold State.setReg
  by_cases hr0 : r == 0#5
  · simp [hr0]
  · simp only [hr0, Bool.false_eq_true, ↓reduceIte]
    have hneq : ((0#5 : Reg) == r) = false := by
      cases heq : (0#5 : Reg) == r with
      | false => rfl
      | true => exact absurd (beq_iff_eq.mpr (beq_iff_eq.mp heq).symm) hr0
    simp [hneq]

private theorem hybrid_step_call_aux (hw : HybridWidths)
    {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    {pre post : List AsmItem} {target : String} {st : State}
    (hrom : RomMatches rom code)
    (hlink : linkHybridWithSpec hw (pre ++ [.call target] ++ post) = .ok (code, labels))
    (h64 : 4 * (totalSizeWith (hybridWordSize hw) pre + hybridWordSize hw (.call target)) < 2 ^ 64)
    (hpc : st.pc = BitVec.ofNat 64 (4 * totalSizeWith (hybridWordSize hw) pre)) :
    ∃ tgt k st', 1 ≤ k ∧
      lookupLabel labels target = some tgt ∧
      RV64.run rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * tgt) ∧
      RegEqExceptT6
        (st.setReg AbiReg.ra
          (BitVec.ofNat 64 (4 * (totalSizeWith (hybridWordSize hw) pre +
            hybridWordSize hw (.call target))))).regs
        st'.regs ∧
      st'.mem = st.mem := by
  rw [totalSizeWith_hybrid_eq] at h64 hpc ⊢
  obtain ⟨is, hres, _, hdec⟩ := linkHybridWithSpec_item_instrs pre (.call target) post hlink
  simp only [resolveHybridItem] at hres
  cases hlook : lookupLabel labels target with
  | none => rw [hlook] at hres; cases hres
  | some tgt =>
    rw [hlook] at hres; dsimp only at hres
    cases hgc : hw.getC target with
    | false =>
      rw [hgc] at hres; simp only [Bool.false_eq_true, ↓reduceIte] at hres
      cases hrg : jalInRange ((tgt : Int) - (hybridTotalWords hw pre : Int)) with
      | false => rw [hrg] at hres; cases hres
      | true =>
        rw [hrg] at hres; simp only [↓reduceIte, Except.ok.injEq] at hres; subst hres
        have hd0 : (code[hybridTotalWords hw pre]?).bind decode =
            some (.jal AbiReg.ra (mkJimm ((tgt : Int) - (hybridTotalWords hw pre : Int)))) := by
          simpa using hdec 0 (by simp)
        have hsz : hybridWordSize hw (.call target) = 1 := by simp [hybridWordSize, hgc]
        let st' : State :=
          { (st.setReg AbiReg.ra (BitVec.ofNat 64 (4 * (hybridTotalWords hw pre + 1)))) with
            pc := BitVec.ofNat 64 (4 * tgt) }
        have hs : RV64.step rom st = .cont st' := by
          rw [step_at_decoded_rom (by rw [hsz] at h64; omega) (rom_decode_of_matches hrom hd0) st hpc]
          simp only [execInstr, st']
          rw [hpc_add_4 st.pc hpc, hpc, pc_add_sextImmJ hrg]
        have hmem : st'.mem = st.mem := by dsimp only [st', State.setReg]; split <;> rfl
        refine ⟨tgt, 1, st', Nat.le_refl 1, rfl, by simp [RV64.run, hs], rfl, ?_, hmem⟩
        rw [hsz]; exact RegEqExceptT6.refl _
    | true =>
      rw [hgc] at hres; simp only [↓reduceIte] at hres
      cases hrg : farInRange ((tgt : Int) - ((hybridTotalWords hw pre + 1 : Nat) : Int)) with
      | false => rw [hrg] at hres; cases hres
      | true =>
        rw [hrg] at hres; simp only [↓reduceIte, Except.ok.injEq] at hres; subst hres
        have hd0 := hdec 0 (by simp)
        have hd1 := hdec 1 (by simp)
        have hd2 := hdec 2 (by simp)
        have hd3 := hdec 3 (by simp)
        simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at hd0 hd1 hd2 hd3
        have hsz : hybridWordSize hw (.call target) = 4 := by simp [hybridWordSize, hgc]
        rw [hsz] at h64 ⊢
        obtain ⟨_, _, _, st', _, _, _, _, hrun, hpc', hra, hget, hmem⟩ :=
          step_far_jalr (rom := rom) (st := st) (pc := hybridTotalWords hw pre) (tgt := tgt)
            (rd := AbiReg.ra) (by decide) (by decide) (by omega) hpc hrg
            (rom_decode_of_matches hrom hd0) (rom_decode_of_matches hrom hd1)
            (rom_decode_of_matches hrom hd2) (rom_decode_of_matches hrom hd3)
        have hzero : st'.regs 0#5 = st.regs 0#5 := run_regs_zero hrun
        let stRa := st.setReg AbiReg.ra (BitVec.ofNat 64 (4 * (hybridTotalWords hw pre + 4)))
        have hregEq : RegEqExceptT6 stRa.regs st'.regs := by
          refine RegEqExceptT6.of_getReg_zero_eq (by rw [setReg_regs_zero', hzero]) ?_
          intro r hr
          by_cases hraEq : r = AbiReg.ra
          · subst hraEq; rw [getReg_setReg_self' st AbiReg.ra (by decide), hra (by decide)]
          · rw [getReg_setReg_other' st AbiReg.ra r hraEq]; exact (hget r hraEq hr.1 hr.2).symm
        exact ⟨tgt, 4, st', by omega, rfl, hrun, hpc', hregEq, hmem⟩

private theorem hybrid_step_branch_core {rom : Rom} {code : Array (BitVec 32)}
    {pc tgt : Nat} {bw : BrWidth} {op : BranchOp} {rs1 rs2 : Reg} {target : String}
    {is : List Instr} {st : State}
    (hrom : RomMatches rom code)
    (hres : resolveBrWith bw op rs1 rs2 target pc tgt = .ok is)
    (hdec : ∀ j, (hj : j < is.length) → (code[pc + j]?).bind decode = some is[j])
    (h64 : 4 * (pc + match bw with | .w1 => 1 | .w2 => 2 | .w3 => 5) < 2 ^ 64)
    (hpc : st.pc = BitVec.ofNat 64 (4 * pc)) :
    ∃ k st', 1 ≤ k ∧
      RV64.run rom k st = .cont st' ∧
      st'.pc = (if evalBranch op (st.getReg rs1) (st.getReg rs2)
                then BitVec.ofNat 64 (4 * tgt)
                else BitVec.ofNat 64 (4 * (pc + match bw with | .w1 => 1 | .w2 => 2 | .w3 => 5))) ∧
      RegEqExceptT6 st.regs st'.regs ∧
      st'.mem = st.mem := by
  cases bw with
  | w1 =>
    simp only [resolveBrWith] at hres
    cases hrg : branchInRange ((tgt : Int) - (pc : Int)) with
    | false => rw [hrg] at hres; cases hres
    | true =>
      rw [hrg] at hres; simp only [↓reduceIte, Except.ok.injEq] at hres; subst hres
      have hd0 : (code[pc]?).bind decode =
          some (.branch op rs1 rs2 (mkBimm ((tgt : Int) - (pc : Int)))) := by
        simpa [branchInstrsFor] using hdec 0 (by simp [branchInstrsFor])
      let nextPc :=
        if evalBranch op (st.getReg rs1) (st.getReg rs2)
        then BitVec.ofNat 64 (4 * tgt)
        else BitVec.ofNat 64 (4 * (pc + 1))
      have hs : RV64.step rom st = .cont { st with pc := nextPc } := by
        rw [step_at_decoded_rom (by omega) (rom_decode_of_matches hrom hd0) st hpc]
        simp only [execInstr, nextPc]
        split
        · rw [hpc, pc_add_sextImmB hrg]
        · rw [hpc_add_4 st.pc hpc]
      exact ⟨1, { st with pc := nextPc }, Nat.le_refl 1, by simp [RV64.run, hs],
        rfl, RegEqExceptT6.refl _, rfl⟩
  | w2 =>
    simp only [resolveBrWith] at hres
    cases hrg : jalInRange ((tgt : Int) - ((pc + 1 : Nat) : Int)) with
    | false => rw [hrg] at hres; cases hres
    | true =>
      rw [hrg] at hres; simp only [↓reduceIte, Except.ok.injEq] at hres; subst hres
      have hd0 : (code[pc]?).bind decode =
          some (.branch (invertBranch op) rs1 rs2 (mkBimm 2)) := by
        simpa [branchInstrsFor] using hdec 0 (by simp [branchInstrsFor])
      have hd1 : (code[pc + 1]?).bind decode =
          some (.jal AbiReg.zero (mkJimm ((tgt : Int) - ((pc + 1 : Nat) : Int)))) := by
        simpa [branchInstrsFor] using hdec 1 (by simp [branchInstrsFor])
      have hcond_inv : evalBranch (invertBranch op) (st.getReg rs1) (st.getReg rs2) =
          !evalBranch op (st.getReg rs1) (st.getReg rs2) :=
        evalBranch_invert op (st.getReg rs1) (st.getReg rs2)
      cases hcond : evalBranch op (st.getReg rs1) (st.getReg rs2) with
      | false =>
        have hinv : evalBranch (invertBranch op) (st.getReg rs1) (st.getReg rs2) = true := by
          rw [hcond_inv, hcond]; rfl
        have hb2 : branchInRange (((pc + 2 : Nat) : Int) - (pc : Int)) = true := by
          simp only [branchInRange, Bool.and_eq_true, decide_eq_true_eq]; omega
        have hpcB : BitVec.ofNat 64 (4 * pc) + sextImmB (mkBimm 2) =
            BitVec.ofNat 64 (4 * (pc + 2)) := by
          have h := pc_add_sextImmB (pc := pc) (tgt := pc + 2) hb2
          have hd : ((pc + 2 : Nat) : Int) - (pc : Int) = 2 := by omega
          rwa [hd] at h
        let st1 : State := { st with pc := BitVec.ofNat 64 (4 * (pc + 2)) }
        have hs0 : RV64.step rom st = .cont st1 := by
          rw [step_at_decoded_rom (by dsimp only at h64; omega) (rom_decode_of_matches hrom hd0) st hpc]
          simp only [execInstr, hinv, ↓reduceIte, st1]; rw [hpc, hpcB]
        exact ⟨1, st1, Nat.le_refl 1, by simp [RV64.run, hs0], by simp [st1],
          RegEqExceptT6.refl _, rfl⟩
      | true =>
        have hinv : evalBranch (invertBranch op) (st.getReg rs1) (st.getReg rs2) = false := by
          rw [hcond_inv, hcond]; rfl
        let st1 : State := { st with pc := BitVec.ofNat 64 (4 * (pc + 1)) }
        have hs0 : RV64.step rom st = .cont st1 := by
          rw [step_at_decoded_rom (by dsimp only at h64; omega) (rom_decode_of_matches hrom hd0) st hpc]
          simp only [execInstr, hinv, Bool.false_eq_true, ↓reduceIte, st1]; rw [hpc_add_4 st.pc hpc]
        let st2 : State := { st1 with pc := BitVec.ofNat 64 (4 * tgt) }
        have hs1 : RV64.step rom st1 = .cont st2 := by
          rw [step_at_decoded_rom (by dsimp only at h64; omega) (rom_decode_of_matches hrom hd1) st1 rfl]
          simp only [execInstr, State.setReg, AbiReg.zero, beq_self_eq_true, ↓reduceIte, st2]
          exact congrArg StepResult.cont (congrArg (fun x => { st1 with pc := x }) (pc_add_sextImmJ hrg))
        exact ⟨2, st2, by omega, by simp [RV64.run, hs0, hs1], by simp [st2],
          RegEqExceptT6.refl _, rfl⟩
  | w3 =>
    simp only [resolveBrWith] at hres
    cases hrg : farInRange ((tgt : Int) - ((pc + 2 : Nat) : Int)) with
    | false => rw [hrg] at hres; cases hres
    | true =>
      rw [hrg] at hres; simp only [↓reduceIte, Except.ok.injEq] at hres; subst hres
      have hd0 : (code[pc]?).bind decode =
          some (.branch (invertBranch op) rs1 rs2 (mkBimm 5)) := by
        simpa [branchInstrsFor] using hdec 0 (by simp [branchInstrsFor])
      have hd1 : (code[pc + 1]?).bind decode =
          some (.jal AbiReg.t6 (mkJimm 1)) := by
        simpa [branchInstrsFor] using hdec 1 (by simp [branchInstrsFor])
      have hd2 : (code[pc + 2]?).bind decode =
          some (.lui AbiReg.s1 (splitFarOffWords ((tgt : Int) - ((pc + 2 : Nat) : Int))).1) := by
        simpa [branchInstrsFor] using hdec 2 (by simp [branchInstrsFor])
      have hd3 : (code[pc + 3]?).bind decode =
          some (.alu .add AbiReg.t6 AbiReg.t6 AbiReg.s1) := by
        simpa [branchInstrsFor] using hdec 3 (by simp [branchInstrsFor])
      have hd4 : (code[pc + 4]?).bind decode =
          some (.jalr AbiReg.zero AbiReg.t6 (splitFarOffWords ((tgt : Int) - ((pc + 2 : Nat) : Int))).2) := by
        simpa [branchInstrsFor] using hdec 4 (by simp [branchInstrsFor])
      cases hcond : evalBranch op (st.getReg rs1) (st.getReg rs2) with
      | false =>
        obtain ⟨st1, _, hrun, hpc1, hregs1, hmem1⟩ :=
          step_far_branch_not_taken (rom := rom) (st := st) (pc := pc) (op := op)
            (rs1 := rs1) (rs2 := rs2) (by dsimp only at h64; omega) hpc hcond (rom_decode_of_matches hrom hd0)
        exact ⟨1, st1, Nat.le_refl 1, hrun, by simp [hpc1],
          RegEqExceptT6.of_eq hregs1.symm, hmem1⟩
      | true =>
        obtain ⟨st5, hrun, hpc5, hget, hmem5⟩ :=
          step_far_branch_taken (rom := rom) (st := st) (pc := pc) (tgt := tgt)
            (op := op) (rs1 := rs1) (rs2 := rs2) (by dsimp only at h64; omega) hpc hrg hcond
            (rom_decode_of_matches hrom hd0) (rom_decode_of_matches hrom hd1)
            (rom_decode_of_matches hrom hd2) (rom_decode_of_matches hrom hd3)
            (rom_decode_of_matches hrom hd4)
        have hzero : st5.regs 0#5 = st.regs 0#5 := run_regs_zero hrun
        have hregEq : RegEqExceptT6 st.regs st5.regs := by
          refine RegEqExceptT6.of_getReg_zero_eq hzero.symm ?_
          intro r hr
          by_cases hr0 : r = 0#5
          · subst hr0; simp [State.getReg]
          · exact (hget r hr.1 hr.2).symm
        exact ⟨5, st5, by omega, hrun, by simp [hpc5], hregEq, hmem5⟩

private theorem resolveHybridWordsGo_word_decoded (hw : HybridWidths) (lm : LabelMap) (pc : Nat)
    (items : List AsmItem) (acc : Array (BitVec 32)) (ws : Array (BitVec 32))
    (hacc : ∀ k, k < acc.size → ∃ inst : Instr, (acc[k]?).bind decode = some inst)
    (hres : resolveHybridWordsGo hw lm pc items acc = .ok ws) :
    ∀ k, k < ws.size → ∃ inst : Instr, (ws[k]?).bind decode = some inst := by
  induction items generalizing pc acc with
  | nil =>
    simp only [resolveHybridWordsGo, Except.ok.injEq] at hres
    subst hres; exact hacc
  | cons item rest ih =>
    simp only [resolveHybridWordsGo] at hres
    cases hi : resolveHybridItem hw lm pc item with
    | error e => rw [hi] at hres; cases hres
    | ok is =>
      rw [hi] at hres
      exact ih (pc + hybridWordSize hw item) (pushEncoded acc is)
        (pushEncoded_word_decoded acc is hacc) hres

/-- Parameterized `LinkModel` backed by `linkHybridWithSpec hw` for **any** `hw : HybridWidths`. -/
def hybridLinkModel (hw : HybridWidths) : LinkModel where
  itemSize := hybridWordSize hw
  itemSize_label _ := rfl
  itemSize_instr _ := rfl
  linkSpec := linkHybridWithSpec hw
  linkSpec_size hlink := by
    rw [totalSizeWith_hybrid_eq]; exact linkHybridWithSpec_size hlink
  word_decoded {items code labels} hlink k hk := by
    simp only [linkHybridWithSpec, bind, Except.bind] at hlink
    cases hcol : collectHybridLabels hw items with
    | error e => rw [hcol] at hlink; cases hlink
    | ok lm =>
      rw [hcol] at hlink; dsimp only at hlink
      cases hres : resolveHybridWordsGo hw lm 0 items #[] with
      | error e => rw [hres] at hlink; cases hlink
      | ok ws =>
        rw [hres] at hlink
        simp only [Except.pure, pure, Except.ok.injEq, Prod.mk.injEq] at hlink
        rcases hlink with ⟨rfl, rfl⟩
        exact resolveHybridWordsGo_word_decoded hw lm 0 items #[] ws (fun _ h => by simp at h) hres k hk
  lookup_label_at {code labels pre name post} hlink := by
    rw [totalSizeWith_hybrid_eq]
    simp only [linkHybridWithSpec, bind, Except.bind] at hlink
    cases hcol : collectHybridLabels hw (pre ++ [.label name] ++ post) with
    | error e => rw [hcol] at hlink; cases hlink
    | ok lm =>
      rw [hcol] at hlink; dsimp only at hlink
      cases hres : resolveHybridWordsGo hw lm 0 (pre ++ [.label name] ++ post) #[] with
      | error e => rw [hres] at hlink; cases hlink
      | ok ws =>
        rw [hres] at hlink
        simp only [Except.pure, pure, Except.ok.injEq, Prod.mk.injEq] at hlink
        rcases hlink with ⟨_, rfl⟩
        exact collectHybridLabels_label_at hw pre post name lm hcol
  step_instr hrom hlink h64 hpc := hybrid_step_instr_aux hw hrom hlink h64 hpc
  step_j hrom hlink h64 hpc := hybrid_step_j_aux hw hrom hlink h64 hpc
  step_call hrom hlink h64 hpc := hybrid_step_call_aux hw hrom hlink h64 hpc
  step_br {rom code labels pre post op rs1 rs2 target st} hrom hlink _ h64 hpc := by
    rw [totalSizeWith_hybrid_eq] at h64 hpc ⊢
    obtain ⟨is, hres, _, hdec⟩ :=
      linkHybridWithSpec_item_instrs pre (.br op rs1 rs2 target) post hlink
    simp only [resolveHybridItem] at hres
    cases hlook : lookupLabel labels target with
    | none => rw [hlook] at hres; cases hres
    | some tgt =>
      rw [hlook] at hres; dsimp only at hres
      dsimp only [hybridWordSize] at h64 ⊢
      obtain ⟨k, st', hk, hrun, hpc', hreg, hmem⟩ :=
        hybrid_step_branch_core hrom hres hdec h64 hpc
      exact ⟨tgt, k, st', hk, rfl, hrun, hpc', hreg, hmem⟩
  step_brLong {rom code labels pre post op rs1 rs2 target st} hrom hlink _ h64 hpc := by
    rw [totalSizeWith_hybrid_eq] at h64 hpc ⊢
    obtain ⟨is, hres, _, hdec⟩ :=
      linkHybridWithSpec_item_instrs pre (.brLong op rs1 rs2 target) post hlink
    simp only [resolveHybridItem] at hres
    cases hlook : lookupLabel labels target with
    | none => rw [hlook] at hres; cases hres
    | some tgt =>
      rw [hlook] at hres; dsimp only at hres
      dsimp only [hybridWordSize] at h64 ⊢
      obtain ⟨k, st', hk, hrun, hpc', hreg, hmem⟩ :=
        hybrid_step_branch_core hrom hres hdec h64 hpc
      exact ⟨tgt, k, st', hk, rfl, hrun, hpc', hreg, hmem⟩

theorem hybrid_totalSize_le_far (hw : HybridWidths) (asm : List AsmItem) :
    (hybridLinkModel hw).totalSize asm ≤ farTotalWords asm := by
  change totalSizeWith (hybridWordSize hw) asm ≤ farTotalWords asm
  rw [totalSizeWith_hybrid_eq]
  exact hybridTotalWords_le_far hw asm

/-! ## 10. Symbolic End-to-End Linker Totality Theorem (No Kernel Reduction!) -/

/-- If `linkFarSpec items` succeeds (`codeFar.size < 2 ^ 22`), then **`linkHybrid items`**
    and **`(hybridLinkModel (computeHybridWidths items)).linkSpec items`** are *guaranteed*
    to succeed with `code.size ≤ farTotalWords items` (without evaluating `relaxCandidateGo`
    inside the Lean kernel!). -/
theorem linkHybrid_ok_of_farSpec {items : List AsmItem}
    (hfar : ∃ codeFar labelsFar, linkFarSpec items = .ok (codeFar, labelsFar)) :
    ∃ code labels,
      (hybridLinkModel (computeHybridWidths items)).linkSpec items = .ok (code, labels) ∧
      linkHybrid items = .ok code ∧
      code.size ≤ farTotalWords items := by
  let cand := relaxCandidateGo 8 items HybridWidths.allNear
  cases hcol : collectHybridLabelsFast cand items with
  | error e =>
    have hhw : computeHybridWidths items = HybridWidths.mkAllFar := by
      simp [computeHybridWidths, cand, hcol]
    rw [hhw]
    obtain ⟨codeFar, labelsFar, hok⟩ := hfar
    have hspec : linkHybridWithSpec HybridWidths.mkAllFar items = .ok (codeFar, labelsFar) :=
      linkHybridWithSpec_allFar_of_far hok
    have hfast : linkHybrid items = .ok codeFar := by
      unfold linkHybrid; rw [hhw, linkHybridWith_eq_spec, hspec]; rfl
    have hsz : codeFar.size = farTotalWords items := linkFarSpec_size hok
    exact ⟨codeFar, labelsFar, hspec, hfast, hsz ▸ Nat.le_refl _⟩
  | ok labs =>
    cases hval : validateHybridGo cand labs 0 items with
    | false =>
      have hhw : computeHybridWidths items = HybridWidths.mkAllFar := by
        simp [computeHybridWidths, cand, hcol, hval]
      rw [hhw]
      obtain ⟨codeFar, labelsFar, hok⟩ := hfar
      have hspec : linkHybridWithSpec HybridWidths.mkAllFar items = .ok (codeFar, labelsFar) :=
        linkHybridWithSpec_allFar_of_far hok
      have hfast : linkHybrid items = .ok codeFar := by
        unfold linkHybrid; rw [hhw, linkHybridWith_eq_spec, hspec]; rfl
      have hsz : codeFar.size = farTotalWords items := linkFarSpec_size hok
      exact ⟨codeFar, labelsFar, hspec, hfast, hsz ▸ Nat.le_refl _⟩
    | true =>
      have hhw : computeHybridWidths items = cand := by
        simp [computeHybridWidths, cand, hcol, hval]
      rw [hhw]
      obtain ⟨ws, hgo, hsz⟩ := resolveHybridWordsFastGo_of_validate cand labs 0 items #[] hval
      have hmap : linkHybridWithMap cand items = .ok (ws, labs) := by
        simp [linkHybridWithMap, bind, Except.bind, hcol, hgo, pure, Except.pure]
      obtain ⟨lm, hspec, _⟩ := (linkHybridWithMap_eq_spec cand items).1 ws labs hmap
      have hfast : linkHybrid items = .ok ws := by
        unfold linkHybrid; rw [hhw, linkHybridWith_eq_spec, hspec]; rfl
      have hszLe : ws.size ≤ farTotalWords items := by
        have h1 : ws.size = hybridTotalWords cand items := by simpa using hsz
        rw [h1]; exact hybridTotalWords_le_far cand items
      exact ⟨ws, lm, hspec, hfast, hszLe⟩

theorem linkHybrid_ok_linkSpec {items : List AsmItem} {code : Array (BitVec 32)}
    (h : linkHybrid items = .ok code) :
    ∃ labels, (hybridLinkModel (computeHybridWidths items)).linkSpec items = .ok (code, labels) :=
  linkHybridWith_ok_spec h

/-! ## 11. Axiom Cleanliness Guards -/

/--
info: 'ConAgua.RISCV.Linker.hybridLinkModel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hybridLinkModel

/--
info: 'ConAgua.RISCV.Linker.linkHybrid_ok_of_farSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms linkHybrid_ok_of_farSpec

/--
info: 'ConAgua.RISCV.Linker.linkHybrid_ok_linkSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms linkHybrid_ok_linkSpec

end ConAgua.RISCV.Linker
