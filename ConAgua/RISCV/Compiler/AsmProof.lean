import ConAgua.RISCV.RV64.Roundtrip
import ConAgua.RISCV.Compiler.Asm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Linker & Macro Correctness Proofs (`ConAgua.RISCV.Compiler.AsmProof`)

Proves:
1. Exact signed offset arithmetic (`sextImmB_mkBimm`, `sextImmJ_mkJimm`, `pc_add_sextImmB`, `pc_add_sextImmJ`).
2. `evalBranch_invert`: `invertBranch op` negates `evalBranch op`.
3. `linkResolved_item_spec` & `linkWithLabels_word_decode`: every word in the linked
   `Array (BitVec 32)` at word index `k` decodes to the expected `Instr` with exact target
   offsets (`pc + sextImm = target_pc`) for `j`, `call`, `br`, and `brLong` veneers,
   and every label resolves to its exact word index.
-/

namespace ConAgua.RISCV.Compiler

open ConAgua.RISCV.RV64

/-! ## 1. Signed Offset Arithmetic & Branch Inversion -/

private theorem toInt_ofInt_eq {n : Nat} (hn : 0 < n) (z : Int)
    (hlo : -(2 ^ (n - 1) : Int) ≤ z) (hhi : z < (2 ^ (n - 1) : Int)) :
    (BitVec.ofInt n z).toInt = z := by
  rw [BitVec.toInt_ofInt]
  have hpow : (2 : Int) ^ n = 2 * (2 ^ (n - 1) : Int) := by
    cases n with
    | zero => omega
    | succ m => simp [Int.pow_succ, Int.mul_comm]
  rw [Int.bmod_def]
  push_cast
  have hmod : z % ((2 : Int) ^ n) = if 0 ≤ z then z else z + (2 : Int) ^ n := by
    split
    · next h0 => exact Int.emod_eq_of_lt h0 (by omega)
    · next h0 =>
      have h1 : 0 ≤ z + (2 : Int) ^ n := by omega
      have h2 : z + (2 : Int) ^ n < (2 : Int) ^ n := by omega
      have heq : (z + (2 : Int) ^ n) % ((2 : Int) ^ n) = z % ((2 : Int) ^ n) := by
        rw [Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]
      rw [← heq, Int.emod_eq_of_lt h1 h2]
  rw [hmod]
  split <;> split <;> omega

private theorem sext_append_zero_12 (bimm : BitVec 12) :
    sextImmB bimm = BitVec.ofInt 64 (2 * bimm.toInt) := by
  unfold sextImmB
  apply BitVec.eq_of_toInt_eq
  have h1 : (bimm ++ 0#1).toInt = 2 * bimm.toInt := by
    rw [BitVec.toInt_append]; simp
  have hlo : -(2 ^ 11 : Int) ≤ bimm.toInt := BitVec.le_toInt bimm
  have hhi : bimm.toInt < (2 ^ 11 : Int) := BitVec.toInt_lt
  rw [BitVec.toInt_signExtend]
  have hmin : min 64 (12 + 1) = 13 := by decide
  rw [hmin, h1, ← BitVec.toInt_ofInt (n := 13) (2 * bimm.toInt)]
  rw [toInt_ofInt_eq (by omega) (2 * bimm.toInt) (by omega) (by omega)]
  rw [toInt_ofInt_eq (by omega) (2 * bimm.toInt) (by omega) (by omega)]

private theorem sext_append_zero_20 (jimm : BitVec 20) :
    sextImmJ jimm = BitVec.ofInt 64 (2 * jimm.toInt) := by
  unfold sextImmJ
  apply BitVec.eq_of_toInt_eq
  have h1 : (jimm ++ 0#1).toInt = 2 * jimm.toInt := by
    rw [BitVec.toInt_append]; simp
  have hlo : -(2 ^ 19 : Int) ≤ jimm.toInt := BitVec.le_toInt jimm
  have hhi : jimm.toInt < (2 ^ 19 : Int) := BitVec.toInt_lt
  rw [BitVec.toInt_signExtend]
  have hmin : min 64 (20 + 1) = 21 := by decide
  rw [hmin, h1, ← BitVec.toInt_ofInt (n := 21) (2 * jimm.toInt)]
  rw [toInt_ofInt_eq (by omega) (2 * jimm.toInt) (by omega) (by omega)]
  rw [toInt_ofInt_eq (by omega) (2 * jimm.toInt) (by omega) (by omega)]

theorem sextImmB_mkBimm {diff : Int} (h : branchInRange diff = true) :
    sextImmB (mkBimm diff) = BitVec.ofInt 64 (4 * diff) := by
  simp only [branchInRange, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [sext_append_zero_12]
  unfold mkBimm
  rw [toInt_ofInt_eq (by omega) (2 * diff) (by omega) (by omega)]
  congr 1; omega

theorem sextImmJ_mkJimm {diff : Int} (h : jalInRange diff = true) :
    sextImmJ (mkJimm diff) = BitVec.ofInt 64 (4 * diff) := by
  simp only [jalInRange, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [sext_append_zero_20]
  unfold mkJimm
  rw [toInt_ofInt_eq (by omega) (2 * diff) (by omega) (by omega)]
  congr 1; omega

theorem pc_add_sextImmB {pc tgt : Nat} (h : branchInRange ((tgt : Int) - (pc : Int)) = true) :
    BitVec.ofNat 64 (4 * pc) + sextImmB (mkBimm ((tgt : Int) - (pc : Int))) = BitVec.ofNat 64 (4 * tgt) := by
  rw [sextImmB_mkBimm h]
  rw [show BitVec.ofNat 64 (4 * pc) = BitVec.ofInt 64 (4 * (pc : Int)) from rfl]
  rw [show BitVec.ofNat 64 (4 * tgt) = BitVec.ofInt 64 (4 * (tgt : Int)) from rfl]
  rw [← BitVec.ofInt_add]
  congr 1; omega

theorem pc_add_sextImmJ {pc tgt : Nat} (h : jalInRange ((tgt : Int) - (pc : Int)) = true) :
    BitVec.ofNat 64 (4 * pc) + sextImmJ (mkJimm ((tgt : Int) - (pc : Int))) = BitVec.ofNat 64 (4 * tgt) := by
  rw [sextImmJ_mkJimm h]
  rw [show BitVec.ofNat 64 (4 * pc) = BitVec.ofInt 64 (4 * (pc : Int)) from rfl]
  rw [show BitVec.ofNat 64 (4 * tgt) = BitVec.ofInt 64 (4 * (tgt : Int)) from rfl]
  rw [← BitVec.ofInt_add]
  congr 1; omega

theorem evalBranch_invert (op : BranchOp) (a b : Word) :
    evalBranch (invertBranch op) a b = !evalBranch op a b := by
  cases op <;> simp [invertBranch, evalBranch, bne]

/-! ## 2. Linker Pass 1 & Pass 2 Structural Lemmas -/

theorem totalWords_nil : totalWords [] = 0 := rfl

private theorem foldl_wordSize_add (xs : List AsmItem) (n : Nat) :
    xs.foldl (fun acc item => acc + item.wordSize) n = n + totalWords xs := by
  induction xs generalizing n with
  | nil => simp [totalWords]
  | cons x xs ih =>
    simp only [List.foldl_cons, totalWords] at *
    rw [ih (n + x.wordSize), ih (0 + x.wordSize)]
    omega

theorem totalWords_cons (x : AsmItem) (xs : List AsmItem) :
    totalWords (x :: xs) = x.wordSize + totalWords xs := by
  unfold totalWords
  simp only [List.foldl_cons, Nat.zero_add]
  exact foldl_wordSize_add xs x.wordSize

theorem totalWords_append (xs ys : List AsmItem) :
    totalWords (xs ++ ys) = totalWords xs + totalWords ys := by
  induction xs with
  | nil => simp [totalWords_nil]
  | cons x xs ih => simp [totalWords_cons, ih, Nat.add_assoc]

private theorem collectLabelsGo_preserved (items : List AsmItem) (pc : Nat)
    (acc lm : LabelMap) (h : collectLabelsGo items pc acc = .ok lm)
    (name : String) (v : Nat) (hacc : lookupLabel acc name = some v) :
    lookupLabel lm name = some v := by
  induction items generalizing pc acc with
  | nil =>
    simp only [collectLabelsGo, Except.ok.injEq] at h
    subst h; exact hacc
  | cons item rest ih =>
    cases item with
    | label n =>
      simp only [collectLabelsGo] at h
      cases hlook : lookupLabel acc n with
      | some _ => rw [hlook] at h; cases h
      | none =>
        rw [hlook] at h
        apply ih pc ((n, pc) :: acc) h
        simp only [lookupLabel]
        split
        · next heq =>
          have : n = name := beq_iff_eq.mp heq
          subst this; rw [hlook] at hacc; cases hacc
        · exact hacc
    | _ => exact ih (pc + _) acc h hacc

private theorem collectLabelsGo_append (xs ys : List AsmItem) (pc : Nat) (acc lm : LabelMap)
    (h : collectLabelsGo (xs ++ ys) pc acc = .ok lm) :
    ∃ mid, collectLabelsGo xs pc acc = .ok mid ∧
           collectLabelsGo ys (pc + totalWords xs) mid = .ok lm := by
  induction xs generalizing pc acc with
  | nil =>
    simp only [List.nil_append, collectLabelsGo, totalWords_nil, Nat.add_zero] at *
    exact ⟨acc, rfl, h⟩
  | cons x xs ih =>
    cases x with
    | label n =>
      simp only [List.cons_append, collectLabelsGo, totalWords_cons, AsmItem.wordSize,
        Nat.zero_add] at *
      cases hlook : lookupLabel acc n with
      | some _ => rw [hlook] at h; cases h
      | none =>
        rw [hlook] at h
        exact ih pc ((n, pc) :: acc) h
    | _ =>
      simp only [List.cons_append, collectLabelsGo, totalWords_cons] at *
      obtain ⟨mid, h1, h2⟩ := ih (pc + _) acc h
      refine ⟨mid, h1, ?_⟩
      simpa [Nat.add_assoc] using h2

theorem collectLabels_label_at (pre post : List AsmItem) (name : String) (lm : LabelMap)
    (h : collectLabels (pre ++ [.label name] ++ post) = .ok lm) :
    lookupLabel lm name = some (totalWords pre) := by
  unfold collectLabels at h
  rw [List.append_assoc] at h
  obtain ⟨mid, _, hpost⟩ := collectLabelsGo_append pre ([.label name] ++ post) 0 [] lm h
  simp only [Nat.zero_add, List.singleton_append, collectLabelsGo] at hpost
  cases hlook : lookupLabel mid name with
  | some _ => rw [hlook] at hpost; cases hpost
  | none =>
    rw [hlook] at hpost
    apply collectLabelsGo_preserved post (totalWords pre) ((name, totalWords pre) :: mid) lm hpost
    simp [lookupLabel]

theorem resolveItem_length {lm : LabelMap} {pc : Nat} {item : AsmItem} {is : List Instr}
    (h : resolveItem lm pc item = .ok is) : is.length = item.wordSize := by
  cases item <;> simp only [resolveItem, AsmItem.wordSize] at h ⊢
  · cases h; rfl
  · cases h; rfl
  · rename_i target
    cases hlook : lookupLabel lm target <;> simp [hlook] at h
    split at h <;> cases h; rfl
  · rename_i target
    cases hlook : lookupLabel lm target <;> simp [hlook] at h
    split at h <;> cases h; rfl
  · rename_i op rs1 rs2 target
    cases hlook : lookupLabel lm target <;> simp [hlook] at h
    split at h <;> cases h; rfl
  · rename_i op rs1 rs2 target
    cases hlook : lookupLabel lm target <;> simp [hlook] at h
    split at h <;> cases h; rfl

private theorem resolveItemsGo_append_acc (lm : LabelMap) (pc : Nat) (items : List AsmItem)
    (acc arr : Array Instr) :
    resolveItemsGo lm pc items acc = .ok arr ↔
      ∃ tail, resolveItemsGo lm pc items #[] = .ok tail ∧ arr = acc ++ tail := by
  induction items generalizing pc acc arr with
  | nil =>
    simp only [resolveItemsGo, Except.ok.injEq]
    constructor
    · intro h; exact ⟨#[], rfl, by simp [h]⟩
    · rintro ⟨tail, h1, h2⟩; cases h1; simp [h2]
  | cons item rest ih =>
    simp only [resolveItemsGo, bind, Except.bind]
    cases hitem : resolveItem lm pc item with
    | error e =>
      simp only []
      constructor
      · intro h; cases h
      · rintro ⟨tail, h1, _⟩; cases h1
    | ok is =>
      simp only []
      rw [ih (pc + item.wordSize) (acc ++ is.toArray) arr]
      constructor
      · rintro ⟨tail, h1, h2⟩
        have hres : resolveItemsGo lm (pc + item.wordSize) rest is.toArray = .ok (is.toArray ++ tail) :=
          (ih (pc + item.wordSize) is.toArray (is.toArray ++ tail)).mpr ⟨tail, h1, rfl⟩
        exact ⟨is.toArray ++ tail, by simpa using hres, by simp [h2, Array.append_assoc]⟩
      · rintro ⟨tail, h1, h2⟩
        obtain ⟨tail', h1', htail⟩ := (ih (pc + item.wordSize) is.toArray tail).mp (by simpa using h1)
        exact ⟨tail', h1', by simp [htail, h2, Array.append_assoc]⟩

private theorem resolveItemsGo_size (lm : LabelMap) (pc : Nat) (items : List AsmItem)
    (acc arr : Array Instr) (h : resolveItemsGo lm pc items acc = .ok arr) :
    arr.size = acc.size + totalWords items := by
  induction items generalizing pc acc with
  | nil =>
    simp only [resolveItemsGo, Except.ok.injEq] at h
    subst h; simp [totalWords_nil]
  | cons item rest ih =>
    simp only [resolveItemsGo, bind, Except.bind] at h
    cases hitem : resolveItem lm pc item with
    | error e => rw [hitem] at h; cases h
    | ok is =>
      rw [hitem] at h
      dsimp only at h
      have hlen := resolveItem_length hitem
      have ih' := ih (pc + item.wordSize) (acc ++ is.toArray) h
      have hsz : is.toArray.size = is.length := by simp
      rw [ih', Array.size_append, hsz, hlen, totalWords_cons]
      omega

private theorem resolveItemsGo_split (lm : LabelMap) (pc : Nat) (xs ys : List AsmItem)
    (acc arr : Array Instr) (h : resolveItemsGo lm pc (xs ++ ys) acc = .ok arr) :
    ∃ a1 a2, resolveItemsGo lm pc xs #[] = .ok a1 ∧
             resolveItemsGo lm (pc + totalWords xs) ys #[] = .ok a2 ∧
             a1.size = totalWords xs ∧
             arr = acc ++ a1 ++ a2 := by
  induction xs generalizing pc acc with
  | nil =>
    simp only [List.nil_append, totalWords_nil, Nat.add_zero] at *
    rw [resolveItemsGo_append_acc] at h
    obtain ⟨a2, ha2, harr⟩ := h
    exact ⟨#[], a2, rfl, ha2, rfl, by simpa using harr⟩
  | cons x xs ih =>
    simp only [List.cons_append, resolveItemsGo, bind, Except.bind, totalWords_cons] at h ⊢
    cases hx : resolveItem lm pc x with
    | error e => rw [hx] at h; cases h
    | ok is =>
      rw [hx] at h
      dsimp only at h ⊢
      obtain ⟨a1, a2, h1, h2, hsz, harr⟩ := ih (pc + x.wordSize) (acc ++ is.toArray) h
      have hlen := resolveItem_length hx
      refine ⟨is.toArray ++ a1, a2, (resolveItemsGo_append_acc lm (pc + x.wordSize) xs (#[] ++ is.toArray) (is.toArray ++ a1)).mpr ⟨a1, h1, by simp⟩, ?_, ?_, ?_⟩
      · simpa [Nat.add_assoc] using h2
      · simp [hlen, hsz]
      · simp [harr, Array.append_assoc]

private theorem resolveItemsGo_singleton (lm : LabelMap) (pc : Nat) (it : AsmItem)
    (a : Array Instr) (h : resolveItemsGo lm pc [it] #[] = .ok a) :
    ∃ is, resolveItem lm pc it = .ok is ∧ a = is.toArray := by
  simp only [resolveItemsGo, bind, Except.bind] at h
  cases hit : resolveItem lm pc it with
  | error e => rw [hit] at h; cases h
  | ok is =>
    rw [hit] at h
    dsimp only at h
    simp only [Except.ok.injEq] at h
    exact ⟨is, rfl, by simpa using h.symm⟩

/-! ## 3. Core Linker Theorem: Item-Level and Word-Level Decode Specifications -/

/-- Semantics of a single item `it` at word offset `pc` inside linked code `code` with `labels`. -/
def ItemDecodedAt (code : Array (BitVec 32)) (labels : LabelMap) (pc : Nat) : AsmItem → Prop
  | .label name =>
    lookupLabel labels name = some pc
  | .instr inst =>
    (code[pc]?).bind decode = some inst
  | .j target =>
    ∃ tgt jimm, lookupLabel labels target = some tgt ∧
      (code[pc]?).bind decode = some (.jal AbiReg.zero jimm) ∧
      BitVec.ofNat 64 (4 * pc) + sextImmJ jimm = BitVec.ofNat 64 (4 * tgt)
  | .call target =>
    ∃ tgt jimm, lookupLabel labels target = some tgt ∧
      (code[pc]?).bind decode = some (.jal AbiReg.ra jimm) ∧
      BitVec.ofNat 64 (4 * pc) + sextImmJ jimm = BitVec.ofNat 64 (4 * tgt)
  | .br op rs1 rs2 target =>
    ∃ tgt bimm, lookupLabel labels target = some tgt ∧
      (code[pc]?).bind decode = some (.branch op rs1 rs2 bimm) ∧
      BitVec.ofNat 64 (4 * pc) + sextImmB bimm = BitVec.ofNat 64 (4 * tgt)
  | .brLong op rs1 rs2 target =>
    ∃ tgt bimm8 jimm, lookupLabel labels target = some tgt ∧
      (code[pc]?).bind decode = some (.branch (invertBranch op) rs1 rs2 bimm8) ∧
      BitVec.ofNat 64 (4 * pc) + sextImmB bimm8 = BitVec.ofNat 64 (4 * (pc + 2)) ∧
      (code[pc + 1]?).bind decode = some (.jal AbiReg.zero jimm) ∧
      BitVec.ofNat 64 (4 * (pc + 1)) + sextImmJ jimm = BitVec.ofNat 64 (4 * tgt)

private theorem array_getElem?_append_middle {α : Type} (a b c : Array α) (i : Nat)
    (hi : i < b.size) :
    (a ++ b ++ c)[a.size + i]? = some b[i] := by
  have h1 : a.size + i < (a ++ b).size := by simp [hi]
  rw [Array.getElem?_append_left h1, Array.getElem?_append_right (by omega)]
  simp [hi]

theorem linkResolved_size {items : List AsmItem} {code : Array (BitVec 32)} {labels : LabelMap}
    (hlink : linkResolved items = .ok (code, labels)) :
    code.size = totalWords items := by
  simp only [linkResolved, bind, Except.bind] at hlink
  cases hcol : collectLabels items with
  | error e => rw [hcol] at hlink; cases hlink
  | ok lm =>
    rw [hcol] at hlink; dsimp only at hlink
    cases hres : resolveItems lm items with
    | error e => rw [hres] at hlink; cases hlink
    | ok instrs =>
      rw [hres] at hlink; dsimp only at hlink
      simp only [Except.pure, pure, Except.ok.injEq, Prod.mk.injEq] at hlink
      rcases hlink with ⟨rfl, _⟩
      simpa using resolveItemsGo_size lm 0 items #[] instrs hres

/-- Core linker theorem: any item `it` at `pre ++ [it] ++ post` in a `linkResolved` program
    decodes at `pc = totalWords pre` to its exact `Instr`(s) with exact target offset. -/
theorem linkResolved_item_spec (pre : List AsmItem) (it : AsmItem) (post : List AsmItem)
    (code : Array (BitVec 32)) (labels : LabelMap)
    (hlink : linkResolved (pre ++ [it] ++ post) = .ok (code, labels)) :
    ItemDecodedAt code labels (totalWords pre) it := by
  simp only [linkResolved, bind, Except.bind] at hlink
  cases hcol : collectLabels (pre ++ [it] ++ post) with
  | error e => rw [hcol] at hlink; cases hlink
  | ok lm =>
    rw [hcol] at hlink; dsimp only at hlink
    cases hres : resolveItems lm (pre ++ [it] ++ post) with
    | error e => rw [hres] at hlink; cases hlink
    | ok instrs =>
      rw [hres] at hlink; dsimp only at hlink
      simp only [Except.pure, pure, Except.ok.injEq, Prod.mk.injEq] at hlink
      rcases hlink with ⟨rfl, rfl⟩
      unfold resolveItems at hres
      rw [List.append_assoc] at hres
      obtain ⟨a1, a23, _, h23, ha1sz, hinstrs⟩ :=
        resolveItemsGo_split lm 0 pre ([it] ++ post) #[] instrs hres
      simp only [Nat.zero_add] at h23
      obtain ⟨a2, a3, h2, _, _, ha23⟩ :=
        resolveItemsGo_split lm (totalWords pre) [it] post #[] a23 h23
      have hfull : instrs = a1 ++ a2 ++ a3 := by
        rw [hinstrs, ha23]; simp [Array.append_assoc]
      have hget : ∀ (j : Nat) (hj : j < a2.size),
          (instrs.map encode)[totalWords pre + j]? = some (encode a2[j]) := by
        intro j hj
        rw [hfull, ← ha1sz]
        simp only [Array.map_append]
        rw [← Array.size_map (f := encode) (xs := a1)]
        rw [array_getElem?_append_middle _ _ _ j (by simpa using hj)]
        simp
      obtain ⟨is, his, rfl⟩ := resolveItemsGo_singleton lm (totalWords pre) it a2 h2
      cases it with
      | label name =>
        exact collectLabels_label_at pre post name lm hcol
      | instr inst =>
        simp only [resolveItem, Except.ok.injEq] at his
        subst his
        have hw := hget 0 (by simp)
        simp only [Nat.add_zero] at hw
        simp only [ItemDecodedAt, hw, Option.bind_some, List.getElem_toArray,
          List.getElem_cons_zero, decode_encode]
      | j target =>
        simp only [resolveItem] at his
        cases hlook : lookupLabel lm target with
        | none => rw [hlook] at his; cases his
        | some tgt =>
          rw [hlook] at his
          by_cases hrange : jalInRange ((tgt : Int) - (totalWords pre : Int)) = true
          · simp only [hrange, ↓reduceIte, Except.ok.injEq] at his
            subst his
            have hw := hget 0 (by simp)
            simp only [Nat.add_zero] at hw
            refine ⟨tgt, mkJimm ((tgt : Int) - (totalWords pre : Int)), hlook, ?_, pc_add_sextImmJ hrange⟩
            simp only [hw, Option.bind_some, List.getElem_toArray, List.getElem_cons_zero]
            exact decode_encode _
          · simp [hrange] at his
      | call target =>
        simp only [resolveItem] at his
        cases hlook : lookupLabel lm target with
        | none => rw [hlook] at his; cases his
        | some tgt =>
          rw [hlook] at his
          by_cases hrange : jalInRange ((tgt : Int) - (totalWords pre : Int)) = true
          · simp only [hrange, ↓reduceIte, Except.ok.injEq] at his
            subst his
            have hw := hget 0 (by simp)
            simp only [Nat.add_zero] at hw
            refine ⟨tgt, mkJimm ((tgt : Int) - (totalWords pre : Int)), hlook, ?_, pc_add_sextImmJ hrange⟩
            simp only [hw, Option.bind_some, List.getElem_toArray, List.getElem_cons_zero]
            exact decode_encode _
          · simp [hrange] at his
      | br op rs1 rs2 target =>
        simp only [resolveItem] at his
        cases hlook : lookupLabel lm target with
        | none => rw [hlook] at his; cases his
        | some tgt =>
          rw [hlook] at his
          by_cases hrange : branchInRange ((tgt : Int) - (totalWords pre : Int)) = true
          · simp only [hrange, ↓reduceIte, Except.ok.injEq] at his
            subst his
            have hw := hget 0 (by simp)
            simp only [Nat.add_zero] at hw
            refine ⟨tgt, mkBimm ((tgt : Int) - (totalWords pre : Int)), hlook, ?_, pc_add_sextImmB hrange⟩
            simp only [hw, Option.bind_some, List.getElem_toArray, List.getElem_cons_zero]
            exact decode_encode _
          · simp [hrange] at his
      | brLong op rs1 rs2 target =>
        simp only [resolveItem] at his
        cases hlook : lookupLabel lm target with
        | none => rw [hlook] at his; cases his
        | some tgt =>
          rw [hlook] at his
          by_cases hrange : jalInRange ((tgt : Int) - ((totalWords pre + 1 : Nat) : Int)) = true
          · simp only [hrange, ↓reduceIte, Except.ok.injEq] at his
            subst his
            have hw0 := hget 0 (by simp)
            have hw1 := hget 1 (by simp)
            simp only [Nat.add_zero] at hw0
            refine ⟨tgt, mkBimm 2, mkJimm ((tgt : Int) - ((totalWords pre + 1 : Nat) : Int)), hlook, ?_, ?_, ?_, ?_⟩
            · simp only [hw0, Option.bind_some, List.getElem_toArray, List.getElem_cons_zero]
              exact decode_encode _
            · have h2r : branchInRange (((totalWords pre + 2 : Nat) : Int) - (totalWords pre : Int)) = true := by
                simp [branchInRange]; omega
              have h2eq : mkBimm 2 = mkBimm (((totalWords pre + 2 : Nat) : Int) - (totalWords pre : Int)) := by
                congr 1; omega
              rw [h2eq]
              exact pc_add_sextImmB h2r
            · simp only [hw1, Option.bind_some, List.getElem_toArray,
                List.getElem_cons_succ, List.getElem_cons_zero]
              exact decode_encode _
            · exact pc_add_sextImmJ hrange
          · push_cast at hrange; simp [hrange] at his

/-- Every word index `k < totalWords items` falls inside a unique concrete item in `items`. -/
theorem exists_split_at_word (items : List AsmItem) (k : Nat) (hk : k < totalWords items) :
    ∃ pre it post, items = pre ++ [it] ++ post ∧
      totalWords pre ≤ k ∧ k < totalWords pre + it.wordSize := by
  induction items generalizing k with
  | nil => simp [totalWords_nil] at hk
  | cons x xs ih =>
    rw [totalWords_cons] at hk
    by_cases hlt : k < x.wordSize
    · exact ⟨[], x, xs, rfl, by simp [totalWords_nil], by simp [totalWords_nil, hlt]⟩
    · have hge : x.wordSize ≤ k := by omega
      obtain ⟨pre, it, post, hsplit, hlo, hhi⟩ := ih (k - x.wordSize) (by omega)
      refine ⟨x :: pre, it, post, ?_, ?_, ?_⟩
      · simp [hsplit]
      · rw [totalWords_cons]; omega
      · rw [totalWords_cons]; omega

/-- Universal word-level linker correctness theorem:
    If `linkWithLabels prog = .ok (code, labels)`, then there exists a relaxed item list
    `relaxed` such that every word index `k < code.size` is owned by an item in `relaxed`
    whose emitted word(s) decode to the exact expected `Instr` with exact target offset. -/
theorem linkWithLabels_word_decode (prog : List AsmItem) (code : Array (BitVec 32))
    (labels : LabelMap) (hlink : linkWithLabels prog = .ok (code, labels)) :
    ∃ relaxed, relax prog = .ok relaxed ∧
      code.size = totalWords relaxed ∧
      (∀ k, k < code.size →
        ∃ pre it post, relaxed = pre ++ [it] ++ post ∧
          totalWords pre ≤ k ∧ k < totalWords pre + it.wordSize ∧
          ItemDecodedAt code labels (totalWords pre) it) := by
  simp only [linkWithLabels, bind, Except.bind] at hlink
  cases hrel : relax prog with
  | error e => rw [hrel] at hlink; cases hlink
  | ok relaxed =>
    rw [hrel] at hlink; dsimp only at hlink
    have hsz := linkResolved_size hlink
    refine ⟨relaxed, rfl, hsz, fun k hk => ?_⟩
    rw [hsz] at hk
    obtain ⟨pre, it, post, hsplit, hlo, hhi⟩ := exists_split_at_word relaxed k hk
    refine ⟨pre, it, post, hsplit, hlo, hhi, ?_⟩
    rw [hsplit] at hlink
    exact linkResolved_item_spec pre it post code labels hlink

/-- info: 'ConAgua.RISCV.Compiler.linkWithLabels_word_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms linkWithLabels_word_decode

end ConAgua.RISCV.Compiler

namespace ConAgua.RISCV.RV64

theorem evalAlu_mul_eq (a b : Word) : evalAlu .mul a b = a * b := rfl

theorem evalAlu_mulhu_eq (a b : Word) :
    evalAlu .mulhu a b = BitVec.ofNat 64 ((a.toNat * b.toNat) / 2 ^ 64) := by
  dsimp [evalAlu]
  apply BitVec.eq_of_toNat_eq
  dsimp [BitVec.extractLsb', BitVec.zeroExtend]
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  have hltA : a.toNat < 2 ^ 64 := a.isLt
  have hltB : b.toNat < 2 ^ 64 := b.isLt
  have hltA128 : a.toNat < 2 ^ 128 := by omega
  have hltB128 : b.toNat < 2 ^ 128 := by omega
  have hprod : a.toNat * b.toNat < 2 ^ 128 := by
    have hle : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  rw [Nat.mod_eq_of_lt hltA128, Nat.mod_eq_of_lt hltB128, Nat.mod_eq_of_lt hprod,
      Nat.shiftRight_eq_div_pow]

end ConAgua.RISCV.RV64
