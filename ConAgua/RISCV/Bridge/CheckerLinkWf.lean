import ConAgua.RISCV.Bridge.CheckerLinkNoT6
import ConAgua.RISCV.Bridge.CheckerLinkLabels
import ConAgua.RISCV.Bridge.CheckerLinkSizeCheck

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Algebraic Far-Linker Well-Formedness for `checkerChipAsm` (`ConAgua.RISCV.Bridge.CheckerLinkWf`)

Pure kernel-checked algebraic proofs (zero `sorry`, zero `native_decide`, zero `bv_decide`,
standard axioms `[propext, Classical.choice, Quot.sound]` only) establishing all `FarLink` /
`farLinkModel` / `LinkModel` / `HybridLink` preconditions for the unified `checkerChipAsm` firmware (`ca_start` + `ca_start_c` + shared compiled functions):

1. **`checkerChipAsm_noT6Branch`:** No `.br` or `.brLong` pseudo-instruction anywhere in
   `compileE`, `compileC`, `compileS`, `compileFn`, `checkerDriverAsm`, or
   `checkerCmpDriverAsm` references scratch register `AbiReg.t6` (`x31`).
2. **`*_lblNames_nodup` & `*_collectFarLabels_ok`:** Purely algebraic scoping proofs showing
   every label in `checkerChipAsm` is distinct and
   `collectFarLabels ... = .ok labels`.
3. **`*_farTotalWords_lt`:** Exact algebraic per-function word-count bound + single-pass
   kernel `rfl` bound check over `checkerProgMini` (`1,966` fns) proving
   `farTotalWords ... < 2 ^ 22` (fitting both the 24-bit `icache_dm` word address space and
   the `±2 GiB` `farInRange` window).
4. **`checkerChipAsm_linkFarSpec_ok`, `checkerChipAsm_linkFar_ok`, & `checkerChipAsm_linkHybrid_ok`:** All branch/jump/call
   targets exist in `labels` and lie in `farInRange`, so `farLinkModel.linkSpec`, `linkFar`,
   and `linkHybrid` all succeed with `code.size < 2 ^ 22`.
-/

namespace ConAgua.RISCV.Bridge

open ConAgua.RISCV.RV64
open ConAgua.RISCV.Compiler
open ConAgua.RISCV.Linker
open _root_.L

/-! ## 6. General `collectFarLabels` & `linkFarSpec` Soundness + `checkerChipAsm` Instantiation -/

private theorem lookupLabel_cons (k : String) (v : Nat) (acc : LabelMap) (s : String) :
    lookupLabel ((k, v) :: acc) s = if k == s then some v else lookupLabel acc s := rfl

private theorem collectFarLabelsGo_ok_le :
    ∀ (items : List AsmItem) (pc : Nat) (acc : LabelMap),
      (lblNames items).Nodup →
      (∀ s ∈ lblNames items, lookupLabel acc s = none) →
      (∀ s k, lookupLabel acc s = some k → k ≤ pc) →
      ∃ labels, collectFarLabelsGo items pc acc = .ok labels ∧
        (∀ s, (lookupLabel labels s).isSome ↔ (lookupLabel acc s).isSome ∨ s ∈ lblNames items) ∧
        (∀ s k, lookupLabel labels s = some k → k ≤ pc + farTotalWords items) := by
  intro items
  induction items with
  | nil =>
    intro pc acc _ _ hacc_le
    refine ⟨acc, rfl, fun s => by simp [lblNames], fun s k hk => ?_⟩
    simpa [farTotalWords] using hacc_le s k hk
  | cons item rest ih =>
    intro pc acc hnd hdis hacc_le
    rw [farTotalWords_cons]
    cases item with
    | label name =>
      simp only [lblNames, List.filterMap_cons, List.nodup_cons] at hnd hdis ⊢
      have hnone : lookupLabel acc name = none := hdis name (by simp)
      have hdis' : ∀ s ∈ lblNames rest, lookupLabel ((name, pc) :: acc) s = none := by
        intro s hs
        rw [lookupLabel_cons]
        have hne : (name == s) = false := beq_false_of_ne (fun heq => hnd.1 (heq ▸ hs))
        rw [hne]
        exact hdis s (List.mem_cons_of_mem _ hs)
      have hacc_le' : ∀ s k, lookupLabel ((name, pc) :: acc) s = some k → k ≤ pc := by
        intro s k hk
        rw [lookupLabel_cons] at hk
        split at hk
        · cases hk; exact Nat.le_refl _
        · exact hacc_le s k hk
      obtain ⟨labels, hcol, hmem, hle⟩ := ih pc ((name, pc) :: acc) hnd.2 hdis' hacc_le'
      refine ⟨labels, ?_, fun s => ?_, fun s k hk => ?_⟩
      · unfold collectFarLabelsGo
        dsimp only
        rw [hnone]
        exact hcol
      · rw [hmem s, lookupLabel_cons]
        by_cases hns : name = s
        · subst hns; simp
        · have hf : (name == s) = false := beq_false_of_ne hns
          simp only [hf, Bool.false_eq_true, ↓reduceIte]
          change _ ∨ s ∈ lblNames rest ↔ _ ∨ s ∈ name :: lblNames rest
          constructor <;> intro h
          · exact h.elim Or.inl (fun hs => Or.inr (List.mem_cons_of_mem _ hs))
          · exact h.elim Or.inl (fun hs => Or.inr ((List.mem_cons.mp hs).resolve_left (fun heq => hns heq.symm)))
      · simpa [farWordSize] using hle s k hk
    | instr i =>
      simp only [lblNames, List.filterMap_cons] at hnd hdis ⊢
      obtain ⟨labels, hcol, hmem, hle⟩ := ih (pc + 1) acc hnd hdis (fun s k hk => Nat.le_trans (hacc_le s k hk) (by omega))
      refine ⟨labels, ?_, hmem, fun s k hk => ?_⟩
      · unfold collectFarLabelsGo; exact hcol
      · have := hle s k hk; simpa [farWordSize, Nat.add_assoc] using this
    | j t =>
      simp only [lblNames, List.filterMap_cons] at hnd hdis ⊢
      obtain ⟨labels, hcol, hmem, hle⟩ := ih (pc + 4) acc hnd hdis (fun s k hk => Nat.le_trans (hacc_le s k hk) (by omega))
      refine ⟨labels, ?_, hmem, fun s k hk => ?_⟩
      · unfold collectFarLabelsGo; exact hcol
      · have := hle s k hk; simpa [farWordSize, Nat.add_assoc] using this
    | «call» t =>
      simp only [lblNames, List.filterMap_cons] at hnd hdis ⊢
      obtain ⟨labels, hcol, hmem, hle⟩ := ih (pc + 4) acc hnd hdis (fun s k hk => Nat.le_trans (hacc_le s k hk) (by omega))
      refine ⟨labels, ?_, hmem, fun s k hk => ?_⟩
      · unfold collectFarLabelsGo; exact hcol
      · have := hle s k hk; simpa [farWordSize, Nat.add_assoc] using this
    | br op r1 r2 t =>
      simp only [lblNames, List.filterMap_cons] at hnd hdis ⊢
      obtain ⟨labels, hcol, hmem, hle⟩ := ih (pc + 5) acc hnd hdis (fun s k hk => Nat.le_trans (hacc_le s k hk) (by omega))
      refine ⟨labels, ?_, hmem, fun s k hk => ?_⟩
      · unfold collectFarLabelsGo; exact hcol
      · have := hle s k hk; simpa [farWordSize, Nat.add_assoc] using this
    | brLong op r1 r2 t =>
      simp only [lblNames, List.filterMap_cons] at hnd hdis ⊢
      obtain ⟨labels, hcol, hmem, hle⟩ := ih (pc + 5) acc hnd hdis (fun s k hk => Nat.le_trans (hacc_le s k hk) (by omega))
      refine ⟨labels, ?_, hmem, fun s k hk => ?_⟩
      · unfold collectFarLabelsGo; exact hcol
      · have := hle s k hk; simpa [farWordSize, Nat.add_assoc] using this

theorem collectFarLabels_ok_of_nodup {items : List AsmItem} (hnd : (lblNames items).Nodup) :
    ∃ labels, collectFarLabels items = .ok labels ∧
      (∀ s, (lookupLabel labels s).isSome ↔ s ∈ lblNames items) ∧
      (∀ s k, lookupLabel labels s = some k → k ≤ farTotalWords items) := by
  obtain ⟨labels, hcol, hmem, hle⟩ := collectFarLabelsGo_ok_le items 0 [] hnd
    (fun _ _ => rfl) (fun _ _ h => by cases h)
  refine ⟨labels, hcol, fun s => ?_, fun s k hk => by simpa using hle s k hk⟩
  simpa [lookupLabel] using hmem s

private theorem pushEncoded_size (acc : Array (BitVec 32)) (is : List Instr) :
    (pushEncoded acc is).size = acc.size + is.length := by
  induction is generalizing acc with
  | nil => simp [pushEncoded]
  | cons i is ih =>
    simp only [pushEncoded, List.length_cons]
    rw [ih]
    simp [Array.size_push]; omega

private theorem farInRange_of_lt {pc tgt bound : Nat} (hb : bound < 2 ^ 29 - 513)
    (hpc : pc ≤ bound) (htgt : tgt ≤ bound) :
    farInRange ((tgt : Int) - (pc : Int)) = true := by
  simp only [farInRange, Bool.and_eq_true, decide_eq_true_eq]
  omega

private theorem resolveFarWordsGo_ok (labels : LabelMap) (totalBound : Nat)
    (hb : totalBound < 2 ^ 29 - 513)
    (hlbls : ∀ s k, lookupLabel labels s = some k → k ≤ totalBound) :
    ∀ (items : List AsmItem) (pc : Nat) (acc : Array (BitVec 32)),
      pc + farTotalWords items ≤ totalBound →
      (∀ t ∈ targetsIn items, (lookupLabel labels t).isSome = true) →
      ∃ words, resolveFarWordsGo labels pc items acc = .ok words ∧
        words.size = acc.size + farTotalWords items := by
  intro items
  induction items with
  | nil =>
    intro pc acc _ _
    exact ⟨acc, rfl, by simp [farTotalWords]⟩
  | cons item rest ih =>
    intro pc acc hpc htgt
    rw [farTotalWords_cons] at hpc
    have hitem_ok : ∃ is, resolveFarItem labels pc item = .ok is ∧ is.length = farWordSize item := by
      cases item with
      | label _ => exact ⟨[], rfl, rfl⟩
      | instr i => exact ⟨[i], rfl, rfl⟩
      | j t =>
        have hmem : (lookupLabel labels t).isSome = true := htgt t (by simp [targetsIn])
        cases hl : lookupLabel labels t with
        | none => rw [hl] at hmem; simp at hmem
        | some tgt =>
          have hrg := farInRange_of_lt hb (show pc + 1 ≤ totalBound by simp [farWordSize] at hpc; omega) (hlbls t tgt hl)
          have hrg' : farInRange ((tgt : Int) - ((pc : Int) + 1)) = true :=
            (show (tgt : Int) - ((pc + 1 : Nat) : Int) = (tgt : Int) - ((pc : Int) + 1) by omega) ▸ hrg
          dsimp [resolveFarItem]; rw [hl]; dsimp only; rw [hrg']; simp only [↓reduceIte]
          exact ⟨_, rfl, by simp [farInstrsFor, farWordSize]⟩
      | «call» t =>
        have hmem : (lookupLabel labels t).isSome = true := htgt t (by simp [targetsIn])
        cases hl : lookupLabel labels t with
        | none => rw [hl] at hmem; simp at hmem
        | some tgt =>
          have hrg := farInRange_of_lt hb (show pc + 1 ≤ totalBound by simp [farWordSize] at hpc; omega) (hlbls t tgt hl)
          have hrg' : farInRange ((tgt : Int) - ((pc : Int) + 1)) = true :=
            (show (tgt : Int) - ((pc + 1 : Nat) : Int) = (tgt : Int) - ((pc : Int) + 1) by omega) ▸ hrg
          dsimp [resolveFarItem]; rw [hl]; dsimp only; rw [hrg']; simp only [↓reduceIte]
          exact ⟨_, rfl, by simp [farInstrsFor, farWordSize]⟩
      | br op r1 r2 t =>
        have hmem : (lookupLabel labels t).isSome = true := htgt t (by simp [targetsIn])
        cases hl : lookupLabel labels t with
        | none => rw [hl] at hmem; simp at hmem
        | some tgt =>
          have hrg := farInRange_of_lt hb (show pc + 2 ≤ totalBound by simp [farWordSize] at hpc; omega) (hlbls t tgt hl)
          have hrg' : farInRange ((tgt : Int) - ((pc : Int) + 2)) = true :=
            (show (tgt : Int) - ((pc + 2 : Nat) : Int) = (tgt : Int) - ((pc : Int) + 2) by omega) ▸ hrg
          dsimp [resolveFarItem]; rw [hl]; dsimp only; rw [hrg']; simp only [↓reduceIte]
          exact ⟨_, rfl, by simp [farInstrsFor, farWordSize]⟩
      | brLong op r1 r2 t =>
        have hmem : (lookupLabel labels t).isSome = true := htgt t (by simp [targetsIn])
        cases hl : lookupLabel labels t with
        | none => rw [hl] at hmem; simp at hmem
        | some tgt =>
          have hrg := farInRange_of_lt hb (show pc + 2 ≤ totalBound by simp [farWordSize] at hpc; omega) (hlbls t tgt hl)
          have hrg' : farInRange ((tgt : Int) - ((pc : Int) + 2)) = true :=
            (show (tgt : Int) - ((pc + 2 : Nat) : Int) = (tgt : Int) - ((pc : Int) + 2) by omega) ▸ hrg
          dsimp [resolveFarItem]; rw [hl]; dsimp only; rw [hrg']; simp only [↓reduceIte]
          exact ⟨_, rfl, by simp [farInstrsFor, farWordSize]⟩
    obtain ⟨is, hres, hlen⟩ := hitem_ok
    have htgt_rest : ∀ t ∈ targetsIn rest, (lookupLabel labels t).isSome = true := by
      intro t ht
      apply htgt t
      cases item <;> simp only [targetsIn, List.filterMap_cons]
      · exact ht
      · exact ht
      · exact List.mem_cons_of_mem _ ht
      · exact List.mem_cons_of_mem _ ht
      · exact List.mem_cons_of_mem _ ht
      · exact List.mem_cons_of_mem _ ht
    obtain ⟨words, hgo, hsz⟩ := ih (pc + farWordSize item) (pushEncoded acc is)
      (by omega) htgt_rest
    refine ⟨words, ?_, ?_⟩
    · unfold resolveFarWordsGo
      rw [hres]
      exact hgo
    · rw [hsz, pushEncoded_size, hlen, farTotalWords_cons]
      omega

theorem linkFarSpec_ok_of_wf {items : List AsmItem}
    (hnd : (lblNames items).Nodup)
    (hlt : farTotalWords items < 2 ^ 22)
    (htgt : ∀ t ∈ targetsIn items, t ∈ lblNames items) :
    ∃ code labels, farLinkModel.linkSpec items = .ok (code, labels) ∧
      code.size = farTotalWords items := by
  obtain ⟨labels, hcol, hmem, hle⟩ := collectFarLabels_ok_of_nodup hnd
  have htgt' : ∀ t ∈ targetsIn items, (lookupLabel labels t).isSome = true :=
    fun t ht => (hmem t).mpr (htgt t ht)
  obtain ⟨words, hgo, hsz⟩ := resolveFarWordsGo_ok labels (farTotalWords items)
    (by omega) hle items 0 #[] (by omega) htgt'
  refine ⟨words, labels, ?_, by simpa using hsz⟩
  change linkFarSpec items = .ok (words, labels)
  simp [linkFarSpec, hcol, hgo, bind, Except.bind, pure, Except.pure]

/-! ### Target-Resolution Proofs for `checkerChipAsm` -/

private theorem targetsIn_cons_instr (i : Instr) (xs : List AsmItem) :
    targetsIn (.instr i :: xs) = targetsIn xs := rfl
private theorem targetsIn_cons_label (s : String) (xs : List AsmItem) :
    targetsIn (.label s :: xs) = targetsIn xs := rfl
private theorem targetsIn_cons_j (t : String) (xs : List AsmItem) :
    targetsIn (.j t :: xs) = t :: targetsIn xs := rfl
private theorem targetsIn_cons_call (t : String) (xs : List AsmItem) :
    targetsIn (.call t :: xs) = t :: targetsIn xs := rfl
private theorem targetsIn_cons_br (op : BranchOp) (r1 r2 : Reg) (t : String) (xs : List AsmItem) :
    targetsIn (.br op r1 r2 t :: xs) = t :: targetsIn xs := rfl
private theorem targetsIn_cons_brLong (op : BranchOp) (r1 r2 : Reg) (t : String) (xs : List AsmItem) :
    targetsIn (.brLong op r1 r2 t :: xs) = t :: targetsIn xs := rfl

private theorem lblNames_cons_label (s : String) (xs : List AsmItem) :
    lblNames (.label s :: xs) = s :: lblNames xs := rfl
private theorem lblNames_cons_instr (i : Instr) (xs : List AsmItem) :
    lblNames (.instr i :: xs) = lblNames xs := rfl
private theorem lblNames_cons_j (t : String) (xs : List AsmItem) :
    lblNames (.j t :: xs) = lblNames xs := rfl
private theorem lblNames_cons_call (t : String) (xs : List AsmItem) :
    lblNames (.call t :: xs) = lblNames xs := rfl
private theorem lblNames_cons_br (op : BranchOp) (r1 r2 : Reg) (t : String) (xs : List AsmItem) :
    lblNames (.br op r1 r2 t :: xs) = lblNames xs := rfl
private theorem lblNames_cons_brLong (op : BranchOp) (r1 r2 : Reg) (t : String) (xs : List AsmItem) :
    lblNames (.brLong op r1 r2 t :: xs) = lblNames xs := rfl

private theorem emitShrMaskFrom_targetsIn (fl : FrameLayout) (rd : Reg) (inner : Expr)
    (lsh : Nat) (lm : BitVec 6) (compInner : Unit → List AsmItem)
    (hi : ∀ t ∈ targetsIn (compInner ()), t = errLabel)
    (t : String) (hm : t ∈ targetsIn (emitShrMaskFrom fl rd inner lsh lm compInner)) :
    t = errLabel := by
  dsimp only [emitShrMaskFrom] at hm
  cases hri : exprReg? fl.alloc inner with
  | some ri =>
    simp only [hri] at hm
    have hs1 : targetsIn (if (lsh == 0) = true then (if (rd == ri) = true then [] else [Asm.mv rd ri])
        else [Asm.slli rd ri (BitVec.ofNat 6 lsh)]) = [] := by
      split
      · split <;> rfl
      · rfl
    simp only [targetsIn_append, targetsIn_nil, hs1, Asm.srli, targetsIn_cons_instr,
      List.nil_append, List.not_mem_nil] at hm
  | none =>
    simp only [hri] at hm
    have hs1 : targetsIn (if (lsh == 0) = true then (if (rd == AbiReg.a0) = true then [] else [Asm.mv rd AbiReg.a0])
        else [Asm.slli rd AbiReg.a0 (BitVec.ofNat 6 lsh)]) = [] := by
      split
      · split <;> rfl
      · rfl
    simp only [targetsIn_append, targetsIn_nil, hs1, Asm.srli, targetsIn_cons_instr,
      List.append_nil] at hm
    exact hi t hm

private theorem emitLd32hPlainFrom_targetsIn (tab : Tab) (fl : FrameLayout)
    (rd : Reg) (a : ArrId) (i : Expr) (hi : Bool) (compI0 : Unit → List AsmItem)
    (hcomp : ∀ t ∈ targetsIn (compI0 ()), t = errLabel)
    (t : String) (hm : t ∈ targetsIn (emitLd32hPlainFrom tab fl rd a i hi compI0)) :
    t = errLabel := by
  dsimp only [emitLd32hPlainFrom] at hm
  cases hri : exprReg? fl.alloc i with
  | some ri =>
    simp only [hri, targetsIn_append, List.mem_append,
      targetsIn_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
      targetsIn_of_allInstrs (ld32hTail_allInstrs _ _ _ _ _),
      Asm.bgeu, targetsIn_nil, targetsIn_cons_br,
      List.mem_cons, List.mem_nil_iff, false_or, or_false] at hm
    exact hm
  | none =>
    simp only [hri, targetsIn_append, List.mem_append,
      targetsIn_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
      targetsIn_of_allInstrs (ld32hTail_allInstrs _ _ _ _ _),
      Asm.bgeu, targetsIn_nil, targetsIn_cons_br,
      List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with hm | rfl
    · exact hcomp t hm
    · exact rfl

private theorem emitLd32hFrom_targetsIn (tab : Tab) (fl : FrameLayout)
    (tmp : Nat) (rd : Reg) (a : ArrId) (th i : Expr) (hi : Bool)
    (compI0 compT0 compI1 : Unit → List AsmItem)
    (hi0 : ∀ t ∈ targetsIn (compI0 ()), t = errLabel)
    (ht0 : ∀ t ∈ targetsIn (compT0 ()), t = errLabel)
    (hi1 : ∀ t ∈ targetsIn (compI1 ()), t = errLabel)
    (t : String) (hm : t ∈ targetsIn (emitLd32hFrom tab fl tmp rd a th i hi compI0 compT0 compI1)) :
    t = errLabel := by
  dsimp only [emitLd32hFrom] at hm
  cases hcv : th.constVal? with
  | some _ =>
    simp only [hcv] at hm
    cases hii : exprReg? fl.alloc i with
    | some _ =>
      simp only [hii, targetsIn_append, List.mem_append,
        targetsIn_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
        targetsIn_of_allInstrs (ld32hTail_allInstrs _ _ _ _ _),
        Asm.bgeu, targetsIn_nil, targetsIn_cons_br,
        List.mem_cons, List.mem_nil_iff, false_or, or_false] at hm
      exact hm
    | none =>
      simp only [hii, targetsIn_append, List.mem_append,
        targetsIn_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
        targetsIn_of_allInstrs (ld32hTail_allInstrs _ _ _ _ _),
        Asm.bgeu, targetsIn_nil, targetsIn_cons_br,
        List.mem_cons, List.mem_nil_iff, or_false] at hm
      rcases hm with hm | rfl
      · exact hi0 t hm
      · exact rfl
  | none =>
    simp only [hcv] at hm
    cases hth : exprReg? fl.alloc th with
    | some rt =>
      cases hi' : exprReg? fl.alloc i with
      | some ri =>
        simp only [hth, hi', targetsIn_append, List.mem_append,
          targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
          targetsIn_of_allInstrs (ld32hTail_allInstrs _ _ _ _ _),
          Asm.andi, Asm.slli, Asm.add, Asm.bgeu,
          targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
          List.mem_cons, List.mem_nil_iff, false_or, or_false] at hm
        exact hm
      | none =>
        simp only [hth, hi', targetsIn_append, List.mem_append,
          targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
          targetsIn_of_allInstrs (ld32hTail_allInstrs _ _ _ _ _),
          Asm.andi, Asm.slli, Asm.add, Asm.bgeu,
          targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
          List.mem_cons, List.mem_nil_iff, or_false] at hm
        rcases hm with hm | rfl
        · exact hi0 t hm
        · exact rfl
    | none =>
      cases hst : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 th with
      | some ct =>
        cases hi' : exprReg? fl.alloc i with
        | some ri =>
          simp only [hth, hst, hi', targetsIn_append, List.mem_append,
            targetsIn_of_allInstrs (emitSimpleExprR_allInstrs hst),
            targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
            targetsIn_of_allInstrs (ld32hTail_allInstrs _ _ _ _ _),
            Asm.andi, Asm.slli, Asm.add, Asm.bgeu,
            targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
            List.mem_cons, List.mem_nil_iff, false_or, or_false] at hm
          exact hm
        | none =>
          simp only [hth, hst, hi', targetsIn_append, List.mem_append,
            targetsIn_of_allInstrs (emitSimpleExprR_allInstrs hst),
            targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
            targetsIn_of_allInstrs (ld32hTail_allInstrs _ _ _ _ _),
            Asm.andi, Asm.slli, Asm.add, Asm.bgeu,
            targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
            List.mem_cons, List.mem_nil_iff, or_false] at hm
          rcases hm with hm | rfl
          · exact hi0 t hm
          · exact rfl
      | none =>
        simp only [hth, hst, targetsIn_append, List.mem_append, or_assoc,
          targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
          targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
          targetsIn_of_allInstrs (ld32hTail_allInstrs _ _ _ _ _),
          Asm.andi, Asm.slli, Asm.add, Asm.bgeu,
          targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
          List.mem_cons, List.mem_nil_iff, or_false] at hm
        rcases hm with hm | hm | rfl
        · exact ht0 t hm
        · exact hi1 t hm
        · exact rfl

private theorem compileBinFallback_targetsIn (tab : Tab) (fl : FrameLayout)
    (tmp : Nat) (rd : Reg) (op : BinOp) (a b : Expr)
    (compA0 compB0 compB1 : Unit → List AsmItem)
    (ha0 : ∀ t ∈ targetsIn (compA0 ()), t = errLabel)
    (hb0 : ∀ t ∈ targetsIn (compB0 ()), t = errLabel)
    (hb1 : ∀ t ∈ targetsIn (compB1 ()), t = errLabel)
    (t : String) (hm : t ∈ targetsIn (compileBinFallback tab fl tmp rd op a b compA0 compB0 compB1)) :
    t = errLabel := by
  dsimp only [compileBinFallback] at hm
  cases hbv : b.constVal? with
  | some w =>
    simp only [hbv] at hm
    cases ha : exprReg? fl.alloc a with
    | some ra =>
      simp only [ha] at hm
      rw [targetsIn_of_allInstrs (emitBinConstRhsTo_allInstrs rd ra op w)] at hm; cases hm
    | none =>
      simp only [ha, targetsIn_append, List.mem_append,
        targetsIn_of_allInstrs (emitBinConstRhsTo_allInstrs rd AbiReg.a0 op w),
        List.mem_nil_iff, or_false] at hm
      exact ha0 t hm
  | none =>
    simp only [hbv] at hm
    cases hav : a.constVal? with
    | some w =>
      simp only [hav] at hm
      cases hb : exprReg? fl.alloc b with
      | some rb =>
        simp only [hb] at hm
        cases op with
        | add | and | or | xor | mul | «mulhi» =>
          dsimp only at hm
          rw [List.nil_append, targetsIn_of_allInstrs (emitBinConstRhsTo_allInstrs rd rb _ w)] at hm; cases hm
        | sub =>
          dsimp only at hm; split at hm
          · simp only [List.nil_append, Asm.sub, targetsIn_cons_instr, targetsIn_nil, List.not_mem_nil] at hm
          · simp only [List.nil_append, targetsIn_append,
              targetsIn_of_allInstrs (li_allInstrs _ _), Asm.sub,
              targetsIn_nil, targetsIn_cons_instr, List.mem_nil_iff] at hm
        | shl | shr =>
          dsimp only at hm
          simp only [List.nil_append, targetsIn_append,
            targetsIn_of_allInstrs (li_allInstrs _ _), Asm.sll, Asm.srl,
            targetsIn_nil, targetsIn_cons_instr, List.mem_nil_iff] at hm
      | none =>
        simp only [hb] at hm
        cases op with
        | add | and | or | xor | mul | «mulhi» =>
          dsimp only at hm
          simp only [targetsIn_append, List.mem_append,
            targetsIn_of_allInstrs (emitBinConstRhsTo_allInstrs rd AbiReg.a0 _ w),
            List.mem_nil_iff, or_false] at hm
          exact hb0 t hm
        | sub =>
          dsimp only at hm; split at hm
          · simp only [targetsIn_append, List.mem_append, Asm.sub,
              targetsIn_nil, targetsIn_cons_instr, List.mem_nil_iff, or_false] at hm
            exact hb0 t hm
          · simp only [targetsIn_append, List.mem_append,
              targetsIn_of_allInstrs (li_allInstrs _ _), Asm.sub,
              targetsIn_nil, targetsIn_cons_instr, List.mem_nil_iff, or_false] at hm
            exact hb0 t hm
        | shl | shr =>
          dsimp only at hm
          simp only [targetsIn_append, List.mem_append,
            targetsIn_of_allInstrs (li_allInstrs _ _), Asm.sll, Asm.srl,
            targetsIn_nil, targetsIn_cons_instr, List.mem_nil_iff, or_false] at hm
          exact hb0 t hm
    | none =>
      simp only [hav] at hm
      cases hb : exprReg? fl.alloc b with
      | some rb =>
        simp only [hb] at hm
        cases ha : exprReg? fl.alloc a with
        | some ra =>
          simp only [ha] at hm
          rw [targetsIn_of_allInstrs (emitBinOp_allInstrs op rd ra rb)] at hm; cases hm
        | none =>
          simp only [ha, targetsIn_append, List.mem_append,
            targetsIn_of_allInstrs (emitBinOp_allInstrs op rd AbiReg.a0 rb),
            List.mem_nil_iff, or_false] at hm
          exact ha0 t hm
      | none =>
        simp only [hb] at hm
        cases ha : exprReg? fl.alloc a with
        | some ra =>
          simp only [ha, targetsIn_append, List.mem_append,
            targetsIn_of_allInstrs (emitBinOp_allInstrs op rd ra AbiReg.a0),
            List.mem_nil_iff, or_false] at hm
          exact hb0 t hm
        | none =>
          simp only [ha] at hm
          cases hsb : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 b with
          | some cb =>
            simp only [hsb, targetsIn_append, List.mem_append,
              targetsIn_of_allInstrs (emitSimpleExprR_allInstrs hsb),
              targetsIn_of_allInstrs (emitBinOp_allInstrs op _ _ _),
              List.mem_nil_iff, or_false] at hm
            exact ha0 t hm
          | none =>
            simp only [hsb] at hm
            cases hsa : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 a with
            | some ca =>
              simp only [hsa, targetsIn_append, List.mem_append,
                targetsIn_of_allInstrs (emitSimpleExprR_allInstrs hsa),
                targetsIn_of_allInstrs (emitBinOp_allInstrs op _ _ _),
                List.mem_nil_iff, or_false] at hm
              exact hb0 t hm
            | none =>
              simp only [hsa] at hm
              split at hm
              · simp only [targetsIn_append, List.mem_append, Asm.mv,
                  targetsIn_cons_instr, targetsIn_nil,
                  targetsIn_of_allInstrs (emitBinOp_allInstrs op _ _ _),
                  List.mem_nil_iff, or_false] at hm
                rcases hm with hm | hm
                · exact ha0 t hm
                · exact hb0 t hm
              · simp only [targetsIn_append, List.mem_append,
                  targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
                  targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
                  targetsIn_of_allInstrs (emitBinOp_allInstrs op _ _ _),
                  List.mem_nil_iff, or_false] at hm
                rcases hm with hm | hm
                · exact ha0 t hm
                · exact hb1 t hm

private theorem compileETo_targetsIn_aux (tab : Tab) (fl : FrameLayout)
    (e : Expr) (tmp : Nat) (rd : Reg) (t : String)
    (hm : t ∈ targetsIn (compileETo tab fl tmp rd e)) :
    t = errLabel := by
  match e with
  | .const _ =>
    dsimp only [compileETo] at hm
    rw [targetsIn_of_allInstrs (li_allInstrs _ _)] at hm; cases hm
  | .var x =>
    dsimp only [compileETo] at hm
    split at hm
    · split at hm
      · cases hm
      · simp only [Asm.mv, targetsIn_cons_instr, targetsIn_nil, List.not_mem_nil] at hm
    · rw [targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _)] at hm; cases hm
  | .len8 _ | .len64 _ | .glob _ =>
    dsimp only [compileETo] at hm
    rw [targetsIn_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _)] at hm; cases hm
  | .bin op a b =>
    unfold compileETo at hm
    dsimp only at hm
    split at hm
    · split at hm
      · split at hm
        · exact emitShrMaskFrom_targetsIn fl rd _ _ _ _
            (fun x hx => compileETo_targetsIn_aux tab fl _ tmp AbiReg.a0 x hx) t hm
        · exact compileBinFallback_targetsIn tab fl tmp rd _ _ _ _ _ _
            (fun x hx => compileETo_targetsIn_aux tab fl _ tmp AbiReg.a0 x hx)
            (fun x hx => compileETo_targetsIn_aux tab fl _ tmp AbiReg.a0 x hx)
            (fun x hx => compileETo_targetsIn_aux tab fl _ (tmp + 1) AbiReg.a0 x hx) t hm
      · exact compileBinFallback_targetsIn tab fl tmp rd _ _ _ _ _ _
          (fun x hx => compileETo_targetsIn_aux tab fl _ tmp AbiReg.a0 x hx)
          (fun x hx => compileETo_targetsIn_aux tab fl _ tmp AbiReg.a0 x hx)
          (fun x hx => compileETo_targetsIn_aux tab fl _ (tmp + 1) AbiReg.a0 x hx) t hm
    · exact emitLd32hPlainFrom_targetsIn tab fl rd _ _ false _
        (fun x hx => compileETo_targetsIn_aux tab fl _ tmp AbiReg.a0 x hx) t hm
    · exact emitLd32hPlainFrom_targetsIn tab fl rd _ _ true _
        (fun x hx => compileETo_targetsIn_aux tab fl _ tmp AbiReg.a0 x hx) t hm
    · exact emitLd32hFrom_targetsIn tab fl tmp rd _ _ _ false _ _ _
        (fun x hx => compileETo_targetsIn_aux tab fl _ tmp AbiReg.a0 x hx)
        (fun x hx => compileETo_targetsIn_aux tab fl _ tmp AbiReg.a0 x hx)
        (fun x hx => compileETo_targetsIn_aux tab fl _ (tmp + 1) AbiReg.a0 x hx) t hm
    · exact emitLd32hFrom_targetsIn tab fl tmp rd _ _ _ true _ _ _
        (fun x hx => compileETo_targetsIn_aux tab fl _ tmp AbiReg.a0 x hx)
        (fun x hx => compileETo_targetsIn_aux tab fl _ tmp AbiReg.a0 x hx)
        (fun x hx => compileETo_targetsIn_aux tab fl _ (tmp + 1) AbiReg.a0 x hx) t hm
    · exact compileBinFallback_targetsIn tab fl tmp rd op a b _ _ _
        (fun x hx => compileETo_targetsIn_aux tab fl a tmp AbiReg.a0 x hx)
        (fun x hx => compileETo_targetsIn_aux tab fl b tmp AbiReg.a0 x hx)
        (fun x hx => compileETo_targetsIn_aux tab fl b (tmp + 1) AbiReg.a0 x hx) t hm
  | .cmpw c a b =>
    have iha := fun k r x hx => compileETo_targetsIn_aux tab fl a k r x hx
    have ihb := fun k r x hx => compileETo_targetsIn_aux tab fl b k r x hx
    dsimp only [compileETo] at hm
    split at hm
    · cases ha : exprReg? fl.alloc a with
      | some _ => simp only [ha, Asm.sltiu, targetsIn_cons_instr, targetsIn_nil, List.not_mem_nil] at hm
      | none =>
        simp only [ha, targetsIn_append, List.mem_append, Asm.sltiu,
          targetsIn_nil, targetsIn_cons_instr, List.mem_nil_iff, or_false] at hm
        exact iha tmp AbiReg.a0 t hm
    · split at hm
      · cases hb : exprReg? fl.alloc b with
        | some _ => simp only [hb, Asm.sltiu, targetsIn_cons_instr, targetsIn_nil, List.not_mem_nil] at hm
        | none =>
          simp only [hb, targetsIn_append, List.mem_append, Asm.sltiu,
            targetsIn_nil, targetsIn_cons_instr, List.mem_nil_iff, or_false] at hm
          exact ihb tmp AbiReg.a0 t hm
      · split at hm
        · cases ha : exprReg? fl.alloc a with
          | some _ => simp only [ha, Asm.sltu, targetsIn_cons_instr, targetsIn_nil, List.not_mem_nil] at hm
          | none =>
            simp only [ha, targetsIn_append, List.mem_append, Asm.sltu,
              targetsIn_nil, targetsIn_cons_instr, List.mem_nil_iff, or_false] at hm
            exact iha tmp AbiReg.a0 t hm
        · split at hm
          · cases hb : exprReg? fl.alloc b with
            | some _ => simp only [hb, Asm.sltu, targetsIn_cons_instr, targetsIn_nil, List.not_mem_nil] at hm
            | none =>
              simp only [hb, targetsIn_append, List.mem_append, Asm.sltu,
                targetsIn_nil, targetsIn_cons_instr, List.mem_nil_iff, or_false] at hm
              exact ihb tmp AbiReg.a0 t hm
          · cases hb : exprReg? fl.alloc b with
            | some rb =>
              simp only [hb] at hm
              cases ha : exprReg? fl.alloc a with
              | some ra =>
                simp only [ha] at hm
                rw [targetsIn_of_allInstrs (emitCmpwTo_allInstrs rd c ra rb)] at hm; cases hm
              | none =>
                simp only [ha, targetsIn_append, List.mem_append,
                  targetsIn_of_allInstrs (emitCmpwTo_allInstrs rd c AbiReg.a0 rb),
                  List.mem_nil_iff, or_false] at hm
                exact iha tmp AbiReg.a0 t hm
            | none =>
              simp only [hb] at hm
              cases ha : exprReg? fl.alloc a with
              | some ra =>
                simp only [ha, targetsIn_append, List.mem_append,
                  targetsIn_of_allInstrs (emitCmpwTo_allInstrs rd c ra AbiReg.a0),
                  List.mem_nil_iff, or_false] at hm
                exact ihb tmp AbiReg.a0 t hm
              | none =>
                simp only [ha] at hm
                cases hsb : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 b with
                | some cb =>
                  simp only [hsb, targetsIn_append, List.mem_append,
                    targetsIn_of_allInstrs (emitSimpleExprR_allInstrs hsb),
                    targetsIn_of_allInstrs (emitCmpwTo_allInstrs rd c _ _),
                    List.mem_nil_iff, or_false] at hm
                  exact iha tmp AbiReg.a0 t hm
                | none =>
                  simp only [hsb] at hm
                  cases hsa : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 a with
                  | some ca =>
                    simp only [hsa, targetsIn_append, List.mem_append,
                      targetsIn_of_allInstrs (emitSimpleExprR_allInstrs hsa),
                      targetsIn_of_allInstrs (emitCmpwTo_allInstrs rd c _ _),
                      List.mem_nil_iff, or_false] at hm
                    exact ihb tmp AbiReg.a0 t hm
                  | none =>
                    simp only [hsa] at hm
                    split at hm
                    · simp only [targetsIn_append, List.mem_append, Asm.mv,
                        targetsIn_cons_instr, targetsIn_nil,
                        targetsIn_of_allInstrs (emitCmpwTo_allInstrs rd c _ _),
                        List.mem_nil_iff, or_false] at hm
                      rcases hm with hm | hm
                      · exact iha tmp AbiReg.a0 t hm
                      · exact ihb tmp AbiReg.a0 t hm
                    · simp only [targetsIn_append, List.mem_append,
                        targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
                        targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
                        targetsIn_of_allInstrs (emitCmpwTo_allInstrs rd c _ _),
                        List.mem_nil_iff, or_false] at hm
                      rcases hm with hm | hm
                      · exact iha tmp AbiReg.a0 t hm
                      · exact ihb (tmp + 1) AbiReg.a0 t hm
  | .ld8 _ i =>
    have ih := fun k r x hx => compileETo_targetsIn_aux tab fl i k r x hx
    dsimp only [compileETo] at hm
    cases hi : exprReg? fl.alloc i with
    | some ri =>
      simp only [hi, targetsIn_append, List.mem_append,
        targetsIn_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
        Asm.bgeu, targetsIn_nil, targetsIn_cons_br,
        List.mem_cons, List.mem_nil_iff, false_or, or_false] at hm
      rcases hm with rfl | hm
      · exact rfl
      · cases hc : i.constVal? with | none => simp only [hc] at hm; cases hm | some _ => simp only [hc] at hm; split at hm <;> cases hm
    | none =>
      simp only [hi, targetsIn_append, List.mem_append, or_assoc,
        targetsIn_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
        Asm.bgeu, targetsIn_nil, targetsIn_cons_br,
        List.mem_cons, List.mem_nil_iff, or_false] at hm
      rcases hm with hm | rfl | hm
      · exact ih tmp AbiReg.a0 t hm
      · exact rfl
      · cases hc : i.constVal? with | none => simp only [hc] at hm; cases hm | some _ => simp only [hc] at hm; split at hm <;> cases hm
  | .ld64 _ i =>
    have ih := fun k r x hx => compileETo_targetsIn_aux tab fl i k r x hx
    dsimp only [compileETo] at hm
    cases hi : exprReg? fl.alloc i with
    | some ri =>
      simp only [hi, targetsIn_append, List.mem_append,
        targetsIn_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
        targetsIn_of_allInstrs (ld64Tail_allInstrs _ _ _ _),
        Asm.bgeu, targetsIn_nil, targetsIn_cons_br,
        List.mem_cons, List.mem_nil_iff, false_or, or_false] at hm
      exact hm
    | none =>
      simp only [hi, targetsIn_append, List.mem_append,
        targetsIn_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
        targetsIn_of_allInstrs (ld64Tail_allInstrs _ _ _ _),
        Asm.bgeu, targetsIn_nil, targetsIn_cons_br,
        List.mem_cons, List.mem_nil_iff, or_false] at hm
      rcases hm with hm | rfl
      · exact ih tmp AbiReg.a0 t hm
      · exact rfl
  | .ldc _ i =>
    have ih := fun k r x hx => compileETo_targetsIn_aux tab fl i k r x hx
    dsimp only [compileETo] at hm
    cases hi : exprReg? fl.alloc i with
    | some _ =>
      simp only [hi, targetsIn_append, List.mem_append,
        targetsIn_of_allInstrs (li_allInstrs _ _),
        targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
        Asm.bgeu, Asm.add,
        targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
        List.mem_cons, List.mem_nil_iff, false_or, or_false] at hm
      exact hm
    | none =>
      simp only [hi, targetsIn_append, List.mem_append,
        targetsIn_of_allInstrs (li_allInstrs _ _),
        targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
        Asm.bgeu, Asm.add,
        targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
        List.mem_cons, List.mem_nil_iff, or_false] at hm
      rcases hm with hm | rfl
      · exact ih tmp AbiReg.a0 t hm
      · exact rfl
  | .ld64t _ th i =>
    have iht := fun k r x hx => compileETo_targetsIn_aux tab fl th k r x hx
    have ihi := fun k r x hx => compileETo_targetsIn_aux tab fl i k r x hx
    dsimp only [compileETo] at hm
    cases hcv : th.constVal? with
    | some _ =>
      simp only [hcv] at hm
      cases hi : exprReg? fl.alloc i with
      | some ri =>
        simp only [hi, targetsIn_append, List.mem_append,
          targetsIn_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
          targetsIn_of_allInstrs (ld64Tail_allInstrs _ _ _ _),
          Asm.bgeu, targetsIn_nil, targetsIn_cons_br,
          List.mem_cons, List.mem_nil_iff, false_or, or_false] at hm
        exact hm
      | none =>
        simp only [hi, targetsIn_append, List.mem_append,
          targetsIn_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
          targetsIn_of_allInstrs (ld64Tail_allInstrs _ _ _ _),
          Asm.bgeu, targetsIn_nil, targetsIn_cons_br,
          List.mem_cons, List.mem_nil_iff, or_false] at hm
        rcases hm with hm | rfl
        · exact ihi tmp AbiReg.a0 t hm
        · exact rfl
    | none =>
      simp only [hcv] at hm
      cases hth : exprReg? fl.alloc th with
      | some rt =>
        cases hi' : exprReg? fl.alloc i with
        | some ri =>
          simp only [hth, hi', targetsIn_append, List.mem_append,
            targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
            targetsIn_of_allInstrs (ld64Tail_allInstrs _ _ _ _),
            Asm.andi, Asm.slli, Asm.add, Asm.bgeu,
            targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
            List.mem_cons, List.mem_nil_iff, false_or, or_false] at hm
          exact hm
        | none =>
          simp only [hth, hi', targetsIn_append, List.mem_append,
            targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
            targetsIn_of_allInstrs (ld64Tail_allInstrs _ _ _ _),
            Asm.andi, Asm.slli, Asm.add, Asm.bgeu,
            targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
            List.mem_cons, List.mem_nil_iff, or_false] at hm
          rcases hm with hm | rfl
          · exact ihi tmp AbiReg.a0 t hm
          · exact rfl
      | none =>
        cases hst : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 th with
        | some ct =>
          cases hi' : exprReg? fl.alloc i with
          | some ri =>
            simp only [hth, hst, hi', targetsIn_append, List.mem_append,
              targetsIn_of_allInstrs (emitSimpleExprR_allInstrs hst),
              targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
              targetsIn_of_allInstrs (ld64Tail_allInstrs _ _ _ _),
              Asm.andi, Asm.slli, Asm.add, Asm.bgeu,
              targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
              List.mem_cons, List.mem_nil_iff, false_or, or_false] at hm
            exact hm
          | none =>
            simp only [hth, hst, hi', targetsIn_append, List.mem_append,
              targetsIn_of_allInstrs (emitSimpleExprR_allInstrs hst),
              targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
              targetsIn_of_allInstrs (ld64Tail_allInstrs _ _ _ _),
              Asm.andi, Asm.slli, Asm.add, Asm.bgeu,
              targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
              List.mem_cons, List.mem_nil_iff, or_false] at hm
            rcases hm with hm | rfl
            · exact ihi tmp AbiReg.a0 t hm
            · exact rfl
        | none =>
          simp only [hth, hst, targetsIn_append, List.mem_append, or_assoc,
            targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
            targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
            targetsIn_of_allInstrs (ld64Tail_allInstrs _ _ _ _),
            Asm.andi, Asm.slli, Asm.add, Asm.bgeu,
            targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
            List.mem_cons, List.mem_nil_iff, or_false] at hm
          rcases hm with hm | hm | rfl
          · exact iht tmp AbiReg.a0 t hm
          · exact ihi (tmp + 1) AbiReg.a0 t hm
          · exact rfl
  | .ld32t _ th i =>
    have iht := fun k r x hx => compileETo_targetsIn_aux tab fl th k r x hx
    have ihi := fun k r x hx => compileETo_targetsIn_aux tab fl i k r x hx
    dsimp only [compileETo] at hm
    cases hcv : th.constVal? with
    | some _ =>
      simp only [hcv] at hm
      cases hi : exprReg? fl.alloc i with
      | some ri =>
        simp only [hi, targetsIn_append, List.mem_append,
          targetsIn_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
          targetsIn_of_allInstrs (ld32tTail_allInstrs _ _ _),
          Asm.srli, Asm.bgeu, targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
          List.mem_cons, List.mem_nil_iff, false_or, or_false] at hm
        exact hm
      | none =>
        simp only [hi, targetsIn_append, List.mem_append,
          targetsIn_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
          targetsIn_of_allInstrs (ld32tTail_allInstrs _ _ _),
          Asm.srli, Asm.bgeu, targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
          List.mem_cons, List.mem_nil_iff, or_false] at hm
        rcases hm with hm | rfl
        · exact ihi tmp AbiReg.a0 t hm
        · exact rfl
    | none =>
      simp only [hcv] at hm
      cases hth : exprReg? fl.alloc th with
      | some rt =>
        cases hi' : exprReg? fl.alloc i with
        | some ri =>
          simp only [hth, hi', targetsIn_append, List.mem_append,
            targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
            targetsIn_of_allInstrs (ld32tTail_allInstrs _ _ _),
            Asm.andi, Asm.slli, Asm.srli, Asm.add, Asm.bgeu,
            targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
            List.mem_cons, List.mem_nil_iff, false_or, or_false] at hm
          exact hm
        | none =>
          simp only [hth, hi', targetsIn_append, List.mem_append,
            targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
            targetsIn_of_allInstrs (ld32tTail_allInstrs _ _ _),
            Asm.andi, Asm.slli, Asm.srli, Asm.add, Asm.bgeu,
            targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
            List.mem_cons, List.mem_nil_iff, or_false] at hm
          rcases hm with hm | rfl
          · exact ihi tmp AbiReg.a0 t hm
          · exact rfl
      | none =>
        cases hst : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 th with
        | some ct =>
          cases hi' : exprReg? fl.alloc i with
          | some ri =>
            simp only [hth, hst, hi', targetsIn_append, List.mem_append,
              targetsIn_of_allInstrs (emitSimpleExprR_allInstrs hst),
              targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
              targetsIn_of_allInstrs (ld32tTail_allInstrs _ _ _),
              Asm.andi, Asm.slli, Asm.srli, Asm.add, Asm.bgeu,
              targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
              List.mem_cons, List.mem_nil_iff, false_or, or_false] at hm
            exact hm
          | none =>
            simp only [hth, hst, hi', targetsIn_append, List.mem_append,
              targetsIn_of_allInstrs (emitSimpleExprR_allInstrs hst),
              targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
              targetsIn_of_allInstrs (ld32tTail_allInstrs _ _ _),
              Asm.andi, Asm.slli, Asm.srli, Asm.add, Asm.bgeu,
              targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
              List.mem_cons, List.mem_nil_iff, or_false] at hm
            rcases hm with hm | rfl
            · exact ihi tmp AbiReg.a0 t hm
            · exact rfl
        | none =>
          simp only [hth, hst, targetsIn_append, List.mem_append, or_assoc,
            targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
            targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
            targetsIn_of_allInstrs (ld32tTail_allInstrs _ _ _),
            Asm.andi, Asm.slli, Asm.srli, Asm.add, Asm.bgeu,
            targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
            List.mem_cons, List.mem_nil_iff, or_false] at hm
          rcases hm with hm | hm | rfl
          · exact iht tmp AbiReg.a0 t hm
          · exact ihi (tmp + 1) AbiReg.a0 t hm
          · exact rfl
  | .len64t _ th =>
    have ih := fun k r x hx => compileETo_targetsIn_aux tab fl th k r x hx
    dsimp only [compileETo] at hm
    cases hcv : th.constVal? with
    | some _ =>
      simp only [hcv] at hm
      rw [targetsIn_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _)] at hm; cases hm
    | none =>
      simp only [hcv] at hm
      cases ht' : exprReg? fl.alloc th with
      | some _ =>
        simp only [ht', targetsIn_append, List.mem_append,
          targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
          Asm.andi, Asm.slli, Asm.add, targetsIn_nil, targetsIn_cons_instr,
          List.mem_nil_iff, or_false] at hm
      | none =>
        simp only [ht', targetsIn_append, List.mem_append,
          targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
          Asm.andi, Asm.slli, Asm.add, targetsIn_nil, targetsIn_cons_instr,
          List.mem_nil_iff, or_false] at hm
        exact ih tmp AbiReg.a0 t hm
  | .ld8x8 src i =>
    have ih := fun k r x hx => compileETo_targetsIn_aux tab fl i k r x hx
    have hreadAll : allInstrs ([Asm.lbu rd AbiReg.t1 7#12] ++
        List.flatMap (fun k =>
          [Asm.lbu AbiReg.t2 AbiReg.t1 (BitVec.ofInt 12 k), Asm.slli rd rd 8#6,
           Asm.or rd rd AbiReg.t2]) [6, 5, 4, 3, 2, 1, 0]) = true := by
      rw [allInstrs_append, Bool.and_eq_true]
      exact ⟨rfl, allInstrs_flatMap (fun _ _ => rfl)⟩
    dsimp only [compileETo] at hm
    cases hi : exprReg? fl.alloc i with
    | some _ =>
      cases src <;> (
        simp only [hi, List.nil_append, targetsIn_append,
          targetsIn_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
          targetsIn_of_allInstrs (li_allInstrs _ _),
          targetsIn_of_allInstrs (addImmOff_allInstrs _ _ _ _),
          targetsIn_of_allInstrs hreadAll, List.mem_append,
          Asm.addi, Asm.bltu, Asm.add, targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
          List.mem_cons, List.mem_nil_iff, or_false] at hm
        rcases hm with rfl | rfl <;> exact rfl)
    | none =>
      cases src <;> (
        simp only [hi, targetsIn_append,
          targetsIn_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
          targetsIn_of_allInstrs (li_allInstrs _ _),
          targetsIn_of_allInstrs (addImmOff_allInstrs _ _ _ _),
          targetsIn_of_allInstrs hreadAll, List.mem_append,
          Asm.addi, Asm.bltu, Asm.add, targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
          List.mem_cons, List.mem_nil_iff, or_false] at hm
        rcases hm with hm | rfl | rfl
        · exact ih tmp AbiReg.a0 t hm
        · exact rfl
        · exact rfl)
  | .ld32h a th i hi =>
    dsimp only [compileETo] at hm
    exact emitLd32hFrom_targetsIn tab fl tmp rd a th i hi _ _ _
      (fun x hx => compileETo_targetsIn_aux tab fl i tmp AbiReg.a0 x hx)
      (fun x hx => compileETo_targetsIn_aux tab fl th tmp AbiReg.a0 x hx)
      (fun x hx => compileETo_targetsIn_aux tab fl i (tmp + 1) AbiReg.a0 x hx) t hm
termination_by sizeOf e

private theorem compileETo_targetsIn (tab : Tab) (fl : FrameLayout) :
    ∀ (e : Expr) (tmp : Nat) (rd : Reg) (t : String),
      t ∈ targetsIn (compileETo tab fl tmp rd e) → t = errLabel :=
  compileETo_targetsIn_aux tab fl

private theorem compileCR_targetsIn (tab : Tab) (fl : FrameLayout) (tmp : Nat) (pfx : String) :
    ∀ (c : Cond) (lblId : Nat) (want : Bool) (target t : String),
      t ∈ targetsIn (compileCR tab fl tmp pfx lblId c want target).1 →
      t = target ∨ t ∈ lblNames (compileCR tab fl tmp pfx lblId c want target).1 ∨
        t = errLabel := by
  intro c
  induction c with
  | cmp op a b =>
    intro lblId want target t hm
    dsimp only [compileCR] at hm
    cases ha : exprReg? fl.alloc a with
    | some ra =>
      simp only [ha] at hm
      cases hb : exprReg? fl.alloc b with
      | some rb =>
        simp only [hb, brCmp_targetsIn, List.mem_singleton] at hm
        exact Or.inl hm
      | none =>
        simp only [hb, targetsIn_append, brCmp_targetsIn, List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | rfl
        · exact Or.inr (Or.inr (compileETo_targetsIn tab fl b tmp AbiReg.a0 t hm))
        · exact Or.inl rfl
    | none =>
      simp only [ha] at hm
      cases hb : exprReg? fl.alloc b with
      | some rb =>
        simp only [hb, targetsIn_append, brCmp_targetsIn, List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | rfl
        · exact Or.inr (Or.inr (compileETo_targetsIn tab fl a tmp AbiReg.a0 t hm))
        · exact Or.inl rfl
      | none =>
        simp only [hb] at hm
        cases hsb : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 b with
        | some cb =>
          simp only [hsb, targetsIn_append, brCmp_targetsIn, List.mem_append, List.mem_singleton,
            targetsIn_of_allInstrs (emitSimpleExprR_allInstrs hsb),
            List.mem_nil_iff, or_false] at hm
          rcases hm with hm | rfl
          · exact Or.inr (Or.inr (compileETo_targetsIn tab fl a tmp AbiReg.a0 t hm))
          · exact Or.inl rfl
        | none =>
          simp only [hsb] at hm
          cases hsa : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 a with
          | some ca =>
            simp only [hsa, targetsIn_append, brCmp_targetsIn, List.mem_append, List.mem_singleton,
              targetsIn_of_allInstrs (emitSimpleExprR_allInstrs hsa),
              List.mem_nil_iff, or_false] at hm
            rcases hm with hm | rfl
            · exact Or.inr (Or.inr (compileETo_targetsIn tab fl b tmp AbiReg.a0 t hm))
            · exact Or.inl rfl
          | none =>
            simp only [hsa] at hm
            split at hm
            · simp only [targetsIn_append, brCmp_targetsIn, List.mem_append, List.mem_singleton,
                or_assoc, Asm.mv, targetsIn_cons_instr, targetsIn_nil,
                List.mem_nil_iff, or_false] at hm
              rcases hm with hm | hm | rfl
              · exact Or.inr (Or.inr (compileETo_targetsIn tab fl a tmp AbiReg.a0 t hm))
              · exact Or.inr (Or.inr (compileETo_targetsIn tab fl b tmp AbiReg.a0 t hm))
              · exact Or.inl rfl
            · simp only [targetsIn_append, brCmp_targetsIn, List.mem_append, List.mem_singleton,
                or_assoc, targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
                targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
                List.mem_nil_iff, or_false] at hm
              rcases hm with hm | hm | rfl
              · exact Or.inr (Or.inr (compileETo_targetsIn tab fl a tmp AbiReg.a0 t hm))
              · exact Or.inr (Or.inr (compileETo_targetsIn tab fl b (tmp + 1) AbiReg.a0 t hm))
              · exact Or.inl rfl
  | not p ih =>
    intro lblId want target t hm
    exact ih lblId (!want) target t hm
  | and p q ihp ihq =>
    intro lblId want target t hm
    dsimp only [compileCR] at hm ⊢
    cases want
    · simp only [Bool.false_eq_true, ↓reduceIte] at hm ⊢
      simp only [targetsIn_append, List.mem_append] at hm
      rcases hm with hm | hm
      · rcases ihp lblId false target t hm with rfl | hp | hm2
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (by rw [lblNames_append, List.mem_append]; exact Or.inl hp))
        · exact Or.inr (Or.inr hm2)
      · rcases ihq _ false target t hm with rfl | hq | hm2
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (by rw [lblNames_append, List.mem_append]; exact Or.inr hq))
        · exact Or.inr (Or.inr hm2)
    · simp only [↓reduceIte] at hm ⊢
      simp only [targetsIn_append, List.mem_append, or_assoc] at hm
      rcases hm with hm | hm | hm
      · rcases ihp (lblId + 1) false _ t hm with rfl | hp | hm2
        · exact Or.inr (Or.inl (by
            rw [lblNames_append, lblNames_singleton_lbl, List.mem_append, List.mem_singleton]; exact Or.inr rfl))
        · exact Or.inr (Or.inl (by
            rw [lblNames_append, lblNames_append, List.mem_append, List.mem_append]; exact Or.inl (Or.inl hp)))
        · exact Or.inr (Or.inr hm2)
      · rcases ihq _ true target t hm with rfl | hq | hm2
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (by
            rw [lblNames_append, lblNames_append, List.mem_append, List.mem_append]; exact Or.inl (Or.inr hq)))
        · exact Or.inr (Or.inr hm2)
      · change t ∈ ([] : List String) at hm; cases hm
  | or p q ihp ihq =>
    intro lblId want target t hm
    dsimp only [compileCR] at hm ⊢
    cases want
    · simp only [Bool.false_eq_true, ↓reduceIte] at hm ⊢
      simp only [targetsIn_append, List.mem_append, or_assoc] at hm
      rcases hm with hm | hm | hm
      · rcases ihp (lblId + 1) true _ t hm with rfl | hp | hm2
        · exact Or.inr (Or.inl (by
            rw [lblNames_append, lblNames_singleton_lbl, List.mem_append, List.mem_singleton]; exact Or.inr rfl))
        · exact Or.inr (Or.inl (by
            rw [lblNames_append, lblNames_append, List.mem_append, List.mem_append]; exact Or.inl (Or.inl hp)))
        · exact Or.inr (Or.inr hm2)
      · rcases ihq _ false target t hm with rfl | hq | hm2
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (by
            rw [lblNames_append, lblNames_append, List.mem_append, List.mem_append]; exact Or.inl (Or.inr hq)))
        · exact Or.inr (Or.inr hm2)
      · change t ∈ ([] : List String) at hm; cases hm
    · simp only [↓reduceIte] at hm ⊢
      simp only [targetsIn_append, List.mem_append] at hm
      rcases hm with hm | hm
      · rcases ihp lblId true target t hm with rfl | hp | hm2
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (by rw [lblNames_append, List.mem_append]; exact Or.inl hp))
        · exact Or.inr (Or.inr hm2)
      · rcases ihq _ true target t hm with rfl | hq | hm2
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (by rw [lblNames_append, List.mem_append]; exact Or.inr hq))
        · exact Or.inr (Or.inr hm2)

private theorem compileEvalExprsToTempsR_targetsIn (tab : Tab) (fl : FrameLayout) :
    ∀ (es : List Expr) (tmp : Nat) (t : String),
      t ∈ targetsIn (compileEvalExprsToTempsR tab fl tmp es) → t = errLabel := by
  intro es
  induction es with
  | nil => intro _ _ hm; cases hm
  | cons e es ih =>
    intro tmp t hm
    dsimp only [compileEvalExprsToTempsR] at hm
    rw [targetsIn_append, List.mem_append] at hm
    rcases hm with hm | hm
    · cases he : exprReg? fl.alloc e with
      | some _ =>
        simp only [he] at hm
        rw [targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)] at hm; cases hm
      | none =>
        simp only [he, targetsIn_append, List.mem_append,
          targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
          List.mem_nil_iff, or_false] at hm
        exact compileETo_targetsIn tab fl e tmp AbiReg.a0 t hm
    · exact ih (tmp + 1) t hm

private theorem compileStorePairR_targetsIn (tab : Tab) (fl : FrameLayout) (i e : Expr) (t : String)
    (hm : t ∈ targetsIn (compileStorePairR tab fl i e).1) :
    t = errLabel := by
  dsimp only [compileStorePairR] at hm
  cases hi : exprReg? fl.alloc i with
  | some _ =>
    simp only [hi] at hm
    cases he : exprReg? fl.alloc e with
    | some _ => simp only [he] at hm; cases hm
    | none => simp only [he] at hm; exact compileETo_targetsIn tab fl e 0 AbiReg.a0 t hm
  | none =>
    simp only [hi] at hm
    cases he : exprReg? fl.alloc e with
    | some _ => simp only [he] at hm; exact compileETo_targetsIn tab fl i 0 AbiReg.a0 t hm
    | none =>
      simp only [he] at hm
      cases hsi : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 i with
      | some ci =>
        simp only [hsi, targetsIn_append, List.mem_append,
          targetsIn_of_allInstrs (emitSimpleExprR_allInstrs hsi),
          List.mem_nil_iff, or_false] at hm
        exact compileETo_targetsIn tab fl e 0 AbiReg.a0 t hm
      | none =>
        simp only [hsi] at hm
        cases hse : emitSimpleExprR tab fl AbiReg.a0 AbiReg.t1 e with
        | some ce =>
          simp only [hse, targetsIn_append, List.mem_append, Asm.mv,
            targetsIn_of_allInstrs (emitSimpleExprR_allInstrs hse),
            targetsIn_nil, targetsIn_cons_instr, List.mem_nil_iff, or_false] at hm
          exact compileETo_targetsIn tab fl i 0 AbiReg.a0 t hm
        | none =>
          simp only [hse, targetsIn_append, List.mem_append,
            targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
            targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
            List.mem_nil_iff, or_false] at hm
          rcases hm with hm | hm
          · exact compileETo_targetsIn tab fl i 0 AbiReg.a0 t hm
          · exact compileETo_targetsIn tab fl e 1 AbiReg.a0 t hm

private theorem compileTierStoreTripleR_targetsIn (tab : Tab) (fl : FrameLayout) (th i e : Expr)
    (t : String) (hm : t ∈ targetsIn (compileTierStoreTripleR tab fl th i e).1) :
    t = errLabel := by
  dsimp only [compileTierStoreTripleR] at hm
  cases ht' : exprReg? fl.alloc th with
  | some _ =>
    simp only [ht'] at hm
    cases hi : exprReg? fl.alloc i with
    | some _ =>
      simp only [hi] at hm
      cases he : exprReg? fl.alloc e with
      | some _ => simp only [he] at hm; cases hm
      | none => simp only [he] at hm; exact compileETo_targetsIn tab fl e 0 AbiReg.a0 t hm
    | none =>
      simp only [hi] at hm
      cases he : exprReg? fl.alloc e with
      | some _ => simp only [he] at hm; exact compileETo_targetsIn tab fl i 0 AbiReg.a0 t hm
      | none =>
        simp only [he] at hm
        cases hsi : emitSimpleExprR tab fl AbiReg.t3 AbiReg.t4 i with
        | some ci =>
          simp only [hsi, targetsIn_append, List.mem_append,
            targetsIn_of_allInstrs (emitSimpleExprR_allInstrs hsi),
            List.mem_nil_iff, or_false] at hm
          exact compileETo_targetsIn tab fl e 0 AbiReg.a0 t hm
        | none =>
          simp only [hsi] at hm
          cases hse : emitSimpleExprR tab fl AbiReg.a0 AbiReg.t4 e with
          | some ce =>
            simp only [hse, targetsIn_append, List.mem_append, Asm.mv,
              targetsIn_of_allInstrs (emitSimpleExprR_allInstrs hse),
              targetsIn_nil, targetsIn_cons_instr, List.mem_nil_iff, or_false] at hm
            exact compileETo_targetsIn tab fl i 0 AbiReg.a0 t hm
          | none =>
            simp only [hse, targetsIn_append, List.mem_append,
              targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
              targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
              List.mem_nil_iff, or_false] at hm
            rcases hm with hm | hm
            · exact compileETo_targetsIn tab fl i 0 AbiReg.a0 t hm
            · exact compileETo_targetsIn tab fl e 1 AbiReg.a0 t hm
  | none =>
    simp only [ht'] at hm
    cases hst : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 th with
    | some ct =>
      simp only [hst] at hm
      cases hsi : emitSimpleExprR tab fl AbiReg.t3 AbiReg.t4 i with
      | some ci =>
        simp only [hsi, targetsIn_append, List.mem_append,
          targetsIn_of_allInstrs (emitSimpleExprR_allInstrs hst),
          targetsIn_of_allInstrs (emitSimpleExprR_allInstrs hsi),
          List.mem_nil_iff, or_false] at hm
        exact compileETo_targetsIn tab fl e 0 AbiReg.a0 t hm
      | none =>
        simp only [hsi] at hm
        cases hse : emitSimpleExprR tab fl AbiReg.a0 AbiReg.t4 e with
        | some ce =>
          simp only [hse, targetsIn_append, List.mem_append, Asm.mv,
            targetsIn_of_allInstrs (emitSimpleExprR_allInstrs hst),
            targetsIn_of_allInstrs (emitSimpleExprR_allInstrs hse),
            targetsIn_nil, targetsIn_cons_instr, List.mem_nil_iff, or_false] at hm
          exact compileETo_targetsIn tab fl i 0 AbiReg.a0 t hm
        | none =>
          simp only [hse, targetsIn_append, List.mem_append,
            targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
            targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
            targetsIn_of_allInstrs (emitSimpleExprR_allInstrs hst),
            List.mem_nil_iff, or_false] at hm
          rcases hm with hm | hm
          · exact compileETo_targetsIn tab fl i 0 AbiReg.a0 t hm
          · exact compileETo_targetsIn tab fl e 1 AbiReg.a0 t hm
    | none =>
      simp only [hst, targetsIn_append, List.mem_append, or_assoc,
        targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
        targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
        List.mem_nil_iff, or_false] at hm
      rcases hm with hm | hm | hm
      · exact compileETo_targetsIn tab fl th 0 AbiReg.a0 t hm
      · exact compileETo_targetsIn tab fl i 1 AbiReg.a0 t hm
      · exact compileETo_targetsIn tab fl e 2 AbiReg.a0 t hm

private theorem compileEvalRevToRegs_targetsIn (tab : Tab) (fl : FrameLayout) :
    ∀ (es : List Expr) (idx : Nat) (t : String),
      t ∈ targetsIn (compileEvalRevToRegs tab fl idx es) → t = errLabel := by
  intro es
  induction es with
  | nil => intro _ _ hm; cases hm
  | cons e rest ih =>
    intro idx t hm
    dsimp only [compileEvalRevToRegs] at hm
    rw [targetsIn_append, List.mem_append] at hm
    rcases hm with hm | hm
    · exact ih (idx + 1) t hm
    · exact compileETo_targetsIn tab fl e 0 (resReg idx) t hm

private theorem compileRetR_targetsIn (tab : Tab) (fl : FrameLayout)
    (retLbl : String) (isTail : Bool) (es : List Expr) (t : String)
    (hm : t ∈ targetsIn (compileRetR tab fl retLbl isTail es)) :
    t = retLbl ∨ t = errLabel := by
  have hjT : ∀ x ∈ targetsIn (if isTail = true then []
      else if (fl.isLeaf && (fl.frameSlots == 0)) = true then [Asm.ret]
      else [Asm.j retLbl]), x = retLbl := by
    intro x hx
    split at hx
    · cases hx
    · split at hx
      · cases hx
      · simpa [Asm.j, targetsIn_cons_j, targetsIn_nil] using hx
  cases es with
  | nil =>
    simp only [compileRetR, targetsIn_append, List.mem_append,
      targetsIn_of_allInstrs (copyTempsToResultsR_allInstrs _ _ _ _),
      List.mem_nil_iff, false_or] at hm
    exact Or.inl (hjT t hm)
  | cons e rest =>
    cases rest with
    | nil =>
      simp only [compileRetR, targetsIn_append, List.mem_append] at hm
      rcases hm with hm | hm
      · exact Or.inr (compileETo_targetsIn tab fl e 0 AbiReg.a0 t hm)
      · exact Or.inl (hjT t hm)
    | cons e2 rs =>
      dsimp only [compileRetR] at hm
      split at hm
      · simp only [targetsIn_append, List.mem_append] at hm
        rcases hm with hm | hm
        · exact Or.inr (compileEvalRevToRegs_targetsIn tab fl (e :: e2 :: rs) 0 t hm)
        · exact Or.inl (hjT t hm)
      · simp only [targetsIn_append, List.mem_append,
          targetsIn_of_allInstrs (copyTempsToResultsR_allInstrs _ _ _ _),
          List.mem_nil_iff, or_false] at hm
        rcases hm with hm | hm
        · exact Or.inr (compileEvalExprsToTempsR_targetsIn tab fl (e :: e2 :: rs) 0 t hm)
        · exact Or.inl (hjT t hm)

private theorem compileCallArgsR_targetsIn (tab : Tab) (fl : FrameLayout)
    (args : List Expr) (t : String)
    (hm : t ∈ targetsIn (compileCallArgsR tab fl args)) :
    t = errLabel ∨ t = exhaustedLabel := by
  have hbud : targetsIn [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
      Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] = [exhaustedLabel] := rfl
  dsimp only [compileCallArgsR] at hm
  split at hm
  · simp only [targetsIn_append, List.mem_append, hbud, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · rw [compileEvalRevToRegs_targetsIn tab fl args 0 t hm]; simp
    · simp
  · have hlds : targetsIn ((List.range (min args.length maxRes)).flatMap fun i =>
        loadMemOff .ld (resReg i) AbiReg.sp AbiReg.t0 (fl.tempSlotOff i)) = [] := by
      rw [targetsIn_flatMap, List.flatMap_eq_nil_iff]
      intro _ _; exact targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _)
    have hptr : targetsIn (if maxRes < args.length then
        addImmOff AbiReg.t0 AbiReg.sp AbiReg.t2 (fl.tempSlotOff maxRes) else []) = [] := by
      split
      · exact targetsIn_of_allInstrs (addImmOff_allInstrs _ _ _ _)
      · rfl
    simp only [targetsIn_append, List.mem_append, hbud, hlds, hptr,
      List.mem_singleton, List.mem_nil_iff, or_false] at hm
    rcases hm with hm | rfl
    · rw [compileEvalExprsToTempsR_targetsIn tab fl args 0 t hm]; simp
    · simp

private theorem compileSR_targetsIn (tab : Tab) (fl : FrameLayout) (pfx retLbl : String) :
    ∀ (s : Stmt) (lblId : Nat) (brkLbl : Option String) (isTail : Bool) (p : Prog) (t : String),
      stmtOkConst0B tab p fl.nlocals (brkLbl.isSome) s = true →
      t ∈ targetsIn (compileSR tab fl pfx lblId brkLbl retLbl isTail s).1 →
      t ∈ lblNames (compileSR tab fl pfx lblId brkLbl retLbl isTail s).1 ∨
        t = retLbl ∨ (∃ b, brkLbl = some b ∧ t = b) ∨
        t = errLabel ∨ t = exhaustedLabel ∨ t = abortLabel ∨
        (t = s!"{pfx}_abort0stub" ∧ stmtHasAbort0 s = true) ∨
        (∃ g, t = fnLabel g ∧ (List.lookup g p).isSome = true) := by
  intro s
  induction s with
  | skip => intro _ _ _ _ _ _ hm; cases hm
  | set x e =>
    intro _ _ _ _ t _ hm
    dsimp only [compileSR] at hm
    split at hm
    · next rx _ =>
      rw [compileETo_targetsIn tab fl e 0 rx t hm]; simp
    · split at hm
      · split at hm
        · cases hm
        · rw [compileETo_targetsIn tab fl e 0 AbiReg.a0 t hm]; simp
      · cases he : exprReg? fl.alloc e with
        | some _ =>
          simp only [he] at hm
          rw [targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)] at hm; cases hm
        | none =>
          simp only [he, targetsIn_append, List.mem_append,
            targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
            List.mem_nil_iff, or_false] at hm
          rw [compileETo_targetsIn tab fl e 0 AbiReg.a0 t hm]; simp
  | gset _ e =>
    intro _ _ _ _ t _ hm
    dsimp only [compileSR] at hm
    cases he : exprReg? fl.alloc e with
    | some _ =>
      simp only [he] at hm
      rw [targetsIn_of_allInstrs (storeMemOffGp_allInstrs _ _ _ _ _)] at hm; cases hm
    | none =>
      simp only [he, targetsIn_append, List.mem_append,
        targetsIn_of_allInstrs (storeMemOffGp_allInstrs _ _ _ _ _),
        List.mem_nil_iff, or_false] at hm
      rw [compileETo_targetsIn tab fl e 0 AbiReg.a0 t hm]; simp
  | st8 _ _ _ => intro _ _ _ _ _ _ hm; cases hm
  | st64 _ i e =>
    intro _ _ _ _ t _ hm
    have hcp := compileStorePairR_targetsIn tab fl i e t
    rcases hpair : compileStorePairR tab fl i e with ⟨cp, ri, re⟩
    rw [hpair] at hcp
    simp only [compileSR, hpair, targetsIn_append, List.mem_append,
      targetsIn_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
      targetsIn_of_allInstrs (st64Tail_allInstrs _ _ _ _),
      Asm.bgeu, targetsIn_nil, targetsIn_cons_br,
      List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with hm | rfl
    · rw [hcp hm]; simp
    · simp
  | st64t _ th i e =>
    intro _ _ _ _ t _ hm
    dsimp only [compileSR] at hm
    cases hcv : th.constVal? with
    | some wt =>
      simp only [hcv] at hm
      have hcp := compileStorePairR_targetsIn tab fl i e t
      rcases hpair : compileStorePairR tab fl i e with ⟨cp, ri, re⟩
      rw [hpair] at hcp
      simp only [hpair, targetsIn_append, List.mem_append,
        targetsIn_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
        targetsIn_of_allInstrs (st64Tail_allInstrs _ _ _ _),
        Asm.bgeu, targetsIn_nil, targetsIn_cons_br,
        List.mem_cons, List.mem_nil_iff, or_false] at hm
      rcases hm with hm | rfl
      · rw [hcp hm]; simp
      · simp
    | none =>
      simp only [hcv] at hm
      have hcp := compileTierStoreTripleR_targetsIn tab fl th i e t
      rcases htp : compileTierStoreTripleR tab fl th i e with ⟨cp, rt, ri, re⟩
      rw [htp] at hcp
      simp only [htp, targetsIn_append, List.mem_append,
        targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
        targetsIn_of_allInstrs (st64Tail_allInstrs _ _ _ _),
        Asm.andi, Asm.slli, Asm.add, Asm.bgeu,
        targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
        List.mem_cons, List.mem_nil_iff, or_false] at hm
      rcases hm with hm | rfl
      · rw [hcp hm]; simp
      · simp
  | st32t _ th i e =>
    intro _ _ _ _ t _ hm
    dsimp only [compileSR] at hm
    cases hcv : th.constVal? with
    | some wt =>
      simp only [hcv] at hm
      have hcp := compileStorePairR_targetsIn tab fl i e t
      rcases hpair : compileStorePairR tab fl i e with ⟨cp, ri, re⟩
      rw [hpair] at hcp
      simp only [hpair, targetsIn_append, List.mem_append,
        targetsIn_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
        targetsIn_of_allInstrs (st32tTail_allInstrs _ _ _ _),
        Asm.srli, Asm.bgeu, targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
        List.mem_cons, List.mem_nil_iff, or_false] at hm
      rcases hm with hm | rfl
      · rw [hcp hm]; simp
      · simp
    | none =>
      simp only [hcv] at hm
      have hcp := compileTierStoreTripleR_targetsIn tab fl th i e t
      rcases htp : compileTierStoreTripleR tab fl th i e with ⟨cp, rt, ri, re⟩
      rw [htp] at hcp
      simp only [htp, targetsIn_append, List.mem_append,
        targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
        targetsIn_of_allInstrs (st32tTail_allInstrs _ _ _ _),
        Asm.andi, Asm.slli, Asm.srli, Asm.add, Asm.bgeu,
        targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br,
        List.mem_cons, List.mem_nil_iff, or_false] at hm
      rcases hm with hm | rfl
      · rw [hcp hm]; simp
      · simp
  | seq s1 s2 ih1 ih2 =>
    intro lblId brkLbl isTail p t hok hm
    simp only [stmtOkConst0B, Bool.and_eq_true] at hok
    dsimp only [compileSR] at hm ⊢
    cases hmatch : tailCallRetMatch tab s1 s2 with
    | some v =>
      rcases v with ⟨xs, f, args, es⟩
      simp only [hmatch] at hm ⊢
      obtain ⟨rfl, rfl, _⟩ := tailCallRetMatch_spec hmatch
      simp only [stmtOkConst0B, Bool.and_eq_true] at hok
      simp only [targetsIn_append, List.mem_append,
        targetsIn_of_allInstrs (framePopItems_allInstrs fl),
        Asm.j, targetsIn_nil, targetsIn_cons_j,
        List.mem_cons, List.mem_nil_iff, or_false] at hm
      rcases hm with hm | rfl
      · rcases compileCallArgsR_targetsIn tab fl args t hm with rfl | rfl <;> simp
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f, rfl, hok.1.1.1⟩))))))
    | none =>
      simp only [hmatch, targetsIn_append, List.mem_append] at hm
      rcases hm with hm | hm
      · rcases ih1 lblId brkLbl false p t hok.1 hm with h | h | h | h | h | h | ⟨rfl, hab⟩ | h
        · exact Or.inl (by simp only [lblNames_append, List.mem_append, h, true_or])
        · simp [h]
        · simp [h]
        · simp [h]
        · simp [h]
        · simp [h]
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by simp [stmtHasAbort0, hab]⟩))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
      · rcases ih2 _ brkLbl isTail p t hok.2 hm with h | h | h | h | h | h | ⟨rfl, hab⟩ | h
        · exact Or.inl (by simp only [lblNames_append, List.mem_append, h, or_true])
        · simp [h]
        · simp [h]
        · simp [h]
        · simp [h]
        · simp [h]
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by simp [stmtHasAbort0, hab]⟩))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  | ite cond s1 s2 ih1 ih2 =>
    intro lblId brkLbl isTail p t hok hm
    simp only [stmtOkConst0B, Bool.and_eq_true] at hok
    by_cases hs2 : s2 = .skip
    · subst hs2
      dsimp only [compileSR] at hm ⊢
      by_cases hab : isAbort0Stmt s1 = true
      · simp only [hab, ↓reduceIte] at hm ⊢
        rcases compileCR_targetsIn tab fl 0 pfx cond lblId true _ t hm with rfl | hc | rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by
            simp [stmtHasAbort0, isAbort0Stmt_implies_stmtHasAbort0 hab]⟩))))))
        · exact Or.inl hc
        · simp
      · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hm ⊢
        simp only [targetsIn_append, List.mem_append, Asm.lbl, targetsIn_nil,
          targetsIn_cons_label, List.mem_nil_iff, or_false] at hm
        rcases hm with hm | hm
        · rcases compileCR_targetsIn tab fl 0 pfx cond (lblId + 1) false _ t hm with rfl | hc | rfl
          · exact Or.inl (by simp only [lblNames_append, lblNames_singleton_lbl, List.mem_append, List.mem_singleton]; simp)
          · exact Or.inl (by simp only [lblNames_append, List.mem_append, hc, true_or])
          · simp
        · rcases ih1 _ brkLbl false p t hok.1.2 hm with h | h | h | h | h | h | ⟨rfl, hab1⟩ | h
          · exact Or.inl (by simp only [lblNames_append, List.mem_append, h, true_or, or_true])
          · simp [h]
          · simp [h]
          · simp [h]
          · simp [h]
          · simp [h]
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by simp [stmtHasAbort0, hab1]⟩))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
    by_cases hs1 : s1 = .skip
    · subst hs1
      have hce : compileSR tab fl pfx lblId brkLbl retLbl isTail (.ite cond .skip s2) =
          if isAbort0Stmt s2 then
            compileCR tab fl 0 pfx lblId cond false s!"{pfx}_abort0stub"
          else
            let endLbl := s!"{pfx}_endif_{lblId}"
            let (cc, id1) := compileCR tab fl 0 pfx (lblId + 1) cond true endLbl
            let (c2, id2) := compileSR tab fl pfx id1 brkLbl retLbl false s2
            (cc ++ c2 ++ [Asm.lbl endLbl], id2) := by cases s2 with | skip => contradiction | _ => rfl
      rw [hce] at hm ⊢
      by_cases hab : isAbort0Stmt s2 = true
      · simp only [hab, ↓reduceIte] at hm ⊢
        rcases compileCR_targetsIn tab fl 0 pfx cond lblId false _ t hm with rfl | hc | rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by
            simp [stmtHasAbort0, isAbort0Stmt_implies_stmtHasAbort0 hab]⟩))))))
        · exact Or.inl hc
        · simp
      · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hm ⊢
        simp only [targetsIn_append, List.mem_append, Asm.lbl, targetsIn_nil,
          targetsIn_cons_label, List.mem_nil_iff, or_false] at hm
        rcases hm with hm | hm
        · rcases compileCR_targetsIn tab fl 0 pfx cond (lblId + 1) true _ t hm with rfl | hc | rfl
          · exact Or.inl (by simp only [lblNames_append, lblNames_singleton_lbl, List.mem_append, List.mem_singleton]; simp)
          · exact Or.inl (by simp only [lblNames_append, List.mem_append, hc, true_or])
          · simp
        · rcases ih2 _ brkLbl false p t hok.2 hm with h | h | h | h | h | h | ⟨rfl, hab2⟩ | h
          · exact Or.inl (by simp only [lblNames_append, List.mem_append, h, true_or, or_true])
          · simp [h]
          · simp [h]
          · simp [h]
          · simp [h]
          · simp [h]
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by simp [stmtHasAbort0, hab2]⟩))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
    have hceGen : (compileSR tab fl pfx lblId brkLbl retLbl isTail (.ite cond s1 s2)).1 =
        (compileCR tab fl 0 pfx (lblId + 1) cond false s!"{pfx}_else_{lblId}").1 ++
        (compileSR tab fl pfx (compileCR tab fl 0 pfx (lblId + 1) cond false s!"{pfx}_else_{lblId}").2 brkLbl retLbl false s1).1 ++
        (if stmtMayFallthrough s1 then [Asm.j s!"{pfx}_endif_{lblId}"] else []) ++
        [Asm.lbl s!"{pfx}_else_{lblId}"] ++
        (compileSR tab fl pfx (compileSR tab fl pfx (compileCR tab fl 0 pfx (lblId + 1) cond false s!"{pfx}_else_{lblId}").2 brkLbl retLbl false s1).2 brkLbl retLbl isTail s2).1 ++
        [Asm.lbl s!"{pfx}_endif_{lblId}"] := by
      cases s2 with | skip => contradiction | _ => cases s1 with | skip => contradiction | _ => rfl
    rw [hceGen] at hm ⊢
    simp only [targetsIn_append, List.mem_append, or_assoc,
      Asm.lbl, targetsIn_nil, targetsIn_cons_label,
      List.mem_nil_iff, or_false] at hm
    rcases hm with hm | hm | hj | hm
    · rcases compileCR_targetsIn tab fl 0 pfx cond (lblId + 1) false _ t hm with rfl | hc | rfl
      · exact Or.inl (by simp only [lblNames_append, lblNames_singleton_lbl, List.mem_append, List.mem_singleton]; simp)
      · exact Or.inl (by simp only [lblNames_append, List.mem_append, hc, true_or])
      · simp
    · rcases ih1 _ brkLbl false p t hok.1.2 hm with h | h | h | h | h | h | ⟨rfl, hab1⟩ | h
      · exact Or.inl (by simp only [lblNames_append, List.mem_append, h, true_or, or_true])
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h]
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by simp [stmtHasAbort0, hab1]⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
    · split at hj
      · have heq : t = s!"{pfx}_endif_{lblId}" := by
          simpa [Asm.j, targetsIn_cons_j, targetsIn_nil] using hj
        subst heq
        exact Or.inl (by simp only [lblNames_append, lblNames_singleton_lbl, List.mem_append, List.mem_singleton]; simp)
      · cases hj
    · rcases ih2 _ brkLbl isTail p t hok.2 hm with h | h | h | h | h | h | ⟨rfl, hab2⟩ | h
      · exact Or.inl (by simp only [lblNames_append, List.mem_append, h, true_or, or_true])
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h]
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by simp [stmtHasAbort0, hab2]⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  | «while» cond body ih =>
    intro lblId brkLbl _ p t hok hm
    simp only [stmtOkConst0B, Bool.and_eq_true] at hok
    simp only [compileSR, targetsIn_append, List.mem_append, or_assoc,
      Asm.lbl, Asm.beq, Asm.addi, Asm.j,
      targetsIn_nil, targetsIn_cons_label, targetsIn_cons_br, targetsIn_cons_instr, targetsIn_cons_j,
      List.mem_cons, List.mem_nil_iff, false_or, or_false] at hm
    rcases hm with hm | hm | rfl | rfl
    · rcases compileCR_targetsIn tab fl 0 pfx cond (lblId + 1) false _ t hm with rfl | hc | rfl
      · exact Or.inl (by
          simp only [compileSR, lblNames_append, Asm.lbl, Asm.beq, Asm.addi, Asm.j,
            lblNames_cons_label, lblNames_cons_br, lblNames_cons_instr, lblNames_cons_j,
            lblNames_nil, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
          simp)
      · exact Or.inl (by simp only [compileSR, lblNames_append, List.mem_append, hc, true_or, or_true])
      · simp
    · rcases ih _ (some _) false p t hok.2 hm with h | h | ⟨b, hb, rfl⟩ | h | h | h | ⟨rfl, hab⟩ | h
      · exact Or.inl (by simp only [compileSR, lblNames_append, List.mem_append, h, true_or, or_true])
      · exact Or.inr (Or.inl h)
      · cases hb
        exact Or.inl (by
          simp only [compileSR, lblNames_append, Asm.lbl, Asm.beq, Asm.addi, Asm.j,
            lblNames_cons_label, lblNames_cons_br, lblNames_cons_instr, lblNames_cons_j,
            lblNames_nil, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
          simp)
      · simp [h]
      · simp [h]
      · simp [h]
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hab⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
    · simp
    · exact Or.inl (by
        simp only [compileSR, lblNames_append, lblNames_singleton_lbl, List.mem_append, List.mem_singleton]
        simp)
  | brk =>
    intro lblId brkLbl _ _ t hok hm
    simp only [stmtOkConst0B] at hok
    cases brkLbl with
    | none => simp at hok
    | some b =>
      dsimp only [compileSR] at hm
      change t ∈ [b] at hm
      rw [List.mem_singleton.mp hm]; simp
  | ret es =>
    intro _ _ isTail _ t _ hm
    rcases compileRetR_targetsIn tab fl retLbl isTail es t hm with rfl | rfl <;> simp
  | «call» xs f args =>
    intro _ _ _ p t hok hm
    simp only [stmtOkConst0B, Bool.and_eq_true] at hok
    have ht5 : targetsIn (if fl.useT5Gp = true then [Asm.addi AbiReg.t5 AbiReg.gp 2047#12] else []) = [] := by
      split <;> rfl
    simp only [compileSR, targetsIn_append, List.mem_append, ht5,
      targetsIn_of_allInstrs (copyResultsToLocalsR_allInstrs _ _ _),
      Asm.call, targetsIn_nil, targetsIn_cons_call,
      List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with hm | rfl
    · rcases compileCallArgsR_targetsIn tab fl args t hm with rfl | rfl <;> simp
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f, rfl, hok.1.1⟩))))))
  | abort e =>
    intro _ _ _ _ t _ hm
    dsimp only [compileSR] at hm
    by_cases h0 : (e.constVal? == some 0) = true
    · simp only [h0, ↓reduceIte, Asm.j, targetsIn_cons_j, targetsIn_nil, List.mem_singleton] at hm
      subst hm
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,
        constVal_eq_zero_implies_stmtHasAbort0 h0⟩))))))
    · simp only [h0, Bool.false_eq_true, ↓reduceIte, targetsIn_append, List.mem_append,
        Asm.j, targetsIn_nil, targetsIn_cons_j,
        List.mem_cons, List.mem_nil_iff, or_false] at hm
      rcases hm with hm | rfl
      · rw [compileETo_targetsIn tab fl e 0 AbiReg.a0 t hm]; simp
      · simp
  | copy64 d di src si n =>
    intro lblId _ _ _ t _ hm
    have hw : ∀ (w : WArr) (tmp : Nat) (x : String),
        x ∈ targetsIn (evalWArrTierToTempR tab fl tmp w).2 → x = errLabel := by
      intro w tmp x hx
      cases w with
      | plain _ =>
        dsimp only [evalWArrTierToTempR] at hx
        rw [targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)] at hx; cases hx
      | tier _ e =>
        dsimp only [evalWArrTierToTempR] at hx
        cases he : exprReg? fl.alloc e with
        | some _ =>
          simp only [he] at hx
          rw [targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)] at hx; cases hx
        | none =>
          simp only [he, targetsIn_append, List.mem_append,
            targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
            List.mem_nil_iff, or_false] at hx
          exact compileETo_targetsIn tab fl e tmp AbiReg.a0 x hx
    simp only [compileSR, targetsIn_append, List.mem_append, or_assoc,
      targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
      targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
      Asm.andi, Asm.slli, Asm.add, Asm.bltu, Asm.sub, Asm.lbl, Asm.beq, Asm.ld, Asm.sd, Asm.addi, Asm.j,
      targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br, targetsIn_cons_label, targetsIn_cons_j,
      List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with hm | hm | hm | hm | hm | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hw d 0 t hm]; simp
    · rw [compileETo_targetsIn tab fl di 1 AbiReg.a0 t hm]; simp
    · rw [hw src 2 t hm]; simp
    · rw [compileETo_targetsIn tab fl si 3 AbiReg.a0 t hm]; simp
    · rw [compileETo_targetsIn tab fl n 4 AbiReg.a0 t hm]; simp
    · simp
    · simp
    · simp
    · simp
    · exact Or.inl (by
        simp only [compileSR, lblNames_append, Asm.slli, Asm.add, Asm.lbl, Asm.beq, Asm.ld,
          Asm.sd, Asm.addi, Asm.j, lblNames_cons_instr, lblNames_cons_label, lblNames_cons_br,
          lblNames_cons_j, lblNames_nil, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
        simp)
    · exact Or.inl (by
        simp only [compileSR, lblNames_append, Asm.slli, Asm.add, Asm.lbl, Asm.beq, Asm.ld,
          Asm.sd, Asm.addi, Asm.j, lblNames_cons_instr, lblNames_cons_label, lblNames_cons_br,
          lblNames_cons_j, lblNames_nil, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
        simp)
  | copy8w d di src si n =>
    intro lblId _ _ _ t _ hm
    have hd : ∀ x ∈ targetsIn (evalWArrTierToTempR tab fl 0 d).2, x = errLabel := by
      intro x hx
      cases d with
      | plain _ =>
        dsimp only [evalWArrTierToTempR] at hx
        rw [targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)] at hx; cases hx
      | tier _ e =>
        dsimp only [evalWArrTierToTempR] at hx
        cases he : exprReg? fl.alloc e with
        | some _ =>
          simp only [he] at hx
          rw [targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)] at hx; cases hx
        | none =>
          simp only [he, targetsIn_append, List.mem_append,
            targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
            List.mem_nil_iff, or_false] at hx
          exact compileETo_targetsIn tab fl e 0 AbiReg.a0 x hx
    simp only [compileSR, targetsIn_append, List.mem_append, or_assoc,
      targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
      targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
      Asm.andi, Asm.slli, Asm.add, Asm.bltu, Asm.sub, Asm.lbl, Asm.beq, Asm.lbu, Asm.sd, Asm.addi, Asm.j,
      targetsIn_nil, targetsIn_cons_instr, targetsIn_cons_br, targetsIn_cons_label, targetsIn_cons_j,
      List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with hm | hm | hm | hm | rfl | rfl | hm | rfl | rfl | rfl | rfl
    · rw [hd t hm]; simp
    · rw [compileETo_targetsIn tab fl di 1 AbiReg.a0 t hm]; simp
    · rw [compileETo_targetsIn tab fl si 3 AbiReg.a0 t hm]; simp
    · rw [compileETo_targetsIn tab fl n 4 AbiReg.a0 t hm]; simp
    · simp
    · simp
    · cases src <;> simp only [targetsIn_append,
        targetsIn_of_allInstrs (li_allInstrs _ _),
        targetsIn_of_allInstrs (addImmOff_allInstrs _ _ _ _),
        targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
        List.append_nil, List.not_mem_nil] at hm
    · simp
    · simp
    · exact Or.inl (by
        simp only [compileSR, lblNames_append, Asm.bltu, Asm.sub, Asm.add, Asm.lbl, Asm.beq,
          Asm.lbu, Asm.sd, Asm.addi, Asm.j, lblNames_cons_br, lblNames_cons_instr,
          lblNames_cons_label, lblNames_cons_j, lblNames_nil, List.mem_append, List.mem_cons,
          List.mem_nil_iff, or_false]
        simp)
    · exact Or.inl (by
        simp only [compileSR, lblNames_append, Asm.bltu, Asm.sub, Asm.add, Asm.lbl, Asm.beq,
          Asm.lbu, Asm.sd, Asm.addi, Asm.j, lblNames_cons_br, lblNames_cons_instr,
          lblNames_cons_label, lblNames_cons_j, lblNames_nil, List.mem_append, List.mem_cons,
          List.mem_nil_iff, or_false]
        simp)
  | scan8 x src i e c =>
    intro lblId _ _ _ t _ hm
    simp only [compileSR, targetsIn_append, List.mem_append, or_assoc,
      targetsIn_of_allInstrs (addImmOff_allInstrs _ _ _ _),
      Asm.bltu, Asm.lbl, Asm.bgeu, Asm.add, Asm.lbu, Asm.bne, Asm.addi, Asm.j,
      targetsIn_nil, targetsIn_cons_br, targetsIn_cons_label, targetsIn_cons_instr, targetsIn_cons_j,
      List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with hm | hm | rfl | rfl | rfl | rfl | rfl | hm
    · cases hse : emitSimpleExprR tab fl AbiReg.a0 AbiReg.t5 e with
      | some ce =>
        simp only [hse] at hm
        cases hi : exprReg? fl.alloc i with
        | some _ =>
          simp only [hi, targetsIn_append, List.mem_append, Asm.mv,
            targetsIn_cons_instr, targetsIn_nil,
            targetsIn_of_allInstrs (emitSimpleExprR_allInstrs hse),
            List.mem_nil_iff, or_false] at hm
        | none =>
          simp only [hi, targetsIn_append, List.mem_append, Asm.mv,
            targetsIn_cons_instr, targetsIn_nil,
            targetsIn_of_allInstrs (emitSimpleExprR_allInstrs hse),
            List.mem_nil_iff, or_false] at hm
          rw [compileETo_targetsIn tab fl i 0 AbiReg.a0 t hm]; simp
      | none =>
        simp only [hse, targetsIn_append, List.mem_append,
          targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
          targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
          List.mem_nil_iff, or_false] at hm
        rcases hm with hm | hm
        · rw [compileETo_targetsIn tab fl i 0 AbiReg.a0 t hm]; simp
        · rw [compileETo_targetsIn tab fl e 1 AbiReg.a0 t hm]; simp
    · cases src <;> simp only [targetsIn_append,
        targetsIn_of_allInstrs (li_allInstrs _ _),
        targetsIn_of_allInstrs (addImmOff_allInstrs _ _ _ _),
        targetsIn_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
        List.append_nil, List.not_mem_nil] at hm
    · simp
    · simp
    · exact Or.inl (by
        simp only [compileSR, lblNames_append, Asm.lbl, Asm.bgeu, Asm.add, Asm.lbu, Asm.bne,
          Asm.addi, Asm.j, lblNames_cons_label, lblNames_cons_br, lblNames_cons_instr,
          lblNames_cons_j, lblNames_nil, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
        simp)
    · exact Or.inl (by
        simp only [compileSR, lblNames_append, Asm.lbl, Asm.bgeu, Asm.add, Asm.lbu, Asm.bne,
          Asm.addi, Asm.j, lblNames_cons_label, lblNames_cons_br, lblNames_cons_instr,
          lblNames_cons_j, lblNames_nil, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
        simp)
    · exact Or.inl (by
        simp only [compileSR, lblNames_append, Asm.lbl, Asm.bgeu, Asm.add, Asm.lbu, Asm.bne,
          Asm.addi, Asm.j, lblNames_cons_label, lblNames_cons_br, lblNames_cons_instr,
          lblNames_cons_j, lblNames_nil, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
        simp)
    · cases hl : fl.alloc.lookup x with
      | some _ => simp only [hl] at hm; cases hm
      | none =>
        simp only [hl] at hm
        split at hm
        · cases hm
        · rw [targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)] at hm; cases hm

private theorem lookup_isSome_mem_lblNames (tab : Tab) (p : Prog) (g : FnName)
    (hg : (List.lookup g p).isSome = true) :
    fnLabel g ∈ lblNames (p.flatMap fun (f, fd) => compileFn tab f fd) := by
  have hmem : ∃ fd, (g, fd) ∈ p := by
    induction p with
    | nil => simp at hg
    | cons kv rest ih =>
      rcases kv with ⟨k, v⟩
      dsimp [List.lookup] at hg
      split at hg
      · next hk =>
        have hk' : g = k := beq_iff_eq.mp hk
        subst hk'; exact ⟨v, by simp⟩
      · obtain ⟨fd, hfd⟩ := ih hg
        exact ⟨fd, List.mem_cons_of_mem _ hfd⟩
  obtain ⟨fd, hfd⟩ := hmem
  rw [lblNames_flatMap, List.mem_flatMap]
  refine ⟨(g, fd), hfd, ?_⟩
  dsimp only [compileFn]
  simp only [lblNames_append, List.mem_append]
  left; left; left
  have hite : ∀ (c : Bool) (a b : List AsmItem),
      fnLabel g ∈ lblNames a → fnLabel g ∈ lblNames b →
      fnLabel g ∈ lblNames (if c then a else b) := by
    intro c a b ha hb; cases c <;> simpa
  apply hite
  · simp only [lblNames_append, lblNames_map_retarget, lblNames_singleton_lbl,
      List.mem_append, List.mem_singleton, true_or]
  · simp only [lblNames_append, lblNames_singleton_lbl,
      List.mem_append, List.mem_singleton, true_or]

private theorem checkerDriver_chip_targetsIn_of_drv (drv : List AsmItem)
    (herr : errLabel ∈ lblNames drv)
    (habort : abortLabel ∈ lblNames drv)
    (hexh : exhaustedLabel ∈ lblNames drv)
    (hdrvT : ∀ t ∈ targetsIn drv, t ∈ lblNames drv ∨ t = fnLabel "check") :
    ∀ t ∈ targetsIn (drv ++ (orderProgFns checkerProgMini).flatMap (fun (f, fd) => compileFn checkerTabMini f fd)),
      t ∈ lblNames (drv ++ (orderProgFns checkerProgMini).flatMap (fun (f, fd) => compileFn checkerTabMini f fd)) := by
  have hprog := checkerProgMini_progOkConst0B
  dsimp only [progOkConst0B] at hprog
  simp only [Bool.and_eq_true, List.all_eq_true] at hprog
  have hfok := hprog.2
  have hlookupCheck : (List.lookup "check" checkerProgMini).isSome = true := by
    obtain ⟨fd, hfd, _⟩ := checkerProgMini_lookup_check
    simp [hfd]
  have hcheckLbl : fnLabel "check" ∈ lblNames (checkerProgMini.flatMap fun (f, fd) => compileFn checkerTabMini f fd) :=
    lookup_isSome_mem_lblNames checkerTabMini checkerProgMini "check" hlookupCheck
  have hfnT : ∀ f fd, (f, fd) ∈ checkerProgMini → ∀ t ∈ targetsIn (compileFn checkerTabMini f fd),
      t ∈ lblNames (compileFn checkerTabMini f fd) ∨
        t = errLabel ∨ t = exhaustedLabel ∨ t = abortLabel ∨
        (∃ g, t = fnLabel g ∧ (List.lookup g checkerProgMini).isSome = true) := by
    intro f fd hmem t ht
    have hok := hfok (f, fd) hmem
    let fl := fnFrameLayoutFor checkerTabMini fd
    have hnlEq : fl.nlocals = numLocalsFn fd := fnFrameLayoutFor_nlocals checkerTabMini fd
    let pfx := fnLabel f
    let epilogue := toString (fnLabel f) ++ toString "_epilogue"
    let canTailElide := !stmtMayFallthrough fd.body
    rcases hcb : compileSR checkerTabMini fl pfx 0 none epilogue canTailElide fd.body with ⟨bodyCode, idEnd⟩
    have hbodyT := compileSR_targetsIn checkerTabMini fl pfx epilogue fd.body 0 none canTailElide checkerProgMini t (hnlEq ▸ hok)
    rw [hcb] at hbodyT
    dsimp only at hbodyT
    let framePush : List AsmItem :=
      if fl.frameBytes == 0 then []
      else
        li AbiReg.t2 (BitVec.ofInt 64 fl.frameBytes) ++
        [Asm.bltu AbiReg.sp AbiReg.t2 errLabel,
         Asm.sub AbiReg.sp AbiReg.sp AbiReg.t2,
         Asm.ld AbiReg.t2 AbiReg.gp 8#12,
         Asm.bltu AbiReg.sp AbiReg.t2 errLabel] ++
        (if fl.isLeaf then [] else [Asm.sd AbiReg.sp AbiReg.ra 0#12]) ++
        saveCalleeRegs fl
    let t5Init : List AsmItem :=
      if fl.useT5Gp then [Asm.addi AbiReg.t5 AbiReg.gp 2047#12] else []
    let prologue : List AsmItem :=
      [Asm.lbl pfx] ++ framePush ++ copyParamsR fl fd.nparams ++ zeroLocalsR fl fd ++ t5Init
    let hasErr := hasBranchTo errLabel prologue || hasBranchTo errLabel bodyCode
    let hasExh := hasBranchTo exhaustedLabel bodyCode
    let hasAb0 := stmtHasAbort0 fd.body
    let needRetarget := hasErr || hasExh
    let errStubLbl := toString pfx ++ toString "_errstub"
    let exhStubLbl := toString pfx ++ toString "_exhstub"
    let abort0Lbl := toString pfx ++ toString "_abort0stub"
    let exhSub? : Option String := if hasExh then some exhStubLbl else none
    let rt := retargetBranchItem errLabel errStubLbl exhaustedLabel exhSub?
    let fallthroughZero : List AsmItem :=
      [Asm.lbl (toString pfx ++ toString "_ret0")] ++
      (if stmtMayFallthrough fd.body then copyTempsToResultsR checkerTabMini fl 0 0 else [])
    let epilogueCode : List AsmItem := [Asm.lbl epilogue] ++ framePopItems fl ++ [Asm.ret]
    let coldStubs : List AsmItem :=
      (if needRetarget then [Asm.lbl errStubLbl, Asm.j errLabel] else []) ++
      (if hasExh then [Asm.lbl exhStubLbl, Asm.j exhaustedLabel] else []) ++
      (if hasAb0 then [Asm.lbl abort0Lbl, Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.j abortLabel] else [])
    have hfnEq : compileFn checkerTabMini f fd =
        (if needRetarget then prologue.map rt ++ bodyCode.map rt else prologue ++ bodyCode) ++
          fallthroughZero ++ epilogueCode ++ coldStubs := by
      dsimp only [compileFn]
      have hcb' : compileSR checkerTabMini fl pfx 0 none epilogue canTailElide fd.body = (bodyCode, idEnd) := hcb
      change (if (hasBranchTo errLabel prologue || hasBranchTo errLabel (compileSR checkerTabMini fl pfx 0 none epilogue canTailElide fd.body).1 ||
            hasBranchTo exhaustedLabel (compileSR checkerTabMini fl pfx 0 none epilogue canTailElide fd.body).1) then
          prologue.map (retargetBranchItem errLabel errStubLbl exhaustedLabel
            (if hasBranchTo exhaustedLabel (compileSR checkerTabMini fl pfx 0 none epilogue canTailElide fd.body).1 then some exhStubLbl else none)) ++
          (compileSR checkerTabMini fl pfx 0 none epilogue canTailElide fd.body).1.map
            (retargetBranchItem errLabel errStubLbl exhaustedLabel
              (if hasBranchTo exhaustedLabel (compileSR checkerTabMini fl pfx 0 none epilogue canTailElide fd.body).1 then some exhStubLbl else none))
        else prologue ++ (compileSR checkerTabMini fl pfx 0 none epilogue canTailElide fd.body).1) ++
        fallthroughZero ++ epilogueCode ++
        ((if (hasBranchTo errLabel prologue || hasBranchTo errLabel (compileSR checkerTabMini fl pfx 0 none epilogue canTailElide fd.body).1 ||
              hasBranchTo exhaustedLabel (compileSR checkerTabMini fl pfx 0 none epilogue canTailElide fd.body).1) then
            [Asm.lbl errStubLbl, Asm.j errLabel] else []) ++
         (if hasBranchTo exhaustedLabel (compileSR checkerTabMini fl pfx 0 none epilogue canTailElide fd.body).1 then
            [Asm.lbl exhStubLbl, Asm.j exhaustedLabel] else []) ++
         (if hasAb0 then [Asm.lbl abort0Lbl, Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.j abortLabel] else [])) = _
      rw [hcb']
    rw [hfnEq] at ht ⊢
    have htg_rt : ∀ {o1 n1 o2 : String} {n2? : Option String} {xs : List AsmItem} {x : String},
        x ∈ targetsIn (xs.map (retargetBranchItem o1 n1 o2 n2?)) →
          x ∈ targetsIn xs ∨ x = n1 ∨ (∃ n2, n2? = some n2 ∧ x = n2) := by
      intro o1 n1 o2 n2? xs x hx
      induction xs with
      | nil => cases hx
      | cons it rest ih =>
        cases it with
        | label _ | instr _ =>
          change x ∈ targetsIn (rest.map (retargetBranchItem o1 n1 o2 n2?)) at hx
          exact ih hx
        | j tgt | «call» tgt =>
          change x ∈ tgt :: targetsIn (rest.map (retargetBranchItem o1 n1 o2 n2?)) at hx
          change x ∈ tgt :: targetsIn rest ∨ _
          rcases List.mem_cons.mp hx with rfl | hx
          · exact Or.inl (List.mem_cons_self)
          · rcases ih hx with h | h | h
            · exact Or.inl (List.mem_cons_of_mem _ h)
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
        | br _ _ _ tgt | brLong _ _ _ tgt =>
          change x ∈ retargetBranchTarget o1 n1 o2 n2? tgt :: targetsIn (rest.map (retargetBranchItem o1 n1 o2 n2?)) at hx
          change x ∈ tgt :: targetsIn rest ∨ _
          rcases List.mem_cons.mp hx with rfl | hx
          · dsimp only [retargetBranchTarget]
            split
            · exact Or.inr (Or.inl rfl)
            · cases n2? with
              | none => exact Or.inl List.mem_cons_self
              | some n2 =>
                dsimp only; split
                · exact Or.inr (Or.inr ⟨n2, rfl, rfl⟩)
                · exact Or.inl List.mem_cons_self
          · rcases ih hx with h | h | h
            · exact Or.inl (List.mem_cons_of_mem _ h)
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
    have hproT : ∀ x ∈ targetsIn prologue, x = errLabel := by
      intro x hx
      have hfpT : ∀ y ∈ targetsIn framePush, y = errLabel := by
        intro y hy
        dsimp only [framePush] at hy
        split at hy
        · cases hy
        · have hra : targetsIn (if fl.isLeaf = true then [] else [Asm.sd AbiReg.sp AbiReg.ra 0#12]) = [] := by
            split <;> rfl
          simp only [targetsIn_append, List.mem_append,
            targetsIn_of_allInstrs (li_allInstrs _ _), hra,
            targetsIn_of_allInstrs (saveCalleeRegs_allInstrs fl),
            Asm.bltu, Asm.sub, Asm.ld,
            targetsIn_nil, targetsIn_cons_br, targetsIn_cons_instr,
            List.mem_cons, List.mem_nil_iff, false_or, or_false] at hy
          rcases hy with rfl | rfl <;> rfl
      have ht5T : targetsIn t5Init = [] := by
        dsimp only [t5Init]; split <;> rfl
      dsimp only [prologue] at hx
      simp only [targetsIn_append, List.mem_append, ht5T,
        Asm.lbl, targetsIn_cons_label, targetsIn_nil,
        targetsIn_of_allInstrs (copyParamsR_allInstrs fl fd.nparams),
        targetsIn_of_allInstrs (zeroLocalsR_allInstrs fl fd),
        List.mem_nil_iff, false_or, or_false] at hx
      exact hfpT x hx
    have hftT : targetsIn fallthroughZero = [] := by
      dsimp only [fallthroughZero]
      have h0 : targetsIn (if stmtMayFallthrough fd.body = true then copyTempsToResultsR checkerTabMini fl 0 0 else []) = [] := by
        split
        · exact targetsIn_of_allInstrs (copyTempsToResultsR_allInstrs _ _ _ _)
        · rfl
      simp only [targetsIn_append, h0, Asm.lbl, targetsIn_cons_label, targetsIn_nil, List.append_nil]
    have hepiT : targetsIn epilogueCode = [] := by
      dsimp only [epilogueCode]
      simp only [targetsIn_append, targetsIn_of_allInstrs (framePopItems_allInstrs fl),
        Asm.lbl, Asm.ret, targetsIn_cons_label, targetsIn_cons_instr, targetsIn_nil, List.append_nil]
    have hcoldT : ∀ x ∈ targetsIn coldStubs, x = errLabel ∨ x = exhaustedLabel ∨ x = abortLabel := by
      intro x hx
      dsimp only [coldStubs] at hx
      rw [targetsIn_append, targetsIn_append, List.mem_append, List.mem_append] at hx
      rcases hx with (h1 | h2) | h3
      · split at h1
        · left; simpa [Asm.lbl, Asm.j, targetsIn_cons_label, targetsIn_cons_j, targetsIn_nil] using h1
        · cases h1
      · split at h2
        · right; left; simpa [Asm.lbl, Asm.j, targetsIn_cons_label, targetsIn_cons_j, targetsIn_nil] using h2
        · cases h2
      · split at h3
        · right; right; simpa [Asm.lbl, Asm.addi, Asm.j, targetsIn_cons_label, targetsIn_cons_instr, targetsIn_cons_j, targetsIn_nil] using h3
        · cases h3
    have hmemEpi : epilogue ∈ lblNames epilogueCode := by
      dsimp only [epilogueCode]
      simp only [lblNames_append, lblNames_singleton_lbl, List.mem_append, List.mem_singleton]
      simp
    have hmemAb0 : hasAb0 = true → abort0Lbl ∈ lblNames coldStubs := by
      intro hab
      dsimp only [coldStubs]
      simp only [hab, ↓reduceIte, lblNames_append, Asm.lbl, Asm.addi, Asm.j,
        lblNames_cons_label, lblNames_cons_instr, lblNames_cons_j, lblNames_nil,
        List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
      simp
    simp only [targetsIn_append, List.mem_append, hftT, hepiT, List.mem_nil_iff, or_false] at ht
    rcases ht with ht_main | ht_cold
    · cases hnr : needRetarget with
      | false =>
        simp only [hnr, Bool.false_eq_true, ↓reduceIte, targetsIn_append, List.mem_append] at ht_main
        rcases ht_main with ht_pro | ht_body
        · rw [hproT t ht_pro]; simp
        · rcases hbodyT ht_body with hb | rfl | ⟨b, hb, _⟩ | rfl | rfl | rfl | ⟨rfl, hab⟩ | ⟨g, hg, hgl⟩
          · exact Or.inl (by simp only [Bool.false_eq_true, ↓reduceIte, lblNames_append, List.mem_append, hb, true_or, or_true])
          · exact Or.inl (by simp only [lblNames_append, List.mem_append, hmemEpi, true_or, or_true])
          · cases hb
          · simp
          · simp
          · simp
          · exact Or.inl (by rw [lblNames_append, List.mem_append]; exact Or.inr (hmemAb0 hab))
          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨g, hg, hgl⟩)))
      | true =>
        have hmemErr : errStubLbl ∈ lblNames coldStubs := by
          dsimp only [coldStubs]
          simp only [hnr, ↓reduceIte, lblNames_append, Asm.lbl, Asm.j,
            lblNames_cons_label, lblNames_cons_j, lblNames_nil,
            List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
          simp
        simp only [hnr, ↓reduceIte, targetsIn_append, List.mem_append] at ht_main
        rcases ht_main with ht_pro | ht_body
        · rcases htg_rt ht_pro with ht_pro | rfl | ⟨n2, hn2, rfl⟩
          · rw [hproT t ht_pro]; simp
          · exact Or.inl (by simp only [lblNames_append, List.mem_append, hmemErr, or_true])
          · have hh : hasExh = true := by
              cases hhb : hasExh with
              | false => simp [exhSub?, hhb] at hn2
              | true => rfl
            have hn2eq : exhStubLbl = t := by
              simp only [exhSub?, hh, ↓reduceIte, Option.some.injEq] at hn2; exact hn2
            rw [← hn2eq]
            exact Or.inl (by
              simp only [coldStubs, hh, ↓reduceIte, lblNames_append, Asm.lbl, Asm.j,
                lblNames_cons_label, lblNames_cons_j, lblNames_nil,
                List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
              simp)
        · rcases htg_rt ht_body with ht_body | rfl | ⟨n2, hn2, rfl⟩
          · rcases hbodyT ht_body with hb | rfl | ⟨b, hb, _⟩ | rfl | rfl | rfl | ⟨rfl, hab⟩ | ⟨g, hg, hgl⟩
            · exact Or.inl (by
                simp only [rt, ↓reduceIte, lblNames_append, lblNames_map_retarget,
                  List.mem_append, hb, true_or, or_true])
            · exact Or.inl (by simp only [lblNames_append, List.mem_append, hmemEpi, true_or, or_true])
            · cases hb
            · simp
            · simp
            · simp
            · exact Or.inl (by rw [lblNames_append, List.mem_append]; exact Or.inr (hmemAb0 hab))
            · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨g, hg, hgl⟩)))
          · exact Or.inl (by simp only [lblNames_append, List.mem_append, hmemErr, or_true])
          · have hh : hasExh = true := by
              cases hhb : hasExh with
              | false => simp [exhSub?, hhb] at hn2
              | true => rfl
            have hn2eq : exhStubLbl = t := by
              simp only [exhSub?, hh, ↓reduceIte, Option.some.injEq] at hn2; exact hn2
            rw [← hn2eq]
            exact Or.inl (by
              simp only [coldStubs, hh, ↓reduceIte, lblNames_append, Asm.lbl, Asm.j,
                lblNames_cons_label, lblNames_cons_j, lblNames_nil,
                List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
              simp)
    · rcases hcoldT t ht_cold with rfl | rfl | rfl <;> simp
  have hpermOrd := orderProgFns_perm checkerProgMini
  have hpermLbl : (lblNames ((orderProgFns checkerProgMini).flatMap fun (f, fd) => compileFn checkerTabMini f fd)).Perm
      (lblNames (checkerProgMini.flatMap fun (f, fd) => compileFn checkerTabMini f fd)) := by
    rw [lblNames_flatMap, lblNames_flatMap]
    exact list_perm_flatMap hpermOrd (fun (f, fd) => lblNames (compileFn checkerTabMini f fd))
  intro t ht
  rw [targetsIn_append, List.mem_append] at ht
  rw [lblNames_append, List.mem_append]
  rcases ht with ht1 | ht2
  · rcases hdrvT t ht1 with h | rfl
    · exact Or.inl h
    · exact Or.inr (hpermLbl.mem_iff.mpr hcheckLbl)
  · rw [targetsIn_flatMap, List.mem_flatMap] at ht2
    obtain ⟨⟨f, fd⟩, hmemOrd, ht'⟩ := ht2
    have hmem : (f, fd) ∈ checkerProgMini := hpermOrd.mem_iff.mp hmemOrd
    rcases hfnT f fd hmem t ht' with hf | rfl | rfl | rfl | ⟨g, rfl, hg⟩
    · exact Or.inr (by rw [lblNames_flatMap, List.mem_flatMap]; exact ⟨(f, fd), hmemOrd, hf⟩)
    · exact Or.inl herr
    · exact Or.inl hexh
    · exact Or.inl habort
    · exact Or.inr (hpermLbl.mem_iff.mpr (lookup_isSome_mem_lblNames checkerTabMini checkerProgMini g hg))

private theorem drvFillConstLoop_targetsIn (loopLbl doneLbl : String) (off : Int)
    (val : BitVec 64) (count : Nat) :
    ∀ t ∈ targetsIn (drvFillConstLoop loopLbl doneLbl off val count),
      t ∈ lblNames (drvFillConstLoop loopLbl doneLbl off val count) := by
  intro t ht
  rw [drvFillConstLoop_lblNames_eq]
  by_cases hc : (count == 0) = true
  · simp only [drvFillConstLoop, hc, ↓reduceIte, targetsIn_nil, List.not_mem_nil] at ht
  · simp only [drvFillConstLoop, hc, Bool.false_eq_true, ↓reduceIte,
      targetsIn_append, targetsIn_of_allInstrs (addImmOff_allInstrs _ _ _ _),
      targetsIn_of_allInstrs (li_allInstrs _ _)] at ht
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    dsimp only [Asm.lbl, Asm.beq, Asm.sd, Asm.addi, Asm.j] at ht
    simp only [targetsIn_nil, targetsIn_cons_label, targetsIn_cons_br, targetsIn_cons_instr,
      targetsIn_cons_j, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ht ⊢
    exact ht.symm

private theorem drvFillStrideLoop_targetsIn (loopLbl doneLbl : String) (off : Int)
    (initOff stride : BitVec 64) (count : Nat) :
    ∀ t ∈ targetsIn (drvFillStrideLoop loopLbl doneLbl off initOff stride count),
      t ∈ lblNames (drvFillStrideLoop loopLbl doneLbl off initOff stride count) := by
  intro t ht
  rw [drvFillStrideLoop_lblNames_eq]
  by_cases hc : (count == 0) = true
  · simp only [drvFillStrideLoop, hc, ↓reduceIte, targetsIn_nil, List.not_mem_nil] at ht
  · simp only [drvFillStrideLoop, hc, Bool.false_eq_true, ↓reduceIte,
      targetsIn_append, targetsIn_of_allInstrs (addImmOff_allInstrs _ _ _ _),
      targetsIn_of_allInstrs (li_allInstrs _ _)] at ht
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    dsimp only [Asm.lbl, Asm.beq, Asm.sd, Asm.add, Asm.addi, Asm.j] at ht
    simp only [targetsIn_nil, targetsIn_cons_label, targetsIn_cons_br, targetsIn_cons_instr,
      targetsIn_cons_j, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ht ⊢
    exact ht.symm

private theorem drvRomStoresAsm_allInstrs (romBase : Int) (bs : List UInt8) :
    allInstrs (drvRomStoresAsm romBase bs) = true := by
  have hsw : ∀ (r : Reg) (slots : List Nat), allInstrs (slots.map fun (s : Nat) =>
      Asm.sw AbiReg.t0 r (BitVec.ofInt 12 (4 * Int.ofNat s - 2048))) = true := by
    intro r slots
    induction slots with
    | nil => rfl
    | cons _ _ ih =>
      rw [List.map_cons, allInstrs_cons, Bool.and_eq_true]
      exact ⟨rfl, ih⟩
  dsimp only [drvRomStoresAsm]
  refine allInstrs_flatMap fun ⟨ws, ci⟩ _ => ?_
  dsimp only [drvRomChunkAsm]
  rw [allInstrs_append, Bool.and_eq_true]
  refine ⟨addImmOff_allInstrs _ _ _ _, allInstrs_flatMap fun ⟨v, slots⟩ _ => ?_⟩
  dsimp only [drvRomGroupAsm]
  split
  · exact hsw AbiReg.zero slots
  · rw [allInstrs_append, Bool.and_eq_true]
    exact ⟨allInstrs_map_instr _, hsw AbiReg.t1 slots⟩

private theorem drvInitSubAsm_targetsIn (tab : Tab) :
    ∀ t ∈ targetsIn (drvInitSubAsm tab), t ∈ lblNames (drvInitSubAsm tab) := by
  have hbufBT : targetsIn (List.flatMap (fun p =>
      storeMemOff .sd AbiReg.gp (if p == 0 then AbiReg.a0 else AbiReg.a2) AbiReg.t0 (tab.dbase p))
      (List.range tab.nbuf)) = [] := by
    rw [targetsIn_flatMap, List.flatMap_eq_nil_iff]
    intro _ _; exact targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)
  have hbufLT : targetsIn (List.flatMap (fun p =>
      storeMemOff .sd AbiReg.gp (if p == 0 then AbiReg.a1 else AbiReg.a3) AbiReg.t0 (tab.dlen p))
      (List.range tab.nbuf)) = [] := by
    rw [targetsIn_flatMap, List.flatMap_eq_nil_iff]
    intro _ _; exact targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)
  have hromT : targetsIn (drvRomStoresAsm tab.romBase tab.rom) = [] :=
    targetsIn_of_allInstrs (drvRomStoresAsm_allInstrs _ _)
  intro t ht
  dsimp only [drvInitSubAsm] at ht ⊢
  simp only [targetsIn_append, hbufBT, hbufLT, hromT,
    targetsIn_of_allInstrs (li_allInstrs _ _),
    Asm.lbl, Asm.add, Asm.sd, Asm.ret,
    targetsIn_nil, targetsIn_cons_label, targetsIn_cons_instr,
    List.nil_append, List.append_nil, List.mem_append, or_assoc] at ht
  simp only [lblNames_append, List.mem_append]
  rcases ht with ht | ht | ht | ht | ht | ht
  · have h := drvFillStrideLoop_targetsIn _ _ _ _ _ _ t ht; simp only [h, true_or, or_true]
  · have h := drvFillConstLoop_targetsIn _ _ _ _ _ t ht; simp only [h, true_or, or_true]
  · have h := drvFillConstLoop_targetsIn _ _ _ _ _ t ht; simp only [h, true_or, or_true]
  · have h := drvFillConstLoop_targetsIn _ _ _ _ _ t ht; simp only [h, true_or, or_true]
  · have h := drvFillConstLoop_targetsIn _ _ _ _ _ t ht; simp only [h, true_or, or_true]
  · have h := drvFillConstLoop_targetsIn _ _ _ _ _ t ht; simp only [h, true_or, or_true]

private theorem checkerChipAsm_targetsIn :
    ∀ t ∈ targetsIn checkerChipAsm, t ∈ lblNames checkerChipAsm := by
  have hdrvLbl := checkerDriverAsm_checkerTabMini_lblNames
  let drv := checkerDriverAsm checkerTabMini ++ checkerCmpDriverAsm checkerTabMini
  have memDrv : ∀ s, s ∈ lblNames (checkerDriverAsm checkerTabMini) → s ∈ lblNames drv :=
    fun s hs => by rw [lblNames_append, List.mem_append]; exact Or.inl hs
  have herr : errLabel ∈ lblNames drv := memDrv _ (by rw [hdrvLbl]; simp [errLabel])
  have habort : abortLabel ∈ lblNames drv := memDrv _ (by rw [hdrvLbl]; simp [abortLabel])
  have hexh : exhaustedLabel ∈ lblNames drv := memDrv _ (by rw [hdrvLbl]; simp [exhaustedLabel])
  have hdone : drvDoneLabel ∈ lblNames drv := memDrv _ (by rw [hdrvLbl]; simp [drvDoneLabel])
  have hretRest : retRestoreLabel ∈ lblNames drv := memDrv _ (by rw [hdrvLbl]; simp [retRestoreLabel])
  have hinitLbl : drvInitLabel ∈ lblNames drv := memDrv _ (by rw [hdrvLbl]; simp [drvInitLabel])
  refine checkerDriver_chip_targetsIn_of_drv drv herr habort hexh (fun t ht => ?_)
  dsimp only [drv] at ht
  rw [targetsIn_append, List.mem_append] at ht
  rcases ht with ht | ht
  · dsimp only [checkerDriverAsm] at ht
    change t ∈ targetsIn _ at ht
    rw [targetsIn_append, List.mem_append] at ht
    rcases ht with ht | ht
    · simp only [targetsIn_append,
        targetsIn_of_allInstrs (li_allInstrs _ _),
        targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
        targetsIn_of_allInstrs (addImmOff_allInstrs _ _ _ _),
        targetsIn_of_allInstrs (callerSaveAsm_allInstrs _ _),
        targetsIn_of_allInstrs (callerRestoreRetAsm_allInstrs _ _)] at ht
      dsimp only [Asm.lbl, Asm.j, Asm.call, Asm.beq, Asm.blt, Asm.bge, Asm.bltu, Asm.raw,
        Asm.mv, Asm.addi, Asm.add, Asm.slli, Asm.srli, Asm.ld, Asm.sd, Asm.ret] at ht
      simp only [targetsIn_nil, targetsIn_cons_label, targetsIn_cons_j, targetsIn_cons_call,
        targetsIn_cons_br, targetsIn_cons_instr, List.mem_append, List.mem_cons,
        List.mem_nil_iff, false_or, or_false, or_assoc] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact Or.inr rfl | exact Or.inl (by assumption)
    · left
      apply memDrv
      rw [checkerDriverAsm_lblNames_eq, List.mem_append]
      exact Or.inr (drvInitSubAsm_targetsIn checkerTabMini t ht)
  · dsimp only [checkerCmpDriverAsm] at ht
    change t ∈ targetsIn _ at ht
    simp only [targetsIn_append,
      targetsIn_of_allInstrs (li_allInstrs _ _),
      targetsIn_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
      targetsIn_of_allInstrs (addImmOff_allInstrs _ _ _ _),
      targetsIn_of_allInstrs (callerSaveAsm_allInstrs _ _)] at ht
    dsimp only [Asm.lbl, Asm.j, Asm.call, Asm.beq, Asm.blt, Asm.bge, Asm.bltu, Asm.bne, Asm.raw,
      Asm.mv, Asm.addi, Asm.add, Asm.slli, Asm.srli, Asm.ld, Asm.sd, Asm.ret] at ht
    simp only [targetsIn_nil, targetsIn_cons_label, targetsIn_cons_j, targetsIn_cons_call,
      targetsIn_cons_br, targetsIn_cons_instr, List.mem_append, List.mem_cons,
      List.mem_nil_iff, false_or, or_false, or_assoc] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inr rfl | exact Or.inl (by assumption)

/-- **`checkerChipAsm_collectFarLabels_ok`:** `collectFarLabels checkerChipAsm` succeeds
    with no duplicate labels. -/
theorem checkerChipAsm_collectFarLabels_ok :
    ∃ labels, collectFarLabels checkerChipAsm = .ok labels := by
  obtain ⟨labels, hcol, _⟩ := collectFarLabels_ok_of_nodup checkerChipAsm_lblNames_nodup
  exact ⟨labels, hcol⟩

/-- **`checkerChipAsm_linkFarSpec_ok`:** `farLinkModel.linkSpec checkerChipAsm` succeeds,
    emitting fewer than `2 ^ 22` RV64 instruction words. -/
theorem checkerChipAsm_linkFarSpec_ok :
    ∃ code labels, farLinkModel.linkSpec checkerChipAsm = .ok (code, labels) ∧
      code.size < 2 ^ 22 := by
  obtain ⟨code, labels, hspec, hsz⟩ := linkFarSpec_ok_of_wf
    checkerChipAsm_lblNames_nodup checkerChipAsm_farTotalWords_lt checkerChipAsm_targetsIn
  exact ⟨code, labels, hspec, hsz ▸ checkerChipAsm_farTotalWords_lt⟩

/-- **`checkerChipAsm_linkFar_ok`:** Fast executable `linkFar checkerChipAsm` succeeds
    with `code.size < 2 ^ 22`. -/
theorem checkerChipAsm_linkFar_ok :
    ∃ code, linkFar checkerChipAsm = .ok code ∧ code.size < 2 ^ 22 := by
  obtain ⟨code, labels, hspec, hsz⟩ := checkerChipAsm_linkFarSpec_ok
  change linkFarSpec checkerChipAsm = .ok (code, labels) at hspec
  refine ⟨code, ?_, hsz⟩
  rw [linkFar_eq_linkFarSpec, hspec]
  rfl

/-- **`checkerChipAsm_linkHybrid_ok`:** `linkHybrid checkerChipAsm` succeeds
    with `code.size < 2 ^ 22`. -/
theorem checkerChipAsm_linkHybrid_ok :
    ∃ code, linkHybrid checkerChipAsm = .ok code ∧ code.size < 2 ^ 22 := by
  obtain ⟨codeFar, labelsFar, hfar, hlt⟩ := checkerChipAsm_linkFarSpec_ok
  change linkFarSpec checkerChipAsm = .ok (codeFar, labelsFar) at hfar
  have hszFar : codeFar.size = farTotalWords checkerChipAsm := linkFarSpec_size hfar
  obtain ⟨code, _, _, hok, hle⟩ := linkHybrid_ok_of_farSpec ⟨codeFar, labelsFar, hfar⟩
  exact ⟨code, hok, by omega⟩

/--
info: 'ConAgua.RISCV.Bridge.checkerChipAsm_noT6Branch' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms checkerChipAsm_noT6Branch

/--
info: 'ConAgua.RISCV.Bridge.checkerChipAsm_lblNames_nodup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms checkerChipAsm_lblNames_nodup

/--
info: 'ConAgua.RISCV.Bridge.checkerChipAsm_farTotalWords_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms checkerChipAsm_farTotalWords_lt

/--
info: 'ConAgua.RISCV.Bridge.checkerChipAsm_totalSize_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms checkerChipAsm_totalSize_lt

/--
info: 'ConAgua.RISCV.Bridge.checkerChipAsm_collectFarLabels_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms checkerChipAsm_collectFarLabels_ok

/--
info: 'ConAgua.RISCV.Bridge.checkerChipAsm_linkFarSpec_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms checkerChipAsm_linkFarSpec_ok

/--
info: 'ConAgua.RISCV.Bridge.checkerChipAsm_linkFar_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms checkerChipAsm_linkFar_ok

/--
info: 'ConAgua.RISCV.Bridge.checkerChipAsm_linkHybrid_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms checkerChipAsm_linkHybrid_ok

end ConAgua.RISCV.Bridge
