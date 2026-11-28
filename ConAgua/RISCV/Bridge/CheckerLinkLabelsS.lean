import ConAgua.RISCV.Bridge.CheckerLinkWfBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Algebraic Label Distinctness (`compileS` helpers) (`ConAgua.RISCV.Bridge.CheckerLinkLabelsS`)

Label-distinctness helpers supporting `(lblNames checkerChipAsm).Nodup`.
-/

namespace ConAgua.RISCV.Bridge

open ConAgua.RISCV.RV64
open ConAgua.RISCV.Compiler
open ConAgua.RISCV.Linker
open _root_.L

/-! ## 4. Algebraic Label Distinctness and `collectFarLabels` -/

private def decStep (a : Nat) (c : Char) : Nat := 10 * a + (c.toNat - '0'.toNat)

private theorem digitChar_toNat_sub {d : Nat} (hd : d < 10) :
    (Nat.digitChar d).toNat - '0'.toNat = d := by
  match d with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl
  | 5 => rfl | 6 => rfl | 7 => rfl | 8 => rfl | 9 => rfl
  | _ + 10 => exfalso; omega

private theorem digitChar_isDigit {d : Nat} (hd : d < 10) :
    (Nat.digitChar d).isDigit = true := by
  match d with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl
  | 5 => rfl | 6 => rfl | 7 => rfl | 8 => rfl | 9 => rfl
  | _ + 10 => exfalso; omega

private theorem toDigitsCore_all_isDigit :
    ∀ fuel n acc, (∀ c ∈ acc, c.isDigit = true) →
      ∀ c ∈ Nat.toDigitsCore 10 fuel n acc, c.isDigit = true := by
  intro fuel
  induction fuel with
  | zero => intro n acc hacc c hc; simpa [Nat.toDigitsCore] using hacc c hc
  | succ fuel ih =>
    intro n acc hacc c hc
    unfold Nat.toDigitsCore at hc
    dsimp only at hc
    split at hc
    · rcases List.mem_cons.mp hc with rfl | hc'
      · exact digitChar_isDigit (Nat.mod_lt n (by omega))
      · exact hacc c hc'
    · refine ih _ _ (fun y hy => ?_) c hc
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact digitChar_isDigit (Nat.mod_lt n (by omega))
      · exact hacc y hy'

private theorem toDigitsCore_ne_nil :
    ∀ fuel n acc, 0 < fuel → Nat.toDigitsCore 10 fuel n acc ≠ [] := by
  intro fuel
  induction fuel with
  | zero => intro _ _ h; omega
  | succ fuel ih =>
    intro n acc _
    unfold Nat.toDigitsCore; dsimp only
    split
    · exact List.cons_ne_nil _ _
    · cases fuel with
      | zero => unfold Nat.toDigitsCore; simp
      | succ f' => exact ih _ _ (by omega)

private theorem foldl_decStep_toDigitsCore :
    ∀ fuel n acc, n ≤ fuel →
      (Nat.toDigitsCore 10 fuel n acc).foldl decStep 0 = acc.foldl decStep n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n acc hn
    have : n = 0 := by omega
    subst this; simp [Nat.toDigitsCore]
  | succ fuel ih =>
    intro n acc hn
    unfold Nat.toDigitsCore; dsimp only
    split
    · simp only [List.foldl_cons, decStep, Nat.mul_zero, Nat.zero_add,
        digitChar_toNat_sub (by omega : n % 10 < 10)]
      rw [Nat.mod_eq_of_lt (by omega)]
    · rw [ih (n / 10) (Nat.digitChar (n % 10) :: acc) (by omega)]
      simp only [List.foldl_cons, decStep, digitChar_toNat_sub (Nat.mod_lt _ (by omega))]
      have : 10 * (n / 10) + n % 10 = n := by omega
      rw [this]

theorem nat_repr_inj {m n : Nat} (h : Nat.repr m = Nat.repr n) : m = n := by
  have hm : (Nat.toDigits 10 m).foldl decStep 0 = m := by
    simpa [Nat.toDigits] using foldl_decStep_toDigitsCore (m + 1) m [] (by omega)
  have hn : (Nat.toDigits 10 n).foldl decStep 0 = n := by
    simpa [Nat.toDigits] using foldl_decStep_toDigitsCore (n + 1) n [] (by omega)
  have hl : Nat.toDigits 10 m = Nat.toDigits 10 n := by
    have h' := congrArg String.toList h
    simpa [Nat.repr, String.toList_ofList] using h'
  rw [← hm, ← hn, hl]

theorem nat_repr_toList_isDigit (n : Nat) :
    ∀ c ∈ (Nat.repr n).toList, c.isDigit = true := by
  intro c hc
  have hc' : c ∈ Nat.toDigits 10 n := by
    simpa [Nat.repr, String.toList_ofList] using hc
  exact toDigitsCore_all_isDigit (n + 1) n [] (fun _ h => by cases h) c hc'

theorem nat_repr_toList_ne_nil (n : Nat) : (Nat.repr n).toList ≠ [] := by
  simpa [Nat.repr, String.toList_ofList, Nat.toDigits] using
    toDigitsCore_ne_nil (n + 1) n [] (by omega)

theorem nat_repr_not_mem_underscore (n : Nat) : '_' ∉ (Nat.repr n).toList := by
  intro h
  have hd := nat_repr_toList_isDigit n '_' h
  simp at hd

theorem list_eq_append_sep_right {α : Type} {c : α}
    {xs₁ ys₁ xs₂ ys₂ : List α} (h1 : c ∉ ys₁) (h2 : c ∉ ys₂)
    (heq : xs₁ ++ c :: ys₁ = xs₂ ++ c :: ys₂) :
    xs₁ = xs₂ ∧ ys₁ = ys₂ := by
  have hrev : ys₁.reverse ++ c :: xs₁.reverse = ys₂.reverse ++ c :: xs₂.reverse := by
    have := congrArg List.reverse heq
    simpa [List.reverse_append] using this
  have hr1 : c ∉ ys₁.reverse := by simpa using h1
  have hr2 : c ∉ ys₂.reverse := by simpa using h2
  have go : ∀ {a₁ b₁ a₂ b₂ : List α}, c ∉ a₁ → c ∉ a₂ →
      a₁ ++ c :: b₁ = a₂ ++ c :: b₂ → a₁ = a₂ ∧ b₁ = b₂ := by
    intro a₁
    induction a₁ with
    | nil =>
      intro b₁ a₂ b₂ _ ha2 h
      cases a₂ with
      | nil => cases h; exact ⟨rfl, rfl⟩
      | cons x a₂' =>
        simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
        exfalso; exact ha2 (h.1 ▸ by simp)
    | cons x a₁' ih =>
      intro b₁ a₂ b₂ ha1 ha2 h
      cases a₂ with
      | nil =>
        simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
        exfalso; exact ha1 (h.1.symm ▸ by simp)
      | cons y a₂' =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, htail⟩ := h
        obtain ⟨ha, hb⟩ := ih (fun hm => ha1 (by simp [hm])) (fun hm => ha2 (by simp [hm])) htail
        exact ⟨congrArg (x :: ·) ha, hb⟩
  obtain ⟨hyrev, hxrev⟩ := go hr1 hr2 hrev
  exact ⟨List.reverse_inj.mp hxrev, List.reverse_inj.mp hyrev⟩

/-- Dynamic statement/condition label tags emitted by `compileC` and `compileS`. -/
def dynTags : List String :=
  ["and", "or", "else", "endif", "while", "endw",
   "c64", "c64_done", "c8w", "c8w_done", "scan", "scan_done"]

/-- Predicate: `s` is a dynamic label `s!"{pfx}_{tag}_{k}"` with `tag ∈ dynTags` and `lo ≤ k < hi`. -/
def isDynLbl (pfx : String) (lo hi : Nat) (s : String) : Prop :=
  ∃ tag ∈ dynTags, ∃ k, lo ≤ k ∧ k < hi ∧ s = pfx ++ "_" ++ tag ++ "_" ++ Nat.repr k

theorem dynLbl_inj {pfx : String} {t₁ t₂ : String}
    (_ht1 : t₁ ∈ dynTags) (_ht2 : t₂ ∈ dynTags) {k₁ k₂ : Nat}
    (heq : pfx ++ "_" ++ t₁ ++ "_" ++ Nat.repr k₁ = pfx ++ "_" ++ t₂ ++ "_" ++ Nat.repr k₂) :
    k₁ = k₂ ∧ t₁ = t₂ := by
  have hchars : (pfx.toList ++ ['_']) ++ (t₁.toList ++ '_' :: (Nat.repr k₁).toList) =
      (pfx.toList ++ ['_']) ++ (t₂.toList ++ '_' :: (Nat.repr k₂).toList) := by
    have := congrArg String.toList heq
    simpa [String.toList_append, List.append_assoc] using this
  have hmid := List.append_cancel_left hchars
  obtain ⟨htchars, hkchars⟩ := list_eq_append_sep_right
    (nat_repr_not_mem_underscore k₁) (nat_repr_not_mem_underscore k₂) hmid
  have hk : Nat.repr k₁ = Nat.repr k₂ := String.toList_inj.mp hkchars
  have ht : t₁ = t₂ := String.toList_inj.mp htchars
  exact ⟨nat_repr_inj hk, ht⟩

theorem compileE_lblNames (tab : Tab) (nlocals : Nat) :
    ∀ (e : Expr) (tmp : Nat), lblNames (compileE tab nlocals tmp e) = [] := by
  intro e
  induction e with
  | const _ => intro _; exact lblNames_of_allInstrs (li_allInstrs _ _)
  | var _ | len8 _ | len64 _ | glob _ => intro _; exact lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _)
  | bin op a b iha ihb =>
    intro tmp
    dsimp only [compileE]
    cases b.constVal? with
    | some w =>
      rw [lblNames_append, iha tmp, lblNames_of_allInstrs (emitBinConstRhs_allInstrs op w), List.nil_append]
    | none =>
      cases a.constVal? with
      | some w =>
        cases op with
        | add | and | or | xor | mul | «mulhi» =>
          rw [lblNames_append, ihb tmp, lblNames_of_allInstrs (emitBinConstRhs_allInstrs _ w), List.nil_append]
        | sub =>
          dsimp only
          split
          · simp only [lblNames_append, ihb tmp, List.nil_append]; rfl
          · simp only [lblNames_append, ihb tmp, lblNames_of_allInstrs (li_allInstrs _ _), List.nil_append]; rfl
        | shl | shr =>
          dsimp only
          simp only [lblNames_append, ihb tmp, lblNames_of_allInstrs (li_allInstrs _ _), List.nil_append]; rfl
      | none =>
        cases hsb : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 b with
        | some cb =>
          simp only [lblNames_append, iha tmp,
            lblNames_of_allInstrs (emitSimpleExpr_allInstrs hsb),
            lblNames_of_allInstrs (emitBinOp_allInstrs op _ _ _), List.nil_append]
        | none =>
          cases hsa : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 a with
          | some ca =>
            simp only [lblNames_append, ihb tmp,
              lblNames_of_allInstrs (emitSimpleExpr_allInstrs hsa),
              lblNames_of_allInstrs (emitBinOp_allInstrs op _ _ _), List.nil_append]
          | none =>
            simp only [lblNames_append, iha tmp, ihb (tmp + 1),
              lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
              lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
              lblNames_of_allInstrs (emitBinOp_allInstrs op _ _ _), List.nil_append]
  | cmpw c a b iha ihb =>
    intro tmp
    dsimp only [compileE]
    split
    · simp only [lblNames_append, iha tmp, List.nil_append]; rfl
    · split
      · simp only [lblNames_append, ihb tmp, List.nil_append]; rfl
      · split
        · simp only [lblNames_append, iha tmp, List.nil_append]; rfl
        · split
          · simp only [lblNames_append, ihb tmp, List.nil_append]; rfl
          · cases hsb : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 b with
            | some cb =>
              simp only [lblNames_append, iha tmp,
                lblNames_of_allInstrs (emitSimpleExpr_allInstrs hsb),
                lblNames_of_allInstrs (emitCmpw_allInstrs c _ _), List.nil_append]
            | none =>
              cases hsa : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 a with
              | some ca =>
                simp only [lblNames_append, ihb tmp,
                  lblNames_of_allInstrs (emitSimpleExpr_allInstrs hsa),
                  lblNames_of_allInstrs (emitCmpw_allInstrs c _ _), List.nil_append]
              | none =>
                simp only [lblNames_append, iha tmp, ihb (tmp + 1),
                  lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
                  lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
                  lblNames_of_allInstrs (emitCmpw_allInstrs c _ _), List.nil_append]
  | ld8 _ _ ih | ld64 _ _ ih =>
    intro tmp
    simp only [compileE, lblNames_append, ih tmp,
      lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append]
    rfl
  | ldc _ _ ih =>
    intro tmp
    simp only [compileE, lblNames_append, ih tmp,
      lblNames_of_allInstrs (li_allInstrs _ _),
      lblNames_of_allInstrs (addImmOff_allInstrs _ _ _ _), List.nil_append]
    rfl
  | ld64t _ t i iht ihi | ld32t _ t i iht ihi =>
    intro tmp
    dsimp only [compileE]
    cases t.constVal? with
    | some _ =>
      dsimp only
      simp only [lblNames_append, ihi tmp,
        lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append]
      rfl
    | none =>
      dsimp only
      cases hst : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 t with
      | some ct =>
        dsimp only
        simp only [lblNames_append, ihi tmp,
          lblNames_of_allInstrs (emitSimpleExpr_allInstrs hst),
          lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append]
        rfl
      | none =>
        dsimp only
        simp only [lblNames_append, iht tmp, ihi (tmp + 1),
          lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append]
        rfl
  | len64t _ t ih =>
    intro tmp
    dsimp only [compileE]
    cases t.constVal? with
    | some _ => exact lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _)
    | none =>
      dsimp only
      simp only [lblNames_append, ih tmp,
        lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append, List.append_nil]
      rfl
  | ld8x8 src _ ih =>
    intro tmp
    have hread : lblNames ([Asm.lbu AbiReg.a0 AbiReg.t1 7#12] ++
        List.flatMap (fun k =>
          [Asm.lbu AbiReg.t2 AbiReg.t1 (BitVec.ofInt 12 k), Asm.slli AbiReg.a0 AbiReg.a0 8#6,
           Asm.or AbiReg.a0 AbiReg.a0 AbiReg.t2]) [6, 5, 4, 3, 2, 1, 0]) = [] := by
      decide
    simp only [compileE, lblNames_append, ih tmp, hread, List.nil_append, List.append_nil]
    refine List.append_eq_nil_iff.mpr ⟨?_, rfl⟩
    cases src <;> simp only [lblNames_append, lblNames_of_allInstrs (li_allInstrs _ _),
      lblNames_of_allInstrs (addImmOff_allInstrs _ _ _ _),
      lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.append_nil]
  | ld32h _ t i hi iht ihi =>
    intro tmp
    dsimp only [compileE]
    cases t.constVal? with
    | some _ =>
      dsimp only
      simp only [lblNames_append, ihi tmp,
        lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append]
      cases hi <;> rfl
    | none =>
      dsimp only
      cases hst : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 t with
      | some ct =>
        dsimp only
        simp only [lblNames_append, ihi tmp,
          lblNames_of_allInstrs (emitSimpleExpr_allInstrs hst),
          lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append]
        cases hi <;> rfl
      | none =>
        dsimp only
        simp only [lblNames_append, iht tmp, ihi (tmp + 1),
          lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append]
        cases hi <;> rfl

theorem compileC_lbls_spec (tab : Tab) (nlocals tmp : Nat) (pfx : String) :
    ∀ (c : Cond) (lblId : Nat) (want : Bool) (target : String),
      lblId ≤ (compileC tab nlocals tmp pfx lblId c want target).2 ∧
      (lblNames (compileC tab nlocals tmp pfx lblId c want target).1).Nodup ∧
      (∀ s ∈ lblNames (compileC tab nlocals tmp pfx lblId c want target).1,
        isDynLbl pfx lblId (compileC tab nlocals tmp pfx lblId c want target).2 s) := by
  intro c
  induction c with
  | cmp op a b =>
    intro lblId want target
    have heq : lblNames (compileC tab nlocals tmp pfx lblId (.cmp op a b) want target).1 = [] := by
      dsimp only [compileC]
      split
      · simp only [lblNames_append, compileE_lblNames, brCmp_lblNames, List.nil_append]
      · split
        · simp only [lblNames_append, compileE_lblNames, brCmp_lblNames, List.nil_append]
        · cases hsb : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 b with
          | some cb =>
            simp only [lblNames_append, compileE_lblNames,
              lblNames_of_allInstrs (emitSimpleExpr_allInstrs hsb),
              brCmp_lblNames, List.nil_append]
          | none =>
            cases hsa : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 a with
            | some ca =>
              simp only [lblNames_append, compileE_lblNames,
                lblNames_of_allInstrs (emitSimpleExpr_allInstrs hsa),
                brCmp_lblNames, List.nil_append]
            | none =>
              simp only [lblNames_append, compileE_lblNames,
                lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
                lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
                brCmp_lblNames, List.nil_append]
    refine ⟨Nat.le_refl _, ?_, ?_⟩
    · rw [heq]; exact List.nodup_nil
    · intro s hs; rw [heq] at hs; cases hs
  | not p ih =>
    intro lblId want target
    exact ih lblId (!want) target
  | and p q ihp ihq =>
    intro lblId want target
    dsimp only [compileC]
    cases want
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rcases h1 : compileC tab nlocals tmp pfx lblId p false target with ⟨cp, id1⟩
      rcases h2 : compileC tab nlocals tmp pfx id1 q false target with ⟨cq, id2⟩
      obtain ⟨hle1, hnd1, hsp1⟩ := ihp lblId false target
      obtain ⟨hle2, hnd2, hsp2⟩ := ihq id1 false target
      rw [h1] at hle1 hnd1 hsp1
      rw [h2] at hle2 hnd2 hsp2
      dsimp only at hle1 hnd1 hsp1 hle2 hnd2 hsp2 ⊢
      refine ⟨Nat.le_trans hle1 hle2, ?_, ?_⟩
      · rw [lblNames_append]
        refine nodup_append_disj hnd1 hnd2 (fun s hs1 hs2 => ?_)
        obtain ⟨t1, ht1, k1, _, hk1hi, heq1⟩ := hsp1 s hs1
        obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hsp2 s hs2
        have ⟨hk, _⟩ := dynLbl_inj ht1 ht2 (heq1.symm.trans heq2)
        omega
      · intro s hs
        rw [lblNames_append, List.mem_append] at hs
        rcases hs with hs | hs
        · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp1 s hs
          exact ⟨t, ht, k, hk1, Nat.lt_of_lt_of_le hk2 hle2, heq⟩
        · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp2 s hs
          exact ⟨t, ht, k, Nat.le_trans hle1 hk1, hk2, heq⟩
    · simp only [↓reduceIte]
      let skipLbl := pfx ++ "_and_" ++ toString lblId
      rcases h1 : compileC tab nlocals tmp pfx (lblId + 1) p false skipLbl with ⟨cp, id1⟩
      rcases h2 : compileC tab nlocals tmp pfx id1 q true target with ⟨cq, id2⟩
      obtain ⟨hle1, hnd1, hsp1⟩ := ihp (lblId + 1) false skipLbl
      obtain ⟨hle2, hnd2, hsp2⟩ := ihq id1 true target
      rw [h1] at hle1 hnd1 hsp1
      rw [h2] at hle2 hnd2 hsp2
      dsimp only at hle1 hnd1 hsp1 hle2 hnd2 hsp2 ⊢
      refine ⟨by omega, ?_, ?_⟩
      · rw [lblNames_append, lblNames_append]
        refine nodup_append_disj (nodup_append_disj hnd1 hnd2 (fun s hs1 hs2 => ?_))
            (by rw [lblNames_singleton_lbl]; simp) (fun s hs12 hs3 => ?_)
        · obtain ⟨t1, ht1, k1, _, hk1hi, heq1⟩ := hsp1 s hs1
          obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hsp2 s hs2
          have ⟨hk, _⟩ := dynLbl_inj ht1 ht2 (heq1.symm.trans heq2)
          omega
        · rw [lblNames_singleton_lbl, List.mem_singleton] at hs3
          subst hs3
          have hskip : toString pfx ++ toString "_and_" ++ toString lblId =
              pfx ++ "_" ++ "and" ++ "_" ++ Nat.repr lblId := by
            change pfx ++ ("_" ++ "and" ++ "_") ++ Nat.repr lblId = _
            simp only [String.append_assoc]
          rcases List.mem_append.mp hs12 with hs1 | hs2
          · obtain ⟨t1, ht1, k1, hk1lo, _, heq1⟩ := hsp1 _ hs1
            have heq1' : pfx ++ "_" ++ "and" ++ "_" ++ Nat.repr lblId =
                pfx ++ "_" ++ t1 ++ "_" ++ Nat.repr k1 := hskip.symm.trans heq1
            have ⟨hk, _⟩ := dynLbl_inj ht1 (by simp [dynTags] : "and" ∈ dynTags) heq1'.symm
            omega
          · obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hsp2 _ hs2
            have heq2' : pfx ++ "_" ++ "and" ++ "_" ++ Nat.repr lblId =
                pfx ++ "_" ++ t2 ++ "_" ++ Nat.repr k2 := hskip.symm.trans heq2
            have ⟨hk, _⟩ := dynLbl_inj ht2 (by simp [dynTags] : "and" ∈ dynTags) heq2'.symm
            omega
      · intro s hs
        rw [lblNames_append, lblNames_append, List.mem_append, List.mem_append] at hs
        rcases hs with (hs1 | hs2) | hs3
        · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp1 s hs1
          exact ⟨t, ht, k, by omega, Nat.lt_of_lt_of_le hk2 hle2, heq⟩
        · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp2 s hs2
          exact ⟨t, ht, k, by omega, hk2, heq⟩
        · rw [lblNames_singleton_lbl, List.mem_singleton] at hs3
          subst hs3
          have hskip : toString pfx ++ toString "_and_" ++ toString lblId =
              pfx ++ "_" ++ "and" ++ "_" ++ Nat.repr lblId := by
            change pfx ++ ("_" ++ "and" ++ "_") ++ Nat.repr lblId = _
            simp only [String.append_assoc]
          exact ⟨"and", by simp [dynTags], lblId, Nat.le_refl _, by omega, hskip⟩
  | or p q ihp ihq =>
    intro lblId want target
    dsimp only [compileC]
    cases want
    · simp only [Bool.false_eq_true, ↓reduceIte]
      let skipLbl := pfx ++ "_or_" ++ toString lblId
      rcases h1 : compileC tab nlocals tmp pfx (lblId + 1) p true skipLbl with ⟨cp, id1⟩
      rcases h2 : compileC tab nlocals tmp pfx id1 q false target with ⟨cq, id2⟩
      obtain ⟨hle1, hnd1, hsp1⟩ := ihp (lblId + 1) true skipLbl
      obtain ⟨hle2, hnd2, hsp2⟩ := ihq id1 false target
      rw [h1] at hle1 hnd1 hsp1
      rw [h2] at hle2 hnd2 hsp2
      dsimp only at hle1 hnd1 hsp1 hle2 hnd2 hsp2 ⊢
      refine ⟨by omega, ?_, ?_⟩
      · rw [lblNames_append, lblNames_append]
        refine nodup_append_disj (nodup_append_disj hnd1 hnd2 (fun s hs1 hs2 => ?_))
            (by rw [lblNames_singleton_lbl]; simp) (fun s hs12 hs3 => ?_)
        · obtain ⟨t1, ht1, k1, _, hk1hi, heq1⟩ := hsp1 s hs1
          obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hsp2 s hs2
          have ⟨hk, _⟩ := dynLbl_inj ht1 ht2 (heq1.symm.trans heq2)
          omega
        · rw [lblNames_singleton_lbl, List.mem_singleton] at hs3
          subst hs3
          have hskip : toString pfx ++ toString "_or_" ++ toString lblId =
              pfx ++ "_" ++ "or" ++ "_" ++ Nat.repr lblId := by
            change pfx ++ ("_" ++ "or" ++ "_") ++ Nat.repr lblId = _
            simp only [String.append_assoc]
          rcases List.mem_append.mp hs12 with hs1 | hs2
          · obtain ⟨t1, ht1, k1, hk1lo, _, heq1⟩ := hsp1 _ hs1
            have heq1' : pfx ++ "_" ++ "or" ++ "_" ++ Nat.repr lblId =
                pfx ++ "_" ++ t1 ++ "_" ++ Nat.repr k1 := hskip.symm.trans heq1
            have ⟨hk, _⟩ := dynLbl_inj ht1 (by simp [dynTags] : "or" ∈ dynTags) heq1'.symm
            omega
          · obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hsp2 _ hs2
            have heq2' : pfx ++ "_" ++ "or" ++ "_" ++ Nat.repr lblId =
                pfx ++ "_" ++ t2 ++ "_" ++ Nat.repr k2 := hskip.symm.trans heq2
            have ⟨hk, _⟩ := dynLbl_inj ht2 (by simp [dynTags] : "or" ∈ dynTags) heq2'.symm
            omega
      · intro s hs
        rw [lblNames_append, lblNames_append, List.mem_append, List.mem_append] at hs
        rcases hs with (hs1 | hs2) | hs3
        · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp1 s hs1
          exact ⟨t, ht, k, by omega, Nat.lt_of_lt_of_le hk2 hle2, heq⟩
        · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp2 s hs2
          exact ⟨t, ht, k, by omega, hk2, heq⟩
        · rw [lblNames_singleton_lbl, List.mem_singleton] at hs3
          subst hs3
          have hskip : toString pfx ++ toString "_or_" ++ toString lblId =
              pfx ++ "_" ++ "or" ++ "_" ++ Nat.repr lblId := by
            change pfx ++ ("_" ++ "or" ++ "_") ++ Nat.repr lblId = _
            simp only [String.append_assoc]
          exact ⟨"or", by simp [dynTags], lblId, Nat.le_refl _, by omega, hskip⟩
    · simp only [↓reduceIte]
      rcases h1 : compileC tab nlocals tmp pfx lblId p true target with ⟨cp, id1⟩
      rcases h2 : compileC tab nlocals tmp pfx id1 q true target with ⟨cq, id2⟩
      obtain ⟨hle1, hnd1, hsp1⟩ := ihp lblId true target
      obtain ⟨hle2, hnd2, hsp2⟩ := ihq id1 true target
      rw [h1] at hle1 hnd1 hsp1
      rw [h2] at hle2 hnd2 hsp2
      dsimp only at hle1 hnd1 hsp1 hle2 hnd2 hsp2 ⊢
      refine ⟨Nat.le_trans hle1 hle2, ?_, ?_⟩
      · rw [lblNames_append]
        refine nodup_append_disj hnd1 hnd2 (fun s hs1 hs2 => ?_)
        obtain ⟨t1, ht1, k1, _, hk1hi, heq1⟩ := hsp1 s hs1
        obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hsp2 s hs2
        have ⟨hk, _⟩ := dynLbl_inj ht1 ht2 (heq1.symm.trans heq2)
        omega
      · intro s hs
        rw [lblNames_append, List.mem_append] at hs
        rcases hs with hs | hs
        · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp1 s hs
          exact ⟨t, ht, k, hk1, Nat.lt_of_lt_of_le hk2 hle2, heq⟩
        · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp2 s hs
          exact ⟨t, ht, k, Nat.le_trans hle1 hk1, hk2, heq⟩

theorem compileEvalExprsToTemps_lblNames (tab : Tab) (nlocals : Nat) :
    ∀ (es : List Expr) (tmp : Nat), lblNames (compileEvalExprsToTemps tab nlocals tmp es) = [] := by
  intro es
  induction es with
  | nil => intro _; rfl
  | cons e es ih =>
    intro tmp
    dsimp only [compileEvalExprsToTemps]
    rw [lblNames_append, ih (tmp + 1), List.append_nil]
    split
    · exact lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)
    · simp only [lblNames_append, compileE_lblNames,
        lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _), List.nil_append]

theorem copyTempsToResults_lblNames (tab : Tab) (nlocals tmp count : Nat) :
    lblNames (copyTempsToResults tab nlocals tmp count) = [] := by
  dsimp only [copyTempsToResults]
  split
  · split <;> rfl
  · rw [lblNames_flatMap, List.flatMap_eq_nil_iff]
    intro i _
    split
    · exact lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _)
    · simp only [lblNames_append, lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
        lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _), List.nil_append]

theorem copyResultsToLocals_lblNames (tab : Tab) (xs : List Var) :
    lblNames (copyResultsToLocals tab xs) = [] := by
  dsimp only [copyResultsToLocals]
  rw [lblNames_flatMap, List.flatMap_eq_nil_iff]
  intro ⟨x, i⟩ _
  split
  · split
    · exact lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)
    · simp [lblNames_append, lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
        lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)]
  · exact lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)

theorem evalWArrTierToTemp_lblNames (tab : Tab) (nlocals tmp : Nat) (w : WArr) :
    lblNames (evalWArrTierToTemp tab nlocals tmp w).2 = [] := by
  cases w with
  | plain _ => exact lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)
  | tier _ t =>
    simp [evalWArrTierToTemp, lblNames_append, compileE_lblNames,
      lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)]

theorem compileStorePair_lblNames (tab : Tab) (nlocals : Nat) (i e : Expr) :
    lblNames (compileStorePair tab nlocals i e) = [] := by
  dsimp only [compileStorePair]
  cases hi : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 i with
  | some ci =>
    simp only [lblNames_append, compileE_lblNames,
      lblNames_of_allInstrs (emitSimpleExpr_allInstrs hi), List.nil_append]
  | none =>
    cases he : emitSimpleExpr tab AbiReg.a0 AbiReg.t1 e with
    | some ce =>
      simp only [lblNames_append, compileE_lblNames,
        lblNames_of_allInstrs (emitSimpleExpr_allInstrs he), List.nil_append, List.append_nil]; rfl
    | none =>
      simp only [lblNames_append, compileE_lblNames,
        lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
        lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append]

theorem compileTierStoreTriple_lblNames (tab : Tab) (nlocals : Nat) (t i e : Expr) :
    lblNames (compileTierStoreTriple tab nlocals t i e) = [] := by
  dsimp only [compileTierStoreTriple]
  cases ht : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 t with
  | some ct =>
    cases hi : emitSimpleExpr tab AbiReg.t3 AbiReg.t4 i with
    | some ci =>
      simp only [lblNames_append, compileE_lblNames,
        lblNames_of_allInstrs (emitSimpleExpr_allInstrs ht),
        lblNames_of_allInstrs (emitSimpleExpr_allInstrs hi), List.nil_append]
    | none =>
      cases he : emitSimpleExpr tab AbiReg.a0 AbiReg.t4 e with
      | some ce =>
        simp only [lblNames_append, compileE_lblNames,
          lblNames_of_allInstrs (emitSimpleExpr_allInstrs ht),
          lblNames_of_allInstrs (emitSimpleExpr_allInstrs he), List.nil_append, List.append_nil]; rfl
      | none =>
        simp only [lblNames_append, compileE_lblNames,
          lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (emitSimpleExpr_allInstrs ht), List.nil_append]
  | none =>
    simp only [lblNames_append, compileE_lblNames,
      lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
      lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append]

section CompileSLblsSpec
set_option maxHeartbeats 600000

theorem compileS_lbls_spec (tab : Tab) (nlocals : Nat) (pfx retLbl : String) :
    ∀ (s : Stmt) (lblId : Nat) (brkLbl : Option String),
      lblId ≤ (compileS tab nlocals pfx lblId brkLbl retLbl s).2 ∧
      (lblNames (compileS tab nlocals pfx lblId brkLbl retLbl s).1).Nodup ∧
      (∀ l ∈ lblNames (compileS tab nlocals pfx lblId brkLbl retLbl s).1,
        isDynLbl pfx lblId (compileS tab nlocals pfx lblId brkLbl retLbl s).2 l) := by
  intro s
  induction s with
  | skip =>
    intro lblId _; exact ⟨Nat.le_refl _, List.nodup_nil, fun _ h => by cases h⟩
  | set x e =>
    intro lblId brkLbl
    have h0 : lblNames (compileS tab nlocals pfx lblId brkLbl retLbl (.set x e)).1 = [] := by
      dsimp only [compileS]
      split
      · exact lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)
      · simp only [lblNames_append, compileE_lblNames,
          lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _), List.nil_append]
    exact ⟨Nat.le_refl _, by rw [h0]; exact List.nodup_nil, fun _ h => by rw [h0] at h; cases h⟩
  | gset x e =>
    intro lblId brkLbl
    have h0 : lblNames (compileS tab nlocals pfx lblId brkLbl retLbl (.gset x e)).1 = [] := by
      dsimp only [compileS]
      split
      · exact lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)
      · simp only [lblNames_append, compileE_lblNames,
          lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _), List.nil_append]
    exact ⟨Nat.le_refl _, by rw [h0]; exact List.nodup_nil, fun _ h => by rw [h0] at h; cases h⟩
  | st8 _ _ _ =>
    intro lblId _; exact ⟨Nat.le_refl _, List.nodup_nil, fun _ h => by cases h⟩
  | st64 a i e =>
    intro lblId brkLbl
    have h0 : lblNames (compileS tab nlocals pfx lblId brkLbl retLbl (.st64 a i e)).1 = [] := by
      simp only [compileS, lblNames_append, compileStorePair_lblNames,
        lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
        List.nil_append, List.append_nil]
      rfl
    exact ⟨Nat.le_refl _, by rw [h0]; exact List.nodup_nil, fun _ h => by rw [h0] at h; cases h⟩
  | st64t a t i e =>
    intro lblId brkLbl
    have h0 : lblNames (compileS tab nlocals pfx lblId brkLbl retLbl (.st64t a t i e)).1 = [] := by
      simp only [compileS, lblNames_append, compileTierStoreTriple_lblNames,
        lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
        List.nil_append, List.append_nil]
      rfl
    exact ⟨Nat.le_refl _, by rw [h0]; exact List.nodup_nil, fun _ h => by rw [h0] at h; cases h⟩
  | st32t a t i e =>
    intro lblId brkLbl
    have h0 : lblNames (compileS tab nlocals pfx lblId brkLbl retLbl (.st32t a t i e)).1 = [] := by
      simp only [compileS, lblNames_append, compileTierStoreTriple_lblNames,
        lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
        List.nil_append, List.append_nil]
      rfl
    exact ⟨Nat.le_refl _, by rw [h0]; exact List.nodup_nil, fun _ h => by rw [h0] at h; cases h⟩
  | brk =>
    intro lblId _; exact ⟨Nat.le_refl _, List.nodup_nil, fun _ h => by cases h⟩
  | abort e =>
    intro lblId brkLbl
    have h0 : lblNames (compileS tab nlocals pfx lblId brkLbl retLbl (.abort e)).1 = [] := by
      simp only [compileS, lblNames_append, compileE_lblNames, List.nil_append]; rfl
    exact ⟨Nat.le_refl _, by rw [h0]; exact List.nodup_nil, fun _ h => by rw [h0] at h; cases h⟩
  | ret es =>
    intro lblId brkLbl
    have h0 : lblNames (compileS tab nlocals pfx lblId brkLbl retLbl (.ret es)).1 = [] := by
      cases es with
      | nil =>
        simp only [compileS, lblNames_append, compileEvalExprsToTemps_lblNames,
          copyTempsToResults_lblNames, List.nil_append]; rfl
      | cons e rest =>
        cases rest with
        | nil => simp only [compileS, lblNames_append, compileE_lblNames, List.nil_append]; rfl
        | cons e2 rs =>
          simp only [compileS, lblNames_append, compileEvalExprsToTemps_lblNames,
            copyTempsToResults_lblNames, List.nil_append]; rfl
    have hid : (compileS tab nlocals pfx lblId brkLbl retLbl (.ret es)).2 = lblId := by
      cases es with | nil => rfl | cons _ r => cases r <;> rfl
    exact ⟨by rw [hid]; exact Nat.le_refl _, by rw [h0]; exact List.nodup_nil, fun _ h => by rw [h0] at h; cases h⟩
  | «call» xs f args =>
    intro lblId brkLbl
    have hptr : lblNames (if args.isEmpty then [] else addImmOff AbiReg.t0 AbiReg.sp AbiReg.t2 (slotOff nlocals)) = [] := by
      split
      · rfl
      · exact lblNames_of_allInstrs (addImmOff_allInstrs _ _ _ _)
    have h0 : lblNames (compileS tab nlocals pfx lblId brkLbl retLbl (.call xs f args)).1 = [] := by
      simp only [compileS, lblNames_append, compileEvalExprsToTemps_lblNames,
        hptr, copyResultsToLocals_lblNames,
        List.nil_append, List.append_nil]
      rfl
    exact ⟨Nat.le_refl _, by rw [h0]; exact List.nodup_nil, fun _ h => by rw [h0] at h; cases h⟩
  | seq s1 s2 ih1 ih2 =>
    intro lblId brkLbl
    dsimp only [compileS]
    rcases h1 : compileS tab nlocals pfx lblId brkLbl retLbl s1 with ⟨c1, id1⟩
    rcases h2 : compileS tab nlocals pfx id1 brkLbl retLbl s2 with ⟨c2, id2⟩
    obtain ⟨hle1, hnd1, hsp1⟩ := ih1 lblId brkLbl
    obtain ⟨hle2, hnd2, hsp2⟩ := ih2 id1 brkLbl
    rw [h1] at hle1 hnd1 hsp1; rw [h2] at hle2 hnd2 hsp2
    dsimp only at hle1 hnd1 hsp1 hle2 hnd2 hsp2 ⊢
    refine ⟨Nat.le_trans hle1 hle2, ?_, ?_⟩
    · rw [lblNames_append]
      refine nodup_append_disj hnd1 hnd2 (fun s hs1 hs2 => ?_)
      obtain ⟨t1, ht1, k1, _, hk1hi, heq1⟩ := hsp1 s hs1
      obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hsp2 s hs2
      have ⟨hk, _⟩ := dynLbl_inj ht1 ht2 (heq1.symm.trans heq2)
      omega
    · intro s hs
      rw [lblNames_append, List.mem_append] at hs
      rcases hs with hs | hs
      · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp1 s hs
        exact ⟨t, ht, k, hk1, Nat.lt_of_lt_of_le hk2 hle2, heq⟩
      · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp2 s hs
        exact ⟨t, ht, k, Nat.le_trans hle1 hk1, hk2, heq⟩
  | ite cond s1 s2 ih1 ih2 =>
    intro lblId brkLbl
    by_cases hs2 : s2 = .skip
    · subst hs2
      dsimp only [compileS]
      let endLbl := pfx ++ "_endif_" ++ toString lblId
      rcases hc : compileC tab nlocals 0 pfx (lblId + 1) cond false endLbl with ⟨cc, id1⟩
      rcases h1 : compileS tab nlocals pfx id1 brkLbl retLbl s1 with ⟨c1, id2⟩
      obtain ⟨hleC, hndC, hspC⟩ := compileC_lbls_spec tab nlocals 0 pfx cond (lblId + 1) false endLbl
      obtain ⟨hle1, hnd1, hsp1⟩ := ih1 id1 brkLbl
      rw [hc] at hleC hndC hspC; rw [h1] at hle1 hnd1 hsp1
      dsimp only at hleC hndC hspC hle1 hnd1 hsp1 ⊢
      have hend : endLbl = pfx ++ "_" ++ "endif" ++ "_" ++ Nat.repr lblId := by
        dsimp only [endLbl]; change pfx ++ ("_" ++ "endif" ++ "_") ++ Nat.repr lblId = _; simp only [String.append_assoc]
      have hlbl : lblNames (cc ++ c1 ++ [Asm.lbl (toString pfx ++ toString "_endif_" ++ toString lblId)]) =
          lblNames cc ++ lblNames c1 ++ [endLbl] := by
        simp only [lblNames_append, lblNames_singleton_lbl]; rfl
      refine ⟨by omega, ?_, ?_⟩
      · rw [hlbl]
        have hndC1 : (lblNames cc ++ lblNames c1).Nodup := by
          refine nodup_append_disj hndC hnd1 (fun s hsC hs1 => ?_)
          obtain ⟨t1, ht1, k1, _, hk1hi, heq1⟩ := hspC s hsC
          obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hsp1 s hs1
          have ⟨hk, _⟩ := dynLbl_inj ht1 ht2 (heq1.symm.trans heq2); omega
        refine nodup_append_disj hndC1 (by simp) (fun s hs hmem => ?_)
        simp only [List.mem_singleton] at hmem; subst hmem
        rcases List.mem_append.mp hs with hsC | hs1
        · obtain ⟨t, ht, k, hklo, _, heq⟩ := hspC _ hsC
          have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "endif") (by simp [dynTags]) (heq.symm.trans hend); omega
        · obtain ⟨t, ht, k, hklo, _, heq⟩ := hsp1 _ hs1
          have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "endif") (by simp [dynTags]) (heq.symm.trans hend); omega
      · intro s hs; rw [hlbl] at hs
        simp only [List.mem_append, List.mem_singleton] at hs
        rcases hs with (hsC | hs1) | rfl
        · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hspC s hsC
          exact ⟨t, ht, k, by omega, by omega, heq⟩
        · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp1 s hs1
          exact ⟨t, ht, k, by omega, hk2, heq⟩
        · exact ⟨"endif", by simp [dynTags], lblId, Nat.le_refl _, by omega, hend⟩
    by_cases hs1 : s1 = .skip
    · subst hs1
      have hce : compileS tab nlocals pfx lblId brkLbl retLbl (.ite cond .skip s2) =
          let endLbl := s!"{pfx}_endif_{lblId}"
          let (cc, id1) := compileC tab nlocals 0 pfx (lblId + 1) cond true endLbl
          let (c2, id2) := compileS tab nlocals pfx id1 brkLbl retLbl s2
          (cc ++ c2 ++ [Asm.lbl endLbl], id2) := by cases s2 with | skip => contradiction | _ => rfl
      rw [hce]
      let endLbl := pfx ++ "_endif_" ++ toString lblId
      rcases hc : compileC tab nlocals 0 pfx (lblId + 1) cond true endLbl with ⟨cc, id1⟩
      rcases h2 : compileS tab nlocals pfx id1 brkLbl retLbl s2 with ⟨c2, id2⟩
      obtain ⟨hleC, hndC, hspC⟩ := compileC_lbls_spec tab nlocals 0 pfx cond (lblId + 1) true endLbl
      obtain ⟨hle2, hnd2, hsp2⟩ := ih2 id1 brkLbl
      rw [hc] at hleC hndC hspC; rw [h2] at hle2 hnd2 hsp2
      have hc' : compileC tab nlocals 0 pfx (lblId + 1) cond true (toString pfx ++ toString "_endif_" ++ toString lblId) = (cc, id1) := hc
      dsimp only at hleC hndC hspC hle2 hnd2 hsp2 ⊢
      rw [hc']; dsimp only; rw [h2]; dsimp only
      have hend : endLbl = pfx ++ "_" ++ "endif" ++ "_" ++ Nat.repr lblId := by
        dsimp only [endLbl]; change pfx ++ ("_" ++ "endif" ++ "_") ++ Nat.repr lblId = _; simp only [String.append_assoc]
      have hlbl : lblNames (cc ++ c2 ++ [Asm.lbl (toString pfx ++ toString "_endif_" ++ toString lblId)]) =
          lblNames cc ++ lblNames c2 ++ [endLbl] := by
        simp only [lblNames_append, lblNames_singleton_lbl]; rfl
      refine ⟨by omega, ?_, ?_⟩
      · rw [hlbl]
        have hndC2 : (lblNames cc ++ lblNames c2).Nodup := by
          refine nodup_append_disj hndC hnd2 (fun s hsC hs2 => ?_)
          obtain ⟨t1, ht1, k1, _, hk1hi, heq1⟩ := hspC s hsC
          obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hsp2 s hs2
          have ⟨hk, _⟩ := dynLbl_inj ht1 ht2 (heq1.symm.trans heq2); omega
        refine nodup_append_disj hndC2 (by simp) (fun s hs hmem => ?_)
        simp only [List.mem_singleton] at hmem; subst hmem
        rcases List.mem_append.mp hs with hsC | hs2
        · obtain ⟨t, ht, k, hklo, _, heq⟩ := hspC _ hsC
          have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "endif") (by simp [dynTags]) (heq.symm.trans hend); omega
        · obtain ⟨t, ht, k, hklo, _, heq⟩ := hsp2 _ hs2
          have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "endif") (by simp [dynTags]) (heq.symm.trans hend); omega
      · intro s hs; rw [hlbl] at hs
        simp only [List.mem_append, List.mem_singleton] at hs
        rcases hs with (hsC | hs2) | rfl
        · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hspC s hsC
          exact ⟨t, ht, k, by omega, by omega, heq⟩
        · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp2 s hs2
          exact ⟨t, ht, k, by omega, hk2, heq⟩
        · exact ⟨"endif", by simp [dynTags], lblId, Nat.le_refl _, by omega, hend⟩
    have hceGen : compileS tab nlocals pfx lblId brkLbl retLbl (.ite cond s1 s2) =
        let elseLbl := s!"{pfx}_else_{lblId}"
        let endLbl := s!"{pfx}_endif_{lblId}"
        let (cc, id1) := compileC tab nlocals 0 pfx (lblId + 1) cond false elseLbl
        let (c1, id2) := compileS tab nlocals pfx id1 brkLbl retLbl s1
        let (c2, id3) := compileS tab nlocals pfx id2 brkLbl retLbl s2
        (cc ++ c1 ++ [Asm.j endLbl, Asm.lbl elseLbl] ++ c2 ++ [Asm.lbl endLbl], id3) := by
      cases s2 with | skip => contradiction | _ => cases s1 with | skip => contradiction | _ => rfl
    rw [hceGen]
    let elseLbl := pfx ++ "_else_" ++ toString lblId
    let endLbl := pfx ++ "_endif_" ++ toString lblId
    rcases hc : compileC tab nlocals 0 pfx (lblId + 1) cond false elseLbl with ⟨cc, id1⟩
    rcases h1 : compileS tab nlocals pfx id1 brkLbl retLbl s1 with ⟨c1, id2⟩
    rcases h2 : compileS tab nlocals pfx id2 brkLbl retLbl s2 with ⟨c2, id3⟩
    obtain ⟨hleC, hndC, hspC⟩ := compileC_lbls_spec tab nlocals 0 pfx cond (lblId + 1) false elseLbl
    obtain ⟨hle1, hnd1, hsp1⟩ := ih1 id1 brkLbl
    obtain ⟨hle2, hnd2, hsp2⟩ := ih2 id2 brkLbl
    rw [hc] at hleC hndC hspC; rw [h1] at hle1 hnd1 hsp1; rw [h2] at hle2 hnd2 hsp2
    have hc' : compileC tab nlocals 0 pfx (lblId + 1) cond false (toString pfx ++ toString "_else_" ++ toString lblId) = (cc, id1) := hc
    dsimp only at hleC hndC hspC hle1 hnd1 hsp1 hle2 hnd2 hsp2 ⊢
    rw [hc']; dsimp only; rw [h1]; dsimp only; rw [h2]; dsimp only
    have helse : elseLbl = pfx ++ "_" ++ "else" ++ "_" ++ Nat.repr lblId := by
      dsimp only [elseLbl]
      change pfx ++ ("_" ++ "else" ++ "_") ++ Nat.repr lblId = _
      simp only [String.append_assoc]
    have hend : endLbl = pfx ++ "_" ++ "endif" ++ "_" ++ Nat.repr lblId := by
      dsimp only [endLbl]
      change pfx ++ ("_" ++ "endif" ++ "_") ++ Nat.repr lblId = _
      simp only [String.append_assoc]
    have hne : elseLbl ≠ endLbl := by
      intro heq
      rw [helse, hend] at heq
      have ⟨_, ht⟩ := dynLbl_inj (pfx := pfx) (t₁ := "else") (t₂ := "endif")
        (by simp [dynTags]) (by simp [dynTags]) heq
      simp at ht
    have hjlbl : ∀ a b, lblNames [Asm.j a, Asm.lbl b] = [b] := fun _ _ => rfl
    have hlbl : lblNames (cc ++ c1 ++ [Asm.j (toString pfx ++ toString "_endif_" ++ toString lblId),
          Asm.lbl (toString pfx ++ toString "_else_" ++ toString lblId)] ++ c2 ++
          [Asm.lbl (toString pfx ++ toString "_endif_" ++ toString lblId)]) =
        lblNames cc ++ lblNames c1 ++ [elseLbl] ++ lblNames c2 ++ [endLbl] := by
      simp only [lblNames_append, hjlbl, lblNames_singleton_lbl]; rfl
    refine ⟨by omega, ?_, ?_⟩
    · rw [hlbl]
      have hndC1 : (lblNames cc ++ lblNames c1).Nodup := by
        refine nodup_append_disj hndC hnd1 (fun s hsC hs1 => ?_)
        obtain ⟨t1, ht1, k1, _, hk1hi, heq1⟩ := hspC s hsC
        obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hsp1 s hs1
        have ⟨hk, _⟩ := dynLbl_inj ht1 ht2 (heq1.symm.trans heq2); omega
      have hndC1e : (lblNames cc ++ lblNames c1 ++ [elseLbl]).Nodup := by
        refine nodup_append_disj hndC1 (by simp) (fun s hs hmem => ?_)
        simp only [List.mem_singleton] at hmem; subst hmem
        rcases List.mem_append.mp hs with hsC | hs1
        · obtain ⟨t, ht, k, hklo, _, heq⟩ := hspC _ hsC
          have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "else") (by simp [dynTags]) (heq.symm.trans helse); omega
        · obtain ⟨t, ht, k, hklo, _, heq⟩ := hsp1 _ hs1
          have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "else") (by simp [dynTags]) (heq.symm.trans helse); omega
      have hndC1e2 : (lblNames cc ++ lblNames c1 ++ [elseLbl] ++ lblNames c2).Nodup := by
        refine nodup_append_disj hndC1e hnd2 (fun s hs hs2 => ?_)
        obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hsp2 s hs2
        simp only [List.mem_append, List.mem_singleton] at hs
        rcases hs with (hsC | hs1) | rfl
        · obtain ⟨t, ht, k, _, hkhi, heq⟩ := hspC s hsC
          have ⟨hk, _⟩ := dynLbl_inj ht ht2 (heq.symm.trans heq2); omega
        · obtain ⟨t, ht, k, _, hkhi, heq⟩ := hsp1 s hs1
          have ⟨hk, _⟩ := dynLbl_inj ht ht2 (heq.symm.trans heq2); omega
        · have ⟨hk, _⟩ := dynLbl_inj (t₁ := "else") (by simp [dynTags]) ht2 (helse.symm.trans heq2); omega
      refine nodup_append_disj hndC1e2 (by simp) (fun s hs hmem => ?_)
      simp only [List.mem_singleton] at hmem; subst hmem
      simp only [List.mem_append, List.mem_singleton] at hs
      rcases hs with ((hsC | hs1) | hEq) | hs2
      · obtain ⟨t, ht, k, hklo, _, heq⟩ := hspC _ hsC
        have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "endif") (by simp [dynTags]) (heq.symm.trans hend); omega
      · obtain ⟨t, ht, k, hklo, _, heq⟩ := hsp1 _ hs1
        have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "endif") (by simp [dynTags]) (heq.symm.trans hend); omega
      · exact hne hEq.symm
      · obtain ⟨t, ht, k, hklo, _, heq⟩ := hsp2 _ hs2
        have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "endif") (by simp [dynTags]) (heq.symm.trans hend); omega
    · intro s hs
      rw [hlbl] at hs
      simp only [List.mem_append, List.mem_singleton] at hs
      rcases hs with (((hsC | hs1) | rfl) | hs2) | rfl
      · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hspC s hsC
        exact ⟨t, ht, k, by omega, by omega, heq⟩
      · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp1 s hs1
        exact ⟨t, ht, k, by omega, by omega, heq⟩
      · exact ⟨"else", by simp [dynTags], lblId, Nat.le_refl _, by omega, helse⟩
      · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp2 s hs2
        exact ⟨t, ht, k, by omega, hk2, heq⟩
      · exact ⟨"endif", by simp [dynTags], lblId, Nat.le_refl _, by omega, hend⟩
  | «while» cond body ih =>
    intro lblId _
    dsimp only [compileS]
    let loopLbl := pfx ++ "_while_" ++ toString lblId
    let endLbl := pfx ++ "_endw_" ++ toString lblId
    rcases hc : compileC tab nlocals 0 pfx (lblId + 1) cond false endLbl with ⟨cc, id1⟩
    rcases hb : compileS tab nlocals pfx id1 (some endLbl) retLbl body with ⟨cb, id2⟩
    obtain ⟨hleC, hndC, hspC⟩ := compileC_lbls_spec tab nlocals 0 pfx cond (lblId + 1) false endLbl
    obtain ⟨hleB, hndB, hspB⟩ := ih id1 (some endLbl)
    rw [hc] at hleC hndC hspC; rw [hb] at hleB hndB hspB
    dsimp only at hleC hndC hspC hleB hndB hspB ⊢
    have hloop : loopLbl = pfx ++ "_" ++ "while" ++ "_" ++ Nat.repr lblId := by
      dsimp only [loopLbl]
      change pfx ++ ("_" ++ "while" ++ "_") ++ Nat.repr lblId = _
      simp only [String.append_assoc]
    have hend : endLbl = pfx ++ "_" ++ "endw" ++ "_" ++ Nat.repr lblId := by
      dsimp only [endLbl]
      change pfx ++ ("_" ++ "endw" ++ "_") ++ Nat.repr lblId = _
      simp only [String.append_assoc]
    have hne : loopLbl ≠ endLbl := by
      intro heq
      rw [hloop, hend] at heq
      have ⟨_, ht⟩ := dynLbl_inj (pfx := pfx) (t₁ := "while") (t₂ := "endw")
        (by simp [dynTags]) (by simp [dynTags]) heq
      simp at ht
    have hwb : ∀ (r : Reg) (k : BitVec 12) (l1 l2 l3 : String),
        lblNames [Asm.beq r AbiReg.zero l1, Asm.addi r r k, Asm.j l2, Asm.lbl l3] = [l3] :=
      fun _ _ _ _ _ => rfl
    have hlbl : lblNames ([Asm.lbl (toString pfx ++ toString "_while_" ++ toString lblId)] ++
          cc ++ cb ++
          [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
           Asm.addi AbiReg.s0 AbiReg.s0 (-1#12),
           Asm.j (toString pfx ++ toString "_while_" ++ toString lblId),
           Asm.lbl (toString pfx ++ toString "_endw_" ++ toString lblId)]) =
        [loopLbl] ++ lblNames cc ++ lblNames cb ++ [endLbl] := by
      simp only [lblNames_append, lblNames_singleton_lbl, hwb]; rfl
    refine ⟨by omega, ?_, ?_⟩
    · rw [hlbl]
      have hndCB : (lblNames cc ++ lblNames cb).Nodup := by
        refine nodup_append_disj hndC hndB (fun s hsC hsB => ?_)
        obtain ⟨t1, ht1, k1, _, hk1hi, heq1⟩ := hspC s hsC
        obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hspB s hsB
        have ⟨hk, _⟩ := dynLbl_inj ht1 ht2 (heq1.symm.trans heq2); omega
      have hndLCB : ([loopLbl] ++ (lblNames cc ++ lblNames cb)).Nodup := by
        refine nodup_append_disj (by simp) hndCB (fun s hs1 hs2 => ?_)
        simp only [List.mem_singleton] at hs1; subst hs1
        rcases List.mem_append.mp hs2 with hsC | hsB
        · obtain ⟨t, ht, k, hklo, _, heq⟩ := hspC _ hsC
          have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "while") (by simp [dynTags]) (heq.symm.trans hloop); omega
        · obtain ⟨t, ht, k, hklo, _, heq⟩ := hspB _ hsB
          have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "while") (by simp [dynTags]) (heq.symm.trans hloop); omega
      have hndLCB' : ([loopLbl] ++ lblNames cc ++ lblNames cb).Nodup := by
        simpa [List.append_assoc] using hndLCB
      refine nodup_append_disj hndLCB' (by simp) (fun s hs hmem => ?_)
      simp only [List.mem_singleton] at hmem; subst hmem
      simp only [List.mem_append, List.mem_singleton] at hs
      rcases hs with (hEq | hsC) | hsB
      · exact hne hEq.symm
      · obtain ⟨t, ht, k, hklo, _, heq⟩ := hspC _ hsC
        have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "endw") (by simp [dynTags]) (heq.symm.trans hend); omega
      · obtain ⟨t, ht, k, hklo, _, heq⟩ := hspB _ hsB
        have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "endw") (by simp [dynTags]) (heq.symm.trans hend); omega
    · intro s hs
      rw [hlbl] at hs
      simp only [List.mem_append, List.mem_singleton] at hs
      rcases hs with ((rfl | hsC) | hsB) | rfl
      · exact ⟨"while", by simp [dynTags], lblId, Nat.le_refl _, by omega, hloop⟩
      · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hspC s hsC
        exact ⟨t, ht, k, by omega, by omega, heq⟩
      · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hspB s hsB
        exact ⟨t, ht, k, by omega, hk2, heq⟩
      · exact ⟨"endw", by simp [dynTags], lblId, Nat.le_refl _, by omega, hend⟩
  | copy64 d di src si n =>
    intro lblId brkLbl
    let loopLbl := toString pfx ++ toString "_c64_" ++ toString lblId
    let doneLbl := toString pfx ++ toString "_c64_done_" ++ toString lblId
    have hloop : loopLbl = pfx ++ "_" ++ "c64" ++ "_" ++ Nat.repr lblId := by
      dsimp only [loopLbl]
      change pfx ++ ("_" ++ "c64" ++ "_") ++ Nat.repr lblId = _
      simp only [String.append_assoc]
    have hdone : doneLbl = pfx ++ "_" ++ "c64_done" ++ "_" ++ Nat.repr lblId := by
      dsimp only [doneLbl]
      change pfx ++ ("_" ++ "c64_done" ++ "_") ++ Nat.repr lblId = _
      simp only [String.append_assoc]
    have hne : loopLbl ≠ doneLbl := by
      intro heq
      rw [hloop, hdone] at heq
      have ⟨_, ht⟩ := dynLbl_inj (pfx := pfx) (t₁ := "c64") (t₂ := "c64_done")
        (by simp [dynTags]) (by simp [dynTags]) heq
      simp at ht
    have hlbl : lblNames (compileS tab nlocals pfx lblId brkLbl retLbl (.copy64 d di src si n)).1 =
        [loopLbl, doneLbl] := by
      simp only [compileS, lblNames_append, evalWArrTierToTemp_lblNames, compileE_lblNames,
        lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
        lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append, List.append_nil]
      rfl
    have hsnd : (compileS tab nlocals pfx lblId brkLbl retLbl (.copy64 d di src si n)).2 = lblId + 1 := rfl
    refine ⟨by rw [hsnd]; omega, ?_, ?_⟩
    · rw [hlbl]; simp [hne]
    · intro s hs; rw [hlbl] at hs; rw [hsnd]
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact ⟨"c64", by simp [dynTags], lblId, Nat.le_refl _, by omega, hloop⟩
      · simp only [List.mem_singleton] at hs'; subst hs'
        exact ⟨"c64_done", by simp [dynTags], lblId, Nat.le_refl _, by omega, hdone⟩
  | copy8w d di src si n =>
    intro lblId brkLbl
    let loopLbl := toString pfx ++ toString "_c8w_" ++ toString lblId
    let doneLbl := toString pfx ++ toString "_c8w_done_" ++ toString lblId
    have hloop : loopLbl = pfx ++ "_" ++ "c8w" ++ "_" ++ Nat.repr lblId := by
      dsimp only [loopLbl]
      change pfx ++ ("_" ++ "c8w" ++ "_") ++ Nat.repr lblId = _
      simp only [String.append_assoc]
    have hdone : doneLbl = pfx ++ "_" ++ "c8w_done" ++ "_" ++ Nat.repr lblId := by
      dsimp only [doneLbl]
      change pfx ++ ("_" ++ "c8w_done" ++ "_") ++ Nat.repr lblId = _
      simp only [String.append_assoc]
    have hne : loopLbl ≠ doneLbl := by
      intro heq
      rw [hloop, hdone] at heq
      have ⟨_, ht⟩ := dynLbl_inj (pfx := pfx) (t₁ := "c8w") (t₂ := "c8w_done")
        (by simp [dynTags]) (by simp [dynTags]) heq
      simp at ht
    have hlbl : lblNames (compileS tab nlocals pfx lblId brkLbl retLbl (.copy8w d di src si n)).1 =
        [loopLbl, doneLbl] := by
      cases src
      · simp only [compileS, lblNames_append, evalWArrTierToTemp_lblNames, compileE_lblNames,
          lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append, List.append_nil]
        rfl
      · simp only [compileS, lblNames_append, evalWArrTierToTemp_lblNames, compileE_lblNames,
          lblNames_of_allInstrs (li_allInstrs _ _),
          lblNames_of_allInstrs (addImmOff_allInstrs _ _ _ _),
          lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append, List.append_nil]
        rfl
    have hsnd : (compileS tab nlocals pfx lblId brkLbl retLbl (.copy8w d di src si n)).2 = lblId + 1 := rfl
    refine ⟨by rw [hsnd]; omega, ?_, ?_⟩
    · rw [hlbl]; simp [hne]
    · intro s hs; rw [hlbl] at hs; rw [hsnd]
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact ⟨"c8w", by simp [dynTags], lblId, Nat.le_refl _, by omega, hloop⟩
      · simp only [List.mem_singleton] at hs'; subst hs'
        exact ⟨"c8w_done", by simp [dynTags], lblId, Nat.le_refl _, by omega, hdone⟩
  | scan8 x src i e c =>
    intro lblId brkLbl
    let loopLbl := toString pfx ++ toString "_scan_" ++ toString lblId
    let doneLbl := toString pfx ++ toString "_scan_done_" ++ toString lblId
    have hloop : loopLbl = pfx ++ "_" ++ "scan" ++ "_" ++ Nat.repr lblId := by
      dsimp only [loopLbl]
      change pfx ++ ("_" ++ "scan" ++ "_") ++ Nat.repr lblId = _
      simp only [String.append_assoc]
    have hdone : doneLbl = pfx ++ "_" ++ "scan_done" ++ "_" ++ Nat.repr lblId := by
      dsimp only [doneLbl]
      change pfx ++ ("_" ++ "scan_done" ++ "_") ++ Nat.repr lblId = _
      simp only [String.append_assoc]
    have hne : loopLbl ≠ doneLbl := by
      intro heq
      rw [hloop, hdone] at heq
      have ⟨_, ht⟩ := dynLbl_inj (pfx := pfx) (t₁ := "scan") (t₂ := "scan_done")
        (by simp [dynTags]) (by simp [dynTags]) heq
      simp at ht
    have hlbl : lblNames (compileS tab nlocals pfx lblId brkLbl retLbl (.scan8 x src i e c)).1 =
        [loopLbl, doneLbl] := by
      cases src
      · simp only [compileS, lblNames_append, compileE_lblNames,
          lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (addImmOff_allInstrs _ _ _ _), List.nil_append, List.append_nil]
        rfl
      · simp only [compileS, lblNames_append, compileE_lblNames,
          lblNames_of_allInstrs (li_allInstrs _ _),
          lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (addImmOff_allInstrs _ _ _ _), List.nil_append, List.append_nil]
        rfl
    have hsnd : (compileS tab nlocals pfx lblId brkLbl retLbl (.scan8 x src i e c)).2 = lblId + 1 := rfl
    refine ⟨by rw [hsnd]; omega, ?_, ?_⟩
    · rw [hlbl]; simp [hne]
    · intro s hs; rw [hlbl] at hs; rw [hsnd]
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact ⟨"scan", by simp [dynTags], lblId, Nat.le_refl _, by omega, hloop⟩
      · simp only [List.mem_singleton] at hs'; subst hs'
        exact ⟨"scan_done", by simp [dynTags], lblId, Nat.le_refl _, by omega, hdone⟩

end CompileSLblsSpec

end ConAgua.RISCV.Bridge
