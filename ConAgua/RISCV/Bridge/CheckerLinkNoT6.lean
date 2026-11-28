import ConAgua.RISCV.Bridge.CheckerLinkWfBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `noT6Branch` Proofs for `checkerChipAsm` (`ConAgua.RISCV.Bridge.CheckerLinkNoT6`)

Proves that no `.br` or `.brLong` pseudo-instruction in `checkerChipAsm`
references scratch register `AbiReg.t6` (`x31`).
-/

namespace ConAgua.RISCV.Bridge

open ConAgua.RISCV.RV64
open ConAgua.RISCV.Compiler
open ConAgua.RISCV.Linker
open _root_.L

/-! ## 3. `noT6Branch` Proof for `checkerChipAsm` -/

theorem compileE_noT6Branch (tab : Tab) (nlocals : Nat) :
    ∀ (e : Expr) (tmp : Nat), noT6Branch (compileE tab nlocals tmp e) = true := by
  intro e
  induction e with
  | const _ => intro _; exact noT6Branch_of_allInstrs (li_allInstrs _ _)
  | var _ | len8 _ | len64 _ | glob _ =>
    intro _; exact noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _)
  | bin op a b iha ihb =>
    intro tmp
    dsimp only [compileE]
    cases b.constVal? with
    | some w =>
      dsimp only
      rw [noT6Branch_append, Bool.and_eq_true]
      exact ⟨iha tmp, noT6Branch_of_allInstrs (emitBinConstRhs_allInstrs op w)⟩
    | none =>
      dsimp only
      cases a.constVal? with
      | some w =>
        dsimp only
        cases op with
        | add | and | or | xor | mul | «mulhi» =>
          dsimp only
          rw [noT6Branch_append, Bool.and_eq_true]
          exact ⟨ihb tmp, noT6Branch_of_allInstrs (emitBinConstRhs_allInstrs _ w)⟩
        | sub =>
          dsimp only
          split
          · rw [noT6Branch_append, Bool.and_eq_true]; exact ⟨ihb tmp, rfl⟩
          · simp only [noT6Branch_append, Bool.and_eq_true, ihb tmp,
              noT6Branch_of_allInstrs (li_allInstrs _ _), true_and]; rfl
        | shl | shr =>
          dsimp only
          simp only [noT6Branch_append, Bool.and_eq_true, ihb tmp,
            noT6Branch_of_allInstrs (li_allInstrs _ _), true_and]; rfl
      | none =>
        dsimp only
        cases hsb : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 b with
        | some cb =>
          simp only [noT6Branch_append, Bool.and_eq_true, iha tmp,
            noT6Branch_of_allInstrs (emitSimpleExpr_allInstrs hsb),
            noT6Branch_of_allInstrs (emitBinOp_allInstrs op _ _ _), and_self]
        | none =>
          cases hsa : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 a with
          | some ca =>
            simp only [noT6Branch_append, Bool.and_eq_true, ihb tmp,
              noT6Branch_of_allInstrs (emitSimpleExpr_allInstrs hsa),
              noT6Branch_of_allInstrs (emitBinOp_allInstrs op _ _ _), and_self]
          | none =>
            simp only [noT6Branch_append, Bool.and_eq_true, iha tmp, ihb (tmp + 1),
              noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
              noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
              noT6Branch_of_allInstrs (emitBinOp_allInstrs op _ _ _), and_self]
  | cmpw c a b iha ihb =>
    intro tmp
    dsimp only [compileE]
    split
    · rw [noT6Branch_append, Bool.and_eq_true]; exact ⟨iha tmp, rfl⟩
    · split
      · rw [noT6Branch_append, Bool.and_eq_true]; exact ⟨ihb tmp, rfl⟩
      · split
        · rw [noT6Branch_append, Bool.and_eq_true]; exact ⟨iha tmp, rfl⟩
        · split
          · rw [noT6Branch_append, Bool.and_eq_true]; exact ⟨ihb tmp, rfl⟩
          · cases hsb : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 b with
            | some cb =>
              simp only [noT6Branch_append, Bool.and_eq_true, iha tmp,
                noT6Branch_of_allInstrs (emitSimpleExpr_allInstrs hsb),
                noT6Branch_of_allInstrs (emitCmpw_allInstrs c _ _), and_self]
            | none =>
              cases hsa : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 a with
              | some ca =>
                simp only [noT6Branch_append, Bool.and_eq_true, ihb tmp,
                  noT6Branch_of_allInstrs (emitSimpleExpr_allInstrs hsa),
                  noT6Branch_of_allInstrs (emitCmpw_allInstrs c _ _), and_self]
              | none =>
                simp only [noT6Branch_append, Bool.and_eq_true, iha tmp, ihb (tmp + 1),
                  noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
                  noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
                  noT6Branch_of_allInstrs (emitCmpw_allInstrs c _ _), and_self]
  | ld8 a i ih | ld64 a i ih =>
    intro tmp
    simp only [compileE, noT6Branch_append, Bool.and_eq_true, ih tmp,
      noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), true_and, and_true]
    decide
  | ldc d i ih =>
    intro tmp
    simp only [compileE, noT6Branch_append, Bool.and_eq_true, ih tmp,
      noT6Branch_of_allInstrs (li_allInstrs _ _),
      noT6Branch_of_allInstrs (addImmOff_allInstrs _ _ _ _), true_and, and_true]
    decide
  | ld64t a t i iht ihi | ld32t a t i iht ihi =>
    intro tmp
    dsimp only [compileE]
    cases t.constVal? with
    | some w =>
      dsimp only
      simp only [noT6Branch_append, Bool.and_eq_true, ihi tmp,
        noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), true_and, and_true]
      decide
    | none =>
      dsimp only
      cases hst : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 t with
      | some ct =>
        dsimp only
        simp only [noT6Branch_append, Bool.and_eq_true, ihi tmp,
          noT6Branch_of_allInstrs (emitSimpleExpr_allInstrs hst),
          noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), true_and, and_true]
        decide
      | none =>
        dsimp only
        simp only [noT6Branch_append, Bool.and_eq_true, iht tmp, ihi (tmp + 1),
          noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
          noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), true_and, and_true]
        decide
  | len64t a t ih =>
    intro tmp
    dsimp only [compileE]
    cases t.constVal? with
    | some _ => exact noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _)
    | none =>
      dsimp only
      simp only [noT6Branch_append, Bool.and_eq_true, ih tmp,
        noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), true_and, and_true]
      decide
  | ld8x8 src i ih =>
    intro tmp
    have hread : noT6Branch ([Asm.lbu AbiReg.a0 AbiReg.t1 7#12] ++
        List.flatMap (fun k =>
          [Asm.lbu AbiReg.t2 AbiReg.t1 (BitVec.ofInt 12 k), Asm.slli AbiReg.a0 AbiReg.a0 8#6,
           Asm.or AbiReg.a0 AbiReg.a0 AbiReg.t2]) [6, 5, 4, 3, 2, 1, 0]) = true := by
      rw [noT6Branch_append, Bool.and_eq_true]
      exact ⟨rfl, noT6Branch_flatMap (fun _ _ => by rfl)⟩
    simp only [compileE, noT6Branch_append, Bool.and_eq_true, ih tmp, hread, true_and, and_true]
    refine ⟨?_, rfl⟩
    cases src <;> simp only [noT6Branch_append, Bool.and_eq_true,
      noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
      noT6Branch_of_allInstrs (li_allInstrs _ _),
      noT6Branch_of_allInstrs (addImmOff_allInstrs _ _ _ _), and_self]
  | ld32h a t i hi iht ihi =>
    intro tmp
    dsimp only [compileE]
    cases t.constVal? with
    | some w =>
      dsimp only
      simp only [noT6Branch_append, Bool.and_eq_true, ihi tmp,
        noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), true_and, and_true]
      cases hi <;> exact ⟨rfl, rfl⟩
    | none =>
      dsimp only
      cases hst : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 t with
      | some ct =>
        dsimp only
        simp only [noT6Branch_append, Bool.and_eq_true, ihi tmp,
          noT6Branch_of_allInstrs (emitSimpleExpr_allInstrs hst),
          noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), true_and, and_true]
        cases hi <;> exact ⟨⟨rfl, rfl⟩, rfl⟩
      | none =>
        dsimp only
        simp only [noT6Branch_append, Bool.and_eq_true, iht tmp, ihi (tmp + 1),
          noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
          noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), true_and, and_true]
        cases hi <;> exact ⟨⟨rfl, rfl⟩, rfl⟩

theorem compileC_noT6Branch (tab : Tab) (nlocals : Nat) (tmp : Nat) (pfx : String) :
    ∀ (c : Cond) (lblId : Nat) (want : Bool) (target : String),
      noT6Branch (compileC tab nlocals tmp pfx lblId c want target).1 = true := by
  intro c
  induction c with
  | cmp op a b =>
    intro lblId want target
    dsimp only [compileC]
    split
    · rw [noT6Branch_append, Bool.and_eq_true]
      exact ⟨compileE_noT6Branch _ _ _ _,
        brCmp_noT6Branch op want AbiReg.a0 AbiReg.zero (by decide) (by decide) target⟩
    · split
      · rw [noT6Branch_append, Bool.and_eq_true]
        exact ⟨compileE_noT6Branch _ _ _ _,
          brCmp_noT6Branch op want AbiReg.zero AbiReg.a0 (by decide) (by decide) target⟩
      · cases hsb : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 b with
        | some cb =>
          simp only [noT6Branch_append, Bool.and_eq_true, compileE_noT6Branch,
            noT6Branch_of_allInstrs (emitSimpleExpr_allInstrs hsb),
            brCmp_noT6Branch op want AbiReg.a0 AbiReg.t0 (by decide) (by decide) target, and_self]
        | none =>
          cases hsa : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 a with
          | some ca =>
            simp only [noT6Branch_append, Bool.and_eq_true, compileE_noT6Branch,
              noT6Branch_of_allInstrs (emitSimpleExpr_allInstrs hsa),
              brCmp_noT6Branch op want AbiReg.t0 AbiReg.a0 (by decide) (by decide) target, and_self]
          | none =>
            simp only [noT6Branch_append, Bool.and_eq_true, compileE_noT6Branch,
              noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
              noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
              brCmp_noT6Branch op want AbiReg.t0 AbiReg.a0 (by decide) (by decide) target, and_self]
  | not p ih =>
    intro lblId want target
    simpa [compileC] using ih lblId (!want) target
  | and p q ihp ihq =>
    intro lblId want target
    dsimp only [compileC]
    cases want
    · simp only [Bool.false_eq_true, ↓reduceIte, noT6Branch_append, Bool.and_eq_true]
      exact ⟨ihp lblId false target, ihq _ false target⟩
    · simp only [↓reduceIte, noT6Branch_append, Bool.and_eq_true]
      exact ⟨⟨ihp (lblId + 1) false _, ihq _ true target⟩, rfl⟩
  | or p q ihp ihq =>
    intro lblId want target
    dsimp only [compileC]
    cases want
    · simp only [Bool.false_eq_true, ↓reduceIte, noT6Branch_append, Bool.and_eq_true]
      exact ⟨⟨ihp (lblId + 1) true _, ihq _ false target⟩, rfl⟩
    · simp only [↓reduceIte, noT6Branch_append, Bool.and_eq_true]
      exact ⟨ihp lblId true target, ihq _ true target⟩

theorem compileEvalExprsToTemps_noT6Branch (tab : Tab) (nlocals : Nat) :
    ∀ (es : List Expr) (tmp : Nat), noT6Branch (compileEvalExprsToTemps tab nlocals tmp es) = true := by
  intro es
  induction es with
  | nil => intro _; rfl
  | cons e es ih =>
    intro tmp
    dsimp only [compileEvalExprsToTemps]
    rw [noT6Branch_append, Bool.and_eq_true]
    refine ⟨?_, ih (tmp + 1)⟩
    split
    · exact noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)
    · simp only [noT6Branch_append, Bool.and_eq_true, compileE_noT6Branch,
        noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _), and_self]

theorem unrollCopyParams_allInstrs (nparams : Nat) :
    allInstrs (unrollCopyParams nparams) = true := by
  dsimp only [unrollCopyParams]
  refine allInstrs_flatMap (fun _ _ => ?_)
  rw [allInstrs_append, Bool.and_eq_true]
  exact ⟨loadMemOff_allInstrs _ _ _ _ _, storeMemOff_allInstrs _ _ _ _ _⟩

theorem unrollZeroLocals_allInstrs (lo count : Nat) :
    allInstrs (unrollZeroLocals lo count) = true := by
  dsimp only [unrollZeroLocals]
  exact allInstrs_flatMap (fun _ _ => storeMemOff_allInstrs _ _ _ _ _)

theorem copyTempsToResults_noT6Branch (tab : Tab) (nlocals tmp count : Nat) :
    noT6Branch (copyTempsToResults tab nlocals tmp count) = true := by
  dsimp only [copyTempsToResults]
  split
  · split <;> rfl
  · refine noT6Branch_flatMap (fun i _ => ?_)
    split
    · exact noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _)
    · simp only [noT6Branch_append, Bool.and_eq_true]
      exact ⟨noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
        noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)⟩

theorem copyResultsToLocals_noT6Branch (tab : Tab) (xs : List Var) :
    noT6Branch (copyResultsToLocals tab xs) = true := by
  dsimp only [copyResultsToLocals]
  refine noT6Branch_flatMap (fun ⟨x, i⟩ _ => ?_)
  split
  · split
    · exact noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)
    · simp only [noT6Branch_append, Bool.and_eq_true]
      exact ⟨noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
        noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)⟩
  · exact noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)

theorem evalWArrTierToTemp_noT6Branch (tab : Tab) (nlocals tmp : Nat) (w : WArr) :
    noT6Branch (evalWArrTierToTemp tab nlocals tmp w).2 = true := by
  cases w with
  | plain a => exact noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)
  | tier a t =>
    simp only [evalWArrTierToTemp, noT6Branch_append, Bool.and_eq_true]
    exact ⟨compileE_noT6Branch tab nlocals t tmp,
      noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)⟩

theorem compileStorePair_noT6Branch (tab : Tab) (nlocals : Nat) (i e : Expr) :
    noT6Branch (compileStorePair tab nlocals i e) = true := by
  dsimp only [compileStorePair]
  cases hi : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 i with
  | some ci =>
    simp only [noT6Branch_append, Bool.and_eq_true, compileE_noT6Branch,
      noT6Branch_of_allInstrs (emitSimpleExpr_allInstrs hi), and_self]
  | none =>
    cases he : emitSimpleExpr tab AbiReg.a0 AbiReg.t1 e with
    | some ce =>
      simp only [noT6Branch_append, Bool.and_eq_true, compileE_noT6Branch,
        noT6Branch_of_allInstrs (emitSimpleExpr_allInstrs he), true_and, and_true]; rfl
    | none =>
      simp only [noT6Branch_append, Bool.and_eq_true, compileE_noT6Branch,
        noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
        noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), and_self]

theorem compileTierStoreTriple_noT6Branch (tab : Tab) (nlocals : Nat) (t i e : Expr) :
    noT6Branch (compileTierStoreTriple tab nlocals t i e) = true := by
  dsimp only [compileTierStoreTriple]
  cases ht : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 t with
  | some ct =>
    cases hi : emitSimpleExpr tab AbiReg.t3 AbiReg.t4 i with
    | some ci =>
      simp only [noT6Branch_append, Bool.and_eq_true, compileE_noT6Branch,
        noT6Branch_of_allInstrs (emitSimpleExpr_allInstrs ht),
        noT6Branch_of_allInstrs (emitSimpleExpr_allInstrs hi), and_self]
    | none =>
      cases he : emitSimpleExpr tab AbiReg.a0 AbiReg.t4 e with
      | some ce =>
        simp only [noT6Branch_append, Bool.and_eq_true, compileE_noT6Branch,
          noT6Branch_of_allInstrs (emitSimpleExpr_allInstrs ht),
          noT6Branch_of_allInstrs (emitSimpleExpr_allInstrs he), true_and, and_true]; rfl
      | none =>
        simp only [noT6Branch_append, Bool.and_eq_true, compileE_noT6Branch,
          noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
          noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
          noT6Branch_of_allInstrs (emitSimpleExpr_allInstrs ht), and_self]
  | none =>
    simp only [noT6Branch_append, Bool.and_eq_true, compileE_noT6Branch,
      noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
      noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), and_self]

theorem compileS_noT6Branch (tab : Tab) (nlocals : Nat) (pfx : String) (retLbl : String) :
    ∀ (s : Stmt) (lblId : Nat) (brkLbl : Option String),
      noT6Branch (compileS tab nlocals pfx lblId brkLbl retLbl s).1 = true := by
  intro s
  induction s with
  | skip => intro _ _; rfl
  | set _ e | gset _ e =>
    intro _ _
    dsimp only [compileS]
    split
    · exact noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)
    · simp only [noT6Branch_append, Bool.and_eq_true, compileE_noT6Branch,
        noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _), and_self]
  | st8 _ _ _ => intro _ _; rfl
  | st64 _ _ _ =>
    intro _ _
    simp only [compileS, noT6Branch_append, Bool.and_eq_true, compileStorePair_noT6Branch,
      noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), true_and, and_true]
    repeat' (first | apply And.intro | rfl)
  | st64t _ _ _ _ | st32t _ _ _ _ =>
    intro _ _
    simp only [compileS, noT6Branch_append, Bool.and_eq_true, compileTierStoreTriple_noT6Branch,
      noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), true_and, and_true]
    repeat' (first | apply And.intro | rfl)
  | seq s1 s2 ih1 ih2 =>
    intro lblId brkLbl
    simp only [compileS, noT6Branch_append, Bool.and_eq_true]
    exact ⟨ih1 lblId brkLbl, ih2 _ brkLbl⟩
  | ite cond s1 s2 ih1 ih2 =>
    intro lblId brkLbl
    by_cases h2 : s2 = .skip
    · subst h2
      simp only [compileS, noT6Branch_append, Bool.and_eq_true, compileC_noT6Branch, ih1, true_and, and_true]; rfl
    · by_cases h1 : s1 = .skip
      · subst h1
        have heq : (compileS tab nlocals pfx lblId brkLbl retLbl (.ite cond .skip s2)).1 =
            (compileC tab nlocals 0 pfx (lblId + 1) cond true s!"{pfx}_endif_{lblId}").1 ++
              (compileS tab nlocals pfx
                (compileC tab nlocals 0 pfx (lblId + 1) cond true s!"{pfx}_endif_{lblId}").2
                brkLbl retLbl s2).1 ++
              [Asm.lbl s!"{pfx}_endif_{lblId}"] := by
          cases s2 with | skip => contradiction | _ => rfl
        rw [heq]
        simp only [noT6Branch_append, Bool.and_eq_true, compileC_noT6Branch, ih2, true_and, and_true]; rfl
      · have heq : (compileS tab nlocals pfx lblId brkLbl retLbl (.ite cond s1 s2)).1 =
            (compileC tab nlocals 0 pfx (lblId + 1) cond false s!"{pfx}_else_{lblId}").1 ++
              (compileS tab nlocals pfx
                (compileC tab nlocals 0 pfx (lblId + 1) cond false s!"{pfx}_else_{lblId}").2
                brkLbl retLbl s1).1 ++
              [Asm.j s!"{pfx}_endif_{lblId}", Asm.lbl s!"{pfx}_else_{lblId}"] ++
              (compileS tab nlocals pfx
                (compileS tab nlocals pfx
                  (compileC tab nlocals 0 pfx (lblId + 1) cond false s!"{pfx}_else_{lblId}").2
                  brkLbl retLbl s1).2
                brkLbl retLbl s2).1 ++
              [Asm.lbl s!"{pfx}_endif_{lblId}"] := by
          cases s2 with | skip => contradiction | _ => cases s1 with | skip => contradiction | _ => rfl
        rw [heq]
        simp only [noT6Branch_append, Bool.and_eq_true, compileC_noT6Branch, ih1, ih2, true_and, and_true]
        repeat' (first | apply And.intro | rfl)
  | «while» cond body ih =>
    intro lblId _
    simp only [compileS, noT6Branch_append, Bool.and_eq_true, compileC_noT6Branch,
      ih, and_true]
    repeat' (first | apply And.intro | rfl)
  | brk => intro _ _; simp [compileS]; rfl
  | ret es =>
    intro _ _
    cases es with
    | nil =>
      simp only [compileS, noT6Branch_append, Bool.and_eq_true,
        compileEvalExprsToTemps_noT6Branch, copyTempsToResults_noT6Branch, true_and]; rfl
    | cons e rest =>
      cases rest with
      | nil =>
        simp only [compileS, noT6Branch_append, Bool.and_eq_true, compileE_noT6Branch, true_and]; rfl
      | cons e2 rs =>
        simp only [compileS, noT6Branch_append, Bool.and_eq_true,
          compileEvalExprsToTemps_noT6Branch, copyTempsToResults_noT6Branch, true_and]; rfl
  | «call» xs f args =>
    intro _ _
    have hptr : noT6Branch (if args.isEmpty then [] else addImmOff AbiReg.t0 AbiReg.sp AbiReg.t2 (slotOff nlocals)) = true := by
      split
      · rfl
      · exact noT6Branch_of_allInstrs (addImmOff_allInstrs _ _ _ _)
    simp only [compileS, noT6Branch_append, Bool.and_eq_true,
      compileEvalExprsToTemps_noT6Branch, hptr,
      copyResultsToLocals_noT6Branch, true_and, and_true]
    repeat' (first | apply And.intro | rfl)
  | abort e =>
    intro _ _
    simp only [compileS, noT6Branch_append, Bool.and_eq_true, compileE_noT6Branch, true_and]
    rfl
  | copy64 d di src si n =>
    intro lblId _
    simp only [compileS, noT6Branch_append, Bool.and_eq_true, evalWArrTierToTemp_noT6Branch,
      compileE_noT6Branch, noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
      noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), true_and, and_true]
    repeat' (first | apply And.intro | rfl)
  | copy8w d di src si n =>
    intro lblId _
    simp only [compileS, noT6Branch_append, Bool.and_eq_true, evalWArrTierToTemp_noT6Branch,
      compileE_noT6Branch, noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
      noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), true_and, and_true]
    repeat' (first | apply And.intro | rfl)
    cases src <;> simp only [noT6Branch_append, Bool.and_eq_true,
      noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
      noT6Branch_of_allInstrs (li_allInstrs _ _),
      noT6Branch_of_allInstrs (addImmOff_allInstrs _ _ _ _), and_self]
  | scan8 x src i e c =>
    intro lblId _
    simp only [compileS, noT6Branch_append, Bool.and_eq_true, compileE_noT6Branch,
      noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
      noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
      noT6Branch_of_allInstrs (addImmOff_allInstrs _ _ _ _), true_and, and_true]
    repeat' (first | apply And.intro | rfl)
    cases src <;> simp only [noT6Branch_append, Bool.and_eq_true,
      noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
      noT6Branch_of_allInstrs (li_allInstrs _ _),
      noT6Branch_of_allInstrs (addImmOff_allInstrs _ _ _ _), and_self]

private theorem noT6Branch_bgeu (r1 r2 : Reg) (h1 : r1 ≠ AbiReg.t6) (h2 : r2 ≠ AbiReg.t6) (t : String) :
    noT6Branch [Asm.bgeu r1 r2 t] = true := by
  simp [noT6Branch, asmItemNoT6Branch, Asm.bgeu, bne_iff_ne.mpr h1, bne_iff_ne.mpr h2]

private theorem emitShrMaskFrom_noT6Branch (fl : FrameLayout) (rd : Reg) (inner : Expr)
    (lsh : Nat) (lm : BitVec 6) (compInner : Unit → List AsmItem)
    (hi : noT6Branch (compInner ()) = true) :
    noT6Branch (emitShrMaskFrom fl rd inner lsh lm compInner) = true := by
  dsimp only [emitShrMaskFrom]
  cases exprReg? fl.alloc inner with
  | some ri =>
    dsimp only
    have hs1 : noT6Branch (if (lsh == 0) = true then (if (rd == ri) = true then [] else [Asm.mv rd ri])
        else [Asm.slli rd ri (BitVec.ofNat 6 lsh)]) = true := by
      split
      · split <;> rfl
      · rfl
    simp only [noT6Branch_append, noT6Branch_nil, Bool.and_eq_true, hs1, true_and]; rfl
  | none =>
    dsimp only
    have hs1 : noT6Branch (if (lsh == 0) = true then (if (rd == AbiReg.a0) = true then [] else [Asm.mv rd AbiReg.a0])
        else [Asm.slli rd AbiReg.a0 (BitVec.ofNat 6 lsh)]) = true := by
      split
      · split <;> rfl
      · rfl
    simp only [noT6Branch_append, Bool.and_eq_true, hi, hs1, true_and]; rfl

private theorem emitLd32hPlainFrom_noT6Branch (tab : Tab) (fl : FrameLayout) (hfl : AllocNoT6 fl)
    (rd : Reg) (a : ArrId) (i : Expr) (hi : Bool) (compI0 : Unit → List AsmItem)
    (hcomp : noT6Branch (compI0 ()) = true) :
    noT6Branch (emitLd32hPlainFrom tab fl rd a i hi compI0) = true := by
  dsimp only [emitLd32hPlainFrom]
  cases hri : exprReg? fl.alloc i with
  | some r =>
    dsimp only
    have hr : r ≠ AbiReg.t6 := exprReg?_ne_t6 hfl hri
    simp only [noT6Branch_append, noT6Branch_nil, Bool.and_eq_true,
      noT6Branch_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
      noT6Branch_bgeu r AbiReg.t0 hr (by decide) errLabel,
      noT6Branch_of_allInstrs (ld32hTail_allInstrs _ _ _ _ _), and_self]
  | none =>
    dsimp only
    simp only [noT6Branch_append, Bool.and_eq_true, hcomp,
      noT6Branch_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
      noT6Branch_bgeu AbiReg.a0 AbiReg.t0 (by decide) (by decide) errLabel,
      noT6Branch_of_allInstrs (ld32hTail_allInstrs _ _ _ _ _), and_self]

private theorem emitLd32hFrom_noT6Branch (tab : Tab) (fl : FrameLayout) (hfl : AllocNoT6 fl)
    (tmp : Nat) (rd : Reg) (a : ArrId) (t i : Expr) (hi : Bool)
    (compI0 compT0 compI1 : Unit → List AsmItem)
    (hi0 : noT6Branch (compI0 ()) = true) (ht0 : noT6Branch (compT0 ()) = true)
    (hi1 : noT6Branch (compI1 ()) = true) :
    noT6Branch (emitLd32hFrom tab fl tmp rd a t i hi compI0 compT0 compI1) = true := by
  dsimp only [emitLd32hFrom]
  cases t.constVal? with
  | some w =>
    dsimp only
    cases hii : exprReg? fl.alloc i with
    | some r =>
      dsimp only
      have hr : r ≠ AbiReg.t6 := exprReg?_ne_t6 hfl hii
      simp only [noT6Branch_append, noT6Branch_nil, Bool.and_eq_true,
        noT6Branch_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
        noT6Branch_bgeu r AbiReg.t2 hr (by decide) errLabel,
        noT6Branch_of_allInstrs (ld32hTail_allInstrs _ _ _ _ _), and_self]
    | none =>
      dsimp only
      simp only [noT6Branch_append, Bool.and_eq_true, hi0,
        noT6Branch_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
        noT6Branch_bgeu AbiReg.a0 AbiReg.t2 (by decide) (by decide) errLabel,
        noT6Branch_of_allInstrs (ld32hTail_allInstrs _ _ _ _ _), and_self]
  | none =>
    have htail : ∀ (head : List AsmItem) (rt ri : Reg),
        noT6Branch head = true → ri ≠ AbiReg.t6 →
        noT6Branch (head ++
          [Asm.andi AbiReg.t0 rt 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
           Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
          loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (tab.len64 (TieredArray.t0 a)) ++
          [Asm.bgeu ri AbiReg.t2 errLabel] ++
          loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t3 (tab.base64 (TieredArray.t0 a)) ++
          ld32hTail rd ri AbiReg.t3 i hi) = true := by
      intro head rt ri hh hri
      simp only [noT6Branch_append, Bool.and_eq_true, hh,
        noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
        noT6Branch_bgeu ri AbiReg.t2 hri (by decide) errLabel,
        noT6Branch_of_allInstrs (ld32hTail_allInstrs _ _ _ _ _), true_and, and_true]
      rfl
    cases exprReg? fl.alloc t with
    | some r =>
      cases hii : exprReg? fl.alloc i with
      | some ri => exact htail [] r ri rfl (exprReg?_ne_t6 hfl hii)
      | none => exact htail _ r AbiReg.a0 hi0 (by decide)
    | none =>
      cases hst : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 t with
      | some ct =>
        cases hii : exprReg? fl.alloc i with
        | some ri => exact htail ct AbiReg.t0 ri (noT6Branch_of_allInstrs (emitSimpleExprR_allInstrs hst)) (exprReg?_ne_t6 hfl hii)
        | none =>
          exact htail _ AbiReg.t0 AbiReg.a0
            (by rw [noT6Branch_append, Bool.and_eq_true]; exact ⟨hi0, noT6Branch_of_allInstrs (emitSimpleExprR_allInstrs hst)⟩)
            (by decide)
      | none =>
        exact htail _ AbiReg.t0 AbiReg.a0
          (by simp only [noT6Branch_append, Bool.and_eq_true, ht0, hi1,
            noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
            noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), and_self])
          (by decide)

private theorem compileBinFallback_noT6Branch (tab : Tab) (fl : FrameLayout)
    (tmp : Nat) (rd : Reg) (op : BinOp) (a b : Expr)
    (compA0 compB0 compB1 : Unit → List AsmItem)
    (ha0 : noT6Branch (compA0 ()) = true) (hb0 : noT6Branch (compB0 ()) = true)
    (hb1 : noT6Branch (compB1 ()) = true) :
    noT6Branch (compileBinFallback tab fl tmp rd op a b compA0 compB0 compB1) = true := by
  dsimp only [compileBinFallback]
  cases b.constVal? with
  | some w =>
    dsimp only
    cases exprReg? fl.alloc a with
    | some ra => exact noT6Branch_of_allInstrs (emitBinConstRhsTo_allInstrs rd ra op w)
    | none =>
      rw [noT6Branch_append, Bool.and_eq_true]
      exact ⟨ha0, noT6Branch_of_allInstrs (emitBinConstRhsTo_allInstrs rd AbiReg.a0 op w)⟩
  | none =>
    dsimp only
    cases a.constVal? with
    | some w =>
      dsimp only
      cases exprReg? fl.alloc b with
      | some rb =>
        cases op with
        | add | and | or | xor | mul | «mulhi» =>
          dsimp only; rw [List.nil_append]
          exact noT6Branch_of_allInstrs (emitBinConstRhsTo_allInstrs rd rb _ w)
        | sub =>
          dsimp only; split
          · rfl
          · simp only [List.nil_append, noT6Branch_append, Bool.and_eq_true,
              noT6Branch_of_allInstrs (li_allInstrs _ _), true_and]; rfl
        | shl | shr =>
          dsimp only
          simp only [List.nil_append, noT6Branch_append, Bool.and_eq_true,
            noT6Branch_of_allInstrs (li_allInstrs _ _), true_and]; rfl
      | none =>
        cases op with
        | add | and | or | xor | mul | «mulhi» =>
          dsimp only
          rw [noT6Branch_append, Bool.and_eq_true]
          exact ⟨hb0, noT6Branch_of_allInstrs (emitBinConstRhsTo_allInstrs rd AbiReg.a0 _ w)⟩
        | sub =>
          dsimp only; split
          · rw [noT6Branch_append, Bool.and_eq_true]; exact ⟨hb0, rfl⟩
          · simp only [noT6Branch_append, Bool.and_eq_true, hb0,
              noT6Branch_of_allInstrs (li_allInstrs _ _), true_and]; rfl
        | shl | shr =>
          dsimp only
          simp only [noT6Branch_append, Bool.and_eq_true, hb0,
            noT6Branch_of_allInstrs (li_allInstrs _ _), true_and]; rfl
    | none =>
      dsimp only
      cases exprReg? fl.alloc b with
      | some rb =>
        cases exprReg? fl.alloc a with
        | some ra => exact noT6Branch_of_allInstrs (emitBinOp_allInstrs op rd ra rb)
        | none =>
          rw [noT6Branch_append, Bool.and_eq_true]
          exact ⟨ha0, noT6Branch_of_allInstrs (emitBinOp_allInstrs op rd AbiReg.a0 rb)⟩
      | none =>
        cases exprReg? fl.alloc a with
        | some ra =>
          rw [noT6Branch_append, Bool.and_eq_true]
          exact ⟨hb0, noT6Branch_of_allInstrs (emitBinOp_allInstrs op rd ra AbiReg.a0)⟩
        | none =>
          cases hsb : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 b with
          | some cb =>
            simp only [noT6Branch_append, Bool.and_eq_true, ha0,
              noT6Branch_of_allInstrs (emitSimpleExprR_allInstrs hsb),
              noT6Branch_of_allInstrs (emitBinOp_allInstrs op _ _ _), and_self]
          | none =>
            cases hsa : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 a with
            | some ca =>
              simp only [noT6Branch_append, Bool.and_eq_true, hb0,
                noT6Branch_of_allInstrs (emitSimpleExprR_allInstrs hsa),
                noT6Branch_of_allInstrs (emitBinOp_allInstrs op _ _ _), and_self]
            | none =>
              dsimp only
              split
              · simp only [noT6Branch_append, Bool.and_eq_true, ha0, hb0,
                  noT6Branch_of_allInstrs (emitBinOp_allInstrs op _ _ _), true_and, and_true]; rfl
              · simp only [noT6Branch_append, Bool.and_eq_true, ha0, hb1,
                  noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
                  noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
                  noT6Branch_of_allInstrs (emitBinOp_allInstrs op _ _ _), and_self]

private theorem compileETo_noT6Branch_aux (tab : Tab) (fl : FrameLayout) (hfl : AllocNoT6 fl)
    (e : Expr) (tmp : Nat) (rd : Reg) : noT6Branch (compileETo tab fl tmp rd e) = true := by
  match e with
  | .const _ => exact noT6Branch_of_allInstrs (li_allInstrs _ _)
  | .var x =>
    dsimp only [compileETo]
    split
    · split <;> rfl
    · exact noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _)
  | .len8 _ | .len64 _ | .glob _ =>
    exact noT6Branch_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _)
  | .bin op a b =>
    unfold compileETo
    dsimp only
    split
    · split
      · split
        · exact emitShrMaskFrom_noT6Branch fl rd _ _ _ _
            (compileETo_noT6Branch_aux tab fl hfl _ tmp AbiReg.a0)
        · exact compileBinFallback_noT6Branch tab fl tmp rd _ _ _ _ _ _
            (compileETo_noT6Branch_aux tab fl hfl _ tmp AbiReg.a0)
            (compileETo_noT6Branch_aux tab fl hfl _ tmp AbiReg.a0)
            (compileETo_noT6Branch_aux tab fl hfl _ (tmp + 1) AbiReg.a0)
      · exact compileBinFallback_noT6Branch tab fl tmp rd _ _ _ _ _ _
          (compileETo_noT6Branch_aux tab fl hfl _ tmp AbiReg.a0)
          (compileETo_noT6Branch_aux tab fl hfl _ tmp AbiReg.a0)
          (compileETo_noT6Branch_aux tab fl hfl _ (tmp + 1) AbiReg.a0)
    · exact emitLd32hPlainFrom_noT6Branch tab fl hfl rd _ _ false _
        (compileETo_noT6Branch_aux tab fl hfl _ tmp AbiReg.a0)
    · exact emitLd32hPlainFrom_noT6Branch tab fl hfl rd _ _ true _
        (compileETo_noT6Branch_aux tab fl hfl _ tmp AbiReg.a0)
    · exact emitLd32hFrom_noT6Branch tab fl hfl tmp rd _ _ _ false _ _ _
        (compileETo_noT6Branch_aux tab fl hfl _ tmp AbiReg.a0)
        (compileETo_noT6Branch_aux tab fl hfl _ tmp AbiReg.a0)
        (compileETo_noT6Branch_aux tab fl hfl _ (tmp + 1) AbiReg.a0)
    · exact emitLd32hFrom_noT6Branch tab fl hfl tmp rd _ _ _ true _ _ _
        (compileETo_noT6Branch_aux tab fl hfl _ tmp AbiReg.a0)
        (compileETo_noT6Branch_aux tab fl hfl _ tmp AbiReg.a0)
        (compileETo_noT6Branch_aux tab fl hfl _ (tmp + 1) AbiReg.a0)
    · exact compileBinFallback_noT6Branch tab fl tmp rd op a b _ _ _
        (compileETo_noT6Branch_aux tab fl hfl a tmp AbiReg.a0)
        (compileETo_noT6Branch_aux tab fl hfl b tmp AbiReg.a0)
        (compileETo_noT6Branch_aux tab fl hfl b (tmp + 1) AbiReg.a0)
  | .cmpw c a b =>
    have iha := fun t r => compileETo_noT6Branch_aux tab fl hfl a t r
    have ihb := fun t r => compileETo_noT6Branch_aux tab fl hfl b t r
    dsimp only [compileETo]
    split
    · cases exprReg? fl.alloc a with
      | some _ => rfl
      | none => rw [noT6Branch_append, Bool.and_eq_true]; exact ⟨iha tmp AbiReg.a0, rfl⟩
    · split
      · cases exprReg? fl.alloc b with
        | some _ => rfl
        | none => rw [noT6Branch_append, Bool.and_eq_true]; exact ⟨ihb tmp AbiReg.a0, rfl⟩
      · split
        · cases exprReg? fl.alloc a with
          | some _ => rfl
          | none => rw [noT6Branch_append, Bool.and_eq_true]; exact ⟨iha tmp AbiReg.a0, rfl⟩
        · split
          · cases exprReg? fl.alloc b with
            | some _ => rfl
            | none => rw [noT6Branch_append, Bool.and_eq_true]; exact ⟨ihb tmp AbiReg.a0, rfl⟩
          · cases exprReg? fl.alloc b with
            | some rb =>
              cases exprReg? fl.alloc a with
              | some ra => exact noT6Branch_of_allInstrs (emitCmpwTo_allInstrs rd c ra rb)
              | none =>
                rw [noT6Branch_append, Bool.and_eq_true]
                exact ⟨iha tmp AbiReg.a0, noT6Branch_of_allInstrs (emitCmpwTo_allInstrs rd c AbiReg.a0 rb)⟩
            | none =>
              cases exprReg? fl.alloc a with
              | some ra =>
                rw [noT6Branch_append, Bool.and_eq_true]
                exact ⟨ihb tmp AbiReg.a0, noT6Branch_of_allInstrs (emitCmpwTo_allInstrs rd c ra AbiReg.a0)⟩
              | none =>
                cases hsb : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 b with
                | some cb =>
                  simp only [noT6Branch_append, Bool.and_eq_true, iha tmp AbiReg.a0,
                    noT6Branch_of_allInstrs (emitSimpleExprR_allInstrs hsb),
                    noT6Branch_of_allInstrs (emitCmpwTo_allInstrs rd c _ _), and_self]
                | none =>
                  cases hsa : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 a with
                  | some ca =>
                    simp only [noT6Branch_append, Bool.and_eq_true, ihb tmp AbiReg.a0,
                      noT6Branch_of_allInstrs (emitSimpleExprR_allInstrs hsa),
                      noT6Branch_of_allInstrs (emitCmpwTo_allInstrs rd c _ _), and_self]
                  | none =>
                    dsimp only
                    split
                    · simp only [noT6Branch_append, Bool.and_eq_true, iha tmp AbiReg.a0, ihb tmp AbiReg.a0,
                        noT6Branch_of_allInstrs (emitCmpwTo_allInstrs rd c _ _), true_and, and_true]; rfl
                    · simp only [noT6Branch_append, Bool.and_eq_true, iha tmp AbiReg.a0, ihb (tmp + 1) AbiReg.a0,
                        noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
                        noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
                        noT6Branch_of_allInstrs (emitCmpwTo_allInstrs rd c _ _), and_self]
  | .ld8 a i =>
    have ih := fun t r => compileETo_noT6Branch_aux tab fl hfl i t r
    dsimp only [compileETo]
    cases hi : exprReg? fl.alloc i with
    | some r =>
      dsimp only
      have hr : r ≠ AbiReg.t6 := exprReg?_ne_t6 hfl hi
      simp only [noT6Branch_append, noT6Branch_nil, Bool.and_eq_true,
        noT6Branch_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
        noT6Branch_bgeu r AbiReg.t0 hr (by decide) errLabel, true_and, and_true]
      cases i.constVal? with | none => rfl | some _ => dsimp only; split <;> rfl
    | none =>
      dsimp only
      simp only [noT6Branch_append, Bool.and_eq_true, ih tmp AbiReg.a0,
        noT6Branch_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
        noT6Branch_bgeu AbiReg.a0 AbiReg.t0 (by decide) (by decide) errLabel, true_and, and_true]
      cases i.constVal? with | none => rfl | some _ => dsimp only; split <;> rfl
  | .ld64 a i =>
    have ih := fun t r => compileETo_noT6Branch_aux tab fl hfl i t r
    dsimp only [compileETo]
    cases hi : exprReg? fl.alloc i with
    | some r =>
      dsimp only
      have hr : r ≠ AbiReg.t6 := exprReg?_ne_t6 hfl hi
      simp only [noT6Branch_append, noT6Branch_nil, Bool.and_eq_true,
        noT6Branch_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
        noT6Branch_bgeu r AbiReg.t0 hr (by decide) errLabel,
        noT6Branch_of_allInstrs (ld64Tail_allInstrs _ _ _ _), and_self]
    | none =>
      dsimp only
      simp only [noT6Branch_append, Bool.and_eq_true, ih tmp AbiReg.a0,
        noT6Branch_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
        noT6Branch_bgeu AbiReg.a0 AbiReg.t0 (by decide) (by decide) errLabel,
        noT6Branch_of_allInstrs (ld64Tail_allInstrs _ _ _ _), and_self]
  | .ldc d i =>
    have ih := fun t r => compileETo_noT6Branch_aux tab fl hfl i t r
    dsimp only [compileETo]
    have hbr : ∀ (ri : Reg), ri ≠ AbiReg.t6 →
        noT6Branch [Asm.bgeu ri AbiReg.t0 errLabel, Asm.add AbiReg.t1 AbiReg.gp ri] = true := by
      intro ri hri
      simp only [noT6Branch, List.all_cons, List.all_nil, asmItemNoT6Branch, Asm.bgeu, Asm.add,
        bne_iff_ne.mpr hri, Bool.true_and, Bool.and_true]
      decide
    cases hi : exprReg? fl.alloc i with
    | some r =>
      dsimp only
      have hr : r ≠ AbiReg.t6 := exprReg?_ne_t6 hfl hi
      simp only [noT6Branch_append, noT6Branch_nil, Bool.and_eq_true,
        noT6Branch_of_allInstrs (li_allInstrs _ _),
        noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
        hbr r hr, and_self]
    | none =>
      dsimp only
      simp only [noT6Branch_append, Bool.and_eq_true, ih tmp AbiReg.a0,
        noT6Branch_of_allInstrs (li_allInstrs _ _),
        noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
        hbr AbiReg.a0 (by decide), and_self]
  | .ld64t a t i =>
    have iht := fun k r => compileETo_noT6Branch_aux tab fl hfl t k r
    have ihi := fun k r => compileETo_noT6Branch_aux tab fl hfl i k r
    dsimp only [compileETo]
    cases t.constVal? with
    | some w =>
      dsimp only
      cases hi : exprReg? fl.alloc i with
      | some r =>
        dsimp only
        have hr : r ≠ AbiReg.t6 := exprReg?_ne_t6 hfl hi
        simp only [noT6Branch_append, noT6Branch_nil, Bool.and_eq_true,
          noT6Branch_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
          noT6Branch_bgeu r AbiReg.t2 hr (by decide) errLabel,
          noT6Branch_of_allInstrs (ld64Tail_allInstrs _ _ _ _), and_self]
      | none =>
        dsimp only
        simp only [noT6Branch_append, Bool.and_eq_true, ihi tmp AbiReg.a0,
          noT6Branch_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
          noT6Branch_bgeu AbiReg.a0 AbiReg.t2 (by decide) (by decide) errLabel,
          noT6Branch_of_allInstrs (ld64Tail_allInstrs _ _ _ _), and_self]
    | none =>
      have htail : ∀ (head : List AsmItem) (rt ri : Reg),
          noT6Branch head = true → ri ≠ AbiReg.t6 →
          noT6Branch (head ++
            [Asm.andi AbiReg.t0 rt 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
             Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
            loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (tab.len64 (TieredArray.t0 a)) ++
            [Asm.bgeu ri AbiReg.t2 errLabel] ++
            loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t3 (tab.base64 (TieredArray.t0 a)) ++
            ld64Tail rd ri AbiReg.t3 i) = true := by
        intro head rt ri hh hri
        simp only [noT6Branch_append, Bool.and_eq_true, hh,
          noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
          noT6Branch_bgeu ri AbiReg.t2 hri (by decide) errLabel,
          noT6Branch_of_allInstrs (ld64Tail_allInstrs _ _ _ _), true_and, and_true]
        rfl
      cases ht : exprReg? fl.alloc t with
      | some r =>
        cases hi : exprReg? fl.alloc i with
        | some ri => exact htail [] r ri rfl (exprReg?_ne_t6 hfl hi)
        | none => exact htail _ r AbiReg.a0 (ihi tmp AbiReg.a0) (by decide)
      | none =>
        cases hst : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 t with
        | some ct =>
          cases hi : exprReg? fl.alloc i with
          | some ri => exact htail ct AbiReg.t0 ri (noT6Branch_of_allInstrs (emitSimpleExprR_allInstrs hst)) (exprReg?_ne_t6 hfl hi)
          | none =>
            exact htail _ AbiReg.t0 AbiReg.a0
              (by rw [noT6Branch_append, Bool.and_eq_true]; exact ⟨ihi tmp AbiReg.a0, noT6Branch_of_allInstrs (emitSimpleExprR_allInstrs hst)⟩)
              (by decide)
        | none =>
          exact htail _ AbiReg.t0 AbiReg.a0
            (by simp only [noT6Branch_append, Bool.and_eq_true, iht tmp AbiReg.a0, ihi (tmp + 1) AbiReg.a0,
              noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
              noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), and_self])
            (by decide)
  | .len64t a t =>
    have ih := fun k r => compileETo_noT6Branch_aux tab fl hfl t k r
    dsimp only [compileETo]
    cases t.constVal? with
    | some _ => exact noT6Branch_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _)
    | none =>
      cases exprReg? fl.alloc t with
      | some _ =>
        simp only [noT6Branch_append, noT6Branch_nil, Bool.and_eq_true,
          noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), true_and, and_true]; rfl
      | none =>
        simp only [noT6Branch_append, Bool.and_eq_true, ih tmp AbiReg.a0,
          noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), true_and, and_true]; rfl
  | .ld8x8 src i =>
    have ih := fun k r => compileETo_noT6Branch_aux tab fl hfl i k r
    have hread : allInstrs ([Asm.lbu rd AbiReg.t1 7#12] ++
        List.flatMap (fun k =>
          [Asm.lbu AbiReg.t2 AbiReg.t1 (BitVec.ofInt 12 k), Asm.slli rd rd 8#6,
           Asm.or rd rd AbiReg.t2]) [6, 5, 4, 3, 2, 1, 0]) = true := by
      rw [allInstrs_append, Bool.and_eq_true]
      exact ⟨rfl, allInstrs_flatMap (fun _ _ => rfl)⟩
    dsimp only [compileETo]
    cases hi : exprReg? fl.alloc i with
    | some r =>
      have hr : (r != AbiReg.t6) = true := bne_iff_ne.mpr (exprReg?_ne_t6 hfl hi)
      cases src <;> (
        simp only [List.nil_append, noT6Branch_append, Bool.and_eq_true,
          noT6Branch_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
          noT6Branch_of_allInstrs (li_allInstrs _ _),
          noT6Branch_of_allInstrs (addImmOff_allInstrs _ _ _ _),
          noT6Branch_of_allInstrs hread, true_and, and_true]
        simp only [noT6Branch, List.all_cons, List.all_nil, asmItemNoT6Branch,
          Asm.addi, Asm.bltu, Asm.add, hr, Bool.and_true, Bool.true_and]
        decide)
    | none =>
      cases src <;>
        simp only [noT6Branch_append, Bool.and_eq_true, ih tmp AbiReg.a0,
          noT6Branch_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
          noT6Branch_of_allInstrs (li_allInstrs _ _),
          noT6Branch_of_allInstrs (addImmOff_allInstrs _ _ _ _),
          noT6Branch_of_allInstrs hread, true_and, and_true] <;>
        decide
  | .ld32t a t i =>
    have iht := fun k r => compileETo_noT6Branch_aux tab fl hfl t k r
    have ihi := fun k r => compileETo_noT6Branch_aux tab fl hfl i k r
    dsimp only [compileETo]
    cases t.constVal? with
    | some w =>
      dsimp only
      cases exprReg? fl.alloc i with
      | some r =>
        dsimp only
        simp only [noT6Branch_append, noT6Branch_nil, Bool.and_eq_true,
          noT6Branch_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
          noT6Branch_of_allInstrs (ld32tTail_allInstrs _ _ _), true_and, and_true]
        rfl
      | none =>
        dsimp only
        simp only [noT6Branch_append, Bool.and_eq_true, ihi tmp AbiReg.a0,
          noT6Branch_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
          noT6Branch_of_allInstrs (ld32tTail_allInstrs _ _ _), true_and, and_true]
        rfl
    | none =>
      have htail : ∀ (head : List AsmItem) (rt ri : Reg),
          noT6Branch head = true →
          noT6Branch (head ++
            [Asm.andi AbiReg.t0 rt 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
             Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
            loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (tab.len64 (TieredArray.t0 a)) ++
            [Asm.srli AbiReg.t3 ri 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
            loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t3 (tab.base64 (TieredArray.t0 a)) ++
            ld32tTail rd ri i) = true := by
        intro head rt ri hh
        simp only [noT6Branch_append, Bool.and_eq_true, hh,
          noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
          noT6Branch_of_allInstrs (ld32tTail_allInstrs _ _ _), true_and, and_true]
        exact ⟨rfl, rfl⟩
      cases exprReg? fl.alloc t with
      | some r =>
        cases exprReg? fl.alloc i with
        | some ri => exact htail [] r ri rfl
        | none => exact htail _ r AbiReg.a0 (ihi tmp AbiReg.a0)
      | none =>
        cases hst : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 t with
        | some ct =>
          cases exprReg? fl.alloc i with
          | some ri => exact htail ct AbiReg.t0 ri (noT6Branch_of_allInstrs (emitSimpleExprR_allInstrs hst))
          | none =>
            exact htail _ AbiReg.t0 AbiReg.a0
              (by rw [noT6Branch_append, Bool.and_eq_true]; exact ⟨ihi tmp AbiReg.a0, noT6Branch_of_allInstrs (emitSimpleExprR_allInstrs hst)⟩)
        | none =>
          exact htail _ AbiReg.t0 AbiReg.a0
            (by simp only [noT6Branch_append, Bool.and_eq_true, iht tmp AbiReg.a0, ihi (tmp + 1) AbiReg.a0,
              noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
              noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), and_self])
  | .ld32h a t i hi =>
    exact emitLd32hFrom_noT6Branch tab fl hfl tmp rd a t i hi _ _ _
      (compileETo_noT6Branch_aux tab fl hfl i tmp AbiReg.a0)
      (compileETo_noT6Branch_aux tab fl hfl t tmp AbiReg.a0)
      (compileETo_noT6Branch_aux tab fl hfl i (tmp + 1) AbiReg.a0)
termination_by sizeOf e

theorem compileETo_noT6Branch (tab : Tab) (fl : FrameLayout) (hfl : AllocNoT6 fl) :
    ∀ (e : Expr) (tmp : Nat) (rd : Reg), noT6Branch (compileETo tab fl tmp rd e) = true :=
  compileETo_noT6Branch_aux tab fl hfl

theorem compileCR_noT6Branch (tab : Tab) (fl : FrameLayout) (hfl : AllocNoT6 fl) (tmp : Nat)
    (pfx : String) :
    ∀ (c : Cond) (lblId : Nat) (want : Bool) (target : String),
      noT6Branch (compileCR tab fl tmp pfx lblId c want target).1 = true := by
  intro c
  induction c with
  | cmp op a b =>
    intro lblId want target
    dsimp only [compileCR]
    cases ha : exprReg? fl.alloc a with
    | some ra =>
      cases hb : exprReg? fl.alloc b with
      | some rb =>
        exact brCmp_noT6Branch op want ra rb (exprReg?_ne_t6 hfl ha) (exprReg?_ne_t6 hfl hb) target
      | none =>
        rw [noT6Branch_append, Bool.and_eq_true]
        exact ⟨compileETo_noT6Branch tab fl hfl b tmp AbiReg.a0,
          brCmp_noT6Branch op want ra AbiReg.a0 (exprReg?_ne_t6 hfl ha) (by decide) target⟩
    | none =>
      cases hb : exprReg? fl.alloc b with
      | some rb =>
        rw [noT6Branch_append, Bool.and_eq_true]
        exact ⟨compileETo_noT6Branch tab fl hfl a tmp AbiReg.a0,
          brCmp_noT6Branch op want AbiReg.a0 rb (by decide) (exprReg?_ne_t6 hfl hb) target⟩
      | none =>
        cases hsb : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 b with
        | some cb =>
          simp only [noT6Branch_append, Bool.and_eq_true, compileETo_noT6Branch tab fl hfl,
            noT6Branch_of_allInstrs (emitSimpleExprR_allInstrs hsb),
            brCmp_noT6Branch op want AbiReg.a0 AbiReg.t0 (by decide) (by decide) target, and_self]
        | none =>
          cases hsa : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 a with
          | some ca =>
            simp only [noT6Branch_append, Bool.and_eq_true, compileETo_noT6Branch tab fl hfl,
              noT6Branch_of_allInstrs (emitSimpleExprR_allInstrs hsa),
              brCmp_noT6Branch op want AbiReg.t0 AbiReg.a0 (by decide) (by decide) target, and_self]
          | none =>
            dsimp only
            split
            · simp only [noT6Branch_append, Bool.and_eq_true, compileETo_noT6Branch tab fl hfl,
                brCmp_noT6Branch op want AbiReg.t4 AbiReg.a0 (by decide) (by decide) target,
                true_and, and_true]; rfl
            · simp only [noT6Branch_append, Bool.and_eq_true, compileETo_noT6Branch tab fl hfl,
                noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
                noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
                brCmp_noT6Branch op want AbiReg.t0 AbiReg.a0 (by decide) (by decide) target, and_self]
  | not p ih =>
    intro lblId want target
    simpa [compileCR] using ih lblId (!want) target
  | and p q ihp ihq =>
    intro lblId want target
    dsimp only [compileCR]
    cases want
    · simp only [Bool.false_eq_true, ↓reduceIte, noT6Branch_append, Bool.and_eq_true]
      exact ⟨ihp lblId false target, ihq _ false target⟩
    · simp only [↓reduceIte, noT6Branch_append, Bool.and_eq_true]
      exact ⟨⟨ihp (lblId + 1) false _, ihq _ true target⟩, rfl⟩
  | or p q ihp ihq =>
    intro lblId want target
    dsimp only [compileCR]
    cases want
    · simp only [Bool.false_eq_true, ↓reduceIte, noT6Branch_append, Bool.and_eq_true]
      exact ⟨⟨ihp (lblId + 1) true _, ihq _ false target⟩, rfl⟩
    · simp only [↓reduceIte, noT6Branch_append, Bool.and_eq_true]
      exact ⟨ihp lblId true target, ihq _ true target⟩

theorem compileEvalExprsToTempsR_noT6Branch (tab : Tab) (fl : FrameLayout) (hfl : AllocNoT6 fl) :
    ∀ (es : List Expr) (tmp : Nat), noT6Branch (compileEvalExprsToTempsR tab fl tmp es) = true := by
  intro es
  induction es with
  | nil => intro _; rfl
  | cons e es ih =>
    intro tmp
    dsimp only [compileEvalExprsToTempsR]
    rw [noT6Branch_append, Bool.and_eq_true]
    refine ⟨?_, ih (tmp + 1)⟩
    cases exprReg? fl.alloc e with
    | some _ => exact noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)
    | none =>
      simp only [noT6Branch_append, Bool.and_eq_true, compileETo_noT6Branch tab fl hfl,
        noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _), and_self]

theorem evalWArrTierToTempR_noT6Branch (tab : Tab) (fl : FrameLayout) (hfl : AllocNoT6 fl)
    (tmp : Nat) (w : WArr) :
    noT6Branch (evalWArrTierToTempR tab fl tmp w).2 = true := by
  cases w with
  | plain _ => exact noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)
  | tier _ t =>
    dsimp only [evalWArrTierToTempR]
    cases exprReg? fl.alloc t with
    | some _ => exact noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)
    | none =>
      rw [noT6Branch_append, Bool.and_eq_true]
      exact ⟨compileETo_noT6Branch tab fl hfl t tmp AbiReg.a0,
        noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)⟩

theorem compileStorePairR_noT6Branch (tab : Tab) (fl : FrameLayout) (hfl : AllocNoT6 fl) (i e : Expr) :
    noT6Branch (compileStorePairR tab fl i e).1 = true ∧
      (compileStorePairR tab fl i e).2.1 ≠ AbiReg.t6 := by
  dsimp only [compileStorePairR]
  cases hi : exprReg? fl.alloc i with
  | some ri =>
    cases exprReg? fl.alloc e with
    | some _ => dsimp only; exact ⟨rfl, exprReg?_ne_t6 hfl hi⟩
    | none => dsimp only; exact ⟨compileETo_noT6Branch tab fl hfl e 0 AbiReg.a0, exprReg?_ne_t6 hfl hi⟩
  | none =>
    cases exprReg? fl.alloc e with
    | some _ => dsimp only; exact ⟨compileETo_noT6Branch tab fl hfl i 0 AbiReg.a0, by decide⟩
    | none =>
      cases hsi : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 i with
      | some ci =>
        dsimp only
        exact ⟨by
          simp only [noT6Branch_append, Bool.and_eq_true, compileETo_noT6Branch tab fl hfl,
            noT6Branch_of_allInstrs (emitSimpleExprR_allInstrs hsi), and_self], by decide⟩
      | none =>
        cases hse : emitSimpleExprR tab fl AbiReg.a0 AbiReg.t1 e with
        | some ce =>
          dsimp only
          exact ⟨by
            simp only [noT6Branch_append, Bool.and_eq_true, compileETo_noT6Branch tab fl hfl,
              noT6Branch_of_allInstrs (emitSimpleExprR_allInstrs hse), true_and, and_true]; rfl, by decide⟩
        | none =>
          dsimp only
          exact ⟨by
            simp only [noT6Branch_append, Bool.and_eq_true, compileETo_noT6Branch tab fl hfl,
              noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
              noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), and_self], by decide⟩

theorem compileTierStoreTripleR_noT6Branch (tab : Tab) (fl : FrameLayout) (hfl : AllocNoT6 fl)
    (t i e : Expr) :
    noT6Branch (compileTierStoreTripleR tab fl t i e).1 = true ∧
      (compileTierStoreTripleR tab fl t i e).2.2.1 ≠ AbiReg.t6 := by
  dsimp only [compileTierStoreTripleR]
  cases exprReg? fl.alloc t with
  | some rt =>
    cases hi : exprReg? fl.alloc i with
    | some ri =>
      cases exprReg? fl.alloc e with
      | some _ => dsimp only; exact ⟨rfl, exprReg?_ne_t6 hfl hi⟩
      | none => dsimp only; exact ⟨compileETo_noT6Branch tab fl hfl e 0 AbiReg.a0, exprReg?_ne_t6 hfl hi⟩
    | none =>
      cases exprReg? fl.alloc e with
      | some _ => dsimp only; exact ⟨compileETo_noT6Branch tab fl hfl i 0 AbiReg.a0, by decide⟩
      | none =>
        cases hsi : emitSimpleExprR tab fl AbiReg.t3 AbiReg.t4 i with
        | some ci =>
          dsimp only
          exact ⟨by
            simp only [noT6Branch_append, Bool.and_eq_true, compileETo_noT6Branch tab fl hfl,
              noT6Branch_of_allInstrs (emitSimpleExprR_allInstrs hsi), and_self], by decide⟩
        | none =>
          cases hse : emitSimpleExprR tab fl AbiReg.a0 AbiReg.t4 e with
          | some ce =>
            dsimp only
            exact ⟨by
              simp only [noT6Branch_append, Bool.and_eq_true, compileETo_noT6Branch tab fl hfl,
                noT6Branch_of_allInstrs (emitSimpleExprR_allInstrs hse), true_and, and_true]; rfl, by decide⟩
          | none =>
            dsimp only
            exact ⟨by
              simp only [noT6Branch_append, Bool.and_eq_true, compileETo_noT6Branch tab fl hfl,
                noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
                noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), and_self], by decide⟩
  | none =>
    cases hst : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 t with
    | some ct =>
      cases hsi : emitSimpleExprR tab fl AbiReg.t3 AbiReg.t4 i with
      | some ci =>
        dsimp only
        exact ⟨by
          simp only [noT6Branch_append, Bool.and_eq_true, compileETo_noT6Branch tab fl hfl,
            noT6Branch_of_allInstrs (emitSimpleExprR_allInstrs hst),
            noT6Branch_of_allInstrs (emitSimpleExprR_allInstrs hsi), and_self], by decide⟩
      | none =>
        cases hse : emitSimpleExprR tab fl AbiReg.a0 AbiReg.t4 e with
        | some ce =>
          dsimp only
          exact ⟨by
            simp only [noT6Branch_append, Bool.and_eq_true, compileETo_noT6Branch tab fl hfl,
              noT6Branch_of_allInstrs (emitSimpleExprR_allInstrs hst),
              noT6Branch_of_allInstrs (emitSimpleExprR_allInstrs hse), true_and, and_true]; rfl, by decide⟩
        | none =>
          dsimp only
          exact ⟨by
            simp only [noT6Branch_append, Bool.and_eq_true, compileETo_noT6Branch tab fl hfl,
              noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
              noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
              noT6Branch_of_allInstrs (emitSimpleExprR_allInstrs hst), and_self], by decide⟩
    | none =>
      dsimp only
      exact ⟨by
        simp only [noT6Branch_append, Bool.and_eq_true, compileETo_noT6Branch tab fl hfl,
          noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
          noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), and_self], by decide⟩

theorem compileEvalRevToRegs_noT6Branch (tab : Tab) (fl : FrameLayout) (hfl : AllocNoT6 fl) :
    ∀ (es : List Expr) (idx : Nat), noT6Branch (compileEvalRevToRegs tab fl idx es) = true := by
  intro es
  induction es with
  | nil => intro _; rfl
  | cons e rest ih =>
    intro idx
    dsimp only [compileEvalRevToRegs]
    rw [noT6Branch_append, Bool.and_eq_true]
    exact ⟨ih (idx + 1), compileETo_noT6Branch tab fl hfl e 0 (resReg idx)⟩

theorem compileRetR_noT6Branch (tab : Tab) (fl : FrameLayout) (hfl : AllocNoT6 fl)
    (retLbl : String) (isTail : Bool) (es : List Expr) :
    noT6Branch (compileRetR tab fl retLbl isTail es) = true := by
  have hj : noT6Branch (if isTail = true then []
      else if fl.isLeaf = true ∧ (fl.frameSlots == 0) = true then [Asm.ret]
      else [Asm.j retLbl]) = true := by
    split
    · rfl
    · split <;> rfl
  cases es with
  | nil =>
    simp only [compileRetR, noT6Branch_append, Bool.and_eq_true,
      noT6Branch_of_allInstrs (copyTempsToResultsR_allInstrs _ _ _ _), hj, and_self]
  | cons e rest =>
    cases rest with
    | nil =>
      simp only [compileRetR, noT6Branch_append, Bool.and_eq_true,
        compileETo_noT6Branch tab fl hfl, hj, and_self]
    | cons e2 rs =>
      dsimp only [compileRetR]
      split
      · simp only [noT6Branch_append, Bool.and_eq_true,
          compileEvalRevToRegs_noT6Branch tab fl hfl, hj, and_self]
      · simp only [noT6Branch_append, Bool.and_eq_true,
          compileEvalExprsToTempsR_noT6Branch tab fl hfl,
          noT6Branch_of_allInstrs (copyTempsToResultsR_allInstrs _ _ _ _), hj, and_self]

theorem compileCallArgsR_noT6Branch (tab : Tab) (fl : FrameLayout) (hfl : AllocNoT6 fl)
    (args : List Expr) :
    noT6Branch (compileCallArgsR tab fl args) = true := by
  have hbud : noT6Branch [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
      Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] = true := by decide
  dsimp only [compileCallArgsR]
  split
  · simp only [noT6Branch_append, Bool.and_eq_true,
      compileEvalRevToRegs_noT6Branch tab fl hfl, hbud, and_self]
  · have hlds : noT6Branch ((List.range (min args.length maxRes)).flatMap fun i =>
        loadMemOff .ld (resReg i) AbiReg.sp AbiReg.t0 (fl.tempSlotOff i)) = true :=
      noT6Branch_flatMap (fun _ _ => noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _))
    have hptr : noT6Branch (if maxRes < args.length then
        addImmOff AbiReg.t0 AbiReg.sp AbiReg.t2 (fl.tempSlotOff maxRes) else []) = true := by
      split
      · exact noT6Branch_of_allInstrs (addImmOff_allInstrs _ _ _ _)
      · rfl
    simp only [noT6Branch_append, Bool.and_eq_true,
      compileEvalExprsToTempsR_noT6Branch tab fl hfl, hbud, hlds, hptr, and_self]

theorem compileSR_noT6Branch (tab : Tab) (fl : FrameLayout) (hfl : AllocNoT6 fl)
    (pfx retLbl : String) :
    ∀ (s : Stmt) (lblId : Nat) (brkLbl : Option String) (isTail : Bool),
      noT6Branch (compileSR tab fl pfx lblId brkLbl retLbl isTail s).1 = true := by
  intro s
  induction s with
  | skip => intro _ _ _; rfl
  | set x e =>
    intro _ _ _
    dsimp only [compileSR]
    split
    · exact compileETo_noT6Branch tab fl hfl e 0 _
    · split
      · split
        · rfl
        · exact compileETo_noT6Branch tab fl hfl e 0 AbiReg.a0
      · cases exprReg? fl.alloc e with
        | some _ => exact noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)
        | none =>
          simp only [noT6Branch_append, Bool.and_eq_true, compileETo_noT6Branch tab fl hfl,
            noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _), and_self]
  | gset _ e =>
    intro _ _ _
    dsimp only [compileSR]
    cases exprReg? fl.alloc e with
    | some _ => exact noT6Branch_of_allInstrs (storeMemOffGp_allInstrs _ _ _ _ _)
    | none =>
      simp only [noT6Branch_append, Bool.and_eq_true, compileETo_noT6Branch tab fl hfl,
        noT6Branch_of_allInstrs (storeMemOffGp_allInstrs _ _ _ _ _), and_self]
  | st8 _ _ _ => intro _ _ _; rfl
  | st64 _ i e =>
    intro _ _ _
    obtain ⟨hcp, hri⟩ := compileStorePairR_noT6Branch tab fl hfl i e
    rcases hpair : compileStorePairR tab fl i e with ⟨cp, ri, re⟩
    rw [hpair] at hcp hri
    dsimp only [compileSR]
    rw [hpair]
    simp only [noT6Branch_append, Bool.and_eq_true, hcp,
      noT6Branch_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
      noT6Branch_bgeu ri AbiReg.t1 hri (by decide) errLabel,
      noT6Branch_of_allInstrs (st64Tail_allInstrs _ _ _ _), and_self]
  | st64t _ t i e =>
    intro _ _ _
    dsimp only [compileSR]
    cases t.constVal? with
    | some wt =>
      dsimp only
      obtain ⟨hcp, hri⟩ := compileStorePairR_noT6Branch tab fl hfl i e
      rcases hpair : compileStorePairR tab fl i e with ⟨cp, ri, re⟩
      rw [hpair] at hcp hri
      dsimp only
      simp only [noT6Branch_append, Bool.and_eq_true, hcp,
        noT6Branch_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
        noT6Branch_bgeu ri AbiReg.t1 hri (by decide) errLabel,
        noT6Branch_of_allInstrs (st64Tail_allInstrs _ _ _ _), and_self]
    | none =>
      dsimp only
      obtain ⟨hcp, hri⟩ := compileTierStoreTripleR_noT6Branch tab fl hfl t i e
      rcases htr : compileTierStoreTripleR tab fl t i e with ⟨cp, rt, ri, re⟩
      rw [htr] at hcp hri
      dsimp only
      simp only [noT6Branch_append, Bool.and_eq_true, hcp,
        noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
        noT6Branch_bgeu ri AbiReg.t2 hri (by decide) errLabel,
        noT6Branch_of_allInstrs (st64Tail_allInstrs _ _ _ _), true_and, and_true]
      rfl
  | st32t _ t i e =>
    intro _ _ _
    dsimp only [compileSR]
    cases t.constVal? with
    | some wt =>
      dsimp only
      obtain ⟨hcp, _⟩ := compileStorePairR_noT6Branch tab fl hfl i e
      rcases hpair : compileStorePairR tab fl i e with ⟨cp, ri, re⟩
      rw [hpair] at hcp
      dsimp only
      simp only [noT6Branch_append, Bool.and_eq_true, hcp,
        noT6Branch_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
        noT6Branch_of_allInstrs (st32tTail_allInstrs _ _ _ _), true_and, and_true]
      rfl
    | none =>
      dsimp only
      obtain ⟨hcp, _⟩ := compileTierStoreTripleR_noT6Branch tab fl hfl t i e
      rcases htr : compileTierStoreTripleR tab fl t i e with ⟨cp, rt, ri, re⟩
      rw [htr] at hcp
      dsimp only
      simp only [noT6Branch_append, Bool.and_eq_true, hcp,
        noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
        noT6Branch_of_allInstrs (st32tTail_allInstrs _ _ _ _), true_and, and_true]
      exact ⟨rfl, rfl⟩
  | seq s1 s2 ih1 ih2 =>
    intro lblId brkLbl isTail
    dsimp only [compileSR]
    cases tailCallRetMatch tab s1 s2 with
    | some v =>
      rcases v with ⟨xs, f, args, es⟩
      simp only [noT6Branch_append, Bool.and_eq_true,
        compileCallArgsR_noT6Branch tab fl hfl,
        noT6Branch_of_allInstrs (framePopItems_allInstrs fl), true_and]; rfl
    | none =>
      simp only [noT6Branch_append, Bool.and_eq_true]
      exact ⟨ih1 lblId brkLbl false, ih2 _ brkLbl isTail⟩
  | ite cond s1 s2 ih1 ih2 =>
    intro lblId brkLbl isTail
    by_cases h2 : s2 = .skip
    · subst h2
      dsimp only [compileSR]
      split
      · exact compileCR_noT6Branch tab fl hfl 0 pfx cond lblId true _
      · simp only [noT6Branch_append, Bool.and_eq_true, compileCR_noT6Branch tab fl hfl,
          ih1, true_and, and_true]; rfl
    · by_cases h1 : s1 = .skip
      · subst h1
        have heq : compileSR tab fl pfx lblId brkLbl retLbl isTail (.ite cond .skip s2) =
            if isAbort0Stmt s2 then
              compileCR tab fl 0 pfx lblId cond false s!"{pfx}_abort0stub"
            else
              let endLbl := s!"{pfx}_endif_{lblId}"
              let (cc, id1) := compileCR tab fl 0 pfx (lblId + 1) cond true endLbl
              let (c2, id2) := compileSR tab fl pfx id1 brkLbl retLbl false s2
              (cc ++ c2 ++ [Asm.lbl endLbl], id2) := by
          cases s2 with | skip => contradiction | _ => rfl
        rw [heq]
        split
        · exact compileCR_noT6Branch tab fl hfl 0 pfx cond lblId false _
        · dsimp only
          simp only [noT6Branch_append, Bool.and_eq_true, compileCR_noT6Branch tab fl hfl, ih2,
            true_and, and_true]; rfl
      · have heq : (compileSR tab fl pfx lblId brkLbl retLbl isTail (.ite cond s1 s2)).1 =
            (compileCR tab fl 0 pfx (lblId + 1) cond false s!"{pfx}_else_{lblId}").1 ++
              (compileSR tab fl pfx
                (compileCR tab fl 0 pfx (lblId + 1) cond false s!"{pfx}_else_{lblId}").2
                brkLbl retLbl false s1).1 ++
              (if stmtMayFallthrough s1 then [Asm.j s!"{pfx}_endif_{lblId}"] else []) ++
              [Asm.lbl s!"{pfx}_else_{lblId}"] ++
              (compileSR tab fl pfx
                (compileSR tab fl pfx
                  (compileCR tab fl 0 pfx (lblId + 1) cond false s!"{pfx}_else_{lblId}").2
                  brkLbl retLbl false s1).2
                brkLbl retLbl isTail s2).1 ++
              [Asm.lbl s!"{pfx}_endif_{lblId}"] := by
          cases s2 with | skip => contradiction | _ => cases s1 with | skip => contradiction | _ => rfl
        rw [heq]
        have hj : noT6Branch (if stmtMayFallthrough s1 = true then [Asm.j s!"{pfx}_endif_{lblId}"] else []) = true := by
          split <;> rfl
        simp only [noT6Branch_append, Bool.and_eq_true, compileCR_noT6Branch tab fl hfl,
          ih1, ih2, hj, true_and, and_true]
        exact ⟨rfl, rfl⟩
  | «while» cond body ih =>
    intro lblId _ _
    simp only [compileSR, noT6Branch_append, Bool.and_eq_true, compileCR_noT6Branch tab fl hfl,
      ih, and_true]
    repeat' (first | apply And.intro | rfl)
  | brk => intro _ _ _; simp [compileSR]; rfl
  | ret es =>
    intro _ _ isTail
    exact compileRetR_noT6Branch tab fl hfl retLbl isTail es
  | «call» xs f args =>
    intro _ _ _
    have ht5 : noT6Branch (if fl.useT5Gp = true then [Asm.addi AbiReg.t5 AbiReg.gp 2047#12] else []) = true := by
      split <;> rfl
    simp only [compileSR, noT6Branch_append, Bool.and_eq_true,
      compileCallArgsR_noT6Branch tab fl hfl, ht5,
      noT6Branch_of_allInstrs (copyResultsToLocalsR_allInstrs _ _ _), true_and, and_true]
    rfl
  | abort e =>
    intro _ _ _
    dsimp only [compileSR]
    split
    · rfl
    · simp only [noT6Branch_append, Bool.and_eq_true, compileETo_noT6Branch tab fl hfl, true_and]; rfl
  | copy64 d di src si n =>
    intro lblId _ _
    simp only [compileSR, noT6Branch_append, Bool.and_eq_true,
      evalWArrTierToTempR_noT6Branch tab fl hfl, compileETo_noT6Branch tab fl hfl,
      noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
      noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), true_and, and_true]
    repeat' (first | apply And.intro | rfl)
  | copy8w d di src si n =>
    intro lblId _ _
    simp only [compileSR, noT6Branch_append, Bool.and_eq_true,
      evalWArrTierToTempR_noT6Branch tab fl hfl, compileETo_noT6Branch tab fl hfl,
      noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
      noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), true_and, and_true]
    repeat' (first | apply And.intro | rfl)
    cases src <;> simp only [noT6Branch_append, Bool.and_eq_true,
      noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
      noT6Branch_of_allInstrs (li_allInstrs _ _),
      noT6Branch_of_allInstrs (addImmOff_allInstrs _ _ _ _), and_self]
  | scan8 x src i e c =>
    intro lblId _ _
    dsimp only [compileSR]
    simp only [noT6Branch_append, Bool.and_eq_true,
      noT6Branch_of_allInstrs (addImmOff_allInstrs _ _ _ _), and_true]
    refine ⟨⟨⟨⟨?_, ?_⟩, rfl⟩, rfl⟩, ?_⟩
    · cases he : emitSimpleExprR tab fl AbiReg.a0 AbiReg.t5 e with
      | some ce =>
        dsimp only
        cases exprReg? fl.alloc i with
        | some _ =>
          dsimp only; rw [noT6Branch_append, Bool.and_eq_true]
          exact ⟨rfl, noT6Branch_of_allInstrs (emitSimpleExprR_allInstrs he)⟩
        | none =>
          dsimp only
          simp only [noT6Branch_append, Bool.and_eq_true, compileETo_noT6Branch tab fl hfl,
            noT6Branch_of_allInstrs (emitSimpleExprR_allInstrs he), true_and, and_true]; rfl
      | none =>
        dsimp only
        simp only [noT6Branch_append, Bool.and_eq_true, compileETo_noT6Branch tab fl hfl,
          noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
          noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), and_self]
    · cases src <;> simp only [noT6Branch_append, Bool.and_eq_true,
        noT6Branch_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
        noT6Branch_of_allInstrs (li_allInstrs _ _),
        noT6Branch_of_allInstrs (addImmOff_allInstrs _ _ _ _), and_self]
    · cases fl.alloc.lookup x with
      | some _ => rfl
      | none =>
        dsimp only
        split
        · rfl
        · exact noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)

private theorem noT6Branch_map_retarget (old1 new1 old2 : String) (new2? : Option String)
    (xs : List AsmItem) :
    noT6Branch (xs.map (retargetBranchItem old1 new1 old2 new2?)) = noT6Branch xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    rw [List.map_cons, noT6Branch_cons, noT6Branch_cons, ih]
    congr 1
    cases x <;> rfl

theorem compileFn_noT6Branch (tab : Tab) (f : FnName) (fd : FunDecl) :
    noT6Branch (compileFn tab f fd) = true := by
  let fl := fnFrameLayoutFor tab fd
  have hfl : AllocNoT6 fl := fnFrameLayoutFor_allocNoT6 tab fd
  let pfx := fnLabel f
  let epilogue := s!"{pfx}_epilogue"
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
  let bodyCode := (compileSR tab fl pfx 0 none epilogue (!stmtMayFallthrough fd.body) fd.body).1
  let hasErr := hasBranchTo errLabel prologue || hasBranchTo errLabel bodyCode
  let hasExh := hasBranchTo exhaustedLabel bodyCode
  let hasAb0 := stmtHasAbort0 fd.body
  let needRetarget := hasErr || hasExh
  let exhSub? : Option String := if hasExh then some s!"{pfx}_exhstub" else none
  let rt := retargetBranchItem errLabel s!"{pfx}_errstub" exhaustedLabel exhSub?
  let fallthroughZero : List AsmItem :=
    [Asm.lbl s!"{pfx}_ret0"] ++
    (if stmtMayFallthrough fd.body then copyTempsToResultsR tab fl 0 0 else [])
  let epilogueCode : List AsmItem := [Asm.lbl epilogue] ++ framePopItems fl ++ [Asm.ret]
  let coldStubs : List AsmItem :=
    (if needRetarget then [Asm.lbl s!"{pfx}_errstub", Asm.j errLabel] else []) ++
    (if hasExh then [Asm.lbl s!"{pfx}_exhstub", Asm.j exhaustedLabel] else []) ++
    (if hasAb0 then [Asm.lbl s!"{pfx}_abort0stub", Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.j abortLabel] else [])
  have hpush : noT6Branch framePush = true := by
    dsimp only [framePush]
    split
    · rfl
    · have hra : noT6Branch (if fl.isLeaf = true then [] else [Asm.sd AbiReg.sp AbiReg.ra 0#12]) = true := by
        split <;> rfl
      simp only [noT6Branch_append, Bool.and_eq_true,
        noT6Branch_of_allInstrs (li_allInstrs _ _), hra,
        noT6Branch_of_allInstrs (saveCalleeRegs_allInstrs fl), true_and, and_true]
      rfl
  have ht5 : noT6Branch t5Init = true := by
    dsimp only [t5Init]; split <;> rfl
  have hpro : noT6Branch prologue = true := by
    dsimp only [prologue]
    simp only [noT6Branch_append, Bool.and_eq_true, hpush, ht5,
      noT6Branch_of_allInstrs (copyParamsR_allInstrs fl fd.nparams),
      noT6Branch_of_allInstrs (zeroLocalsR_allInstrs fl fd), and_true]
    rfl
  have hbody : noT6Branch bodyCode = true :=
    compileSR_noT6Branch tab fl hfl pfx epilogue fd.body 0 none (!stmtMayFallthrough fd.body)
  have hmain : noT6Branch (if needRetarget then prologue.map rt ++ bodyCode.map rt else prologue ++ bodyCode) = true := by
    split
    · simp only [rt, noT6Branch_append, noT6Branch_map_retarget, Bool.and_eq_true, hpro, hbody, and_self]
    · simp only [noT6Branch_append, Bool.and_eq_true, hpro, hbody, and_self]
  have hft : noT6Branch fallthroughZero = true := by
    dsimp only [fallthroughZero]
    have h0 : noT6Branch (if stmtMayFallthrough fd.body = true then copyTempsToResultsR tab fl 0 0 else []) = true := by
      split
      · exact noT6Branch_of_allInstrs (copyTempsToResultsR_allInstrs _ _ _ _)
      · rfl
    rw [noT6Branch_append, Bool.and_eq_true]; exact ⟨rfl, h0⟩
  have hepi : noT6Branch epilogueCode = true := by
    dsimp only [epilogueCode]
    simp only [noT6Branch_append, Bool.and_eq_true,
      noT6Branch_of_allInstrs (framePopItems_allInstrs fl), and_true]; exact ⟨rfl, rfl⟩
  have hcold : noT6Branch coldStubs = true := by
    dsimp only [coldStubs]
    have h1 : noT6Branch (if needRetarget = true then [Asm.lbl s!"{pfx}_errstub", Asm.j errLabel] else []) = true := by
      split <;> rfl
    have h2 : noT6Branch (if hasExh = true then [Asm.lbl s!"{pfx}_exhstub", Asm.j exhaustedLabel] else []) = true := by
      split <;> rfl
    have h3 : noT6Branch (if hasAb0 = true then [Asm.lbl s!"{pfx}_abort0stub", Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.j abortLabel] else []) = true := by
      split <;> rfl
    simp only [noT6Branch_append, Bool.and_eq_true, h1, h2, h3, and_self]
  change noT6Branch ((if needRetarget then prologue.map rt ++ bodyCode.map rt else prologue ++ bodyCode) ++
    fallthroughZero ++ epilogueCode ++ coldStubs) = true
  simp only [noT6Branch_append, Bool.and_eq_true, hmain, hft, hepi, hcold, and_self]

theorem drvFillConstLoop_noT6Branch (loopLbl doneLbl : String) (off : Int) (val : BitVec 64)
    (count : Nat) :
    noT6Branch (drvFillConstLoop loopLbl doneLbl off val count) = true := by
  dsimp only [drvFillConstLoop]
  split
  · rfl
  · simp only [noT6Branch_append, Bool.and_eq_true,
      noT6Branch_of_allInstrs (addImmOff_allInstrs _ _ _ _),
      noT6Branch_of_allInstrs (li_allInstrs _ _), true_and]
    rfl

theorem drvFillStrideLoop_noT6Branch (loopLbl doneLbl : String) (off : Int)
    (initOff stride : BitVec 64) (count : Nat) :
    noT6Branch (drvFillStrideLoop loopLbl doneLbl off initOff stride count) = true := by
  dsimp only [drvFillStrideLoop]
  split
  · rfl
  · simp only [noT6Branch_append, Bool.and_eq_true,
      noT6Branch_of_allInstrs (addImmOff_allInstrs _ _ _ _),
      noT6Branch_of_allInstrs (li_allInstrs _ _), true_and, and_true]
    exact ⟨rfl, rfl⟩

theorem drvInitSubAsm_noT6Branch (tab : Tab) :
    noT6Branch (drvInitSubAsm tab) = true := by
  dsimp only [drvInitSubAsm]
  have hbufB : noT6Branch (List.flatMap (fun p =>
      storeMemOff .sd AbiReg.gp (if p == 0 then AbiReg.a0 else AbiReg.a2) AbiReg.t0 (tab.dbase p))
      (List.range tab.nbuf)) = true :=
    noT6Branch_flatMap (fun _ _ => noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _))
  have hbufL : noT6Branch (List.flatMap (fun p =>
      storeMemOff .sd AbiReg.gp (if p == 0 then AbiReg.a1 else AbiReg.a3) AbiReg.t0 (tab.dlen p))
      (List.range tab.nbuf)) = true :=
    noT6Branch_flatMap (fun _ _ => noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _))
  have hrom : noT6Branch (List.flatMap (fun (w, i) =>
      li AbiReg.t1 w ++ storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.romBase + 8 * (i : Int)))
      (romWords64 tab.rom).zipIdx) = true :=
    noT6Branch_flatMap (fun ⟨_, _⟩ _ => by
      simp only [noT6Branch_append, Bool.and_eq_true,
        noT6Branch_of_allInstrs (li_allInstrs _ _),
        noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _), and_self])
  simp only [noT6Branch_append, Bool.and_eq_true,
    noT6Branch_of_allInstrs (li_allInstrs _ _),
    drvFillConstLoop_noT6Branch, drvFillStrideLoop_noT6Branch,
    hbufB, hbufL, hrom, true_and, and_true]
  repeat' (first | apply And.intro | rfl)

theorem checkerDriverAsm_noT6Branch (tab : Tab) :
    noT6Branch (checkerDriverAsm tab) = true := by
  dsimp only [checkerDriverAsm]
  simp only [noT6Branch_append, Bool.and_eq_true,
    noT6Branch_of_allInstrs (li_allInstrs _ _),
    noT6Branch_of_allInstrs (addImmOff_allInstrs _ _ _ _),
    noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
    noT6Branch_of_allInstrs (callerSaveAsm_allInstrs _ _),
    noT6Branch_of_allInstrs (callerRestoreRetAsm_allInstrs _ _),
    drvInitSubAsm_noT6Branch, true_and, and_true]
  repeat' (first | apply And.intro | rfl)

theorem checkerCmpDriverAsm_noT6Branch (tab : Tab) :
    noT6Branch (checkerCmpDriverAsm tab) = true := by
  dsimp only [checkerCmpDriverAsm]
  simp only [noT6Branch_append, Bool.and_eq_true,
    noT6Branch_of_allInstrs (li_allInstrs _ _),
    noT6Branch_of_allInstrs (addImmOff_allInstrs _ _ _ _),
    noT6Branch_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
    noT6Branch_of_allInstrs (callerSaveAsm_allInstrs _ _),
    true_and, and_true]
  repeat' (first | apply And.intro | rfl)

/-- Every `.br` / `.brLong` in `checkerChipAsm tab p` avoids `AbiReg.t6` (`x31`). -/
theorem checkerChipAsm_noT6Branch_gen (tab : Tab) (p : Prog) :
    noT6Branch (checkerChipAsm tab p) = true := by
  dsimp only [checkerChipAsm]
  simp only [noT6Branch_append, Bool.and_eq_true]
  exact ⟨⟨checkerDriverAsm_noT6Branch tab, checkerCmpDriverAsm_noT6Branch tab⟩,
    noT6Branch_flatMap (fun (f, fd) _ => compileFn_noT6Branch tab f fd)⟩

/-- **`checkerChipAsm_noT6Branch`:** No `.br` / `.brLong` in `checkerChipAsm` reads `AbiReg.t6`. -/
theorem checkerChipAsm_noT6Branch : noT6Branch checkerChipAsm = true :=
  checkerChipAsm_noT6Branch_gen checkerTabMini checkerProgMini

end ConAgua.RISCV.Bridge
