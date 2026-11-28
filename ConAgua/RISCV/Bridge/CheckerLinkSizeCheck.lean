import ConAgua.RISCV.Bridge.CheckerProgScan
import ConAgua.RISCV.Bridge.CheckerLinkSize

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Combined Size Check for `checkerChipAsm` (`ConAgua.RISCV.Bridge.CheckerLinkSizeCheck`)

Derives `< 2 ^ 22` word-count bounds for the unified `checkerChipAsm` image
directly from the single-pass fused scan `checkerProg_fnBoundAndFrameL_sum_lt` in
`CheckerProgScan`, using free-variable-parameterized equivalence lemmas so neither
`L.Checker.checkerProg` nor `checkerProgMini` is ever unfolded.
-/

namespace ConAgua.RISCV.Bridge

open ConAgua.RISCV.RV64
open ConAgua.RISCV.Compiler
open ConAgua.RISCV.Linker
open _root_.L

private theorem exprTempsAndBoundL_eq : ∀ (e : L.Expr),
    exprTempsAndBoundL e =
      (maxTempsExpr e, exprBound32 e)
  | .const _ | .var _ | .len8 _ | .len64 _ | .glob _ => rfl
  | .bin _ a b | .cmpw _ a b | .ld64t _ a b | .ld32t _ a b | .ld32h _ a b _ => by
    have ha := exprTempsAndBoundL_eq a
    have hb := exprTempsAndBoundL_eq b
    dsimp only [exprTempsAndBoundL, maxTempsExpr, exprBound32]
    rw [ha, hb]
  | .ld8 _ i | .ld64 _ i | .ldc _ i | .len64t _ i | .ld8x8 _ i => by
    have hi := exprTempsAndBoundL_eq i
    dsimp only [exprTempsAndBoundL, maxTempsExpr, exprBound32]
    rw [hi]

private theorem warrTempsAndBoundL_eq : ∀ (w : L.WArr),
    warrTempsAndBoundL w =
      ((match w with | .plain _ => 0 | .tier _ t => maxTempsExpr t),
       warrBound32 w)
  | .plain _ => rfl
  | .tier _ t => by
    have ht := exprTempsAndBoundL_eq t
    dsimp only [warrTempsAndBoundL, warrBound32]
    rw [ht]

private theorem condTempsAndBoundL_eq : ∀ (c : L.Cond),
    condTempsAndBoundL c =
      (maxTempsCond c, condBound32 c)
  | .cmp _ a b => by
    have ha := exprTempsAndBoundL_eq a
    have hb := exprTempsAndBoundL_eq b
    dsimp only [condTempsAndBoundL, maxTempsCond, condBound32]
    rw [ha, hb]
  | .and p q | .or p q => by
    have hp := condTempsAndBoundL_eq p
    have hq := condTempsAndBoundL_eq q
    dsimp only [condTempsAndBoundL, maxTempsCond, condBound32]
    rw [hp, hq]
  | .not p => condTempsAndBoundL_eq p

private theorem exprsTempsAndBoundLGo_eq : ∀ (es : List L.Expr) (idx mt b32 : Nat),
    exprsTempsAndBoundLGo idx mt b32 es =
      ((es.zipIdx idx).foldl (fun acc (e, i) => max acc (i + max 1 (maxTempsExpr e))) mt,
       b32 + exprsBound32 es)
  | [], _, _, _ => by simp [exprsTempsAndBoundLGo, exprsBound32]
  | e :: es, idx, mt, b32 => by
    have he := exprTempsAndBoundL_eq e
    have ih := exprsTempsAndBoundLGo_eq es (idx + 1)
      (max mt (idx + max 1 (maxTempsExpr e))) (b32 + exprBound32 e + 6)
    dsimp only [exprsTempsAndBoundLGo]
    rw [he, ih]
    simp only [List.zipIdx_cons, List.foldl_cons, exprsBound32]
    congr 1
    omega

private theorem exprsTempsAndBoundL_eq (es : List L.Expr) :
    exprsTempsAndBoundL es =
      (maxTempsExprs es, exprsBound32 es) := by
  dsimp only [exprsTempsAndBoundL, maxTempsExprs]
  rw [exprsTempsAndBoundLGo_eq]
  simp [Nat.zero_add]

private theorem stmtTempsAndBoundL_eq : ∀ (s : L.Stmt),
    stmtTempsAndBoundL s =
      (maxTempsStmt s, stmtBound32 10 s)
  | .skip | .brk => rfl
  | .set _ e | .gset _ e | .abort e => by
    have he := exprTempsAndBoundL_eq e
    dsimp only [stmtTempsAndBoundL, maxTempsStmt, stmtBound32]
    rw [he]
  | .st8 _ i e => by
    have hi := exprTempsAndBoundL_eq i
    have he := exprTempsAndBoundL_eq e
    dsimp only [stmtTempsAndBoundL, maxTempsStmt, stmtBound32]
    rw [hi, he]
  | .st64 _ i e => by
    have hi := exprTempsAndBoundL_eq i
    have he := exprTempsAndBoundL_eq e
    dsimp only [stmtTempsAndBoundL, maxTempsStmt, stmtBound32]
    rw [hi, he]
  | .st64t _ t i e | .st32t _ t i e => by
    have ht := exprTempsAndBoundL_eq t
    have hi := exprTempsAndBoundL_eq i
    have he := exprTempsAndBoundL_eq e
    dsimp only [stmtTempsAndBoundL, maxTempsStmt, stmtBound32]
    rw [ht, hi, he]
  | .seq s₁ s₂ => by
    have h1 := stmtTempsAndBoundL_eq s₁
    have h2 := stmtTempsAndBoundL_eq s₂
    dsimp only [stmtTempsAndBoundL, maxTempsStmt, stmtBound32]
    rw [h1, h2]
  | .ite c s₁ s₂ => by
    have hc := condTempsAndBoundL_eq c
    have h1 := stmtTempsAndBoundL_eq s₁
    have h2 := stmtTempsAndBoundL_eq s₂
    dsimp only [stmtTempsAndBoundL, maxTempsStmt, stmtBound32]
    rw [hc, h1, h2]
  | .while c s => by
    have hc := condTempsAndBoundL_eq c
    have hs := stmtTempsAndBoundL_eq s
    dsimp only [stmtTempsAndBoundL, maxTempsStmt, stmtBound32]
    rw [hc, hs]
  | .ret es => by
    have hes := exprsTempsAndBoundL_eq es
    dsimp only [stmtTempsAndBoundL, maxTempsStmt, stmtBound32]
    rw [hes]
  | .call xs f args => by
    have ha := exprsTempsAndBoundL_eq args
    dsimp only [stmtTempsAndBoundL, maxTempsStmt, stmtBound32]
    rw [ha]
    simp [maxResL, maxRes]
  | .copy64 d di s si n => by
    have hd := warrTempsAndBoundL_eq d
    have hdi := exprTempsAndBoundL_eq di
    have hs := warrTempsAndBoundL_eq s
    have hsi := exprTempsAndBoundL_eq si
    have hn := exprTempsAndBoundL_eq n
    dsimp only [stmtTempsAndBoundL, maxTempsStmt, stmtBound32]
    rw [hd, hdi, hs, hsi, hn]
    cases s <;> rfl
  | .copy8w d di _ si n => by
    have hd := warrTempsAndBoundL_eq d
    have hdi := exprTempsAndBoundL_eq di
    have hsi := exprTempsAndBoundL_eq si
    have hn := exprTempsAndBoundL_eq n
    dsimp only [stmtTempsAndBoundL, maxTempsStmt, stmtBound32]
    rw [hd, hdi, hsi, hn]
    rfl
  | .scan8 x s i e c => by
    have hi := exprTempsAndBoundL_eq i
    have he := exprTempsAndBoundL_eq e
    dsimp only [stmtTempsAndBoundL, maxTempsStmt, stmtBound32]
    rw [hi, he]

private theorem fastExpr_maxVar_le {lm : L.Compiler.NTree} {nb ng nl : Nat} :
    ∀ {e : L.Expr}, fastExpr lm nb ng nl e = true → maxVarExpr e ≤ nl
  | .const _, _ | .len8 _, _ | .len64 _, _ | .glob _, _ => Nat.zero_le _
  | .var x, h => by
    simp only [fastExpr, decide_eq_true_eq] at h
    exact h
  | .bin _ a b, h | .cmpw _ a b, h => by
    simp only [fastExpr, Bool.and_eq_true] at h
    simp only [maxVarExpr, Nat.max_le]
    exact ⟨fastExpr_maxVar_le h.1, fastExpr_maxVar_le h.2⟩
  | .ld8 _ i, h | .ld64 _ i, h | .len64t _ i, h => by
    simp only [fastExpr, Bool.and_eq_true] at h
    exact fastExpr_maxVar_le (e := i) h.2
  | .ldc _ i, h => fastExpr_maxVar_le (e := i) h
  | .ld64t _ t i, h | .ld32t _ t i, h | .ld32h _ t i _, h => by
    simp only [fastExpr, Bool.and_eq_true] at h
    simp only [maxVarExpr, Nat.max_le]
    exact ⟨fastExpr_maxVar_le h.1.2, fastExpr_maxVar_le h.2⟩
  | .ld8x8 b i, h => by
    cases b with
    | arr _ =>
      simp only [fastExpr, Bool.and_eq_true] at h
      exact fastExpr_maxVar_le (e := i) h.2
    | rom _ => exact fastExpr_maxVar_le (e := i) h

private theorem fastCond_maxVar_le {lm : L.Compiler.NTree} {nb ng nl : Nat} :
    ∀ {c : L.Cond}, fastCond lm nb ng nl c = true → maxVarCond c ≤ nl
  | .cmp _ a b, h => by
    simp only [fastCond, Bool.and_eq_true] at h
    simp only [maxVarCond, Nat.max_le]
    exact ⟨fastExpr_maxVar_le h.1, fastExpr_maxVar_le h.2⟩
  | .and p q, h | .or p q, h => by
    simp only [fastCond, Bool.and_eq_true] at h
    simp only [maxVarCond, Nat.max_le]
    exact ⟨fastCond_maxVar_le h.1, fastCond_maxVar_le h.2⟩
  | .not p, h => fastCond_maxVar_le (c := p) h

private theorem fastWArr_maxVar_le {lm : L.Compiler.NTree} {nb ng nl : Nat} :
    ∀ {w : L.WArr}, fastWArr lm nb ng nl w = true → maxVarWArr w ≤ nl
  | .plain _, _ => Nat.zero_le _
  | .tier _ t, h => by
    simp only [fastWArr, Bool.and_eq_true] at h
    exact fastExpr_maxVar_le h.2

private theorem maxVarVars_le {nl : Nat} : ∀ {xs : List Var},
    xs.all (· < nl) = true → maxVarVars xs ≤ nl
  | [], _ => Nat.zero_le _
  | x :: xs, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [maxVarVars, Nat.max_le]
    exact ⟨h.1, maxVarVars_le h.2⟩

private theorem maxVarExprs_le {lm : L.Compiler.NTree} {nb ng nl : Nat} : ∀ {es : List L.Expr},
    es.all (fastExpr lm nb ng nl) = true → maxVarExprs es ≤ nl
  | [], _ => Nat.zero_le _
  | e :: es, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [maxVarExprs, Nat.max_le]
    exact ⟨fastExpr_maxVar_le h.1, maxVarExprs_le h.2⟩

private theorem fastStmt_maxVar_le {lm : L.Compiler.NTree} {nb ng nres : Nat} {tr : L.Compiler.NTree} {nl : Nat} :
    ∀ {inLoop : Bool} {s : L.Stmt},
      fastStmt lm nb ng nres tr nl inLoop s = true → maxVarStmt s ≤ nl
  | _, .skip, _ | _, .brk, _ => Nat.zero_le _
  | _, .set x e, h => by
    simp only [fastStmt, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [maxVarStmt, Nat.max_le]
    exact ⟨h.1, fastExpr_maxVar_le h.2⟩
  | _, .gset _ e, h => by
    simp only [fastStmt, Bool.and_eq_true] at h
    exact fastExpr_maxVar_le h.2
  | _, .abort e, h => fastExpr_maxVar_le h
  | _, .st8 _ _ _, h => by cases h
  | _, .st64 _ i e, h => by
    simp only [fastStmt, Bool.and_eq_true] at h
    simp only [maxVarStmt, Nat.max_le]
    exact ⟨fastExpr_maxVar_le h.1.2, fastExpr_maxVar_le h.2⟩
  | _, .st64t _ t i e, h | _, .st32t _ t i e, h => by
    simp only [fastStmt, Bool.and_eq_true] at h
    simp only [maxVarStmt, Nat.max_le]
    exact ⟨fastExpr_maxVar_le h.1.1.2, fastExpr_maxVar_le h.1.2, fastExpr_maxVar_le h.2⟩
  | _, .seq s₁ s₂, h => by
    simp only [fastStmt, Bool.and_eq_true] at h
    simp only [maxVarStmt, Nat.max_le]
    exact ⟨fastStmt_maxVar_le h.1, fastStmt_maxVar_le h.2⟩
  | _, .ite c s₁ s₂, h => by
    simp only [fastStmt, Bool.and_eq_true] at h
    simp only [maxVarStmt, Nat.max_le]
    exact ⟨fastCond_maxVar_le h.1.1, fastStmt_maxVar_le h.1.2, fastStmt_maxVar_le h.2⟩
  | _, .while c s, h => by
    simp only [fastStmt, Bool.and_eq_true] at h
    simp only [maxVarStmt, Nat.max_le]
    exact ⟨fastCond_maxVar_le h.1, fastStmt_maxVar_le h.2⟩
  | _, .ret es, h => by
    simp only [fastStmt, Bool.and_eq_true] at h
    exact maxVarExprs_le h.2
  | _, .call xs _ args, h => by
    simp only [fastStmt, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [maxVarStmt, Nat.max_le]
    exact ⟨maxVarExprs_le h.2, maxVarVars_le h.1.2⟩
  | _, .copy64 d di s si n, h => by
    simp only [fastStmt, Bool.and_eq_true] at h
    simp only [maxVarStmt, Nat.max_le]
    exact ⟨fastWArr_maxVar_le h.1.1.1.1, fastExpr_maxVar_le h.1.1.1.2,
      fastWArr_maxVar_le h.1.1.2, fastExpr_maxVar_le h.1.2, fastExpr_maxVar_le h.2⟩
  | _, .copy8w d di _ si n, h => by
    simp only [fastStmt, Bool.and_eq_true] at h
    simp only [maxVarStmt, Nat.max_le]
    exact ⟨fastWArr_maxVar_le h.1.1.1.1, fastExpr_maxVar_le h.1.1.1.2,
      fastExpr_maxVar_le h.1.2, fastExpr_maxVar_le h.2⟩
  | _, .scan8 x _ i e _, h => by
    simp only [fastStmt, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [maxVarStmt, Nat.max_le]
    exact ⟨h.1.1.1.1, fastExpr_maxVar_le h.1.1.2, fastExpr_maxVar_le h.1.2⟩

private def fnBoundAndFrameUB (fd : FunDecl) : Nat :=
  let nl := max fd.nlocals fd.nparams
  if (nl + maxTempsStmt fd.body).blt 100000 then
    59 + 12 * fd.nparams + 6 * (nl - fd.nparams) + stmtBound32 10 fd.body
  else
    5000000

private theorem fnBoundAndFrameL_eq (fd : L.FunDecl) :
    fnBoundAndFrameL fd = fnBoundAndFrameUB fd := by
  dsimp only [fnBoundAndFrameL, fnBoundAndFrameUB]
  rw [stmtTempsAndBoundL_eq]

private theorem foldl_fnBoundAndFrameL_eq (prog : L.Prog) :
    ∀ init : Nat,
      prog.foldl (fun acc x => acc + fnBoundAndFrameL x.2) init =
        prog.foldl (fun acc p => acc + fnBoundAndFrameUB p.2) init := by
  induction prog with
  | nil => intro init; rfl
  | cons hd tl ih =>
    intro init
    simp only [List.foldl_cons]
    rw [fnBoundAndFrameL_eq]
    exact ih _

private theorem nat_blt_iff_lt (a b : Nat) : a.blt b = true ↔ a < b := by
  simp only [Nat.blt, Nat.ble_eq]; omega

def fnBoundAndFrameCheck (p : FnName × FunDecl) : Nat :=
  let fd := p.2
  let nl := numLocalsFn fd
  if (nl + maxTempsStmt fd.body).blt 100000 then
    59 + 12 * fd.nparams + 6 * (nl - fd.nparams) + stmtBound32 10 fd.body
  else
    5000000

private theorem frames_and_sum_of_ub_lt (mprog : List (FnName × FunDecl))
    (hmaxv : ∀ p ∈ mprog, maxVarStmt p.2.body ≤ p.2.nlocals)
    (hlt : mprog.foldl (fun acc p => acc + fnBoundAndFrameUB p.2) 0 < 3800000) :
    (∀ p ∈ mprog, numLocalsFn p.2 + maxTempsStmt p.2.body < 100000) ∧
    mprog.foldl (fun acc p => acc + fnBound32 10 p.2) 0 < 3800000 ∧
    mprog.foldl (fun acc p => acc + fnBoundAndFrameCheck p) 0 < 3800000 := by
  have hfold_mono : ∀ (ps : List (FnName × FunDecl)) (init : Nat),
      init ≤ ps.foldl (fun acc p => acc + fnBoundAndFrameUB p.2) init := by
    intro ps
    induction ps with
    | nil => intro init; simp
    | cons p ps ih =>
      intro init
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_add_right _ _) (ih _)
  have hmem_le : ∀ (ps : List (FnName × FunDecl)) (init : Nat) (p : FnName × FunDecl),
      p ∈ ps → init + fnBoundAndFrameUB p.2 ≤ ps.foldl (fun acc q => acc + fnBoundAndFrameUB q.2) init := by
    intro ps
    induction ps with
    | nil => intro _ _ hm; cases hm
    | cons q qs ih =>
      intro init p hm
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact hfold_mono qs _
      · exact Nat.le_trans (Nat.add_le_add_right (Nat.le_add_right _ _) _) (ih _ p hm')
  have hframes : ∀ p ∈ mprog, numLocalsFn p.2 + maxTempsStmt p.2.body < 100000 := by
    intro p hp
    have hle := hmem_le mprog 0 p hp
    dsimp only [fnBoundAndFrameUB] at hle
    split at hle
    · next hc =>
      have hub : max p.2.nlocals p.2.nparams + maxTempsStmt p.2.body < 100000 :=
        (nat_blt_iff_lt _ _).mp hc
      have hnl := numLocalsFn_le_maxVar p.2
      have hmv := hmaxv p hp
      omega
    · have h5 : 5000000 ≤ mprog.foldl (fun acc q => acc + fnBoundAndFrameUB q.2) 0 := by
        simpa [fnBoundAndFrameUB] using Nat.le_trans (by omega) hle
      omega
  have hle_fn : ∀ p ∈ mprog, fnBound32 10 p.2 ≤ fnBoundAndFrameUB p.2 := by
    intro p hp
    have hle := hmem_le mprog 0 p hp
    dsimp only [fnBoundAndFrameUB, fnBound32] at hle ⊢
    split at hle
    · next hc =>
      simp only [hc, ↓reduceIte]
      have hnl := numLocalsFn_le_maxVar p.2
      have hmv := hmaxv p hp
      omega
    · have h5 : 5000000 ≤ mprog.foldl (fun acc q => acc + fnBoundAndFrameUB q.2) 0 := by
        simpa [fnBoundAndFrameUB] using Nat.le_trans (by omega) hle
      omega
  have hfold_le : ∀ (ps : List (FnName × FunDecl)) (f g : (FnName × FunDecl) → Nat),
      (∀ p ∈ ps, f p ≤ g p) →
      ∀ init₁ init₂ : Nat, init₁ ≤ init₂ →
        ps.foldl (fun acc p => acc + f p) init₁ ≤ ps.foldl (fun acc p => acc + g p) init₂ := by
    intro ps f g hfg
    induction ps with
    | nil => intro i1 i2 hi; exact hi
    | cons p ps ih =>
      intro i1 i2 hi
      simp only [List.foldl_cons]
      exact ih (fun q hq => hfg q (List.mem_cons_of_mem _ hq)) _ _
        (Nat.add_le_add hi (hfg p (List.mem_cons_self ..)))
  have hsum32 : mprog.foldl (fun acc p => acc + fnBound32 10 p.2) 0 < 3800000 :=
    Nat.lt_of_le_of_lt (hfold_le mprog (fun p => fnBound32 10 p.2) (fun p => fnBoundAndFrameUB p.2) hle_fn 0 0 (Nat.le_refl 0)) hlt
  have heq : ∀ (ps : List (FnName × FunDecl)) (init : Nat),
      (∀ p ∈ ps, numLocalsFn p.2 + maxTempsStmt p.2.body < 100000) →
      ps.foldl (fun acc p => acc + fnBoundAndFrameCheck p) init =
        ps.foldl (fun acc p => acc + fnBound32 10 p.2) init := by
    intro ps
    induction ps with
    | nil => intro _ _; rfl
    | cons p ps ih =>
      intro init hps
      have hp := hps p (by simp)
      have hbc : (numLocalsFn p.2 + maxTempsStmt p.2.body).blt 100000 = true :=
        (nat_blt_iff_lt _ _).mpr hp
      simp only [List.foldl_cons, fnBoundAndFrameCheck, fnBound32, hbc, ↓reduceIte]
      exact ih _ (fun q hq => hps q (by simp [hq]))
  refine ⟨hframes, hsum32, ?_⟩
  rw [heq mprog 0 hframes]
  exact hsum32

private theorem checkerProgMini_frames_and_sum_all :
    (∀ p ∈ checkerProgMini, numLocalsFn p.2 + maxTempsStmt p.2.body < 100000) ∧
    checkerProgMini.foldl (fun acc p => acc + fnBound32 10 p.2) 0 < 3800000 ∧
    checkerProgMini.foldl (fun acc p => acc + fnBoundAndFrameCheck p) 0 < 3800000 := by
  have hlt : checkerProgMini.foldl (fun acc p => acc + fnBoundAndFrameUB p.2) 0 < 3800000 := by
    dsimp only [checkerProgMini]
    rw [← foldl_fnBoundAndFrameL_eq L.Checker.checkerProg 0]
    exact checkerProg_fnBoundAndFrameL_sum_lt
  have hmaxv : ∀ p ∈ checkerProgMini, maxVarStmt p.2.body ≤ p.2.nlocals :=
    fun x hx => fastStmt_maxVar_le (checkerProg_fastStmt_all x hx)
  exact frames_and_sum_of_ub_lt checkerProgMini hmaxv hlt

theorem checkerProgMini_fnBound32_sum_lt :
    ((checkerProgMini.foldl (fun acc p => acc + fnBoundAndFrameCheck p) 0).blt 3800000) = true :=
  (nat_blt_iff_lt _ _).mpr checkerProgMini_frames_and_sum_all.2.2

private theorem sum_lt_2pow22 {a b c d : Nat} (ha : a ≤ 100000) (hb : b ≤ 100000) (hc : c ≤ d) (hd : d < 3800000) :
    a + b + c < 2 ^ 22 := by omega

private theorem progOkConst0B_all {tab : Tab} {p : List (FnName × FunDecl)}
    (h : progOkConst0B tab p = true) :
    ∀ q ∈ p, stmtOkConst0B tab p (numLocalsFn q.2) false q.2.body = true := by
  dsimp only [progOkConst0B] at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact h.2

private theorem chipAsm_farTotalWords_lt_gen (drv cmpDrv : List AsmItem)
    (p : List (FnName × FunDecl)) (tab : Tab)
    (ht : TabSmall32 tab) (hnres : tab.nres = 10)
    (hdrv : farTotalWords drv ≤ 100000)
    (hcmp : farTotalWords cmpDrv ≤ 100000)
    (hframes : ∀ q ∈ p, numLocalsFn q.2 + maxTempsStmt q.2.body < 100000)
    (hsum : p.foldl (fun acc q => acc + fnBound32 10 q.2) 0 < 3800000)
    (hfok : ∀ q ∈ p, stmtOkConst0B tab p (numLocalsFn q.2) false q.2.body = true) :
    farTotalWords (drv ++ cmpDrv ++ ((orderProgFns p).flatMap fun (f, fd) => compileFn tab f fd)) < 2 ^ 22 := by
  rw [farTotalWords_append, farTotalWords_append,
    farTotalWords_flatMap_perm (orderProgFns_perm p) (fun (f, fd) => compileFn tab f fd)]
  have hfns := farTotalWords_flatMap_le p
    (fun (f, fd) => compileFn tab f fd)
    (fun q => fnBound32 tab.nres q.2)
    (fun ⟨f, fd⟩ hmem => compileFn_farTotalWords_le ht f fd p
      (hframes (f, fd) hmem) (hfok (f, fd) hmem))
  rw [hnres] at hfns
  exact sum_lt_2pow22 hdrv hcmp hfns hsum

/-- **`checkerChipAsm_farTotalWords_lt`:** Unified binary size is `< 2 ^ 22` words (`16 MiB`). -/
theorem checkerChipAsm_farTotalWords_lt : farTotalWords checkerChipAsm < 2 ^ 22 :=
  chipAsm_farTotalWords_lt_gen (checkerDriverAsm checkerTabMini) (checkerCmpDriverAsm checkerTabMini)
    checkerProgMini checkerTabMini
    checkerTabMini_small32 (by decide)
    (checkerDriverAsm_farTotalWords_le checkerTabMini_small32)
    (checkerCmpDriverAsm_farTotalWords_le checkerTabMini_small32)
    checkerProgMini_frames_and_sum_all.1 checkerProgMini_frames_and_sum_all.2.1
    (progOkConst0B_all checkerProgMini_progOkConst0B)

/-- **`checkerChipAsm_totalSize_lt`:** `farLinkModel.totalSize checkerChipAsm < 2 ^ 22`. -/
theorem checkerChipAsm_totalSize_lt : farLinkModel.totalSize checkerChipAsm < 2 ^ 22 := by
  rw [far_totalSize_eq]; exact checkerChipAsm_farTotalWords_lt

end ConAgua.RISCV.Bridge
