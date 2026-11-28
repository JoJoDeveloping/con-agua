import ConAgua.RISCV.Compiler.RegSimExpr
import ConAgua.RISCV.Compiler.ProgSimScan

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Register-Allocated Liveness & Base-Statement Helpers (`ConAgua.RISCV.Compiler.RegSimStmtBase`)

Proves:
1. Pure `MiniL` liveness soundness (`stmtVarLive`): skipping zero-initialization of
   dead locals (`varNeedsZeroInit fd x = false`) preserves both `execB` and `stackNeedB`.
2. Register-allocated store-operand & tiered-array helpers (`evalWArrTierToTempR`,
   `compileStorePairR`, `compileTierStoreTripleR`) and `PreservedFrameRegs` helpers.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard Lean axioms only.
-/

namespace ConAgua.RISCV.Compiler

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Linker

/-! ## 1. Pure `MiniL` Liveness Soundness (`stmtVarLive`) -/

private theorem evalE_dead_var_eq (x : Var) (e : Expr) (hnu : exprUsesVar x e = false)
    (m : _root_.L.Mem) (l1 l2 : _root_.L.Locals) (hag : ∀ y, y ≠ x → l1 y = l2 y) :
    match _root_.L.evalE e ⟨m, l1⟩, _root_.L.evalE e ⟨m, l2⟩ with
    | .ok (v1, _), .ok (v2, _) => v1 = v2
    | .error e1, .error e2 => e1 = e2
    | _, _ => False := by
  induction e with
  | const w => rfl
  | var y =>
    simp only [exprUsesVar, beq_eq_false_iff_ne] at hnu
    exact hag y hnu
  | len8 a | len64 a | glob a => rfl
  | ld8 a i ih =>
    simp only [exprUsesVar] at hnu
    have h := ih hnu
    rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨v2, h2⟩ | h2 <;>
    simp only [h1, h2] at h
    · subst h
      dsimp only [_root_.L.evalE]
      simp only [Bind.bind, StateT.bind, Except.bind, h1, h2, _root_.L.ld8, get, getThe,
        MonadStateOf.get, StateT.get, Pure.pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, Function.comp_apply]
      by_cases hb : v1.toNat < (m.arr8 a).size <;> simp only [hb] <;> rfl
    · dsimp only [_root_.L.evalE]
      simp only [Bind.bind, StateT.bind, Except.bind, h1, h2]
  | ld64 a i ih =>
    simp only [exprUsesVar] at hnu
    have h := ih hnu
    rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨v2, h2⟩ | h2 <;>
    simp only [h1, h2] at h
    · subst h
      dsimp only [_root_.L.evalE]
      simp only [Bind.bind, StateT.bind, Except.bind, h1, h2, _root_.L.ld64, get, getThe,
        MonadStateOf.get, StateT.get, Pure.pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, Function.comp_apply]
      by_cases hb : v1.toNat < (m.arr64 (.t0 a)).size <;> simp only [hb] <;> rfl
    · dsimp only [_root_.L.evalE]
      simp only [Bind.bind, StateT.bind, Except.bind, h1, h2]
  | ldc d i ih =>
    simp only [exprUsesVar] at hnu
    have h := ih hnu
    rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨v2, h2⟩ | h2 <;>
    simp only [h1, h2] at h
    · subst h
      dsimp only [_root_.L.evalE]
      simp only [Bind.bind, StateT.bind, Except.bind, h1, h2, _root_.L.ldc,
        Pure.pure, throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
      by_cases hb : v1.toNat < d.length <;> simp only [hb] <;> rfl
    · dsimp only [_root_.L.evalE]
      simp only [Bind.bind, StateT.bind, Except.bind, h1, h2]
  | ld8x8 src i ih =>
    simp only [exprUsesVar] at hnu
    have h := ih hnu
    rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨v2, h2⟩ | h2 <;>
    simp only [h1, h2] at h
    · subst h
      dsimp only [_root_.L.evalE]
      simp only [Bind.bind, StateT.bind, Except.bind, h1, h2, _root_.L.ld8x8, get, getThe,
        MonadStateOf.get, StateT.get, Pure.pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, Function.comp_apply]
      by_cases hb : v1.toNat + 8 ≤ (m.src8 src).size <;> simp only [hb, ↓reduceIte] <;> rfl
    · dsimp only [_root_.L.evalE]
      simp only [Bind.bind, StateT.bind, Except.bind, h1, h2]
  | len64t a t ih =>
    simp only [exprUsesVar] at hnu
    have h := ih hnu
    rcases _root_.L.evalE_pure t ⟨m, l1⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure t ⟨m, l2⟩ with ⟨v2, h2⟩ | h2 <;>
    simp only [h1, h2] at h
    · subst h
      dsimp only [_root_.L.evalE]
      simp only [Bind.bind, StateT.bind, Except.bind, h1, h2, get, getThe,
        MonadStateOf.get, StateT.get, Pure.pure, StateT.pure, Except.pure]
    · dsimp only [_root_.L.evalE]
      simp only [Bind.bind, StateT.bind, Except.bind, h1, h2]
  | bin op a b iha ihb =>
    simp only [exprUsesVar, Bool.or_eq_false_iff] at hnu
    have ha := iha hnu.1; have hb := ihb hnu.2
    rcases _root_.L.evalE_pure a ⟨m, l1⟩ with ⟨va1, ha1⟩ | ha1 <;>
    rcases _root_.L.evalE_pure a ⟨m, l2⟩ with ⟨va2, ha2⟩ | ha2 <;>
    simp only [ha1, ha2] at ha
    · subst ha
      rcases _root_.L.evalE_pure b ⟨m, l1⟩ with ⟨vb1, hb1⟩ | hb1 <;>
      rcases _root_.L.evalE_pure b ⟨m, l2⟩ with ⟨vb2, hb2⟩ | hb2 <;>
      simp only [hb1, hb2] at hb
      · subst hb
        simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ha1, ha2, hb1, hb2, Pure.pure, StateT.pure, Except.pure]
      · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ha1, ha2, hb1, hb2]
    · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ha1, ha2]
  | cmpw c a b iha ihb =>
    simp only [exprUsesVar, Bool.or_eq_false_iff] at hnu
    have ha := iha hnu.1; have hb := ihb hnu.2
    rcases _root_.L.evalE_pure a ⟨m, l1⟩ with ⟨va1, ha1⟩ | ha1 <;>
    rcases _root_.L.evalE_pure a ⟨m, l2⟩ with ⟨va2, ha2⟩ | ha2 <;>
    simp only [ha1, ha2] at ha
    · subst ha
      rcases _root_.L.evalE_pure b ⟨m, l1⟩ with ⟨vb1, hb1⟩ | hb1 <;>
      rcases _root_.L.evalE_pure b ⟨m, l2⟩ with ⟨vb2, hb2⟩ | hb2 <;>
      simp only [hb1, hb2] at hb
      · subst hb
        simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ha1, ha2, hb1, hb2, Pure.pure, StateT.pure, Except.pure]
      · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ha1, ha2, hb1, hb2]
    · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ha1, ha2]
  | ld64t a t i iht ihi =>
    simp only [exprUsesVar, Bool.or_eq_false_iff] at hnu
    have ht := iht hnu.1; have hi := ihi hnu.2
    rcases _root_.L.evalE_pure t ⟨m, l1⟩ with ⟨vt1, ht1⟩ | ht1 <;>
    rcases _root_.L.evalE_pure t ⟨m, l2⟩ with ⟨vt2, ht2⟩ | ht2 <;>
    simp only [ht1, ht2] at ht
    · subst ht
      rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨vi1, hi1⟩ | hi1 <;>
      rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨vi2, hi2⟩ | hi2 <;>
      simp only [hi1, hi2] at hi
      · subst hi
        simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2, _root_.L.ld64,
          get, getThe, MonadStateOf.get, StateT.get, Pure.pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
        by_cases hb : vi1.toNat < (m.arr64 (tierA a vt1)).size <;> simp only [hb] <;> rfl
      · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2]
    · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2]
  | ld32t a t i iht ihi =>
    simp only [exprUsesVar, Bool.or_eq_false_iff] at hnu
    have ht := iht hnu.1; have hi := ihi hnu.2
    rcases _root_.L.evalE_pure t ⟨m, l1⟩ with ⟨vt1, ht1⟩ | ht1 <;>
    rcases _root_.L.evalE_pure t ⟨m, l2⟩ with ⟨vt2, ht2⟩ | ht2 <;>
    simp only [ht1, ht2] at ht
    · subst ht
      rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨vi1, hi1⟩ | hi1 <;>
      rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨vi2, hi2⟩ | hi2 <;>
      simp only [hi1, hi2] at hi
      · subst hi
        simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2, _root_.L.ld32,
          get, getThe, MonadStateOf.get, StateT.get, Pure.pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
        by_cases hb : (vi1 / 2).toNat < (m.arr64 (tierA a vt1)).size <;> simp only [hb] <;> rfl
      · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2]
    · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2]
  | ld32h a t i hiFlag iht ihi =>
    simp only [exprUsesVar, Bool.or_eq_false_iff] at hnu
    have ht := iht hnu.1; have hi := ihi hnu.2
    rcases _root_.L.evalE_pure t ⟨m, l1⟩ with ⟨vt1, ht1⟩ | ht1 <;>
    rcases _root_.L.evalE_pure t ⟨m, l2⟩ with ⟨vt2, ht2⟩ | ht2 <;>
    simp only [ht1, ht2] at ht
    · subst ht
      rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨vi1, hi1⟩ | hi1 <;>
      rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨vi2, hi2⟩ | hi2 <;>
      simp only [hi1, hi2] at hi
      · subst hi
        simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2, _root_.L.ld64,
          get, getThe, MonadStateOf.get, StateT.get, Pure.pure, StateT.pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
        by_cases hb : vi1.toNat < (m.arr64 (tierA a vt1)).size <;> simp only [hb] <;> rfl
      · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2]
    · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2]

private theorem evalC_dead_var_eq (x : Var) (c : Cond) (hnu : condUsesVar x c = false)
    (m : _root_.L.Mem) (l1 l2 : _root_.L.Locals) (hag : ∀ y, y ≠ x → l1 y = l2 y) :
    match _root_.L.evalC c ⟨m, l1⟩, _root_.L.evalC c ⟨m, l2⟩ with
    | .ok (b1, _), .ok (b2, _) => b1 = b2
    | .error e1, .error e2 => e1 = e2
    | _, _ => False := by
  induction c with
  | cmp op a b =>
    simp only [condUsesVar, Bool.or_eq_false_iff] at hnu
    have ha := evalE_dead_var_eq x a hnu.1 m l1 l2 hag
    have hb := evalE_dead_var_eq x b hnu.2 m l1 l2 hag
    rcases _root_.L.evalE_pure a ⟨m, l1⟩ with ⟨va1, ha1⟩ | ha1 <;>
    rcases _root_.L.evalE_pure a ⟨m, l2⟩ with ⟨va2, ha2⟩ | ha2 <;>
    simp only [ha1, ha2] at ha
    · subst ha
      rcases _root_.L.evalE_pure b ⟨m, l1⟩ with ⟨vb1, hb1⟩ | hb1 <;>
      rcases _root_.L.evalE_pure b ⟨m, l2⟩ with ⟨vb2, hb2⟩ | hb2 <;>
      simp only [hb1, hb2] at hb
      · subst hb
        simp only [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, ha1, ha2, hb1, hb2, Pure.pure, StateT.pure, Except.pure]
      · simp only [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, ha1, ha2, hb1, hb2]
    · simp only [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, ha1, ha2]
  | not p ih =>
    have hp := ih hnu
    rcases _root_.L.evalC_pure p ⟨m, l1⟩ with ⟨b1, h1⟩ | h1 <;>
    rcases _root_.L.evalC_pure p ⟨m, l2⟩ with ⟨b2, h2⟩ | h2 <;>
    simp only [h1, h2] at hp
    · subst hp
      simp only [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, h1, h2, Pure.pure, StateT.pure, Except.pure]
    · simp only [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, h1, h2]
  | and p q ihp ihq =>
    simp only [condUsesVar, Bool.or_eq_false_iff] at hnu
    have hp := ihp hnu.1; have hq := ihq hnu.2
    rcases _root_.L.evalC_pure p ⟨m, l1⟩ with ⟨b1, h1⟩ | h1 <;>
    rcases _root_.L.evalC_pure p ⟨m, l2⟩ with ⟨b2, h2⟩ | h2 <;>
    simp only [h1, h2] at hp
    · subst hp
      cases b1
      · simp only [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, h1, h2, Bool.false_eq_true, ↓reduceIte,
          Pure.pure, StateT.pure, Except.pure]
      · simp only [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, h1, h2, ↓reduceIte]
        exact hq
    · simp only [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, h1, h2]
  | or p q ihp ihq =>
    simp only [condUsesVar, Bool.or_eq_false_iff] at hnu
    have hp := ihp hnu.1; have hq := ihq hnu.2
    rcases _root_.L.evalC_pure p ⟨m, l1⟩ with ⟨b1, h1⟩ | h1 <;>
    rcases _root_.L.evalC_pure p ⟨m, l2⟩ with ⟨b2, h2⟩ | h2 <;>
    simp only [h1, h2] at hp
    · subst hp
      cases b1
      · simp only [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, h1, h2, Bool.false_eq_true, ↓reduceIte]
        exact hq
      · simp only [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, h1, h2, ↓reduceIte,
          Pure.pure, StateT.pure, Except.pure]
    · simp only [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, h1, h2]

private theorem evalArgs_dead_var_eq (x : Var) (es : List Expr) (hnu : es.any (exprUsesVar x) = false)
    (m : _root_.L.Mem) (l1 l2 : _root_.L.Locals) (hag : ∀ y, y ≠ x → l1 y = l2 y) :
    match _root_.L.evalArgs es ⟨m, l1⟩, _root_.L.evalArgs es ⟨m, l2⟩ with
    | .ok (vs1, _), .ok (vs2, _) => vs1 = vs2
    | .error e1, .error e2 => e1 = e2
    | _, _ => False := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at hnu
    have he := evalE_dead_var_eq x e hnu.1 m l1 l2 hag
    have hes := ih hnu.2
    rcases _root_.L.evalE_pure e ⟨m, l1⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure e ⟨m, l2⟩ with ⟨v2, h2⟩ | h2 <;>
    simp only [h1, h2] at he
    · subst he
      rcases _root_.L.evalArgs_pure es ⟨m, l1⟩ with ⟨vs1, hs1⟩ | hs1 <;>
      rcases _root_.L.evalArgs_pure es ⟨m, l2⟩ with ⟨vs2, hs2⟩ | hs2 <;>
      simp only [hs1, hs2] at hes
      · subst hes
        simp only [_root_.L.evalArgs, Bind.bind, StateT.bind, Except.bind, h1, h2, hs1, hs2,
          Pure.pure, StateT.pure, Except.pure]
      · simp only [_root_.L.evalArgs, Bind.bind, StateT.bind, Except.bind, h1, h2, hs1, hs2]
    · simp only [_root_.L.evalArgs, Bind.bind, StateT.bind, Except.bind, h1, h2]

private theorem warr_dead_var_eq (x : Var) (w : WArr) (hnu : warrUsesVar x w = false)
    (m : _root_.L.Mem) (l1 l2 : _root_.L.Locals) (hag : ∀ y, y ≠ x → l1 y = l2 y) :
    match _root_.L.warr w ⟨m, l1⟩, _root_.L.warr w ⟨m, l2⟩ with
    | .ok (a1, _), .ok (a2, _) => a1 = a2
    | .error e1, .error e2 => e1 = e2
    | _, _ => False := by
  cases w with
  | plain a => rfl
  | tier a t =>
    simp only [warrUsesVar] at hnu
    have ht := evalE_dead_var_eq x t hnu m l1 l2 hag
    rcases _root_.L.evalE_pure t ⟨m, l1⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure t ⟨m, l2⟩ with ⟨v2, h2⟩ | h2 <;>
    simp only [h1, h2] at ht
    · subst ht
      simp only [_root_.L.warr, Bind.bind, StateT.bind, Except.bind, h1, h2, Pure.pure, StateT.pure, Except.pure]
    · simp only [_root_.L.warr, Bind.bind, StateT.bind, Except.bind, h1, h2]

private theorem setLocs_mem (st : _root_.L.St) (xs : List Var) (vs : List _root_.L.Word) :
    (st.setLocs xs vs).mem = st.mem := by
  induction xs generalizing st vs with
  | nil => rfl
  | cons _ zs ih => exact ih _ vs.tail

private theorem setLocs_dead_var_eq (x : Var) (xs : List Var) (vs : List _root_.L.Word)
    (m : _root_.L.Mem) (l1 l2 : _root_.L.Locals) (hag : ∀ y, y ≠ x → l1 y = l2 y) :
    (∀ y, y ≠ x → (_root_.L.St.setLocs ⟨m, l1⟩ xs vs).loc y = (_root_.L.St.setLocs ⟨m, l2⟩ xs vs).loc y) ∧
    (x ∈ xs → (_root_.L.St.setLocs ⟨m, l1⟩ xs vs).loc x = (_root_.L.St.setLocs ⟨m, l2⟩ xs vs).loc x) := by
  induction xs generalizing l1 l2 vs with
  | nil => exact ⟨hag, fun h => by cases h⟩
  | cons z zs ih =>
    simp only [_root_.L.St.setLocs, _root_.L.St.setLoc]
    have hag' : ∀ y, y ≠ x →
        (fun w => if w = z then vs.headD 0 else l1 w) y =
        (fun w => if w = z then vs.headD 0 else l2 w) y := by
      intro y hy; dsimp only
      by_cases hyz : y = z
      · simp [hyz]
      · simp [hyz, hag y hy]
    have hrest := ih vs.tail _ _ hag'
    refine ⟨hrest.1, fun hmem => ?_⟩
    rcases List.mem_cons.mp hmem with rfl | htail
    · have hEq : (fun w => if w = x then vs.headD 0 else l1 w) = (fun w => if w = x then vs.headD 0 else l2 w) := by
        funext w
        by_cases hwx : w = x
        · simp [hwx]
        · simp [hwx, hag w hwx]
      rw [hEq]
    · exact hrest.2 htail

/-- Simultaneous liveness soundness for `execB` and `stackNeedB` on a single dead local `x`. -/
theorem execB_stackNeedB_dead_var_eq (p : Prog) (x : Var) :
    ∀ (b : Nat) (s : Stmt),
      (stmtVarLive x s).1 = false →
      ∀ (m : _root_.L.Mem) (l1 l2 : _root_.L.Locals),
        (∀ y, y ≠ x → l1 y = l2 y) →
        stackNeedB p b s ⟨m, l1⟩ = stackNeedB p b s ⟨m, l2⟩ ∧
        match execB p b s ⟨m, l1⟩, execB p b s ⟨m, l2⟩ with
        | .error e1, .error e2 => e1 = e2
        | .ok (sig1, st1', b1), .ok (sig2, st2', b2) =>
          sig1 = sig2 ∧ st1'.mem = st2'.mem ∧ b1 = b2 ∧
          (∀ y, y ≠ x → st1'.loc y = st2'.loc y) ∧
          (sig1 = .normal → (stmtVarLive x s).2 = true → st1'.loc x = st2'.loc x)
        | _, _ => False := by
  refine execB_ind (P := fun b s =>
      (stmtVarLive x s).1 = false →
      ∀ (m : _root_.L.Mem) (l1 l2 : _root_.L.Locals),
        (∀ y, y ≠ x → l1 y = l2 y) →
        stackNeedB p b s ⟨m, l1⟩ = stackNeedB p b s ⟨m, l2⟩ ∧
        match execB p b s ⟨m, l1⟩, execB p b s ⟨m, l2⟩ with
        | .error e1, .error e2 => e1 = e2
        | .ok (sig1, st1', b1), .ok (sig2, st2', b2) =>
          sig1 = sig2 ∧ st1'.mem = st2'.mem ∧ b1 = b2 ∧
          (∀ y, y ≠ x → st1'.loc y = st2'.loc y) ∧
          (sig1 = .normal → (stmtVarLive x s).2 = true → st1'.loc x = st2'.loc x)
        | _, _ => False) fun b s ih hnu m l1 l2 hag => ?_
  cases s with
  | skip =>
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    dsimp only [stmtVarLive]; rw [execB_skip, execB_skip]
    exact ⟨rfl, rfl, rfl, hag, fun _ h => by cases h⟩
  | brk =>
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    dsimp only [stmtVarLive]; rw [execB_brk, execB_brk]
    exact ⟨rfl, rfl, rfl, hag, fun h _ => by cases h⟩
  | set z e =>
    dsimp only [stmtVarLive] at hnu ⊢
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    have he := evalE_dead_var_eq x e hnu m l1 l2 hag
    rw [execB_set, execB_set]
    rcases _root_.L.evalE_pure e ⟨m, l1⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure e ⟨m, l2⟩ with ⟨v2, h2⟩ | h2
    · rw [h1, h2] at he ⊢; subst he
      refine ⟨rfl, rfl, rfl, fun y hy => ?_, fun _ hzx => ?_⟩
      · simp only [_root_.L.St.setLoc]
        by_cases hyz : y = z
        · simp [hyz]
        · simp [hyz, hag y hy]
      · simp only [beq_iff_eq] at hzx; subst hzx; simp [_root_.L.St.setLoc]
    · rw [h1, h2] at he; exact False.elim he
    · rw [h1, h2] at he; exact False.elim he
    · rw [h1, h2]
  | gset g e =>
    dsimp only [stmtVarLive] at hnu ⊢
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    have he := evalE_dead_var_eq x e hnu m l1 l2 hag
    rw [execB_gset, execB_gset]
    rcases _root_.L.evalE_pure e ⟨m, l1⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure e ⟨m, l2⟩ with ⟨v2, h2⟩ | h2
    · rw [h1, h2] at he ⊢; subst he; exact ⟨rfl, rfl, rfl, hag, fun _ h => by cases h⟩
    · rw [h1, h2] at he; exact False.elim he
    · rw [h1, h2] at he; exact False.elim he
    · rw [h1, h2]
  | abort e =>
    dsimp only [stmtVarLive] at hnu ⊢
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    have he := evalE_dead_var_eq x e hnu m l1 l2 hag
    rw [execB_abort, execB_abort]
    rcases _root_.L.evalE_pure e ⟨m, l1⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure e ⟨m, l2⟩ with ⟨v2, h2⟩ | h2
    · rw [h1, h2] at he ⊢; subst he; rfl
    · rw [h1, h2] at he; exact False.elim he
    · rw [h1, h2] at he; exact False.elim he
    · rw [h1, h2]
  | ret es =>
    dsimp only [stmtVarLive] at hnu ⊢
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    have hes := evalArgs_dead_var_eq x es hnu m l1 l2 hag
    rw [execB_ret, execB_ret]
    rcases _root_.L.evalArgs_pure es ⟨m, l1⟩ with ⟨vs1, h1⟩ | h1 <;>
    rcases _root_.L.evalArgs_pure es ⟨m, l2⟩ with ⟨vs2, h2⟩ | h2
    · rw [h1, h2] at hes ⊢; subst hes; exact ⟨rfl, rfl, rfl, hag, fun h _ => by cases h⟩
    · rw [h1, h2] at hes; exact False.elim hes
    · rw [h1, h2] at hes; exact False.elim hes
    · rw [h1, h2]
  | st8 a i e =>
    simp only [stmtVarLive, Bool.or_eq_false_iff] at hnu ⊢
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    have hi := evalE_dead_var_eq x i hnu.1 m l1 l2 hag
    have he := evalE_dead_var_eq x e hnu.2 m l1 l2 hag
    rw [execB_st8, execB_st8]
    rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨vi1, hi1⟩ | hi1 <;>
    rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨vi2, hi2⟩ | hi2 <;>
    simp only [hi1, hi2] at hi
    · subst hi
      rcases _root_.L.evalE_pure e ⟨m, l1⟩ with ⟨ve1, he1⟩ | he1 <;>
      rcases _root_.L.evalE_pure e ⟨m, l2⟩ with ⟨ve2, he2⟩ | he2 <;>
      simp only [he1, he2] at he
      · subst he
        simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi1, hi2, he1, he2,
          _root_.L.st8, get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set,
          Pure.pure, StateT.pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
        by_cases hb : vi1.toNat < (m.arr8 a).size
        · simp only [hb, ↓reduceIte]; exact ⟨rfl, rfl, rfl, hag, fun _ h => by cases h⟩
        · simp only [hb]; rfl
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi1, hi2, he1, he2]
    · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi1, hi2]
  | st64 a i e =>
    simp only [stmtVarLive, Bool.or_eq_false_iff] at hnu ⊢
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    have hi := evalE_dead_var_eq x i hnu.1 m l1 l2 hag
    have he := evalE_dead_var_eq x e hnu.2 m l1 l2 hag
    rw [execB_st64, execB_st64]
    rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨vi1, hi1⟩ | hi1 <;>
    rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨vi2, hi2⟩ | hi2 <;>
    simp only [hi1, hi2] at hi
    · subst hi
      rcases _root_.L.evalE_pure e ⟨m, l1⟩ with ⟨ve1, he1⟩ | he1 <;>
      rcases _root_.L.evalE_pure e ⟨m, l2⟩ with ⟨ve2, he2⟩ | he2 <;>
      simp only [he1, he2] at he
      · subst he
        simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi1, hi2, he1, he2,
          _root_.L.st64, get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set,
          Pure.pure, StateT.pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
        by_cases hb : vi1.toNat < (m.arr64 a).size
        · simp only [hb, ↓reduceIte]; exact ⟨rfl, rfl, rfl, hag, fun _ h => by cases h⟩
        · simp only [hb]; rfl
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi1, hi2, he1, he2]
    · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi1, hi2]
  | st64t a t i e =>
    simp only [stmtVarLive, Bool.or_eq_false_iff] at hnu ⊢
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    have ht := evalE_dead_var_eq x t hnu.1.1 m l1 l2 hag
    have hi := evalE_dead_var_eq x i hnu.1.2 m l1 l2 hag
    have he := evalE_dead_var_eq x e hnu.2 m l1 l2 hag
    rw [execB_st64t, execB_st64t]
    rcases _root_.L.evalE_pure t ⟨m, l1⟩ with ⟨vt1, ht1⟩ | ht1 <;>
    rcases _root_.L.evalE_pure t ⟨m, l2⟩ with ⟨vt2, ht2⟩ | ht2 <;>
    simp only [ht1, ht2] at ht
    · subst ht
      rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨vi1, hi1⟩ | hi1 <;>
      rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨vi2, hi2⟩ | hi2 <;>
      simp only [hi1, hi2] at hi
      · subst hi
        rcases _root_.L.evalE_pure e ⟨m, l1⟩ with ⟨ve1, he1⟩ | he1 <;>
        rcases _root_.L.evalE_pure e ⟨m, l2⟩ with ⟨ve2, he2⟩ | he2 <;>
        simp only [he1, he2] at he
        · subst he
          simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2, he1, he2,
            _root_.L.st64, get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set,
            Pure.pure, StateT.pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
          by_cases hb : vi1.toNat < (m.arr64 (tierA a vt1)).size
          · simp only [hb, ↓reduceIte]; exact ⟨rfl, rfl, rfl, hag, fun _ h => by cases h⟩
          · simp only [hb]; rfl
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2, he1, he2]
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2]
    · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht1, ht2]
  | st32t a t i e =>
    simp only [stmtVarLive, Bool.or_eq_false_iff] at hnu ⊢
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    have ht := evalE_dead_var_eq x t hnu.1.1 m l1 l2 hag
    have hi := evalE_dead_var_eq x i hnu.1.2 m l1 l2 hag
    have he := evalE_dead_var_eq x e hnu.2 m l1 l2 hag
    rw [execB_st32t, execB_st32t]
    rcases _root_.L.evalE_pure t ⟨m, l1⟩ with ⟨vt1, ht1⟩ | ht1 <;>
    rcases _root_.L.evalE_pure t ⟨m, l2⟩ with ⟨vt2, ht2⟩ | ht2 <;>
    simp only [ht1, ht2] at ht
    · subst ht
      rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨vi1, hi1⟩ | hi1 <;>
      rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨vi2, hi2⟩ | hi2 <;>
      simp only [hi1, hi2] at hi
      · subst hi
        rcases _root_.L.evalE_pure e ⟨m, l1⟩ with ⟨ve1, he1⟩ | he1 <;>
        rcases _root_.L.evalE_pure e ⟨m, l2⟩ with ⟨ve2, he2⟩ | he2 <;>
        simp only [he1, he2] at he
        · subst he
          simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2, he1, he2,
            _root_.L.st32, get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set,
            Pure.pure, StateT.pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
          by_cases hb : (vi1 / 2).toNat < (m.arr64 (tierA a vt1)).size
          · simp only [hb, ↓reduceIte]; exact ⟨rfl, rfl, rfl, hag, fun _ h => by cases h⟩
          · simp only [hb]; rfl
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2, he1, he2]
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2]
    · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht1, ht2]
  | copy64 d di src si n =>
    simp only [stmtVarLive, Bool.or_eq_false_iff] at hnu ⊢
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    have hd := warr_dead_var_eq x d hnu.1.1.1.1 m l1 l2 hag
    have hdi := evalE_dead_var_eq x di hnu.1.1.1.2 m l1 l2 hag
    have hs := warr_dead_var_eq x src hnu.1.1.2 m l1 l2 hag
    have hsi := evalE_dead_var_eq x si hnu.1.2 m l1 l2 hag
    have hn := evalE_dead_var_eq x n hnu.2 m l1 l2 hag
    rw [execB_copy64, execB_copy64]
    rcases _root_.L.warr_pure d ⟨m, l1⟩ with ⟨da1, hd1⟩ | hd1 <;>
    rcases _root_.L.warr_pure d ⟨m, l2⟩ with ⟨da2, hd2⟩ | hd2 <;>
    simp only [hd1, hd2] at hd
    · subst hd
      rcases _root_.L.evalE_pure di ⟨m, l1⟩ with ⟨vdi1, hdi1⟩ | hdi1 <;>
      rcases _root_.L.evalE_pure di ⟨m, l2⟩ with ⟨vdi2, hdi2⟩ | hdi2 <;>
      simp only [hdi1, hdi2] at hdi
      · subst hdi
        rcases _root_.L.warr_pure src ⟨m, l1⟩ with ⟨sa1, hs1⟩ | hs1 <;>
        rcases _root_.L.warr_pure src ⟨m, l2⟩ with ⟨sa2, hs2⟩ | hs2 <;>
        simp only [hs1, hs2] at hs
        · subst hs
          rcases _root_.L.evalE_pure si ⟨m, l1⟩ with ⟨vsi1, hsi1⟩ | hsi1 <;>
          rcases _root_.L.evalE_pure si ⟨m, l2⟩ with ⟨vsi2, hsi2⟩ | hsi2 <;>
          simp only [hsi1, hsi2] at hsi
          · subst hsi
            rcases _root_.L.evalE_pure n ⟨m, l1⟩ with ⟨vn1, hn1⟩ | hn1 <;>
            rcases _root_.L.evalE_pure n ⟨m, l2⟩ with ⟨vn2, hn2⟩ | hn2 <;>
            simp only [hn1, hn2] at hn
            · subst hn
              simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hd1, hd2, hdi1, hdi2, hs1, hs2, hsi1, hsi2, hn1, hn2,
                get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set,
                Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
              by_cases hb : vdi1.toNat + vn1.toNat ≤ (m.arr64 da1).size ∧ vsi1.toNat + vn1.toNat ≤ (m.arr64 sa1).size
              · simp only [hb]; exact ⟨rfl, rfl, rfl, hag, fun _ h => by cases h⟩
              · simp only [hb]; rfl
            · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hd1, hd2, hdi1, hdi2, hs1, hs2, hsi1, hsi2, hn1, hn2]
          · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hd1, hd2, hdi1, hdi2, hs1, hs2, hsi1, hsi2]
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hd1, hd2, hdi1, hdi2, hs1, hs2]
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hd1, hd2, hdi1, hdi2]
    · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hd1, hd2]
  | copy8w d di src si n =>
    simp only [stmtVarLive, Bool.or_eq_false_iff] at hnu ⊢
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    have hd := warr_dead_var_eq x d hnu.1.1.1 m l1 l2 hag
    have hdi := evalE_dead_var_eq x di hnu.1.1.2 m l1 l2 hag
    have hsi := evalE_dead_var_eq x si hnu.1.2 m l1 l2 hag
    have hn := evalE_dead_var_eq x n hnu.2 m l1 l2 hag
    rw [execB_copy8w, execB_copy8w]
    rcases _root_.L.warr_pure d ⟨m, l1⟩ with ⟨da1, hd1⟩ | hd1 <;>
    rcases _root_.L.warr_pure d ⟨m, l2⟩ with ⟨da2, hd2⟩ | hd2 <;>
    simp only [hd1, hd2] at hd
    · subst hd
      rcases _root_.L.evalE_pure di ⟨m, l1⟩ with ⟨vdi1, hdi1⟩ | hdi1 <;>
      rcases _root_.L.evalE_pure di ⟨m, l2⟩ with ⟨vdi2, hdi2⟩ | hdi2 <;>
      simp only [hdi1, hdi2] at hdi
      · subst hdi
        rcases _root_.L.evalE_pure si ⟨m, l1⟩ with ⟨vsi1, hsi1⟩ | hsi1 <;>
        rcases _root_.L.evalE_pure si ⟨m, l2⟩ with ⟨vsi2, hsi2⟩ | hsi2 <;>
        simp only [hsi1, hsi2] at hsi
        · subst hsi
          rcases _root_.L.evalE_pure n ⟨m, l1⟩ with ⟨vn1, hn1⟩ | hn1 <;>
          rcases _root_.L.evalE_pure n ⟨m, l2⟩ with ⟨vn2, hn2⟩ | hn2 <;>
          simp only [hn1, hn2] at hn
          · subst hn
            simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hd1, hd2, hdi1, hdi2, hsi1, hsi2, hn1, hn2,
              get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set,
              Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
            by_cases hb : vdi1.toNat + vn1.toNat ≤ (m.arr64 da1).size ∧ vsi1.toNat + vn1.toNat ≤ (m.src8 src).size
            · simp only [hb]; exact ⟨rfl, rfl, rfl, hag, fun _ h => by cases h⟩
            · simp only [hb]; rfl
          · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hd1, hd2, hdi1, hdi2, hsi1, hsi2, hn1, hn2]
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hd1, hd2, hdi1, hdi2, hsi1, hsi2]
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hd1, hd2, hdi1, hdi2]
    · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hd1, hd2]
  | scan8 z src i e c =>
    simp only [stmtVarLive, Bool.or_eq_false_iff] at hnu ⊢
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    have hi := evalE_dead_var_eq x i hnu.1 m l1 l2 hag
    have he := evalE_dead_var_eq x e hnu.2 m l1 l2 hag
    rw [execB_scan8, execB_scan8]
    rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨vi1, hi1⟩ | hi1 <;>
    rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨vi2, hi2⟩ | hi2 <;>
    simp only [hi1, hi2] at hi
    · subst hi
      rcases _root_.L.evalE_pure e ⟨m, l1⟩ with ⟨ve1, he1⟩ | he1 <;>
      rcases _root_.L.evalE_pure e ⟨m, l2⟩ with ⟨ve2, he2⟩ | he2 <;>
      simp only [he1, he2] at he
      · subst he
        simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi1, hi2, he1, he2,
          get, getThe, MonadStateOf.get, StateT.get, _root_.L.setLoc, modify, modifyGet,
          MonadStateOf.modifyGet, Pure.pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
        by_cases hb : vi1 ≤ ve1 ∧ ve1.toNat ≤ (m.src8 src).size
        · simp only [hb]
          refine ⟨rfl, rfl, rfl, fun y hy => ?_, fun _ hzx => ?_⟩
          · simp only [_root_.L.St.setLoc]
            by_cases hyz : y = z
            · simp [hyz]
            · simp [hyz, hag y hy]
          · simp only [beq_iff_eq] at hzx; subst hzx; simp [_root_.L.St.setLoc]
        · simp only [hb]; rfl
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi1, hi2, he1, he2]
    · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi1, hi2]
  | call xs f args =>
    simp only [stmtVarLive] at hnu ⊢
    have hargs := evalArgs_dead_var_eq x args hnu m l1 l2 hag
    rw [stackNeedB_call, stackNeedB_call, execB_call, execB_call]
    rcases _root_.L.evalArgs_pure args ⟨m, l1⟩ with ⟨vs1, h1⟩ | h1 <;>
    rcases _root_.L.evalArgs_pure args ⟨m, l2⟩ with ⟨vs2, h2⟩ | h2
    · rw [h1, h2] at hargs ⊢; subst hargs
      cases hlk : p.lookup f with
      | none => exact ⟨by cases b <;> rfl, rfl⟩
      | some fd =>
        cases b with
        | zero => exact ⟨rfl, rfl⟩
        | succ b' =>
          refine ⟨rfl, ?_⟩
          cases hx : execB p b' fd.body { mem := m, loc := Locals.init vs1 } with
          | error err => dsimp only; rw [hx]
          | ok res =>
            rcases res with ⟨sig, st2, b2⟩
            dsimp only; rw [hx]
            have hlocs := setLocs_dead_var_eq x xs sig.retVal st2.mem l1 l2 hag
            refine ⟨rfl, by simp only [setLocs_mem], rfl, hlocs.1, fun _ hmem => ?_⟩
            simp only [decide_eq_true_eq] at hmem
            exact hlocs.2 hmem
    · rw [h1, h2] at hargs; exact False.elim hargs
    · rw [h1, h2] at hargs; exact False.elim hargs
    · rw [h1, h2]; exact ⟨rfl, rfl⟩
  | seq s1 s2 =>
    simp only [stmtVarLive, Bool.or_eq_false_iff, Bool.and_eq_false_iff, Bool.not_eq_false'] at hnu ⊢
    have h1 := ih b s1 (execBRel_seq_left b s1 s2) hnu.1 m l1 l2 hag
    rw [stackNeedB_seq, stackNeedB_seq, execB_seq, execB_seq]
    cases hx1 : execB p b s1 ⟨m, l1⟩ with
    | error e1 =>
      cases hx2 : execB p b s1 ⟨m, l2⟩ with
      | error e2 => rw [hx1, hx2] at h1; exact ⟨h1.1, h1.2⟩
      | ok r2 => rw [hx1, hx2] at h1; exact False.elim h1.2
    | ok r1 =>
      rcases r1 with ⟨sig1, st1', b1⟩
      cases hx2 : execB p b s1 ⟨m, l2⟩ with
      | error e2 => rw [hx1, hx2] at h1; exact False.elim h1.2
      | ok r2 =>
        rcases r2 with ⟨sig2, st2', b2⟩
        rw [hx1, hx2] at h1
        rcases h1 with ⟨hsn1, rfl, hmemEq, rfl, hag1, hw1⟩
        cases sig1 with
        | brk => exact ⟨hsn1, ⟨rfl, hmemEq, rfl, hag1, fun h _ => by cases h⟩⟩
        | ret vs => exact ⟨hsn1, ⟨rfl, hmemEq, rfl, hag1, fun h _ => by cases h⟩⟩
        | normal =>
          rcases hnu.2 with hw1t | hr2f
          · have hlocEq : st1'.loc = st2'.loc := funext fun y =>
              if hy : y = x then hy ▸ hw1 rfl hw1t else hag1 y hy
            have hstEq : st1' = st2' := by cases st1'; cases st2'; simp only [St.mk.injEq] at *; exact ⟨hmemEq, hlocEq⟩
            rw [hstEq]
            refine ⟨by rw [hsn1], ?_⟩
            dsimp only
            cases hx2 : execB p b1 s2 st2' with
            | error _ => rfl
            | ok res => exact ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
          · have hbLe : b1 ≤ b := execB_fuel_le hx1
            have h2 := ih b1 s2 (execBRel_seq_right hbLe s1 s2) hr2f st1'.mem st1'.loc st2'.loc hag1
            have hst2Eq : (⟨st1'.mem, st2'.loc⟩ : _root_.L.St) = st2' := by cases st2'; simp only [St.mk.injEq]; exact ⟨hmemEq, trivial⟩
            rw [hst2Eq] at h2
            refine ⟨by dsimp only; rw [hsn1, h2.1], ?_⟩
            dsimp only
            cases hy1 : execB p b1 s2 st1' with
            | error e1 =>
              cases hy2 : execB p b1 s2 st2' with
              | error e2 => rw [hy1, hy2] at h2; exact h2.2
              | ok r2' => rw [hy1, hy2] at h2; exact False.elim h2.2
            | ok r1' =>
              rcases r1' with ⟨sig1', st1'', b1''⟩
              cases hy2 : execB p b1 s2 st2' with
              | error e2 => rw [hy1, hy2] at h2; exact False.elim h2.2
              | ok r2' =>
                rcases r2' with ⟨sig2', st2'', b2''⟩
                rw [hy1, hy2] at h2
                rcases h2.2 with ⟨rfl, hmem2, rfl, hag2, hw2⟩
                refine ⟨rfl, hmem2, rfl, hag2, fun hnorm hor => ?_⟩
                rw [Bool.or_eq_true] at hor
                rcases hor with hw1t | hw2t
                · have hlocEq : st1'.loc = st2'.loc := funext fun y =>
                    if hy : y = x then hy ▸ hw1 rfl hw1t else hag1 y hy
                  have hstEq : st1' = st2' := by cases st1'; cases st2'; simp only [St.mk.injEq]; exact ⟨hmemEq, hlocEq⟩
                  rw [hstEq, hy2] at hy1
                  have := Prod.mk.inj (Except.ok.inj hy1)
                  have := Prod.mk.inj this.2
                  rw [this.1]
                · exact hw2 hnorm hw2t
  | ite c s1 s2 =>
    simp only [stmtVarLive, Bool.or_eq_false_iff] at hnu ⊢
    have hc := evalC_dead_var_eq x c hnu.1.1 m l1 l2 hag
    rw [stackNeedB_ite, stackNeedB_ite, execB_ite, execB_ite]
    rcases _root_.L.evalC_pure c ⟨m, l1⟩ with ⟨bc1, hc1⟩ | hc1 <;>
    rcases _root_.L.evalC_pure c ⟨m, l2⟩ with ⟨bc2, hc2⟩ | hc2 <;>
    simp only [hc1, hc2] at hc
    · rw [hc1, hc2]; subst hc
      cases bc1
      · dsimp only
        have h2 := ih b s2 (execBRel_ite_right b c s1 s2) hnu.2 m l1 l2 hag
        refine ⟨h2.1, ?_⟩
        cases hy1 : execB p b s2 ⟨m, l1⟩ with
        | error e1 =>
          cases hy2 : execB p b s2 ⟨m, l2⟩ with
          | error e2 => rw [hy1, hy2] at h2; exact h2.2
          | ok _ => rw [hy1, hy2] at h2; exact False.elim h2.2
        | ok r1 =>
          rcases r1 with ⟨sig1, st1', b1⟩
          cases hy2 : execB p b s2 ⟨m, l2⟩ with
          | error _ => rw [hy1, hy2] at h2; exact False.elim h2.2
          | ok r2 =>
            rcases r2 with ⟨sig2, st2', b2⟩
            rw [hy1, hy2] at h2
            rcases h2.2 with ⟨rfl, hmem2, rfl, hag2, hw2⟩
            exact ⟨rfl, hmem2, rfl, hag2, fun hnorm hand => hw2 hnorm (Bool.and_eq_true _ _ |>.mp hand).2⟩
      · dsimp only
        have h1 := ih b s1 (execBRel_ite_left b c s1 s2) hnu.1.2 m l1 l2 hag
        refine ⟨h1.1, ?_⟩
        cases hy1 : execB p b s1 ⟨m, l1⟩ with
        | error e1 =>
          cases hy2 : execB p b s1 ⟨m, l2⟩ with
          | error e2 => rw [hy1, hy2] at h1; exact h1.2
          | ok _ => rw [hy1, hy2] at h1; exact False.elim h1.2
        | ok r1 =>
          rcases r1 with ⟨sig1, st1', b1⟩
          cases hy2 : execB p b s1 ⟨m, l2⟩ with
          | error _ => rw [hy1, hy2] at h1; exact False.elim h1.2
          | ok r2 =>
            rcases r2 with ⟨sig2, st2', b2⟩
            rw [hy1, hy2] at h1
            rcases h1.2 with ⟨rfl, hmem1, rfl, hag1, hw1⟩
            exact ⟨rfl, hmem1, rfl, hag1, fun hnorm hand => hw1 hnorm (Bool.and_eq_true _ _ |>.mp hand).1⟩
    · rw [hc1, hc2]; exact ⟨rfl, rfl⟩
  | «while» c body =>
    have hnuW := hnu
    simp only [stmtVarLive, Bool.or_eq_false_iff] at hnu ⊢
    have hc := evalC_dead_var_eq x c hnu.1 m l1 l2 hag
    rw [stackNeedB_while, stackNeedB_while, execB_while, execB_while]
    rcases _root_.L.evalC_pure c ⟨m, l1⟩ with ⟨bc1, hc1⟩ | hc1 <;>
    rcases _root_.L.evalC_pure c ⟨m, l2⟩ with ⟨bc2, hc2⟩ | hc2 <;>
    simp only [hc1, hc2] at hc
    · rw [hc1, hc2]; subst hc
      cases bc1
      · exact ⟨rfl, ⟨rfl, rfl, rfl, hag, fun _ h => by cases h⟩⟩
      · dsimp only
        have hb := ih b body (execBRel_while_body b c body) hnu.2 m l1 l2 hag
        cases hx1 : execB p b body ⟨m, l1⟩ with
        | error e1 =>
          cases hx2 : execB p b body ⟨m, l2⟩ with
          | error e2 => rw [hx1, hx2] at hb; exact ⟨hb.1, hb.2⟩
          | ok _ => rw [hx1, hx2] at hb; exact False.elim hb.2
        | ok r1 =>
          rcases r1 with ⟨sig1, st1', b1⟩
          cases hx2 : execB p b body ⟨m, l2⟩ with
          | error _ => rw [hx1, hx2] at hb; exact False.elim hb.2
          | ok r2 =>
            rcases r2 with ⟨sig2, st2', b2⟩
            rw [hx1, hx2] at hb
            rcases hb with ⟨hsnB, rfl, hmemB, rfl, hagB, _⟩
            cases sig1 with
            | brk => exact ⟨hsnB, ⟨rfl, hmemB, rfl, hagB, fun _ h => by cases h⟩⟩
            | ret vs => exact ⟨hsnB, ⟨rfl, hmemB, rfl, hagB, fun h _ => by cases h⟩⟩
            | normal =>
              cases b1 with
              | zero => exact ⟨hsnB, rfl⟩
              | succ b1' =>
                have hlt : b1' < b := by have := execB_fuel_le hx1; omega
                have hw := ih b1' (.while c body) (execBRel_while_next hlt c body) hnuW st1'.mem st1'.loc st2'.loc hagB
                have hst2Eq : (⟨st1'.mem, st2'.loc⟩ : _root_.L.St) = st2' := by cases st2'; simp only [St.mk.injEq]; exact ⟨hmemB, trivial⟩
                rw [hst2Eq] at hw
                exact ⟨by dsimp only; rw [hsnB, hw.1], hw.2⟩
    · rw [hc1, hc2]; exact ⟨rfl, rfl⟩

private def patchLocals (l1 l2 : _root_.L.Locals) : List Var → _root_.L.Locals
  | [] => l1
  | x :: xs => fun y => if y = x then l2 x else patchLocals l1 l2 xs y

private theorem patchLocals_eq_right (l1 l2 : _root_.L.Locals) (xs : List Var)
    (hag : ∀ y, y ∉ xs → l1 y = l2 y) : patchLocals l1 l2 xs = l2 := by
  induction xs generalizing l1 with
  | nil => funext y; exact hag y (by simp)
  | cons x xs ih =>
    funext y
    simp only [patchLocals]
    by_cases hyx : y = x
    · subst hyx; simp
    · simp only [hyx, ↓reduceIte]
      have h1 : ∀ z, z ∉ xs → (fun w => if w = x then l2 x else l1 w) z = l2 z := by
        intro z hz; dsimp only
        by_cases hzx : z = x
        · subst hzx; simp
        · simp only [hzx, ↓reduceIte]; exact hag z (by simp [hzx, hz])
      have h2 := congrFun (ih (fun w => if w = x then l2 x else l1 w) h1) y
      have hpatch : ∀ (l1' l1'' : _root_.L.Locals) (zs : List Var) (w : Var),
          (∀ u, u ≠ x → l1' u = l1'' u) → w ≠ x → patchLocals l1' l2 zs w = patchLocals l1'' l2 zs w := by
        intro l1' l1'' zs; induction zs with
        | nil => intro w h hne; exact h w hne
        | cons z zs' ihz =>
          intro w h hne; simp only [patchLocals]
          by_cases hwz : w = z
          · simp [hwz]
          · simp [hwz, ihz w h hne]
      rw [hpatch l1 (fun w => if w = x then l2 x else l1 w) xs y (fun u hu => by simp [hu]) hyx]
      exact h2

/-- Multi-variable liveness soundness: differing arbitrarily on dead locals `xs` preserves
    both `stackNeedB` and the return signal/memory/fuel of `execB`. -/
theorem execB_stackNeedB_dead_vars_eq (p : Prog) (b : Nat) (s : Stmt) (m : _root_.L.Mem)
    (xs : List Var) (hdead : ∀ x ∈ xs, (stmtVarLive x s).1 = false)
    (l1 l2 : _root_.L.Locals) (hag : ∀ y, y ∉ xs → l1 y = l2 y) :
    stackNeedB p b s ⟨m, l1⟩ = stackNeedB p b s ⟨m, l2⟩ ∧
    match execB p b s ⟨m, l1⟩, execB p b s ⟨m, l2⟩ with
    | .error e1, .error e2 => e1 = e2
    | .ok (sig1, st1', b1), .ok (sig2, st2', b2) =>
      sig1 = sig2 ∧ st1'.mem = st2'.mem ∧ b1 = b2
    | _, _ => False := by
  have haux : ∀ (zs : List Var), (∀ x ∈ zs, (stmtVarLive x s).1 = false) →
      stackNeedB p b s ⟨m, l1⟩ = stackNeedB p b s ⟨m, patchLocals l1 l2 zs⟩ ∧
      match execB p b s ⟨m, l1⟩, execB p b s ⟨m, patchLocals l1 l2 zs⟩ with
      | .error e1, .error e2 => e1 = e2
      | .ok (sig1, st1', b1), .ok (sig2, st2', b2) =>
        sig1 = sig2 ∧ st1'.mem = st2'.mem ∧ b1 = b2
      | _, _ => False := by
    intro zs hdz
    induction zs with
    | nil =>
      refine ⟨rfl, ?_⟩
      cases hx : execB p b s ⟨m, l1⟩ with
      | error _ => dsimp only [patchLocals]; rw [hx]
      | ok _ => dsimp only [patchLocals]; rw [hx]; exact ⟨rfl, rfl, rfl⟩
    | cons x zs' ih =>
      have h1 := ih (fun z hz => hdz z (List.mem_cons_of_mem x hz))
      have hstep := execB_stackNeedB_dead_var_eq p x b s (hdz x (List.mem_cons_self ..))
        m (patchLocals l1 l2 zs') (patchLocals l1 l2 (x :: zs'))
        (fun y hy => by simp [patchLocals, hy])
      refine ⟨h1.1.trans hstep.1, ?_⟩
      cases hA : execB p b s ⟨m, l1⟩ with
      | error e1 =>
        cases hB : execB p b s ⟨m, patchLocals l1 l2 zs'⟩ with
        | error e2 =>
          cases hC : execB p b s ⟨m, patchLocals l1 l2 (x :: zs')⟩ with
          | error e3 =>
            rw [hA, hB] at h1; rw [hB, hC] at hstep; exact h1.2.trans hstep.2
          | ok _ => rw [hB, hC] at hstep; exact False.elim hstep.2
        | ok _ => rw [hA, hB] at h1; exact False.elim h1.2
      | ok r1 =>
        rcases r1 with ⟨sig1, st1', b1⟩
        cases hB : execB p b s ⟨m, patchLocals l1 l2 zs'⟩ with
        | error _ => rw [hA, hB] at h1; exact False.elim h1.2
        | ok r2 =>
          rcases r2 with ⟨sig2, st2', b2⟩
          cases hC : execB p b s ⟨m, patchLocals l1 l2 (x :: zs')⟩ with
          | error _ => rw [hB, hC] at hstep; exact False.elim hstep.2
          | ok r3 =>
            rcases r3 with ⟨sig3, st3', b3⟩
            rw [hA, hB] at h1; rw [hB, hC] at hstep
            exact ⟨h1.2.1.trans hstep.2.1, h1.2.2.1.trans hstep.2.2.1, h1.2.2.2.trans hstep.2.2.2.1⟩
  have hres := haux xs hdead
  rwa [patchLocals_eq_right l1 l2 xs hag] at hres

/-! ## 2. Frame Preservation & Store-Operand / WArr Helpers -/

theorem ProgFrameOkR.of_mem_outside_stack {tab : Tab} {L : ProgLayout tab} {fl : FrameLayout}
    (hfl : FrameLayoutOk fl) {sp : BitVec 64} {st1 st2 : State} {loc : _root_.L.Locals}
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (s : MemSpan) (hdisj : MemDisjoint s L.stackSpan)
    (hpres : PreservedFrameRegs fl (fun _ => False) st1 st2)
    (heq : MemEqOutside s st1.mem st2.mem)
    (hf : ProgFrameOkR L fl sp st1 loc) : ProgFrameOkR L fl sp st2 loc := by
  have hvalid : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  intro x hx
  have hfx := hf x hx
  cases hl : fl.alloc.lookup x with
  | some r =>
    rw [hl] at hfx; dsimp only at hfx ⊢
    have hmem := (regAllocValid_lookup hfl.valid hl).2.1
    rw [hpres.regs r (allowedRegs_sub_true hmem) (by intro h; cases h), hfx]
  | none =>
    rw [hl] at hfx; dsimp only at hfx ⊢
    intro hmx
    have hsi := hfl.spillIdx_lt hmx
    rw [← hfx hmx, varSlotOff_ofInt]
    apply MemEqOutside.readWord64_eq heq
    intro k hk
    apply hdisj.symm
    apply frameSpanR_sub_stackSpan L hlo hhi
    refine ⟨8 * (fl.protectedSlots + fl.spillIdx x) + k, ?_, ?_⟩
    · dsimp only [frameSpanR, FrameLayout.frameSlots]; omega
    · dsimp only [frameSpanR]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]

def warrUsedTemps : _root_.L.WArr → Nat
  | .plain _ => 0
  | .tier _ t => usedTempsExpr t

theorem reg_evalWArrTierToTempR_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (w : _root_.L.WArr) (hwOk : warrOkB env.tab fl.nlocals w = true)
    (hVf : WArrVarsInFrame fl w)
    (tmp : Nat)
    (htmp : tmp + max 1 (warrUsedTemps w) ≤ fl.usedTemps)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ (evalWArrTierToTempR env.tab fl tmp w).2 ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOkR L fl sp st loc) :
    let daCode := evalWArrTierToTempR env.tab fl tmp w
    match _root_.L.warr w ⟨lm, loc⟩ with
    | .ok (da, _) =>
      ∃ k st' u,
        RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize daCode.2)) ∧
        da = _root_.L.tierA daCode.1 u ∧
        env.tab.wordPosOkB da = true ∧
        (L.T + (if (u &&& 1 == 0) = true then 0#64 else 8#64) +
            BitVec.ofInt 64 (env.tab.len64 (.t0 daCode.1)) =
            L.T + BitVec.ofInt 64 (env.tab.len64 da)) ∧
        (L.T + (if (u &&& 1 == 0) = true then 0#64 else 8#64) +
            BitVec.ofInt 64 (env.tab.base64 (.t0 daCode.1)) =
            L.T + BitVec.ofInt 64 (env.tab.base64 da)) ∧
        readWord64 st'.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff tmp)) = u.toBitVec ∧
        PreservedFrameRegs fl (fun _ => False) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem
    | .error _ =>
      ∃ k st',
        RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (fun _ => False) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
  have hvalid : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  cases w with
  | plain a =>
    dsimp only [evalWArrTierToTempR, _root_.L.warr, warrOkB, warrUsedTemps] at hwOk htmp hlink ⊢
    have halX : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (fl.tempSlotOff tmp)) 8 = true := by
      rw [hsp, tempSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hspAlign _
    have hpc64 := linkResolved_sub_pc64 env pre _ post hlink
    obtain ⟨st', hrun, hoth, hmem, hpc'⟩ :=
      storeMemOff_sd_correct_lm lkm env.hrom pre post AbiReg.sp AbiReg.zero AbiReg.t0
        (by decide) (by decide) (by decide) (fl.tempSlotOff tmp) hlink hpc64 st hpc halX
    have hout : MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
      rw [hmem, hsp, tempSlotOff_ofInt]
      exact MemEqOutside.writeWord64 st.mem _ _ fun k hk =>
        tempSlotSpanR_sub_tempSpanR fl sp hvalid (Nat.le_refl tmp) (by omega) _ ⟨k, hk, rfl⟩
    have h0eq : (0 : _root_.L.Word) &&& 1 = 0 := by decide
    have hta0 : _root_.L.tierA a 0 = .t0 a := by simp [_root_.L.tierA, h0eq]
    have hslot0 : readWord64 st'.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff tmp)) = (0 : _root_.L.Word).toBitVec := by
      rw [hmem, hsp, getReg_zero]; exact readWord64_writeWord64_self _ _ _
    simp only [Pure.pure, Except.pure, StateT.pure]
    refine ⟨_, st', 0, hrun, hpc', hta0.symm, hwOk, ?_, ?_, hslot0,
      PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hoth, hout⟩
    · simp only [h0eq, beq_self_eq_true, ↓reduceIte, BitVec.add_zero]
    · simp only [h0eq, beq_self_eq_true, ↓reduceIte, BitVec.add_zero]
  | tier a t =>
    simp only [evalWArrTierToTempR, warrOkB, warrUsedTemps, Bool.and_eq_true] at hwOk htmp hlink ⊢
    cases hrt : exprReg? fl.alloc t with
    | some rt =>
      simp only [hrt] at hlink ⊢
      obtain ⟨hrtMem, _, u, hu, hgrt⟩ := reg_exprReg_sim (lm := lm) hfl hf hwOk.2 hrt
      have hrt0 : rt ≠ AbiReg.t0 := exprReg_ne_scratch hrtMem (by decide)
      have halX : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (fl.tempSlotOff tmp)) 8 = true := by
        rw [hsp, tempSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hspAlign _
      have hpc64 := linkResolved_sub_pc64 env pre _ post hlink
      obtain ⟨st', hrun, hoth, hmem, hpc'⟩ :=
        storeMemOff_sd_correct_lm lkm env.hrom pre post AbiReg.sp rt AbiReg.t0
          (by decide) (by decide) hrt0.symm (fl.tempSlotOff tmp) hlink hpc64 st hpc halX
      have hout : MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
        rw [hmem, hsp, tempSlotOff_ofInt]
        exact MemEqOutside.writeWord64 st.mem _ _ fun k hk =>
          tempSlotSpanR_sub_tempSpanR fl sp hvalid (Nat.le_refl tmp) (by omega) _ ⟨k, hk, rfl⟩
      have hmini : _root_.L.warr (.tier a t) ⟨lm, loc⟩ = .ok (_root_.L.tierA a u, ⟨lm, loc⟩) := by
        simp [_root_.L.warr, Bind.bind, StateT.bind, Except.bind, hu, Pure.pure, Except.pure, StateT.pure]
      rw [hmini]
      have hta := tieredOk_len64_addr_T L.T a u hwOk.1
      exact ⟨_, st', u, hrun, hpc', rfl, hta.1, hta.2.1, hta.2.2,
        by rw [hmem, hsp, hgrt]; exact readWord64_writeWord64_self _ _ _,
        PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hoth, hout⟩
    | none =>
      simp only [hrt] at hlink ⊢
      let ce := compileETo env.tab fl tmp AbiReg.a0 t
      let cs := storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp)
      have hpc64 := linkResolved_sub_pc64 env pre (ce ++ cs) post hlink
      have htw_all : lkm.totalSize (ce ++ cs) = lkm.totalSize ce + lkm.totalSize cs := lkm.totalSize_append ce cs
      have re := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi t pre (cs ++ post) tmp
        AbiReg.a0 (Or.inl rfl) hwOk.2 (fun x hx => hVf x (by simp [warrUsesVar, hx])) (by omega)
        (by simpa only [ce, cs, List.append_assoc] using hlink)
        (by rw [htw_all] at hpc64; dsimp only [ce] at hpc64; omega) st hpc hgp ht5 hsp hm hf
      rcases _root_.L.evalE_pure t ⟨lm, loc⟩ with ⟨u, hu⟩ | hu
      · simp only [hu] at re
        obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := re
        have htw1 : lkm.totalSize (pre ++ ce) = lkm.totalSize pre + lkm.totalSize ce := lkm.totalSize_append pre ce
        have halS : isAligned (st1.getReg AbiReg.sp + BitVec.ofInt 64 (fl.tempSlotOff tmp)) 8 = true := by
          rw [hpres1.abi.sp.trans hsp, tempSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hspAlign _
        obtain ⟨st2, hrunS, hothS, hmemS, hpc2⟩ :=
          storeMemOff_sd_correct_lm lkm env.hrom (pre ++ ce) post AbiReg.sp AbiReg.a0 AbiReg.t0
            (by decide) (by decide) (by decide) (fl.tempSlotOff tmp)
            (by simpa only [ce, cs, List.append_assoc] using hlink)
            (by rw [htw1]; rw [htw_all] at hpc64; dsimp only [cs] at hpc64 ⊢; omega) st1 (by rw [htw1]; exact hpc1) halS
        have heqS : MemEqOutside (tempSpanR fl sp tmp) st1.mem st2.mem := by
          rw [hmemS, hpres1.abi.sp.trans hsp, tempSlotOff_ofInt]
          exact MemEqOutside.writeWord64 st1.mem _ _ fun k hk =>
            tempSlotSpanR_sub_tempSpanR fl sp hvalid (Nat.le_refl tmp) (by omega) _ ⟨k, hk, rfl⟩
        have hmini : _root_.L.warr (.tier a t) ⟨lm, loc⟩ = .ok (_root_.L.tierA a u, ⟨lm, loc⟩) := by
          simp [_root_.L.warr, Bind.bind, StateT.bind, Except.bind, hu, Pure.pure, Except.pure, StateT.pure]
        rw [hmini]
        have hta := tieredOk_len64_addr_T L.T a u hwOk.1
        exact ⟨k1 + lkm.totalSize cs, st2, u,
          by rw [run_add, hrun1]; dsimp only; exact hrunS,
          by rw [hpc2, htw1, htw_all]; dsimp only [cs]; congr 2; omega,
          rfl, hta.1, hta.2.1, hta.2.2,
          by rw [hmemS, hpres1.abi.sp.trans hsp, ha0_1]; exact readWord64_writeWord64_self _ _ _,
          (PreservedFrameRegs.of_a0 hpres1).trans (PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hothS),
          heq1.trans heqS⟩
      · simp only [hu] at re
        obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := re
        have hmini : _root_.L.warr (.tier a t) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.warr, Bind.bind, StateT.bind, Except.bind, hu]
        rw [hmini]
        exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩

/-- Helper: register in `{zero, a0, t0, t3} ∪ allowedRegs` is never in `{t1, t2, t4, t6}`. -/
theorem storeReg_ne_scratch {r : Reg}
    (hr : r = AbiReg.zero ∨ r = AbiReg.a0 ∨ r = AbiReg.t0 ∨ r = AbiReg.t3 ∨ r ∈ allowedRegs true)
    {q : Reg} (hq : q ∈ [AbiReg.t1, AbiReg.t2, AbiReg.t4, AbiReg.t6, AbiReg.s1]) : r ≠ q := by
  rcases hr with rfl | rfl | rfl | rfl | hmem
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
  · apply allowedRegs_disj_reserved true hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide

theorem tierValReg_ne_scratch {r : Reg}
    (hr : r = AbiReg.zero ∨ r = AbiReg.a0 ∨ r = AbiReg.t3 ∨ r ∈ allowedRegs true)
    {q : Reg} (hq : q ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t4, AbiReg.t6, AbiReg.s1]) : r ≠ q := by
  rcases hr with rfl | rfl | rfl | hmem
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · apply allowedRegs_disj_reserved true hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem reg_compileStorePairR_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (i e : Expr) (pre post : List AsmItem)
    (hiOk : exprOkB env.tab fl.nlocals i = true)
    (heOk : exprOkB env.tab fl.nlocals e = true)
    (hVfI : ExprVarsInFrame fl i) (hVfE : ExprVarsInFrame fl e)
    (hTmp : (if isSimpleExpr i then usedTempsExpr e
             else if isSimpleExpr e then usedTempsExpr i
             else max (usedTempsExpr i) (1 + usedTempsExpr e)) ≤ fl.usedTemps)
    (hlink : lkm.linkSpec (pre ++ (compileStorePairR env.tab fl i e).1 ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    let res := compileStorePairR env.tab fl i e
    (res.2.1 = AbiReg.zero ∨ res.2.1 = AbiReg.a0 ∨ res.2.1 = AbiReg.t0 ∨ res.2.1 ∈ allowedRegs true) ∧
    (res.2.2 = AbiReg.zero ∨ res.2.2 = AbiReg.a0 ∨ res.2.2 = AbiReg.t0 ∨ res.2.2 ∈ allowedRegs true) ∧
    match _root_.L.evalE i ⟨lm, loc⟩ with
    | .ok (vi, _) =>
      match _root_.L.evalE e ⟨lm, loc⟩ with
      | .ok (ve, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize res.1)) ∧
          st'.getReg res.2.1 = vi.toBitVec ∧
          st'.getReg res.2.2 = ve.toBitVec ∧
          PreservedFrameRegs fl (fun _ => False) st st' ∧
          MemEqOutside (tempSpanR fl sp 0) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedFrameRegs fl (fun _ => False) st st' ∧
          MemEqOutside (tempSpanR fl sp 0) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (fun _ => False) st st' ∧
        MemEqOutside (tempSpanR fl sp 0) st.mem st'.mem := by
  have hvalid : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  have h64 := linkResolved_sub_pc64 env pre (compileStorePairR env.tab fl i e).1 post hlink
  have hTmpI : usedTempsExpr i ≤ fl.usedTemps := by
    cases hsi : isSimpleExpr i
    · cases hse : isSimpleExpr e <;> simp only [hsi, hse, Bool.false_eq_true, ↓reduceIte] at hTmp <;> omega
    · rw [usedTempsExpr_of_isSimple hsi]; exact Nat.zero_le _
  have hTmpE : usedTempsExpr e ≤ fl.usedTemps := by
    cases hsi : isSimpleExpr i
    · cases hse : isSimpleExpr e
      · simp only [hsi, hse, Bool.false_eq_true, ↓reduceIte] at hTmp; omega
      · rw [usedTempsExpr_of_isSimple hse]; exact Nat.zero_le _
    · simp only [hsi, ↓reduceIte] at hTmp; exact hTmp
  cases hri : exprReg? fl.alloc i with
  | some ri =>
    obtain ⟨hriMem, _, vi, hvi, hgri⟩ := reg_exprReg_sim (lm := lm) hfl hframeOk hiOk hri
    have hriW : ri = AbiReg.zero ∨ ri = AbiReg.a0 ∨ ri = AbiReg.t0 ∨ ri ∈ allowedRegs true := by
      rcases hriMem with rfl | hm; exact Or.inl rfl; exact Or.inr (Or.inr (Or.inr hm))
    cases hre : exprReg? fl.alloc e with
    | some re =>
      obtain ⟨hreMem, _, ve, hve, hgre⟩ := reg_exprReg_sim (lm := lm) hfl hframeOk heOk hre
      have hreW : re = AbiReg.zero ∨ re = AbiReg.a0 ∨ re = AbiReg.t0 ∨ re ∈ allowedRegs true := by
        rcases hreMem with rfl | hm; exact Or.inl rfl; exact Or.inr (Or.inr (Or.inr hm))
      simp only [compileStorePairR, hri, hre, hvi, hve]
      exact ⟨hriW, hreW, 0, st, rfl, by rw [lkm.totalSize_nil, Nat.add_zero]; exact hpc,
        hgri, hgre, PreservedFrameRegs.refl _ _ _, MemEqOutside.refl _ _⟩
    | none =>
      simp only [compileStorePairR, hri, hre] at hlink h64 ⊢
      refine ⟨hriW, by simp, ?_⟩
      rw [hvi]
      have reSim := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi e pre post 0 AbiReg.a0 (Or.inl rfl)
        heOk hVfE (by omega) hlink h64 st hpc hgp ht5 hsp hmemRel hframeOk
      rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨ve, hve⟩ | hve
      · simp only [hve] at reSim ⊢
        obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := reSim
        exact ⟨k1, st1, hrun1, hpc1, (hpres1.getReg_of_exprReg hriMem).trans hgri, ha0_1,
          PreservedFrameRegs.of_a0 hpres1, heq1⟩
      · simp only [hve] at reSim ⊢
        obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := reSim
        exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
  | none =>
    cases hre : exprReg? fl.alloc e with
    | some re =>
      obtain ⟨hreMem, _, ve, hve, hgre⟩ := reg_exprReg_sim (lm := lm) hfl hframeOk heOk hre
      have hreW : re = AbiReg.zero ∨ re = AbiReg.a0 ∨ re = AbiReg.t0 ∨ re ∈ allowedRegs true := by
        rcases hreMem with rfl | hm; exact Or.inl rfl; exact Or.inr (Or.inr (Or.inr hm))
      simp only [compileStorePairR, hri, hre] at hlink h64 ⊢
      refine ⟨by simp, hreW, ?_⟩
      have riSim := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi i pre post 0 AbiReg.a0 (Or.inl rfl)
        hiOk hVfI (by omega) hlink h64 st hpc hgp ht5 hsp hmemRel hframeOk
      rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
      · simp only [hvi] at riSim ⊢; rw [hve]
        obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := riSim
        exact ⟨k1, st1, hrun1, hpc1, ha0_1, (hpres1.getReg_of_exprReg hreMem).trans hgre,
          PreservedFrameRegs.of_a0 hpres1, heq1⟩
      · simp only [hvi] at riSim ⊢
        obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := riSim
        exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
    | none =>
      cases hsi : emitSimpleExprR env.tab fl AbiReg.t0 AbiReg.t1 i with
      | some ci =>
        simp only [compileStorePairR, hri, hre, hsi] at hlink h64 ⊢
        refine ⟨by simp, by simp, ?_⟩
        have htw_all : lkm.totalSize (compileETo env.tab fl 0 AbiReg.a0 e ++ ci) =
            lkm.totalSize (compileETo env.tab fl 0 AbiReg.a0 e) + lkm.totalSize ci := lkm.totalSize_append _ _
        have reSim := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi e pre (ci ++ post) 0
          AbiReg.a0 (Or.inl rfl) heOk hVfE (by omega)
          (by simpa only [List.append_assoc] using hlink)
          (by rw [htw_all] at h64; omega) st hpc hgp ht5 hsp hmemRel hframeOk
        have hPureI : ∃ vi, _root_.L.evalE i ⟨lm, loc⟩ = .ok (vi, ⟨lm, loc⟩) := by
          cases i with
          | const w => exact ⟨w, rfl⟩
          | var x => exact ⟨loc x, rfl⟩
          | len8 a => exact ⟨UInt64.ofNat (lm.arr8 a).size, rfl⟩
          | len64 a => exact ⟨UInt64.ofNat (lm.arr64 (.t0 a)).size, rfl⟩
          | glob g => exact ⟨lm.glob g, rfl⟩
          | _ => simp [emitSimpleExprR] at hsi
        obtain ⟨vi, hvi⟩ := hPureI
        rw [hvi]
        rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨ve, hve⟩ | hve
        · simp only [hve] at reSim ⊢
          obtain ⟨ke, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := reSim
          have htw1 : lkm.totalSize (pre ++ compileETo env.tab fl 0 AbiReg.a0 e) =
              lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl 0 AbiReg.a0 e) := lkm.totalSize_append _ _
          obtain ⟨vi', ki, st2, hvi', hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
            reg_emitSimpleExprR_sim env L fl hfl lm loc hspAlign
              (pre ++ compileETo env.tab fl 0 AbiReg.a0 e) post
              AbiReg.t0 AbiReg.t1 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide) i ci hsi hiOk hVfI
              (by simpa only [List.append_assoc] using hlink)
              (by rw [htw1]; rw [htw_all] at h64; omega) st1 (by rw [htw1]; exact hpc1)
              (hpres1.abi.gp.trans hgp) (ht5.of_preserved hpres1) (hpres1.abi.sp.trans hsp)
              (ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) heq1 hmemRel)
              (ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) hpres1 heq1 hframeOk)
          rw [hvi] at hvi'
          have hviEq : vi = vi' := (Prod.mk.inj (Except.ok.inj hvi')).1
          subst hviEq
          exact ⟨ke + ki, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
            by rw [hpc2, htw1, htw_all]; congr 2; omega, ht0_2,
            (hoth2 AbiReg.a0 (by decide) (by decide)).trans ha0_1,
            (PreservedFrameRegs.of_a0 hpres1).trans (PreservedFrameRegs.of_scratch2 AbiReg.t0 AbiReg.t1 (by decide) (by decide) hoth2),
            by rw [hmem2]; exact heq1⟩
        · simp only [hve] at reSim ⊢
          obtain ⟨ke, st1, hrun1, hpc1, hpres1, heq1⟩ := reSim
          exact ⟨ke, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
      | none =>
        cases hse : emitSimpleExprR env.tab fl AbiReg.a0 AbiReg.t1 e with
        | some ce =>
          simp only [compileStorePairR, hri, hre, hsi, hse] at hlink h64 ⊢
          refine ⟨by simp, by simp, ?_⟩
          have htw_all : lkm.totalSize (compileETo env.tab fl 0 AbiReg.a0 i ++ [Asm.mv AbiReg.t0 AbiReg.a0] ++ ce) =
              lkm.totalSize (compileETo env.tab fl 0 AbiReg.a0 i) + 1 + lkm.totalSize ce := by
            simp only [lkm.totalSize_append, Asm.mv, lkm.totalSize_instr]
          have riSim := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi i pre
            (([Asm.mv AbiReg.t0 AbiReg.a0] ++ ce) ++ post) 0 AbiReg.a0 (Or.inl rfl) hiOk hVfI (by omega)
            (by simpa only [List.append_assoc] using hlink)
            (by rw [htw_all] at h64; omega) st hpc hgp ht5 hsp hmemRel hframeOk
          rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
          · simp only [hvi] at riSim ⊢
            obtain ⟨ki, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := riSim
            have htw1 : lkm.totalSize (pre ++ compileETo env.tab fl 0 AbiReg.a0 i) =
                lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl 0 AbiReg.a0 i) := lkm.totalSize_append _ _
            have hsMv := step_item_instr_lm lkm env.hrom (pre ++ compileETo env.tab fl 0 AbiReg.a0 i) (ce ++ post)
              (.aluImm .addi AbiReg.t0 AbiReg.a0 0#12)
              (by simpa only [Asm.mv, List.append_assoc] using hlink)
              (by rw [htw1]; rw [htw_all] at h64; omega) st1 (by rw [htw1]; exact hpc1)
            let st2 := stepReg st1 AbiReg.t0 (st1.getReg AbiReg.a0) (st1.pc + 4#64)
            have hrun2 : RV64.run env.rom 1 st1 = .cont st2 :=
              run_one_cont _ _ st2 (by rw [hsMv]; simp only [execInstr, evalAluImm, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero]; rfl)
            have htw2 : lkm.totalSize (pre ++ compileETo env.tab fl 0 AbiReg.a0 i ++ [Asm.mv AbiReg.t0 AbiReg.a0]) =
                lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl 0 AbiReg.a0 i) + 1 := by
              rw [lkm.totalSize_append, htw1, Asm.mv, lkm.totalSize_instr]
            have hpc2 : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ compileETo env.tab fl 0 AbiReg.a0 i ++ [Asm.mv AbiReg.t0 AbiReg.a0])) := by
              change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1, htw2]
            have hpres2 : PreservedFrameRegs fl (fun _ => False) st1 st2 :=
              PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) (fun r hr => getReg_stepReg_ne st1 AbiReg.t0 r hr _ _)
            have hpres02 : PreservedFrameRegs fl (fun _ => False) st st2 := (PreservedFrameRegs.of_a0 hpres1).trans hpres2
            have hmem2 : st2.mem = st1.mem := mem_stepReg st1 _ _ _
            obtain ⟨ve, ke, st3, hve, hrun3, hpc3, ha0_3, hoth3, hmem3⟩ :=
              reg_emitSimpleExprR_sim env L fl hfl lm loc hspAlign
                (pre ++ compileETo env.tab fl 0 AbiReg.a0 i ++ [Asm.mv AbiReg.t0 AbiReg.a0]) post
                AbiReg.a0 AbiReg.t1 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide) e ce hse heOk hVfE
                (by simpa only [List.append_assoc] using hlink)
                (by rw [htw2]; rw [htw_all] at h64; omega) st2 hpc2
                (hpres02.abi.gp.trans hgp) (ht5.of_preserved hpres02) (hpres02.abi.sp.trans hsp)
                (by rw [hmem2]; exact ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) heq1 hmemRel)
                (ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) (hpres02.mono (fun _ h => False.elim h))
                  (by rw [hmem2]; exact heq1) hframeOk)
            rw [hve]
            have ht0_2 : st2.getReg AbiReg.t0 = vi.toBitVec := (getReg_stepReg_eq st1 AbiReg.t0 (by decide) _ _).trans ha0_1
            exact ⟨ki + (1 + ke), st3,
              by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
              by rw [hpc3, htw2, htw_all]; congr 2; omega,
              (hoth3 AbiReg.t0 (by decide) (by decide)).trans ht0_2, ha0_3,
              hpres02.trans (PreservedFrameRegs.of_scratch2 AbiReg.a0 AbiReg.t1 (by decide) (by decide) hoth3),
              by rw [hmem3, hmem2]; exact heq1⟩
          · simp only [hvi] at riSim ⊢
            obtain ⟨ki, st1, hrun1, hpc1, hpres1, heq1⟩ := riSim
            exact ⟨ki, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
        | none =>
          have hnsI : isSimpleExpr i = false := isSimpleExpr_false_of_emitSimple_none hsi
          have hnsE : isSimpleExpr e = false := isSimpleExpr_false_of_emitSimple_none hse
          simp only [hnsI, hnsE, Bool.false_eq_true, ↓reduceIte] at hTmp
          simp only [compileStorePairR, hri, hre, hsi, hse] at hlink h64 ⊢
          refine ⟨by simp, by simp, ?_⟩
          have rseq := reg_evalTwoSpill_of_ih env L fl hfl lm loc hspAlign hlo hhi i e pre post 0
            (by omega) (by omega) (by omega)
            (fun p q tm r st' hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' =>
              reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi i p q tm r hr hiOk hVfI ht hl h6 st' hpc' hgp' ht5' hsp' hm' hf')
            (fun p q tm r st' hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' =>
              reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi e p q tm r hr heOk hVfE ht hl h6 st' hpc' hgp' ht5' hsp' hm' hf')
            hlink h64 st hpc hgp ht5 hsp hmemRel hframeOk
          rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
          · rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨ve, hve⟩ | hve
            · simp only [hvi, hve] at rseq ⊢
              obtain ⟨k1, st1, hrun1, hpc1, ht0_1, ha0_1, hpres1, heq1⟩ := rseq
              exact ⟨k1, st1, hrun1, hpc1, ht0_1, ha0_1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
            · simp only [hvi, hve] at rseq ⊢
              obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := rseq
              exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
          · simp only [hvi] at rseq ⊢
            obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := rseq
            exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩

/-- Helper for evaluating `(i, e)` into `(t3, a0)` using `tempSlotOff 0` (when `t` is already in a reg or simple). -/
private theorem reg_evalTwoSpill_t3_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (i e : Expr) (pre post : List AsmItem)
    (hiOk : exprOkB env.tab fl.nlocals i = true)
    (heOk : exprOkB env.tab fl.nlocals e = true)
    (hVfI : ExprVarsInFrame fl i) (hVfE : ExprVarsInFrame fl e)
    (htmp_le : 1 ≤ fl.usedTemps)
    (htmp1 : usedTempsExpr i ≤ fl.usedTemps)
    (htmp2 : 1 + usedTempsExpr e ≤ fl.usedTemps)
    (hlink : lkm.linkSpec (pre ++
      (compileETo env.tab fl 0 AbiReg.a0 i ++
       storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 0) ++
       compileETo env.tab fl 1 AbiReg.a0 e ++
       loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 0)) ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    match _root_.L.evalE i ⟨lm, loc⟩ with
    | .ok (vi, _) =>
      match _root_.L.evalE e ⟨lm, loc⟩ with
      | .ok (ve, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize
            (compileETo env.tab fl 0 AbiReg.a0 i ++
             storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 0) ++
             compileETo env.tab fl 1 AbiReg.a0 e ++
             loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 0)))) ∧
          st'.getReg AbiReg.t3 = vi.toBitVec ∧
          st'.getReg AbiReg.a0 = ve.toBitVec ∧
          PreservedFrameRegs fl (fun _ => False) st st' ∧
          MemEqOutside (tempSpanR fl sp 0) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedFrameRegs fl (fun _ => False) st st' ∧
          MemEqOutside (tempSpanR fl sp 0) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (fun _ => False) st st' ∧
        MemEqOutside (tempSpanR fl sp 0) st.mem st'.mem := by
  have hvalid : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  let c1 := compileETo env.tab fl 0 AbiReg.a0 i
  let cs := storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 0)
  let c2 := compileETo env.tab fl 1 AbiReg.a0 e
  let cl := loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 0)
  have h64 := linkResolved_sub_pc64 env pre (c1 ++ cs ++ c2 ++ cl) post hlink
  have htw_all : lkm.totalSize (c1 ++ cs ++ c2 ++ cl) =
      lkm.totalSize c1 + lkm.totalSize cs + lkm.totalSize c2 + lkm.totalSize cl := by
    simp only [lkm.totalSize_append]
  have r1 := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi i pre ((cs ++ c2 ++ cl) ++ post)
    0 AbiReg.a0 (Or.inl rfl) hiOk hVfI (by omega)
    (by simpa only [c1, cs, c2, cl, List.append_assoc] using hlink)
    (by rw [htw_all] at h64; dsimp only [c1] at h64; omega) st hpc hgp ht5 hsp hmemRel hframeOk
  rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
  · simp only [hvi] at r1 ⊢
    obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := r1
    have htw1 : lkm.totalSize (pre ++ c1) = lkm.totalSize pre + lkm.totalSize c1 := lkm.totalSize_append pre c1
    have halS : isAligned (st1.getReg AbiReg.sp + BitVec.ofInt 64 (fl.tempSlotOff 0)) 8 = true := by
      rw [hpres1.abi.sp.trans hsp, tempSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hspAlign _
    obtain ⟨st2, hrunS, hothS, hmemS, hpc2⟩ :=
      storeMemOff_sd_correct_lm lkm env.hrom (pre ++ c1) ((c2 ++ cl) ++ post) AbiReg.sp AbiReg.a0 AbiReg.t0
        (by decide) (by decide) (by decide) (fl.tempSlotOff 0)
        (by simpa only [c1, cs, c2, cl, List.append_assoc] using hlink)
        (by rw [htw1]; rw [htw_all] at h64; dsimp only [cs] at h64 ⊢; omega) st1 (by rw [htw1]; exact hpc1) halS
    have heqS : MemEqOutside (tempSpanR fl sp 0) st1.mem st2.mem := by
      rw [hmemS, hpres1.abi.sp.trans hsp, tempSlotOff_ofInt]
      exact MemEqOutside.writeWord64 st1.mem _ _ fun k hk =>
        tempSlotSpanR_sub_tempSpanR fl sp hvalid (Nat.le_refl 0) (by omega) _ ⟨k, hk, rfl⟩
    have heq02 : MemEqOutside (tempSpanR fl sp 0) st.mem st2.mem := heq1.trans heqS
    have hpres02 : PreservedFrameRegs fl (fun _ => False) st st2 :=
      (PreservedFrameRegs.of_a0 hpres1).trans (PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hothS)
    have htw2 : lkm.totalSize (pre ++ c1 ++ cs) = lkm.totalSize pre + lkm.totalSize c1 + lkm.totalSize cs := by
      rw [lkm.totalSize_append, htw1]
    have r2 := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi e (pre ++ c1 ++ cs) (cl ++ post)
      1 AbiReg.a0 (Or.inl rfl) heOk hVfE (by omega)
      (by simpa only [c1, cs, c2, cl, List.append_assoc] using hlink)
      (by rw [htw2]; rw [htw_all] at h64; dsimp only [c2] at h64; omega) st2 (by rw [htw2, ← htw1]; exact hpc2)
      (hpres02.abi.gp.trans hgp) (ht5.of_preserved hpres02) (hpres02.abi.sp.trans hsp)
      (ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) heq02 hmemRel)
      (ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) (hpres02.mono (fun _ h => False.elim h)) heq02 hframeOk)
    rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨ve, hve⟩ | hve
    · simp only [hve] at r2 ⊢
      obtain ⟨k2, st3, hrun2, hpc3, ha0_3, hpres3, heq3⟩ := r2
      have htw3 : lkm.totalSize (pre ++ c1 ++ cs ++ c2) =
          lkm.totalSize pre + lkm.totalSize c1 + lkm.totalSize cs + lkm.totalSize c2 := by
        rw [lkm.totalSize_append, htw2]
      have halL : isAligned (st3.getReg AbiReg.sp + BitVec.ofInt 64 (fl.tempSlotOff 0)) 8 = true := by
        rw [hpres3.abi.sp.trans (hpres02.abi.sp.trans hsp), tempSlotOff_ofInt]
        exact isAligned8_add_int_mul8 sp hspAlign _
      obtain ⟨st4, hrunL, hothL, ht3_4, hmemL, hpc4⟩ :=
        loadMemOff_ld_correct_lm lkm env.hrom (pre ++ c1 ++ cs ++ c2) post AbiReg.t3 AbiReg.sp AbiReg.t1
          (by decide) (by decide) (by decide) (fl.tempSlotOff 0)
          (by simpa only [c1, cs, c2, cl, List.append_assoc] using hlink)
          (by rw [htw3]; rw [htw_all] at h64; dsimp only [cl] at h64 ⊢; omega) st3 (by rw [htw3, ← htw2]; exact hpc3) halL
      have hslot3 : readWord64 st3.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff 0)) = vi.toBitVec := by
        have h2 : readWord64 st2.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff 0)) = vi.toBitVec := by
          rw [hmemS, hpres1.abi.sp.trans hsp, ha0_1]; exact readWord64_writeWord64_self st1.mem _ _
        rw [← h2]
        apply MemEqOutside.readWord64_eq heq3
        intro k hk; rw [tempSlotOff_ofInt]
        exact (tempSpanR_disj_tempSlot fl sp hvalid (Nat.lt_succ_self 0) (by omega)).symm _ ⟨k, hk, rfl⟩
      have heq3' : MemEqOutside (tempSpanR fl sp 0) st2.mem st3.mem :=
        heq3.mono (tempSpanR_mono fl sp hvalid (Nat.zero_le 1) (by omega))
      exact ⟨k1 + (lkm.totalSize cs + (k2 + lkm.totalSize cl)), st4,
        by rw [run_add, hrun1]; dsimp only; rw [run_add, hrunS]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrunL,
        by rw [hpc4, htw3, htw_all]; dsimp only [cl]; congr 2; omega,
        by rw [ht3_4, hpres3.abi.sp.trans (hpres02.abi.sp.trans hsp), hslot3],
        (hothL AbiReg.a0 (by decide) (by decide)).trans ha0_3,
        hpres02.trans ((PreservedFrameRegs.of_a0 hpres3).trans
          (PreservedFrameRegs.of_scratch2 AbiReg.t3 AbiReg.t1 (by decide) (by decide) hothL)),
        by rw [hmemL]; exact heq02.trans heq3'⟩
    · simp only [hve] at r2 ⊢
      obtain ⟨k2, st3, hrun2, hpc3, hpres3, heq3⟩ := r2
      have heq3' : MemEqOutside (tempSpanR fl sp 0) st2.mem st3.mem :=
        heq3.mono (tempSpanR_mono fl sp hvalid (Nat.zero_le 1) (by omega))
      exact ⟨k1 + (lkm.totalSize cs + k2), st3,
        by rw [run_add, hrun1]; dsimp only; rw [run_add, hrunS]; dsimp only; exact hrun2,
        hpc3, hpres02.trans (PreservedFrameRegs.of_a0 hpres3), heq02.trans heq3'⟩
  · simp only [hvi] at r1 ⊢
    obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := r1
    exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩

theorem reg_compileTierStoreTripleR_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (t i e : Expr) (pre post : List AsmItem)
    (htOk : exprOkB env.tab fl.nlocals t = true)
    (hiOk : exprOkB env.tab fl.nlocals i = true)
    (heOk : exprOkB env.tab fl.nlocals e = true)
    (hVfT : ExprVarsInFrame fl t) (hVfI : ExprVarsInFrame fl i) (hVfE : ExprVarsInFrame fl e)
    (hTmp : (if isSimpleExpr t then
               if isSimpleExpr i then usedTempsExpr e
               else if isSimpleExpr e then usedTempsExpr i
               else max (usedTempsExpr i) (1 + usedTempsExpr e)
             else max (usedTempsExpr t) (max (1 + usedTempsExpr i) (2 + usedTempsExpr e))) ≤ fl.usedTemps)
    (hlink : lkm.linkSpec (pre ++ (compileTierStoreTripleR env.tab fl t i e).1 ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    let res := compileTierStoreTripleR env.tab fl t i e
    (res.2.1 = AbiReg.zero ∨ res.2.1 = AbiReg.t0 ∨ res.2.1 ∈ allowedRegs true) ∧
    (res.2.2.1 = AbiReg.zero ∨ res.2.2.1 = AbiReg.a0 ∨ res.2.2.1 = AbiReg.t3 ∨ res.2.2.1 ∈ allowedRegs true) ∧
    (res.2.2.2 = AbiReg.zero ∨ res.2.2.2 = AbiReg.a0 ∨ res.2.2.2 = AbiReg.t3 ∨ res.2.2.2 ∈ allowedRegs true) ∧
    match _root_.L.evalE t ⟨lm, loc⟩ with
    | .ok (vt, _) =>
      match _root_.L.evalE i ⟨lm, loc⟩ with
      | .ok (vi, _) =>
        match _root_.L.evalE e ⟨lm, loc⟩ with
        | .ok (ve, _) =>
          ∃ k st', RV64.run env.rom k st = .cont st' ∧
            st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize res.1)) ∧
            st'.getReg res.2.1 = vt.toBitVec ∧
            st'.getReg res.2.2.1 = vi.toBitVec ∧
            st'.getReg res.2.2.2 = ve.toBitVec ∧
            PreservedFrameRegs fl (fun _ => False) st st' ∧
            MemEqOutside (tempSpanR fl sp 0) st.mem st'.mem
        | .error _ =>
          ∃ k st', RV64.run env.rom k st = .cont st' ∧
            st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
            PreservedFrameRegs fl (fun _ => False) st st' ∧
            MemEqOutside (tempSpanR fl sp 0) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedFrameRegs fl (fun _ => False) st st' ∧
          MemEqOutside (tempSpanR fl sp 0) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (fun _ => False) st st' ∧
        MemEqOutside (tempSpanR fl sp 0) st.mem st'.mem := by
  have hvalid : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  have h64 := linkResolved_sub_pc64 env pre (compileTierStoreTripleR env.tab fl t i e).1 post hlink
  have hPureSimple : ∀ (e' : Expr) (rd tmpR : Reg) (ce : List AsmItem),
      emitSimpleExprR env.tab fl rd tmpR e' = some ce →
      ∃ v, _root_.L.evalE e' ⟨lm, loc⟩ = .ok (v, ⟨lm, loc⟩) := by
    intro e' rd tmpR ce hs
    cases e' with
    | const w => exact ⟨w, rfl⟩
    | var x => exact ⟨loc x, rfl⟩
    | len8 a => exact ⟨UInt64.ofNat (lm.arr8 a).size, rfl⟩
    | len64 a => exact ⟨UInt64.ofNat (lm.arr64 (.t0 a)).size, rfl⟩
    | glob g => exact ⟨lm.glob g, rfl⟩
    | _ => simp [emitSimpleExprR] at hs
  cases hrt : exprReg? fl.alloc t with
  | some rt =>
    have hstSimple : isSimpleExpr t = true := isSimpleExpr_of_exprReg hrt
    simp only [hstSimple, ↓reduceIte] at hTmp
    have hTmpI : usedTempsExpr i ≤ fl.usedTemps := by
      cases hsi : isSimpleExpr i
      · cases hse : isSimpleExpr e <;> simp only [hsi, hse, Bool.false_eq_true, ↓reduceIte] at hTmp <;> omega
      · rw [usedTempsExpr_of_isSimple hsi]; exact Nat.zero_le _
    have hTmpE : usedTempsExpr e ≤ fl.usedTemps := by
      cases hsi : isSimpleExpr i
      · cases hse : isSimpleExpr e
        · simp only [hsi, hse, Bool.false_eq_true, ↓reduceIte] at hTmp; omega
        · rw [usedTempsExpr_of_isSimple hse]; exact Nat.zero_le _
      · simp only [hsi, ↓reduceIte] at hTmp; exact hTmp
    obtain ⟨hrtMem, _, vt, hvt, hgrt⟩ := reg_exprReg_sim (lm := lm) hfl hframeOk htOk hrt
    have hrtW : rt = AbiReg.zero ∨ rt = AbiReg.t0 ∨ rt ∈ allowedRegs true := by
      rcases hrtMem with rfl | hm; exact Or.inl rfl; exact Or.inr (Or.inr hm)
    cases hri : exprReg? fl.alloc i with
    | some ri =>
      obtain ⟨hriMem, _, vi, hvi, hgri⟩ := reg_exprReg_sim (lm := lm) hfl hframeOk hiOk hri
      have hriW : ri = AbiReg.zero ∨ ri = AbiReg.a0 ∨ ri = AbiReg.t3 ∨ ri ∈ allowedRegs true := by
        rcases hriMem with rfl | hm; exact Or.inl rfl; exact Or.inr (Or.inr (Or.inr hm))
      cases hre : exprReg? fl.alloc e with
      | some re =>
        obtain ⟨hreMem, _, ve, hve, hgre⟩ := reg_exprReg_sim (lm := lm) hfl hframeOk heOk hre
        have hreW : re = AbiReg.zero ∨ re = AbiReg.a0 ∨ re = AbiReg.t3 ∨ re ∈ allowedRegs true := by
          rcases hreMem with rfl | hm; exact Or.inl rfl; exact Or.inr (Or.inr (Or.inr hm))
        simp only [compileTierStoreTripleR, hrt, hri, hre, hvt, hvi, hve]
        exact ⟨hrtW, hriW, hreW, 0, st, rfl, by rw [lkm.totalSize_nil, Nat.add_zero]; exact hpc,
          hgrt, hgri, hgre, PreservedFrameRegs.refl _ _ _, MemEqOutside.refl _ _⟩
      | none =>
        simp only [compileTierStoreTripleR, hrt, hri, hre] at hlink h64 ⊢
        refine ⟨hrtW, hriW, by simp, ?_⟩
        rw [hvt, hvi]
        have reSim := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi e pre post 0 AbiReg.a0 (Or.inl rfl)
          heOk hVfE (by omega) hlink h64 st hpc hgp ht5 hsp hmemRel hframeOk
        rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨ve, hve⟩ | hve
        · simp only [hve] at reSim ⊢
          obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := reSim
          exact ⟨k1, st1, hrun1, hpc1, (hpres1.getReg_of_exprReg hrtMem).trans hgrt,
            (hpres1.getReg_of_exprReg hriMem).trans hgri, ha0_1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
        · simp only [hve] at reSim ⊢
          obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := reSim
          exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
    | none =>
      cases hre : exprReg? fl.alloc e with
      | some re =>
        obtain ⟨hreMem, _, ve, hve, hgre⟩ := reg_exprReg_sim (lm := lm) hfl hframeOk heOk hre
        have hreW : re = AbiReg.zero ∨ re = AbiReg.a0 ∨ re = AbiReg.t3 ∨ re ∈ allowedRegs true := by
          rcases hreMem with rfl | hm; exact Or.inl rfl; exact Or.inr (Or.inr (Or.inr hm))
        simp only [compileTierStoreTripleR, hrt, hri, hre] at hlink h64 ⊢
        refine ⟨hrtW, by simp, hreW, ?_⟩
        rw [hvt]
        have riSim := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi i pre post 0 AbiReg.a0 (Or.inl rfl)
          hiOk hVfI (by omega) hlink h64 st hpc hgp ht5 hsp hmemRel hframeOk
        rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
        · simp only [hvi] at riSim ⊢; rw [hve]
          obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := riSim
          exact ⟨k1, st1, hrun1, hpc1, (hpres1.getReg_of_exprReg hrtMem).trans hgrt,
            ha0_1, (hpres1.getReg_of_exprReg hreMem).trans hgre, PreservedFrameRegs.of_a0 hpres1, heq1⟩
        · simp only [hvi] at riSim ⊢
          obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := riSim
          exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
      | none =>
        cases hsi : emitSimpleExprR env.tab fl AbiReg.t3 AbiReg.t4 i with
        | some ci =>
          simp only [compileTierStoreTripleR, hrt, hri, hre, hsi] at hlink h64 ⊢
          refine ⟨hrtW, by simp, by simp, ?_⟩
          rw [hvt]
          obtain ⟨vi, hvi⟩ := hPureSimple i AbiReg.t3 AbiReg.t4 ci hsi
          rw [hvi]
          have htw_all : lkm.totalSize (compileETo env.tab fl 0 AbiReg.a0 e ++ ci) =
              lkm.totalSize (compileETo env.tab fl 0 AbiReg.a0 e) + lkm.totalSize ci := lkm.totalSize_append _ _
          have reSim := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi e pre (ci ++ post) 0
            AbiReg.a0 (Or.inl rfl) heOk hVfE (by omega)
            (by simpa only [List.append_assoc] using hlink)
            (by rw [htw_all] at h64; omega) st hpc hgp ht5 hsp hmemRel hframeOk
          rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨ve, hve⟩ | hve
          · simp only [hve] at reSim ⊢
            obtain ⟨ke, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := reSim
            have htw1 : lkm.totalSize (pre ++ compileETo env.tab fl 0 AbiReg.a0 e) =
                lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl 0 AbiReg.a0 e) := lkm.totalSize_append _ _
            obtain ⟨vi', ki, st2, hvi', hrun2, hpc2, ht3_2, hoth2, hmem2⟩ :=
              reg_emitSimpleExprR_sim env L fl hfl lm loc hspAlign
                (pre ++ compileETo env.tab fl 0 AbiReg.a0 e) post
                AbiReg.t3 AbiReg.t4 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide) i ci hsi hiOk hVfI
                (by simpa only [List.append_assoc] using hlink)
                (by rw [htw1]; rw [htw_all] at h64; omega) st1 (by rw [htw1]; exact hpc1)
                (hpres1.abi.gp.trans hgp) (ht5.of_preserved hpres1) (hpres1.abi.sp.trans hsp)
                (ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) heq1 hmemRel)
                (ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) hpres1 heq1 hframeOk)
            rw [hvi] at hvi'; have hEqTmp := (Prod.mk.inj (Except.ok.inj hvi')).1; subst hEqTmp
            have hpres2 : PreservedFrameRegs fl (fun _ => False) st1 st2 :=
              PreservedFrameRegs.of_scratch2 AbiReg.t3 AbiReg.t4 (by decide) (by decide) hoth2
            exact ⟨ke + ki, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
              by rw [hpc2, htw1, htw_all]; congr 2; omega,
              (hoth2 rt (exprReg_ne_scratch hrtMem (by decide)) (exprReg_ne_scratch hrtMem (by decide))).trans
                ((hpres1.getReg_of_exprReg hrtMem).trans hgrt),
              ht3_2, (hoth2 AbiReg.a0 (by decide) (by decide)).trans ha0_1,
              (PreservedFrameRegs.of_a0 hpres1).trans hpres2, by rw [hmem2]; exact heq1⟩
          · simp only [hve] at reSim ⊢
            obtain ⟨ke, st1, hrun1, hpc1, hpres1, heq1⟩ := reSim
            exact ⟨ke, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
        | none =>
          cases hse : emitSimpleExprR env.tab fl AbiReg.a0 AbiReg.t4 e with
          | some ce =>
            simp only [compileTierStoreTripleR, hrt, hri, hre, hsi, hse] at hlink h64 ⊢
            refine ⟨hrtW, by simp, by simp, ?_⟩
            rw [hvt]
            have htw_all : lkm.totalSize (compileETo env.tab fl 0 AbiReg.a0 i ++ [Asm.mv AbiReg.t3 AbiReg.a0] ++ ce) =
                lkm.totalSize (compileETo env.tab fl 0 AbiReg.a0 i) + 1 + lkm.totalSize ce := by
              simp only [lkm.totalSize_append, Asm.mv, lkm.totalSize_instr]
            have riSim := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi i pre
              (([Asm.mv AbiReg.t3 AbiReg.a0] ++ ce) ++ post) 0 AbiReg.a0 (Or.inl rfl) hiOk hVfI (by omega)
              (by simpa only [List.append_assoc] using hlink)
              (by rw [htw_all] at h64; omega) st hpc hgp ht5 hsp hmemRel hframeOk
            rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
            · simp only [hvi] at riSim ⊢
              obtain ⟨ki, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := riSim
              have htw1 : lkm.totalSize (pre ++ compileETo env.tab fl 0 AbiReg.a0 i) =
                  lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl 0 AbiReg.a0 i) := lkm.totalSize_append _ _
              have hsMv := step_item_instr_lm lkm env.hrom (pre ++ compileETo env.tab fl 0 AbiReg.a0 i) (ce ++ post)
                (.aluImm .addi AbiReg.t3 AbiReg.a0 0#12)
                (by simpa only [Asm.mv, List.append_assoc] using hlink)
                (by rw [htw1]; rw [htw_all] at h64; omega) st1 (by rw [htw1]; exact hpc1)
              let st2 := stepReg st1 AbiReg.t3 (st1.getReg AbiReg.a0) (st1.pc + 4#64)
              have hrun2 : RV64.run env.rom 1 st1 = .cont st2 :=
                run_one_cont _ _ st2 (by rw [hsMv]; simp only [execInstr, evalAluImm, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero]; rfl)
              have htw2 : lkm.totalSize (pre ++ compileETo env.tab fl 0 AbiReg.a0 i ++ [Asm.mv AbiReg.t3 AbiReg.a0]) =
                  lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl 0 AbiReg.a0 i) + 1 := by
                rw [lkm.totalSize_append, htw1, Asm.mv, lkm.totalSize_instr]
              have hpc2 : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ compileETo env.tab fl 0 AbiReg.a0 i ++ [Asm.mv AbiReg.t3 AbiReg.a0])) := by
                change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1, htw2]
              have hpres2 : PreservedFrameRegs fl (fun _ => False) st1 st2 :=
                PreservedFrameRegs.of_scratch1 AbiReg.t3 (by decide) (fun r hr => getReg_stepReg_ne st1 AbiReg.t3 r hr _ _)
              have hpres02 : PreservedFrameRegs fl (fun _ => False) st st2 := (PreservedFrameRegs.of_a0 hpres1).trans hpres2
              have hmem2 : st2.mem = st1.mem := mem_stepReg st1 _ _ _
              obtain ⟨ve, ke, st3, hve, hrun3, hpc3, ha0_3, hoth3, hmem3⟩ :=
                reg_emitSimpleExprR_sim env L fl hfl lm loc hspAlign
                  (pre ++ compileETo env.tab fl 0 AbiReg.a0 i ++ [Asm.mv AbiReg.t3 AbiReg.a0]) post
                  AbiReg.a0 AbiReg.t4 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide) e ce hse heOk hVfE
                  (by simpa only [List.append_assoc] using hlink)
                  (by rw [htw2]; rw [htw_all] at h64; omega) st2 hpc2
                  (hpres02.abi.gp.trans hgp) (ht5.of_preserved hpres02) (hpres02.abi.sp.trans hsp)
                  (by rw [hmem2]; exact ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) heq1 hmemRel)
                  (ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) (hpres02.mono (fun _ h => False.elim h))
                    (by rw [hmem2]; exact heq1) hframeOk)
              rw [hve]
              have ht3_2 : st2.getReg AbiReg.t3 = vi.toBitVec := (getReg_stepReg_eq st1 AbiReg.t3 (by decide) _ _).trans ha0_1
              exact ⟨ki + (1 + ke), st3,
                by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
                by rw [hpc3, htw2, htw_all]; congr 2; omega,
                (hoth3 rt (exprReg_ne_scratch hrtMem (by decide)) (exprReg_ne_scratch hrtMem (by decide))).trans
                  ((getReg_stepReg_ne st1 AbiReg.t3 rt (exprReg_ne_scratch hrtMem (by decide)) _ _).trans
                    ((hpres1.getReg_of_exprReg hrtMem).trans hgrt)),
                (hoth3 AbiReg.t3 (by decide) (by decide)).trans ht3_2, ha0_3,
                hpres02.trans (PreservedFrameRegs.of_scratch2 AbiReg.a0 AbiReg.t4 (by decide) (by decide) hoth3),
                by rw [hmem3, hmem2]; exact heq1⟩
            · simp only [hvi] at riSim ⊢
              obtain ⟨ki, st1, hrun1, hpc1, hpres1, heq1⟩ := riSim
              exact ⟨ki, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
          | none =>
            have hnsI : isSimpleExpr i = false := isSimpleExpr_false_of_emitSimple_none hsi
            have hnsE : isSimpleExpr e = false := isSimpleExpr_false_of_emitSimple_none hse
            simp only [hnsI, hnsE, Bool.false_eq_true, ↓reduceIte] at hTmp
            simp only [compileTierStoreTripleR, hrt, hri, hre, hsi, hse] at hlink h64 ⊢
            refine ⟨hrtW, by simp, by simp, ?_⟩
            rw [hvt]
            have rseq := reg_evalTwoSpill_t3_sim env L fl hfl lm loc hspAlign hlo hhi i e pre post hiOk heOk hVfI hVfE
              (by omega) (by omega) (by omega) hlink st hpc hgp ht5 hsp hmemRel hframeOk
            rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
            · rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨ve, hve⟩ | hve
              · simp only [hvi, hve] at rseq ⊢
                obtain ⟨k1, st1, hrun1, hpc1, ht3_1, ha0_1, hpres1, heq1⟩ := rseq
                have hrt1 : st1.getReg rt = vt.toBitVec := by
                  rcases hrtMem with rfl | hm; exact hgrt
                  exact (hpres1.regs rt (allowedRegs_sub_true hm) (by intro h; cases h)).trans hgrt
                exact ⟨k1, st1, hrun1, hpc1, hrt1, ht3_1, ha0_1, hpres1, heq1⟩
              · simp only [hvi, hve] at rseq ⊢; exact rseq
            · simp only [hvi] at rseq ⊢; exact rseq
  | none =>
    cases hst : emitSimpleExprR env.tab fl AbiReg.t0 AbiReg.t1 t with
    | some ct =>
      have hstSimple : isSimpleExpr t = true := by
        cases t <;> simp [emitSimpleExprR, isSimpleExpr] at hst ⊢
      simp only [hstSimple, ↓reduceIte] at hTmp
      have hTmpI : usedTempsExpr i ≤ fl.usedTemps := by
        cases hsi : isSimpleExpr i
        · cases hse : isSimpleExpr e <;> simp only [hsi, hse, Bool.false_eq_true, ↓reduceIte] at hTmp <;> omega
        · rw [usedTempsExpr_of_isSimple hsi]; exact Nat.zero_le _
      have hTmpE : usedTempsExpr e ≤ fl.usedTemps := by
        cases hsi : isSimpleExpr i
        · cases hse : isSimpleExpr e
          · simp only [hsi, hse, Bool.false_eq_true, ↓reduceIte] at hTmp; omega
          · rw [usedTempsExpr_of_isSimple hse]; exact Nat.zero_le _
        · simp only [hsi, ↓reduceIte] at hTmp; exact hTmp
      obtain ⟨vt, hvt⟩ := hPureSimple t AbiReg.t0 AbiReg.t1 ct hst
      cases hsi : emitSimpleExprR env.tab fl AbiReg.t3 AbiReg.t4 i with
      | some ci =>
        simp only [compileTierStoreTripleR, hrt, hst, hsi] at hlink h64 ⊢
        refine ⟨by simp, by simp, by simp, ?_⟩
        obtain ⟨vi, hvi⟩ := hPureSimple i AbiReg.t3 AbiReg.t4 ci hsi
        rw [hvt, hvi]
        have htw_all : lkm.totalSize (compileETo env.tab fl 0 AbiReg.a0 e ++ ct ++ ci) =
            lkm.totalSize (compileETo env.tab fl 0 AbiReg.a0 e) + lkm.totalSize ct + lkm.totalSize ci := by
          simp only [lkm.totalSize_append]
        have reSim := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi e pre ((ct ++ ci) ++ post) 0
          AbiReg.a0 (Or.inl rfl) heOk hVfE (by omega)
          (by simpa only [List.append_assoc] using hlink)
          (by rw [htw_all] at h64; omega) st hpc hgp ht5 hsp hmemRel hframeOk
        rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨ve, hve⟩ | hve
        · simp only [hve] at reSim ⊢
          obtain ⟨ke, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := reSim
          have htw1 : lkm.totalSize (pre ++ compileETo env.tab fl 0 AbiReg.a0 e) =
              lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl 0 AbiReg.a0 e) := lkm.totalSize_append _ _
          obtain ⟨vt', kt, st2, hvt', hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
            reg_emitSimpleExprR_sim env L fl hfl lm loc hspAlign
              (pre ++ compileETo env.tab fl 0 AbiReg.a0 e) (ci ++ post)
              AbiReg.t0 AbiReg.t1 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide) t ct hst htOk hVfT
              (by simpa only [List.append_assoc] using hlink)
              (by rw [htw1]; rw [htw_all] at h64; omega) st1 (by rw [htw1]; exact hpc1)
              (hpres1.abi.gp.trans hgp) (ht5.of_preserved hpres1) (hpres1.abi.sp.trans hsp)
              (ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) heq1 hmemRel)
              (ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) hpres1 heq1 hframeOk)
          rw [hvt] at hvt'; have hEqTmp := (Prod.mk.inj (Except.ok.inj hvt')).1; subst hEqTmp
          have hpres02 : PreservedFrameRegs fl (fun _ => False) st st2 :=
            (PreservedFrameRegs.of_a0 hpres1).trans (PreservedFrameRegs.of_scratch2 AbiReg.t0 AbiReg.t1 (by decide) (by decide) hoth2)
          have htw2 : lkm.totalSize (pre ++ compileETo env.tab fl 0 AbiReg.a0 e ++ ct) =
              lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl 0 AbiReg.a0 e) + lkm.totalSize ct := by
            rw [lkm.totalSize_append, htw1]
          obtain ⟨vi', ki, st3, hvi', hrun3, hpc3, ht3_3, hoth3, hmem3⟩ :=
            reg_emitSimpleExprR_sim env L fl hfl lm loc hspAlign
              (pre ++ compileETo env.tab fl 0 AbiReg.a0 e ++ ct) post
              AbiReg.t3 AbiReg.t4 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide) i ci hsi hiOk hVfI
              (by simpa only [List.append_assoc] using hlink)
              (by rw [htw2]; rw [htw_all] at h64; omega) st2 (by rw [htw2, ← htw1]; exact hpc2)
              (hpres02.abi.gp.trans hgp) (ht5.of_preserved hpres02) (hpres02.abi.sp.trans hsp)
              (by rw [hmem2]; exact ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) heq1 hmemRel)
              (ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) (hpres02.mono (fun _ h => False.elim h))
                (by rw [hmem2]; exact heq1) hframeOk)
          rw [hvi] at hvi'; have hEqTmp := (Prod.mk.inj (Except.ok.inj hvi')).1; subst hEqTmp
          exact ⟨ke + (kt + ki), st3,
            by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
            by rw [hpc3, htw2, htw_all]; congr 2; omega,
            (hoth3 AbiReg.t0 (by decide) (by decide)).trans ht0_2,
            ht3_3, (hoth3 AbiReg.a0 (by decide) (by decide)).trans ((hoth2 AbiReg.a0 (by decide) (by decide)).trans ha0_1),
            hpres02.trans (PreservedFrameRegs.of_scratch2 AbiReg.t3 AbiReg.t4 (by decide) (by decide) hoth3),
            by rw [hmem3, hmem2]; exact heq1⟩
        · simp only [hve] at reSim ⊢
          obtain ⟨ke, st1, hrun1, hpc1, hpres1, heq1⟩ := reSim
          exact ⟨ke, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
      | none =>
        cases hse : emitSimpleExprR env.tab fl AbiReg.a0 AbiReg.t4 e with
        | some ce =>
          simp only [compileTierStoreTripleR, hrt, hst, hsi, hse] at hlink h64 ⊢
          refine ⟨by simp, by simp, by simp, ?_⟩
          rw [hvt]
          have htw_all : lkm.totalSize (compileETo env.tab fl 0 AbiReg.a0 i ++ [Asm.mv AbiReg.t3 AbiReg.a0] ++ ct ++ ce) =
              lkm.totalSize (compileETo env.tab fl 0 AbiReg.a0 i) + 1 + lkm.totalSize ct + lkm.totalSize ce := by
            simp only [lkm.totalSize_append, Asm.mv, lkm.totalSize_instr]
          have riSim := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi i pre
            (([Asm.mv AbiReg.t3 AbiReg.a0] ++ ct ++ ce) ++ post) 0 AbiReg.a0 (Or.inl rfl) hiOk hVfI (by omega)
            (by simpa only [List.append_assoc] using hlink)
            (by rw [htw_all] at h64; omega) st hpc hgp ht5 hsp hmemRel hframeOk
          rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
          · simp only [hvi] at riSim ⊢
            obtain ⟨ki, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := riSim
            have htw1 : lkm.totalSize (pre ++ compileETo env.tab fl 0 AbiReg.a0 i) =
                lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl 0 AbiReg.a0 i) := lkm.totalSize_append _ _
            have hsMv := step_item_instr_lm lkm env.hrom (pre ++ compileETo env.tab fl 0 AbiReg.a0 i) ((ct ++ ce) ++ post)
              (.aluImm .addi AbiReg.t3 AbiReg.a0 0#12)
              (by simpa only [Asm.mv, List.append_assoc] using hlink)
              (by rw [htw1]; rw [htw_all] at h64; omega) st1 (by rw [htw1]; exact hpc1)
            let st2 := stepReg st1 AbiReg.t3 (st1.getReg AbiReg.a0) (st1.pc + 4#64)
            have hrun2 : RV64.run env.rom 1 st1 = .cont st2 :=
              run_one_cont _ _ st2 (by rw [hsMv]; simp only [execInstr, evalAluImm, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero]; rfl)
            have htw2 : lkm.totalSize (pre ++ compileETo env.tab fl 0 AbiReg.a0 i ++ [Asm.mv AbiReg.t3 AbiReg.a0]) =
                lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl 0 AbiReg.a0 i) + 1 := by
              rw [lkm.totalSize_append, htw1, Asm.mv, lkm.totalSize_instr]
            have hpc2 : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ compileETo env.tab fl 0 AbiReg.a0 i ++ [Asm.mv AbiReg.t3 AbiReg.a0])) := by
              change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1, htw2]
            have hpres02 : PreservedFrameRegs fl (fun _ => False) st st2 :=
              (PreservedFrameRegs.of_a0 hpres1).trans
                (PreservedFrameRegs.of_scratch1 AbiReg.t3 (by decide) (fun r hr => getReg_stepReg_ne st1 AbiReg.t3 r hr _ _))
            have hmem2 : st2.mem = st1.mem := mem_stepReg st1 _ _ _
            obtain ⟨vt', kt, st3, hvt', hrun3, hpc3, ht0_3, hoth3, hmem3⟩ :=
              reg_emitSimpleExprR_sim env L fl hfl lm loc hspAlign
                (pre ++ compileETo env.tab fl 0 AbiReg.a0 i ++ [Asm.mv AbiReg.t3 AbiReg.a0]) (ce ++ post)
                AbiReg.t0 AbiReg.t1 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide) t ct hst htOk hVfT
                (by simpa only [List.append_assoc] using hlink)
                (by rw [htw2]; rw [htw_all] at h64; omega) st2 hpc2
                (hpres02.abi.gp.trans hgp) (ht5.of_preserved hpres02) (hpres02.abi.sp.trans hsp)
                (by rw [hmem2]; exact ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) heq1 hmemRel)
                (ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) (hpres02.mono (fun _ h => False.elim h))
                  (by rw [hmem2]; exact heq1) hframeOk)
            rw [hvt] at hvt'; have hEqTmp := (Prod.mk.inj (Except.ok.inj hvt')).1; subst hEqTmp
            have hpres03 : PreservedFrameRegs fl (fun _ => False) st st3 :=
              hpres02.trans (PreservedFrameRegs.of_scratch2 AbiReg.t0 AbiReg.t1 (by decide) (by decide) hoth3)
            have htw3 : lkm.totalSize (pre ++ compileETo env.tab fl 0 AbiReg.a0 i ++ [Asm.mv AbiReg.t3 AbiReg.a0] ++ ct) =
                lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl 0 AbiReg.a0 i) + 1 + lkm.totalSize ct := by
              rw [lkm.totalSize_append, htw2]
            obtain ⟨ve, ke, st4, hve, hrun4, hpc4, ha0_4, hoth4, hmem4⟩ :=
              reg_emitSimpleExprR_sim env L fl hfl lm loc hspAlign
                (pre ++ compileETo env.tab fl 0 AbiReg.a0 i ++ [Asm.mv AbiReg.t3 AbiReg.a0] ++ ct) post
                AbiReg.a0 AbiReg.t4 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide) e ce hse heOk hVfE
                (by simpa only [List.append_assoc] using hlink)
                (by rw [htw3]; rw [htw_all] at h64; omega) st3 (by rw [htw3, ← htw2]; exact hpc3)
                (hpres03.abi.gp.trans hgp) (ht5.of_preserved hpres03) (hpres03.abi.sp.trans hsp)
                (by rw [hmem3, hmem2]; exact ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) heq1 hmemRel)
                (ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) (hpres03.mono (fun _ h => False.elim h))
                  (by rw [hmem3, hmem2]; exact heq1) hframeOk)
            rw [hve]
            have ht3_2 : st2.getReg AbiReg.t3 = vi.toBitVec := (getReg_stepReg_eq st1 AbiReg.t3 (by decide) _ _).trans ha0_1
            exact ⟨ki + (1 + (kt + ke)), st4,
              by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; rw [run_add, hrun3]; dsimp only; exact hrun4,
              by rw [hpc4, htw3, htw_all]; congr 2; omega,
              (hoth4 AbiReg.t0 (by decide) (by decide)).trans ht0_3,
              (hoth4 AbiReg.t3 (by decide) (by decide)).trans ((hoth3 AbiReg.t3 (by decide) (by decide)).trans ht3_2), ha0_4,
              hpres03.trans (PreservedFrameRegs.of_scratch2 AbiReg.a0 AbiReg.t4 (by decide) (by decide) hoth4),
              by rw [hmem4, hmem3, hmem2]; exact heq1⟩
          · simp only [hvi] at riSim ⊢
            obtain ⟨ki, st1, hrun1, hpc1, hpres1, heq1⟩ := riSim
            exact ⟨ki, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
        | none =>
          have hnsI : isSimpleExpr i = false := isSimpleExpr_false_of_emitSimple_none hsi
          have hnsE : isSimpleExpr e = false := isSimpleExpr_false_of_emitSimple_none hse
          simp only [hnsI, hnsE, Bool.false_eq_true, ↓reduceIte] at hTmp
          simp only [compileTierStoreTripleR, hrt, hst, hsi, hse] at hlink h64 ⊢
          refine ⟨by simp, by simp, by simp, ?_⟩
          rw [hvt]
          let seq := compileETo env.tab fl 0 AbiReg.a0 i ++
            storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 0) ++
            compileETo env.tab fl 1 AbiReg.a0 e ++
            loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 0)
          have htw_all : lkm.totalSize (seq ++ ct) = lkm.totalSize seq + lkm.totalSize ct := lkm.totalSize_append seq ct
          have rseq := reg_evalTwoSpill_t3_sim env L fl hfl lm loc hspAlign hlo hhi i e pre (ct ++ post) hiOk heOk hVfI hVfE
            (by omega) (by omega) (by omega)
            (by simpa only [seq, List.append_assoc] using hlink) st hpc hgp ht5 hsp hmemRel hframeOk
          rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
          · rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨ve, hve⟩ | hve
            · simp only [hvi, hve] at rseq ⊢
              obtain ⟨k1, st1, hrun1, hpc1, ht3_1, ha0_1, hpres1, heq1⟩ := rseq
              have htw1 : lkm.totalSize (pre ++ seq) = lkm.totalSize pre + lkm.totalSize seq := lkm.totalSize_append pre seq
              obtain ⟨vt', kt, st2, hvt', hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
                reg_emitSimpleExprR_sim env L fl hfl lm loc hspAlign (pre ++ seq) post
                  AbiReg.t0 AbiReg.t1 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide) t ct hst htOk hVfT
                  (by simpa only [seq, List.append_assoc] using hlink)
                  (by rw [htw1]; dsimp only [seq] at htw_all ⊢; rw [htw_all] at h64; omega)
                  st1 (by rw [htw1]; exact hpc1) (hpres1.abi.gp.trans hgp) (ht5.of_preserved hpres1) (hpres1.abi.sp.trans hsp)
                  (ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) heq1 hmemRel)
                  (ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) (hpres1.mono (fun _ h => False.elim h)) heq1 hframeOk)
              rw [hvt] at hvt'; have hEqTmp := (Prod.mk.inj (Except.ok.inj hvt')).1; subst hEqTmp
              exact ⟨k1 + kt, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
                by rw [hpc2, htw1]; dsimp only [seq] at htw_all ⊢; rw [htw_all]; congr 2; omega,
                ht0_2, (hoth2 AbiReg.t3 (by decide) (by decide)).trans ht3_1,
                (hoth2 AbiReg.a0 (by decide) (by decide)).trans ha0_1,
                hpres1.trans (PreservedFrameRegs.of_scratch2 AbiReg.t0 AbiReg.t1 (by decide) (by decide) hoth2),
                by rw [hmem2]; exact heq1⟩
            · simp only [hvi, hve] at rseq ⊢; exact rseq
          · simp only [hvi] at rseq ⊢; exact rseq
    | none =>
      have hnsT : isSimpleExpr t = false := isSimpleExpr_false_of_emitSimple_none hst
      simp only [hnsT, Bool.false_eq_true, ↓reduceIte] at hTmp
      simp only [compileTierStoreTripleR, hrt, hst] at hlink h64 ⊢
      refine ⟨by simp, by simp, by simp, ?_⟩
      let ct := compileETo env.tab fl 0 AbiReg.a0 t
      let cs0 := storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 0)
      let ci := compileETo env.tab fl 1 AbiReg.a0 i
      let cs1 := storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 1)
      let ce := compileETo env.tab fl 2 AbiReg.a0 e
      let cl0 := loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 0)
      let cl1 := loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 1)
      have htw_all : lkm.totalSize (ct ++ cs0 ++ ci ++ cs1 ++ ce ++ cl0 ++ cl1) =
          lkm.totalSize ct + lkm.totalSize cs0 + lkm.totalSize ci + lkm.totalSize cs1 +
          lkm.totalSize ce + lkm.totalSize cl0 + lkm.totalSize cl1 := by
        simp only [lkm.totalSize_append]
      have rtSim := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi t pre
        ((cs0 ++ ci ++ cs1 ++ ce ++ cl0 ++ cl1) ++ post) 0 AbiReg.a0 (Or.inl rfl) htOk hVfT (by omega)
        (by simpa only [ct, cs0, ci, cs1, ce, cl0, cl1, List.append_assoc] using hlink)
        (by rw [htw_all] at h64; dsimp only [ct] at h64; omega) st hpc hgp ht5 hsp hmemRel hframeOk
      rcases _root_.L.evalE_pure t ⟨lm, loc⟩ with ⟨vt, hvt⟩ | hvt
      · simp only [hvt] at rtSim ⊢
        obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := rtSim
        have htw1 : lkm.totalSize (pre ++ ct) = lkm.totalSize pre + lkm.totalSize ct := lkm.totalSize_append pre ct
        have halS0 : isAligned (st1.getReg AbiReg.sp + BitVec.ofInt 64 (fl.tempSlotOff 0)) 8 = true := by
          rw [hpres1.abi.sp.trans hsp, tempSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hspAlign _
        obtain ⟨st2, hrunS0, hothS0, hmemS0, hpc2⟩ :=
          storeMemOff_sd_correct_lm lkm env.hrom (pre ++ ct) ((ci ++ cs1 ++ ce ++ cl0 ++ cl1) ++ post)
            AbiReg.sp AbiReg.a0 AbiReg.t0 (by decide) (by decide) (by decide) (fl.tempSlotOff 0)
            (by simpa only [ct, cs0, ci, cs1, ce, cl0, cl1, List.append_assoc] using hlink)
            (by rw [htw1]; rw [htw_all] at h64; dsimp only [cs0] at h64 ⊢; omega) st1 (by rw [htw1]; exact hpc1) halS0
        have heqS0 : MemEqOutside (tempSpanR fl sp 0) st1.mem st2.mem := by
          rw [hmemS0, hpres1.abi.sp.trans hsp, tempSlotOff_ofInt]
          exact MemEqOutside.writeWord64 st1.mem _ _ fun k hk =>
            tempSlotSpanR_sub_tempSpanR fl sp hvalid (Nat.le_refl 0) (by omega) _ ⟨k, hk, rfl⟩
        have heq02 := heq1.trans heqS0
        have hpres02 : PreservedFrameRegs fl (fun _ => False) st st2 :=
          (PreservedFrameRegs.of_a0 hpres1).trans (PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hothS0)
        have htw2 : lkm.totalSize (pre ++ ct ++ cs0) = lkm.totalSize pre + lkm.totalSize ct + lkm.totalSize cs0 := by
          rw [lkm.totalSize_append, htw1]
        have riSim := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi i (pre ++ ct ++ cs0)
          ((cs1 ++ ce ++ cl0 ++ cl1) ++ post) 1 AbiReg.a0 (Or.inl rfl) hiOk hVfI (by omega)
          (by simpa only [ct, cs0, ci, cs1, ce, cl0, cl1, List.append_assoc] using hlink)
          (by rw [htw2]; rw [htw_all] at h64; dsimp only [ci] at h64; omega) st2 (by rw [htw2, ← htw1]; exact hpc2)
          (hpres02.abi.gp.trans hgp) (ht5.of_preserved hpres02) (hpres02.abi.sp.trans hsp)
          (ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) heq02 hmemRel)
          (ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) (hpres02.mono (fun _ h => False.elim h)) heq02 hframeOk)
        rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
        · simp only [hvi] at riSim ⊢
          obtain ⟨k2, st3, hrun3, hpc3, ha0_3, hpres3, heq3⟩ := riSim
          have htw3 : lkm.totalSize (pre ++ ct ++ cs0 ++ ci) =
              lkm.totalSize pre + lkm.totalSize ct + lkm.totalSize cs0 + lkm.totalSize ci := by
            rw [lkm.totalSize_append, htw2]
          have halS1 : isAligned (st3.getReg AbiReg.sp + BitVec.ofInt 64 (fl.tempSlotOff 1)) 8 = true := by
            rw [hpres3.abi.sp.trans (hpres02.abi.sp.trans hsp), tempSlotOff_ofInt]
            exact isAligned8_add_int_mul8 sp hspAlign _
          obtain ⟨st4, hrunS1, hothS1, hmemS1, hpc4⟩ :=
            storeMemOff_sd_correct_lm lkm env.hrom (pre ++ ct ++ cs0 ++ ci) ((ce ++ cl0 ++ cl1) ++ post)
              AbiReg.sp AbiReg.a0 AbiReg.t0 (by decide) (by decide) (by decide) (fl.tempSlotOff 1)
              (by simpa only [ct, cs0, ci, cs1, ce, cl0, cl1, List.append_assoc] using hlink)
              (by rw [htw3]; rw [htw_all] at h64; dsimp only [cs1] at h64 ⊢; omega) st3 (by rw [htw3, ← htw2]; exact hpc3) halS1
          have heqS1 : MemEqOutside (tempSpanR fl sp 1) st3.mem st4.mem := by
            rw [hmemS1, hpres3.abi.sp.trans (hpres02.abi.sp.trans hsp), tempSlotOff_ofInt]
            exact MemEqOutside.writeWord64 st3.mem _ _ fun k hk =>
              tempSlotSpanR_sub_tempSpanR fl sp hvalid (Nat.le_refl 1) (by omega) _ ⟨k, hk, rfl⟩
          have heq24 : MemEqOutside (tempSpanR fl sp 1) st2.mem st4.mem := heq3.trans heqS1
          have heq04 : MemEqOutside (tempSpanR fl sp 0) st.mem st4.mem :=
            heq02.trans (heq24.mono (tempSpanR_mono fl sp hvalid (Nat.zero_le 1) (by omega)))
          have hpres04 : PreservedFrameRegs fl (fun _ => False) st st4 :=
            hpres02.trans ((PreservedFrameRegs.of_a0 hpres3).trans (PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hothS1))
          have htw4 : lkm.totalSize (pre ++ ct ++ cs0 ++ ci ++ cs1) =
              lkm.totalSize pre + lkm.totalSize ct + lkm.totalSize cs0 + lkm.totalSize ci + lkm.totalSize cs1 := by
            rw [lkm.totalSize_append, htw3]
          have reSim := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi e (pre ++ ct ++ cs0 ++ ci ++ cs1)
            ((cl0 ++ cl1) ++ post) 2 AbiReg.a0 (Or.inl rfl) heOk hVfE (by omega)
            (by simpa only [ct, cs0, ci, cs1, ce, cl0, cl1, List.append_assoc] using hlink)
            (by rw [htw4]; rw [htw_all] at h64; dsimp only [ce] at h64; omega) st4 (by rw [htw4, ← htw3]; exact hpc4)
            (hpres04.abi.gp.trans hgp) (ht5.of_preserved hpres04) (hpres04.abi.sp.trans hsp)
            (ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) heq04 hmemRel)
            (ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) (hpres04.mono (fun _ h => False.elim h)) heq04 hframeOk)
          rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨ve, hve⟩ | hve
          · simp only [hve] at reSim ⊢
            obtain ⟨k3, st5, hrun5, hpc5, ha0_5, hpres5, heq5⟩ := reSim
            have htw5 : lkm.totalSize (pre ++ ct ++ cs0 ++ ci ++ cs1 ++ ce) =
                lkm.totalSize pre + lkm.totalSize ct + lkm.totalSize cs0 + lkm.totalSize ci + lkm.totalSize cs1 + lkm.totalSize ce := by
              rw [lkm.totalSize_append, htw4]
            have hsp5 : st5.getReg AbiReg.sp = sp := hpres5.abi.sp.trans (hpres04.abi.sp.trans hsp)
            have halL0 : isAligned (st5.getReg AbiReg.sp + BitVec.ofInt 64 (fl.tempSlotOff 0)) 8 = true := by
              rw [hsp5, tempSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hspAlign _
            obtain ⟨st6, hrunL0, hothL0, ht0_6, hmemL0, hpc6⟩ :=
              loadMemOff_ld_correct_lm lkm env.hrom (pre ++ ct ++ cs0 ++ ci ++ cs1 ++ ce) (cl1 ++ post)
                AbiReg.t0 AbiReg.sp AbiReg.t1 (by decide) (by decide) (by decide) (fl.tempSlotOff 0)
                (by simpa only [ct, cs0, ci, cs1, ce, cl0, cl1, List.append_assoc] using hlink)
                (by rw [htw5]; rw [htw_all] at h64; dsimp only [cl0] at h64 ⊢; omega) st5 (by rw [htw5, ← htw4]; exact hpc5) halL0
            have htw6 : lkm.totalSize (pre ++ ct ++ cs0 ++ ci ++ cs1 ++ ce ++ cl0) =
                lkm.totalSize pre + lkm.totalSize ct + lkm.totalSize cs0 + lkm.totalSize ci + lkm.totalSize cs1 + lkm.totalSize ce + lkm.totalSize cl0 := by
              rw [lkm.totalSize_append, htw5]
            have hsp6 : st6.getReg AbiReg.sp = sp := (hothL0 AbiReg.sp (by decide) (by decide)).trans hsp5
            have halL1 : isAligned (st6.getReg AbiReg.sp + BitVec.ofInt 64 (fl.tempSlotOff 1)) 8 = true := by
              rw [hsp6, tempSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hspAlign _
            obtain ⟨st7, hrunL1, hothL1, ht3_7, hmemL1, hpc7⟩ :=
              loadMemOff_ld_correct_lm lkm env.hrom (pre ++ ct ++ cs0 ++ ci ++ cs1 ++ ce ++ cl0) post
                AbiReg.t3 AbiReg.sp AbiReg.t1 (by decide) (by decide) (by decide) (fl.tempSlotOff 1)
                (by simpa only [ct, cs0, ci, cs1, ce, cl0, cl1, List.append_assoc] using hlink)
                (by rw [htw6]; rw [htw_all] at h64; dsimp only [cl1] at h64 ⊢; omega) st6 (by rw [htw6, ← htw5]; exact hpc6) halL1
            have hslot0_5 : readWord64 st5.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff 0)) = vt.toBitVec := by
              have h2 : readWord64 st2.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff 0)) = vt.toBitVec := by
                rw [hmemS0, hpres1.abi.sp.trans hsp, ha0_1]; exact readWord64_writeWord64_self st1.mem _ _
              have heq25 : MemEqOutside (tempSpanR fl sp 1) st2.mem st5.mem :=
                heq24.trans (heq5.mono (tempSpanR_mono fl sp hvalid (by omega : 1 ≤ 2) (by omega)))
              rw [← h2]; apply MemEqOutside.readWord64_eq heq25
              intro k hk; rw [tempSlotOff_ofInt]
              exact (tempSpanR_disj_tempSlot fl sp hvalid (Nat.lt_succ_self 0) (by omega)).symm _ ⟨k, hk, rfl⟩
            have hslot1_5 : readWord64 st5.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff 1)) = vi.toBitVec := by
              have h4 : readWord64 st4.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff 1)) = vi.toBitVec := by
                rw [hmemS1, hpres3.abi.sp.trans (hpres02.abi.sp.trans hsp), ha0_3]; exact readWord64_writeWord64_self st3.mem _ _
              rw [← h4]; apply MemEqOutside.readWord64_eq heq5
              intro k hk; rw [tempSlotOff_ofInt]
              exact (tempSpanR_disj_tempSlot fl sp hvalid (by omega : 1 < 2) (by omega)).symm _ ⟨k, hk, rfl⟩
            have heq05 : MemEqOutside (tempSpanR fl sp 0) st.mem st5.mem :=
              heq04.trans (heq5.mono (tempSpanR_mono fl sp hvalid (Nat.zero_le 2) (by omega)))
            exact ⟨k1 + (lkm.totalSize cs0 + (k2 + (lkm.totalSize cs1 + (k3 + (lkm.totalSize cl0 + lkm.totalSize cl1))))), st7,
              by rw [run_add, hrun1]; dsimp only; rw [run_add, hrunS0]; dsimp only
                 rw [run_add, hrun3]; dsimp only; rw [run_add, hrunS1]; dsimp only
                 rw [run_add, hrun5]; dsimp only; rw [run_add, hrunL0]; dsimp only; exact hrunL1,
              by rw [hpc7, htw6, htw_all]; exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (by dsimp only [cl1]; omega),
              by rw [hothL1 AbiReg.t0 (by decide) (by decide), ht0_6, hsp5, hslot0_5],
              by rw [ht3_7, hmemL0, hsp6, hslot1_5],
              (hothL1 AbiReg.a0 (by decide) (by decide)).trans ((hothL0 AbiReg.a0 (by decide) (by decide)).trans ha0_5),
              hpres04.trans ((PreservedFrameRegs.of_a0 hpres5).trans
                ((PreservedFrameRegs.of_scratch2 AbiReg.t0 AbiReg.t1 (by decide) (by decide) hothL0).trans
                 (PreservedFrameRegs.of_scratch2 AbiReg.t3 AbiReg.t1 (by decide) (by decide) hothL1))),
              by rw [hmemL1, hmemL0]; exact heq05⟩
          · simp only [hve] at reSim ⊢
            obtain ⟨k3, st5, hrun5, hpc5, hpres5, heq5⟩ := reSim
            exact ⟨k1 + (lkm.totalSize cs0 + (k2 + (lkm.totalSize cs1 + k3))), st5,
              by rw [run_add, hrun1]; dsimp only; rw [run_add, hrunS0]; dsimp only
                 rw [run_add, hrun3]; dsimp only; rw [run_add, hrunS1]; dsimp only; exact hrun5,
              hpc5, hpres04.trans (PreservedFrameRegs.of_a0 hpres5),
              heq04.trans (heq5.mono (tempSpanR_mono fl sp hvalid (Nat.zero_le 2) (by omega)))⟩
        · simp only [hvi] at riSim ⊢
          obtain ⟨k2, st3, hrun3, hpc3, hpres3, heq3⟩ := riSim
          exact ⟨k1 + (lkm.totalSize cs0 + k2), st3,
            by rw [run_add, hrun1]; dsimp only; rw [run_add, hrunS0]; dsimp only; exact hrun3,
            hpc3, hpres02.trans (PreservedFrameRegs.of_a0 hpres3),
            heq02.trans (heq3.mono (tempSpanR_mono fl sp hvalid (Nat.zero_le 1) (by omega)))⟩
      · simp only [hvt] at rtSim ⊢
        obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := rtSim
        exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩

theorem preservedFrameRegs_of_t6_s1 {fl : FrameLayout} {excl : Reg → Prop} {s1 s2 : State}
    (heq : ∀ q, q ≠ AbiReg.t6 ∧ q ≠ AbiReg.s1 → s2.getReg q = s1.getReg q) :
    PreservedFrameRegs fl excl s1 s2 :=
  ⟨⟨heq _ (by decide), heq _ (by decide), heq _ (by decide), heq _ (by decide)⟩,
   fun _ => heq _ (by decide),
   fun _ => heq _ (by decide),
   fun r hr _ => heq r ⟨allowedRegs_ne_t6 hr, allowedRegs_ne_s1 hr⟩⟩

end ConAgua.RISCV.Compiler
