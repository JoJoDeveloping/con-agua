import ConAgua.Checker.ProgWf
import ConAgua.Checker.ProgTree
import ConAgua.RISCV.Compiler.ProgSimMain
import ConAgua.RISCV.Bridge.CheckerIso
import ConAgua.RISCV.Bridge.CheckerProgScan
import ConAgua.RISCV.Bridge.CheckerProgIScan

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Fast Kernel Reflection Well-Formedness Proofs (`ConAgua.RISCV.Bridge.CheckerWfFast`)

Proves inside Lean's kernel (zero `sorry`, zero `native_decide`, zero `bv_decide`,
axioms strictly `[propext, Classical.choice, Quot.sound]`):
1. `checkerProgMini_fnNames_nodup` & `checkerProgIMini_fnNames_nodup`:
   `(checkerProgMini.map Prod.fst).Nodup` and `(checkerProgIMini.map Prod.fst).Nodup`
   via `L.Compiler.progTree_spec`.
2. `checkerTabMini_romSlices_ok` & `romSliceOkFast_sound`:
   all 11 distinct ROM slices used across `checkerProgMini` and `checkerProgIMini`
   satisfy `ConAgua.RISCV.Compiler.Tab.romSliceOkB checkerTabMini d = true`, with a cached
   fast checker `romSliceOkFast` proven sound against `Tab.romSliceOkB`.
3. `checkerProgMini_progArgsOkB` & `checkerProgIMini_progArgsOkB`:
   `ConAgua.RISCV.Compiler.progArgsOkB checkerProgMini = true` and
   `ConAgua.RISCV.Compiler.progArgsOkB checkerProgIMini = true`.
-/

namespace ConAgua.RISCV.Bridge

open ConAgua.RISCV.Compiler

/-! ## 1. Distinct Function Names (`Nodup`) -/

theorem checkerProgMini_fnNames_nodup :
    (checkerProgMini.map Prod.fst).Nodup :=
  (L.Compiler.progTree_spec L.Checker.checkerProg_wf.tree_eq).1

theorem checkerProgIMini_fnNames_nodup :
    (checkerProgIMini.map Prod.fst).Nodup :=
  (L.Compiler.progTree_spec L.Checker.checkerProgI_wf.tree_eq).1

/-! ## 2. `progArgsOkB` for Both `checkerProgMini` and `checkerProgIMini` -/

private theorem stmtMayFallL_eq : ∀ s : L.Stmt,
    stmtMayFallthrough s = stmtMayFallL s
  | .skip | .brk | .abort _ | .set _ _ | .gset _ _ | .st8 _ _ _ | .st64 _ _ _
  | .ret _ | .call _ _ _ | .st64t _ _ _ _ | .st32t _ _ _ _
  | .copy64 _ _ _ _ _ | .copy8w _ _ _ _ _ | .scan8 _ _ _ _ _ | .while _ _ => rfl
  | .seq s₁ s₂ => by
    simp only [stmtMayFallthrough, stmtMayFallL, stmtMayFallL_eq s₁, stmtMayFallL_eq s₂]
  | .ite _ s₁ s₂ => by
    simp only [stmtMayFallthrough, stmtMayFallL, stmtMayFallL_eq s₁, stmtMayFallL_eq s₂]

private theorem stmtMinRetRawL_eq : ∀ s : L.Stmt,
    stmtMinRetRaw s = stmtMinRetRawL s
  | .skip | .brk | .abort _ | .set _ _ | .gset _ _ | .st8 _ _ _ | .st64 _ _ _
  | .call _ _ _ | .st64t _ _ _ _ | .st32t _ _ _ _
  | .copy64 _ _ _ _ _ | .copy8w _ _ _ _ _ | .scan8 _ _ _ _ _ => rfl
  | .ret es => rfl
  | .seq s₁ s₂ => by
    dsimp only [stmtMinRetRaw, stmtMinRetRawL]
    rw [stmtMinRetRawL_eq s₁, stmtMinRetRawL_eq s₂]
    cases stmtMinRetRawL s₁ <;> cases stmtMinRetRawL s₂ <;> rfl
  | .ite _ s₁ s₂ => by
    dsimp only [stmtMinRetRaw, stmtMinRetRawL]
    rw [stmtMinRetRawL_eq s₁, stmtMinRetRawL_eq s₂]
    cases stmtMinRetRawL s₁ <;> cases stmtMinRetRawL s₂ <;> rfl
  | .while _ b => by
    dsimp only [stmtMinRetRaw, stmtMinRetRawL]
    exact stmtMinRetRawL_eq b

private theorem fnMinRetL_eq (fd : L.FunDecl) :
    fnMinRet fd = fnMinRetL fd := by
  dsimp only [fnMinRet, fnMinRetL]
  rw [stmtMayFallL_eq, stmtMinRetRawL_eq]
  cases stmtMayFallL fd.body with
  | true => simp only [eq_self, ↓reduceIte]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases stmtMinRetRawL fd.body <;> rfl

private theorem mem_of_lookup_some_wf {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List (α × β)) {k : α} {v : β}, l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => by simp at h
  | (a, b) :: t, k, v, h => by
    simp only [List.lookup] at h
    by_cases hka : (k == a) = true
    · simp only [hka] at h; cases Option.some.inj h; rw [eq_of_beq hka]; exact List.Mem.head _
    · have hf : (k == a) = false := Bool.eq_false_iff.mpr hka
      simp only [hf] at h; exact List.Mem.tail _ (mem_of_lookup_some_wf t h)

private theorem stmtMinRetRawL_pos (s : L.Stmt) : ∀ {k : Nat},
    stmtMinRetRawL s = some k → 1 ≤ k := by
  induction s with
  | ret es => intro k h; simp only [stmtMinRetRawL, Option.some.injEq] at h; omega
  | seq s₁ s₂ ih1 ih2 =>
    intro k h; dsimp only [stmtMinRetRawL] at h
    cases h1 : stmtMinRetRawL s₁ with
    | none => rw [h1] at h; exact ih2 h
    | some a =>
      cases h2 : stmtMinRetRawL s₂ with
      | none => rw [h1, h2] at h; cases h; exact ih1 h1
      | some b =>
        rw [h1, h2] at h; simp only [Option.some.injEq] at h
        have ha := ih1 h1; have hb := ih2 h2; omega
  | ite _ s₁ s₂ ih1 ih2 =>
    intro k h; dsimp only [stmtMinRetRawL] at h
    cases h1 : stmtMinRetRawL s₁ with
    | none => rw [h1] at h; exact ih2 h
    | some a =>
      cases h2 : stmtMinRetRawL s₂ with
      | none => rw [h1, h2] at h; cases h; exact ih1 h1
      | some b =>
        rw [h1, h2] at h; simp only [Option.some.injEq] at h
        have ha := ih1 h1; have hb := ih2 h2; omega
  | «while» _ b ih => intro k h; exact ih h
  | _ => intro k h; cases h

private theorem fnMinRetL_pos (fd : L.FunDecl) : 1 ≤ fnMinRetL fd := by
  dsimp only [fnMinRetL]
  split
  · exact Nat.le_refl 1
  · cases h : stmtMinRetRawL fd.body with
    | none => simp
    | some k => exact stmtMinRetRawL_pos fd.body h

private theorem stmt_wf_imp_stmtArgsOkB {p : L.Prog} {rt : L.Compiler.NTree}
    (hrt : ∀ x ∈ p, (rt.find (L.Compiler.nameCode x.1)).getD 1 ≤ fnMinRetL x.2) :
    ∀ {nl : Nat} {tab : L.Compiler.Tab} {s : L.Stmt},
      L.Compiler.Stmt.wf p nl tab s = true →
      stmtRetOkNTree rt s = true →
      stmtArgsOkB p s = true
  | _, _, .skip, _, _ | _, _, .brk, _, _ | _, _, .abort _, _, _ | _, _, .set _ _, _, _
  | _, _, .st8 _ _ _, _, _ | _, _, .st64 _ _ _, _, _ | _, _, .ret _, _, _ | _, _, .gset _ _, _, _
  | _, _, .st64t _ _ _ _, _, _ | _, _, .copy64 _ _ _ _ _, _, _
  | _, _, .copy8w _ _ _ _ _, _, _ | _, _, .scan8 _ _ _ _ _, _, _ | _, _, .st32t _ _ _ _, _, _ => rfl
  | nl, tab, .seq s₁ s₂, h, hr => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true] at h
    simp only [stmtRetOkNTree, Bool.and_eq_true] at hr
    simp only [stmtArgsOkB, Bool.and_eq_true]
    exact ⟨stmt_wf_imp_stmtArgsOkB hrt h.1 hr.1, stmt_wf_imp_stmtArgsOkB hrt h.2 hr.2⟩
  | nl, tab, .ite c s₁ s₂, h, hr => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true] at h
    simp only [stmtRetOkNTree, Bool.and_eq_true] at hr
    simp only [stmtArgsOkB, Bool.and_eq_true]
    exact ⟨stmt_wf_imp_stmtArgsOkB hrt h.1.2 hr.1, stmt_wf_imp_stmtArgsOkB hrt h.2 hr.2⟩
  | nl, tab, .while c s, h, hr => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true] at h
    simp only [stmtRetOkNTree] at hr
    simp only [stmtArgsOkB]
    exact stmt_wf_imp_stmtArgsOkB hrt h.2 hr
  | nl, tab, .call xs f args, h, hr => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true] at h
    simp only [stmtArgsOkB]
    rcases h with ⟨_, hcall⟩
    cases hlook : p.lookup f with
    | none => rw [hlook] at hcall; cases hcall
    | some fd =>
      rw [hlook] at hcall
      have heq : args.length = fd.nparams := by simpa using hcall
      have hmem : (f, fd) ∈ p := mem_of_lookup_some_wf p hlook
      have hbound := hrt (f, fd) hmem
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨heq, ?_⟩
      change xs.length ≤ fnMinRet fd
      rw [fnMinRetL_eq]
      dsimp only [stmtRetOkNTree] at hr
      by_cases h1 : xs.length ≤ 1
      · exact Nat.le_trans h1 (fnMinRetL_pos fd)
      · simp only [h1, ↓reduceIte] at hr
        cases hf : rt.find (L.Compiler.nameCode f) with
        | none => rw [hf] at hr; cases hr
        | some r =>
          rw [hf] at hr hbound
          simp only [Option.getD_some] at hbound
          exact Nat.le_trans (of_decide_eq_true hr) hbound

private def stmtArgsOkNTree (t rt : L.Compiler.NTree) : L.Stmt → Bool
  | .seq s₁ s₂ => stmtArgsOkNTree t rt s₁ && stmtArgsOkNTree t rt s₂
  | .ite _ s₁ s₂ => stmtArgsOkNTree t rt s₁ && stmtArgsOkNTree t rt s₂
  | .while _ s => stmtArgsOkNTree t rt s
  | .call xs f args =>
    (match t.find (L.Compiler.nameCode f) with
    | some n => decide (args.length = n)
    | none => false) &&
    (if xs.length ≤ 1 then true
     else match rt.find (L.Compiler.nameCode f) with
      | some r => decide (xs.length ≤ r)
      | none => false)
  | _ => true

private theorem stmtArgsOkNTree_sound {p : L.Prog} {t rt : L.Compiler.NTree}
    (ht : ∀ f, t.find (L.Compiler.nameCode f) = (p.lookup f).map (·.nparams))
    (hrt : ∀ x ∈ p, (rt.find (L.Compiler.nameCode x.1)).getD 1 ≤ fnMinRetL x.2) :
    ∀ {s : L.Stmt}, stmtArgsOkNTree t rt s = true →
      stmtArgsOkB p s = true
  | .skip, _ | .brk, _ | .abort _, _ | .set _ _, _ | .st8 _ _ _, _ | .st64 _ _ _, _
  | .ret _, _ | .gset _ _, _ | .st64t _ _ _ _, _ | .copy64 _ _ _ _ _, _
  | .copy8w _ _ _ _ _, _ | .scan8 _ _ _ _ _, _ | .st32t _ _ _ _, _ => rfl
  | .seq s₁ s₂, h => by
    simp only [stmtArgsOkNTree, Bool.and_eq_true] at h
    simp only [stmtArgsOkB, Bool.and_eq_true]
    exact ⟨stmtArgsOkNTree_sound ht hrt h.1, stmtArgsOkNTree_sound ht hrt h.2⟩
  | .ite _ s₁ s₂, h => by
    simp only [stmtArgsOkNTree, Bool.and_eq_true] at h
    simp only [stmtArgsOkB, Bool.and_eq_true]
    exact ⟨stmtArgsOkNTree_sound ht hrt h.1, stmtArgsOkNTree_sound ht hrt h.2⟩
  | .while _ s, h => by
    simp only [stmtArgsOkNTree] at h
    simp only [stmtArgsOkB]
    exact stmtArgsOkNTree_sound ht hrt h
  | .call xs f args, h => by
    simp only [stmtArgsOkNTree, Bool.and_eq_true] at h
    rcases h with ⟨harg, hret⟩
    rw [ht f] at harg
    simp only [stmtArgsOkB]
    cases hlook : p.lookup f with
    | none => rw [hlook] at harg; cases harg
    | some fd =>
      rw [hlook] at harg
      simp only [Option.map_some, Bool.and_eq_true, decide_eq_true_eq] at harg ⊢
      refine ⟨harg, ?_⟩
      change xs.length ≤ fnMinRet fd
      rw [fnMinRetL_eq]
      have hbound := hrt (f, fd) (mem_of_lookup_some_wf p hlook)
      by_cases h1 : xs.length ≤ 1
      · exact Nat.le_trans h1 (fnMinRetL_pos fd)
      · simp only [h1, ↓reduceIte] at hret
        cases hf : rt.find (L.Compiler.nameCode f) with
        | none => rw [hf] at hret; cases hret
        | some r =>
          rw [hf] at hret hbound
          simp only [Option.getD_some] at hbound
          exact Nat.le_trans (of_decide_eq_true hret) hbound

/-! ## 3. All 11 ROM Slices Used Across `checkerProgMini` & `checkerProgIMini` -/

private theorem riscv_romIdx_eq_agua (d : List UInt8) :
    ∀ l : List UInt8, ConAgua.RISCV.Compiler.romIdx d l = L.Compiler.romIdx d l
  | [] => rfl
  | b :: rest => by
    simp only [ConAgua.RISCV.Compiler.romIdx, L.Compiler.romIdx, riscv_romIdx_eq_agua d rest]

private theorem romIdx_nil : ∀ l : List UInt8, L.Compiler.romIdx [] l = 0
  | [] => rfl
  | _ :: _ => rfl

private theorem romSliceOkB_of_agua_romOk (t : L.Compiler.Tab) (d : List UInt8)
    (hok : L.Compiler.romOk t d = true) :
    (toRiscvTab t).romSliceOkB d = true := by
  cases d with
  | nil =>
    simp only [Tab.romSliceOkB, toRiscvTab, riscv_romIdx_eq_agua, romIdx_nil,
      List.length_nil, Nat.add_zero, List.range_zero, List.all_nil, Bool.and_true, decide_eq_true_eq]
    exact Nat.zero_le _
  | cons b bs =>
    have hpref : (b :: bs) <+: t.rom.drop (L.Compiler.romIdx (b :: bs) t.rom) :=
      List.isPrefixOf_iff_prefix.mp hok
    have hlen : (b :: bs).length ≤ (t.rom.drop (L.Compiler.romIdx (b :: bs) t.rom)).length := hpref.length_le
    rw [List.length_drop] at hlen
    have hpos : 0 < (b :: bs).length := by simp
    have hbound : L.Compiler.romIdx (b :: bs) t.rom + (b :: bs).length ≤ t.rom.length := by omega
    simp only [Tab.romSliceOkB, toRiscvTab, riscv_romIdx_eq_agua, Bool.and_eq_true,
      decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq]
    refine ⟨hbound, fun j hj => ?_⟩
    have hget := (hpref.getElem hj).symm
    have hidx : L.Compiler.romIdx (b :: bs) t.rom + j < t.rom.length := by omega
    simp only [List.getElem_drop] at hget
    rw [List.getElem?_eq_getElem hidx, List.getElem?_eq_getElem hj, hget]

private theorem bsrc_wf_roms {tab : L.Compiler.Tab} : ∀ {b : L.BSrc},
    L.Compiler.BSrc.wf tab b = true → ∀ d ∈ L.Compiler.BSrc.roms b, L.Compiler.romOk tab d = true
  | .arr _, _, d, hd => by simp [L.Compiler.BSrc.roms] at hd
  | .rom d₀, h, d, hd => by
    simp only [L.Compiler.BSrc.wf, L.Compiler.BSrc.roms, L.Compiler.romOk,
      Bool.and_eq_true, List.mem_singleton] at h hd ⊢
    subst hd; exact h.1

private theorem expr_wf_roms {nl : Nat} {tab : L.Compiler.Tab} : ∀ {e : L.Expr},
    L.Compiler.Expr.wf nl tab e = true → ∀ d ∈ L.Compiler.Expr.roms e, L.Compiler.romOk tab d = true
  | .const _, _, d, hd | .var _, _, d, hd | .len8 _, _, d, hd | .len64 _, _, d, hd
  | .glob _, _, d, hd => by simp [L.Compiler.Expr.roms] at hd
  | .bin _ a b, h, d, hd | .cmpw _ a b, h, d, hd => by
    simp only [L.Compiler.Expr.wf, Bool.and_eq_true, L.Compiler.Expr.roms, List.mem_append] at h hd
    rcases hd with hd | hd
    · exact expr_wf_roms h.1 d hd
    · exact expr_wf_roms h.2 d hd
  | .ld8 _ i, h, d, hd | .ld64 _ i, h, d, hd => by
    simp only [L.Compiler.Expr.wf, Bool.and_eq_true, L.Compiler.Expr.roms] at h hd
    exact expr_wf_roms h.2 d hd
  | .ldc d₀ i, h, d, hd => by
    simp only [L.Compiler.Expr.wf, Bool.and_eq_true, L.Compiler.Expr.roms, List.mem_cons] at h hd
    rcases hd with rfl | hd
    · exact h.1
    · exact expr_wf_roms h.2 d hd
  | .ld64t _ t i, h, d, hd | .ld32t _ t i, h, d, hd | .ld32h _ t i _, h, d, hd => by
    simp only [L.Compiler.Expr.wf, Bool.and_eq_true, L.Compiler.Expr.roms, List.mem_append] at h hd
    rcases hd with hd | hd
    · exact expr_wf_roms h.1.2 d hd
    · exact expr_wf_roms h.2 d hd
  | .len64t _ t, h, d, hd => by
    simp only [L.Compiler.Expr.wf, Bool.and_eq_true, L.Compiler.Expr.roms] at h hd
    exact expr_wf_roms h.2 d hd
  | .ld8x8 b i, h, d, hd => by
    simp only [L.Compiler.Expr.wf, Bool.and_eq_true, L.Compiler.Expr.roms, List.mem_append] at h hd
    rcases hd with hd | hd
    · exact bsrc_wf_roms h.1 d hd
    · exact expr_wf_roms h.2 d hd

private theorem cond_wf_roms {nl : Nat} {tab : L.Compiler.Tab} : ∀ {c : L.Cond},
    L.Compiler.Cond.wf nl tab c = true → ∀ d ∈ L.Compiler.Cond.roms c, L.Compiler.romOk tab d = true
  | .cmp _ a b, h, d, hd => by
    simp only [L.Compiler.Cond.wf, Bool.and_eq_true, L.Compiler.Cond.roms, List.mem_append] at h hd
    rcases hd with hd | hd
    · exact expr_wf_roms h.1 d hd
    · exact expr_wf_roms h.2 d hd
  | .and p q, h, d, hd | .or p q, h, d, hd => by
    simp only [L.Compiler.Cond.wf, Bool.and_eq_true, L.Compiler.Cond.roms, List.mem_append] at h hd
    rcases hd with hd | hd
    · exact cond_wf_roms h.1 d hd
    · exact cond_wf_roms h.2 d hd
  | .not p, h, d, hd => cond_wf_roms (c := p) h d hd

private theorem warr_wf_roms {nl : Nat} {tab : L.Compiler.Tab} : ∀ {w : L.WArr},
    L.Compiler.WArr.wf nl tab w = true → ∀ d ∈ L.Compiler.WArr.roms w, L.Compiler.romOk tab d = true
  | .plain _, _, d, hd => by simp [L.Compiler.WArr.roms] at hd
  | .tier _ t, h, d, hd => by
    simp only [L.Compiler.WArr.wf, Bool.and_eq_true, L.Compiler.WArr.roms] at h hd
    exact expr_wf_roms h.2 d hd

private theorem opnd_wf_roms {nl : Nat} {tab : L.Compiler.Tab} {e : L.Expr}
    (h : L.Compiler.Expr.opndWf nl tab e = true) :
    ∀ d ∈ L.Compiler.Expr.roms e, L.Compiler.romOk tab d = true := by
  simp only [L.Compiler.Expr.opndWf, Bool.and_eq_true] at h
  exact expr_wf_roms h.2

private theorem stmt_wf_roms {p : L.Prog} {nl : Nat} {tab : L.Compiler.Tab} : ∀ {s : L.Stmt},
    L.Compiler.Stmt.wf p nl tab s = true → ∀ d ∈ L.Compiler.Stmt.roms s, L.Compiler.romOk tab d = true
  | .skip, _, d, hd | .brk, _, d, hd => by simp [L.Compiler.Stmt.roms] at hd
  | .abort e, h, d, hd => expr_wf_roms h d hd
  | .set _ e, h, d, hd | .gset _ e, h, d, hd => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true, L.Compiler.Stmt.roms] at h hd
    exact expr_wf_roms h.2 d hd
  | .st8 _ i e, h, d, hd | .st64 _ i e, h, d, hd => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true, L.Compiler.Stmt.roms, List.mem_append] at h hd
    rcases hd with hd | hd
    · exact expr_wf_roms h.1.2 d hd
    · exact expr_wf_roms h.2 d hd
  | .seq s₁ s₂, h, d, hd => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true, L.Compiler.Stmt.roms, List.mem_append] at h hd
    rcases hd with hd | hd
    · exact stmt_wf_roms h.1 d hd
    · exact stmt_wf_roms h.2 d hd
  | .ite c s₁ s₂, h, d, hd => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true, L.Compiler.Stmt.roms, List.mem_append] at h hd
    rcases hd with (hd | hd) | hd
    · exact cond_wf_roms h.1.1 d hd
    · exact stmt_wf_roms h.1.2 d hd
    · exact stmt_wf_roms h.2 d hd
  | .while c s, h, d, hd => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true, L.Compiler.Stmt.roms, List.mem_append] at h hd
    rcases hd with hd | hd
    · exact cond_wf_roms h.1 d hd
    · exact stmt_wf_roms h.2 d hd
  | .ret es, h, d, hd => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true, List.all_eq_true,
      L.Compiler.Stmt.roms, List.mem_flatMap] at h hd
    rcases hd with ⟨e, he, hd⟩
    exact expr_wf_roms (h.1 e he) d hd
  | .call _ _ args, h, d, hd => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true, List.all_eq_true,
      L.Compiler.Stmt.roms, List.mem_flatMap] at h hd
    rcases hd with ⟨e, he, hd⟩
    exact expr_wf_roms (h.1.2 e he) d hd
  | .st64t _ t i e, h, d, hd | .st32t _ t i e, h, d, hd => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true, L.Compiler.Stmt.roms, List.mem_append] at h hd
    rcases hd with (hd | hd) | hd
    · exact expr_wf_roms h.1.1.2 d hd
    · exact expr_wf_roms h.1.2 d hd
    · exact expr_wf_roms h.2 d hd
  | .copy64 dst di src si n, h, d, hd => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true, L.Compiler.Stmt.roms, List.mem_append] at h hd
    rcases hd with (((hd | hd) | hd) | hd) | hd
    · exact warr_wf_roms h.1.1.1.1 d hd
    · exact opnd_wf_roms h.1.1.1.2 d hd
    · exact warr_wf_roms h.1.1.2 d hd
    · exact opnd_wf_roms h.1.2 d hd
    · exact opnd_wf_roms h.2 d hd
  | .copy8w dst di src si n, h, d, hd => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true, L.Compiler.Stmt.roms, List.mem_append] at h hd
    rcases hd with (((hd | hd) | hd) | hd) | hd
    · exact warr_wf_roms h.1.1.1.1 d hd
    · exact opnd_wf_roms h.1.1.1.2 d hd
    · exact bsrc_wf_roms h.1.1.2 d hd
    · exact opnd_wf_roms h.1.2 d hd
    · exact opnd_wf_roms h.2 d hd
  | .scan8 _ s i e c, h, d, hd => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true, L.Compiler.Stmt.roms,
      List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at h hd
    rcases hd with ((hd | hd) | hd) | rfl
    · exact bsrc_wf_roms h.1.1.1.1.2 d hd
    · exact opnd_wf_roms h.1.1.1.2 d hd
    · exact opnd_wf_roms h.1.1.2 d hd
    · exact h.2

/-- Cached ROM-slice checker over `checkerAllowedRoms`. -/
def romSliceOkFast (d : List UInt8) : Bool :=
  checkerAllowedRoms.elem d

private theorem checkerProgI_roms_ok :
    ∀ x ∈ L.Checker.checkerProgI, ∀ d ∈ L.Compiler.Stmt.roms x.2.body,
      L.Compiler.romOk L.Checker.checkerTab d = true := by
  have hwf := L.Checker.checkerProgI_wf
  rw [L.Compiler.Prog.wf_eq] at hwf
  simp only [L.Compiler.Prog.wfSpec, Bool.and_eq_true, List.all_eq_true] at hwf
  intro x hx d hd
  have hfx := hwf.1.1 x hx
  rw [L.Compiler.FunDecl.wf_eq] at hfx
  simp only [L.Compiler.FunDecl.wfSpec, Bool.and_eq_true] at hfx
  exact stmt_wf_roms hfx.1.2 d hd

private theorem checkerProgI_romSlices_ok :
    ∀ x ∈ L.Checker.checkerProgI, ∀ d ∈ L.Compiler.Stmt.roms x.2.body,
      checkerTabMini.romSliceOkB d = true := by
  intro x hx d hd
  exact romSliceOkB_of_agua_romOk L.Checker.checkerTab d (checkerProgI_roms_ok x hx d hd)

/-- Soundness of the cached ROM slice predicate `romSliceOkFast` against `Tab.romSliceOkB`. -/
theorem romSliceOkFast_sound {d : List UInt8} (h : romSliceOkFast d = true) :
    checkerTabMini.romSliceOkB d = true := by
  simp only [romSliceOkFast, checkerAllowedRoms, List.elem_eq_mem, decide_eq_true_eq,
    List.mem_flatMap] at h
  rcases h with ⟨i, _, hi⟩
  split at hi
  · rename_i x hget
    have hx : x ∈ L.Checker.checkerProgI := List.mem_of_getElem? hget
    exact checkerProgI_romSlices_ok x hx d hi
  · cases hi

private theorem bsrcRomsOk_sound {romOk : List UInt8 → Bool} : ∀ {b : L.BSrc},
    bsrcRomsOk romOk b = true → ∀ d ∈ L.Compiler.BSrc.roms b, romOk d = true
  | .arr _, _, d, hd => by simp [L.Compiler.BSrc.roms] at hd
  | .rom d₀, h, d, hd => by
    simp only [L.Compiler.BSrc.roms, List.mem_singleton] at hd
    subst hd; exact h

private theorem exprRomsOk_sound {romOk : List UInt8 → Bool} : ∀ {e : L.Expr},
    exprRomsOk romOk e = true → ∀ d ∈ L.Compiler.Expr.roms e, romOk d = true
  | .const _, _, d, hd | .var _, _, d, hd | .len8 _, _, d, hd | .len64 _, _, d, hd
  | .glob _, _, d, hd => by simp [L.Compiler.Expr.roms] at hd
  | .bin _ a b, h, d, hd | .cmpw _ a b, h, d, hd => by
    simp only [exprRomsOk, Bool.and_eq_true, L.Compiler.Expr.roms, List.mem_append] at h hd
    rcases hd with hd | hd
    · exact exprRomsOk_sound h.1 d hd
    · exact exprRomsOk_sound h.2 d hd
  | .ld8 _ i, h, d, hd | .ld64 _ i, h, d, hd | .len64t _ i, h, d, hd => by
    simp only [exprRomsOk, L.Compiler.Expr.roms] at h hd
    exact exprRomsOk_sound h d hd
  | .ldc d₀ i, h, d, hd => by
    simp only [exprRomsOk, Bool.and_eq_true, L.Compiler.Expr.roms, List.mem_cons] at h hd
    rcases hd with rfl | hd
    · exact h.1
    · exact exprRomsOk_sound h.2 d hd
  | .ld64t _ t i, h, d, hd | .ld32t _ t i, h, d, hd | .ld32h _ t i _, h, d, hd => by
    simp only [exprRomsOk, Bool.and_eq_true, L.Compiler.Expr.roms, List.mem_append] at h hd
    rcases hd with hd | hd
    · exact exprRomsOk_sound h.1 d hd
    · exact exprRomsOk_sound h.2 d hd
  | .ld8x8 b i, h, d, hd => by
    simp only [exprRomsOk, Bool.and_eq_true, L.Compiler.Expr.roms, List.mem_append] at h hd
    rcases hd with hd | hd
    · exact bsrcRomsOk_sound h.1 d hd
    · exact exprRomsOk_sound h.2 d hd

private theorem condRomsOk_sound {romOk : List UInt8 → Bool} : ∀ {c : L.Cond},
    condRomsOk romOk c = true → ∀ d ∈ L.Compiler.Cond.roms c, romOk d = true
  | .cmp _ a b, h, d, hd => by
    simp only [condRomsOk, Bool.and_eq_true, L.Compiler.Cond.roms, List.mem_append] at h hd
    rcases hd with hd | hd
    · exact exprRomsOk_sound h.1 d hd
    · exact exprRomsOk_sound h.2 d hd
  | .and p q, h, d, hd | .or p q, h, d, hd => by
    simp only [condRomsOk, Bool.and_eq_true, L.Compiler.Cond.roms, List.mem_append] at h hd
    rcases hd with hd | hd
    · exact condRomsOk_sound h.1 d hd
    · exact condRomsOk_sound h.2 d hd
  | .not p, h, d, hd => condRomsOk_sound (c := p) h d hd

private theorem warrRomsOk_sound {romOk : List UInt8 → Bool} : ∀ {w : L.WArr},
    warrRomsOk romOk w = true → ∀ d ∈ L.Compiler.WArr.roms w, romOk d = true
  | .plain _, _, d, hd => by simp [L.Compiler.WArr.roms] at hd
  | .tier _ t, h, d, hd => exprRomsOk_sound h d hd

private theorem stmtArgsAndRomsOk_sound {t rt : L.Compiler.NTree} {romOk : List UInt8 → Bool} :
    ∀ {s : L.Stmt}, stmtArgsAndRomsOk t rt romOk s = true →
      stmtArgsOkNTree t rt s = true ∧ (∀ d ∈ L.Compiler.Stmt.roms s, romOk d = true)
  | .skip, _ | .brk, _ => ⟨rfl, fun d hd => by simp [L.Compiler.Stmt.roms] at hd⟩
  | .abort e, h => ⟨rfl, exprRomsOk_sound h⟩
  | .set _ e, h | .gset _ e, h => ⟨rfl, exprRomsOk_sound h⟩
  | .st8 _ i e, h | .st64 _ i e, h => by
    simp only [stmtArgsAndRomsOk, Bool.and_eq_true, L.Compiler.Stmt.roms, List.mem_append] at h ⊢
    refine ⟨rfl, fun d hd => ?_⟩
    rcases hd with hd | hd
    · exact exprRomsOk_sound h.1 d hd
    · exact exprRomsOk_sound h.2 d hd
  | .seq s₁ s₂, h => by
    simp only [stmtArgsAndRomsOk, Bool.and_eq_true, stmtArgsOkNTree, L.Compiler.Stmt.roms, List.mem_append] at h ⊢
    have ih1 := stmtArgsAndRomsOk_sound h.1
    have ih2 := stmtArgsAndRomsOk_sound h.2
    refine ⟨⟨ih1.1, ih2.1⟩, fun d hd => ?_⟩
    rcases hd with hd | hd
    · exact ih1.2 d hd
    · exact ih2.2 d hd
  | .ite c s₁ s₂, h => by
    simp only [stmtArgsAndRomsOk, Bool.and_eq_true, stmtArgsOkNTree, L.Compiler.Stmt.roms, List.mem_append] at h ⊢
    have ih1 := stmtArgsAndRomsOk_sound h.1.2
    have ih2 := stmtArgsAndRomsOk_sound h.2
    refine ⟨⟨ih1.1, ih2.1⟩, fun d hd => ?_⟩
    rcases hd with (hd | hd) | hd
    · exact condRomsOk_sound h.1.1 d hd
    · exact ih1.2 d hd
    · exact ih2.2 d hd
  | .while c s, h => by
    simp only [stmtArgsAndRomsOk, Bool.and_eq_true, stmtArgsOkNTree, L.Compiler.Stmt.roms, List.mem_append] at h ⊢
    have ih := stmtArgsAndRomsOk_sound h.2
    refine ⟨ih.1, fun d hd => ?_⟩
    rcases hd with hd | hd
    · exact condRomsOk_sound h.1 d hd
    · exact ih.2 d hd
  | .ret es, h => by
    simp only [stmtArgsAndRomsOk, List.all_eq_true] at h
    refine ⟨rfl, fun d hd => ?_⟩
    rw [L.Compiler.Stmt.roms, List.mem_flatMap] at hd
    rcases hd with ⟨e, he, hd⟩
    exact exprRomsOk_sound (h e he) d hd
  | .call xs f args, h => by
    simp only [stmtArgsAndRomsOk, Bool.and_eq_true, List.all_eq_true, stmtArgsOkNTree] at h ⊢
    refine ⟨h.1, fun d hd => ?_⟩
    rw [L.Compiler.Stmt.roms, List.mem_flatMap] at hd
    rcases hd with ⟨e, he, hd⟩
    exact exprRomsOk_sound (h.2 e he) d hd
  | .st64t _ tt i e, h | .st32t _ tt i e, h => by
    simp only [stmtArgsAndRomsOk, Bool.and_eq_true, L.Compiler.Stmt.roms, List.mem_append] at h ⊢
    refine ⟨rfl, fun d hd => ?_⟩
    rcases hd with (hd | hd) | hd
    · exact exprRomsOk_sound h.1.1 d hd
    · exact exprRomsOk_sound h.1.2 d hd
    · exact exprRomsOk_sound h.2 d hd
  | .copy64 dst di src si n, h => by
    simp only [stmtArgsAndRomsOk, Bool.and_eq_true, L.Compiler.Stmt.roms, List.mem_append] at h ⊢
    refine ⟨rfl, fun d hd => ?_⟩
    rcases hd with (((hd | hd) | hd) | hd) | hd
    · exact warrRomsOk_sound h.1.1.1.1 d hd
    · exact exprRomsOk_sound h.1.1.1.2 d hd
    · exact warrRomsOk_sound h.1.1.2 d hd
    · exact exprRomsOk_sound h.1.2 d hd
    · exact exprRomsOk_sound h.2 d hd
  | .copy8w dst di src si n, h => by
    simp only [stmtArgsAndRomsOk, Bool.and_eq_true, L.Compiler.Stmt.roms, List.mem_append] at h ⊢
    refine ⟨rfl, fun d hd => ?_⟩
    rcases hd with (((hd | hd) | hd) | hd) | hd
    · exact warrRomsOk_sound h.1.1.1.1 d hd
    · exact exprRomsOk_sound h.1.1.1.2 d hd
    · exact bsrcRomsOk_sound h.1.1.2 d hd
    · exact exprRomsOk_sound h.1.2 d hd
    · exact exprRomsOk_sound h.2 d hd
  | .scan8 _ s i e c, h => by
    simp only [stmtArgsAndRomsOk, Bool.and_eq_true, L.Compiler.Stmt.roms,
      List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at h ⊢
    refine ⟨rfl, fun d hd => ?_⟩
    rcases hd with ((hd | hd) | hd) | rfl
    · exact bsrcRomsOk_sound h.1.1.1 d hd
    · exact exprRomsOk_sound h.1.1.2 d hd
    · exact exprRomsOk_sound h.1.2 d hd
    · exact h.2

theorem checkerProgMini_progArgsOkB :
    progArgsOkB checkerProgMini = true := by
  have htree := (L.Compiler.progTree_spec L.Checker.checkerProg_wf.tree_eq).2
  simp only [checkerProgMini, progArgsOkB, List.all_eq_true]
  intro x hx
  exact stmtArgsOkNTree_sound htree (fun y hy => (checkerProg_argsAndRoms_all y hy).1)
    (stmtArgsAndRomsOk_sound (checkerProg_argsAndRoms_all x hx).2).1

theorem checkerProgIMini_progArgsOkB :
    progArgsOkB checkerProgIMini = true := by
  have hwf := L.Checker.checkerProgI_wf
  rw [L.Compiler.Prog.wf_eq] at hwf
  simp only [L.Compiler.Prog.wfSpec, Bool.and_eq_true, List.all_eq_true] at hwf
  have hall := hwf.1.1
  simp only [checkerProgIMini, progArgsOkB, List.all_eq_true]
  intro x hx
  have hfx := hall x hx
  rw [L.Compiler.FunDecl.wf_eq] at hfx
  simp only [L.Compiler.FunDecl.wfSpec, Bool.and_eq_true] at hfx
  exact stmt_wf_imp_stmtArgsOkB (fun y hy => (checkerProgI_ret_all y hy).1) hfx.1.2 (checkerProgI_ret_all x hx).2

/-- Every ROM slice used anywhere in `checkerProgMini` or `checkerProgIMini` satisfies
    `checkerTabMini.romSliceOkB d = true`. -/
theorem checkerTabMini_romSlices_ok :
    (∀ x ∈ L.Checker.checkerProg, ∀ d ∈ L.Compiler.Stmt.roms x.2.body,
      checkerTabMini.romSliceOkB d = true) ∧
    (∀ x ∈ L.Checker.checkerProgI, ∀ d ∈ L.Compiler.Stmt.roms x.2.body,
      checkerTabMini.romSliceOkB d = true) := by
  refine ⟨fun x hx d hd => ?_, checkerProgI_romSlices_ok⟩
  have h1 := (stmtArgsAndRomsOk_sound (checkerProg_argsAndRoms_all x hx).2).2 d hd
  rw [allowedRomsLit_eq] at h1
  exact romSliceOkFast_sound h1

/-- info: 'ConAgua.RISCV.Bridge.checkerProgMini_fnNames_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgMini_fnNames_nodup

/-- info: 'ConAgua.RISCV.Bridge.checkerProgIMini_fnNames_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgIMini_fnNames_nodup

/-- info: 'ConAgua.RISCV.Bridge.checkerProgMini_progArgsOkB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgMini_progArgsOkB

/-- info: 'ConAgua.RISCV.Bridge.checkerProgIMini_progArgsOkB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgIMini_progArgsOkB

/-- info: 'ConAgua.RISCV.Bridge.romSliceOkFast_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms romSliceOkFast_sound

/-- info: 'ConAgua.RISCV.Bridge.checkerTabMini_romSlices_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerTabMini_romSlices_ok

end ConAgua.RISCV.Bridge
