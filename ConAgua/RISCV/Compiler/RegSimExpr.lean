import ConAgua.RISCV.Compiler.ProgSimBase
import ConAgua.RISCV.Compiler.ProgSimFuel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Register-Allocated Expression, Condition & Argument Simulation (`ConAgua.RISCV.Compiler.RegSimExpr`)

Forward simulation for Opt #5's translation-validated register allocator:
1. Decidable validator soundness (`regAllocValid_spec`) and compact frame-layout bounds
   (`fnFrameLayout_ok`, `fnFrameLayout_frameBytes_le`, `usedTempsStmt_le_maxTempsStmt`).
2. `PreservedFrameRegs`, `ProgFrameOkR`, `tempSpanR`, `FnWriteMaskR` invariants.
3. Direct-register operand (`exprReg?`) and leaf (`emitSimpleExprR`) simulation.
4. Full expression (`reg_evalExpr_sim` for `compileETo`), condition (`reg_evalCond_sim` for `compileCR`),
   and argument-list (`reg_evalArgs_sim` for `compileEvalExprsToTempsR`) simulation.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard Lean axioms only.
-/

namespace ConAgua.RISCV.Compiler

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Linker

/-! ## 1. Register-Bank Disjointness, Validator Soundness & Frame Geometry -/

/-- Registers reserved by the compiler / ABI that are NEVER allocated to locals. -/
def reservedAbiRegs : List Reg :=
  [AbiReg.zero, AbiReg.ra, AbiReg.sp, AbiReg.gp, AbiReg.s0, AbiReg.s1, AbiReg.s2,
   AbiReg.a0, AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3, AbiReg.t4, AbiReg.t5, AbiReg.t6]

/-- Valid destination register for `compileETo`: `a0` or any register in `allowedRegs true`
    (`a1..a7`, `s3..s11`, `tp`) — covers both allocated variable regs and all call/ret `resReg i`. -/
def ValidTargetReg (_fl : FrameLayout) (rd : Reg) : Prop :=
  rd = AbiReg.a0 ∨ rd ∈ allowedRegs true

theorem allowedRegs_sub_true {isLeaf : Bool} {r : Reg} (hr : r ∈ allowedRegs isLeaf) :
    r ∈ allowedRegs true := by
  cases isLeaf
  · exact List.mem_append_right _ hr
  · exact hr

theorem resReg_mem_allowed_true {i : Nat} (hi : 1 ≤ i) : resReg i ∈ allowedRegs true := by
  match i with
  | 0 => omega
  | 1 | 2 | 3 | 4 | 5 | 6 => decide
  | _ + 7 => exact show AbiReg.a7 ∈ allowedRegs true by decide

theorem resReg_validTargetReg (fl : FrameLayout) (i : Nat) : ValidTargetReg fl (resReg i) := by
  cases i with
  | zero => exact Or.inl rfl
  | succ j => exact Or.inr (resReg_mem_allowed_true (by omega))

theorem sextImm12_ofNat_lt (n : Nat) (hn : n < 2048) :
    sextImm12 (BitVec.ofNat 12 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have h12 : n < 2 ^ 12 := by omega
  have h64 : n < 2 ^ 64 := by omega
  have hmsb : (BitVec.ofNat 12 n).msb = false := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h12]
    exact decide_eq_false (by omega)
  rw [sextImm12, BitVec.signExtend_eq_setWidth_of_msb_false hmsb, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h12, Nat.mod_eq_of_lt h64]

theorem allowedRegs_disj_reserved (isLeaf : Bool) {r q : Reg}
    (hr : r ∈ allowedRegs isLeaf) (hq : q ∈ reservedAbiRegs) : r ≠ q := by
  have hall : (allowedRegs isLeaf).all (fun a => reservedAbiRegs.all (fun b => a != b)) = true := by
    cases isLeaf <;> decide
  rw [List.all_eq_true] at hall
  have h1 := hall r hr
  rw [List.all_eq_true] at h1
  exact bne_iff_ne.mp (h1 q hq)

theorem allowedRegs_ne_zero {isLeaf : Bool} {r : Reg} (hr : r ∈ allowedRegs isLeaf) : r ≠ AbiReg.zero :=
  allowedRegs_disj_reserved isLeaf hr (by simp [reservedAbiRegs])
theorem allowedRegs_ne_ra {isLeaf : Bool} {r : Reg} (hr : r ∈ allowedRegs isLeaf) : r ≠ AbiReg.ra :=
  allowedRegs_disj_reserved isLeaf hr (by simp [reservedAbiRegs])
theorem allowedRegs_ne_sp {isLeaf : Bool} {r : Reg} (hr : r ∈ allowedRegs isLeaf) : r ≠ AbiReg.sp :=
  allowedRegs_disj_reserved isLeaf hr (by simp [reservedAbiRegs])
theorem allowedRegs_ne_gp {isLeaf : Bool} {r : Reg} (hr : r ∈ allowedRegs isLeaf) : r ≠ AbiReg.gp :=
  allowedRegs_disj_reserved isLeaf hr (by simp [reservedAbiRegs])
theorem allowedRegs_ne_s0 {isLeaf : Bool} {r : Reg} (hr : r ∈ allowedRegs isLeaf) : r ≠ AbiReg.s0 :=
  allowedRegs_disj_reserved isLeaf hr (by simp [reservedAbiRegs])
theorem allowedRegs_ne_s1 {isLeaf : Bool} {r : Reg} (hr : r ∈ allowedRegs isLeaf) : r ≠ AbiReg.s1 :=
  allowedRegs_disj_reserved isLeaf hr (by simp [reservedAbiRegs])
theorem allowedRegs_ne_s2 {isLeaf : Bool} {r : Reg} (hr : r ∈ allowedRegs isLeaf) : r ≠ AbiReg.s2 :=
  allowedRegs_disj_reserved isLeaf hr (by simp [reservedAbiRegs])
theorem allowedRegs_ne_a0 {isLeaf : Bool} {r : Reg} (hr : r ∈ allowedRegs isLeaf) : r ≠ AbiReg.a0 :=
  allowedRegs_disj_reserved isLeaf hr (by simp [reservedAbiRegs])
theorem allowedRegs_ne_t0 {isLeaf : Bool} {r : Reg} (hr : r ∈ allowedRegs isLeaf) : r ≠ AbiReg.t0 :=
  allowedRegs_disj_reserved isLeaf hr (by simp [reservedAbiRegs])
theorem allowedRegs_ne_t1 {isLeaf : Bool} {r : Reg} (hr : r ∈ allowedRegs isLeaf) : r ≠ AbiReg.t1 :=
  allowedRegs_disj_reserved isLeaf hr (by simp [reservedAbiRegs])
theorem allowedRegs_ne_t2 {isLeaf : Bool} {r : Reg} (hr : r ∈ allowedRegs isLeaf) : r ≠ AbiReg.t2 :=
  allowedRegs_disj_reserved isLeaf hr (by simp [reservedAbiRegs])
theorem allowedRegs_ne_t3 {isLeaf : Bool} {r : Reg} (hr : r ∈ allowedRegs isLeaf) : r ≠ AbiReg.t3 :=
  allowedRegs_disj_reserved isLeaf hr (by simp [reservedAbiRegs])
theorem allowedRegs_ne_t4 {isLeaf : Bool} {r : Reg} (hr : r ∈ allowedRegs isLeaf) : r ≠ AbiReg.t4 :=
  allowedRegs_disj_reserved isLeaf hr (by simp [reservedAbiRegs])
theorem allowedRegs_ne_t5 {isLeaf : Bool} {r : Reg} (hr : r ∈ allowedRegs isLeaf) : r ≠ AbiReg.t5 :=
  allowedRegs_disj_reserved isLeaf hr (by simp [reservedAbiRegs])
theorem allowedRegs_ne_t6 {isLeaf : Bool} {r : Reg} (hr : r ∈ allowedRegs isLeaf) : r ≠ AbiReg.t6 :=
  allowedRegs_disj_reserved isLeaf hr (by simp [reservedAbiRegs])

theorem calleeSaved_mem_allowed (isLeaf : Bool) {r : Reg} (hr : r ∈ calleeSavedBank) :
    r ∈ allowedRegs isLeaf := by
  cases isLeaf
  · exact hr
  · exact List.mem_append_right _ hr

theorem nonLeaf_allowed_ne_resReg {r : Reg} (hr : r ∈ allowedRegs false) (i : Nat) :
    r ≠ resReg i := by
  let resRegs : List Reg :=
    [AbiReg.a0, AbiReg.a1, AbiReg.a2, AbiReg.a3, AbiReg.a4, AbiReg.a5, AbiReg.a6, AbiReg.a7]
  have hall : (allowedRegs false).all (fun a => resRegs.all (fun b => a != b)) = true := by decide
  have hres : resReg i ∈ resRegs := by
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | _ + 7 => simp [resReg, resRegs]
  rw [List.all_eq_true] at hall
  have h1 := hall r hr
  rw [List.all_eq_true] at h1
  exact bne_iff_ne.mp (h1 (resReg i) hres)

theorem ValidTargetReg.ne_zero {fl : FrameLayout} {rd : Reg} (h : ValidTargetReg fl rd) : rd ≠ AbiReg.zero :=
  h.elim (fun h => h ▸ by decide) allowedRegs_ne_zero
theorem ValidTargetReg.ne_ra {fl : FrameLayout} {rd : Reg} (h : ValidTargetReg fl rd) : rd ≠ AbiReg.ra :=
  h.elim (fun h => h ▸ by decide) allowedRegs_ne_ra
theorem ValidTargetReg.ne_sp {fl : FrameLayout} {rd : Reg} (h : ValidTargetReg fl rd) : rd ≠ AbiReg.sp :=
  h.elim (fun h => h ▸ by decide) allowedRegs_ne_sp
theorem ValidTargetReg.ne_gp {fl : FrameLayout} {rd : Reg} (h : ValidTargetReg fl rd) : rd ≠ AbiReg.gp :=
  h.elim (fun h => h ▸ by decide) allowedRegs_ne_gp
theorem ValidTargetReg.ne_s0 {fl : FrameLayout} {rd : Reg} (h : ValidTargetReg fl rd) : rd ≠ AbiReg.s0 :=
  h.elim (fun h => h ▸ by decide) allowedRegs_ne_s0
theorem ValidTargetReg.ne_s1 {fl : FrameLayout} {rd : Reg} (h : ValidTargetReg fl rd) : rd ≠ AbiReg.s1 :=
  h.elim (fun h => h ▸ by decide) allowedRegs_ne_s1
theorem ValidTargetReg.ne_s2 {fl : FrameLayout} {rd : Reg} (h : ValidTargetReg fl rd) : rd ≠ AbiReg.s2 :=
  h.elim (fun h => h ▸ by decide) allowedRegs_ne_s2
theorem ValidTargetReg.ne_t0 {fl : FrameLayout} {rd : Reg} (h : ValidTargetReg fl rd) : rd ≠ AbiReg.t0 :=
  h.elim (fun h => h ▸ by decide) allowedRegs_ne_t0
theorem ValidTargetReg.ne_t1 {fl : FrameLayout} {rd : Reg} (h : ValidTargetReg fl rd) : rd ≠ AbiReg.t1 :=
  h.elim (fun h => h ▸ by decide) allowedRegs_ne_t1
theorem ValidTargetReg.ne_t2 {fl : FrameLayout} {rd : Reg} (h : ValidTargetReg fl rd) : rd ≠ AbiReg.t2 :=
  h.elim (fun h => h ▸ by decide) allowedRegs_ne_t2
theorem ValidTargetReg.ne_t3 {fl : FrameLayout} {rd : Reg} (h : ValidTargetReg fl rd) : rd ≠ AbiReg.t3 :=
  h.elim (fun h => h ▸ by decide) allowedRegs_ne_t3
theorem ValidTargetReg.ne_t4 {fl : FrameLayout} {rd : Reg} (h : ValidTargetReg fl rd) : rd ≠ AbiReg.t4 :=
  h.elim (fun h => h ▸ by decide) allowedRegs_ne_t4
theorem ValidTargetReg.ne_t5 {fl : FrameLayout} {rd : Reg} (h : ValidTargetReg fl rd) : rd ≠ AbiReg.t5 :=
  h.elim (fun h => h ▸ by decide) allowedRegs_ne_t5
theorem ValidTargetReg.ne_t6 {fl : FrameLayout} {rd : Reg} (h : ValidTargetReg fl rd) : rd ≠ AbiReg.t6 :=
  h.elim (fun h => h ▸ by decide) allowedRegs_ne_t6

private theorem regAllocValid_go_spec (nl : Nat) :
    ∀ (alloc : RegAlloc) (seenV : List Var),
      regAllocValid.go nl (allowedRegs true) seenV alloc = true →
      (∀ p ∈ alloc, p.1 < nl ∧ p.2 ∈ allowedRegs true ∧ p.1 ∉ seenV) ∧
      (alloc.map Prod.fst).Nodup := by
  intro alloc
  induction alloc with
  | nil => intro _ _; exact ⟨(fun _ h => nomatch h), List.nodup_nil⟩
  | cons hd tl ih =>
    intro seenV h
    rcases hd with ⟨x, r⟩
    simp only [regAllocValid.go, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not] at h
    obtain ⟨⟨⟨hxlt, hrbank⟩, hxseen⟩, htl⟩ := h
    obtain ⟨hm, hndV⟩ := ih (x :: seenV) htl
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact ⟨hxlt, hrbank, hxseen⟩
      · have h1 := hm p hp'
        exact ⟨h1.1, h1.2.1, fun h => h1.2.2 (List.mem_cons_of_mem _ h)⟩
    · refine List.nodup_cons.mpr ⟨?_, hndV⟩
      intro hmem
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmem
      exact (hm p hp).2.2 List.mem_cons_self

theorem regAllocValid_spec {isLeaf : Bool} {nl : Nat} {alloc : RegAlloc}
    (hv : regAllocValid isLeaf nl alloc = true) :
    (∀ p ∈ alloc, p.1 < nl ∧ p.2 ∈ allowedRegs true) ∧
    (alloc.map Prod.fst).Nodup := by
  obtain ⟨hm, h1⟩ := regAllocValid_go_spec nl alloc [] hv
  exact ⟨fun p hp => ⟨(hm p hp).1, (hm p hp).2.1⟩, h1⟩

theorem list_lookup_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {k : α} {v : β}, l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => by cases h
  | (a, b) :: tl, k, v, h => by
    simp only [List.lookup] at h
    by_cases hka : k == a
    · simp only [hka, Option.some.injEq] at h
      have hka' : k = a := beq_iff_eq.mp hka
      subst hka'; subst h; exact List.mem_cons_self
    · simp only [Bool.eq_false_iff.mpr hka] at h
      exact List.mem_cons_of_mem _ (list_lookup_mem h)

theorem list_lookup_some_of_mem_nodup {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {k : α} {v : β}, (l.map Prod.fst).Nodup → (k, v) ∈ l → l.lookup k = some v
  | [], _, _, _, hm => nomatch hm
  | (a, b) :: tl, k, v, hnd, hm => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hm with heq | hm'
    · cases heq; simp [List.lookup]
    · have hne : k ≠ a := by
        intro h; subst h; exact hnd.1 (List.mem_map.mpr ⟨(k, v), hm', rfl⟩)
      simp only [List.lookup, beq_false_of_ne hne]
      exact list_lookup_some_of_mem_nodup hnd.2 hm'

theorem list_lookup_none_of_not_mem_fst {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {k : α}, k ∉ l.map Prod.fst → l.lookup k = none
  | [], _, _ => rfl
  | (a, b) :: tl, k, hnm => by
    have hne : k ≠ a := fun h => hnm (h ▸ List.mem_cons_self)
    simp only [List.lookup, beq_false_of_ne hne]
    exact list_lookup_none_of_not_mem_fst fun hm => hnm (List.mem_cons_of_mem _ hm)

theorem regAllocValid_lookup {isLeaf : Bool} {nl : Nat} {alloc : RegAlloc}
    (hv : regAllocValid isLeaf nl alloc = true) {x : Var} {r : Reg}
    (hl : alloc.lookup x = some r) :
    x < nl ∧ r ∈ allowedRegs true ∧ r ∈ alloc.map Prod.snd := by
  have hm := list_lookup_mem hl
  obtain ⟨h1, _⟩ := regAllocValid_spec hv
  exact ⟨(h1 _ hm).1, (h1 _ hm).2, List.mem_map.mpr ⟨(x, r), hm, rfl⟩⟩

theorem calleeSavedBank_nodup : calleeSavedBank.Nodup := by decide

/-- Well-formedness invariant on a function's `FrameLayout`. -/
structure FrameLayoutOk (fl : FrameLayout) : Prop where
  valid : regAllocValid fl.isLeaf fl.nlocals fl.alloc = true
  savedDef : fl.savedRegs = calleeSavedBank.filter (fun r => fl.alloc.any fun p => p.2 == r)
  spilledSub : ∀ x ∈ fl.spilledVars, x < fl.nlocals ∧ fl.alloc.lookup x = none
  spilledNodup : fl.spilledVars.Nodup

theorem fnFrameLayoutWith_ok (rawAlloc : RegAlloc) (fd : FunDecl) :
    FrameLayoutOk (fnFrameLayoutWith rawAlloc fd) := by
  unfold fnFrameLayoutWith
  dsimp only
  split
  · next hv =>
    refine ⟨(Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp hv).1).1, rfl, ?_,
      List.Pairwise.filter _ List.nodup_range⟩
    intro x hx
    rw [List.mem_filter, List.mem_range, Bool.and_eq_true, Option.isNone_iff_eq_none] at hx
    exact ⟨hx.1, hx.2.1⟩
  · refine ⟨rfl, rfl, ?_, List.Pairwise.filter _ List.nodup_range⟩
    intro x hx
    rw [List.mem_filter, List.mem_range, Bool.and_eq_true, Option.isNone_iff_eq_none] at hx
    exact ⟨hx.1, hx.2.1⟩

theorem fnFrameLayout_ok (fd : FunDecl) : FrameLayoutOk (fnFrameLayout fd) :=
  fnFrameLayoutWith_ok (chooseRegAlloc fd) fd

theorem fnFrameLayoutWith_spilled_of_used (rawAlloc : RegAlloc) (fd : FunDecl) {x : Var}
    (hx : x < (fnFrameLayoutWith rawAlloc fd).nlocals)
    (hnone : (fnFrameLayoutWith rawAlloc fd).alloc.lookup x = none)
    (huse : stmtUsesVar x fd.body = true) :
    x ∈ (fnFrameLayoutWith rawAlloc fd).spilledVars := by
  unfold fnFrameLayoutWith at hx hnone ⊢
  dsimp only at hx hnone ⊢
  rw [List.mem_filter, List.mem_range, Bool.and_eq_true, Option.isNone_iff_eq_none]
  exact ⟨hx, hnone, huse⟩

theorem fnFrameLayout_spilled_of_used (fd : FunDecl) {x : Var}
    (hx : x < (fnFrameLayout fd).nlocals)
    (hnone : (fnFrameLayout fd).alloc.lookup x = none)
    (huse : stmtUsesVar x fd.body = true) :
    x ∈ (fnFrameLayout fd).spilledVars :=
  fnFrameLayoutWith_spilled_of_used (chooseRegAlloc fd) fd hx hnone huse

theorem fnFrameLayoutWith_args_valid (rawAlloc : RegAlloc) (fd : FunDecl) :
    regAllocArgsValid (fnFrameLayoutWith rawAlloc fd).isLeaf fd.nparams (fnFrameLayoutWith rawAlloc fd).alloc = true := by
  unfold fnFrameLayoutWith
  dsimp only
  split
  · next hv => exact (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp hv).1).2
  · simp [regAllocArgsValid, List.lookup]

theorem fnFrameLayout_args_valid (fd : FunDecl) :
    regAllocArgsValid (fnFrameLayout fd).isLeaf fd.nparams (fnFrameLayout fd).alloc = true :=
  fnFrameLayoutWith_args_valid (chooseRegAlloc fd) fd

theorem fnFrameLayoutWith_graph_valid (rawAlloc : RegAlloc) (fd : FunDecl) :
    regAllocGraphValid (fnFrameLayoutWith rawAlloc fd).isLeaf (fnFrameLayoutWith rawAlloc fd).nlocals
      (fnFrameLayoutWith rawAlloc fd).alloc fd = true := by
  unfold fnFrameLayoutWith
  dsimp only
  split
  · next hv => exact (Bool.and_eq_true _ _ |>.mp hv).2
  · cases hlf : !stmtHasCall fd.body <;> simp [regAllocGraphValid]
    clear hlf; induction fd.body with
    | call xs _ _ =>
      simp only [stmtCallResValid, callResListValid, List.all_eq_true]
      intro p _; rcases p with ⟨x, i⟩; simp [List.lookup]
    | seq _ _ ih1 ih2 => simp [stmtCallResValid, ih1, ih2]
    | ite _ _ _ ih1 ih2 => simp [stmtCallResValid, ih1, ih2]
    | «while» _ _ ih => simp [stmtCallResValid, ih]
    | _ => rfl

theorem fnFrameLayout_graph_valid (fd : FunDecl) :
    regAllocGraphValid (fnFrameLayout fd).isLeaf (fnFrameLayout fd).nlocals (fnFrameLayout fd).alloc fd = true :=
  fnFrameLayoutWith_graph_valid (chooseRegAlloc fd) fd

private theorem FrameLayoutOk.with_useT5Gp {fl : FrameLayout} (h : FrameLayoutOk fl) (b : Bool) :
    FrameLayoutOk { fl with useT5Gp := b } :=
  ⟨h.valid, h.savedDef, h.spilledSub, h.spilledNodup⟩

theorem fnFrameLayoutForWith_ok (rawAlloc : RegAlloc) (tab : Tab) (fd : FunDecl) :
    FrameLayoutOk (fnFrameLayoutForWith rawAlloc tab fd) := by
  rw [fnFrameLayoutForWith]
  exact (fnFrameLayoutWith_ok rawAlloc fd).with_useT5Gp _

theorem fnFrameLayoutFor_ok (tab : Tab) (fd : FunDecl) : FrameLayoutOk (fnFrameLayoutFor tab fd) :=
  fnFrameLayoutForWith_ok (chooseRegAlloc fd) tab fd

theorem fnFrameLayoutForWith_spilled_of_used (rawAlloc : RegAlloc) (tab : Tab) (fd : FunDecl) {x : Var}
    (hx : x < (fnFrameLayoutForWith rawAlloc tab fd).nlocals)
    (hnone : (fnFrameLayoutForWith rawAlloc tab fd).alloc.lookup x = none)
    (huse : stmtUsesVar x fd.body = true) :
    x ∈ (fnFrameLayoutForWith rawAlloc tab fd).spilledVars :=
  fnFrameLayoutWith_spilled_of_used rawAlloc fd hx hnone huse

theorem fnFrameLayoutFor_spilled_of_used (tab : Tab) (fd : FunDecl) {x : Var}
    (hx : x < (fnFrameLayoutFor tab fd).nlocals)
    (hnone : (fnFrameLayoutFor tab fd).alloc.lookup x = none)
    (huse : stmtUsesVar x fd.body = true) :
    x ∈ (fnFrameLayoutFor tab fd).spilledVars :=
  fnFrameLayoutForWith_spilled_of_used (chooseRegAlloc fd) tab fd hx hnone huse

theorem fnFrameLayoutForWith_args_valid (rawAlloc : RegAlloc) (tab : Tab) (fd : FunDecl) :
    regAllocArgsValid (fnFrameLayoutForWith rawAlloc tab fd).isLeaf fd.nparams
      (fnFrameLayoutForWith rawAlloc tab fd).alloc = true :=
  fnFrameLayoutWith_args_valid rawAlloc fd

theorem fnFrameLayoutFor_args_valid (tab : Tab) (fd : FunDecl) :
    regAllocArgsValid (fnFrameLayoutFor tab fd).isLeaf fd.nparams (fnFrameLayoutFor tab fd).alloc = true :=
  fnFrameLayoutForWith_args_valid (chooseRegAlloc fd) tab fd

theorem fnFrameLayoutForWith_graph_valid (rawAlloc : RegAlloc) (tab : Tab) (fd : FunDecl) :
    regAllocGraphValid (fnFrameLayoutForWith rawAlloc tab fd).isLeaf (fnFrameLayoutForWith rawAlloc tab fd).nlocals
      (fnFrameLayoutForWith rawAlloc tab fd).alloc fd = true :=
  fnFrameLayoutWith_graph_valid rawAlloc fd

theorem fnFrameLayoutFor_graph_valid (tab : Tab) (fd : FunDecl) :
    regAllocGraphValid (fnFrameLayoutFor tab fd).isLeaf (fnFrameLayoutFor tab fd).nlocals
      (fnFrameLayoutFor tab fd).alloc fd = true :=
  fnFrameLayoutForWith_graph_valid (chooseRegAlloc fd) tab fd

theorem fnFrameLayoutForWith_no_copyScan (rawAlloc : RegAlloc) (tab : Tab) (fd : FunDecl)
    (h : (fnFrameLayoutForWith rawAlloc tab fd).useT5Gp = true) : stmtHasCopyScan fd.body = false := by
  simp only [fnFrameLayoutForWith, shouldUseT5Gp] at h
  cases hcs : stmtHasCopyScan fd.body with
  | false => rfl
  | true => simp [hcs] at h

theorem fnFrameLayoutFor_no_copyScan (tab : Tab) (fd : FunDecl)
    (h : (fnFrameLayoutFor tab fd).useT5Gp = true) : stmtHasCopyScan fd.body = false :=
  fnFrameLayoutForWith_no_copyScan (chooseRegAlloc fd) tab fd h

theorem regAllocArgsValid_ne {isLeaf : Bool} {nparams : Nat} {alloc : RegAlloc}
    (hva : regAllocArgsValid isLeaf nparams alloc = true)
    {i : Nat} {ri : Reg} (hiLt : i < min nparams maxRes) (hli : alloc.lookup i = some ri)
    {j : Nat} (hij : i < j) (hjLt : j < min nparams maxRes) :
    ri ≠ resReg j := by
  simp only [regAllocArgsValid, List.all_eq_true, List.mem_range] at hva
  have h1 := hva i hiLt
  rw [hli] at h1
  simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not, beq_eq_false_iff_ne] at h1
  rcases h1 j hjLt with hnot | hne
  · exact absurd hij hnot
  · exact hne

theorem FrameLayoutOk.spilled_nodup {fl : FrameLayout} (h : FrameLayoutOk fl) :
    fl.spilledVars.Nodup := h.spilledNodup

theorem FrameLayoutOk.saved_nodup {fl : FrameLayout} (h : FrameLayoutOk fl) :
    fl.savedRegs.Nodup := by
  rw [h.savedDef]
  exact List.Pairwise.filter _ calleeSavedBank_nodup

theorem FrameLayoutOk.saved_mem_callee {fl : FrameLayout} (h : FrameLayoutOk fl) {r : Reg}
    (hr : r ∈ fl.savedRegs) : r ∈ calleeSavedBank := by
  rw [h.savedDef, List.mem_filter] at hr
  exact hr.1

theorem FrameLayoutOk.saved_mem_iff {fl : FrameLayout} (h : FrameLayoutOk fl) {r : Reg} :
    r ∈ fl.savedRegs ↔ r ∈ calleeSavedBank ∧ r ∈ fl.alloc.map Prod.snd := by
  rw [h.savedDef, List.mem_filter, List.any_eq_true]
  constructor
  · rintro ⟨hcal, ⟨p, hp, heq⟩⟩
    exact ⟨hcal, List.mem_map.mpr ⟨p, hp, (beq_iff_eq.mp heq)⟩⟩
  · rintro ⟨hcal, hmap⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmap
    exact ⟨hcal, p, hp, beq_self_eq_true _⟩

theorem FrameLayoutOk.spillIdx_lt {fl : FrameLayout} (_h : FrameLayoutOk fl) {x : Var}
    (hmem : x ∈ fl.spilledVars) :
    fl.spillIdx x < fl.spilledVars.length :=
  List.idxOf_lt_length_of_mem hmem

theorem FrameLayoutOk.spillIdx_inj {fl : FrameLayout} (_h : FrameLayoutOk fl) {x y : Var}
    (hmx : x ∈ fl.spilledVars) (hmy : y ∈ fl.spilledVars)
    (heq : fl.spillIdx x = fl.spillIdx y) : x = y := by
  have h1 : fl.spilledVars[fl.spilledVars.idxOf x]'(List.idxOf_lt_length_of_mem hmx) = x :=
    List.getElem_idxOf (List.idxOf_lt_length_of_mem hmx)
  have h2 : fl.spilledVars[fl.spilledVars.idxOf y]'(List.idxOf_lt_length_of_mem hmy) = y :=
    List.getElem_idxOf (List.idxOf_lt_length_of_mem hmy)
  dsimp only [FrameLayout.spillIdx] at heq
  rw [← h1, ← h2]
  simp [heq]

private theorem length_filter_add_not {α : Type} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => rfl
  | cons a tl ih =>
    cases hp : p a <;> simp [List.filter, hp] <;> omega

private theorem length_le_of_nodup_sublist {α : Type} [DecidableEq α] :
    ∀ {l1 l2 : List α}, l1.Nodup → (∀ x ∈ l1, x ∈ l2) → l1.length ≤ l2.length
  | [], _, _, _ => Nat.zero_le _
  | a :: tl, l2, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have ha : a ∈ l2 := hsub a List.mem_cons_self
    have htl : ∀ x ∈ tl, x ∈ l2.erase a := fun x hx =>
      (List.mem_erase_of_ne (by intro h; subst h; exact hnd.1 hx)).mpr
        (hsub x (List.mem_cons_of_mem _ hx))
    have hrec := length_le_of_nodup_sublist hnd.2 htl
    have her : (l2.erase a).length + 1 = l2.length := by
      rw [List.length_erase_of_mem ha]
      have hpos : 0 < l2.length := List.length_pos_of_mem ha
      omega
    simp only [List.length_cons]; omega

theorem FrameLayoutOk.alloc_add_spilled_le {fl : FrameLayout} (h : FrameLayoutOk fl) :
    fl.alloc.length + fl.spilledVars.length ≤ fl.nlocals := by
  obtain ⟨hmem, hndV⟩ := regAllocValid_spec h.valid
  have hsub1 : ∀ x ∈ fl.alloc.map Prod.fst,
      x ∈ (List.range fl.nlocals).filter (fun y => !(fl.alloc.lookup y).isNone) := by
    intro x hx
    obtain ⟨⟨x', r⟩, hp, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_filter, List.mem_range]
    refine ⟨(hmem _ hp).1, ?_⟩
    rw [list_lookup_some_of_mem_nodup hndV hp]; rfl
  have hle1 : fl.alloc.length ≤ ((List.range fl.nlocals).filter (fun y => !(fl.alloc.lookup y).isNone)).length := by
    simpa [List.length_map] using length_le_of_nodup_sublist hndV hsub1
  have hsub2 : ∀ x ∈ fl.spilledVars,
      x ∈ (List.range fl.nlocals).filter (fun y => (fl.alloc.lookup y).isNone) := by
    intro x hx
    obtain ⟨hxlt, hnone⟩ := h.spilledSub x hx
    rw [List.mem_filter, List.mem_range, Option.isNone_iff_eq_none]
    exact ⟨hxlt, hnone⟩
  have hle2 : fl.spilledVars.length ≤ ((List.range fl.nlocals).filter (fun y => (fl.alloc.lookup y).isNone)).length :=
    length_le_of_nodup_sublist h.spilledNodup hsub2
  have hsum := length_filter_add_not (fun y => (fl.alloc.lookup y).isNone) (List.range fl.nlocals)
  rw [List.length_range] at hsum
  omega

theorem FrameLayoutOk.slots_le {fl : FrameLayout} (h : FrameLayoutOk fl) :
    fl.protectedSlots + fl.spilledVars.length ≤ 1 + fl.nlocals := by
  have hsaved : fl.savedRegs.length ≤ fl.alloc.length := by
    have hsub : ∀ r ∈ fl.savedRegs, r ∈ fl.alloc.map Prod.snd := fun r hr => (h.saved_mem_iff.mp hr).2
    simpa [List.length_map] using length_le_of_nodup_sublist h.saved_nodup hsub
  have h1 := h.alloc_add_spilled_le
  have hra : fl.raSlots ≤ 1 := by unfold FrameLayout.raSlots; split <;> omega
  unfold FrameLayout.protectedSlots
  omega

theorem usedTempsExpr_le_maxTempsExpr : ∀ e : Expr, usedTempsExpr e ≤ maxTempsExpr e
  | .const _ | .var _ | .len8 _ | .len64 _ | .glob _ => Nat.le_refl 0
  | .ld8 _ i | .ld64 _ i | .ldc _ i | .len64t _ i | .ld8x8 _ i => usedTempsExpr_le_maxTempsExpr i
  | .bin _ a b | .cmpw _ a b => by
    have ha := usedTempsExpr_le_maxTempsExpr a
    have hb := usedTempsExpr_le_maxTempsExpr b
    dsimp only [usedTempsExpr, maxTempsExpr]
    split
    · omega
    · split
      · omega
      · split <;> omega
  | .ld64t _ t i | .ld32t _ t i | .ld32h _ t i _ => by
    have ht := usedTempsExpr_le_maxTempsExpr t
    have hi := usedTempsExpr_le_maxTempsExpr i
    dsimp only [usedTempsExpr, maxTempsExpr]
    split <;> omega

theorem usedTempsExpr_of_isSimple {e : Expr} (h : isSimpleExpr e = true) : usedTempsExpr e = 0 := by
  cases e <;> simp [isSimpleExpr, usedTempsExpr] at h ⊢

theorem usedTempsExpr_of_exprNoT4 {e : Expr} (h : exprNoT4 e = true) : usedTempsExpr e = 0 := by
  induction e with
  | const _ | var _ | len8 _ | len64 _ | glob _ => rfl
  | ld8 _ _ ih | ld64 _ _ ih | ldc _ _ ih | len64t _ _ ih | ld8x8 _ _ ih => exact ih h
  | bin _ a b iha ihb | cmpw _ a b iha ihb =>
    simp only [exprNoT4, Bool.or_eq_true, Bool.and_eq_true] at h
    dsimp only [usedTempsExpr]
    cases hb' : isSimpleExpr b
    · cases ha' : isSimpleExpr a
      · simp [hb', ha'] at h
      · simp only [↓reduceIte]
        rcases h with ⟨hb, _⟩ | ⟨_, hb⟩
        · rw [hb'] at hb; cases hb
        · exact ihb hb
    · simp only [↓reduceIte]
      rcases h with ⟨_, ha⟩ | ⟨ha, _⟩
      · exact iha ha
      · exact usedTempsExpr_of_isSimple ha
  | ld64t _ t i _ ihi | ld32t _ t i _ ihi | ld32h _ t i _ _ ihi =>
    simp only [exprNoT4, Bool.and_eq_true] at h
    simp only [usedTempsExpr, h.1, ↓reduceIte]
    exact ihi h.2

theorem usedTempsCond_le_maxTempsCond : ∀ c : Cond, usedTempsCond c ≤ maxTempsCond c
  | .cmp _ a b => by
    have ha := usedTempsExpr_le_maxTempsExpr a
    have hb := usedTempsExpr_le_maxTempsExpr b
    dsimp only [usedTempsCond, maxTempsCond]
    split
    · omega
    · split
      · omega
      · split <;> omega
  | .and p q | .or p q => by
    have hp := usedTempsCond_le_maxTempsCond p
    have hq := usedTempsCond_le_maxTempsCond q
    dsimp only [usedTempsCond, maxTempsCond]; omega
  | .not p => usedTempsCond_le_maxTempsCond p

private theorem foldl_max_le {α : Type} (f g : α → Nat) (hfg : ∀ x, f x ≤ g x)
    (l : List α) : ∀ a b, a ≤ b → l.foldl (fun acc x => max acc (f x)) a ≤ l.foldl (fun acc x => max acc (g x)) b := by
  induction l with
  | nil => intro a b h; exact h
  | cons x tl ih =>
    intro a b h
    exact ih _ _ (Nat.max_le.mpr ⟨Nat.le_trans h (Nat.le_max_left _ _), Nat.le_trans (hfg x) (Nat.le_max_right _ _)⟩)

theorem usedTempsExprs_le_maxTempsExprs (es : List Expr) : usedTempsExprs es ≤ maxTempsExprs es :=
  foldl_max_le (fun p : Expr × Nat => p.2 + max 1 (usedTempsExpr p.1))
    (fun p : Expr × Nat => p.2 + max 1 (maxTempsExpr p.1))
    (fun p => by have := usedTempsExpr_le_maxTempsExpr p.1; omega) es.zipIdx 0 0 (Nat.le_refl 0)

theorem usedTempsStmt_le_maxTempsStmt : ∀ s : Stmt, usedTempsStmt s ≤ maxTempsStmt s
  | .skip | .brk => Nat.le_refl 0
  | .set _ e | .abort e | .gset _ e => usedTempsExpr_le_maxTempsExpr e
  | .st8 _ i e | .st64 _ i e => by
    have hi := usedTempsExpr_le_maxTempsExpr i
    have he := usedTempsExpr_le_maxTempsExpr e
    dsimp only [usedTempsStmt, maxTempsStmt]
    split
    · omega
    · split <;> omega
  | .st64t _ t i e | .st32t _ t i e => by
    have ht := usedTempsExpr_le_maxTempsExpr t
    have hi := usedTempsExpr_le_maxTempsExpr i
    have he := usedTempsExpr_le_maxTempsExpr e
    dsimp only [usedTempsStmt, maxTempsStmt]
    split
    · split
      · omega
      · split <;> omega
    · omega
  | .seq s1 s2 => by
    have h1 := usedTempsStmt_le_maxTempsStmt s1
    have h2 := usedTempsStmt_le_maxTempsStmt s2
    dsimp only [usedTempsStmt, maxTempsStmt]; omega
  | .ite c s1 s2 => by
    have hc := usedTempsCond_le_maxTempsCond c
    have h1 := usedTempsStmt_le_maxTempsStmt s1
    have h2 := usedTempsStmt_le_maxTempsStmt s2
    dsimp only [usedTempsStmt, maxTempsStmt]; omega
  | .while c b => by
    have hc := usedTempsCond_le_maxTempsCond c
    have hb := usedTempsStmt_le_maxTempsStmt b
    dsimp only [usedTempsStmt, maxTempsStmt]; omega
  | .ret [e] => by
    have he := usedTempsExpr_le_maxTempsExpr e
    simp only [usedTempsStmt, maxTempsStmt, maxTempsExprs, List.zipIdx, List.foldl]
    omega
  | .ret [] => Nat.le_refl 0
  | .ret (e1 :: e2 :: es) => usedTempsExprs_le_maxTempsExprs (e1 :: e2 :: es)
  | .call _ _ args => usedTempsExprs_le_maxTempsExprs args
  | .copy64 d di s si n => by
    have hdi := usedTempsExpr_le_maxTempsExpr di
    have hsi := usedTempsExpr_le_maxTempsExpr si
    have hn := usedTempsExpr_le_maxTempsExpr n
    cases d with
    | plain _ =>
      cases s with
      | plain _ => dsimp only [usedTempsStmt, maxTempsStmt]; omega
      | tier _ st => have := usedTempsExpr_le_maxTempsExpr st; dsimp only [usedTempsStmt, maxTempsStmt]; omega
    | tier _ dt =>
      have := usedTempsExpr_le_maxTempsExpr dt
      cases s with
      | plain _ => dsimp only [usedTempsStmt, maxTempsStmt]; omega
      | tier _ st => have := usedTempsExpr_le_maxTempsExpr st; dsimp only [usedTempsStmt, maxTempsStmt]; omega
  | .copy8w d di _ si n => by
    have hdi := usedTempsExpr_le_maxTempsExpr di
    have hsi := usedTempsExpr_le_maxTempsExpr si
    have hn := usedTempsExpr_le_maxTempsExpr n
    cases d with
    | plain _ => dsimp only [usedTempsStmt, maxTempsStmt]; omega
    | tier _ dt => have := usedTempsExpr_le_maxTempsExpr dt; dsimp only [usedTempsStmt, maxTempsStmt]; omega
  | .scan8 _ _ i e _ => by
    have hi := usedTempsExpr_le_maxTempsExpr i
    have he := usedTempsExpr_le_maxTempsExpr e
    dsimp only [usedTempsStmt, maxTempsStmt]
    split <;> omega

private theorem maxTempsExprs_foldl_ge_r (l : List (Expr × Nat)) (init : Nat) :
    init ≤ l.foldl (fun acc (e, idx) => max acc (idx + max 1 (maxTempsExpr e))) init := by
  induction l generalizing init with
  | nil => exact Nat.le_refl _
  | cons hd tl ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem maxUsedTempsExprs_le_foldl : ∀ (es : List Expr) (start init : Nat),
    maxUsedTempsExprs es ≤
      (es.zipIdx start).foldl (fun acc (e, idx) => max acc (idx + max 1 (maxTempsExpr e))) init
  | [], _, _ => Nat.zero_le _
  | e :: rest, start, init => by
    simp only [maxUsedTempsExprs, List.zipIdx_cons, List.foldl_cons]
    apply Nat.max_le.mpr
    constructor
    · have he := usedTempsExpr_le_maxTempsExpr e
      exact Nat.le_trans (by omega : usedTempsExpr e ≤ max init (start + max 1 (maxTempsExpr e)))
        (maxTempsExprs_foldl_ge_r _ _)
    · exact maxUsedTempsExprs_le_foldl rest (start + 1) _

theorem maxUsedTempsExprs_le_maxTempsExprs (es : List Expr) :
    maxUsedTempsExprs es ≤ maxTempsExprs es :=
  maxUsedTempsExprs_le_foldl es 0 0

theorem usedTempsCallArgs_le_maxTempsExprs (alloc : RegAlloc) (args : List Expr) :
    usedTempsCallArgs alloc args ≤ maxTempsExprs args := by
  unfold usedTempsCallArgs
  split
  · exact maxUsedTempsExprs_le_maxTempsExprs args
  · exact usedTempsExprs_le_maxTempsExprs args

theorem usedTempsRetR_le_maxTempsExprs (isLeaf : Bool) (alloc : RegAlloc) (es : List Expr) :
    usedTempsRetR isLeaf alloc es ≤ maxTempsExprs es := by
  cases es with
  | nil => exact Nat.le_refl 0
  | cons e1 rest =>
    cases rest with
    | nil =>
      have he := usedTempsExpr_le_maxTempsExpr e1
      simp only [usedTempsRetR, maxTempsExprs, List.zipIdx, List.foldl]
      omega
    | cons e2 rest2 =>
      dsimp only [usedTempsRetR]
      split
      · exact maxUsedTempsExprs_le_maxTempsExprs _
      · exact usedTempsExprs_le_maxTempsExprs _

theorem usedTempsStmtR_le_maxTempsStmt (isLeaf : Bool) (alloc : RegAlloc) :
    ∀ s : Stmt, usedTempsStmtR isLeaf alloc s ≤ maxTempsStmt s
  | .seq s1 s2 => by
    have h1 := usedTempsStmtR_le_maxTempsStmt isLeaf alloc s1
    have h2 := usedTempsStmtR_le_maxTempsStmt isLeaf alloc s2
    dsimp only [usedTempsStmtR, maxTempsStmt]; omega
  | .ite c s1 s2 => by
    have hc := usedTempsCond_le_maxTempsCond c
    have h1 := usedTempsStmtR_le_maxTempsStmt isLeaf alloc s1
    have h2 := usedTempsStmtR_le_maxTempsStmt isLeaf alloc s2
    dsimp only [usedTempsStmtR, maxTempsStmt]; omega
  | .while c b => by
    have hc := usedTempsCond_le_maxTempsCond c
    have hb := usedTempsStmtR_le_maxTempsStmt isLeaf alloc b
    dsimp only [usedTempsStmtR, maxTempsStmt]; omega
  | .ret es => usedTempsRetR_le_maxTempsExprs isLeaf alloc es
  | .call _ _ args => usedTempsCallArgs_le_maxTempsExprs alloc args
  | .skip => usedTempsStmt_le_maxTempsStmt .skip
  | .brk => usedTempsStmt_le_maxTempsStmt .brk
  | .set x e => usedTempsStmt_le_maxTempsStmt (.set x e)
  | .gset g e => usedTempsStmt_le_maxTempsStmt (.gset g e)
  | .abort e => usedTempsStmt_le_maxTempsStmt (.abort e)
  | .st8 a i e => usedTempsStmt_le_maxTempsStmt (.st8 a i e)
  | .st64 a i e => usedTempsStmt_le_maxTempsStmt (.st64 a i e)
  | .st64t a t i e => usedTempsStmt_le_maxTempsStmt (.st64t a t i e)
  | .st32t a t i e => usedTempsStmt_le_maxTempsStmt (.st32t a t i e)
  | .copy64 d di s si n => usedTempsStmt_le_maxTempsStmt (.copy64 d di s si n)
  | .copy8w d di s si n => usedTempsStmt_le_maxTempsStmt (.copy8w d di s si n)
  | .scan8 x s i e c => usedTempsStmt_le_maxTempsStmt (.scan8 x s i e c)

theorem fnFrameLayoutWith_frameSlots_le (rawAlloc : RegAlloc) (fd : FunDecl) :
    (fnFrameLayoutWith rawAlloc fd).frameSlots ≤ 1 + numLocalsFn fd + maxTempsStmt fd.body := by
  have hok := fnFrameLayoutWith_ok rawAlloc fd
  have h1 := hok.slots_le
  have h2 : (fnFrameLayoutWith rawAlloc fd).usedTemps ≤ maxTempsStmt fd.body :=
    usedTempsStmtR_le_maxTempsStmt (fnFrameLayoutWith rawAlloc fd).isLeaf (fnFrameLayoutWith rawAlloc fd).alloc fd.body
  have hnl : (fnFrameLayoutWith rawAlloc fd).nlocals = numLocalsFn fd := rfl
  unfold FrameLayout.frameSlots
  omega

theorem fnFrameLayout_frameSlots_le (fd : FunDecl) :
    (fnFrameLayout fd).frameSlots ≤ 1 + numLocalsFn fd + maxTempsStmt fd.body :=
  fnFrameLayoutWith_frameSlots_le (chooseRegAlloc fd) fd

theorem fnFrameLayoutWith_frameBytes_le (rawAlloc : RegAlloc) (fd : FunDecl) :
    8 * (fnFrameLayoutWith rawAlloc fd).frameSlots ≤ fnFrameBytes fd := by
  have h := fnFrameLayoutWith_frameSlots_le rawAlloc fd
  unfold fnFrameBytes
  omega

theorem fnFrameLayout_frameBytes_le (fd : FunDecl) :
    8 * (fnFrameLayout fd).frameSlots ≤ fnFrameBytes fd :=
  fnFrameLayoutWith_frameBytes_le (chooseRegAlloc fd) fd

private theorem frameSlots_with_useT5Gp (fl : FrameLayout) (b : Bool) :
    ({ fl with useT5Gp := b } : FrameLayout).frameSlots = fl.frameSlots := rfl

theorem fnFrameLayoutForWith_frameBytes_le (rawAlloc : RegAlloc) (tab : Tab) (fd : FunDecl) :
    8 * (fnFrameLayoutForWith rawAlloc tab fd).frameSlots ≤ fnFrameBytes fd := by
  rw [fnFrameLayoutForWith, frameSlots_with_useT5Gp]
  exact fnFrameLayoutWith_frameBytes_le rawAlloc fd

theorem fnFrameLayoutFor_frameBytes_le (tab : Tab) (fd : FunDecl) :
    8 * (fnFrameLayoutFor tab fd).frameSlots ≤ fnFrameBytes fd :=
  fnFrameLayoutForWith_frameBytes_le (chooseRegAlloc fd) tab fd

/-! ## 2. Frame-Register Preservation, Memory Spans & Frame Relation -/

/-- Preservation of ABI registers (`gp, s0, sp, s2`), leaf `ra`, hoisted `t5`, and all `allowedRegs`
    not in the exclusion predicate `excl`. -/
structure PreservedFrameRegs (fl : FrameLayout) (excl : Reg → Prop) (st st' : State) : Prop where
  abi : PreservedRegs st st'
  leafRa : fl.isLeaf = true → st'.getReg AbiReg.ra = st.getReg AbiReg.ra
  t5Gp : fl.useT5Gp = true → st'.getReg AbiReg.t5 = st.getReg AbiReg.t5
  regs : ∀ r, r ∈ allowedRegs true → ¬excl r → st'.getReg r = st.getReg r

theorem PreservedFrameRegs.refl (fl : FrameLayout) (excl : Reg → Prop) (st : State) :
    PreservedFrameRegs fl excl st st :=
  ⟨PreservedRegs.refl st, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

theorem PreservedFrameRegs.trans {fl : FrameLayout} {excl : Reg → Prop} {s1 s2 s3 : State}
    (h12 : PreservedFrameRegs fl excl s1 s2) (h23 : PreservedFrameRegs fl excl s2 s3) :
    PreservedFrameRegs fl excl s1 s3 :=
  ⟨h12.abi.trans h23.abi, fun hl => (h23.leafRa hl).trans (h12.leafRa hl),
   fun ht => (h23.t5Gp ht).trans (h12.t5Gp ht),
   fun r hr he => (h23.regs r hr he).trans (h12.regs r hr he)⟩

theorem PreservedFrameRegs.mono {fl : FrameLayout} {e1 e2 : Reg → Prop} {s1 s2 : State}
    (himp : ∀ r, e1 r → e2 r) (h : PreservedFrameRegs fl e1 s1 s2) :
    PreservedFrameRegs fl e2 s1 s2 :=
  ⟨h.abi, h.leafRa, h.t5Gp, fun r hr he => h.regs r hr (fun h1 => he (himp r h1))⟩

/-- Expression/statement scratch registers (`a0, t0..t4, t6`): disjoint from `{gp, sp, s0, s1, s2, ra, t5}` and `allowedRegs`. -/
def scratchRegs : List Reg :=
  [AbiReg.a0, AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3, AbiReg.t4, AbiReg.t6]

theorem scratchRegs_sub_reserved {r : Reg} (h : r ∈ scratchRegs) : r ∈ reservedAbiRegs := by
  simp only [scratchRegs, reservedAbiRegs, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem scratchRegs_ne_abi {r : Reg} (h : r ∈ scratchRegs) :
    r ≠ AbiReg.gp ∧ r ≠ AbiReg.sp ∧ r ≠ AbiReg.s0 ∧ r ≠ AbiReg.s1 ∧ r ≠ AbiReg.s2 ∧ r ≠ AbiReg.ra ∧ r ≠ AbiReg.t5 := by
  simp only [scratchRegs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem PreservedFrameRegs.of_scratch1 {fl : FrameLayout} {excl : Reg → Prop} {s1 s2 : State}
    (r0 : Reg) (hr0 : r0 ∈ scratchRegs)
    (heq : ∀ r, r ≠ r0 → s2.getReg r = s1.getReg r) :
    PreservedFrameRegs fl excl s1 s2 := by
  have habi := scratchRegs_ne_abi hr0
  refine ⟨⟨heq _ habi.1.symm, heq _ habi.2.1.symm, heq _ habi.2.2.1.symm,
      heq _ habi.2.2.2.2.1.symm⟩,
    fun _ => heq _ habi.2.2.2.2.2.1.symm,
    fun _ => heq _ habi.2.2.2.2.2.2.symm,
    fun r hr _ => heq r (allowedRegs_disj_reserved true hr (scratchRegs_sub_reserved hr0))⟩

theorem PreservedFrameRegs.of_scratch2 {fl : FrameLayout} {excl : Reg → Prop} {s1 s2 : State}
    (r0 r1 : Reg) (hr0 : r0 ∈ scratchRegs) (hr1 : r1 ∈ scratchRegs)
    (heq : ∀ r, r ≠ r0 → r ≠ r1 → s2.getReg r = s1.getReg r) :
    PreservedFrameRegs fl excl s1 s2 := by
  have h0 := scratchRegs_ne_abi hr0
  have h1 := scratchRegs_ne_abi hr1
  refine ⟨⟨heq _ h0.1.symm h1.1.symm, heq _ h0.2.1.symm h1.2.1.symm,
      heq _ h0.2.2.1.symm h1.2.2.1.symm,
      heq _ h0.2.2.2.2.1.symm h1.2.2.2.2.1.symm⟩,
    fun _ => heq _ h0.2.2.2.2.2.1.symm h1.2.2.2.2.2.1.symm,
    fun _ => heq _ h0.2.2.2.2.2.2.symm h1.2.2.2.2.2.2.symm,
    fun r hr _ => heq r
      (allowedRegs_disj_reserved true hr (scratchRegs_sub_reserved hr0))
      (allowedRegs_disj_reserved true hr (scratchRegs_sub_reserved hr1))⟩

theorem PreservedFrameRegs.of_target1 {fl : FrameLayout} {excl : Reg → Prop} {s1 s2 : State}
    (rd : Reg) (hrd : ValidTargetReg fl rd) (hexcl : rd ∈ allowedRegs true → excl rd)
    (heq : ∀ r, r ≠ rd → s2.getReg r = s1.getReg r) :
    PreservedFrameRegs fl excl s1 s2 :=
  ⟨⟨heq _ hrd.ne_gp.symm, heq _ hrd.ne_sp.symm, heq _ hrd.ne_s0.symm,
    heq _ hrd.ne_s2.symm⟩,
   fun _ => heq _ hrd.ne_ra.symm,
   fun _ => heq _ hrd.ne_t5.symm,
   fun r hr hne => heq r (fun he => hne (he ▸ hexcl (he ▸ hr)))⟩

theorem PreservedFrameRegs.of_target_scratch {fl : FrameLayout} {excl : Reg → Prop} {s1 s2 : State}
    (rd r1 : Reg) (hrd : ValidTargetReg fl rd) (hexcl : rd ∈ allowedRegs true → excl rd)
    (hr1 : r1 ∈ scratchRegs)
    (heq : ∀ r, r ≠ rd → r ≠ r1 → s2.getReg r = s1.getReg r) :
    PreservedFrameRegs fl excl s1 s2 := by
  have h1 := scratchRegs_ne_abi hr1
  refine ⟨⟨heq _ hrd.ne_gp.symm h1.1.symm, heq _ hrd.ne_sp.symm h1.2.1.symm,
      heq _ hrd.ne_s0.symm h1.2.2.1.symm,
      heq _ hrd.ne_s2.symm h1.2.2.2.2.1.symm⟩,
    fun _ => heq _ hrd.ne_ra.symm h1.2.2.2.2.2.1.symm,
    fun _ => heq _ hrd.ne_t5.symm h1.2.2.2.2.2.2.symm,
    fun r hr hne => heq r (fun he => hne (he ▸ hexcl (he ▸ hr)))
      (allowedRegs_disj_reserved true hr (scratchRegs_sub_reserved hr1))⟩

theorem PreservedFrameRegs.of_regEqExceptT6 {fl : FrameLayout} {excl : Reg → Prop} {s1 s2 : State}
    (h : RegEqExceptT6 s1.regs s2.regs) : PreservedFrameRegs fl excl s1 s2 :=
  ⟨PreservedRegs.of_regEqExceptT6 h,
   fun _ => (h.getReg_eq (by decide)).symm,
   fun _ => (h.getReg_eq (by decide)).symm,
   fun r hr _ => (h.getReg_eq ⟨allowedRegs_ne_t6 hr, allowedRegs_ne_s1 hr⟩).symm⟩

theorem PreservedFrameRegs.of_t6_s1 {fl : FrameLayout} {excl : Reg → Prop} {s1 s2 : State}
    (h : ∀ q, q ≠ AbiReg.t6 ∧ q ≠ AbiReg.s1 → s2.getReg q = s1.getReg q) :
    PreservedFrameRegs fl excl s1 s2 :=
  ⟨⟨h _ (by decide), h _ (by decide), h _ (by decide), h _ (by decide)⟩,
   fun _ => h _ (by decide),
   fun _ => h _ (by decide),
   fun r hr _ => h r ⟨allowedRegs_ne_t6 hr, allowedRegs_ne_s1 hr⟩⟩

theorem PreservedFrameRegs.of_stepReg_scratch {fl : FrameLayout} {excl : Reg → Prop}
    (st : State) (r0 : Reg) (hr0 : r0 ∈ scratchRegs) (v pc' : RV64.Word) :
    PreservedFrameRegs fl excl st (stepReg st r0 v pc') :=
  PreservedFrameRegs.of_scratch1 r0 hr0 fun r hr => getReg_stepReg_ne st r0 r hr v pc'

theorem PreservedFrameRegs.of_stepReg_target {fl : FrameLayout} {excl : Reg → Prop}
    (st : State) (rd : Reg) (hrd : ValidTargetReg fl rd)
    (hexcl : rd ∈ allowedRegs true → excl rd) (v pc' : RV64.Word) :
    PreservedFrameRegs fl excl st (stepReg st rd v pc') :=
  PreservedFrameRegs.of_target1 rd hrd hexcl fun r hr => getReg_stepReg_ne st rd r hr v pc'

theorem PreservedFrameRegs.of_a0_to {fl : FrameLayout} {excl : Reg → Prop} {s1 s2 : State}
    (h : PreservedFrameRegs fl (· = AbiReg.a0) s1 s2) :
    PreservedFrameRegs fl excl s1 s2 :=
  ⟨h.abi, h.leafRa, h.t5Gp, fun r hr _ => h.regs r hr (allowedRegs_ne_a0 hr)⟩

/-- Helper base register and adjusted offset for `loadMemOffGp` / `storeMemOffGp`. -/
def gpBaseReg (useT5 : Bool) (off : Int) : Reg :=
  if useT5 && fitsDoublePos12Int off then AbiReg.t5 else AbiReg.gp

def gpAdjOff (useT5 : Bool) (off : Int) : Int :=
  if useT5 && fitsDoublePos12Int off then off - 2047 else off

theorem gpBaseReg_ne_temp (useT5 : Bool) (off : Int) {q : Reg}
    (hq : q ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3, AbiReg.t4, AbiReg.t6]) :
    gpBaseReg useT5 off ≠ q := by
  unfold gpBaseReg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  split <;> (rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

theorem gpBaseReg_ne_t6_s1 (useT5 : Bool) (off : Int) :
    gpBaseReg useT5 off ≠ AbiReg.t6 ∧ gpBaseReg useT5 off ≠ AbiReg.s1 := by
  unfold gpBaseReg; split <;> decide

theorem loadMemOffGp_eq_loadMemOff (useT5 : Bool) (op : LoadOp) (rd tmp : Reg) (off : Int) :
    loadMemOffGp useT5 op rd tmp off = loadMemOff op rd (gpBaseReg useT5 off) tmp (gpAdjOff useT5 off) := by
  unfold loadMemOffGp gpBaseReg gpAdjOff
  by_cases h : (useT5 && fitsDoublePos12Int off) = true
  · simp only [h, ↓reduceIte, loadMemOff]
    have h2 : fitsDoublePos12Int off = true := (Bool.and_eq_true _ _ |>.mp h).2
    simp only [fitsDoublePos12Int, Bool.and_eq_true, decide_eq_true_eq] at h2
    have hfit : fitsImm12Int (off - 2047) = true := by
      simp only [fitsImm12Int, Bool.and_eq_true, decide_eq_true_eq]; omega
    simp only [hfit, ↓reduceIte]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]

theorem storeMemOffGp_eq_storeMemOff (useT5 : Bool) (op : StoreOp) (rs tmp : Reg) (off : Int) :
    storeMemOffGp useT5 op rs tmp off = storeMemOff op (gpBaseReg useT5 off) rs tmp (gpAdjOff useT5 off) := by
  unfold storeMemOffGp gpBaseReg gpAdjOff
  by_cases h : (useT5 && fitsDoublePos12Int off) = true
  · simp only [h, ↓reduceIte, storeMemOff]
    have h2 : fitsDoublePos12Int off = true := (Bool.and_eq_true _ _ |>.mp h).2
    simp only [fitsDoublePos12Int, Bool.and_eq_true, decide_eq_true_eq] at h2
    have hfit : fitsImm12Int (off - 2047) = true := by
      simp only [fitsImm12Int, Bool.and_eq_true, decide_eq_true_eq]; omega
    simp only [hfit, ↓reduceIte]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]

theorem gpBaseReg_addr {useT5 : Bool} {off : Int} {T : BitVec 64} {st : State}
    (hgp : st.getReg AbiReg.gp = T)
    (ht5 : useT5 = true → st.getReg AbiReg.t5 = T + 2047#64) :
    st.getReg (gpBaseReg useT5 off) + BitVec.ofInt 64 (gpAdjOff useT5 off) = T + BitVec.ofInt 64 off := by
  unfold gpBaseReg gpAdjOff
  by_cases h : (useT5 && fitsDoublePos12Int off) = true
  · rcases Bool.and_eq_true _ _ |>.mp h with ⟨hu, _⟩
    simp only [h, ↓reduceIte, ht5 hu, BitVec.add_assoc]
    congr 1
    rw [show (2047#64 : BitVec 64) = BitVec.ofInt 64 2047 from rfl, ← BitVec.ofInt_add]
    congr 1; omega
  · simp only [h, Bool.false_eq_true, ↓reduceIte, hgp]

theorem loadMemOffGp_ld_correct_lm (lm : LinkModel) {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code)
    (pre post : List AsmItem) (useT5 : Bool) (rd tmp : Reg)
    (hrd : rd ≠ 0#5) (htmp : tmp ≠ 0#5) (htmpGp : tmp ≠ AbiReg.gp) (htmpT5 : useT5 = true → tmp ≠ AbiReg.t5)
    (off : Int) (T : BitVec 64)
    (hlink : lm.linkSpec (pre ++ loadMemOffGp useT5 .ld rd tmp off ++ post) = .ok (code, labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (loadMemOffGp useT5 .ld rd tmp off)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = T)
    (ht5 : useT5 = true → st.getReg AbiReg.t5 = T + 2047#64)
    (hal : isAligned (T + BitVec.ofInt 64 off) 8 = true) :
    ∃ st', RV64.run rom (lm.totalSize (loadMemOffGp useT5 .ld rd tmp off)) st = .cont st' ∧
      (∀ q, q ≠ rd → q ≠ tmp → st'.getReg q = st.getReg q) ∧
      st'.getReg rd = readWord64 st.mem (T + BitVec.ofInt 64 off) ∧
      st'.mem = st.mem ∧
      st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (loadMemOffGp useT5 .ld rd tmp off))) := by
  have hneBase : gpBaseReg useT5 off ≠ tmp := by
    unfold gpBaseReg
    by_cases h : (useT5 && fitsDoublePos12Int off) = true
    · simp only [h, ↓reduceIte]; exact (htmpT5 (Bool.and_eq_true _ _ |>.mp h).1).symm
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact htmpGp.symm
  have haddr := gpBaseReg_addr (off := off) hgp ht5
  rw [loadMemOffGp_eq_loadMemOff] at hlink h64 ⊢
  obtain ⟨st', hrun, hoth, hrd', hmem, hpc'⟩ :=
    loadMemOff_ld_correct_lm lm hrom pre post rd (gpBaseReg useT5 off) tmp
      hrd htmp hneBase (gpAdjOff useT5 off) hlink h64 st hpc (by rw [haddr]; exact hal)
  exact ⟨st', hrun, hoth, by rw [hrd', haddr], hmem, hpc'⟩

theorem storeMemOffGp_sd_correct_lm (lm : LinkModel) {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code)
    (pre post : List AsmItem) (useT5 : Bool) (rs tmp : Reg)
    (htmp : tmp ≠ 0#5) (htmpGp : tmp ≠ AbiReg.gp) (htmpT5 : useT5 = true → tmp ≠ AbiReg.t5) (htmpRs : tmp ≠ rs)
    (off : Int) (T : BitVec 64)
    (hlink : lm.linkSpec (pre ++ storeMemOffGp useT5 .sd rs tmp off ++ post) = .ok (code, labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (storeMemOffGp useT5 .sd rs tmp off)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = T)
    (ht5 : useT5 = true → st.getReg AbiReg.t5 = T + 2047#64)
    (hal : isAligned (T + BitVec.ofInt 64 off) 8 = true) :
    ∃ st', RV64.run rom (lm.totalSize (storeMemOffGp useT5 .sd rs tmp off)) st = .cont st' ∧
      (∀ q, q ≠ tmp → st'.getReg q = st.getReg q) ∧
      st'.mem = writeWord64 st.mem (T + BitVec.ofInt 64 off) (st.getReg rs) ∧
      st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (storeMemOffGp useT5 .sd rs tmp off))) := by
  have hneBase : gpBaseReg useT5 off ≠ tmp := by
    unfold gpBaseReg
    by_cases h : (useT5 && fitsDoublePos12Int off) = true
    · simp only [h, ↓reduceIte]; exact (htmpT5 (Bool.and_eq_true _ _ |>.mp h).1).symm
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact htmpGp.symm
  have haddr := gpBaseReg_addr (off := off) hgp ht5
  rw [storeMemOffGp_eq_storeMemOff] at hlink h64 ⊢
  obtain ⟨st', hrun, hoth, hmem, hpc'⟩ :=
    storeMemOff_sd_correct_lm lm hrom pre post (gpBaseReg useT5 off) rs tmp
      htmp hneBase.symm htmpRs (gpAdjOff useT5 off) hlink h64 st hpc (by rw [haddr]; exact hal)
  exact ⟨st', hrun, hoth, by rw [hmem, haddr], hpc'⟩

/-- Invariant asserting that hoisted `t5` holds `L.T + 2047` whenever `fl.useT5Gp = true`. -/
abbrev T5GpOk {tab : Tab} (L : ProgLayout tab) (fl : FrameLayout) (st : State) : Prop :=
  fl.useT5Gp = true → st.getReg AbiReg.t5 = L.T + 2047#64

theorem T5GpOk.of_preserved {tab : Tab} {L : ProgLayout tab} {fl : FrameLayout} {P : Reg → Prop}
    {st st' : State} (hpres : PreservedFrameRegs fl P st st') (ht5 : T5GpOk L fl st) :
    T5GpOk L fl st' := fun h => (hpres.t5Gp h).trans (ht5 h)

theorem bv_shr_and_lowMask {x mask : BitVec 64} {lm : BitVec 6} {sh : Nat}
    (hmask : mask = (1#64 <<< (64 - lm.toNat)) - 1#64)
    (hlm0 : 0 < lm.toNat) (hlm64 : lm.toNat < 64)
    (hsh : sh ≤ lm.toNat) :
    (x >>> sh) &&& mask = (x <<< (lm.toNat - sh)) >>> lm.toNat := by
  have _ := hlm64
  have hmaskBits : ∀ i : Nat, i < 64 → mask.getLsbD i = decide (i < 64 - lm.toNat) := by
    intro i hi
    rw [hmask]
    have hpow : 1 ≤ 2 ^ (64 - lm.toNat) := Nat.one_le_pow _ 2 (by omega)
    have hlt64 : 2 ^ (64 - lm.toNat) < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) (by omega)
    have hsub : ((1#64 <<< (64 - lm.toNat)) - 1#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ (64 - lm.toNat) - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft, show (1#64).toNat = 1 from rfl, Nat.shiftLeft_eq,
        Nat.one_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64,
        Nat.mod_eq_of_lt (show 2 ^ (64 - lm.toNat) - 1 < 2 ^ 64 by omega)]
      have : 2 ^ 64 - 1 + 2 ^ (64 - lm.toNat) = 2 ^ 64 + (2 ^ (64 - lm.toNat) - 1) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hsub, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
    simp only [hi, decide_true, Bool.true_and]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_shiftLeft, hmaskBits i hi]
  by_cases hlt : i < 64 - lm.toNat
  · have h1 : lm.toNat + i < 64 := by omega
    have h2 : ¬(lm.toNat + i < lm.toNat - sh) := by omega
    have h3 : lm.toNat + i - (lm.toNat - sh) = sh + i := by omega
    simp only [hlt, decide_true, Bool.and_true, h1, h2, decide_false, Bool.not_false, Bool.true_and, h3]
  · have h1 : ¬(lm.toNat + i < 64) := by omega
    simp only [hlt, decide_false, Bool.and_false, h1, Bool.false_and]

theorem lowMaskShift_spec {mask : UInt64} {lm : BitVec 6} (h : lowMaskShift? mask = some lm) :
    mask.toBitVec = (1#64 <<< (64 - lm.toNat)) - 1#64 ∧ 0 < lm.toNat ∧ lm.toNat < 64 := by
  simp only [lowMaskShift?] at h
  split at h
  · cases h
  · split at h
    · next hcond =>
      cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond
      rcases hcond with ⟨⟨hk12, hk64⟩, hmeq⟩
      have hlm : (BitVec.ofNat 6 (64 - ctz64 (mask.toBitVec + 1#64))).toNat = 64 - ctz64 (mask.toBitVec + 1#64) := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine ⟨?_, by omega, by omega⟩
      rw [hlm, show 64 - (64 - ctz64 (mask.toBitVec + 1#64)) = ctz64 (mask.toBitVec + 1#64) by omega]
      exact hmeq
    · cases h

theorem half32b_false_eq_and (w : UInt64) : half32b false w = w &&& 0xffffffff := by
  simp only [half32b, Bool.false_eq_true, ↓reduceIte]

theorem half32b_true_eq_shr (w : UInt64) : half32b true w = w >>> 32 := by
  simp only [half32b, ↓reduceIte]

/-- Compact frame memory spans under `FrameLayout`. -/
def frameSpanR (fl : FrameLayout) (sp : BitVec 64) : MemSpan :=
  { base := sp, size := 8 * fl.frameSlots }

def varSlotSpanR (fl : FrameLayout) (sp : BitVec 64) (x : Var) : MemSpan :=
  slotSpan sp (fl.protectedSlots + fl.spillIdx x)

def tempSlotSpanR (fl : FrameLayout) (sp : BitVec 64) (tmp : Nat) : MemSpan :=
  slotSpan sp (fl.protectedSlots + fl.spilledVars.length + tmp)

def tempSpanR (fl : FrameLayout) (sp : BitVec 64) (tmp : Nat) : MemSpan :=
  { base := sp + BitVec.ofNat 64 (8 * (fl.protectedSlots + fl.spilledVars.length + tmp)),
    size := 8 * (fl.usedTemps - tmp) }

def localsTempSpanR (fl : FrameLayout) (sp : BitVec 64) : MemSpan :=
  { base := sp + BitVec.ofNat 64 (8 * fl.protectedSlots),
    size := 8 * (fl.spilledVars.length + fl.usedTemps) }

theorem varSlotOff_ofInt (fl : FrameLayout) (x : Var) :
    BitVec.ofInt 64 (fl.varSlotOff x) = BitVec.ofNat 64 (8 * (fl.protectedSlots + fl.spillIdx x)) := by
  unfold FrameLayout.varSlotOff
  rw [show (8 : Int) * ((fl.protectedSlots + fl.spillIdx x : Nat) : Int) =
      ((8 * (fl.protectedSlots + fl.spillIdx x) : Nat) : Int) from by omega, BitVec.ofInt_natCast]

theorem tempSlotOff_ofInt (fl : FrameLayout) (tmp : Nat) :
    BitVec.ofInt 64 (fl.tempSlotOff tmp) =
      BitVec.ofNat 64 (8 * (fl.protectedSlots + fl.spilledVars.length + tmp)) := by
  unfold FrameLayout.tempSlotOff
  rw [show (8 : Int) * ((fl.protectedSlots + fl.spilledVars.length + tmp : Nat) : Int) =
      ((8 * (fl.protectedSlots + fl.spilledVars.length + tmp) : Nat) : Int) from by omega, BitVec.ofInt_natCast]

theorem savedOff_ofInt (fl : FrameLayout) (i : Nat) :
    BitVec.ofInt 64 (fl.savedOff i) = BitVec.ofNat 64 (8 * (fl.raSlots + i)) := by
  unfold FrameLayout.savedOff
  rw [show (8 : Int) * ((fl.raSlots + i : Nat) : Int) = ((8 * (fl.raSlots + i) : Nat) : Int) from by omega,
    BitVec.ofInt_natCast]

theorem frameSpanR_sub_stackSpan {tab : Tab} (L : ProgLayout tab) {fl : FrameLayout} {sp : BitVec 64}
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat) :
    (frameSpanR fl sp).sub L.stackSpan := by
  intro a ha
  rcases ha with ⟨k, hk, rfl⟩
  dsimp only [frameSpanR] at hk
  have hvalid : L.stackTop.toNat ≤ 2 ^ 64 := L.hStackValid
  have hsub : sp.toNat - L.stackLimit.toNat + k < L.stackTop.toNat - L.stackLimit.toNat := by omega
  refine ⟨sp.toNat - L.stackLimit.toNat + k, hsub, ?_⟩
  apply BitVec.eq_of_toNat_eq
  dsimp only [ProgLayout.stackSpan, frameSpanR]
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem tempSpanR_sub_frameSpanR (fl : FrameLayout) (sp : BitVec 64) (tmp : Nat)
    (_hvalid : (frameSpanR fl sp).valid) (htmp : tmp ≤ fl.usedTemps) :
    (tempSpanR fl sp tmp).sub (frameSpanR fl sp) := by
  intro a ha
  rcases ha with ⟨k, hk, rfl⟩
  dsimp only [tempSpanR, frameSpanR, MemSpan.valid, FrameLayout.frameSlots] at hk ⊢
  refine ⟨8 * (fl.protectedSlots + fl.spilledVars.length + tmp) + k, ?_, ?_⟩
  · dsimp only [frameSpanR, FrameLayout.frameSlots]; omega
  · dsimp only [frameSpanR]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem tempSpanR_mono (fl : FrameLayout) (sp : BitVec 64) {t1 t2 : Nat}
    (_hvalid : (frameSpanR fl sp).valid) (h12 : t1 ≤ t2) (h2 : t2 ≤ fl.usedTemps) :
    (tempSpanR fl sp t2).sub (tempSpanR fl sp t1) := by
  intro a ha
  rcases ha with ⟨k, hk, rfl⟩
  dsimp only [tempSpanR, frameSpanR, MemSpan.valid, FrameLayout.frameSlots] at hk ⊢
  refine ⟨8 * (t2 - t1) + k, ?_, ?_⟩
  · dsimp only [tempSpanR]; omega
  · dsimp only [tempSpanR]
    rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 1
    rw [show 8 * (fl.protectedSlots + fl.spilledVars.length + t1) + (8 * (t2 - t1) + k) =
        8 * (fl.protectedSlots + fl.spilledVars.length + t2) + k by omega]

theorem tempSlotSpanR_sub_tempSpanR (fl : FrameLayout) (sp : BitVec 64) {t1 tmp : Nat}
    (_hvalid : (frameSpanR fl sp).valid) (hle : t1 ≤ tmp) (hlt : tmp < fl.usedTemps) :
    (tempSlotSpanR fl sp tmp).sub (tempSpanR fl sp t1) := by
  intro a ha
  rcases ha with ⟨k, hk, rfl⟩
  dsimp only [tempSlotSpanR, slotSpan, slotAddr, tempSpanR, frameSpanR, MemSpan.valid,
    FrameLayout.frameSlots] at hk ⊢
  refine ⟨8 * (tmp - t1) + k, ?_, ?_⟩
  · dsimp only [tempSpanR]; omega
  · dsimp only [tempSpanR]
    rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 1
    rw [show 8 * (fl.protectedSlots + fl.spilledVars.length + t1) + (8 * (tmp - t1) + k) =
        8 * (fl.protectedSlots + fl.spilledVars.length + tmp) + k by omega]

theorem tempSpanR_disj_varSlot (fl : FrameLayout) (hfl : FrameLayoutOk fl) (sp : BitVec 64)
    (hvalid : (frameSpanR fl sp).valid) (tmp : Nat) (htmp : tmp ≤ fl.usedTemps)
    {x : Var} (hmem : x ∈ fl.spilledVars) :
    MemDisjoint (tempSpanR fl sp tmp) (varSlotSpanR fl sp x) := by
  have hsi := hfl.spillIdx_lt hmem
  dsimp only [frameSpanR, MemSpan.valid, FrameLayout.frameSlots] at hvalid
  intro a h1 h2
  rcases h1 with ⟨k1, hk1, ha1⟩
  rcases h2 with ⟨k2, hk2, ha2⟩
  dsimp only [tempSpanR, varSlotSpanR, slotSpan, slotAddr] at hk1 hk2 ha1 ha2
  have heq : (sp + BitVec.ofNat 64 (8 * (fl.protectedSlots + fl.spilledVars.length + tmp)) + BitVec.ofNat 64 k1).toNat =
      (sp + BitVec.ofNat 64 (8 * (fl.protectedSlots + fl.spillIdx x)) + BitVec.ofNat 64 k2).toNat := by
    rw [← ha1, ← ha2]
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
    BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq
  omega

theorem tempSpanR_disj_tempSlot (fl : FrameLayout) (sp : BitVec 64)
    (hvalid : (frameSpanR fl sp).valid) {t1 t2 : Nat} (hlt : t1 < t2) (h2 : t2 ≤ fl.usedTemps) :
    MemDisjoint (tempSpanR fl sp t2) (tempSlotSpanR fl sp t1) := by
  dsimp only [frameSpanR, MemSpan.valid, FrameLayout.frameSlots] at hvalid
  intro a h1 h2m
  rcases h1 with ⟨k1, hk1, ha1⟩
  rcases h2m with ⟨k2, hk2, ha2⟩
  dsimp only [tempSpanR, tempSlotSpanR, slotSpan, slotAddr] at hk1 hk2 ha1 ha2
  have heq : (sp + BitVec.ofNat 64 (8 * (fl.protectedSlots + fl.spilledVars.length + t2)) + BitVec.ofNat 64 k1).toNat =
      (sp + BitVec.ofNat 64 (8 * (fl.protectedSlots + fl.spilledVars.length + t1)) + BitVec.ofNat 64 k2).toNat := by
    rw [← ha1, ← ha2]
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
    BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq
  omega

theorem varSlotSpanR_disj_of_ne (fl : FrameLayout) (hfl : FrameLayoutOk fl) (sp : BitVec 64)
    (hvalid : (frameSpanR fl sp).valid) {x y : Var}
    (hmx : x ∈ fl.spilledVars) (hmy : y ∈ fl.spilledVars) (hne : x ≠ y) :
    MemDisjoint (varSlotSpanR fl sp x) (varSlotSpanR fl sp y) := by
  have hsx := hfl.spillIdx_lt hmx
  have hsy := hfl.spillIdx_lt hmy
  have hneIdx : fl.spillIdx x ≠ fl.spillIdx y := fun he => hne (hfl.spillIdx_inj hmx hmy he)
  dsimp only [frameSpanR, MemSpan.valid, FrameLayout.frameSlots] at hvalid
  intro a h1 h2
  rcases h1 with ⟨k1, hk1, ha1⟩
  rcases h2 with ⟨k2, hk2, ha2⟩
  dsimp only [varSlotSpanR, slotSpan, slotAddr] at hk1 hk2 ha1 ha2
  have heq : (sp + BitVec.ofNat 64 (8 * (fl.protectedSlots + fl.spillIdx x)) + BitVec.ofNat 64 k1).toNat =
      (sp + BitVec.ofNat 64 (8 * (fl.protectedSlots + fl.spillIdx y)) + BitVec.ofNat 64 k2).toNat := by
    rw [← ha1, ← ha2]
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
    BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq
  omega

/-- Every read variable not assigned a register has a stack spill slot in `fl.spilledVars`. -/
def VarInFrame (fl : FrameLayout) (x : Var) : Prop :=
  fl.alloc.lookup x = none → x ∈ fl.spilledVars

def ExprVarsInFrame (fl : FrameLayout) (e : Expr) : Prop :=
  ∀ x, exprUsesVar x e = true → VarInFrame fl x

def CondVarsInFrame (fl : FrameLayout) (c : Cond) : Prop :=
  ∀ x, condUsesVar x c = true → VarInFrame fl x

def ExprsVarsInFrame (fl : FrameLayout) (es : List Expr) : Prop :=
  ∀ x, es.any (exprUsesVar x) = true → VarInFrame fl x

def WArrVarsInFrame (fl : FrameLayout) (w : WArr) : Prop :=
  ∀ x, warrUsesVar x w = true → VarInFrame fl x

def StmtVarsInFrame (fl : FrameLayout) (s : Stmt) : Prop :=
  ∀ x, stmtUsesVar x s = true → VarInFrame fl x

/-- Register + stack frame relation for `fl`: allocated vars live in their assigned registers,
    spilled vars (`x ∈ fl.spilledVars`) live at `sp + fl.varSlotOff x`. -/
def ProgFrameOkR {tab : Tab} (_L : ProgLayout tab) (fl : FrameLayout) (sp : BitVec 64)
    (st : State) (loc : _root_.L.Locals) : Prop :=
  ∀ x, x < fl.nlocals →
    match fl.alloc.lookup x with
    | some r => st.getReg r = (loc x).toBitVec
    | none   => x ∈ fl.spilledVars → readWord64 st.mem (sp + BitVec.ofInt 64 (fl.varSlotOff x)) = (loc x).toBitVec

/-- Frame invariant restricted to variables currently live according to `live : Var → Bool`.
    Supports both call-free caller-saved registers and live-range register sharing (graph coloring). -/
def ProgFrameOkLive {tab : Tab} (_L : ProgLayout tab) (fl : FrameLayout) (sp : BitVec 64)
    (st : State) (loc : _root_.L.Locals) (live : Var → Bool) : Prop :=
  ∀ x, x < fl.nlocals → live x = true →
    match fl.alloc.lookup x with
    | some r => st.getReg r = (loc x).toBitVec
    | none   => x ∈ fl.spilledVars → readWord64 st.mem (sp + BitVec.ofInt 64 (fl.varSlotOff x)) = (loc x).toBitVec

theorem ProgFrameOkR.toLive {tab : Tab} {L : ProgLayout tab} {fl : FrameLayout} {sp : BitVec 64}
    {st : State} {loc loc' : _root_.L.Locals} {live : Var → Bool}
    (hf : ProgFrameOkR L fl sp st loc') (hag : ∀ x, live x = true → loc' x = loc x) :
    ProgFrameOkLive L fl sp st loc live := by
  intro x hx hlv; rw [← hag x hlv]; exact hf x hx

theorem ProgFrameOkR.toLive_self {tab : Tab} {L : ProgLayout tab} {fl : FrameLayout} {sp : BitVec 64}
    {st : State} {loc : _root_.L.Locals} (live : Var → Bool)
    (hf : ProgFrameOkR L fl sp st loc) :
    ProgFrameOkLive L fl sp st loc live :=
  hf.toLive fun _ _ => rfl

theorem ProgFrameOkR.of_preserved_temp {tab : Tab} {L : ProgLayout tab} {fl : FrameLayout}
    (hfl : FrameLayoutOk fl) {sp : BitVec 64} {tmp : Nat} {st1 st2 : State} {loc : _root_.L.Locals}
    (hvalid : (frameSpanR fl sp).valid) (htmp : tmp ≤ fl.usedTemps)
    (hpres : PreservedFrameRegs fl (· = AbiReg.a0) st1 st2)
    (heq : MemEqOutside (tempSpanR fl sp tmp) st1.mem st2.mem)
    (hf : ProgFrameOkR L fl sp st1 loc) : ProgFrameOkR L fl sp st2 loc := by
  intro x hx
  have hfx := hf x hx
  cases hl : fl.alloc.lookup x with
  | some r =>
    rw [hl] at hfx
    dsimp only at hfx ⊢
    have hmem := (regAllocValid_lookup hfl.valid hl).2.1
    rw [hpres.regs r (allowedRegs_sub_true hmem) (allowedRegs_ne_a0 hmem), hfx]
  | none =>
    rw [hl] at hfx
    dsimp only at hfx ⊢
    intro hmem
    rw [← hfx hmem, varSlotOff_ofInt]
    exact MemEqOutside.readWord64_eq heq _ fun k hk =>
      (tempSpanR_disj_varSlot fl hfl sp hvalid tmp htmp hmem).symm _
        ⟨k, hk, by simp [varSlotSpanR, slotSpan, slotAddr]⟩

theorem ProgFrameOkR.of_set_reg_live {tab : Tab} {L : ProgLayout tab} {fl : FrameLayout}
    (hfl : FrameLayoutOk fl) {sp : BitVec 64} {st1 st2 : State} {loc : _root_.L.Locals}
    {live2 : Var → Bool}
    (hvalid : (frameSpanR fl sp).valid)
    {x : Var} {rx : Reg} {v : _root_.L.Word}
    (hlx : fl.alloc.lookup x = some rx)
    (hpres : PreservedFrameRegs fl (· = rx) st1 st2)
    (hrx : st2.getReg rx = v.toBitVec)
    (heq : MemEqOutside (tempSpanR fl sp 0) st1.mem st2.mem)
    (hnoClob : ∀ y, y ≠ x → live2 y = true → fl.alloc.lookup y ≠ some rx)
    (hf : ProgFrameOkR L fl sp st1 loc) :
    ProgFrameOkLive L fl sp st2 (fun y => if y = x then v else loc y) live2 := by
  intro y hy hly2
  by_cases hxy : y = x
  · subst hxy; rw [hlx]; simp only [↓reduceIte]; exact hrx
  · simp only [hxy, ↓reduceIte]
    have hfy := hf y hy
    cases hly : fl.alloc.lookup y with
    | some ry =>
      rw [hly] at hfy; dsimp only at hfy ⊢
      have hmem := (regAllocValid_lookup hfl.valid hly).2.1
      have hne : ry ≠ rx := fun he => hnoClob y hxy hly2 (he ▸ hly)
      rw [hpres.regs ry (allowedRegs_sub_true hmem) hne, hfy]
    | none =>
      rw [hly] at hfy; dsimp only at hfy ⊢
      intro hmy
      rw [← hfy hmy, varSlotOff_ofInt]
      exact MemEqOutside.readWord64_eq heq _ fun k hk =>
        (tempSpanR_disj_varSlot fl hfl sp hvalid 0 (Nat.zero_le _) hmy).symm _
          ⟨k, hk, by simp [varSlotSpanR, slotSpan, slotAddr]⟩

theorem ProgFrameOkR.of_set_dead {tab : Tab} {L : ProgLayout tab} {fl : FrameLayout}
    (hfl : FrameLayoutOk fl) {sp : BitVec 64} {st1 st2 : State} {loc : _root_.L.Locals}
    (hvalid : (frameSpanR fl sp).valid)
    {x : Var} (v : _root_.L.Word)
    (hlx : fl.alloc.lookup x = none) (hnot : x ∉ fl.spilledVars)
    (hpres : PreservedFrameRegs fl (· = AbiReg.a0) st1 st2)
    (heq : MemEqOutside (tempSpanR fl sp 0) st1.mem st2.mem)
    (hf : ProgFrameOkR L fl sp st1 loc) :
    ProgFrameOkR L fl sp st2 (fun y => if y = x then v else loc y) := by
  intro y hy
  by_cases hxy : y = x
  · subst hxy; rw [hlx]; intro hmx; exact absurd hmx hnot
  · simp only [hxy, ↓reduceIte]
    exact ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) hpres heq hf y hy

theorem ProgFrameOkLive.of_set_reg {tab : Tab} {L : ProgLayout tab} {fl : FrameLayout}
    (hfl : FrameLayoutOk fl) {sp : BitVec 64} {st1 st2 : State} {loc : _root_.L.Locals}
    {live1 live2 : Var → Bool}
    (hvalid : (frameSpanR fl sp).valid)
    {x : Var} {rx : Reg} {v : _root_.L.Word}
    (hlx : fl.alloc.lookup x = some rx)
    (hpres : PreservedFrameRegs fl (· = rx) st1 st2)
    (hrx : st2.getReg rx = v.toBitVec)
    (heq : MemEqOutside (tempSpanR fl sp 0) st1.mem st2.mem)
    (hsub : ∀ y, y ≠ x → live2 y = true → live1 y = true)
    (hnoClob : ∀ y, y ≠ x → live2 y = true → fl.alloc.lookup y ≠ some rx)
    (hf : ProgFrameOkLive L fl sp st1 loc live1) :
    ProgFrameOkLive L fl sp st2 (fun y => if y = x then v else loc y) live2 := by
  intro y hy hly2
  by_cases hxy : y = x
  · subst hxy; rw [hlx]; simp only [↓reduceIte]; exact hrx
  · simp only [hxy, ↓reduceIte]
    have hfy := hf y hy (hsub y hxy hly2)
    cases hly : fl.alloc.lookup y with
    | some ry =>
      rw [hly] at hfy; dsimp only at hfy ⊢
      have hmem := (regAllocValid_lookup hfl.valid hly).2.1
      have hne : ry ≠ rx := fun he => hnoClob y hxy hly2 (he ▸ hly)
      rw [hpres.regs ry (allowedRegs_sub_true hmem) hne, hfy]
    | none =>
      rw [hly] at hfy; dsimp only at hfy ⊢
      intro hmy
      rw [← hfy hmy, varSlotOff_ofInt]
      exact MemEqOutside.readWord64_eq heq _ fun k hk =>
        (tempSpanR_disj_varSlot fl hfl sp hvalid 0 (Nat.zero_le _) hmy).symm _
          ⟨k, hk, by simp [varSlotSpanR, slotSpan, slotAddr]⟩

theorem ProgFrameOkR.of_set_spill {tab : Tab} {L : ProgLayout tab} {fl : FrameLayout}
    (hfl : FrameLayoutOk fl) {sp : BitVec 64} {st1 st2 : State} {loc : _root_.L.Locals}
    (hvalid : (frameSpanR fl sp).valid)
    {x : Var} {v : _root_.L.Word} (hmx : x ∈ fl.spilledVars)
    (hpres : PreservedFrameRegs fl (· = AbiReg.a0) st1 st2)
    (hmem : st2.mem = writeWord64 st1.mem (sp + BitVec.ofInt 64 (fl.varSlotOff x)) v.toBitVec)
    (hf : ProgFrameOkR L fl sp st1 loc) :
    ProgFrameOkR L fl sp st2 (fun y => if y = x then v else loc y) := by
  have ⟨_, hxn⟩ := hfl.spilledSub x hmx
  have hsi := hfl.spillIdx_lt hmx
  dsimp only [frameSpanR, MemSpan.valid, FrameLayout.frameSlots] at hvalid
  intro y hy
  by_cases hxy : y = x
  · subst hxy; rw [hxn, hmem]; simp only [↓reduceIte]
    intro _
    exact readWord64_writeWord64_self st1.mem _ v.toBitVec
  · simp only [hxy, ↓reduceIte]
    have hfy := hf y hy
    cases hly : fl.alloc.lookup y with
    | some ry =>
      rw [hly] at hfy; dsimp only at hfy ⊢
      have hmemR := (regAllocValid_lookup hfl.valid hly).2.1
      rw [hpres.regs ry (allowedRegs_sub_true hmemR) (allowedRegs_ne_a0 hmemR), hfy]
    | none =>
      rw [hly] at hfy; dsimp only at hfy ⊢
      intro hmy
      rw [← hfy hmy, hmem]
      have hout : MemEqOutside (varSlotSpanR fl sp x) st1.mem
          (writeWord64 st1.mem (sp + BitVec.ofInt 64 (fl.varSlotOff x)) v.toBitVec) := by
        rw [varSlotOff_ofInt]
        exact MemEqOutside.writeWord64 st1.mem _ v.toBitVec fun k hk =>
          ⟨k, hk, rfl⟩
      rw [varSlotOff_ofInt]
      exact MemEqOutside.readWord64_eq hout _ fun k hk =>
        (varSlotSpanR_disj_of_ne fl hfl sp hvalid hmx hmy (Ne.symm hxy)).symm _
          ⟨k, hk, by simp [varSlotSpanR, slotSpan, slotAddr, varSlotOff_ofInt]⟩

theorem ProgMemRel.of_tempSpanR {tab : Tab} {L : ProgLayout tab} {fl : FrameLayout}
    {sp : BitVec 64} {tmp : Nat} {m1 m2 : ByteMem} {lm : _root_.L.Mem}
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (htmp : tmp ≤ fl.usedTemps)
    (heq : MemEqOutside (tempSpanR fl sp tmp) m1 m2)
    (hrel : ProgMemRel tab L m1 lm) : ProgMemRel tab L m2 lm :=
  ProgMemRel.of_stack_eqOutside
    (MemSpan.sub_trans (tempSpanR_sub_frameSpanR fl sp tmp (Nat.le_trans hhi L.hStackValid) htmp)
      (frameSpanR_sub_stackSpan L hlo hhi))
    heq hrel

/-- Write mask for a register-allocated function at `sp`: may modify stack below `sp`,
    spilled locals and temps `[sp + 8 * fl.protectedSlots, sp + 8 * fl.frameSlots)` (preserving
    saved `ra` and saved callee-saved regs at `[sp, sp + 8 * fl.protectedSlots)`),
    `resGlobSpan`, and arrays. -/
def FnWriteMaskR {tab : Tab} (L : ProgLayout tab) (fl : FrameLayout) (sp : BitVec 64)
    (a : BitVec 64) : Prop :=
  (L.stackSpan.contains a ∧
    (a.toNat < sp.toNat ∨
      (sp.toNat + 8 * fl.protectedSlots ≤ a.toNat ∧ a.toNat < sp.toNat + 8 * fl.frameSlots))) ∨
  L.resGlobSpan.contains a ∨
  (∃ idx, tab.bytePosOkB idx = true ∧ (L.arr8Span idx).contains a) ∨
  (∃ s, tab.wordPosOkB s = true ∧ (L.arr64Span s).contains a)

theorem fnWriteMaskR_of_tempSpanR {tab : Tab} (L : ProgLayout tab) {fl : FrameLayout}
    {sp : BitVec 64} {tmp : Nat}
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (htmp : tmp ≤ fl.usedTemps) :
    ∀ a, (tempSpanR fl sp tmp).contains a → FnWriteMaskR L fl sp a := by
  have hvalid : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  intro a ha
  left
  refine ⟨frameSpanR_sub_stackSpan L hlo hhi a (tempSpanR_sub_frameSpanR fl sp tmp hvalid htmp a ha), Or.inr ?_⟩
  rcases ha with ⟨k, hk, rfl⟩
  dsimp only [tempSpanR, frameSpanR, MemSpan.valid, FrameLayout.frameSlots] at hvalid hk ⊢
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem fnWriteMaskR_of_varSlot {tab : Tab} (L : ProgLayout tab) {fl : FrameLayout}
    (hfl : FrameLayoutOk fl) {sp : BitVec 64} {x : Var}
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (hmx : x ∈ fl.spilledVars) :
    ∀ a, (varSlotSpanR fl sp x).contains a → FnWriteMaskR L fl sp a := by
  have hvalid : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  have hsi := hfl.spillIdx_lt hmx
  intro a ha
  rcases ha with ⟨k, hk, rfl⟩
  dsimp only [varSlotSpanR, slotSpan, slotAddr, frameSpanR, MemSpan.valid, FrameLayout.frameSlots] at hvalid hk ⊢
  left
  refine ⟨frameSpanR_sub_stackSpan L hlo hhi _ ⟨8 * (fl.protectedSlots + fl.spillIdx x) + k,
    by dsimp only [frameSpanR, FrameLayout.frameSlots]; omega,
    by dsimp only [frameSpanR]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]⟩, Or.inr ?_⟩
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  dsimp only [FrameLayout.frameSlots]; omega

theorem fnWriteMaskR_of_localsTempSpanR {tab : Tab} (L : ProgLayout tab) {fl : FrameLayout}
    {sp : BitVec 64}
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat) :
    ∀ a, (localsTempSpanR fl sp).contains a → FnWriteMaskR L fl sp a := by
  have hvalid : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  intro a ha
  rcases ha with ⟨k, hk, rfl⟩
  dsimp only [localsTempSpanR, frameSpanR, MemSpan.valid, FrameLayout.frameSlots] at hvalid hk ⊢
  left
  refine ⟨frameSpanR_sub_stackSpan L hlo hhi _ ⟨8 * fl.protectedSlots + k,
    by dsimp only [frameSpanR, FrameLayout.frameSlots]; omega,
    by dsimp only [frameSpanR]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]⟩, Or.inr ?_⟩
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  dsimp only [FrameLayout.frameSlots]; omega

theorem fnWriteMaskR_not_protected {tab : Tab} (L : ProgLayout tab) {fl : FrameLayout}
    {sp : BitVec 64} (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    {slot : Nat} (hslot : slot < fl.protectedSlots) {k : Nat} (hk : k < 8) :
    ¬FnWriteMaskR L fl sp (sp + BitVec.ofNat 64 (8 * slot) + BitVec.ofNat 64 k) := by
  have hvalid : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  dsimp only [frameSpanR, MemSpan.valid, FrameLayout.frameSlots] at hvalid
  have hsubStack := frameSpanR_sub_stackSpan L hlo hhi
  have hcont : L.stackSpan.contains (sp + BitVec.ofNat 64 (8 * slot) + BitVec.ofNat 64 k) :=
    hsubStack _ ⟨8 * slot + k, by dsimp only [frameSpanR, FrameLayout.frameSlots]; omega,
      by dsimp only [frameSpanR]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]⟩
  have htoNat : (sp + BitVec.ofNat 64 (8 * slot) + BitVec.ofNat 64 k).toNat = sp.toNat + 8 * slot + k := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  intro hm
  rcases hm with ⟨_, hlt | ⟨hge, _⟩⟩ | hres | ⟨idx, hidx, h8⟩ | ⟨s, hs, h64⟩
  · omega
  · omega
  · exact (MemSpan.disjoint_to_memDisjoint L.tabSpan_valid L.stackSpan_valid L.htabDisjStack) _
      (L.resGlob_sub_tab _ hres) hcont
  · exact (MemSpan.disjoint_to_memDisjoint (L.arr8Span_valid idx) L.stackSpan_valid (L.h8DisjStack idx hidx)) _
      h8 hcont
  · exact (MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid s) L.stackSpan_valid (L.h64DisjStack s hs)) _
      h64 hcont

/-! ## 3. Single-Instruction & Leaf Expression Helpers -/

theorem step_lwu_off_r {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (rd base : Reg) (off : BitVec 12) (hrd : rd ≠ AbiReg.zero)
    (hlink : lkm.linkSpec (pre ++ [Asm.raw (.load .lwu rd base off)] ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + 1) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hal : isAligned (st.getReg base + sextImm12 off) 4 = true) :
    let addr := st.getReg base + sextImm12 off
    let st' := stepReg st rd ((loadBytes st.mem addr 4).zeroExtend 64) (st.pc + 4#64)
    RV64.run env.rom 1 st = .cont st' ∧
    st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)) ∧
    st'.getReg rd = (loadBytes st.mem addr 4).zeroExtend 64 ∧
    (∀ r, r ≠ rd → st'.getReg r = st.getReg r) ∧
    st'.mem = st.mem := by
  intro addr st'
  have hs := step_item_instr_lm lkm env.hrom pre post (.load .lwu rd base off) hlink (by omega) st hpc
  refine ⟨run_one_cont _ _ st' (by rw [hs]; simp only [execInstr, hal]; rfl),
    pc_add_4_ofNat st.pc hpc, getReg_stepReg_eq st rd hrd _ _,
    fun r hr => getReg_stepReg_ne st rd r hr _ _,
    by dsimp only [st', stepReg, RV64.State.setReg]; split <;> rfl⟩

theorem step_lbu_off_r {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (rd base : Reg) (off : BitVec 12) (hrd : rd ≠ AbiReg.zero)
    (hlink : lkm.linkSpec (pre ++ [Asm.lbu rd base off] ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + 1) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre)) :
    let addr := st.getReg base + sextImm12 off
    let st' := stepReg st rd ((loadBytes st.mem addr 1).zeroExtend 64) (st.pc + 4#64)
    RV64.run env.rom 1 st = .cont st' ∧
    st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)) ∧
    st'.getReg rd = (st.mem addr).zeroExtend 64 ∧
    (∀ r, r ≠ rd → st'.getReg r = st.getReg r) ∧
    st'.mem = st.mem := by
  intro addr st'
  have hs := step_item_instr_lm lkm env.hrom pre post (.load .lbu rd base off) hlink (by omega) st hpc
  refine ⟨run_one_cont _ _ st' (by rw [hs]; simp only [execInstr]; rfl),
    pc_add_4_ofNat st.pc hpc, by rw [getReg_stepReg_eq st rd hrd _ _, loadBytes_one],
    fun r hr => getReg_stepReg_ne st rd r hr _ _,
    by dsimp only [st', stepReg, RV64.State.setReg]; split <;> rfl⟩

theorem step_sw_off_r {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (base rs : Reg) (off : BitVec 12)
    (hlink : lkm.linkSpec (pre ++ [Asm.raw (.store .sw base rs off)] ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + 1) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hal : isAligned (st.getReg base + sextImm12 off) 4 = true) :
    let addr := st.getReg base + sextImm12 off
    let st' := { st with pc := st.pc + 4#64, mem := RV64.storeBytes st.mem addr 4 ((st.getReg rs).extractLsb' 0 32) }
    RV64.run env.rom 1 st = .cont st' ∧
    st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)) ∧
    (∀ r, st'.getReg r = st.getReg r) := by
  intro addr st'
  have hs := step_item_instr_lm lkm env.hrom pre post (.store .sw base rs off) hlink (by omega) st hpc
  exact ⟨run_one_cont _ _ st' (by rw [hs]; simp only [execInstr, hal]; rfl),
    pc_add_4_ofNat st.pc hpc, fun _ => rfl⟩

/-- Direct-register operand semantics (`exprReg? fl.alloc e = some r`). -/
theorem reg_exprReg_sim {tab : Tab} {L : ProgLayout tab} {fl : FrameLayout}
    (hfl : FrameLayoutOk fl) {lm : _root_.L.Mem} {loc : _root_.L.Locals} {sp : BitVec 64}
    {st : State} (hf : ProgFrameOkR L fl sp st loc)
    {e : Expr} {r : Reg} (heOk : exprOkB tab fl.nlocals e = true)
    (hr : exprReg? fl.alloc e = some r) :
    (r = AbiReg.zero ∨ r ∈ allowedRegs true) ∧
    (∀ q ∈ scratchRegs, r ≠ q) ∧
    ∃ v, _root_.L.evalE e ⟨lm, loc⟩ = .ok (v, ⟨lm, loc⟩) ∧ st.getReg r = v.toBitVec := by
  cases e with
  | const w =>
    simp only [exprReg?] at hr
    split at hr
    · next hw =>
      cases hr
      have hw0 : w = 0 := beq_iff_eq.mp hw
      subst hw0
      refine ⟨Or.inl rfl, fun q hq => ?_, 0, rfl, rfl⟩
      simp only [scratchRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · cases hr
  | var x =>
    simp only [exprReg?] at hr
    simp only [exprOkB, decide_eq_true_eq] at heOk
    have hmem := (regAllocValid_lookup hfl.valid hr).2.1
    have hfx := hf x heOk
    rw [hr] at hfx
    refine ⟨Or.inr hmem, fun q hq => allowedRegs_disj_reserved true hmem (scratchRegs_sub_reserved hq),
      loc x, rfl, hfx⟩
  | _ => cases hr

/-- Pure non-trapping leaf expression directly emitted into scratch register `rd` using `tmp`. -/
theorem reg_emitSimpleExprR_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (_hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (pre post : List AsmItem) (rd tmp : Reg)
    (hrd0 : rd ≠ 0#5) (htmp0 : tmp ≠ 0#5) (htmpSp : tmp ≠ AbiReg.sp) (htmpGp : tmp ≠ AbiReg.gp)
    (htmpT5 : fl.useT5Gp = true → tmp ≠ AbiReg.t5)
    (e : Expr) (ce : List AsmItem)
    (hsimp : emitSimpleExprR env.tab fl rd tmp e = some ce)
    (heOk : exprOkB env.tab fl.nlocals e = true)
    (hVf : ExprVarsInFrame fl e)
    (hlink : lkm.linkSpec (pre ++ ce ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize ce) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : fl.useT5Gp = true → st.getReg AbiReg.t5 = L.T + 2047#64)
    (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    ∃ v k st', _root_.L.evalE e ⟨lm, loc⟩ = .ok (v, ⟨lm, loc⟩) ∧
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize ce)) ∧
      st'.getReg rd = v.toBitVec ∧
      (∀ r, r ≠ rd → r ≠ tmp → st'.getReg r = st.getReg r) ∧
      st'.mem = st.mem := by
  cases e with
  | const w =>
    simp only [emitSimpleExprR, Option.some.injEq] at hsimp; subst hsimp
    obtain ⟨st', hrun, hoth, hrd, hmem, hpc'⟩ :=
      li_correct_lm lkm env.hrom pre post rd hrd0 (BitVec.ofNat 64 w.toNat) hlink h64 st hpc
    exact ⟨w, lkm.totalSize (li rd (BitVec.ofNat 64 w.toNat)), st', rfl, hrun, hpc',
      by rw [hrd, show BitVec.ofNat 64 w.toNat = w.toBitVec from by
        rw [← UInt64.toBitVec_ofNat' w.toNat, UInt64.ofNat_toNat]],
      fun r hr _ => hoth r hr, hmem⟩
  | var x =>
    simp only [exprOkB, decide_eq_true_eq] at heOk
    simp only [emitSimpleExprR] at hsimp
    have hfx := hframeOk x heOk
    cases hl : fl.alloc.lookup x with
    | some rx =>
      rw [hl] at hsimp hfx
      simp only [Option.some.injEq] at hsimp; subst hsimp
      by_cases heq : rd = rx
      · subst heq; simp only [beq_self_eq_true, ↓reduceIte] at hlink h64 ⊢
        exact ⟨loc x, 0, st, rfl, rfl, by simpa using hpc, hfx, fun _ _ _ => rfl, rfl⟩
      · simp only [beq_false_of_ne heq, Bool.false_eq_true, ↓reduceIte] at hlink h64 ⊢
        have htw1 : lkm.totalSize [Asm.mv rd rx] = 1 := by simp [Asm.mv, lkm.itemSize_instr]
        rw [htw1] at h64 ⊢
        have hs := step_item_instr_lm lkm env.hrom pre post (.aluImm .addi rd rx 0#12)
          (by simpa [Asm.mv, Asm.addi] using hlink) (by omega) st hpc
        exact ⟨loc x, 1, stepReg st rd (loc x).toBitVec (st.pc + 4#64), rfl,
          run_one_cont _ _ _ (by rw [hs]; simp only [execInstr, evalAluImm, hfx,
            show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero]; rfl),
          pc_add_4_ofNat st.pc hpc, getReg_stepReg_eq _ _ hrd0 _ _,
          fun r hr _ => getReg_stepReg_ne _ _ r hr _ _, mem_stepReg _ _ _ _⟩
    | none =>
      rw [hl] at hsimp hfx
      simp only [Option.some.injEq] at hsimp; subst hsimp
      have hal : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (fl.varSlotOff x)) 8 = true := by
        rw [hsp, varSlotOff_ofInt]; exact isAligned8_add_mul8 sp hspAlign _
      obtain ⟨st', hrun, hoth, hrd, hmem, hpc'⟩ :=
        loadMemOff_ld_correct_lm lkm env.hrom pre post rd AbiReg.sp tmp
          hrd0 htmp0 htmpSp.symm (fl.varSlotOff x) hlink h64 st hpc hal
      exact ⟨loc x, lkm.totalSize (loadMemOff .ld rd AbiReg.sp tmp (fl.varSlotOff x)), st',
        rfl, hrun, hpc', by rw [hrd, hsp]; exact hfx (hVf x (by simp [exprUsesVar]) hl), hoth, hmem⟩
  | len8 a =>
    simp only [exprOkB] at heOk
    simp only [emitSimpleExprR, Option.some.injEq] at hsimp; subst hsimp
    have halign : isAligned (L.T + BitVec.ofInt 64 (env.tab.len8 a)) 8 = true := by
      rw [Tab.len8, Tab.dlen]
      rw [show (16 : Int) + 8 * ((env.tab.nb + env.tab.nw : Nat) : Int) + 8 * (env.tab.pos8 a : Int) =
          ((8 * (2 + env.tab.nb + env.tab.nw + env.tab.pos8 a) : Nat) : Int) from by omega, BitVec.ofInt_natCast]
      exact isAligned8_add_mul8 L.T L.hTAlign _
    obtain ⟨st', hrun, hoth, hrd, hmem, hpc'⟩ :=
      loadMemOffGp_ld_correct_lm lkm env.hrom pre post fl.useT5Gp rd tmp
        hrd0 htmp0 htmpGp htmpT5 (env.tab.len8 a) L.T hlink h64 st hpc hgp ht5 halign
    have haRel := hmemRel.1 a heOk
    refine ⟨UInt64.ofNat (lm.arr8 a).size,
      lkm.totalSize (loadMemOffGp fl.useT5Gp .ld rd tmp (env.tab.len8 a)), st',
      by simp [_root_.L.evalE, _root_.L.Mem.len8, get, getThe, MonadStateOf.get, StateT.get, Bind.bind,
        StateT.bind, Pure.pure, StateT.pure, Except.pure, Except.bind],
      hrun, hpc', ?_, hoth, hmem⟩
    rw [hrd, haRel.2.2.1]; rfl
  | len64 a =>
    simp only [exprOkB] at heOk
    simp only [emitSimpleExprR, Option.some.injEq] at hsimp; subst hsimp
    have halign : isAligned (L.T + BitVec.ofInt 64 (env.tab.len64 (TieredArray.t0 a))) 8 = true := by
      rw [Tab.len64, Tab.dlen]
      rw [show (16 : Int) + 8 * ((env.tab.nb + env.tab.nw : Nat) : Int) +
          8 * (env.tab.pos64 (TieredArray.t0 a) : Int) =
          ((8 * (2 + env.tab.nb + env.tab.nw + env.tab.pos64 (TieredArray.t0 a)) : Nat) : Int) from by omega,
        BitVec.ofInt_natCast]
      exact isAligned8_add_mul8 L.T L.hTAlign _
    obtain ⟨st', hrun, hoth, hrd, hmem, hpc'⟩ :=
      loadMemOffGp_ld_correct_lm lkm env.hrom pre post fl.useT5Gp rd tmp
        hrd0 htmp0 htmpGp htmpT5 (env.tab.len64 (TieredArray.t0 a)) L.T hlink h64 st hpc hgp ht5 halign
    have hwRel := hmemRel.2.1 (TieredArray.t0 a) heOk
    refine ⟨UInt64.ofNat (lm.arr64 (TieredArray.t0 a)).size,
      lkm.totalSize (loadMemOffGp fl.useT5Gp .ld rd tmp (env.tab.len64 (TieredArray.t0 a))), st',
      by simp [_root_.L.evalE, _root_.L.Mem.len64, get, getThe, MonadStateOf.get, StateT.get, Bind.bind,
        StateT.bind, Pure.pure, StateT.pure, Except.pure, Except.bind],
      hrun, hpc', ?_, hoth, hmem⟩
    rw [hrd, hwRel.2.2.1]; rfl
  | glob g =>
    simp only [exprOkB, decide_eq_true_eq] at heOk
    simp only [emitSimpleExprR, Option.some.injEq] at hsimp; subst hsimp
    have halign : isAligned (L.T + BitVec.ofInt 64 (env.tab.globOff g)) 8 = true := by
      rw [Tab.globOff, Tab.globBase, Tab.resBase, Tab.romBase]
      rw [show (16 : Int) + 24 * ((env.tab.nb + env.tab.nw : Nat) : Int) +
          8 * (env.tab.romWords : Int) + 8 * (env.tab.nxres : Int) + 8 * (g.id : Int) =
          ((8 * (2 + 3 * (env.tab.nb + env.tab.nw) + env.tab.romWords + env.tab.nxres + g.id) : Nat) : Int) from by omega,
        BitVec.ofInt_natCast]
      exact isAligned8_add_mul8 L.T L.hTAlign _
    obtain ⟨st', hrun, hoth, hrd, hmem, hpc'⟩ :=
      loadMemOffGp_ld_correct_lm lkm env.hrom pre post fl.useT5Gp rd tmp
        hrd0 htmp0 htmpGp htmpT5 (env.tab.globOff g) L.T hlink h64 st hpc hgp ht5 halign
    refine ⟨lm.glob g,
      lkm.totalSize (loadMemOffGp fl.useT5Gp .ld rd tmp (env.tab.globOff g)), st',
      by simp [_root_.L.evalE, get, getThe, MonadStateOf.get, StateT.get, Bind.bind,
        StateT.bind, Pure.pure, StateT.pure, Except.pure, Except.bind],
      hrun, hpc', by rw [hrd, hmemRel.2.2.2 g heOk], hoth, hmem⟩
  | _ => simp [emitSimpleExprR] at hsimp


/-! ## 4. Expression Simulation (`reg_evalExpr_sim` for `compileETo`) -/

theorem PreservedFrameRegs.of_a0 {fl : FrameLayout} {P : Reg → Prop} {st st' : State}
    (h : PreservedFrameRegs fl (· = AbiReg.a0) st st') : PreservedFrameRegs fl P st st' :=
  ⟨h.abi, h.leafRa, h.t5Gp, fun r hr _ => h.regs r hr (allowedRegs_ne_a0 hr)⟩

theorem PreservedFrameRegs.getReg_of_exprReg {fl : FrameLayout} {st st' : State}
    (h : PreservedFrameRegs fl (· = AbiReg.a0) st st') {r : Reg}
    (hr : r = AbiReg.zero ∨ r ∈ allowedRegs true) : st'.getReg r = st.getReg r := by
  rcases hr with rfl | hmem
  · rfl
  · exact h.regs r (allowedRegs_sub_true hmem) (allowedRegs_ne_a0 hmem)

theorem exprReg_ne_scratch {r : Reg}
    (hr : r = AbiReg.zero ∨ r ∈ allowedRegs true) {q : Reg} (hq : q ∈ scratchRegs) : r ≠ q := by
  rcases hr with rfl | hmem
  · simp only [scratchRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact allowedRegs_disj_reserved true hmem (scratchRegs_sub_reserved hq)

theorem idxReg_ne_s1 {r : Reg}
    (hr : r = AbiReg.zero ∨ r = AbiReg.a0 ∨ r ∈ allowedRegs true) :
    r ≠ AbiReg.s1 := by
  rcases hr with rfl | rfl | hmem
  · decide
  · decide
  · exact allowedRegs_ne_s1 hmem

theorem idxReg_ne_temp {r : Reg}
    (hr : r = AbiReg.zero ∨ r = AbiReg.a0 ∨ r ∈ allowedRegs true)
    {q : Reg} (hq : q ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3, AbiReg.t4, AbiReg.t5, AbiReg.t6]) :
    r ≠ q := by
  rcases hr with rfl | rfl | hmem
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · apply allowedRegs_disj_reserved true hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem ValidTargetReg.ne_temp {fl : FrameLayout} {rd : Reg} (hrd : ValidTargetReg fl rd)
    {q : Reg} (hq : q ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3, AbiReg.t4, AbiReg.t5, AbiReg.t6]) :
    rd ≠ q := by
  rcases hrd with rfl | hmem
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · apply allowedRegs_disj_reserved true hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem isSimpleExpr_of_exprReg {alloc : RegAlloc} {e : Expr} {r : Reg}
    (h : exprReg? alloc e = some r) : isSimpleExpr e = true := by
  cases e <;> simp [exprReg?, isSimpleExpr] at h ⊢

theorem isSimpleExpr_of_constVal {e : Expr} {w : _root_.L.Word}
    (h : e.constVal? = some w) : isSimpleExpr e = true := by
  cases e <;> simp [Expr.constVal?, isSimpleExpr] at h ⊢

theorem isSimpleExpr_false_of_emitSimple_none {tab : Tab} {fl : FrameLayout} {rd tmp : Reg} {e : Expr}
    (h : emitSimpleExprR tab fl rd tmp e = none) : isSimpleExpr e = false := by
  cases e with
  | var x => simp only [emitSimpleExprR] at h; cases hlk : fl.alloc.lookup x <;> rw [hlk] at h <;> simp at h
  | _ => simp [emitSimpleExprR, isSimpleExpr] at h ⊢

theorem usedTempsExpr_bin_left (op : BinOp) (a b : Expr) :
    usedTempsExpr a ≤ usedTempsExpr (.bin op a b) := by
  dsimp only [usedTempsExpr]
  cases hb : isSimpleExpr b
  · cases ha : isSimpleExpr a
    · cases hnt : exprNoT4 b
      · exact Nat.le_max_left _ _
      · exact Nat.le_refl _
    · rw [usedTempsExpr_of_isSimple ha]; exact Nat.zero_le _
  · exact Nat.le_refl _

theorem usedTempsExpr_bin_right (op : BinOp) (a b : Expr) :
    usedTempsExpr b ≤ usedTempsExpr (.bin op a b) := by
  dsimp only [usedTempsExpr]
  cases hb : isSimpleExpr b
  · cases ha : isSimpleExpr a
    · cases hnt : exprNoT4 b
      · exact Nat.le_trans (Nat.le_add_left _ 1) (Nat.le_max_right _ _)
      · rw [usedTempsExpr_of_exprNoT4 hnt]; exact Nat.zero_le _
    · exact Nat.le_refl _
  · rw [usedTempsExpr_of_isSimple hb]; exact Nat.zero_le _

theorem usedTempsExpr_cmpw_left (c : Cmp) (a b : Expr) :
    usedTempsExpr a ≤ usedTempsExpr (.cmpw c a b) := by
  dsimp only [usedTempsExpr]
  cases hb : isSimpleExpr b
  · cases ha : isSimpleExpr a
    · cases hnt : exprNoT4 b
      · exact Nat.le_max_left _ _
      · exact Nat.le_refl _
    · rw [usedTempsExpr_of_isSimple ha]; exact Nat.zero_le _
  · exact Nat.le_refl _

theorem usedTempsExpr_cmpw_right (c : Cmp) (a b : Expr) :
    usedTempsExpr b ≤ usedTempsExpr (.cmpw c a b) := by
  dsimp only [usedTempsExpr]
  cases hb : isSimpleExpr b
  · cases ha : isSimpleExpr a
    · cases hnt : exprNoT4 b
      · exact Nat.le_trans (Nat.le_add_left _ 1) (Nat.le_max_right _ _)
      · rw [usedTempsExpr_of_exprNoT4 hnt]; exact Nat.zero_le _
    · exact Nat.le_refl _
  · rw [usedTempsExpr_of_isSimple hb]; exact Nat.zero_le _

theorem isSimpleExpr_imp_exprNoT4 {e : Expr} (h : isSimpleExpr e = true) : exprNoT4 e = true := by
  cases e <;> simp [isSimpleExpr, exprNoT4] at h ⊢

theorem exprNoT4_bin_left {op : BinOp} {a b : Expr} (h : exprNoT4 (.bin op a b) = true)
    (hb : isSimpleExpr b = true) : exprNoT4 a = true := by
  simp only [exprNoT4, hb, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ha | ⟨ha, _⟩
  · exact ha
  · exact isSimpleExpr_imp_exprNoT4 ha

theorem exprNoT4_bin_right {op : BinOp} {a b : Expr} (h : exprNoT4 (.bin op a b) = true)
    (ha : isSimpleExpr a = true) : exprNoT4 b = true := by
  simp only [exprNoT4, ha, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨hb, _⟩ | hb
  · exact isSimpleExpr_imp_exprNoT4 hb
  · exact hb

theorem exprNoT4_cmpw_left {c : Cmp} {a b : Expr} (h : exprNoT4 (.cmpw c a b) = true)
    (hb : isSimpleExpr b = true) : exprNoT4 a = true := by
  simp only [exprNoT4, hb, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ha | ⟨ha, _⟩
  · exact ha
  · exact isSimpleExpr_imp_exprNoT4 ha

theorem exprNoT4_cmpw_right {c : Cmp} {a b : Expr} (h : exprNoT4 (.cmpw c a b) = true)
    (ha : isSimpleExpr a = true) : exprNoT4 b = true := by
  simp only [exprNoT4, ha, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨hb, _⟩ | hb
  · exact isSimpleExpr_imp_exprNoT4 hb
  · exact hb

/-- Single-instruction simulation for `emitBinOp op rd rL rR` into any valid target `rd`. -/
theorem step_emitBinOp_r {lkm : LinkModel} (env : CodeEnvGen lkm) (fl : FrameLayout)
    (pre post : List AsmItem) (op : BinOp) (rd rL rR : Reg) (hrd : ValidTargetReg fl rd)
    (va vb : _root_.L.Word)
    (hlink : lkm.linkSpec (pre ++ [emitBinOp op rd rL rR] ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + 1) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hL : st.getReg rL = va.toBitVec) (hR : st.getReg rR = vb.toBitVec) :
    ∃ st', RV64.run env.rom 1 st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize [emitBinOp op rd rL rR])) ∧
      st'.getReg rd = (op.eval va vb).toBitVec ∧
      PreservedFrameRegs fl (· = rd) st st' ∧
      st'.mem = st.mem ∧
      st'.getReg AbiReg.t4 = st.getReg AbiReg.t4 := by
  have step1 : ∀ (i : Instr) (w : RV64.Word)
      (hi : emitBinOp op rd rL rR = .instr i)
      (hexec : execInstr st i = .cont (stepReg st rd w (st.pc + 4#64)))
      (hw : w = (op.eval va vb).toBitVec),
      ∃ st', RV64.run env.rom 1 st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize [emitBinOp op rd rL rR])) ∧
        st'.getReg rd = (op.eval va vb).toBitVec ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        st'.mem = st.mem ∧
        st'.getReg AbiReg.t4 = st.getReg AbiReg.t4 := by
    intro i w hi hexec hw
    rw [hi] at hlink ⊢
    rw [lkm.totalSize_instr]
    have hs := step_item_instr_lm lkm env.hrom pre post i hlink (by omega) st hpc
    refine ⟨stepReg st rd w (st.pc + 4#64),
      run_one_cont _ _ _ (by rw [hs, hexec]),
      pc_add_4_ofNat st.pc hpc,
      by rw [getReg_stepReg_eq st rd hrd.ne_zero, hw],
      PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) (fun r hr => getReg_stepReg_ne st rd r hr _ _),
      mem_stepReg _ _ _ _,
      getReg_stepReg_ne st rd AbiReg.t4 (hrd.ne_temp (by decide)).symm _ _⟩
  cases op with
  | add =>
    exact step1 (.alu .add rd rL rR) (va.toBitVec + vb.toBitVec) rfl
      (by simp [execInstr, evalAlu, hL, hR, stepReg]) (by rw [uint64_binop_toBitVec .add])
  | sub =>
    exact step1 (.alu .sub rd rL rR) (va.toBitVec - vb.toBitVec) rfl
      (by simp [execInstr, evalAlu, hL, hR, stepReg]) (by rw [uint64_binop_toBitVec .sub])
  | and =>
    exact step1 (.alu .and rd rL rR) (va.toBitVec &&& vb.toBitVec) rfl
      (by simp [execInstr, evalAlu, hL, hR, stepReg]) (by rw [uint64_binop_toBitVec .and])
  | or =>
    exact step1 (.alu .or rd rL rR) (va.toBitVec ||| vb.toBitVec) rfl
      (by simp [execInstr, evalAlu, hL, hR, stepReg]) (by rw [uint64_binop_toBitVec .or])
  | xor =>
    exact step1 (.alu .xor rd rL rR) (va.toBitVec ^^^ vb.toBitVec) rfl
      (by simp [execInstr, evalAlu, hL, hR, stepReg]) (by rw [uint64_binop_toBitVec .xor])
  | shl =>
    exact step1 (.alu .sll rd rL rR) (va.toBitVec <<< (vb.toBitVec.toNat % 64)) rfl
      (by simp [execInstr, evalAlu, hL, hR, stepReg])
      (by rw [uint64_binop_toBitVec .shl, BitVec.extractLsb'_toNat, Nat.shiftRight_zero])
  | shr =>
    exact step1 (.alu .srl rd rL rR) (va.toBitVec >>> (vb.toBitVec.toNat % 64)) rfl
      (by simp [execInstr, evalAlu, hL, hR, stepReg])
      (by rw [uint64_binop_toBitVec .shr, BitVec.extractLsb'_toNat, Nat.shiftRight_zero])
  | mul =>
    exact step1 (.alu .mul rd rL rR) (va.toBitVec * vb.toBitVec) rfl
      (by simp [execInstr, evalAlu_mul_eq, hL, hR, stepReg]) (by rw [BinOp.eval, UInt64.toBitVec_mul])
  | mulhi =>
    exact step1 (.alu .mulhu rd rL rR) (BitVec.ofNat 64 ((va.toBitVec.toNat * vb.toBitVec.toNat) / 2 ^ 64)) rfl
      (by simp [execInstr, evalAlu_mulhu_eq, hL, hR, stepReg]) (prog_mul_lo_hi_toNat va vb).2

/-- 3-instruction tiered descriptor header offset computation: `t1 := T + (if u&&&1 == 0 then 0 else 8)`. -/
theorem step_tierHdr_r {lkm : LinkModel} (env : CodeEnvGen lkm) (fl : FrameLayout) {T : BitVec 64}
    (pre post : List AsmItem) (rsrc : Reg) (u : _root_.L.Word)
    (hlink : lkm.linkSpec (pre ++
        [Asm.andi AbiReg.t0 rsrc 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
         Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + 3) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = T) (hsrc : st.getReg rsrc = u.toBitVec) :
    let off := if (u &&& 1) == 0 then 0#64 else 8#64
    ∃ st', RV64.run env.rom 3 st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 3)) ∧
      st'.getReg AbiReg.t1 = T + off ∧
      st'.mem = st.mem ∧
      PreservedFrameRegs fl (· = AbiReg.a0) st st' ∧
      (∀ r, r ≠ AbiReg.t0 → r ≠ AbiReg.t1 → st'.getReg r = st.getReg r) := by
  intro off
  let i1 : Instr := .aluImm .andi AbiReg.t0 rsrc 1#12
  let i2 : Instr := .shImm .slli AbiReg.t0 AbiReg.t0 3#6
  let i3 : Instr := .alu .add AbiReg.t1 AbiReg.gp AbiReg.t0
  have hl1 : lkm.linkSpec (pre ++ [Asm.raw i1] ++ ([Asm.raw i2, Asm.raw i3] ++ post)) =
      .ok (env.code, env.labels) := by
    simpa [i1, i2, i3, Asm.andi, Asm.slli, Asm.add, Asm.raw, List.append_assoc] using hlink
  have hs1 := step_item_instr_lm lkm env.hrom pre ([Asm.raw i2, Asm.raw i3] ++ post) i1 hl1
    (by omega) st hpc
  let st1 := stepReg st AbiReg.t0 (u.toBitVec &&& sextImm12 1#12) (st.pc + 4#64)
  have ht0_1 : st1.getReg AbiReg.t0 = u.toBitVec &&& 1#64 := by
    change (stepReg st AbiReg.t0 _ _).getReg AbiReg.t0 = _
    rw [getReg_stepReg_eq _ _ (by decide), show sextImm12 1#12 = 1#64 from rfl]
  have htw1 : lkm.totalSize (pre ++ [Asm.raw i1]) = lkm.totalSize pre + 1 := by
    rw [lkm.totalSize_append, Asm.raw, lkm.totalSize_instr]
  have hpc1 : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ [Asm.raw i1])) := by
    change st.pc + 4#64 = _; rw [pc_add_4_ofNat st.pc hpc, htw1]
  have hl2 : lkm.linkSpec ((pre ++ [Asm.raw i1]) ++ [Asm.raw i2] ++ ([Asm.raw i3] ++ post)) =
      .ok (env.code, env.labels) := by
    simpa [i1, i2, i3, Asm.andi, Asm.slli, Asm.add, Asm.raw, List.append_assoc] using hlink
  have hs2 := step_item_instr_lm lkm env.hrom (pre ++ [Asm.raw i1]) ([Asm.raw i3] ++ post) i2 hl2
    (by rw [htw1]; omega) st1 hpc1
  let st2 := stepReg st1 AbiReg.t0 (st1.getReg AbiReg.t0 <<< 3) (st1.pc + 4#64)
  have ht0_2 : st2.getReg AbiReg.t0 = off := by
    change (stepReg st1 AbiReg.t0 _ _).getReg AbiReg.t0 = _
    rw [getReg_stepReg_eq _ _ (by decide), ht0_1]
    by_cases h0 : u &&& 1 = 0
    · simp only [off, beq_iff_eq, h0, ↓reduceIte]
      have hbit := (tierA_bit0 0 u).1 h0 |>.2
      have hz : u.toBitVec &&& 1#64 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hbit)
      rw [hz]; rfl
    · simp only [off, beq_iff_eq, h0, ↓reduceIte]
      have hbit := (tierA_bit0 0 u).2 h0 |>.2
      have ho : u.toBitVec &&& 1#64 = 1#64 := BitVec.eq_of_toNat_eq (by simpa using hbit)
      rw [ho]; rfl
  have htw2 : lkm.totalSize (pre ++ [Asm.raw i1] ++ [Asm.raw i2]) = lkm.totalSize pre + 2 := by
    rw [lkm.totalSize_append, htw1, Asm.raw, lkm.totalSize_instr]
  have hpc2 : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ [Asm.raw i1] ++ [Asm.raw i2])) := by
    change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1, htw2, htw1]
  have hl3 : lkm.linkSpec ((pre ++ [Asm.raw i1] ++ [Asm.raw i2]) ++ [Asm.raw i3] ++ post) =
      .ok (env.code, env.labels) := by
    simpa [i1, i2, i3, Asm.andi, Asm.slli, Asm.add, Asm.raw, List.append_assoc] using hlink
  have hs3 := step_item_instr_lm lkm env.hrom (pre ++ [Asm.raw i1] ++ [Asm.raw i2]) post i3 hl3
    (by rw [htw2]; omega) st2 hpc2
  let st3 := stepReg st2 AbiReg.t1 (st2.getReg AbiReg.gp + st2.getReg AbiReg.t0) (st2.pc + 4#64)
  have hgp2 : st2.getReg AbiReg.gp = T := by
    change (stepReg st1 AbiReg.t0 _ _).getReg AbiReg.gp = T
    rw [getReg_stepReg_ne _ _ _ (by decide), getReg_stepReg_ne _ _ _ (by decide), hgp]
  have hoth : ∀ r, r ≠ AbiReg.t0 → r ≠ AbiReg.t1 → st3.getReg r = st.getReg r := fun r hr0 hr1 => by
    change (stepReg st2 AbiReg.t1 _ _).getReg r = st.getReg r
    rw [getReg_stepReg_ne st2 AbiReg.t1 r hr1, getReg_stepReg_ne st1 AbiReg.t0 r hr0,
        getReg_stepReg_ne st AbiReg.t0 r hr0]
  refine ⟨st3, ?_, ?_, ?_, rfl,
    PreservedFrameRegs.of_scratch2 AbiReg.t0 AbiReg.t1 (by decide) (by decide) hoth, hoth⟩
  · rw [show (3 : Nat) = 1 + (1 + 1) from rfl]
    rw [run_add, run_one_cont _ _ st1 (by rw [hs1]; simp only [execInstr, evalAluImm, hsrc, i1]; rfl)]
    dsimp only
    rw [run_add, run_one_cont _ _ st2 (by rw [hs2]; simp only [execInstr, i2]; rfl)]
    dsimp only
    exact run_one_cont _ _ st3 (by rw [hs3]; simp only [execInstr, evalAlu, i3]; rfl)
  · change st2.pc + 4#64 = _; rw [pc_add_4_ofNat st2.pc hpc2, htw2]
  · change (stepReg st2 AbiReg.t1 _ _).getReg AbiReg.t1 = T + off
    rw [getReg_stepReg_eq _ _ (by decide), hgp2, ht0_2]

private theorem le64_byte_eq_r (b : Array UInt8) (idx : Nat) (hib : idx + 8 ≤ b.size) :
    let v : Nat → Nat := fun k => if hk : idx + k < b.size then b[idx + k].toNat else 0
    (le64 b idx).toBitVec =
      ((((((((0#64 <<< 8 ||| BitVec.ofNat 64 (v 7)) <<< 8 ||| BitVec.ofNat 64 (v 6))
        <<< 8 ||| BitVec.ofNat 64 (v 5)) <<< 8 ||| BitVec.ofNat 64 (v 4))
        <<< 8 ||| BitVec.ofNat 64 (v 3)) <<< 8 ||| BitVec.ofNat 64 (v 2))
        <<< 8 ||| BitVec.ofNat 64 (v 1)) <<< 8 ||| BitVec.ofNat 64 (v 0)) := by
  intro v
  have hlt : ∀ k, k < 8 → v k < 256 := fun k hk => by
    have hik : idx + k < b.size := by omega
    simp only [v, hik, ↓reduceDIte]; exact UInt8.toNat_lt (b[idx + k])
  have hstep : ∀ (acc : BitVec 64) (d : Nat), d < 256 →
      (acc <<< 8 ||| BitVec.ofNat 64 d).toNat = (acc.toNat * 256 + d) % 2 ^ 64 := by
    intro acc d hd
    have hlt64 : d < 2 ^ 64 := by omega
    rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64,
        Nat.shiftLeft_eq]
    have hdiv : acc.toNat * 256 % 2 ^ 64 = (acc.toNat % 2 ^ 56) * 256 := by
      have hp : (2 ^ 64 : Nat) = 2 ^ 56 * 256 := by decide
      rw [hp, Nat.mul_mod_mul_right]
    have hbound : acc.toNat * 256 % 2 ^ 64 + d < 2 ^ 64 := by
      rw [hdiv]; have := Nat.mod_lt acc.toNat (by decide : 0 < 2 ^ 56); omega
    have hmod_or : (acc.toNat * 256 % 2 ^ 64) ||| d = (acc.toNat * 256 % 2 ^ 64) + d := by
      rw [hdiv, ← Nat.shiftLeft_eq _ 8, ← Nat.shiftLeft_add_eq_or_of_lt hd, Nat.shiftLeft_eq]
    rw [hmod_or, ← Nat.mod_eq_of_lt hbound, Nat.mod_add_mod]
  apply BitVec.eq_of_toNat_eq
  rw [hstep _ _ (hlt 0 (by decide)), hstep _ _ (hlt 1 (by decide)), hstep _ _ (hlt 2 (by decide)),
      hstep _ _ (hlt 3 (by decide)), hstep _ _ (hlt 4 (by decide)), hstep _ _ (hlt 5 (by decide)),
      hstep _ _ (hlt 6 (by decide)), hstep _ _ (hlt 7 (by decide))]
  have hzero : (0#64 : BitVec 64).toNat = 0 := rfl
  rw [hzero, Nat.zero_mul, Nat.zero_add]
  have hf : ∀ (a b : Nat), (a % 2 ^ 64 * 256 + b) % 2 ^ 64 = (a * 256 + b) % 2 ^ 64 := by
    intro a b; rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
  rw [Nat.mod_eq_of_lt (show v 7 < 2 ^ 64 from Nat.lt_trans (hlt 7 (by decide)) (by decide)),
      hf _ (v 5), hf _ (v 4), hf _ (v 3), hf _ (v 2), hf _ (v 1), hf _ (v 0)]
  dsimp only [le64]
  rw [UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
  simp only [List.range, List.range.loop, List.map, List.foldr]
  have hb0 : idx + 0 < b.size := by omega
  have hb1 : idx + 1 < b.size := by omega
  have hb2 : idx + 2 < b.size := by omega
  have hb3 : idx + 3 < b.size := by omega
  have hb4 : idx + 4 < b.size := by omega
  have hb5 : idx + 5 < b.size := by omega
  have hb6 : idx + 6 < b.size := by omega
  have hb7 : idx + 7 < b.size := by omega
  simp only [v, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, ↓reduceDIte,
    getElem!_pos b (idx + 0) hb0, getElem!_pos b (idx + 1) hb1,
    getElem!_pos b (idx + 2) hb2, getElem!_pos b (idx + 3) hb3,
    getElem!_pos b (idx + 4) hb4, getElem!_pos b (idx + 5) hb5,
    getElem!_pos b (idx + 6) hb6, getElem!_pos b (idx + 7) hb7]
  have hlt_all :
      (((((((b[idx + 7].toNat * 256 + b[idx + 6].toNat) * 256 + b[idx + 5].toNat) * 256 +
        b[idx + 4].toNat) * 256 + b[idx + 3].toNat) * 256 + b[idx + 2].toNat) * 256 +
        b[idx + 1].toNat) * 256 + b[idx + 0].toNat) < 2 ^ 64 := by
    have x0 := UInt8.toNat_lt (b[idx + 0]); have x1 := UInt8.toNat_lt (b[idx + 1])
    have x2 := UInt8.toNat_lt (b[idx + 2]); have x3 := UInt8.toNat_lt (b[idx + 3])
    have x4 := UInt8.toNat_lt (b[idx + 4]); have x5 := UInt8.toNat_lt (b[idx + 5])
    have x6 := UInt8.toNat_lt (b[idx + 6]); have x7 := UInt8.toNat_lt (b[idx + 7])
    omega
  rw [Nat.mod_eq_of_lt hlt_all]; omega

private theorem sextImm12_nat_lt8_r (k : Nat) (hk : k < 8) :
    sextImm12 (BitVec.ofInt 12 (k : Int)) = BitVec.ofNat 64 k := by
  have hk12 : BitVec.ofInt 12 (k : Int) = BitVec.ofNat 12 k := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    have hm : (k : Int) % (2 ^ 12 : Nat) = (k : Int) := Int.emod_eq_of_lt (by omega) (by omega)
    rw [← Int.natCast_emod, Int.toNat_natCast]
  rw [hk12]; exact sextImm12_of_lt2048_nat k (by omega)

/-- 22-instruction unaligned little-endian 64-bit load directly into arbitrary target `rd`. -/
theorem le64_8bytes_sim_r {lkm : LinkModel} (env : CodeEnvGen lkm) (fl : FrameLayout)
    (pre post : List AsmItem) (rd : Reg) (hrd : ValidTargetReg fl rd)
    (bytes : Array UInt8) (idx : Nat) (hib : idx + 8 ≤ bytes.size)
    (hlink : lkm.linkSpec (pre ++ ([Asm.lbu rd AbiReg.t1 7#12] ++
        ([6, 5, 4, 3, 2, 1, 0].flatMap fun k =>
          [Asm.lbu AbiReg.t2 AbiReg.t1 (BitVec.ofInt 12 (k : Int)),
           Asm.slli rd rd 8#6,
           Asm.or rd rd AbiReg.t2])) ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + 22) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hmem : ∀ j (hj : j < 8),
      st.mem (st.getReg AbiReg.t1 + BitVec.ofNat 64 j) = (bytes[idx + j]'(by omega)).toBitVec) :
    ∃ st', RV64.run env.rom 22 st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 22)) ∧
      st'.getReg rd = (le64 bytes idx).toBitVec ∧
      st'.mem = st.mem ∧
      PreservedFrameRegs fl (· = rd) st st' ∧
      st'.getReg AbiReg.t4 = st.getReg AbiReg.t4 := by
  have hrd0 : rd ≠ AbiReg.zero := hrd.ne_zero
  have hrdT1 : rd ≠ AbiReg.t1 := hrd.ne_temp (by decide)
  have hrdT2 : rd ≠ AbiReg.t2 := hrd.ne_temp (by decide)
  have hrdT4 : rd ≠ AbiReg.t4 := hrd.ne_temp (by decide)
  let blk := fun (k : Nat) =>
    [Asm.lbu AbiReg.t2 AbiReg.t1 (BitVec.ofInt 12 (k : Int)),
     Asm.slli rd rd 8#6,
     Asm.or rd rd AbiReg.t2]
  have stepOne : ∀ (k : Nat) (hk : k < 8) (p1 p2 : List AsmItem) (s : State),
      lkm.linkSpec (p1 ++ blk k ++ p2) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize p1 + 3) < 2 ^ 64 →
      s.pc = BitVec.ofNat 64 (4 * lkm.totalSize p1) →
      s.getReg AbiReg.t1 = st.getReg AbiReg.t1 →
      s.mem = st.mem →
      ∃ s', RV64.run env.rom 3 s = .cont s' ∧
        s'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize p1 + 3)) ∧
        s'.getReg rd = ((s.getReg rd <<< 8) ||| BitVec.ofNat 64 (bytes[idx + k]'(by omega)).toNat) ∧
        s'.getReg AbiReg.t1 = st.getReg AbiReg.t1 ∧
        s'.mem = st.mem ∧
        PreservedFrameRegs fl (· = rd) s s' ∧
        s'.getReg AbiReg.t4 = s.getReg AbiReg.t4 := by
    intro k hk p1 p2 s hl hk64 hsp ht1 hsmem
    let off := BitVec.ofInt 12 (k : Int)
    have hl1 : lkm.linkSpec (p1 ++ [Asm.lbu AbiReg.t2 AbiReg.t1 off] ++
        ([Asm.slli rd rd 8#6, Asm.or rd rd AbiReg.t2] ++ p2)) = .ok (env.code, env.labels) := by
      simpa [blk, off, List.append_assoc] using hl
    obtain ⟨hr1, hpc1, ht2_1, hoth1, hm1⟩ :=
      step_lbu_off_r env p1 ([Asm.slli rd rd 8#6, Asm.or rd rd AbiReg.t2] ++ p2)
        AbiReg.t2 AbiReg.t1 off (by decide) hl1 (by omega) s hsp
    let s1 := stepReg s AbiReg.t2 ((loadBytes s.mem (s.getReg AbiReg.t1 + sextImm12 off) 1).zeroExtend 64) (s.pc + 4#64)
    have htw1 : lkm.totalSize (p1 ++ [Asm.lbu AbiReg.t2 AbiReg.t1 off]) = lkm.totalSize p1 + 1 := by
      rw [lkm.totalSize_append, Asm.lbu, lkm.totalSize_instr]
    have hpc1' : s1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p1 ++ [Asm.lbu AbiReg.t2 AbiReg.t1 off])) := by
      rw [htw1]; exact hpc1
    have hl2 : lkm.linkSpec ((p1 ++ [Asm.lbu AbiReg.t2 AbiReg.t1 off]) ++
        [Asm.raw (.shImm .slli rd rd 8#6)] ++ ([Asm.or rd rd AbiReg.t2] ++ p2)) =
        .ok (env.code, env.labels) := by
      simpa [blk, off, Asm.slli, Asm.raw, List.append_assoc] using hl
    have hs2 := step_item_instr_lm lkm env.hrom (p1 ++ [Asm.lbu AbiReg.t2 AbiReg.t1 off])
      ([Asm.or rd rd AbiReg.t2] ++ p2) (.shImm .slli rd rd 8#6) hl2 (by rw [htw1]; omega) s1 hpc1'
    let s2 := stepReg s1 rd (s1.getReg rd <<< 8) (s1.pc + 4#64)
    have htw2 : lkm.totalSize (p1 ++ [Asm.lbu AbiReg.t2 AbiReg.t1 off] ++ [Asm.slli rd rd 8#6]) = lkm.totalSize p1 + 2 := by
      rw [lkm.totalSize_append, htw1, Asm.slli, lkm.totalSize_instr]
    have hpc2 : s2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p1 ++ [Asm.lbu AbiReg.t2 AbiReg.t1 off] ++ [Asm.slli rd rd 8#6])) := by
      change s1.pc + 4#64 = _; rw [pc_add_4_ofNat s1.pc hpc1', htw2, htw1]
    have hl3 : lkm.linkSpec ((p1 ++ [Asm.lbu AbiReg.t2 AbiReg.t1 off] ++ [Asm.slli rd rd 8#6]) ++
        [Asm.raw (.alu .or rd rd AbiReg.t2)] ++ p2) = .ok (env.code, env.labels) := by
      simpa [blk, off, Asm.or, Asm.slli, Asm.raw, List.append_assoc] using hl
    have hs3 := step_item_instr_lm lkm env.hrom
      (p1 ++ [Asm.lbu AbiReg.t2 AbiReg.t1 off] ++ [Asm.slli rd rd 8#6]) p2
      (.alu .or rd rd AbiReg.t2) hl3 (by rw [htw2]; omega) s2 hpc2
    let s3 := stepReg s2 rd (s2.getReg rd ||| s2.getReg AbiReg.t2) (s2.pc + 4#64)
    have hrd1 : s1.getReg rd = s.getReg rd := hoth1 rd hrdT2
    have hrd2 : s2.getReg rd = s.getReg rd <<< 8 := by
      change (stepReg s1 rd _ _).getReg rd = _; rw [getReg_stepReg_eq _ _ hrd0, hrd1]
    have ht2_2 : s2.getReg AbiReg.t2 = (s.mem (s.getReg AbiReg.t1 + sextImm12 off)).zeroExtend 64 := by
      change (stepReg s1 rd _ _).getReg AbiReg.t2 = _; rw [getReg_stepReg_ne _ _ _ hrdT2.symm]; exact ht2_1
    have hbyte : (s.mem (s.getReg AbiReg.t1 + sextImm12 off)).zeroExtend 64 =
        BitVec.ofNat 64 (bytes[idx + k]'(by omega)).toNat := by
      rw [hsmem, ht1, sextImm12_nat_lt8_r k hk, hmem k hk]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.zeroExtend, BitVec.toNat_setWidth, UInt8.toNat_toBitVec, BitVec.toNat_ofNat]
    have hothAll : ∀ r, r ≠ rd → r ≠ AbiReg.t2 → s3.getReg r = s.getReg r := fun r hrr hrt2 => by
      change (stepReg s2 rd _ _).getReg r = s.getReg r
      rw [getReg_stepReg_ne s2 rd r hrr, getReg_stepReg_ne s1 rd r hrr, hoth1 r hrt2]
    refine ⟨s3, ?_, ?_, ?_, (hothAll AbiReg.t1 hrdT1.symm (by decide)).trans ht1,
      (mem_stepReg _ _ _ _).trans ((mem_stepReg _ _ _ _).trans (hm1.trans hsmem)),
      PreservedFrameRegs.of_target_scratch rd AbiReg.t2 hrd (fun _ => rfl) (by decide) hothAll,
      hothAll AbiReg.t4 hrdT4.symm (by decide)⟩
    · rw [show (3 : Nat) = 1 + (1 + 1) from rfl, run_add, hr1]; dsimp only
      rw [run_add, run_one_cont _ _ s2 (by rw [hs2]; simp only [execInstr]; rfl)]; dsimp only
      exact run_one_cont _ _ s3 (by rw [hs3]; simp only [execInstr, evalAlu]; rfl)
    · change s2.pc + 4#64 = _; rw [pc_add_4_ofNat s2.pc hpc2, htw2]
    · change (stepReg s2 rd _ _).getReg rd = _
      rw [getReg_stepReg_eq _ _ hrd0, hrd2, ht2_2, hbyte]
  let b7 := [Asm.lbu rd AbiReg.t1 7#12]
  have hflat : ([6, 5, 4, 3, 2, 1, 0].flatMap blk) =
      blk 6 ++ blk 5 ++ blk 4 ++ blk 3 ++ blk 2 ++ blk 1 ++ blk 0 := rfl
  change lkm.linkSpec (pre ++ (b7 ++ ([6, 5, 4, 3, 2, 1, 0].flatMap blk)) ++ post) = .ok (env.code, env.labels) at hlink
  rw [hflat] at hlink
  have hl7 : lkm.linkSpec (pre ++ [Asm.lbu rd AbiReg.t1 7#12] ++
      (blk 6 ++ blk 5 ++ blk 4 ++ blk 3 ++ blk 2 ++ blk 1 ++ blk 0 ++ post)) =
      .ok (env.code, env.labels) := by simpa only [b7, List.append_assoc] using hlink
  obtain ⟨hr7, hpc7, ha7_0, hoth7, hm7⟩ :=
    step_lbu_off_r env pre (blk 6 ++ blk 5 ++ blk 4 ++ blk 3 ++ blk 2 ++ blk 1 ++ blk 0 ++ post)
      rd AbiReg.t1 7#12 hrd0 hl7 (by omega) st hpc
  let s7 := stepReg st rd ((loadBytes st.mem (st.getReg AbiReg.t1 + sextImm12 7#12) 1).zeroExtend 64) (st.pc + 4#64)
  have ha7 : s7.getReg rd = ((0#64 <<< 8) ||| BitVec.ofNat 64 (bytes[idx + 7]'(by omega)).toNat) := by
    rw [ha7_0, show sextImm12 7#12 = BitVec.ofNat 64 7 from rfl,
        hmem 7 (by decide), show (0#64 : BitVec 64) <<< 8 = 0#64 from rfl, BitVec.zero_or]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.zeroExtend, BitVec.toNat_setWidth, UInt8.toNat_toBitVec, BitVec.toNat_ofNat]
  have ht7 : s7.getReg AbiReg.t1 = st.getReg AbiReg.t1 := hoth7 _ hrdT1.symm
  have ht4_7 : s7.getReg AbiReg.t4 = st.getReg AbiReg.t4 := hoth7 _ hrdT4.symm
  have hp7 : PreservedFrameRegs fl (· = rd) st s7 :=
    PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) hoth7
  have hblkSz : ∀ k, lkm.totalSize (blk k) = 3 := fun _ => by
    simp [blk, Asm.lbu, Asm.slli, Asm.or, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
  have tw7 : lkm.totalSize (pre ++ b7) = lkm.totalSize pre + 1 := by
    rw [lkm.totalSize_append]; simp only [b7, Asm.lbu, lkm.totalSize_instr]
  obtain ⟨s6, hr6, hpc6, ha6, ht6, hm6, hp6, ht4_6⟩ := stepOne 6 (by decide) (pre ++ b7) _ s7
    (by simpa only [List.append_assoc] using hlink) (by rw [tw7]; omega) (by rw [tw7]; exact hpc7) ht7 hm7
  have tw6 : lkm.totalSize (pre ++ b7 ++ blk 6) = lkm.totalSize pre + 4 := by rw [lkm.totalSize_append, tw7, hblkSz]
  obtain ⟨s5, hr5, hpc5, ha5, ht5, hm5, hp5, ht4_5⟩ := stepOne 5 (by decide) (pre ++ b7 ++ blk 6) _ s6
    (by simpa only [List.append_assoc] using hlink) (by rw [tw6]; omega) (by rw [hpc6, tw7, tw6]) ht6 hm6
  have tw5 : lkm.totalSize (pre ++ b7 ++ blk 6 ++ blk 5) = lkm.totalSize pre + 7 := by rw [lkm.totalSize_append, tw6, hblkSz]
  obtain ⟨s4, hr4, hpc4, ha4, ht4, hm4, hp4, ht4_4⟩ := stepOne 4 (by decide) (pre ++ b7 ++ blk 6 ++ blk 5) _ s5
    (by simpa only [List.append_assoc] using hlink) (by rw [tw5]; omega) (by rw [hpc5, tw6, tw5]) ht5 hm5
  have tw4 : lkm.totalSize (pre ++ b7 ++ blk 6 ++ blk 5 ++ blk 4) = lkm.totalSize pre + 10 := by rw [lkm.totalSize_append, tw5, hblkSz]
  obtain ⟨s3, hr3, hpc3, ha3, ht3, hm3, hp3, ht4_3⟩ := stepOne 3 (by decide) (pre ++ b7 ++ blk 6 ++ blk 5 ++ blk 4) _ s4
    (by simpa only [List.append_assoc] using hlink) (by rw [tw4]; omega) (by rw [hpc4, tw5, tw4]) ht4 hm4
  have tw3 : lkm.totalSize (pre ++ b7 ++ blk 6 ++ blk 5 ++ blk 4 ++ blk 3) = lkm.totalSize pre + 13 := by rw [lkm.totalSize_append, tw4, hblkSz]
  obtain ⟨s2, hr2, hpc2, ha2, ht2, hm2, hp2, ht4_2⟩ := stepOne 2 (by decide) (pre ++ b7 ++ blk 6 ++ blk 5 ++ blk 4 ++ blk 3) _ s3
    (by simpa only [List.append_assoc] using hlink) (by rw [tw3]; omega) (by rw [hpc3, tw4, tw3]) ht3 hm3
  have tw2 : lkm.totalSize (pre ++ b7 ++ blk 6 ++ blk 5 ++ blk 4 ++ blk 3 ++ blk 2) = lkm.totalSize pre + 16 := by rw [lkm.totalSize_append, tw3, hblkSz]
  obtain ⟨s1, hr1, hpc1, ha1, ht1, hm1, hp1, ht4_1⟩ := stepOne 1 (by decide) (pre ++ b7 ++ blk 6 ++ blk 5 ++ blk 4 ++ blk 3 ++ blk 2) _ s2
    (by simpa only [List.append_assoc] using hlink) (by rw [tw2]; omega) (by rw [hpc2, tw3, tw2]) ht2 hm2
  have tw1 : lkm.totalSize (pre ++ b7 ++ blk 6 ++ blk 5 ++ blk 4 ++ blk 3 ++ blk 2 ++ blk 1) = lkm.totalSize pre + 19 := by rw [lkm.totalSize_append, tw2, hblkSz]
  obtain ⟨s0, hr0, hpc0, ha0', _, hm0, hp0, ht4_0⟩ := stepOne 0 (by decide) (pre ++ b7 ++ blk 6 ++ blk 5 ++ blk 4 ++ blk 3 ++ blk 2 ++ blk 1) _ s1
    (by simpa only [List.append_assoc] using hlink) (by rw [tw1]; omega) (by rw [hpc1, tw2, tw1]) ht1 hm1
  refine ⟨s0, ?_, ?_, ?_, hm0, hp7.trans (hp6.trans (hp5.trans (hp4.trans (hp3.trans (hp2.trans (hp1.trans hp0)))))),
    ht4_0.trans (ht4_1.trans (ht4_2.trans (ht4_3.trans (ht4_4.trans (ht4_5.trans (ht4_6.trans ht4_7))))))⟩
  · rw [show (22 : Nat) = 1 + (3 + (3 + (3 + (3 + (3 + (3 + 3)))))) from rfl]
    rw [run_add, hr7]; dsimp only
    rw [run_add, hr6]; dsimp only
    rw [run_add, hr5]; dsimp only
    rw [run_add, hr4]; dsimp only
    rw [run_add, hr3]; dsimp only
    rw [run_add, hr2]; dsimp only
    rw [run_add, hr1]; dsimp only
    exact hr0
  · rw [hpc0, tw1]
  · rw [ha0', ha1, ha2, ha3, ha4, ha5, ha6, ha7, le64_byte_eq_r bytes idx hib]
    have hb0 : idx + 0 < bytes.size := by omega
    have hb1 : idx + 1 < bytes.size := by omega
    have hb2 : idx + 2 < bytes.size := by omega
    have hb3 : idx + 3 < bytes.size := by omega
    have hb4 : idx + 4 < bytes.size := by omega
    have hb5 : idx + 5 < bytes.size := by omega
    have hb6 : idx + 6 < bytes.size := by omega
    have hb7 : idx + 7 < bytes.size := by omega
    simp only [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, ↓reduceDIte]

/-- Shared helper for evaluating a single operand `i` into `(ci, ri)` via `exprReg?` or `compileETo ... a0`. -/
theorem reg_evalIdx_of_ih {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (i : Expr) (pre tail : List AsmItem) (tmp : Nat)
    (hiOk : exprOkB env.tab fl.nlocals i = true)
    (hTmp : tmp + usedTempsExpr i ≤ fl.usedTemps)
    (ihi : ∀ (pre post : List AsmItem) (tmp : Nat) (rd : Reg) (st : State),
      ValidTargetReg fl rd →
      tmp + usedTempsExpr i ≤ fl.usedTemps →
      lkm.linkSpec (pre ++ compileETo env.tab fl tmp rd i ++ post) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd i)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → T5GpOk L fl st → st.getReg AbiReg.sp = sp →
      ProgMemRel env.tab L st.mem lm → ProgFrameOkR L fl sp st loc →
      match _root_.L.evalE i ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd i))) ∧
          st'.getReg rd = v.toBitVec ∧
          PreservedFrameRegs fl (· = rd) st st' ∧
          MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem ∧
          (exprNoT4 i = true → st'.getReg AbiReg.t4 = st.getReg AbiReg.t4)
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedFrameRegs fl (· = rd) st st' ∧
          MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem)
    (hlink : let (ci, _) := match exprReg? fl.alloc i with
        | some r => ([], r) | none => (compileETo env.tab fl tmp AbiReg.a0 i, AbiReg.a0)
      lkm.linkSpec (pre ++ ci ++ tail) = .ok (env.code, env.labels))
    (h64 : let (ci, _) := match exprReg? fl.alloc i with
        | some r => ([], r) | none => (compileETo env.tab fl tmp AbiReg.a0 i, AbiReg.a0)
      4 * (lkm.totalSize pre + lkm.totalSize ci) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    let (ci, ri) := match exprReg? fl.alloc i with
      | some r => ([], r) | none => (compileETo env.tab fl tmp AbiReg.a0 i, AbiReg.a0)
    (ri = AbiReg.zero ∨ ri = AbiReg.a0 ∨ ri ∈ allowedRegs true) ∧
    match _root_.L.evalE i ⟨lm, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize ci)) ∧
        st'.getReg ri = v.toBitVec ∧
        PreservedFrameRegs fl (· = AbiReg.a0) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem ∧
        (exprNoT4 i = true → st'.getReg AbiReg.t4 = st.getReg AbiReg.t4)
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = AbiReg.a0) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
  cases hr : exprReg? fl.alloc i with
  | some r =>
    dsimp only
    obtain ⟨hmem, _, v, hv, hgr⟩ := reg_exprReg_sim hfl hframeOk hiOk hr
    refine ⟨by rcases hmem with h0 | hm; exact Or.inl h0; exact Or.inr (Or.inr hm), ?_⟩
    rw [hv]
    exact ⟨0, st, rfl, by rw [lkm.totalSize_nil, Nat.add_zero]; exact hpc, hgr,
      PreservedFrameRegs.refl _ _ _, MemEqOutside.refl _ _, fun _ => rfl⟩
  | none =>
    simp only [hr] at hlink h64 ⊢
    exact ⟨Or.inr (Or.inl trivial),
      ihi pre tail tmp AbiReg.a0 st (Or.inl rfl) hTmp hlink h64 hpc hgp ht5 hsp hmemRel hframeOk⟩

/-- Shared helper for evaluating `(e1, e2)` using one spill slot `tempSlotOff tmp`:
    puts `v1` in `t0` and `v2` in `a0`, preserving frame regs and `tempSpanR fl sp tmp`. -/
theorem reg_evalTwoSpill_of_ih {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (e1 e2 : Expr) (pre tail : List AsmItem) (tmp : Nat)
    (htmp_le : tmp + 1 ≤ fl.usedTemps)
    (htmp1 : tmp + usedTempsExpr e1 ≤ fl.usedTemps)
    (htmp2 : tmp + 1 + usedTempsExpr e2 ≤ fl.usedTemps)
    (ih1 : ∀ (pre post : List AsmItem) (tmp : Nat) (rd : Reg) (st : State),
      ValidTargetReg fl rd →
      tmp + usedTempsExpr e1 ≤ fl.usedTemps →
      lkm.linkSpec (pre ++ compileETo env.tab fl tmp rd e1 ++ post) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd e1)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → T5GpOk L fl st → st.getReg AbiReg.sp = sp →
      ProgMemRel env.tab L st.mem lm → ProgFrameOkR L fl sp st loc →
      match _root_.L.evalE e1 ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd e1))) ∧
          st'.getReg rd = v.toBitVec ∧
          PreservedFrameRegs fl (· = rd) st st' ∧
          MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedFrameRegs fl (· = rd) st st' ∧
          MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem)
    (ih2 : ∀ (pre post : List AsmItem) (tmp : Nat) (rd : Reg) (st : State),
      ValidTargetReg fl rd →
      tmp + usedTempsExpr e2 ≤ fl.usedTemps →
      lkm.linkSpec (pre ++ compileETo env.tab fl tmp rd e2 ++ post) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd e2)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → T5GpOk L fl st → st.getReg AbiReg.sp = sp →
      ProgMemRel env.tab L st.mem lm → ProgFrameOkR L fl sp st loc →
      match _root_.L.evalE e2 ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd e2))) ∧
          st'.getReg rd = v.toBitVec ∧
          PreservedFrameRegs fl (· = rd) st st' ∧
          MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedFrameRegs fl (· = rd) st st' ∧
          MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem)
    (hlink : lkm.linkSpec (pre ++
        (compileETo env.tab fl tmp AbiReg.a0 e1 ++
         storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp) ++
         compileETo env.tab fl (tmp + 1) AbiReg.a0 e2 ++
         loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff tmp)) ++ tail) =
        .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize
        (compileETo env.tab fl tmp AbiReg.a0 e1 ++
         storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp) ++
         compileETo env.tab fl (tmp + 1) AbiReg.a0 e2 ++
         loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff tmp))) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    let seq := compileETo env.tab fl tmp AbiReg.a0 e1 ++
               storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp) ++
               compileETo env.tab fl (tmp + 1) AbiReg.a0 e2 ++
               loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff tmp)
    match _root_.L.evalE e1 ⟨lm, loc⟩, _root_.L.evalE e2 ⟨lm, loc⟩ with
    | .ok (v1, _), .ok (v2, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize seq)) ∧
        st'.getReg AbiReg.t0 = v1.toBitVec ∧
        st'.getReg AbiReg.a0 = v2.toBitVec ∧
        PreservedFrameRegs fl (· = AbiReg.a0) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem
    | _, _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = AbiReg.a0) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
  let c1 := compileETo env.tab fl tmp AbiReg.a0 e1
  let cs := storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp)
  let c2 := compileETo env.tab fl (tmp + 1) AbiReg.a0 e2
  let cl := loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff tmp)
  have hf : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  have htw_all : lkm.totalSize (c1 ++ cs ++ c2 ++ cl) =
      lkm.totalSize c1 + lkm.totalSize cs + lkm.totalSize c2 + lkm.totalSize cl := by
    simp only [lkm.totalSize_append]
  have h64' : 4 * (lkm.totalSize pre + (lkm.totalSize c1 + lkm.totalSize cs + lkm.totalSize c2 + lkm.totalSize cl)) < 2 ^ 64 := by
    rw [← htw_all]; exact h64
  have h64_1 : 4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 e1)) < 2 ^ 64 := by
    dsimp only [c1] at h64'; omega
  have r1 := ih1 pre (cs ++ c2 ++ cl ++ tail) tmp AbiReg.a0 st (Or.inl rfl) htmp1
    (by simpa only [c1, cs, c2, cl, List.append_assoc] using hlink)
    h64_1 hpc hgp ht5 hsp hmemRel hframeOk
  rcases _root_.L.evalE_pure e1 ⟨lm, loc⟩ with ⟨v1, hv1⟩ | hv1
  · simp only [hv1] at r1
    obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := r1
    have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.abi.gp.trans hgp
    have hsp1 : st1.getReg AbiReg.sp = sp := hpres1.abi.sp.trans hsp
    have htw_p1 : lkm.totalSize (pre ++ c1) = lkm.totalSize pre + lkm.totalSize c1 := lkm.totalSize_append _ _
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ c1)) := by rw [htw_p1]; exact hpc1
    have halS : isAligned (st1.getReg AbiReg.sp + BitVec.ofInt 64 (fl.tempSlotOff tmp)) 8 = true := by
      rw [hsp1, tempSlotOff_ofInt]; exact isAligned8_add_mul8 sp hspAlign _
    obtain ⟨st2, hrunS, hothS, hmem2, hpc2⟩ :=
      storeMemOff_sd_correct_lm lkm env.hrom (pre ++ c1) (c2 ++ cl ++ tail) AbiReg.sp AbiReg.a0 AbiReg.t0
        (by decide) (by decide) (by decide) (fl.tempSlotOff tmp)
        (by simpa only [c1, cs, c2, cl, List.append_assoc] using hlink)
        (by rw [htw_p1]; dsimp only [cs] at h64'; omega) st1 hpc1' halS
    have hpresS : PreservedFrameRegs fl (· = AbiReg.a0) st1 st2 :=
      PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hothS
    have heqS : MemEqOutside (tempSpanR fl sp tmp) st1.mem st2.mem := by
      rw [hmem2, hsp1, tempSlotOff_ofInt]
      apply MemEqOutside.writeWord64
      intro k hk
      exact tempSlotSpanR_sub_tempSpanR fl sp hf (Nat.le_refl tmp) (by omega) _ ⟨k, hk, rfl⟩
    have heq02 : MemEqOutside (tempSpanR fl sp tmp) st.mem st2.mem := heq1.trans heqS
    have hmemRel2 := ProgMemRel.of_tempSpanR hlo hhi (by omega) heq02 hmemRel
    have hframeOk2 := ProgFrameOkR.of_preserved_temp hfl hf (by omega) (hpres1.trans hpresS) heq02 hframeOk
    have hslot2 : readWord64 st2.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff tmp)) = v1.toBitVec := by
      rw [hmem2, hsp1, ← ha0_1, readWord64_writeWord64_self]
    have htw_p2 : lkm.totalSize (pre ++ c1 ++ cs) = lkm.totalSize pre + lkm.totalSize c1 + lkm.totalSize cs := by
      rw [lkm.totalSize_append, htw_p1]
    have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ c1 ++ cs)) := by
      rw [htw_p2, ← htw_p1]; exact hpc2
    have r2 := ih2 (pre ++ c1 ++ cs) (cl ++ tail) (tmp + 1) AbiReg.a0 st2 (Or.inl rfl) htmp2
      (by simpa only [c1, cs, c2, cl, List.append_assoc] using hlink)
      (by rw [htw_p2]; dsimp only [c2] at h64'; omega) hpc2'
      (hpresS.abi.gp.trans hgp1) ((hpres1.trans hpresS).t5Gp |> fun h => fun hu => (h hu).trans (ht5 hu))
      (hpresS.abi.sp.trans hsp1) hmemRel2 hframeOk2
    rcases _root_.L.evalE_pure e2 ⟨lm, loc⟩ with ⟨v2, hv2⟩ | hv2
    · simp only [hv1, hv2] at r2 ⊢
      obtain ⟨k2, st3, hrun2, hpc3, ha0_3, hpres2, heq2⟩ := r2
      have hsp3 : st3.getReg AbiReg.sp = sp := hpres2.abi.sp.trans (hpresS.abi.sp.trans hsp1)
      have htw_p3 : lkm.totalSize (pre ++ c1 ++ cs ++ c2) =
          lkm.totalSize pre + lkm.totalSize c1 + lkm.totalSize cs + lkm.totalSize c2 := by
        rw [lkm.totalSize_append, htw_p2]
      have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ c1 ++ cs ++ c2)) := by
        rw [htw_p3, ← htw_p2]; exact hpc3
      have halL : isAligned (st3.getReg AbiReg.sp + BitVec.ofInt 64 (fl.tempSlotOff tmp)) 8 = true := by
        rw [hsp3, tempSlotOff_ofInt]; exact isAligned8_add_mul8 sp hspAlign _
      obtain ⟨st4, hrunL, hothL, ht0_4, hmem4, hpc4⟩ :=
        loadMemOff_ld_correct_lm lkm env.hrom (pre ++ c1 ++ cs ++ c2) tail
          AbiReg.t0 AbiReg.sp AbiReg.t1 (by decide) (by decide) (by decide) (fl.tempSlotOff tmp)
          (by simpa only [c1, cs, c2, cl, List.append_assoc] using hlink)
          (by rw [htw_p3]; dsimp only [cl] at h64'; omega) st3 hpc3' halL
      have hpresL : PreservedFrameRegs fl (· = AbiReg.a0) st3 st4 :=
        PreservedFrameRegs.of_scratch2 AbiReg.t0 AbiReg.t1 (by decide) (by decide) hothL
      have hslot3 : readWord64 st3.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff tmp)) = v1.toBitVec := by
        rw [← hslot2]
        apply MemEqOutside.readWord64_eq heq2
        intro k hk; rw [tempSlotOff_ofInt]
        exact (tempSpanR_disj_tempSlot fl sp hf (by omega) (by omega)).symm _ ⟨k, hk, rfl⟩
      have heq2' : MemEqOutside (tempSpanR fl sp tmp) st2.mem st3.mem :=
        heq2.mono (tempSpanR_mono fl sp hf (Nat.le_succ tmp) htmp_le)
      refine ⟨k1 + (lkm.totalSize cs + (k2 + lkm.totalSize cl)), st4, ?_, ?_, ?_, ?_,
        ((hpres1.trans hpresS).trans hpres2).trans hpresL,
        by rw [hmem4]; exact heq02.trans heq2'⟩
      · rw [run_add, hrun1]; dsimp only
        rw [run_add, hrunS]; dsimp only
        rw [run_add, hrun2]; dsimp only
        exact hrunL
      · rw [hpc4, htw_p3]; change BitVec.ofNat 64 (4 * _) = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (c1 ++ cs ++ c2 ++ cl))); rw [htw_all]; dsimp only [cl]; congr 2; omega
      · rw [ht0_4, hsp3, hslot3]
      · rw [hothL AbiReg.a0 (by decide) (by decide), ha0_3]
    · simp only [hv1, hv2] at r2 ⊢
      obtain ⟨k2, st3, hrun2, hpc3, hpres2, heq2⟩ := r2
      have heq2' : MemEqOutside (tempSpanR fl sp tmp) st2.mem st3.mem :=
        heq2.mono (tempSpanR_mono fl sp hf (Nat.le_succ tmp) htmp_le)
      exact ⟨k1 + (lkm.totalSize cs + k2), st3,
        by rw [run_add, hrun1]; dsimp only; rw [run_add, hrunS]; dsimp only; exact hrun2,
        hpc3, (hpres1.trans hpresS).trans hpres2, heq02.trans heq2'⟩
  · simp only [hv1] at r1 ⊢; exact r1

/-- Shared helper for evaluating `(e1, e2)` using `t4` to hold `v1` when `exprNoT4 e2 = true`:
    puts `v1` in `t4` and `v2` in `a0` with zero stack spills. -/
theorem reg_evalTwoT4_of_ih {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (e1 e2 : Expr) (pre tail : List AsmItem) (tmp : Nat)
    (hnt2 : exprNoT4 e2 = true)
    (htmp1 : tmp + usedTempsExpr e1 ≤ fl.usedTemps)
    (ih1 : ∀ (pre post : List AsmItem) (tmp : Nat) (rd : Reg) (st : State),
      ValidTargetReg fl rd →
      tmp + usedTempsExpr e1 ≤ fl.usedTemps →
      lkm.linkSpec (pre ++ compileETo env.tab fl tmp rd e1 ++ post) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd e1)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → T5GpOk L fl st → st.getReg AbiReg.sp = sp →
      ProgMemRel env.tab L st.mem lm → ProgFrameOkR L fl sp st loc →
      match _root_.L.evalE e1 ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd e1))) ∧
          st'.getReg rd = v.toBitVec ∧
          PreservedFrameRegs fl (· = rd) st st' ∧
          MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedFrameRegs fl (· = rd) st st' ∧
          MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem)
    (ih2 : ∀ (pre post : List AsmItem) (tmp : Nat) (rd : Reg) (st : State),
      ValidTargetReg fl rd →
      tmp + usedTempsExpr e2 ≤ fl.usedTemps →
      lkm.linkSpec (pre ++ compileETo env.tab fl tmp rd e2 ++ post) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd e2)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → T5GpOk L fl st → st.getReg AbiReg.sp = sp →
      ProgMemRel env.tab L st.mem lm → ProgFrameOkR L fl sp st loc →
      match _root_.L.evalE e2 ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd e2))) ∧
          st'.getReg rd = v.toBitVec ∧
          PreservedFrameRegs fl (· = rd) st st' ∧
          MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem ∧
          (exprNoT4 e2 = true → st'.getReg AbiReg.t4 = st.getReg AbiReg.t4)
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedFrameRegs fl (· = rd) st st' ∧
          MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem)
    (hlink : lkm.linkSpec (pre ++
        (compileETo env.tab fl tmp AbiReg.a0 e1 ++
         [Asm.mv AbiReg.t4 AbiReg.a0] ++
         compileETo env.tab fl tmp AbiReg.a0 e2) ++ tail) =
        .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize
        (compileETo env.tab fl tmp AbiReg.a0 e1 ++
         [Asm.mv AbiReg.t4 AbiReg.a0] ++
         compileETo env.tab fl tmp AbiReg.a0 e2)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    let seq := compileETo env.tab fl tmp AbiReg.a0 e1 ++
               [Asm.mv AbiReg.t4 AbiReg.a0] ++
               compileETo env.tab fl tmp AbiReg.a0 e2
    match _root_.L.evalE e1 ⟨lm, loc⟩, _root_.L.evalE e2 ⟨lm, loc⟩ with
    | .ok (v1, _), .ok (v2, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize seq)) ∧
        st'.getReg AbiReg.t4 = v1.toBitVec ∧
        st'.getReg AbiReg.a0 = v2.toBitVec ∧
        PreservedFrameRegs fl (· = AbiReg.a0) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem
    | _, _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = AbiReg.a0) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
  let c1 := compileETo env.tab fl tmp AbiReg.a0 e1
  let cmv := [Asm.mv AbiReg.t4 AbiReg.a0]
  let c2 := compileETo env.tab fl tmp AbiReg.a0 e2
  have hf : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  have htmp2 : tmp + usedTempsExpr e2 ≤ fl.usedTemps := by
    rw [usedTempsExpr_of_exprNoT4 hnt2]; omega
  have htw_mv : lkm.totalSize cmv = 1 := by simp [cmv, Asm.mv, lkm.totalSize_instr]
  have htw_all : lkm.totalSize (c1 ++ cmv ++ c2) = lkm.totalSize c1 + 1 + lkm.totalSize c2 := by
    simp only [lkm.totalSize_append, htw_mv]
  have h64' : 4 * (lkm.totalSize pre + (lkm.totalSize c1 + 1 + lkm.totalSize c2)) < 2 ^ 64 := by
    rw [← htw_all]; exact h64
  have r1 := ih1 pre (cmv ++ c2 ++ tail) tmp AbiReg.a0 st (Or.inl rfl) htmp1
    (by simpa only [c1, cmv, c2, List.append_assoc] using hlink)
    (by dsimp only [c1] at h64'; omega) hpc hgp ht5 hsp hmemRel hframeOk
  rcases _root_.L.evalE_pure e1 ⟨lm, loc⟩ with ⟨v1, hv1⟩ | hv1
  · simp only [hv1] at r1
    obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := r1
    have htw1 : lkm.totalSize (pre ++ c1) = lkm.totalSize pre + lkm.totalSize c1 := lkm.totalSize_append _ _
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ c1)) := by rw [htw1]; exact hpc1
    have hsMv := step_item_instr_lm lkm env.hrom (pre ++ c1) (c2 ++ tail)
      (.aluImm .addi AbiReg.t4 AbiReg.a0 0#12)
      (by simpa only [c1, cmv, c2, Asm.mv, List.append_assoc] using hlink)
      (by rw [htw1]; omega) st1 hpc1'
    let st2 := stepReg st1 AbiReg.t4 (st1.getReg AbiReg.a0) (st1.pc + 4#64)
    have hrunMv : RV64.run env.rom 1 st1 = .cont st2 :=
      run_one_cont _ _ st2 (by rw [hsMv]; simp only [execInstr, evalAluImm, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero]; rfl)
    have htw2 : lkm.totalSize (pre ++ c1 ++ cmv) = lkm.totalSize pre + lkm.totalSize c1 + 1 := by
      rw [lkm.totalSize_append, htw1, htw_mv]
    have hpc2 : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ c1 ++ cmv)) := by
      change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1', htw2, htw1]
    have hpresMv : PreservedFrameRegs fl (· = AbiReg.a0) st1 st2 :=
      PreservedFrameRegs.of_scratch1 AbiReg.t4 (by decide) (fun r hr => getReg_stepReg_ne st1 AbiReg.t4 r hr _ _)
    have hpres02 : PreservedFrameRegs fl (· = AbiReg.a0) st st2 := hpres1.trans hpresMv
    have hm2 : st2.mem = st1.mem := mem_stepReg st1 _ _ _
    have ht4_2 : st2.getReg AbiReg.t4 = v1.toBitVec :=
      (getReg_stepReg_eq st1 AbiReg.t4 (by decide) _ _).trans ha0_1
    have r2 := ih2 (pre ++ c1 ++ cmv) tail tmp AbiReg.a0 st2 (Or.inl rfl) htmp2
      (by simpa only [c1, cmv, c2, List.append_assoc] using hlink)
      (by rw [htw2]; dsimp only [c2] at h64'; omega) hpc2
      (hpres02.abi.gp.trans hgp) (ht5.of_preserved hpres02) (hpres02.abi.sp.trans hsp)
      (by rw [hm2]; exact ProgMemRel.of_tempSpanR hlo hhi (show tmp ≤ fl.usedTemps by omega) heq1 hmemRel)
      (ProgFrameOkR.of_preserved_temp hfl hf (show tmp ≤ fl.usedTemps by omega) hpres02 (by rw [hm2]; exact heq1) hframeOk)
    rcases _root_.L.evalE_pure e2 ⟨lm, loc⟩ with ⟨v2, hv2⟩ | hv2
    · simp only [hv1, hv2] at r2 ⊢
      obtain ⟨k2, st3, hrun2, hpc3, ha0_3, hpres2, heq2, ht4_3⟩ := r2
      exact ⟨k1 + (1 + k2), st3,
        by rw [run_add, hrun1]; dsimp only; rw [run_add, hrunMv]; dsimp only; exact hrun2,
        by rw [hpc3, htw2]; change BitVec.ofNat 64 (4 * _) = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (c1 ++ cmv ++ c2))); rw [htw_all]; dsimp only [c2]; congr 2; omega,
        (ht4_3 hnt2).trans ht4_2, ha0_3, hpres02.trans hpres2,
        heq1.trans (by rw [← hm2]; exact heq2)⟩
    · simp only [hv1, hv2] at r2 ⊢
      obtain ⟨k2, st3, hrun2, hpc3, hpres2, heq2⟩ := r2
      exact ⟨k1 + (1 + k2), st3,
        by rw [run_add, hrun1]; dsimp only; rw [run_add, hrunMv]; dsimp only; exact hrun2,
        hpc3, hpres02.trans hpres2, heq1.trans (by rw [← hm2]; exact heq2)⟩
  · simp only [hv1] at r1 ⊢; exact r1

/-- Shared 3-way `(head, rt, ri)` evaluation helper for tiered loads (`ld64t`, `ld32t`, `ld32h`). -/
theorem reg_evalTierHead_of_ih {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (t i : Expr) (pre tail : List AsmItem) (tmp : Nat)
    (htOk : exprOkB env.tab fl.nlocals t = true) (hiOk : exprOkB env.tab fl.nlocals i = true)
    (hVfT : ExprVarsInFrame fl t)
    (hTmp : tmp + (if isSimpleExpr t then usedTempsExpr i else max (usedTempsExpr t) (1 + usedTempsExpr i)) ≤ fl.usedTemps)
    (iht : ∀ (pre post : List AsmItem) (tmp : Nat) (rd : Reg) (st : State),
      ValidTargetReg fl rd →
      tmp + usedTempsExpr t ≤ fl.usedTemps →
      lkm.linkSpec (pre ++ compileETo env.tab fl tmp rd t ++ post) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd t)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → T5GpOk L fl st → st.getReg AbiReg.sp = sp →
      ProgMemRel env.tab L st.mem lm → ProgFrameOkR L fl sp st loc →
      match _root_.L.evalE t ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd t))) ∧
          st'.getReg rd = v.toBitVec ∧
          PreservedFrameRegs fl (· = rd) st st' ∧
          MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedFrameRegs fl (· = rd) st st' ∧
          MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem)
    (ihi : ∀ (pre post : List AsmItem) (tmp : Nat) (rd : Reg) (st : State),
      ValidTargetReg fl rd →
      tmp + usedTempsExpr i ≤ fl.usedTemps →
      lkm.linkSpec (pre ++ compileETo env.tab fl tmp rd i ++ post) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd i)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → T5GpOk L fl st → st.getReg AbiReg.sp = sp →
      ProgMemRel env.tab L st.mem lm → ProgFrameOkR L fl sp st loc →
      match _root_.L.evalE i ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd i))) ∧
          st'.getReg rd = v.toBitVec ∧
          PreservedFrameRegs fl (· = rd) st st' ∧
          MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem ∧
          (exprNoT4 i = true → st'.getReg AbiReg.t4 = st.getReg AbiReg.t4)
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedFrameRegs fl (· = rd) st st' ∧
          MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem)
    (hlink : let (head, _, _) := match exprReg? fl.alloc t with
        | some r => match exprReg? fl.alloc i with
          | some ri => ([], r, ri)
          | none => (compileETo env.tab fl tmp AbiReg.a0 i, r, AbiReg.a0)
        | none => match emitSimpleExprR env.tab fl AbiReg.t0 AbiReg.t1 t with
          | some ct => match exprReg? fl.alloc i with
            | some ri => (ct, AbiReg.t0, ri)
            | none => (compileETo env.tab fl tmp AbiReg.a0 i ++ ct, AbiReg.t0, AbiReg.a0)
          | none =>
            (compileETo env.tab fl tmp AbiReg.a0 t ++
             storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp) ++
             compileETo env.tab fl (tmp + 1) AbiReg.a0 i ++
             loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff tmp),
             AbiReg.t0, AbiReg.a0)
      lkm.linkSpec (pre ++ head ++ tail) = .ok (env.code, env.labels))
    (h64 : let (head, _, _) := match exprReg? fl.alloc t with
        | some r => match exprReg? fl.alloc i with
          | some ri => ([], r, ri)
          | none => (compileETo env.tab fl tmp AbiReg.a0 i, r, AbiReg.a0)
        | none => match emitSimpleExprR env.tab fl AbiReg.t0 AbiReg.t1 t with
          | some ct => match exprReg? fl.alloc i with
            | some ri => (ct, AbiReg.t0, ri)
            | none => (compileETo env.tab fl tmp AbiReg.a0 i ++ ct, AbiReg.t0, AbiReg.a0)
          | none =>
            (compileETo env.tab fl tmp AbiReg.a0 t ++
             storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp) ++
             compileETo env.tab fl (tmp + 1) AbiReg.a0 i ++
             loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff tmp),
             AbiReg.t0, AbiReg.a0)
      4 * (lkm.totalSize pre + lkm.totalSize head) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    let (head, rt, ri) := match exprReg? fl.alloc t with
      | some r => match exprReg? fl.alloc i with
        | some ri => ([], r, ri)
        | none => (compileETo env.tab fl tmp AbiReg.a0 i, r, AbiReg.a0)
      | none => match emitSimpleExprR env.tab fl AbiReg.t0 AbiReg.t1 t with
        | some ct => match exprReg? fl.alloc i with
          | some ri => (ct, AbiReg.t0, ri)
          | none => (compileETo env.tab fl tmp AbiReg.a0 i ++ ct, AbiReg.t0, AbiReg.a0)
        | none =>
          (compileETo env.tab fl tmp AbiReg.a0 t ++
           storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp) ++
           compileETo env.tab fl (tmp + 1) AbiReg.a0 i ++
           loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff tmp),
           AbiReg.t0, AbiReg.a0)
    (ri = AbiReg.zero ∨ ri = AbiReg.a0 ∨ ri ∈ allowedRegs true) ∧
    match _root_.L.evalE t ⟨lm, loc⟩, _root_.L.evalE i ⟨lm, loc⟩ with
    | .ok (vt, _), .ok (vi, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize head)) ∧
        st'.getReg rt = vt.toBitVec ∧
        st'.getReg ri = vi.toBitVec ∧
        PreservedFrameRegs fl (· = AbiReg.a0) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem ∧
        (isSimpleExpr t = true → exprNoT4 i = true → st'.getReg AbiReg.t4 = st.getReg AbiReg.t4)
    | _, _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = AbiReg.a0) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
  have hf : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  cases hrt : exprReg? fl.alloc t with
  | some r =>
    have hst : isSimpleExpr t = true := isSimpleExpr_of_exprReg hrt
    simp only [hst, ↓reduceIte] at hTmp
    obtain ⟨hrmem, _, vt, hvt, hgrt⟩ := reg_exprReg_sim hfl hframeOk htOk hrt
    cases hri : exprReg? fl.alloc i with
    | some ri =>
      simp only [hrt, hri] at hlink h64 ⊢
      obtain ⟨hrimem, _, vi, hvi, hgri⟩ := reg_exprReg_sim hfl hframeOk hiOk hri
      refine ⟨by rcases hrimem with h0 | hm; exact Or.inl h0; exact Or.inr (Or.inr hm), ?_⟩
      rw [hvt, hvi]
      exact ⟨0, st, rfl, by rw [lkm.totalSize_nil, Nat.add_zero]; exact hpc, hgrt, hgri,
        PreservedFrameRegs.refl _ _ _, MemEqOutside.refl _ _, fun _ _ => rfl⟩
    | none =>
      simp only [hrt, hri] at hlink h64 ⊢
      have riRes := ihi pre tail tmp AbiReg.a0 st (Or.inl rfl) hTmp hlink h64 hpc hgp ht5 hsp hmemRel hframeOk
      refine ⟨Or.inr (Or.inl trivial), ?_⟩
      rw [hvt]
      rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
      · simp only [hvi] at riRes ⊢
        obtain ⟨k1, st1, hr1, hpc1, ha0_1, hpres1, heq1, ht4_1⟩ := riRes
        exact ⟨k1, st1, hr1, hpc1, (hpres1.getReg_of_exprReg hrmem).trans hgrt, ha0_1, hpres1, heq1, fun _ hnt => ht4_1 hnt⟩
      · simp only [hvi] at riRes ⊢; exact riRes
  | none =>
    cases hst_em : emitSimpleExprR env.tab fl AbiReg.t0 AbiReg.t1 t with
    | some ct =>
      have hst : isSimpleExpr t = true := by
        cases t <;> simp [emitSimpleExprR, isSimpleExpr] at hst_em ⊢
      simp only [hst, ↓reduceIte] at hTmp
      cases hri : exprReg? fl.alloc i with
      | some ri =>
        simp only [hrt, hst_em, hri] at hlink h64 ⊢
        obtain ⟨hrimem, hriScr, vi, hvi, hgri⟩ := reg_exprReg_sim hfl hframeOk hiOk hri
        obtain ⟨vt, kt, st1, hvt, hr1, hpc1, ht0_1, hoth1, hmem1⟩ :=
          reg_emitSimpleExprR_sim env L fl hfl lm loc hspAlign pre tail AbiReg.t0 AbiReg.t1
            (by decide) (by decide) (by decide) (by decide) (fun _ => by decide) t ct hst_em htOk hVfT hlink h64
            st hpc hgp ht5 hsp hmemRel hframeOk
        refine ⟨by rcases hrimem with h0 | hm; exact Or.inl h0; exact Or.inr (Or.inr hm), ?_⟩
        rw [hvt, hvi]
        exact ⟨kt, st1, hr1, hpc1, ht0_1,
          (hoth1 ri (hriScr AbiReg.t0 (by decide)) (hriScr AbiReg.t1 (by decide))).trans hgri,
          PreservedFrameRegs.of_scratch2 AbiReg.t0 AbiReg.t1 (by decide) (by decide) hoth1,
          by rw [hmem1]; exact MemEqOutside.refl _ _,
          fun _ _ => hoth1 AbiReg.t4 (by decide) (by decide)⟩
      | none =>
        simp only [hrt, hst_em, hri] at hlink h64 ⊢
        have htw_all : lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 i ++ ct) =
            lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 i) + lkm.totalSize ct :=
          lkm.totalSize_append _ _
        have riRes := ihi pre (ct ++ tail) tmp AbiReg.a0 st (Or.inl rfl) hTmp
          (by simpa only [List.append_assoc] using hlink)
          (by rw [htw_all] at h64; omega) hpc hgp ht5 hsp hmemRel hframeOk
        refine ⟨Or.inr (Or.inl trivial), ?_⟩
        rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
        · simp only [hvi] at riRes
          obtain ⟨k1, st1, hr1, hpc1, ha0_1, hpres1, heq1, ht4_1⟩ := riRes
          have htw1 : lkm.totalSize (pre ++ compileETo env.tab fl tmp AbiReg.a0 i) =
              lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 i) :=
            lkm.totalSize_append _ _
          have hmemRel1 := ProgMemRel.of_tempSpanR hlo hhi (by omega) heq1 hmemRel
          have hframeOk1 := ProgFrameOkR.of_preserved_temp hfl hf (by omega) hpres1 heq1 hframeOk
          obtain ⟨vt, kt, st2, hvt, hr2, hpc2, ht0_2, hoth2, hmem2⟩ :=
            reg_emitSimpleExprR_sim env L fl hfl lm loc hspAlign
              (pre ++ compileETo env.tab fl tmp AbiReg.a0 i) tail AbiReg.t0 AbiReg.t1
              (by decide) (by decide) (by decide) (by decide) (fun _ => by decide) t ct hst_em htOk hVfT
              (by simpa only [List.append_assoc] using hlink)
              (by rw [htw1]; rw [htw_all] at h64; omega)
              st1 (by rw [htw1]; exact hpc1) (hpres1.abi.gp.trans hgp) (ht5.of_preserved hpres1)
              (hpres1.abi.sp.trans hsp) hmemRel1 hframeOk1
          rw [hvt, hvi]
          exact ⟨k1 + kt, st2, by rw [run_add, hr1]; dsimp only; exact hr2,
            by rw [hpc2, htw1, htw_all]; congr 2; omega,
            ht0_2, (hoth2 AbiReg.a0 (by decide) (by decide)).trans ha0_1,
            hpres1.trans (PreservedFrameRegs.of_scratch2 AbiReg.t0 AbiReg.t1 (by decide) (by decide) hoth2),
            by rw [hmem2]; exact heq1,
            fun _ hnt => (hoth2 AbiReg.t4 (by decide) (by decide)).trans (ht4_1 hnt)⟩
        · -- `i` traps; prove `t` is pure non-trapping via `emitSimpleExprR`
          have ⟨vt, hvt⟩ : ∃ vt, _root_.L.evalE t ⟨lm, loc⟩ = .ok (vt, ⟨lm, loc⟩) := by
            cases t with
            | const w => exact ⟨w, rfl⟩
            | var x => exact ⟨loc x, rfl⟩
            | len8 a => exact ⟨lm.len8 a, rfl⟩
            | len64 a => exact ⟨lm.len64 a, rfl⟩
            | glob g => exact ⟨lm.glob g, rfl⟩
            | _ => simp [emitSimpleExprR] at hst_em
          simp only [hvt, hvi] at riRes ⊢
          exact riRes
    | none =>
      have hstF : isSimpleExpr t = false := isSimpleExpr_false_of_emitSimple_none hst_em
      simp only [hstF, Bool.false_eq_true, ↓reduceIte] at hTmp
      simp only [hrt, hst_em] at hlink h64 ⊢
      refine ⟨Or.inr (Or.inl trivial), ?_⟩
      have hsp' := reg_evalTwoSpill_of_ih env L fl hfl lm loc hspAlign hlo hhi t i pre tail tmp
        (by omega) (by omega) (by omega) iht
        (fun p q tm rd' st' hrd' htm hl h6 hpc' hgp' ht5' hsp' hm' hf' => by
          have r := ihi p q tm rd' st' hrd' htm hl h6 hpc' hgp' ht5' hsp' hm' hf'
          cases hv : _root_.L.evalE i ⟨lm, loc⟩ with
          | ok res => simp only [hv] at r; rcases r with ⟨k, st2, h1, h2, h3, h4, h5, _⟩; exact ⟨k, st2, h1, h2, h3, h4, h5⟩
          | error _ => simp only [hv] at r; exact r)
        hlink h64 st hpc hgp ht5 hsp hmemRel hframeOk
      cases hvt : _root_.L.evalE t ⟨lm, loc⟩ with
      | ok _ =>
        cases hvi : _root_.L.evalE i ⟨lm, loc⟩ with
        | ok _ =>
          simp only [hvt, hvi] at hsp'
          rcases hsp' with ⟨k, st', h1, h2, h3, h4, h5, h6⟩
          exact ⟨k, st', h1, h2, h3, h4, h5, h6, fun h => by rw [hstF] at h; cases h⟩
        | error _ => simp only [hvt, hvi] at hsp'; exact hsp'
      | error _ => simp only [hvt] at hsp'; exact hsp'

/-- Shared body for 64-bit word-array loads (`ld64`, `ld64t` const-tier, `ld64t` dyn-tier). -/
theorem reg_ld64_body_r {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout)
    (lm : _root_.L.Mem) (s : TieredArray) (hsOk : env.tab.wordPosOkB s = true)
    (pre post : List AsmItem)
    (rd ri lenBase baseBase rLen rTmpLen rBase rTmpBase : Reg)
    (hrd : ValidTargetReg fl rd)
    (hri : ri = AbiReg.zero ∨ ri = AbiReg.a0 ∨ ri ∈ allowedRegs true)
    (hrLen : rLen ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3])
    (hrTmpLen : rTmpLen ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3])
    (hrBase : rBase ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3])
    (hrTmpBase : rTmpBase ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3])
    (hBaseTmp : rBase ≠ rTmpBase)
    (hLenBaseTmpLen : lenBase ≠ rTmpLen)
    (hBaseBaseLen : baseBase ≠ rLen)
    (hBaseBaseTmpLen : baseBase ≠ rTmpLen)
    (hBaseBaseTmpBase : baseBase ≠ rTmpBase)
    (hBaseBaseT6 : baseBase ≠ AbiReg.t6 ∧ baseBase ≠ AbiReg.s1)
    (lenOff baseOff : Int) (vi : _root_.L.Word)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hlenAddr : st.getReg lenBase + BitVec.ofInt 64 lenOff = L.T + BitVec.ofInt 64 (env.tab.len64 s))
    (hbaseAddr : st.getReg baseBase + BitVec.ofInt 64 baseOff = L.T + BitVec.ofInt 64 (env.tab.base64 s))
    (hriVal : st.getReg ri = vi.toBitVec)
    (hmemRel : ProgMemRel env.tab L st.mem lm)
    (hlink : lkm.linkSpec (pre ++
        (loadMemOff .ld rLen lenBase rTmpLen lenOff ++
         [Asm.bgeu ri rLen errLabel] ++
         loadMemOff .ld rBase baseBase rTmpBase baseOff ++
         [Asm.slli rTmpBase ri 3#6, Asm.add rBase rBase rTmpBase, Asm.ld rd rBase 0#12]) ++ post) =
        .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize
        (loadMemOff .ld rLen lenBase rTmpLen lenOff ++
         [Asm.bgeu ri rLen errLabel] ++
         loadMemOff .ld rBase baseBase rTmpBase baseOff ++
         [Asm.slli rTmpBase ri 3#6, Asm.add rBase rBase rTmpBase, Asm.ld rd rBase 0#12])) < 2 ^ 64) :
    let code :=
      loadMemOff .ld rLen lenBase rTmpLen lenOff ++
      [Asm.bgeu ri rLen errLabel] ++
      loadMemOff .ld rBase baseBase rTmpBase baseOff ++
      [Asm.slli rTmpBase ri 3#6, Asm.add rBase rBase rTmpBase, Asm.ld rd rBase 0#12]
    if h : vi.toNat < (lm.arr64 s).size then
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize code)) ∧
        st'.getReg rd = ((lm.arr64 s)[vi.toNat]'h).toBitVec ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        st'.mem = st.mem ∧
        st'.getReg AbiReg.t4 = st.getReg AbiReg.t4
    else
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        st'.mem = st.mem := by
  have hmemScr : ∀ r, r ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3] →
      r ∈ scratchRegs ∧ r ≠ AbiReg.zero ∧ r ≠ AbiReg.t6 ∧ r ≠ AbiReg.t4 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide, by decide⟩
  have ⟨hrLenS, hrLen0, hrLenT6, hrLenT4⟩ := hmemScr rLen hrLen
  have ⟨hrTmpLenS, hrTmpLen0, _, hrTmpLenT4⟩ := hmemScr rTmpLen hrTmpLen
  have ⟨hrBaseS, hrBase0, _, hrBaseT4⟩ := hmemScr rBase hrBase
  have ⟨hrTmpBaseS, hrTmpBase0, _, hrTmpBaseT4⟩ := hmemScr rTmpBase hrTmpBase
  have hriT6 : ri ≠ AbiReg.t6 := idxReg_ne_temp hri (by decide)
  have hriLen : ri ≠ rLen := idxReg_ne_temp hri (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrLen ⊢
    rcases hrLen with rfl | rfl | rfl | rfl <;> simp)
  have hriTmpLen : ri ≠ rTmpLen := idxReg_ne_temp hri (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrTmpLen ⊢
    rcases hrTmpLen with rfl | rfl | rfl | rfl <;> simp)
  have hriBase : ri ≠ rBase := idxReg_ne_temp hri (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrBase ⊢
    rcases hrBase with rfl | rfl | rfl | rfl <;> simp)
  have hriTmpBase : ri ≠ rTmpBase := idxReg_ne_temp hri (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrTmpBase ⊢
    rcases hrTmpBase with rfl | rfl | rfl | rfl <;> simp)
  let clen := loadMemOff .ld rLen lenBase rTmpLen lenOff
  let cbr := [Asm.bgeu ri rLen errLabel]
  let cbase := loadMemOff .ld rBase baseBase rTmpBase baseOff
  let ctail := [Asm.slli rTmpBase ri 3#6, Asm.add rBase rBase rTmpBase, Asm.ld rd rBase 0#12]
  have htw_tail : lkm.totalSize ctail = 3 := by
    simp [ctail, Asm.slli, Asm.add, Asm.ld, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
  have htw_all : lkm.totalSize (clen ++ cbr ++ cbase ++ ctail) =
      lkm.totalSize clen + lkm.totalSize cbr + lkm.totalSize cbase + 3 := by
    simp only [lkm.totalSize_append, htw_tail]
  have h64' : 4 * (lkm.totalSize pre + (lkm.totalSize clen + lkm.totalSize cbr + lkm.totalSize cbase + 3)) < 2 ^ 64 := by
    rw [← htw_all]; exact h64
  rcases hmemRel.2.1 s hsOk with ⟨_, hlt61, hlenR, hbaseR, hwordsR⟩
  have halLen : isAligned (st.getReg lenBase + BitVec.ofInt 64 lenOff) 8 = true := by
    rw [hlenAddr, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
  obtain ⟨st1, hrun1, hoth1, hrLen1, hmem1, hpc1⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre (cbr ++ cbase ++ ctail ++ post)
      rLen lenBase rTmpLen hrLen0 hrTmpLen0 hLenBaseTmpLen lenOff
      (by simpa only [clen, cbr, cbase, ctail, List.append_assoc] using hlink)
      (by dsimp only [clen] at h64'; omega) st hpc halLen
  have hpres1 : PreservedFrameRegs fl (· = rd) st st1 :=
    PreservedFrameRegs.of_scratch2 rLen rTmpLen hrLenS hrTmpLenS hoth1
  have htw1 : lkm.totalSize (pre ++ clen) = lkm.totalSize pre + lkm.totalSize clen := lkm.totalSize_append _ _
  have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ clen)) := by rw [htw1]; exact hpc1
  have hrLen1' : st1.getReg rLen = BitVec.ofNat 64 (lm.arr64 s).size := by
    rw [hrLen1, hlenAddr, hlenR]
  have hri1 : st1.getReg ri = vi.toBitVec := (hoth1 ri hriLen hriTmpLen).trans hriVal
  have hbaseReg1 : st1.getReg baseBase = st.getReg baseBase := hoth1 baseBase hBaseBaseLen hBaseBaseTmpLen
  have hlinkBr : lkm.linkSpec ((pre ++ clen) ++ [.br .bgeu ri rLen errLabel] ++ (cbase ++ ctail ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [clen, cbr, cbase, ctail, Asm.bgeu, List.append_assoc] using hlink
  have h64Br : 4 * (lkm.totalSize (pre ++ clen) + lkm.itemSize (.br .bgeu ri rLen errLabel)) < 2 ^ 64 := by
    rw [htw1]
    have : lkm.itemSize (.br .bgeu ri rLen errLabel) = lkm.totalSize cbr := by simp [cbr, Asm.bgeu, lkm.totalSize_singleton]
    omega
  split
  · next hbound =>
    have hcondF : evalBranch .bgeu (st1.getReg ri) (st1.getReg rLen) = false := by
      simp [evalBranch, hri1, hrLen1']
      rw [BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
          Nat.mod_eq_of_lt (by omega : (lm.arr64 s).size < 2 ^ 64), decide_eq_true hbound]
    obtain ⟨kBr, st2, hrun2, hpc2', hoth2, _, hmem2⟩ :=
      prog_step_br_fall env (pre ++ clen) (cbase ++ ctail ++ post)
        .bgeu ri rLen errLabel env.errTarget env.herrLbl ⟨hriT6, hrLenT6⟩
        hlinkBr h64Br st1 hpc1' hcondF
    have hpres2 : PreservedFrameRegs fl (· = rd) st1 st2 :=
      PreservedFrameRegs.of_t6_s1 hoth2
    have htw2 : lkm.totalSize (pre ++ clen ++ cbr) = lkm.totalSize pre + lkm.totalSize clen + lkm.totalSize cbr := by
      rw [lkm.totalSize_append, htw1]
    have hpc2 : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ clen ++ cbr)) := by
      rw [hpc2', htw2, htw1]; rfl
    have hbaseReg2 : st2.getReg baseBase = st.getReg baseBase := (hoth2 baseBase hBaseBaseT6).trans hbaseReg1
    have halBase : isAligned (st2.getReg baseBase + BitVec.ofInt 64 baseOff) 8 = true := by
      rw [hbaseReg2, hbaseAddr, Tab.base64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨st3, hrun3, hoth3, hrBase3, hmem3, hpc3⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom (pre ++ clen ++ cbr) (ctail ++ post)
        rBase baseBase rTmpBase hrBase0 hrTmpBase0 hBaseBaseTmpBase baseOff
        (by simpa only [clen, cbr, cbase, ctail, List.append_assoc] using hlink)
        (by rw [htw2]; dsimp only [cbase] at h64'; omega) st2 hpc2 halBase
    have hpres3 : PreservedFrameRegs fl (· = rd) st2 st3 :=
      PreservedFrameRegs.of_scratch2 rBase rTmpBase hrBaseS hrTmpBaseS hoth3
    let p3 := pre ++ clen ++ cbr ++ cbase
    have htw3 : lkm.totalSize p3 = lkm.totalSize pre + lkm.totalSize clen + lkm.totalSize cbr + lkm.totalSize cbase := by
      dsimp only [p3]; rw [lkm.totalSize_append, htw2]
    have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize p3) := by rw [htw3, ← htw2]; exact hpc3
    have hsSll := step_item_instr_lm lkm env.hrom p3 ([Asm.add rBase rBase rTmpBase, Asm.ld rd rBase 0#12] ++ post)
      (.shImm .slli rTmpBase ri 3#6)
      (by simpa only [p3, clen, cbr, cbase, ctail, Asm.slli, List.append_assoc, List.cons_append, List.nil_append] using hlink)
      (by rw [htw3]; omega) st3 hpc3'
    let st4 := stepReg st3 rTmpBase (st3.getReg ri <<< 3) (st3.pc + 4#64)
    have hpres4 : PreservedFrameRegs fl (· = rd) st3 st4 :=
      PreservedFrameRegs.of_scratch1 rTmpBase hrTmpBaseS (fun r hr => getReg_stepReg_ne st3 rTmpBase r hr _ _)
    have htw4 : lkm.totalSize (p3 ++ [Asm.slli rTmpBase ri 3#6]) = lkm.totalSize p3 + 1 := by
      rw [lkm.totalSize_append, Asm.slli, lkm.totalSize_instr]
    have hpc4 : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p3 ++ [Asm.slli rTmpBase ri 3#6])) := by
      change st3.pc + 4#64 = _; rw [pc_add_4_ofNat st3.pc hpc3', htw4]
    have hsAdd := step_item_instr_lm lkm env.hrom (p3 ++ [Asm.slli rTmpBase ri 3#6]) ([Asm.ld rd rBase 0#12] ++ post)
      (.alu .add rBase rBase rTmpBase)
      (by simpa only [p3, clen, cbr, cbase, ctail, Asm.slli, Asm.add, List.append_assoc, List.cons_append, List.nil_append] using hlink)
      (by rw [htw4, htw3]; omega) st4 hpc4
    let st5 := stepReg st4 rBase (st4.getReg rBase + st4.getReg rTmpBase) (st4.pc + 4#64)
    have hpres5 : PreservedFrameRegs fl (· = rd) st4 st5 :=
      PreservedFrameRegs.of_scratch1 rBase hrBaseS (fun r hr => getReg_stepReg_ne st4 rBase r hr _ _)
    have htw5 : lkm.totalSize (p3 ++ [Asm.slli rTmpBase ri 3#6] ++ [Asm.add rBase rBase rTmpBase]) = lkm.totalSize p3 + 2 := by
      rw [lkm.totalSize_append, htw4, Asm.add, lkm.totalSize_instr]
    have hpc5 : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p3 ++ [Asm.slli rTmpBase ri 3#6] ++ [Asm.add rBase rBase rTmpBase])) := by
      change st4.pc + 4#64 = _; rw [pc_add_4_ofNat st4.pc hpc4, htw5, htw4]
    have hrBase5 : st5.getReg rBase = L.base64 s + BitVec.ofNat 64 (8 * vi.toNat) := by
      have hb3 : st3.getReg rBase = L.base64 s := by
        rw [hrBase3, hmem2, hmem1, hbaseReg2, hbaseAddr, hbaseR]
      have hri3 : st3.getReg ri = vi.toBitVec := (hoth3 ri hriBase hriTmpBase).trans ((hoth2 ri ⟨hriT6, idxReg_ne_s1 hri⟩).trans hri1)
      have htmp4 : st4.getReg rTmpBase = BitVec.ofNat 64 (8 * vi.toNat) := by
        change (stepReg st3 rTmpBase _ _).getReg rTmpBase = _
        rw [getReg_stepReg_eq _ _ hrTmpBase0, hri3]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_shiftLeft, UInt64.toNat_toBitVec, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
        rw [show (2 ^ 3 : Nat) = 8 from rfl, Nat.mul_comm _ 8, Nat.mod_eq_of_lt (by omega)]
      have hb4 : st4.getReg rBase = L.base64 s :=
        (getReg_stepReg_ne st3 rTmpBase rBase hBaseTmp _ _).trans hb3
      change (stepReg st4 rBase _ _).getReg rBase = _
      rw [getReg_stepReg_eq _ _ hrBase0, hb4, htmp4]
    have hsLd := step_item_instr_lm lkm env.hrom (p3 ++ [Asm.slli rTmpBase ri 3#6] ++ [Asm.add rBase rBase rTmpBase]) post
      (.load .ld rd rBase 0#12)
      (by simpa only [p3, clen, cbr, cbase, ctail, Asm.slli, Asm.add, Asm.ld, List.append_assoc, List.cons_append, List.nil_append] using hlink)
      (by rw [htw5, htw3]; omega) st5 hpc5
    have halLd : isAligned (st5.getReg rBase + sextImm12 0#12) 8 = true := by
      rw [show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero, hrBase5]
      exact isAligned8_add_mul8 (L.base64 s) (L.h64Align s) vi.toNat
    let st6 := stepReg st5 rd (loadBytes st5.mem (st5.getReg rBase + sextImm12 0#12) 8) (st5.pc + 4#64)
    have hpres6 : PreservedFrameRegs fl (· = rd) st5 st6 :=
      PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) (fun r hr => getReg_stepReg_ne st5 rd r hr _ _)
    have hmem5 : st5.mem = st.mem := by
      dsimp only [st5, st4]; rw [mem_stepReg, mem_stepReg, hmem3, hmem2, hmem1]
    refine ⟨lkm.totalSize clen + (kBr + (lkm.totalSize cbase + (1 + (1 + 1)))), st6, ?_, ?_, ?_,
      hpres1.trans (hpres2.trans (hpres3.trans (hpres4.trans (hpres5.trans hpres6)))),
      (mem_stepReg _ _ _ _).trans hmem5, ?_⟩
    · rw [run_add, hrun1]; dsimp only
      rw [run_add, hrun2]; dsimp only
      rw [run_add, hrun3]; dsimp only
      rw [run_add, run_one_cont _ _ st4 (by rw [hsSll]; rfl)]; dsimp only
      rw [run_add, run_one_cont _ _ st5 (by rw [hsAdd]; rfl)]; dsimp only
      exact run_one_cont _ _ st6 (by rw [hsLd]; simp only [execInstr, halLd]; rfl)
    · change st5.pc + 4#64 = _
      rw [pc_add_4_ofNat st5.pc hpc5, htw5, htw3]
      change BitVec.ofNat 64 (4 * _) = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (clen ++ cbr ++ cbase ++ ctail)))
      rw [htw_all]; congr 2; omega
    · change (stepReg st5 rd _ _).getReg rd = _
      rw [getReg_stepReg_eq _ _ hrd.ne_zero, hmem5, show sextImm12 0#12 = 0#64 from rfl,
          BitVec.add_zero, hrBase5]
      exact hwordsR vi.toNat hbound
    · exact (getReg_stepReg_ne st5 rd AbiReg.t4 (hrd.ne_temp (by decide)).symm _ _).trans
        ((getReg_stepReg_ne st4 rBase AbiReg.t4 hrBaseT4.symm _ _).trans
          ((getReg_stepReg_ne st3 rTmpBase AbiReg.t4 hrTmpBaseT4.symm _ _).trans
            ((hoth3 AbiReg.t4 hrBaseT4.symm hrTmpBaseT4.symm).trans
              ((hoth2 AbiReg.t4 (by decide)).trans (hoth1 AbiReg.t4 hrLenT4.symm hrTmpLenT4.symm)))))
  · next hbound =>
    have hcondT : evalBranch .bgeu (st1.getReg ri) (st1.getReg rLen) = true := by
      simp [evalBranch, hri1, hrLen1']
      rw [BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
          Nat.mod_eq_of_lt (by omega : (lm.arr64 s).size < 2 ^ 64), decide_eq_false hbound]
    obtain ⟨kBr, st2, hrun2, hpc2', hoth2, _, hmem2⟩ :=
      prog_step_br_taken env (pre ++ clen) (cbase ++ ctail ++ post)
        .bgeu ri rLen errLabel env.errTarget env.herrLbl ⟨hriT6, hrLenT6⟩
        hlinkBr h64Br st1 hpc1' hcondT
    exact ⟨lkm.totalSize clen + kBr, st2,
      by rw [run_add, hrun1]; dsimp only; exact hrun2,
      hpc2', hpres1.trans (PreservedFrameRegs.of_t6_s1 hoth2),
      hmem2.trans hmem1⟩

/-- Constant-index (`vi.toNat < 256`) 64-bit word-array load body using immediate offset `8 * vi.toNat`. -/
theorem reg_ld64_const_body_r {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout)
    (lm : _root_.L.Mem) (s : TieredArray) (hsOk : env.tab.wordPosOkB s = true)
    (pre post : List AsmItem)
    (rd ri lenBase baseBase rLen rTmpLen rBase rTmpBase : Reg)
    (hrd : ValidTargetReg fl rd)
    (hri : ri = AbiReg.zero ∨ ri = AbiReg.a0 ∨ ri ∈ allowedRegs true)
    (hrLen : rLen ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3])
    (hrTmpLen : rTmpLen ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3])
    (hrBase : rBase ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3])
    (hrTmpBase : rTmpBase ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3])
    (hLenBaseTmpLen : lenBase ≠ rTmpLen)
    (hBaseBaseLen : baseBase ≠ rLen)
    (hBaseBaseTmpLen : baseBase ≠ rTmpLen)
    (hBaseBaseTmpBase : baseBase ≠ rTmpBase)
    (hBaseBaseT6 : baseBase ≠ AbiReg.t6 ∧ baseBase ≠ AbiReg.s1)
    (lenOff baseOff : Int) (vi : _root_.L.Word) (hviLt : vi.toNat < 256)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hlenAddr : st.getReg lenBase + BitVec.ofInt 64 lenOff = L.T + BitVec.ofInt 64 (env.tab.len64 s))
    (hbaseAddr : st.getReg baseBase + BitVec.ofInt 64 baseOff = L.T + BitVec.ofInt 64 (env.tab.base64 s))
    (hriVal : st.getReg ri = vi.toBitVec)
    (hmemRel : ProgMemRel env.tab L st.mem lm)
    (hlink : lkm.linkSpec (pre ++
        (loadMemOff .ld rLen lenBase rTmpLen lenOff ++
         [Asm.bgeu ri rLen errLabel] ++
         loadMemOff .ld rBase baseBase rTmpBase baseOff ++
         [Asm.ld rd rBase (BitVec.ofNat 12 (8 * vi.toNat))]) ++ post) =
        .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize
        (loadMemOff .ld rLen lenBase rTmpLen lenOff ++
         [Asm.bgeu ri rLen errLabel] ++
         loadMemOff .ld rBase baseBase rTmpBase baseOff ++
         [Asm.ld rd rBase (BitVec.ofNat 12 (8 * vi.toNat))])) < 2 ^ 64) :
    let code :=
      loadMemOff .ld rLen lenBase rTmpLen lenOff ++
      [Asm.bgeu ri rLen errLabel] ++
      loadMemOff .ld rBase baseBase rTmpBase baseOff ++
      [Asm.ld rd rBase (BitVec.ofNat 12 (8 * vi.toNat))]
    if h : vi.toNat < (lm.arr64 s).size then
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize code)) ∧
        st'.getReg rd = ((lm.arr64 s)[vi.toNat]'h).toBitVec ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        st'.mem = st.mem ∧
        st'.getReg AbiReg.t4 = st.getReg AbiReg.t4
    else
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        st'.mem = st.mem := by
  have hmemScr : ∀ r, r ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3] →
      r ∈ scratchRegs ∧ r ≠ AbiReg.zero ∧ r ≠ AbiReg.t6 ∧ r ≠ AbiReg.t4 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide, by decide⟩
  have ⟨hrLenS, hrLen0, hrLenT6, hrLenT4⟩ := hmemScr rLen hrLen
  have ⟨hrTmpLenS, hrTmpLen0, _, hrTmpLenT4⟩ := hmemScr rTmpLen hrTmpLen
  have ⟨hrBaseS, hrBase0, _, hrBaseT4⟩ := hmemScr rBase hrBase
  have ⟨hrTmpBaseS, hrTmpBase0, _, hrTmpBaseT4⟩ := hmemScr rTmpBase hrTmpBase
  have hriT6 : ri ≠ AbiReg.t6 := idxReg_ne_temp hri (by decide)
  have hriLen : ri ≠ rLen := idxReg_ne_temp hri (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrLen ⊢
    rcases hrLen with rfl | rfl | rfl | rfl <;> simp)
  have hriTmpLen : ri ≠ rTmpLen := idxReg_ne_temp hri (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrTmpLen ⊢
    rcases hrTmpLen with rfl | rfl | rfl | rfl <;> simp)
  let clen := loadMemOff .ld rLen lenBase rTmpLen lenOff
  let cbr := [Asm.bgeu ri rLen errLabel]
  let cbase := loadMemOff .ld rBase baseBase rTmpBase baseOff
  let off12 : BitVec 12 := BitVec.ofNat 12 (8 * vi.toNat)
  let ctail := [Asm.ld rd rBase off12]
  have htw_tail : lkm.totalSize ctail = 1 := by simp [ctail, Asm.ld, lkm.totalSize_instr]
  have htw_all : lkm.totalSize (clen ++ cbr ++ cbase ++ ctail) =
      lkm.totalSize clen + lkm.totalSize cbr + lkm.totalSize cbase + 1 := by
    simp only [lkm.totalSize_append, htw_tail]
  have h64' : 4 * (lkm.totalSize pre + (lkm.totalSize clen + lkm.totalSize cbr + lkm.totalSize cbase + 1)) < 2 ^ 64 := by
    rw [← htw_all]; exact h64
  rcases hmemRel.2.1 s hsOk with ⟨_, hlt61, hlenR, hbaseR, hwordsR⟩
  have halLen : isAligned (st.getReg lenBase + BitVec.ofInt 64 lenOff) 8 = true := by
    rw [hlenAddr, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
  obtain ⟨st1, hrun1, hoth1, hrLen1, hmem1, hpc1⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre (cbr ++ cbase ++ ctail ++ post)
      rLen lenBase rTmpLen hrLen0 hrTmpLen0 hLenBaseTmpLen lenOff
      (by simpa only [clen, cbr, cbase, ctail, off12, List.append_assoc] using hlink)
      (by dsimp only [clen] at h64'; omega) st hpc halLen
  have hpres1 : PreservedFrameRegs fl (· = rd) st st1 :=
    PreservedFrameRegs.of_scratch2 rLen rTmpLen hrLenS hrTmpLenS hoth1
  have htw1 : lkm.totalSize (pre ++ clen) = lkm.totalSize pre + lkm.totalSize clen := lkm.totalSize_append _ _
  have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ clen)) := by rw [htw1]; exact hpc1
  have hrLen1' : st1.getReg rLen = BitVec.ofNat 64 (lm.arr64 s).size := by rw [hrLen1, hlenAddr, hlenR]
  have hri1 : st1.getReg ri = vi.toBitVec := (hoth1 ri hriLen hriTmpLen).trans hriVal
  have hbaseReg1 : st1.getReg baseBase = st.getReg baseBase := hoth1 baseBase hBaseBaseLen hBaseBaseTmpLen
  have hlinkBr : lkm.linkSpec ((pre ++ clen) ++ [.br .bgeu ri rLen errLabel] ++ (cbase ++ ctail ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [clen, cbr, cbase, ctail, off12, Asm.bgeu, List.append_assoc] using hlink
  have h64Br : 4 * (lkm.totalSize (pre ++ clen) + lkm.itemSize (.br .bgeu ri rLen errLabel)) < 2 ^ 64 := by
    rw [htw1]
    have : lkm.itemSize (.br .bgeu ri rLen errLabel) = lkm.totalSize cbr := by simp [cbr, Asm.bgeu, lkm.totalSize_singleton]
    omega
  split
  · next hbound =>
    have hcondF : evalBranch .bgeu (st1.getReg ri) (st1.getReg rLen) = false := by
      simp [evalBranch, hri1, hrLen1']
      rw [BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
          Nat.mod_eq_of_lt (by omega : (lm.arr64 s).size < 2 ^ 64), decide_eq_true hbound]
    obtain ⟨kBr, st2, hrun2, hpc2', hoth2, _, hmem2⟩ :=
      prog_step_br_fall env (pre ++ clen) (cbase ++ ctail ++ post)
        .bgeu ri rLen errLabel env.errTarget env.herrLbl ⟨hriT6, hrLenT6⟩
        hlinkBr h64Br st1 hpc1' hcondF
    have hpres2 : PreservedFrameRegs fl (· = rd) st1 st2 :=
      PreservedFrameRegs.of_t6_s1 hoth2
    have htw2 : lkm.totalSize (pre ++ clen ++ cbr) = lkm.totalSize pre + lkm.totalSize clen + lkm.totalSize cbr := by
      rw [lkm.totalSize_append, htw1]
    have hpc2 : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ clen ++ cbr)) := by
      rw [hpc2', htw2, htw1]; rfl
    have hbaseReg2 : st2.getReg baseBase = st.getReg baseBase := (hoth2 baseBase hBaseBaseT6).trans hbaseReg1
    have halBase : isAligned (st2.getReg baseBase + BitVec.ofInt 64 baseOff) 8 = true := by
      rw [hbaseReg2, hbaseAddr, Tab.base64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨st3, hrun3, hoth3, hrBase3, hmem3, hpc3⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom (pre ++ clen ++ cbr) (ctail ++ post)
        rBase baseBase rTmpBase hrBase0 hrTmpBase0 hBaseBaseTmpBase baseOff
        (by simpa only [clen, cbr, cbase, ctail, off12, List.append_assoc] using hlink)
        (by rw [htw2]; dsimp only [cbase] at h64'; omega) st2 hpc2 halBase
    have hpres3 : PreservedFrameRegs fl (· = rd) st2 st3 :=
      PreservedFrameRegs.of_scratch2 rBase rTmpBase hrBaseS hrTmpBaseS hoth3
    let p3 := pre ++ clen ++ cbr ++ cbase
    have htw3 : lkm.totalSize p3 = lkm.totalSize pre + lkm.totalSize clen + lkm.totalSize cbr + lkm.totalSize cbase := by
      dsimp only [p3]; rw [lkm.totalSize_append, htw2]
    have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize p3) := by rw [htw3, ← htw2]; exact hpc3
    have hrBase3' : st3.getReg rBase = L.base64 s := by rw [hrBase3, hmem2, hmem1, hbaseReg2, hbaseAddr, hbaseR]
    have hsext : sextImm12 off12 = BitVec.ofNat 64 (8 * vi.toNat) := sextImm12_ofNat_lt (8 * vi.toNat) (by omega)
    have hsLd := step_item_instr_lm lkm env.hrom p3 post (.load .ld rd rBase off12)
      (by simpa only [p3, clen, cbr, cbase, ctail, off12, Asm.ld, List.append_assoc, List.cons_append, List.nil_append] using hlink)
      (by rw [htw3]; omega) st3 hpc3'
    have halLd : isAligned (st3.getReg rBase + sextImm12 off12) 8 = true := by
      rw [hrBase3', hsext]; exact isAligned8_add_mul8 (L.base64 s) (L.h64Align s) vi.toNat
    let st4 := stepReg st3 rd (loadBytes st3.mem (st3.getReg rBase + sextImm12 off12) 8) (st3.pc + 4#64)
    have hpres4 : PreservedFrameRegs fl (· = rd) st3 st4 :=
      PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) (fun r hr => getReg_stepReg_ne st3 rd r hr _ _)
    have hm3 : st3.mem = st.mem := by rw [hmem3, hmem2, hmem1]
    refine ⟨lkm.totalSize clen + (kBr + (lkm.totalSize cbase + 1)), st4, ?_, ?_, ?_,
      hpres1.trans (hpres2.trans (hpres3.trans hpres4)), (mem_stepReg _ _ _ _).trans hm3, ?_⟩
    · rw [run_add, hrun1]; dsimp only
      rw [run_add, hrun2]; dsimp only
      rw [run_add, hrun3]; dsimp only
      exact run_one_cont _ _ st4 (by rw [hsLd]; simp only [execInstr, halLd]; rfl)
    · change st3.pc + 4#64 = _
      rw [pc_add_4_ofNat st3.pc hpc3', htw3]
      change BitVec.ofNat 64 (4 * _) = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (clen ++ cbr ++ cbase ++ ctail)))
      rw [htw_all]; congr 2; omega
    · change (stepReg st3 rd _ _).getReg rd = _
      rw [getReg_stepReg_eq _ _ hrd.ne_zero, hm3, hrBase3', hsext]
      exact hwordsR vi.toNat hbound
    · exact (getReg_stepReg_ne st3 rd AbiReg.t4 (hrd.ne_temp (by decide)).symm _ _).trans
        ((hoth3 AbiReg.t4 hrBaseT4.symm hrTmpBaseT4.symm).trans
          ((hoth2 AbiReg.t4 (by decide)).trans (hoth1 AbiReg.t4 hrLenT4.symm hrTmpLenT4.symm)))
  · next hbound =>
    have hcondT : evalBranch .bgeu (st1.getReg ri) (st1.getReg rLen) = true := by
      simp [evalBranch, hri1, hrLen1']
      rw [BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
          Nat.mod_eq_of_lt (by omega : (lm.arr64 s).size < 2 ^ 64), decide_eq_false hbound]
    obtain ⟨kBr, st2, hrun2, hpc2', hoth2, _, hmem2⟩ :=
      prog_step_br_taken env (pre ++ clen) (cbase ++ ctail ++ post)
        .bgeu ri rLen errLabel env.errTarget env.herrLbl ⟨hriT6, hrLenT6⟩
        hlinkBr h64Br st1 hpc1' hcondT
    exact ⟨lkm.totalSize clen + kBr, st2,
      by rw [run_add, hrun1]; dsimp only; exact hrun2,
      hpc2', hpres1.trans (PreservedFrameRegs.of_t6_s1 hoth2),
      hmem2.trans hmem1⟩

/-- Shared body for 32-bit packed tiered loads (`ld32t` const-tier & dyn-tier). -/
theorem reg_ld32t_body_r {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout)
    (lm : _root_.L.Mem) (s : TieredArray) (hsOk : env.tab.wordPosOkB s = true)
    (pre post : List AsmItem)
    (rd ri lenBase baseBase : Reg)
    (hrd : ValidTargetReg fl rd)
    (hri : ri = AbiReg.zero ∨ ri = AbiReg.a0 ∨ ri ∈ allowedRegs true)
    (hLenBase3 : lenBase ≠ AbiReg.t3)
    (hBaseBase2 : baseBase ≠ AbiReg.t2) (hBaseBase3 : baseBase ≠ AbiReg.t3) (hBaseBaseT6 : baseBase ≠ AbiReg.t6 ∧ baseBase ≠ AbiReg.s1)
    (lenOff baseOff : Int) (vi : _root_.L.Word)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hlenAddr : st.getReg lenBase + BitVec.ofInt 64 lenOff = L.T + BitVec.ofInt 64 (env.tab.len64 s))
    (hbaseAddr : st.getReg baseBase + BitVec.ofInt 64 baseOff = L.T + BitVec.ofInt 64 (env.tab.base64 s))
    (hriVal : st.getReg ri = vi.toBitVec)
    (hmemRel : ProgMemRel env.tab L st.mem lm)
    (hlink : lkm.linkSpec (pre ++
        (loadMemOff .ld AbiReg.t2 lenBase AbiReg.t3 lenOff ++
         [Asm.srli AbiReg.t3 ri 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
         loadMemOff .ld AbiReg.t1 baseBase AbiReg.t3 baseOff ++
         [Asm.slli AbiReg.t3 ri 2#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3, Asm.lwu rd AbiReg.t1 0#12]) ++ post) =
        .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize
        (loadMemOff .ld AbiReg.t2 lenBase AbiReg.t3 lenOff ++
         [Asm.srli AbiReg.t3 ri 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
         loadMemOff .ld AbiReg.t1 baseBase AbiReg.t3 baseOff ++
         [Asm.slli AbiReg.t3 ri 2#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3, Asm.lwu rd AbiReg.t1 0#12])) < 2 ^ 64) :
    let code :=
      loadMemOff .ld AbiReg.t2 lenBase AbiReg.t3 lenOff ++
      [Asm.srli AbiReg.t3 ri 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 baseBase AbiReg.t3 baseOff ++
      [Asm.slli AbiReg.t3 ri 2#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3, Asm.lwu rd AbiReg.t1 0#12]
    if h : (vi / 2).toNat < (lm.arr64 s).size then
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize code)) ∧
        st'.getReg rd = (half32 ((lm.arr64 s)[(vi / 2).toNat]'h) vi).toBitVec ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        st'.mem = st.mem ∧
        st'.getReg AbiReg.t4 = st.getReg AbiReg.t4
    else
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        st'.mem = st.mem := by
  have hriT1 : ri ≠ AbiReg.t1 := idxReg_ne_temp hri (by decide)
  have hriT2 : ri ≠ AbiReg.t2 := idxReg_ne_temp hri (by decide)
  have hriT3 : ri ≠ AbiReg.t3 := idxReg_ne_temp hri (by decide)
  have hriT6 : ri ≠ AbiReg.t6 := idxReg_ne_temp hri (by decide)
  let clen := loadMemOff .ld AbiReg.t2 lenBase AbiReg.t3 lenOff
  let csrl := [Asm.srli AbiReg.t3 ri 1#6]
  let cbr := [Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel]
  let cbase := loadMemOff .ld AbiReg.t1 baseBase AbiReg.t3 baseOff
  let ctail := [Asm.slli AbiReg.t3 ri 2#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3, Asm.lwu rd AbiReg.t1 0#12]
  have htw_tail : lkm.totalSize ctail = 3 := by
    simp [ctail, Asm.slli, Asm.add, Asm.lwu, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
  have htw_all : lkm.totalSize (clen ++ [Asm.srli AbiReg.t3 ri 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++ cbase ++ ctail) =
      lkm.totalSize clen + 1 + lkm.totalSize cbr + lkm.totalSize cbase + 3 := by
    have hsplit : [Asm.srli AbiReg.t3 ri 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] = csrl ++ cbr := rfl
    rw [hsplit]; simp only [lkm.totalSize_append, htw_tail, csrl, Asm.srli, lkm.totalSize_instr]; omega
  have h64' : 4 * (lkm.totalSize pre + (lkm.totalSize clen + 1 + lkm.totalSize cbr + lkm.totalSize cbase + 3)) < 2 ^ 64 := by
    rw [← htw_all]; exact h64
  rcases hmemRel.2.1 s hsOk with ⟨_, hlt61, hlenR, hbaseR, hwordsR⟩
  have halLen : isAligned (st.getReg lenBase + BitVec.ofInt 64 lenOff) 8 = true := by
    rw [hlenAddr, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
  obtain ⟨st1, hrun1, hoth1, ht2_1, hmem1, hpc1⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre (csrl ++ cbr ++ cbase ++ ctail ++ post)
      AbiReg.t2 lenBase AbiReg.t3 (by decide) (by decide) hLenBase3 lenOff
      (by simpa only [clen, csrl, cbr, cbase, ctail, List.append_assoc, List.cons_append, List.nil_append] using hlink)
      (by dsimp only [clen] at h64'; omega) st hpc halLen
  have hpres1 : PreservedFrameRegs fl (· = rd) st st1 :=
    PreservedFrameRegs.of_scratch2 AbiReg.t2 AbiReg.t3 (by decide) (by decide) hoth1
  have htw1 : lkm.totalSize (pre ++ clen) = lkm.totalSize pre + lkm.totalSize clen := lkm.totalSize_append _ _
  have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ clen)) := by rw [htw1]; exact hpc1
  have hri1 : st1.getReg ri = vi.toBitVec := (hoth1 ri hriT2 hriT3).trans hriVal
  have ht2_1' : st1.getReg AbiReg.t2 = BitVec.ofNat 64 (lm.arr64 s).size := by rw [ht2_1, hlenAddr, hlenR]
  have hbaseReg1 : st1.getReg baseBase = st.getReg baseBase := hoth1 baseBase hBaseBase2 hBaseBase3
  have hsSrl := step_item_instr_lm lkm env.hrom (pre ++ clen) (cbr ++ cbase ++ ctail ++ post)
    (.shImm .srli AbiReg.t3 ri 1#6)
    (by simpa only [clen, csrl, cbr, cbase, ctail, Asm.srli, List.append_assoc, List.cons_append, List.nil_append] using hlink)
    (by rw [htw1]; omega) st1 hpc1'
  let st2 := stepReg st1 AbiReg.t3 (st1.getReg ri >>> 1) (st1.pc + 4#64)
  have hpres2 : PreservedFrameRegs fl (· = rd) st1 st2 :=
    PreservedFrameRegs.of_scratch1 AbiReg.t3 (by decide) (fun r hr => getReg_stepReg_ne st1 AbiReg.t3 r hr _ _)
  have htw2 : lkm.totalSize (pre ++ clen ++ csrl) = lkm.totalSize pre + lkm.totalSize clen + 1 := by
    rw [lkm.totalSize_append, htw1]; simp only [csrl, Asm.srli, lkm.totalSize_instr]
  have hpc2 : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ clen ++ csrl)) := by
    change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1', htw2, htw1]
  have ht3_2 : st2.getReg AbiReg.t3 = BitVec.ofNat 64 (vi / 2).toNat := by
    change (stepReg st1 AbiReg.t3 _ _).getReg AbiReg.t3 = _
    rw [getReg_stepReg_eq _ _ (by decide), hri1]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, UInt64.toNat_toBitVec]
    change vi.toNat >>> 1 = _
    rw [Nat.shiftRight_eq_div_pow]; simp only [Nat.pow_one]
    have hvit : vi.toNat < 2 ^ 64 := vi.toBitVec.isLt
    rw [BitVec.toNat_ofNat, show (vi / 2).toNat = vi.toNat / 2 from rfl, Nat.mod_eq_of_lt (by omega)]
  have ht2_2 : st2.getReg AbiReg.t2 = BitVec.ofNat 64 (lm.arr64 s).size :=
    (getReg_stepReg_ne st1 AbiReg.t3 AbiReg.t2 (by decide) _ _).trans ht2_1'
  have hlinkBr : lkm.linkSpec ((pre ++ clen ++ csrl) ++ [.br .bgeu AbiReg.t3 AbiReg.t2 errLabel] ++ (cbase ++ ctail ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [clen, csrl, cbr, cbase, ctail, Asm.bgeu, List.append_assoc, List.cons_append, List.nil_append] using hlink
  have h64Br : 4 * (lkm.totalSize (pre ++ clen ++ csrl) + lkm.itemSize (.br .bgeu AbiReg.t3 AbiReg.t2 errLabel)) < 2 ^ 64 := by
    rw [htw2]
    have : lkm.itemSize (.br .bgeu AbiReg.t3 AbiReg.t2 errLabel) = lkm.totalSize cbr := by simp [cbr, Asm.bgeu, lkm.totalSize_singleton]
    omega
  split
  · next hbound =>
    have hbound' : vi.toNat / 2 < (lm.arr64 s).size := hbound
    have hcondF : evalBranch .bgeu (st2.getReg AbiReg.t3) (st2.getReg AbiReg.t2) = false := by
      have hdvlt : vi.toNat / 2 < 2 ^ 64 := by have := vi.toBitVec.isLt; omega
      simp [evalBranch, ht3_2, ht2_2]
      rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hdvlt, Nat.mod_eq_of_lt (by omega : (lm.arr64 s).size < 2 ^ 64),
          decide_eq_true hbound']
    obtain ⟨kBr, st3, hrun3, hpc3', hoth3, _, hmem3⟩ :=
      prog_step_br_fall env (pre ++ clen ++ csrl) (cbase ++ ctail ++ post)
        .bgeu AbiReg.t3 AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide)
        hlinkBr h64Br st2 hpc2 hcondF
    have hpres3 : PreservedFrameRegs fl (· = rd) st2 st3 :=
      PreservedFrameRegs.of_t6_s1 hoth3
    have htw3 : lkm.totalSize (pre ++ clen ++ csrl ++ cbr) =
        lkm.totalSize pre + lkm.totalSize clen + 1 + lkm.totalSize cbr := by
      rw [lkm.totalSize_append, htw2]
    have hpc3 : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ clen ++ csrl ++ cbr)) := by
      rw [hpc3', htw3, htw2]; rfl
    have hbaseReg3 : st3.getReg baseBase = st.getReg baseBase :=
      (hoth3 baseBase hBaseBaseT6).trans ((getReg_stepReg_ne st1 AbiReg.t3 baseBase hBaseBase3 _ _).trans hbaseReg1)
    have halBase : isAligned (st3.getReg baseBase + BitVec.ofInt 64 baseOff) 8 = true := by
      rw [hbaseReg3, hbaseAddr, Tab.base64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨st4, hrun4, hoth4, ht1_4, hmem4, hpc4⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom (pre ++ clen ++ csrl ++ cbr) (ctail ++ post)
        AbiReg.t1 baseBase AbiReg.t3 (by decide) (by decide) hBaseBase3 baseOff
        (by simpa only [clen, csrl, cbr, cbase, ctail, List.append_assoc, List.cons_append, List.nil_append] using hlink)
        (by rw [htw3]; dsimp only [cbase] at h64'; omega) st3 hpc3 halBase
    have hpres4 : PreservedFrameRegs fl (· = rd) st3 st4 :=
      PreservedFrameRegs.of_scratch2 AbiReg.t1 AbiReg.t3 (by decide) (by decide) hoth4
    let p4 := pre ++ clen ++ csrl ++ cbr ++ cbase
    have htw4 : lkm.totalSize p4 = lkm.totalSize pre + lkm.totalSize clen + 1 + lkm.totalSize cbr + lkm.totalSize cbase := by
      dsimp only [p4]; rw [lkm.totalSize_append, htw3]
    have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize p4) := by rw [htw4, ← htw3]; exact hpc4
    have hsSll := step_item_instr_lm lkm env.hrom p4
      ([Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3, Asm.lwu rd AbiReg.t1 0#12] ++ post)
      (.shImm .slli AbiReg.t3 ri 2#6)
      (by simpa only [p4, clen, csrl, cbr, cbase, ctail, Asm.slli, List.append_assoc, List.cons_append, List.nil_append] using hlink)
      (by rw [htw4]; omega) st4 hpc4'
    let st5 := stepReg st4 AbiReg.t3 (st4.getReg ri <<< 2) (st4.pc + 4#64)
    have hpres5 : PreservedFrameRegs fl (· = rd) st4 st5 :=
      PreservedFrameRegs.of_scratch1 AbiReg.t3 (by decide) (fun r hr => getReg_stepReg_ne st4 AbiReg.t3 r hr _ _)
    have htw5 : lkm.totalSize (p4 ++ [Asm.slli AbiReg.t3 ri 2#6]) = lkm.totalSize p4 + 1 := by
      rw [lkm.totalSize_append, Asm.slli, lkm.totalSize_instr]
    have hpc5 : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p4 ++ [Asm.slli AbiReg.t3 ri 2#6])) := by
      change st4.pc + 4#64 = _; rw [pc_add_4_ofNat st4.pc hpc4', htw5]
    have hsAdd := step_item_instr_lm lkm env.hrom (p4 ++ [Asm.slli AbiReg.t3 ri 2#6])
      ([Asm.lwu rd AbiReg.t1 0#12] ++ post) (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.t3)
      (by simpa only [p4, clen, csrl, cbr, cbase, ctail, Asm.slli, Asm.add, List.append_assoc, List.cons_append, List.nil_append] using hlink)
      (by rw [htw5, htw4]; omega) st5 hpc5
    let st6 := stepReg st5 AbiReg.t1 (st5.getReg AbiReg.t1 + st5.getReg AbiReg.t3) (st5.pc + 4#64)
    have hpres6 : PreservedFrameRegs fl (· = rd) st5 st6 :=
      PreservedFrameRegs.of_scratch1 AbiReg.t1 (by decide) (fun r hr => getReg_stepReg_ne st5 AbiReg.t1 r hr _ _)
    have htw6 : lkm.totalSize (p4 ++ [Asm.slli AbiReg.t3 ri 2#6] ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3]) =
        lkm.totalSize p4 + 2 := by
      rw [lkm.totalSize_append, htw5, Asm.add, lkm.totalSize_instr]
    have hpc6 : st6.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p4 ++ [Asm.slli AbiReg.t3 ri 2#6] ++
        [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3])) := by
      change st5.pc + 4#64 = _; rw [pc_add_4_ofNat st5.pc hpc5, htw6, htw5]
    have ht1_6 : st6.getReg AbiReg.t1 = L.base64 s + BitVec.ofNat 64 (4 * vi.toNat) := by
      have ht1' : st4.getReg AbiReg.t1 = L.base64 s := by
        rw [ht1_4, hmem3, mem_stepReg, hmem1, hbaseReg3, hbaseAddr, hbaseR]
      have hri4 : st4.getReg ri = vi.toBitVec :=
        (hoth4 ri hriT1 hriT3).trans ((hoth3 ri ⟨hriT6, idxReg_ne_s1 hri⟩).trans ((getReg_stepReg_ne st1 AbiReg.t3 ri hriT3 _ _).trans hri1))
      have hvi_lt : 4 * vi.toNat < 2 ^ 64 := by omega
      have ht3_5 : st5.getReg AbiReg.t3 = BitVec.ofNat 64 (4 * vi.toNat) := by
        change (stepReg st4 AbiReg.t3 _ _).getReg AbiReg.t3 = _
        rw [getReg_stepReg_eq _ _ (by decide), hri4]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_shiftLeft, UInt64.toNat_toBitVec, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
        rw [show (2 ^ 2 : Nat) = 4 from rfl, Nat.mul_comm _ 4, Nat.mod_eq_of_lt hvi_lt]
      have ht1_5 : st5.getReg AbiReg.t1 = L.base64 s :=
        (getReg_stepReg_ne st4 AbiReg.t3 AbiReg.t1 (by decide) _ _).trans ht1'
      change (stepReg st5 AbiReg.t1 _ _).getReg AbiReg.t1 = _
      rw [getReg_stepReg_eq _ _ (by decide), ht1_5, ht3_5]
    have hal6 : isAligned (st6.getReg AbiReg.t1 + sextImm12 0#12) 4 = true := by
      rw [show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero, ht1_6]
      exact isAligned4_add_mul4 (L.base64 s) (L.h64Align s) vi.toNat
    let st7 := stepReg st6 rd ((loadBytes st6.mem (st6.getReg AbiReg.t1 + sextImm12 0#12) 4).zeroExtend 64) (st6.pc + 4#64)
    obtain ⟨hrun7, hpc7, hrd7, hoth7, hmem7⟩ :=
      step_lwu_off_r env (p4 ++ [Asm.slli AbiReg.t3 ri 2#6] ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3])
        post rd AbiReg.t1 0#12 hrd.ne_zero
        (by simpa only [p4, clen, csrl, cbr, cbase, ctail, Asm.lwu, Asm.raw, Asm.add, Asm.slli,
            List.append_assoc, List.cons_append, List.nil_append] using hlink)
        (by rw [htw6, htw4]; omega) st6 hpc6 hal6
    have hpres7 : PreservedFrameRegs fl (· = rd) st6 st7 :=
      PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) hoth7
    have hm6 : st6.mem = st.mem := by
      dsimp only [st6, st5]; rw [mem_stepReg, mem_stepReg, hmem4, hmem3, mem_stepReg, hmem1]
    have hrd7' : st7.getReg rd = (half32 ((lm.arr64 s)[(vi / 2).toNat]) vi).toBitVec := by
      rw [hrd7, hm6, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero, ht1_6]
      have hw := hwordsR (vi / 2).toNat hbound
      have him : (vi % 2).toNat = vi.toNat % 2 := by
        rw [UInt64.toNat_mod, show (2 : UInt64).toNat = 2 from rfl]
      by_cases hev : vi % 2 = 0
      · have hmod0 : vi.toNat % 2 = 0 := by rw [← him, hev]; rfl
        have h48 : 4 * vi.toNat = 8 * (vi / 2).toNat := by
          have : (vi / 2).toNat = vi.toNat / 2 := rfl; omega
        rw [h48, loadBytes_zeroExtend32_lo, hw]
        simp only [half32, hev, ↓reduceIte, UInt64.toNat_toBitVec, UInt64.ofNat_toNat]
      · have hmod1 : vi.toNat % 2 = 1 := by
          have hne0 : vi.toNat % 2 ≠ 0 := fun h0 => hev (UInt64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (by
            rw [UInt64.toNat_toBitVec, him, h0]; rfl)))
          omega
        have h48 : L.base64 s + BitVec.ofNat 64 (4 * vi.toNat) =
            (L.base64 s + BitVec.ofNat 64 (8 * (vi / 2).toNat)) + 4#64 := by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 1
          have : (vi / 2).toNat = vi.toNat / 2 := rfl
          rw [show 4 * vi.toNat = 8 * (vi / 2).toNat + 4 by omega]
        rw [h48, loadBytes_zeroExtend32_hi, hw]
        simp only [half32, hev, ↓reduceIte, UInt64.toNat_toBitVec, UInt64.ofNat_toNat]
        apply BitVec.eq_of_toNat_eq
        simp only [UInt64.toNat_toBitVec, UInt64.toNat_shiftRight, UInt64.toNat_div,
          show (32 : UInt64).toNat % 64 = 32 from rfl, show (4294967296 : UInt64).toNat = 2 ^ 32 from rfl,
          Nat.shiftRight_eq_div_pow]
    refine ⟨lkm.totalSize clen + (1 + (kBr + (lkm.totalSize cbase + (1 + (1 + 1))))), st7, ?_, ?_, hrd7',
      hpres1.trans (hpres2.trans (hpres3.trans (hpres4.trans (hpres5.trans (hpres6.trans hpres7))))),
      hmem7.trans hm6, ?_⟩
    · rw [run_add, hrun1]; dsimp only
      rw [run_add, run_one_cont _ _ st2 (by rw [hsSrl]; rfl)]; dsimp only
      rw [run_add, hrun3]; dsimp only
      rw [run_add, hrun4]; dsimp only
      rw [run_add, run_one_cont _ _ st5 (by rw [hsSll]; rfl)]; dsimp only
      rw [run_add, run_one_cont _ _ st6 (by rw [hsAdd]; rfl)]; dsimp only
      exact hrun7
    · rw [hpc7, htw6, htw4]
      change BitVec.ofNat 64 (4 * _) = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (clen ++ [Asm.srli AbiReg.t3 ri 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++ cbase ++ ctail)))
      rw [htw_all]; congr 2; omega
    · exact (hoth7 AbiReg.t4 (hrd.ne_temp (by decide)).symm).trans
        ((getReg_stepReg_ne st5 AbiReg.t1 AbiReg.t4 (by decide) _ _).trans
          ((getReg_stepReg_ne st4 AbiReg.t3 AbiReg.t4 (by decide) _ _).trans
            ((hoth4 AbiReg.t4 (by decide) (by decide)).trans
              ((hoth3 AbiReg.t4 (by decide)).trans
                ((getReg_stepReg_ne st1 AbiReg.t3 AbiReg.t4 (by decide) _ _).trans
                  (hoth1 AbiReg.t4 (by decide) (by decide)))))))
  · next hbound =>
    have hbound' : ¬(vi.toNat / 2 < (lm.arr64 s).size) := hbound
    have hcondT : evalBranch .bgeu (st2.getReg AbiReg.t3) (st2.getReg AbiReg.t2) = true := by
      have hdvlt : vi.toNat / 2 < 2 ^ 64 := by have := vi.toBitVec.isLt; rw [UInt64.toNat_toBitVec] at this; omega
      have hdivEq : (vi / 2).toNat = vi.toNat / 2 := rfl
      simp [evalBranch, ht3_2, ht2_2, hdivEq]
      rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hdvlt, Nat.mod_eq_of_lt (by omega : (lm.arr64 s).size < 2 ^ 64),
          decide_eq_false hbound']
    obtain ⟨kBr, st3, hrun3, hpc3', hoth3, _, hmem3⟩ :=
      prog_step_br_taken env (pre ++ clen ++ csrl) (cbase ++ ctail ++ post)
        .bgeu AbiReg.t3 AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide)
        hlinkBr h64Br st2 hpc2 hcondT
    exact ⟨lkm.totalSize clen + (1 + kBr), st3,
      by rw [run_add, hrun1]; dsimp only; rw [run_add, run_one_cont _ _ st2 (by rw [hsSrl]; rfl)]; dsimp only; exact hrun3,
      hpc3', hpres1.trans (hpres2.trans (PreservedFrameRegs.of_t6_s1 hoth3)),
      by rw [hmem3, mem_stepReg, hmem1]⟩

/-- Constant-index (`vi.toNat < 512`) 32-bit packed tiered load body using immediate offset `4 * vi.toNat`. -/
theorem reg_ld32t_const_body_r {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout)
    (lm : _root_.L.Mem) (s : TieredArray) (hsOk : env.tab.wordPosOkB s = true)
    (pre post : List AsmItem)
    (rd ri lenBase baseBase : Reg)
    (hrd : ValidTargetReg fl rd)
    (hri : ri = AbiReg.zero ∨ ri = AbiReg.a0 ∨ ri ∈ allowedRegs true)
    (hLenBase3 : lenBase ≠ AbiReg.t3)
    (hBaseBase2 : baseBase ≠ AbiReg.t2) (hBaseBase3 : baseBase ≠ AbiReg.t3) (hBaseBaseT6 : baseBase ≠ AbiReg.t6 ∧ baseBase ≠ AbiReg.s1)
    (lenOff baseOff : Int) (vi : _root_.L.Word) (hviLt : vi.toNat < 512)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hlenAddr : st.getReg lenBase + BitVec.ofInt 64 lenOff = L.T + BitVec.ofInt 64 (env.tab.len64 s))
    (hbaseAddr : st.getReg baseBase + BitVec.ofInt 64 baseOff = L.T + BitVec.ofInt 64 (env.tab.base64 s))
    (hriVal : st.getReg ri = vi.toBitVec)
    (hmemRel : ProgMemRel env.tab L st.mem lm)
    (hlink : lkm.linkSpec (pre ++
        (loadMemOff .ld AbiReg.t2 lenBase AbiReg.t3 lenOff ++
         [Asm.srli AbiReg.t3 ri 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
         loadMemOff .ld AbiReg.t1 baseBase AbiReg.t3 baseOff ++
         [Asm.lwu rd AbiReg.t1 (BitVec.ofNat 12 (4 * vi.toNat))]) ++ post) =
        .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize
        (loadMemOff .ld AbiReg.t2 lenBase AbiReg.t3 lenOff ++
         [Asm.srli AbiReg.t3 ri 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
         loadMemOff .ld AbiReg.t1 baseBase AbiReg.t3 baseOff ++
         [Asm.lwu rd AbiReg.t1 (BitVec.ofNat 12 (4 * vi.toNat))])) < 2 ^ 64) :
    let code :=
      loadMemOff .ld AbiReg.t2 lenBase AbiReg.t3 lenOff ++
      [Asm.srli AbiReg.t3 ri 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 baseBase AbiReg.t3 baseOff ++
      [Asm.lwu rd AbiReg.t1 (BitVec.ofNat 12 (4 * vi.toNat))]
    if h : (vi / 2).toNat < (lm.arr64 s).size then
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize code)) ∧
        st'.getReg rd = (half32 ((lm.arr64 s)[(vi / 2).toNat]'h) vi).toBitVec ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        st'.mem = st.mem ∧
        st'.getReg AbiReg.t4 = st.getReg AbiReg.t4
    else
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        st'.mem = st.mem := by
  have hriT2 : ri ≠ AbiReg.t2 := idxReg_ne_temp hri (by decide)
  have hriT3 : ri ≠ AbiReg.t3 := idxReg_ne_temp hri (by decide)
  let clen := loadMemOff .ld AbiReg.t2 lenBase AbiReg.t3 lenOff
  let csrl := [Asm.srli AbiReg.t3 ri 1#6]
  let cbr := [Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel]
  let cbase := loadMemOff .ld AbiReg.t1 baseBase AbiReg.t3 baseOff
  let off12 : BitVec 12 := BitVec.ofNat 12 (4 * vi.toNat)
  let ctail := [Asm.lwu rd AbiReg.t1 off12]
  have htw_tail : lkm.totalSize ctail = 1 := by simp [ctail, Asm.lwu, lkm.totalSize_instr]
  have htw_all : lkm.totalSize (clen ++ [Asm.srli AbiReg.t3 ri 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++ cbase ++ ctail) =
      lkm.totalSize clen + 1 + lkm.totalSize cbr + lkm.totalSize cbase + 1 := by
    have hsplit : [Asm.srli AbiReg.t3 ri 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] = csrl ++ cbr := rfl
    rw [hsplit]; simp only [lkm.totalSize_append, htw_tail, csrl, Asm.srli, lkm.totalSize_instr]; omega
  have h64' : 4 * (lkm.totalSize pre + (lkm.totalSize clen + 1 + lkm.totalSize cbr + lkm.totalSize cbase + 1)) < 2 ^ 64 := by
    rw [← htw_all]; exact h64
  rcases hmemRel.2.1 s hsOk with ⟨_, hlt61, hlenR, hbaseR, hwordsR⟩
  have halLen : isAligned (st.getReg lenBase + BitVec.ofInt 64 lenOff) 8 = true := by
    rw [hlenAddr, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
  obtain ⟨st1, hrun1, hoth1, ht2_1, hmem1, hpc1⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre (csrl ++ cbr ++ cbase ++ ctail ++ post)
      AbiReg.t2 lenBase AbiReg.t3 (by decide) (by decide) hLenBase3 lenOff
      (by simpa only [clen, csrl, cbr, cbase, ctail, off12, List.append_assoc, List.cons_append, List.nil_append] using hlink)
      (by dsimp only [clen] at h64'; omega) st hpc halLen
  have hpres1 : PreservedFrameRegs fl (· = rd) st st1 :=
    PreservedFrameRegs.of_scratch2 AbiReg.t2 AbiReg.t3 (by decide) (by decide) hoth1
  have htw1 : lkm.totalSize (pre ++ clen) = lkm.totalSize pre + lkm.totalSize clen := lkm.totalSize_append _ _
  have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ clen)) := by rw [htw1]; exact hpc1
  have hri1 : st1.getReg ri = vi.toBitVec := (hoth1 ri hriT2 hriT3).trans hriVal
  have ht2_1' : st1.getReg AbiReg.t2 = BitVec.ofNat 64 (lm.arr64 s).size := by rw [ht2_1, hlenAddr, hlenR]
  have hbaseReg1 : st1.getReg baseBase = st.getReg baseBase := hoth1 baseBase hBaseBase2 hBaseBase3
  have hsSrl := step_item_instr_lm lkm env.hrom (pre ++ clen) (cbr ++ cbase ++ ctail ++ post)
    (.shImm .srli AbiReg.t3 ri 1#6)
    (by simpa only [clen, csrl, cbr, cbase, ctail, off12, Asm.srli, List.append_assoc, List.cons_append, List.nil_append] using hlink)
    (by rw [htw1]; omega) st1 hpc1'
  let st2 := stepReg st1 AbiReg.t3 (st1.getReg ri >>> 1) (st1.pc + 4#64)
  have hpres2 : PreservedFrameRegs fl (· = rd) st1 st2 :=
    PreservedFrameRegs.of_scratch1 AbiReg.t3 (by decide) (fun r hr => getReg_stepReg_ne st1 AbiReg.t3 r hr _ _)
  have htw2 : lkm.totalSize (pre ++ clen ++ csrl) = lkm.totalSize pre + lkm.totalSize clen + 1 := by
    rw [lkm.totalSize_append, htw1]; simp only [csrl, Asm.srli, lkm.totalSize_instr]
  have hpc2 : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ clen ++ csrl)) := by
    change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1', htw2, htw1]
  have ht3_2 : st2.getReg AbiReg.t3 = BitVec.ofNat 64 (vi / 2).toNat := by
    change (stepReg st1 AbiReg.t3 _ _).getReg AbiReg.t3 = _
    rw [getReg_stepReg_eq _ _ (by decide), hri1]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, UInt64.toNat_toBitVec]
    change vi.toNat >>> 1 = _
    rw [Nat.shiftRight_eq_div_pow]; simp only [Nat.pow_one]
    have hvit : vi.toNat < 2 ^ 64 := vi.toBitVec.isLt
    rw [BitVec.toNat_ofNat, show (vi / 2).toNat = vi.toNat / 2 from rfl, Nat.mod_eq_of_lt (by omega)]
  have ht2_2 : st2.getReg AbiReg.t2 = BitVec.ofNat 64 (lm.arr64 s).size :=
    (getReg_stepReg_ne st1 AbiReg.t3 AbiReg.t2 (by decide) _ _).trans ht2_1'
  have hlinkBr : lkm.linkSpec ((pre ++ clen ++ csrl) ++ [.br .bgeu AbiReg.t3 AbiReg.t2 errLabel] ++ (cbase ++ ctail ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [clen, csrl, cbr, cbase, ctail, off12, Asm.bgeu, List.append_assoc, List.cons_append, List.nil_append] using hlink
  have h64Br : 4 * (lkm.totalSize (pre ++ clen ++ csrl) + lkm.itemSize (.br .bgeu AbiReg.t3 AbiReg.t2 errLabel)) < 2 ^ 64 := by
    rw [htw2]
    have : lkm.itemSize (.br .bgeu AbiReg.t3 AbiReg.t2 errLabel) = lkm.totalSize cbr := by simp [cbr, Asm.bgeu, lkm.totalSize_singleton]
    omega
  split
  · next hbound =>
    have hbound' : vi.toNat / 2 < (lm.arr64 s).size := hbound
    have hcondF : evalBranch .bgeu (st2.getReg AbiReg.t3) (st2.getReg AbiReg.t2) = false := by
      have hdvlt : vi.toNat / 2 < 2 ^ 64 := by have := vi.toBitVec.isLt; omega
      simp [evalBranch, ht3_2, ht2_2]
      rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hdvlt, Nat.mod_eq_of_lt (by omega : (lm.arr64 s).size < 2 ^ 64),
          decide_eq_true hbound']
    obtain ⟨kBr, st3, hrun3, hpc3', hoth3, _, hmem3⟩ :=
      prog_step_br_fall env (pre ++ clen ++ csrl) (cbase ++ ctail ++ post)
        .bgeu AbiReg.t3 AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide)
        hlinkBr h64Br st2 hpc2 hcondF
    have hpres3 : PreservedFrameRegs fl (· = rd) st2 st3 :=
      PreservedFrameRegs.of_t6_s1 hoth3
    have htw3 : lkm.totalSize (pre ++ clen ++ csrl ++ cbr) =
        lkm.totalSize pre + lkm.totalSize clen + 1 + lkm.totalSize cbr := by
      rw [lkm.totalSize_append, htw2]
    have hpc3 : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ clen ++ csrl ++ cbr)) := by
      rw [hpc3', htw3, htw2]; rfl
    have hbaseReg3 : st3.getReg baseBase = st.getReg baseBase :=
      (hoth3 baseBase hBaseBaseT6).trans ((getReg_stepReg_ne st1 AbiReg.t3 baseBase hBaseBase3 _ _).trans hbaseReg1)
    have halBase : isAligned (st3.getReg baseBase + BitVec.ofInt 64 baseOff) 8 = true := by
      rw [hbaseReg3, hbaseAddr, Tab.base64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨st4, hrun4, hoth4, ht1_4, hmem4, hpc4⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom (pre ++ clen ++ csrl ++ cbr) (ctail ++ post)
        AbiReg.t1 baseBase AbiReg.t3 (by decide) (by decide) hBaseBase3 baseOff
        (by simpa only [clen, csrl, cbr, cbase, ctail, off12, List.append_assoc, List.cons_append, List.nil_append] using hlink)
        (by rw [htw3]; dsimp only [cbase] at h64'; omega) st3 hpc3 halBase
    have hpres4 : PreservedFrameRegs fl (· = rd) st3 st4 :=
      PreservedFrameRegs.of_scratch2 AbiReg.t1 AbiReg.t3 (by decide) (by decide) hoth4
    let p4 := pre ++ clen ++ csrl ++ cbr ++ cbase
    have htw4 : lkm.totalSize p4 = lkm.totalSize pre + lkm.totalSize clen + 1 + lkm.totalSize cbr + lkm.totalSize cbase := by
      dsimp only [p4]; rw [lkm.totalSize_append, htw3]
    have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize p4) := by rw [htw4, ← htw3]; exact hpc4
    have ht1_4' : st4.getReg AbiReg.t1 = L.base64 s := by
      rw [ht1_4, hmem3, mem_stepReg, hmem1, hbaseReg3, hbaseAddr, hbaseR]
    have hsext : sextImm12 off12 = BitVec.ofNat 64 (4 * vi.toNat) := sextImm12_ofNat_lt (4 * vi.toNat) (by omega)
    have hal4 : isAligned (st4.getReg AbiReg.t1 + sextImm12 off12) 4 = true := by
      rw [ht1_4', hsext]; exact isAligned4_add_mul4 (L.base64 s) (L.h64Align s) vi.toNat
    let st5 := stepReg st4 rd ((loadBytes st4.mem (st4.getReg AbiReg.t1 + sextImm12 off12) 4).zeroExtend 64) (st4.pc + 4#64)
    obtain ⟨hrun5, hpc5, hrd5, hoth5, hmem5⟩ :=
      step_lwu_off_r env p4 post rd AbiReg.t1 off12 hrd.ne_zero
        (by simpa only [p4, clen, csrl, cbr, cbase, ctail, off12, Asm.lwu, Asm.raw,
            List.append_assoc, List.cons_append, List.nil_append] using hlink)
        (by rw [htw4]; omega) st4 hpc4' hal4
    have hpres5 : PreservedFrameRegs fl (· = rd) st4 st5 :=
      PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) hoth5
    have hm4 : st4.mem = st.mem := by rw [hmem4, hmem3, mem_stepReg, hmem1]
    have hrd5' : st5.getReg rd = (half32 ((lm.arr64 s)[(vi / 2).toNat]) vi).toBitVec := by
      rw [hrd5, hm4, ht1_4', hsext]
      have hw := hwordsR (vi / 2).toNat hbound
      have him : (vi % 2).toNat = vi.toNat % 2 := by
        rw [UInt64.toNat_mod, show (2 : UInt64).toNat = 2 from rfl]
      by_cases hev : vi % 2 = 0
      · have hmod0 : vi.toNat % 2 = 0 := by rw [← him, hev]; rfl
        have h48 : 4 * vi.toNat = 8 * (vi / 2).toNat := by
          have : (vi / 2).toNat = vi.toNat / 2 := rfl; omega
        rw [h48, loadBytes_zeroExtend32_lo, hw]
        simp only [half32, hev, ↓reduceIte, UInt64.toNat_toBitVec, UInt64.ofNat_toNat]
      · have hmod1 : vi.toNat % 2 = 1 := by
          have hne0 : vi.toNat % 2 ≠ 0 := fun h0 => hev (UInt64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (by
            rw [UInt64.toNat_toBitVec, him, h0]; rfl)))
          omega
        have h48 : L.base64 s + BitVec.ofNat 64 (4 * vi.toNat) =
            (L.base64 s + BitVec.ofNat 64 (8 * (vi / 2).toNat)) + 4#64 := by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 1
          have : (vi / 2).toNat = vi.toNat / 2 := rfl
          rw [show 4 * vi.toNat = 8 * (vi / 2).toNat + 4 by omega]
        rw [h48, loadBytes_zeroExtend32_hi, hw]
        simp only [half32, hev, ↓reduceIte, UInt64.toNat_toBitVec, UInt64.ofNat_toNat]
        apply BitVec.eq_of_toNat_eq
        simp only [UInt64.toNat_toBitVec, UInt64.toNat_shiftRight, UInt64.toNat_div,
          show (32 : UInt64).toNat % 64 = 32 from rfl, show (4294967296 : UInt64).toNat = 2 ^ 32 from rfl,
          Nat.shiftRight_eq_div_pow]
    refine ⟨lkm.totalSize clen + (1 + (kBr + (lkm.totalSize cbase + 1))), st5, ?_, ?_, hrd5',
      hpres1.trans (hpres2.trans (hpres3.trans (hpres4.trans hpres5))), hmem5.trans hm4, ?_⟩
    · rw [run_add, hrun1]; dsimp only
      rw [run_add, run_one_cont _ _ st2 (by rw [hsSrl]; rfl)]; dsimp only
      rw [run_add, hrun3]; dsimp only
      rw [run_add, hrun4]; dsimp only
      exact hrun5
    · rw [hpc5, htw4]
      change BitVec.ofNat 64 (4 * _) = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (clen ++ [Asm.srli AbiReg.t3 ri 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++ cbase ++ ctail)))
      rw [htw_all]; congr 2; omega
    · exact (hoth5 AbiReg.t4 (hrd.ne_temp (by decide)).symm).trans
        ((hoth4 AbiReg.t4 (by decide) (by decide)).trans
          ((hoth3 AbiReg.t4 (by decide)).trans
            ((getReg_stepReg_ne st1 AbiReg.t3 AbiReg.t4 (by decide) _ _).trans
              (hoth1 AbiReg.t4 (by decide) (by decide)))))
  · next hbound =>
    have hbound' : ¬(vi.toNat / 2 < (lm.arr64 s).size) := hbound
    have hcondT : evalBranch .bgeu (st2.getReg AbiReg.t3) (st2.getReg AbiReg.t2) = true := by
      have hdvlt : vi.toNat / 2 < 2 ^ 64 := by have := vi.toBitVec.isLt; rw [UInt64.toNat_toBitVec] at this; omega
      have hdivEq : (vi / 2).toNat = vi.toNat / 2 := rfl
      simp [evalBranch, ht3_2, ht2_2, hdivEq]
      rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hdvlt, Nat.mod_eq_of_lt (by omega : (lm.arr64 s).size < 2 ^ 64),
          decide_eq_false hbound']
    obtain ⟨kBr, st3, hrun3, hpc3', hoth3, _, hmem3⟩ :=
      prog_step_br_taken env (pre ++ clen ++ csrl) (cbase ++ ctail ++ post)
        .bgeu AbiReg.t3 AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide)
        hlinkBr h64Br st2 hpc2 hcondT
    exact ⟨lkm.totalSize clen + (1 + kBr), st3,
      by rw [run_add, hrun1]; dsimp only; rw [run_add, run_one_cont _ _ st2 (by rw [hsSrl]; rfl)]; dsimp only; exact hrun3,
      hpc3', hpres1.trans (hpres2.trans (PreservedFrameRegs.of_t6_s1 hoth3)),
      by rw [hmem3, mem_stepReg, hmem1]⟩

/-- Shared body for 32-bit halfword loads (`ld32h`, plain & tiered). -/
theorem reg_ld32h_body_r {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout)
    (lm : _root_.L.Mem) (s : TieredArray) (hsOk : env.tab.wordPosOkB s = true) (hi : Bool)
    (pre post : List AsmItem)
    (rd ri lenBase baseBase rLen rTmpLen rBase rTmpBase : Reg)
    (hrd : ValidTargetReg fl rd)
    (hri : ri = AbiReg.zero ∨ ri = AbiReg.a0 ∨ ri ∈ allowedRegs true)
    (hrLen : rLen ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3])
    (hrTmpLen : rTmpLen ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3])
    (hrBase : rBase ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3])
    (hrTmpBase : rTmpBase ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3])
    (hBaseTmp : rBase ≠ rTmpBase)
    (hLenBaseTmpLen : lenBase ≠ rTmpLen)
    (hBaseBaseLen : baseBase ≠ rLen)
    (hBaseBaseTmpLen : baseBase ≠ rTmpLen)
    (hBaseBaseTmpBase : baseBase ≠ rTmpBase)
    (hBaseBaseT6 : baseBase ≠ AbiReg.t6 ∧ baseBase ≠ AbiReg.s1)
    (lenOff baseOff : Int) (vi : _root_.L.Word)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hlenAddr : st.getReg lenBase + BitVec.ofInt 64 lenOff = L.T + BitVec.ofInt 64 (env.tab.len64 s))
    (hbaseAddr : st.getReg baseBase + BitVec.ofInt 64 baseOff = L.T + BitVec.ofInt 64 (env.tab.base64 s))
    (hriVal : st.getReg ri = vi.toBitVec)
    (hmemRel : ProgMemRel env.tab L st.mem lm)
    (hlink : lkm.linkSpec (pre ++
        (loadMemOff .ld rLen lenBase rTmpLen lenOff ++
         [Asm.bgeu ri rLen errLabel] ++
         loadMemOff .ld rBase baseBase rTmpBase baseOff ++
         [Asm.slli rTmpBase ri 3#6, Asm.add rBase rBase rTmpBase,
          Asm.lwu rd rBase (if hi then 4#12 else 0#12)]) ++ post) =
        .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize
        (loadMemOff .ld rLen lenBase rTmpLen lenOff ++
         [Asm.bgeu ri rLen errLabel] ++
         loadMemOff .ld rBase baseBase rTmpBase baseOff ++
         [Asm.slli rTmpBase ri 3#6, Asm.add rBase rBase rTmpBase,
          Asm.lwu rd rBase (if hi then 4#12 else 0#12)])) < 2 ^ 64) :
    let code :=
      loadMemOff .ld rLen lenBase rTmpLen lenOff ++
      [Asm.bgeu ri rLen errLabel] ++
      loadMemOff .ld rBase baseBase rTmpBase baseOff ++
      [Asm.slli rTmpBase ri 3#6, Asm.add rBase rBase rTmpBase,
       Asm.lwu rd rBase (if hi then 4#12 else 0#12)]
    if h : vi.toNat < (lm.arr64 s).size then
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize code)) ∧
        st'.getReg rd = (half32b hi ((lm.arr64 s)[vi.toNat]'h)).toBitVec ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        st'.mem = st.mem ∧
        st'.getReg AbiReg.t4 = st.getReg AbiReg.t4
    else
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        st'.mem = st.mem := by
  have hmemScr : ∀ r, r ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3] →
      r ∈ scratchRegs ∧ r ≠ AbiReg.zero ∧ r ≠ AbiReg.t6 ∧ r ≠ AbiReg.t4 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide, by decide⟩
  have ⟨hrLenS, hrLen0, hrLenT6, hrLenT4⟩ := hmemScr rLen hrLen
  have ⟨hrTmpLenS, hrTmpLen0, _, hrTmpLenT4⟩ := hmemScr rTmpLen hrTmpLen
  have ⟨hrBaseS, hrBase0, _, hrBaseT4⟩ := hmemScr rBase hrBase
  have ⟨hrTmpBaseS, hrTmpBase0, _, hrTmpBaseT4⟩ := hmemScr rTmpBase hrTmpBase
  have hriT6 : ri ≠ AbiReg.t6 := idxReg_ne_temp hri (by decide)
  have hriLen : ri ≠ rLen := idxReg_ne_temp hri (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrLen ⊢
    rcases hrLen with rfl | rfl | rfl | rfl <;> simp)
  have hriTmpLen : ri ≠ rTmpLen := idxReg_ne_temp hri (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrTmpLen ⊢
    rcases hrTmpLen with rfl | rfl | rfl | rfl <;> simp)
  have hriBase : ri ≠ rBase := idxReg_ne_temp hri (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrBase ⊢
    rcases hrBase with rfl | rfl | rfl | rfl <;> simp)
  have hriTmpBase : ri ≠ rTmpBase := idxReg_ne_temp hri (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrTmpBase ⊢
    rcases hrTmpBase with rfl | rfl | rfl | rfl <;> simp)
  let offImm : BitVec 12 := if hi then 4#12 else 0#12
  let clen := loadMemOff .ld rLen lenBase rTmpLen lenOff
  let cbr := [Asm.bgeu ri rLen errLabel]
  let cbase := loadMemOff .ld rBase baseBase rTmpBase baseOff
  let ctail := [Asm.slli rTmpBase ri 3#6, Asm.add rBase rBase rTmpBase, Asm.lwu rd rBase offImm]
  have htw_tail : lkm.totalSize ctail = 3 := by
    simp [ctail, Asm.slli, Asm.add, Asm.lwu, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
  have htw_all : lkm.totalSize (clen ++ cbr ++ cbase ++ ctail) =
      lkm.totalSize clen + lkm.totalSize cbr + lkm.totalSize cbase + 3 := by
    simp only [lkm.totalSize_append, htw_tail]
  have h64' : 4 * (lkm.totalSize pre + (lkm.totalSize clen + lkm.totalSize cbr + lkm.totalSize cbase + 3)) < 2 ^ 64 := by
    rw [← htw_all]; exact h64
  rcases hmemRel.2.1 s hsOk with ⟨_, hlt61, hlenR, hbaseR, hwordsR⟩
  have halLen : isAligned (st.getReg lenBase + BitVec.ofInt 64 lenOff) 8 = true := by
    rw [hlenAddr, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
  obtain ⟨st1, hrun1, hoth1, hrLen1, hmem1, hpc1⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre (cbr ++ cbase ++ ctail ++ post)
      rLen lenBase rTmpLen hrLen0 hrTmpLen0 hLenBaseTmpLen lenOff
      (by simpa only [clen, cbr, cbase, ctail, offImm, List.append_assoc] using hlink)
      (by dsimp only [clen] at h64'; omega) st hpc halLen
  have hpres1 : PreservedFrameRegs fl (· = rd) st st1 :=
    PreservedFrameRegs.of_scratch2 rLen rTmpLen hrLenS hrTmpLenS hoth1
  have htw1 : lkm.totalSize (pre ++ clen) = lkm.totalSize pre + lkm.totalSize clen := lkm.totalSize_append _ _
  have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ clen)) := by rw [htw1]; exact hpc1
  have hri1 : st1.getReg ri = vi.toBitVec := (hoth1 ri hriLen hriTmpLen).trans hriVal
  have hrLen1' : st1.getReg rLen = BitVec.ofNat 64 (lm.arr64 s).size := by rw [hrLen1, hlenAddr, hlenR]
  have hbaseReg1 : st1.getReg baseBase = st.getReg baseBase := hoth1 baseBase hBaseBaseLen hBaseBaseTmpLen
  have hlinkBr : lkm.linkSpec ((pre ++ clen) ++ [.br .bgeu ri rLen errLabel] ++ (cbase ++ ctail ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [clen, cbr, cbase, ctail, offImm, Asm.bgeu, List.append_assoc] using hlink
  have h64Br : 4 * (lkm.totalSize (pre ++ clen) + lkm.itemSize (.br .bgeu ri rLen errLabel)) < 2 ^ 64 := by
    rw [htw1]
    have : lkm.itemSize (.br .bgeu ri rLen errLabel) = lkm.totalSize cbr := by simp [cbr, Asm.bgeu, lkm.totalSize_singleton]
    omega
  by_cases hbound : vi.toNat < (lm.arr64 s).size
  · simp only [hbound, ↓reduceDIte]
    have hcondF : evalBranch .bgeu (st1.getReg ri) (st1.getReg rLen) = false := by
      simp [evalBranch, hri1, hrLen1']
      rw [BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
          Nat.mod_eq_of_lt (by omega : (lm.arr64 s).size < 2 ^ 64), decide_eq_true hbound]
    obtain ⟨kBr, st2, hrun2, hpc2', hoth2, _, hmem2⟩ :=
      prog_step_br_fall env (pre ++ clen) (cbase ++ ctail ++ post)
        .bgeu ri rLen errLabel env.errTarget env.herrLbl ⟨hriT6, hrLenT6⟩
        hlinkBr h64Br st1 hpc1' hcondF
    have hpres2 : PreservedFrameRegs fl (· = rd) st1 st2 :=
      PreservedFrameRegs.of_t6_s1 hoth2
    have htw2 : lkm.totalSize (pre ++ clen ++ cbr) = lkm.totalSize pre + lkm.totalSize clen + lkm.totalSize cbr := by
      rw [lkm.totalSize_append, htw1]
    have hpc2 : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ clen ++ cbr)) := by
      rw [hpc2', htw2, htw1]; rfl
    have hbaseReg2 : st2.getReg baseBase = st.getReg baseBase := (hoth2 baseBase hBaseBaseT6).trans hbaseReg1
    have halBase : isAligned (st2.getReg baseBase + BitVec.ofInt 64 baseOff) 8 = true := by
      rw [hbaseReg2, hbaseAddr, Tab.base64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨st3, hrun3, hoth3, hrBase3, hmem3, hpc3⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom (pre ++ clen ++ cbr) (ctail ++ post)
        rBase baseBase rTmpBase hrBase0 hrTmpBase0 hBaseBaseTmpBase baseOff
        (by simpa only [clen, cbr, cbase, ctail, offImm, List.append_assoc] using hlink)
        (by rw [htw2]; dsimp only [cbase] at h64'; omega) st2 hpc2 halBase
    have hpres3 : PreservedFrameRegs fl (· = rd) st2 st3 :=
      PreservedFrameRegs.of_scratch2 rBase rTmpBase hrBaseS hrTmpBaseS hoth3
    let p3 := pre ++ clen ++ cbr ++ cbase
    have htw3 : lkm.totalSize p3 = lkm.totalSize pre + lkm.totalSize clen + lkm.totalSize cbr + lkm.totalSize cbase := by
      dsimp only [p3]; rw [lkm.totalSize_append, htw2]
    have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize p3) := by rw [htw3, ← htw2]; exact hpc3
    have hsSll := step_item_instr_lm lkm env.hrom p3
      ([Asm.add rBase rBase rTmpBase, Asm.lwu rd rBase offImm] ++ post)
      (.shImm .slli rTmpBase ri 3#6)
      (by simpa only [p3, clen, cbr, cbase, ctail, offImm, Asm.slli, List.append_assoc, List.cons_append, List.nil_append] using hlink)
      (by rw [htw3]; omega) st3 hpc3'
    let st4 := stepReg st3 rTmpBase (st3.getReg ri <<< 3) (st3.pc + 4#64)
    have hpres4 : PreservedFrameRegs fl (· = rd) st3 st4 :=
      PreservedFrameRegs.of_scratch1 rTmpBase hrTmpBaseS (fun r hr => getReg_stepReg_ne st3 rTmpBase r hr _ _)
    have htw4 : lkm.totalSize (p3 ++ [Asm.slli rTmpBase ri 3#6]) = lkm.totalSize p3 + 1 := by
      rw [lkm.totalSize_append, Asm.slli, lkm.totalSize_instr]
    have hpc4 : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p3 ++ [Asm.slli rTmpBase ri 3#6])) := by
      change st3.pc + 4#64 = _; rw [pc_add_4_ofNat st3.pc hpc3', htw4]
    have hsAdd := step_item_instr_lm lkm env.hrom (p3 ++ [Asm.slli rTmpBase ri 3#6])
      ([Asm.lwu rd rBase offImm] ++ post) (.alu .add rBase rBase rTmpBase)
      (by simpa only [p3, clen, cbr, cbase, ctail, offImm, Asm.slli, Asm.add, List.append_assoc, List.cons_append, List.nil_append] using hlink)
      (by rw [htw4, htw3]; omega) st4 hpc4
    let st5 := stepReg st4 rBase (st4.getReg rBase + st4.getReg rTmpBase) (st4.pc + 4#64)
    have hpres5 : PreservedFrameRegs fl (· = rd) st4 st5 :=
      PreservedFrameRegs.of_scratch1 rBase hrBaseS (fun r hr => getReg_stepReg_ne st4 rBase r hr _ _)
    have htw5 : lkm.totalSize (p3 ++ [Asm.slli rTmpBase ri 3#6] ++ [Asm.add rBase rBase rTmpBase]) =
        lkm.totalSize p3 + 2 := by
      rw [lkm.totalSize_append, htw4, Asm.add, lkm.totalSize_instr]
    have hpc5 : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p3 ++ [Asm.slli rTmpBase ri 3#6] ++
        [Asm.add rBase rBase rTmpBase])) := by
      change st4.pc + 4#64 = _; rw [pc_add_4_ofNat st4.pc hpc4, htw5, htw4]
    have hrBase5 : st5.getReg rBase = L.base64 s + BitVec.ofNat 64 (8 * vi.toNat) := by
      have hb3 : st3.getReg rBase = L.base64 s := by
        rw [hrBase3, hmem2, hmem1, hbaseReg2, hbaseAddr, hbaseR]
      have hri3 : st3.getReg ri = vi.toBitVec := (hoth3 ri hriBase hriTmpBase).trans ((hoth2 ri ⟨hriT6, idxReg_ne_s1 hri⟩).trans hri1)
      have htmp4 : st4.getReg rTmpBase = BitVec.ofNat 64 (8 * vi.toNat) := by
        change (stepReg st3 rTmpBase _ _).getReg rTmpBase = _
        rw [getReg_stepReg_eq _ _ hrTmpBase0, hri3]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_shiftLeft, UInt64.toNat_toBitVec, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
        rw [show (2 ^ 3 : Nat) = 8 from rfl, Nat.mul_comm _ 8, Nat.mod_eq_of_lt (by omega)]
      have hb4 : st4.getReg rBase = L.base64 s :=
        (getReg_stepReg_ne st3 rTmpBase rBase hBaseTmp _ _).trans hb3
      change (stepReg st4 rBase _ _).getReg rBase = _
      rw [getReg_stepReg_eq _ _ hrBase0, hb4, htmp4]
    have hal5 : isAligned (st5.getReg rBase + sextImm12 offImm) 4 = true := by
      rw [hrBase5]
      cases hi
      · simp only [offImm, Bool.false_eq_true, ↓reduceIte, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero]
        exact isAligned4_of_isAligned8 _ (isAligned8_add_mul8 (L.base64 s) (L.h64Align s) vi.toNat)
      · simp only [offImm, ↓reduceIte, show sextImm12 4#12 = 4#64 from rfl]
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * vi.toNat + 4 = 4 * (2 * vi.toNat + 1) by omega]
        exact isAligned4_add_mul4 (L.base64 s) (L.h64Align s) (2 * vi.toNat + 1)
    let st6 := stepReg st5 rd ((loadBytes st5.mem (st5.getReg rBase + sextImm12 offImm) 4).zeroExtend 64) (st5.pc + 4#64)
    obtain ⟨hrun6, hpc6, hrd6, hoth6, hmem6⟩ :=
      step_lwu_off_r env (p3 ++ [Asm.slli rTmpBase ri 3#6] ++ [Asm.add rBase rBase rTmpBase])
        post rd rBase offImm hrd.ne_zero
        (by simpa only [p3, clen, cbr, cbase, ctail, offImm, Asm.lwu, Asm.raw, Asm.add, Asm.slli,
            List.append_assoc, List.cons_append, List.nil_append] using hlink)
        (by rw [htw5, htw3]; omega) st5 hpc5 hal5
    have hpres6 : PreservedFrameRegs fl (· = rd) st5 st6 :=
      PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) hoth6
    have hm5 : st5.mem = st.mem := by
      dsimp only [st5, st4]; rw [mem_stepReg, mem_stepReg, hmem3, hmem2, hmem1]
    have hrd6' : st6.getReg rd = (half32b hi ((lm.arr64 s)[vi.toNat])).toBitVec := by
      rw [hrd6, hm5, hrBase5]
      have hw := hwordsR vi.toNat hbound
      cases hi
      · simp only [offImm, Bool.false_eq_true, ↓reduceIte, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero]
        rw [loadBytes_zeroExtend32_lo, hw]
        simp only [half32b, Bool.false_eq_true, ↓reduceIte, UInt64.toNat_toBitVec, UInt64.ofNat_toNat]
        apply BitVec.eq_of_toNat_eq
        simp only [UInt64.toNat_toBitVec, UInt64.toNat_mod, UInt64.toNat_and,
          show (4294967296 : UInt64).toNat = 2 ^ 32 from rfl,
          show (4294967295 : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      · simp only [offImm, ↓reduceIte, show sextImm12 4#12 = 4#64 from rfl]
        rw [loadBytes_zeroExtend32_hi, hw]
        simp only [half32b, ↓reduceIte, UInt64.toNat_toBitVec, UInt64.ofNat_toNat]
    refine ⟨lkm.totalSize clen + (kBr + (lkm.totalSize cbase + (1 + (1 + 1)))), st6, ?_, ?_, hrd6',
      hpres1.trans (hpres2.trans (hpres3.trans (hpres4.trans (hpres5.trans hpres6)))),
      hmem6.trans hm5, ?_⟩
    · rw [run_add, hrun1]; dsimp only
      rw [run_add, hrun2]; dsimp only
      rw [run_add, hrun3]; dsimp only
      rw [run_add, run_one_cont _ _ st4 (by rw [hsSll]; rfl)]; dsimp only
      rw [run_add, run_one_cont _ _ st5 (by rw [hsAdd]; rfl)]; dsimp only
      exact hrun6
    · rw [hpc6, htw5, htw3]
      change BitVec.ofNat 64 (4 * _) = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (clen ++ cbr ++ cbase ++ ctail)))
      rw [htw_all]; congr 2; omega
    · exact (hoth6 AbiReg.t4 (hrd.ne_temp (by decide)).symm).trans
        ((getReg_stepReg_ne st4 rBase AbiReg.t4 hrBaseT4.symm _ _).trans
          ((getReg_stepReg_ne st3 rTmpBase AbiReg.t4 hrTmpBaseT4.symm _ _).trans
            ((hoth3 AbiReg.t4 hrBaseT4.symm hrTmpBaseT4.symm).trans
              ((hoth2 AbiReg.t4 (by decide)).trans (hoth1 AbiReg.t4 hrLenT4.symm hrTmpLenT4.symm)))))
  · simp only [hbound, ↓reduceDIte]
    have hcondT : evalBranch .bgeu (st1.getReg ri) (st1.getReg rLen) = true := by
      simp [evalBranch, hri1, hrLen1']
      rw [BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
          Nat.mod_eq_of_lt (by omega : (lm.arr64 s).size < 2 ^ 64), decide_eq_false hbound]
    obtain ⟨kBr, st2, hrun2, hpc2', hoth2, _, hmem2⟩ :=
      prog_step_br_taken env (pre ++ clen) (cbase ++ ctail ++ post)
        .bgeu ri rLen errLabel env.errTarget env.herrLbl ⟨hriT6, hrLenT6⟩
        hlinkBr h64Br st1 hpc1' hcondT
    exact ⟨lkm.totalSize clen + kBr, st2,
      by rw [run_add, hrun1]; dsimp only; exact hrun2,
      hpc2', hpres1.trans (PreservedFrameRegs.of_t6_s1 hoth2),
      hmem2.trans hmem1⟩

/-- Constant-index (`vi.toNat < 255`) 32-bit halfword load body using immediate offset `8 * vi + (if hi then 4 else 0)`. -/
theorem reg_ld32h_const_body_r {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout)
    (lm : _root_.L.Mem) (s : TieredArray) (hsOk : env.tab.wordPosOkB s = true) (hi : Bool)
    (pre post : List AsmItem)
    (rd ri lenBase baseBase rLen rTmpLen rBase rTmpBase : Reg)
    (hrd : ValidTargetReg fl rd)
    (hri : ri = AbiReg.zero ∨ ri = AbiReg.a0 ∨ ri ∈ allowedRegs true)
    (hrLen : rLen ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3])
    (hrTmpLen : rTmpLen ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3])
    (hrBase : rBase ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3])
    (hrTmpBase : rTmpBase ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3])
    (hLenBaseTmpLen : lenBase ≠ rTmpLen)
    (hBaseBaseLen : baseBase ≠ rLen)
    (hBaseBaseTmpLen : baseBase ≠ rTmpLen)
    (hBaseBaseTmpBase : baseBase ≠ rTmpBase)
    (hBaseBaseT6 : baseBase ≠ AbiReg.t6 ∧ baseBase ≠ AbiReg.s1)
    (lenOff baseOff : Int) (vi : _root_.L.Word) (hviLt : vi.toNat < 255)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hlenAddr : st.getReg lenBase + BitVec.ofInt 64 lenOff = L.T + BitVec.ofInt 64 (env.tab.len64 s))
    (hbaseAddr : st.getReg baseBase + BitVec.ofInt 64 baseOff = L.T + BitVec.ofInt 64 (env.tab.base64 s))
    (hriVal : st.getReg ri = vi.toBitVec)
    (hmemRel : ProgMemRel env.tab L st.mem lm)
    (hlink : lkm.linkSpec (pre ++
        (loadMemOff .ld rLen lenBase rTmpLen lenOff ++
         [Asm.bgeu ri rLen errLabel] ++
         loadMemOff .ld rBase baseBase rTmpBase baseOff ++
         [Asm.lwu rd rBase (BitVec.ofNat 12 (8 * vi.toNat + if hi then 4 else 0))]) ++ post) =
        .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize
        (loadMemOff .ld rLen lenBase rTmpLen lenOff ++
         [Asm.bgeu ri rLen errLabel] ++
         loadMemOff .ld rBase baseBase rTmpBase baseOff ++
         [Asm.lwu rd rBase (BitVec.ofNat 12 (8 * vi.toNat + if hi then 4 else 0))])) < 2 ^ 64) :
    let code :=
      loadMemOff .ld rLen lenBase rTmpLen lenOff ++
      [Asm.bgeu ri rLen errLabel] ++
      loadMemOff .ld rBase baseBase rTmpBase baseOff ++
      [Asm.lwu rd rBase (BitVec.ofNat 12 (8 * vi.toNat + if hi then 4 else 0))]
    if h : vi.toNat < (lm.arr64 s).size then
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize code)) ∧
        st'.getReg rd = (half32b hi ((lm.arr64 s)[vi.toNat]'h)).toBitVec ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        st'.mem = st.mem ∧
        st'.getReg AbiReg.t4 = st.getReg AbiReg.t4
    else
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        st'.mem = st.mem := by
  have hmemScr : ∀ r, r ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3] →
      r ∈ scratchRegs ∧ r ≠ AbiReg.zero ∧ r ≠ AbiReg.t6 ∧ r ≠ AbiReg.t4 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide, by decide⟩
  have ⟨hrLenS, hrLen0, hrLenT6, hrLenT4⟩ := hmemScr rLen hrLen
  have ⟨hrTmpLenS, hrTmpLen0, _, hrTmpLenT4⟩ := hmemScr rTmpLen hrTmpLen
  have ⟨hrBaseS, hrBase0, _, hrBaseT4⟩ := hmemScr rBase hrBase
  have ⟨hrTmpBaseS, hrTmpBase0, _, hrTmpBaseT4⟩ := hmemScr rTmpBase hrTmpBase
  have hriT6 : ri ≠ AbiReg.t6 := idxReg_ne_temp hri (by decide)
  have hriLen : ri ≠ rLen := idxReg_ne_temp hri (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrLen ⊢
    rcases hrLen with rfl | rfl | rfl | rfl <;> simp)
  have hriTmpLen : ri ≠ rTmpLen := idxReg_ne_temp hri (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrTmpLen ⊢
    rcases hrTmpLen with rfl | rfl | rfl | rfl <;> simp)
  let off12 : BitVec 12 := BitVec.ofNat 12 (8 * vi.toNat + if hi then 4 else 0)
  let clen := loadMemOff .ld rLen lenBase rTmpLen lenOff
  let cbr := [Asm.bgeu ri rLen errLabel]
  let cbase := loadMemOff .ld rBase baseBase rTmpBase baseOff
  let ctail := [Asm.lwu rd rBase off12]
  have htw_tail : lkm.totalSize ctail = 1 := by simp [ctail, Asm.lwu, lkm.totalSize_instr]
  have htw_all : lkm.totalSize (clen ++ cbr ++ cbase ++ ctail) =
      lkm.totalSize clen + lkm.totalSize cbr + lkm.totalSize cbase + 1 := by
    simp only [lkm.totalSize_append, htw_tail]
  have h64' : 4 * (lkm.totalSize pre + (lkm.totalSize clen + lkm.totalSize cbr + lkm.totalSize cbase + 1)) < 2 ^ 64 := by
    rw [← htw_all]; exact h64
  rcases hmemRel.2.1 s hsOk with ⟨_, hlt61, hlenR, hbaseR, hwordsR⟩
  have halLen : isAligned (st.getReg lenBase + BitVec.ofInt 64 lenOff) 8 = true := by
    rw [hlenAddr, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
  obtain ⟨st1, hrun1, hoth1, hrLen1, hmem1, hpc1⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre (cbr ++ cbase ++ ctail ++ post)
      rLen lenBase rTmpLen hrLen0 hrTmpLen0 hLenBaseTmpLen lenOff
      (by simpa only [clen, cbr, cbase, ctail, off12, List.append_assoc] using hlink)
      (by dsimp only [clen] at h64'; omega) st hpc halLen
  have hpres1 : PreservedFrameRegs fl (· = rd) st st1 :=
    PreservedFrameRegs.of_scratch2 rLen rTmpLen hrLenS hrTmpLenS hoth1
  have htw1 : lkm.totalSize (pre ++ clen) = lkm.totalSize pre + lkm.totalSize clen := lkm.totalSize_append _ _
  have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ clen)) := by rw [htw1]; exact hpc1
  have hri1 : st1.getReg ri = vi.toBitVec := (hoth1 ri hriLen hriTmpLen).trans hriVal
  have hrLen1' : st1.getReg rLen = BitVec.ofNat 64 (lm.arr64 s).size := by rw [hrLen1, hlenAddr, hlenR]
  have hbaseReg1 : st1.getReg baseBase = st.getReg baseBase := hoth1 baseBase hBaseBaseLen hBaseBaseTmpLen
  have hlinkBr : lkm.linkSpec ((pre ++ clen) ++ [.br .bgeu ri rLen errLabel] ++ (cbase ++ ctail ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [clen, cbr, cbase, ctail, off12, Asm.bgeu, List.append_assoc] using hlink
  have h64Br : 4 * (lkm.totalSize (pre ++ clen) + lkm.itemSize (.br .bgeu ri rLen errLabel)) < 2 ^ 64 := by
    rw [htw1]
    have : lkm.itemSize (.br .bgeu ri rLen errLabel) = lkm.totalSize cbr := by simp [cbr, Asm.bgeu, lkm.totalSize_singleton]
    omega
  by_cases hbound : vi.toNat < (lm.arr64 s).size
  · simp only [hbound, ↓reduceDIte]
    have hcondF : evalBranch .bgeu (st1.getReg ri) (st1.getReg rLen) = false := by
      simp [evalBranch, hri1, hrLen1']
      rw [BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
          Nat.mod_eq_of_lt (by omega : (lm.arr64 s).size < 2 ^ 64), decide_eq_true hbound]
    obtain ⟨kBr, st2, hrun2, hpc2', hoth2, _, hmem2⟩ :=
      prog_step_br_fall env (pre ++ clen) (cbase ++ ctail ++ post)
        .bgeu ri rLen errLabel env.errTarget env.herrLbl ⟨hriT6, hrLenT6⟩
        hlinkBr h64Br st1 hpc1' hcondF
    have hpres2 : PreservedFrameRegs fl (· = rd) st1 st2 :=
      PreservedFrameRegs.of_t6_s1 hoth2
    have htw2 : lkm.totalSize (pre ++ clen ++ cbr) = lkm.totalSize pre + lkm.totalSize clen + lkm.totalSize cbr := by
      rw [lkm.totalSize_append, htw1]
    have hpc2 : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ clen ++ cbr)) := by
      rw [hpc2', htw2, htw1]; rfl
    have hbaseReg2 : st2.getReg baseBase = st.getReg baseBase := (hoth2 baseBase hBaseBaseT6).trans hbaseReg1
    have halBase : isAligned (st2.getReg baseBase + BitVec.ofInt 64 baseOff) 8 = true := by
      rw [hbaseReg2, hbaseAddr, Tab.base64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨st3, hrun3, hoth3, hrBase3, hmem3, hpc3⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom (pre ++ clen ++ cbr) (ctail ++ post)
        rBase baseBase rTmpBase hrBase0 hrTmpBase0 hBaseBaseTmpBase baseOff
        (by simpa only [clen, cbr, cbase, ctail, off12, List.append_assoc] using hlink)
        (by rw [htw2]; dsimp only [cbase] at h64'; omega) st2 hpc2 halBase
    have hpres3 : PreservedFrameRegs fl (· = rd) st2 st3 :=
      PreservedFrameRegs.of_scratch2 rBase rTmpBase hrBaseS hrTmpBaseS hoth3
    let p3 := pre ++ clen ++ cbr ++ cbase
    have htw3 : lkm.totalSize p3 = lkm.totalSize pre + lkm.totalSize clen + lkm.totalSize cbr + lkm.totalSize cbase := by
      dsimp only [p3]; rw [lkm.totalSize_append, htw2]
    have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize p3) := by rw [htw3, ← htw2]; exact hpc3
    have hrBase3' : st3.getReg rBase = L.base64 s := by rw [hrBase3, hmem2, hmem1, hbaseReg2, hbaseAddr, hbaseR]
    have hsext : sextImm12 off12 = BitVec.ofNat 64 (8 * vi.toNat + if hi then 4 else 0) :=
      sextImm12_ofNat_lt _ (by
        cases hi
        · change 8 * vi.toNat + 0 < 2048; omega
        · change 8 * vi.toNat + 4 < 2048; omega)
    have hal3 : isAligned (st3.getReg rBase + sextImm12 off12) 4 = true := by
      rw [hrBase3', hsext]
      cases hi
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact isAligned4_of_isAligned8 _ (isAligned8_add_mul8 (L.base64 s) (L.h64Align s) vi.toNat)
      · simp only [↓reduceIte, show 8 * vi.toNat + 4 = 4 * (2 * vi.toNat + 1) by omega]
        exact isAligned4_add_mul4 (L.base64 s) (L.h64Align s) (2 * vi.toNat + 1)
    let st4 := stepReg st3 rd ((loadBytes st3.mem (st3.getReg rBase + sextImm12 off12) 4).zeroExtend 64) (st3.pc + 4#64)
    obtain ⟨hrun4, hpc4, hrd4, hoth4, hmem4⟩ :=
      step_lwu_off_r env p3 post rd rBase off12 hrd.ne_zero
        (by simpa only [p3, clen, cbr, cbase, ctail, off12, Asm.lwu, Asm.raw,
            List.append_assoc, List.cons_append, List.nil_append] using hlink)
        (by rw [htw3]; omega) st3 hpc3' hal3
    have hpres4 : PreservedFrameRegs fl (· = rd) st3 st4 :=
      PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) hoth4
    have hm3 : st3.mem = st.mem := by rw [hmem3, hmem2, hmem1]
    have hrd4' : st4.getReg rd = (half32b hi ((lm.arr64 s)[vi.toNat])).toBitVec := by
      rw [hrd4, hm3, hrBase3', hsext]
      have hw := hwordsR vi.toNat hbound
      cases hi
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        rw [loadBytes_zeroExtend32_lo, hw]
        simp only [half32b, Bool.false_eq_true, ↓reduceIte, UInt64.toNat_toBitVec, UInt64.ofNat_toNat]
        apply BitVec.eq_of_toNat_eq
        simp only [UInt64.toNat_toBitVec, UInt64.toNat_mod, UInt64.toNat_and,
          show (4294967296 : UInt64).toNat = 2 ^ 32 from rfl,
          show (4294967295 : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      · simp only [↓reduceIte, BitVec.ofNat_add, ← BitVec.add_assoc]
        rw [loadBytes_zeroExtend32_hi, hw]
        simp only [half32b, ↓reduceIte, UInt64.toNat_toBitVec, UInt64.ofNat_toNat]
    refine ⟨lkm.totalSize clen + (kBr + (lkm.totalSize cbase + 1)), st4, ?_, ?_, hrd4',
      hpres1.trans (hpres2.trans (hpres3.trans hpres4)), hmem4.trans hm3, ?_⟩
    · rw [run_add, hrun1]; dsimp only
      rw [run_add, hrun2]; dsimp only
      rw [run_add, hrun3]; dsimp only
      exact hrun4
    · rw [hpc4, htw3]
      change BitVec.ofNat 64 (4 * _) = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (clen ++ cbr ++ cbase ++ ctail)))
      rw [htw_all]; congr 2; omega
    · exact (hoth4 AbiReg.t4 (hrd.ne_temp (by decide)).symm).trans
        ((hoth3 AbiReg.t4 hrBaseT4.symm hrTmpBaseT4.symm).trans
          ((hoth2 AbiReg.t4 (by decide)).trans (hoth1 AbiReg.t4 hrLenT4.symm hrTmpLenT4.symm)))
  · simp only [hbound, ↓reduceDIte]
    have hcondT : evalBranch .bgeu (st1.getReg ri) (st1.getReg rLen) = true := by
      simp [evalBranch, hri1, hrLen1']
      rw [BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
          Nat.mod_eq_of_lt (by omega : (lm.arr64 s).size < 2 ^ 64), decide_eq_false hbound]
    obtain ⟨kBr, st2, hrun2, hpc2', hoth2, _, hmem2⟩ :=
      prog_step_br_taken env (pre ++ clen) (cbase ++ ctail ++ post)
        .bgeu ri rLen errLabel env.errTarget env.herrLbl ⟨hriT6, hrLenT6⟩
        hlinkBr h64Br st1 hpc1' hcondT
    exact ⟨lkm.totalSize clen + kBr, st2,
      by rw [run_add, hrun1]; dsimp only; exact hrun2,
      hpc2', hpres1.trans (PreservedFrameRegs.of_t6_s1 hoth2),
      hmem2.trans hmem1⟩

abbrev RegEvalExprIH {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) (sp : BitVec 64) (e : Expr) : Prop :=
  ∀ (pre post : List AsmItem) (tmp : Nat) (rd : Reg),
    ValidTargetReg fl rd →
    exprOkB env.tab fl.nlocals e = true →
    tmp + usedTempsExpr e ≤ fl.usedTemps →
    lkm.linkSpec (pre ++ compileETo env.tab fl tmp rd e ++ post) = .ok (env.code, env.labels) →
    4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd e)) < 2 ^ 64 →
    ∀ (st : State),
    st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
    st.getReg AbiReg.gp = L.T → T5GpOk L fl st → st.getReg AbiReg.sp = sp →
    ProgMemRel env.tab L st.mem lm → ProgFrameOkR L fl sp st loc →
    match _root_.L.evalE e ⟨lm, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd e))) ∧
        st'.getReg rd = v.toBitVec ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem ∧
        (exprNoT4 e = true → st'.getReg AbiReg.t4 = st.getReg AbiReg.t4)
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem

private theorem reg_evalExpr_bin_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (op : BinOp) (a b : Expr) (iha : RegEvalExprIH env L fl lm loc sp a) (ihb : RegEvalExprIH env L fl lm loc sp b)
    (pre post : List AsmItem) (tmp : Nat) (rd : Reg) (hrd : ValidTargetReg fl rd)
    (heOk : exprOkB env.tab fl.nlocals (.bin op a b) = true)
    (hVf : ExprVarsInFrame fl (.bin op a b))
    (hTmp : tmp + usedTempsExpr (.bin op a b) ≤ fl.usedTemps)
    (hlink : lkm.linkSpec (pre ++ compileBinFallback env.tab fl tmp rd op a b
        (fun () => compileETo env.tab fl tmp AbiReg.a0 a)
        (fun () => compileETo env.tab fl tmp AbiReg.a0 b)
        (fun () => compileETo env.tab fl (tmp + 1) AbiReg.a0 b) ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (compileBinFallback env.tab fl tmp rd op a b
        (fun () => compileETo env.tab fl tmp AbiReg.a0 a)
        (fun () => compileETo env.tab fl tmp AbiReg.a0 b)
        (fun () => compileETo env.tab fl (tmp + 1) AbiReg.a0 b))) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    let code := compileBinFallback env.tab fl tmp rd op a b
      (fun () => compileETo env.tab fl tmp AbiReg.a0 a)
      (fun () => compileETo env.tab fl tmp AbiReg.a0 b)
      (fun () => compileETo env.tab fl (tmp + 1) AbiReg.a0 b)
    match _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize code)) ∧
        st'.getReg rd = v.toBitVec ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem ∧
        (exprNoT4 (.bin op a b) = true → st'.getReg AbiReg.t4 = st.getReg AbiReg.t4)
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
  intro code
  have hf : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  simp only [exprOkB, Bool.and_eq_true] at heOk
  have hTmpA : tmp + usedTempsExpr a ≤ fl.usedTemps := Nat.le_trans (Nat.add_le_add_left (usedTempsExpr_bin_left op a b) tmp) hTmp
  have hTmpB : tmp + usedTempsExpr b ≤ fl.usedTemps := Nat.le_trans (Nat.add_le_add_left (usedTempsExpr_bin_right op a b) tmp) hTmp
  cases hbC : b.constVal? with
  | some w =>
    have hbeq : b = .const w := expr_constVal_eq_some hbC
    have hsbT : isSimpleExpr b = true := by rw [hbeq]; rfl
    have hvb : _root_.L.evalE b ⟨lm, loc⟩ = .ok (w, ⟨lm, loc⟩) := by rw [hbeq]; rfl
    cases hra : exprReg? fl.alloc a with
    | some ra =>
      have hdef : code = emitBinConstRhsTo rd ra op w := by
        simp [code, compileBinFallback, hbC, hra]
      change lkm.linkSpec (pre ++ code ++ post) = _ at hlink
      change 4 * (lkm.totalSize pre + lkm.totalSize code) < 2 ^ 64 at h64
      rw [hdef] at hlink h64 ⊢
      obtain ⟨_, hraScr, va, hva, hgra⟩ := reg_exprReg_sim hfl hframeOk heOk.1 hra
      have hev : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .ok (op.eval va w, ⟨lm, loc⟩) := by
        dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
      rw [hev]
      obtain ⟨k, st', hrun, hpc', hrd', hoth, hmem⟩ :=
        emitBinConstRhsTo_sim_lm lkm env pre post rd ra hrd.ne_zero (hrd.ne_temp (by decide))
          (hraScr AbiReg.t0 (by decide)) op w va st hlink h64 hpc hgra
      exact ⟨k, st', hrun, hpc', hrd',
        PreservedFrameRegs.of_target_scratch rd AbiReg.t0 hrd (fun _ => rfl) (by decide) hoth,
        by rw [hmem]; exact MemEqOutside.refl _ _,
        fun _ => hoth AbiReg.t4 (hrd.ne_temp (by decide)).symm (by decide)⟩
    | none =>
      have hdef : code =
          compileETo env.tab fl tmp AbiReg.a0 a ++ emitBinConstRhsTo rd AbiReg.a0 op w := by
        simp [code, compileBinFallback, hbC, hra]
      change lkm.linkSpec (pre ++ code ++ post) = _ at hlink
      change 4 * (lkm.totalSize pre + lkm.totalSize code) < 2 ^ 64 at h64
      rw [hdef] at hlink h64 ⊢
      have htw_all : lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a ++ emitBinConstRhsTo rd AbiReg.a0 op w) =
          lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a) + lkm.totalSize (emitBinConstRhsTo rd AbiReg.a0 op w) :=
        lkm.totalSize_append _ _
      have ra := iha pre (emitBinConstRhsTo rd AbiReg.a0 op w ++ post) tmp AbiReg.a0 (Or.inl rfl) heOk.1 hTmpA
        (by simpa only [List.append_assoc] using hlink) (by rw [htw_all] at h64; omega)
        st hpc hgp ht5 hsp hmemRel hframeOk
      rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va, hva⟩ | hva
      · simp only [hva] at ra
        obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1, ht4_1⟩ := ra
        have hev : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .ok (op.eval va w, ⟨lm, loc⟩) := by
          dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
        rw [hev]
        have htw1 : lkm.totalSize (pre ++ compileETo env.tab fl tmp AbiReg.a0 a) =
            lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a) := lkm.totalSize_append _ _
        obtain ⟨k2, st2, hrun2, hpc2, hrd2, hoth2, hmem2⟩ :=
          emitBinConstRhsTo_sim_lm lkm env (pre ++ compileETo env.tab fl tmp AbiReg.a0 a) post rd AbiReg.a0
            hrd.ne_zero (hrd.ne_temp (by decide)) (by decide) op w va st1
            (by simpa only [List.append_assoc] using hlink)
            (by rw [htw1]; rw [htw_all] at h64; omega) (by rw [htw1]; exact hpc1) ha0_1
        exact ⟨k1 + k2, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
          by rw [hpc2, htw1, htw_all]; congr 2; omega, hrd2,
          (PreservedFrameRegs.of_a0 hpres1).trans
            (PreservedFrameRegs.of_target_scratch rd AbiReg.t0 hrd (fun _ => rfl) (by decide) hoth2),
          by rw [hmem2]; exact heq1,
          fun hnt => (hoth2 AbiReg.t4 (hrd.ne_temp (by decide)).symm (by decide)).trans
            (ht4_1 (exprNoT4_bin_left hnt hsbT))⟩
      · simp only [hva] at ra
        obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := ra
        have hev : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .error .oob := by
          dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]
        rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
  | none =>
    cases haC : a.constVal? with
    | some w =>
      have haeq : a = .const w := expr_constVal_eq_some haC
      have hsaT : isSimpleExpr a = true := by rw [haeq]; rfl
      have hva : _root_.L.evalE a ⟨lm, loc⟩ = .ok (w, ⟨lm, loc⟩) := by rw [haeq]; rfl
      let pB := match exprReg? fl.alloc b with | some r => ([], r) | none => (compileETo env.tab fl tmp AbiReg.a0 b, AbiReg.a0)
      have htailComm : ∀ (cTail : List AsmItem)
          (hdef : code = pB.1 ++ cTail)
          (htailSim : ∀ (vb : _root_.L.Word) (st1 : State),
            (pB.2 = AbiReg.zero ∨ pB.2 = AbiReg.a0 ∨ pB.2 ∈ allowedRegs true) →
            lkm.linkSpec ((pre ++ pB.1) ++ cTail ++ post) = .ok (env.code, env.labels) →
            4 * (lkm.totalSize (pre ++ pB.1) + lkm.totalSize cTail) < 2 ^ 64 →
            st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ pB.1)) →
            st1.getReg pB.2 = vb.toBitVec →
            ∃ k2 st2, RV64.run env.rom k2 st1 = .cont st2 ∧
              st2.pc = BitVec.ofNat 64 (4 * (lkm.totalSize (pre ++ pB.1) + lkm.totalSize cTail)) ∧
              st2.getReg rd = (op.eval w vb).toBitVec ∧
              PreservedFrameRegs fl (· = rd) st1 st2 ∧
              st2.mem = st1.mem ∧
              st2.getReg AbiReg.t4 = st1.getReg AbiReg.t4),
          match _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ with
          | .ok (v, _) =>
            ∃ k st', RV64.run env.rom k st = .cont st' ∧
              st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize code)) ∧
              st'.getReg rd = v.toBitVec ∧ PreservedFrameRegs fl (· = rd) st st' ∧
              MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem ∧
              (exprNoT4 (.bin op a b) = true → st'.getReg AbiReg.t4 = st.getReg AbiReg.t4)
          | .error _ =>
            ∃ k st', RV64.run env.rom k st = .cont st' ∧
              st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
              PreservedFrameRegs fl (· = rd) st st' ∧
              MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
        intro cTail hdef htailSim
        change lkm.linkSpec (pre ++ code ++ post) = _ at hlink
        change 4 * (lkm.totalSize pre + lkm.totalSize code) < 2 ^ 64 at h64
        rw [hdef] at hlink h64 ⊢
        have htw_all : lkm.totalSize (pB.1 ++ cTail) = lkm.totalSize pB.1 + lkm.totalSize cTail := lkm.totalSize_append _ _
        have rb := reg_evalIdx_of_ih env L fl hfl lm loc b pre (cTail ++ post) tmp heOk.2 hTmpB
          (fun p q t r s hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => ihb p q t r hr heOk.2 ht hl h6 s hpc' hgp' ht5' hsp' hm' hf')
          (by simpa only [pB, List.append_assoc] using hlink)
          (by rw [htw_all] at h64; dsimp only [pB] at h64 ⊢; omega)
          st hpc hgp ht5 hsp hmemRel hframeOk
        rcases rb with ⟨hpB2, rbSim⟩
        rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
        · simp only [hvb] at rbSim
          obtain ⟨k1, st1, hrun1, hpc1, hrb1, hpres1, heq1, ht4_1⟩ := rbSim
          have hev : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .ok (op.eval w vb, ⟨lm, loc⟩) := by
            dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
          rw [hev]
          have htw1 : lkm.totalSize (pre ++ pB.1) = lkm.totalSize pre + lkm.totalSize pB.1 := lkm.totalSize_append _ _
          obtain ⟨k2, st2, hrun2, hpc2, hrd2, hpres2, hmem2, ht4_2⟩ :=
            htailSim vb st1 hpB2 (by simpa only [List.append_assoc] using hlink)
              (by rw [htw1]; rw [htw_all] at h64; omega) (by rw [htw1]; exact hpc1) hrb1
          exact ⟨k1 + k2, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
            by rw [hpc2, htw1, htw_all]; congr 2; omega, hrd2,
            (PreservedFrameRegs.of_a0 hpres1).trans hpres2, by rw [hmem2]; exact heq1,
            fun hnt => ht4_2.trans (ht4_1 (exprNoT4_bin_right hnt hsaT))⟩
        · simp only [hvb] at rbSim
          obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := rbSim
          have hev : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .error .oob := by
            dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
          rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
      have stepComm : (∀ vb, op.eval w vb = op.eval vb w) →
          code = pB.1 ++ emitBinConstRhsTo rd pB.2 op w →
          match _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ with
          | .ok (v, _) =>
            ∃ k st', RV64.run env.rom k st = .cont st' ∧
              st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize code)) ∧
              st'.getReg rd = v.toBitVec ∧ PreservedFrameRegs fl (· = rd) st st' ∧
              MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem ∧
              (exprNoT4 (.bin op a b) = true → st'.getReg AbiReg.t4 = st.getReg AbiReg.t4)
          | .error _ =>
            ∃ k st', RV64.run env.rom k st = .cont st' ∧
              st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
              PreservedFrameRegs fl (· = rd) st st' ∧
              MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
        intro hcomm hdef
        refine htailComm (emitBinConstRhsTo rd pB.2 op w) hdef fun vb st1 hpB2 hl2 h64_2 hpc1 hrb1 => ?_
        obtain ⟨k2, st2, hrun2, hpc2, hrd2, hoth2, hmem2⟩ :=
          emitBinConstRhsTo_sim_lm lkm env (pre ++ pB.1) post rd pB.2 hrd.ne_zero
            (hrd.ne_temp (by decide)) (idxReg_ne_temp hpB2 (by decide)) op w vb st1 hl2 h64_2 hpc1 hrb1
        exact ⟨k2, st2, hrun2, hpc2, by rw [hrd2, hcomm vb],
          PreservedFrameRegs.of_target_scratch rd AbiReg.t0 hrd (fun _ => rfl) (by decide) hoth2, hmem2,
          hoth2 AbiReg.t4 (hrd.ne_temp (by decide)).symm (by decide)⟩
      have stepLiOp : (code =
          pB.1 ++ li AbiReg.t0 w.toBitVec ++ [emitBinOp op rd AbiReg.t0 pB.2]) →
          match _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ with
          | .ok (v, _) =>
            ∃ k st', RV64.run env.rom k st = .cont st' ∧
              st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize code)) ∧
              st'.getReg rd = v.toBitVec ∧ PreservedFrameRegs fl (· = rd) st st' ∧
              MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem ∧
              (exprNoT4 (.bin op a b) = true → st'.getReg AbiReg.t4 = st.getReg AbiReg.t4)
          | .error _ =>
            ∃ k st', RV64.run env.rom k st = .cont st' ∧
              st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
              PreservedFrameRegs fl (· = rd) st st' ∧
              MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
        intro hdef
        refine htailComm (li AbiReg.t0 w.toBitVec ++ [emitBinOp op rd AbiReg.t0 pB.2])
          (by rw [hdef, List.append_assoc]) fun vb st1 hpB2 hl2 h64_2 hpc1 hrb1 => ?_
        have htwLi : lkm.totalSize (li AbiReg.t0 w.toBitVec ++ [emitBinOp op rd AbiReg.t0 pB.2]) =
            lkm.totalSize (li AbiReg.t0 w.toBitVec) + lkm.totalSize [emitBinOp op rd AbiReg.t0 pB.2] :=
          lkm.totalSize_append _ _
        have hsz1 : lkm.totalSize [emitBinOp op rd AbiReg.t0 pB.2] = 1 := by
          cases op <;> simp [emitBinOp, Asm.add, Asm.sub, Asm.and, Asm.or, Asm.xor, Asm.sll, Asm.srl, Asm.mul, Asm.mulhu, lkm.totalSize_instr]
        obtain ⟨st2, hrunLi, hothLi, ht0_2, hmem2, hpc2⟩ :=
          li_correct_lm lkm env.hrom (pre ++ pB.1) ([emitBinOp op rd AbiReg.t0 pB.2] ++ post)
            AbiReg.t0 (by decide) w.toBitVec (by simpa only [List.append_assoc] using hl2)
            (by rw [htwLi] at h64_2; omega) st1 hpc1
        have htw2 : lkm.totalSize ((pre ++ pB.1) ++ li AbiReg.t0 w.toBitVec) =
            lkm.totalSize (pre ++ pB.1) + lkm.totalSize (li AbiReg.t0 w.toBitVec) := lkm.totalSize_append _ _
        obtain ⟨st3, hrunOp, hpc3, hrd3, hpres3, hmem3, ht4_3⟩ :=
          step_emitBinOp_r env fl ((pre ++ pB.1) ++ li AbiReg.t0 w.toBitVec) post op rd AbiReg.t0 pB.2
            hrd w vb (by simpa only [List.append_assoc] using hl2)
            (by rw [htw2]; rw [htwLi, hsz1] at h64_2; omega) st2 (by rw [htw2]; exact hpc2)
            ht0_2 ((hothLi pB.2 (idxReg_ne_temp hpB2 (by decide))).trans hrb1)
        exact ⟨lkm.totalSize (li AbiReg.t0 w.toBitVec) + 1, st3,
          by rw [run_add, hrunLi]; dsimp only; exact hrunOp,
          by rw [hpc3, htw2, htwLi]; congr 2; omega, hrd3,
          (PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hothLi).trans hpres3, hmem3.trans hmem2,
          ht4_3.trans (hothLi AbiReg.t4 (by decide))⟩
      cases op with
      | add => exact stepComm (fun vb => UInt64.add_comm w vb) (by cases h : exprReg? fl.alloc b <;> simp [code, compileBinFallback, hbC, haC, pB, h])
      | and => exact stepComm (fun vb => UInt64.and_comm w vb) (by cases h : exprReg? fl.alloc b <;> simp [code, compileBinFallback, hbC, haC, pB, h])
      | or  => exact stepComm (fun vb => UInt64.or_comm w vb) (by cases h : exprReg? fl.alloc b <;> simp [code, compileBinFallback, hbC, haC, pB, h])
      | xor => exact stepComm (fun vb => UInt64.xor_comm w vb) (by cases h : exprReg? fl.alloc b <;> simp [code, compileBinFallback, hbC, haC, pB, h])
      | mul => exact stepComm (fun vb => UInt64.mul_comm w vb) (by cases h : exprReg? fl.alloc b <;> simp [code, compileBinFallback, hbC, haC, pB, h])
      | mulhi =>
        exact stepComm (fun vb => by simp only [BinOp.eval, Nat.mul_comm]) (by cases h : exprReg? fl.alloc b <;> simp [code, compileBinFallback, hbC, haC, pB, h])
      | sub =>
        by_cases hw0 : w = 0
        · subst hw0
          refine htailComm [Asm.sub rd AbiReg.zero pB.2]
            (by cases h : exprReg? fl.alloc b <;> simp [code, compileBinFallback, hbC, haC, pB, h]) fun vb st1 _ hl2 h64_2 hpc1 hrb1 => ?_
          obtain ⟨st2, hrun2, hpc2, hrd2, hpres2, hmem2, ht4_2⟩ :=
            step_emitBinOp_r env fl (pre ++ pB.1) post .sub rd AbiReg.zero pB.2 hrd 0 vb
              hl2 (by rw [lkm.totalSize_append]; simp [Asm.sub, lkm.totalSize_instr] at h64_2; omega) st1 hpc1 rfl hrb1
          exact ⟨1, st2, hrun2, hpc2, hrd2, hpres2, hmem2, ht4_2⟩
        · have hbf : (w == 0) = false := beq_false_of_ne hw0
          exact stepLiOp (by cases h : exprReg? fl.alloc b <;> simp [code, compileBinFallback, hbC, haC, hbf, pB, emitBinOp, h])
      | shl => exact stepLiOp (by cases h : exprReg? fl.alloc b <;> simp [code, compileBinFallback, hbC, haC, pB, emitBinOp, h])
      | shr => exact stepLiOp (by cases h : exprReg? fl.alloc b <;> simp [code, compileBinFallback, hbC, haC, pB, emitBinOp, h])
    | none =>
      cases hrb : exprReg? fl.alloc b with
      | some rb =>
        have hsbT : isSimpleExpr b = true := isSimpleExpr_of_exprReg hrb
        obtain ⟨hrbMem, _, vb, hvb, hgrb⟩ := reg_exprReg_sim hfl hframeOk heOk.2 hrb
        cases hra : exprReg? fl.alloc a with
        | some ra =>
          have hdef : code = [emitBinOp op rd ra rb] := by
            simp [code, compileBinFallback, hbC, haC, hrb, hra]
          change lkm.linkSpec (pre ++ code ++ post) = _ at hlink
          change 4 * (lkm.totalSize pre + lkm.totalSize code) < 2 ^ 64 at h64
          rw [hdef] at hlink h64 ⊢
          obtain ⟨_, _, va, hva, hgra⟩ := reg_exprReg_sim (lm := lm) hfl hframeOk heOk.1 hra
          have hev : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .ok (op.eval va vb, ⟨lm, loc⟩) := by
            dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
          rw [hev]
          have hsz1 : lkm.totalSize [emitBinOp op rd ra rb] = 1 := by
            cases op <;> simp [emitBinOp, Asm.add, Asm.sub, Asm.and, Asm.or, Asm.xor, Asm.sll, Asm.srl, Asm.mul, Asm.mulhu, lkm.totalSize_instr]
          obtain ⟨st', hrun, hpc', hrd', hpres, hmem, ht4'⟩ :=
            step_emitBinOp_r env fl pre post op rd ra rb hrd va vb hlink (by rw [hsz1] at h64; omega) st hpc hgra hgrb
          exact ⟨1, st', hrun, hpc', hrd', hpres, by rw [hmem]; exact MemEqOutside.refl _ _, fun _ => ht4'⟩
        | none =>
          have hdef : code =
              compileETo env.tab fl tmp AbiReg.a0 a ++ [emitBinOp op rd AbiReg.a0 rb] := by
            simp [code, compileBinFallback, hbC, haC, hrb, hra]
          change lkm.linkSpec (pre ++ code ++ post) = _ at hlink
          change 4 * (lkm.totalSize pre + lkm.totalSize code) < 2 ^ 64 at h64
          rw [hdef] at hlink h64 ⊢
          have hsz1 : lkm.totalSize [emitBinOp op rd AbiReg.a0 rb] = 1 := by
            cases op <;> simp [emitBinOp, Asm.add, Asm.sub, Asm.and, Asm.or, Asm.xor, Asm.sll, Asm.srl, Asm.mul, Asm.mulhu, lkm.totalSize_instr]
          have htw_all : lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a ++ [emitBinOp op rd AbiReg.a0 rb]) =
              lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a) + 1 := by rw [lkm.totalSize_append, hsz1]
          have ra := iha pre ([emitBinOp op rd AbiReg.a0 rb] ++ post) tmp AbiReg.a0 (Or.inl rfl) heOk.1 hTmpA
            (by simpa only [List.append_assoc] using hlink) (by rw [htw_all] at h64; omega)
            st hpc hgp ht5 hsp hmemRel hframeOk
          rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va, hva⟩ | hva
          · simp only [hva] at ra
            obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1, ht4_1⟩ := ra
            have hev : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .ok (op.eval va vb, ⟨lm, loc⟩) := by
              dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
            rw [hev]
            have htw1 : lkm.totalSize (pre ++ compileETo env.tab fl tmp AbiReg.a0 a) =
                lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a) := lkm.totalSize_append _ _
            obtain ⟨st2, hrun2, hpc2, hrd2, hpres2, hmem2, ht4_2⟩ :=
              step_emitBinOp_r env fl (pre ++ compileETo env.tab fl tmp AbiReg.a0 a) post op rd AbiReg.a0 rb hrd va vb
                (by simpa only [List.append_assoc] using hlink)
                (by rw [htw1]; rw [htw_all] at h64; omega) st1 (by rw [htw1]; exact hpc1)
                ha0_1 ((hpres1.getReg_of_exprReg hrbMem).trans hgrb)
            exact ⟨k1 + 1, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
              by rw [hpc2, htw1, hsz1, htw_all, Nat.add_assoc], hrd2,
              (PreservedFrameRegs.of_a0 hpres1).trans hpres2, by rw [hmem2]; exact heq1,
              fun hnt => ht4_2.trans (ht4_1 (exprNoT4_bin_left hnt hsbT))⟩
          · simp only [hva] at ra
            obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := ra
            have hev : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .error .oob := by
              dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]
            rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
      | none =>
        cases hra : exprReg? fl.alloc a with
        | some ra =>
          have hsaT : isSimpleExpr a = true := isSimpleExpr_of_exprReg hra
          have hdef : code =
              compileETo env.tab fl tmp AbiReg.a0 b ++ [emitBinOp op rd ra AbiReg.a0] := by
            simp [code, compileBinFallback, hbC, haC, hrb, hra]
          change lkm.linkSpec (pre ++ code ++ post) = _ at hlink
          change 4 * (lkm.totalSize pre + lkm.totalSize code) < 2 ^ 64 at h64
          rw [hdef] at hlink h64 ⊢
          obtain ⟨hraMem, _, va, hva, hgra⟩ := reg_exprReg_sim (lm := lm) hfl hframeOk heOk.1 hra
          have hsz1 : lkm.totalSize [emitBinOp op rd ra AbiReg.a0] = 1 := by
            cases op <;> simp [emitBinOp, Asm.add, Asm.sub, Asm.and, Asm.or, Asm.xor, Asm.sll, Asm.srl, Asm.mul, Asm.mulhu, lkm.totalSize_instr]
          have htw_all : lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 b ++ [emitBinOp op rd ra AbiReg.a0]) =
              lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 b) + 1 := by rw [lkm.totalSize_append, hsz1]
          have rb := ihb pre ([emitBinOp op rd ra AbiReg.a0] ++ post) tmp AbiReg.a0 (Or.inl rfl) heOk.2 hTmpB
            (by simpa only [List.append_assoc] using hlink) (by rw [htw_all] at h64; omega)
            st hpc hgp ht5 hsp hmemRel hframeOk
          rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
          · simp only [hvb] at rb
            obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1, ht4_1⟩ := rb
            have hev : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .ok (op.eval va vb, ⟨lm, loc⟩) := by
              dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
            rw [hev]
            have htw1 : lkm.totalSize (pre ++ compileETo env.tab fl tmp AbiReg.a0 b) =
                lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 b) := lkm.totalSize_append _ _
            obtain ⟨st2, hrun2, hpc2, hrd2, hpres2, hmem2, ht4_2⟩ :=
              step_emitBinOp_r env fl (pre ++ compileETo env.tab fl tmp AbiReg.a0 b) post op rd ra AbiReg.a0 hrd va vb
                (by simpa only [List.append_assoc] using hlink)
                (by rw [htw1]; rw [htw_all] at h64; omega) st1 (by rw [htw1]; exact hpc1)
                ((hpres1.getReg_of_exprReg hraMem).trans hgra) ha0_1
            exact ⟨k1 + 1, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
              by rw [hpc2, htw1, hsz1, htw_all, Nat.add_assoc], hrd2,
              (PreservedFrameRegs.of_a0 hpres1).trans hpres2, by rw [hmem2]; exact heq1,
              fun hnt => ht4_2.trans (ht4_1 (exprNoT4_bin_right hnt hsaT))⟩
          · simp only [hvb] at rb
            obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := rb
            have hev : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .error .oob := by
              dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
            rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
        | none =>
          cases hsb : emitSimpleExprR env.tab fl AbiReg.t0 AbiReg.t1 b with
          | some cb =>
            have hsbT : isSimpleExpr b = true := by cases b <;> simp [emitSimpleExprR, isSimpleExpr] at hsb ⊢
            have hdef : code =
                compileETo env.tab fl tmp AbiReg.a0 a ++ cb ++ [emitBinOp op rd AbiReg.a0 AbiReg.t0] := by
              simp [code, compileBinFallback, hbC, haC, hrb, hra, hsb]
            change lkm.linkSpec (pre ++ code ++ post) = _ at hlink
            change 4 * (lkm.totalSize pre + lkm.totalSize code) < 2 ^ 64 at h64
            rw [hdef] at hlink h64 ⊢
            have hsz1 : lkm.totalSize [emitBinOp op rd AbiReg.a0 AbiReg.t0] = 1 := by
              cases op <;> simp [emitBinOp, Asm.add, Asm.sub, Asm.and, Asm.or, Asm.xor, Asm.sll, Asm.srl, Asm.mul, Asm.mulhu, lkm.totalSize_instr]
            have htw_all : lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a ++ cb ++ [emitBinOp op rd AbiReg.a0 AbiReg.t0]) =
                lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a) + lkm.totalSize cb + 1 := by
              simp only [lkm.totalSize_append, hsz1]
            have ra := iha pre (cb ++ [emitBinOp op rd AbiReg.a0 AbiReg.t0] ++ post) tmp AbiReg.a0 (Or.inl rfl) heOk.1 hTmpA
              (by simpa only [List.append_assoc] using hlink) (by rw [htw_all] at h64; omega)
              st hpc hgp ht5 hsp hmemRel hframeOk
            rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va, hva⟩ | hva
            · simp only [hva] at ra
              obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1, ht4_1⟩ := ra
              have htw1 : lkm.totalSize (pre ++ compileETo env.tab fl tmp AbiReg.a0 a) =
                  lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a) := lkm.totalSize_append _ _
              have hmemRel1 := ProgMemRel.of_tempSpanR hlo hhi (by omega) heq1 hmemRel
              have hframeOk1 := ProgFrameOkR.of_preserved_temp hfl hf (by omega) hpres1 heq1 hframeOk
              obtain ⟨vb, k2, st2, hvb, hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
                reg_emitSimpleExprR_sim env L fl hfl lm loc hspAlign
                  (pre ++ compileETo env.tab fl tmp AbiReg.a0 a) ([emitBinOp op rd AbiReg.a0 AbiReg.t0] ++ post)
                  AbiReg.t0 AbiReg.t1 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide) b cb hsb heOk.2
                  (fun x hx => hVf x (by simp [exprUsesVar, hx]))
                  (by simpa only [List.append_assoc] using hlink) (by rw [htw1]; rw [htw_all] at h64; omega)
                  st1 (by rw [htw1]; exact hpc1) (hpres1.abi.gp.trans hgp) (ht5.of_preserved hpres1)
                  (hpres1.abi.sp.trans hsp) hmemRel1 hframeOk1
              have hev : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .ok (op.eval va vb, ⟨lm, loc⟩) := by
                dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
              rw [hev]
              have htw2 : lkm.totalSize (pre ++ compileETo env.tab fl tmp AbiReg.a0 a ++ cb) =
                  lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a) + lkm.totalSize cb := by
                rw [lkm.totalSize_append, htw1]
              obtain ⟨st3, hrun3, hpc3, hrd3, hpres3, hmem3, ht4_3⟩ :=
                step_emitBinOp_r env fl (pre ++ compileETo env.tab fl tmp AbiReg.a0 a ++ cb) post op rd AbiReg.a0 AbiReg.t0
                  hrd va vb (by simpa only [List.append_assoc] using hlink)
                  (by rw [htw2]; rw [htw_all] at h64; omega) st2 (by rw [htw2, ← htw1]; exact hpc2)
                  ((hoth2 AbiReg.a0 (by decide) (by decide)).trans ha0_1) ht0_2
              exact ⟨k1 + (k2 + 1), st3,
                by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
                by rw [hpc3, htw2, hsz1, htw_all]; congr 2; omega, hrd3,
                (PreservedFrameRegs.of_a0 hpres1).trans
                  ((PreservedFrameRegs.of_scratch2 AbiReg.t0 AbiReg.t1 (by decide) (by decide) hoth2).trans hpres3),
                by rw [hmem3, hmem2]; exact heq1,
                fun hnt => ht4_3.trans ((hoth2 AbiReg.t4 (by decide) (by decide)).trans (ht4_1 (exprNoT4_bin_left hnt hsbT)))⟩
            · simp only [hva] at ra
              obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := ra
              have hev : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .error .oob := by
                dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]
              rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
          | none =>
            cases hsa : emitSimpleExprR env.tab fl AbiReg.t0 AbiReg.t1 a with
            | some ca =>
              have hsaT : isSimpleExpr a = true := by cases a <;> simp [emitSimpleExprR, isSimpleExpr] at hsa ⊢
              have hdef : code =
                  compileETo env.tab fl tmp AbiReg.a0 b ++ ca ++ [emitBinOp op rd AbiReg.t0 AbiReg.a0] := by
                simp [code, compileBinFallback, hbC, haC, hrb, hra, hsb, hsa]
              change lkm.linkSpec (pre ++ code ++ post) = _ at hlink
              change 4 * (lkm.totalSize pre + lkm.totalSize code) < 2 ^ 64 at h64
              rw [hdef] at hlink h64 ⊢
              have hsz1 : lkm.totalSize [emitBinOp op rd AbiReg.t0 AbiReg.a0] = 1 := by
                cases op <;> simp [emitBinOp, Asm.add, Asm.sub, Asm.and, Asm.or, Asm.xor, Asm.sll, Asm.srl, Asm.mul, Asm.mulhu, lkm.totalSize_instr]
              have htw_all : lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 b ++ ca ++ [emitBinOp op rd AbiReg.t0 AbiReg.a0]) =
                  lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 b) + lkm.totalSize ca + 1 := by
                simp only [lkm.totalSize_append, hsz1]
              have rb := ihb pre (ca ++ [emitBinOp op rd AbiReg.t0 AbiReg.a0] ++ post) tmp AbiReg.a0 (Or.inl rfl) heOk.2 hTmpB
                (by simpa only [List.append_assoc] using hlink) (by rw [htw_all] at h64; omega)
                st hpc hgp ht5 hsp hmemRel hframeOk
              rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
              · simp only [hvb] at rb
                obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1, ht4_1⟩ := rb
                have htw1 : lkm.totalSize (pre ++ compileETo env.tab fl tmp AbiReg.a0 b) =
                    lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 b) := lkm.totalSize_append _ _
                have hmemRel1 := ProgMemRel.of_tempSpanR hlo hhi (by omega) heq1 hmemRel
                have hframeOk1 := ProgFrameOkR.of_preserved_temp hfl hf (by omega) hpres1 heq1 hframeOk
                obtain ⟨va, k2, st2, hva, hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
                  reg_emitSimpleExprR_sim env L fl hfl lm loc hspAlign
                    (pre ++ compileETo env.tab fl tmp AbiReg.a0 b) ([emitBinOp op rd AbiReg.t0 AbiReg.a0] ++ post)
                    AbiReg.t0 AbiReg.t1 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide) a ca hsa heOk.1
                    (fun x hx => hVf x (by simp [exprUsesVar, hx]))
                    (by simpa only [List.append_assoc] using hlink) (by rw [htw1]; rw [htw_all] at h64; omega)
                    st1 (by rw [htw1]; exact hpc1) (hpres1.abi.gp.trans hgp) (ht5.of_preserved hpres1)
                    (hpres1.abi.sp.trans hsp) hmemRel1 hframeOk1
                have hev : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .ok (op.eval va vb, ⟨lm, loc⟩) := by
                  dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
                rw [hev]
                have htw2 : lkm.totalSize (pre ++ compileETo env.tab fl tmp AbiReg.a0 b ++ ca) =
                    lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 b) + lkm.totalSize ca := by
                  rw [lkm.totalSize_append, htw1]
                obtain ⟨st3, hrun3, hpc3, hrd3, hpres3, hmem3, ht4_3⟩ :=
                  step_emitBinOp_r env fl (pre ++ compileETo env.tab fl tmp AbiReg.a0 b ++ ca) post op rd AbiReg.t0 AbiReg.a0
                    hrd va vb (by simpa only [List.append_assoc] using hlink)
                    (by rw [htw2]; rw [htw_all] at h64; omega) st2 (by rw [htw2, ← htw1]; exact hpc2)
                    ht0_2 ((hoth2 AbiReg.a0 (by decide) (by decide)).trans ha0_1)
                exact ⟨k1 + (k2 + 1), st3,
                  by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
                  by rw [hpc3, htw2, hsz1, htw_all]; congr 2; omega, hrd3,
                  (PreservedFrameRegs.of_a0 hpres1).trans
                    ((PreservedFrameRegs.of_scratch2 AbiReg.t0 AbiReg.t1 (by decide) (by decide) hoth2).trans hpres3),
                  by rw [hmem3, hmem2]; exact heq1,
                  fun hnt => ht4_3.trans ((hoth2 AbiReg.t4 (by decide) (by decide)).trans (ht4_1 (exprNoT4_bin_right hnt hsaT)))⟩
              · have ⟨va, hva⟩ : ∃ va, _root_.L.evalE a ⟨lm, loc⟩ = .ok (va, ⟨lm, loc⟩) := by
                  cases a with
                  | const w => exact ⟨w, rfl⟩ | var x => exact ⟨loc x, rfl⟩
                  | len8 ar => exact ⟨lm.len8 ar, rfl⟩ | len64 ar => exact ⟨lm.len64 ar, rfl⟩
                  | glob g => exact ⟨lm.glob g, rfl⟩ | _ => simp [emitSimpleExprR] at hsa
                simp only [hvb] at rb
                obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := rb
                have hev : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .error .oob := by
                  dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
                rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
            | none =>
              have hsbF : isSimpleExpr b = false := isSimpleExpr_false_of_emitSimple_none hsb
              have hsaF : isSimpleExpr a = false := isSimpleExpr_false_of_emitSimple_none hsa
              have hntFalse : exprNoT4 (.bin op a b) = false := by simp [exprNoT4, hsbF, hsaF]
              by_cases hntB : exprNoT4 b = true
              · let seq := compileETo env.tab fl tmp AbiReg.a0 a ++
                  [Asm.mv AbiReg.t4 AbiReg.a0] ++
                  compileETo env.tab fl tmp AbiReg.a0 b
                have hdef : code = seq ++ [emitBinOp op rd AbiReg.t4 AbiReg.a0] := by
                  simp [code, compileBinFallback, hbC, haC, hrb, hra, hsb, hsa, hntB, seq, List.append_assoc]
                change lkm.linkSpec (pre ++ code ++ post) = _ at hlink
                change 4 * (lkm.totalSize pre + lkm.totalSize code) < 2 ^ 64 at h64
                rw [hdef] at hlink h64 ⊢
                have hsz1 : lkm.totalSize [emitBinOp op rd AbiReg.t4 AbiReg.a0] = 1 := by
                  cases op <;> simp [emitBinOp, Asm.add, Asm.sub, Asm.and, Asm.or, Asm.xor, Asm.sll, Asm.srl, Asm.mul, Asm.mulhu, lkm.totalSize_instr]
                have htw_all : lkm.totalSize (seq ++ [emitBinOp op rd AbiReg.t4 AbiReg.a0]) = lkm.totalSize seq + 1 := by
                  rw [lkm.totalSize_append, hsz1]
                have h64_seq : 4 * (lkm.totalSize pre + lkm.totalSize seq) < 2 ^ 64 := by rw [htw_all] at h64; omega
                have rPair := reg_evalTwoT4_of_ih env L fl hfl lm loc hlo hhi a b pre
                  ([emitBinOp op rd AbiReg.t4 AbiReg.a0] ++ post) tmp hntB hTmpA
                  (fun p q t r s hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => by
                    have r := iha p q t r hr heOk.1 ht hl h6 s hpc' hgp' ht5' hsp' hm' hf'
                    cases hv : _root_.L.evalE a ⟨lm, loc⟩ with
                    | ok _ => simp only [hv] at r; rcases r with ⟨k, st', h1, h2, h3, h4, h5, _⟩; exact ⟨k, st', h1, h2, h3, h4, h5⟩
                    | error _ => simp only [hv] at r; exact r)
                  (fun p q t r s hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => ihb p q t r hr heOk.2 ht hl h6 s hpc' hgp' ht5' hsp' hm' hf')
                  (by simpa only [seq, List.append_assoc] using hlink)
                  h64_seq st hpc hgp ht5 hsp hmemRel hframeOk
                rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va, hva⟩ | hva
                · rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
                  · simp only [hva, hvb] at rPair
                    obtain ⟨k1, st1, hrun1, hpc1, ht4_1, ha0_1, hpres1, heq1⟩ := rPair
                    have hev : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .ok (op.eval va vb, ⟨lm, loc⟩) := by
                      dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
                    rw [hev]
                    have htw1 : lkm.totalSize (pre ++ seq) = lkm.totalSize pre + lkm.totalSize seq := lkm.totalSize_append _ _
                    obtain ⟨st2, hrun2, hpc2, hrd2, hpres2, hmem2, _⟩ :=
                      step_emitBinOp_r env fl (pre ++ seq) post op rd AbiReg.t4 AbiReg.a0 hrd va vb
                        (by simpa only [List.append_assoc] using hlink)
                        (by rw [htw1]; rw [htw_all] at h64; omega) st1 (by rw [htw1]; exact hpc1) ht4_1 ha0_1
                    exact ⟨k1 + 1, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
                      by rw [hpc2, htw1, hsz1, htw_all, Nat.add_assoc], hrd2,
                      (PreservedFrameRegs.of_a0 hpres1).trans hpres2, by rw [hmem2]; exact heq1,
                      fun h => by rw [hntFalse] at h; cases h⟩
                  · simp only [hva, hvb] at rPair
                    obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := rPair
                    have hev : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .error .oob := by
                      dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
                    rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
                · simp only [hva] at rPair
                  obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := rPair
                  have hev : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .error .oob := by
                    dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]
                  rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
              · have hntBF : exprNoT4 b = false := Bool.eq_false_iff.mpr hntB
                simp only [usedTempsExpr, hsbF, hsaF, hntBF, Bool.false_eq_true, ↓reduceIte] at hTmp
                let seq := compileETo env.tab fl tmp AbiReg.a0 a ++
                  storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp) ++
                  compileETo env.tab fl (tmp + 1) AbiReg.a0 b ++
                  loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff tmp)
                have hdef : code = seq ++ [emitBinOp op rd AbiReg.t0 AbiReg.a0] := by
                  simp [code, compileBinFallback, hbC, haC, hrb, hra, hsb, hsa, hntBF, seq, List.append_assoc]
                change lkm.linkSpec (pre ++ code ++ post) = _ at hlink
                change 4 * (lkm.totalSize pre + lkm.totalSize code) < 2 ^ 64 at h64
                rw [hdef] at hlink h64 ⊢
                have hsz1 : lkm.totalSize [emitBinOp op rd AbiReg.t0 AbiReg.a0] = 1 := by
                  cases op <;> simp [emitBinOp, Asm.add, Asm.sub, Asm.and, Asm.or, Asm.xor, Asm.sll, Asm.srl, Asm.mul, Asm.mulhu, lkm.totalSize_instr]
                have htw_all : lkm.totalSize (seq ++ [emitBinOp op rd AbiReg.t0 AbiReg.a0]) = lkm.totalSize seq + 1 := by
                  rw [lkm.totalSize_append, hsz1]
                have h64_seq : 4 * (lkm.totalSize pre + lkm.totalSize seq) < 2 ^ 64 := by rw [htw_all] at h64; omega
                have rPair := reg_evalTwoSpill_of_ih env L fl hfl lm loc hspAlign hlo hhi a b pre
                  ([emitBinOp op rd AbiReg.t0 AbiReg.a0] ++ post) tmp (by omega) (by omega) (by omega)
                  (fun p q t r s hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => by
                    have r := iha p q t r hr heOk.1 ht hl h6 s hpc' hgp' ht5' hsp' hm' hf'
                    cases hv : _root_.L.evalE a ⟨lm, loc⟩ with
                    | ok _ => simp only [hv] at r; rcases r with ⟨k, st', h1, h2, h3, h4, h5, _⟩; exact ⟨k, st', h1, h2, h3, h4, h5⟩
                    | error _ => simp only [hv] at r; exact r)
                  (fun p q t r s hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => by
                    have r := ihb p q t r hr heOk.2 ht hl h6 s hpc' hgp' ht5' hsp' hm' hf'
                    cases hv : _root_.L.evalE b ⟨lm, loc⟩ with
                    | ok _ => simp only [hv] at r; rcases r with ⟨k, st', h1, h2, h3, h4, h5, _⟩; exact ⟨k, st', h1, h2, h3, h4, h5⟩
                    | error _ => simp only [hv] at r; exact r)
                  (by simpa only [seq, List.append_assoc] using hlink)
                  h64_seq st hpc hgp ht5 hsp hmemRel hframeOk
                rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va, hva⟩ | hva
                · rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
                  · simp only [hva, hvb] at rPair
                    obtain ⟨k1, st1, hrun1, hpc1, ht0_1, ha0_1, hpres1, heq1⟩ := rPair
                    have hev : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .ok (op.eval va vb, ⟨lm, loc⟩) := by
                      dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
                    rw [hev]
                    have htw1 : lkm.totalSize (pre ++ seq) = lkm.totalSize pre + lkm.totalSize seq := lkm.totalSize_append _ _
                    obtain ⟨st2, hrun2, hpc2, hrd2, hpres2, hmem2, _⟩ :=
                      step_emitBinOp_r env fl (pre ++ seq) post op rd AbiReg.t0 AbiReg.a0 hrd va vb
                        (by simpa only [List.append_assoc] using hlink)
                        (by rw [htw1]; rw [htw_all] at h64; omega) st1 (by rw [htw1]; exact hpc1) ht0_1 ha0_1
                    exact ⟨k1 + 1, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
                      by rw [hpc2, htw1, hsz1, htw_all, Nat.add_assoc], hrd2,
                      (PreservedFrameRegs.of_a0 hpres1).trans hpres2, by rw [hmem2]; exact heq1,
                      fun h => by rw [hntFalse] at h; cases h⟩
                  · simp only [hva, hvb] at rPair
                    obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := rPair
                    have hev : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .error .oob := by
                      dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
                    rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
                · simp only [hva] at rPair
                  obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := rPair
                  have hev : _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ = .error .oob := by
                    dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]
                  rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩

private theorem reg_evalExpr_cmpw_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (c : Cmp) (a b : Expr) (iha : RegEvalExprIH env L fl lm loc sp a) (ihb : RegEvalExprIH env L fl lm loc sp b)
    (pre post : List AsmItem) (tmp : Nat) (rd : Reg) (hrd : ValidTargetReg fl rd)
    (heOk : exprOkB env.tab fl.nlocals (.cmpw c a b) = true)
    (hVf : ExprVarsInFrame fl (.cmpw c a b))
    (hTmp : tmp + usedTempsExpr (.cmpw c a b) ≤ fl.usedTemps)
    (hlink : lkm.linkSpec (pre ++ compileETo env.tab fl tmp rd (.cmpw c a b) ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd (.cmpw c a b))) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    match _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd (.cmpw c a b)))) ∧
        st'.getReg rd = v.toBitVec ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem ∧
        (exprNoT4 (.cmpw c a b) = true → st'.getReg AbiReg.t4 = st.getReg AbiReg.t4)
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
  have hf : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  simp only [exprOkB, Bool.and_eq_true] at heOk
  have hTmpA : tmp + usedTempsExpr a ≤ fl.usedTemps := Nat.le_trans (Nat.add_le_add_left (usedTempsExpr_cmpw_left c a b) tmp) hTmp
  have hTmpB : tmp + usedTempsExpr b ≤ fl.usedTemps := Nat.le_trans (Nat.add_le_add_left (usedTempsExpr_cmpw_right c a b) tmp) hTmp
  have stepZeroEq : ∀ (x : Expr) (hxOk : exprOkB env.tab fl.nlocals x = true)
      (hxTmp : tmp + usedTempsExpr x ≤ fl.usedTemps)
      (hntX : exprNoT4 (.cmpw c a b) = true → exprNoT4 x = true)
      (ihx : ∀ (pre post : List AsmItem) (tmp : Nat) (rd : Reg) (st : State),
        ValidTargetReg fl rd → tmp + usedTempsExpr x ≤ fl.usedTemps →
        lkm.linkSpec (pre ++ compileETo env.tab fl tmp rd x ++ post) = .ok (env.code, env.labels) →
        4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd x)) < 2 ^ 64 →
        st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
        st.getReg AbiReg.gp = L.T → T5GpOk L fl st → st.getReg AbiReg.sp = sp →
        ProgMemRel env.tab L st.mem lm → ProgFrameOkR L fl sp st loc →
        match _root_.L.evalE x ⟨lm, loc⟩ with
        | .ok (v, _) =>
          ∃ k st', RV64.run env.rom k st = .cont st' ∧
            st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd x))) ∧
            st'.getReg rd = v.toBitVec ∧ PreservedFrameRegs fl (· = rd) st st' ∧
            MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem ∧
            (exprNoT4 x = true → st'.getReg AbiReg.t4 = st.getReg AbiReg.t4)
        | .error _ =>
          ∃ k st', RV64.run env.rom k st = .cont st' ∧
            st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧ PreservedFrameRegs fl (· = rd) st st' ∧
            MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem)
      (isNe : Bool)
      (hdef : compileETo env.tab fl tmp rd (.cmpw c a b) =
        match exprReg? fl.alloc x with
        | some rx => [if isNe then Asm.sltu rd AbiReg.zero rx else Asm.sltiu rd rx 1#12]
        | none => compileETo env.tab fl tmp AbiReg.a0 x ++ [if isNe then Asm.sltu rd AbiReg.zero AbiReg.a0 else Asm.sltiu rd AbiReg.a0 1#12])
      (hevOk : ∀ vx, _root_.L.evalE x ⟨lm, loc⟩ = .ok (vx, ⟨lm, loc⟩) →
        _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .ok ((if isNe then (if vx != 0 then 1 else 0) else (if vx == 0 then 1 else 0)), ⟨lm, loc⟩))
      (hevErr : _root_.L.evalE x ⟨lm, loc⟩ = .error .oob → _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .error .oob),
      match _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd (.cmpw c a b)))) ∧
          st'.getReg rd = v.toBitVec ∧ PreservedFrameRegs fl (· = rd) st st' ∧
          MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem ∧
          (exprNoT4 (.cmpw c a b) = true → st'.getReg AbiReg.t4 = st.getReg AbiReg.t4)
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedFrameRegs fl (· = rd) st st' ∧
          MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
    intro x hxOk hxTmp hntX ihx isNe hdef hevOk hevErr
    let pX := match exprReg? fl.alloc x with | some rx => ([], rx) | none => (compileETo env.tab fl tmp AbiReg.a0 x, AbiReg.a0)
    let tail := [if isNe then Asm.sltu rd AbiReg.zero pX.2 else Asm.sltiu rd pX.2 1#12]
    have hdef' : compileETo env.tab fl tmp rd (.cmpw c a b) = pX.1 ++ tail := by
      rw [hdef]; cases hrx : exprReg? fl.alloc x <;> simp [pX, tail, hrx]
    rw [hdef'] at hlink h64 ⊢
    have hsz1 : lkm.totalSize tail = 1 := by cases isNe <;> simp [tail, Asm.sltu, Asm.sltiu, lkm.totalSize_instr]
    have htw_all : lkm.totalSize (pX.1 ++ tail) = lkm.totalSize pX.1 + 1 := by rw [lkm.totalSize_append, hsz1]
    have rxRes := reg_evalIdx_of_ih env L fl hfl lm loc x pre (tail ++ post) tmp hxOk hxTmp ihx
      (by simpa only [pX, List.append_assoc] using hlink)
      (by rw [htw_all] at h64; dsimp only [pX] at h64 ⊢; omega) st hpc hgp ht5 hsp hmemRel hframeOk
    rcases rxRes with ⟨_, rxSim⟩
    rcases _root_.L.evalE_pure x ⟨lm, loc⟩ with ⟨vx, hvx⟩ | hvx
    · simp only [hvx] at rxSim
      obtain ⟨k1, st1, hrun1, hpc1, hrx1, hpres1, heq1, ht4_1⟩ := rxSim
      rw [hevOk vx hvx]
      have htw1 : lkm.totalSize (pre ++ pX.1) = lkm.totalSize pre + lkm.totalSize pX.1 := lkm.totalSize_append _ _
      have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ pX.1)) := by rw [htw1]; exact hpc1
      cases isNe
      · simp only [Bool.false_eq_true, ↓reduceIte] at hlink h64 ⊢
        have hs := step_item_instr_lm lkm env.hrom (pre ++ pX.1) post (.aluImm .sltiu rd pX.2 1#12)
          (by simpa only [tail, Bool.false_eq_true, ↓reduceIte, Asm.sltiu, List.append_assoc] using hlink)
          (by rw [htw1]; rw [htw_all] at h64; omega) st1 hpc1'
        let st2 := stepReg st1 rd (if vx.toBitVec.ult 1#64 then 1#64 else 0#64) (st1.pc + 4#64)
        refine ⟨k1 + 1, st2,
          by rw [run_add, hrun1]; dsimp only
             exact run_one_cont _ _ st2 (by rw [hs]; dsimp only [execInstr, evalAluImm]; rw [hrx1, show sextImm12 1#12 = 1#64 from rfl]; rfl),
          by change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1', htw1, htw_all, Nat.add_assoc],
          ?_, (PreservedFrameRegs.of_a0 hpres1).trans
            (PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) (fun r hr => getReg_stepReg_ne st1 rd r hr _ _)),
          by rw [mem_stepReg]; exact heq1,
          fun hnt => (getReg_stepReg_ne st1 rd AbiReg.t4 (hrd.ne_temp (by decide)).symm _ _).trans (ht4_1 (hntX hnt))⟩
        rw [getReg_stepReg_eq _ _ hrd.ne_zero]
        by_cases h0 : vx = 0
        · subst h0; rfl
        · have hult : vx.toBitVec.ult 1#64 = false := by
            rw [BitVec.ult, show (1#64 : BitVec 64).toNat = 1 from rfl, UInt64.toNat_toBitVec, decide_eq_false_iff_not]
            intro hlt; exact h0 (UInt64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (by rw [UInt64.toNat_toBitVec, show (0 : UInt64).toBitVec.toNat = 0 from rfl]; omega)))
          rw [hult, beq_eq_false_iff_ne.mpr h0]; rfl
      · simp only [↓reduceIte] at hlink h64 ⊢
        have hs := step_item_instr_lm lkm env.hrom (pre ++ pX.1) post (.alu .sltu rd AbiReg.zero pX.2)
          (by simpa only [tail, ↓reduceIte, Asm.sltu, List.append_assoc] using hlink)
          (by rw [htw1]; rw [htw_all] at h64; omega) st1 hpc1'
        let st2 := stepReg st1 rd (if (0#64).ult vx.toBitVec then 1#64 else 0#64) (st1.pc + 4#64)
        refine ⟨k1 + 1, st2,
          by rw [run_add, hrun1]; dsimp only
             exact run_one_cont _ _ st2 (by rw [hs]; dsimp only [execInstr, evalAlu]; rw [getReg_zero, hrx1]; rfl),
          by change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1', htw1, htw_all, Nat.add_assoc],
          ?_, (PreservedFrameRegs.of_a0 hpres1).trans
            (PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) (fun r hr => getReg_stepReg_ne st1 rd r hr _ _)),
          by rw [mem_stepReg]; exact heq1,
          fun hnt => (getReg_stepReg_ne st1 rd AbiReg.t4 (hrd.ne_temp (by decide)).symm _ _).trans (ht4_1 (hntX hnt))⟩
        rw [getReg_stepReg_eq _ _ hrd.ne_zero]
        by_cases h0 : vx = 0
        · subst h0; rfl
        · have hult : (0#64).ult vx.toBitVec = true := by
            rw [BitVec.ult, show (0#64 : BitVec 64).toNat = 0 from rfl, UInt64.toNat_toBitVec, decide_eq_true_eq]
            have : vx.toNat ≠ 0 := fun h => h0 (UInt64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (by rw [UInt64.toNat_toBitVec]; exact h)))
            omega
          rw [hult, show (vx != 0) = true by simp [bne, beq_eq_false_iff_ne.mpr h0]]; rfl
    · simp only [hvx] at rxSim
      obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := rxSim
      rw [hevErr hvx]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
  by_cases h1 : (c == .eq && b.constVal? == some 0) = true
  · simp only [Bool.and_eq_true, beq_iff_eq] at h1
    rcases h1 with ⟨rfl, hb0⟩
    have hsbT : isSimpleExpr b = true := isSimpleExpr_of_constVal hb0
    have hvb : _root_.L.evalE b ⟨lm, loc⟩ = .ok (0, ⟨lm, loc⟩) := by rw [expr_constVal_eq_some hb0]; rfl
    exact stepZeroEq a heOk.1 hTmpA (fun hnt => exprNoT4_cmpw_left hnt hsbT)
      (fun p q t r s hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => iha p q t r hr heOk.1 ht hl h6 s hpc' hgp' ht5' hsp' hm' hf')
      false (by cases h : exprReg? fl.alloc a <;> simp [compileETo, hb0, h])
      (fun va hva => by dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl)
      (fun hva => by dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva])
  · by_cases h2 : (c == .eq && a.constVal? == some 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h2
      rcases h2 with ⟨rfl, ha0⟩
      have hsaT : isSimpleExpr a = true := isSimpleExpr_of_constVal ha0
      have hva : _root_.L.evalE a ⟨lm, loc⟩ = .ok (0, ⟨lm, loc⟩) := by rw [expr_constVal_eq_some ha0]; rfl
      have h1f : (b.constVal? == some 0) = false := by
        cases hb' : b.constVal? == some 0 <;> simp_all
      exact stepZeroEq b heOk.2 hTmpB (fun hnt => exprNoT4_cmpw_right hnt hsaT)
        (fun p q t r s hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => ihb p q t r hr heOk.2 ht hl h6 s hpc' hgp' ht5' hsp' hm' hf')
        false (by cases h : exprReg? fl.alloc b <;> simp [compileETo, h1f, ha0, h])
        (fun vb hvb => by
          dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]
          dsimp only [Pure.pure, StateT.pure, Except.pure, Cmp.evalW, Cmp.eval]
          by_cases h : vb = 0
          · subst h; rfl
          · simp [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (Ne.symm h)])
        (fun hvb => by dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl)
    · by_cases h3 : (c == .ne && b.constVal? == some 0) = true
      · simp only [Bool.and_eq_true, beq_iff_eq] at h3
        rcases h3 with ⟨rfl, hb0⟩
        have hsbT : isSimpleExpr b = true := isSimpleExpr_of_constVal hb0
        have hvb : _root_.L.evalE b ⟨lm, loc⟩ = .ok (0, ⟨lm, loc⟩) := by rw [expr_constVal_eq_some hb0]; rfl
        exact stepZeroEq a heOk.1 hTmpA (fun hnt => exprNoT4_cmpw_left hnt hsbT)
          (fun p q t r s hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => iha p q t r hr heOk.1 ht hl h6 s hpc' hgp' ht5' hsp' hm' hf')
          true (by cases h : exprReg? fl.alloc a <;> simp [compileETo, hb0, h])
          (fun va hva => by dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl)
          (fun hva => by dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva])
      · by_cases h4 : (c == .ne && a.constVal? == some 0) = true
        · simp only [Bool.and_eq_true, beq_iff_eq] at h4
          rcases h4 with ⟨rfl, ha0⟩
          have hsaT : isSimpleExpr a = true := isSimpleExpr_of_constVal ha0
          have hva : _root_.L.evalE a ⟨lm, loc⟩ = .ok (0, ⟨lm, loc⟩) := by rw [expr_constVal_eq_some ha0]; rfl
          have h3f : (b.constVal? == some 0) = false := by
            cases hb' : b.constVal? == some 0 <;> simp_all
          exact stepZeroEq b heOk.2 hTmpB (fun hnt => exprNoT4_cmpw_right hnt hsaT)
            (fun p q t r s hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => ihb p q t r hr heOk.2 ht hl h6 s hpc' hgp' ht5' hsp' hm' hf')
            true (by cases h : exprReg? fl.alloc b <;> simp [compileETo, h3f, ha0, h])
            (fun vb hvb => by
              dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]
              dsimp only [Pure.pure, StateT.pure, Except.pure, Cmp.evalW, Cmp.eval]
              by_cases h : vb = 0
              · subst h; rfl
              · simp [bne, beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (Ne.symm h)])
            (fun hvb => by dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl)
        · have h1F : (c == .eq && b.constVal? == some 0) = false := Bool.eq_false_iff.mpr h1
          have h2F : (c == .eq && a.constVal? == some 0) = false := Bool.eq_false_iff.mpr h2
          have h3F : (c == .ne && b.constVal? == some 0) = false := Bool.eq_false_iff.mpr h3
          have h4F : (c == .ne && a.constVal? == some 0) = false := Bool.eq_false_iff.mpr h4
          cases hrb : exprReg? fl.alloc b with
          | some rb =>
            have hsbT : isSimpleExpr b = true := isSimpleExpr_of_exprReg hrb
            obtain ⟨hrbMem, _, vb, hvb, hgrb⟩ := reg_exprReg_sim hfl hframeOk heOk.2 hrb
            cases hra : exprReg? fl.alloc a with
            | some ra =>
              have hdef : compileETo env.tab fl tmp rd (.cmpw c a b) = emitCmpwTo rd c ra rb := by
                simp [compileETo, h1F, h2F, h3F, h4F, hrb, hra]
              rw [hdef] at hlink h64 ⊢
              obtain ⟨_, _, va, hva, hgra⟩ := reg_exprReg_sim (lm := lm) hfl hframeOk heOk.1 hra
              have hev : _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .ok (c.evalW va vb, ⟨lm, loc⟩) := by
                dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
              rw [hev]
              obtain ⟨k, st', hrun, hpc', hrd', hoth, hmem⟩ :=
                emitCmpwTo_sim_lm lkm env pre post rd hrd.ne_zero c ra rb va vb st hlink h64 hpc hgra hgrb
              exact ⟨k, st', hrun, hpc', hrd',
                PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) hoth, by rw [hmem]; exact MemEqOutside.refl _ _,
                fun _ => hoth AbiReg.t4 (hrd.ne_temp (by decide)).symm⟩
            | none =>
              have hdef : compileETo env.tab fl tmp rd (.cmpw c a b) =
                  compileETo env.tab fl tmp AbiReg.a0 a ++ emitCmpwTo rd c AbiReg.a0 rb := by
                simp [compileETo, h1F, h2F, h3F, h4F, hrb, hra]
              rw [hdef] at hlink h64 ⊢
              have htw_all : lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a ++ emitCmpwTo rd c AbiReg.a0 rb) =
                  lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a) + lkm.totalSize (emitCmpwTo rd c AbiReg.a0 rb) :=
                lkm.totalSize_append _ _
              have ra := iha pre (emitCmpwTo rd c AbiReg.a0 rb ++ post) tmp AbiReg.a0 (Or.inl rfl) heOk.1 hTmpA
                (by simpa only [List.append_assoc] using hlink) (by rw [htw_all] at h64; omega)
                st hpc hgp ht5 hsp hmemRel hframeOk
              rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va, hva⟩ | hva
              · simp only [hva] at ra
                obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1, ht4_1⟩ := ra
                have hev : _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .ok (c.evalW va vb, ⟨lm, loc⟩) := by
                  dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
                rw [hev]
                have htw1 : lkm.totalSize (pre ++ compileETo env.tab fl tmp AbiReg.a0 a) =
                    lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a) := lkm.totalSize_append _ _
                obtain ⟨k2, st2, hrun2, hpc2, hrd2, hoth2, hmem2⟩ :=
                  emitCmpwTo_sim_lm lkm env (pre ++ compileETo env.tab fl tmp AbiReg.a0 a) post rd hrd.ne_zero
                    c AbiReg.a0 rb va vb st1 (by simpa only [List.append_assoc] using hlink)
                    (by rw [htw1]; rw [htw_all] at h64; omega) (by rw [htw1]; exact hpc1)
                    ha0_1 ((hpres1.getReg_of_exprReg hrbMem).trans hgrb)
                exact ⟨k1 + k2, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
                  by rw [hpc2, htw1, htw_all]; congr 2; omega, hrd2,
                  (PreservedFrameRegs.of_a0 hpres1).trans (PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) hoth2),
                  by rw [hmem2]; exact heq1,
                  fun hnt => (hoth2 AbiReg.t4 (hrd.ne_temp (by decide)).symm).trans (ht4_1 (exprNoT4_cmpw_left hnt hsbT))⟩
              · simp only [hva] at ra
                obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := ra
                have hev : _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .error .oob := by
                  dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]
                rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
          | none =>
            cases hra : exprReg? fl.alloc a with
            | some ra =>
              have hsaT : isSimpleExpr a = true := isSimpleExpr_of_exprReg hra
              have hdef : compileETo env.tab fl tmp rd (.cmpw c a b) =
                  compileETo env.tab fl tmp AbiReg.a0 b ++ emitCmpwTo rd c ra AbiReg.a0 := by
                simp [compileETo, h1F, h2F, h3F, h4F, hrb, hra]
              rw [hdef] at hlink h64 ⊢
              obtain ⟨hraMem, _, va, hva, hgra⟩ := reg_exprReg_sim (lm := lm) hfl hframeOk heOk.1 hra
              have htw_all : lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 b ++ emitCmpwTo rd c ra AbiReg.a0) =
                  lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 b) + lkm.totalSize (emitCmpwTo rd c ra AbiReg.a0) :=
                lkm.totalSize_append _ _
              have rb := ihb pre (emitCmpwTo rd c ra AbiReg.a0 ++ post) tmp AbiReg.a0 (Or.inl rfl) heOk.2 hTmpB
                (by simpa only [List.append_assoc] using hlink) (by rw [htw_all] at h64; omega)
                st hpc hgp ht5 hsp hmemRel hframeOk
              rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
              · simp only [hvb] at rb
                obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1, ht4_1⟩ := rb
                have hev : _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .ok (c.evalW va vb, ⟨lm, loc⟩) := by
                  dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
                rw [hev]
                have htw1 : lkm.totalSize (pre ++ compileETo env.tab fl tmp AbiReg.a0 b) =
                    lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 b) := lkm.totalSize_append _ _
                obtain ⟨k2, st2, hrun2, hpc2, hrd2, hoth2, hmem2⟩ :=
                  emitCmpwTo_sim_lm lkm env (pre ++ compileETo env.tab fl tmp AbiReg.a0 b) post rd hrd.ne_zero
                    c ra AbiReg.a0 va vb st1 (by simpa only [List.append_assoc] using hlink)
                    (by rw [htw1]; rw [htw_all] at h64; omega) (by rw [htw1]; exact hpc1)
                    ((hpres1.getReg_of_exprReg hraMem).trans hgra) ha0_1
                exact ⟨k1 + k2, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
                  by rw [hpc2, htw1, htw_all]; congr 2; omega, hrd2,
                  (PreservedFrameRegs.of_a0 hpres1).trans (PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) hoth2),
                  by rw [hmem2]; exact heq1,
                  fun hnt => (hoth2 AbiReg.t4 (hrd.ne_temp (by decide)).symm).trans (ht4_1 (exprNoT4_cmpw_right hnt hsaT))⟩
              · simp only [hvb] at rb
                obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := rb
                have hev : _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .error .oob := by
                  dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
                rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
            | none =>
              cases hsb : emitSimpleExprR env.tab fl AbiReg.t0 AbiReg.t1 b with
              | some cb =>
                have hsbT : isSimpleExpr b = true := by cases b <;> simp [emitSimpleExprR, isSimpleExpr] at hsb ⊢
                have hdef : compileETo env.tab fl tmp rd (.cmpw c a b) =
                    compileETo env.tab fl tmp AbiReg.a0 a ++ cb ++ emitCmpwTo rd c AbiReg.a0 AbiReg.t0 := by
                  simp [compileETo, h1F, h2F, h3F, h4F, hrb, hra, hsb]
                rw [hdef] at hlink h64 ⊢
                have htw_all : lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a ++ cb ++ emitCmpwTo rd c AbiReg.a0 AbiReg.t0) =
                    lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a) + lkm.totalSize cb + lkm.totalSize (emitCmpwTo rd c AbiReg.a0 AbiReg.t0) := by
                  simp only [lkm.totalSize_append]
                have ra := iha pre (cb ++ emitCmpwTo rd c AbiReg.a0 AbiReg.t0 ++ post) tmp AbiReg.a0 (Or.inl rfl) heOk.1 hTmpA
                  (by simpa only [List.append_assoc] using hlink) (by rw [htw_all] at h64; omega)
                  st hpc hgp ht5 hsp hmemRel hframeOk
                rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va, hva⟩ | hva
                · simp only [hva] at ra
                  obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1, ht4_1⟩ := ra
                  have htw1 : lkm.totalSize (pre ++ compileETo env.tab fl tmp AbiReg.a0 a) =
                      lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a) := lkm.totalSize_append _ _
                  have hmemRel1 := ProgMemRel.of_tempSpanR hlo hhi (by omega) heq1 hmemRel
                  have hframeOk1 := ProgFrameOkR.of_preserved_temp hfl hf (by omega) hpres1 heq1 hframeOk
                  obtain ⟨vb, k2, st2, hvb, hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
                    reg_emitSimpleExprR_sim env L fl hfl lm loc hspAlign
                      (pre ++ compileETo env.tab fl tmp AbiReg.a0 a) (emitCmpwTo rd c AbiReg.a0 AbiReg.t0 ++ post)
                      AbiReg.t0 AbiReg.t1 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide) b cb hsb heOk.2
                      (fun x hx => hVf x (by simp [exprUsesVar, hx]))
                      (by simpa only [List.append_assoc] using hlink) (by rw [htw1]; rw [htw_all] at h64; omega)
                      st1 (by rw [htw1]; exact hpc1) (hpres1.abi.gp.trans hgp) (ht5.of_preserved hpres1)
                      (hpres1.abi.sp.trans hsp) hmemRel1 hframeOk1
                  have hev : _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .ok (c.evalW va vb, ⟨lm, loc⟩) := by
                    dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
                  rw [hev]
                  have htw2 : lkm.totalSize (pre ++ compileETo env.tab fl tmp AbiReg.a0 a ++ cb) =
                      lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a) + lkm.totalSize cb := by
                    rw [lkm.totalSize_append, htw1]
                  obtain ⟨k3, st3, hrun3, hpc3, hrd3, hoth3, hmem3⟩ :=
                    emitCmpwTo_sim_lm lkm env (pre ++ compileETo env.tab fl tmp AbiReg.a0 a ++ cb) post rd hrd.ne_zero
                      c AbiReg.a0 AbiReg.t0 va vb st2 (by simpa only [List.append_assoc] using hlink)
                      (by rw [htw2]; rw [htw_all] at h64; omega) (by rw [htw2, ← htw1]; exact hpc2)
                      ((hoth2 AbiReg.a0 (by decide) (by decide)).trans ha0_1) ht0_2
                  exact ⟨k1 + (k2 + k3), st3,
                    by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
                    by rw [hpc3, htw2, htw_all]; congr 2; omega, hrd3,
                    (PreservedFrameRegs.of_a0 hpres1).trans
                      ((PreservedFrameRegs.of_scratch2 AbiReg.t0 AbiReg.t1 (by decide) (by decide) hoth2).trans
                        (PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) hoth3)),
                    by rw [hmem3, hmem2]; exact heq1,
                    fun hnt => (hoth3 AbiReg.t4 (hrd.ne_temp (by decide)).symm).trans
                      ((hoth2 AbiReg.t4 (by decide) (by decide)).trans (ht4_1 (exprNoT4_cmpw_left hnt hsbT)))⟩
                · simp only [hva] at ra
                  obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := ra
                  have hev : _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .error .oob := by
                    dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]
                  rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
              | none =>
                cases hsa : emitSimpleExprR env.tab fl AbiReg.t0 AbiReg.t1 a with
                | some ca =>
                  have hsaT : isSimpleExpr a = true := by cases a <;> simp [emitSimpleExprR, isSimpleExpr] at hsa ⊢
                  have hdef : compileETo env.tab fl tmp rd (.cmpw c a b) =
                      compileETo env.tab fl tmp AbiReg.a0 b ++ ca ++ emitCmpwTo rd c AbiReg.t0 AbiReg.a0 := by
                    simp [compileETo, h1F, h2F, h3F, h4F, hrb, hra, hsb, hsa]
                  rw [hdef] at hlink h64 ⊢
                  have htw_all : lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 b ++ ca ++ emitCmpwTo rd c AbiReg.t0 AbiReg.a0) =
                      lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 b) + lkm.totalSize ca + lkm.totalSize (emitCmpwTo rd c AbiReg.t0 AbiReg.a0) := by
                    simp only [lkm.totalSize_append]
                  have rb := ihb pre (ca ++ emitCmpwTo rd c AbiReg.t0 AbiReg.a0 ++ post) tmp AbiReg.a0 (Or.inl rfl) heOk.2 hTmpB
                    (by simpa only [List.append_assoc] using hlink) (by rw [htw_all] at h64; omega)
                    st hpc hgp ht5 hsp hmemRel hframeOk
                  rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
                  · simp only [hvb] at rb
                    obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1, ht4_1⟩ := rb
                    have htw1 : lkm.totalSize (pre ++ compileETo env.tab fl tmp AbiReg.a0 b) =
                        lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 b) := lkm.totalSize_append _ _
                    have hmemRel1 := ProgMemRel.of_tempSpanR hlo hhi (by omega) heq1 hmemRel
                    have hframeOk1 := ProgFrameOkR.of_preserved_temp hfl hf (by omega) hpres1 heq1 hframeOk
                    obtain ⟨va, k2, st2, hva, hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
                      reg_emitSimpleExprR_sim env L fl hfl lm loc hspAlign
                        (pre ++ compileETo env.tab fl tmp AbiReg.a0 b) (emitCmpwTo rd c AbiReg.t0 AbiReg.a0 ++ post)
                        AbiReg.t0 AbiReg.t1 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide) a ca hsa heOk.1
                        (fun x hx => hVf x (by simp [exprUsesVar, hx]))
                        (by simpa only [List.append_assoc] using hlink) (by rw [htw1]; rw [htw_all] at h64; omega)
                        st1 (by rw [htw1]; exact hpc1) (hpres1.abi.gp.trans hgp) (ht5.of_preserved hpres1)
                        (hpres1.abi.sp.trans hsp) hmemRel1 hframeOk1
                    have hev : _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .ok (c.evalW va vb, ⟨lm, loc⟩) := by
                      dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
                    rw [hev]
                    have htw2 : lkm.totalSize (pre ++ compileETo env.tab fl tmp AbiReg.a0 b ++ ca) =
                        lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 b) + lkm.totalSize ca := by
                      rw [lkm.totalSize_append, htw1]
                    obtain ⟨k3, st3, hrun3, hpc3, hrd3, hoth3, hmem3⟩ :=
                      emitCmpwTo_sim_lm lkm env (pre ++ compileETo env.tab fl tmp AbiReg.a0 b ++ ca) post rd hrd.ne_zero
                        c AbiReg.t0 AbiReg.a0 va vb st2 (by simpa only [List.append_assoc] using hlink)
                        (by rw [htw2]; rw [htw_all] at h64; omega) (by rw [htw2, ← htw1]; exact hpc2)
                        ht0_2 ((hoth2 AbiReg.a0 (by decide) (by decide)).trans ha0_1)
                    exact ⟨k1 + (k2 + k3), st3,
                      by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
                      by rw [hpc3, htw2, htw_all]; congr 2; omega, hrd3,
                      (PreservedFrameRegs.of_a0 hpres1).trans
                        ((PreservedFrameRegs.of_scratch2 AbiReg.t0 AbiReg.t1 (by decide) (by decide) hoth2).trans
                          (PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) hoth3)),
                      by rw [hmem3, hmem2]; exact heq1,
                      fun hnt => (hoth3 AbiReg.t4 (hrd.ne_temp (by decide)).symm).trans
                        ((hoth2 AbiReg.t4 (by decide) (by decide)).trans (ht4_1 (exprNoT4_cmpw_right hnt hsaT)))⟩
                  · have ⟨va, hva⟩ : ∃ va, _root_.L.evalE a ⟨lm, loc⟩ = .ok (va, ⟨lm, loc⟩) := by
                      cases a with
                      | const w => exact ⟨w, rfl⟩ | var x => exact ⟨loc x, rfl⟩
                      | len8 ar => exact ⟨lm.len8 ar, rfl⟩ | len64 ar => exact ⟨lm.len64 ar, rfl⟩
                      | glob g => exact ⟨lm.glob g, rfl⟩ | _ => simp [emitSimpleExprR] at hsa
                    simp only [hvb] at rb
                    obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := rb
                    have hev : _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .error .oob := by
                      dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
                    rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
                | none =>
                  have hsbF : isSimpleExpr b = false := isSimpleExpr_false_of_emitSimple_none hsb
                  have hsaF : isSimpleExpr a = false := isSimpleExpr_false_of_emitSimple_none hsa
                  have hntFalse : exprNoT4 (.cmpw c a b) = false := by simp [exprNoT4, hsbF, hsaF]
                  by_cases hntB : exprNoT4 b = true
                  · let seq := compileETo env.tab fl tmp AbiReg.a0 a ++
                      [Asm.mv AbiReg.t4 AbiReg.a0] ++
                      compileETo env.tab fl tmp AbiReg.a0 b
                    have hdef : compileETo env.tab fl tmp rd (.cmpw c a b) = seq ++ emitCmpwTo rd c AbiReg.t4 AbiReg.a0 := by
                      simp [compileETo, h1F, h2F, h3F, h4F, hrb, hra, hsb, hsa, hntB, seq, List.append_assoc]
                    rw [hdef] at hlink h64 ⊢
                    have htw_all : lkm.totalSize (seq ++ emitCmpwTo rd c AbiReg.t4 AbiReg.a0) =
                        lkm.totalSize seq + lkm.totalSize (emitCmpwTo rd c AbiReg.t4 AbiReg.a0) := lkm.totalSize_append _ _
                    have h64_seq : 4 * (lkm.totalSize pre + lkm.totalSize seq) < 2 ^ 64 := by rw [htw_all] at h64; omega
                    have rPair := reg_evalTwoT4_of_ih env L fl hfl lm loc hlo hhi a b pre
                      (emitCmpwTo rd c AbiReg.t4 AbiReg.a0 ++ post) tmp hntB hTmpA
                      (fun p q t r s hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => by
                        have r := iha p q t r hr heOk.1 ht hl h6 s hpc' hgp' ht5' hsp' hm' hf'
                        cases hv : _root_.L.evalE a ⟨lm, loc⟩ with
                        | ok _ => simp only [hv] at r; rcases r with ⟨k, st', h1, h2, h3, h4, h5, _⟩; exact ⟨k, st', h1, h2, h3, h4, h5⟩
                        | error _ => simp only [hv] at r; exact r)
                      (fun p q t r s hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => ihb p q t r hr heOk.2 ht hl h6 s hpc' hgp' ht5' hsp' hm' hf')
                      (by simpa only [seq, List.append_assoc] using hlink)
                      h64_seq st hpc hgp ht5 hsp hmemRel hframeOk
                    rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va, hva⟩ | hva
                    · rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
                      · simp only [hva, hvb] at rPair
                        obtain ⟨k1, st1, hrun1, hpc1, ht4_1, ha0_1, hpres1, heq1⟩ := rPair
                        have hev : _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .ok (c.evalW va vb, ⟨lm, loc⟩) := by
                          dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
                        rw [hev]
                        have htw1 : lkm.totalSize (pre ++ seq) = lkm.totalSize pre + lkm.totalSize seq := lkm.totalSize_append _ _
                        obtain ⟨k2, st2, hrun2, hpc2, hrd2, hoth2, hmem2⟩ :=
                          emitCmpwTo_sim_lm lkm env (pre ++ seq) post rd hrd.ne_zero c AbiReg.t4 AbiReg.a0 va vb st1
                            (by simpa only [List.append_assoc] using hlink)
                            (by rw [htw1]; rw [htw_all] at h64; omega) (by rw [htw1]; exact hpc1) ht4_1 ha0_1
                        exact ⟨k1 + k2, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
                          by rw [hpc2, htw1, htw_all]; congr 2; omega, hrd2,
                          (PreservedFrameRegs.of_a0 hpres1).trans (PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) hoth2),
                          by rw [hmem2]; exact heq1,
                          fun h => by rw [hntFalse] at h; cases h⟩
                      · simp only [hva, hvb] at rPair
                        obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := rPair
                        have hev : _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .error .oob := by
                          dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
                        rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
                    · simp only [hva] at rPair
                      obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := rPair
                      have hev : _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .error .oob := by
                        dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]
                      rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
                  · have hntBF : exprNoT4 b = false := Bool.eq_false_iff.mpr hntB
                    simp only [usedTempsExpr, hsbF, hsaF, hntBF, Bool.false_eq_true, ↓reduceIte] at hTmp
                    let seq := compileETo env.tab fl tmp AbiReg.a0 a ++
                      storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp) ++
                      compileETo env.tab fl (tmp + 1) AbiReg.a0 b ++
                      loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff tmp)
                    have hdef : compileETo env.tab fl tmp rd (.cmpw c a b) = seq ++ emitCmpwTo rd c AbiReg.t0 AbiReg.a0 := by
                      simp [compileETo, h1F, h2F, h3F, h4F, hrb, hra, hsb, hsa, hntBF, seq, List.append_assoc]
                    rw [hdef] at hlink h64 ⊢
                    have htw_all : lkm.totalSize (seq ++ emitCmpwTo rd c AbiReg.t0 AbiReg.a0) =
                        lkm.totalSize seq + lkm.totalSize (emitCmpwTo rd c AbiReg.t0 AbiReg.a0) := lkm.totalSize_append _ _
                    have h64_seq : 4 * (lkm.totalSize pre + lkm.totalSize seq) < 2 ^ 64 := by rw [htw_all] at h64; omega
                    have rPair := reg_evalTwoSpill_of_ih env L fl hfl lm loc hspAlign hlo hhi a b pre
                      (emitCmpwTo rd c AbiReg.t0 AbiReg.a0 ++ post) tmp (by omega) (by omega) (by omega)
                      (fun p q t r s hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => by
                        have r := iha p q t r hr heOk.1 ht hl h6 s hpc' hgp' ht5' hsp' hm' hf'
                        cases hv : _root_.L.evalE a ⟨lm, loc⟩ with
                        | ok _ => simp only [hv] at r; rcases r with ⟨k, st', h1, h2, h3, h4, h5, _⟩; exact ⟨k, st', h1, h2, h3, h4, h5⟩
                        | error _ => simp only [hv] at r; exact r)
                      (fun p q t r s hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => by
                        have r := ihb p q t r hr heOk.2 ht hl h6 s hpc' hgp' ht5' hsp' hm' hf'
                        cases hv : _root_.L.evalE b ⟨lm, loc⟩ with
                        | ok _ => simp only [hv] at r; rcases r with ⟨k, st', h1, h2, h3, h4, h5, _⟩; exact ⟨k, st', h1, h2, h3, h4, h5⟩
                        | error _ => simp only [hv] at r; exact r)
                      (by simpa only [seq, List.append_assoc] using hlink)
                      h64_seq st hpc hgp ht5 hsp hmemRel hframeOk
                    rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va, hva⟩ | hva
                    · rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
                      · simp only [hva, hvb] at rPair
                        obtain ⟨k1, st1, hrun1, hpc1, ht0_1, ha0_1, hpres1, heq1⟩ := rPair
                        have hev : _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .ok (c.evalW va vb, ⟨lm, loc⟩) := by
                          dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
                        rw [hev]
                        have htw1 : lkm.totalSize (pre ++ seq) = lkm.totalSize pre + lkm.totalSize seq := lkm.totalSize_append _ _
                        obtain ⟨k2, st2, hrun2, hpc2, hrd2, hoth2, hmem2⟩ :=
                          emitCmpwTo_sim_lm lkm env (pre ++ seq) post rd hrd.ne_zero c AbiReg.t0 AbiReg.a0 va vb st1
                            (by simpa only [List.append_assoc] using hlink)
                            (by rw [htw1]; rw [htw_all] at h64; omega) (by rw [htw1]; exact hpc1) ht0_1 ha0_1
                        exact ⟨k1 + k2, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
                          by rw [hpc2, htw1, htw_all]; congr 2; omega, hrd2,
                          (PreservedFrameRegs.of_a0 hpres1).trans (PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) hoth2),
                          by rw [hmem2]; exact heq1,
                          fun h => by rw [hntFalse] at h; cases h⟩
                      · simp only [hva, hvb] at rPair
                        obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := rPair
                        have hev : _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .error .oob := by
                          dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]; dsimp only; rw [hvb]; try rfl
                        rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
                    · simp only [hva] at rPair
                      obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := rPair
                      have hev : _root_.L.evalE (.cmpw c a b) ⟨lm, loc⟩ = .error .oob := by
                        dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hva]
                      rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩

/-- Dispatch `ld64Tail` to `reg_ld64_const_body_r` or `reg_ld64_body_r`. -/
private theorem reg_ld64Tail_body_r {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) (s : TieredArray) (hsOk : env.tab.wordPosOkB s = true)
    (i : Expr) (vi : _root_.L.Word) (hvi : _root_.L.evalE i ⟨lm, loc⟩ = .ok (vi, ⟨lm, loc⟩))
    (pre post : List AsmItem)
    (rd ri lenBase baseBase rLen rTmpLen rTmpBase : Reg)
    (hrd : ValidTargetReg fl rd)
    (hri : ri = AbiReg.zero ∨ ri = AbiReg.a0 ∨ ri ∈ allowedRegs true)
    (hrLen : rLen ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3])
    (hrTmpLen : rTmpLen ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3])
    (hrTmpBase : rTmpBase ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3])
    (hBaseTmp : AbiReg.t1 ≠ rTmpBase)
    (hLenBaseTmpLen : lenBase ≠ rTmpLen)
    (hBaseBaseLen : baseBase ≠ rLen)
    (hBaseBaseTmpLen : baseBase ≠ rTmpLen)
    (hBaseBaseTmpBase : baseBase ≠ rTmpBase)
    (hBaseBaseT6 : baseBase ≠ AbiReg.t6 ∧ baseBase ≠ AbiReg.s1)
    (lenOff baseOff : Int)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hlenAddr : st.getReg lenBase + BitVec.ofInt 64 lenOff = L.T + BitVec.ofInt 64 (env.tab.len64 s))
    (hbaseAddr : st.getReg baseBase + BitVec.ofInt 64 baseOff = L.T + BitVec.ofInt 64 (env.tab.base64 s))
    (hriVal : st.getReg ri = vi.toBitVec)
    (hmemRel : ProgMemRel env.tab L st.mem lm)
    (hlink : lkm.linkSpec (pre ++
        (loadMemOff .ld rLen lenBase rTmpLen lenOff ++
         [Asm.bgeu ri rLen errLabel] ++
         loadMemOff .ld AbiReg.t1 baseBase rTmpBase baseOff ++
         ld64Tail rd ri rTmpBase i) ++ post) =
        .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize
        (loadMemOff .ld rLen lenBase rTmpLen lenOff ++
         [Asm.bgeu ri rLen errLabel] ++
         loadMemOff .ld AbiReg.t1 baseBase rTmpBase baseOff ++
         ld64Tail rd ri rTmpBase i)) < 2 ^ 64) :
    let code :=
      loadMemOff .ld rLen lenBase rTmpLen lenOff ++
      [Asm.bgeu ri rLen errLabel] ++
      loadMemOff .ld AbiReg.t1 baseBase rTmpBase baseOff ++
      ld64Tail rd ri rTmpBase i
    if h : vi.toNat < (lm.arr64 s).size then
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize code)) ∧
        st'.getReg rd = ((lm.arr64 s)[vi.toNat]'h).toBitVec ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        st'.mem = st.mem ∧
        st'.getReg AbiReg.t4 = st.getReg AbiReg.t4
    else
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        st'.mem = st.mem := by
  cases hiC : i.constVal? with
  | some wi =>
    have hiEq : i = .const wi := expr_constVal_eq_some hiC
    have hviEq : vi = wi := by rw [hiEq] at hvi; exact (Prod.mk.inj (Except.ok.inj hvi)).1.symm
    subst hviEq
    by_cases hlt : vi.toNat < 256
    · have ht : ld64Tail rd ri rTmpBase i = [Asm.ld rd AbiReg.t1 (BitVec.ofNat 12 (8 * vi.toNat))] := by
        simp only [ld64Tail, hiC, hlt, ↓reduceIte]
      rw [ht] at hlink h64 ⊢
      exact reg_ld64_const_body_r env L fl lm s hsOk pre post rd ri lenBase baseBase rLen rTmpLen AbiReg.t1 rTmpBase
        hrd hri hrLen hrTmpLen (by decide) hrTmpBase hLenBaseTmpLen hBaseBaseLen hBaseBaseTmpLen hBaseBaseTmpBase hBaseBaseT6
        lenOff baseOff vi hlt st hpc hlenAddr hbaseAddr hriVal hmemRel hlink h64
    · have ht : ld64Tail rd ri rTmpBase i =
          [Asm.slli rTmpBase ri 3#6, Asm.add AbiReg.t1 AbiReg.t1 rTmpBase, Asm.ld rd AbiReg.t1 0#12] := by
        simp only [ld64Tail, hiC, hlt, ↓reduceIte]
      rw [ht] at hlink h64 ⊢
      exact reg_ld64_body_r env L fl lm s hsOk pre post rd ri lenBase baseBase rLen rTmpLen AbiReg.t1 rTmpBase
        hrd hri hrLen hrTmpLen (by decide) hrTmpBase hBaseTmp hLenBaseTmpLen hBaseBaseLen hBaseBaseTmpLen hBaseBaseTmpBase hBaseBaseT6
        lenOff baseOff vi st hpc hlenAddr hbaseAddr hriVal hmemRel hlink h64
  | none =>
    have ht : ld64Tail rd ri rTmpBase i =
        [Asm.slli rTmpBase ri 3#6, Asm.add AbiReg.t1 AbiReg.t1 rTmpBase, Asm.ld rd AbiReg.t1 0#12] := by
      simp only [ld64Tail, hiC]
    rw [ht] at hlink h64 ⊢
    exact reg_ld64_body_r env L fl lm s hsOk pre post rd ri lenBase baseBase rLen rTmpLen AbiReg.t1 rTmpBase
      hrd hri hrLen hrTmpLen (by decide) hrTmpBase hBaseTmp hLenBaseTmpLen hBaseBaseLen hBaseBaseTmpLen hBaseBaseTmpBase hBaseBaseT6
      lenOff baseOff vi st hpc hlenAddr hbaseAddr hriVal hmemRel hlink h64

/-- Dispatch `ld32tTail` to `reg_ld32t_const_body_r` or `reg_ld32t_body_r`. -/
private theorem reg_ld32tTail_body_r {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) (s : TieredArray) (hsOk : env.tab.wordPosOkB s = true)
    (i : Expr) (vi : _root_.L.Word) (hvi : _root_.L.evalE i ⟨lm, loc⟩ = .ok (vi, ⟨lm, loc⟩))
    (pre post : List AsmItem)
    (rd ri lenBase baseBase : Reg)
    (hrd : ValidTargetReg fl rd)
    (hri : ri = AbiReg.zero ∨ ri = AbiReg.a0 ∨ ri ∈ allowedRegs true)
    (hLenBase3 : lenBase ≠ AbiReg.t3)
    (hBaseBase2 : baseBase ≠ AbiReg.t2) (hBaseBase3 : baseBase ≠ AbiReg.t3) (hBaseBaseT6 : baseBase ≠ AbiReg.t6 ∧ baseBase ≠ AbiReg.s1)
    (lenOff baseOff : Int)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hlenAddr : st.getReg lenBase + BitVec.ofInt 64 lenOff = L.T + BitVec.ofInt 64 (env.tab.len64 s))
    (hbaseAddr : st.getReg baseBase + BitVec.ofInt 64 baseOff = L.T + BitVec.ofInt 64 (env.tab.base64 s))
    (hriVal : st.getReg ri = vi.toBitVec)
    (hmemRel : ProgMemRel env.tab L st.mem lm)
    (hlink : lkm.linkSpec (pre ++
        (loadMemOff .ld AbiReg.t2 lenBase AbiReg.t3 lenOff ++
         [Asm.srli AbiReg.t3 ri 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
         loadMemOff .ld AbiReg.t1 baseBase AbiReg.t3 baseOff ++
         ld32tTail rd ri i) ++ post) =
        .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize
        (loadMemOff .ld AbiReg.t2 lenBase AbiReg.t3 lenOff ++
         [Asm.srli AbiReg.t3 ri 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
         loadMemOff .ld AbiReg.t1 baseBase AbiReg.t3 baseOff ++
         ld32tTail rd ri i)) < 2 ^ 64) :
    let code :=
      loadMemOff .ld AbiReg.t2 lenBase AbiReg.t3 lenOff ++
      [Asm.srli AbiReg.t3 ri 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 baseBase AbiReg.t3 baseOff ++
      ld32tTail rd ri i
    if h : (vi / 2).toNat < (lm.arr64 s).size then
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize code)) ∧
        st'.getReg rd = (half32 ((lm.arr64 s)[(vi / 2).toNat]'h) vi).toBitVec ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        st'.mem = st.mem ∧
        st'.getReg AbiReg.t4 = st.getReg AbiReg.t4
    else
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        st'.mem = st.mem := by
  cases hiC : i.constVal? with
  | some wi =>
    have hiEq : i = .const wi := expr_constVal_eq_some hiC
    have hviEq : vi = wi := by rw [hiEq] at hvi; exact (Prod.mk.inj (Except.ok.inj hvi)).1.symm
    subst hviEq
    by_cases hlt : vi.toNat < 512
    · have ht : ld32tTail rd ri i = [Asm.lwu rd AbiReg.t1 (BitVec.ofNat 12 (4 * vi.toNat))] := by
        simp only [ld32tTail, hiC, hlt, ↓reduceIte]
      rw [ht] at hlink h64 ⊢
      exact reg_ld32t_const_body_r env L fl lm s hsOk pre post rd ri lenBase baseBase
        hrd hri hLenBase3 hBaseBase2 hBaseBase3 hBaseBaseT6 lenOff baseOff vi hlt
        st hpc hlenAddr hbaseAddr hriVal hmemRel hlink h64
    · have ht : ld32tTail rd ri i =
          [Asm.slli AbiReg.t3 ri 2#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3, Asm.lwu rd AbiReg.t1 0#12] := by
        simp only [ld32tTail, hiC, hlt, ↓reduceIte]
      rw [ht] at hlink h64 ⊢
      exact reg_ld32t_body_r env L fl lm s hsOk pre post rd ri lenBase baseBase
        hrd hri hLenBase3 hBaseBase2 hBaseBase3 hBaseBaseT6 lenOff baseOff vi
        st hpc hlenAddr hbaseAddr hriVal hmemRel hlink h64
  | none =>
    have ht : ld32tTail rd ri i =
        [Asm.slli AbiReg.t3 ri 2#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3, Asm.lwu rd AbiReg.t1 0#12] := by
      simp only [ld32tTail, hiC]
    rw [ht] at hlink h64 ⊢
    exact reg_ld32t_body_r env L fl lm s hsOk pre post rd ri lenBase baseBase
      hrd hri hLenBase3 hBaseBase2 hBaseBase3 hBaseBaseT6 lenOff baseOff vi
      st hpc hlenAddr hbaseAddr hriVal hmemRel hlink h64

/-- Dispatch `ld32hTail` to `reg_ld32h_const_body_r` or `reg_ld32h_body_r`. -/
private theorem reg_ld32hTail_body_r {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) (s : TieredArray) (hsOk : env.tab.wordPosOkB s = true) (hi : Bool)
    (i : Expr) (vi : _root_.L.Word) (hvi : _root_.L.evalE i ⟨lm, loc⟩ = .ok (vi, ⟨lm, loc⟩))
    (pre post : List AsmItem)
    (rd ri lenBase baseBase rLen rTmpLen rTmpBase : Reg)
    (hrd : ValidTargetReg fl rd)
    (hri : ri = AbiReg.zero ∨ ri = AbiReg.a0 ∨ ri ∈ allowedRegs true)
    (hrLen : rLen ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3])
    (hrTmpLen : rTmpLen ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3])
    (hrTmpBase : rTmpBase ∈ [AbiReg.t0, AbiReg.t1, AbiReg.t2, AbiReg.t3])
    (hBaseTmp : AbiReg.t1 ≠ rTmpBase)
    (hLenBaseTmpLen : lenBase ≠ rTmpLen)
    (hBaseBaseLen : baseBase ≠ rLen)
    (hBaseBaseTmpLen : baseBase ≠ rTmpLen)
    (hBaseBaseTmpBase : baseBase ≠ rTmpBase)
    (hBaseBaseT6 : baseBase ≠ AbiReg.t6 ∧ baseBase ≠ AbiReg.s1)
    (lenOff baseOff : Int)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hlenAddr : st.getReg lenBase + BitVec.ofInt 64 lenOff = L.T + BitVec.ofInt 64 (env.tab.len64 s))
    (hbaseAddr : st.getReg baseBase + BitVec.ofInt 64 baseOff = L.T + BitVec.ofInt 64 (env.tab.base64 s))
    (hriVal : st.getReg ri = vi.toBitVec)
    (hmemRel : ProgMemRel env.tab L st.mem lm)
    (hlink : lkm.linkSpec (pre ++
        (loadMemOff .ld rLen lenBase rTmpLen lenOff ++
         [Asm.bgeu ri rLen errLabel] ++
         loadMemOff .ld AbiReg.t1 baseBase rTmpBase baseOff ++
         ld32hTail rd ri rTmpBase i hi) ++ post) =
        .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize
        (loadMemOff .ld rLen lenBase rTmpLen lenOff ++
         [Asm.bgeu ri rLen errLabel] ++
         loadMemOff .ld AbiReg.t1 baseBase rTmpBase baseOff ++
         ld32hTail rd ri rTmpBase i hi)) < 2 ^ 64) :
    let code :=
      loadMemOff .ld rLen lenBase rTmpLen lenOff ++
      [Asm.bgeu ri rLen errLabel] ++
      loadMemOff .ld AbiReg.t1 baseBase rTmpBase baseOff ++
      ld32hTail rd ri rTmpBase i hi
    if h : vi.toNat < (lm.arr64 s).size then
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize code)) ∧
        st'.getReg rd = (half32b hi ((lm.arr64 s)[vi.toNat]'h)).toBitVec ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        st'.mem = st.mem ∧
        st'.getReg AbiReg.t4 = st.getReg AbiReg.t4
    else
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        st'.mem = st.mem := by
  cases hiC : i.constVal? with
  | some wi =>
    have hiEq : i = .const wi := expr_constVal_eq_some hiC
    have hviEq : vi = wi := by rw [hiEq] at hvi; exact (Prod.mk.inj (Except.ok.inj hvi)).1.symm
    subst hviEq
    by_cases hlt : vi.toNat < 255
    · have ht : ld32hTail rd ri rTmpBase i hi =
          [Asm.lwu rd AbiReg.t1 (BitVec.ofNat 12 (8 * vi.toNat + if hi then 4 else 0))] := by
        simp only [ld32hTail, hiC, hlt, ↓reduceIte]
      rw [ht] at hlink h64 ⊢
      exact reg_ld32h_const_body_r env L fl lm s hsOk hi pre post rd ri lenBase baseBase rLen rTmpLen AbiReg.t1 rTmpBase
        hrd hri hrLen hrTmpLen (by decide) hrTmpBase hLenBaseTmpLen hBaseBaseLen hBaseBaseTmpLen hBaseBaseTmpBase hBaseBaseT6
        lenOff baseOff vi hlt st hpc hlenAddr hbaseAddr hriVal hmemRel hlink h64
    · have ht : ld32hTail rd ri rTmpBase i hi =
          [Asm.slli rTmpBase ri 3#6, Asm.add AbiReg.t1 AbiReg.t1 rTmpBase,
           Asm.lwu rd AbiReg.t1 (if hi then 4#12 else 0#12)] := by
        simp only [ld32hTail, hiC, hlt, ↓reduceIte]
      rw [ht] at hlink h64 ⊢
      exact reg_ld32h_body_r env L fl lm s hsOk hi pre post rd ri lenBase baseBase rLen rTmpLen AbiReg.t1 rTmpBase
        hrd hri hrLen hrTmpLen (by decide) hrTmpBase hBaseTmp hLenBaseTmpLen hBaseBaseLen hBaseBaseTmpLen hBaseBaseTmpBase hBaseBaseT6
        lenOff baseOff vi st hpc hlenAddr hbaseAddr hriVal hmemRel hlink h64
  | none =>
    have ht : ld32hTail rd ri rTmpBase i hi =
        [Asm.slli rTmpBase ri 3#6, Asm.add AbiReg.t1 AbiReg.t1 rTmpBase,
         Asm.lwu rd AbiReg.t1 (if hi then 4#12 else 0#12)] := by
      simp only [ld32hTail, hiC]
    rw [ht] at hlink h64 ⊢
    exact reg_ld32h_body_r env L fl lm s hsOk hi pre post rd ri lenBase baseBase rLen rTmpLen AbiReg.t1 rTmpBase
      hrd hri hrLen hrTmpLen (by decide) hrTmpBase hBaseTmp hLenBaseTmpLen hBaseBaseLen hBaseBaseTmpLen hBaseBaseTmpBase hBaseBaseT6
      lenOff baseOff vi st hpc hlenAddr hbaseAddr hriVal hmemRel hlink h64

private theorem reg_evalExpr_ld64t_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (a : ArrId) (t i : Expr) (iht : RegEvalExprIH env L fl lm loc sp t) (ihi : RegEvalExprIH env L fl lm loc sp i)
    (pre post : List AsmItem) (tmp : Nat) (rd : Reg) (hrd : ValidTargetReg fl rd)
    (heOk : exprOkB env.tab fl.nlocals (.ld64t a t i) = true)
    (hVfT : ExprVarsInFrame fl t)
    (hTmp : tmp + usedTempsExpr (.ld64t a t i) ≤ fl.usedTemps)
    (hlink : lkm.linkSpec (pre ++ compileETo env.tab fl tmp rd (.ld64t a t i) ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd (.ld64t a t i))) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    match _root_.L.evalE (.ld64t a t i) ⟨lm, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd (.ld64t a t i)))) ∧
        st'.getReg rd = v.toBitVec ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem ∧
        (exprNoT4 (.ld64t a t i) = true → st'.getReg AbiReg.t4 = st.getReg AbiReg.t4)
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
  simp only [exprOkB, Bool.and_eq_true] at heOk
  simp only [usedTempsExpr] at hTmp
  cases htC : t.constVal? with
  | some w =>
    have hteq : t = .const w := expr_constVal_eq_some htC
    have hvt : _root_.L.evalE t ⟨lm, loc⟩ = .ok (w, ⟨lm, loc⟩) := by rw [hteq]; rfl
    have hst : isSimpleExpr t = true := isSimpleExpr_of_constVal htC
    simp only [hst, ↓reduceIte] at hTmp
    let s := tierA a w
    let pI := match exprReg? fl.alloc i with | some r => ([], r) | none => (compileETo env.tab fl tmp AbiReg.a0 i, AbiReg.a0)
    let cbody :=
      loadMemOff .ld AbiReg.t2 (gpBaseReg fl.useT5Gp (env.tab.len64 s)) AbiReg.t3 (gpAdjOff fl.useT5Gp (env.tab.len64 s)) ++
      [Asm.bgeu pI.2 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 (gpBaseReg fl.useT5Gp (env.tab.base64 s)) AbiReg.t3 (gpAdjOff fl.useT5Gp (env.tab.base64 s)) ++
      ld64Tail rd pI.2 AbiReg.t3 i
    have hdef : compileETo env.tab fl tmp rd (.ld64t a t i) = pI.1 ++ cbody := by
      cases h : exprReg? fl.alloc i <;>
        simp [compileETo, htC, s, pI, h, cbody, loadMemOffGp_eq_loadMemOff, List.append_assoc]
    rw [hdef] at hlink h64 ⊢
    have htw_all : lkm.totalSize (pI.1 ++ cbody) = lkm.totalSize pI.1 + lkm.totalSize cbody := lkm.totalSize_append _ _
    have riRes := reg_evalIdx_of_ih env L fl hfl lm loc i pre (cbody ++ post) tmp heOk.2 hTmp
      (fun p q tm r st' hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => ihi p q tm r hr heOk.2 ht hl h6 st' hpc' hgp' ht5' hsp' hm' hf')
      (by simpa only [pI, List.append_assoc] using hlink)
      (by rw [htw_all] at h64; dsimp only [pI] at h64 ⊢; omega) st hpc hgp ht5 hsp hmemRel hframeOk
    rcases riRes with ⟨hri, riSim⟩
    rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
    · simp only [hvi] at riSim
      obtain ⟨k1, st1, hrun1, hpc1, hri1, hpres1, heq1, ht4_1⟩ := riSim
      have htw1 : lkm.totalSize (pre ++ pI.1) = lkm.totalSize pre + lkm.totalSize pI.1 := lkm.totalSize_append _ _
      have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.abi.gp.trans hgp
      have ht5_1 : T5GpOk L fl st1 := ht5.of_preserved hpres1
      have hmemRel1 := ProgMemRel.of_tempSpanR hlo hhi (by omega) heq1 hmemRel
      have hsOk : env.tab.wordPosOkB s = true := (tieredOk_len64_addr_T L.T a w heOk.1.1).1
      have rb := reg_ld64Tail_body_r env L fl lm loc s hsOk i vi hvi (pre ++ pI.1) post rd pI.2
        (gpBaseReg fl.useT5Gp (env.tab.len64 s)) (gpBaseReg fl.useT5Gp (env.tab.base64 s))
        AbiReg.t2 AbiReg.t3 AbiReg.t3 hrd hri (by decide) (by decide) (by decide) (by decide)
        (gpBaseReg_ne_temp _ _ (by decide)) (gpBaseReg_ne_temp _ _ (by decide))
        (gpBaseReg_ne_temp _ _ (by decide)) (gpBaseReg_ne_temp _ _ (by decide)) (gpBaseReg_ne_t6_s1 _ _)
        (gpAdjOff fl.useT5Gp (env.tab.len64 s)) (gpAdjOff fl.useT5Gp (env.tab.base64 s))
        st1 (by rw [htw1]; exact hpc1) (gpBaseReg_addr hgp1 ht5_1) (gpBaseReg_addr hgp1 ht5_1)
        hri1 hmemRel1 (by simpa only [cbody, List.append_assoc] using hlink)
        (by rw [htw1]; rw [htw_all] at h64; dsimp only [cbody] at h64; omega)
      by_cases hbound : vi.toNat < (lm.arr64 s).size
      · simp only [hbound, ↓reduceDIte] at rb
        obtain ⟨k2, st2, hrun2, hpc2, hrd2, hpres2, hmem2, ht4_2⟩ := rb
        have hev : _root_.L.evalE (.ld64t a t i) ⟨lm, loc⟩ = .ok ((lm.arr64 s)[vi.toNat]'hbound, ⟨lm, loc⟩) := by
          change (_root_.L.evalE t >>= fun u => _root_.L.evalE i >>= _root_.L.ld64 (tierA a u)) ⟨lm, loc⟩ = _
          simp only [Bind.bind, StateT.bind, Except.bind, hvt, hvi, _root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get]
          simp [s, hbound, Pure.pure, StateT.pure, Except.pure]
        rw [hev]
        exact ⟨k1 + k2, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
          by dsimp only [cbody] at htw_all; rw [hpc2, htw1, htw_all]; congr 2; omega, hrd2,
          (PreservedFrameRegs.of_a0 hpres1).trans hpres2, by rw [hmem2]; exact heq1,
          fun hnt => ht4_2.trans (ht4_1 (by simp only [exprNoT4, hst, Bool.true_and] at hnt; exact hnt))⟩
      · simp only [hbound, ↓reduceDIte] at rb
        obtain ⟨k2, st2, hrun2, hpc2, hpres2, hmem2⟩ := rb
        have hev : _root_.L.evalE (.ld64t a t i) ⟨lm, loc⟩ = .error .oob := by
          change (_root_.L.evalE t >>= fun u => _root_.L.evalE i >>= _root_.L.ld64 (tierA a u)) ⟨lm, loc⟩ = _
          simp only [Bind.bind, StateT.bind, Except.bind, hvt, hvi, _root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get]
          simp [s, hbound, Pure.pure, Except.pure, Function.comp_apply, throw, throwThe, MonadExceptOf.throw, StateT.lift]; rfl
        rw [hev]
        exact ⟨k1 + k2, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
          hpc2, (PreservedFrameRegs.of_a0 hpres1).trans hpres2, by rw [hmem2]; exact heq1⟩
    · simp only [hvi] at riSim
      obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := riSim
      have hev : _root_.L.evalE (.ld64t a t i) ⟨lm, loc⟩ = .error .oob := by
        dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hvt]; dsimp only; rw [hvi]; try rfl
      rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
  | none =>
    let pH := match exprReg? fl.alloc t with
      | some r => match exprReg? fl.alloc i with
        | some ri => ([], r, ri) | none => (compileETo env.tab fl tmp AbiReg.a0 i, r, AbiReg.a0)
      | none => match emitSimpleExprR env.tab fl AbiReg.t0 AbiReg.t1 t with
        | some ct => match exprReg? fl.alloc i with
          | some ri => (ct, AbiReg.t0, ri) | none => (compileETo env.tab fl tmp AbiReg.a0 i ++ ct, AbiReg.t0, AbiReg.a0)
        | none =>
          (compileETo env.tab fl tmp AbiReg.a0 t ++
           storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp) ++
           compileETo env.tab fl (tmp + 1) AbiReg.a0 i ++
           loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff tmp), AbiReg.t0, AbiReg.a0)
    let chdr := [Asm.andi AbiReg.t0 pH.2.1 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0]
    let cbody :=
      loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (env.tab.len64 (TieredArray.t0 a)) ++
      [Asm.bgeu pH.2.2 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t3 (env.tab.base64 (TieredArray.t0 a)) ++
      ld64Tail rd pH.2.2 AbiReg.t3 i
    have hdef : compileETo env.tab fl tmp rd (.ld64t a t i) = pH.1 ++ chdr ++ cbody := by
      cases ht' : exprReg? fl.alloc t with
      | some r => cases hi' : exprReg? fl.alloc i <;> simp [compileETo, htC, pH, chdr, cbody, ht', hi', List.append_assoc]
      | none =>
        cases hs' : emitSimpleExprR env.tab fl AbiReg.t0 AbiReg.t1 t with
        | some ct => cases hi' : exprReg? fl.alloc i <;> simp [compileETo, htC, pH, chdr, cbody, ht', hs', hi', List.append_assoc]
        | none => simp [compileETo, htC, pH, chdr, cbody, ht', hs', List.append_assoc]
    rw [hdef] at hlink h64 ⊢
    have htw_hdr : lkm.totalSize chdr = 3 := by
      simp [chdr, Asm.andi, Asm.slli, Asm.add, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
    have htw_all : lkm.totalSize (pH.1 ++ chdr ++ cbody) = lkm.totalSize pH.1 + 3 + lkm.totalSize cbody := by
      simp only [lkm.totalSize_append, htw_hdr]
    have rHead := reg_evalTierHead_of_ih env L fl hfl lm loc hspAlign hlo hhi t i pre (chdr ++ cbody ++ post) tmp
      heOk.1.2 heOk.2 hVfT hTmp
      (fun p q tm r st' hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => by
        have r := iht p q tm r hr heOk.1.2 ht hl h6 st' hpc' hgp' ht5' hsp' hm' hf'
        cases hv : _root_.L.evalE t ⟨lm, loc⟩ with
        | ok _ => simp only [hv] at r; rcases r with ⟨k, st2, h1, h2, h3, h4, h5, _⟩; exact ⟨k, st2, h1, h2, h3, h4, h5⟩
        | error _ => simp only [hv] at r; exact r)
      (fun p q tm r st' hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => ihi p q tm r hr heOk.2 ht hl h6 st' hpc' hgp' ht5' hsp' hm' hf')
      (by simpa only [pH, List.append_assoc] using hlink)
      (by rw [htw_all] at h64; dsimp only [pH] at h64 ⊢; omega) st hpc hgp ht5 hsp hmemRel hframeOk
    rcases rHead with ⟨hri, headSim⟩
    rcases _root_.L.evalE_pure t ⟨lm, loc⟩ with ⟨vt, hvt⟩ | hvt
    · rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
      · simp only [hvt, hvi] at headSim
        obtain ⟨k1, st1, hrun1, hpc1, hrt1, hri1, hpres1, heq1, ht4_1⟩ := headSim
        have htw1 : lkm.totalSize (pre ++ pH.1) = lkm.totalSize pre + lkm.totalSize pH.1 := lkm.totalSize_append _ _
        have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.abi.gp.trans hgp
        have hmemRel1 := ProgMemRel.of_tempSpanR hlo hhi (by omega) heq1 hmemRel
        obtain ⟨st2, hrun2, hpc2, ht1_2, hmem2, hpres2, hoth2⟩ :=
          step_tierHdr_r env fl (pre ++ pH.1) (cbody ++ post) pH.2.1 vt
            (by simpa only [chdr, List.append_assoc] using hlink)
            (by rw [htw1]; rw [htw_all] at h64; omega) st1 (by rw [htw1]; exact hpc1) hgp1 hrt1
        have htw2 : lkm.totalSize (pre ++ pH.1 ++ chdr) = lkm.totalSize pre + lkm.totalSize pH.1 + 3 := by
          rw [lkm.totalSize_append, htw1, htw_hdr]
        have hta := tieredOk_len64_addr_T L.T a vt heOk.1.1
        have hri2 : st2.getReg pH.2.2 = vi.toBitVec :=
          (hoth2 pH.2.2 (idxReg_ne_temp hri (by decide)) (idxReg_ne_temp hri (by decide))).trans hri1
        have rb := reg_ld64Tail_body_r env L fl lm loc (tierA a vt) hta.1 i vi hvi (pre ++ pH.1 ++ chdr) post rd pH.2.2
          AbiReg.t1 AbiReg.t1 AbiReg.t2 AbiReg.t3 AbiReg.t3
          hrd hri (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (env.tab.len64 (TieredArray.t0 a)) (env.tab.base64 (TieredArray.t0 a))
          st2 (by rw [htw2, ← htw1]; exact hpc2) (by rw [ht1_2]; exact hta.2.1) (by rw [ht1_2]; exact hta.2.2)
          hri2 (by rw [hmem2]; exact hmemRel1)
          (by simpa only [cbody, List.append_assoc] using hlink)
          (by rw [htw2]; rw [htw_all] at h64; dsimp only [cbody] at h64; omega)
        by_cases hbound : vi.toNat < (lm.arr64 (tierA a vt)).size
        · simp only [hbound, ↓reduceDIte] at rb
          obtain ⟨k3, st3, hrun3, hpc3, hrd3, hpres3, hmem3, ht4_3⟩ := rb
          have hev : _root_.L.evalE (.ld64t a t i) ⟨lm, loc⟩ = .ok ((lm.arr64 (tierA a vt))[vi.toNat]'hbound, ⟨lm, loc⟩) := by
            change (_root_.L.evalE t >>= fun u => _root_.L.evalE i >>= _root_.L.ld64 (tierA a u)) ⟨lm, loc⟩ = _
            simp only [Bind.bind, StateT.bind, Except.bind, hvt, hvi, _root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get]
            simp [hbound, Pure.pure, StateT.pure, Except.pure]
          rw [hev]
          exact ⟨k1 + (3 + k3), st3,
            by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
            by dsimp only [cbody] at htw_all; rw [hpc3, htw2, htw_all]; congr 2; omega, hrd3,
            (PreservedFrameRegs.of_a0 (hpres1.trans hpres2)).trans hpres3, by rw [hmem3, hmem2]; exact heq1,
            fun hnt => by
              simp only [exprNoT4, Bool.and_eq_true] at hnt
              exact ht4_3.trans ((hoth2 AbiReg.t4 (by decide) (by decide)).trans (ht4_1 hnt.1 hnt.2))⟩
        · simp only [hbound, ↓reduceDIte] at rb
          obtain ⟨k3, st3, hrun3, hpc3, hpres3, hmem3⟩ := rb
          have hev : _root_.L.evalE (.ld64t a t i) ⟨lm, loc⟩ = .error .oob := by
            change (_root_.L.evalE t >>= fun u => _root_.L.evalE i >>= _root_.L.ld64 (tierA a u)) ⟨lm, loc⟩ = _
            simp only [Bind.bind, StateT.bind, Except.bind, hvt, hvi, _root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get]
            simp [hbound, Pure.pure, Except.pure, Function.comp_apply, throw, throwThe, MonadExceptOf.throw, StateT.lift]; rfl
          rw [hev]
          exact ⟨k1 + (3 + k3), st3,
            by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
            hpc3, (PreservedFrameRegs.of_a0 (hpres1.trans hpres2)).trans hpres3, by rw [hmem3, hmem2]; exact heq1⟩
      · simp only [hvt, hvi] at headSim
        obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := headSim
        have hev : _root_.L.evalE (.ld64t a t i) ⟨lm, loc⟩ = .error .oob := by
          dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hvt]; dsimp only; rw [hvi]; try rfl
        rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
    · simp only [hvt] at headSim
      obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := headSim
      have hev : _root_.L.evalE (.ld64t a t i) ⟨lm, loc⟩ = .error .oob := by
        dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hvt]
      rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩

private def ld8x8SetupSrcR (tab : Tab) (useT5 : Bool) : BSrc → List AsmItem
  | .arr a => loadMemOffGp useT5 .ld AbiReg.t0 AbiReg.t2 (tab.len8 a) ++
              loadMemOffGp useT5 .ld AbiReg.t1 AbiReg.t2 (tab.base8 a)
  | .rom d => li AbiReg.t0 (BitVec.ofNat 64 d.length) ++
              addImmOff AbiReg.t1 AbiReg.gp AbiReg.t2 (tab.romBase + (romIdx d tab.rom : Int))

private theorem reg_ld8x8_setup_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (lm : _root_.L.Mem)
    (src : BSrc) (rI : Reg) (hrI : rI = AbiReg.zero ∨ rI = AbiReg.a0 ∨ rI ∈ allowedRegs true) (vi : UInt64)
    (rd : Reg) (pre post : List AsmItem)
    (hsrcOk : bsrcOkB env.tab src = true)
    (hlink : lkm.linkSpec (pre ++ ld8x8SetupSrcR env.tab fl.useT5Gp src ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (ld8x8SetupSrcR env.tab fl.useT5Gp src)) < 2 ^ 64)
    (st1 : State) (hpc1 : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp1 : st1.getReg AbiReg.gp = L.T) (ht5_1 : T5GpOk L fl st1) (hrI1 : st1.getReg rI = vi.toBitVec)
    (hmemRel1 : ProgMemRel env.tab L st1.mem lm) :
    ∃ ks st2, RV64.run env.rom ks st1 = .cont st2 ∧
      st2.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (ld8x8SetupSrcR env.tab fl.useT5Gp src))) ∧
      st2.getReg AbiReg.t0 = BitVec.ofNat 64 (lm.src8 src).size ∧
      (lm.src8 src).size < 2 ^ 64 ∧
      st2.getReg rI = vi.toBitVec ∧
      (∀ j (hj : j < (lm.src8 src).size), st2.mem (st2.getReg AbiReg.t1 + BitVec.ofNat 64 j) = ((lm.src8 src)[j]'hj).toBitVec) ∧
      PreservedFrameRegs fl (· = rd) st1 st2 ∧
      st2.mem = st1.mem ∧
      st2.getReg AbiReg.t4 = st1.getReg AbiReg.t4 := by
  cases src with
  | arr a =>
    dsimp only [bsrcOkB, _root_.L.Mem.src8, ld8x8SetupSrcR] at hsrcOk hlink h64 ⊢
    rcases hmemRel1.1 a hsrcOk with ⟨_, hlt64, hlenR, hbaseR, hbytesR⟩
    let c1 := loadMemOffGp fl.useT5Gp .ld AbiReg.t0 AbiReg.t2 (env.tab.len8 a)
    let c2 := loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (env.tab.base8 a)
    have htw_s : lkm.totalSize (c1 ++ c2) = lkm.totalSize c1 + lkm.totalSize c2 := lkm.totalSize_append c1 c2
    have h64' : 4 * (lkm.totalSize pre + (lkm.totalSize c1 + lkm.totalSize c2)) < 2 ^ 64 := by
      dsimp only [c1, c2] at htw_s ⊢; rw [← htw_s]; exact h64
    have hal1 : isAligned (L.T + BitVec.ofInt 64 (env.tab.len8 a)) 8 = true := by
      rw [Tab.len8_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨sa, hra, hotha, ht0a, hmema, hpca⟩ :=
      loadMemOffGp_ld_correct_lm lkm env.hrom pre (c2 ++ post) fl.useT5Gp
        AbiReg.t0 AbiReg.t2 (by decide) (by decide) (by decide) (fun _ => by decide) (env.tab.len8 a) L.T
        (by simpa only [c1, c2, List.append_assoc] using hlink)
        (by dsimp only [c1] at h64' ⊢; omega) st1 hpc1 hgp1 ht5_1 hal1
    have htwa : lkm.totalSize (pre ++ c1) = lkm.totalSize pre + lkm.totalSize c1 := lkm.totalSize_append pre c1
    have hgpa : sa.getReg AbiReg.gp = L.T := (hotha AbiReg.gp (by decide) (by decide)).trans hgp1
    have ht5a : T5GpOk L fl sa := fun h => (hotha AbiReg.t5 (by decide) (by decide)).trans (ht5_1 h)
    have hal2 : isAligned (L.T + BitVec.ofInt 64 (env.tab.base8 a)) 8 = true := by
      rw [Tab.base8_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨sb, hrb, hothb, ht1b, hmemb, hpcb⟩ :=
      loadMemOffGp_ld_correct_lm lkm env.hrom (pre ++ c1) post fl.useT5Gp
        AbiReg.t1 AbiReg.t2 (by decide) (by decide) (by decide) (fun _ => by decide) (env.tab.base8 a) L.T
        (by simpa only [c1, c2, List.append_assoc] using hlink)
        (by rw [htwa]; dsimp only [c2] at h64' ⊢; omega) sa (by rw [htwa]; exact hpca) hgpa ht5a hal2
    refine ⟨lkm.totalSize c1 + lkm.totalSize c2, sb, by rw [run_add, hra]; dsimp only; exact hrb,
      by rw [hpcb, htwa]; dsimp only [c1, c2] at htw_s ⊢; rw [htw_s]; congr 2; omega,
      by rw [hothb AbiReg.t0 (by decide) (by decide), ht0a, hlenR], hlt64,
      (hothb rI (idxReg_ne_temp hrI (by decide)) (idxReg_ne_temp hrI (by decide))).trans
        ((hotha rI (idxReg_ne_temp hrI (by decide)) (idxReg_ne_temp hrI (by decide))).trans hrI1),
      fun j hj => by rw [hmemb, hmema, ht1b, hmema, hbaseR]; exact hbytesR j hj,
      (PreservedFrameRegs.of_scratch2 AbiReg.t0 AbiReg.t2 (by decide) (by decide) hotha).trans
        (PreservedFrameRegs.of_scratch2 AbiReg.t1 AbiReg.t2 (by decide) (by decide) hothb),
      hmemb.trans hmema,
      (hothb AbiReg.t4 (by decide) (by decide)).trans (hotha AbiReg.t4 (by decide) (by decide))⟩
  | rom d =>
    dsimp only [bsrcOkB, _root_.L.Mem.src8, ld8x8SetupSrcR] at hsrcOk hlink h64 ⊢
    have ⟨hromBound, hromBytes⟩ := Tab.romSliceOk_spec hsrcOk
    have hdlt64 : d.length < 2 ^ 64 := by
      have hrb16 : 16 ≤ env.tab.romBase.toNat := by simp [Tab.romBase]; omega
      have := L.tab_rom_bound; have := L.hTValid; omega
    let c1 := li AbiReg.t0 (BitVec.ofNat 64 d.length)
    let c2 := addImmOff AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.romBase + (romIdx d env.tab.rom : Int))
    have htw_s : lkm.totalSize (c1 ++ c2) = lkm.totalSize c1 + lkm.totalSize c2 := lkm.totalSize_append c1 c2
    have h64' : 4 * (lkm.totalSize pre + (lkm.totalSize c1 + lkm.totalSize c2)) < 2 ^ 64 := by
      dsimp only [c1, c2] at htw_s ⊢; rw [← htw_s]; exact h64
    obtain ⟨sa, hra, hotha, ht0a, hmema, hpca⟩ :=
      li_correct_lm lkm env.hrom pre (c2 ++ post)
        AbiReg.t0 (by decide) (BitVec.ofNat 64 d.length)
        (by simpa only [c1, c2, List.append_assoc] using hlink)
        (by dsimp only [c1] at h64' ⊢; omega) st1 hpc1
    have htwa : lkm.totalSize (pre ++ c1) = lkm.totalSize pre + lkm.totalSize c1 := lkm.totalSize_append pre c1
    have hgpa : sa.getReg AbiReg.gp = L.T := (hotha AbiReg.gp (by decide)).trans hgp1
    obtain ⟨sb, hrb, hothb, ht1b, hmemb, hpcb⟩ :=
      addImmOff_correct_lm lkm env.hrom (pre ++ c1) post
        AbiReg.t1 AbiReg.gp AbiReg.t2 (by decide) (by decide) (by decide)
        (env.tab.romBase + (romIdx d env.tab.rom : Int))
        (by simpa only [c1, c2, List.append_assoc] using hlink)
        (by rw [htwa]; dsimp only [c2] at h64' ⊢; omega) sa (by rw [htwa]; exact hpca)
    have hrbNN : 0 ≤ env.tab.romBase := by simp [Tab.romBase]; omega
    refine ⟨lkm.totalSize c1 + lkm.totalSize c2, sb, by rw [run_add, hra]; dsimp only; exact hrb,
      by rw [hpcb, htwa]; dsimp only [c1, c2] at htw_s ⊢; rw [htw_s]; congr 2; omega,
      by rw [hothb AbiReg.t0 (by decide) (by decide), ht0a]; simp,
      by simpa using hdlt64,
      (hothb rI (idxReg_ne_temp hrI (by decide)) (idxReg_ne_temp hrI (by decide))).trans
        ((hotha rI (idxReg_ne_temp hrI (by decide))).trans hrI1),
      fun j hj => by
        have hjl : j < d.length := by simpa using hj
        rw [hmemb, hmema, ht1b, hgpa]
        have hoffEq : BitVec.ofInt 64 (env.tab.romBase + (romIdx d env.tab.rom : Int)) =
            BitVec.ofNat 64 (env.tab.romBase.toNat + romIdx d env.tab.rom) := by
          rw [show env.tab.romBase + (romIdx d env.tab.rom : Int) = ((env.tab.romBase.toNat + romIdx d env.tab.rom : Nat) : Int) by omega,
              BitVec.ofInt_natCast]
        rw [hoffEq, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc,
            hmemRel1.2.2.1 (romIdx d env.tab.rom + j) (by omega)]
        have hbEq := hromBytes j hjl
        rw [List.getElem?_eq_getElem (by omega)] at hbEq
        have hdEq : env.tab.rom[romIdx d env.tab.rom + j]'(by omega) = d[j]'hjl := Option.some.inj hbEq
        rw [hdEq]; simp,
      (PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hotha).trans
        (PreservedFrameRegs.of_scratch2 AbiReg.t1 AbiReg.t2 (by decide) (by decide) hothb),
      hmemb.trans hmema,
      (hothb AbiReg.t4 (by decide) (by decide)).trans (hotha AbiReg.t4 (by decide))⟩

private theorem reg_ld8x8_body_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (fl : FrameLayout) (pre post : List AsmItem)
    (rI : Reg) (hrI : rI = AbiReg.zero ∨ rI = AbiReg.a0 ∨ rI ∈ allowedRegs true) (vi : UInt64)
    (rd : Reg) (hrd : ValidTargetReg fl rd)
    (bytes : Array UInt8) (hszlt : bytes.size < 2 ^ 64)
    (hlink : lkm.linkSpec (pre ++
      [Asm.addi AbiReg.t2 AbiReg.zero 8#12, Asm.bltu AbiReg.t0 AbiReg.t2 errLabel,
       Asm.addi AbiReg.t0 AbiReg.t0 (-8#12), Asm.bltu AbiReg.t0 rI errLabel, Asm.add AbiReg.t1 AbiReg.t1 rI] ++
      ([Asm.lbu rd AbiReg.t1 7#12] ++
        ([6, 5, 4, 3, 2, 1, 0].flatMap fun k =>
          [Asm.lbu AbiReg.t2 AbiReg.t1 (BitVec.ofInt 12 (k : Int)), Asm.slli rd rd 8#6, Asm.or rd rd AbiReg.t2])) ++
      post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre +
      lkm.totalSize ([Asm.addi AbiReg.t2 AbiReg.zero 8#12, Asm.bltu AbiReg.t0 AbiReg.t2 errLabel,
       Asm.addi AbiReg.t0 AbiReg.t0 (-8#12), Asm.bltu AbiReg.t0 rI errLabel, Asm.add AbiReg.t1 AbiReg.t1 rI] ++
      ([Asm.lbu rd AbiReg.t1 7#12] ++
        ([6, 5, 4, 3, 2, 1, 0].flatMap fun k =>
          [Asm.lbu AbiReg.t2 AbiReg.t1 (BitVec.ofInt 12 (k : Int)), Asm.slli rd rd 8#6, Asm.or rd rd AbiReg.t2])))) < 2 ^ 64)
    (st2 : State) (hpc2 : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (ht0_2 : st2.getReg AbiReg.t0 = BitVec.ofNat 64 bytes.size)
    (hrI2 : st2.getReg rI = vi.toBitVec)
    (hbytes2 : ∀ j (hj : j < bytes.size), st2.mem (st2.getReg AbiReg.t1 + BitVec.ofNat 64 j) = (bytes[j]'hj).toBitVec) :
    if vi.toNat + 8 ≤ bytes.size then
      ∃ k st', RV64.run env.rom k st2 = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre +
          lkm.totalSize ([Asm.addi AbiReg.t2 AbiReg.zero 8#12, Asm.bltu AbiReg.t0 AbiReg.t2 errLabel,
            Asm.addi AbiReg.t0 AbiReg.t0 (-8#12), Asm.bltu AbiReg.t0 rI errLabel, Asm.add AbiReg.t1 AbiReg.t1 rI] ++
          ([Asm.lbu rd AbiReg.t1 7#12] ++
            ([6, 5, 4, 3, 2, 1, 0].flatMap fun k =>
              [Asm.lbu AbiReg.t2 AbiReg.t1 (BitVec.ofInt 12 (k : Int)), Asm.slli rd rd 8#6, Asm.or rd rd AbiReg.t2]))))) ∧
        st'.getReg rd = (le64 bytes vi.toNat).toBitVec ∧
        PreservedFrameRegs fl (· = rd) st2 st' ∧
        st'.mem = st2.mem ∧
        st'.getReg AbiReg.t4 = st2.getReg AbiReg.t4
    else
      ∃ k st', RV64.run env.rom k st2 = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = rd) st2 st' ∧
        st'.mem = st2.mem := by
  let readBytes := [Asm.lbu rd AbiReg.t1 7#12] ++
    ([6, 5, 4, 3, 2, 1, 0].flatMap fun k =>
      [Asm.lbu AbiReg.t2 AbiReg.t1 (BitVec.ofInt 12 (k : Int)), Asm.slli rd rd 8#6, Asm.or rd rd AbiReg.t2])
  let cchk := [Asm.addi AbiReg.t2 AbiReg.zero 8#12, Asm.bltu AbiReg.t0 AbiReg.t2 errLabel,
    Asm.addi AbiReg.t0 AbiReg.t0 (-8#12), Asm.bltu AbiReg.t0 rI errLabel, Asm.add AbiReg.t1 AbiReg.t1 rI]
  let br1 := [Asm.bltu AbiReg.t0 AbiReg.t2 errLabel]
  let br2 := [Asm.bltu AbiReg.t0 rI errLabel]
  have htw_rb : lkm.totalSize readBytes = 22 := by
    simp [readBytes, Asm.lbu, Asm.slli, Asm.or, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
  have htw_chk : lkm.totalSize cchk = 1 + lkm.totalSize br1 + 1 + lkm.totalSize br2 + 1 := by
    simp [cchk, br1, br2, Asm.addi, Asm.add, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]; omega
  have htw_body : lkm.totalSize (cchk ++ readBytes) = (1 + lkm.totalSize br1 + 1 + lkm.totalSize br2 + 1) + 22 := by
    rw [lkm.totalSize_append, htw_chk, htw_rb]
  have hlink0 : lkm.linkSpec (pre ++ cchk ++ readBytes ++ post) = .ok (env.code, env.labels) := hlink
  have h64_0 : 4 * (lkm.totalSize pre + lkm.totalSize (cchk ++ readBytes)) < 2 ^ 64 := h64
  have hsAddi8 := step_item_instr_lm lkm env.hrom pre
    ([Asm.bltu AbiReg.t0 AbiReg.t2 errLabel, Asm.addi AbiReg.t0 AbiReg.t0 (-8#12),
      Asm.bltu AbiReg.t0 rI errLabel, Asm.add AbiReg.t1 AbiReg.t1 rI] ++ readBytes ++ post)
    (.aluImm .addi AbiReg.t2 AbiReg.zero 8#12)
    (by
      have heq : pre ++ [Asm.addi AbiReg.t2 AbiReg.zero 8#12] ++
          ([Asm.bltu AbiReg.t0 AbiReg.t2 errLabel, Asm.addi AbiReg.t0 AbiReg.t0 (-8#12),
            Asm.bltu AbiReg.t0 rI errLabel, Asm.add AbiReg.t1 AbiReg.t1 rI] ++ readBytes ++ post) =
          pre ++ cchk ++ readBytes ++ post := by
        dsimp only [cchk]; simp only [List.append_assoc, List.cons_append, List.nil_append]
      change lkm.linkSpec (pre ++ [Asm.addi AbiReg.t2 AbiReg.zero 8#12] ++ _) = _
      rw [heq]; exact hlink0)
    (by rw [htw_body] at h64_0; omega) st2 hpc2
  let st3 := stepReg st2 AbiReg.t2 8#64 (st2.pc + 4#64)
  have hpres3 : PreservedFrameRegs fl (· = rd) st2 st3 :=
    PreservedFrameRegs.of_scratch1 AbiReg.t2 (by decide) (fun r hr => getReg_stepReg_ne st2 AbiReg.t2 r hr _ _)
  let p3 := pre ++ [Asm.addi AbiReg.t2 AbiReg.zero 8#12]
  have htw3 : lkm.totalSize p3 = lkm.totalSize pre + 1 := by
    dsimp only [p3]; rw [lkm.totalSize_append, Asm.addi, lkm.totalSize_instr]
  have hpc3 : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize p3) := by
    change st2.pc + 4#64 = _; rw [pc_add_4_ofNat st2.pc hpc2, htw3]
  have ht0_3 : st3.getReg AbiReg.t0 = BitVec.ofNat 64 bytes.size :=
    (getReg_stepReg_ne st2 AbiReg.t2 AbiReg.t0 (by decide) _ _).trans ht0_2
  have ht2_3 : st3.getReg AbiReg.t2 = 8#64 := getReg_stepReg_eq st2 AbiReg.t2 (by decide) _ _
  have hlinkBr1 : lkm.linkSpec (p3 ++ [.br .bltu AbiReg.t0 AbiReg.t2 errLabel] ++
      ([Asm.addi AbiReg.t0 AbiReg.t0 (-8#12), Asm.bltu AbiReg.t0 rI errLabel,
        Asm.add AbiReg.t1 AbiReg.t1 rI] ++ readBytes ++ post)) = .ok (env.code, env.labels) := by
    have heq : p3 ++ [Asm.bltu AbiReg.t0 AbiReg.t2 errLabel] ++
        ([Asm.addi AbiReg.t0 AbiReg.t0 (-8#12), Asm.bltu AbiReg.t0 rI errLabel,
          Asm.add AbiReg.t1 AbiReg.t1 rI] ++ readBytes ++ post) =
        pre ++ cchk ++ readBytes ++ post := by
      dsimp only [p3, cchk]; simp only [List.append_assoc, List.cons_append, List.nil_append]
    change lkm.linkSpec (p3 ++ [Asm.bltu AbiReg.t0 AbiReg.t2 errLabel] ++ _) = _
    rw [heq]; exact hlink0
  have h64Br1 : 4 * (lkm.totalSize p3 + lkm.itemSize (.br .bltu AbiReg.t0 AbiReg.t2 errLabel)) < 2 ^ 64 := by
    rw [htw3]; rw [htw_body] at h64_0
    have : lkm.itemSize (.br .bltu AbiReg.t0 AbiReg.t2 errLabel) = lkm.totalSize br1 := by simp [br1, Asm.bltu, lkm.totalSize_singleton]
    omega
  by_cases hge8 : 8 ≤ bytes.size
  · have hcondF1 : evalBranch .bltu (st3.getReg AbiReg.t0) (st3.getReg AbiReg.t2) = false := by
      simp [evalBranch, ht0_3, ht2_3, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hszlt]
      omega
    obtain ⟨kBr1, st4, hrun4, hpc4', hoth4, _, hmem4⟩ :=
      prog_step_br_fall env p3
        ([Asm.addi AbiReg.t0 AbiReg.t0 (-8#12), Asm.bltu AbiReg.t0 rI errLabel,
          Asm.add AbiReg.t1 AbiReg.t1 rI] ++ readBytes ++ post)
        .bltu AbiReg.t0 AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide)
        hlinkBr1 h64Br1 st3 hpc3 hcondF1
    have hpres4 : PreservedFrameRegs fl (· = rd) st3 st4 :=
      PreservedFrameRegs.of_t6_s1 hoth4
    let p4 := p3 ++ br1
    have htw4 : lkm.totalSize p4 = lkm.totalSize pre + 1 + lkm.totalSize br1 := by
      dsimp only [p4]; rw [lkm.totalSize_append, htw3]
    have hpc4 : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize p4) := by rw [hpc4', htw4, htw3]; rfl
    have hsSub8 := step_item_instr_lm lkm env.hrom p4
      ([Asm.bltu AbiReg.t0 rI errLabel, Asm.add AbiReg.t1 AbiReg.t1 rI] ++ readBytes ++ post)
      (.aluImm .addi AbiReg.t0 AbiReg.t0 (-8#12))
      (by
        have heq : p4 ++ [Asm.addi AbiReg.t0 AbiReg.t0 (-8#12)] ++
            ([Asm.bltu AbiReg.t0 rI errLabel, Asm.add AbiReg.t1 AbiReg.t1 rI] ++ readBytes ++ post) =
            pre ++ cchk ++ readBytes ++ post := by
          dsimp only [p4, p3, br1, cchk]; simp only [List.append_assoc, List.cons_append, List.nil_append]
        change lkm.linkSpec (p4 ++ [Asm.addi AbiReg.t0 AbiReg.t0 (-8#12)] ++ _) = _
        rw [heq]; exact hlink0)
      (by rw [htw4]; rw [htw_body] at h64_0; omega) st4 hpc4
    let st5 := stepReg st4 AbiReg.t0 (st4.getReg AbiReg.t0 + sextImm12 (-8#12)) (st4.pc + 4#64)
    have hpres5 : PreservedFrameRegs fl (· = rd) st4 st5 :=
      PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) (fun r hr => getReg_stepReg_ne st4 AbiReg.t0 r hr _ _)
    let p5 := p4 ++ [Asm.addi AbiReg.t0 AbiReg.t0 (-8#12)]
    have htw5 : lkm.totalSize p5 = lkm.totalSize p4 + 1 := by
      dsimp only [p5]; rw [lkm.totalSize_append, Asm.addi, lkm.totalSize_instr]
    have hpc5 : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize p5) := by
      change st4.pc + 4#64 = _; rw [pc_add_4_ofNat st4.pc hpc4, htw5]
    have ht0_5 : st5.getReg AbiReg.t0 = BitVec.ofNat 64 (bytes.size - 8) := by
      have ht0_4 : st4.getReg AbiReg.t0 = BitVec.ofNat 64 bytes.size := (hoth4 AbiReg.t0 (by decide)).trans ht0_3
      change (stepReg st4 AbiReg.t0 _ _).getReg AbiReg.t0 = _
      rw [getReg_stepReg_eq _ _ (by decide), ht0_4, show sextImm12 (-8#12) = -8#64 from by decide]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          show (-8#64 : BitVec 64).toNat = 2 ^ 64 - 8 from by decide,
          Nat.mod_eq_of_lt hszlt, Nat.mod_eq_of_lt (by omega : bytes.size - 8 < 2 ^ 64),
          show bytes.size + (2 ^ 64 - 8) = 2 ^ 64 + (bytes.size - 8) by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : bytes.size - 8 < 2 ^ 64)]
    have hri5 : st5.getReg rI = vi.toBitVec :=
      (getReg_stepReg_ne st4 AbiReg.t0 rI (idxReg_ne_temp hrI (by decide)) _ _).trans
        ((hoth4 rI ⟨idxReg_ne_temp hrI (by decide), idxReg_ne_s1 hrI⟩).trans
          ((getReg_stepReg_ne st2 AbiReg.t2 rI (idxReg_ne_temp hrI (by decide)) _ _).trans hrI2))
    have hlinkBr2 : lkm.linkSpec (p5 ++ [.br .bltu AbiReg.t0 rI errLabel] ++
        ([Asm.add AbiReg.t1 AbiReg.t1 rI] ++ readBytes ++ post)) = .ok (env.code, env.labels) := by
      have heq : p5 ++ [Asm.bltu AbiReg.t0 rI errLabel] ++
          ([Asm.add AbiReg.t1 AbiReg.t1 rI] ++ readBytes ++ post) =
          pre ++ cchk ++ readBytes ++ post := by
        dsimp only [p5, p4, p3, br1, cchk]; simp only [List.append_assoc, List.cons_append, List.nil_append]
      change lkm.linkSpec (p5 ++ [Asm.bltu AbiReg.t0 rI errLabel] ++ _) = _
      rw [heq]; exact hlink0
    have h64Br2 : 4 * (lkm.totalSize p5 + lkm.itemSize (.br .bltu AbiReg.t0 rI errLabel)) < 2 ^ 64 := by
      rw [htw5, htw4]; rw [htw_body] at h64_0
      have : lkm.itemSize (.br .bltu AbiReg.t0 rI errLabel) = lkm.totalSize br2 := by simp [br2, Asm.bltu, lkm.totalSize_singleton]
      omega
    by_cases hbound : vi.toNat + 8 ≤ bytes.size
    · simp only [hbound, ↓reduceIte]
      have hcondF2 : evalBranch .bltu (st5.getReg AbiReg.t0) (st5.getReg rI) = false := by
        simp [evalBranch, ht0_5, hri5, BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec, Nat.mod_eq_of_lt (by omega : bytes.size - 8 < 2 ^ 64)]
        omega
      obtain ⟨kBr2, st6, hrun6, hpc6', hoth6, _, hmem6⟩ :=
        prog_step_br_fall env p5 ([Asm.add AbiReg.t1 AbiReg.t1 rI] ++ readBytes ++ post)
          .bltu AbiReg.t0 rI errLabel env.errTarget env.herrLbl ⟨by decide, idxReg_ne_temp hrI (by decide)⟩
          hlinkBr2 h64Br2 st5 hpc5 hcondF2
      have hpres6 : PreservedFrameRegs fl (· = rd) st5 st6 :=
        PreservedFrameRegs.of_t6_s1 hoth6
      let p6 := p5 ++ br2
      have htw6 : lkm.totalSize p6 = lkm.totalSize p5 + lkm.totalSize br2 := lkm.totalSize_append p5 br2
      have hpc6 : st6.pc = BitVec.ofNat 64 (4 * lkm.totalSize p6) := by rw [hpc6', htw6]; rfl
      have hsAdd := step_item_instr_lm lkm env.hrom p6 (readBytes ++ post)
        (.alu .add AbiReg.t1 AbiReg.t1 rI)
        (by
          have heq : p6 ++ [Asm.add AbiReg.t1 AbiReg.t1 rI] ++ (readBytes ++ post) =
              pre ++ cchk ++ readBytes ++ post := by
            dsimp only [p6, p5, p4, p3, br1, br2, cchk]; simp only [List.append_assoc, List.cons_append, List.nil_append]
          change lkm.linkSpec (p6 ++ [Asm.add AbiReg.t1 AbiReg.t1 rI] ++ (readBytes ++ post)) = _
          rw [heq]; exact hlink0)
        (by rw [htw6, htw5, htw4]; rw [htw_body] at h64_0; omega) st6 hpc6
      let st7 := stepReg st6 AbiReg.t1 (st6.getReg AbiReg.t1 + st6.getReg rI) (st6.pc + 4#64)
      have hpres7 : PreservedFrameRegs fl (· = rd) st6 st7 :=
        PreservedFrameRegs.of_scratch1 AbiReg.t1 (by decide) (fun r hr => getReg_stepReg_ne st6 AbiReg.t1 r hr _ _)
      let p7 := p6 ++ [Asm.add AbiReg.t1 AbiReg.t1 rI]
      have htw7 : lkm.totalSize p7 = lkm.totalSize p6 + 1 := by
        dsimp only [p7]; rw [lkm.totalSize_append, Asm.add, lkm.totalSize_instr]
      have hpc7 : st7.pc = BitVec.ofNat 64 (4 * lkm.totalSize p7) := by
        change st6.pc + 4#64 = _; rw [pc_add_4_ofNat st6.pc hpc6, htw7]
      have ht1_7 : st7.getReg AbiReg.t1 = st2.getReg AbiReg.t1 + BitVec.ofNat 64 vi.toNat := by
        have ht1_6 : st6.getReg AbiReg.t1 = st2.getReg AbiReg.t1 :=
          (hoth6 AbiReg.t1 (by decide)).trans
            ((getReg_stepReg_ne st4 AbiReg.t0 AbiReg.t1 (by decide) _ _).trans
              ((hoth4 AbiReg.t1 (by decide)).trans (getReg_stepReg_ne st2 AbiReg.t2 AbiReg.t1 (by decide) _ _)))
        have hri6 : st6.getReg rI = vi.toBitVec := (hoth6 rI ⟨idxReg_ne_temp hrI (by decide), idxReg_ne_s1 hrI⟩).trans hri5
        change (stepReg st6 AbiReg.t1 _ _).getReg AbiReg.t1 = _
        rw [getReg_stepReg_eq _ _ (by decide), ht1_6, hri6, u64_toBitVec_eq_ofNat]
      have hm7 : st7.mem = st2.mem := by
        dsimp only [st7, st5, st3]; rw [mem_stepReg, hmem6, mem_stepReg, hmem4, mem_stepReg]
      have hlink8 : lkm.linkSpec (p7 ++ readBytes ++ post) = .ok (env.code, env.labels) := by
        have heq : p7 ++ readBytes ++ post = pre ++ cchk ++ readBytes ++ post := by
          dsimp only [p7, p6, p5, p4, p3, br1, br2, cchk]; simp only [List.append_assoc, List.cons_append, List.nil_append]
        rw [heq]; exact hlink0
      obtain ⟨st8, hrun8, hpc8, hrd8, hmem8, hpres8, ht4_8⟩ :=
        le64_8bytes_sim_r env fl p7 post rd hrd bytes vi.toNat hbound
          hlink8 (by rw [htw7, htw6, htw5, htw4]; rw [htw_body] at h64_0; omega) st7 hpc7
          (fun j hj => by rw [hm7, ht1_7, BitVec.add_assoc, ← BitVec.ofNat_add]; exact hbytes2 (vi.toNat + j) (by omega))
      have hpc8' : st8.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (cchk ++ readBytes))) :=
        hpc8.trans (congrArg (fun n => BitVec.ofNat 64 (4 * n)) (by rw [htw7, htw6, htw5, htw4, htw_body]; omega))
      refine ⟨1 + (kBr1 + (1 + (kBr2 + (1 + 22)))), st8, ?_, hpc8', hrd8,
        hpres3.trans (hpres4.trans (hpres5.trans (hpres6.trans (hpres7.trans hpres8)))),
        hmem8.trans hm7, ?_⟩
      · rw [run_add, run_one_cont _ _ st3 (by rw [hsAddi8]; simp only [execInstr, evalAluImm, getReg_zero, show sextImm12 8#12 = 8#64 from rfl, BitVec.zero_add]; rfl)]; dsimp only
        rw [run_add, hrun4]; dsimp only
        rw [run_add, run_one_cont _ _ st5 (by rw [hsSub8]; rfl)]; dsimp only
        rw [run_add, hrun6]; dsimp only
        rw [run_add, run_one_cont _ _ st7 (by rw [hsAdd]; rfl)]; dsimp only
        exact hrun8
      · exact ht4_8.trans
          ((getReg_stepReg_ne st6 AbiReg.t1 AbiReg.t4 (by decide) _ _).trans
            ((hoth6 AbiReg.t4 (by decide)).trans
              ((getReg_stepReg_ne st4 AbiReg.t0 AbiReg.t4 (by decide) _ _).trans
                ((hoth4 AbiReg.t4 (by decide)).trans
                  (getReg_stepReg_ne st2 AbiReg.t2 AbiReg.t4 (by decide) _ _)))))
    · simp only [hbound, ↓reduceIte]
      have hcondT2 : evalBranch .bltu (st5.getReg AbiReg.t0) (st5.getReg rI) = true := by
        simp [evalBranch, ht0_5, hri5, BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec, Nat.mod_eq_of_lt (by omega : bytes.size - 8 < 2 ^ 64)]
        omega
      obtain ⟨kBr2, st6, hrun6, hpc6', hoth6, _, hmem6⟩ :=
        prog_step_br_taken env p5 ([Asm.add AbiReg.t1 AbiReg.t1 rI] ++ readBytes ++ post)
          .bltu AbiReg.t0 rI errLabel env.errTarget env.herrLbl ⟨by decide, idxReg_ne_temp hrI (by decide)⟩
          hlinkBr2 h64Br2 st5 hpc5 hcondT2
      refine ⟨1 + (kBr1 + (1 + kBr2)), st6, ?_, hpc6',
        hpres3.trans (hpres4.trans (hpres5.trans (PreservedFrameRegs.of_t6_s1 hoth6))),
        by rw [hmem6, mem_stepReg, hmem4, mem_stepReg]⟩
      rw [run_add, run_one_cont _ _ st3 (by rw [hsAddi8]; simp only [execInstr, evalAluImm, getReg_zero, show sextImm12 8#12 = 8#64 from rfl, BitVec.zero_add]; rfl)]; dsimp only
      rw [run_add, hrun4]; dsimp only
      rw [run_add, run_one_cont _ _ st5 (by rw [hsSub8]; rfl)]; dsimp only
      exact hrun6
  · have hnb : ¬(vi.toNat + 8 ≤ bytes.size) := by omega
    simp only [hnb, ↓reduceIte]
    have hcondT1 : evalBranch .bltu (st3.getReg AbiReg.t0) (st3.getReg AbiReg.t2) = true := by
      simp [evalBranch, ht0_3, ht2_3, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hszlt]
      omega
    obtain ⟨kBr1, st4, hrun4, hpc4', hoth4, _, hmem4⟩ :=
      prog_step_br_taken env p3
        ([Asm.addi AbiReg.t0 AbiReg.t0 (-8#12), Asm.bltu AbiReg.t0 rI errLabel,
          Asm.add AbiReg.t1 AbiReg.t1 rI] ++ readBytes ++ post)
        .bltu AbiReg.t0 AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide)
        hlinkBr1 h64Br1 st3 hpc3 hcondT1
    refine ⟨1 + kBr1, st4, ?_, hpc4',
      hpres3.trans (PreservedFrameRegs.of_t6_s1 hoth4),
      by rw [hmem4, mem_stepReg]⟩
    rw [run_add, run_one_cont _ _ st3 (by rw [hsAddi8]; simp only [execInstr, evalAluImm, getReg_zero, show sextImm12 8#12 = 8#64 from rfl, BitVec.zero_add]; rfl)]; dsimp only
    exact hrun4

private theorem reg_evalExpr_ld8x8_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (_hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (src : BSrc) (i : Expr) (ihi : RegEvalExprIH env L fl lm loc sp i)
    (pre post : List AsmItem) (tmp : Nat) (rd : Reg) (hrd : ValidTargetReg fl rd)
    (heOk : exprOkB env.tab fl.nlocals (.ld8x8 src i) = true)
    (hTmp : tmp + usedTempsExpr (.ld8x8 src i) ≤ fl.usedTemps)
    (hlink : lkm.linkSpec (pre ++ compileETo env.tab fl tmp rd (.ld8x8 src i) ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd (.ld8x8 src i))) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    match _root_.L.evalE (.ld8x8 src i) ⟨lm, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd (.ld8x8 src i)))) ∧
        st'.getReg rd = v.toBitVec ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem ∧
        (exprNoT4 (.ld8x8 src i) = true → st'.getReg AbiReg.t4 = st.getReg AbiReg.t4)
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
  simp only [usedTempsExpr] at hTmp
  have hsrcOk : bsrcOkB env.tab src = true := by
    cases src <;> simp only [exprOkB, Bool.and_eq_true] at heOk <;> exact heOk.1
  have hiOk : exprOkB env.tab fl.nlocals i = true := by
    cases src <;> simp only [exprOkB, Bool.and_eq_true] at heOk <;> exact heOk.2
  let pI := match exprReg? fl.alloc i with | some r => ([], r) | none => (compileETo env.tab fl tmp AbiReg.a0 i, AbiReg.a0)
  let setupSrc := ld8x8SetupSrcR env.tab fl.useT5Gp src
  let readBytes := [Asm.lbu rd AbiReg.t1 7#12] ++
    ([6, 5, 4, 3, 2, 1, 0].flatMap fun k =>
      [Asm.lbu AbiReg.t2 AbiReg.t1 (BitVec.ofInt 12 (k : Int)), Asm.slli rd rd 8#6, Asm.or rd rd AbiReg.t2])
  let cchk := [Asm.addi AbiReg.t2 AbiReg.zero 8#12, Asm.bltu AbiReg.t0 AbiReg.t2 errLabel,
    Asm.addi AbiReg.t0 AbiReg.t0 (-8#12), Asm.bltu AbiReg.t0 pI.2 errLabel, Asm.add AbiReg.t1 AbiReg.t1 pI.2]
  have hdef : compileETo env.tab fl tmp rd (.ld8x8 src i) = pI.1 ++ setupSrc ++ (cchk ++ readBytes) := by
    cases h : exprReg? fl.alloc i <;> cases src <;> simp [compileETo, pI, h, setupSrc, ld8x8SetupSrcR, cchk, readBytes, List.append_assoc]
  rw [hdef] at hlink h64 ⊢
  have htw_all : lkm.totalSize (pI.1 ++ setupSrc ++ (cchk ++ readBytes)) =
      lkm.totalSize pI.1 + lkm.totalSize setupSrc + lkm.totalSize (cchk ++ readBytes) := by
    simp only [lkm.totalSize_append]
  have riRes := reg_evalIdx_of_ih env L fl hfl lm loc i pre (setupSrc ++ (cchk ++ readBytes) ++ post) tmp hiOk hTmp
    (fun p q tm r st' hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => ihi p q tm r hr hiOk ht hl h6 st' hpc' hgp' ht5' hsp' hm' hf')
    (by simpa only [pI, List.append_assoc] using hlink)
    (by rw [htw_all] at h64; dsimp only [pI] at h64 ⊢; omega) st hpc hgp ht5 hsp hmemRel hframeOk
  rcases riRes with ⟨hri, riSim⟩
  rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
  · simp only [hvi] at riSim
    obtain ⟨k1, st1, hrun1, hpc1, hri1, hpres1, heq1, ht4_1⟩ := riSim
    have htw1 : lkm.totalSize (pre ++ pI.1) = lkm.totalSize pre + lkm.totalSize pI.1 := lkm.totalSize_append _ _
    have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.abi.gp.trans hgp
    have ht5_1 : T5GpOk L fl st1 := ht5.of_preserved hpres1
    have hmemRel1 := ProgMemRel.of_tempSpanR hlo hhi (by omega) heq1 hmemRel
    obtain ⟨ks, st2, hrun2, hpc2, ht0_2, hszlt, hri2, hbytes2, hpres2, hmem2, ht4_2⟩ :=
      reg_ld8x8_setup_sim env L fl lm src pI.2 hri vi rd (pre ++ pI.1) ((cchk ++ readBytes) ++ post) hsrcOk
        (by simpa only [setupSrc, List.append_assoc] using hlink)
        (by rw [htw1]; rw [htw_all] at h64; dsimp only [setupSrc] at h64; omega)
        st1 (by rw [htw1]; exact hpc1) hgp1 ht5_1 hri1 hmemRel1
    let p2 := pre ++ pI.1 ++ setupSrc
    have htw2 : lkm.totalSize p2 = lkm.totalSize pre + lkm.totalSize pI.1 + lkm.totalSize setupSrc := by
      dsimp only [p2]; rw [lkm.totalSize_append, htw1]
    have hbody := reg_ld8x8_body_sim env fl p2 post pI.2 hri vi rd hrd (lm.src8 src) hszlt
      (by simpa only [p2, cchk, readBytes, List.append_assoc] using hlink)
      (by rw [htw2]; rw [htw_all] at h64; dsimp only [cchk, readBytes] at h64; omega)
      st2 (by rw [htw2, ← htw1]; exact hpc2) ht0_2 hri2 hbytes2
    have hevEval : _root_.L.evalE (.ld8x8 src i) ⟨lm, loc⟩ =
        if vi.toNat + 8 ≤ (lm.src8 src).size then .ok (le64 (lm.src8 src) vi.toNat, ⟨lm, loc⟩) else .error .oob := by
      change (_root_.L.evalE i >>= _root_.L.ld8x8 src) ⟨lm, loc⟩ = _
      dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hvi]
      dsimp only [_root_.L.ld8x8, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Pure.pure, Except.pure, Except.bind]
      by_cases hb : vi.toNat + 8 ≤ (lm.src8 src).size
      · simp only [hb, ↓reduceIte]; rfl
      · simp only [hb, ↓reduceIte]; rfl
    rw [hevEval]
    by_cases hbound : vi.toNat + 8 ≤ (lm.src8 src).size
    · simp only [hbound, ↓reduceIte] at hbody ⊢
      obtain ⟨kb, st3, hrun3, hpc3, hrd3, hpres3, hmem3, ht4_3⟩ := hbody
      refine ⟨k1 + (ks + kb), st3,
        by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
        hpc3.trans (congrArg (fun n => BitVec.ofNat 64 (4 * n)) (by rw [htw2, htw_all]; dsimp only [cchk, readBytes]; omega)),
        hrd3, (PreservedFrameRegs.of_a0 hpres1).trans (hpres2.trans hpres3),
        by rw [hmem3, hmem2]; exact heq1,
        fun hnt => ht4_3.trans (ht4_2.trans (ht4_1 hnt))⟩
    · simp only [hbound, ↓reduceIte] at hbody ⊢
      obtain ⟨kb, st3, hrun3, hpc3, hpres3, hmem3⟩ := hbody
      refine ⟨k1 + (ks + kb), st3,
        by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
        hpc3, (PreservedFrameRegs.of_a0 hpres1).trans (hpres2.trans hpres3),
        by rw [hmem3, hmem2]; exact heq1⟩
  · simp only [hvi] at riSim
    obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := riSim
    have hev : _root_.L.evalE (.ld8x8 src i) ⟨lm, loc⟩ = .error .oob := by
      dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hvi]
    rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩

private theorem reg_evalExpr_ld32t_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (a : ArrId) (t i : Expr) (iht : RegEvalExprIH env L fl lm loc sp t) (ihi : RegEvalExprIH env L fl lm loc sp i)
    (pre post : List AsmItem) (tmp : Nat) (rd : Reg) (hrd : ValidTargetReg fl rd)
    (heOk : exprOkB env.tab fl.nlocals (.ld32t a t i) = true)
    (hVfT : ExprVarsInFrame fl t)
    (hTmp : tmp + usedTempsExpr (.ld32t a t i) ≤ fl.usedTemps)
    (hlink : lkm.linkSpec (pre ++ compileETo env.tab fl tmp rd (.ld32t a t i) ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd (.ld32t a t i))) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    match _root_.L.evalE (.ld32t a t i) ⟨lm, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd (.ld32t a t i)))) ∧
        st'.getReg rd = v.toBitVec ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem ∧
        (exprNoT4 (.ld32t a t i) = true → st'.getReg AbiReg.t4 = st.getReg AbiReg.t4)
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
  simp only [exprOkB, Bool.and_eq_true] at heOk
  simp only [usedTempsExpr] at hTmp
  cases htC : t.constVal? with
  | some w =>
    have hteq : t = .const w := expr_constVal_eq_some htC
    have hvt : _root_.L.evalE t ⟨lm, loc⟩ = .ok (w, ⟨lm, loc⟩) := by rw [hteq]; rfl
    have hst : isSimpleExpr t = true := isSimpleExpr_of_constVal htC
    simp only [hst, ↓reduceIte] at hTmp
    let s := tierA a w
    let pI := match exprReg? fl.alloc i with | some r => ([], r) | none => (compileETo env.tab fl tmp AbiReg.a0 i, AbiReg.a0)
    let cbody :=
      loadMemOff .ld AbiReg.t2 (gpBaseReg fl.useT5Gp (env.tab.len64 s)) AbiReg.t3 (gpAdjOff fl.useT5Gp (env.tab.len64 s)) ++
      [Asm.srli AbiReg.t3 pI.2 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 (gpBaseReg fl.useT5Gp (env.tab.base64 s)) AbiReg.t3 (gpAdjOff fl.useT5Gp (env.tab.base64 s)) ++
      ld32tTail rd pI.2 i
    have hdef : compileETo env.tab fl tmp rd (.ld32t a t i) = pI.1 ++ cbody := by
      cases h : exprReg? fl.alloc i <;>
        simp [compileETo, htC, s, pI, h, cbody, loadMemOffGp_eq_loadMemOff, List.append_assoc]
    rw [hdef] at hlink h64 ⊢
    have htw_all : lkm.totalSize (pI.1 ++ cbody) = lkm.totalSize pI.1 + lkm.totalSize cbody := lkm.totalSize_append _ _
    have riRes := reg_evalIdx_of_ih env L fl hfl lm loc i pre (cbody ++ post) tmp heOk.2 hTmp
      (fun p q tm r st' hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => ihi p q tm r hr heOk.2 ht hl h6 st' hpc' hgp' ht5' hsp' hm' hf')
      (by simpa only [pI, List.append_assoc] using hlink)
      (by rw [htw_all] at h64; dsimp only [pI] at h64 ⊢; omega) st hpc hgp ht5 hsp hmemRel hframeOk
    rcases riRes with ⟨hri, riSim⟩
    rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
    · simp only [hvi] at riSim
      obtain ⟨k1, st1, hrun1, hpc1, hri1, hpres1, heq1, ht4_1⟩ := riSim
      have htw1 : lkm.totalSize (pre ++ pI.1) = lkm.totalSize pre + lkm.totalSize pI.1 := lkm.totalSize_append _ _
      have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.abi.gp.trans hgp
      have ht5_1 : T5GpOk L fl st1 := ht5.of_preserved hpres1
      have hmemRel1 := ProgMemRel.of_tempSpanR hlo hhi (by omega) heq1 hmemRel
      have hta := tierAddrOk_len64_addr_T L.T a w (tier32Ok_to_tierAddrOk heOk.1.1 hvt)
      have rb := reg_ld32tTail_body_r env L fl lm loc s hta.1 i vi hvi (pre ++ pI.1) post rd pI.2
        (gpBaseReg fl.useT5Gp (env.tab.len64 s)) (gpBaseReg fl.useT5Gp (env.tab.base64 s))
        hrd hri (gpBaseReg_ne_temp _ _ (by decide)) (gpBaseReg_ne_temp _ _ (by decide))
        (gpBaseReg_ne_temp _ _ (by decide)) (gpBaseReg_ne_t6_s1 _ _)
        (gpAdjOff fl.useT5Gp (env.tab.len64 s)) (gpAdjOff fl.useT5Gp (env.tab.base64 s))
        st1 (by rw [htw1]; exact hpc1) (gpBaseReg_addr hgp1 ht5_1) (gpBaseReg_addr hgp1 ht5_1)
        hri1 hmemRel1 (by simpa only [cbody, List.append_assoc] using hlink)
        (by rw [htw1]; rw [htw_all] at h64; dsimp only [cbody] at h64; omega)
      by_cases hbound : (vi / 2).toNat < (lm.arr64 s).size
      · simp only [hbound, ↓reduceDIte] at rb
        obtain ⟨k2, st2, hrun2, hpc2, hrd2, hpres2, hmem2, ht4_2⟩ := rb
        have hev : _root_.L.evalE (.ld32t a t i) ⟨lm, loc⟩ = .ok (half32 ((lm.arr64 s)[(vi / 2).toNat]'hbound) vi, ⟨lm, loc⟩) := by
          change (_root_.L.evalE t >>= fun u => _root_.L.evalE i >>= _root_.L.ld32 (tierA a u)) ⟨lm, loc⟩ = _
          simp only [Bind.bind, StateT.bind, Except.bind, hvt, hvi, _root_.L.ld32, get, getThe, MonadStateOf.get, StateT.get]
          have hb' : vi.toNat / 2 < (lm.arr64 s).size := hbound
          simp [s, hb', Pure.pure, StateT.pure, Except.pure]
        rw [hev]
        exact ⟨k1 + k2, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
          by dsimp only [cbody] at htw_all; rw [hpc2, htw1, htw_all]; congr 2; omega, hrd2,
          (PreservedFrameRegs.of_a0 hpres1).trans hpres2, by rw [hmem2]; exact heq1,
          fun hnt => ht4_2.trans (ht4_1 (by simp only [exprNoT4, hst, Bool.true_and] at hnt; exact hnt))⟩
      · simp only [hbound, ↓reduceDIte] at rb
        obtain ⟨k2, st2, hrun2, hpc2, hpres2, hmem2⟩ := rb
        have hev : _root_.L.evalE (.ld32t a t i) ⟨lm, loc⟩ = .error .oob := by
          change (_root_.L.evalE t >>= fun u => _root_.L.evalE i >>= _root_.L.ld32 (tierA a u)) ⟨lm, loc⟩ = _
          simp only [Bind.bind, StateT.bind, Except.bind, hvt, hvi, _root_.L.ld32, get, getThe, MonadStateOf.get, StateT.get]
          have hb' : ¬(vi.toNat / 2 < (lm.arr64 s).size) := hbound
          simp [s, hb', Pure.pure, Except.pure, Function.comp_apply, throw, throwThe, MonadExceptOf.throw, StateT.lift]; rfl
        rw [hev]
        exact ⟨k1 + k2, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
          hpc2, (PreservedFrameRegs.of_a0 hpres1).trans hpres2, by rw [hmem2]; exact heq1⟩
    · simp only [hvi] at riSim
      obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := riSim
      have hev : _root_.L.evalE (.ld32t a t i) ⟨lm, loc⟩ = .error .oob := by
        dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hvt]; dsimp only; rw [hvi]; try rfl
      rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
  | none =>
    let pH := match exprReg? fl.alloc t with
      | some r => match exprReg? fl.alloc i with
        | some ri => ([], r, ri) | none => (compileETo env.tab fl tmp AbiReg.a0 i, r, AbiReg.a0)
      | none => match emitSimpleExprR env.tab fl AbiReg.t0 AbiReg.t1 t with
        | some ct => match exprReg? fl.alloc i with
          | some ri => (ct, AbiReg.t0, ri) | none => (compileETo env.tab fl tmp AbiReg.a0 i ++ ct, AbiReg.t0, AbiReg.a0)
        | none =>
          (compileETo env.tab fl tmp AbiReg.a0 t ++
           storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp) ++
           compileETo env.tab fl (tmp + 1) AbiReg.a0 i ++
           loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff tmp), AbiReg.t0, AbiReg.a0)
    let chdr := [Asm.andi AbiReg.t0 pH.2.1 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0]
    let cbody :=
      loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (env.tab.len64 (TieredArray.t0 a)) ++
      [Asm.srli AbiReg.t3 pH.2.2 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t3 (env.tab.base64 (TieredArray.t0 a)) ++
      ld32tTail rd pH.2.2 i
    have hdef : compileETo env.tab fl tmp rd (.ld32t a t i) = pH.1 ++ chdr ++ cbody := by
      cases ht' : exprReg? fl.alloc t with
      | some r => cases hi' : exprReg? fl.alloc i <;> simp [compileETo, htC, pH, chdr, cbody, ht', hi', List.append_assoc]
      | none =>
        cases hs' : emitSimpleExprR env.tab fl AbiReg.t0 AbiReg.t1 t with
        | some ct => cases hi' : exprReg? fl.alloc i <;> simp [compileETo, htC, pH, chdr, cbody, ht', hs', hi', List.append_assoc]
        | none => simp [compileETo, htC, pH, chdr, cbody, ht', hs', List.append_assoc]
    rw [hdef] at hlink h64 ⊢
    have htw_hdr : lkm.totalSize chdr = 3 := by
      simp [chdr, Asm.andi, Asm.slli, Asm.add, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
    have htw_all : lkm.totalSize (pH.1 ++ chdr ++ cbody) = lkm.totalSize pH.1 + 3 + lkm.totalSize cbody := by
      simp only [lkm.totalSize_append, htw_hdr]
    have rHead := reg_evalTierHead_of_ih env L fl hfl lm loc hspAlign hlo hhi t i pre (chdr ++ cbody ++ post) tmp
      heOk.1.2 heOk.2 hVfT hTmp
      (fun p q tm r st' hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => by
        have r := iht p q tm r hr heOk.1.2 ht hl h6 st' hpc' hgp' ht5' hsp' hm' hf'
        cases hv : _root_.L.evalE t ⟨lm, loc⟩ with
        | ok _ => simp only [hv] at r; rcases r with ⟨k, st2, h1, h2, h3, h4, h5, _⟩; exact ⟨k, st2, h1, h2, h3, h4, h5⟩
        | error _ => simp only [hv] at r; exact r)
      (fun p q tm r st' hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => ihi p q tm r hr heOk.2 ht hl h6 st' hpc' hgp' ht5' hsp' hm' hf')
      (by simpa only [pH, List.append_assoc] using hlink)
      (by rw [htw_all] at h64; dsimp only [pH] at h64 ⊢; omega) st hpc hgp ht5 hsp hmemRel hframeOk
    rcases rHead with ⟨hri, headSim⟩
    rcases _root_.L.evalE_pure t ⟨lm, loc⟩ with ⟨vt, hvt⟩ | hvt
    · rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
      · simp only [hvt, hvi] at headSim
        obtain ⟨k1, st1, hrun1, hpc1, hrt1, hri1, hpres1, heq1, ht4_1⟩ := headSim
        have htw1 : lkm.totalSize (pre ++ pH.1) = lkm.totalSize pre + lkm.totalSize pH.1 := lkm.totalSize_append _ _
        have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.abi.gp.trans hgp
        have hmemRel1 := ProgMemRel.of_tempSpanR hlo hhi (by omega) heq1 hmemRel
        obtain ⟨st2, hrun2, hpc2, ht1_2, hmem2, hpres2, hoth2⟩ :=
          step_tierHdr_r env fl (pre ++ pH.1) (cbody ++ post) pH.2.1 vt
            (by simpa only [chdr, List.append_assoc] using hlink)
            (by rw [htw1]; rw [htw_all] at h64; omega) st1 (by rw [htw1]; exact hpc1) hgp1 hrt1
        have htw2 : lkm.totalSize (pre ++ pH.1 ++ chdr) = lkm.totalSize pre + lkm.totalSize pH.1 + 3 := by
          rw [lkm.totalSize_append, htw1, htw_hdr]
        have hta := tierAddrOk_len64_addr_T L.T a vt (tier32Ok_to_tierAddrOk heOk.1.1 hvt)
        have hri2 : st2.getReg pH.2.2 = vi.toBitVec :=
          (hoth2 pH.2.2 (idxReg_ne_temp hri (by decide)) (idxReg_ne_temp hri (by decide))).trans hri1
        have rb := reg_ld32tTail_body_r env L fl lm loc (tierA a vt) hta.1 i vi hvi (pre ++ pH.1 ++ chdr) post rd pH.2.2
          AbiReg.t1 AbiReg.t1 hrd hri (by decide) (by decide) (by decide) (by decide)
          (env.tab.len64 (TieredArray.t0 a)) (env.tab.base64 (TieredArray.t0 a))
          st2 (by rw [htw2, ← htw1]; exact hpc2) (by rw [ht1_2]; exact hta.2.1) (by rw [ht1_2]; exact hta.2.2)
          hri2 (by rw [hmem2]; exact hmemRel1)
          (by simpa only [cbody, List.append_assoc] using hlink)
          (by rw [htw2]; rw [htw_all] at h64; dsimp only [cbody] at h64; omega)
        by_cases hbound : (vi / 2).toNat < (lm.arr64 (tierA a vt)).size
        · simp only [hbound, ↓reduceDIte] at rb
          obtain ⟨k3, st3, hrun3, hpc3, hrd3, hpres3, hmem3, ht4_3⟩ := rb
          have hev : _root_.L.evalE (.ld32t a t i) ⟨lm, loc⟩ = .ok (half32 ((lm.arr64 (tierA a vt))[(vi / 2).toNat]'hbound) vi, ⟨lm, loc⟩) := by
            change (_root_.L.evalE t >>= fun u => _root_.L.evalE i >>= _root_.L.ld32 (tierA a u)) ⟨lm, loc⟩ = _
            simp only [Bind.bind, StateT.bind, Except.bind, hvt, hvi, _root_.L.ld32, get, getThe, MonadStateOf.get, StateT.get]
            have hb' : vi.toNat / 2 < (lm.arr64 (tierA a vt)).size := hbound
            simp [hb', Pure.pure, StateT.pure, Except.pure]
          rw [hev]
          exact ⟨k1 + (3 + k3), st3,
            by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
            by dsimp only [cbody] at htw_all; rw [hpc3, htw2, htw_all]; congr 2; omega, hrd3,
            (PreservedFrameRegs.of_a0 (hpres1.trans hpres2)).trans hpres3, by rw [hmem3, hmem2]; exact heq1,
            fun hnt => by
              simp only [exprNoT4, Bool.and_eq_true] at hnt
              exact ht4_3.trans ((hoth2 AbiReg.t4 (by decide) (by decide)).trans (ht4_1 hnt.1 hnt.2))⟩
        · simp only [hbound, ↓reduceDIte] at rb
          obtain ⟨k3, st3, hrun3, hpc3, hpres3, hmem3⟩ := rb
          have hev : _root_.L.evalE (.ld32t a t i) ⟨lm, loc⟩ = .error .oob := by
            change (_root_.L.evalE t >>= fun u => _root_.L.evalE i >>= _root_.L.ld32 (tierA a u)) ⟨lm, loc⟩ = _
            simp only [Bind.bind, StateT.bind, Except.bind, hvt, hvi, _root_.L.ld32, get, getThe, MonadStateOf.get, StateT.get]
            have hb' : ¬(vi.toNat / 2 < (lm.arr64 (tierA a vt)).size) := hbound
            simp [hb', Pure.pure, Except.pure, Function.comp_apply, throw, throwThe, MonadExceptOf.throw, StateT.lift]; rfl
          rw [hev]
          exact ⟨k1 + (3 + k3), st3,
            by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
            hpc3, (PreservedFrameRegs.of_a0 (hpres1.trans hpres2)).trans hpres3, by rw [hmem3, hmem2]; exact heq1⟩
      · simp only [hvt, hvi] at headSim
        obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := headSim
        have hev : _root_.L.evalE (.ld32t a t i) ⟨lm, loc⟩ = .error .oob := by
          dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hvt]; dsimp only; rw [hvi]; try rfl
        rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
    · simp only [hvt] at headSim
      obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := headSim
      have hev : _root_.L.evalE (.ld32t a t i) ⟨lm, loc⟩ = .error .oob := by
        dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hvt]
      rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩

/-- Simulation for `emitLd32hFrom` (used for `.ld32h` and fused `.ld64t & 0xffffffff` / `>> 32`). -/
private theorem reg_emitLd32hFrom_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (a : ArrId) (t i : Expr) (hiFlag : Bool) (iht : RegEvalExprIH env L fl lm loc sp t) (ihi : RegEvalExprIH env L fl lm loc sp i)
    (pre post : List AsmItem) (tmp : Nat) (rd : Reg) (hrd : ValidTargetReg fl rd)
    (heOk : exprOkB env.tab fl.nlocals (.ld32h a t i hiFlag) = true)
    (hVfT : ExprVarsInFrame fl t)
    (hTmp : tmp + usedTempsExpr (.ld32h a t i hiFlag) ≤ fl.usedTemps)
    (hlink : lkm.linkSpec (pre ++ emitLd32hFrom env.tab fl tmp rd a t i hiFlag
        (fun () => compileETo env.tab fl tmp AbiReg.a0 i)
        (fun () => compileETo env.tab fl tmp AbiReg.a0 t)
        (fun () => compileETo env.tab fl (tmp + 1) AbiReg.a0 i) ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (emitLd32hFrom env.tab fl tmp rd a t i hiFlag
        (fun () => compileETo env.tab fl tmp AbiReg.a0 i)
        (fun () => compileETo env.tab fl tmp AbiReg.a0 t)
        (fun () => compileETo env.tab fl (tmp + 1) AbiReg.a0 i))) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    let code := emitLd32hFrom env.tab fl tmp rd a t i hiFlag
      (fun () => compileETo env.tab fl tmp AbiReg.a0 i)
      (fun () => compileETo env.tab fl tmp AbiReg.a0 t)
      (fun () => compileETo env.tab fl (tmp + 1) AbiReg.a0 i)
    match _root_.L.evalE (.ld32h a t i hiFlag) ⟨lm, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize code)) ∧
        st'.getReg rd = v.toBitVec ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem ∧
        (exprNoT4 (.ld32h a t i hiFlag) = true → st'.getReg AbiReg.t4 = st.getReg AbiReg.t4)
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
  intro code
  simp only [exprOkB, Bool.and_eq_true] at heOk
  simp only [usedTempsExpr] at hTmp
  cases htC : t.constVal? with
  | some w =>
    have hteq : t = .const w := expr_constVal_eq_some htC
    have hvt : _root_.L.evalE t ⟨lm, loc⟩ = .ok (w, ⟨lm, loc⟩) := by rw [hteq]; rfl
    have hst : isSimpleExpr t = true := isSimpleExpr_of_constVal htC
    simp only [hst, ↓reduceIte] at hTmp
    let s := tierA a w
    let pI := match exprReg? fl.alloc i with | some r => ([], r) | none => (compileETo env.tab fl tmp AbiReg.a0 i, AbiReg.a0)
    let cbody :=
      loadMemOff .ld AbiReg.t2 (gpBaseReg fl.useT5Gp (env.tab.len64 s)) AbiReg.t3 (gpAdjOff fl.useT5Gp (env.tab.len64 s)) ++
      [Asm.bgeu pI.2 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 (gpBaseReg fl.useT5Gp (env.tab.base64 s)) AbiReg.t3 (gpAdjOff fl.useT5Gp (env.tab.base64 s)) ++
      ld32hTail rd pI.2 AbiReg.t3 i hiFlag
    have hdef : code = pI.1 ++ cbody := by
      cases h : exprReg? fl.alloc i <;>
        simp [code, emitLd32hFrom, htC, s, pI, h, cbody, loadMemOffGp_eq_loadMemOff, List.append_assoc]
    change lkm.linkSpec (pre ++ code ++ post) = _ at hlink
    change 4 * (lkm.totalSize pre + lkm.totalSize code) < 2 ^ 64 at h64
    rw [hdef] at hlink h64 ⊢
    have htw_all : lkm.totalSize (pI.1 ++ cbody) = lkm.totalSize pI.1 + lkm.totalSize cbody := lkm.totalSize_append _ _
    have riRes := reg_evalIdx_of_ih env L fl hfl lm loc i pre (cbody ++ post) tmp heOk.2 hTmp
      (fun p q tm r st' hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => ihi p q tm r hr heOk.2 ht hl h6 st' hpc' hgp' ht5' hsp' hm' hf')
      (by simpa only [pI, List.append_assoc] using hlink)
      (by rw [htw_all] at h64; dsimp only [pI] at h64 ⊢; omega) st hpc hgp ht5 hsp hmemRel hframeOk
    rcases riRes with ⟨hri, riSim⟩
    rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
    · simp only [hvi] at riSim
      obtain ⟨k1, st1, hrun1, hpc1, hri1, hpres1, heq1, ht4_1⟩ := riSim
      have htw1 : lkm.totalSize (pre ++ pI.1) = lkm.totalSize pre + lkm.totalSize pI.1 := lkm.totalSize_append _ _
      have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.abi.gp.trans hgp
      have ht5_1 : T5GpOk L fl st1 := ht5.of_preserved hpres1
      have hmemRel1 := ProgMemRel.of_tempSpanR hlo hhi (by omega) heq1 hmemRel
      have hsOk : env.tab.wordPosOkB s = true := (tieredOk_len64_addr_T L.T a w heOk.1.1).1
      have rb := reg_ld32hTail_body_r env L fl lm loc s hsOk hiFlag i vi hvi (pre ++ pI.1) post rd pI.2
        (gpBaseReg fl.useT5Gp (env.tab.len64 s)) (gpBaseReg fl.useT5Gp (env.tab.base64 s))
        AbiReg.t2 AbiReg.t3 AbiReg.t3 hrd hri (by decide) (by decide) (by decide) (by decide)
        (gpBaseReg_ne_temp _ _ (by decide)) (gpBaseReg_ne_temp _ _ (by decide))
        (gpBaseReg_ne_temp _ _ (by decide)) (gpBaseReg_ne_temp _ _ (by decide)) (gpBaseReg_ne_t6_s1 _ _)
        (gpAdjOff fl.useT5Gp (env.tab.len64 s)) (gpAdjOff fl.useT5Gp (env.tab.base64 s))
        st1 (by rw [htw1]; exact hpc1) (gpBaseReg_addr hgp1 ht5_1) (gpBaseReg_addr hgp1 ht5_1)
        hri1 hmemRel1 (by simpa only [cbody, List.append_assoc] using hlink)
        (by rw [htw1]; rw [htw_all] at h64; dsimp only [cbody] at h64; omega)
      by_cases hbound : vi.toNat < (lm.arr64 s).size
      · simp only [hbound, ↓reduceDIte] at rb
        obtain ⟨k2, st2, hrun2, hpc2, hrd2, hpres2, hmem2, ht4_2⟩ := rb
        have hev : _root_.L.evalE (.ld32h a t i hiFlag) ⟨lm, loc⟩ =
            .ok (half32b hiFlag ((lm.arr64 s)[vi.toNat]'hbound), ⟨lm, loc⟩) := by
          change (_root_.L.evalE t >>= fun u => _root_.L.evalE i >>= fun idx => do
            let w' ← _root_.L.ld64 (tierA a u) idx; return half32b hiFlag w') ⟨lm, loc⟩ = _
          simp only [Bind.bind, StateT.bind, Except.bind, hvt, hvi, _root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get]
          simp [s, hbound, Pure.pure, StateT.pure, Except.pure]
        rw [hev]
        exact ⟨k1 + k2, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
          by dsimp only [cbody] at htw_all; rw [hpc2, htw1, htw_all]; congr 2; omega, hrd2,
          (PreservedFrameRegs.of_a0 hpres1).trans hpres2, by rw [hmem2]; exact heq1,
          fun hnt => ht4_2.trans (ht4_1 (by simp only [exprNoT4, hst, Bool.true_and] at hnt; exact hnt))⟩
      · simp only [hbound, ↓reduceDIte] at rb
        obtain ⟨k2, st2, hrun2, hpc2, hpres2, hmem2⟩ := rb
        have hev : _root_.L.evalE (.ld32h a t i hiFlag) ⟨lm, loc⟩ = .error .oob := by
          change (_root_.L.evalE t >>= fun u => _root_.L.evalE i >>= fun idx => do
            let w' ← _root_.L.ld64 (tierA a u) idx; return half32b hiFlag w') ⟨lm, loc⟩ = _
          simp only [Bind.bind, StateT.bind, Except.bind, hvt, hvi, _root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get]
          simp [s, hbound, Pure.pure, Except.pure, Function.comp_apply, throw, throwThe, MonadExceptOf.throw, StateT.lift]; rfl
        rw [hev]
        exact ⟨k1 + k2, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
          hpc2, (PreservedFrameRegs.of_a0 hpres1).trans hpres2, by rw [hmem2]; exact heq1⟩
    · simp only [hvi] at riSim
      obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := riSim
      have hev : _root_.L.evalE (.ld32h a t i hiFlag) ⟨lm, loc⟩ = .error .oob := by
        dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hvt]; dsimp only; rw [hvi]; try rfl
      rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
  | none =>
    let pH := match exprReg? fl.alloc t with
      | some r => match exprReg? fl.alloc i with
        | some ri => ([], r, ri) | none => (compileETo env.tab fl tmp AbiReg.a0 i, r, AbiReg.a0)
      | none => match emitSimpleExprR env.tab fl AbiReg.t0 AbiReg.t1 t with
        | some ct => match exprReg? fl.alloc i with
          | some ri => (ct, AbiReg.t0, ri) | none => (compileETo env.tab fl tmp AbiReg.a0 i ++ ct, AbiReg.t0, AbiReg.a0)
        | none =>
          (compileETo env.tab fl tmp AbiReg.a0 t ++
           storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp) ++
           compileETo env.tab fl (tmp + 1) AbiReg.a0 i ++
           loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff tmp), AbiReg.t0, AbiReg.a0)
    let chdr := [Asm.andi AbiReg.t0 pH.2.1 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0]
    let cbody :=
      loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (env.tab.len64 (TieredArray.t0 a)) ++
      [Asm.bgeu pH.2.2 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t3 (env.tab.base64 (TieredArray.t0 a)) ++
      ld32hTail rd pH.2.2 AbiReg.t3 i hiFlag
    have hdef : code = pH.1 ++ chdr ++ cbody := by
      cases ht' : exprReg? fl.alloc t with
      | some r => cases hi' : exprReg? fl.alloc i <;> simp [code, emitLd32hFrom, htC, pH, chdr, cbody, ht', hi', List.append_assoc]
      | none =>
        cases hs' : emitSimpleExprR env.tab fl AbiReg.t0 AbiReg.t1 t with
        | some ct => cases hi' : exprReg? fl.alloc i <;> simp [code, emitLd32hFrom, htC, pH, chdr, cbody, ht', hs', hi', List.append_assoc]
        | none => simp [code, emitLd32hFrom, htC, pH, chdr, cbody, ht', hs', List.append_assoc]
    change lkm.linkSpec (pre ++ code ++ post) = _ at hlink
    change 4 * (lkm.totalSize pre + lkm.totalSize code) < 2 ^ 64 at h64
    rw [hdef] at hlink h64 ⊢
    have htw_hdr : lkm.totalSize chdr = 3 := by
      simp [chdr, Asm.andi, Asm.slli, Asm.add, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
    have htw_all : lkm.totalSize (pH.1 ++ chdr ++ cbody) = lkm.totalSize pH.1 + 3 + lkm.totalSize cbody := by
      simp only [lkm.totalSize_append, htw_hdr]
    have rHead := reg_evalTierHead_of_ih env L fl hfl lm loc hspAlign hlo hhi t i pre (chdr ++ cbody ++ post) tmp
      heOk.1.2 heOk.2 hVfT hTmp
      (fun p q tm r st' hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => by
        have r := iht p q tm r hr heOk.1.2 ht hl h6 st' hpc' hgp' ht5' hsp' hm' hf'
        cases hv : _root_.L.evalE t ⟨lm, loc⟩ with
        | ok _ => simp only [hv] at r; rcases r with ⟨k, st2, h1, h2, h3, h4, h5, _⟩; exact ⟨k, st2, h1, h2, h3, h4, h5⟩
        | error _ => simp only [hv] at r; exact r)
      (fun p q tm r st' hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => ihi p q tm r hr heOk.2 ht hl h6 st' hpc' hgp' ht5' hsp' hm' hf')
      (by simpa only [pH, List.append_assoc] using hlink)
      (by rw [htw_all] at h64; dsimp only [pH] at h64 ⊢; omega) st hpc hgp ht5 hsp hmemRel hframeOk
    rcases rHead with ⟨hri, headSim⟩
    rcases _root_.L.evalE_pure t ⟨lm, loc⟩ with ⟨vt, hvt⟩ | hvt
    · rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
      · simp only [hvt, hvi] at headSim
        obtain ⟨k1, st1, hrun1, hpc1, hrt1, hri1, hpres1, heq1, ht4_1⟩ := headSim
        have htw1 : lkm.totalSize (pre ++ pH.1) = lkm.totalSize pre + lkm.totalSize pH.1 := lkm.totalSize_append _ _
        have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.abi.gp.trans hgp
        have hmemRel1 := ProgMemRel.of_tempSpanR hlo hhi (by omega) heq1 hmemRel
        obtain ⟨st2, hrun2, hpc2, ht1_2, hmem2, hpres2, hoth2⟩ :=
          step_tierHdr_r env fl (pre ++ pH.1) (cbody ++ post) pH.2.1 vt
            (by simpa only [chdr, List.append_assoc] using hlink)
            (by rw [htw1]; rw [htw_all] at h64; omega) st1 (by rw [htw1]; exact hpc1) hgp1 hrt1
        have htw2 : lkm.totalSize (pre ++ pH.1 ++ chdr) = lkm.totalSize pre + lkm.totalSize pH.1 + 3 := by
          rw [lkm.totalSize_append, htw1, htw_hdr]
        have hta := tieredOk_len64_addr_T L.T a vt heOk.1.1
        have hri2 : st2.getReg pH.2.2 = vi.toBitVec :=
          (hoth2 pH.2.2 (idxReg_ne_temp hri (by decide)) (idxReg_ne_temp hri (by decide))).trans hri1
        have rb := reg_ld32hTail_body_r env L fl lm loc (tierA a vt) hta.1 hiFlag i vi hvi (pre ++ pH.1 ++ chdr) post rd pH.2.2
          AbiReg.t1 AbiReg.t1 AbiReg.t2 AbiReg.t3 AbiReg.t3
          hrd hri (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (env.tab.len64 (TieredArray.t0 a)) (env.tab.base64 (TieredArray.t0 a))
          st2 (by rw [htw2, ← htw1]; exact hpc2) (by rw [ht1_2]; exact hta.2.1) (by rw [ht1_2]; exact hta.2.2)
          hri2 (by rw [hmem2]; exact hmemRel1)
          (by simpa only [cbody, List.append_assoc] using hlink)
          (by rw [htw2]; rw [htw_all] at h64; dsimp only [cbody] at h64; omega)
        by_cases hbound : vi.toNat < (lm.arr64 (tierA a vt)).size
        · simp only [hbound, ↓reduceDIte] at rb
          obtain ⟨k3, st3, hrun3, hpc3, hrd3, hpres3, hmem3, ht4_3⟩ := rb
          have hev : _root_.L.evalE (.ld32h a t i hiFlag) ⟨lm, loc⟩ =
              .ok (half32b hiFlag ((lm.arr64 (tierA a vt))[vi.toNat]'hbound), ⟨lm, loc⟩) := by
            change (_root_.L.evalE t >>= fun u => _root_.L.evalE i >>= fun idx => do
              let w' ← _root_.L.ld64 (tierA a u) idx; return half32b hiFlag w') ⟨lm, loc⟩ = _
            simp only [Bind.bind, StateT.bind, Except.bind, hvt, hvi, _root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get]
            simp [hbound, Pure.pure, StateT.pure, Except.pure]
          rw [hev]
          exact ⟨k1 + (3 + k3), st3,
            by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
            by dsimp only [cbody] at htw_all; rw [hpc3, htw2, htw_all]; congr 2; omega, hrd3,
            (PreservedFrameRegs.of_a0 (hpres1.trans hpres2)).trans hpres3, by rw [hmem3, hmem2]; exact heq1,
            fun hnt => by
              simp only [exprNoT4, Bool.and_eq_true] at hnt
              exact ht4_3.trans ((hoth2 AbiReg.t4 (by decide) (by decide)).trans (ht4_1 hnt.1 hnt.2))⟩
        · simp only [hbound, ↓reduceDIte] at rb
          obtain ⟨k3, st3, hrun3, hpc3, hpres3, hmem3⟩ := rb
          have hev : _root_.L.evalE (.ld32h a t i hiFlag) ⟨lm, loc⟩ = .error .oob := by
            change (_root_.L.evalE t >>= fun u => _root_.L.evalE i >>= fun idx => do
              let w' ← _root_.L.ld64 (tierA a u) idx; return half32b hiFlag w') ⟨lm, loc⟩ = _
            simp only [Bind.bind, StateT.bind, Except.bind, hvt, hvi, _root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get]
            simp [hbound, Pure.pure, Except.pure, Function.comp_apply, throw, throwThe, MonadExceptOf.throw, StateT.lift]; rfl
          rw [hev]
          exact ⟨k1 + (3 + k3), st3,
            by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
            hpc3, (PreservedFrameRegs.of_a0 (hpres1.trans hpres2)).trans hpres3, by rw [hmem3, hmem2]; exact heq1⟩
      · simp only [hvt, hvi] at headSim
        obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := headSim
        have hev : _root_.L.evalE (.ld32h a t i hiFlag) ⟨lm, loc⟩ = .error .oob := by
          dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hvt]; dsimp only; rw [hvi]; try rfl
        rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
    · simp only [hvt] at headSim
      obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := headSim
      have hev : _root_.L.evalE (.ld32h a t i hiFlag) ⟨lm, loc⟩ = .error .oob := by
        dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hvt]
      rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩

/-- Simulation for `emitLd32hPlainFrom` (fused `.ld64 a i & 0xffffffff` / `>> 32`). -/
private theorem reg_emitLd32hPlainFrom_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (a : ArrId) (i : Expr) (hiFlag : Bool) (ihi : RegEvalExprIH env L fl lm loc sp i)
    (pre post : List AsmItem) (tmp : Nat) (rd : Reg) (hrd : ValidTargetReg fl rd)
    (haOk : env.tab.wordPosOkB (TieredArray.t0 a) = true)
    (hiOk : exprOkB env.tab fl.nlocals i = true)
    (hTmp : tmp + usedTempsExpr i ≤ fl.usedTemps)
    (hlink : lkm.linkSpec (pre ++ emitLd32hPlainFrom env.tab fl rd a i hiFlag
        (fun () => compileETo env.tab fl tmp AbiReg.a0 i) ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (emitLd32hPlainFrom env.tab fl rd a i hiFlag
        (fun () => compileETo env.tab fl tmp AbiReg.a0 i))) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    let code := emitLd32hPlainFrom env.tab fl rd a i hiFlag (fun () => compileETo env.tab fl tmp AbiReg.a0 i)
    match _root_.L.evalE (.ld64 a i) ⟨lm, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize code)) ∧
        st'.getReg rd = (half32b hiFlag v).toBitVec ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem ∧
        (exprNoT4 i = true → st'.getReg AbiReg.t4 = st.getReg AbiReg.t4)
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
  intro code
  let s := TieredArray.t0 a
  let pI := match exprReg? fl.alloc i with | some r => ([], r) | none => (compileETo env.tab fl tmp AbiReg.a0 i, AbiReg.a0)
  let cbody :=
    loadMemOff .ld AbiReg.t0 (gpBaseReg fl.useT5Gp (env.tab.len64 s)) AbiReg.t1 (gpAdjOff fl.useT5Gp (env.tab.len64 s)) ++
    [Asm.bgeu pI.2 AbiReg.t0 errLabel] ++
    loadMemOff .ld AbiReg.t1 (gpBaseReg fl.useT5Gp (env.tab.base64 s)) AbiReg.t2 (gpAdjOff fl.useT5Gp (env.tab.base64 s)) ++
    ld32hTail rd pI.2 AbiReg.t2 i hiFlag
  have hdef : code = pI.1 ++ cbody := by
    cases h : exprReg? fl.alloc i <;>
      simp [code, emitLd32hPlainFrom, s, pI, h, cbody, loadMemOffGp_eq_loadMemOff, List.append_assoc]
  change lkm.linkSpec (pre ++ code ++ post) = _ at hlink
  change 4 * (lkm.totalSize pre + lkm.totalSize code) < 2 ^ 64 at h64
  rw [hdef] at hlink h64 ⊢
  have htw_all : lkm.totalSize (pI.1 ++ cbody) = lkm.totalSize pI.1 + lkm.totalSize cbody := lkm.totalSize_append _ _
  have riRes := reg_evalIdx_of_ih env L fl hfl lm loc i pre (cbody ++ post) tmp hiOk hTmp
    (fun p q tm r st' hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => ihi p q tm r hr hiOk ht hl h6 st' hpc' hgp' ht5' hsp' hm' hf')
    (by simpa only [pI, List.append_assoc] using hlink)
    (by rw [htw_all] at h64; dsimp only [pI] at h64 ⊢; omega) st hpc hgp ht5 hsp hmemRel hframeOk
  rcases riRes with ⟨hri, riSim⟩
  rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
  · simp only [hvi] at riSim
    obtain ⟨k1, st1, hrun1, hpc1, hri1, hpres1, heq1, ht4_1⟩ := riSim
    have htw1 : lkm.totalSize (pre ++ pI.1) = lkm.totalSize pre + lkm.totalSize pI.1 := lkm.totalSize_append _ _
    have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.abi.gp.trans hgp
    have ht5_1 : T5GpOk L fl st1 := ht5.of_preserved hpres1
    have hmemRel1 := ProgMemRel.of_tempSpanR hlo hhi (by omega) heq1 hmemRel
    have rb := reg_ld32hTail_body_r env L fl lm loc s haOk hiFlag i vi hvi (pre ++ pI.1) post rd pI.2
      (gpBaseReg fl.useT5Gp (env.tab.len64 s)) (gpBaseReg fl.useT5Gp (env.tab.base64 s))
      AbiReg.t0 AbiReg.t1 AbiReg.t2 hrd hri (by decide) (by decide) (by decide) (by decide)
      (gpBaseReg_ne_temp _ _ (by decide)) (gpBaseReg_ne_temp _ _ (by decide))
      (gpBaseReg_ne_temp _ _ (by decide)) (gpBaseReg_ne_temp _ _ (by decide)) (gpBaseReg_ne_t6_s1 _ _)
      (gpAdjOff fl.useT5Gp (env.tab.len64 s)) (gpAdjOff fl.useT5Gp (env.tab.base64 s))
      st1 (by rw [htw1]; exact hpc1) (gpBaseReg_addr hgp1 ht5_1) (gpBaseReg_addr hgp1 ht5_1)
      hri1 hmemRel1 (by simpa only [cbody, List.append_assoc] using hlink)
      (by rw [htw1]; rw [htw_all] at h64; dsimp only [cbody] at h64; omega)
    by_cases hbound : vi.toNat < (lm.arr64 s).size
    · simp only [hbound, ↓reduceDIte] at rb
      obtain ⟨k2, st2, hrun2, hpc2, hrd2, hpres2, hmem2, ht4_2⟩ := rb
      have hev : _root_.L.evalE (.ld64 a i) ⟨lm, loc⟩ = .ok ((lm.arr64 s)[vi.toNat]'hbound, ⟨lm, loc⟩) := by
        change (_root_.L.evalE i >>= _root_.L.ld64 s) ⟨lm, loc⟩ = _
        simp only [Bind.bind, StateT.bind, Except.bind, hvi, _root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get]
        simp [s, hbound, Pure.pure, StateT.pure, Except.pure]
      rw [hev]
      exact ⟨k1 + k2, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
        by dsimp only [cbody] at htw_all; rw [hpc2, htw1, htw_all]; congr 2; omega, hrd2,
        (PreservedFrameRegs.of_a0 hpres1).trans hpres2, by rw [hmem2]; exact heq1,
        fun hnt => ht4_2.trans (ht4_1 hnt)⟩
    · simp only [hbound, ↓reduceDIte] at rb
      obtain ⟨k2, st2, hrun2, hpc2, hpres2, hmem2⟩ := rb
      have hev : _root_.L.evalE (.ld64 a i) ⟨lm, loc⟩ = .error .oob := by
        change (_root_.L.evalE i >>= _root_.L.ld64 s) ⟨lm, loc⟩ = _
        simp only [Bind.bind, StateT.bind, Except.bind, hvi, _root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get]
        simp [s, hbound, Pure.pure, Except.pure, Function.comp_apply, throw, throwThe, MonadExceptOf.throw, StateT.lift]; rfl
      rw [hev]
      exact ⟨k1 + k2, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
        hpc2, (PreservedFrameRegs.of_a0 hpres1).trans hpres2, by rw [hmem2]; exact heq1⟩
  · simp only [hvi] at riSim
    obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := riSim
    have hev : _root_.L.evalE (.ld64 a i) ⟨lm, loc⟩ = .error .oob := by
      dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hvi]
    rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩

/-- Simulation for fused `(inner >> k) & mask` emitted via `emitShrMaskFrom`. -/
private theorem reg_emitShrMask_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (inner : Expr) (k mask : UInt64) (lmSh : BitVec 6)
    (hlm : lowMaskShift? mask = some lmSh)
    (hshLe : k.toNat % 64 ≤ lmSh.toNat)
    (ihInner : RegEvalExprIH env L fl lm loc sp inner)
    (pre post : List AsmItem) (tmp : Nat) (rd : Reg) (hrd : ValidTargetReg fl rd)
    (hiOk : exprOkB env.tab fl.nlocals inner = true)
    (hTmp : tmp + usedTempsExpr inner ≤ fl.usedTemps)
    (hlink : lkm.linkSpec (pre ++ emitShrMaskFrom fl rd inner (lmSh.toNat - k.toNat % 64) lmSh
        (fun () => compileETo env.tab fl tmp AbiReg.a0 inner) ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (emitShrMaskFrom fl rd inner (lmSh.toNat - k.toNat % 64) lmSh
        (fun () => compileETo env.tab fl tmp AbiReg.a0 inner))) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    let code := emitShrMaskFrom fl rd inner (lmSh.toNat - k.toNat % 64) lmSh
      (fun () => compileETo env.tab fl tmp AbiReg.a0 inner)
    match _root_.L.evalE (.bin .and (.bin .shr inner (.const k)) (.const mask)) ⟨lm, loc⟩ with
    | .ok (v, _) =>
      ∃ k' st', RV64.run env.rom k' st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize code)) ∧
        st'.getReg rd = v.toBitVec ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem ∧
        (exprNoT4 inner = true → st'.getReg AbiReg.t4 = st.getReg AbiReg.t4)
    | .error _ =>
      ∃ k' st', RV64.run env.rom k' st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
  intro code
  have ⟨hmaskEq, hlm0, hlm64⟩ := lowMaskShift_spec hlm
  let lsh := lmSh.toNat - k.toNat % 64
  let pI := match exprReg? fl.alloc inner with
    | some r => ([], r) | none => (compileETo env.tab fl tmp AbiReg.a0 inner, AbiReg.a0)
  let s1 := if lsh == 0 then (if rd == pI.2 then [] else [Asm.mv rd pI.2]) else [Asm.slli rd pI.2 (BitVec.ofNat 6 lsh)]
  let s2 := [Asm.srli rd rd lmSh]
  have hdef : code = pI.1 ++ s1 ++ s2 := by
    cases h : exprReg? fl.alloc inner <;> simp [code, emitShrMaskFrom, pI, h, s1, s2, lsh, List.append_assoc]
  change lkm.linkSpec (pre ++ code ++ post) = _ at hlink
  change 4 * (lkm.totalSize pre + lkm.totalSize code) < 2 ^ 64 at h64
  rw [hdef] at hlink h64 ⊢
  have htw_s2 : lkm.totalSize s2 = 1 := by simp [s2, Asm.srli, lkm.totalSize_instr]
  have htw_all : lkm.totalSize (pI.1 ++ s1 ++ s2) = lkm.totalSize pI.1 + lkm.totalSize s1 + 1 := by
    simp only [lkm.totalSize_append, htw_s2]
  have riRes := reg_evalIdx_of_ih env L fl hfl lm loc inner pre (s1 ++ s2 ++ post) tmp hiOk hTmp
    (fun p q tm r st' hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' => ihInner p q tm r hr hiOk ht hl h6 st' hpc' hgp' ht5' hsp' hm' hf')
    (by simpa only [pI, List.append_assoc] using hlink)
    (by rw [htw_all] at h64; dsimp only [pI] at h64 ⊢; omega) st hpc hgp ht5 hsp hmemRel hframeOk
  rcases riRes with ⟨_, riSim⟩
  rcases _root_.L.evalE_pure inner ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
  · simp only [hvi] at riSim
    obtain ⟨k1, st1, hrun1, hpc1, hri1, hpres1, heq1, ht4_1⟩ := riSim
    have htw1 : lkm.totalSize (pre ++ pI.1) = lkm.totalSize pre + lkm.totalSize pI.1 := lkm.totalSize_append _ _
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ pI.1)) := by rw [htw1]; exact hpc1
    have hstep1 : ∃ k2 st2, RV64.run env.rom k2 st1 = .cont st2 ∧
        st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ pI.1 ++ s1)) ∧
        st2.getReg rd = vi.toBitVec <<< lsh ∧
        PreservedFrameRegs fl (· = rd) st1 st2 ∧
        st2.mem = st1.mem ∧
        st2.getReg AbiReg.t4 = st1.getReg AbiReg.t4 := by
      by_cases hl0 : lsh = 0
      · have hs1Eq : s1 = if rd == pI.2 then [] else [Asm.mv rd pI.2] := by simp [s1, hl0]
        by_cases hrEq : rd = pI.2
        · have hs1Nil : s1 = [] := by rw [hs1Eq, hrEq]; simp
          refine ⟨0, st1, rfl, by rw [hs1Nil, List.append_nil]; exact hpc1',
            by rw [hrEq, hri1, hl0, BitVec.shiftLeft_zero], PreservedFrameRegs.refl _ _ _, rfl, rfl⟩
        · have hs1Mv : s1 = [Asm.mv rd pI.2] := by rw [hs1Eq, beq_false_of_ne hrEq]; rfl
          have htw_s1 : lkm.totalSize s1 = 1 := by rw [hs1Mv, Asm.mv, lkm.totalSize_instr]
          have hs := step_item_instr_lm lkm env.hrom (pre ++ pI.1) (s2 ++ post) (.aluImm .addi rd pI.2 0#12)
            (by rw [hs1Mv] at hlink; simpa only [Asm.mv, Asm.addi, List.append_assoc] using hlink)
            (by rw [htw1]; rw [htw_all, htw_s1] at h64; omega) st1 hpc1'
          let st2 := stepReg st1 rd (st1.getReg pI.2 + sextImm12 0#12) (st1.pc + 4#64)
          refine ⟨1, st2, run_one_cont _ _ st2 (by rw [hs]; rfl),
            by change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1', lkm.totalSize_append (pre ++ pI.1) s1, htw_s1],
            by change (stepReg st1 rd _ _).getReg rd = _
               rw [getReg_stepReg_eq _ _ hrd.ne_zero, hri1, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero, hl0, BitVec.shiftLeft_zero],
            PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) (fun r hr => getReg_stepReg_ne st1 rd r hr _ _),
            mem_stepReg _ _ _ _,
            getReg_stepReg_ne st1 rd AbiReg.t4 (hrd.ne_temp (by decide)).symm _ _⟩
      · have hs1Sll : s1 = [Asm.slli rd pI.2 (BitVec.ofNat 6 lsh)] := by simp [s1, beq_false_of_ne hl0]
        have htw_s1 : lkm.totalSize s1 = 1 := by rw [hs1Sll, Asm.slli, lkm.totalSize_instr]
        have hs := step_item_instr_lm lkm env.hrom (pre ++ pI.1) (s2 ++ post) (.shImm .slli rd pI.2 (BitVec.ofNat 6 lsh))
          (by rw [hs1Sll] at hlink; simpa only [Asm.slli, List.append_assoc] using hlink)
          (by rw [htw1]; rw [htw_all, htw_s1] at h64; omega) st1 hpc1'
        let st2 := stepReg st1 rd (st1.getReg pI.2 <<< (BitVec.ofNat 6 lsh).toNat) (st1.pc + 4#64)
        refine ⟨1, st2, run_one_cont _ _ st2 (by rw [hs]; rfl),
          by change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1', lkm.totalSize_append (pre ++ pI.1) s1, htw_s1],
          by change (stepReg st1 rd _ _).getReg rd = _
             rw [getReg_stepReg_eq _ _ hrd.ne_zero, hri1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)],
          PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) (fun r hr => getReg_stepReg_ne st1 rd r hr _ _),
          mem_stepReg _ _ _ _,
          getReg_stepReg_ne st1 rd AbiReg.t4 (hrd.ne_temp (by decide)).symm _ _⟩
    obtain ⟨k2, st2, hrun2, hpc2, hrd2, hpres2, hmem2, ht4_2⟩ := hstep1
    have htw2 : lkm.totalSize (pre ++ pI.1 ++ s1) = lkm.totalSize pre + lkm.totalSize pI.1 + lkm.totalSize s1 := by
      rw [lkm.totalSize_append, htw1]
    have hs3 := step_item_instr_lm lkm env.hrom (pre ++ pI.1 ++ s1) post (.shImm .srli rd rd lmSh)
      (by simpa only [s2, Asm.srli, List.append_assoc] using hlink)
      (by rw [htw2]; rw [htw_all] at h64; omega) st2 hpc2
    let st3 := stepReg st2 rd (st2.getReg rd >>> lmSh.toNat) (st2.pc + 4#64)
    have hev : _root_.L.evalE (.bin .and (.bin .shr inner (.const k)) (.const mask)) ⟨lm, loc⟩ =
        .ok (BinOp.and.eval (BinOp.shr.eval vi k) mask, ⟨lm, loc⟩) := by
      dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hvi]; rfl
    rw [hev]
    have hval : (vi.toBitVec <<< lsh) >>> lmSh.toNat = (BinOp.and.eval (BinOp.shr.eval vi k) mask).toBitVec := by
      rw [uint64_binop_toBitVec .and, uint64_binop_toBitVec .shr]
      dsimp only
      have hex : (k.toBitVec.extractLsb' 0 6).toNat = k.toNat % 64 := by
        rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, UInt64.toNat_toBitVec]
      rw [hex]
      exact (bv_shr_and_lowMask hmaskEq hlm0 hlm64 hshLe).symm
    refine ⟨k1 + (k2 + 1), st3,
      by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact run_one_cont _ _ st3 (by rw [hs3]; rfl),
      by change st2.pc + 4#64 = _; rw [pc_add_4_ofNat st2.pc hpc2, htw2, htw_all]; congr 2; omega,
      by change (stepReg st2 rd _ _).getReg rd = _; rw [getReg_stepReg_eq _ _ hrd.ne_zero, hrd2, hval],
      (PreservedFrameRegs.of_a0 hpres1).trans (hpres2.trans
        (PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) (fun r hr => getReg_stepReg_ne st2 rd r hr _ _))),
      by rw [mem_stepReg, hmem2]; exact heq1,
      fun hnt => (getReg_stepReg_ne st2 rd AbiReg.t4 (hrd.ne_temp (by decide)).symm _ _).trans (ht4_2.trans (ht4_1 hnt))⟩
  · simp only [hvi] at riSim
    obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := riSim
    have hev : _root_.L.evalE (.bin .and (.bin .shr inner (.const k)) (.const mask)) ⟨lm, loc⟩ = .error .oob := by
      dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hvi]
    rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩

/-- Full forward simulation of `compileETo tab fl tmp rd e` for any valid target `rd`,
    additionally tracking preservation of `t4` whenever `exprNoT4 e = true`. -/
theorem reg_evalExpr_sim_noT4 {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (e : Expr) (pre post : List AsmItem) (tmp : Nat) (rd : Reg)
    (hrd : ValidTargetReg fl rd)
    (heOk : exprOkB env.tab fl.nlocals e = true)
    (hVf : ExprVarsInFrame fl e)
    (hTmp : tmp + usedTempsExpr e ≤ fl.usedTemps)
    (hlink : lkm.linkSpec (pre ++ compileETo env.tab fl tmp rd e ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd e)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    match _root_.L.evalE e ⟨lm, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd e))) ∧
        st'.getReg rd = v.toBitVec ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem ∧
        (exprNoT4 e = true → st'.getReg AbiReg.t4 = st.getReg AbiReg.t4)
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
  have hf : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  have exprNoT4_of_isSimple : ∀ {x : Expr}, isSimpleExpr x = true → exprNoT4 x = true := by
    intro x hx; cases x <;> simp [isSimpleExpr, exprNoT4] at hx ⊢
  suffices ∀ (n : Nat) (e : Expr), sizeOf e ≤ n →
      ∀ (pre post : List AsmItem) (tmp : Nat) (rd : Reg),
      ValidTargetReg fl rd →
      exprOkB env.tab fl.nlocals e = true →
      ExprVarsInFrame fl e →
      tmp + usedTempsExpr e ≤ fl.usedTemps →
      lkm.linkSpec (pre ++ compileETo env.tab fl tmp rd e ++ post) = .ok (env.code, env.labels) →
      4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd e)) < 2 ^ 64 →
      ∀ (st : State), st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → T5GpOk L fl st → st.getReg AbiReg.sp = sp →
      ProgMemRel env.tab L st.mem lm → ProgFrameOkR L fl sp st loc →
      match _root_.L.evalE e ⟨lm, loc⟩ with
      | .ok (v, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd e))) ∧
          st'.getReg rd = v.toBitVec ∧
          PreservedFrameRegs fl (· = rd) st st' ∧
          MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem ∧
          (exprNoT4 e = true → st'.getReg AbiReg.t4 = st.getReg AbiReg.t4)
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedFrameRegs fl (· = rd) st st' ∧
          MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem from
    this (sizeOf e) e (Nat.le_refl _) pre post tmp rd hrd heOk hVf hTmp hlink h64 st hpc hgp ht5 hsp hmemRel hframeOk
  intro n
  induction n with
  | zero => intro e hsz; cases e <;> simp at hsz
  | succ n ih =>
    intro e hsz pre post tmp rd hrd heOk hVf hTmp hlink h64 st hpc hgp ht5 hsp hmemRel hframeOk
    let mkIH (e' : Expr) (hsz' : sizeOf e' ≤ n) (hvf' : ExprVarsInFrame fl e') :
        RegEvalExprIH env L fl lm loc sp e' :=
      fun p q tm r hr hok ht hl h6 s hpc' hgp' ht5' hsp' hm' hf' =>
        ih e' hsz' p q tm r hr hok hvf' ht hl h6 s hpc' hgp' ht5' hsp' hm' hf'
    cases e with
    | const w =>
      simp only [compileETo] at hlink h64 ⊢
      obtain ⟨st', hrun, hoth, hrd', hmem, hpc'⟩ :=
        li_correct_lm lkm env.hrom pre post rd hrd.ne_zero (BitVec.ofNat 64 w.toNat) hlink h64 st hpc
      have hw : BitVec.ofNat 64 w.toNat = w.toBitVec := by
        rw [← UInt64.toBitVec_ofNat' w.toNat, UInt64.ofNat_toNat]
      exact ⟨_, st', hrun, hpc', hrd'.trans hw,
        PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) hoth, by rw [hmem]; exact MemEqOutside.refl _ _,
        fun _ => hoth AbiReg.t4 (hrd.ne_temp (by decide)).symm⟩
    | var x =>
      simp only [exprOkB, decide_eq_true_eq] at heOk
      simp only [compileETo] at hlink h64 ⊢
      have hfx := hframeOk x heOk
      cases hlk : fl.alloc.lookup x with
      | some rx =>
        rw [hlk] at hfx hlink h64
        dsimp only at hfx hlink h64 ⊢
        by_cases heq : rd = rx
        · subst heq; simp only [beq_self_eq_true, ↓reduceIte, lkm.totalSize_nil, Nat.add_zero]
          exact ⟨0, st, rfl, hpc, hfx, PreservedFrameRegs.refl _ _ _, MemEqOutside.refl _ _, fun _ => rfl⟩
        · have hbf : (rd == rx) = false := beq_false_of_ne heq
          simp only [hbf, Bool.false_eq_true, ↓reduceIte] at hlink h64 ⊢
          have hs := step_item_instr_lm lkm env.hrom pre post (.aluImm .addi rd rx 0#12)
            (by simpa only [Asm.mv, Asm.addi] using hlink) (by simp [Asm.mv, lkm.itemSize_instr] at h64; omega) st hpc
          let st' := stepReg st rd (st.getReg rx + sextImm12 0#12) (st.pc + 4#64)
          refine ⟨1, st', run_one_cont _ _ st' (by rw [hs]; rfl),
            by rw [Asm.mv, lkm.totalSize_instr]; exact pc_add_4_ofNat st.pc hpc,
            by rw [getReg_stepReg_eq _ _ hrd.ne_zero, hfx, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero],
            PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) (fun r hr => getReg_stepReg_ne st rd r hr _ _),
            by rw [mem_stepReg]; exact MemEqOutside.refl _ _,
            fun _ => getReg_stepReg_ne st rd AbiReg.t4 (hrd.ne_temp (by decide)).symm _ _⟩
      | none =>
        rw [hlk] at hfx hlink h64
        dsimp only at hfx hlink h64 ⊢
        have hal : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (fl.varSlotOff x)) 8 = true := by
          rw [hsp, varSlotOff_ofInt]; exact isAligned8_add_mul8 sp hspAlign _
        obtain ⟨st', hrun, hoth, hrd', hmem, hpc'⟩ :=
          loadMemOff_ld_correct_lm lkm env.hrom pre post rd AbiReg.sp AbiReg.t0
            hrd.ne_zero (by decide) (by decide) (fl.varSlotOff x) hlink h64 st hpc hal
        exact ⟨_, st', hrun, hpc', by rw [hrd', hsp]; exact hfx (hVf x (by simp [exprUsesVar]) hlk),
          PreservedFrameRegs.of_target_scratch rd AbiReg.t0 hrd (fun _ => rfl) (by decide) hoth,
          by rw [hmem]; exact MemEqOutside.refl _ _,
          fun _ => hoth AbiReg.t4 (hrd.ne_temp (by decide)).symm (by decide)⟩
    | len8 a =>
      simp only [compileETo] at hlink h64 ⊢
      obtain ⟨v, k, st', hev, hrun, hpc', hrd', hoth, hmem⟩ :=
        reg_emitSimpleExprR_sim env L fl hfl lm loc hspAlign pre post rd AbiReg.t0
          hrd.ne_zero (by decide) (by decide) (by decide) (fun _ => by decide) (.len8 a) _ rfl heOk hVf hlink h64
          st hpc hgp ht5 hsp hmemRel hframeOk
      rw [hev]
      exact ⟨k, st', hrun, hpc', hrd',
        PreservedFrameRegs.of_target_scratch rd AbiReg.t0 hrd (fun _ => rfl) (by decide) hoth,
        by rw [hmem]; exact MemEqOutside.refl _ _,
        fun _ => hoth AbiReg.t4 (hrd.ne_temp (by decide)).symm (by decide)⟩
    | len64 a =>
      simp only [compileETo] at hlink h64 ⊢
      obtain ⟨v, k, st', hev, hrun, hpc', hrd', hoth, hmem⟩ :=
        reg_emitSimpleExprR_sim env L fl hfl lm loc hspAlign pre post rd AbiReg.t0
          hrd.ne_zero (by decide) (by decide) (by decide) (fun _ => by decide) (.len64 a) _ rfl heOk hVf hlink h64
          st hpc hgp ht5 hsp hmemRel hframeOk
      rw [hev]
      exact ⟨k, st', hrun, hpc', hrd',
        PreservedFrameRegs.of_target_scratch rd AbiReg.t0 hrd (fun _ => rfl) (by decide) hoth,
        by rw [hmem]; exact MemEqOutside.refl _ _,
        fun _ => hoth AbiReg.t4 (hrd.ne_temp (by decide)).symm (by decide)⟩
    | glob g =>
      simp only [compileETo] at hlink h64 ⊢
      obtain ⟨v, k, st', hev, hrun, hpc', hrd', hoth, hmem⟩ :=
        reg_emitSimpleExprR_sim env L fl hfl lm loc hspAlign pre post rd AbiReg.t0
          hrd.ne_zero (by decide) (by decide) (by decide) (fun _ => by decide) (.glob g) _ rfl heOk hVf hlink h64
          st hpc hgp ht5 hsp hmemRel hframeOk
      rw [hev]
      exact ⟨k, st', hrun, hpc', hrd',
        PreservedFrameRegs.of_target_scratch rd AbiReg.t0 hrd (fun _ => rfl) (by decide) hoth,
        by rw [hmem]; exact MemEqOutside.refl _ _,
        fun _ => hoth AbiReg.t4 (hrd.ne_temp (by decide)).symm (by decide)⟩
    | bin op a b =>
      have hfb : ∀ (code : List AsmItem),
          code = compileBinFallback env.tab fl tmp rd op a b
            (fun () => compileETo env.tab fl tmp AbiReg.a0 a)
            (fun () => compileETo env.tab fl tmp AbiReg.a0 b)
            (fun () => compileETo env.tab fl (tmp + 1) AbiReg.a0 b) →
          lkm.linkSpec (pre ++ code ++ post) = .ok (env.code, env.labels) →
          4 * (lkm.totalSize pre + lkm.totalSize code) < 2 ^ 64 →
          match _root_.L.evalE (.bin op a b) ⟨lm, loc⟩ with
          | .ok (v, _) =>
            ∃ k st', RV64.run env.rom k st = .cont st' ∧
              st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize code)) ∧
              st'.getReg rd = v.toBitVec ∧
              PreservedFrameRegs fl (· = rd) st st' ∧
              MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem ∧
              (exprNoT4 (.bin op a b) = true → st'.getReg AbiReg.t4 = st.getReg AbiReg.t4)
          | .error _ =>
            ∃ k st', RV64.run env.rom k st = .cont st' ∧
              st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
              PreservedFrameRegs fl (· = rd) st st' ∧
              MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
        intro code hdef hl h6
        subst hdef
        exact reg_evalExpr_bin_sim env L fl hfl lm loc hspAlign hlo hhi op a b
          (mkIH a (by simp at hsz; omega) (fun x hx => hVf x (by simp [exprUsesVar, hx])))
          (mkIH b (by simp at hsz; omega) (fun x hx => hVf x (by simp [exprUsesVar, hx])))
          pre post tmp rd hrd heOk hVf hTmp hl h6 st hpc hgp ht5 hsp hmemRel hframeOk
      generalize hce : compileETo env.tab fl tmp rd (.bin op a b) = code at hlink h64 ⊢
      rw [compileETo.eq_def] at hce
      dsimp only at hce
      split at hce
      · next inner k mask =>
        cases hlm : lowMaskShift? mask with
        | none =>
          simp only [hlm] at hce
          exact hfb code hce.symm hlink h64
        | some lmSh =>
          by_cases hsh : (0 < k.toNat % 64 && k.toNat % 64 ≤ lmSh.toNat) = true
          · simp only [hlm, hsh, ↓reduceIte] at hce
            subst hce
            have hshLe : k.toNat % 64 ≤ lmSh.toNat := by
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hsh; exact hsh.2
            have hiOk : exprOkB env.tab fl.nlocals inner = true := by
              simp only [exprOkB, Bool.and_eq_true] at heOk; exact heOk.1.1
            have hiVf : ExprVarsInFrame fl inner := fun x hx => hVf x (by simp [exprUsesVar, hx])
            have hiTmp : tmp + usedTempsExpr inner ≤ fl.usedTemps := by
              simpa only [usedTempsExpr, isSimpleExpr, ↓reduceIte] using hTmp
            have r := reg_emitShrMask_sim env L fl hfl lm loc inner k mask lmSh hlm hshLe
              (mkIH inner (by simp at hsz; omega) hiVf)
              pre post tmp rd hrd hiOk hiTmp hlink h64 st hpc hgp ht5 hsp hmemRel hframeOk
            cases hv : _root_.L.evalE (.bin .and (.bin .shr inner (.const k)) (.const mask)) ⟨lm, loc⟩ with
            | ok _ =>
              simp only [hv] at r
              rcases r with ⟨k', st', h1, h2, h3, h4, h5, h6⟩
              refine ⟨k', st', h1, h2, h3, h4, h5, fun hnt => h6 ?_⟩
              simp only [exprNoT4, isSimpleExpr, Bool.true_and, Bool.and_true, Bool.or_false,
                Bool.or_eq_true] at hnt
              rcases hnt with hnt | hs
              · exact hnt
              · exact exprNoT4_of_isSimple hs
            | error _ => simp only [hv] at r; exact r
          · have hshF : (0 < k.toNat % 64 && k.toNat % 64 ≤ lmSh.toNat) = false := Bool.eq_false_iff.mpr hsh
            simp only [hlm, hshF, Bool.false_eq_true, ↓reduceIte] at hce
            exact hfb code hce.symm hlink h64
      · next arr i =>
        subst hce
        simp only [exprOkB, Bool.and_eq_true] at heOk
        have hiVf : ExprVarsInFrame fl i := fun x hx => hVf x (by simp [exprUsesVar, hx])
        have hiTmp : tmp + usedTempsExpr i ≤ fl.usedTemps := by
          simpa only [usedTempsExpr, isSimpleExpr, ↓reduceIte] using hTmp
        have r := reg_emitLd32hPlainFrom_sim env L fl hfl lm loc hlo hhi arr i false
          (mkIH i (by simp at hsz; omega) hiVf)
          pre post tmp rd hrd heOk.1.1 heOk.1.2 hiTmp hlink h64 st hpc hgp ht5 hsp hmemRel hframeOk
        rcases _root_.L.evalE_pure (.ld64 arr i) ⟨lm, loc⟩ with ⟨v, hv⟩ | hv
        · simp only [hv] at r
          obtain ⟨k', st', h1, h2, h3, h4, h5, h6⟩ := r
          have hev : _root_.L.evalE (.bin .and (.ld64 arr i) (.const 0xffffffff)) ⟨lm, loc⟩ =
              .ok (BinOp.and.eval v 0xffffffff, ⟨lm, loc⟩) := by
            rw [_root_.L.evalE]; dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hv]; rfl
          rw [hev]
          refine ⟨k', st', h1, h2, ?_, h4, h5, fun hnt => h6 ?_⟩
          · rw [h3, half32b_false_eq_and]; rfl
          · simp only [exprNoT4, isSimpleExpr, Bool.true_and, Bool.false_and, Bool.or_false] at hnt; exact hnt
        · simp only [hv] at r
          have hev : _root_.L.evalE (.bin .and (.ld64 arr i) (.const 0xffffffff)) ⟨lm, loc⟩ = .error .oob := by
            rw [_root_.L.evalE]; dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hv]
          rw [hev]; exact r
      · next arr i =>
        subst hce
        simp only [exprOkB, Bool.and_eq_true] at heOk
        have hiVf : ExprVarsInFrame fl i := fun x hx => hVf x (by simp [exprUsesVar, hx])
        have hiTmp : tmp + usedTempsExpr i ≤ fl.usedTemps := by
          simpa only [usedTempsExpr, isSimpleExpr, ↓reduceIte] using hTmp
        have r := reg_emitLd32hPlainFrom_sim env L fl hfl lm loc hlo hhi arr i true
          (mkIH i (by simp at hsz; omega) hiVf)
          pre post tmp rd hrd heOk.1.1 heOk.1.2 hiTmp hlink h64 st hpc hgp ht5 hsp hmemRel hframeOk
        rcases _root_.L.evalE_pure (.ld64 arr i) ⟨lm, loc⟩ with ⟨v, hv⟩ | hv
        · simp only [hv] at r
          obtain ⟨k', st', h1, h2, h3, h4, h5, h6⟩ := r
          have hev : _root_.L.evalE (.bin .shr (.ld64 arr i) (.const 32)) ⟨lm, loc⟩ =
              .ok (BinOp.shr.eval v 32, ⟨lm, loc⟩) := by
            rw [_root_.L.evalE]; dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hv]; rfl
          rw [hev]
          refine ⟨k', st', h1, h2, ?_, h4, h5, fun hnt => h6 ?_⟩
          · rw [h3, half32b_true_eq_shr]; rfl
          · simp only [exprNoT4, isSimpleExpr, Bool.true_and, Bool.false_and, Bool.or_false] at hnt; exact hnt
        · simp only [hv] at r
          have hev : _root_.L.evalE (.bin .shr (.ld64 arr i) (.const 32)) ⟨lm, loc⟩ = .error .oob := by
            rw [_root_.L.evalE]; dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hv]
          rw [hev]; exact r
      · next arr t i =>
        subst hce
        have hOk32h : exprOkB env.tab fl.nlocals (.ld32h arr t i false) = true := by
          simp only [exprOkB, Bool.and_eq_true] at heOk ⊢; exact heOk.1
        have hVfT : ExprVarsInFrame fl t := fun x hx => hVf x (by simp [exprUsesVar, hx])
        have hVfI : ExprVarsInFrame fl i := fun x hx => hVf x (by simp [exprUsesVar, hx])
        have hTmp32h : tmp + usedTempsExpr (.ld32h arr t i false) ≤ fl.usedTemps := by
          simpa only [usedTempsExpr, isSimpleExpr, ↓reduceIte] using hTmp
        have hevEq : _root_.L.evalE (.bin .and (.ld64t arr t i) (.const 0xffffffff)) ⟨lm, loc⟩ =
            _root_.L.evalE (.ld32h arr t i false) ⟨lm, loc⟩ := by
          rcases _root_.L.evalE_pure t ⟨lm, loc⟩ with ⟨vt, hvt⟩ | hvt
          · rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
            · dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]
              rw [hvt]; dsimp only; rw [hvi]; dsimp only
              cases _root_.L.ld64 (tierA arr vt) vi ⟨lm, loc⟩ with
              | error _ => rfl
              | ok _ => rfl
            · dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]
              rw [hvt]; dsimp only; rw [hvi]
          · dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]
            rw [hvt]
        have r := reg_emitLd32hFrom_sim env L fl hfl lm loc hspAlign hlo hhi arr t i false
          (mkIH t (by simp at hsz; omega) hVfT) (mkIH i (by simp at hsz; omega) hVfI)
          pre post tmp rd hrd hOk32h hVfT hTmp32h hlink h64 st hpc hgp ht5 hsp hmemRel hframeOk
        rw [hevEq]
        cases hv : _root_.L.evalE (.ld32h arr t i false) ⟨lm, loc⟩ with
        | ok _ =>
          simp only [hv] at r
          rcases r with ⟨k', st', h1, h2, h3, h4, h5, h6⟩
          exact ⟨k', st', h1, h2, h3, h4, h5, fun hnt => h6 (by
            simp only [exprNoT4, isSimpleExpr, Bool.true_and, Bool.false_and, Bool.or_false] at hnt ⊢; exact hnt)⟩
        | error _ => simp only [hv] at r; exact r
      · next arr t i =>
        subst hce
        have hOk32h : exprOkB env.tab fl.nlocals (.ld32h arr t i true) = true := by
          simp only [exprOkB, Bool.and_eq_true] at heOk ⊢; exact heOk.1
        have hVfT : ExprVarsInFrame fl t := fun x hx => hVf x (by simp [exprUsesVar, hx])
        have hVfI : ExprVarsInFrame fl i := fun x hx => hVf x (by simp [exprUsesVar, hx])
        have hTmp32h : tmp + usedTempsExpr (.ld32h arr t i true) ≤ fl.usedTemps := by
          simpa only [usedTempsExpr, isSimpleExpr, ↓reduceIte] using hTmp
        have hevEq : _root_.L.evalE (.bin .shr (.ld64t arr t i) (.const 32)) ⟨lm, loc⟩ =
            _root_.L.evalE (.ld32h arr t i true) ⟨lm, loc⟩ := by
          rcases _root_.L.evalE_pure t ⟨lm, loc⟩ with ⟨vt, hvt⟩ | hvt
          · rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
            · dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]
              rw [hvt]; dsimp only; rw [hvi]; dsimp only
              cases _root_.L.ld64 (tierA arr vt) vi ⟨lm, loc⟩ with
              | error _ => rfl
              | ok _ => rfl
            · dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]
              rw [hvt]; dsimp only; rw [hvi]
          · dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]
            rw [hvt]
        have r := reg_emitLd32hFrom_sim env L fl hfl lm loc hspAlign hlo hhi arr t i true
          (mkIH t (by simp at hsz; omega) hVfT) (mkIH i (by simp at hsz; omega) hVfI)
          pre post tmp rd hrd hOk32h hVfT hTmp32h hlink h64 st hpc hgp ht5 hsp hmemRel hframeOk
        rw [hevEq]
        cases hv : _root_.L.evalE (.ld32h arr t i true) ⟨lm, loc⟩ with
        | ok _ =>
          simp only [hv] at r
          rcases r with ⟨k', st', h1, h2, h3, h4, h5, h6⟩
          exact ⟨k', st', h1, h2, h3, h4, h5, fun hnt => h6 (by
            simp only [exprNoT4, isSimpleExpr, Bool.true_and, Bool.false_and, Bool.or_false] at hnt ⊢; exact hnt)⟩
        | error _ => simp only [hv] at r; exact r
      · exact hfb code hce.symm hlink h64
    | cmpw c a b =>
      exact reg_evalExpr_cmpw_sim env L fl hfl lm loc hspAlign hlo hhi c a b
        (mkIH a (by simp at hsz; omega) (fun x hx => hVf x (by simp [exprUsesVar, hx])))
        (mkIH b (by simp at hsz; omega) (fun x hx => hVf x (by simp [exprUsesVar, hx])))
        pre post tmp rd hrd heOk hVf hTmp hlink h64 st hpc hgp ht5 hsp hmemRel hframeOk
    | ld8 a i =>
      simp only [exprOkB, Bool.and_eq_true] at heOk
      simp only [usedTempsExpr] at hTmp
      let pI := match exprReg? fl.alloc i with | some r => ([], r) | none => (compileETo env.tab fl tmp AbiReg.a0 i, AbiReg.a0)
      let clen := loadMemOffGp fl.useT5Gp .ld AbiReg.t0 AbiReg.t1 (env.tab.len8 a)
      let cbr := [Asm.bgeu pI.2 AbiReg.t0 errLabel]
      let cbase := loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (env.tab.base8 a)
      let ctail := match i.constVal? with
        | some w =>
          if w.toNat < 2048 then [Asm.lbu rd AbiReg.t1 (BitVec.ofNat 12 w.toNat)]
          else [Asm.add AbiReg.t1 AbiReg.t1 pI.2, Asm.lbu rd AbiReg.t1 0#12]
        | none => [Asm.add AbiReg.t1 AbiReg.t1 pI.2, Asm.lbu rd AbiReg.t1 0#12]
      have hdef : compileETo env.tab fl tmp rd (.ld8 a i) = pI.1 ++ clen ++ cbr ++ cbase ++ ctail := by
        cases h : exprReg? fl.alloc i <;> cases hi : i.constVal? <;>
          simp [compileETo, pI, h, hi, clen, cbr, cbase, ctail, List.append_assoc]
      rw [hdef] at hlink h64 ⊢
      have htw_all : lkm.totalSize (pI.1 ++ clen ++ cbr ++ cbase ++ ctail) =
          lkm.totalSize pI.1 + lkm.totalSize clen + lkm.totalSize cbr + lkm.totalSize cbase + lkm.totalSize ctail := by
        simp only [lkm.totalSize_append]
      have riRes := reg_evalIdx_of_ih env L fl hfl lm loc i pre (clen ++ cbr ++ cbase ++ ctail ++ post) tmp heOk.2 hTmp
        (fun p q t r s hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' =>
          mkIH i (by simp at hsz; omega) (fun x hx => hVf x (by simpa [exprUsesVar] using hx))
            p q t r hr heOk.2 ht hl h6 s hpc' hgp' ht5' hsp' hm' hf')
        (by simpa only [pI, List.append_assoc] using hlink)
        (by rw [htw_all] at h64; dsimp only [pI] at h64 ⊢; omega) st hpc hgp ht5 hsp hmemRel hframeOk
      rcases riRes with ⟨hri, riSim⟩
      rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
      · simp only [hvi] at riSim
        obtain ⟨k1, st1, hrun1, hpc1, hri1, hpres1, heq1, ht4_1⟩ := riSim
        have htw1 : lkm.totalSize (pre ++ pI.1) = lkm.totalSize pre + lkm.totalSize pI.1 := lkm.totalSize_append _ _
        have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.abi.gp.trans hgp
        have ht5_1 : T5GpOk L fl st1 := ht5.of_preserved hpres1
        have hmemRel1 := ProgMemRel.of_tempSpanR hlo hhi (by omega) heq1 hmemRel
        rcases hmemRel1.1 a heOk.1 with ⟨_, hlt64, hlenR, hbaseR, hbytesR⟩
        have halLen : isAligned (L.T + BitVec.ofInt 64 (env.tab.len8 a)) 8 = true := by
          rw [Tab.len8_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
        obtain ⟨st2, hrun2, hoth2, ht0_2, hmem2, hpc2⟩ :=
          loadMemOffGp_ld_correct_lm lkm env.hrom (pre ++ pI.1) (cbr ++ cbase ++ ctail ++ post)
            fl.useT5Gp AbiReg.t0 AbiReg.t1 (by decide) (by decide) (by decide) (fun _ => by decide) (env.tab.len8 a) L.T
            (by simpa only [List.append_assoc] using hlink)
            (by rw [htw1]; rw [htw_all] at h64; dsimp only [clen] at h64; omega) st1 (by rw [htw1]; exact hpc1) hgp1 ht5_1 halLen
        have hpres2 : PreservedFrameRegs fl (· = rd) st1 st2 :=
          PreservedFrameRegs.of_scratch2 AbiReg.t0 AbiReg.t1 (by decide) (by decide) hoth2
        have htw2 : lkm.totalSize (pre ++ pI.1 ++ clen) = lkm.totalSize pre + lkm.totalSize pI.1 + lkm.totalSize clen := by
          rw [lkm.totalSize_append, htw1]
        have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ pI.1 ++ clen)) := by rw [htw2, ← htw1]; exact hpc2
        have hri2 : st2.getReg pI.2 = vi.toBitVec :=
          (hoth2 pI.2 (idxReg_ne_temp hri (by decide)) (idxReg_ne_temp hri (by decide))).trans hri1
        have ht0_2' : st2.getReg AbiReg.t0 = BitVec.ofNat 64 (lm.arr8 a).size := by rw [ht0_2, hlenR]
        have hlinkBr : lkm.linkSpec ((pre ++ pI.1 ++ clen) ++ [.br .bgeu pI.2 AbiReg.t0 errLabel] ++ (cbase ++ ctail ++ post)) =
            .ok (env.code, env.labels) := by
          simpa only [cbr, Asm.bgeu, List.append_assoc] using hlink
        have h64Br : 4 * (lkm.totalSize (pre ++ pI.1 ++ clen) + lkm.itemSize (.br .bgeu pI.2 AbiReg.t0 errLabel)) < 2 ^ 64 := by
          rw [htw2]; rw [htw_all] at h64
          have : lkm.itemSize (.br .bgeu pI.2 AbiReg.t0 errLabel) = lkm.totalSize cbr := by simp [cbr, Asm.bgeu, lkm.totalSize_singleton]
          omega
        by_cases hbound : vi.toNat < (lm.arr8 a).size
        · have hev : _root_.L.evalE (.ld8 a i) ⟨lm, loc⟩ = .ok (((lm.arr8 a)[vi.toNat]'hbound).toUInt64, ⟨lm, loc⟩) := by
            change (_root_.L.evalE i >>= _root_.L.ld8 a) ⟨lm, loc⟩ = _
            simp only [Bind.bind, StateT.bind, Except.bind, hvi, _root_.L.ld8, get, getThe, MonadStateOf.get, StateT.get]
            simp [hbound, Pure.pure, StateT.pure, Except.pure]
          rw [hev]
          have hcondF : evalBranch .bgeu (st2.getReg pI.2) (st2.getReg AbiReg.t0) = false := by
            simp [evalBranch, hri2, ht0_2']
            rw [BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec, Nat.mod_eq_of_lt hlt64, decide_eq_true hbound]
          obtain ⟨kBr, st3, hrun3, hpc3', hoth3, _, hmem3⟩ :=
            prog_step_br_fall env (pre ++ pI.1 ++ clen) (cbase ++ ctail ++ post)
              .bgeu pI.2 AbiReg.t0 errLabel env.errTarget env.herrLbl ⟨idxReg_ne_temp hri (by decide), by decide⟩
              hlinkBr h64Br st2 hpc2' hcondF
          have hpres3 : PreservedFrameRegs fl (· = rd) st2 st3 :=
            PreservedFrameRegs.of_t6_s1 hoth3
          have htw3 : lkm.totalSize (pre ++ pI.1 ++ clen ++ cbr) =
              lkm.totalSize pre + lkm.totalSize pI.1 + lkm.totalSize clen + lkm.totalSize cbr := by
            rw [lkm.totalSize_append, htw2]
          have hpc3 : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ pI.1 ++ clen ++ cbr)) := by rw [hpc3', htw3, htw2]; rfl
          have hgp3 : st3.getReg AbiReg.gp = L.T := (hoth3 AbiReg.gp (by decide)).trans ((hoth2 AbiReg.gp (by decide) (by decide)).trans hgp1)
          have ht5_3 : T5GpOk L fl st3 := fun h => (hoth3 AbiReg.t5 (by decide)).trans ((hoth2 AbiReg.t5 (by decide) (by decide)).trans (ht5_1 h))
          have halBase : isAligned (L.T + BitVec.ofInt 64 (env.tab.base8 a)) 8 = true := by
            rw [Tab.base8_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
          obtain ⟨st4, hrun4, hoth4, ht1_4, hmem4, hpc4⟩ :=
            loadMemOffGp_ld_correct_lm lkm env.hrom (pre ++ pI.1 ++ clen ++ cbr) (ctail ++ post)
              fl.useT5Gp AbiReg.t1 AbiReg.t2 (by decide) (by decide) (by decide) (fun _ => by decide) (env.tab.base8 a) L.T
              (by simpa only [List.append_assoc] using hlink)
              (by rw [htw3]; rw [htw_all] at h64; dsimp only [cbase] at h64; omega) st3 hpc3 hgp3 ht5_3 halBase
          have hpres4 : PreservedFrameRegs fl (· = rd) st3 st4 :=
            PreservedFrameRegs.of_scratch2 AbiReg.t1 AbiReg.t2 (by decide) (by decide) hoth4
          let p4 := pre ++ pI.1 ++ clen ++ cbr ++ cbase
          have htw4 : lkm.totalSize p4 =
              lkm.totalSize pre + lkm.totalSize pI.1 + lkm.totalSize clen + lkm.totalSize cbr + lkm.totalSize cbase := by
            dsimp only [p4]; rw [lkm.totalSize_append, htw3]
          have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize p4) := by rw [htw4, ← htw3]; exact hpc4
          have ht1' : st4.getReg AbiReg.t1 = L.base8 a := by rw [ht1_4, hmem3, hmem2, hbaseR]
          have hm4 : st4.mem = st1.mem := by rw [hmem4, hmem3, hmem2]
          have ht4_04 : exprNoT4 (.ld8 a i) = true → st4.getReg AbiReg.t4 = st.getReg AbiReg.t4 := fun hnt =>
            (hoth4 AbiReg.t4 (by decide) (by decide)).trans
              ((hoth3 AbiReg.t4 (by decide)).trans
                ((hoth2 AbiReg.t4 (by decide) (by decide)).trans (ht4_1 hnt)))
          have htailRun : ∀ (hT : ctail = [Asm.add AbiReg.t1 AbiReg.t1 pI.2, Asm.lbu rd AbiReg.t1 0#12]),
              ∃ k st', RV64.run env.rom k st = .cont st' ∧
                st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (pI.1 ++ clen ++ cbr ++ cbase ++ ctail))) ∧
                st'.getReg rd = ((lm.arr8 a)[vi.toNat]'hbound).toUInt64.toBitVec ∧
                PreservedFrameRegs fl (· = rd) st st' ∧
                MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem ∧
                (exprNoT4 (.ld8 a i) = true → st'.getReg AbiReg.t4 = st.getReg AbiReg.t4) := by
            intro hT
            have htw_t : lkm.totalSize ctail = 2 := by
              rw [hT]; simp [Asm.add, Asm.lbu, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
            have hsAdd := step_item_instr_lm lkm env.hrom p4 ([Asm.lbu rd AbiReg.t1 0#12] ++ post)
              (.alu .add AbiReg.t1 AbiReg.t1 pI.2)
              (by rw [hT] at hlink; simpa only [p4, Asm.add, List.append_assoc, List.cons_append, List.nil_append] using hlink)
              (by rw [htw4]; rw [htw_all, htw_t] at h64; omega) st4 hpc4'
            let st5 := stepReg st4 AbiReg.t1 (st4.getReg AbiReg.t1 + st4.getReg pI.2) (st4.pc + 4#64)
            have hpres5 : PreservedFrameRegs fl (· = rd) st4 st5 :=
              PreservedFrameRegs.of_scratch1 AbiReg.t1 (by decide) (fun r hr => getReg_stepReg_ne st4 AbiReg.t1 r hr _ _)
            have htw5 : lkm.totalSize (p4 ++ [Asm.add AbiReg.t1 AbiReg.t1 pI.2]) = lkm.totalSize p4 + 1 := by
              rw [lkm.totalSize_append, Asm.add, lkm.totalSize_instr]
            have hpc5 : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p4 ++ [Asm.add AbiReg.t1 AbiReg.t1 pI.2])) := by
              change st4.pc + 4#64 = _; rw [pc_add_4_ofNat st4.pc hpc4', htw5]
            have ht1_5 : st5.getReg AbiReg.t1 = L.base8 a + BitVec.ofNat 64 vi.toNat := by
              have hri4 : st4.getReg pI.2 = vi.toBitVec :=
                (hoth4 pI.2 (idxReg_ne_temp hri (by decide)) (idxReg_ne_temp hri (by decide))).trans
                  ((hoth3 pI.2 ⟨idxReg_ne_temp hri (by decide), idxReg_ne_s1 hri⟩).trans hri2)
              change (stepReg st4 AbiReg.t1 _ _).getReg AbiReg.t1 = _
              rw [getReg_stepReg_eq _ _ (by decide), ht1', hri4]
              congr 1; rw [← UInt64.toBitVec_ofNat' vi.toNat, UInt64.ofNat_toNat]
            obtain ⟨hrun6, hpc6, hrd6, hoth6, hmem6⟩ :=
              step_lbu_off_r env (p4 ++ [Asm.add AbiReg.t1 AbiReg.t1 pI.2]) post rd AbiReg.t1 0#12 hrd.ne_zero
                (by rw [hT] at hlink; simpa only [p4, Asm.lbu, Asm.add, List.append_assoc, List.cons_append, List.nil_append] using hlink)
                (by rw [htw5, htw4]; rw [htw_all, htw_t] at h64; omega) st5 hpc5
            let st6 := stepReg st5 rd ((loadBytes st5.mem (st5.getReg AbiReg.t1 + sextImm12 0#12) 1).zeroExtend 64) (st5.pc + 4#64)
            have hpres6 : PreservedFrameRegs fl (· = rd) st5 st6 :=
              PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) hoth6
            have hm5 : st5.mem = st1.mem := by dsimp only [st5]; rw [mem_stepReg, hm4]
            refine ⟨k1 + (lkm.totalSize clen + (kBr + (lkm.totalSize cbase + (1 + 1)))), st6, ?_, ?_, ?_,
              (PreservedFrameRegs.of_a0 hpres1).trans (hpres2.trans (hpres3.trans (hpres4.trans (hpres5.trans hpres6)))),
              by rw [hmem6, hm5]; exact heq1,
              fun hnt => (hoth6 AbiReg.t4 (hrd.ne_temp (by decide)).symm).trans
                ((getReg_stepReg_ne st4 AbiReg.t1 AbiReg.t4 (by decide) _ _).trans (ht4_04 hnt))⟩
            · rw [run_add, hrun1]; dsimp only
              rw [run_add, hrun2]; dsimp only
              rw [run_add, hrun3]; dsimp only
              rw [run_add, hrun4]; dsimp only
              rw [run_add, run_one_cont _ _ st5 (by rw [hsAdd]; rfl)]; dsimp only
              exact hrun6
            · rw [hpc6, htw5, htw4, htw_all, htw_t]; congr 2; omega
            · rw [hrd6, hm5, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero, ht1_5, hbytesR vi.toNat hbound]
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.zeroExtend, BitVec.toNat_setWidth, UInt8.toNat_toBitVec, UInt64.toNat_toBitVec, UInt8.toNat_toUInt64]
              exact Nat.mod_eq_of_lt (Nat.lt_trans (UInt8.toNat_lt _) (by decide))
          cases hiC : i.constVal? with
          | some w =>
            have hiEq : i = .const w := expr_constVal_eq_some hiC
            have hviEq : vi = w := by rw [hiEq] at hvi; exact (Prod.mk.inj (Except.ok.inj hvi)).1.symm
            subst hviEq
            by_cases hlt : vi.toNat < 2048
            · have hT : ctail = [Asm.lbu rd AbiReg.t1 (BitVec.ofNat 12 vi.toNat)] := by simp only [ctail, hiC, hlt, ↓reduceIte]
              have htw_t : lkm.totalSize ctail = 1 := by rw [hT]; simp [Asm.lbu, lkm.totalSize_instr]
              obtain ⟨hrun5, hpc5, hrd5, hoth5, hmem5⟩ :=
                step_lbu_off_r env p4 post rd AbiReg.t1 (BitVec.ofNat 12 vi.toNat) hrd.ne_zero
                  (by rw [hT] at hlink; simpa only [p4, List.append_assoc] using hlink)
                  (by rw [htw4]; rw [htw_all, htw_t] at h64; omega) st4 hpc4'
              let st5 := stepReg st4 rd ((loadBytes st4.mem (st4.getReg AbiReg.t1 + sextImm12 (BitVec.ofNat 12 vi.toNat)) 1).zeroExtend 64) (st4.pc + 4#64)
              have hpres5 : PreservedFrameRegs fl (· = rd) st4 st5 :=
                PreservedFrameRegs.of_target1 rd hrd (fun _ => rfl) hoth5
              refine ⟨k1 + (lkm.totalSize clen + (kBr + (lkm.totalSize cbase + 1))), st5, ?_, ?_, ?_,
                (PreservedFrameRegs.of_a0 hpres1).trans (hpres2.trans (hpres3.trans (hpres4.trans hpres5))),
                by rw [hmem5, hm4]; exact heq1,
                fun hnt => (hoth5 AbiReg.t4 (hrd.ne_temp (by decide)).symm).trans (ht4_04 hnt)⟩
              · rw [run_add, hrun1]; dsimp only
                rw [run_add, hrun2]; dsimp only
                rw [run_add, hrun3]; dsimp only
                rw [run_add, hrun4]; dsimp only
                exact hrun5
              · rw [hpc5, htw4, htw_all, htw_t]; congr 2; omega
              · rw [hrd5, hm4, ht1', sextImm12_ofNat_lt vi.toNat hlt, hbytesR vi.toNat hbound]
                apply BitVec.eq_of_toNat_eq
                rw [BitVec.zeroExtend, BitVec.toNat_setWidth, UInt8.toNat_toBitVec, UInt64.toNat_toBitVec, UInt8.toNat_toUInt64]
                exact Nat.mod_eq_of_lt (Nat.lt_trans (UInt8.toNat_lt _) (by decide))
            · exact htailRun (by simp only [ctail, hiC, hlt, ↓reduceIte])
          | none => exact htailRun (by simp only [ctail, hiC])
        · have hev : _root_.L.evalE (.ld8 a i) ⟨lm, loc⟩ = .error .oob := by
            change (_root_.L.evalE i >>= _root_.L.ld8 a) ⟨lm, loc⟩ = _
            simp only [Bind.bind, StateT.bind, Except.bind, hvi, _root_.L.ld8, get, getThe, MonadStateOf.get, StateT.get]
            simp [hbound, Pure.pure, Except.pure, Function.comp_apply, throw, throwThe, MonadExceptOf.throw, StateT.lift]; rfl
          rw [hev]
          have hcondT : evalBranch .bgeu (st2.getReg pI.2) (st2.getReg AbiReg.t0) = true := by
            simp [evalBranch, hri2, ht0_2']
            rw [BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec, Nat.mod_eq_of_lt hlt64, decide_eq_false hbound]
          obtain ⟨kBr, st3, hrun3, hpc3', hoth3, _, hmem3⟩ :=
            prog_step_br_taken env (pre ++ pI.1 ++ clen) (cbase ++ ctail ++ post)
              .bgeu pI.2 AbiReg.t0 errLabel env.errTarget env.herrLbl ⟨idxReg_ne_temp hri (by decide), by decide⟩
              hlinkBr h64Br st2 hpc2' hcondT
          exact ⟨k1 + (lkm.totalSize clen + kBr), st3,
            by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
            hpc3', (PreservedFrameRegs.of_a0 hpres1).trans (hpres2.trans (PreservedFrameRegs.of_t6_s1 hoth3)),
            by rw [hmem3, hmem2]; exact heq1⟩
      · simp only [hvi] at riSim
        obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := riSim
        have hev : _root_.L.evalE (.ld8 a i) ⟨lm, loc⟩ = .error .oob := by
          dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hvi]
        rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
    | ld64 a i =>
      simp only [exprOkB, Bool.and_eq_true] at heOk
      simp only [usedTempsExpr] at hTmp
      let s := TieredArray.t0 a
      let pI := match exprReg? fl.alloc i with | some r => ([], r) | none => (compileETo env.tab fl tmp AbiReg.a0 i, AbiReg.a0)
      let cbody :=
        loadMemOff .ld AbiReg.t0 (gpBaseReg fl.useT5Gp (env.tab.len64 s)) AbiReg.t1 (gpAdjOff fl.useT5Gp (env.tab.len64 s)) ++
        [Asm.bgeu pI.2 AbiReg.t0 errLabel] ++
        loadMemOff .ld AbiReg.t1 (gpBaseReg fl.useT5Gp (env.tab.base64 s)) AbiReg.t2 (gpAdjOff fl.useT5Gp (env.tab.base64 s)) ++
        ld64Tail rd pI.2 AbiReg.t2 i
      have hdef : compileETo env.tab fl tmp rd (.ld64 a i) = pI.1 ++ cbody := by
        cases h : exprReg? fl.alloc i <;>
          simp [compileETo, s, pI, h, cbody, loadMemOffGp_eq_loadMemOff, List.append_assoc]
      rw [hdef] at hlink h64 ⊢
      have htw_all : lkm.totalSize (pI.1 ++ cbody) = lkm.totalSize pI.1 + lkm.totalSize cbody := lkm.totalSize_append _ _
      have riRes := reg_evalIdx_of_ih env L fl hfl lm loc i pre (cbody ++ post) tmp heOk.2 hTmp
        (fun p q t r st' hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' =>
          mkIH i (by simp at hsz; omega) (fun x hx => hVf x (by simpa [exprUsesVar] using hx))
            p q t r hr heOk.2 ht hl h6 st' hpc' hgp' ht5' hsp' hm' hf')
        (by simpa only [pI, List.append_assoc] using hlink)
        (by rw [htw_all] at h64; dsimp only [pI] at h64 ⊢; omega) st hpc hgp ht5 hsp hmemRel hframeOk
      rcases riRes with ⟨hri, riSim⟩
      rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
      · simp only [hvi] at riSim
        obtain ⟨k1, st1, hrun1, hpc1, hri1, hpres1, heq1, ht4_1⟩ := riSim
        have htw1 : lkm.totalSize (pre ++ pI.1) = lkm.totalSize pre + lkm.totalSize pI.1 := lkm.totalSize_append _ _
        have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.abi.gp.trans hgp
        have ht5_1 : T5GpOk L fl st1 := ht5.of_preserved hpres1
        have hmemRel1 := ProgMemRel.of_tempSpanR hlo hhi (by omega) heq1 hmemRel
        have rb := reg_ld64Tail_body_r env L fl lm loc s heOk.1 i vi hvi (pre ++ pI.1) post rd pI.2
          (gpBaseReg fl.useT5Gp (env.tab.len64 s)) (gpBaseReg fl.useT5Gp (env.tab.base64 s))
          AbiReg.t0 AbiReg.t1 AbiReg.t2 hrd hri (by decide) (by decide) (by decide) (by decide)
          (gpBaseReg_ne_temp _ _ (by decide)) (gpBaseReg_ne_temp _ _ (by decide))
          (gpBaseReg_ne_temp _ _ (by decide)) (gpBaseReg_ne_temp _ _ (by decide)) (gpBaseReg_ne_t6_s1 _ _)
          (gpAdjOff fl.useT5Gp (env.tab.len64 s)) (gpAdjOff fl.useT5Gp (env.tab.base64 s))
          st1 (by rw [htw1]; exact hpc1) (gpBaseReg_addr hgp1 ht5_1) (gpBaseReg_addr hgp1 ht5_1)
          hri1 hmemRel1 (by simpa only [cbody, List.append_assoc] using hlink)
          (by rw [htw1]; rw [htw_all] at h64; dsimp only [cbody] at h64; omega)
        by_cases hbound : vi.toNat < (lm.arr64 s).size
        · simp only [hbound, ↓reduceDIte] at rb
          obtain ⟨k2, st2, hrun2, hpc2, hrd2, hpres2, hmem2, ht4_2⟩ := rb
          have hev : _root_.L.evalE (.ld64 a i) ⟨lm, loc⟩ = .ok ((lm.arr64 s)[vi.toNat]'hbound, ⟨lm, loc⟩) := by
            change (_root_.L.evalE i >>= _root_.L.ld64 s) ⟨lm, loc⟩ = _
            simp only [Bind.bind, StateT.bind, Except.bind, hvi, _root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get]
            simp [s, hbound, Pure.pure, StateT.pure, Except.pure]
          rw [hev]
          exact ⟨k1 + k2, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
            by dsimp only [cbody] at htw_all; rw [hpc2, htw1, htw_all]; congr 2; omega, hrd2,
            (PreservedFrameRegs.of_a0 hpres1).trans hpres2, by rw [hmem2]; exact heq1,
            fun hnt => ht4_2.trans (ht4_1 hnt)⟩
        · simp only [hbound, ↓reduceDIte] at rb
          obtain ⟨k2, st2, hrun2, hpc2, hpres2, hmem2⟩ := rb
          have hev : _root_.L.evalE (.ld64 a i) ⟨lm, loc⟩ = .error .oob := by
            change (_root_.L.evalE i >>= _root_.L.ld64 s) ⟨lm, loc⟩ = _
            simp only [Bind.bind, StateT.bind, Except.bind, hvi, _root_.L.ld64, get, getThe, MonadStateOf.get, StateT.get]
            simp [s, hbound, Pure.pure, Except.pure, Function.comp_apply, throw, throwThe, MonadExceptOf.throw, StateT.lift]; rfl
          rw [hev]
          exact ⟨k1 + k2, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
            hpc2, (PreservedFrameRegs.of_a0 hpres1).trans hpres2, by rw [hmem2]; exact heq1⟩
      · simp only [hvi] at riSim
        obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := riSim
        have hev : _root_.L.evalE (.ld64 a i) ⟨lm, loc⟩ = .error .oob := by
          dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hvi]
        rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
    | ldc d i =>
      simp only [exprOkB, Bool.and_eq_true] at heOk
      simp only [usedTempsExpr] at hTmp
      let pI := match exprReg? fl.alloc i with | some r => ([], r) | none => (compileETo env.tab fl tmp AbiReg.a0 i, AbiReg.a0)
      let cli := li AbiReg.t0 (BitVec.ofNat 64 d.length)
      let cbr := [Asm.bgeu pI.2 AbiReg.t0 errLabel]
      let cadd := [Asm.add AbiReg.t1 AbiReg.gp pI.2]
      let clbu := loadMemOff .lbu rd AbiReg.t1 AbiReg.t2 (env.tab.romBase + (romIdx d env.tab.rom : Int))
      have hdef : compileETo env.tab fl tmp rd (.ldc d i) = pI.1 ++ cli ++ cbr ++ cadd ++ clbu := by
        cases h : exprReg? fl.alloc i <;> simp [compileETo, pI, h, cli, cbr, cadd, clbu, List.append_assoc]
      rw [hdef] at hlink h64 ⊢
      have htw_add : lkm.totalSize cadd = 1 := by simp [cadd, Asm.add, lkm.totalSize_instr]
      have htw_all : lkm.totalSize (pI.1 ++ cli ++ cbr ++ cadd ++ clbu) =
          lkm.totalSize pI.1 + lkm.totalSize cli + lkm.totalSize cbr + 1 + lkm.totalSize clbu := by
        simp only [lkm.totalSize_append, htw_add]
      have riRes := reg_evalIdx_of_ih env L fl hfl lm loc i pre (cli ++ cbr ++ cadd ++ clbu ++ post) tmp heOk.2 hTmp
        (fun p q t r s hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' =>
          mkIH i (by simp at hsz; omega) (fun x hx => hVf x (by simpa [exprUsesVar] using hx))
            p q t r hr heOk.2 ht hl h6 s hpc' hgp' ht5' hsp' hm' hf')
        (by simpa only [pI, List.append_assoc] using hlink)
        (by rw [htw_all] at h64; dsimp only [pI] at h64 ⊢; omega) st hpc hgp ht5 hsp hmemRel hframeOk
      rcases riRes with ⟨hri, riSim⟩
      rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
      · simp only [hvi] at riSim
        obtain ⟨k1, st1, hrun1, hpc1, hri1, hpres1, heq1, ht4_1⟩ := riSim
        have htw1 : lkm.totalSize (pre ++ pI.1) = lkm.totalSize pre + lkm.totalSize pI.1 := lkm.totalSize_append _ _
        have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.abi.gp.trans hgp
        have hmemRel1 := ProgMemRel.of_tempSpanR hlo hhi (by omega) heq1 hmemRel
        have ⟨hromBound, hromBytes⟩ := Tab.romSliceOk_spec heOk.1
        have hdlt64 : d.length < 2 ^ 64 := by
          have hrb16 : 16 ≤ env.tab.romBase.toNat := by simp [Tab.romBase]; omega
          have := L.tab_rom_bound; have := L.hTValid; omega
        obtain ⟨st2, hrun2, hoth2, ht0_2, hmem2, hpc2⟩ :=
          li_correct_lm lkm env.hrom (pre ++ pI.1) (cbr ++ cadd ++ clbu ++ post)
            AbiReg.t0 (by decide) (BitVec.ofNat 64 d.length)
            (by simpa only [List.append_assoc] using hlink)
            (by rw [htw1]; rw [htw_all] at h64; dsimp only [cli] at h64; omega) st1 (by rw [htw1]; exact hpc1)
        have hpres2 : PreservedFrameRegs fl (· = rd) st1 st2 :=
          PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hoth2
        have htw2 : lkm.totalSize (pre ++ pI.1 ++ cli) = lkm.totalSize pre + lkm.totalSize pI.1 + lkm.totalSize cli := by
          rw [lkm.totalSize_append, htw1]
        have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ pI.1 ++ cli)) := by rw [htw2, ← htw1]; exact hpc2
        have hri2 : st2.getReg pI.2 = vi.toBitVec := (hoth2 pI.2 (idxReg_ne_temp hri (by decide))).trans hri1
        have hlinkBr : lkm.linkSpec ((pre ++ pI.1 ++ cli) ++ [.br .bgeu pI.2 AbiReg.t0 errLabel] ++ (cadd ++ clbu ++ post)) =
            .ok (env.code, env.labels) := by
          simpa only [cbr, Asm.bgeu, List.append_assoc] using hlink
        have h64Br : 4 * (lkm.totalSize (pre ++ pI.1 ++ cli) + lkm.itemSize (.br .bgeu pI.2 AbiReg.t0 errLabel)) < 2 ^ 64 := by
          rw [htw2]; rw [htw_all] at h64
          have : lkm.itemSize (.br .bgeu pI.2 AbiReg.t0 errLabel) = lkm.totalSize cbr := by simp [cbr, Asm.bgeu, lkm.totalSize_singleton]
          omega
        by_cases hbound : vi.toNat < d.length
        · have hev : _root_.L.evalE (.ldc d i) ⟨lm, loc⟩ = .ok ((d[vi.toNat]'hbound).toUInt64, ⟨lm, loc⟩) := by
            change (_root_.L.evalE i >>= fun idx => if h : idx.toNat < d.length then pure (d[idx.toNat]'h).toUInt64 else throw .oob) ⟨lm, loc⟩ = _
            simp only [Bind.bind, StateT.bind, Except.bind, hvi, hbound, ↓reduceDIte, Pure.pure, StateT.pure, Except.pure]
          rw [hev]
          have hcondF : evalBranch .bgeu (st2.getReg pI.2) (st2.getReg AbiReg.t0) = false := by
            simp [evalBranch, hri2, ht0_2]
            rw [BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec, Nat.mod_eq_of_lt hdlt64, decide_eq_true hbound]
          obtain ⟨kBr, st3, hrun3, hpc3', hoth3, _, hmem3⟩ :=
            prog_step_br_fall env (pre ++ pI.1 ++ cli) (cadd ++ clbu ++ post)
              .bgeu pI.2 AbiReg.t0 errLabel env.errTarget env.herrLbl ⟨idxReg_ne_temp hri (by decide), by decide⟩
              hlinkBr h64Br st2 hpc2' hcondF
          have hpres3 : PreservedFrameRegs fl (· = rd) st2 st3 :=
            PreservedFrameRegs.of_t6_s1 hoth3
          let p3 := pre ++ pI.1 ++ cli ++ cbr
          have htw3 : lkm.totalSize p3 =
              lkm.totalSize pre + lkm.totalSize pI.1 + lkm.totalSize cli + lkm.totalSize cbr := by
            dsimp only [p3]; rw [lkm.totalSize_append, htw2]
          have hpc3 : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize p3) := by rw [hpc3', htw3, htw2]; rfl
          have hgp3 : st3.getReg AbiReg.gp = L.T := (hoth3 AbiReg.gp (by decide)).trans ((hoth2 AbiReg.gp (by decide)).trans hgp1)
          have hri3 : st3.getReg pI.2 = vi.toBitVec := (hoth3 pI.2 ⟨idxReg_ne_temp hri (by decide), idxReg_ne_s1 hri⟩).trans hri2
          have hsAdd := step_item_instr_lm lkm env.hrom p3 (clbu ++ post) (.alu .add AbiReg.t1 AbiReg.gp pI.2)
            (by simpa only [p3, cadd, Asm.add, List.append_assoc] using hlink)
            (by rw [htw3]; rw [htw_all] at h64; omega) st3 hpc3
          let st4 := stepReg st3 AbiReg.t1 (st3.getReg AbiReg.gp + st3.getReg pI.2) (st3.pc + 4#64)
          have hpres4 : PreservedFrameRegs fl (· = rd) st3 st4 :=
            PreservedFrameRegs.of_scratch1 AbiReg.t1 (by decide) (fun r hr => getReg_stepReg_ne st3 AbiReg.t1 r hr _ _)
          have htw4 : lkm.totalSize (p3 ++ cadd) = lkm.totalSize p3 + 1 := by rw [lkm.totalSize_append, htw_add]
          have hpc4 : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize (p3 ++ cadd)) := by
            change st3.pc + 4#64 = _; rw [pc_add_4_ofNat st3.pc hpc3, htw4]
          obtain ⟨st5, hrun5, hoth5, hrd5, hmem5, hpc5⟩ :=
            loadMemOff_lbu_correct_lm lkm env.hrom (p3 ++ cadd) post rd AbiReg.t1 AbiReg.t2
              hrd.ne_zero (by decide) (by decide) (env.tab.romBase + (romIdx d env.tab.rom : Int))
              (by simpa only [p3, List.append_assoc] using hlink)
              (by rw [htw4, htw3]; rw [htw_all] at h64; dsimp only [clbu] at h64; omega) st4 hpc4
          have hpres5 : PreservedFrameRegs fl (· = rd) st4 st5 :=
            PreservedFrameRegs.of_target_scratch rd AbiReg.t2 hrd (fun _ => rfl) (by decide) hoth5
          have hm4 : st4.mem = st1.mem := by dsimp only [st4]; rw [mem_stepReg, hmem3, hmem2]
          have haddr4 : st4.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.romBase + (romIdx d env.tab.rom : Int)) =
              L.T + BitVec.ofNat 64 (env.tab.romBase.toNat + (romIdx d env.tab.rom + vi.toNat)) := by
            have hrbNN : 0 ≤ env.tab.romBase := by simp [Tab.romBase]; omega
            have hoffEq : BitVec.ofInt 64 (env.tab.romBase + (romIdx d env.tab.rom : Int)) =
                BitVec.ofNat 64 (env.tab.romBase.toNat + romIdx d env.tab.rom) := by
              rw [show env.tab.romBase + (romIdx d env.tab.rom : Int) = ((env.tab.romBase.toNat + romIdx d env.tab.rom : Nat) : Int) by omega,
                  BitVec.ofInt_natCast]
            change (stepReg st3 AbiReg.t1 _ _).getReg AbiReg.t1 + _ = _
            rw [getReg_stepReg_eq _ _ (by decide), hgp3, hri3, hoffEq,
                show vi.toBitVec = BitVec.ofNat 64 vi.toNat from by rw [← UInt64.toBitVec_ofNat' vi.toNat, UInt64.ofNat_toNat],
                BitVec.add_assoc, ← BitVec.ofNat_add, show vi.toNat + (env.tab.romBase.toNat + romIdx d env.tab.rom) =
                  env.tab.romBase.toNat + (romIdx d env.tab.rom + vi.toNat) by omega]
          refine ⟨k1 + (lkm.totalSize cli + (kBr + (1 + lkm.totalSize clbu))), st5, ?_, ?_, ?_,
            (PreservedFrameRegs.of_a0 hpres1).trans (hpres2.trans (hpres3.trans (hpres4.trans hpres5))),
            by rw [hmem5, hm4]; exact heq1,
            fun hnt => (hoth5 AbiReg.t4 (hrd.ne_temp (by decide)).symm (by decide)).trans
              ((getReg_stepReg_ne st3 AbiReg.t1 AbiReg.t4 (by decide) _ _).trans
                ((hoth3 AbiReg.t4 (by decide)).trans ((hoth2 AbiReg.t4 (by decide)).trans (ht4_1 hnt))))⟩
          · rw [run_add, hrun1]; dsimp only
            rw [run_add, hrun2]; dsimp only
            rw [run_add, hrun3]; dsimp only
            rw [run_add, run_one_cont _ _ st4 (by rw [hsAdd]; rfl)]; dsimp only
            exact hrun5
          · rw [hpc5, htw4, htw3, htw_all]; dsimp only [clbu]; congr 2; omega
          · rw [hrd5, hm4, haddr4, loadBytes_one]
            have hromAt := hmemRel1.2.2.1 (romIdx d env.tab.rom + vi.toNat) (by omega)
            rw [hromAt]
            have hbEq := hromBytes vi.toNat hbound
            rw [List.getElem?_eq_getElem (by omega)] at hbEq
            have hdEq : env.tab.rom[romIdx d env.tab.rom + vi.toNat]'(by omega) = d[vi.toNat]'hbound := Option.some.inj hbEq
            rw [hdEq]
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.zeroExtend, BitVec.toNat_setWidth, UInt8.toNat_toBitVec, UInt64.toNat_toBitVec, UInt8.toNat_toUInt64]
            exact Nat.mod_eq_of_lt (Nat.lt_trans (UInt8.toNat_lt _) (by decide))
        · have hev : _root_.L.evalE (.ldc d i) ⟨lm, loc⟩ = .error .oob := by
            change (_root_.L.evalE i >>= fun idx => if h : idx.toNat < d.length then pure (d[idx.toNat]'h).toUInt64 else throw .oob) ⟨lm, loc⟩ = _
            simp only [Bind.bind, StateT.bind, Except.bind, hvi, hbound, ↓reduceDIte, Function.comp_apply, throw, throwThe, MonadExceptOf.throw, StateT.lift]
          rw [hev]
          have hcondT : evalBranch .bgeu (st2.getReg pI.2) (st2.getReg AbiReg.t0) = true := by
            simp [evalBranch, hri2, ht0_2]
            rw [BitVec.ult, BitVec.toNat_ofNat, UInt64.toNat_toBitVec, Nat.mod_eq_of_lt hdlt64, decide_eq_false hbound]
          obtain ⟨kBr, st3, hrun3, hpc3', hoth3, _, hmem3⟩ :=
            prog_step_br_taken env (pre ++ pI.1 ++ cli) (cadd ++ clbu ++ post)
              .bgeu pI.2 AbiReg.t0 errLabel env.errTarget env.herrLbl ⟨idxReg_ne_temp hri (by decide), by decide⟩
              hlinkBr h64Br st2 hpc2' hcondT
          exact ⟨k1 + (lkm.totalSize cli + kBr), st3,
            by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
            hpc3', (PreservedFrameRegs.of_a0 hpres1).trans (hpres2.trans (PreservedFrameRegs.of_t6_s1 hoth3)),
            by rw [hmem3, hmem2]; exact heq1⟩
      · simp only [hvi] at riSim
        obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := riSim
        have hev : _root_.L.evalE (.ldc d i) ⟨lm, loc⟩ = .error .oob := by
          dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hvi]
        rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
    | ld64t a t i =>
      exact reg_evalExpr_ld64t_sim env L fl hfl lm loc hspAlign hlo hhi a t i
        (mkIH t (by simp at hsz; omega) (fun x hx => hVf x (by simp [exprUsesVar, hx])))
        (mkIH i (by simp at hsz; omega) (fun x hx => hVf x (by simp [exprUsesVar, hx])))
        pre post tmp rd hrd heOk (fun x hx => hVf x (by simp [exprUsesVar, hx])) hTmp hlink h64 st hpc hgp ht5 hsp hmemRel hframeOk
    | len64t a t =>
      simp only [exprOkB, Bool.and_eq_true] at heOk
      simp only [usedTempsExpr] at hTmp
      cases htC : t.constVal? with
      | some w =>
        have hteq : t = .const w := expr_constVal_eq_some htC
        have hvt : _root_.L.evalE t ⟨lm, loc⟩ = .ok (w, ⟨lm, loc⟩) := by rw [hteq]; rfl
        have hdef : compileETo env.tab fl tmp rd (.len64t a t) =
            loadMemOffGp fl.useT5Gp .ld rd AbiReg.t2 (env.tab.len64 (tierA a w)) := by
          simp [compileETo, htC]
        rw [hdef] at hlink h64 ⊢
        have hsOk : env.tab.wordPosOkB (tierA a w) = true := (tieredOk_len64_addr_T L.T a w heOk.1).1
        have hal : isAligned (L.T + BitVec.ofInt 64 (env.tab.len64 (tierA a w))) 8 = true := by
          rw [Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
        obtain ⟨st1, hrun1, hoth1, hrd1, hmem1, hpc1⟩ :=
          loadMemOffGp_ld_correct_lm lkm env.hrom pre post fl.useT5Gp rd AbiReg.t2
            hrd.ne_zero (by decide) (by decide) (fun _ => by decide) (env.tab.len64 (tierA a w)) L.T
            hlink h64 st hpc hgp ht5 hal
        have hev : _root_.L.evalE (.len64t a t) ⟨lm, loc⟩ = .ok (UInt64.ofNat (lm.arr64 (tierA a w)).size, ⟨lm, loc⟩) := by
          change (_root_.L.evalE t >>= fun u => do let s ← get; return UInt64.ofNat (s.mem.arr64 (tierA a u)).size) ⟨lm, loc⟩ = _
          simp [Bind.bind, StateT.bind, Except.bind, hvt, get, getThe, MonadStateOf.get, StateT.get, Pure.pure, StateT.pure, Except.pure]
        rw [hev]
        exact ⟨_, st1, hrun1, hpc1, by rw [hrd1, (hmemRel.2.1 (tierA a w) hsOk).2.2.1]; rfl,
          PreservedFrameRegs.of_target_scratch rd AbiReg.t2 hrd (fun _ => rfl) (by decide) hoth1,
          by rw [hmem1]; exact MemEqOutside.refl _ _,
          fun _ => hoth1 AbiReg.t4 (hrd.ne_temp (by decide)).symm (by decide)⟩
      | none =>
        let pT := match exprReg? fl.alloc t with | some r => ([], r) | none => (compileETo env.tab fl tmp AbiReg.a0 t, AbiReg.a0)
        let chdr := [Asm.andi AbiReg.t0 pT.2 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0]
        let cld := loadMemOff .ld rd AbiReg.t1 AbiReg.t2 (env.tab.len64 (TieredArray.t0 a))
        have hdef : compileETo env.tab fl tmp rd (.len64t a t) = pT.1 ++ chdr ++ cld := by
          cases h : exprReg? fl.alloc t <;> simp [compileETo, htC, pT, h, chdr, cld, List.append_assoc]
        rw [hdef] at hlink h64 ⊢
        have htw_hdr : lkm.totalSize chdr = 3 := by
          simp [chdr, Asm.andi, Asm.slli, Asm.add, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
        have htw_all : lkm.totalSize (pT.1 ++ chdr ++ cld) = lkm.totalSize pT.1 + 3 + lkm.totalSize cld := by
          simp only [lkm.totalSize_append, htw_hdr]
        have rtRes := reg_evalIdx_of_ih env L fl hfl lm loc t pre (chdr ++ cld ++ post) tmp heOk.2 hTmp
          (fun p q tm r st' hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' =>
            mkIH t (by simp at hsz; omega) (fun x hx => hVf x (by simpa [exprUsesVar] using hx))
              p q tm r hr heOk.2 ht hl h6 st' hpc' hgp' ht5' hsp' hm' hf')
          (by simpa only [pT, List.append_assoc] using hlink)
          (by rw [htw_all] at h64; dsimp only [pT] at h64 ⊢; omega) st hpc hgp ht5 hsp hmemRel hframeOk
        rcases rtRes with ⟨_, rtSim⟩
        rcases _root_.L.evalE_pure t ⟨lm, loc⟩ with ⟨vt, hvt⟩ | hvt
        · simp only [hvt] at rtSim
          obtain ⟨k1, st1, hrun1, hpc1, hrt1, hpres1, heq1, ht4_1⟩ := rtSim
          have htw1 : lkm.totalSize (pre ++ pT.1) = lkm.totalSize pre + lkm.totalSize pT.1 := lkm.totalSize_append _ _
          have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.abi.gp.trans hgp
          have hmemRel1 := ProgMemRel.of_tempSpanR hlo hhi (by omega) heq1 hmemRel
          obtain ⟨st2, hrun2, hpc2, ht1_2, hmem2, hpres2, hoth2⟩ :=
            step_tierHdr_r env fl (pre ++ pT.1) (cld ++ post) pT.2 vt
              (by simpa only [chdr, List.append_assoc] using hlink)
              (by rw [htw1]; rw [htw_all] at h64; omega) st1 (by rw [htw1]; exact hpc1) hgp1 hrt1
          have htw2 : lkm.totalSize (pre ++ pT.1 ++ chdr) = lkm.totalSize pre + lkm.totalSize pT.1 + 3 := by
            rw [lkm.totalSize_append, htw1, htw_hdr]
          have hta := tieredOk_len64_addr_T L.T a vt heOk.1
          have hal : isAligned (st2.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.len64 (TieredArray.t0 a))) 8 = true := by
            rw [ht1_2, hta.2.1, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
          obtain ⟨st3, hrun3, hoth3, hrd3, hmem3, hpc3⟩ :=
            loadMemOff_ld_correct_lm lkm env.hrom (pre ++ pT.1 ++ chdr) post rd AbiReg.t1 AbiReg.t2
              hrd.ne_zero (by decide) (by decide) (env.tab.len64 (TieredArray.t0 a))
              (by simpa only [cld, List.append_assoc] using hlink)
              (by rw [htw2]; rw [htw_all] at h64; dsimp only [cld] at h64; omega) st2 (by rw [htw2, ← htw1]; exact hpc2) hal
          have hev : _root_.L.evalE (.len64t a t) ⟨lm, loc⟩ = .ok (UInt64.ofNat (lm.arr64 (tierA a vt)).size, ⟨lm, loc⟩) := by
            change (_root_.L.evalE t >>= fun u => do let s ← get; return UInt64.ofNat (s.mem.arr64 (tierA a u)).size) ⟨lm, loc⟩ = _
            simp [Bind.bind, StateT.bind, Except.bind, hvt, get, getThe, MonadStateOf.get, StateT.get, Pure.pure, StateT.pure, Except.pure]
          rw [hev]
          exact ⟨k1 + (3 + lkm.totalSize cld), st3,
            by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
            by dsimp only [cld] at htw_all; rw [hpc3, htw2, htw_all]; congr 2; omega,
            by rw [hrd3, hmem2, ht1_2, hta.2.1, (hmemRel1.2.1 (tierA a vt) hta.1).2.2.1]; rfl,
            (PreservedFrameRegs.of_a0 (hpres1.trans hpres2)).trans
              (PreservedFrameRegs.of_target_scratch rd AbiReg.t2 hrd (fun _ => rfl) (by decide) hoth3),
            by rw [hmem3, hmem2]; exact heq1,
            fun hnt => (hoth3 AbiReg.t4 (hrd.ne_temp (by decide)).symm (by decide)).trans
              ((hoth2 AbiReg.t4 (by decide) (by decide)).trans (ht4_1 hnt))⟩
        · simp only [hvt] at rtSim
          obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := rtSim
          have hev : _root_.L.evalE (.len64t a t) ⟨lm, loc⟩ = .error .oob := by
            dsimp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind]; rw [hvt]
          rw [hev]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
    | ld8x8 src i =>
      exact reg_evalExpr_ld8x8_sim env L fl hfl lm loc hspAlign hlo hhi src i
        (mkIH i (by simp at hsz; omega) (fun x hx => hVf x (by simpa [exprUsesVar] using hx)))
        pre post tmp rd hrd heOk hTmp hlink h64 st hpc hgp ht5 hsp hmemRel hframeOk
    | ld32t a t i =>
      exact reg_evalExpr_ld32t_sim env L fl hfl lm loc hspAlign hlo hhi a t i
        (mkIH t (by simp at hsz; omega) (fun x hx => hVf x (by simp [exprUsesVar, hx])))
        (mkIH i (by simp at hsz; omega) (fun x hx => hVf x (by simp [exprUsesVar, hx])))
        pre post tmp rd hrd heOk (fun x hx => hVf x (by simp [exprUsesVar, hx])) hTmp hlink h64 st hpc hgp ht5 hsp hmemRel hframeOk
    | ld32h a t i hiFlag =>
      exact reg_emitLd32hFrom_sim env L fl hfl lm loc hspAlign hlo hhi a t i hiFlag
        (mkIH t (by simp at hsz; omega) (fun x hx => hVf x (by simp [exprUsesVar, hx])))
        (mkIH i (by simp at hsz; omega) (fun x hx => hVf x (by simp [exprUsesVar, hx])))
        pre post tmp rd hrd heOk (fun x hx => hVf x (by simp [exprUsesVar, hx])) hTmp hlink h64 st hpc hgp ht5 hsp hmemRel hframeOk

/-- Full forward simulation of `compileETo tab fl tmp rd e` for any valid target `rd`. -/
theorem reg_evalExpr_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (e : Expr) (pre post : List AsmItem) (tmp : Nat) (rd : Reg)
    (hrd : ValidTargetReg fl rd)
    (heOk : exprOkB env.tab fl.nlocals e = true)
    (hVf : ExprVarsInFrame fl e)
    (hTmp : tmp + usedTempsExpr e ≤ fl.usedTemps)
    (hlink : lkm.linkSpec (pre ++ compileETo env.tab fl tmp rd e ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd e)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    match _root_.L.evalE e ⟨lm, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp rd e))) ∧
        st'.getReg rd = v.toBitVec ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· = rd) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
  have r := reg_evalExpr_sim_noT4 env L fl hfl lm loc hspAlign hlo hhi e pre post tmp rd hrd heOk hVf hTmp hlink h64 st hpc hgp ht5 hsp hmemRel hframeOk
  cases hv : _root_.L.evalE e ⟨lm, loc⟩ with
  | ok _ => simp only [hv] at r; rcases r with ⟨k, st', h1, h2, h3, h4, h5, _⟩; exact ⟨k, st', h1, h2, h3, h4, h5⟩
  | error _ => simp only [hv] at r; exact r

/-! ## 5. Condition & Argument-List Simulation (`reg_evalCond_sim`, `reg_evalArgs_sim`) -/

theorem usedTempsCond_cmp_left (op : Cmp) (a b : Expr) :
    usedTempsExpr a ≤ usedTempsCond (.cmp op a b) := by
  dsimp only [usedTempsCond]
  cases hb : isSimpleExpr b
  · cases ha : isSimpleExpr a
    · cases hnt : exprNoT4 b
      · exact Nat.le_max_left _ _
      · exact Nat.le_refl _
    · rw [usedTempsExpr_of_isSimple ha]; exact Nat.zero_le _
  · exact Nat.le_refl _

theorem usedTempsCond_cmp_right (op : Cmp) (a b : Expr) :
    usedTempsExpr b ≤ usedTempsCond (.cmp op a b) := by
  dsimp only [usedTempsCond]
  cases hb : isSimpleExpr b
  · cases ha : isSimpleExpr a
    · cases hnt : exprNoT4 b
      · exact Nat.le_trans (Nat.le_add_left _ 1) (Nat.le_max_right _ _)
      · rw [usedTempsExpr_of_exprNoT4 hnt]; exact Nat.zero_le _
    · exact Nat.le_refl _
  · rw [usedTempsExpr_of_isSimple hb]; exact Nat.zero_le _

theorem reg_evalCond_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (c : Cond) (pre post : List AsmItem) (tmp : Nat) (pfx : String) (lblId : Nat)
    (want : Bool) (target : String) (tgt : Nat)
    (hcOk : condOkB env.tab fl.nlocals c = true)
    (hVf : CondVarsInFrame fl c) (hTmp : tmp + usedTempsCond c ≤ fl.usedTemps)
    (htgt : lookupLabel env.labels target = some tgt)
    (hlink : lkm.linkSpec (pre ++ (compileCR env.tab fl tmp pfx lblId c want target).1 ++ post) =
      .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (compileCR env.tab fl tmp pfx lblId c want target).1) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    match _root_.L.evalC c ⟨lm, loc⟩ with
    | .ok (b, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (if b == want then tgt else
          lkm.totalSize pre + lkm.totalSize (compileCR env.tab fl tmp pfx lblId c want target).1)) ∧
        PreservedFrameRegs fl (fun _ => False) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (fun _ => False) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
  have hf : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  induction c generalizing pre post tmp pfx lblId want target tgt st with
  | cmp op a b =>
    simp only [condOkB, Bool.and_eq_true] at hcOk
    have hTmpA : tmp + usedTempsExpr a ≤ fl.usedTemps :=
      Nat.le_trans (Nat.add_le_add_left (usedTempsCond_cmp_left op a b) tmp) hTmp
    have hTmpB : tmp + usedTempsExpr b ≤ fl.usedTemps :=
      Nat.le_trans (Nat.add_le_add_left (usedTempsCond_cmp_right op a b) tmp) hTmp
    cases hra : exprReg? fl.alloc a with
    | some ra =>
      obtain ⟨hraMem, _, va, hva, hgra⟩ := reg_exprReg_sim (lm := lm) hfl hframeOk hcOk.1 hra
      have hrat6 : ra ≠ AbiReg.t6 := exprReg_ne_scratch hraMem (by decide)
      cases hrb : exprReg? fl.alloc b with
      | some rb =>
        obtain ⟨hrbMem, _, vb, hvb, hgrb⟩ := reg_exprReg_sim (lm := lm) hfl hframeOk hcOk.2 hrb
        have hrbt6 : rb ≠ AbiReg.t6 := exprReg_ne_scratch hrbMem (by decide)
        have hcc : (compileCR env.tab fl tmp pfx lblId (.cmp op a b) want target).1 =
            [brCmp op want ra rb target] := by simp only [compileCR, hra, hrb]
        rw [hcc] at hlink h64 ⊢
        have htw_s : lkm.totalSize [brCmp op want ra rb target] = lkm.itemSize (brCmp op want ra rb target) :=
          lkm.totalSize_singleton _
        obtain ⟨kbr, st2, _, hrunBr, hpc2, hreg2, hmem2⟩ :=
          brCmp_step_reg_lm lkm env pre post op want ra rb hrat6 hrbt6 target tgt va vb st htgt
            hlink (by rw [← htw_s]; exact h64) hpc hgra hgrb
        have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .ok (op.eval va vb, ⟨lm, loc⟩) := by
          simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
        rw [heval]
        exact ⟨kbr, st2, hrunBr, by rw [hpc2, htw_s],
          PreservedFrameRegs.of_regEqExceptT6 hreg2, by rw [hmem2]; exact MemEqOutside.refl _ _⟩
      | none =>
        have hcc : (compileCR env.tab fl tmp pfx lblId (.cmp op a b) want target).1 =
            compileETo env.tab fl tmp AbiReg.a0 b ++ [brCmp op want ra AbiReg.a0 target] := by
          simp only [compileCR, hra, hrb]
        rw [hcc] at hlink h64 ⊢
        have htw_cc : lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 b ++ [brCmp op want ra AbiReg.a0 target]) =
            lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 b) + lkm.itemSize (brCmp op want ra AbiReg.a0 target) := by
          rw [lkm.totalSize_append, lkm.totalSize_singleton]
        have rb := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi b pre
          ([brCmp op want ra AbiReg.a0 target] ++ post) tmp AbiReg.a0 (Or.inl rfl) hcOk.2
          (fun x hx => hVf x (by simp [condUsesVar, hx])) hTmpB
          (by simpa only [List.append_assoc] using hlink)
          (by rw [htw_cc] at h64; omega) st hpc hgp ht5 hsp hmemRel hframeOk
        rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
        · simp only [hvb] at rb
          obtain ⟨kb, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := rb
          have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .ok (op.eval va vb, ⟨lm, loc⟩) := by
            simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
          rw [heval]
          have htw1 : lkm.totalSize (pre ++ compileETo env.tab fl tmp AbiReg.a0 b) =
              lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 b) := lkm.totalSize_append _ _
          obtain ⟨kbr, st2, _, hrunBr, hpc2, hreg2, hmem2⟩ :=
            brCmp_step_reg_lm lkm env (pre ++ compileETo env.tab fl tmp AbiReg.a0 b) post op want
              ra AbiReg.a0 hrat6 (by decide) target tgt va vb st1 htgt
              (by simpa only [List.append_assoc] using hlink)
              (by rw [htw1, Nat.add_assoc, ← htw_cc]; exact h64)
              (by rw [htw1]; exact hpc1)
              ((hpres1.getReg_of_exprReg hraMem).trans hgra) ha0_1
          exact ⟨kb + kbr, st2, by rw [run_add, hrun1]; exact hrunBr,
            by rw [hpc2, htw1, Nat.add_assoc, ← htw_cc],
            (PreservedFrameRegs.of_a0 hpres1).trans (PreservedFrameRegs.of_regEqExceptT6 hreg2),
            by rw [hmem2]; exact heq1⟩
        · simp only [hvb] at rb
          obtain ⟨kb, st1, hrun1, hpc1, hpres1, heq1⟩ := rb
          have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .error .oob := by
            simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb]
          rw [heval]; exact ⟨kb, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
    | none =>
      cases hrb : exprReg? fl.alloc b with
      | some rb =>
        obtain ⟨hrbMem, _, vb, hvb, hgrb⟩ := reg_exprReg_sim (lm := lm) hfl hframeOk hcOk.2 hrb
        have hrbt6 : rb ≠ AbiReg.t6 := exprReg_ne_scratch hrbMem (by decide)
        have hcc : (compileCR env.tab fl tmp pfx lblId (.cmp op a b) want target).1 =
            compileETo env.tab fl tmp AbiReg.a0 a ++ [brCmp op want AbiReg.a0 rb target] := by
          simp only [compileCR, hra, hrb]
        rw [hcc] at hlink h64 ⊢
        have htw_cc : lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a ++ [brCmp op want AbiReg.a0 rb target]) =
            lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a) + lkm.itemSize (brCmp op want AbiReg.a0 rb target) := by
          rw [lkm.totalSize_append, lkm.totalSize_singleton]
        have ra := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi a pre
          ([brCmp op want AbiReg.a0 rb target] ++ post) tmp AbiReg.a0 (Or.inl rfl) hcOk.1
          (fun x hx => hVf x (by simp [condUsesVar, hx])) hTmpA
          (by simpa only [List.append_assoc] using hlink)
          (by rw [htw_cc] at h64; omega) st hpc hgp ht5 hsp hmemRel hframeOk
        rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va, hva⟩ | hva
        · simp only [hva] at ra
          obtain ⟨ka, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ra
          have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .ok (op.eval va vb, ⟨lm, loc⟩) := by
            simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
          rw [heval]
          have htw1 : lkm.totalSize (pre ++ compileETo env.tab fl tmp AbiReg.a0 a) =
              lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a) := lkm.totalSize_append _ _
          obtain ⟨kbr, st2, _, hrunBr, hpc2, hreg2, hmem2⟩ :=
            brCmp_step_reg_lm lkm env (pre ++ compileETo env.tab fl tmp AbiReg.a0 a) post op want
              AbiReg.a0 rb (by decide) hrbt6 target tgt va vb st1 htgt
              (by simpa only [List.append_assoc] using hlink)
              (by rw [htw1, Nat.add_assoc, ← htw_cc]; exact h64)
              (by rw [htw1]; exact hpc1) ha0_1 ((hpres1.getReg_of_exprReg hrbMem).trans hgrb)
          exact ⟨ka + kbr, st2, by rw [run_add, hrun1]; exact hrunBr,
            by rw [hpc2, htw1, Nat.add_assoc, ← htw_cc],
            (PreservedFrameRegs.of_a0 hpres1).trans (PreservedFrameRegs.of_regEqExceptT6 hreg2),
            by rw [hmem2]; exact heq1⟩
        · simp only [hva] at ra
          obtain ⟨ka, st1, hrun1, hpc1, hpres1, heq1⟩ := ra
          have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .error .oob := by
            simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva]
          rw [heval]; exact ⟨ka, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
      | none =>
        cases hsb : emitSimpleExprR env.tab fl AbiReg.t0 AbiReg.t1 b with
        | some cb =>
          have hcc : (compileCR env.tab fl tmp pfx lblId (.cmp op a b) want target).1 =
              compileETo env.tab fl tmp AbiReg.a0 a ++ cb ++ [brCmp op want AbiReg.a0 AbiReg.t0 target] := by
            simp only [compileCR, hra, hrb, hsb, List.append_assoc]
          rw [hcc] at hlink h64 ⊢
          have htw_cc : lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a ++ cb ++ [brCmp op want AbiReg.a0 AbiReg.t0 target]) =
              lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a) + lkm.totalSize cb +
                lkm.itemSize (brCmp op want AbiReg.a0 AbiReg.t0 target) := by
            rw [lkm.totalSize_append, lkm.totalSize_append, lkm.totalSize_singleton]
          have ra := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi a pre
            (cb ++ [brCmp op want AbiReg.a0 AbiReg.t0 target] ++ post) tmp AbiReg.a0 (Or.inl rfl) hcOk.1
            (fun x hx => hVf x (by simp [condUsesVar, hx])) hTmpA
            (by simpa only [List.append_assoc] using hlink)
            (by rw [htw_cc] at h64; omega) st hpc hgp ht5 hsp hmemRel hframeOk
          rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va, hva⟩ | hva
          · simp only [hva] at ra
            obtain ⟨ka, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ra
            have htw1 : lkm.totalSize (pre ++ compileETo env.tab fl tmp AbiReg.a0 a) =
                lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a) := lkm.totalSize_append _ _
            obtain ⟨vb, kb, st2, hvb, hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
              reg_emitSimpleExprR_sim env L fl hfl lm loc hspAlign
                (pre ++ compileETo env.tab fl tmp AbiReg.a0 a) ([brCmp op want AbiReg.a0 AbiReg.t0 target] ++ post)
                AbiReg.t0 AbiReg.t1 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide) b cb hsb hcOk.2
                (fun x hx => hVf x (by simp [condUsesVar, hx]))
                (by simpa only [List.append_assoc] using hlink)
                (by rw [htw1]; rw [htw_cc] at h64; omega) st1 (by rw [htw1]; exact hpc1)
                (hpres1.abi.gp.trans hgp) (ht5.of_preserved hpres1) (hpres1.abi.sp.trans hsp)
                (ProgMemRel.of_tempSpanR hlo hhi (by omega) heq1 hmemRel)
                (ProgFrameOkR.of_preserved_temp hfl hf (by omega) hpres1 heq1 hframeOk)
            have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .ok (op.eval va vb, ⟨lm, loc⟩) := by
              simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
            rw [heval]
            have hpres2 : PreservedFrameRegs fl (fun _ => False) st1 st2 :=
              PreservedFrameRegs.of_scratch2 AbiReg.t0 AbiReg.t1 (by decide) (by decide) hoth2
            have htw2 : lkm.totalSize (pre ++ compileETo env.tab fl tmp AbiReg.a0 a ++ cb) =
                lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 a) + lkm.totalSize cb := by
              rw [lkm.totalSize_append, htw1]
            obtain ⟨kbr, st3, _, hrunBr, hpc3, hreg3, hmem3⟩ :=
              brCmp_step_reg_lm lkm env (pre ++ compileETo env.tab fl tmp AbiReg.a0 a ++ cb) post op want
                AbiReg.a0 AbiReg.t0 (by decide) (by decide) target tgt va vb st2 htgt
                (by simpa only [List.append_assoc] using hlink)
                (by rw [htw2]; rw [htw_cc] at h64; omega)
                (by rw [htw2, ← htw1]; exact hpc2)
                ((hoth2 AbiReg.a0 (by decide) (by decide)).trans ha0_1) ht0_2
            exact ⟨ka + (kb + kbr), st3,
              by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrunBr,
              by rw [hpc3, htw2, htw_cc]; cases (op.eval va vb == want) <;> simp [Nat.add_assoc],
              (PreservedFrameRegs.of_a0 hpres1).trans (hpres2.trans (PreservedFrameRegs.of_regEqExceptT6 hreg3)),
              by rw [hmem3, hmem2]; exact heq1⟩
          · simp only [hva] at ra
            obtain ⟨ka, st1, hrun1, hpc1, hpres1, heq1⟩ := ra
            have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .error .oob := by
              simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva]
            rw [heval]; exact ⟨ka, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
        | none =>
          cases hsa : emitSimpleExprR env.tab fl AbiReg.t0 AbiReg.t1 a with
          | some ca =>
            have hcc : (compileCR env.tab fl tmp pfx lblId (.cmp op a b) want target).1 =
                compileETo env.tab fl tmp AbiReg.a0 b ++ ca ++ [brCmp op want AbiReg.t0 AbiReg.a0 target] := by
              simp only [compileCR, hra, hrb, hsb, hsa, List.append_assoc]
            rw [hcc] at hlink h64 ⊢
            have htw_cc : lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 b ++ ca ++ [brCmp op want AbiReg.t0 AbiReg.a0 target]) =
                lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 b) + lkm.totalSize ca +
                  lkm.itemSize (brCmp op want AbiReg.t0 AbiReg.a0 target) := by
              rw [lkm.totalSize_append, lkm.totalSize_append, lkm.totalSize_singleton]
            have rb := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi b pre
              (ca ++ [brCmp op want AbiReg.t0 AbiReg.a0 target] ++ post) tmp AbiReg.a0 (Or.inl rfl) hcOk.2
              (fun x hx => hVf x (by simp [condUsesVar, hx])) hTmpB
              (by simpa only [List.append_assoc] using hlink)
              (by rw [htw_cc] at h64; omega) st hpc hgp ht5 hsp hmemRel hframeOk
            rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
            · simp only [hvb] at rb
              obtain ⟨kb, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := rb
              have htw1 : lkm.totalSize (pre ++ compileETo env.tab fl tmp AbiReg.a0 b) =
                  lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 b) := lkm.totalSize_append _ _
              obtain ⟨va, ka, st2, hva, hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
                reg_emitSimpleExprR_sim env L fl hfl lm loc hspAlign
                  (pre ++ compileETo env.tab fl tmp AbiReg.a0 b) ([brCmp op want AbiReg.t0 AbiReg.a0 target] ++ post)
                  AbiReg.t0 AbiReg.t1 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide) a ca hsa hcOk.1
                  (fun x hx => hVf x (by simp [condUsesVar, hx]))
                  (by simpa only [List.append_assoc] using hlink)
                  (by rw [htw1]; rw [htw_cc] at h64; omega) st1 (by rw [htw1]; exact hpc1)
                  (hpres1.abi.gp.trans hgp) (ht5.of_preserved hpres1) (hpres1.abi.sp.trans hsp)
                  (ProgMemRel.of_tempSpanR hlo hhi (by omega) heq1 hmemRel)
                  (ProgFrameOkR.of_preserved_temp hfl hf (by omega) hpres1 heq1 hframeOk)
              have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .ok (op.eval va vb, ⟨lm, loc⟩) := by
                simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
              rw [heval]
              have hpres2 : PreservedFrameRegs fl (fun _ => False) st1 st2 :=
                PreservedFrameRegs.of_scratch2 AbiReg.t0 AbiReg.t1 (by decide) (by decide) hoth2
              have htw2 : lkm.totalSize (pre ++ compileETo env.tab fl tmp AbiReg.a0 b ++ ca) =
                  lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 b) + lkm.totalSize ca := by
                rw [lkm.totalSize_append, htw1]
              obtain ⟨kbr, st3, _, hrunBr, hpc3, hreg3, hmem3⟩ :=
                brCmp_step_reg_lm lkm env (pre ++ compileETo env.tab fl tmp AbiReg.a0 b ++ ca) post op want
                  AbiReg.t0 AbiReg.a0 (by decide) (by decide) target tgt va vb st2 htgt
                  (by simpa only [List.append_assoc] using hlink)
                  (by rw [htw2]; rw [htw_cc] at h64; omega)
                  (by rw [htw2, ← htw1]; exact hpc2)
                  ht0_2 ((hoth2 AbiReg.a0 (by decide) (by decide)).trans ha0_1)
              exact ⟨kb + (ka + kbr), st3,
                by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrunBr,
                by rw [hpc3, htw2, htw_cc]; cases (op.eval va vb == want) <;> simp [Nat.add_assoc],
                (PreservedFrameRegs.of_a0 hpres1).trans (hpres2.trans (PreservedFrameRegs.of_regEqExceptT6 hreg3)),
                by rw [hmem3, hmem2]; exact heq1⟩
            · simp only [hvb] at rb
              obtain ⟨kb, st1, hrun1, hpc1, hpres1, heq1⟩ := rb
              have hPureA : ∃ va, _root_.L.evalE a ⟨lm, loc⟩ = .ok (va, ⟨lm, loc⟩) := by
                cases a with
                | const w => exact ⟨w, rfl⟩
                | var x => exact ⟨loc x, rfl⟩
                | len8 arr => exact ⟨UInt64.ofNat (lm.arr8 arr).size, rfl⟩
                | len64 arr => exact ⟨UInt64.ofNat (lm.arr64 (TieredArray.t0 arr)).size, rfl⟩
                | glob g => exact ⟨lm.glob g, rfl⟩
                | _ => simp [emitSimpleExprR] at hsa
              obtain ⟨va, hva⟩ := hPureA
              have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .error .oob := by
                simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb]
              rw [heval]; exact ⟨kb, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
          | none =>
            have hnsB : isSimpleExpr b = false := isSimpleExpr_false_of_emitSimple_none hsb
            have hnsA : isSimpleExpr a = false := isSimpleExpr_false_of_emitSimple_none hsa
            by_cases hntB : exprNoT4 b = true
            · let seq := compileETo env.tab fl tmp AbiReg.a0 a ++
                [Asm.mv AbiReg.t4 AbiReg.a0] ++
                compileETo env.tab fl tmp AbiReg.a0 b
              have hcc : (compileCR env.tab fl tmp pfx lblId (.cmp op a b) want target).1 =
                  seq ++ [brCmp op want AbiReg.t4 AbiReg.a0 target] := by
                simp only [compileCR, hra, hrb, hsb, hsa, hntB, ↓reduceIte, seq, List.append_assoc]
              rw [hcc] at hlink h64 ⊢
              have htw_cc : lkm.totalSize (seq ++ [brCmp op want AbiReg.t4 AbiReg.a0 target]) =
                  lkm.totalSize seq + lkm.itemSize (brCmp op want AbiReg.t4 AbiReg.a0 target) := by
                rw [lkm.totalSize_append, lkm.totalSize_singleton]
              have rseq := reg_evalTwoT4_of_ih env L fl hfl lm loc hlo hhi a b pre
                ([brCmp op want AbiReg.t4 AbiReg.a0 target] ++ post) tmp hntB hTmpA
                (fun p q tm r st' hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' =>
                  reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi a p q tm r hr hcOk.1 (fun x hx => hVf x (by simp [condUsesVar, hx])) ht hl h6 st' hpc' hgp' ht5' hsp' hm' hf')
                (fun p q tm r st' hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' =>
                  reg_evalExpr_sim_noT4 env L fl hfl lm loc hspAlign hlo hhi b p q tm r hr hcOk.2 (fun x hx => hVf x (by simp [condUsesVar, hx])) ht hl h6 st' hpc' hgp' ht5' hsp' hm' hf')
                (by simpa only [seq, List.append_assoc] using hlink)
                (by dsimp only [seq] at htw_cc; rw [htw_cc] at h64; omega) st hpc hgp ht5 hsp hmemRel hframeOk
              rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va, hva⟩ | hva
              · rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
                · simp only [hva, hvb] at rseq
                  obtain ⟨kseq, st1, hrun1, hpc1, ht4_1, ha0_1, hpres1, heq1⟩ := rseq
                  have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .ok (op.eval va vb, ⟨lm, loc⟩) := by
                    simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
                  rw [heval]
                  have htw_ps : lkm.totalSize (pre ++ seq) = lkm.totalSize pre + lkm.totalSize seq :=
                    lkm.totalSize_append _ _
                  obtain ⟨kbr, st2, _, hrunBr, hpc2, hreg2, hmem2⟩ :=
                    brCmp_step_reg_lm lkm env (pre ++ seq) post op want AbiReg.t4 AbiReg.a0 (by decide) (by decide)
                      target tgt va vb st1 htgt
                      (by simpa only [List.append_assoc] using hlink)
                      (by rw [htw_ps, Nat.add_assoc, ← htw_cc]; exact h64)
                      (by rw [htw_ps]; exact hpc1) ht4_1 ha0_1
                  exact ⟨kseq + kbr, st2, by rw [run_add, hrun1]; exact hrunBr,
                    by rw [hpc2, htw_ps, htw_cc, Nat.add_assoc],
                    (PreservedFrameRegs.of_a0 hpres1).trans (PreservedFrameRegs.of_regEqExceptT6 hreg2),
                    by rw [hmem2]; exact heq1⟩
                · simp only [hva, hvb] at rseq
                  obtain ⟨kseq, st1, hrun1, hpc1, hpres1, heq1⟩ := rseq
                  have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .error .oob := by
                    simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb]
                  rw [heval]; exact ⟨kseq, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
              · simp only [hva] at rseq
                obtain ⟨kseq, st1, hrun1, hpc1, hpres1, heq1⟩ := rseq
                have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .error .oob := by
                  simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva]
                rw [heval]; exact ⟨kseq, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
            · have hntBF : exprNoT4 b = false := Bool.eq_false_iff.mpr hntB
              simp only [usedTempsCond, hnsB, hnsA, hntBF, Bool.false_eq_true, ↓reduceIte] at hTmp
              let seq := compileETo env.tab fl tmp AbiReg.a0 a ++
                storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp) ++
                compileETo env.tab fl (tmp + 1) AbiReg.a0 b ++
                loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff tmp)
              have hcc : (compileCR env.tab fl tmp pfx lblId (.cmp op a b) want target).1 =
                  seq ++ [brCmp op want AbiReg.t0 AbiReg.a0 target] := by
                simp only [compileCR, hra, hrb, hsb, hsa, hntBF, Bool.false_eq_true, ↓reduceIte, seq, List.append_assoc]
              rw [hcc] at hlink h64 ⊢
              have htw_cc : lkm.totalSize (seq ++ [brCmp op want AbiReg.t0 AbiReg.a0 target]) =
                  lkm.totalSize seq + lkm.itemSize (brCmp op want AbiReg.t0 AbiReg.a0 target) := by
                rw [lkm.totalSize_append, lkm.totalSize_singleton]
              have rseq := reg_evalTwoSpill_of_ih env L fl hfl lm loc hspAlign hlo hhi a b pre
                ([brCmp op want AbiReg.t0 AbiReg.a0 target] ++ post) tmp (by omega) (by omega) (by omega)
                (fun p q tm r st' hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' =>
                  reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi a p q tm r hr hcOk.1 (fun x hx => hVf x (by simp [condUsesVar, hx])) ht hl h6 st' hpc' hgp' ht5' hsp' hm' hf')
                (fun p q tm r st' hr ht hl h6 hpc' hgp' ht5' hsp' hm' hf' =>
                  reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi b p q tm r hr hcOk.2 (fun x hx => hVf x (by simp [condUsesVar, hx])) ht hl h6 st' hpc' hgp' ht5' hsp' hm' hf')
                (by simpa only [seq, List.append_assoc] using hlink)
                (by dsimp only [seq] at htw_cc; rw [htw_cc] at h64; omega) st hpc hgp ht5 hsp hmemRel hframeOk
              rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va, hva⟩ | hva
              · rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb, hvb⟩ | hvb
                · simp only [hva, hvb] at rseq
                  obtain ⟨kseq, st1, hrun1, hpc1, ht0_1, ha0_1, hpres1, heq1⟩ := rseq
                  have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .ok (op.eval va vb, ⟨lm, loc⟩) := by
                    simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb, Pure.pure, StateT.pure, Except.pure]
                  rw [heval]
                  have htw_ps : lkm.totalSize (pre ++ seq) = lkm.totalSize pre + lkm.totalSize seq :=
                    lkm.totalSize_append _ _
                  obtain ⟨kbr, st2, _, hrunBr, hpc2, hreg2, hmem2⟩ :=
                    brCmp_step_reg_lm lkm env (pre ++ seq) post op want AbiReg.t0 AbiReg.a0 (by decide) (by decide)
                      target tgt va vb st1 htgt
                      (by simpa only [List.append_assoc] using hlink)
                      (by rw [htw_ps, Nat.add_assoc, ← htw_cc]; exact h64)
                      (by rw [htw_ps]; exact hpc1) ht0_1 ha0_1
                  exact ⟨kseq + kbr, st2, by rw [run_add, hrun1]; exact hrunBr,
                    by rw [hpc2, htw_ps, htw_cc, Nat.add_assoc],
                    (PreservedFrameRegs.of_a0 hpres1).trans (PreservedFrameRegs.of_regEqExceptT6 hreg2),
                    by rw [hmem2]; exact heq1⟩
                · simp only [hva, hvb] at rseq
                  obtain ⟨kseq, st1, hrun1, hpc1, hpres1, heq1⟩ := rseq
                  have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .error .oob := by
                    simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva, hvb]
                  rw [heval]; exact ⟨kseq, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
              · simp only [hva] at rseq
                obtain ⟨kseq, st1, hrun1, hpc1, hpres1, heq1⟩ := rseq
                have heval : _root_.L.evalC (.cmp op a b) ⟨lm, loc⟩ = .error .oob := by
                  simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hva]
                rw [heval]; exact ⟨kseq, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩
  | not p ihp =>
    simp only [condOkB] at hcOk
    dsimp only [usedTempsCond] at hTmp
    have rp := ihp pre post tmp pfx lblId (!want) target tgt hcOk
      (fun x hx => hVf x (by simp [condUsesVar, hx])) hTmp htgt hlink h64 st hpc hgp ht5 hsp hmemRel hframeOk
    rcases _root_.L.evalC_pure p ⟨lm, loc⟩ with ⟨bp, hbp⟩ | hbp
    · simp only [hbp] at rp
      have heval : _root_.L.evalC (.not p) ⟨lm, loc⟩ = .ok (!bp, ⟨lm, loc⟩) := by
        simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, Pure.pure, StateT.pure, Except.pure]
      rw [heval]; cases bp <;> cases want <;> exact rp
    · simp only [hbp] at rp
      have heval : _root_.L.evalC (.not p) ⟨lm, loc⟩ = .error .oob := by
        simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp]
      rw [heval]; exact rp
  | and p q ihp ihq =>
    simp only [condOkB, Bool.and_eq_true] at hcOk
    dsimp only [usedTempsCond] at hTmp
    have hVfP : CondVarsInFrame fl p := fun x hx => hVf x (by simp [condUsesVar, hx])
    have hVfQ : CondVarsInFrame fl q := fun x hx => hVf x (by simp [condUsesVar, hx])
    cases want
    · let cp := (compileCR env.tab fl tmp pfx lblId p false target).1
      let id1 := (compileCR env.tab fl tmp pfx lblId p false target).2
      let cq := (compileCR env.tab fl tmp pfx id1 q false target).1
      have hcp_def : (compileCR env.tab fl tmp pfx lblId (.and p q) false target).1 = cp ++ cq := rfl
      have htw_cc : lkm.totalSize (compileCR env.tab fl tmp pfx lblId (.and p q) false target).1 =
          lkm.totalSize cp + lkm.totalSize cq := by rw [hcp_def, lkm.totalSize_append]
      have rp := ihp pre (cq ++ post) tmp pfx lblId false target tgt hcOk.1 hVfP (by omega) htgt
        (by rw [show pre ++ cp ++ (cq ++ post) = pre ++ (compileCR env.tab fl tmp pfx lblId (.and p q) false target).1 ++ post from by
            rw [hcp_def]; simp only [List.append_assoc]]; exact hlink)
        (by rw [htw_cc] at h64; dsimp only [cp, cq] at h64 ⊢; omega) st hpc hgp ht5 hsp hmemRel hframeOk
      rcases _root_.L.evalC_pure p ⟨lm, loc⟩ with ⟨bp, hbp⟩ | hbp
      · cases bp
        · simp only [hbp] at rp
          have heval : _root_.L.evalC (.and p q) ⟨lm, loc⟩ = .ok (false, ⟨lm, loc⟩) := by
            simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, Pure.pure, StateT.pure, Except.pure]
          rw [heval]; exact rp
        · simp only [hbp] at rp
          obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := rp
          have htw1 : lkm.totalSize (pre ++ cp) = lkm.totalSize pre + lkm.totalSize cp := lkm.totalSize_append _ _
          have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ cp)) := by rw [htw1]; exact hpc1
          have rq := ihq (pre ++ cp) post tmp pfx id1 false target tgt hcOk.2 hVfQ (by omega) htgt
            (by rw [show (pre ++ cp) ++ cq ++ post = pre ++ (compileCR env.tab fl tmp pfx lblId (.and p q) false target).1 ++ post from by
                rw [hcp_def]; simp only [List.append_assoc]]; exact hlink)
            (by rw [htw1]; rw [htw_cc] at h64; dsimp only [cp, cq] at h64 ⊢; omega) st1 hpc1'
            (hpres1.abi.gp.trans hgp) (ht5.of_preserved hpres1) (hpres1.abi.sp.trans hsp)
            (ProgMemRel.of_tempSpanR hlo hhi (by omega) heq1 hmemRel)
            (ProgFrameOkR.of_preserved_temp hfl hf (by omega) (hpres1.mono (fun _ h => False.elim h)) heq1 hframeOk)
          rcases _root_.L.evalC_pure q ⟨lm, loc⟩ with ⟨bq, hbq⟩ | hbq
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : _root_.L.evalC (.and p q) ⟨lm, loc⟩ = .ok (bq, ⟨lm, loc⟩) := by
              simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            exact ⟨kp + kq, st2, by rw [run_add, hrun1]; exact hrun2,
              by rw [hpc2, htw1, htw_cc, Nat.add_assoc], hpres1.trans hpres2, heq1.trans heq2⟩
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : _root_.L.evalC (.and p q) ⟨lm, loc⟩ = .error .oob := by
              simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            exact ⟨kp + kq, st2, by rw [run_add, hrun1]; exact hrun2, hpc2, hpres1.trans hpres2, heq1.trans heq2⟩
      · simp only [hbp] at rp
        have heval : _root_.L.evalC (.and p q) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp]
        rw [heval]; exact rp
    · let skipLbl := s!"{pfx}_and_{lblId}"
      let cp := (compileCR env.tab fl tmp pfx (lblId + 1) p false skipLbl).1
      let id1 := (compileCR env.tab fl tmp pfx (lblId + 1) p false skipLbl).2
      let cq := (compileCR env.tab fl tmp pfx id1 q true target).1
      have hcp_def : (compileCR env.tab fl tmp pfx lblId (.and p q) true target).1 =
          cp ++ cq ++ [Asm.lbl skipLbl] := rfl
      have htw_cc : lkm.totalSize (compileCR env.tab fl tmp pfx lblId (.and p q) true target).1 =
          lkm.totalSize cp + lkm.totalSize cq := by
        rw [hcp_def, lkm.totalSize_append, lkm.totalSize_append, Asm.lbl, lkm.totalSize_label]; omega
      have hskip : lookupLabel env.labels skipLbl = some (lkm.totalSize (pre ++ cp ++ cq)) :=
        lookupLabel_of_lbl_lm lkm (pre ++ cp ++ cq) post skipLbl (by
          rw [show (pre ++ cp ++ cq) ++ [Asm.lbl skipLbl] ++ post =
              pre ++ (compileCR env.tab fl tmp pfx lblId (.and p q) true target).1 ++ post from by
              rw [hcp_def]; simp only [List.append_assoc]]; exact hlink)
      have rp := ihp pre (cq ++ [Asm.lbl skipLbl] ++ post) tmp pfx (lblId + 1) false skipLbl
        (lkm.totalSize (pre ++ cp ++ cq)) hcOk.1 hVfP (by omega) hskip
        (by rw [show pre ++ cp ++ (cq ++ [Asm.lbl skipLbl] ++ post) =
            pre ++ (compileCR env.tab fl tmp pfx lblId (.and p q) true target).1 ++ post from by
            rw [hcp_def]; simp only [List.append_assoc]]; exact hlink)
        (by rw [htw_cc] at h64; dsimp only [cp, cq] at h64 ⊢; omega) st hpc hgp ht5 hsp hmemRel hframeOk
      rcases _root_.L.evalC_pure p ⟨lm, loc⟩ with ⟨bp, hbp⟩ | hbp
      · cases bp
        · simp only [hbp] at rp
          obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := rp
          have heval : _root_.L.evalC (.and p q) ⟨lm, loc⟩ = .ok (false, ⟨lm, loc⟩) := by
            simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, Pure.pure, StateT.pure, Except.pure]
          rw [heval]
          exact ⟨kp, st1, hrun1, by rw [hpc1]; simp [htw_cc, lkm.totalSize_append], hpres1, heq1⟩
        · simp only [hbp] at rp
          obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := rp
          have htw1 : lkm.totalSize (pre ++ cp) = lkm.totalSize pre + lkm.totalSize cp := lkm.totalSize_append _ _
          have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ cp)) := by rw [htw1]; exact hpc1
          have rq := ihq (pre ++ cp) ([Asm.lbl skipLbl] ++ post) tmp pfx id1 true target tgt hcOk.2 hVfQ (by omega) htgt
            (by rw [show (pre ++ cp) ++ cq ++ ([Asm.lbl skipLbl] ++ post) =
                pre ++ (compileCR env.tab fl tmp pfx lblId (.and p q) true target).1 ++ post from by
                rw [hcp_def]; simp only [List.append_assoc]]; exact hlink)
            (by rw [htw1]; rw [htw_cc] at h64; dsimp only [cp, cq] at h64 ⊢; omega) st1 hpc1'
            (hpres1.abi.gp.trans hgp) (ht5.of_preserved hpres1) (hpres1.abi.sp.trans hsp)
            (ProgMemRel.of_tempSpanR hlo hhi (by omega) heq1 hmemRel)
            (ProgFrameOkR.of_preserved_temp hfl hf (by omega) (hpres1.mono (fun _ h => False.elim h)) heq1 hframeOk)
          rcases _root_.L.evalC_pure q ⟨lm, loc⟩ with ⟨bq, hbq⟩ | hbq
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : _root_.L.evalC (.and p q) ⟨lm, loc⟩ = .ok (bq, ⟨lm, loc⟩) := by
              simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            exact ⟨kp + kq, st2, by rw [run_add, hrun1]; exact hrun2,
              by rw [hpc2, htw1, htw_cc, Nat.add_assoc], hpres1.trans hpres2, heq1.trans heq2⟩
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : _root_.L.evalC (.and p q) ⟨lm, loc⟩ = .error .oob := by
              simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            exact ⟨kp + kq, st2, by rw [run_add, hrun1]; exact hrun2, hpc2, hpres1.trans hpres2, heq1.trans heq2⟩
      · simp only [hbp] at rp
        have heval : _root_.L.evalC (.and p q) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp]
        rw [heval]; exact rp
  | or p q ihp ihq =>
    simp only [condOkB, Bool.and_eq_true] at hcOk
    dsimp only [usedTempsCond] at hTmp
    have hVfP : CondVarsInFrame fl p := fun x hx => hVf x (by simp [condUsesVar, hx])
    have hVfQ : CondVarsInFrame fl q := fun x hx => hVf x (by simp [condUsesVar, hx])
    cases want
    · let skipLbl := s!"{pfx}_or_{lblId}"
      let cp := (compileCR env.tab fl tmp pfx (lblId + 1) p true skipLbl).1
      let id1 := (compileCR env.tab fl tmp pfx (lblId + 1) p true skipLbl).2
      let cq := (compileCR env.tab fl tmp pfx id1 q false target).1
      have hcp_def : (compileCR env.tab fl tmp pfx lblId (.or p q) false target).1 =
          cp ++ cq ++ [Asm.lbl skipLbl] := rfl
      have htw_cc : lkm.totalSize (compileCR env.tab fl tmp pfx lblId (.or p q) false target).1 =
          lkm.totalSize cp + lkm.totalSize cq := by
        rw [hcp_def, lkm.totalSize_append, lkm.totalSize_append, Asm.lbl, lkm.totalSize_label]; omega
      have hskip : lookupLabel env.labels skipLbl = some (lkm.totalSize (pre ++ cp ++ cq)) :=
        lookupLabel_of_lbl_lm lkm (pre ++ cp ++ cq) post skipLbl (by
          rw [show (pre ++ cp ++ cq) ++ [Asm.lbl skipLbl] ++ post =
              pre ++ (compileCR env.tab fl tmp pfx lblId (.or p q) false target).1 ++ post from by
              rw [hcp_def]; simp only [List.append_assoc]]; exact hlink)
      have rp := ihp pre (cq ++ [Asm.lbl skipLbl] ++ post) tmp pfx (lblId + 1) true skipLbl
        (lkm.totalSize (pre ++ cp ++ cq)) hcOk.1 hVfP (by omega) hskip
        (by rw [show pre ++ cp ++ (cq ++ [Asm.lbl skipLbl] ++ post) =
            pre ++ (compileCR env.tab fl tmp pfx lblId (.or p q) false target).1 ++ post from by
            rw [hcp_def]; simp only [List.append_assoc]]; exact hlink)
        (by rw [htw_cc] at h64; dsimp only [cp, cq] at h64 ⊢; omega) st hpc hgp ht5 hsp hmemRel hframeOk
      rcases _root_.L.evalC_pure p ⟨lm, loc⟩ with ⟨bp, hbp⟩ | hbp
      · cases bp
        · simp only [hbp] at rp
          obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := rp
          have htw1 : lkm.totalSize (pre ++ cp) = lkm.totalSize pre + lkm.totalSize cp := lkm.totalSize_append _ _
          have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ cp)) := by rw [htw1]; exact hpc1
          have rq := ihq (pre ++ cp) ([Asm.lbl skipLbl] ++ post) tmp pfx id1 false target tgt hcOk.2 hVfQ (by omega) htgt
            (by rw [show (pre ++ cp) ++ cq ++ ([Asm.lbl skipLbl] ++ post) =
                pre ++ (compileCR env.tab fl tmp pfx lblId (.or p q) false target).1 ++ post from by
                rw [hcp_def]; simp only [List.append_assoc]]; exact hlink)
            (by rw [htw1]; rw [htw_cc] at h64; dsimp only [cp, cq] at h64 ⊢; omega) st1 hpc1'
            (hpres1.abi.gp.trans hgp) (ht5.of_preserved hpres1) (hpres1.abi.sp.trans hsp)
            (ProgMemRel.of_tempSpanR hlo hhi (by omega) heq1 hmemRel)
            (ProgFrameOkR.of_preserved_temp hfl hf (by omega) (hpres1.mono (fun _ h => False.elim h)) heq1 hframeOk)
          rcases _root_.L.evalC_pure q ⟨lm, loc⟩ with ⟨bq, hbq⟩ | hbq
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : _root_.L.evalC (.or p q) ⟨lm, loc⟩ = .ok (bq, ⟨lm, loc⟩) := by
              simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            exact ⟨kp + kq, st2, by rw [run_add, hrun1]; exact hrun2,
              by rw [hpc2, htw1, htw_cc, Nat.add_assoc], hpres1.trans hpres2, heq1.trans heq2⟩
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : _root_.L.evalC (.or p q) ⟨lm, loc⟩ = .error .oob := by
              simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            exact ⟨kp + kq, st2, by rw [run_add, hrun1]; exact hrun2, hpc2, hpres1.trans hpres2, heq1.trans heq2⟩
        · simp only [hbp] at rp
          obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := rp
          have heval : _root_.L.evalC (.or p q) ⟨lm, loc⟩ = .ok (true, ⟨lm, loc⟩) := by
            simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, Pure.pure, StateT.pure, Except.pure]
          rw [heval]
          exact ⟨kp, st1, hrun1, by rw [hpc1]; simp [htw_cc, lkm.totalSize_append], hpres1, heq1⟩
      · simp only [hbp] at rp
        have heval : _root_.L.evalC (.or p q) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp]
        rw [heval]; exact rp
    · let cp := (compileCR env.tab fl tmp pfx lblId p true target).1
      let id1 := (compileCR env.tab fl tmp pfx lblId p true target).2
      let cq := (compileCR env.tab fl tmp pfx id1 q true target).1
      have hcp_def : (compileCR env.tab fl tmp pfx lblId (.or p q) true target).1 = cp ++ cq := rfl
      have htw_cc : lkm.totalSize (compileCR env.tab fl tmp pfx lblId (.or p q) true target).1 =
          lkm.totalSize cp + lkm.totalSize cq := by rw [hcp_def, lkm.totalSize_append]
      have rp := ihp pre (cq ++ post) tmp pfx lblId true target tgt hcOk.1 hVfP (by omega) htgt
        (by rw [show pre ++ cp ++ (cq ++ post) = pre ++ (compileCR env.tab fl tmp pfx lblId (.or p q) true target).1 ++ post from by
            rw [hcp_def]; simp only [List.append_assoc]]; exact hlink)
        (by rw [htw_cc] at h64; dsimp only [cp, cq] at h64 ⊢; omega) st hpc hgp ht5 hsp hmemRel hframeOk
      rcases _root_.L.evalC_pure p ⟨lm, loc⟩ with ⟨bp, hbp⟩ | hbp
      · cases bp
        · simp only [hbp] at rp
          obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := rp
          have htw1 : lkm.totalSize (pre ++ cp) = lkm.totalSize pre + lkm.totalSize cp := lkm.totalSize_append _ _
          have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ cp)) := by rw [htw1]; exact hpc1
          have rq := ihq (pre ++ cp) post tmp pfx id1 true target tgt hcOk.2 hVfQ (by omega) htgt
            (by rw [show (pre ++ cp) ++ cq ++ post = pre ++ (compileCR env.tab fl tmp pfx lblId (.or p q) true target).1 ++ post from by
                rw [hcp_def]; simp only [List.append_assoc]]; exact hlink)
            (by rw [htw1]; rw [htw_cc] at h64; dsimp only [cp, cq] at h64 ⊢; omega) st1 hpc1'
            (hpres1.abi.gp.trans hgp) (ht5.of_preserved hpres1) (hpres1.abi.sp.trans hsp)
            (ProgMemRel.of_tempSpanR hlo hhi (by omega) heq1 hmemRel)
            (ProgFrameOkR.of_preserved_temp hfl hf (by omega) (hpres1.mono (fun _ h => False.elim h)) heq1 hframeOk)
          rcases _root_.L.evalC_pure q ⟨lm, loc⟩ with ⟨bq, hbq⟩ | hbq
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : _root_.L.evalC (.or p q) ⟨lm, loc⟩ = .ok (bq, ⟨lm, loc⟩) := by
              simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            exact ⟨kp + kq, st2, by rw [run_add, hrun1]; exact hrun2,
              by rw [hpc2, htw1, htw_cc, Nat.add_assoc], hpres1.trans hpres2, heq1.trans heq2⟩
          · simp only [hbq] at rq
            obtain ⟨kq, st2, hrun2, hpc2, hpres2, heq2⟩ := rq
            have heval : _root_.L.evalC (.or p q) ⟨lm, loc⟩ = .error .oob := by
              simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, hbq]
            rw [heval]
            exact ⟨kp + kq, st2, by rw [run_add, hrun1]; exact hrun2, hpc2, hpres1.trans hpres2, heq1.trans heq2⟩
        · simp only [hbp] at rp
          have heval : _root_.L.evalC (.or p q) ⟨lm, loc⟩ = .ok (true, ⟨lm, loc⟩) := by
            simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp, Pure.pure, StateT.pure, Except.pure]
          rw [heval]; exact rp
      · simp only [hbp] at rp
        have heval : _root_.L.evalC (.or p q) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, hbp]
        rw [heval]; exact rp

theorem reg_evalArgs_sim_aux {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (es : List Expr) (pre post : List AsmItem) (tmp : Nat)
    (hesOk : es.all (exprOkB env.tab fl.nlocals) = true)
    (hVf : ExprsVarsInFrame fl es)
    (hTmp : ∀ e idx, (e, idx) ∈ es.zipIdx → tmp + idx + max 1 (usedTempsExpr e) ≤ fl.usedTemps)
    (hlink : lkm.linkSpec (pre ++ compileEvalExprsToTempsR env.tab fl tmp es ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (compileEvalExprsToTempsR env.tab fl tmp es)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    match _root_.L.evalArgs es ⟨lm, loc⟩ with
    | .ok (vs, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileEvalExprsToTempsR env.tab fl tmp es))) ∧
        vs.length = es.length ∧
        (∀ idx (hidx : idx < vs.length),
          readWord64 st'.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff (tmp + idx))) = vs[idx].toBitVec) ∧
        PreservedFrameRegs fl (fun _ => False) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (fun _ => False) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
  have hf : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  induction es generalizing pre post tmp st with
  | nil =>
    simp only [_root_.L.evalArgs, Pure.pure, StateT.pure, Except.pure, compileEvalExprsToTempsR,
      lkm.totalSize_nil, Nat.add_zero, List.length_nil]
    exact ⟨0, st, rfl, hpc, trivial, fun _ h => absurd h (Nat.not_lt_zero _),
      PreservedFrameRegs.refl _ _ _, MemEqOutside.refl _ _⟩
  | cons e es ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hesOk
    have hVfE : ExprVarsInFrame fl e := fun x hx => hVf x (by simp [hx])
    have hVfEs : ExprsVarsInFrame fl es := fun x hx => hVf x (by simp [hx])
    have hmem0 : (e, 0) ∈ (e :: es).zipIdx := by simp [List.zipIdx]
    have hTmpE := hTmp e 0 hmem0
    have hTmpRest : ∀ e' idx, (e', idx) ∈ es.zipIdx → (tmp + 1) + idx + max 1 (usedTempsExpr e') ≤ fl.usedTemps := by
      intro e' idx hm
      have hm' : (e', idx + 1) ∈ (e :: es).zipIdx := (mem_zipIdx_cons_succ e e' es idx).mpr hm
      have h := hTmp e' (idx + 1) hm'; omega
    let crest := compileEvalExprsToTempsR env.tab fl (tmp + 1) es
    cases hre : exprReg? fl.alloc e with
    | some r =>
      obtain ⟨hrMem, _, v, hv, hgr⟩ := reg_exprReg_sim (lm := lm) hfl hframeOk hesOk.1 hre
      have hrt0 : r ≠ AbiReg.t0 := exprReg_ne_scratch hrMem (by decide)
      let cs0 := storeMemOff .sd AbiReg.sp r AbiReg.t0 (fl.tempSlotOff tmp)
      have hdef : compileEvalExprsToTempsR env.tab fl tmp (e :: es) = cs0 ++ crest := by
        simp only [compileEvalExprsToTempsR, hre, cs0, crest]
      have htw_all : lkm.totalSize (compileEvalExprsToTempsR env.tab fl tmp (e :: es)) =
          lkm.totalSize cs0 + lkm.totalSize (compileEvalExprsToTempsR env.tab fl (tmp + 1) es) := by
        rw [hdef]; dsimp only [crest]; exact lkm.totalSize_append _ _
      have halS : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (fl.tempSlotOff tmp)) 8 = true := by
        rw [hsp, tempSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hspAlign _
      obtain ⟨st2, hrunS, hothS, hmemS, hpc2⟩ :=
        storeMemOff_sd_correct_lm lkm env.hrom pre (crest ++ post) AbiReg.sp r AbiReg.t0
          (by decide) (by decide) hrt0.symm (fl.tempSlotOff tmp)
          (by rw [show pre ++ cs0 ++ (crest ++ post) = pre ++ compileEvalExprsToTempsR env.tab fl tmp (e :: es) ++ post from by
              rw [hdef]; simp only [List.append_assoc]]; exact hlink)
          (by rw [htw_all] at h64; dsimp only [cs0] at h64 ⊢; omega) st hpc halS
      have hpresS : PreservedFrameRegs fl (fun _ => False) st st2 :=
        PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hothS
      have heq02 : MemEqOutside (tempSpanR fl sp tmp) st.mem st2.mem := by
        rw [hmemS, hsp, tempSlotOff_ofInt]
        exact MemEqOutside.writeWord64 st.mem _ _ fun k hk =>
          tempSlotSpanR_sub_tempSpanR fl sp hf (Nat.le_refl tmp) (by omega) _ ⟨k, hk, rfl⟩
      have htw2 : lkm.totalSize (pre ++ cs0) = lkm.totalSize pre + lkm.totalSize cs0 := lkm.totalSize_append _ _
      have rrest := ih (pre ++ cs0) post (tmp + 1) hesOk.2 hVfEs hTmpRest
        (by rw [show (pre ++ cs0) ++ crest ++ post = pre ++ compileEvalExprsToTempsR env.tab fl tmp (e :: es) ++ post from by
            rw [hdef]; simp only [List.append_assoc]]; exact hlink)
        (by rw [htw2]; rw [htw_all] at h64; omega) st2 (by rw [htw2]; exact hpc2)
        (hpresS.abi.gp.trans hgp) (ht5.of_preserved hpresS) (hpresS.abi.sp.trans hsp)
        (ProgMemRel.of_tempSpanR hlo hhi (by omega) heq02 hmemRel)
        (ProgFrameOkR.of_preserved_temp hfl hf (by omega) (hpresS.mono (fun _ h => False.elim h)) heq02 hframeOk)
      rcases _root_.L.evalArgs_pure es ⟨lm, loc⟩ with ⟨vs, hvs⟩ | hvs
      · simp only [hvs] at rrest
        obtain ⟨k2, st3, hrun2, hpc3, hlen, hslots, hpres2, heq2⟩ := rrest
        have heval : _root_.L.evalArgs (e :: es) ⟨lm, loc⟩ = .ok (v :: vs, ⟨lm, loc⟩) := by
          change (_root_.L.evalE e >>= fun v' => _root_.L.evalArgs es >>= fun vs' => pure (v' :: vs')) ⟨lm, loc⟩ = _
          dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hv]; dsimp only; rw [hvs]; rfl
        rw [heval]
        have heq2' : MemEqOutside (tempSpanR fl sp tmp) st2.mem st3.mem :=
          heq2.mono (tempSpanR_mono fl sp hf (Nat.le_succ tmp) (by omega))
        refine ⟨lkm.totalSize cs0 + k2, st3,
          by rw [run_add, hrunS]; dsimp only; exact hrun2,
          by rw [hpc3, htw2, htw_all]; congr 2; omega,
          by simp [hlen], ?_, hpresS.trans hpres2, heq02.trans heq2'⟩
        intro idx hidx
        cases idx with
        | zero =>
          simp only [Nat.add_zero, List.getElem_cons_zero]
          have h2 : readWord64 st2.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff tmp)) = v.toBitVec := by
            rw [hmemS, hsp, hgr]; exact readWord64_writeWord64_self st.mem _ _
          rw [← h2]
          apply MemEqOutside.readWord64_eq heq2
          intro k hk; rw [tempSlotOff_ofInt]
          exact (tempSpanR_disj_tempSlot fl sp hf (Nat.lt_succ_self tmp) (by omega)).symm _ ⟨k, hk, rfl⟩
        | succ idx' =>
          simp only [List.getElem_cons_succ]
          rw [show tmp + (idx' + 1) = (tmp + 1) + idx' by omega]
          exact hslots idx' (by simpa using hidx)
      · simp only [hvs] at rrest
        obtain ⟨k2, st3, hrun2, hpc3, hpres2, heq2⟩ := rrest
        have heval : _root_.L.evalArgs (e :: es) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.evalArgs, Bind.bind, StateT.bind, Except.bind, hv, hvs]
        rw [heval]
        have heq2' : MemEqOutside (tempSpanR fl sp tmp) st2.mem st3.mem :=
          heq2.mono (tempSpanR_mono fl sp hf (Nat.le_succ tmp) (by omega))
        exact ⟨lkm.totalSize cs0 + k2, st3,
          by rw [run_add, hrunS]; dsimp only; exact hrun2,
          hpc3, hpresS.trans hpres2, heq02.trans heq2'⟩
    | none =>
      let ce := compileETo env.tab fl tmp AbiReg.a0 e
      let cs := storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp)
      have hdef : compileEvalExprsToTempsR env.tab fl tmp (e :: es) = ce ++ cs ++ crest := by
        simp only [compileEvalExprsToTempsR, hre, ce, cs, crest, List.append_assoc]
      have htw_all : lkm.totalSize (compileEvalExprsToTempsR env.tab fl tmp (e :: es)) =
          lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 e) + lkm.totalSize cs +
            lkm.totalSize (compileEvalExprsToTempsR env.tab fl (tmp + 1) es) := by
        rw [hdef]; dsimp only [ce, crest]; simp only [lkm.totalSize_append]
      have re := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi e pre ((cs ++ crest) ++ post) tmp
        AbiReg.a0 (Or.inl rfl) hesOk.1 hVfE (by omega)
        (by rw [show pre ++ ce ++ ((cs ++ crest) ++ post) = pre ++ compileEvalExprsToTempsR env.tab fl tmp (e :: es) ++ post from by
            rw [hdef]; simp only [List.append_assoc]]; exact hlink)
        (by rw [htw_all] at h64; omega) st hpc hgp ht5 hsp hmemRel hframeOk
      rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨v, hv⟩ | hv
      · simp only [hv] at re
        obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := re
        have htw1 : lkm.totalSize (pre ++ ce) = lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 e) :=
          lkm.totalSize_append _ _
        have halS : isAligned (st1.getReg AbiReg.sp + BitVec.ofInt 64 (fl.tempSlotOff tmp)) 8 = true := by
          rw [hpres1.abi.sp.trans hsp, tempSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hspAlign _
        obtain ⟨st2, hrunS, hothS, hmemS, hpc2⟩ :=
          storeMemOff_sd_correct_lm lkm env.hrom (pre ++ ce) (crest ++ post) AbiReg.sp AbiReg.a0 AbiReg.t0
            (by decide) (by decide) (by decide) (fl.tempSlotOff tmp)
            (by rw [show (pre ++ ce) ++ cs ++ (crest ++ post) = pre ++ compileEvalExprsToTempsR env.tab fl tmp (e :: es) ++ post from by
                rw [hdef]; simp only [List.append_assoc]]; exact hlink)
            (by rw [htw1]; rw [htw_all] at h64; dsimp only [cs] at h64 ⊢; omega) st1 (by rw [htw1]; exact hpc1) halS
        have hpresS : PreservedFrameRegs fl (fun _ => False) st1 st2 :=
          PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hothS
        have heqS : MemEqOutside (tempSpanR fl sp tmp) st1.mem st2.mem := by
          rw [hmemS, hpres1.abi.sp.trans hsp, tempSlotOff_ofInt]
          exact MemEqOutside.writeWord64 st1.mem _ _ fun k hk =>
            tempSlotSpanR_sub_tempSpanR fl sp hf (Nat.le_refl tmp) (by omega) _ ⟨k, hk, rfl⟩
        have heq02 : MemEqOutside (tempSpanR fl sp tmp) st.mem st2.mem := heq1.trans heqS
        have hpres02 : PreservedFrameRegs fl (fun _ => False) st st2 :=
          (PreservedFrameRegs.of_a0 hpres1).trans hpresS
        have htw2 : lkm.totalSize (pre ++ ce ++ cs) =
            lkm.totalSize pre + lkm.totalSize (compileETo env.tab fl tmp AbiReg.a0 e) + lkm.totalSize cs := by
          rw [lkm.totalSize_append, htw1]
        have rrest := ih (pre ++ ce ++ cs) post (tmp + 1) hesOk.2 hVfEs hTmpRest
          (by rw [show (pre ++ ce ++ cs) ++ crest ++ post = pre ++ compileEvalExprsToTempsR env.tab fl tmp (e :: es) ++ post from by
              rw [hdef]; simp only [List.append_assoc]]; exact hlink)
          (by rw [htw2]; rw [htw_all] at h64; omega) st2 (by rw [htw2, ← htw1]; exact hpc2)
          (hpres02.abi.gp.trans hgp) (ht5.of_preserved hpres02) (hpres02.abi.sp.trans hsp)
          (ProgMemRel.of_tempSpanR hlo hhi (by omega) heq02 hmemRel)
          (ProgFrameOkR.of_preserved_temp hfl hf (by omega) (hpres02.mono (fun _ h => False.elim h)) heq02 hframeOk)
        rcases _root_.L.evalArgs_pure es ⟨lm, loc⟩ with ⟨vs, hvs⟩ | hvs
        · simp only [hvs] at rrest
          obtain ⟨k2, st3, hrun2, hpc3, hlen, hslots, hpres2, heq2⟩ := rrest
          have heval : _root_.L.evalArgs (e :: es) ⟨lm, loc⟩ = .ok (v :: vs, ⟨lm, loc⟩) := by
            change (_root_.L.evalE e >>= fun v' => _root_.L.evalArgs es >>= fun vs' => pure (v' :: vs')) ⟨lm, loc⟩ = _
            dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hv]; dsimp only; rw [hvs]; rfl
          rw [heval]
          have heq2' : MemEqOutside (tempSpanR fl sp tmp) st2.mem st3.mem :=
            heq2.mono (tempSpanR_mono fl sp hf (Nat.le_succ tmp) (by omega))
          refine ⟨k1 + (lkm.totalSize cs + k2), st3, ?_, ?_, by simp [hlen], ?_,
            hpres02.trans hpres2, heq02.trans heq2'⟩
          · rw [run_add, hrun1]; dsimp only; rw [run_add, hrunS]; dsimp only; exact hrun2
          · rw [hpc3, htw2, htw_all]; dsimp only [cs]; congr 2; omega
          · intro idx hidx
            cases idx with
            | zero =>
              simp only [Nat.add_zero, List.getElem_cons_zero]
              have h2 : readWord64 st2.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff tmp)) = v.toBitVec := by
                rw [hmemS, hpres1.abi.sp.trans hsp, ha0_1]; exact readWord64_writeWord64_self st1.mem _ _
              rw [← h2]
              apply MemEqOutside.readWord64_eq heq2
              intro k hk; rw [tempSlotOff_ofInt]
              exact (tempSpanR_disj_tempSlot fl sp hf (Nat.lt_succ_self tmp) (by omega)).symm _ ⟨k, hk, rfl⟩
            | succ idx' =>
              simp only [List.getElem_cons_succ]
              rw [show tmp + (idx' + 1) = (tmp + 1) + idx' by omega]
              exact hslots idx' (by simpa using hidx)
        · simp only [hvs] at rrest
          obtain ⟨k2, st3, hrun2, hpc3, hpres2, heq2⟩ := rrest
          have heval : _root_.L.evalArgs (e :: es) ⟨lm, loc⟩ = .error .oob := by
            simp [_root_.L.evalArgs, Bind.bind, StateT.bind, Except.bind, hv, hvs]
          rw [heval]
          have heq2' : MemEqOutside (tempSpanR fl sp tmp) st2.mem st3.mem :=
            heq2.mono (tempSpanR_mono fl sp hf (Nat.le_succ tmp) (by omega))
          exact ⟨k1 + (lkm.totalSize cs + k2), st3,
            by rw [run_add, hrun1]; dsimp only; rw [run_add, hrunS]; dsimp only; exact hrun2,
            hpc3, hpres02.trans hpres2, heq02.trans heq2'⟩
      · simp only [hv] at re
        obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := re
        have heval : _root_.L.evalArgs (e :: es) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.evalArgs, Bind.bind, StateT.bind, Except.bind, hv]
        rw [heval]; exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1, heq1⟩

theorem reg_evalArgs_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (es : List Expr) (pre post : List AsmItem) (tmp : Nat)
    (hesOk : es.all (exprOkB env.tab fl.nlocals) = true)
    (hVf : ExprsVarsInFrame fl es)
    (hTmp : tmp + usedTempsExprs es ≤ fl.usedTemps)
    (hlink : lkm.linkSpec (pre ++ compileEvalExprsToTempsR env.tab fl tmp es ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (compileEvalExprsToTempsR env.tab fl tmp es)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    match _root_.L.evalArgs es ⟨lm, loc⟩ with
    | .ok (vs, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileEvalExprsToTempsR env.tab fl tmp es))) ∧
        vs.length = es.length ∧
        (∀ idx (hidx : idx < vs.length),
          readWord64 st'.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff (tmp + idx))) = vs[idx].toBitVec) ∧
        PreservedFrameRegs fl (fun _ => False) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (fun _ => False) st st' ∧
        MemEqOutside (tempSpanR fl sp tmp) st.mem st'.mem := by
  apply reg_evalArgs_sim_aux env L fl hfl lm loc hspAlign hlo hhi es pre post tmp hesOk hVf
    _ hlink h64 st hpc hgp ht5 hsp hmemRel hframeOk
  intro e idx hmem
  have hm := foldl_max_mem (f := fun (p : Expr × Nat) => p.2 + max 1 (usedTempsExpr p.1))
    (xs := es.zipIdx) (init := 0) (x := (e, idx)) hmem
  dsimp only [usedTempsExprs] at hTmp
  dsimp only at hm
  omega

/-- Distinct indices `< maxRes` map to distinct argument/result registers `a0..a7`. -/
theorem resReg_ne_of_ne {i j : Nat} (hi : i < maxRes) (hj : j < maxRes) (hne : i ≠ j) :
    resReg i ≠ resReg j := by
  have hfin : ∀ (a b : Fin 8), a ≠ b → resReg a.val ≠ resReg b.val := by decide
  exact hfin ⟨i, hi⟩ ⟨j, hj⟩ (fun h => hne (congrArg Fin.val h))

/-- Argument/result registers `resReg _` are disjoint from `calleeSavedBank`. -/
theorem resReg_not_mem_calleeSaved (i : Nat) {r : Reg} (hr : r ∈ calleeSavedBank) :
    r ≠ resReg i := by
  have hlt : ∀ (a : Fin 8), ∀ q ∈ calleeSavedBank, q ≠ resReg a.val := by decide
  by_cases hi : i < 8
  · exact hlt ⟨i, hi⟩ r hr
  · have hdef : resReg i = AbiReg.a7 := by
      match i with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
      | _ + 7 => rfl
    rw [hdef]; exact hlt ⟨7, by decide⟩ r hr

/-- If `e` reads no variable allocated to a register in `forbidden`, changing locals only
    for variables allocated into `forbidden` leaves `_root_.L.evalE e` unchanged. -/
theorem evalE_eq_of_not_forbidden (alloc : RegAlloc) (forbidden : List Reg) (e : Expr)
    (h : exprReadsForbidden alloc forbidden e = false) (lm : _root_.L.Mem) (loc loc' : _root_.L.Locals)
    (hag : ∀ x, (match alloc.lookup x with | some r => r ∈ forbidden | none => false) = false → loc' x = loc x) :
    match _root_.L.evalE e ⟨lm, loc'⟩, _root_.L.evalE e ⟨lm, loc⟩ with
    | .ok (v1, _), .ok (v2, _) => v1 = v2
    | .error e1, .error e2 => e1 = e2
    | _, _ => False := by
  induction e with
  | const w => rfl
  | var x =>
    simp only [exprReadsForbidden] at h
    exact hag x (by cases hlk : alloc.lookup x <;> simp [hlk] at h ⊢; exact h)
  | len8 a | len64 a | glob a => rfl
  | ld8 a i ih =>
    simp only [exprReadsForbidden] at h
    have hi := ih h
    rcases _root_.L.evalE_pure i ⟨lm, loc'⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨v2, h2⟩ | h2 <;> simp only [h1, h2] at hi
    · subst hi
      dsimp only [_root_.L.evalE]
      simp only [Bind.bind, StateT.bind, Except.bind, h1, h2, _root_.L.ld8, get, getThe,
        MonadStateOf.get, StateT.get, Pure.pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw]
      by_cases hb : v1.toNat < (lm.arr8 a).size <;> simp only [hb, ↓reduceDIte] <;> rfl
    · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, h1, h2]
  | ld64 a i ih =>
    simp only [exprReadsForbidden] at h
    have hi := ih h
    rcases _root_.L.evalE_pure i ⟨lm, loc'⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨v2, h2⟩ | h2 <;> simp only [h1, h2] at hi
    · subst hi
      dsimp only [_root_.L.evalE]
      simp only [Bind.bind, StateT.bind, Except.bind, h1, h2, _root_.L.ld64, get, getThe,
        MonadStateOf.get, StateT.get, Pure.pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw]
      by_cases hb : v1.toNat < (lm.arr64 (.t0 a)).size <;> simp only [hb, ↓reduceDIte] <;> rfl
    · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, h1, h2]
  | ldc d i ih =>
    simp only [exprReadsForbidden] at h
    have hi := ih h
    rcases _root_.L.evalE_pure i ⟨lm, loc'⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨v2, h2⟩ | h2 <;> simp only [h1, h2] at hi
    · subst hi
      dsimp only [_root_.L.evalE]
      simp only [Bind.bind, StateT.bind, Except.bind, h1, h2, _root_.L.ldc,
        Pure.pure, throw, throwThe, MonadExceptOf.throw]
      by_cases hb : v1.toNat < d.length <;> simp only [hb, ↓reduceDIte] <;> rfl
    · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, h1, h2]
  | ld8x8 src i ih =>
    simp only [exprReadsForbidden] at h
    have hi := ih h
    rcases _root_.L.evalE_pure i ⟨lm, loc'⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨v2, h2⟩ | h2 <;> simp only [h1, h2] at hi
    · subst hi
      dsimp only [_root_.L.evalE]
      simp only [Bind.bind, StateT.bind, Except.bind, h1, h2, _root_.L.ld8x8, get, getThe,
        MonadStateOf.get, StateT.get, Pure.pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw]
      by_cases hb : v1.toNat + 8 ≤ (lm.src8 src).size <;> simp only [hb, ↓reduceIte] <;> rfl
    · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, h1, h2]
  | len64t a t ih =>
    simp only [exprReadsForbidden] at h
    have ht := ih h
    rcases _root_.L.evalE_pure t ⟨lm, loc'⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure t ⟨lm, loc⟩ with ⟨v2, h2⟩ | h2 <;> simp only [h1, h2] at ht
    · subst ht
      simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, h1, h2, get, getThe,
        MonadStateOf.get, StateT.get, Pure.pure, StateT.pure, Except.pure]
    · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, h1, h2]
  | bin op a b iha ihb =>
    simp only [exprReadsForbidden, Bool.or_eq_false_iff] at h
    have ha := iha h.1; have hb := ihb h.2
    rcases _root_.L.evalE_pure a ⟨lm, loc'⟩ with ⟨va1, ha1⟩ | ha1 <;>
    rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va2, ha2⟩ | ha2 <;> simp only [ha1, ha2] at ha
    · subst ha
      rcases _root_.L.evalE_pure b ⟨lm, loc'⟩ with ⟨vb1, hb1⟩ | hb1 <;>
      rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb2, hb2⟩ | hb2 <;> simp only [hb1, hb2] at hb
      · subst hb; simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ha1, ha2, hb1, hb2, Pure.pure, StateT.pure, Except.pure]
      · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ha1, ha2, hb1, hb2]
    · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ha1, ha2]
  | cmpw c a b iha ihb =>
    simp only [exprReadsForbidden, Bool.or_eq_false_iff] at h
    have ha := iha h.1; have hb := ihb h.2
    rcases _root_.L.evalE_pure a ⟨lm, loc'⟩ with ⟨va1, ha1⟩ | ha1 <;>
    rcases _root_.L.evalE_pure a ⟨lm, loc⟩ with ⟨va2, ha2⟩ | ha2 <;> simp only [ha1, ha2] at ha
    · subst ha
      rcases _root_.L.evalE_pure b ⟨lm, loc'⟩ with ⟨vb1, hb1⟩ | hb1 <;>
      rcases _root_.L.evalE_pure b ⟨lm, loc⟩ with ⟨vb2, hb2⟩ | hb2 <;> simp only [hb1, hb2] at hb
      · subst hb; simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ha1, ha2, hb1, hb2, Pure.pure, StateT.pure, Except.pure]
      · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ha1, ha2, hb1, hb2]
    · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ha1, ha2]
  | ld64t a t i iht ihi =>
    simp only [exprReadsForbidden, Bool.or_eq_false_iff] at h
    have ht := iht h.1; have hi := ihi h.2
    rcases _root_.L.evalE_pure t ⟨lm, loc'⟩ with ⟨vt1, ht1⟩ | ht1 <;>
    rcases _root_.L.evalE_pure t ⟨lm, loc⟩ with ⟨vt2, ht2⟩ | ht2 <;> simp only [ht1, ht2] at ht
    · subst ht
      rcases _root_.L.evalE_pure i ⟨lm, loc'⟩ with ⟨vi1, hi1⟩ | hi1 <;>
      rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi2, hi2⟩ | hi2 <;> simp only [hi1, hi2] at hi
      · subst hi
        simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2, _root_.L.ld64,
          get, getThe, MonadStateOf.get, StateT.get, Pure.pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw]
        by_cases hb : vi1.toNat < (lm.arr64 (tierA a vt1)).size <;> simp only [hb, ↓reduceDIte] <;> rfl
      · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2]
    · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2]
  | ld32t a t i iht ihi =>
    simp only [exprReadsForbidden, Bool.or_eq_false_iff] at h
    have ht := iht h.1; have hi := ihi h.2
    rcases _root_.L.evalE_pure t ⟨lm, loc'⟩ with ⟨vt1, ht1⟩ | ht1 <;>
    rcases _root_.L.evalE_pure t ⟨lm, loc⟩ with ⟨vt2, ht2⟩ | ht2 <;> simp only [ht1, ht2] at ht
    · subst ht
      rcases _root_.L.evalE_pure i ⟨lm, loc'⟩ with ⟨vi1, hi1⟩ | hi1 <;>
      rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi2, hi2⟩ | hi2 <;> simp only [hi1, hi2] at hi
      · subst hi
        simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2, _root_.L.ld32,
          get, getThe, MonadStateOf.get, StateT.get, Pure.pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw]
        by_cases hb : (vi1 / 2).toNat < (lm.arr64 (tierA a vt1)).size <;> simp only [hb, ↓reduceDIte] <;> rfl
      · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2]
    · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2]
  | ld32h a t i hiFlag iht ihi =>
    simp only [exprReadsForbidden, Bool.or_eq_false_iff] at h
    have ht := iht h.1; have hi := ihi h.2
    rcases _root_.L.evalE_pure t ⟨lm, loc'⟩ with ⟨vt1, ht1⟩ | ht1 <;>
    rcases _root_.L.evalE_pure t ⟨lm, loc⟩ with ⟨vt2, ht2⟩ | ht2 <;> simp only [ht1, ht2] at ht
    · subst ht
      rcases _root_.L.evalE_pure i ⟨lm, loc'⟩ with ⟨vi1, hi1⟩ | hi1 <;>
      rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi2, hi2⟩ | hi2 <;> simp only [hi1, hi2] at hi
      · subst hi
        simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2, _root_.L.ld64,
          get, getThe, MonadStateOf.get, StateT.get, Pure.pure, StateT.pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw]
        by_cases hb : vi1.toNat < (lm.arr64 (tierA a vt1)).size <;> simp only [hb, ↓reduceDIte] <;> rfl
      · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2]
    · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2]

/-- Direct reverse-order evaluation of `es` into `resReg (idx + i)` (`a0..a7`) with zero temp spills.
    Works for all non-leaf functions (`!fl.isLeaf = true`, where all locals live in `calleeSavedBank`)
    and for leaf functions whenever `revDirectSafeAux fl.alloc idx es = true`. -/
theorem reg_evalRevToRegs_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (es : List Expr) (idx : Nat) (pre post : List AsmItem)
    (hlen : idx + es.length ≤ maxRes)
    (hsafe : revDirectSafeAux fl.alloc idx es = true)
    (hesOk : es.all (exprOkB env.tab fl.nlocals) = true)
    (hVf : ExprsVarsInFrame fl es)
    (hTmp : maxUsedTempsExprs es ≤ fl.usedTemps)
    (hlink : lkm.linkSpec (pre ++ compileEvalRevToRegs env.tab fl idx es ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (compileEvalRevToRegs env.tab fl idx es)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    match _root_.L.evalArgs es ⟨lm, loc⟩ with
    | .ok (vs, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileEvalRevToRegs env.tab fl idx es))) ∧
        vs.length = es.length ∧
        (∀ i (hi : i < vs.length), st'.getReg (resReg (idx + i)) = vs[i].toBitVec) ∧
        PreservedFrameRegs fl (fun r => ∃ d, d < es.length ∧ r = resReg (idx + d)) st st' ∧
        MemEqOutside (tempSpanR fl sp 0) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (fun r => ∃ d, d < es.length ∧ r = resReg (idx + d)) st st' ∧
        MemEqOutside (tempSpanR fl sp 0) st.mem st'.mem := by
  have hf : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  induction es generalizing idx pre post st with
  | nil =>
    simp only [_root_.L.evalArgs, Pure.pure, StateT.pure, Except.pure, compileEvalRevToRegs,
      lkm.totalSize_nil, Nat.add_zero, List.length_nil]
    exact ⟨0, st, rfl, hpc, trivial, fun _ h => absurd h (Nat.not_lt_zero _),
      PreservedFrameRegs.refl _ _ _, MemEqOutside.refl _ _⟩
  | cons e rest ih =>
    simp only [List.length_cons] at hlen ⊢
    simp only [List.all_cons, Bool.and_eq_true] at hesOk
    have hVfE : ExprVarsInFrame fl e := fun x hx => hVf x (by simp [hx])
    have hVfRest : ExprsVarsInFrame fl rest := fun x hx => hVf x (by simp [hx])
    simp only [maxUsedTempsExprs] at hTmp
    let crest := compileEvalRevToRegs env.tab fl (idx + 1) rest
    let ce := compileETo env.tab fl 0 (resReg idx) e
    have hdef : compileEvalRevToRegs env.tab fl idx (e :: rest) = crest ++ ce := rfl
    have htw_all : lkm.totalSize (compileEvalRevToRegs env.tab fl idx (e :: rest)) =
        lkm.totalSize crest + lkm.totalSize ce := by rw [hdef]; exact lkm.totalSize_append _ _
    have hsafeRest : revDirectSafeAux fl.alloc (idx + 1) rest = true := by
      simp only [revDirectSafeAux, Bool.and_eq_true] at hsafe; exact hsafe.2
    have rRest := ih (idx + 1) pre (ce ++ post) (by omega) hsafeRest hesOk.2 hVfRest (by omega)
      (by rw [hdef] at hlink; simpa only [List.append_assoc] using hlink)
      (by rw [htw_all] at h64; dsimp only [crest] at h64 ⊢; omega) st hpc hgp ht5 hsp hmemRel hframeOk
    rcases _root_.L.evalArgs_pure rest ⟨lm, loc⟩ with ⟨vs, hvs⟩ | hvs
    · simp only [hvs] at rRest
      obtain ⟨k1, st1, hrun1, hpc1, hlen1, hregs1, hpres1, heq1⟩ := rRest
      have htw1 : lkm.totalSize (pre ++ crest) = lkm.totalSize pre + lkm.totalSize crest := lkm.totalSize_append _ _
      have hpres1_lift : PreservedFrameRegs fl (fun r => ∃ d, d < rest.length + 1 ∧ r = resReg (idx + d)) st st1 :=
        hpres1.mono (fun r ⟨d, hd, hr⟩ => ⟨d + 1, by omega, by rw [hr, show idx + 1 + d = idx + (d + 1) by omega]⟩)
      -- Construct `loc'` matching `st1` on registers written by `rest`, and `loc` elsewhere.
      let written := (List.range rest.length).map (fun d => resReg (idx + 1 + d))
      let loc' : _root_.L.Locals := fun x =>
        match fl.alloc.lookup x with
        | some r => if r ∈ written then UInt64.ofBitVec (st1.getReg r) else loc x
        | none => loc x
      have hframeOk1 : ProgFrameOkR L fl sp st1 loc' := by
        intro x hx
        have hfx := hframeOk x hx
        cases hlk : fl.alloc.lookup x with
        | some rx =>
          rw [hlk] at hfx; dsimp only [loc'] at hfx ⊢; rw [hlk]; dsimp only
          by_cases hw : rx ∈ written
          · simp only [hw, ↓reduceIte, UInt64.toBitVec_ofBitVec]
          · simp only [hw, ↓reduceIte]
            have hmem := (regAllocValid_lookup hfl.valid hlk).2.1
            have hnot : ¬(∃ d, d < rest.length ∧ rx = resReg (idx + 1 + d)) := by
              rintro ⟨d, hd, rfl⟩
              exact hw (List.mem_map.mpr ⟨d, List.mem_range.mpr hd, rfl⟩)
            rw [hpres1.regs rx hmem hnot, hfx]
        | none =>
          rw [hlk] at hfx; dsimp only [loc'] at hfx ⊢; rw [hlk]; dsimp only
          intro hmx
          rw [← hfx hmx, varSlotOff_ofInt]
          apply MemEqOutside.readWord64_eq heq1
          intro k hk
          exact (tempSpanR_disj_varSlot fl hfl sp hf 0 (Nat.zero_le _) hmx).symm _
            ⟨k, hk, by simp [varSlotSpanR, slotSpan, slotAddr]⟩
      have heEq : match _root_.L.evalE e ⟨lm, loc'⟩, _root_.L.evalE e ⟨lm, loc⟩ with
          | .ok (v1, _), .ok (v2, _) => v1 = v2
          | .error e1, .error e2 => e1 = e2
          | _, _ => False := by
        simp only [revDirectSafeAux, Bool.and_eq_true, Bool.not_eq_true'] at hsafe
        exact evalE_eq_of_not_forbidden fl.alloc written e hsafe.1 lm loc loc' fun x hx => by
          dsimp only [loc']
          cases hlk : fl.alloc.lookup x with
          | none => rfl
          | some rx =>
            simp only [hlk, decide_eq_false_iff_not] at hx
            simp [hx]
      have reSim := reg_evalExpr_sim env L fl hfl lm loc' hspAlign hlo hhi e (pre ++ crest) post 0
        (resReg idx) (resReg_validTargetReg fl idx) hesOk.1 hVfE (by omega)
        (by rw [hdef] at hlink; simpa only [List.append_assoc] using hlink)
        (by rw [htw1]; rw [htw_all] at h64; dsimp only [ce] at h64 ⊢; omega) st1 (by rw [htw1]; exact hpc1)
        (hpres1.abi.gp.trans hgp) (ht5.of_preserved hpres1) (hpres1.abi.sp.trans hsp)
        (ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) heq1 hmemRel) hframeOk1
      rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨v, hv⟩ | hv
      · rcases _root_.L.evalE_pure e ⟨lm, loc'⟩ with ⟨v', hv'⟩ | hv'
        · simp only [hv', hv] at heEq; subst heEq
          simp only [hv'] at reSim
          obtain ⟨k2, st2, hrun2, hpc2, hrd2, hpres2, heq2⟩ := reSim
          have heval : _root_.L.evalArgs (e :: rest) ⟨lm, loc⟩ = .ok (v' :: vs, ⟨lm, loc⟩) := by
            change (_root_.L.evalE e >>= fun v0 => _root_.L.evalArgs rest >>= fun vs0 => pure (v0 :: vs0)) ⟨lm, loc⟩ = _
            dsimp only [Bind.bind, StateT.bind, Except.bind]; rw [hv]; dsimp only; rw [hvs]; rfl
          rw [heval]
          have hpres2_lift : PreservedFrameRegs fl (fun r => ∃ d, d < rest.length + 1 ∧ r = resReg (idx + d)) st1 st2 :=
            hpres2.mono (fun r hr => ⟨0, Nat.zero_lt_succ _, by simpa using hr⟩)
          refine ⟨k1 + k2, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
            by rw [hpc2, htw1, htw_all]; dsimp only [ce]; congr 2; omega, by simp [hlen1], ?_,
            hpres1_lift.trans hpres2_lift, heq1.trans heq2⟩
          intro i hi
          cases i with
          | zero => simp only [Nat.add_zero, List.getElem_cons_zero]; exact hrd2
          | succ j =>
            simp only [List.getElem_cons_succ]
            have hj : j < vs.length := by simpa using hi
            have hregEq : resReg (idx + (j + 1)) = resReg (idx + 1 + j) := by congr 1; omega
            rw [hregEq]
            have hmemAllowed : resReg (idx + 1 + j) ∈ allowedRegs true :=
              resReg_mem_allowed_true (by omega)
            have hne : resReg (idx + 1 + j) ≠ resReg idx :=
              resReg_ne_of_ne (by omega) (by omega) (by omega)
            rw [hpres2.regs (resReg (idx + 1 + j)) hmemAllowed hne, hregs1 j hj]
        · simp only [hv', hv] at heEq
      · rcases _root_.L.evalE_pure e ⟨lm, loc'⟩ with ⟨v', hv'⟩ | hv'
        · simp only [hv', hv] at heEq
        · simp only [hv'] at reSim
          obtain ⟨k2, st2, hrun2, hpc2, hpres2, heq2⟩ := reSim
          have heval : _root_.L.evalArgs (e :: rest) ⟨lm, loc⟩ = .error .oob := by
            simp [_root_.L.evalArgs, Bind.bind, StateT.bind, Except.bind, hv]
          rw [heval]
          have hpres2_lift : PreservedFrameRegs fl (fun r => ∃ d, d < rest.length + 1 ∧ r = resReg (idx + d)) st1 st2 :=
            hpres2.mono (fun r hr => ⟨0, Nat.zero_lt_succ _, by simpa using hr⟩)
          exact ⟨k1 + k2, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
            hpc2, hpres1_lift.trans hpres2_lift, heq1.trans heq2⟩
    · simp only [hvs] at rRest
      obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := rRest
      have hpres1_lift : PreservedFrameRegs fl (fun r => ∃ d, d < rest.length + 1 ∧ r = resReg (idx + d)) st st1 :=
        hpres1.mono (fun r ⟨d, hd, hr⟩ => ⟨d + 1, by omega, by rw [hr, show idx + 1 + d = idx + (d + 1) by omega]⟩)
      have heval : _root_.L.evalArgs (e :: rest) ⟨lm, loc⟩ = .error .oob := by
        rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨v, hv⟩ | hv
        · simp [_root_.L.evalArgs, Bind.bind, StateT.bind, Except.bind, hv, hvs]
        · simp [_root_.L.evalArgs, Bind.bind, StateT.bind, Except.bind, hv]
      rw [heval]
      exact ⟨k1, st1, hrun1, hpc1, hpres1_lift, heq1⟩

end ConAgua.RISCV.Compiler
