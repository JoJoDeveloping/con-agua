import ConAgua.RISCV.Bridge.CheckerProgScanBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Single-Pass Fused Kernel Scan for `L.Checker.checkerProgI`

Runs the fused single-pass AST scan on `L.Checker.checkerProgI` (independent of
`CheckerProgScan`, so `checkerProg` and `checkerProgI` compile in parallel) and
combines slices with free-variable-parameterized lemmas.
-/

namespace ConAgua.RISCV.Bridge

section ParallelScansI
set_option maxRecDepth 65536
set_option maxHeartbeats 800000

kernel_eq_true checkerProgI_fused_part0 :
  sliceFusedIOk 0 512 L.Checker.checkerProgI

kernel_eq_true checkerProgI_fused_part1 :
  sliceFusedIOk 512 512 L.Checker.checkerProgI

kernel_eq_true checkerProgI_fused_part2 :
  sliceFusedIOk 1024 512 L.Checker.checkerProgI

kernel_eq_true checkerProgI_fused_part3 :
  sliceFusedIOk 1536 512 L.Checker.checkerProgI

kernel_eq_true checkerProgI_drop_2048_empty :
  (L.Checker.checkerProgI.drop 2048).isEmpty

end ParallelScansI

private theorem list_mem_take_drop_4_I {α : Type} (xs : List α) (x : α)
    (he : (xs.drop 2048).isEmpty = true) (hx : x ∈ xs) :
    x ∈ (xs.drop 0).take 512 ∨
    x ∈ (xs.drop 512).take 512 ∨
    x ∈ (xs.drop 1024).take 512 ∨
    x ∈ (xs.drop 1536).take 512 := by
  have hd : xs.drop 2048 = [] := List.isEmpty_iff.mp he
  have h1 : xs = xs.take 512 ++ xs.drop 512 := (List.take_append_drop 512 xs).symm
  have h2 : xs.drop 512 = (xs.drop 512).take 512 ++ xs.drop 1024 := by
    have := (List.take_append_drop 512 (xs.drop 512)).symm
    simpa [List.drop_drop, Nat.reduceAdd] using this
  have h3 : xs.drop 1024 = (xs.drop 1024).take 512 ++ xs.drop 1536 := by
    have := (List.take_append_drop 512 (xs.drop 1024)).symm
    simpa [List.drop_drop, Nat.reduceAdd] using this
  have h4 : xs.drop 1536 = (xs.drop 1536).take 512 := by
    have := (List.take_append_drop 512 (xs.drop 1536)).symm
    simpa [List.drop_drop, Nat.reduceAdd, hd] using this
  rw [h1, h2, h3, h4] at hx
  simp only [List.drop_zero]
  simp only [List.mem_append] at hx
  rcases hx with hx0 | hx1 | hx2 | hx3
  · exact Or.inl hx0
  · exact Or.inr (Or.inl hx1)
  · exact Or.inr (Or.inr (Or.inl hx2))
  · exact Or.inr (Or.inr (Or.inr hx3))

private theorem sliceFusedIGo_sound (xs : List (L.FnName × L.FunDecl))
    (h : sliceFusedIGo xs = true) :
    ∀ x ∈ xs, fnFusedIOk x = true := by
  induction xs with
  | nil => intro _ hm; cases hm
  | cons x xs ih =>
    dsimp only [sliceFusedIGo] at h
    cases hscan : stmtScanIL minRetTreeILit false x.2.body with
    | fail => rw [hscan] at h; cases h
    | ok mf mr =>
      rw [hscan] at h
      dsimp only at h
      cases hmr : ((minRetTreeILit.find (L.Compiler.nameCode x.1)).getD 1).ble
          (if mf then 1 else if mr == 0 then 100 else mr) with
      | false => simp only [hmr, Bool.false_eq_true, ↓reduceIte] at h
      | true =>
        simp only [hmr, ↓reduceIte] at h
        obtain ⟨hret, hbrk, hc0, hnst8, hmf, hmrEq⟩ := stmtScanIL_sound hscan
        have hminRet : fnMinRetL x.2 = (if mf then 1 else if mr == 0 then 100 else mr) := by
          dsimp only [fnMinRetL]
          rw [← hmf, ← hmrEq]
          cases mf <;> cases mr <;> rfl
        have hmrDec : decide ((minRetTreeILit.find (L.Compiler.nameCode x.1)).getD 1 ≤ fnMinRetL x.2) = true := by
          rw [hminRet]
          exact decide_eq_true (Nat.ble_eq.mp hmr)
        have hfn : fnFusedIOk x = true := by
          simp only [fnFusedIOk, Bool.and_eq_true]
          exact ⟨⟨⟨⟨hmrDec, hret⟩, hbrk⟩, hc0⟩, hnst8⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact hfn
        · exact ih h y hy'

private theorem combine_progI_4 (p : L.Prog)
    (h0 : sliceFusedIOk 0 512 p = true)
    (h1 : sliceFusedIOk 512 512 p = true)
    (h2 : sliceFusedIOk 1024 512 p = true)
    (h3 : sliceFusedIOk 1536 512 p = true)
    (he : (p.drop 2048).isEmpty = true) :
    ∀ x ∈ p, fnFusedIOk x = true := by
  have ha0 := sliceFusedIGo_sound ((p.drop 0).take 512) h0
  have ha1 := sliceFusedIGo_sound ((p.drop 512).take 512) h1
  have ha2 := sliceFusedIGo_sound ((p.drop 1024).take 512) h2
  have ha3 := sliceFusedIGo_sound ((p.drop 1536).take 512) h3
  intro x hx
  rcases list_mem_take_drop_4_I p x he hx with m0 | m1 | m2 | m3
  · exact ha0 x m0
  · exact ha1 x m1
  · exact ha2 x m2
  · exact ha3 x m3

private theorem checkerProgI_fused_all :
    ∀ x ∈ L.Checker.checkerProgI, fnFusedIOk x = true :=
  combine_progI_4 L.Checker.checkerProgI
    checkerProgI_fused_part0 checkerProgI_fused_part1 checkerProgI_fused_part2 checkerProgI_fused_part3
    checkerProgI_drop_2048_empty

private theorem fnFusedIOk_unpack {x : L.FnName × L.FunDecl} (h : fnFusedIOk x = true) :
    ((minRetTreeILit.find (L.Compiler.nameCode x.1)).getD 1 ≤ fnMinRetL x.2 ∧
     stmtRetOkNTree minRetTreeILit x.2.body = true) ∧
    (brkOkL false x.2.body = true ∧ const0OnlyL_S x.2.body = true ∧ noSt8L x.2.body = true) := by
  simp only [fnFusedIOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨⟨h.1.1.1.1, h.1.1.1.2⟩, ⟨h.1.1.2, h.1.2, h.2⟩⟩

theorem checkerProgI_ret_all :
    ∀ x ∈ L.Checker.checkerProgI,
      (minRetTreeILit.find (L.Compiler.nameCode x.1)).getD 1 ≤ fnMinRetL x.2 ∧
      stmtRetOkNTree minRetTreeILit x.2.body = true :=
  fun x hx => (fnFusedIOk_unpack (checkerProgI_fused_all x hx)).1

theorem checkerProgI_brk_const0_all :
    ∀ x ∈ L.Checker.checkerProgI,
      brkOkL false x.2.body = true ∧
      const0OnlyL_S x.2.body = true ∧
      noSt8L x.2.body = true :=
  fun x hx => (fnFusedIOk_unpack (checkerProgI_fused_all x hx)).2

end ConAgua.RISCV.Bridge
