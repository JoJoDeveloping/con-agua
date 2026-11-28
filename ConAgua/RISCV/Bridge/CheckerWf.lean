import ConAgua.RISCV.Compiler.ProgSimMain
import ConAgua.RISCV.Bridge.CheckerIso

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Checker Well-Formedness Proofs & Audit (`ConAgua.RISCV.Bridge.CheckerWf`)

Proves inside Lean's kernel (zero `sorry`, zero `native_decide`, axioms strictly
`[propext, Classical.choice, Quot.sound]`):
- `toRiscvTab_arrAtOkB_of_layOk`: any `L.Compiler.Tab` satisfying `layOk` satisfies
  `ConAgua.RISCV.Compiler.Tab.arrAtOkB`, yielding `checkerTabMini_arrAtOkB` in <1s without
  unfolding `checkerTab`.
- `checkerTabMini_nres_pos`: `1 ≤ checkerTabMini.nres`.
- `checkerProgMini_lookup_check` & `checkerProgIMini_lookup_check`: `"check"` is present
  with `nparams = 0`.
-/

namespace ConAgua.RISCV.Bridge

open ConAgua.RISCV.Compiler

private theorem getD_arrAtD (l : List L.TieredArray) {i : Nat} (hi : i < l.length) :
    L.Compiler.arrAtD l i = l[i] := by
  simp [L.Compiler.arrAtD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

private theorem tiered_eq_t0_of_hi_false :
    ∀ {s : L.TieredArray}, s.hi = false → s = L.TieredArray.t0 s.arr
  | ⟨_, false⟩, _ => rfl

/-- Any valid `L.Compiler.Tab` (`t.layOk`) satisfies `ConAgua.RISCV.Compiler.Tab.arrAtOkB`
    under `toRiscvTab`. -/
theorem toRiscvTab_arrAtOkB_of_layOk (t : L.Compiler.Tab) :
    (toRiscvTab t).arrAtOkB = true := by
  have hlay := t.layOk
  simp only [L.Compiler.layOkB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at hlay
  rcases hlay with ⟨⟨⟨⟨hlen, _hmAll⟩, hfind⟩, hbyteHi⟩, _hwHi⟩
  simp only [Tab.arrAtOkB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [toRiscvTab, hlen]
  · intro p hp
    dsimp [toRiscvTab] at hp
    have hpLen : p < t.arrAt.length := by omega
    have hget : (toRiscvTab t).arrAt[p]? = some t.arrAt[p] := by
      simp [toRiscvTab, List.getElem?_eq_getElem hpLen]
    rw [hget]
    have hhi0 : t.arrAt[p].hi = false := by
      have hb := hbyteHi p hp
      rw [getD_arrAtD t.arrAt hpLen] at hb
      simpa using hb
    have hfindp : t.lmap.find t.arrAt[p].code = some p := by
      have hf := hfind p (by omega)
      rw [getD_arrAtD t.arrAt hpLen] at hf
      exact hf
    have hcode : (L.TieredArray.t0 t.arrAt[p].arr).code = t.arrAt[p].code := by
      rw [← tiered_eq_t0_of_hi_false hhi0]
    have hfindR : (toRiscvTab t).lmap.find (L.TieredArray.t0 t.arrAt[p].arr).code = some p := by
      dsimp [toRiscvTab]
      rw [toRiscvNTree_find, hcode, hfindp]
    have hpos8 : (toRiscvTab t).pos8 t.arrAt[p].arr = p := by
      simp [Tab.pos8, hfindR]
    rw [Bool.and_eq_true]
    refine ⟨by simp [hhi0], ?_⟩
    change (toRiscvTab t).bytePosOkB t.arrAt[p].arr = true
    simp only [Tab.bytePosOkB, hpos8, hfindR, hget]
    rw [← tiered_eq_t0_of_hi_false hhi0]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_true]
    dsimp [toRiscvTab]
    exact hp
  · intro j hj
    dsimp [toRiscvTab] at hj
    let p := t.nb + j
    have hpLen : p < t.arrAt.length := by
      dsimp [p]; omega
    have hget : (toRiscvTab t).arrAt[p]? = some t.arrAt[p] := by
      simp [toRiscvTab, p, List.getElem?_eq_getElem hpLen]
    change (match (toRiscvTab t).arrAt[p]? with
      | some s => (toRiscvTab t).wordPosOkB s
      | none => false) = true
    rw [hget]
    have hfindp : t.lmap.find t.arrAt[p].code = some p := by
      have hf := hfind p (by dsimp [p]; omega)
      rw [getD_arrAtD t.arrAt hpLen] at hf
      exact hf
    have hfindR : (toRiscvTab t).lmap.find t.arrAt[p].code = some p := by
      dsimp [toRiscvTab]
      rw [toRiscvNTree_find, hfindp]
    have hpos64 : (toRiscvTab t).pos64 t.arrAt[p] = p := by
      simp [Tab.pos64, hfindR]
    simp only [Tab.wordPosOkB, hpos64, hfindR, hget, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq, and_true]
    dsimp [toRiscvTab, p]
    omega

theorem checkerTabMini_arrAtOkB : checkerTabMini.arrAtOkB = true :=
  toRiscvTab_arrAtOkB_of_layOk L.Checker.checkerTab

theorem checkerTabMini_nres_pos : 1 ≤ checkerTabMini.nres := by
  decide

theorem checkerProgMini_lookup_check :
    ∃ fd, checkerProgMini.lookup "check" = some fd ∧ fd.nparams = 0 := by
  have h : (checkerProgMini.lookup "check").map (·.nparams) = some 0 := by decide
  rw [Option.map_eq_some_iff] at h
  exact h

theorem checkerProgIMini_lookup_check :
    ∃ fd, checkerProgIMini.lookup "check" = some fd ∧ fd.nparams = 0 := by
  obtain ⟨fd, hfd, hn⟩ := checkerProgMini_lookup_check
  obtain ⟨fd', hfd', hn'⟩ := checkerProgIMini_lookup "check" fd hfd
  exact ⟨fd', hfd', hn'.trans hn⟩

/-- info: 'ConAgua.RISCV.Bridge.toRiscvTab_arrAtOkB_of_layOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms toRiscvTab_arrAtOkB_of_layOk

/-- info: 'ConAgua.RISCV.Bridge.checkerTabMini_arrAtOkB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerTabMini_arrAtOkB

/-- info: 'ConAgua.RISCV.Bridge.checkerTabMini_nres_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerTabMini_nres_pos

/-- info: 'ConAgua.RISCV.Bridge.checkerProgMini_lookup_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgMini_lookup_check

/-- info: 'ConAgua.RISCV.Bridge.checkerProgIMini_lookup_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgIMini_lookup_check

end ConAgua.RISCV.Bridge
