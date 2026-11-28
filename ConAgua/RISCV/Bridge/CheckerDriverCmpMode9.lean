import ConAgua.RISCV.Bridge.CheckerDriverCmpCommon

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ConAgua.RISCV.Bridge

open ConAgua.RISCV.RV64
open ConAgua.RISCV.Compiler
open ConAgua.RISCV.Linker
open _root_.L

def cmp9WriteSpan (regionBase : BitVec 64) (a : BitVec 64) : Prop :=
  (⟨regionBase, 16⟩ : MemSpan).contains a ∨
  (∃ g ∈ ([phiGVar, ploGVar, modeGVar] : List GVar),
    (⟨regionBase + BitVec.ofInt 64 (checkerTabMini.globOff g), 8⟩ : MemSpan).contains a)

private theorem cmp9WriteSpan_sub_slot0 (regionBase : BitVec 64)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64) :
    ∀ a, cmp9WriteSpan regionBase a → (⟨regionBase, abiSlot⟩ : MemSpan).contains a := by
  intro a ha
  rcases ha with h | ⟨g, hg, hgl⟩
  · exact memSpan_offset_sub_slot0 regionBase hReg64 (by simp [abiSlot] : 0 + 16 ≤ abiSlot) _
      (by simpa only [BitVec.add_zero] using h)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rw [globOff_bitvec] at hgl
    have hg12 : g.id < checkerTabMini.ng := by
      rcases hg with rfl | rfl | rfl <;> decide
    exact memSpan_offset_sub_slot0 regionBase hReg64 (globOff_bound hg12) _ hgl

private theorem cmp9WriteSpan_disj_tabOff (regionBase : BitVec 64)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    {lo sz : Nat} (hle : lo + sz ≤ abiSlot) (h16 : 16 ≤ lo)
    (hGlobNe : ∀ g ∈ ([phiGVar, ploGVar, modeGVar] : List GVar),
      lo + sz ≤ checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + g.id) ∨
      checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + g.id) + 8 ≤ lo) :
    ∀ k, k < sz → ¬ cmp9WriteSpan regionBase (regionBase + BitVec.ofNat 64 lo + BitVec.ofNat 64 k) := by
  intro k hk hw
  have hNeedEq := checkerTabMini_abiNeed_eq
  have h211 : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; simp [abiSlot]
  have hR : regionBase.toNat + abiSlot ≤ 2 ^ 64 := by omega
  rcases hw with h | ⟨g, hg, hgl⟩
  · exact memSpan_offset_disjoint_contains_false hR hle (by simp [abiSlot] : 0 + 16 ≤ abiSlot)
      (Or.inr h16) ⟨k, hk, rfl⟩ (by simpa only [BitVec.add_zero] using h)
  · rw [globOff_bitvec] at hgl
    have hg' := hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
    have hg12 : g.id < checkerTabMini.ng := by rcases hg' with rfl | rfl | rfl <;> decide
    exact memSpan_offset_disjoint_contains_false hR hle (globOff_bound hg12) (hGlobNe g hg) ⟨k, hk, rfl⟩ hgl

theorem cmp9WriteSpan_disj_callerSave (regionBase : BitVec 64)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64) :
    ∀ i, i < callerSaveRegs.length → ∀ k, k < 8 →
      ¬cmp9WriteSpan regionBase
        (regionBase + BitVec.ofInt 64 (checkerTabMini.saveBase 0) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 k) := by
  intro i hi k hk
  have hlen : callerSaveRegs.length = 16 := rfl
  have hnn := checkerTabMini_saveBase_nonneg
  have hcoe : ((checkerTabMini.saveBase 0).toNat : Int) = checkerTabMini.saveBase 0 :=
    Int.toNat_of_nonneg hnn
  have hleSlot : (checkerTabMini.saveBase 0).toNat + 8 * i + 8 ≤ abiSlot := by
    have := checkerTabMini_saveBase_le_abiSlot; omega
  have hgtArgs : checkerTabMini.args.toNat < (checkerTabMini.saveBase 0).toNat + 8 * i := by
    have := checkerTabMini_args_lt_saveBase; omega
  have hargsNat := checkerTabMini_args_eq
  have hresNat := checkerTabMini_resBase_eq
  have hcast : regionBase + BitVec.ofInt 64 (checkerTabMini.saveBase 0) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 k =
      regionBase + BitVec.ofNat 64 ((checkerTabMini.saveBase 0).toNat + 8 * i) + BitVec.ofNat 64 k := by
    rw [show BitVec.ofInt 64 (checkerTabMini.saveBase 0) = BitVec.ofNat 64 (checkerTabMini.saveBase 0).toNat from by
      rw [← BitVec.ofInt_natCast, hcoe],
      BitVec.add_assoc regionBase _ (BitVec.ofNat 64 (8 * i)), ← BitVec.ofNat_add]
  rw [hcast]
  apply cmp9WriteSpan_disj_tabOff regionBase hReg64 hleSlot (by omega)
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    have hg12 : g.id < 12 := by rcases hg with rfl | rfl | rfl <;> decide
    have := t_nxres; have := t_ng
    right; omega
  · exact hk

theorem cmpMode9Setup_sim (img : LinkedCmpImage) (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (ret6 : _root_.L.Word)
    (pre post : List AsmItem)
    (hlink : img.lkm.linkSpec (pre ++ cmpDrvMode9Setup checkerTabMini ++ post) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase)
    (hs6 : st.getReg AbiReg.s6 = (ret6 - 9223372036854775808).toBitVec) :
    ∃ k st',
      RV64.run (linkedCmpEnv img).rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize (pre ++ cmpDrvMode9Setup checkerTabMini)) ∧
      st'.getReg AbiReg.gp = regionBase ∧
      st'.getReg AbiReg.s0 = BitVec.ofNat 64 (abiFuel - 2) ∧
      st'.getReg AbiReg.sp = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) ∧
      st'.getReg AbiReg.s2 = st.getReg AbiReg.s2 ∧
      st'.getReg AbiReg.t0 = regionBase + BitVec.ofInt 64 checkerTabMini.args ∧
      st'.getReg AbiReg.t1 = 0#64 ∧
      ProgMemOutside (cmp9WriteSpan regionBase) st.mem st'.mem ∧
      readWord64 st'.mem regionBase = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) ∧
      readWord64 st'.mem (regionBase + 8#64) = regionBase + BitVec.ofNat 64 abiSlot ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff phiGVar)) =
        (ret6 - 9223372036854775808).toBitVec ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff ploGVar)) = 0#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) = 9#64 := by
  let cPhi := storeMemOff .sd AbiReg.gp AbiReg.s6 AbiReg.t0 (checkerTabMini.globOff phiGVar)
  let cPlo := storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (checkerTabMini.globOff ploGVar)
  let cMode := cmpDrvSetMode 9 checkerTabMini
  have hNeedEq := checkerTabMini_abiNeed_eq
  have h211 : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; simp [abiSlot]
  have hR : regionBase.toNat + abiSlot ≤ 2 ^ 64 := by omega
  have hl1 : img.lkm.linkSpec (pre ++ cPhi ++ (cPlo ++ cMode ++ drvResetStack ++
      cmpDrvCallPrep checkerTabMini ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [cmpDrvMode9Setup, cPhi, cPlo, cMode, List.append_assoc] using hlink
  have hpc1_64 := linkResolved_sub_pc64 (linkedCmpEnv img) pre cPhi _ hl1
  have halPhi : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.globOff phiGVar)) 8 = true := by
    rw [hgp, globOff_bitvec]; exact isAligned8_add_nat_mul8 regionBase hRegAlign _ (by
      rw [checkerTabMini_resBase_eq, Int.toNat_natCast, t_nxres]; omega)
  obtain ⟨s1, hrun1, hoth1, hm1, hpc1⟩ :=
    storeMemOff_sd_correct_lm img.lkm (linkedCmpEnv img).hrom pre _ AbiReg.gp AbiReg.s6 AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.globOff phiGVar) hl1 hpc1_64 st hpc halPhi
  let p1 := pre ++ cPhi
  have hpc1' : s1.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p1) := by
    simpa only [p1, img.lkm.totalSize_append] using hpc1
  have hs1gp : s1.getReg AbiReg.gp = regionBase := (hoth1 _ (by decide)).trans hgp
  have hl2 : img.lkm.linkSpec (p1 ++ cPlo ++ (cMode ++ drvResetStack ++
      cmpDrvCallPrep checkerTabMini ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p1, List.append_assoc] using hl1
  have hpc2_64 := linkResolved_sub_pc64 (linkedCmpEnv img) p1 cPlo _ hl2
  have halPlo : isAligned (s1.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.globOff ploGVar)) 8 = true := by
    rw [hs1gp, globOff_bitvec]; exact isAligned8_add_nat_mul8 regionBase hRegAlign _ (by
      rw [checkerTabMini_resBase_eq, Int.toNat_natCast, t_nxres]; omega)
  obtain ⟨s2, hrun2, hoth2, hm2, hpc2⟩ :=
    storeMemOff_sd_correct_lm img.lkm (linkedCmpEnv img).hrom p1 _ AbiReg.gp AbiReg.zero AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.globOff ploGVar) hl2 hpc2_64 s1 hpc1' halPlo
  let p2 := p1 ++ cPlo
  have hpc2' : s2.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p2) := by
    simpa only [p2, img.lkm.totalSize_append] using hpc2
  have hs2gp : s2.getReg AbiReg.gp = regionBase := (hoth2 _ (by decide)).trans hs1gp
  have hl3 : img.lkm.linkSpec (p2 ++ cMode ++ (drvResetStack ++
      cmpDrvCallPrep checkerTabMini ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p2, List.append_assoc] using hl2
  obtain ⟨k3, s3, hrun3, hpc3, hs3gp, hoth3, hm3⟩ :=
    cmpDrvSetMode_sim img regionBase hRegAlign hReg64 9 p2 _ hl3 s2 hpc2' hs2gp
  let p3 := p2 ++ cMode
  have hpc3' : s3.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p3) := by
    simpa only [p3, img.lkm.totalSize_append] using hpc3
  have hl4 : img.lkm.linkSpec (p3 ++ drvResetStack ++ (cmpDrvCallPrep checkerTabMini ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p3, List.append_assoc] using hl3
  obtain ⟨k4, s4, hrun4, hpc4, hoth4, hout4, hTop4, hLim4⟩ :=
    drvResetStack_sim_gen (linkedCmpEnv img) regionBase hRegAlign p3 _ hl4 s3 hpc3' hs3gp
  let p4 := p3 ++ drvResetStack
  have hpc4' : s4.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p4) := by
    simpa only [p4, img.lkm.totalSize_append] using hpc4
  have hs4gp : s4.getReg AbiReg.gp = regionBase := (hoth4 _ (by decide)).trans hs3gp
  have hl5 : img.lkm.linkSpec (p4 ++ cmpDrvCallPrep checkerTabMini ++ post) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p4, List.append_assoc] using hl4
  obtain ⟨k5, s5, hrun5, hpc5, hm5, hs5gp, hs5sp, hs5s0, hs5t0, hs5t1, hoth5⟩ :=
    linkedCmpDrvCallPrep_sim img regionBase hRegAlign p4 post hl5 (checkerCmp_exhausted_lbl img) s4 hpc4' hs4gp
  have hphiM : s1.mem = writeWord64 st.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff phiGVar))
      ((ret6 - 9223372036854775808).toBitVec) := by
    rw [hm1, hgp, hs6]
  have hploM : s2.mem = writeWord64 s1.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff ploGVar)) 0#64 := by
    rw [hm2, hs1gp]; rfl
  have hmodeM : s3.mem = writeWord64 s2.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) 9#64 :=
    hm3
  let ws03 : List (Int × BitVec 64) :=
    [(checkerTabMini.globOff phiGVar, (ret6 - 9223372036854775808).toBitVec),
     (checkerTabMini.globOff ploGVar, 0#64),
     (checkerTabMini.globOff modeGVar, 9#64)]
  have hs3Eq : s3.mem = applyTabWrites regionBase st.mem ws03 := by
    rw [hmodeM, hploM, hphiM]; simp only [ws03, applyTabWrites]
  have hout03 : ProgMemOutside (cmp9WriteSpan regionBase) st.mem s3.mem := by
    rw [hs3Eq]
    refine progMemOutside_applyTabWrites ws03 (fun e he k hk => ?_) st.mem
    simp only [ws03, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact Or.inr ⟨phiGVar, by simp, ⟨k, hk, rfl⟩⟩
    · exact Or.inr ⟨ploGVar, by simp, ⟨k, hk, rfl⟩⟩
    · exact Or.inr ⟨modeGVar, by simp, ⟨k, hk, rfl⟩⟩
  have hout34' : ProgMemOutside (cmp9WriteSpan regionBase) s3.mem s4.mem :=
    ProgMemOutside.of_memEqOutside (fun _ h => Or.inl h) hout4
  have hout04 : ProgMemOutside (cmp9WriteSpan regionBase) st.mem s4.mem :=
    hout03.trans hout34'
  have hphiOff := globOff_eq_nat phiGVar
  have hploOff := globOff_eq_nat ploGVar
  have hmodeOff := globOff_eq_nat modeGVar
  have hphiN : checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + phiGVar.id) + 8 ≤ abiSlot := globOff_bound (by decide)
  have hploN : checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + ploGVar.id) + 8 ≤ abiSlot := globOff_bound (by decide)
  have hmodeN : checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + modeGVar.id) + 8 ≤ abiSlot := globOff_bound (by decide)
  have hphiOk : tabOffOk (checkerTabMini.globOff phiGVar) := ⟨by rw [hphiOff]; omega, by rw [hphiOff, Int.toNat_natCast]; exact hphiN⟩
  have hploOk : tabOffOk (checkerTabMini.globOff ploGVar) := ⟨by rw [hploOff]; omega, by rw [hploOff, Int.toNat_natCast]; exact hploN⟩
  have hmodeOk : tabOffOk (checkerTabMini.globOff modeGVar) := ⟨by rw [hmodeOff]; omega, by rw [hmodeOff, Int.toNat_natCast]; exact hmodeN⟩
  have hrGe := resBase_ge_16
  have hPhiVal : readWord64 s4.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff phiGVar)) =
      (ret6 - 9223372036854775808).toBitVec := by
    have e34 : readWord64 s4.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff phiGVar)) =
        readWord64 s3.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff phiGVar)) := by
      rw [hphiOff, BitVec.ofInt_natCast]
      exact MemEqOutside.readWord64_eq hout4 _ fun k hk hc =>
        memSpan_offset_disjoint_contains_false hR hphiN (by simp [abiSlot] : 0 + 16 ≤ abiSlot)
          (Or.inr (by omega)) ⟨k, hk, rfl⟩ (by simpa only [BitVec.add_zero] using hc)
    have hs3tail : s3.mem = applyTabWrites regionBase s1.mem
        [(checkerTabMini.globOff ploGVar, 0#64), (checkerTabMini.globOff modeGVar, 9#64)] := by
      rw [hmodeM, hploM]; simp only [applyTabWrites]
    rw [e34, hs3tail]
    rw [readWord64_applyTabWrites_disj hR hphiOk _ (fun e he => by
      have hne1 : phiGVar.id ≠ ploGVar.id := by decide
      have hne2 : phiGVar.id ≠ modeGVar.id := by decide
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact ⟨hploOk, by dsimp only [tabOffDisj]; rw [hphiOff, hploOff, Int.toNat_natCast, Int.toNat_natCast]; omega⟩
      · exact ⟨hmodeOk, by dsimp only [tabOffDisj]; rw [hphiOff, hmodeOff, Int.toNat_natCast, Int.toNat_natCast]; omega⟩) _]
    rw [hphiM, readWord64_writeWord64_self]
  have hPloVal : readWord64 s4.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff ploGVar)) = 0#64 := by
    have e34 : readWord64 s4.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff ploGVar)) =
        readWord64 s3.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff ploGVar)) := by
      rw [hploOff, BitVec.ofInt_natCast]
      exact MemEqOutside.readWord64_eq hout4 _ fun k hk hc =>
        memSpan_offset_disjoint_contains_false hR hploN (by simp [abiSlot] : 0 + 16 ≤ abiSlot)
          (Or.inr (by omega)) ⟨k, hk, rfl⟩ (by simpa only [BitVec.add_zero] using hc)
    have hs3tail : s3.mem = applyTabWrites regionBase s2.mem [(checkerTabMini.globOff modeGVar, 9#64)] := by
      rw [hmodeM]; simp only [applyTabWrites]
    rw [e34, hs3tail]
    rw [readWord64_applyTabWrites_disj hR hploOk _ (fun e he => by
      have hne : ploGVar.id ≠ modeGVar.id := by decide
      simp only [List.mem_singleton] at he; subst he
      exact ⟨hmodeOk, by dsimp only [tabOffDisj]; rw [hploOff, hmodeOff, Int.toNat_natCast, Int.toNat_natCast]; omega⟩) _]
    rw [hploM, readWord64_writeWord64_self]
  have hModeVal : readWord64 s4.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) = 9#64 := by
    have e34 : readWord64 s4.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) =
        readWord64 s3.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) := by
      rw [hmodeOff, BitVec.ofInt_natCast]
      exact MemEqOutside.readWord64_eq hout4 _ fun k hk hc =>
        memSpan_offset_disjoint_contains_false hR hmodeN (by simp [abiSlot] : 0 + 16 ≤ abiSlot)
          (Or.inr (by omega)) ⟨k, hk, rfl⟩ (by simpa only [BitVec.add_zero] using hc)
    rw [e34, hmodeM, readWord64_writeWord64_self]
  refine ⟨img.lkm.totalSize cPhi + img.lkm.totalSize cPlo + k3 + k4 + k5, s5, ?_, ?_,
    hs5gp, hs5s0, by rw [hs5sp]; exact hTop4,
    (hoth5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hoth4 _ (by decide)).trans ((hoth3 _ (by decide) (by decide)).trans
        ((hoth2 _ (by decide)).trans (hoth1 _ (by decide))))),
    hs5t0, hs5t1, by rw [hm5]; exact hout04,
    by rw [hm5]; exact hTop4, by rw [hm5]; exact hLim4,
    by rw [hm5]; exact hPhiVal, by rw [hm5]; exact hPloVal, by rw [hm5]; exact hModeVal⟩
  · rw [run_add, run_add, run_add, run_add, hrun1]
    dsimp only; rw [hrun2]; dsimp only; rw [hrun3]; dsimp only; rw [hrun4]; exact hrun5
  · rw [hpc5]
    exact congrArg (fun n => BitVec.ofNat 64 (4 * n))
      (by dsimp only [p4, p3, p2, p1, cmpDrvMode9Setup, cPhi, cPlo, cMode]
          simp only [img.lkm.totalSize_append, Nat.add_assoc])

theorem cmpMode9_progMemRel
    {solBase pinsBase regionBase : BitVec 64} {solLen pinsLen : Nat}
    (hSol64 : solBase.toNat + solLen ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pinsLen ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjSolPins : MemSpan.disjoint ⟨solBase, solLen⟩ ⟨pinsBase, pinsLen⟩)
    (hDisjSolReg : MemSpan.disjoint ⟨solBase, solLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pinsLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    {rmem8 rmem9 : ByteMem} {m8 : _root_.L.Mem} {ret6 : _root_.L.Word}
    (hRel8 : ProgMemRel checkerTabMini
      (checkerLayoutCmpB solBase pinsBase regionBase solLen pinsLen
        hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg)
      rmem8 m8)
    (hout : ProgMemOutside (cmp9WriteSpan regionBase) rmem8 rmem9)
    (hPhi : readWord64 rmem9 (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff phiGVar)) =
      (ret6 - 9223372036854775808).toBitVec)
    (hPlo : readWord64 rmem9 (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff ploGVar)) = 0#64)
    (hMode : readWord64 rmem9 (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) = 9#64) :
    ProgMemRel checkerTabMini
      (checkerLayoutCmpB solBase pinsBase regionBase solLen pinsLen
        hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg)
      rmem9 (cmpPhase9Mem m8 ret6) := by
  let LB := checkerLayoutCmpB solBase pinsBase regionBase solLen pinsLen
    hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg
  have hNeedEq := checkerTabMini_abiNeed_eq
  have h211 : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; simp [abiSlot]
  have hR : regionBase.toNat + abiSlot ≤ 2 ^ 64 := by omega
  have hr := resBase_ge_16
  have houtSlot0 : ProgMemOutside (fun a => (⟨regionBase, abiSlot⟩ : MemSpan).contains a) rmem8 rmem9 :=
    hout.mono (cmp9WriteSpan_sub_slot0 regionBase hReg64)
  rcases hRel8 with ⟨hA8, hA64, hArom, hAg⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases hA8 a ha with ⟨hcap, hlt, hlen, hbase, hbytes⟩
    have hpos8lt : checkerTabMini.pos8 a < 2 := by
      have hlt' := (Tab.bytePosOk_lt ha).1; rw [t_nb] at hlt'; exact hlt'
    have hDisj8 : ∀ k, k < (m8.arr8 a).size →
        ¬(⟨regionBase, abiSlot⟩ : MemSpan).contains (LB.base8 a + BitVec.ofNat 64 k) := by
      intro k hk hc
      exact MemSpan.disjoint_to_memDisjoint (LB.arr8Span_valid a) LB.tabSpan_valid (LB.h8DisjTab a ha) _
        ⟨k, Nat.lt_of_lt_of_le hk hcap, rfl⟩ hc
    have harr8 : (cmpPhase9Mem m8 ret6).arr8 a = m8.arr8 a := rfl
    have hlen9 : readWord64 rmem9 (LB.T + BitVec.ofInt 64 (checkerTabMini.len8 a)) =
        BitVec.ofNat 64 ((cmpPhase9Mem m8 ret6).arr8 a).size := by
      have hd : checkerTabMini.len8 a = ((1656 + 8 * checkerTabMini.pos8 a : Nat) : Int) := by
        change checkerTabMini.dlen (checkerTabMini.pos8 a) = _; simp only [Tab.dlen, t_nb, t_nw]; omega
      rw [harr8, ← hlen]; change readWord64 rmem9 (regionBase + BitVec.ofInt 64 (checkerTabMini.len8 a)) = _
      apply hout.readWord64_eq; rw [hd, BitVec.ofInt_natCast]
      exact cmp9WriteSpan_disj_tabOff regionBase hReg64 (by simp [abiSlot]; omega) (by omega) fun g _ => by omega
    have hbase9 : readWord64 rmem9 (LB.T + BitVec.ofInt 64 (checkerTabMini.base8 a)) = LB.base8 a := by
      have hb : checkerTabMini.base8 a = ((16 + 8 * checkerTabMini.pos8 a : Nat) : Int) := by
        change checkerTabMini.dbase (checkerTabMini.pos8 a) = _; simp only [Tab.dbase]; omega
      rw [← hbase]; change readWord64 rmem9 (regionBase + BitVec.ofInt 64 (checkerTabMini.base8 a)) = _
      apply hout.readWord64_eq; rw [hb, BitVec.ofInt_natCast]
      exact cmp9WriteSpan_disj_tabOff regionBase hReg64 (by simp [abiSlot]; omega) (by omega) fun g _ => by omega
    refine ⟨by rw [harr8]; exact hcap, by rw [harr8]; exact hlt, hlen9, hbase9, fun i hi => ?_⟩
    simp only [harr8]
    rw [houtSlot0 _ (hDisj8 i hi), hbytes i hi]
    rfl
  · intro s hs
    have ⟨hlo, hhi⟩ := checkerTabMini_wordPos_bounds hs
    rcases hA64 s hs with ⟨hcap, hlt, hlen, hbase, hwords⟩
    have harr64 : (cmpPhase9Mem m8 ret6).arr64 s = m8.arr64 s := rfl
    have hlen9 : readWord64 rmem9 (LB.T + BitVec.ofInt 64 (checkerTabMini.len64 s)) =
        BitVec.ofNat 64 ((cmpPhase9Mem m8 ret6).arr64 s).size := by
      have hd : checkerTabMini.len64 s = ((1656 + 8 * checkerTabMini.pos64 s : Nat) : Int) := by
        change checkerTabMini.dlen (checkerTabMini.pos64 s) = _; simp only [Tab.dlen, t_nb, t_nw]; omega
      rw [harr64, ← hlen]; change readWord64 rmem9 (regionBase + BitVec.ofInt 64 (checkerTabMini.len64 s)) = _
      apply hout.readWord64_eq; rw [hd, BitVec.ofInt_natCast]
      exact cmp9WriteSpan_disj_tabOff regionBase hReg64 (by simp [abiSlot]; omega) (by omega) fun g _ => by omega
    have hbase9 : readWord64 rmem9 (LB.T + BitVec.ofInt 64 (checkerTabMini.base64 s)) = LB.base64 s := by
      have hb : checkerTabMini.base64 s = ((16 + 8 * checkerTabMini.pos64 s : Nat) : Int) := by
        change checkerTabMini.dbase (checkerTabMini.pos64 s) = _; simp only [Tab.dbase]; omega
      rw [← hbase]; change readWord64 rmem9 (regionBase + BitVec.ofInt 64 (checkerTabMini.base64 s)) = _
      apply hout.readWord64_eq; rw [hb, BitVec.ofInt_natCast]
      exact cmp9WriteSpan_disj_tabOff regionBase hReg64 (by simp [abiSlot]; omega) (by omega) fun g _ => by omega
    refine ⟨by rw [harr64]; exact hcap, by rw [harr64]; exact hlt, hlen9, hbase9, fun i hi => ?_⟩
    have hi' : i < (m8.arr64 s).size := hi
    simp only [harr64]
    rw [← hwords i hi']
    apply houtSlot0.readWord64_eq
    intro k hk hc
    change (m8.arr64 s).size ≤ LB.cap64 s at hcap
    have hc' : LB.tabSpan.contains ((LB.arr64Span s).base + BitVec.ofNat 64 (8 * i + k)) := by
      dsimp only [ProgLayout.arr64Span, ProgLayout.tabSpan]
      change (⟨regionBase, abiSlot⟩ : MemSpan).contains (LB.base64 s + BitVec.ofNat 64 (8 * i + k))
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]; exact hc
    exact MemSpan.disjoint_to_memDisjoint (LB.arr64Span_valid s) LB.tabSpan_valid (LB.h64DisjTab s hs) _
      ⟨8 * i + k, by dsimp only [ProgLayout.arr64Span]; have := Nat.lt_of_lt_of_le hi' hcap; omega, rfl⟩ hc'
  · intro k hk
    rw [← hArom k hk]
    apply hout
    have hromNn := ProgLayout.romBase_nonneg checkerTabMini
    have hk8 : k < 8 * checkerTabMini.romWords := by simp only [Tab.romWords]; omega
    have hbd : checkerTabMini.romBase.toNat + k + 1 ≤ abiSlot := by
      have harg := checkerTabMini_args_lt
      rw [checkerTabMini_args_eq, Int.toNat_natCast] at harg
      rw [checkerTabMini_romBase_eq, Int.toNat_natCast]; omega
    have hromGe : 16 + 24 * 205 ≤ checkerTabMini.romBase.toNat + k := by
      rw [checkerTabMini_romBase_eq, Int.toNat_natCast]; omega
    have hromRes : checkerTabMini.romBase.toNat + k < checkerTabMini.resBase.toNat := by
      rw [checkerTabMini_romBase_eq, checkerTabMini_resBase_eq, Int.toNat_natCast, Int.toNat_natCast]; omega
    have hadd0 : LB.T + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + k) =
        regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + k) + BitVec.ofNat 64 0 := by
      change regionBase + _ = _; rw [BitVec.add_zero]
    rw [hadd0]
    exact cmp9WriteSpan_disj_tabOff regionBase hReg64 hbd (by omega) (fun g _ => by omega) 0 (by decide)
  · intro g hg
    by_cases hphi : g = phiGVar
    · subst hphi
      change readWord64 rmem9 (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff phiGVar)) = _
      have hval : (cmpPhase9Mem m8 ret6).glob phiGVar = ret6 - 9223372036854775808 := by
        simp [cmpPhase9Mem, seqNextMini, _root_.L.Mem.setG, (by decide : phiGVar ≠ modeGVar)]
      rw [hval]; exact hPhi
    · by_cases hplo : g = ploGVar
      · subst hplo
        change readWord64 rmem9 (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff ploGVar)) = _
        have hval : (cmpPhase9Mem m8 ret6).glob ploGVar = 0 := by
          simp [cmpPhase9Mem, seqNextMini, _root_.L.Mem.setG,
            (by decide : ploGVar ≠ modeGVar), (by decide : ploGVar ≠ phiGVar)]
        rw [hval]; exact hPlo
      · by_cases hmode : g = modeGVar
        · subst hmode
          change readWord64 rmem9 (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) = _
          have hval : (cmpPhase9Mem m8 ret6).glob modeGVar = 9 := by
            simp [cmpPhase9Mem, seqNextMini, _root_.L.Mem.setG]
          rw [hval]; exact hMode
        · have hneIds : g.id ≠ phiGVar.id ∧ g.id ≠ ploGVar.id ∧ g.id ≠ modeGVar.id := by
            refine ⟨fun h => hphi (by cases g; simp at h; subst h; rfl),
                    fun h => hplo (by cases g; simp at h; subst h; rfl),
                    fun h => hmode (by cases g; simp at h; subst h; rfl)⟩
          have hval : (cmpPhase9Mem m8 ret6).glob g = m8.glob g := by
            simp [cmpPhase9Mem, seqNextMini, _root_.L.Mem.setG, hphi, hplo, hmode]
          rw [hval, ← hAg g hg]
          apply hout.readWord64_eq
          have hgl := globOff_eq_nat g
          have hgb := globOff_bound hg
          rw [hgl, BitVec.ofInt_natCast]
          exact cmp9WriteSpan_disj_tabOff regionBase hReg64 hgb (by omega) fun g' hg' => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
            rcases hg' with rfl | rfl | rfl <;> omega

private def checkerCheckFd : _root_.L.FunDecl :=
  { nparams := 0
    nlocals := 1
    body :=
      .seq (.ite (.cmp .eq (.glob ⟨8⟩) (.const 1)) (.seq (.call [0] "check_a" [.const 1]) (.ret [.var 0])) .skip)
        (.seq (.ite (.cmp .eq (.glob ⟨8⟩) (.const 3)) (.seq (.call [0] "check_a" [.const 0]) (.ret [.var 0])) .skip)
          (.seq (.ite (.cmp .eq (.glob ⟨8⟩) (.const 2)) (.seq (.call [0] "check_b" []) (.ret [.var 0])) .skip)
            (.seq (.ite (.cmp .eq (.glob ⟨8⟩) (.const 4)) (.seq (.call [0] "check_c1" []) (.ret [.var 0])) .skip)
              (.seq (.ite (.cmp .eq (.glob ⟨8⟩) (.const 5)) (.seq (.call [0] "check_c2" []) (.ret [.var 0])) .skip)
                (.seq (.ite (.cmp .eq (.glob ⟨8⟩) (.const 6)) (.seq (.call [0] "check_c3" [.const 0]) (.ret [.var 0])) .skip)
                  (.seq (.ite (.cmp .eq (.glob ⟨8⟩) (.const 7)) (.seq (.call [0] "check_c3" [.const 1]) (.ret [.var 0])) .skip)
                    (.seq (.ite (.cmp .eq (.glob ⟨8⟩) (.const 8)) (.seq (.call [0] "check_bs" []) (.ret [.var 0])) .skip)
                      (.seq (.ite (.cmp .eq (.glob ⟨8⟩) (.const 9)) (.seq (.call [0] "check_bc" []) (.ret [.var 0])) .skip)
                        (.abort (.const 0)))))))))) }

private def stmtEqB : _root_.L.Stmt → _root_.L.Stmt → Bool
  | .skip, .skip => true
  | .set x1 e1, .set x2 e2 => decide (x1 = x2) && decide (e1 = e2)
  | .st8 a1 i1 e1, .st8 a2 i2 e2 => decide (a1 = a2) && decide (i1 = i2) && decide (e1 = e2)
  | .st64 a1 i1 e1, .st64 a2 i2 e2 => decide (a1 = a2) && decide (i1 = i2) && decide (e1 = e2)
  | .seq s1 t1, .seq s2 t2 => stmtEqB s1 s2 && stmtEqB t1 t2
  | .ite c1 s1 t1, .ite c2 s2 t2 => decide (c1 = c2) && stmtEqB s1 s2 && stmtEqB t1 t2
  | .while c1 s1, .while c2 s2 => decide (c1 = c2) && stmtEqB s1 s2
  | .brk, .brk => true
  | .ret es1, .ret es2 => decide (es1 = es2)
  | .call xs1 f1 args1, .call xs2 f2 args2 => decide (xs1 = xs2) && decide (f1 = f2) && decide (args1 = args2)
  | .abort e1, .abort e2 => decide (e1 = e2)
  | .gset g1 e1, .gset g2 e2 => decide (g1 = g2) && decide (e1 = e2)
  | .st64t a1 t1 i1 e1, .st64t a2 t2 i2 e2 =>
    decide (a1 = a2) && decide (t1 = t2) && decide (i1 = i2) && decide (e1 = e2)
  | .copy64 d1 di1 s1 si1 n1, .copy64 d2 di2 s2 si2 n2 =>
    decide (d1 = d2) && decide (di1 = di2) && decide (s1 = s2) && decide (si1 = si2) && decide (n1 = n2)
  | .copy8w d1 di1 s1 si1 n1, .copy8w d2 di2 s2 si2 n2 =>
    decide (d1 = d2) && decide (di1 = di2) && decide (s1 = s2) && decide (si1 = si2) && decide (n1 = n2)
  | .scan8 x1 s1 i1 e1 c1, .scan8 x2 s2 i2 e2 c2 =>
    decide (x1 = x2) && decide (s1 = s2) && decide (i1 = i2) && decide (e1 = e2) && decide (c1 = c2)
  | .st32t a1 t1 i1 e1, .st32t a2 t2 i2 e2 =>
    decide (a1 = a2) && decide (t1 = t2) && decide (i1 = i2) && decide (e1 = e2)
  | _, _ => false

private theorem stmtEqB_sound : ∀ s1 s2 : _root_.L.Stmt, stmtEqB s1 s2 = true → s1 = s2
  | .skip, .skip, _ => rfl
  | .set _ _, .set _ _, h => by
    simp only [stmtEqB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨rfl, rfl⟩; rfl
  | .st8 _ _ _, .st8 _ _ _, h => by
    simp only [stmtEqB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨rfl, rfl⟩, rfl⟩; rfl
  | .st64 _ _ _, .st64 _ _ _, h => by
    simp only [stmtEqB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨rfl, rfl⟩, rfl⟩; rfl
  | .seq s1 t1, .seq s2 t2, h => by
    simp only [stmtEqB, Bool.and_eq_true] at h
    rw [stmtEqB_sound s1 s2 h.1, stmtEqB_sound t1 t2 h.2]
  | .ite _ s1 t1, .ite _ s2 t2, h => by
    simp only [stmtEqB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨rfl, hs⟩, ht⟩
    rw [stmtEqB_sound s1 s2 hs, stmtEqB_sound t1 t2 ht]
  | .while _ s1, .while _ s2, h => by
    simp only [stmtEqB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨rfl, hs⟩
    rw [stmtEqB_sound s1 s2 hs]
  | .brk, .brk, _ => rfl
  | .ret _, .ret _, h => by
    simp only [stmtEqB, decide_eq_true_eq] at h; subst h; rfl
  | .call _ _ _, .call _ _ _, h => by
    simp only [stmtEqB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨rfl, rfl⟩, rfl⟩; rfl
  | .abort _, .abort _, h => by
    simp only [stmtEqB, decide_eq_true_eq] at h; subst h; rfl
  | .gset _ _, .gset _ _, h => by
    simp only [stmtEqB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨rfl, rfl⟩; rfl
  | .st64t _ _ _ _, .st64t _ _ _ _, h => by
    simp only [stmtEqB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩; rfl
  | .copy64 _ _ _ _ _, .copy64 _ _ _ _ _, h => by
    simp only [stmtEqB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩; rfl
  | .copy8w _ _ _ _ _, .copy8w _ _ _ _ _, h => by
    simp only [stmtEqB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩; rfl
  | .scan8 _ _ _ _ _, .scan8 _ _ _ _ _, h => by
    simp only [stmtEqB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩; rfl
  | .st32t _ _ _ _, .st32t _ _ _ _, h => by
    simp only [stmtEqB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩; rfl

private theorem checkerProgMini_lookup_check_eq :
    checkerProgMini.lookup "check" = some checkerCheckFd := by
  have h : ((checkerProgMini.lookup "check").map fun fd =>
      fd.nparams == checkerCheckFd.nparams &&
      fd.nlocals == checkerCheckFd.nlocals &&
      stmtEqB fd.body checkerCheckFd.body) = some true := by
    decide
  cases hlk : checkerProgMini.lookup "check" with
  | none => rw [hlk] at h; cases h
  | some fd =>
    rw [hlk, Option.map_some, Option.some.injEq, Bool.and_eq_true, Bool.and_eq_true,
      beq_iff_eq, beq_iff_eq] at h
    rcases fd with ⟨np, nl, bd⟩
    rcases h with ⟨⟨h1, h2⟩, h3⟩
    have hbd := stmtEqB_sound bd checkerCheckFd.body h3
    change np = 0 at h1; change nl = 1 at h2
    subst h1; subst h2; subst hbd
    rfl

private theorem check_mode89_eq (md : _root_.L.Word) (hmd : md = 8 ∨ md = 9)
    (k : Nat) (m : _root_.L.Mem) (hmode : m.glob modeGVar = md) :
    let fn := if md = 8 then "check_bs" else "check_bc"
    _root_.L.run checkerProgMini (k + 1) "check" [] m =
      (_root_.L.run checkerProgMini k fn [] m).map fun (rs, m') => ([rs.headD 0], m') := by
  have hm8 : m.glob ⟨8⟩ = md := by
    have : modeGVar = ⟨8⟩ := by decide
    rw [← this]; exact hmode
  dsimp only
  unfold _root_.L.run
  let s0 : _root_.L.St := { mem := m, loc := _root_.L.Locals.init [] }
  let fn := if md = 8 then "check_bs" else "check_bc"
  let rhs := (_root_.L.invoke checkerProgMini (_root_.L.exec checkerProgMini k) fn []).run s0
  change Except.map (fun p => (p.1, p.2.mem))
      ((_root_.L.invoke checkerProgMini (_root_.L.exec checkerProgMini (k + 1)) "check" []).run s0) =
    Except.map (fun p => ([p.1.headD 0], p.2)) (Except.map (fun p => (p.1, p.2.mem)) rhs)
  rw [_root_.L.invoke, _root_.L.lookupFn, checkerProgMini_lookup_check_eq]
  dsimp only [_root_.L.callFn, checkerCheckFd, _root_.L.exec, _root_.L.step,
    _root_.L.evalC, _root_.L.evalE, _root_.L.evalArgs, _root_.L.Cmp.eval,
    _root_.L.Locals.init, _root_.L.setLocs, _root_.L.St.setLocs, _root_.L.St.setLoc,
    _root_.L.Sig.retVal, _root_.L.Sig.retOr, s0,
    get, getThe, set, modify, modifyGet, MonadState.get, MonadState.set,
    MonadStateOf.get, MonadStateOf.set, MonadStateOf.modifyGet,
    StateT.modifyGet, StateT.run, StateT.bind, StateT.pure, StateT.get, StateT.set,
    Pure.pure, Except.pure, Bind.bind, Except.bind]
  rw [hm8]
  rcases hmd with rfl | rfl
  · simp only [hm8, show ((8 : _root_.L.Word) == 1) = false from rfl,
      show ((8 : _root_.L.Word) == 3) = false from rfl,
      show ((8 : _root_.L.Word) == 2) = false from rfl,
      show ((8 : _root_.L.Word) == 4) = false from rfl,
      show ((8 : _root_.L.Word) == 5) = false from rfl,
      show ((8 : _root_.L.Word) == 6) = false from rfl,
      show ((8 : _root_.L.Word) == 7) = false from rfl,
      show ((8 : _root_.L.Word) == 8) = true from rfl,
      StateT.pure, StateT.bind, StateT.get, StateT.modifyGet,
      Pure.pure, Bind.bind, Except.pure, Except.bind,
      Bool.false_eq_true, ↓reduceIte]
    have hrhs : _root_.L.invoke checkerProgMini (_root_.L.exec checkerProgMini k) "check_bs" []
        { mem := m, loc := _root_.L.Locals.init [] } = rhs := rfl
    rw [hrhs]
    cases rhs with
    | error e => rfl
    | ok pair => rfl
  · simp only [hm8, show ((9 : _root_.L.Word) == 1) = false from rfl,
      show ((9 : _root_.L.Word) == 3) = false from rfl,
      show ((9 : _root_.L.Word) == 2) = false from rfl,
      show ((9 : _root_.L.Word) == 4) = false from rfl,
      show ((9 : _root_.L.Word) == 5) = false from rfl,
      show ((9 : _root_.L.Word) == 6) = false from rfl,
      show ((9 : _root_.L.Word) == 7) = false from rfl,
      show ((9 : _root_.L.Word) == 8) = false from rfl,
      show ((9 : _root_.L.Word) == 9) = true from rfl,
      StateT.pure, StateT.bind, StateT.get, StateT.modifyGet,
      Pure.pure, Bind.bind, Except.pure, Except.bind,
      Bool.false_eq_true, ↓reduceIte]
    have hrhs : _root_.L.invoke checkerProgMini (_root_.L.exec checkerProgMini k) "check_bc" []
        { mem := m, loc := _root_.L.Locals.init [] } = rhs := rfl
    rw [hrhs]
    cases rhs with
    | error e => rfl
    | ok pair => rfl

theorem run_check_mode89_agree_ok
    (md : _root_.L.Word) (hmd : md = 8 ∨ md = 9)
    {k : Nat} {mW mN mW' : _root_.L.Mem} {rs : List _root_.L.Word}
    (hAg : L.Agree L.Checker.phaseBPa (fun _ => false) mW mN)
    (hmode : mW.glob modeGVar = md)
    (hrun : _root_.L.run checkerProgMini (k + 1) "check" [] mW = .ok (rs, mW')) :
    ∃ mN',
      _root_.L.run checkerProgMini (k + 1) "check" [] mN = .ok (rs, mN') ∧
      L.Agree L.Checker.phaseBPa (fun _ => false) mW' mN' := by
  have hmodeN : mN.glob modeGVar = md := by
    have hglobEq : mW.glob modeGVar = mN.glob modeGVar := congrFun hAg.2.2 modeGVar
    rw [← hglobEq]; exact hmode
  rw [check_mode89_eq md hmd k mW hmode] at hrun
  rw [check_mode89_eq md hmd k mN hmodeN]
  have hQ := L.Checker.checkerProg_cqSeq
  obtain ⟨fs, hfs8, hfs9, hrd⟩ := hQ.reads
  rcases hmd with rfl | rfl
  · simp only [↓reduceIte] at hrun ⊢
    cases hsub : _root_.L.run checkerProgMini k "check_bs" [] mW with
    | error e => simp [hsub, Except.map] at hrun
    | ok pair =>
      rcases pair with ⟨rsSub, mW''⟩
      rw [hsub] at hrun
      simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hrun
      rcases hrun with ⟨rfl, rfl⟩
      obtain ⟨mN', hLN', hAg'⟩ := L.run_agree_ok hrd hfs8 hAg hsub
      refine ⟨mN', ?_, hAg'⟩
      rw [hLN']; rfl
  · simp only [show ¬((9 : _root_.L.Word) = 8) from by decide, ↓reduceIte] at hrun ⊢
    cases hsub : _root_.L.run checkerProgMini k "check_bc" [] mW with
    | error e => simp [hsub, Except.map] at hrun
    | ok pair =>
      rcases pair with ⟨rsSub, mW''⟩
      rw [hsub] at hrun
      simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hrun
      rcases hrun with ⟨rfl, rfl⟩
      obtain ⟨mN', hLN', hAg'⟩ := L.run_agree_ok hrd hfs9 hAg hsub
      refine ⟨mN', ?_, hAg'⟩
      rw [hLN']; rfl

def cmpPreCall4 : List AsmItem :=
  checkerDriverAsm checkerTabMini ++ cmpDrvPfx ++ drvNeedLi checkerTabMini ++
  cmpDrvBootCheck checkerTabMini ++ [Asm.call drvInitLabel] ++ cmpDrvMode4Setup checkerTabMini

def cmpPreCall5 : List AsmItem :=
  cmpPreCall4 ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode4Post ++ cmpDrvMode5Setup checkerTabMini

def cmpPreCall6 : List AsmItem :=
  cmpPreCall5 ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode5Post ++ cmpDrvMode6Setup checkerTabMini

def cmpPreCall8 : List AsmItem :=
  cmpPreCall6 ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode6Post ++ cmpDrvMode8Setup checkerTabMini

def cmpPreCall9 : List AsmItem :=
  cmpPreCall8 ++ [Asm.call (fnLabel "check")] ++ cmpDrvMode8Post ++ cmpDrvMode9Setup checkerTabMini

def cmpTail9 (img : LinkedCmpImage) : List AsmItem :=
  [Asm.j drvDoneLabel] ++ linkedCmpFnsAsm img

def cmpTail8 (img : LinkedCmpImage) : List AsmItem :=
  cmpDrvMode8Post ++ cmpDrvMode9Setup checkerTabMini ++ [Asm.call (fnLabel "check")] ++ cmpTail9 img

def cmpTail6 (img : LinkedCmpImage) : List AsmItem :=
  cmpDrvMode6Post ++ cmpDrvMode8Setup checkerTabMini ++ [Asm.call (fnLabel "check")] ++ cmpTail8 img

def cmpTail5 (img : LinkedCmpImage) : List AsmItem :=
  cmpDrvMode5Post ++ cmpDrvMode6Setup checkerTabMini ++ [Asm.call (fnLabel "check")] ++ cmpTail6 img

def cmpTail4 (img : LinkedCmpImage) : List AsmItem :=
  cmpDrvMode4Post ++ cmpDrvMode5Setup checkerTabMini ++ [Asm.call (fnLabel "check")] ++ cmpTail5 img


end ConAgua.RISCV.Bridge
