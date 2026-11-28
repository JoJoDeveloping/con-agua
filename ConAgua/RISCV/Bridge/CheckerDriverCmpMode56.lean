import ConAgua.RISCV.Bridge.CheckerDriverCmpCommon

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ConAgua.RISCV.Bridge

open ConAgua.RISCV.RV64
open ConAgua.RISCV.Compiler
open ConAgua.RISCV.Linker
open _root_.L

def cmp5WriteSpan (regionBase : BitVec 64) (a : BitVec 64) : Prop :=
  (⟨regionBase, 16⟩ : MemSpan).contains a ∨
  (⟨regionBase + BitVec.ofNat 64 16, 8⟩ : MemSpan).contains a ∨
  (⟨regionBase + BitVec.ofNat 64 1656, 8⟩ : MemSpan).contains a ∨
  (⟨regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar), 8⟩ : MemSpan).contains a

private theorem cmp5WriteSpan_sub_slot0 (regionBase : BitVec 64)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64) :
    ∀ a, cmp5WriteSpan regionBase a → (⟨regionBase, abiSlot⟩ : MemSpan).contains a := by
  intro a ha
  rcases ha with h | h | h | h
  · exact memSpan_offset_sub_slot0 regionBase hReg64 (by simp [abiSlot] : 0 + 16 ≤ abiSlot) _
      (by simpa only [BitVec.add_zero] using h)
  · exact memSpan_offset_sub_slot0 regionBase hReg64 (by simp [abiSlot] : 16 + 8 ≤ abiSlot) _ h
  · exact memSpan_offset_sub_slot0 regionBase hReg64 (by simp [abiSlot] : 1656 + 8 ≤ abiSlot) _ h
  · rw [globOff_bitvec] at h
    exact memSpan_offset_sub_slot0 regionBase hReg64 (globOff_bound (g := modeGVar) (by decide)) _ h

private theorem cmp5WriteSpan_disj_tabOff (regionBase : BitVec 64)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    {lo sz : Nat} (hle : lo + sz ≤ abiSlot) (h16 : 16 ≤ lo)
    (h16ne : lo + sz ≤ 16 ∨ 16 + 8 ≤ lo)
    (h1704ne : lo + sz ≤ 1656 ∨ 1656 + 8 ≤ lo)
    (hModeNe : lo + sz ≤ checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + modeGVar.id) ∨
      checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + modeGVar.id) + 8 ≤ lo) :
    ∀ k, k < sz → ¬ cmp5WriteSpan regionBase (regionBase + BitVec.ofNat 64 lo + BitVec.ofNat 64 k) := by
  intro k hk hw
  have hNeedEq := checkerTabMini_abiNeed_eq
  have h211 : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; simp [abiSlot]
  have hR : regionBase.toNat + abiSlot ≤ 2 ^ 64 := by omega
  rcases hw with h | h | h | h
  · exact memSpan_offset_disjoint_contains_false hR hle (by simp [abiSlot] : 0 + 16 ≤ abiSlot)
      (Or.inr h16) ⟨k, hk, rfl⟩ (by simpa only [BitVec.add_zero] using h)
  · exact memSpan_offset_disjoint_contains_false hR hle (by simp [abiSlot] : 16 + 8 ≤ abiSlot)
      h16ne ⟨k, hk, rfl⟩ h
  · exact memSpan_offset_disjoint_contains_false hR hle (by simp [abiSlot] : 1656 + 8 ≤ abiSlot)
      h1704ne ⟨k, hk, rfl⟩ h
  · rw [globOff_bitvec] at h
    exact memSpan_offset_disjoint_contains_false hR hle (globOff_bound (g := modeGVar) (by decide))
      hModeNe ⟨k, hk, rfl⟩ h

theorem cmp5WriteSpan_disj_callerSave (regionBase : BitVec 64)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64) :
    ∀ i, i < callerSaveRegs.length → ∀ k, k < 8 →
      ¬cmp5WriteSpan regionBase
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
  apply cmp5WriteSpan_disj_tabOff regionBase hReg64 hleSlot (by omega) (Or.inr (by omega)) (Or.inr (by omega))
  · have : modeGVar.id < 12 := by decide
    have := t_nxres; have := t_ng
    right; omega
  · exact hk

theorem cmpMode5Setup_sim (img : LinkedCmpImage) (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (solBase solLenBv : BitVec 64)
    (pre post : List AsmItem)
    (hlink : img.lkm.linkSpec (pre ++ cmpDrvMode5Setup checkerTabMini ++ post) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase)
    (hs3 : st.getReg AbiReg.s3 = solBase)
    (hs4 : st.getReg AbiReg.s4 = solLenBv) :
    ∃ k st',
      RV64.run (linkedCmpEnv img).rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize (pre ++ cmpDrvMode5Setup checkerTabMini)) ∧
      st'.getReg AbiReg.gp = regionBase ∧
      st'.getReg AbiReg.sp = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) ∧
      st'.getReg AbiReg.s0 = BitVec.ofNat 64 (abiFuel - 2) ∧
      st'.getReg AbiReg.s2 = st.getReg AbiReg.s2 ∧
      st'.getReg AbiReg.t0 = regionBase + BitVec.ofInt 64 checkerTabMini.args ∧
      st'.getReg AbiReg.t1 = 0#64 ∧
      ProgMemOutside (cmp5WriteSpan regionBase) st.mem st'.mem ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 0)) = solBase ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 0)) = solLenBv ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) = 5#64 ∧
      readWord64 st'.mem regionBase = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) ∧
      readWord64 st'.mem (regionBase + 8#64) = regionBase + BitVec.ofNat 64 abiSlot := by
  let cB := storeMemOff .sd AbiReg.gp AbiReg.s3 AbiReg.t0 (checkerTabMini.dbase 0)
  let cL := storeMemOff .sd AbiReg.gp AbiReg.s4 AbiReg.t0 (checkerTabMini.dlen 0)
  have hNeedEq := checkerTabMini_abiNeed_eq
  have h211 : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; simp [abiSlot]
  have hR : regionBase.toNat + abiSlot ≤ 2 ^ 64 := by omega
  have hl1 : img.lkm.linkSpec (pre ++ cB ++ (cL ++ drvResetStack ++
      cmpDrvSetMode 5 checkerTabMini ++ cmpDrvCallPrep checkerTabMini ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [cmpDrvMode5Setup, cB, cL, List.append_assoc] using hlink
  have hpc1_64 := linkResolved_sub_pc64 (linkedCmpEnv img) pre cB _ hl1
  have hal1 : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.dbase 0)) 8 = true := by
    rw [hgp, dbase_bv]; exact isAligned8_add_nat_mul8 regionBase hRegAlign _ (by simp)
  obtain ⟨s1, hrun1, hoth1, hm1, hpc1⟩ :=
    storeMemOff_sd_correct_lm img.lkm (linkedCmpEnv img).hrom pre _ AbiReg.gp AbiReg.s3 AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.dbase 0) hl1 hpc1_64 st hpc hal1
  let p1 := pre ++ cB
  have hpc1' : s1.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p1) := by
    simpa only [p1, img.lkm.totalSize_append] using hpc1
  have hs1gp : s1.getReg AbiReg.gp = regionBase := (hoth1 _ (by decide)).trans hgp
  have hs1s4 : s1.getReg AbiReg.s4 = solLenBv := (hoth1 _ (by decide)).trans hs4
  have hl2 : img.lkm.linkSpec (p1 ++ cL ++ (drvResetStack ++
      cmpDrvSetMode 5 checkerTabMini ++ cmpDrvCallPrep checkerTabMini ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p1, List.append_assoc] using hl1
  have hpc2_64 := linkResolved_sub_pc64 (linkedCmpEnv img) p1 cL _ hl2
  have hal2 : isAligned (s1.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.dlen 0)) 8 = true := by
    rw [hs1gp, dlen_bv]; exact isAligned8_add_nat_mul8 regionBase hRegAlign _ (by simp)
  obtain ⟨s2, hrun2, hoth2, hm2, hpc2⟩ :=
    storeMemOff_sd_correct_lm img.lkm (linkedCmpEnv img).hrom p1 _ AbiReg.gp AbiReg.s4 AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.dlen 0) hl2 hpc2_64 s1 hpc1' hal2
  let p2 := p1 ++ cL
  have hpc2' : s2.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p2) := by
    simpa only [p2, img.lkm.totalSize_append] using hpc2
  have hs2gp : s2.getReg AbiReg.gp = regionBase := (hoth2 _ (by decide)).trans hs1gp
  have hl3 : img.lkm.linkSpec (p2 ++ drvResetStack ++
      (cmpDrvSetMode 5 checkerTabMini ++ cmpDrvCallPrep checkerTabMini ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p2, List.append_assoc] using hl2
  obtain ⟨k3, s3, hrun3, hpc3, hoth3, hout3, hTop3, hLim3⟩ :=
    drvResetStack_sim_gen (linkedCmpEnv img) regionBase hRegAlign p2 _ hl3 s2 hpc2' hs2gp
  let p3 := p2 ++ drvResetStack
  have hpc3' : s3.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p3) := by
    simpa only [p3, img.lkm.totalSize_append] using hpc3
  have hs3gp : s3.getReg AbiReg.gp = regionBase := (hoth3 _ (by decide)).trans hs2gp
  have hl4 : img.lkm.linkSpec (p3 ++ cmpDrvSetMode 5 checkerTabMini ++
      (cmpDrvCallPrep checkerTabMini ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p3, List.append_assoc] using hl3
  obtain ⟨k4, s4, hrun4, hpc4, hs4gp, hoth4, hm4⟩ :=
    cmpDrvSetMode_sim img regionBase hRegAlign hReg64 5 p3 _ hl4 s3 hpc3' hs3gp
  let p4 := p3 ++ cmpDrvSetMode 5 checkerTabMini
  have hpc4' : s4.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p4) := by
    simpa only [p4, img.lkm.totalSize_append] using hpc4
  have hl5 : img.lkm.linkSpec (p4 ++ cmpDrvCallPrep checkerTabMini ++ post) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p4, List.append_assoc] using hl4
  obtain ⟨k5, s5, hrun5, hpc5, hm5, hs5gp, hs5sp, hs5s0, hs5t0, hs5t1, hoth5⟩ :=
    linkedCmpDrvCallPrep_sim img regionBase hRegAlign p4 post hl5 (checkerCmp_exhausted_lbl img) s4 hpc4' hs4gp
  let ws02 : List (Int × BitVec 64) := [(checkerTabMini.dbase 0, solBase), (checkerTabMini.dlen 0, solLenBv)]
  have hs1m' : s1.mem = writeWord64 st.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 0)) solBase := by
    rw [hm1, hgp, hs3]
  have hs2m' : s2.mem = writeWord64 s1.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 0)) solLenBv := by
    rw [hm2, hs1gp, hs1s4]
  have hs2mEq : s2.mem = applyTabWrites regionBase st.mem ws02 := by
    rw [hs2m', hs1m']; simp only [ws02, applyTabWrites]
  have hs4mEq : s4.mem = applyTabWrites regionBase s3.mem [(checkerTabMini.globOff modeGVar, 5#64)] := by
    rw [hm4]; simp only [applyTabWrites]
  have hout04 : ProgMemOutside (cmp5WriteSpan regionBase) st.mem s4.mem := by
    have h02 : ProgMemOutside (cmp5WriteSpan regionBase) st.mem s2.mem := by
      rw [hs2mEq]
      refine progMemOutside_applyTabWrites ws02 (fun e he k hk => ?_) st.mem
      simp only [ws02, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · rw [dbase_bv]; exact Or.inr (Or.inl ⟨k, hk, rfl⟩)
      · rw [dlen_bv]; exact Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩))
    have h23 : ProgMemOutside (cmp5WriteSpan regionBase) s2.mem s3.mem :=
      ProgMemOutside.of_memEqOutside (fun _ h => Or.inl h) hout3
    have h34 : ProgMemOutside (cmp5WriteSpan regionBase) s3.mem s4.mem := by
      rw [hm4]
      exact progMemOutside_writeWord64_of_sub fun k hk => Or.inr (Or.inr (Or.inr ⟨k, hk, rfl⟩))
    exact h02.trans (h23.trans h34)
  have hm5Eq : s5.mem = s4.mem := hm5
  have hgbMode := globOff_bound (g := modeGVar) (by decide)
  have hrGe := resBase_ge_16
  have hmodeOff : checkerTabMini.globOff modeGVar =
      ((checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + modeGVar.id) : Nat) : Int) :=
    globOff_eq_nat modeGVar
  have hmodeOk : tabOffOk (checkerTabMini.globOff modeGVar) :=
    ⟨by rw [hmodeOff]; omega, by rw [hmodeOff, Int.toNat_natCast]; exact hgbMode⟩
  have hdb0Eq : checkerTabMini.dbase 0 = 16 := by simp [Tab.dbase]
  have hdl0Eq : checkerTabMini.dlen 0 = 1656 := by simp [Tab.dlen, t_nb, t_nw]
  have hdb0Ok : tabOffOk (checkerTabMini.dbase 0) :=
    ⟨by rw [hdb0Eq]; omega, by rw [hdb0Eq]; simp [abiSlot]⟩
  have hdl0Ok : tabOffOk (checkerTabMini.dlen 0) :=
    ⟨by rw [hdl0Eq]; omega, by rw [hdl0Eq]; simp [abiSlot]⟩
  have h0B : readWord64 s4.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 0)) = solBase := by
    have e34 : readWord64 s4.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 0)) =
        readWord64 s3.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 0)) := by
      rw [hs4mEq]
      exact readWord64_applyTabWrites_disj hR hdb0Ok _ (fun e he => by
        simp only [List.mem_singleton] at he; subst he
        exact ⟨hmodeOk, Or.inl (by rw [hdb0Eq, hmodeOff, Int.toNat_natCast]; omega)⟩) _
    have e23 : readWord64 s3.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 0)) =
        readWord64 s2.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 0)) := by
      rw [dbase_bv, Nat.mul_zero, Nat.add_zero]
      exact MemEqOutside.readWord64_eq hout3 _ fun k hk hc =>
        memSpan_offset_disjoint_contains_false hR (by simp [abiSlot] : 16 + 8 ≤ abiSlot)
          (by simp [abiSlot] : 0 + 16 ≤ abiSlot) (Or.inr (by omega))
          ⟨k, hk, rfl⟩ (by simpa only [BitVec.add_zero] using hc)
    have e12 : readWord64 s2.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 0)) =
        readWord64 s1.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 0)) := by
      have hm2' : s2.mem = applyTabWrites regionBase s1.mem [(checkerTabMini.dlen 0, solLenBv)] := by
        rw [hs2m']; simp only [applyTabWrites]
      rw [hm2']
      exact readWord64_applyTabWrites_disj hR hdb0Ok _ (fun e he => by
        simp only [List.mem_singleton] at he; subst he
        exact ⟨hdl0Ok, Or.inl (by rw [hdb0Eq, hdl0Eq]; omega)⟩) _
    rw [e34, e23, e12, hs1m', readWord64_writeWord64_self]
  have h0L : readWord64 s4.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 0)) = solLenBv := by
    have e34 : readWord64 s4.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 0)) =
        readWord64 s3.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 0)) := by
      rw [hs4mEq]
      exact readWord64_applyTabWrites_disj hR hdl0Ok _ (fun e he => by
        simp only [List.mem_singleton] at he; subst he
        exact ⟨hmodeOk, Or.inl (by rw [hdl0Eq, hmodeOff, Int.toNat_natCast]; omega)⟩) _
    have e23 : readWord64 s3.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 0)) =
        readWord64 s2.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 0)) := by
      rw [dlen_bv, Nat.mul_zero, Nat.add_zero]
      exact MemEqOutside.readWord64_eq hout3 _ fun k hk hc =>
        memSpan_offset_disjoint_contains_false hR (by simp [abiSlot] : 1656 + 8 ≤ abiSlot)
          (by simp [abiSlot] : 0 + 16 ≤ abiSlot) (Or.inr (by omega))
          ⟨k, hk, rfl⟩ (by simpa only [BitVec.add_zero] using hc)
    rw [e34, e23, hs2m', readWord64_writeWord64_self]
  have hMode5 : readWord64 s4.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) = 5#64 := by
    rw [hm4, readWord64_writeWord64_self]
  have hTop4 : readWord64 s4.mem regionBase = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) := by
    have hz : BitVec.ofInt 64 0 = 0#64 := rfl
    rw [← BitVec.add_zero regionBase, ← hz, hs4mEq]
    rw [readWord64_applyTabWrites_disj hR ⟨by omega, by simp [abiSlot]⟩ _ (fun e he => by
      simp only [List.mem_singleton] at he; subst he
      exact ⟨hmodeOk, Or.inl (by rw [hmodeOff, Int.toNat_natCast]; omega)⟩) _]
    rw [hz, BitVec.add_zero, hTop3]
  have hLim4 : readWord64 s4.mem (regionBase + 8#64) = regionBase + BitVec.ofNat 64 abiSlot := by
    have h8 : BitVec.ofInt 64 8 = 8#64 := rfl
    rw [← h8, hs4mEq]
    rw [readWord64_applyTabWrites_disj hR ⟨by omega, by simp [abiSlot]⟩ _ (fun e he => by
      simp only [List.mem_singleton] at he; subst he
      exact ⟨hmodeOk, Or.inl (by rw [hmodeOff, Int.toNat_natCast]; omega)⟩) _]
    rw [h8, hLim3]
  refine ⟨img.lkm.totalSize cB + img.lkm.totalSize cL + k3 + k4 + k5, s5, ?_, ?_,
    hs5gp, by rw [hs5sp]; exact hTop4,
    hs5s0,
    (hoth5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hoth4 _ (by decide) (by decide)).trans ((hoth3 _ (by decide)).trans
        ((hoth2 _ (by decide)).trans (hoth1 _ (by decide))))),
    hs5t0, hs5t1, by rw [hm5Eq]; exact hout04,
    by rw [hm5Eq]; exact h0B, by rw [hm5Eq]; exact h0L,
    by rw [hm5Eq]; exact hMode5, by rw [hm5Eq]; exact hTop4, by rw [hm5Eq]; exact hLim4⟩
  · rw [run_add, run_add, run_add, run_add, hrun1]; dsimp only; rw [hrun2]
    dsimp only; rw [hrun3]; dsimp only; rw [hrun4]; exact hrun5
  · rw [hpc5]
    exact congrArg (fun n => BitVec.ofNat 64 (4 * n))
      (by dsimp only [p4, p3, p2, p1, cmpDrvMode5Setup, cB, cL]
          simp only [img.lkm.totalSize_append, Nat.add_assoc])

theorem cmpMode5_progMemRel
    {chalBase solBase pinsBase regionBase : BitVec 64}
    {chalLen solLen pinsLen : Nat}
    (hChal64 : chalBase.toNat + chalLen ≤ 2 ^ 64)
    (hSol64 : solBase.toNat + solLen ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pinsLen ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjChalPins : MemSpan.disjoint ⟨chalBase, chalLen⟩ ⟨pinsBase, pinsLen⟩)
    (hDisjChalReg : MemSpan.disjoint ⟨chalBase, chalLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pinsLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjSolPins : MemSpan.disjoint ⟨solBase, solLen⟩ ⟨pinsBase, pinsLen⟩)
    (hDisjSolReg : MemSpan.disjoint ⟨solBase, solLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    {rmem4 rmem5 : ByteMem} {m4 : _root_.L.Mem} {solBytes : ByteArray}
    (hSolSz : solBytes.size = solLen) (hSolLt64 : solLen < 2 ^ 64)
    (hRel4 : ProgMemRel checkerTabMini
      (checkerLayoutA chalBase pinsBase regionBase chalLen pinsLen
        hChal64 hPins64 hRegAlign hReg64 hDisjChalPins hDisjChalReg hDisjPinsReg) rmem4 m4)
    (hSolMem4 : ∀ i, (hi : i < solBytes.size) →
      rmem4 (solBase + BitVec.ofNat 64 i) = solBytes[i].toBitVec)
    (hout : ProgMemOutside (cmp5WriteSpan regionBase) rmem4 rmem5)
    (h0B : readWord64 rmem5 (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 0)) = solBase)
    (h0L : readWord64 rmem5 (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 0)) = BitVec.ofNat 64 solLen)
    (hMode5 : readWord64 rmem5 (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) = 5#64) :
    ProgMemRel checkerTabMini
      (checkerLayoutA solBase pinsBase regionBase solLen pinsLen
        hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg)
      rmem5 (cmpPhase5Mem m4 solBytes) := by
  let LA4 := checkerLayoutA chalBase pinsBase regionBase chalLen pinsLen
    hChal64 hPins64 hRegAlign hReg64 hDisjChalPins hDisjChalReg hDisjPinsReg
  let LA5 := checkerLayoutA solBase pinsBase regionBase solLen pinsLen
    hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg
  have hNeedEq := checkerTabMini_abiNeed_eq
  have h211 : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; simp [abiSlot]
  have houtSlot0 : ProgMemOutside (fun a => (⟨regionBase, abiSlot⟩ : MemSpan).contains a) rmem4 rmem5 :=
    hout.mono (cmp5WriteSpan_sub_slot0 regionBase hReg64)
  rcases hRel4 with ⟨hA8, hA64, hArom, hAg⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases checkerTabMini_bytePos_cases ha with rfl | rfl
    · have hArr : (cmpPhase5Mem m4 solBytes).arr8 inArr = solBytes.data := rfl
      have hcap : LA5.cap8 inArr = solLen := by simp [LA5, checkerLayoutA]
      have hbase : LA5.base8 inArr = solBase := by simp [LA5, checkerLayoutA]
      have hsz : ((cmpPhase5Mem m4 solBytes).arr8 inArr).size = solLen := by
        rw [hArr, ByteArray.size_data]; exact hSolSz
      refine ⟨by rw [hsz, hcap]; exact Nat.le_refl _, by rw [hsz]; exact hSolLt64, ?_, ?_, ?_⟩
      · change readWord64 rmem5 (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen (checkerTabMini.pos8 inArr))) = _
        rw [t_pos8_in, hsz]; exact h0L
      · change readWord64 rmem5 (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase (checkerTabMini.pos8 inArr))) = _
        rw [hbase, t_pos8_in]; exact h0B
      · intro i hi
        have hi' : i < solBytes.size := by rw [hArr, ByteArray.size_data] at hi; exact hi
        have hnot : ¬(⟨regionBase, abiSlot⟩ : MemSpan).contains (LA5.base8 inArr + BitVec.ofNat 64 i) := by
          have hdisjSub : MemSpan.disjoint ⟨solBase, solLen⟩ ⟨regionBase, abiSlot⟩ := by
            dsimp only [MemSpan.disjoint] at hDisjSolReg ⊢; rw [hNeedEq] at hDisjSolReg
            rcases hDisjSolReg with h | h
            · exact Or.inl (by omega)
            · exact Or.inr (by omega)
          rw [hbase]
          exact @MemSpan.disjoint_to_memDisjoint ⟨solBase, solLen⟩ ⟨regionBase, abiSlot⟩
            hSol64 (by dsimp only [MemSpan.valid]; omega) hdisjSub _ ⟨i, hSolSz ▸ hi', rfl⟩
        rw [houtSlot0 _ hnot, hbase, hSolMem4 i hi']
        simp only [hArr]; rfl
    · have hne : pbArr ≠ inArr := by decide
      rcases hA8 pbArr ha with ⟨hcap, hlt, hlen, hbase, hbytes⟩
      have harr : (cmpPhase5Mem m4 solBytes).arr8 pbArr = m4.arr8 pbArr := rfl
      have hcap5 : LA5.cap8 pbArr = LA4.cap8 pbArr := by simp [LA5, LA4, checkerLayoutA, hne]
      have hbase5 : LA5.base8 pbArr = LA4.base8 pbArr := by simp [LA5, LA4, checkerLayoutA, hne]
      have hDisjPb : ∀ k, k < (m4.arr8 pbArr).size →
          ¬(⟨regionBase, abiSlot⟩ : MemSpan).contains (LA4.base8 pbArr + BitVec.ofNat 64 k) := by
        intro k hk hc
        exact MemSpan.disjoint_to_memDisjoint (LA4.arr8Span_valid pbArr) LA4.tabSpan_valid
          (LA4.h8DisjTab pbArr ha) _ ⟨k, Nat.lt_of_lt_of_le hk hcap, rfl⟩ hc
      have hlen5 : readWord64 rmem5 (LA5.T + BitVec.ofInt 64 (checkerTabMini.len8 pbArr)) =
          BitVec.ofNat 64 ((cmpPhase5Mem m4 solBytes).arr8 pbArr).size := by
        have hd : checkerTabMini.len8 pbArr = ((1656 + 8 * 1 : Nat) : Int) := by
          change checkerTabMini.dlen (checkerTabMini.pos8 pbArr) = _
          rw [t_pos8_pb]; simp [Tab.dlen, t_nb, t_nw]
        have hr := resBase_ge_16
        change readWord64 rmem5 (regionBase + BitVec.ofInt 64 (checkerTabMini.len8 pbArr)) = _
        rw [harr, ← hlen]
        apply hout.readWord64_eq
        rw [hd, BitVec.ofInt_natCast]
        exact cmp5WriteSpan_disj_tabOff regionBase hReg64 (by simp [abiSlot] : 1656 + 8 * 1 + 8 ≤ abiSlot)
          (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
      have hbase5' : readWord64 rmem5 (LA5.T + BitVec.ofInt 64 (checkerTabMini.base8 pbArr)) = LA5.base8 pbArr := by
        have hb : checkerTabMini.base8 pbArr = ((16 + 8 * 1 : Nat) : Int) := by
          change checkerTabMini.dbase (checkerTabMini.pos8 pbArr) = _
          rw [t_pos8_pb]; simp [Tab.dbase]
        have hr := resBase_ge_16
        change readWord64 rmem5 (regionBase + BitVec.ofInt 64 (checkerTabMini.base8 pbArr)) = _
        rw [hbase5, ← hbase]
        apply hout.readWord64_eq
        rw [hb, BitVec.ofInt_natCast]
        exact cmp5WriteSpan_disj_tabOff regionBase hReg64 (by simp [abiSlot] : 24 + 8 ≤ abiSlot)
          (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      refine ⟨by rw [harr, hcap5]; exact hcap, by rw [harr]; exact hlt, hlen5, hbase5', fun i hi => ?_⟩
      have hi' : i < (m4.arr8 pbArr).size := by simpa only [harr] using hi
      rw [hbase5, houtSlot0 _ (hDisjPb i hi'), hbytes i hi']
      simp only [harr]
  · intro s hs
    have ⟨hlo, hhi⟩ := checkerTabMini_wordPos_bounds hs
    rcases hA64 s hs with ⟨hcap, hlt, hlen, hbase, hwords⟩
    have hcap5 : LA5.cap64 s = LA4.cap64 s := by simp [LA5, LA4, checkerLayoutA, hs]
    have hbase5 : LA5.base64 s = LA4.base64 s := by simp [LA5, LA4, checkerLayoutA, hs]
    have harrEq : (cmpPhase5Mem m4 solBytes).arr64 s = m4.arr64 s := rfl
    have hr := resBase_ge_16
    have hlen5 : readWord64 rmem5 (LA5.T + BitVec.ofInt 64 (checkerTabMini.len64 s)) =
        BitVec.ofNat 64 ((cmpPhase5Mem m4 solBytes).arr64 s).size := by
      have hd : checkerTabMini.len64 s = ((1656 + 8 * checkerTabMini.pos64 s : Nat) : Int) := by
        change checkerTabMini.dlen (checkerTabMini.pos64 s) = _
        simp only [Tab.dlen, t_nb, t_nw]; omega
      change readWord64 rmem5 (regionBase + BitVec.ofInt 64 (checkerTabMini.len64 s)) = _
      rw [harrEq, ← hlen]
      apply hout.readWord64_eq
      rw [hd, BitVec.ofInt_natCast]
      exact cmp5WriteSpan_disj_tabOff regionBase hReg64 (by simp [abiSlot]; omega)
        (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
    have hbase5' : readWord64 rmem5 (LA5.T + BitVec.ofInt 64 (checkerTabMini.base64 s)) = LA5.base64 s := by
      have hb : checkerTabMini.base64 s = ((16 + 8 * checkerTabMini.pos64 s : Nat) : Int) := by
        change checkerTabMini.dbase (checkerTabMini.pos64 s) = _
        simp only [Tab.dbase]; omega
      change readWord64 rmem5 (regionBase + BitVec.ofInt 64 (checkerTabMini.base64 s)) = _
      rw [hbase5, ← hbase]
      apply hout.readWord64_eq
      rw [hb, BitVec.ofInt_natCast]
      exact cmp5WriteSpan_disj_tabOff regionBase hReg64 (by simp [abiSlot]; omega)
        (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    refine ⟨by rw [harrEq, hcap5]; exact hcap, by rw [harrEq]; exact hlt, hlen5, hbase5', fun i hi => ?_⟩
    simp only [harrEq] at hi ⊢
    rw [hbase5, ← hwords i hi]
    apply houtSlot0.readWord64_eq
    intro k hk ⟨m, hm, hmeq⟩
    dsimp only at hm
    have hbas : LA4.base64 s = regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.pos64 s) := by
      simp [LA4, checkerLayoutA, hs]
    have hcapA : LA4.cap64 s = abiWords := by simp [LA4, checkerLayoutA, hs]
    rw [hbas] at hmeq
    have h8w : 8 * abiWords = abiSlot := by simp [abiWords, abiSlot]
    have hi_lt : i < abiWords := by rw [← hcapA]; exact Nat.lt_of_lt_of_le hi hcap
    have hlo64 : abiSlot * checkerTabMini.pos64 s < 2 ^ 64 := by
      have := Nat.mul_le_mul_left abiSlot hhi; simp [abiSlot] at *; omega
    have hm211 : abiSlot * checkerTabMini.pos64 s + abiSlot ≤ 205 * abiSlot := by
      have := Nat.mul_le_mul_left abiSlot (by omega : checkerTabMini.pos64 s + 1 ≤ 205)
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm abiSlot 205] at this; exact this
    have hsum64 : abiSlot * checkerTabMini.pos64 s + (8 * i + k) < 2 ^ 64 := by omega
    have hrTot64 : regionBase.toNat + (abiSlot * checkerTabMini.pos64 s + (8 * i + k)) < 2 ^ 64 := by omega
    have hm64 : m < 2 ^ 64 := by simp [abiSlot] at hm; omega
    have hrm64 : regionBase.toNat + m < 2 ^ 64 := by omega
    have hadd : regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.pos64 s) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 k =
        regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.pos64 s + (8 * i + k)) := by
      rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    rw [hadd] at hmeq
    have hto := congrArg BitVec.toNat hmeq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hsum64, Nat.mod_eq_of_lt hrTot64,
      Nat.mod_eq_of_lt hm64, Nat.mod_eq_of_lt hrm64] at hto
    have hm2 : abiSlot * 2 ≤ abiSlot * checkerTabMini.pos64 s := Nat.mul_le_mul_left abiSlot hlo
    omega
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
    have hadd0 : LA5.T + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + k) =
        regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + k) + BitVec.ofNat 64 0 := by
      dsimp only [LA5, checkerLayoutA]; rw [BitVec.add_zero]
    rw [hadd0]
    exact cmp5WriteSpan_disj_tabOff regionBase hReg64 hbd (by omega) (Or.inr (by omega))
      (Or.inr (by omega)) (Or.inl (by omega)) 0 (by decide)
  · intro g hg
    by_cases hgm : g = modeGVar
    · subst hgm
      change readWord64 rmem5 (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) = _
      rw [hMode5]
      have hval : (cmpPhase5Mem m4 solBytes).glob modeGVar = 5 := by
        simp [cmpPhase5Mem, cmpM5Mini, _root_.L.Mem.setG]
      rw [hval]; rfl
    · have hgne : g.id ≠ modeGVar.id := by
        intro heq; apply hgm; cases g; simp only at heq; subst heq; rfl
      have hval : (cmpPhase5Mem m4 solBytes).glob g = m4.glob g := by
        simp [cmpPhase5Mem, cmpM5Mini, cmpInMini, _root_.L.Mem.setG, hgm]
      rw [hval, ← hAg g hg]
      apply hout.readWord64_eq
      have hgl := globOff_eq_nat g
      have hgb := globOff_bound hg
      have hr := resBase_ge_16
      have hgl' : BitVec.ofInt 64 (checkerTabMini.globOff g) =
          BitVec.ofNat 64 (checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + g.id)) :=
        globOff_bitvec g
      rw [hgl']
      exact cmp5WriteSpan_disj_tabOff regionBase hReg64 hgb (by omega) (Or.inr (by omega))
        (Or.inr (by omega)) (by omega)

theorem cmpMode6Setup_sim (img : LinkedCmpImage) (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (pre post : List AsmItem)
    (hlink : img.lkm.linkSpec (pre ++ cmpDrvMode6Setup checkerTabMini ++ post) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase) :
    ∃ k st',
      RV64.run (linkedCmpEnv img).rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize (pre ++ cmpDrvMode6Setup checkerTabMini)) ∧
      st'.getReg AbiReg.gp = regionBase ∧
      st'.getReg AbiReg.sp = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) ∧
      st'.getReg AbiReg.s0 = BitVec.ofNat 64 (abiFuel - 2) ∧
      st'.getReg AbiReg.s2 = st.getReg AbiReg.s2 ∧
      st'.getReg AbiReg.s5 = st.getReg AbiReg.s5 ∧
      st'.getReg AbiReg.t0 = regionBase + BitVec.ofInt 64 checkerTabMini.args ∧
      st'.getReg AbiReg.t1 = 0#64 ∧
      (∃ stMid, MemEqOutside ⟨regionBase, 16⟩ st.mem stMid ∧
        st'.mem = writeWord64 stMid (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) 6#64) ∧
      readWord64 st'.mem regionBase = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) ∧
      readWord64 st'.mem (regionBase + 8#64) = regionBase + BitVec.ofNat 64 abiSlot := by
  have hNeedEq := checkerTabMini_abiNeed_eq
  have h211 : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; simp [abiSlot]
  have hR : regionBase.toNat + abiSlot ≤ 2 ^ 64 := by omega
  have hl1 : img.lkm.linkSpec (pre ++ drvResetStack ++
      (cmpDrvSetMode 6 checkerTabMini ++ cmpDrvCallPrep checkerTabMini ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [cmpDrvMode6Setup, List.append_assoc] using hlink
  obtain ⟨k1, s1, hrun1, hpc1, hoth1, hout1, hTop1, hLim1⟩ :=
    drvResetStack_sim_gen (linkedCmpEnv img) regionBase hRegAlign pre _ hl1 st hpc hgp
  let p1 := pre ++ drvResetStack
  have hpc1' : s1.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p1) := by
    simpa only [p1, img.lkm.totalSize_append] using hpc1
  have hs1gp : s1.getReg AbiReg.gp = regionBase := (hoth1 _ (by decide)).trans hgp
  have hl2 : img.lkm.linkSpec (p1 ++ cmpDrvSetMode 6 checkerTabMini ++
      (cmpDrvCallPrep checkerTabMini ++ post)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p1, List.append_assoc] using hl1
  obtain ⟨k2, s2, hrun2, hpc2, hs2gp, hoth2, hm2⟩ :=
    cmpDrvSetMode_sim img regionBase hRegAlign hReg64 6 p1 _ hl2 s1 hpc1' hs1gp
  let p2 := p1 ++ cmpDrvSetMode 6 checkerTabMini
  have hpc2' : s2.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize p2) := by
    simpa only [p2, img.lkm.totalSize_append] using hpc2
  have hl3 : img.lkm.linkSpec (p2 ++ cmpDrvCallPrep checkerTabMini ++ post) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [p2, List.append_assoc] using hl2
  obtain ⟨k3, s3, hrun3, hpc3, hm3, hs3gp, hs3sp, hs3s0, hs3t0, hs3t1, hoth3⟩ :=
    linkedCmpDrvCallPrep_sim img regionBase hRegAlign p2 post hl3 (checkerCmp_exhausted_lbl img) s2 hpc2' hs2gp
  have hgbMode := globOff_bound (g := modeGVar) (by decide)
  have hrGe := resBase_ge_16
  have hmodeOff : checkerTabMini.globOff modeGVar =
      ((checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + modeGVar.id) : Nat) : Int) :=
    globOff_eq_nat modeGVar
  have hmodeOk : tabOffOk (checkerTabMini.globOff modeGVar) :=
    ⟨by rw [hmodeOff]; omega, by rw [hmodeOff, Int.toNat_natCast]; exact hgbMode⟩
  have hs2mEq : s2.mem = applyTabWrites regionBase s1.mem [(checkerTabMini.globOff modeGVar, 6#64)] := by
    rw [hm2]; simp only [applyTabWrites]
  have hTop2 : readWord64 s2.mem regionBase = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) := by
    have hz : BitVec.ofInt 64 0 = 0#64 := rfl
    rw [← BitVec.add_zero regionBase, ← hz, hs2mEq]
    rw [readWord64_applyTabWrites_disj hR ⟨by omega, by simp [abiSlot]⟩ _ (fun e he => by
      simp only [List.mem_singleton] at he; subst he
      exact ⟨hmodeOk, Or.inl (by rw [hmodeOff, Int.toNat_natCast]; omega)⟩) _]
    rw [hz, BitVec.add_zero, hTop1]
  have hLim2 : readWord64 s2.mem (regionBase + 8#64) = regionBase + BitVec.ofNat 64 abiSlot := by
    have h8 : BitVec.ofInt 64 8 = 8#64 := rfl
    rw [← h8, hs2mEq]
    rw [readWord64_applyTabWrites_disj hR ⟨by omega, by simp [abiSlot]⟩ _ (fun e he => by
      simp only [List.mem_singleton] at he; subst he
      exact ⟨hmodeOk, Or.inl (by rw [hmodeOff, Int.toNat_natCast]; omega)⟩) _]
    rw [h8, hLim1]
  refine ⟨k1 + k2 + k3, s3, ?_, ?_, hs3gp,
    by rw [hs3sp]; exact hTop2,
    hs3s0,
    (hoth3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hoth2 _ (by decide) (by decide)).trans (hoth1 _ (by decide))),
    (hoth3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hoth2 _ (by decide) (by decide)).trans (hoth1 _ (by decide))),
    hs3t0, hs3t1, ⟨s1.mem, hout1, by rw [hm3, hm2]⟩,
    by rw [hm3]; exact hTop2, by rw [hm3]; exact hLim2⟩
  · rw [run_add, run_add, hrun1]; dsimp only; rw [hrun2]; exact hrun3
  · rw [hpc3]
    exact congrArg (fun n => BitVec.ofNat 64 (4 * n))
      (by dsimp only [p2, p1, cmpDrvMode6Setup]
          simp only [img.lkm.totalSize_append, Nat.add_assoc])

theorem cmpMode6_progMemRel
    {solBase pinsBase regionBase : BitVec 64} {solLen pinsLen : Nat}
    (hSol64 : solBase.toNat + solLen ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pinsLen ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjSolPins : MemSpan.disjoint ⟨solBase, solLen⟩ ⟨pinsBase, pinsLen⟩)
    (hDisjSolReg : MemSpan.disjoint ⟨solBase, solLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pinsLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    {rmem5 rmemMid rmem6 : ByteMem} {m5 : _root_.L.Mem}
    (hRel5 : ProgMemRel checkerTabMini
      (checkerLayoutA solBase pinsBase regionBase solLen pinsLen
        hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg) rmem5 m5)
    (houtMid : MemEqOutside ⟨regionBase, 16⟩ rmem5 rmemMid)
    (hm6 : rmem6 = writeWord64 rmemMid (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) 6#64) :
    ProgMemRel checkerTabMini
      (checkerLayoutA solBase pinsBase regionBase solLen pinsLen
        hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg)
      rmem6 (cmpPhase6Mem m5) := by
  let LA := checkerLayoutA solBase pinsBase regionBase solLen pinsLen
    hSol64 hPins64 hRegAlign hReg64 hDisjSolPins hDisjSolReg hDisjPinsReg
  have hNeedEq := checkerTabMini_abiNeed_eq
  have h211 : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; simp [abiSlot]
  have hR : regionBase.toNat + abiSlot ≤ 2 ^ 64 := by omega
  have hgbMode := globOff_bound (g := modeGVar) (by decide)
  have hr := resBase_ge_16
  have houtSlot0 : MemEqOutside ⟨regionBase, abiSlot⟩ rmem5 rmem6 := by
    have h0 : MemEqOutside ⟨regionBase, abiSlot⟩ rmem5 rmemMid :=
      memEqOutside_mono (by
        have hsub := memSpan_offset_sub_slot0 regionBase hReg64 (by simp [abiSlot] : 0 + 16 ≤ abiSlot)
        simpa only [BitVec.add_zero] using hsub) houtMid
    have h1 : MemEqOutside ⟨regionBase, abiSlot⟩ rmemMid rmem6 := by
      rw [hm6, globOff_bitvec]
      exact memEqOutside_mono (memSpan_offset_sub_slot0 regionBase hReg64 hgbMode)
        (memEqOutside_writeWord64_tabOff rmemMid regionBase _ 6#64)
    exact h0.trans h1
  have readWord_pres : ∀ {lo : Nat}, lo + 8 ≤ abiSlot → 16 ≤ lo →
      (lo + 8 ≤ checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + modeGVar.id) ∨
       checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + modeGVar.id) + 8 ≤ lo) →
      readWord64 rmem6 (regionBase + BitVec.ofNat 64 lo) = readWord64 rmem5 (regionBase + BitVec.ofNat 64 lo) := by
    intro lo hle h16 hdisj
    have e1 : readWord64 rmem6 (regionBase + BitVec.ofNat 64 lo) =
        readWord64 rmemMid (regionBase + BitVec.ofNat 64 lo) := by
      rw [hm6, globOff_bitvec]
      exact MemEqOutside.readWord64_eq (memEqOutside_writeWord64_tabOff rmemMid regionBase _ 6#64)
        _ fun k hk hc => memSpan_offset_disjoint_contains_false hR hle hgbMode hdisj ⟨k, hk, rfl⟩ hc
    have e0 : readWord64 rmemMid (regionBase + BitVec.ofNat 64 lo) =
        readWord64 rmem5 (regionBase + BitVec.ofNat 64 lo) :=
      MemEqOutside.readWord64_eq houtMid _ fun k hk hc =>
        memSpan_offset_disjoint_contains_false hR hle (by simp [abiSlot] : 0 + 16 ≤ abiSlot)
          (Or.inr h16) ⟨k, hk, rfl⟩ (by simpa only [BitVec.add_zero] using hc)
    rw [e1, e0]
  rcases hRel5 with ⟨hA8, hA64, hArom, hAg⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases hA8 a ha with ⟨hcap, hlt, hlen, hbase, hbytes⟩
    have hpos8lt : checkerTabMini.pos8 a < 2 := by
      have hlt' := (Tab.bytePosOk_lt ha).1; rw [t_nb] at hlt'; exact hlt'
    have hDisj8 : ∀ k, k < (m5.arr8 a).size →
        ¬(⟨regionBase, abiSlot⟩ : MemSpan).contains (LA.base8 a + BitVec.ofNat 64 k) := by
      intro k hk hc
      exact MemSpan.disjoint_to_memDisjoint (LA.arr8Span_valid a) LA.tabSpan_valid (LA.h8DisjTab a ha) _
        ⟨k, Nat.lt_of_lt_of_le hk hcap, rfl⟩ hc
    have harr8 : (cmpPhase6Mem m5).arr8 a = m5.arr8 a := rfl
    refine ⟨by rw [harr8]; exact hcap, by rw [harr8]; exact hlt, ?_, ?_, fun i hi => ?_⟩
    · rw [harr8, ← hlen]; change readWord64 rmem6 (regionBase + BitVec.ofInt 64 (checkerTabMini.len8 a)) = _
      have hd : checkerTabMini.len8 a = ((1656 + 8 * checkerTabMini.pos8 a : Nat) : Int) := by
        change checkerTabMini.dlen (checkerTabMini.pos8 a) = _; simp [Tab.dlen, t_nb, t_nw]
      rw [hd, BitVec.ofInt_natCast]
      exact readWord_pres (by simp [abiSlot]; omega) (by omega) (Or.inl (by omega))
    · rw [← hbase]; change readWord64 rmem6 (regionBase + BitVec.ofInt 64 (checkerTabMini.base8 a)) = _
      have hb : checkerTabMini.base8 a = ((16 + 8 * checkerTabMini.pos8 a : Nat) : Int) := by
        change checkerTabMini.dbase (checkerTabMini.pos8 a) = _; simp [Tab.dbase]
      rw [hb, BitVec.ofInt_natCast]
      exact readWord_pres (by simp [abiSlot]; omega) (by omega) (Or.inl (by omega))
    · have hi' : i < (m5.arr8 a).size := hi
      rw [houtSlot0 _ (hDisj8 i hi'), hbytes i hi']
      simp only [harr8]
  · intro s hs
    have ⟨hlo, hhi⟩ := checkerTabMini_wordPos_bounds hs
    rcases hA64 s hs with ⟨hcap, hlt, hlen, hbase, hwords⟩
    have harr64 : (cmpPhase6Mem m5).arr64 s = m5.arr64 s := rfl
    refine ⟨by rw [harr64]; exact hcap, by rw [harr64]; exact hlt, ?_, ?_, fun i hi => ?_⟩
    · rw [harr64, ← hlen]; change readWord64 rmem6 (regionBase + BitVec.ofInt 64 (checkerTabMini.len64 s)) = _
      have hd : checkerTabMini.len64 s = ((1656 + 8 * checkerTabMini.pos64 s : Nat) : Int) := by
        change checkerTabMini.dlen (checkerTabMini.pos64 s) = _; simp only [Tab.dlen, t_nb, t_nw]; omega
      rw [hd, BitVec.ofInt_natCast]
      exact readWord_pres (by simp [abiSlot]; omega) (by omega) (Or.inl (by omega))
    · rw [← hbase]; change readWord64 rmem6 (regionBase + BitVec.ofInt 64 (checkerTabMini.base64 s)) = _
      have hb : checkerTabMini.base64 s = ((16 + 8 * checkerTabMini.pos64 s : Nat) : Int) := by
        change checkerTabMini.dbase (checkerTabMini.pos64 s) = _; simp [Tab.dbase]
      rw [hb, BitVec.ofInt_natCast]
      exact readWord_pres (by simp [abiSlot]; omega) (by omega) (Or.inl (by omega))
    · have hi' : i < (m5.arr64 s).size := hi
      simp only [harr64]
      rw [← hwords i hi']
      apply houtSlot0.readWord64_eq
      intro k hk ⟨m, hm, hmeq⟩
      dsimp only at hm
      have hbas : LA.base64 s = regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.pos64 s) := by
        simp [LA, checkerLayoutA, hs]
      have hcapA : LA.cap64 s = abiWords := by simp [LA, checkerLayoutA, hs]
      rw [hbas] at hmeq
      have h8w : 8 * abiWords = abiSlot := by simp [abiWords, abiSlot]
      have hi_lt : i < abiWords := by rw [← hcapA]; exact Nat.lt_of_lt_of_le hi hcap
      have hlo64 : abiSlot * checkerTabMini.pos64 s < 2 ^ 64 := by
        have := Nat.mul_le_mul_left abiSlot hhi; simp [abiSlot] at *; omega
      have hm211 : abiSlot * checkerTabMini.pos64 s + abiSlot ≤ 205 * abiSlot := by
        have := Nat.mul_le_mul_left abiSlot (by omega : checkerTabMini.pos64 s + 1 ≤ 205)
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm abiSlot 205] at this; exact this
      have hsum64 : abiSlot * checkerTabMini.pos64 s + (8 * i + k) < 2 ^ 64 := by omega
      have hrTot64 : regionBase.toNat + (abiSlot * checkerTabMini.pos64 s + (8 * i + k)) < 2 ^ 64 := by omega
      have hm64 : m < 2 ^ 64 := by simp [abiSlot] at hm; omega
      have hrm64 : regionBase.toNat + m < 2 ^ 64 := by omega
      have hadd : regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.pos64 s) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 k =
          regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.pos64 s + (8 * i + k)) := by
        rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
      rw [hadd] at hmeq
      have hto := congrArg BitVec.toNat hmeq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hsum64, Nat.mod_eq_of_lt hrTot64,
        Nat.mod_eq_of_lt hm64, Nat.mod_eq_of_lt hrm64] at hto
      have hm2 : abiSlot * 2 ≤ abiSlot * checkerTabMini.pos64 s := Nat.mul_le_mul_left abiSlot hlo
      omega
  · intro k hk
    rw [← hArom k hk]
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
    have hLAT : LA.T = regionBase := by simp [LA, checkerLayoutA]
    have e1 : rmem6 (LA.T + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + k)) =
        rmemMid (LA.T + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + k)) := by
      rw [hm6, globOff_bitvec, hLAT]
      exact memEqOutside_writeWord64_tabOff rmemMid regionBase
        (checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + modeGVar.id)) 6#64 _ fun hc =>
        memSpan_offset_disjoint_contains_false hR hbd hgbMode (Or.inl (by omega))
          ⟨0, Nat.zero_lt_one, by rw [BitVec.add_zero]⟩ hc
    have e0 : rmemMid (LA.T + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + k)) =
        rmem5 (LA.T + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + k)) := by
      rw [hLAT]
      exact houtMid _ fun hc =>
        memSpan_offset_disjoint_contains_false hR hbd (by simp [abiSlot] : 0 + 16 ≤ abiSlot) (Or.inr (by omega))
          ⟨0, Nat.zero_lt_one, by rw [BitVec.add_zero]⟩ (by simpa only [BitVec.add_zero] using hc)
    rw [e1, e0]
  · intro g hg
    by_cases hgm : g = modeGVar
    · subst hgm
      change readWord64 rmem6 (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) = _
      rw [hm6, readWord64_writeWord64_self]; simp [cmpPhase6Mem, _root_.L.Mem.setG]
    · have hgne : g.id ≠ modeGVar.id := by
        intro heq; apply hgm; cases g; simp only at heq; subst heq; rfl
      have hval : (cmpPhase6Mem m5).glob g = m5.glob g := by
        simp [cmpPhase6Mem, _root_.L.Mem.setG, hgm]
      rw [hval, ← hAg g hg]
      have hgl' := globOff_bitvec g
      have hgb := globOff_bound hg
      change readWord64 rmem6 (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff g)) =
        readWord64 rmem5 (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff g))
      rw [hgl']
      exact readWord_pres hgb (by omega) (by omega)


end ConAgua.RISCV.Bridge
