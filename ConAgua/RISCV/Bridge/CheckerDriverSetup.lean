import ConAgua.RISCV.Bridge.CheckerDriverSetupA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Phase B Setup and Memory-Relation Transport (`ConAgua.RISCV.Bridge.CheckerDriverSetup`)
-/

namespace ConAgua.RISCV.Bridge

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Compiler
open ConAgua.RISCV.Linker

/-! ## 3. Phase B Descriptor Clear, Setup Simulation, and `ProgMemRel` Transport -/

theorem drvClearDesc_sim_gen {lkm : LinkModel} (env : CodeEnvGen lkm) (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (pos : Nat) (_hpos : pos < 205)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ drvClearDesc checkerTabMini pos ++ post) =
      .ok (env.code, env.labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre +
        lkm.totalSize (drvClearDesc checkerTabMini pos))) ∧
      (∀ q, q ≠ AbiReg.t0 → st'.getReg q = st.getReg q) ∧
      st'.mem =
        writeWord64
          (writeWord64
            (writeWord64 st.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase pos)) 0#64)
            (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen pos)) 0#64)
          (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen32 pos)) 0#64 := by
  let cB := storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (checkerTabMini.dbase pos)
  let cL := storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (checkerTabMini.dlen pos)
  let cL32 := storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (checkerTabMini.dlen32 pos)
  have hl1 : lkm.linkSpec (pre ++ cB ++ (cL ++ cL32 ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [drvClearDesc, cB, cL, cL32, List.append_assoc] using hlink
  have hpc1_64 := linkResolved_sub_pc64 env pre cB _ hl1
  have hal1 : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.dbase pos)) 8 = true := by
    rw [hgp]
    have hBase : BitVec.ofInt 64 (checkerTabMini.dbase pos) = BitVec.ofNat 64 (16 + 8 * pos) := by
      simp [Tab.dbase]
      rw [show (16 + 8 * (pos : Int)) = ((16 + 8 * pos : Nat) : Int) from by omega, BitVec.ofInt_natCast]
    rw [hBase]; exact isAligned8_add_nat_mul8 regionBase hRegAlign _ (by omega)
  obtain ⟨s1, hrun1, hoth1, hm1, hpc1⟩ :=
    storeMemOff_sd_correct_lm lkm env.hrom pre _ AbiReg.gp AbiReg.zero AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.dbase pos) hl1 hpc1_64 st hpc hal1
  let p1 := pre ++ cB
  have hpc1' : s1.pc = BitVec.ofNat 64 (4 * lkm.totalSize p1) := by
    simpa only [p1, lkm.totalSize_append] using hpc1
  have hs1gp : s1.getReg AbiReg.gp = regionBase := (hoth1 _ (by decide)).trans hgp
  have hl2 : lkm.linkSpec (p1 ++ cL ++ (cL32 ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p1, List.append_assoc] using hl1
  have hpc2_64 := linkResolved_sub_pc64 env p1 cL _ hl2
  have hal2 : isAligned (s1.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.dlen pos)) 8 = true := by
    rw [hs1gp, dlen_bv]; exact isAligned8_add_nat_mul8 regionBase hRegAlign _ (by omega)
  obtain ⟨s2, hrun2, hoth2, hm2, hpc2⟩ :=
    storeMemOff_sd_correct_lm lkm env.hrom p1 _ AbiReg.gp AbiReg.zero AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.dlen pos) hl2 hpc2_64 s1 hpc1' hal2
  let p2 := p1 ++ cL
  have hpc2' : s2.pc = BitVec.ofNat 64 (4 * lkm.totalSize p2) := by
    simpa only [p2, lkm.totalSize_append] using hpc2
  have hs2gp : s2.getReg AbiReg.gp = regionBase := (hoth2 _ (by decide)).trans hs1gp
  have hl3 : lkm.linkSpec (p2 ++ cL32 ++ post) =
      .ok (env.code, env.labels) := by
    simpa only [p2, List.append_assoc] using hl2
  have hpc3_64 := linkResolved_sub_pc64 env p2 cL32 post hl3
  have hal3 : isAligned (s2.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.dlen32 pos)) 8 = true := by
    rw [hs2gp, dlen32_bv]; exact isAligned8_add_nat_mul8 regionBase hRegAlign _ (by omega)
  obtain ⟨s3, hrun3, hoth3, hm3, hpc3⟩ :=
    storeMemOff_sd_correct_lm lkm env.hrom p2 post AbiReg.gp AbiReg.zero AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.dlen32 pos) hl3 hpc3_64 s2 hpc2' hal3
  refine ⟨lkm.totalSize cB + lkm.totalSize cL + lkm.totalSize cL32, s3,
    ?_, ?_, fun q hq => (hoth3 q hq).trans ((hoth2 q hq).trans (hoth1 q hq)), ?_⟩
  · rw [run_add, run_add, hrun1]; dsimp only; rw [hrun2]; exact hrun3
  · rw [hpc3]; dsimp only [p2, p1, drvClearDesc, cB, cL, cL32]
    simp only [lkm.totalSize_append, Nat.add_assoc]
  · have hz1 : st.getReg AbiReg.zero = 0#64 := getReg_zero st
    have hz2 : s1.getReg AbiReg.zero = 0#64 := getReg_zero s1
    have hz3 : s2.getReg AbiReg.zero = 0#64 := getReg_zero s2
    rw [hm3, hs2gp, hz3, hm2, hs1gp, hz2, hm1, hgp, hz1]

theorem drvClearDesc_sim (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (pos : Nat) (hpos : pos < 205)
    (pre post : List AsmItem)
    (hlink : checkerLM.linkSpec (pre ++ drvClearDesc checkerTabMini pos ++ post) =
      .ok (checkerEnv.code, checkerEnv.labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase) :
    ∃ k st',
      RV64.run checkerEnv.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (checkerLM.totalSize pre +
        checkerLM.totalSize (drvClearDesc checkerTabMini pos))) ∧
      (∀ q, q ≠ AbiReg.t0 → st'.getReg q = st.getReg q) ∧
      st'.mem =
        writeWord64
          (writeWord64
            (writeWord64 st.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase pos)) 0#64)
            (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen pos)) 0#64)
          (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen32 pos)) 0#64 := by
  exact drvClearDesc_sim_gen checkerEnv regionBase hRegAlign pos hpos pre post hlink st hpc hgp

/-- Addresses in slot 0 modified by `drvPhaseBSetup`. -/
def phaseBWriteSpan (regionBase : BitVec 64) (a : BitVec 64) : Prop :=
  (⟨regionBase, 16⟩ : MemSpan).contains a ∨
  (∃ p, (p = 180 ∨ p = 181 ∨ p = 182) ∧
    ((⟨regionBase + BitVec.ofInt 64 (checkerTabMini.dbase p), 8⟩ : MemSpan).contains a ∨
     (⟨regionBase + BitVec.ofInt 64 (checkerTabMini.dlen p), 8⟩ : MemSpan).contains a ∨
     (⟨regionBase + BitVec.ofInt 64 (checkerTabMini.dlen32 p), 8⟩ : MemSpan).contains a)) ∨
  (∃ g : GVar, (g = phiGVar ∨ g = ploGVar ∨ g = modeGVar) ∧
    (⟨regionBase + BitVec.ofInt 64 (checkerTabMini.globOff g), 8⟩ : MemSpan).contains a)

private theorem phaseBWriteSpan_sub_slot0 (regionBase : BitVec 64)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64) :
    ∀ a, phaseBWriteSpan regionBase a → (⟨regionBase, abiSlot⟩ : MemSpan).contains a := by
  intro a ha
  rcases ha with hhdr | ⟨p, hp, hdesc⟩ | ⟨g, hg, hgl⟩
  · exact memSpan_offset_sub_slot0 regionBase hReg64 (by simp [abiSlot] : 0 + 16 ≤ abiSlot)
      _ (by simpa only [BitVec.add_zero] using hhdr)
  · rcases hdesc with h | h | h
    · rw [dbase_bv] at h
      exact memSpan_offset_sub_slot0 regionBase hReg64 (by rcases hp with rfl | rfl | rfl <;> simp [abiSlot]) _ h
    · rw [dlen_bv] at h
      exact memSpan_offset_sub_slot0 regionBase hReg64 (by rcases hp with rfl | rfl | rfl <;> simp [abiSlot]) _ h
    · rw [dlen32_bv] at h
      exact memSpan_offset_sub_slot0 regionBase hReg64 (by rcases hp with rfl | rfl | rfl <;> simp [abiSlot]) _ h
  · rw [globOff_bitvec] at hgl
    have hg12 : g.id < checkerTabMini.ng := by rcases hg with rfl | rfl | rfl <;> decide
    exact memSpan_offset_sub_slot0 regionBase hReg64 (globOff_bound hg12) _ hgl

private theorem phaseBWriteSpan_disj_tabOff (regionBase : BitVec 64)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    {off : Int} (hnn : 0 ≤ off) (hbd : off.toNat + 8 ≤ abiSlot)
    (hnotHdr : 16 ≤ off.toNat)
    (hnotDesc : ∀ p, p = 180 ∨ p = 181 ∨ p = 182 →
      (off.toNat + 8 ≤ (16 + 8 * p) ∨ (16 + 8 * p) + 8 ≤ off.toNat) ∧
      (off.toNat + 8 ≤ (16 + 8 * 205 + 8 * p) ∨ (16 + 8 * 205 + 8 * p) + 8 ≤ off.toNat) ∧
      (off.toNat + 8 ≤ (16 + 16 * 205 + 8 * p) ∨ (16 + 16 * 205 + 8 * p) + 8 ≤ off.toNat))
    (hnotGlob : ∀ g : GVar, g = phiGVar ∨ g = ploGVar ∨ g = modeGVar →
      off.toNat + 8 ≤ checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + g.id) ∨
      checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + g.id) + 8 ≤ off.toNat) :
    ∀ k, k < 8 → ¬phaseBWriteSpan regionBase (regionBase + BitVec.ofInt 64 off + BitVec.ofNat 64 k) := by
  intro k hk hw
  have hNeedEq := checkerTabMini_abiNeed_eq
  have h211 : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; simp [abiSlot]
  have hR : regionBase.toNat + abiSlot ≤ 2 ^ 64 := by omega
  have hoff : BitVec.ofInt 64 off = BitVec.ofNat 64 off.toNat := by
    rw [← Int.toNat_of_nonneg hnn, BitVec.ofInt_natCast]; rfl
  rw [hoff] at hw
  rcases hw with hhdr | ⟨p, hp, hdesc⟩ | ⟨g, hg, hgl⟩
  · exact memSpan_offset_disjoint_contains_false hR hbd (by simp [abiSlot] : 0 + 16 ≤ abiSlot)
      (Or.inr hnotHdr) ⟨k, hk, rfl⟩ (by simpa only [BitVec.add_zero] using hhdr)
  · obtain ⟨hd1, hd2, hd3⟩ := hnotDesc p hp
    rcases hdesc with h | h | h
    · rw [dbase_bv] at h
      have hpb : 16 + 8 * p + 8 ≤ abiSlot := by rcases hp with rfl | rfl | rfl <;> simp [abiSlot]
      exact memSpan_offset_disjoint_contains_false hR hbd hpb hd1 ⟨k, hk, rfl⟩ h
    · rw [dlen_bv] at h
      have hpb : 1656 + 8 * p + 8 ≤ abiSlot := by rcases hp with rfl | rfl | rfl <;> simp [abiSlot]
      exact memSpan_offset_disjoint_contains_false hR hbd hpb
        (by simpa [show 1656 = 16 + 8 * 205 from rfl] using hd2) ⟨k, hk, rfl⟩ h
    · rw [dlen32_bv] at h
      have hpb : 3296 + 8 * p + 8 ≤ abiSlot := by rcases hp with rfl | rfl | rfl <;> simp [abiSlot]
      exact memSpan_offset_disjoint_contains_false hR hbd hpb
        (by simpa [show 3296 = 16 + 16 * 205 from rfl] using hd3) ⟨k, hk, rfl⟩ h
  · rw [globOff_bitvec] at hgl
    have hg12 : g.id < checkerTabMini.ng := by rcases hg with rfl | rfl | rfl <;> decide
    exact memSpan_offset_disjoint_contains_false hR hbd (globOff_bound hg12) (hnotGlob g hg) ⟨k, hk, rfl⟩ hgl

theorem phaseBWriteSpan_disj_callerSave (regionBase : BitVec 64)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64) :
    ∀ i, i < callerSaveRegs.length → ∀ k, k < 8 →
      ¬phaseBWriteSpan regionBase
        (regionBase + BitVec.ofInt 64 (checkerTabMini.saveBase 0) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 k) := by
  intro i hi k hk
  have hlen : callerSaveRegs.length = 16 := rfl
  have hnn : 0 ≤ checkerTabMini.saveBase 0 + ((8 * i : Nat) : Int) := by
    have := checkerTabMini_saveBase_nonneg; omega
  have hleSlot : (checkerTabMini.saveBase 0 + ((8 * i : Nat) : Int)).toNat + 8 ≤ abiSlot := by
    have := checkerTabMini_saveBase_le_abiSlot
    have := checkerTabMini_saveBase_nonneg
    omega
  have hgtArgs : checkerTabMini.args.toNat < (checkerTabMini.saveBase 0 + ((8 * i : Nat) : Int)).toNat := by
    have := checkerTabMini_args_lt_saveBase
    have := checkerTabMini_saveBase_nonneg
    omega
  have hargsNat := checkerTabMini_args_eq
  have hresNat := checkerTabMini_resBase_eq
  have hcast : regionBase + BitVec.ofInt 64 (checkerTabMini.saveBase 0) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 k =
      regionBase + BitVec.ofInt 64 (checkerTabMini.saveBase 0 + ((8 * i : Nat) : Int)) + BitVec.ofNat 64 k := by
    rw [BitVec.add_assoc regionBase _ (BitVec.ofNat 64 (8 * i)),
      ← BitVec.ofInt_natCast (w := 64) (8 * i), ← BitVec.ofInt_add]
  rw [hcast]
  apply phaseBWriteSpan_disj_tabOff regionBase hReg64 hnn hleSlot (by omega)
  · intro p hp
    rcases hp with rfl | rfl | rfl <;> refine ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
  · intro g hg
    have hg12 : g.id < 12 := by rcases hg with rfl | rfl | rfl <;> decide
    have := t_nxres; have := t_ng
    right; omega
  · exact hk

private def drvBPart1 (tab : Tab) : List AsmItem :=
  [Asm.slli AbiReg.t3 AbiReg.a0 1#6,
   Asm.srli AbiReg.t3 AbiReg.t3 1#6] ++
  storeMemOff .sd AbiReg.gp AbiReg.t3 AbiReg.t0 (tab.globOff phiGVar) ++
  storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.globOff ploGVar) ++
  li AbiReg.t1 (BitVec.ofNat 64 2) ++
  storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.globOff modeGVar) ++
  drvResetStack

private def drvBPart2 (tab : Tab) : List AsmItem :=
  drvClearDesc tab 180 ++
  drvClearDesc tab 182 ++
  li AbiReg.t1 (BitVec.ofNat 64 (abiSlot * tab.slotOf 180)) ++
  [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1] ++
  storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.dbase 181) ++
  li AbiReg.t1 (BitVec.ofNat 64 L.Arena.hdrW) ++
  storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.dlen 181) ++
  li AbiReg.t1 (BitVec.ofNat 64 (2 * L.Arena.hdrW)) ++
  storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.dlen32 181)

private def drvBPart3 (tab : Tab) : List AsmItem :=
  li AbiReg.s0 (BitVec.ofNat 64 (abiFuel - 1)) ++
  [Asm.ld AbiReg.sp AbiReg.gp,
   Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
   Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++
  addImmOff AbiReg.t0 AbiReg.gp AbiReg.t2 tab.args ++
  li AbiReg.t1 0#64

private theorem drvPhaseBSetup_eq_parts :
    drvPhaseBSetup checkerTabMini =
      drvBPart1 checkerTabMini ++ drvBPart2 checkerTabMini ++ drvBPart3 checkerTabMini := by
  dsimp only [drvPhaseBSetup, drvBPart1, drvBPart2, drvBPart3]
  rw [t_pos_out, t_pos_hdrf, t_pos_ctlf]
  simp only [List.cons_append, List.nil_append, List.append_assoc]

theorem slli_srli_uint64 (retA : _root_.L.Word) (hretA : 2 ^ 63 ≤ retA.toNat) :
    evalShiftImm .srli (evalShiftImm .slli retA.toBitVec 1#6) 1#6 =
      (retA - 9223372036854775808).toBitVec := by
  have hbv : retA.toBitVec.toNat = retA.toNat := rfl
  rw [slli_srli_clr63 retA.toBitVec (by rw [hbv]; exact hretA), UInt64.toBitVec_sub]
  have h92 : (9223372036854775808 : UInt64).toBitVec = BitVec.ofNat 64 (2 ^ 63) := by
    apply BitVec.eq_of_toNat_eq
    simp only [UInt64.toBitVec_ofNat, BitVec.toNat_ofNat]
  rw [h92]
  apply BitVec.eq_of_toNat_eq
  have hle : BitVec.ofNat 64 (2 ^ 63) ≤ retA.toBitVec := by
    simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
  rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hlt : retA.toNat < 2 ^ 64 := retA.toBitVec.isLt
  omega

private theorem drvB_slli_srli_sim (env : CodeEnvGen checkerLM) (regionBase : BitVec 64)
    (retA : _root_.L.Word) (hretA : 2 ^ 63 ≤ retA.toNat)
    (pre post : List AsmItem)
    (hlink : checkerLM.linkSpec (pre ++ [Asm.slli AbiReg.t3 AbiReg.a0 1#6,
        Asm.srli AbiReg.t3 AbiReg.t3 1#6] ++ post) =
      .ok (env.code, env.labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase)
    (ha0 : st.getReg AbiReg.a0 = retA.toBitVec) :
    ∃ s2,
      RV64.run env.rom 2 st = .cont s2 ∧
      s2.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize (pre ++ [Asm.slli AbiReg.t3 AbiReg.a0 1#6,
        Asm.srli AbiReg.t3 AbiReg.t3 1#6])) ∧
      s2.getReg AbiReg.gp = regionBase ∧
      s2.getReg AbiReg.s2 = st.getReg AbiReg.s2 ∧
      s2.getReg AbiReg.t3 = (retA - 9223372036854775808).toBitVec ∧
      s2.mem = st.mem := by
  let cSlli := Asm.slli AbiReg.t3 AbiReg.a0 1#6
  let cSrli := Asm.srli AbiReg.t3 AbiReg.t3 1#6
  have hl1 : checkerLM.linkSpec (pre ++ [cSlli] ++ ([cSrli] ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [cSlli, cSrli, List.cons_append, List.nil_append, List.append_assoc] using hlink
  have hs1ex : ∃ s1, RV64.run env.rom 1 st = .cont s1 ∧
      s1.pc = BitVec.ofNat 64 (4 * (checkerLM.totalSize pre + 1)) ∧
      s1.getReg AbiReg.t3 = evalShiftImm .slli (st.getReg AbiReg.a0) 1#6 ∧
      (∀ q, q ≠ AbiReg.t3 → s1.getReg q = st.getReg q) ∧
      s1.mem = st.mem :=
    let h := run_shImm_rd_step env pre ([cSrli] ++ post) .slli AbiReg.t3 AbiReg.a0 1#6 (by decide) hl1 st hpc
    ⟨_, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  obtain ⟨s1, hr1, hpc1, ht3_1, hoth1, hm1⟩ := hs1ex
  let p1 := pre ++ [cSlli]
  have hpc1' : s1.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p1) := by
    simpa only [p1, cSlli, Asm.slli, checkerLM.totalSize_append, checkerLM.totalSize_instr] using hpc1
  have hl2 : checkerLM.linkSpec (p1 ++ [cSrli] ++ post) =
      .ok (env.code, env.labels) := by
    simpa only [p1, List.append_assoc] using hl1
  have hs2ex : ∃ s2, RV64.run env.rom 1 s1 = .cont s2 ∧
      s2.pc = BitVec.ofNat 64 (4 * (checkerLM.totalSize p1 + 1)) ∧
      s2.getReg AbiReg.t3 = evalShiftImm .srli (s1.getReg AbiReg.t3) 1#6 ∧
      (∀ q, q ≠ AbiReg.t3 → s2.getReg q = s1.getReg q) ∧
      s2.mem = s1.mem :=
    let h := run_shImm_rd_step env p1 post .srli AbiReg.t3 AbiReg.t3 1#6 (by decide) hl2 s1 hpc1'
    ⟨_, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  obtain ⟨s2, hr2, hpc2, ht3_2, hoth2, hm2⟩ := hs2ex
  refine ⟨s2, by rw [show (2 : Nat) = 1 + 1 from rfl, run_add, hr1]; exact hr2, ?_,
    (hoth2 _ (by decide)).trans ((hoth1 _ (by decide)).trans hgp),
    (hoth2 _ (by decide)).trans (hoth1 _ (by decide)), ?_, hm2.trans hm1⟩
  · rw [hpc2]; exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (by
      simp only [p1, cSlli, Asm.slli, checkerLM.totalSize_append,
        checkerLM.totalSize_cons, checkerLM.totalSize_nil, Nat.add_zero, Nat.add_assoc]; rfl)
  · rw [ht3_2, ht3_1, ha0]
    exact slli_srli_uint64 retA hretA

private theorem drvPhaseBSetup_p1_sim (env : CodeEnvGen checkerLM) (henv : env = checkerEnv) (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (retA : _root_.L.Word) (hretA : 2 ^ 63 ≤ retA.toNat)
    (pre post : List AsmItem)
    (hlink : checkerLM.linkSpec (pre ++ drvBPart1 checkerTabMini ++ post) =
      .ok (env.code, env.labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase)
    (ha0 : st.getReg AbiReg.a0 = retA.toBitVec) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (checkerLM.totalSize pre +
        checkerLM.totalSize (drvBPart1 checkerTabMini))) ∧
      st'.getReg AbiReg.gp = regionBase ∧
      st'.getReg AbiReg.s2 = st.getReg AbiReg.s2 ∧
      ProgMemOutside (phaseBWriteSpan regionBase) st.mem st'.mem ∧
      readWord64 st'.mem regionBase = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) ∧
      readWord64 st'.mem (regionBase + 8#64) = regionBase + BitVec.ofNat 64 abiSlot ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff phiGVar)) =
        (retA - 9223372036854775808).toBitVec ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff ploGVar)) = 0#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) = 2#64 := by
  have hNeedEq := checkerTabMini_abiNeed_eq
  have h211 : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; simp [abiSlot]
  have hR : regionBase.toNat + abiSlot ≤ 2 ^ 64 := by omega
  have hresGe16 : 16 + 24 * 205 ≤ checkerTabMini.resBase.toNat := resBase_ge_16
  have hresMod : checkerTabMini.resBase.toNat % 8 = 0 := by
    rw [checkerTabMini_resBase_eq, Int.toNat_natCast]; omega
  let cShift := [Asm.slli AbiReg.t3 AbiReg.a0 1#6, Asm.srli AbiReg.t3 AbiReg.t3 1#6]
  let cPhiSt := storeMemOff .sd AbiReg.gp AbiReg.t3 AbiReg.t0 (checkerTabMini.globOff phiGVar)
  let cPloSt := storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (checkerTabMini.globOff ploGVar)
  let cModeLi := li AbiReg.t1 (BitVec.ofNat 64 2)
  let cModeSt := storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (checkerTabMini.globOff modeGVar)
  have hl12 : checkerLM.linkSpec (pre ++ cShift ++
      (cPhiSt ++ cPloSt ++ cModeLi ++ cModeSt ++ drvResetStack ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [drvBPart1, cShift, cPhiSt, cPloSt, cModeLi, cModeSt,
      List.cons_append, List.nil_append, List.append_assoc] using hlink
  obtain ⟨s2, hr12, hpc2', hs2gp, hs2_s2, hs2t3, hm12⟩ :=
    drvB_slli_srli_sim env regionBase retA hretA pre _ hl12 st hpc hgp ha0
  let p2 := pre ++ cShift
  have hl3 : checkerLM.linkSpec (p2 ++ cPhiSt ++ (cPloSt ++ cModeLi ++ cModeSt ++ drvResetStack ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p2, List.append_assoc] using hl12
  have hpc3_64 := linkResolved_sub_pc64 env p2 cPhiSt _ hl3
  have halPhi : isAligned (s2.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.globOff phiGVar)) 8 = true := by
    rw [hs2gp, globOff_bitvec]; exact isAligned8_add_nat_mul8 regionBase hRegAlign _ (by omega)
  obtain ⟨s3, hrun3, hoth3, hm3, hpc3⟩ :=
    storeMemOff_sd_correct_lm checkerLM env.hrom p2 _ AbiReg.gp AbiReg.t3 AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.globOff phiGVar) hl3 hpc3_64 s2 hpc2' halPhi
  let p3 := p2 ++ cPhiSt
  have hpc3' : s3.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p3) := by
    simpa only [p3, checkerLM.totalSize_append] using hpc3
  have hs3gp : s3.getReg AbiReg.gp = regionBase := (hoth3 _ (by decide)).trans hs2gp
  have hl4 : checkerLM.linkSpec (p3 ++ cPloSt ++ (cModeLi ++ cModeSt ++ drvResetStack ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p3, List.append_assoc] using hl3
  have hpc4_64 := linkResolved_sub_pc64 env p3 cPloSt _ hl4
  have halPlo : isAligned (s3.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.globOff ploGVar)) 8 = true := by
    rw [hs3gp, globOff_bitvec]; exact isAligned8_add_nat_mul8 regionBase hRegAlign _ (by omega)
  obtain ⟨s4, hrun4, hoth4, hm4, hpc4⟩ :=
    storeMemOff_sd_correct_lm checkerLM env.hrom p3 _ AbiReg.gp AbiReg.zero AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.globOff ploGVar) hl4 hpc4_64 s3 hpc3' halPlo
  let p4 := p3 ++ cPloSt
  have hpc4' : s4.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p4) := by
    simpa only [p4, checkerLM.totalSize_append] using hpc4
  have hs4gp : s4.getReg AbiReg.gp = regionBase := (hoth4 _ (by decide)).trans hs3gp
  have hl5 : checkerLM.linkSpec (p4 ++ cModeLi ++ (cModeSt ++ drvResetStack ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p4, List.append_assoc] using hl4
  have hpc5_64 := linkResolved_sub_pc64 env p4 cModeLi _ hl5
  obtain ⟨s5a, hrun5a, hoth5a, ht1_5a, hm5a, hpc5a⟩ :=
    li_correct_lm checkerLM env.hrom p4 _ AbiReg.t1 (by decide) (BitVec.ofNat 64 2) hl5 hpc5_64 s4 hpc4'
  let p5a := p4 ++ cModeLi
  have hpc5a' : s5a.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p5a) := by
    simpa only [p5a, checkerLM.totalSize_append] using hpc5a
  have hs5agp : s5a.getReg AbiReg.gp = regionBase := (hoth5a _ (by decide)).trans hs4gp
  have hl5b : checkerLM.linkSpec (p5a ++ cModeSt ++ (drvResetStack ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p5a, List.append_assoc] using hl5
  have hpc5b_64 := linkResolved_sub_pc64 env p5a cModeSt _ hl5b
  have halMode : isAligned (s5a.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) 8 = true := by
    rw [hs5agp, globOff_bitvec]; exact isAligned8_add_nat_mul8 regionBase hRegAlign _ (by omega)
  obtain ⟨s5, hrun5b, hoth5b, hm5b, hpc5⟩ :=
    storeMemOff_sd_correct_lm checkerLM env.hrom p5a _ AbiReg.gp AbiReg.t1 AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.globOff modeGVar) hl5b hpc5b_64 s5a hpc5a' halMode
  let p5 := p5a ++ cModeSt
  have hpc5' : s5.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p5) := by
    simpa only [p5, checkerLM.totalSize_append] using hpc5
  have hs5gp : s5.getReg AbiReg.gp = regionBase := (hoth5b _ (by decide)).trans hs5agp
  have hl6 : checkerLM.linkSpec (p5 ++ drvResetStack ++ post) = .ok (env.code, env.labels) := by
    simpa only [p5, List.append_assoc] using hl5b
  obtain ⟨k6, s6, hrun6, hpc6, hoth6, hout6, hHdrTop6, hHdrLim6⟩ :=
    drvResetStack_sim regionBase hRegAlign p5 post (henv ▸ hl6) s5 hpc5' hs5gp
  have hrun6 : RV64.run env.rom k6 s5 = .cont s6 := henv ▸ hrun6
  have hout3 : ProgMemOutside (phaseBWriteSpan regionBase) st.mem s3.mem := by
    rw [hm3, hs2gp, hm12]
    exact progMemOutside_writeWord64_of_sub fun k hk =>
      Or.inr (Or.inr ⟨phiGVar, Or.inl rfl, ⟨k, hk, rfl⟩⟩)
  have hout4 : ProgMemOutside (phaseBWriteSpan regionBase) s3.mem s4.mem := by
    rw [hm4, hs3gp]
    exact progMemOutside_writeWord64_of_sub fun k hk =>
      Or.inr (Or.inr ⟨ploGVar, Or.inr (Or.inl rfl), ⟨k, hk, rfl⟩⟩)
  have hout5 : ProgMemOutside (phaseBWriteSpan regionBase) s4.mem s5.mem := by
    rw [hm5b, hs5agp, hm5a]
    exact progMemOutside_writeWord64_of_sub fun k hk =>
      Or.inr (Or.inr ⟨modeGVar, Or.inr (Or.inr rfl), ⟨k, hk, rfl⟩⟩)
  have hout6' : ProgMemOutside (phaseBWriteSpan regionBase) s5.mem s6.mem :=
    ProgMemOutside.of_memEqOutside (fun _ h => Or.inl h) hout6
  have houtAll := hout3.trans (hout4.trans (hout5.trans hout6'))
  have hPhiOff := globOff_eq_nat phiGVar
  have hPloOff := globOff_eq_nat ploGVar
  have hModeOff := globOff_eq_nat modeGVar
  have hPhiBd := globOff_bound (g := phiGVar) (by decide)
  have hPloBd := globOff_bound (g := ploGVar) (by decide)
  have hModeBd := globOff_bound (g := modeGVar) (by decide)
  have hPhiN : 0 ≤ checkerTabMini.globOff phiGVar := by rw [hPhiOff]; omega
  have hPloN : 0 ≤ checkerTabMini.globOff ploGVar := by rw [hPloOff]; omega
  have hModeN : 0 ≤ checkerTabMini.globOff modeGVar := by rw [hModeOff]; omega
  have hPhiB : (checkerTabMini.globOff phiGVar).toNat + 8 ≤ abiSlot := by rw [hPhiOff, Int.toNat_natCast]; exact hPhiBd
  have hPloB : (checkerTabMini.globOff ploGVar).toNat + 8 ≤ abiSlot := by rw [hPloOff, Int.toNat_natCast]; exact hPloBd
  have hModeB : (checkerTabMini.globOff modeGVar).toNat + 8 ≤ abiSlot := by rw [hModeOff, Int.toNat_natCast]; exact hModeBd
  have hPres6 : ∀ (g : GVar), g = phiGVar ∨ g = ploGVar ∨ g = modeGVar →
      readWord64 s6.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff g)) =
        readWord64 s5.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff g)) := by
    intro g hg
    have hg12 : g.id < checkerTabMini.ng := by rcases hg with rfl | rfl | rfl <;> decide
    have hgEq := globOff_eq_nat g
    have hb : checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + g.id) + 8 ≤ abiSlot := globOff_bound hg12
    apply MemEqOutside.readWord64_eq hout6 _ fun k hk hc => ?_
    rw [globOff_bitvec] at hc
    exact memSpan_offset_disjoint_contains_false hR hb (by simp [abiSlot] : 0 + 16 ≤ abiSlot)
      (Or.inr (by omega)) ⟨k, hk, rfl⟩ (by simpa only [BitVec.add_zero] using hc)
  have hPhiModeD : (checkerTabMini.globOff phiGVar).toNat + 8 ≤ (checkerTabMini.globOff modeGVar).toNat ∨
      (checkerTabMini.globOff modeGVar).toNat + 8 ≤ (checkerTabMini.globOff phiGVar).toNat := by
    have hne : phiGVar.id ≠ modeGVar.id := by decide
    rw [hPhiOff, hModeOff, Int.toNat_natCast, Int.toNat_natCast]; omega
  have hPhiPloD : (checkerTabMini.globOff phiGVar).toNat + 8 ≤ (checkerTabMini.globOff ploGVar).toNat ∨
      (checkerTabMini.globOff ploGVar).toNat + 8 ≤ (checkerTabMini.globOff phiGVar).toNat := by
    have hne : phiGVar.id ≠ ploGVar.id := by decide
    rw [hPhiOff, hPloOff, Int.toNat_natCast, Int.toNat_natCast]; omega
  have hPloModeD : (checkerTabMini.globOff ploGVar).toNat + 8 ≤ (checkerTabMini.globOff modeGVar).toNat ∨
      (checkerTabMini.globOff modeGVar).toNat + 8 ≤ (checkerTabMini.globOff ploGVar).toNat := by
    have hne : ploGVar.id ≠ modeGVar.id := by decide
    rw [hPloOff, hModeOff, Int.toNat_natCast, Int.toNat_natCast]; omega
  have hPhi6 : readWord64 s6.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff phiGVar)) =
      (retA - 9223372036854775808).toBitVec := by
    rw [hPres6 phiGVar (Or.inl rfl), hm5b, hs5agp, hm5a,
      readWord64_writeWord64_tabOff hR hPhiN hModeN hPhiB hModeB hPhiModeD,
      hm4, hs3gp,
      readWord64_writeWord64_tabOff hR hPhiN hPloN hPhiB hPloB hPhiPloD,
      hm3, hs2gp, hs2t3, readWord64_writeWord64_self]
  have hPlo6 : readWord64 s6.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff ploGVar)) = 0#64 := by
    rw [hPres6 ploGVar (Or.inr (Or.inl rfl)), hm5b, hs5agp, hm5a,
      readWord64_writeWord64_tabOff hR hPloN hModeN hPloB hModeB hPloModeD,
      hm4, hs3gp, show s3.getReg AbiReg.zero = 0#64 from getReg_zero s3, readWord64_writeWord64_self]
  have hMode6 : readWord64 s6.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) = 2#64 := by
    rw [hPres6 modeGVar (Or.inr (Or.inr rfl)), hm5b, hs5agp, hm5a, ht1_5a, readWord64_writeWord64_self]
  have hpcEnd : checkerLM.totalSize (p5 ++ drvResetStack) =
      checkerLM.totalSize pre + checkerLM.totalSize (drvBPart1 checkerTabMini) := by
    dsimp only [p5, p5a, p4, p3, p2, drvBPart1, cShift]
    simp only [cPhiSt, cPloSt, cModeLi, cModeSt, checkerLM.totalSize_append,
      checkerLM.totalSize_cons, checkerLM.totalSize_nil, Nat.add_zero, Nat.add_assoc]
  refine ⟨2 + checkerLM.totalSize cPhiSt + checkerLM.totalSize cPloSt +
      checkerLM.totalSize cModeLi + checkerLM.totalSize cModeSt + k6, s6, ?_, ?_,
      (hoth6 _ (by decide)).trans hs5gp,
      (hoth6 _ (by decide)).trans ((hoth5b _ (by decide)).trans ((hoth5a _ (by decide)).trans
        ((hoth4 _ (by decide)).trans ((hoth3 _ (by decide)).trans hs2_s2)))),
      houtAll, hHdrTop6, hHdrLim6, hPhi6, hPlo6, hMode6⟩
  · rw [run_add, run_add, run_add, run_add, run_add, hr12]
    dsimp only; rw [hrun3]; dsimp only; rw [hrun4]; dsimp only; rw [hrun5a]
    dsimp only; rw [hrun5b]; exact hrun6
  · rw [hpc6]; exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (by
      rw [← checkerLM.totalSize_append p5 drvResetStack]; exact hpcEnd)

private theorem drvPhaseBSetup_p2_sim (env : CodeEnvGen checkerLM) (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (pre post : List AsmItem)
    (hlink : checkerLM.linkSpec (pre ++ drvBPart2 checkerTabMini ++ post) =
      .ok (env.code, env.labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (checkerLM.totalSize pre +
        checkerLM.totalSize (drvBPart2 checkerTabMini))) ∧
      st'.getReg AbiReg.gp = regionBase ∧
      st'.getReg AbiReg.s2 = st.getReg AbiReg.s2 ∧
      ProgMemOutside (phaseBWriteSpan regionBase) st.mem st'.mem ∧
      (∀ (off : Int), (off = 0 ∨ off = 8) →
        readWord64 st'.mem (regionBase + BitVec.ofInt 64 off) =
          readWord64 st.mem (regionBase + BitVec.ofInt 64 off)) ∧
      (∀ (g : GVar), g = phiGVar ∨ g = ploGVar ∨ g = modeGVar →
        readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff g)) =
          readWord64 st.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff g))) ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 180)) = 0#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 180)) = 0#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 182)) = 0#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 182)) = 0#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 181)) =
        regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.slotOf 180) ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 181)) =
        BitVec.ofNat 64 L.Arena.hdrW := by
  have hNeedEq := checkerTabMini_abiNeed_eq
  have h211 : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; simp [abiSlot]
  have hR : regionBase.toNat + abiSlot ≤ 2 ^ 64 := by omega
  have hresGe16 : 16 + 24 * 205 ≤ checkerTabMini.resBase.toNat := resBase_ge_16
  have hresMod : checkerTabMini.resBase.toNat % 8 = 0 := by
    rw [checkerTabMini_resBase_eq, Int.toNat_natCast]; omega
  let cClrOut := drvClearDesc checkerTabMini 180
  let cClrCtl := drvClearDesc checkerTabMini 182
  let cHdrBaseLi := li AbiReg.t1 (BitVec.ofNat 64 (abiSlot * checkerTabMini.slotOf 180))
  let cHdrBaseAdd := [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1]
  let cHdrBaseSt := storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (checkerTabMini.dbase 181)
  let cHdrLenLi := li AbiReg.t1 (BitVec.ofNat 64 L.Arena.hdrW)
  let cHdrLenSt := storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (checkerTabMini.dlen 181)
  let cHdrL32Li := li AbiReg.t1 (BitVec.ofNat 64 (2 * L.Arena.hdrW))
  let cHdrL32St := storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (checkerTabMini.dlen32 181)
  have hl7 : checkerLM.linkSpec (pre ++ cClrOut ++
      (cClrCtl ++ cHdrBaseLi ++ cHdrBaseAdd ++ cHdrBaseSt ++
       cHdrLenLi ++ cHdrLenSt ++ cHdrL32Li ++ cHdrL32St ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [drvBPart2, cClrOut, cClrCtl, cHdrBaseLi, cHdrBaseAdd, cHdrBaseSt,
      cHdrLenLi, cHdrLenSt, cHdrL32Li, cHdrL32St, List.append_assoc] using hlink
  obtain ⟨k7, s7, hrun7, hpc7, hoth7, hm7⟩ :=
    drvClearDesc_sim_gen env regionBase hRegAlign 180 (by omega) pre _ hl7 st hpc hgp
  let p7 := pre ++ cClrOut
  have hpc7' : s7.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p7) := by
    simpa only [p7, checkerLM.totalSize_append] using hpc7
  have hs7gp : s7.getReg AbiReg.gp = regionBase := (hoth7 _ (by decide)).trans hgp
  have hl8 : checkerLM.linkSpec (p7 ++ cClrCtl ++
      (cHdrBaseLi ++ cHdrBaseAdd ++ cHdrBaseSt ++
       cHdrLenLi ++ cHdrLenSt ++ cHdrL32Li ++ cHdrL32St ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p7, List.append_assoc] using hl7
  obtain ⟨k8, s8, hrun8, hpc8, hoth8, hm8⟩ :=
    drvClearDesc_sim_gen env regionBase hRegAlign 182 (by omega) p7 _ hl8 s7 hpc7' hs7gp
  let p8 := p7 ++ cClrCtl
  have hpc8' : s8.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p8) := by
    simpa only [p8, checkerLM.totalSize_append] using hpc8
  have hs8gp : s8.getReg AbiReg.gp = regionBase := (hoth8 _ (by decide)).trans hs7gp
  have hl9a : checkerLM.linkSpec (p8 ++ cHdrBaseLi ++
      (cHdrBaseAdd ++ cHdrBaseSt ++ cHdrLenLi ++ cHdrLenSt ++ cHdrL32Li ++ cHdrL32St ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p8, List.append_assoc] using hl8
  have hpc9a_64 := linkResolved_sub_pc64 env p8 cHdrBaseLi _ hl9a
  obtain ⟨s9a, hrun9a, hoth9a, ht1_9a, hm9a, hpc9a⟩ :=
    li_correct_lm checkerLM env.hrom p8 _ AbiReg.t1 (by decide)
      (BitVec.ofNat 64 (abiSlot * checkerTabMini.slotOf 180)) hl9a hpc9a_64 s8 hpc8'
  let p9a := p8 ++ cHdrBaseLi
  have hpc9a' : s9a.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p9a) := by
    simpa only [p9a, checkerLM.totalSize_append] using hpc9a
  have hs9agp : s9a.getReg AbiReg.gp = regionBase := (hoth9a _ (by decide)).trans hs8gp
  have hl9b : checkerLM.linkSpec (p9a ++ [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1] ++
      (cHdrBaseSt ++ cHdrLenLi ++ cHdrLenSt ++ cHdrL32Li ++ cHdrL32St ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p9a, cHdrBaseAdd, List.append_assoc] using hl9a
  obtain ⟨hr9b, hpc9b, ht1_9b, hoth9b, hm9b⟩ :=
    run_alu_rd_step env p9a _ .add AbiReg.t1 AbiReg.gp AbiReg.t1 (by decide) hl9b s9a hpc9a'
  let s9b := stepReg s9a AbiReg.t1 (evalAlu .add (s9a.getReg AbiReg.gp) (s9a.getReg AbiReg.t1))
    (BitVec.ofNat 64 (4 * (checkerLM.totalSize p9a + 1)))
  let p9b := p9a ++ cHdrBaseAdd
  have hpc9b' : s9b.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p9b) := by
    simpa only [p9b, cHdrBaseAdd, checkerLM.totalSize_append, Asm.add, checkerLM.totalSize_instr] using hpc9b
  have hs9bgp : s9b.getReg AbiReg.gp = regionBase := (hoth9b _ (by decide)).trans hs9agp
  have hs9bt1 : s9b.getReg AbiReg.t1 = regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.slotOf 180) := by
    rw [ht1_9b]; change s9a.getReg AbiReg.gp + s9a.getReg AbiReg.t1 = _
    rw [hs9agp, ht1_9a]
  have hl9c : checkerLM.linkSpec (p9b ++ cHdrBaseSt ++
      (cHdrLenLi ++ cHdrLenSt ++ cHdrL32Li ++ cHdrL32St ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p9b, List.append_assoc] using hl9b
  have hpc9c_64 := linkResolved_sub_pc64 env p9b cHdrBaseSt _ hl9c
  have halHB : isAligned (s9b.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.dbase 181)) 8 = true := by
    rw [hs9bgp]
    have hb : BitVec.ofInt 64 (checkerTabMini.dbase 181) = BitVec.ofNat 64 (16 + 8 * 181) := by simp [Tab.dbase]
    rw [hb]; exact isAligned8_add_nat_mul8 regionBase hRegAlign _ (by omega)
  obtain ⟨s9, hrun9c, hoth9c, hm9c, hpc9⟩ :=
    storeMemOff_sd_correct_lm checkerLM env.hrom p9b _ AbiReg.gp AbiReg.t1 AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.dbase 181) hl9c hpc9c_64 s9b hpc9b' halHB
  let p9 := p9b ++ cHdrBaseSt
  have hpc9' : s9.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p9) := by
    simpa only [p9, checkerLM.totalSize_append] using hpc9
  have hs9gp : s9.getReg AbiReg.gp = regionBase := (hoth9c _ (by decide)).trans hs9bgp
  have hl10a : checkerLM.linkSpec (p9 ++ cHdrLenLi ++ (cHdrLenSt ++ cHdrL32Li ++ cHdrL32St ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p9, List.append_assoc] using hl9c
  have hpc10a_64 := linkResolved_sub_pc64 env p9 cHdrLenLi _ hl10a
  obtain ⟨s10a, hrun10a, hoth10a, ht1_10a, hm10a, hpc10a⟩ :=
    li_correct_lm checkerLM env.hrom p9 _ AbiReg.t1 (by decide)
      (BitVec.ofNat 64 L.Arena.hdrW) hl10a hpc10a_64 s9 hpc9'
  let p10a := p9 ++ cHdrLenLi
  have hpc10a' : s10a.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p10a) := by
    simpa only [p10a, checkerLM.totalSize_append] using hpc10a
  have hs10agp : s10a.getReg AbiReg.gp = regionBase := (hoth10a _ (by decide)).trans hs9gp
  have hl10b : checkerLM.linkSpec (p10a ++ cHdrLenSt ++ (cHdrL32Li ++ cHdrL32St ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p10a, List.append_assoc] using hl10a
  have hpc10b_64 := linkResolved_sub_pc64 env p10a cHdrLenSt _ hl10b
  have halHL : isAligned (s10a.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.dlen 181)) 8 = true := by
    rw [hs10agp]
    have hl : BitVec.ofInt 64 (checkerTabMini.dlen 181) = BitVec.ofNat 64 (16 + 8 * 205 + 8 * 181) := by
      simp [Tab.dlen, t_nb, t_nw]
    rw [hl]; exact isAligned8_add_nat_mul8 regionBase hRegAlign _ (by omega)
  obtain ⟨s10, hrun10b, hoth10b, hm10b, hpc10⟩ :=
    storeMemOff_sd_correct_lm checkerLM env.hrom p10a _ AbiReg.gp AbiReg.t1 AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.dlen 181) hl10b hpc10b_64 s10a hpc10a' halHL
  let p10 := p10a ++ cHdrLenSt
  have hpc10' : s10.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p10) := by
    simpa only [p10, checkerLM.totalSize_append] using hpc10
  have hs10gp : s10.getReg AbiReg.gp = regionBase := (hoth10b _ (by decide)).trans hs10agp
  have hl11a : checkerLM.linkSpec (p10 ++ cHdrL32Li ++ (cHdrL32St ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p10, List.append_assoc] using hl10b
  have hpc11a_64 := linkResolved_sub_pc64 env p10 cHdrL32Li _ hl11a
  obtain ⟨s11a, hrun11a, hoth11a, ht1_11a, hm11a, hpc11a⟩ :=
    li_correct_lm checkerLM env.hrom p10 _ AbiReg.t1 (by decide)
      (BitVec.ofNat 64 (2 * L.Arena.hdrW)) hl11a hpc11a_64 s10 hpc10'
  let p11a := p10 ++ cHdrL32Li
  have hpc11a' : s11a.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p11a) := by
    simpa only [p11a, checkerLM.totalSize_append] using hpc11a
  have hs11agp : s11a.getReg AbiReg.gp = regionBase := (hoth11a _ (by decide)).trans hs10gp
  have hl11b : checkerLM.linkSpec (p11a ++ cHdrL32St ++ post) =
      .ok (env.code, env.labels) := by
    simpa only [p11a, List.append_assoc] using hl11a
  have hpc11b_64 := linkResolved_sub_pc64 env p11a cHdrL32St _ hl11b
  have halHL32 : isAligned (s11a.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.dlen32 181)) 8 = true := by
    rw [hs11agp]
    have hl32 : BitVec.ofInt 64 (checkerTabMini.dlen32 181) = BitVec.ofNat 64 (16 + 16 * 205 + 8 * 181) := by
      simp [Tab.dlen32, t_nb, t_nw]
    rw [hl32]; exact isAligned8_add_nat_mul8 regionBase hRegAlign _ (by omega)
  obtain ⟨s11, hrun11b, hoth11b, hm11b, hpc11⟩ :=
    storeMemOff_sd_correct_lm checkerLM env.hrom p11a _ AbiReg.gp AbiReg.t1 AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.dlen32 181) hl11b hpc11b_64 s11a hpc11a' halHL32
  let w181B := regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.slotOf 180)
  let ws : List (Int × BitVec 64) :=
    [(checkerTabMini.dbase 180, 0#64), (checkerTabMini.dlen 180, 0#64), (checkerTabMini.dlen32 180, 0#64),
     (checkerTabMini.dbase 182, 0#64), (checkerTabMini.dlen 182, 0#64), (checkerTabMini.dlen32 182, 0#64),
     (checkerTabMini.dbase 181, w181B),
     (checkerTabMini.dlen 181, BitVec.ofNat 64 L.Arena.hdrW),
     (checkerTabMini.dlen32 181, BitVec.ofNat 64 (2 * L.Arena.hdrW))]
  have hs11Mem : s11.mem = applyTabWrites regionBase st.mem ws := by
    rw [hm11b, hs11agp, ht1_11a, hm11a, hm10b, hs10agp, ht1_10a, hm10a,
      hm9c, hs9bgp, hs9bt1, hm9b, hm9a, hm8, hm7]
    rfl
  have hWriteSpan : ∀ (p : Nat), p = 180 ∨ p = 181 ∨ p = 182 →
      (∀ k, k < 8 → phaseBWriteSpan regionBase (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase p) + BitVec.ofNat 64 k)) ∧
      (∀ k, k < 8 → phaseBWriteSpan regionBase (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen p) + BitVec.ofNat 64 k)) ∧
      (∀ k, k < 8 → phaseBWriteSpan regionBase (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen32 p) + BitVec.ofNat 64 k)) :=
    fun p hp =>
      ⟨fun k hk => Or.inr (Or.inl ⟨p, hp, Or.inl ⟨k, hk, rfl⟩⟩),
       fun k hk => Or.inr (Or.inl ⟨p, hp, Or.inr (Or.inl ⟨k, hk, rfl⟩)⟩),
       fun k hk => Or.inr (Or.inl ⟨p, hp, Or.inr (Or.inr ⟨k, hk, rfl⟩)⟩)⟩
  have houtAll : ProgMemOutside (phaseBWriteSpan regionBase) st.mem s11.mem := by
    rw [hs11Mem]
    apply progMemOutside_applyTabWrites ws
    intro e he
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hWriteSpan 180 (Or.inl rfl)).1
    · exact (hWriteSpan 180 (Or.inl rfl)).2.1
    · exact (hWriteSpan 180 (Or.inl rfl)).2.2
    · exact (hWriteSpan 182 (Or.inr (Or.inr rfl))).1
    · exact (hWriteSpan 182 (Or.inr (Or.inr rfl))).2.1
    · exact (hWriteSpan 182 (Or.inr (Or.inr rfl))).2.2
    · exact (hWriteSpan 181 (Or.inr (Or.inl rfl))).1
    · exact (hWriteSpan 181 (Or.inr (Or.inl rfl))).2.1
    · exact (hWriteSpan 181 (Or.inr (Or.inl rfl))).2.2
  have hb180eq : checkerTabMini.dbase 180 = ((16 + 8 * 180 : Nat) : Int) := by simp [Tab.dbase]
  have hl180eq : checkerTabMini.dlen 180 = ((1656 + 8 * 180 : Nat) : Int) := by
    simp only [Tab.dlen, t_nb, t_nw]; omega
  have hd180eq : checkerTabMini.dlen32 180 = ((3296 + 8 * 180 : Nat) : Int) := by
    simp only [Tab.dlen32, t_nb, t_nw]; omega
  have hb181eq : checkerTabMini.dbase 181 = ((16 + 8 * 181 : Nat) : Int) := by simp [Tab.dbase]
  have hl181eq : checkerTabMini.dlen 181 = ((1656 + 8 * 181 : Nat) : Int) := by
    simp only [Tab.dlen, t_nb, t_nw]; omega
  have hd181eq : checkerTabMini.dlen32 181 = ((3296 + 8 * 181 : Nat) : Int) := by
    simp only [Tab.dlen32, t_nb, t_nw]; omega
  have hb182eq : checkerTabMini.dbase 182 = ((16 + 8 * 182 : Nat) : Int) := by simp [Tab.dbase]
  have hl182eq : checkerTabMini.dlen 182 = ((1656 + 8 * 182 : Nat) : Int) := by
    simp only [Tab.dlen, t_nb, t_nw]; omega
  have hd182eq : checkerTabMini.dlen32 182 = ((3296 + 8 * 182 : Nat) : Int) := by
    simp only [Tab.dlen32, t_nb, t_nw]; omega
  have hb180n : (checkerTabMini.dbase 180).toNat = 16 + 8 * 180 := by rw [hb180eq, Int.toNat_natCast]
  have hl180n : (checkerTabMini.dlen 180).toNat = 1656 + 8 * 180 := by rw [hl180eq, Int.toNat_natCast]
  have hd180n : (checkerTabMini.dlen32 180).toNat = 3296 + 8 * 180 := by rw [hd180eq, Int.toNat_natCast]
  have hb181n : (checkerTabMini.dbase 181).toNat = 16 + 8 * 181 := by rw [hb181eq, Int.toNat_natCast]
  have hl181n : (checkerTabMini.dlen 181).toNat = 1656 + 8 * 181 := by rw [hl181eq, Int.toNat_natCast]
  have hd181n : (checkerTabMini.dlen32 181).toNat = 3296 + 8 * 181 := by rw [hd181eq, Int.toNat_natCast]
  have hb182n : (checkerTabMini.dbase 182).toNat = 16 + 8 * 182 := by rw [hb182eq, Int.toNat_natCast]
  have hl182n : (checkerTabMini.dlen 182).toNat = 1656 + 8 * 182 := by rw [hl182eq, Int.toNat_natCast]
  have hd182n : (checkerTabMini.dlen32 182).toNat = 3296 + 8 * 182 := by rw [hd182eq, Int.toNat_natCast]
  have hb180ok : tabOffOk (checkerTabMini.dbase 180) := ⟨by rw [hb180eq]; omega, by rw [hb180n]; simp [abiSlot]⟩
  have hl180ok : tabOffOk (checkerTabMini.dlen 180) := ⟨by rw [hl180eq]; omega, by rw [hl180n]; simp [abiSlot]⟩
  have hd180ok : tabOffOk (checkerTabMini.dlen32 180) := ⟨by rw [hd180eq]; omega, by rw [hd180n]; simp [abiSlot]⟩
  have hb181ok : tabOffOk (checkerTabMini.dbase 181) := ⟨by rw [hb181eq]; omega, by rw [hb181n]; simp [abiSlot]⟩
  have hl181ok : tabOffOk (checkerTabMini.dlen 181) := ⟨by rw [hl181eq]; omega, by rw [hl181n]; simp [abiSlot]⟩
  have hd181ok : tabOffOk (checkerTabMini.dlen32 181) := ⟨by rw [hd181eq]; omega, by rw [hd181n]; simp [abiSlot]⟩
  have hb182ok : tabOffOk (checkerTabMini.dbase 182) := ⟨by rw [hb182eq]; omega, by rw [hb182n]; simp [abiSlot]⟩
  have hl182ok : tabOffOk (checkerTabMini.dlen 182) := ⟨by rw [hl182eq]; omega, by rw [hl182n]; simp [abiSlot]⟩
  have hd182ok : tabOffOk (checkerTabMini.dlen32 182) := ⟨by rw [hd182eq]; omega, by rw [hd182n]; simp [abiSlot]⟩
  have hPresGen : ∀ {off : Int}, tabOffOk off →
      (off.toNat + 8 ≤ 16 ∨ 16 + 24 * 205 ≤ off.toNat) →
      readWord64 s11.mem (regionBase + BitVec.ofInt 64 off) =
        readWord64 st.mem (regionBase + BitVec.ofInt 64 off) := by
    intro off hoff hdisj
    rw [hs11Mem]
    apply readWord64_applyTabWrites_disj hR hoff ws _ st.mem
    intro e he
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨hb180ok, by rcases hdisj with h | h <;> first | exact Or.inl (by omega) | exact Or.inr (by omega)⟩
    · exact ⟨hl180ok, by rcases hdisj with h | h <;> first | exact Or.inl (by omega) | exact Or.inr (by omega)⟩
    · exact ⟨hd180ok, by rcases hdisj with h | h <;> first | exact Or.inl (by omega) | exact Or.inr (by omega)⟩
    · exact ⟨hb182ok, by rcases hdisj with h | h <;> first | exact Or.inl (by omega) | exact Or.inr (by omega)⟩
    · exact ⟨hl182ok, by rcases hdisj with h | h <;> first | exact Or.inl (by omega) | exact Or.inr (by omega)⟩
    · exact ⟨hd182ok, by rcases hdisj with h | h <;> first | exact Or.inl (by omega) | exact Or.inr (by omega)⟩
    · exact ⟨hb181ok, by rcases hdisj with h | h <;> first | exact Or.inl (by omega) | exact Or.inr (by omega)⟩
    · exact ⟨hl181ok, by rcases hdisj with h | h <;> first | exact Or.inl (by omega) | exact Or.inr (by omega)⟩
    · exact ⟨hd181ok, by rcases hdisj with h | h <;> first | exact Or.inl (by omega) | exact Or.inr (by omega)⟩
  have hTabHdrPres : ∀ (off : Int), (off = 0 ∨ off = 8) →
      readWord64 s11.mem (regionBase + BitVec.ofInt 64 off) =
        readWord64 st.mem (regionBase + BitVec.ofInt 64 off) := fun off hoff =>
    hPresGen ⟨by rcases hoff with rfl | rfl <;> omega, by rcases hoff with rfl | rfl <;> simp [abiSlot]⟩
      (Or.inl (by rcases hoff with rfl | rfl <;> omega))
  have hGlobPres : ∀ (g : GVar), g = phiGVar ∨ g = ploGVar ∨ g = modeGVar →
      readWord64 s11.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff g)) =
        readWord64 st.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff g)) := by
    intro g hg
    have hg12 : g.id < checkerTabMini.ng := by rcases hg with rfl | rfl | rfl <;> decide
    have hgEq := globOff_eq_nat g
    exact hPresGen ⟨by rw [hgEq]; omega, by rw [hgEq, Int.toNat_natCast]; exact globOff_bound hg12⟩
      (Or.inr (by rw [hgEq, Int.toNat_natCast]; omega))
  have applyTabWrites_append : ∀ (xs ys : List (Int × BitVec 64)) (m : ByteMem),
      applyTabWrites regionBase m (xs ++ ys) =
        applyTabWrites regionBase (applyTabWrites regionBase m xs) ys := by
    intro xs; induction xs with
    | nil => intro _ _; rfl
    | cons _ _ ih => intro ys m; exact ih ys _
  have hAt : ∀ (xs : List (Int × BitVec 64)) (off : Int) (w : BitVec 64) (ys : List (Int × BitVec 64)),
      ws = xs ++ (off, w) :: ys →
      tabOffOk off →
      (∀ e ∈ ys, tabOffOk e.1 ∧ tabOffDisj off e.1) →
      readWord64 s11.mem (regionBase + BitVec.ofInt 64 off) = w := by
    intro xs off w ys hws hoff hys
    rw [hs11Mem, hws, applyTabWrites_append]
    change readWord64 (applyTabWrites regionBase
      (writeWord64 (applyTabWrites regionBase st.mem xs) (regionBase + BitVec.ofInt 64 off) w) ys) _ = w
    rw [readWord64_applyTabWrites_disj hR hoff ys hys, readWord64_writeWord64_self]
  have h180BVal : readWord64 s11.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 180)) = 0#64 :=
    hAt [] _ _
      [(checkerTabMini.dlen 180, 0#64), (checkerTabMini.dlen32 180, 0#64),
       (checkerTabMini.dbase 182, 0#64), (checkerTabMini.dlen 182, 0#64), (checkerTabMini.dlen32 182, 0#64),
       (checkerTabMini.dbase 181, w181B),
       (checkerTabMini.dlen 181, BitVec.ofNat 64 L.Arena.hdrW),
       (checkerTabMini.dlen32 181, BitVec.ofNat 64 (2 * L.Arena.hdrW))]
      rfl hb180ok (fun e he => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hl180ok, Or.inl (by omega)⟩
        · exact ⟨hd180ok, Or.inl (by omega)⟩
        · exact ⟨hb182ok, Or.inl (by omega)⟩
        · exact ⟨hl182ok, Or.inl (by omega)⟩
        · exact ⟨hd182ok, Or.inl (by omega)⟩
        · exact ⟨hb181ok, Or.inl (by omega)⟩
        · exact ⟨hl181ok, Or.inl (by omega)⟩
        · exact ⟨hd181ok, Or.inl (by omega)⟩)
  have h180LVal : readWord64 s11.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 180)) = 0#64 :=
    hAt [(checkerTabMini.dbase 180, 0#64)] _ _
      [(checkerTabMini.dlen32 180, 0#64),
       (checkerTabMini.dbase 182, 0#64), (checkerTabMini.dlen 182, 0#64), (checkerTabMini.dlen32 182, 0#64),
       (checkerTabMini.dbase 181, w181B),
       (checkerTabMini.dlen 181, BitVec.ofNat 64 L.Arena.hdrW),
       (checkerTabMini.dlen32 181, BitVec.ofNat 64 (2 * L.Arena.hdrW))]
      rfl hl180ok (fun e he => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨hd180ok, Or.inl (by omega)⟩
        · exact ⟨hb182ok, Or.inr (by omega)⟩
        · exact ⟨hl182ok, Or.inl (by omega)⟩
        · exact ⟨hd182ok, Or.inl (by omega)⟩
        · exact ⟨hb181ok, Or.inr (by omega)⟩
        · exact ⟨hl181ok, Or.inl (by omega)⟩
        · exact ⟨hd181ok, Or.inl (by omega)⟩)
  have h182BVal : readWord64 s11.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 182)) = 0#64 :=
    hAt [(checkerTabMini.dbase 180, 0#64), (checkerTabMini.dlen 180, 0#64), (checkerTabMini.dlen32 180, 0#64)] _ _
      [(checkerTabMini.dlen 182, 0#64), (checkerTabMini.dlen32 182, 0#64),
       (checkerTabMini.dbase 181, w181B),
       (checkerTabMini.dlen 181, BitVec.ofNat 64 L.Arena.hdrW),
       (checkerTabMini.dlen32 181, BitVec.ofNat 64 (2 * L.Arena.hdrW))]
      rfl hb182ok (fun e he => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl | rfl
        · exact ⟨hl182ok, Or.inl (by omega)⟩
        · exact ⟨hd182ok, Or.inl (by omega)⟩
        · exact ⟨hb181ok, Or.inr (by omega)⟩
        · exact ⟨hl181ok, Or.inl (by omega)⟩
        · exact ⟨hd181ok, Or.inl (by omega)⟩)
  have h182LVal : readWord64 s11.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 182)) = 0#64 :=
    hAt [(checkerTabMini.dbase 180, 0#64), (checkerTabMini.dlen 180, 0#64), (checkerTabMini.dlen32 180, 0#64),
       (checkerTabMini.dbase 182, 0#64)] _ _
      [(checkerTabMini.dlen32 182, 0#64),
       (checkerTabMini.dbase 181, w181B),
       (checkerTabMini.dlen 181, BitVec.ofNat 64 L.Arena.hdrW),
       (checkerTabMini.dlen32 181, BitVec.ofNat 64 (2 * L.Arena.hdrW))]
      rfl hl182ok (fun e he => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl
        · exact ⟨hd182ok, Or.inl (by omega)⟩
        · exact ⟨hb181ok, Or.inr (by omega)⟩
        · exact ⟨hl181ok, Or.inr (by omega)⟩
        · exact ⟨hd181ok, Or.inl (by omega)⟩)
  have h181BVal : readWord64 s11.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 181)) =
      regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.slotOf 180) :=
    hAt [(checkerTabMini.dbase 180, 0#64), (checkerTabMini.dlen 180, 0#64), (checkerTabMini.dlen32 180, 0#64),
       (checkerTabMini.dbase 182, 0#64), (checkerTabMini.dlen 182, 0#64), (checkerTabMini.dlen32 182, 0#64)] _ _
      [(checkerTabMini.dlen 181, BitVec.ofNat 64 L.Arena.hdrW),
       (checkerTabMini.dlen32 181, BitVec.ofNat 64 (2 * L.Arena.hdrW))]
      rfl hb181ok (fun e he => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · exact ⟨hl181ok, Or.inl (by omega)⟩
        · exact ⟨hd181ok, Or.inl (by omega)⟩)
  have h181LVal : readWord64 s11.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 181)) =
      BitVec.ofNat 64 L.Arena.hdrW :=
    hAt [(checkerTabMini.dbase 180, 0#64), (checkerTabMini.dlen 180, 0#64), (checkerTabMini.dlen32 180, 0#64),
       (checkerTabMini.dbase 182, 0#64), (checkerTabMini.dlen 182, 0#64), (checkerTabMini.dlen32 182, 0#64),
       (checkerTabMini.dbase 181, w181B)] _ _
      [(checkerTabMini.dlen32 181, BitVec.ofNat 64 (2 * L.Arena.hdrW))]
      rfl hl181ok (fun e he => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl
        exact ⟨hd181ok, Or.inl (by omega)⟩)
  have hpcEnd : checkerLM.totalSize (p11a ++ cHdrL32St) =
      checkerLM.totalSize pre + checkerLM.totalSize (drvBPart2 checkerTabMini) := by
    dsimp only [p11a, p10, p10a, p9, p9b, p9a, p8, p7, drvBPart2]
    simp only [cClrOut, cClrCtl, cHdrBaseLi, cHdrBaseAdd, cHdrBaseSt,
      cHdrLenLi, cHdrLenSt, cHdrL32Li, cHdrL32St, checkerLM.totalSize_append, Nat.add_assoc]
  refine ⟨k7 + k8 + checkerLM.totalSize cHdrBaseLi + 1 + checkerLM.totalSize cHdrBaseSt +
      checkerLM.totalSize cHdrLenLi + checkerLM.totalSize cHdrLenSt +
      checkerLM.totalSize cHdrL32Li + checkerLM.totalSize cHdrL32St, s11, ?_, ?_,
      (hoth11b _ (by decide)).trans hs11agp,
      (hoth11b _ (by decide)).trans ((hoth11a _ (by decide)).trans ((hoth10b _ (by decide)).trans
        ((hoth10a _ (by decide)).trans ((hoth9c _ (by decide)).trans ((hoth9b _ (by decide)).trans
          ((hoth9a _ (by decide)).trans ((hoth8 _ (by decide)).trans (hoth7 _ (by decide))))))))),
      houtAll, hTabHdrPres, hGlobPres, h180BVal, h180LVal, h182BVal, h182LVal, h181BVal, h181LVal⟩
  · rw [run_add, run_add, run_add, run_add, run_add, run_add, run_add, run_add, hrun7]
    dsimp only; rw [hrun8]; dsimp only; rw [hrun9a]; dsimp only; rw [hr9b]; dsimp only; rw [hrun9c]
    dsimp only; rw [hrun10a]; dsimp only; rw [hrun10b]; dsimp only; rw [hrun11a]; exact hrun11b
  · rw [hpc11, ← checkerLM.totalSize_append p11a cHdrL32St, hpcEnd]

private theorem drvPhaseBSetup_p3_sim (env : CodeEnvGen checkerLM) (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (pre post : List AsmItem)
    (hlink : checkerLM.linkSpec (pre ++ drvBPart3 checkerTabMini ++ post) =
      .ok (env.code, env.labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (checkerLM.totalSize pre +
        checkerLM.totalSize (drvBPart3 checkerTabMini))) ∧
      st'.getReg AbiReg.gp = regionBase ∧
      st'.getReg AbiReg.s0 = BitVec.ofNat 64 (abiFuel - 2) ∧
      st'.getReg AbiReg.sp = readWord64 st.mem regionBase ∧
      st'.getReg AbiReg.s2 = st.getReg AbiReg.s2 ∧
      st'.getReg AbiReg.t0 = regionBase + BitVec.ofInt 64 checkerTabMini.args ∧
      st'.getReg AbiReg.t1 = 0#64 ∧
      st'.mem = st.mem := by
  let cFuelLi := li AbiReg.s0 (BitVec.ofNat 64 (abiFuel - 1))
  let cLdSp := Asm.ld AbiReg.sp AbiReg.gp
  let cBeq := Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel
  let cDec := Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)
  let cArgs := addImmOff AbiReg.t0 AbiReg.gp AbiReg.t2 checkerTabMini.args
  let cT1 := li AbiReg.t1 0#64
  have hl12 : checkerLM.linkSpec (pre ++ cFuelLi ++ ([cLdSp, cBeq, cDec] ++ cArgs ++ cT1 ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [drvBPart3, cFuelLi, cLdSp, cBeq, cDec, cArgs, cT1,
      List.cons_append, List.nil_append, List.append_assoc] using hlink
  have hpc12_64 := linkResolved_sub_pc64 env pre cFuelLi _ hl12
  obtain ⟨s12, hrun12, hoth12, hs0_12, hm12, hpc12⟩ :=
    li_correct_lm checkerLM env.hrom pre _ AbiReg.s0 (by decide)
      (BitVec.ofNat 64 (abiFuel - 1)) hl12 hpc12_64 st hpc
  let p12 := pre ++ cFuelLi
  have hpc12' : s12.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p12) := by
    simpa only [p12, checkerLM.totalSize_append] using hpc12
  have hs12gp : s12.getReg AbiReg.gp = regionBase := (hoth12 _ (by decide)).trans hgp
  have hl13 : checkerLM.linkSpec (p12 ++ [Asm.raw (.load .ld AbiReg.sp AbiReg.gp 0#12)] ++
      ([cBeq, cDec] ++ cArgs ++ cT1 ++ post)) = .ok (env.code, env.labels) := by
    simpa only [p12, cLdSp, Asm.ld, Asm.raw, List.cons_append, List.nil_append, List.append_assoc] using hl12
  have hpc13_64 := linkResolved_sub_pc64 env p12 [Asm.raw (.load .ld AbiReg.sp AbiReg.gp 0#12)] _ hl13
  have hlt13_64 : 4 * (checkerLM.totalSize p12 + 1) < 2 ^ 64 := by
    simpa only [Asm.raw, checkerLM.totalSize_instr] using hpc13_64
  have halSp : isAligned (s12.getReg AbiReg.gp + sextImm12 0#12) 8 = true := by
    have hz : sextImm12 0#12 = 0#64 := rfl; rw [hs12gp, hz, BitVec.add_zero]; exact hRegAlign
  obtain ⟨hr13, hpc13, hsp13, hoth13, hm13⟩ :=
    step_ld_off env p12 _ AbiReg.sp AbiReg.gp 0#12 (by decide) hl13 hlt13_64 s12 hpc12' halSp
  let s13 := stepReg s12 AbiReg.sp (readWord64 s12.mem (s12.getReg AbiReg.gp + sextImm12 0#12)) (s12.pc + 4#64)
  let p13 := p12 ++ [cLdSp]
  have hpc13' : s13.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p13) := by
    simpa only [p13, cLdSp, Asm.ld, Asm.raw, checkerLM.totalSize_append, checkerLM.totalSize_instr] using hpc13
  have hs13s0 : s13.getReg AbiReg.s0 = BitVec.ofNat 64 (abiFuel - 1) :=
    (hoth13 _ (by decide)).trans hs0_12
  have hl14 : checkerLM.linkSpec (p13 ++ [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel] ++
      ([cDec] ++ cArgs ++ cT1 ++ post)) = .ok (env.code, env.labels) := by
    simpa only [p13, cLdSp, Asm.ld, Asm.raw, cBeq, List.cons_append, List.nil_append, List.append_assoc] using hl13
  have hbr14 := run_br_step env p13 _ .beq AbiReg.s0 AbiReg.zero exhaustedLabel
    env.exhaustedTarget env.hexhaustedLbl (by decide) hl14 s13 hpc13'
  have hev14 : evalBranch .beq (s13.getReg AbiReg.s0) (s13.getReg AbiReg.zero) = false := by
    rw [hs13s0, getReg_zero]
    have hne : BitVec.ofNat 64 (abiFuel - 1) ≠ 0#64 := by simp [abiFuel]
    simp [evalBranch, hne]
  rw [hev14] at hbr14
  obtain ⟨k14, s14, _, hrun14, hpc14, hoth14, _, hm14⟩ := hbr14
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc14
  let p14 := p13 ++ [cBeq]
  have hpc14' : s14.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p14) := by
    rw [hpc14]; dsimp only [p14]; rw [checkerLM.totalSize_append p13 _]; rfl
  have hl15 : checkerLM.linkSpec (p14 ++ [Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++
      (cArgs ++ cT1 ++ post)) = .ok (env.code, env.labels) := by
    simpa only [p14, cDec, List.cons_append, List.nil_append, List.append_assoc] using hl14
  obtain ⟨hr15, hpc15, hs0_15, hoth15, hm15⟩ :=
    run_aluImm_rd_step env p14 _ .addi AbiReg.s0 AbiReg.s0 (-1#12) (by decide) hl15 s14 hpc14'
  let s15 := stepReg s14 AbiReg.s0 (evalAluImm .addi (s14.getReg AbiReg.s0) (-1#12))
    (BitVec.ofNat 64 (4 * (checkerLM.totalSize p14 + 1)))
  let p15 := p14 ++ [cDec]
  have hpc15' : s15.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p15) := by
    simpa only [p15, cDec, checkerLM.totalSize_append, Asm.addi, checkerLM.totalSize_instr] using hpc15
  have hl16 : checkerLM.linkSpec (p15 ++ cArgs ++ (cT1 ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p15, List.append_assoc] using hl15
  have hpc16_64 := linkResolved_sub_pc64 env p15 cArgs _ hl16
  have hs15gp : s15.getReg AbiReg.gp = regionBase :=
    (hoth15 _ (by decide)).trans ((hoth14 _ (by decide)).trans ((hoth13 _ (by decide)).trans hs12gp))
  obtain ⟨s16, hrun16, hoth16, ht0_16, hm16, hpc16⟩ :=
    addImmOff_correct_lm checkerLM env.hrom p15 _ AbiReg.t0 AbiReg.gp AbiReg.t2
      (by decide) (by decide) (by decide) checkerTabMini.args hl16 hpc16_64 s15 hpc15'
  let p16 := p15 ++ cArgs
  have hpc16' : s16.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p16) := by
    simpa only [p16, checkerLM.totalSize_append] using hpc16
  have hl17 : checkerLM.linkSpec (p16 ++ cT1 ++ post) =
      .ok (env.code, env.labels) := by
    simpa only [p16, List.append_assoc] using hl16
  have hpc17_64 := linkResolved_sub_pc64 env p16 cT1 post hl17
  obtain ⟨s17, hrun17, hoth17, ht1_17, hm17, hpc17⟩ :=
    li_correct_lm checkerLM env.hrom p16 post AbiReg.t1 (by decide) 0#64 hl17 hpc17_64 s16 hpc16'
  have hs17gp : s17.getReg AbiReg.gp = regionBase :=
    (hoth17 _ (by decide)).trans ((hoth16 _ (by decide) (by decide)).trans hs15gp)
  have hs17s0 : s17.getReg AbiReg.s0 = BitVec.ofNat 64 (abiFuel - 2) := by
    rw [hoth17 _ (by decide), hoth16 _ (by decide) (by decide), hs0_15]
    change evalAluImm .addi (s14.getReg AbiReg.s0) (-1#12) = BitVec.ofNat 64 (abiFuel - 2)
    rw [hoth14 _ (by decide), hs13s0]; simp [abiFuel]; decide
  have hs17sp : s17.getReg AbiReg.sp = readWord64 st.mem regionBase := by
    rw [hoth17 _ (by decide), hoth16 _ (by decide) (by decide), hoth15 _ (by decide), hoth14 _ (by decide), hsp13]
    have hz : sextImm12 0#12 = 0#64 := rfl
    rw [hs12gp, hz, BitVec.add_zero, hm12]
  have hs17s2 : s17.getReg AbiReg.s2 = st.getReg AbiReg.s2 :=
    (hoth17 _ (by decide)).trans ((hoth16 _ (by decide) (by decide)).trans ((hoth15 _ (by decide)).trans
      ((hoth14 _ (by decide)).trans ((hoth13 _ (by decide)).trans (hoth12 _ (by decide))))))
  have hs17t0 : s17.getReg AbiReg.t0 = regionBase + BitVec.ofInt 64 checkerTabMini.args := by
    rw [hoth17 _ (by decide), ht0_16, hs15gp]
  have hpcEnd : checkerLM.totalSize (p16 ++ cT1) =
      checkerLM.totalSize pre + checkerLM.totalSize (drvBPart3 checkerTabMini) := by
    dsimp only [p16, p15, p14, p13, p12, drvBPart3]
    simp only [cFuelLi, cLdSp, cBeq, cDec, cArgs, cT1, checkerLM.totalSize_append,
      checkerLM.totalSize_cons, checkerLM.totalSize_nil, Nat.add_zero, Nat.add_assoc]
  refine ⟨checkerLM.totalSize cFuelLi + 1 + k14 + 1 + checkerLM.totalSize cArgs +
      checkerLM.totalSize cT1, s17, ?_, ?_, hs17gp, hs17s0, hs17sp, hs17s2, hs17t0, ht1_17,
      by rw [hm17, hm16, hm15, hm14, hm13, hm12]⟩
  · rw [run_add, run_add, run_add, run_add, run_add, hrun12]
    dsimp only; rw [hr13]; dsimp only; rw [hrun14]; dsimp only; rw [hr15]; dsimp only; rw [hrun16]
    exact hrun17
  · rw [hpc17, ← checkerLM.totalSize_append p16 cT1, hpcEnd]

private theorem drvPhaseBSetup_sim_gen (env : CodeEnvGen checkerLM) (henv : env = checkerEnv) (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (retA : _root_.L.Word) (hretA : 2 ^ 63 ≤ retA.toNat)
    (pre post : List AsmItem)
    (hlink : checkerLM.linkSpec (pre ++ drvPhaseBSetup checkerTabMini ++ post) =
      .ok (env.code, env.labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase)
    (ha0 : st.getReg AbiReg.a0 = retA.toBitVec) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (checkerLM.totalSize pre +
        checkerLM.totalSize (drvPhaseBSetup checkerTabMini))) ∧
      st'.getReg AbiReg.gp = regionBase ∧
      st'.getReg AbiReg.s0 = BitVec.ofNat 64 (abiFuel - 2) ∧
      st'.getReg AbiReg.sp = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) ∧
      st'.getReg AbiReg.s2 = st.getReg AbiReg.s2 ∧
      st'.getReg AbiReg.t0 = regionBase + BitVec.ofInt 64 checkerTabMini.args ∧
      st'.getReg AbiReg.t1 = 0#64 ∧
      ProgMemOutside (phaseBWriteSpan regionBase) st.mem st'.mem ∧
      readWord64 st'.mem regionBase = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) ∧
      readWord64 st'.mem (regionBase + 8#64) = regionBase + BitVec.ofNat 64 abiSlot ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff phiGVar)) =
        (retA - 9223372036854775808).toBitVec ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff ploGVar)) = 0#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) = 2#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 180)) = 0#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 180)) = 0#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 182)) = 0#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 182)) = 0#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 181)) =
        regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.slotOf 180) ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 181)) =
        BitVec.ofNat 64 L.Arena.hdrW := by
  have hl1 : checkerLM.linkSpec (pre ++ drvBPart1 checkerTabMini ++
      (drvBPart2 checkerTabMini ++ drvBPart3 checkerTabMini ++ post)) =
      .ok (env.code, env.labels) := by
    have h := hlink
    rw [drvPhaseBSetup_eq_parts] at h
    simpa only [List.append_assoc] using h
  obtain ⟨k1, s1, hr1, hpc1, hgp1, hs2_1, hout1, hTop1, hLim1, hPhi1, hPlo1, hMode1⟩ :=
    drvPhaseBSetup_p1_sim env henv regionBase hRegAlign hReg64 retA hretA pre _ hl1 st hpc hgp ha0
  let p1 := pre ++ drvBPart1 checkerTabMini
  have hpc1' : s1.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p1) := by
    simpa only [p1, checkerLM.totalSize_append] using hpc1
  have hl2 : checkerLM.linkSpec (p1 ++ drvBPart2 checkerTabMini ++
      (drvBPart3 checkerTabMini ++ post)) = .ok (env.code, env.labels) := by
    simpa only [p1, List.append_assoc] using hl1
  obtain ⟨k2, s2, hr2, hpc2, hgp2, hs2_2, hout2, hHdr, hGlob, h180B, h180L, h182B, h182L, h181B, h181L⟩ :=
    drvPhaseBSetup_p2_sim env regionBase hRegAlign hReg64 p1 _ hl2 s1 hpc1' hgp1
  let p2 := p1 ++ drvBPart2 checkerTabMini
  have hpc2' : s2.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p2) := by
    simpa only [p2, checkerLM.totalSize_append] using hpc2
  have hl3 : checkerLM.linkSpec (p2 ++ drvBPart3 checkerTabMini ++ post) =
      .ok (env.code, env.labels) := by
    simpa only [p2, List.append_assoc] using hl2
  obtain ⟨k3, s3, hr3, hpc3, hgp3, hs0_3, hsp3, hs2_3, ht0_3, ht1_3, hm3⟩ :=
    drvPhaseBSetup_p3_sim env regionBase hRegAlign p2 post hl3 s2 hpc2' hgp2
  have h0bv : BitVec.ofInt 64 0 = 0#64 := rfl
  have hTop2 : readWord64 s2.mem regionBase = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) := by
    have h := hHdr 0 (Or.inl rfl); rw [h0bv, BitVec.add_zero] at h; rw [h, hTop1]
  have hLim2 : readWord64 s2.mem (regionBase + 8#64) = regionBase + BitVec.ofNat 64 abiSlot := by
    have h := hHdr 8 (Or.inr rfl); change readWord64 s2.mem (regionBase + 8#64) = readWord64 s1.mem (regionBase + 8#64) at h
    rw [h, hLim1]
  refine ⟨k1 + k2 + k3, s3, ?_, ?_, hgp3, hs0_3, by rw [hsp3, hTop2],
    hs2_3.trans (hs2_2.trans hs2_1), ht0_3, ht1_3,
    by rw [hm3]; exact hout1.trans hout2, by rw [hm3]; exact hTop2, by rw [hm3]; exact hLim2,
    by rw [hm3, hGlob phiGVar (Or.inl rfl), hPhi1],
    by rw [hm3, hGlob ploGVar (Or.inr (Or.inl rfl)), hPlo1],
    by rw [hm3, hGlob modeGVar (Or.inr (Or.inr rfl)), hMode1],
    by rw [hm3]; exact h180B, by rw [hm3]; exact h180L,
    by rw [hm3]; exact h182B, by rw [hm3]; exact h182L,
    by rw [hm3]; exact h181B, by rw [hm3]; exact h181L⟩
  · rw [run_add, run_add, hr1]; dsimp only; rw [hr2]; exact hr3
  · rw [hpc3]; exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (by
      dsimp only [p2, p1]; rw [drvPhaseBSetup_eq_parts]
      simp only [checkerLM.totalSize_append, Nat.add_assoc])

theorem drvPhaseBSetup_sim (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (retA : _root_.L.Word) (hretA : 2 ^ 63 ≤ retA.toNat)
    (pre post : List AsmItem)
    (hlink : checkerLM.linkSpec (pre ++ drvPhaseBSetup checkerTabMini ++ post) =
      .ok (checkerEnv.code, checkerEnv.labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase)
    (ha0 : st.getReg AbiReg.a0 = retA.toBitVec) :
    ∃ k st',
      RV64.run checkerEnv.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (checkerLM.totalSize pre +
        checkerLM.totalSize (drvPhaseBSetup checkerTabMini))) ∧
      st'.getReg AbiReg.gp = regionBase ∧
      st'.getReg AbiReg.s0 = BitVec.ofNat 64 (abiFuel - 2) ∧
      st'.getReg AbiReg.sp = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) ∧
      st'.getReg AbiReg.s2 = st.getReg AbiReg.s2 ∧
      st'.getReg AbiReg.t0 = regionBase + BitVec.ofInt 64 checkerTabMini.args ∧
      st'.getReg AbiReg.t1 = 0#64 ∧
      ProgMemOutside (phaseBWriteSpan regionBase) st.mem st'.mem ∧
      readWord64 st'.mem regionBase = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) ∧
      readWord64 st'.mem (regionBase + 8#64) = regionBase + BitVec.ofNat 64 abiSlot ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff phiGVar)) =
        (retA - 9223372036854775808).toBitVec ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff ploGVar)) = 0#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) = 2#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 180)) = 0#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 180)) = 0#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 182)) = 0#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 182)) = 0#64 ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 181)) =
        regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.slotOf 180) ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 181)) =
        BitVec.ofNat 64 L.Arena.hdrW := by
  exact drvPhaseBSetup_sim_gen checkerEnv rfl regionBase hRegAlign hReg64 retA hretA pre post hlink st hpc hgp ha0

theorem phaseB_progMemRel_gen
    (hdrLen : Nat) (hhdr : 8 * hdrLen ≤ abiSlot) (hhdrPos : 0 < hdrLen) (hhdrLe : hdrLen ≤ abiWords)
    {inBase pinsBase regionBase : BitVec 64} {inLen pinsLen : Nat}
    (hIn64 : inBase.toNat + inLen ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pinsLen ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjInPins : MemSpan.disjoint ⟨inBase, inLen⟩ ⟨pinsBase, pinsLen⟩)
    (hDisjInReg : MemSpan.disjoint ⟨inBase, inLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pinsLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    {rmemA rmemB : ByteMem} {m1 mB : _root_.L.Mem} {phiVal modeVal : _root_.L.Word}
    (hRelA : ProgMemRel checkerTabMini
      (checkerLayoutA inBase pinsBase regionBase inLen pinsLen hIn64 hPins64 hRegAlign hReg64 hDisjInPins hDisjInReg hDisjPinsReg)
      rmemA m1)
    (hm1Sz : (m1.words (.t0 L.Arena.OUT)).size = abiWords)
    (hmBBytes : ∀ a, mB.bytes a = m1.bytes a)
    (hmBOut : mB.words (.t0 L.Arena.OUT) = #[])
    (hmBCtlf : mB.words (.t0 L.Arena.CTLF) = #[])
    (hmBHdrf : mB.words (.t0 L.Arena.HDRF) = (m1.words (.t0 L.Arena.OUT)).extract 0 hdrLen)
    (hmBWordsOther : ∀ s, s ≠ .t0 L.Arena.OUT → s ≠ .t0 L.Arena.CTLF → s ≠ .t0 L.Arena.HDRF →
      mB.words s = m1.words s)
    (hmBPhi : mB.glob phiGVar = phiVal)
    (hmBPlo : mB.glob ploGVar = 0)
    (hmBMode : mB.glob modeGVar = modeVal)
    (hmBGlobOther : ∀ g, g ≠ phiGVar → g ≠ ploGVar → g ≠ modeGVar → mB.glob g = m1.glob g)
    (hout : ProgMemOutside (phaseBWriteSpan regionBase) rmemA rmemB)
    (hPhi : readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff phiGVar)) =
      phiVal.toBitVec)
    (hPlo : readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff ploGVar)) = 0#64)
    (hMode : readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) =
      modeVal.toBitVec)
    (h180B : readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 180)) = 0#64)
    (h180L : readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 180)) = 0#64)
    (h182B : readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 182)) = 0#64)
    (h182L : readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 182)) = 0#64)
    (h181B : readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 181)) =
      regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.slotOf 180))
    (h181L : readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 181)) =
      BitVec.ofNat 64 hdrLen) :
    ProgMemRel checkerTabMini
      (checkerLayoutBGen hdrLen hhdr hhdrPos inBase pinsBase regionBase inLen pinsLen
        hIn64 hPins64 hRegAlign hReg64 hDisjInPins hDisjInReg hDisjPinsReg)
      rmemB mB := by
  let LA := checkerLayoutA inBase pinsBase regionBase inLen pinsLen hIn64 hPins64 hRegAlign hReg64 hDisjInPins hDisjInReg hDisjPinsReg
  let LB := checkerLayoutBGen hdrLen hhdr hhdrPos inBase pinsBase regionBase inLen pinsLen
    hIn64 hPins64 hRegAlign hReg64 hDisjInPins hDisjInReg hDisjPinsReg
  have hNeedEq := checkerTabMini_abiNeed_eq
  have h211 : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; simp [abiSlot]
  have houtSlot0 : ProgMemOutside (fun a => (⟨regionBase, abiSlot⟩ : MemSpan).contains a) rmemA rmemB :=
    hout.mono (phaseBWriteSpan_sub_slot0 regionBase hReg64)
  rcases hRelA with ⟨hA8, hA64, hArom, hAg⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases hA8 a ha with ⟨hcap, hlt, hlen, hbase, hbytes⟩
    have hpos8lt : checkerTabMini.pos8 a < 2 := by
      have hlt' := (Tab.bytePosOk_lt ha).1; rw [t_nb] at hlt'; exact hlt'
    have hcapB : LB.cap8 a = LA.cap8 a := rfl
    have hbaseB : LB.base8 a = LA.base8 a := rfl
    have hDisj8 : ∀ k, k < (m1.arr8 a).size →
        ¬(⟨regionBase, abiSlot⟩ : MemSpan).contains (LA.base8 a + BitVec.ofNat 64 k) := by
      intro k hk hc
      have hc8 : (LA.arr8Span a).contains (LA.base8 a + BitVec.ofNat 64 k) :=
        ⟨k, by dsimp only [ProgLayout.arr8Span]; exact Nat.lt_of_lt_of_le hk hcap, rfl⟩
      have hcT : LA.tabSpan.contains (LA.base8 a + BitVec.ofNat 64 k) := hc
      exact MemSpan.disjoint_to_memDisjoint (LA.arr8Span_valid a) LA.tabSpan_valid (LA.h8DisjTab a ha) _ hc8 hcT
    have harr8 : mB.arr8 a = m1.arr8 a := hmBBytes a
    have hlenB : readWord64 rmemB (LB.T + BitVec.ofInt 64 (checkerTabMini.len8 a)) =
        BitVec.ofNat 64 (mB.arr8 a).size := by
      have hd : checkerTabMini.len8 a = ((1656 + 8 * checkerTabMini.pos8 a : Nat) : Int) := by
        change checkerTabMini.dlen (checkerTabMini.pos8 a) = _
        simp only [Tab.dlen, t_nb, t_nw]; omega
      have hLA_T : LA.T = regionBase := rfl
      change readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.len8 a)) = _
      rw [harr8, ← hlen, hLA_T]
      apply hout.readWord64_eq
      rw [hd]
      apply phaseBWriteSpan_disj_tabOff regionBase hReg64 (by omega)
        (by rw [Int.toNat_natCast]; simp [abiSlot]; omega) (by rw [Int.toNat_natCast]; omega)
        (fun p hp => by
          rw [Int.toNat_natCast]
          refine ⟨by omega, by rcases hp with rfl | rfl | rfl <;> omega, by omega⟩)
        (fun g _ => by
          rw [Int.toNat_natCast]
          have hr := resBase_ge_16
          left; omega)
    have hbaseB' : readWord64 rmemB (LB.T + BitVec.ofInt 64 (checkerTabMini.base8 a)) = LB.base8 a := by
      have hb : checkerTabMini.base8 a = ((16 + 8 * checkerTabMini.pos8 a : Nat) : Int) := by
        change checkerTabMini.dbase (checkerTabMini.pos8 a) = _
        simp only [Tab.dbase]; omega
      change readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.base8 a)) = _
      rw [hbaseB, ← hbase]
      apply hout.readWord64_eq
      rw [hb]
      apply phaseBWriteSpan_disj_tabOff regionBase hReg64 (by omega)
        (by rw [Int.toNat_natCast]; simp [abiSlot]; omega) (by rw [Int.toNat_natCast]; omega)
        (fun p hp => by
          rw [Int.toNat_natCast]
          refine ⟨by rcases hp with rfl | rfl | rfl <;> omega, by omega, by omega⟩)
        (fun g _ => by
          rw [Int.toNat_natCast]
          have hr := resBase_ge_16
          left; omega)
    refine ⟨by rw [harr8, hcapB]; exact hcap, by rw [harr8]; exact hlt, hlenB, hbaseB', fun i hi => ?_⟩
    have hi' : i < (m1.arr8 a).size := by simpa only [harr8] using hi
    have helem : (mB.arr8 a)[i] = (m1.arr8 a)[i] := by simp only [harr8]
    rw [hbaseB, houtSlot0 _ (hDisj8 i hi'), helem, hbytes i hi']
  · intro s hs
    have ⟨hlo, hhi⟩ := checkerTabMini_wordPos_bounds hs
    by_cases hOut : s = .t0 L.Arena.OUT
    · subst hOut
      have hcap0 : LB.cap64 (.t0 L.Arena.OUT) = 0 := by simp [LB, checkerLayoutBGen]
      have hbase0 : LB.base64 (.t0 L.Arena.OUT) = 0#64 := by simp [LB, checkerLayoutBGen]
      have hsz0 : (mB.arr64 (.t0 L.Arena.OUT)).size = 0 := by
        change (mB.words (.t0 L.Arena.OUT)).size = 0; rw [hmBOut]; rfl
      refine ⟨by rw [hsz0, hcap0]; exact Nat.le_refl _, by rw [hsz0]; decide, ?_, ?_, fun i hi => by rw [hsz0] at hi; omega⟩
      · rw [hsz0]; change readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 180)) = 0#64
        exact h180L
      · rw [hbase0]; change readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 180)) = 0#64
        exact h180B
    · by_cases hCtlf : s = .t0 L.Arena.CTLF
      · subst hCtlf
        have hne : (TieredArray.t0 L.Arena.CTLF) ≠ (TieredArray.t0 L.Arena.OUT) := by decide
        have hcap0 : LB.cap64 (.t0 L.Arena.CTLF) = 0 := by simp [LB, checkerLayoutBGen, hne]
        have hbase0 : LB.base64 (.t0 L.Arena.CTLF) = 0#64 := by simp [LB, checkerLayoutBGen, hne]
        have hsz0 : (mB.arr64 (.t0 L.Arena.CTLF)).size = 0 := by
          change (mB.words (.t0 L.Arena.CTLF)).size = 0; rw [hmBCtlf]; rfl
        refine ⟨by rw [hsz0, hcap0]; exact Nat.le_refl _, by rw [hsz0]; decide, ?_, ?_, fun i hi => by rw [hsz0] at hi; omega⟩
        · rw [hsz0]; change readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 182)) = 0#64
          exact h182L
        · rw [hbase0]; change readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 182)) = 0#64
          exact h182B
      · by_cases hHdrf : s = .t0 L.Arena.HDRF
        · subst hHdrf
          have hne1 : (TieredArray.t0 L.Arena.HDRF) ≠ (TieredArray.t0 L.Arena.OUT) := by decide
          have hne2 : (TieredArray.t0 L.Arena.HDRF) ≠ (TieredArray.t0 L.Arena.CTLF) := by decide
          have hszH : (mB.arr64 (.t0 L.Arena.HDRF)).size = hdrLen := by
            change (mB.words (.t0 L.Arena.HDRF)).size = hdrLen
            rw [hmBHdrf, Array.size_extract, hm1Sz]; omega
          have hcapH : LB.cap64 (.t0 L.Arena.HDRF) = hdrLen := by
            simp [LB, checkerLayoutBGen, hne1, hne2]
          have hbaseH : LB.base64 (.t0 L.Arena.HDRF) =
              regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.pos64 (.t0 L.Arena.OUT)) := by
            simp [LB, checkerLayoutBGen, hne1, hne2]
          have hslot180 : checkerTabMini.slotOf 180 = checkerTabMini.pos64 (.t0 L.Arena.OUT) := by
            rw [t_pos_out]; simp [Tab.slotOf, t_nbuf]
          refine ⟨by rw [hszH, hcapH]; exact Nat.le_refl _,
            by rw [hszH]; exact Nat.lt_of_le_of_lt hhdrLe (by decide), ?_, ?_, ?_⟩
          · rw [hszH]; change readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 181)) = _
            exact h181L
          · rw [hbaseH, ← hslot180]
            change readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 181)) = _
            exact h181B
          · intro i hi
            have hiH : i < hdrLen := by rw [hszH] at hi; exact hi
            have hiOut : i < (m1.arr64 (.t0 L.Arena.OUT)).size := by
              change i < (m1.words (.t0 L.Arena.OUT)).size; rw [hm1Sz]; omega
            rcases hA64 (.t0 L.Arena.OUT) t_word_out with ⟨_, _, _, _, hOutElems⟩
            have hOutBase : LA.base64 (.t0 L.Arena.OUT) = LB.base64 (.t0 L.Arena.HDRF) := by
              rw [hbaseH]; simp [LA, checkerLayoutA, t_word_out]
            have helem : (mB.arr64 (.t0 L.Arena.HDRF))[i] = (m1.arr64 (.t0 L.Arena.OUT))[i] := by
              simp only [_root_.L.Mem.arr64, hmBHdrf, Array.getElem_extract, Nat.zero_add]
            rw [helem, ← hOutElems i hiOut, hOutBase]
            apply houtSlot0.readWord64_eq
            intro k hk ⟨m, hm, hmeq⟩
            dsimp only at hm
            rw [hbaseH, t_pos_out] at hmeq
            have hm64 : m < 2 ^ 64 := by simp [abiSlot] at hm; omega
            have hrm64 : regionBase.toNat + m < 2 ^ 64 := by omega
            have hlo64 : abiSlot * 180 < 2 ^ 64 := by simp [abiSlot]
            have h8ik64 : 8 * i + k < 2 ^ 64 := by omega
            have hrTot64 : regionBase.toNat + (abiSlot * 180 + (8 * i + k)) < 2 ^ 64 := by omega
            have hadd : regionBase + BitVec.ofNat 64 (abiSlot * 180) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 k =
                regionBase + BitVec.ofNat 64 (abiSlot * 180 + (8 * i + k)) := by
              rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
            rw [hadd] at hmeq
            have hto := congrArg BitVec.toNat hmeq
            simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega : abiSlot * 180 + (8 * i + k) < 2 ^ 64),
              Nat.mod_eq_of_lt hrTot64, Nat.mod_eq_of_lt hm64, Nat.mod_eq_of_lt hrm64] at hto
            omega
        · rcases hA64 s hs with ⟨hcap, hlt, hlen, hbase, hwords⟩
          have hcapB : LB.cap64 s = LA.cap64 s := by simp [LB, LA, checkerLayoutBGen, checkerLayoutA, hs, hOut, hCtlf, hHdrf]
          have hbaseB : LB.base64 s = LA.base64 s := by simp [LB, LA, checkerLayoutBGen, checkerLayoutA, hs, hOut, hCtlf, hHdrf]
          have harrEq : mB.arr64 s = m1.arr64 s := hmBWordsOther s hOut hCtlf hHdrf
          have hposNe : checkerTabMini.pos64 s ≠ 180 ∧ checkerTabMini.pos64 s ≠ 181 ∧ checkerTabMini.pos64 s ≠ 182 := by
            refine ⟨fun h => hOut (Tab.wordPosOk_inj hs t_word_out (h.trans t_pos_out.symm)),
                    fun h => hHdrf (Tab.wordPosOk_inj hs t_word_hdrf (h.trans t_pos_hdrf.symm)),
                    fun h => hCtlf (Tab.wordPosOk_inj hs t_word_ctlf (h.trans t_pos_ctlf.symm))⟩
          have hlenB : readWord64 rmemB (LB.T + BitVec.ofInt 64 (checkerTabMini.len64 s)) =
              BitVec.ofNat 64 (mB.arr64 s).size := by
            have hd : checkerTabMini.len64 s = ((1656 + 8 * checkerTabMini.pos64 s : Nat) : Int) := by
              change checkerTabMini.dlen (checkerTabMini.pos64 s) = _
              simp only [Tab.dlen, t_nb, t_nw]; omega
            change readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.len64 s)) = _
            rw [harrEq, ← hlen]
            apply hout.readWord64_eq
            rw [hd]
            apply phaseBWriteSpan_disj_tabOff regionBase hReg64 (by omega)
              (by rw [Int.toNat_natCast]; simp [abiSlot]; omega) (by rw [Int.toNat_natCast]; omega)
              (fun p hp => by
                rw [Int.toNat_natCast]
                have hpne : checkerTabMini.pos64 s ≠ p := by rcases hp with rfl | rfl | rfl <;> omega
                refine ⟨by omega, by omega, by omega⟩)
              (fun g _ => by
                rw [Int.toNat_natCast]
                have hr := resBase_ge_16
                left; omega)
          have hbaseB' : readWord64 rmemB (LB.T + BitVec.ofInt 64 (checkerTabMini.base64 s)) = LB.base64 s := by
            have hb : checkerTabMini.base64 s = ((16 + 8 * checkerTabMini.pos64 s : Nat) : Int) := by
              change checkerTabMini.dbase (checkerTabMini.pos64 s) = _
              simp only [Tab.dbase]; omega
            change readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.base64 s)) = _
            rw [hbaseB, ← hbase]
            apply hout.readWord64_eq
            rw [hb]
            apply phaseBWriteSpan_disj_tabOff regionBase hReg64 (by omega)
              (by rw [Int.toNat_natCast]; simp [abiSlot]; omega) (by rw [Int.toNat_natCast]; omega)
              (fun p hp => by
                rw [Int.toNat_natCast]
                have hpne : checkerTabMini.pos64 s ≠ p := by rcases hp with rfl | rfl | rfl <;> omega
                refine ⟨by omega, by omega, by omega⟩)
              (fun g _ => by
                rw [Int.toNat_natCast]
                have hr := resBase_ge_16
                left; omega)
          refine ⟨by rw [harrEq, hcapB]; exact hcap, by rw [harrEq]; exact hlt, hlenB, hbaseB', fun i hi => ?_⟩
          simp only [harrEq] at hi ⊢
          rw [hbaseB, ← hwords i hi]
          apply houtSlot0.readWord64_eq
          intro k hk ⟨m, hm, hmeq⟩
          dsimp only at hm
          have hbas : LA.base64 s = regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.pos64 s) := by
            simp [LA, checkerLayoutA, hs]
          have hcapA : LA.cap64 s = abiWords := by simp [LA, checkerLayoutA, hs]
          rw [hbas] at hmeq
          have h8w : 8 * abiWords = abiSlot := by simp [abiWords, abiSlot]
          have hi_lt : i < abiWords := by
            rw [← hcapA]; exact Nat.lt_of_lt_of_le hi hcap
          have hlo64 : abiSlot * checkerTabMini.pos64 s < 2 ^ 64 := by
            have := Nat.mul_le_mul_left abiSlot hhi; simp [abiSlot] at *; omega
          have h8ik64 : 8 * i + k < 2 ^ 64 := by omega
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
    have hk8 : k < 8 * checkerTabMini.romWords := by
      simp only [Tab.romWords]; omega
    have hR : regionBase.toNat + abiSlot ≤ 2 ^ 64 := by omega
    have hbd : checkerTabMini.romBase.toNat + k + 1 ≤ abiSlot := by
      have harg := checkerTabMini_args_lt
      rw [checkerTabMini_args_eq, Int.toNat_natCast] at harg
      rw [checkerTabMini_romBase_eq, Int.toNat_natCast]
      omega
    have hromGe : 16 + 24 * 205 ≤ checkerTabMini.romBase.toNat + k := by
      rw [checkerTabMini_romBase_eq, Int.toNat_natCast]; omega
    have hromRes : checkerTabMini.romBase.toNat + k < checkerTabMini.resBase.toNat := by
      rw [checkerTabMini_romBase_eq, checkerTabMini_resBase_eq, Int.toNat_natCast, Int.toNat_natCast]
      omega
    intro hw
    have hLB_T : LB.T = regionBase := rfl
    rw [hLB_T] at hw
    rcases hw with hhdr | ⟨p, hp, hdesc⟩ | ⟨g, hg, hgl⟩
    · exact memSpan_offset_disjoint_contains_false hR hbd (by simp [abiSlot] : 0 + 16 ≤ abiSlot)
        (Or.inr (by omega)) ⟨0, Nat.zero_lt_one, by rw [BitVec.add_zero]⟩
        (by simpa only [BitVec.add_zero] using hhdr)
    · rcases hdesc with h | h | h
      · rw [dbase_bv] at h
        have hpb : 16 + 8 * p + 8 ≤ abiSlot := by rcases hp with rfl | rfl | rfl <;> simp [abiSlot]
        exact memSpan_offset_disjoint_contains_false hR hbd hpb
          (Or.inr (by rcases hp with rfl | rfl | rfl <;> omega))
          ⟨0, Nat.zero_lt_one, by rw [BitVec.add_zero]⟩ h
      · rw [dlen_bv] at h
        have hpb : 1656 + 8 * p + 8 ≤ abiSlot := by rcases hp with rfl | rfl | rfl <;> simp [abiSlot]
        exact memSpan_offset_disjoint_contains_false hR hbd hpb
          (Or.inr (by rcases hp with rfl | rfl | rfl <;> omega))
          ⟨0, Nat.zero_lt_one, by rw [BitVec.add_zero]⟩ h
      · rw [dlen32_bv] at h
        have hpb : 3296 + 8 * p + 8 ≤ abiSlot := by rcases hp with rfl | rfl | rfl <;> simp [abiSlot]
        exact memSpan_offset_disjoint_contains_false hR hbd hpb
          (Or.inr (by rcases hp with rfl | rfl | rfl <;> omega))
          ⟨0, Nat.zero_lt_one, by rw [BitVec.add_zero]⟩ h
    · rw [globOff_bitvec] at hgl
      have hg12 : g.id < checkerTabMini.ng := by rcases hg with rfl | rfl | rfl <;> decide
      exact memSpan_offset_disjoint_contains_false hR hbd (globOff_bound hg12)
        (Or.inl (by omega)) ⟨0, Nat.zero_lt_one, by rw [BitVec.add_zero]⟩ hgl
  · intro g hg
    by_cases hphi : g = phiGVar
    · subst hphi
      change readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff phiGVar)) = _
      rw [hmBPhi]; exact hPhi
    · by_cases hplo : g = ploGVar
      · subst hplo
        change readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff ploGVar)) = _
        rw [hmBPlo]; exact hPlo
      · by_cases hmode : g = modeGVar
        · subst hmode
          change readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) = _
          rw [hmBMode]; exact hMode
        · have hneIds : g.id ≠ phiGVar.id ∧ g.id ≠ ploGVar.id ∧ g.id ≠ modeGVar.id := by
            refine ⟨fun h => hphi (by cases g; simp at h; subst h; rfl),
                    fun h => hplo (by cases g; simp at h; subst h; rfl),
                    fun h => hmode (by cases g; simp at h; subst h; rfl)⟩
          rw [hmBGlobOther g hphi hplo hmode, ← hAg g hg]
          apply hout.readWord64_eq
          have hgl := globOff_eq_nat g
          have hgb := globOff_bound hg
          have hr := resBase_ge_16
          rw [hgl]
          apply phaseBWriteSpan_disj_tabOff regionBase hReg64 (by omega)
            (by rw [Int.toNat_natCast]; exact hgb)
            (by rw [Int.toNat_natCast]; omega)
            (fun p hp => by
              rw [Int.toNat_natCast]
              refine ⟨by rcases hp with rfl | rfl | rfl <;> omega,
                by rcases hp with rfl | rfl | rfl <;> omega,
                by rcases hp with rfl | rfl | rfl <;> omega⟩)
            (fun g' hg' => by
              rw [Int.toNat_natCast]
              have hne' : g.id ≠ g'.id := by
                rcases hg' with rfl | rfl | rfl
                · exact hneIds.1
                · exact hneIds.2.1
                · exact hneIds.2.2
              omega)

theorem phaseB_progMemRel_of_phaseA
    {inBase pinsBase regionBase : BitVec 64} {inLen pinsLen : Nat}
    (hIn64 : inBase.toNat + inLen ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pinsLen ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjInPins : MemSpan.disjoint ⟨inBase, inLen⟩ ⟨pinsBase, pinsLen⟩)
    (hDisjInReg : MemSpan.disjoint ⟨inBase, inLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pinsLen⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    {rmemA rmemB : ByteMem} {m1 : _root_.L.Mem} {retA : _root_.L.Word}
    (hRelA : ProgMemRel checkerTabMini
      (checkerLayoutA inBase pinsBase regionBase inLen pinsLen hIn64 hPins64 hRegAlign hReg64 hDisjInPins hDisjInReg hDisjPinsReg)
      rmemA m1)
    (hm1Sz : (m1.words (.t0 L.Arena.OUT)).size = abiWords)
    (hout : ProgMemOutside (phaseBWriteSpan regionBase) rmemA rmemB)
    (hPhi : readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff phiGVar)) =
      (retA - 9223372036854775808).toBitVec)
    (hPlo : readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff ploGVar)) = 0#64)
    (hMode : readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) = 2#64)
    (h180B : readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 180)) = 0#64)
    (h180L : readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 180)) = 0#64)
    (h182B : readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 182)) = 0#64)
    (h182L : readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 182)) = 0#64)
    (h181B : readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 181)) =
      regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.slotOf 180))
    (h181L : readWord64 rmemB (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 181)) =
      BitVec.ofNat 64 L.Arena.hdrW) :
    ProgMemRel checkerTabMini
      (checkerLayoutB inBase pinsBase regionBase inLen pinsLen hIn64 hPins64 hRegAlign hReg64 hDisjInPins hDisjInReg hDisjPinsReg)
      rmemB (phaseBMem m1 retA) :=
  phaseB_progMemRel_gen L.Arena.hdrW (by decide) (by decide) (by decide)
    hIn64 hPins64 hRegAlign hReg64 hDisjInPins hDisjInReg hDisjPinsReg
    hRelA hm1Sz (fun _ => rfl) rfl rfl rfl (fun _ h1 h2 h3 => by simp [phaseBMem, h1, h2, h3])
    rfl (by simp [phaseBMem, (by decide : ploGVar ≠ phiGVar)])
    (by simp [phaseBMem, (by decide : modeGVar ≠ phiGVar), (by decide : modeGVar ≠ ploGVar)])
    (fun g h1 h2 h3 => by simp [phaseBMem, h1, h2, h3])
    hout hPhi hPlo hMode h180B h180L h182B h182L h181B h181L


theorem mul4_and_not1_cd (pc : Nat) (_hlt : 4 * pc < 2 ^ 64) :
    BitVec.ofNat 64 (4 * pc) &&& ~~~1#64 = BitVec.ofNat 64 (4 * pc) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_ofNat]
  have hlt64 : decide (i < 64) = true := decide_eq_true hi
  rw [hlt64, Bool.true_and]
  cases i with
  | zero =>
    have hm : (4 * pc) % 2 = 0 := by omega
    simp [hm]
  | succ i' =>
    have hdiv : 1 / 2 ^ (i' + 1) = 0 :=
      Nat.div_eq_of_lt (Nat.one_lt_pow (Nat.succ_ne_zero i') (by decide))
    have htb : Nat.testBit 1 (i' + 1) = false := by
      simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
    rw [htb]; simp


end ConAgua.RISCV.Bridge
