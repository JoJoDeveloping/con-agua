import ConAgua.RISCV.Bridge.CheckerDriverBase
import ConAgua.Checker.CheckARun

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Setup and Phase Simulation Helpers for Linked Checker Driver Proofs (`ConAgua.RISCV.Bridge.CheckerDriverSetup`)

Shared bitvec, memory-disjointness, Phase A setup, and Phase B descriptor/setup simulation
lemmas used by both `CheckerDriverFlat` and `CheckerDriverCmpSetup` / `CheckerDriverCmp`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard Lean axioms only.
-/

namespace ConAgua.RISCV.Bridge

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Compiler
open ConAgua.RISCV.Linker

/-! ## 1. Small BitVec, Shift-Step, and Memory Helpers -/

theorem checkerChipAsm_eq' :
    checkerChipAsm =
      checkerDriverAsm checkerTabMini ++ checkerCmpDriverAsm checkerTabMini ++ checkerFnsAsm :=
  rfl

theorem run_shImm_rd_step {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (op : ShiftImmOp) (rd rs1 : Reg) (sh : BitVec 6) (hrd : rd ≠ 0#5)
    (hlink : lkm.linkSpec (pre ++ [AsmItem.instr (.shImm op rd rs1 sh)] ++ post) =
      .ok (env.code, env.labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre)) :
    let st' := stepReg st rd (evalShiftImm op (st.getReg rs1) sh)
      (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
    RV64.run env.rom 1 st = .cont st' ∧
    st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)) ∧
    st'.getReg rd = evalShiftImm op (st.getReg rs1) sh ∧
    (∀ q, q ≠ rd → st'.getReg q = st.getReg q) ∧
    st'.mem = st.mem := by
  have hpc64 := linkResolved_sub_pc64 env pre [AsmItem.instr (.shImm op rd rs1 sh)] post hlink
  have htw : lkm.totalSize [AsmItem.instr (.shImm op rd rs1 sh)] = 1 := lkm.totalSize_instr _
  have hlt : 4 * lkm.totalSize pre < 2 ^ 64 := by rw [htw] at hpc64; omega
  have hstep := step_item_instr_lm lkm env.hrom pre post (.shImm op rd rs1 sh) hlink hlt st hpc
  let st' := stepReg st rd (evalShiftImm op (st.getReg rs1) sh)
    (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
  have hrun : RV64.run env.rom 1 st = .cont st' := by
    apply run_one_cont; rw [hstep]
    simp only [execInstr, pc_add_4_ofNat st.pc hpc, st', stepReg, setReg_mem]
  exact ⟨hrun, rfl, getReg_stepReg_eq st rd hrd _ _,
    fun q hq => getReg_stepReg_ne st rd q hq _ _, by simp [stepReg, setReg_mem]⟩

theorem slli_srli_clr63 (x : BitVec 64) (hx : 2 ^ 63 ≤ x.toNat) :
    evalShiftImm .srli (evalShiftImm .slli x 1#6) 1#6 = BitVec.ofNat 64 (x.toNat - 2 ^ 63) := by
  apply BitVec.eq_of_toNat_eq
  simp only [evalShiftImm, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 1 < 64)]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have hlt : x.toNat < 2 ^ 64 := x.isLt
  have hmod : x.toNat * 2 % 2 ^ 64 = 2 * (x.toNat - 2 ^ 63) := by omega
  rw [hmod]
  omega

theorem memEqOutside_mono {s1 s2 : MemSpan} {m1 m2 : ByteMem}
    (hsub : s1.sub s2) (h : MemEqOutside s1 m1 m2) : MemEqOutside s2 m1 m2 :=
  fun a ha => h a (fun h1 => ha (hsub a h1))

theorem memSpan_offset_sub_slot0 (regionBase : BitVec 64) {lo sz : Nat}
    (_hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hle : lo + sz ≤ abiSlot) :
    (⟨regionBase + BitVec.ofNat 64 lo, sz⟩ : MemSpan).sub ⟨regionBase, abiSlot⟩ := by
  have hNeedEq := checkerTabMini_abiNeed_eq
  have h184 : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; simp [abiSlot]
  intro a ⟨k, hk, ha⟩
  subst ha
  dsimp only [MemSpan.contains] at hk ⊢
  refine ⟨lo + k, by omega, ?_⟩
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem memSpan_offset_disjoint_contains_false {base : BitVec 64} {need lo1 sz1 lo2 sz2 : Nat}
    (hneed : base.toNat + need ≤ 2 ^ 64) (h1 : lo1 + sz1 ≤ need) (h2 : lo2 + sz2 ≤ need)
    (hd : lo1 + sz1 ≤ lo2 ∨ lo2 + sz2 ≤ lo1) {a : BitVec 64}
    (ha1 : (⟨base + BitVec.ofNat 64 lo1, sz1⟩ : MemSpan).contains a)
    (ha2 : (⟨base + BitVec.ofNat 64 lo2, sz2⟩ : MemSpan).contains a) : False := by
  rcases Nat.eq_zero_or_pos sz1 with rfl | hsz1
  · exact False.elim (by rcases ha1 with ⟨k, hk, _⟩; dsimp only [MemSpan.contains] at hk; omega)
  rcases Nat.eq_zero_or_pos sz2 with rfl | hsz2
  · exact False.elim (by rcases ha2 with ⟨k, hk, _⟩; dsimp only [MemSpan.contains] at hk; omega)
  have hdisj := memSpan_offset_disjoint_offset hneed h1 h2 hd
  have hv1 : (⟨base + BitVec.ofNat 64 lo1, sz1⟩ : MemSpan).valid := by
    dsimp only [MemSpan.valid]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  have hv2 : (⟨base + BitVec.ofNat 64 lo2, sz2⟩ : MemSpan).valid := by
    dsimp only [MemSpan.valid]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  exact MemSpan.disjoint_to_memDisjoint hv1 hv2 hdisj a ha1 ha2

theorem dbase_bv (p : Nat) :
    BitVec.ofInt 64 (checkerTabMini.dbase p) = BitVec.ofNat 64 (16 + 8 * p) := by
  simp only [Tab.dbase]
  rw [show (16 + 8 * (p : Int)) = ((16 + 8 * p : Nat) : Int) from by omega, BitVec.ofInt_natCast]

theorem dlen_bv (p : Nat) :
    BitVec.ofInt 64 (checkerTabMini.dlen p) = BitVec.ofNat 64 (1656 + 8 * p) := by
  simp only [Tab.dlen, t_nb, t_nw]
  rw [show (16 + 8 * ((2 + 203 : Nat) : Int) + 8 * (p : Int)) = ((1656 + 8 * p : Nat) : Int) from by omega,
    BitVec.ofInt_natCast]

theorem dlen32_bv (p : Nat) :
    BitVec.ofInt 64 (checkerTabMini.dlen32 p) = BitVec.ofNat 64 (3296 + 8 * p) := by
  simp only [Tab.dlen32, t_nb, t_nw]
  rw [show (16 + 16 * ((2 + 203 : Nat) : Int) + 8 * (p : Int)) = ((3296 + 8 * p : Nat) : Int) from by omega,
    BitVec.ofInt_natCast]

theorem memEqOutside_writeWord64_tabOff (m : ByteMem) (base : BitVec 64) (lo : Nat) (w : BitVec 64) :
    MemEqOutside ⟨base + BitVec.ofNat 64 lo, 8⟩ m
      (writeWord64 m (base + BitVec.ofNat 64 lo) w) :=
  MemEqOutside.writeWord64 m (base + BitVec.ofNat 64 lo) w fun _ hk => ⟨_, hk, rfl⟩

theorem checkerTabMini_args_lt_saveBase :
    checkerTabMini.args.toNat < (checkerTabMini.saveBase 0).toNat := by
  rw [checkerTabMini_saveBase_eq, checkerTabMini_args_eq]; omega

theorem drvRegsSaved_of_progMemOutside {regionBase : BitVec 64} {initSt : RV64.State}
    {P : BitVec 64 → Prop} {m1 m2 : ByteMem}
    (hout : ProgMemOutside P m1 m2)
    (hdisj : ∀ i, i < callerSaveRegs.length → ∀ k, k < 8 →
      ¬P (regionBase + BitVec.ofInt 64 (checkerTabMini.saveBase 0) +
        BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 k))
    (hsaved : DrvRegsSaved regionBase initSt m1) :
    DrvRegsSaved regionBase initSt m2 := by
  intro i hi
  rw [← hsaved i hi]
  apply loadBytes_congr
  intro k hk
  exact hout _ (hdisj i hi k hk)

theorem drvRegsSaved_of_memEqOutside_le_args
    {regionBase : BitVec 64} {initSt : RV64.State}
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini ≤ 2 ^ 64)
    {off sz : Nat} (hle : off + sz ≤ checkerTabMini.args.toNat)
    {m1 m2 : ByteMem}
    (heq : MemEqOutside ⟨regionBase + BitVec.ofNat 64 off, sz⟩ m1 m2)
    (hsaved : DrvRegsSaved regionBase initSt m1) :
    DrvRegsSaved regionBase initSt m2 := by
  have hNeedEq := checkerTabMini_abiNeed_eq
  have hSlotLe : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; simp [abiSlot]
  have hR : regionBase.toNat + abiSlot ≤ 2 ^ 64 := by omega
  have hnn := checkerTabMini_saveBase_nonneg
  have hleSlot := checkerTabMini_saveBase_le_abiSlot
  have hcoe : ((checkerTabMini.saveBase 0).toNat : Int) = checkerTabMini.saveBase 0 :=
    Int.toNat_of_nonneg hnn
  have hltSave : checkerTabMini.args.toNat < (checkerTabMini.saveBase 0).toNat :=
    checkerTabMini_args_lt_saveBase
  apply drvRegsSaved_of_memEqOutside heq _ hsaved
  intro i hi k hk hc
  have hlen : callerSaveRegs.length = 16 := rfl
  have hcast : BitVec.ofInt 64 (checkerTabMini.saveBase 0) =
      BitVec.ofNat 64 (checkerTabMini.saveBase 0).toNat := by
    rw [← BitVec.ofInt_natCast, hcoe]
  rw [hcast, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add] at hc
  exact memSpan_offset_disjoint_contains_false hR
    (by omega : (checkerTabMini.saveBase 0).toNat + (8 * i + k) + 1 ≤ abiSlot)
    (by omega : off + sz ≤ abiSlot)
    (Or.inr (by omega))
    ⟨0, Nat.zero_lt_one, by rw [BitVec.add_zero]⟩ hc

theorem drvRegsSaved_of_callWriteMask_eq
    (L : ProgLayout checkerTabMini)
    {regionBase : BitVec 64} {initSt : RV64.State}
    {m1 m2 : ByteMem} (callerSp : BitVec 64)
    (hTabSave : checkerTabMini.saveBase 0 + 128 ≤ (L.tabBytes : Int))
    (hMask : ProgMemOutside (CallWriteMask L callerSp) m1 m2)
    (hsaved : DrvRegsSaved L.T initSt m1)
    (hT : L.T = regionBase) :
    DrvRegsSaved regionBase initSt m2 :=
  hT ▸ drvRegsSaved_of_callWriteMask callerSp hTabSave hMask hsaved

theorem drvRegsSaved_of_writeWord64_lt_args
    {regionBase : BitVec 64} {initSt : RV64.State}
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini ≤ 2 ^ 64)
    {off : Int} (hnn : 0 ≤ off) (hle : off.toNat + 8 ≤ checkerTabMini.args.toNat)
    {m : ByteMem} (wval : BitVec 64)
    (hsaved : DrvRegsSaved regionBase initSt m) :
    DrvRegsSaved regionBase initSt (writeWord64 m (regionBase + BitVec.ofInt 64 off) wval) := by
  have hcoe : (off.toNat : Int) = off := Int.toNat_of_nonneg hnn
  have hcast : BitVec.ofInt 64 off = BitVec.ofNat 64 off.toNat := by
    rw [← BitVec.ofInt_natCast, hcoe]
  rw [hcast]
  exact drvRegsSaved_of_memEqOutside_le_args hReg64 hle
    (memEqOutside_writeWord64_tabOff m regionBase off.toNat wval) hsaved

theorem checkerLayout_stack_diff (regionBase : BitVec 64)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64) :
    (regionBase + BitVec.ofNat 64 (abiSlot + abiStack)).toNat -
      (regionBase + BitVec.ofNat 64 abiSlot).toNat = abiStack := by
  have hNeedEq := checkerTabMini_abiNeed_eq
  have h1 : abiSlot + abiStack < 2 ^ 64 := by simp [abiSlot, abiStack]
  have h2 : regionBase.toNat + (abiSlot + abiStack) < 2 ^ 64 := by
    have : abiSlot + abiStack ≤ 205 * abiSlot := by simp [abiSlot, abiStack]
    omega
  have h3 : abiSlot < 2 ^ 64 := by simp [abiSlot]
  have h4 : regionBase.toNat + abiSlot < 2 ^ 64 := by
    have : abiSlot ≤ 205 * abiSlot := by simp [abiSlot]
    omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4]
  omega

theorem globOff_eq_nat (g : GVar) :
    checkerTabMini.globOff g = ((checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + g.id) : Nat) : Int) := by
  have hrnn : 0 ≤ checkerTabMini.resBase := ProgLayout.resBase_nonneg checkerTabMini
  have hres : checkerTabMini.resBase = (checkerTabMini.resBase.toNat : Int) :=
    (Int.toNat_of_nonneg hrnn).symm
  unfold Tab.globOff Tab.globBase
  rw [hres, show (8 : Int) = ((8 : Nat) : Int) from rfl,
    ← Int.natCast_mul, ← Int.natCast_mul, ← Int.natCast_add, ← Int.natCast_add]
  exact congrArg Nat.cast (by omega)

theorem resBase_ge_16 : 16 + 24 * 205 ≤ checkerTabMini.resBase.toNat := by
  rw [checkerTabMini_resBase_eq, Int.toNat_natCast]; omega

theorem globOff_bitvec (g : GVar) :
    BitVec.ofInt 64 (checkerTabMini.globOff g) =
      BitVec.ofNat 64 (checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + g.id)) := by
  rw [globOff_eq_nat, BitVec.ofInt_natCast]

theorem globOff_bound {g : GVar} (hg : g.id < checkerTabMini.ng) :
    checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + g.id) + 8 ≤ abiSlot := by
  have hargs := checkerTabMini_args_lt
  rw [checkerTabMini_args_eq, Int.toNat_natCast] at hargs
  rw [t_ng] at hg
  rw [checkerTabMini_resBase_eq, Int.toNat_natCast, t_nxres]
  omega

theorem resultsInState_a0 {L : ProgLayout checkerTabMini} {r : RV64.State}
    {vs : List _root_.L.Word} (hres : ResultsInState checkerTabMini L r vs) :
    r.getReg AbiReg.a0 = (vs.headD 0).toBitVec := by
  have h0 : 0 < min (min (max 1 vs.length) checkerTabMini.nres) maxRes := by
    rw [t_nres]; simp only [maxRes]; omega
  have h := hres.1 0 h0
  change r.getReg AbiReg.a0 = (vs.getD 0 0).toBitVec at h
  rw [h]; cases vs <;> rfl

/-! ## 2. Phase A Setup Simulation and Entry `ProgMemRel` -/

private theorem drvPhaseASetup_sim_gen (env : CodeEnvGen checkerLM) (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (pre post : List AsmItem)
    (hlink : checkerLM.linkSpec (pre ++ drvPhaseASetup checkerTabMini ++ post) =
      .ok (env.code, env.labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (checkerLM.totalSize pre +
        checkerLM.totalSize (drvPhaseASetup checkerTabMini))) ∧
      st'.getReg AbiReg.gp = regionBase ∧
      st'.getReg AbiReg.s0 = BitVec.ofNat 64 (abiFuel - 2) ∧
      st'.getReg AbiReg.sp = readWord64 st.mem regionBase ∧
      st'.getReg AbiReg.s2 = st.getReg AbiReg.s2 ∧
      st'.getReg AbiReg.t0 = regionBase + BitVec.ofInt 64 checkerTabMini.args ∧
      st'.getReg AbiReg.t1 = 0#64 ∧
      st'.mem = writeWord64 st.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) 3#64 := by
  let cModeLi := li AbiReg.t1 (BitVec.ofNat 64 3)
  let cModeSt := storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (checkerTabMini.globOff modeGVar)
  let cFuelLi := li AbiReg.s0 (BitVec.ofNat 64 (abiFuel - 1))
  let cLdSp := Asm.ld AbiReg.sp AbiReg.gp
  let cBeq := Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel
  let cDec := Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)
  let cArgs := addImmOff AbiReg.t0 AbiReg.gp AbiReg.t2 checkerTabMini.args
  let cT1 := li AbiReg.t1 0#64
  have hl1 : checkerLM.linkSpec (pre ++ cModeLi ++
      (cModeSt ++ cFuelLi ++ [cLdSp, cBeq, cDec] ++ cArgs ++ cT1 ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [drvPhaseASetup, cModeLi, cModeSt, cFuelLi, cLdSp, cBeq, cDec, cArgs, cT1,
      List.cons_append, List.nil_append, List.append_assoc] using hlink
  have hpc1_64 := linkResolved_sub_pc64 env pre cModeLi _ hl1
  obtain ⟨s1, hrun1, hoth1, ht1_1, hm1, hpc1⟩ :=
    li_correct_lm checkerLM env.hrom pre _ AbiReg.t1 (by decide)
      (BitVec.ofNat 64 3) hl1 hpc1_64 st hpc
  let p1 := pre ++ cModeLi
  have hpc1' : s1.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p1) := by
    simpa only [p1, checkerLM.totalSize_append] using hpc1
  have hs1gp : s1.getReg AbiReg.gp = regionBase := (hoth1 _ (by decide)).trans hgp
  have hl2 : checkerLM.linkSpec (p1 ++ cModeSt ++
      (cFuelLi ++ [cLdSp, cBeq, cDec] ++ cArgs ++ cT1 ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p1, List.append_assoc] using hl1
  have hpc2_64 := linkResolved_sub_pc64 env p1 cModeSt _ hl2
  have halMode : isAligned (s1.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) 8 = true := by
    rw [hs1gp, globOff_bitvec]
    refine isAligned8_add_nat_mul8 regionBase hRegAlign _ ?_
    have hrmNat : checkerTabMini.resBase.toNat = 16 + 24 * 205 + 8 * checkerTabMini.romWords := by
      rw [checkerTabMini_resBase_eq, Int.toNat_natCast]
    rw [hrmNat, t_nxres]; omega
  obtain ⟨s2, hrun2, hoth2, hm2, hpc2⟩ :=
    storeMemOff_sd_correct_lm checkerLM env.hrom p1 _ AbiReg.gp AbiReg.t1 AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.globOff modeGVar) hl2 hpc2_64 s1 hpc1' halMode
  let p2 := p1 ++ cModeSt
  have hpc2' : s2.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p2) := by
    simpa only [p2, checkerLM.totalSize_append] using hpc2
  have hs2gp : s2.getReg AbiReg.gp = regionBase := (hoth2 _ (by decide)).trans hs1gp
  have hs2m : s2.mem = writeWord64 st.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) 3#64 := by
    rw [hm2, hs1gp, ht1_1, hm1]
  have hl3 : checkerLM.linkSpec (p2 ++ cFuelLi ++
      ([cLdSp, cBeq, cDec] ++ cArgs ++ cT1 ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p2, List.append_assoc] using hl2
  have hpc3_64 := linkResolved_sub_pc64 env p2 cFuelLi _ hl3
  obtain ⟨s3, hrun3, hoth3, hs0_3, hm3, hpc3⟩ :=
    li_correct_lm checkerLM env.hrom p2 _ AbiReg.s0 (by decide)
      (BitVec.ofNat 64 (abiFuel - 1)) hl3 hpc3_64 s2 hpc2'
  let p3 := p2 ++ cFuelLi
  have hpc3' : s3.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p3) := by
    simpa only [p3, checkerLM.totalSize_append] using hpc3
  have hs3gp : s3.getReg AbiReg.gp = regionBase := (hoth3 _ (by decide)).trans hs2gp
  have hl4 : checkerLM.linkSpec (p3 ++ [Asm.raw (.load .ld AbiReg.sp AbiReg.gp 0#12)] ++
      ([cBeq, cDec] ++ cArgs ++ cT1 ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p3, cLdSp, Asm.ld, Asm.raw, List.cons_append, List.nil_append, List.append_assoc] using hl3
  have hpc4_64 := linkResolved_sub_pc64 env p3 [Asm.raw (.load .ld AbiReg.sp AbiReg.gp 0#12)] _ hl4
  have hlt4_64 : 4 * (checkerLM.totalSize p3 + 1) < 2 ^ 64 := by
    simpa only [Asm.raw, checkerLM.totalSize_instr] using hpc4_64
  have halSp : isAligned (s3.getReg AbiReg.gp + sextImm12 0#12) 8 = true := by
    have hz : sextImm12 0#12 = 0#64 := rfl
    rw [hs3gp, hz, BitVec.add_zero]; exact hRegAlign
  obtain ⟨hr4, hpc4, hsp4, hoth4, hm4⟩ :=
    step_ld_off env p3 _ AbiReg.sp AbiReg.gp 0#12 (by decide) hl4 hlt4_64 s3 hpc3' halSp
  let s4 := stepReg s3 AbiReg.sp (readWord64 s3.mem (s3.getReg AbiReg.gp + sextImm12 0#12)) (s3.pc + 4#64)
  let p4 := p3 ++ [cLdSp]
  have hpc4' : s4.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p4) := by
    simpa only [p4, cLdSp, Asm.ld, Asm.raw, checkerLM.totalSize_append, checkerLM.totalSize_instr] using hpc4
  have hs4s0 : s4.getReg AbiReg.s0 = BitVec.ofNat 64 (abiFuel - 1) :=
    (hoth4 _ (by decide)).trans hs0_3
  have hs4sp : s4.getReg AbiReg.sp = readWord64 st.mem regionBase := by
    have hz : sextImm12 0#12 = 0#64 := rfl
    rw [hsp4, hs3gp, hz, BitVec.add_zero, hm3, hs2m]
    have hdisjMode : 0 + 8 ≤ (checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + modeGVar.id)) ∨
        (checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + modeGVar.id)) + 8 ≤ 0 := by
      have hr := resBase_ge_16
      left; omega
    have hneedEq := checkerTabMini_abiNeed_eq
    have hgb := globOff_bound (g := modeGVar) (by decide)
    have h184 : abiSlot ≤ abiNeed checkerTabMini := by rw [hneedEq]; simp [abiSlot]
    have hrw := readWord64_writeWord64_tabOff (m := st.mem) (base := regionBase) (need := abiSlot)
      (by omega) (off1 := 0) (off2 := checkerTabMini.globOff modeGVar)
      (by omega) (by rw [globOff_eq_nat]; omega)
      (by omega) (by rw [globOff_eq_nat, Int.toNat_natCast]; exact hgb)
      (by rw [globOff_eq_nat, Int.toNat_natCast]; exact hdisjMode) 3#64
    have h0bv : BitVec.ofInt 64 0 = 0#64 := rfl
    rw [h0bv, BitVec.add_zero] at hrw
    exact hrw
  have hl5 : checkerLM.linkSpec (p4 ++ [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel] ++
      ([cDec] ++ cArgs ++ cT1 ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p4, cLdSp, Asm.ld, Asm.raw, cBeq, List.cons_append, List.nil_append, List.append_assoc] using hl4
  have hbr5 := run_br_step env p4 _ .beq AbiReg.s0 AbiReg.zero exhaustedLabel
    env.exhaustedTarget env.hexhaustedLbl (by decide) hl5 s4 hpc4'
  have hev5 : evalBranch .beq (s4.getReg AbiReg.s0) (s4.getReg AbiReg.zero) = false := by
    rw [hs4s0, getReg_zero]
    have hne : BitVec.ofNat 64 (abiFuel - 1) ≠ 0#64 := by
      simp [abiFuel]
    simp [evalBranch, hne]
  rw [hev5] at hbr5
  obtain ⟨k5, s5, _, hrun5, hpc5, hoth5, _, hm5⟩ := hbr5
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc5
  let p5 := p4 ++ [cBeq]
  have hpc5' : s5.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p5) := by
    rw [hpc5]; dsimp only [p5]; rw [checkerLM.totalSize_append p4 _]; rfl
  have hl6 : checkerLM.linkSpec (p5 ++ [Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++
      (cArgs ++ cT1 ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p5, cDec, List.cons_append, List.nil_append, List.append_assoc] using hl5
  obtain ⟨hr6, hpc6, hs0_6, hoth6, hm6⟩ :=
    run_aluImm_rd_step env p5 _ .addi AbiReg.s0 AbiReg.s0 (-1#12) (by decide) hl6 s5 hpc5'
  let s6 := stepReg s5 AbiReg.s0 (evalAluImm .addi (s5.getReg AbiReg.s0) (-1#12))
    (BitVec.ofNat 64 (4 * (checkerLM.totalSize p5 + 1)))
  let p6 := p5 ++ [cDec]
  have hpc6' : s6.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p6) := by
    simpa only [p6, cDec, checkerLM.totalSize_append, Asm.addi, checkerLM.totalSize_instr] using hpc6
  have hl7 : checkerLM.linkSpec (p6 ++ cArgs ++ (cT1 ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p6, List.append_assoc] using hl6
  have hpc7_64 := linkResolved_sub_pc64 env p6 cArgs _ hl7
  have hs6gp : s6.getReg AbiReg.gp = regionBase :=
    (hoth6 _ (by decide)).trans ((hoth5 _ (by decide)).trans ((hoth4 _ (by decide)).trans hs3gp))
  obtain ⟨s7, hrun7, hoth7, ht0_7, hm7, hpc7⟩ :=
    addImmOff_correct_lm checkerLM env.hrom p6 _ AbiReg.t0 AbiReg.gp AbiReg.t2
      (by decide) (by decide) (by decide) checkerTabMini.args hl7 hpc7_64 s6 hpc6'
  let p7 := p6 ++ cArgs
  have hpc7' : s7.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p7) := by
    simpa only [p7, checkerLM.totalSize_append] using hpc7
  have hl8 : checkerLM.linkSpec (p7 ++ cT1 ++ post) =
      .ok (env.code, env.labels) := by
    simpa only [p7, List.append_assoc] using hl7
  have hpc8_64 := linkResolved_sub_pc64 env p7 cT1 post hl8
  obtain ⟨s8, hrun8, hoth8, ht1_8, hm8, hpc8⟩ :=
    li_correct_lm checkerLM env.hrom p7 post AbiReg.t1 (by decide) 0#64 hl8 hpc8_64 s7 hpc7'
  have hpcEnd : checkerLM.totalSize (p7 ++ cT1) =
      checkerLM.totalSize pre + checkerLM.totalSize (drvPhaseASetup checkerTabMini) := by
    dsimp only [p7, p6, p5, p4, p3, p2, p1, drvPhaseASetup,
      cModeLi, cModeSt, cFuelLi, cLdSp, cBeq, cDec, cArgs, cT1]
    simp only [checkerLM.totalSize_append, checkerLM.totalSize_cons, checkerLM.totalSize_nil,
      Nat.add_zero, Nat.add_assoc]
  have hs8gp : s8.getReg AbiReg.gp = regionBase :=
    (hoth8 _ (by decide)).trans ((hoth7 _ (by decide) (by decide)).trans hs6gp)
  have hs8s0 : s8.getReg AbiReg.s0 = BitVec.ofNat 64 (abiFuel - 2) := by
    rw [hoth8 _ (by decide), hoth7 _ (by decide) (by decide), hs0_6]
    change evalAluImm .addi (s5.getReg AbiReg.s0) (-1#12) = BitVec.ofNat 64 (abiFuel - 2)
    rw [hoth5 _ (by decide), hs4s0]
    simp [abiFuel]; decide
  have hs8sp : s8.getReg AbiReg.sp = readWord64 st.mem regionBase := by
    rw [hoth8 _ (by decide), hoth7 _ (by decide) (by decide), hoth6 _ (by decide),
      hoth5 _ (by decide), hs4sp]
  have hs8s2 : s8.getReg AbiReg.s2 = st.getReg AbiReg.s2 := by
    rw [hoth8 _ (by decide), hoth7 _ (by decide) (by decide), hoth6 _ (by decide),
      hoth5 _ (by decide), hoth4 _ (by decide), hoth3 _ (by decide), hoth2 _ (by decide), hoth1 _ (by decide)]
  have hs8t0 : s8.getReg AbiReg.t0 = regionBase + BitVec.ofInt 64 checkerTabMini.args := by
    rw [hoth8 _ (by decide), ht0_7, hs6gp]
  have hs8m : s8.mem = writeWord64 st.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) 3#64 := by
    rw [hm8, hm7, hm6, hm5, hm4, hm3, hs2m]
  refine ⟨checkerLM.totalSize cModeLi + checkerLM.totalSize cModeSt +
      checkerLM.totalSize cFuelLi + 1 + k5 + 1 + checkerLM.totalSize cArgs +
      checkerLM.totalSize cT1, s8, ?_, ?_, hs8gp, hs8s0, hs8sp, hs8s2, hs8t0, ht1_8, hs8m⟩
  · rw [run_add, run_add, run_add, run_add, run_add, run_add, run_add, hrun1]
    dsimp only; rw [hrun2]; dsimp only; rw [hrun3]; dsimp only; rw [hr4]
    dsimp only; rw [hrun5]; dsimp only; rw [hr6]; dsimp only; rw [hrun7]; exact hrun8
  · rw [hpc8, ← checkerLM.totalSize_append p7 cT1, hpcEnd]

theorem drvPhaseASetup_sim (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (pre post : List AsmItem)
    (hlink : checkerLM.linkSpec (pre ++ drvPhaseASetup checkerTabMini ++ post) =
      .ok (checkerEnv.code, checkerEnv.labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase) :
    ∃ k st',
      RV64.run checkerEnv.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (checkerLM.totalSize pre +
        checkerLM.totalSize (drvPhaseASetup checkerTabMini))) ∧
      st'.getReg AbiReg.gp = regionBase ∧
      st'.getReg AbiReg.s0 = BitVec.ofNat 64 (abiFuel - 2) ∧
      st'.getReg AbiReg.sp = readWord64 st.mem regionBase ∧
      st'.getReg AbiReg.s2 = st.getReg AbiReg.s2 ∧
      st'.getReg AbiReg.t0 = regionBase + BitVec.ofInt 64 checkerTabMini.args ∧
      st'.getReg AbiReg.t1 = 0#64 ∧
      st'.mem = writeWord64 st.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar)) 3#64 := by
  exact drvPhaseASetup_sim_gen checkerEnv regionBase hRegAlign hReg64 pre post hlink st hpc hgp

theorem phaseInit_hdr_and_rel
    {inBase pinsBase regionBase : BitVec 64}
    {inBytes pins : ByteArray}
    (modeVal : _root_.L.Word)
    (initMem m0 m1 m2 m3 m4 m5 m6 m7 : ByteMem)
    (hin63 : inBytes.size < 2 ^ 63) (hpins63 : pins.size < 2 ^ 63)
    (hIn64 : inBase.toNat + inBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjInPins : MemSpan.disjoint ⟨inBase, inBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjInReg : MemSpan.disjoint ⟨inBase, inBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hInMem : ∀ i, (hi : i < inBytes.size) → initMem (inBase + BitVec.ofNat 64 i) = inBytes[i].toBitVec)
    (hPinsMem : ∀ i, (hi : i < pins.size) → initMem (pinsBase + BitVec.ofNat 64 i) = pins[i].toBitVec)
    (hRegZero : ∀ k, k < abiNeed checkerTabMini → initMem (regionBase + BitVec.ofNat 64 k) = 0#8)
    (hout0 : MemEqOutside (callerSaveSpan regionBase (checkerTabMini.saveBase 0)) initMem m0)
    (hout1 : MemEqOutside ⟨regionBase, 16⟩ m0 m1)
    (hHdrTop1 : readWord64 m1 regionBase = regionBase + BitVec.ofNat 64 (abiSlot + abiStack))
    (hHdrLim1 : readWord64 m1 (regionBase + 8#64) = regionBase + BitVec.ofNat 64 abiSlot)
    (hout2 : MemEqOutside ⟨regionBase + BitVec.ofNat 64 16, 8 * 205⟩ m1 m2)
    (hBase2 : ∀ i, i < checkerTabMini.nb + checkerTabMini.nw →
      readWord64 m2 (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase i)) =
        if i < 2 then if (i == 0) = true then inBase else pinsBase else
          regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.slotOf i))
    (hout3 : MemEqOutside ⟨regionBase + BitVec.ofNat 64 (16 + 8 * 205), 8 * 205⟩ m2 m3)
    (hLen3 : ∀ i, i < checkerTabMini.nb + checkerTabMini.nw →
      readWord64 m3 (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen i)) =
        if i < 2 then if (i == 0) = true then BitVec.ofNat 64 inBytes.size else BitVec.ofNat 64 pins.size
        else BitVec.ofNat 64 abiWords)
    (hout4 : MemEqOutside ⟨regionBase + BitVec.ofNat 64 (16 + 16 * 205), 8 * 205⟩ m3 m4)
    (hout5 : MemEqOutside ⟨regionBase + BitVec.ofNat 64 checkerTabMini.romBase.toNat,
      8 * checkerTabMini.romWords⟩ m4 m5)
    (hRom5 : ∀ m, (hm : m < checkerTabMini.rom.length) →
      m5 (regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + m)) = checkerTabMini.rom[m].toBitVec)
    (hout6 : MemEqOutside ⟨regionBase + BitVec.ofNat 64 checkerTabMini.resBase.toNat,
      8 * (checkerTabMini.nxres + checkerTabMini.ng)⟩ m5 m6)
    (hZero6 : ∀ i, i < checkerTabMini.nxres + checkerTabMini.ng →
      readWord64 m6 (regionBase + BitVec.ofNat 64 checkerTabMini.resBase.toNat + BitVec.ofNat 64 (8 * i)) = 0#64)
    (hm7 : m7 = writeWord64 m6 (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar))
      modeVal.toBitVec) :
    let LA := checkerLayoutA inBase pinsBase regionBase inBytes.size pins.size
      hIn64 hPins64 hRegAlign hReg64 hDisjInPins hDisjInReg hDisjPinsReg
    MemEqOutside ⟨regionBase, abiSlot⟩ initMem m7 ∧
    readWord64 m6 regionBase = LA.stackTop ∧
    TabHeaderOk LA m7 ∧
    ProgMemRel checkerTabMini LA m7 (loadMemMini inBytes pins (fun _ => abiWords) modeVal) := by
  intro LA
  have hNeedEq : abiNeed checkerTabMini = 205 * abiSlot := checkerTabMini_abiNeed_eq
  have hargsLt := checkerTabMini_args_lt
  have hresNat : checkerTabMini.resBase.toNat = 16 + 24 * 205 + 8 * checkerTabMini.romWords := by
    rw [checkerTabMini_resBase_eq, Int.toNat_natCast]
  have hromNat : checkerTabMini.romBase.toNat = 16 + 24 * 205 := by
    rw [checkerTabMini_romBase_eq, Int.toNat_natCast]
  have hargsNat : checkerTabMini.args.toNat =
      16 + 24 * 205 + 8 * checkerTabMini.romWords + 8 * 2 + 8 * 12 := by
    rw [checkerTabMini_args_eq, Int.toNat_natCast]
  have haNat : checkerTabMini.args.toNat =
      checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + checkerTabMini.ng) := by
    rw [hargsNat, hresNat, t_nxres, t_ng]
  have hresEq : checkerTabMini.resBase.toNat = checkerTabMini.romBase.toNat + 8 * checkerTabMini.romWords := by
    rw [hresNat, hromNat]
  have hromBounds : checkerTabMini.romBase.toNat + 8 * checkerTabMini.romWords ≤ abiSlot := by omega
  have hresBounds : checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + checkerTabMini.ng) ≤ abiSlot := by omega
  have hromBaseGe : 16 + 24 * 205 ≤ checkerTabMini.romBase.toNat := by omega
  have h211 : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; simp [abiSlot]
  have hR : regionBase.toNat + abiSlot ≤ 2 ^ 64 := by omega
  have hout7Slot0 : MemEqOutside ⟨regionBase, abiSlot⟩ initMem m7 := by
    have hinit0 : MemEqOutside ⟨regionBase, abiSlot⟩ initMem m0 := by
      have hnn := checkerTabMini_saveBase_nonneg
      have hcoe : ((checkerTabMini.saveBase 0).toNat : Int) = checkerTabMini.saveBase 0 :=
        Int.toNat_of_nonneg hnn
      have hle128 : (checkerTabMini.saveBase 0).toNat + 128 ≤ abiSlot := by
        have := checkerTabMini_saveBase_le_abiSlot; omega
      have hcast : BitVec.ofInt 64 (checkerTabMini.saveBase 0) =
          BitVec.ofNat 64 (checkerTabMini.saveBase 0).toNat := by
        rw [← BitVec.ofInt_natCast, hcoe]
      have hsub : (callerSaveSpan regionBase (checkerTabMini.saveBase 0)).sub ⟨regionBase, abiSlot⟩ := by
        dsimp only [callerSaveSpan]
        rw [hcast]
        exact memSpan_offset_sub_slot0 regionBase hReg64 hle128
      exact memEqOutside_mono hsub hout0
    have h01 : MemEqOutside ⟨regionBase, abiSlot⟩ m0 m1 :=
      memEqOutside_mono (by
        have hsub := memSpan_offset_sub_slot0 regionBase hReg64 (by simp [abiSlot] : 0 + 16 ≤ abiSlot)
        simpa only [BitVec.add_zero] using hsub) hout1
    have h12 : MemEqOutside ⟨regionBase, abiSlot⟩ m1 m2 :=
      memEqOutside_mono (memSpan_offset_sub_slot0 regionBase hReg64 (by simp [abiSlot])) hout2
    have h23 : MemEqOutside ⟨regionBase, abiSlot⟩ m2 m3 :=
      memEqOutside_mono (memSpan_offset_sub_slot0 regionBase hReg64 (by simp [abiSlot])) hout3
    have h34 : MemEqOutside ⟨regionBase, abiSlot⟩ m3 m4 :=
      memEqOutside_mono (memSpan_offset_sub_slot0 regionBase hReg64 (by simp [abiSlot])) hout4
    have h45 : MemEqOutside ⟨regionBase, abiSlot⟩ m4 m5 :=
      memEqOutside_mono (memSpan_offset_sub_slot0 regionBase hReg64 hromBounds) hout5
    have h56 : MemEqOutside ⟨regionBase, abiSlot⟩ m5 m6 :=
      memEqOutside_mono (memSpan_offset_sub_slot0 regionBase hReg64 hresBounds) hout6
    have h67 : MemEqOutside ⟨regionBase, abiSlot⟩ m6 m7 := by
      rw [hm7, globOff_bitvec]
      exact memEqOutside_mono (memSpan_offset_sub_slot0 regionBase hReg64
        (globOff_bound (g := modeGVar) (by decide)))
        (memEqOutside_writeWord64_tabOff m6 regionBase
          (checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + modeGVar.id))
          modeVal.toBitVec)
    exact hinit0.trans (h01.trans (h12.trans (h23.trans (h34.trans (h45.trans (h56.trans h67))))))
  have readAfter3to7 : ∀ (lo : Nat), lo + 8 ≤ 16 + 8 * 205 →
      readWord64 m7 (regionBase + BitVec.ofNat 64 lo) =
        readWord64 m2 (regionBase + BitVec.ofNat 64 lo) := by
    intro lo hlo
    have e23 : readWord64 m3 (regionBase + BitVec.ofNat 64 lo) =
        readWord64 m2 (regionBase + BitVec.ofNat 64 lo) :=
      MemEqOutside.readWord64_eq hout3 _ fun k hk hc =>
        memSpan_offset_disjoint_contains_false hR (by omega : lo + 8 ≤ abiSlot)
          (by simp [abiSlot] : 16 + 8 * 205 + 8 * 205 ≤ abiSlot) (Or.inl hlo) ⟨k, hk, rfl⟩ hc
    have e34 : readWord64 m4 (regionBase + BitVec.ofNat 64 lo) =
        readWord64 m3 (regionBase + BitVec.ofNat 64 lo) :=
      MemEqOutside.readWord64_eq hout4 _ fun k hk hc =>
        memSpan_offset_disjoint_contains_false hR (by omega : lo + 8 ≤ abiSlot)
          (by simp [abiSlot] : 16 + 16 * 205 + 8 * 205 ≤ abiSlot) (Or.inl (by omega)) ⟨k, hk, rfl⟩ hc
    have e45 : readWord64 m5 (regionBase + BitVec.ofNat 64 lo) =
        readWord64 m4 (regionBase + BitVec.ofNat 64 lo) :=
      MemEqOutside.readWord64_eq hout5 _ fun k hk hc =>
        memSpan_offset_disjoint_contains_false hR (by omega : lo + 8 ≤ abiSlot)
          hromBounds (Or.inl (by omega)) ⟨k, hk, rfl⟩ hc
    have e56 : readWord64 m6 (regionBase + BitVec.ofNat 64 lo) =
        readWord64 m5 (regionBase + BitVec.ofNat 64 lo) :=
      MemEqOutside.readWord64_eq hout6 _ fun k hk hc =>
        memSpan_offset_disjoint_contains_false hR (by omega : lo + 8 ≤ abiSlot)
          hresBounds (Or.inl (by omega)) ⟨k, hk, rfl⟩ hc
    have e67 : readWord64 m7 (regionBase + BitVec.ofNat 64 lo) =
        readWord64 m6 (regionBase + BitVec.ofNat 64 lo) := by
      rw [hm7, globOff_bitvec]
      exact MemEqOutside.readWord64_eq
        (memEqOutside_writeWord64_tabOff m6 regionBase
          (checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + modeGVar.id))
          modeVal.toBitVec)
        _ fun k hk hc =>
          memSpan_offset_disjoint_contains_false hR (by omega : lo + 8 ≤ abiSlot)
            (globOff_bound (g := modeGVar) (by decide)) (Or.inl (by omega)) ⟨k, hk, rfl⟩ hc
    rw [e67, e56, e45, e34, e23]
  have readAfter4to7 : ∀ (lo : Nat), 16 + 8 * 205 ≤ lo → lo + 8 ≤ 16 + 16 * 205 →
      readWord64 m7 (regionBase + BitVec.ofNat 64 lo) =
        readWord64 m3 (regionBase + BitVec.ofNat 64 lo) := by
    intro lo _ hhi
    have e34 : readWord64 m4 (regionBase + BitVec.ofNat 64 lo) =
        readWord64 m3 (regionBase + BitVec.ofNat 64 lo) :=
      MemEqOutside.readWord64_eq hout4 _ fun k hk hc =>
        memSpan_offset_disjoint_contains_false hR (by omega : lo + 8 ≤ abiSlot)
          (by simp [abiSlot] : 16 + 16 * 205 + 8 * 205 ≤ abiSlot) (Or.inl hhi) ⟨k, hk, rfl⟩ hc
    have e45 : readWord64 m5 (regionBase + BitVec.ofNat 64 lo) =
        readWord64 m4 (regionBase + BitVec.ofNat 64 lo) :=
      MemEqOutside.readWord64_eq hout5 _ fun k hk hc =>
        memSpan_offset_disjoint_contains_false hR (by omega : lo + 8 ≤ abiSlot)
          hromBounds (Or.inl (by omega)) ⟨k, hk, rfl⟩ hc
    have e56 : readWord64 m6 (regionBase + BitVec.ofNat 64 lo) =
        readWord64 m5 (regionBase + BitVec.ofNat 64 lo) :=
      MemEqOutside.readWord64_eq hout6 _ fun k hk hc =>
        memSpan_offset_disjoint_contains_false hR (by omega : lo + 8 ≤ abiSlot)
          hresBounds (Or.inl (by omega)) ⟨k, hk, rfl⟩ hc
    have e67 : readWord64 m7 (regionBase + BitVec.ofNat 64 lo) =
        readWord64 m6 (regionBase + BitVec.ofNat 64 lo) := by
      rw [hm7, globOff_bitvec]
      exact MemEqOutside.readWord64_eq
        (memEqOutside_writeWord64_tabOff m6 regionBase
          (checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + modeGVar.id))
          modeVal.toBitVec)
        _ fun k hk hc =>
          memSpan_offset_disjoint_contains_false hR (by omega : lo + 8 ≤ abiSlot)
            (globOff_bound (g := modeGVar) (by decide)) (Or.inl (by omega)) ⟨k, hk, rfl⟩ hc
    rw [e67, e56, e45, e34]
  have hm6Top : readWord64 m6 regionBase = LA.stackTop := by
    have hTopEq : LA.stackTop = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) := by
      simp [LA, checkerLayoutA]
    rw [hTopEq]
    have h0 : readWord64 m6 regionBase = readWord64 m2 regionBase := by
      have e23 : readWord64 m3 regionBase = readWord64 m2 regionBase :=
        MemEqOutside.readWord64_eq hout3 _ fun k hk hc =>
          memSpan_offset_disjoint_contains_false hR (by simp [abiSlot] : 0 + 8 ≤ abiSlot)
            (by simp [abiSlot] : 16 + 8 * 205 + 8 * 205 ≤ abiSlot) (Or.inl (by omega))
            ⟨k, hk, by rw [BitVec.add_zero]⟩ hc
      have e34 : readWord64 m4 regionBase = readWord64 m3 regionBase :=
        MemEqOutside.readWord64_eq hout4 _ fun k hk hc =>
          memSpan_offset_disjoint_contains_false hR (by simp [abiSlot] : 0 + 8 ≤ abiSlot)
            (by simp [abiSlot] : 16 + 16 * 205 + 8 * 205 ≤ abiSlot) (Or.inl (by omega))
            ⟨k, hk, by rw [BitVec.add_zero]⟩ hc
      have e45 : readWord64 m5 regionBase = readWord64 m4 regionBase :=
        MemEqOutside.readWord64_eq hout5 _ fun k hk hc =>
          memSpan_offset_disjoint_contains_false hR (by simp [abiSlot] : 0 + 8 ≤ abiSlot)
            hromBounds (Or.inl (by omega)) ⟨k, hk, by rw [BitVec.add_zero]⟩ hc
      have e56 : readWord64 m6 regionBase = readWord64 m5 regionBase :=
        MemEqOutside.readWord64_eq hout6 _ fun k hk hc =>
          memSpan_offset_disjoint_contains_false hR (by simp [abiSlot] : 0 + 8 ≤ abiSlot)
            hresBounds (Or.inl (by omega)) ⟨k, hk, by rw [BitVec.add_zero]⟩ hc
      rw [e56, e45, e34, e23]
    have h12 : readWord64 m2 regionBase = readWord64 m1 regionBase :=
      MemEqOutside.readWord64_eq hout2 _ fun k hk hc =>
        memSpan_offset_disjoint_contains_false hR (by simp [abiSlot] : 0 + 8 ≤ abiSlot)
          (by simp [abiSlot] : 16 + 8 * 205 ≤ abiSlot) (Or.inl (by omega))
          ⟨k, hk, by rw [BitVec.add_zero]⟩ hc
    rw [h0, h12, hHdrTop1]
  have hHdr : TabHeaderOk LA m7 := by
    have hTopEq : LA.stackTop = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) := by
      simp [LA, checkerLayoutA]
    have hLimEq : LA.stackLimit = regionBase + BitVec.ofNat 64 abiSlot := by
      simp [LA, checkerLayoutA]
    have hTEq : LA.T = regionBase := by simp [LA, checkerLayoutA]
    refine ⟨?_, ?_⟩
    · rw [hTEq, hTopEq]
      have h0 := readAfter3to7 0 (by omega)
      rw [BitVec.add_zero] at h0
      have h12 : readWord64 m2 regionBase = readWord64 m1 regionBase :=
        MemEqOutside.readWord64_eq hout2 _ fun k hk hc =>
          memSpan_offset_disjoint_contains_false hR (by simp [abiSlot] : 0 + 8 ≤ abiSlot)
            (by simp [abiSlot] : 16 + 8 * 205 ≤ abiSlot) (Or.inl (by omega))
            ⟨k, hk, by rw [BitVec.add_zero]⟩ hc
      rw [h0, h12, hHdrTop1]
    · rw [hTEq, hLimEq]
      have h8 := readAfter3to7 8 (by omega)
      have h12 : readWord64 m2 (regionBase + 8#64) = readWord64 m1 (regionBase + 8#64) :=
        MemEqOutside.readWord64_eq hout2 _ fun k hk hc =>
          memSpan_offset_disjoint_contains_false hR (by simp [abiSlot] : 8 + 8 ≤ abiSlot)
            (by simp [abiSlot] : 16 + 8 * 205 ≤ abiSlot) (Or.inl (by omega)) ⟨k, hk, rfl⟩ hc
      rw [h8, h12, hHdrLim1]
  have hMemRel : ProgMemRel checkerTabMini LA m7 (loadMemMini inBytes pins (fun _ => abiWords) modeVal) := by
    have hne : pbArr ≠ inArr := by decide
    have hInArr : (loadMemMini inBytes pins (fun _ => abiWords) modeVal).arr8 inArr = inBytes.data := by
      dsimp only [loadMemMini, _root_.L.Mem.arr8]; simp only [ite_true]
    have hPbArr : (loadMemMini inBytes pins (fun _ => abiWords) modeVal).arr8 pbArr = pins.data := by
      dsimp only [loadMemMini, _root_.L.Mem.arr8]; simp only [hne, ↓reduceIte]
    have hCapIn : LA.cap8 inArr = inBytes.size := by simp [LA, checkerLayoutA]
    have hCapPb : LA.cap8 pbArr = pins.size := by simp [LA, checkerLayoutA, hne]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a ha
      rcases checkerTabMini_bytePos_cases ha with rfl | rfl
      · refine ⟨by rw [hInArr, hCapIn]; exact Nat.le_refl _,
          by rw [hInArr]; change inBytes.size < 2 ^ 64; omega, ?_, ?_, ?_⟩
        · change readWord64 m7 (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen (checkerTabMini.pos8 inArr))) =
            BitVec.ofNat 64 inBytes.data.size
          rw [t_pos8_in]
          have hLenInt : BitVec.ofInt 64 (checkerTabMini.dlen 0) = BitVec.ofNat 64 (16 + 8 * 205) := by
            simp [Tab.dlen, t_nb, t_nw]
          rw [hLenInt, readAfter4to7 (16 + 8 * 205) (by omega) (by omega), ← hLenInt,
            hLen3 0 (by rw [t_nb, t_nw]; omega)]
          rfl
        · change readWord64 m7 (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase (checkerTabMini.pos8 inArr))) =
            inBase
          rw [t_pos8_in]
          have hBaseInt : BitVec.ofInt 64 (checkerTabMini.dbase 0) = BitVec.ofNat 64 16 := by
            simp [Tab.dbase]
          rw [hBaseInt, readAfter3to7 16 (by omega), ← hBaseInt,
            hBase2 0 (by rw [t_nb, t_nw]; omega)]
          rfl
        · intro i hi
          have hi' : i < inBytes.size := by rw [hInArr] at hi; exact hi
          have hnot : ¬(⟨regionBase, abiSlot⟩ : MemSpan).contains (LA.base8 inArr + BitVec.ofNat 64 i) := by
            have hdisjSub : MemSpan.disjoint ⟨inBase, inBytes.size⟩ ⟨regionBase, abiSlot⟩ := by
              have hdisj := hDisjInReg
              dsimp only [MemSpan.disjoint] at hdisj ⊢
              rw [hNeedEq] at hdisj
              rcases hdisj with h | h
              · exact Or.inl (by omega)
              · exact Or.inr (by omega)
            have hbaseEq : LA.base8 inArr = inBase := by simp [LA, checkerLayoutA]
            rw [hbaseEq]
            exact @MemSpan.disjoint_to_memDisjoint ⟨inBase, inBytes.size⟩ ⟨regionBase, abiSlot⟩
              hIn64 (by dsimp only [MemSpan.valid]; omega) hdisjSub _ ⟨i, hi', rfl⟩
          rw [hout7Slot0 _ hnot]
          have hbaseEq : LA.base8 inArr = inBase := by simp [LA, checkerLayoutA]
          rw [hbaseEq, hInMem i hi']
          simp only [hInArr]; rfl
      · refine ⟨by rw [hPbArr, hCapPb]; exact Nat.le_refl _,
          by rw [hPbArr]; change pins.size < 2 ^ 64; omega, ?_, ?_, ?_⟩
        · change readWord64 m7 (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen (checkerTabMini.pos8 pbArr))) =
            BitVec.ofNat 64 pins.data.size
          rw [t_pos8_pb]
          have hLenInt : BitVec.ofInt 64 (checkerTabMini.dlen 1) = BitVec.ofNat 64 (16 + 8 * 205 + 8) := by
            simp [Tab.dlen, t_nb, t_nw]
          rw [hLenInt, readAfter4to7 (16 + 8 * 205 + 8) (by omega) (by omega), ← hLenInt,
            hLen3 1 (by rw [t_nb, t_nw]; omega)]
          rfl
        · change readWord64 m7 (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase (checkerTabMini.pos8 pbArr))) =
            pinsBase
          rw [t_pos8_pb]
          have hBaseInt : BitVec.ofInt 64 (checkerTabMini.dbase 1) = BitVec.ofNat 64 (16 + 8) := by
            simp [Tab.dbase]
          rw [hBaseInt, readAfter3to7 (16 + 8) (by omega), ← hBaseInt,
            hBase2 1 (by rw [t_nb, t_nw]; omega)]
          rfl
        · intro i hi
          have hi' : i < pins.size := by rw [hPbArr] at hi; exact hi
          have hnot : ¬(⟨regionBase, abiSlot⟩ : MemSpan).contains (LA.base8 pbArr + BitVec.ofNat 64 i) := by
            have hdisjSub : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiSlot⟩ := by
              have hdisj := hDisjPinsReg
              dsimp only [MemSpan.disjoint] at hdisj ⊢
              rw [hNeedEq] at hdisj
              rcases hdisj with h | h
              · exact Or.inl (by omega)
              · exact Or.inr (by omega)
            have hbaseEq : LA.base8 pbArr = pinsBase := by simp [LA, checkerLayoutA, hne]
            rw [hbaseEq]
            exact @MemSpan.disjoint_to_memDisjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiSlot⟩
              hPins64 (by dsimp only [MemSpan.valid]; omega) hdisjSub _ ⟨i, hi', rfl⟩
          rw [hout7Slot0 _ hnot]
          have hbaseEq : LA.base8 pbArr = pinsBase := by simp [LA, checkerLayoutA, hne]
          rw [hbaseEq, hPinsMem i hi']
          simp only [hPbArr]; rfl
    · intro s hs
      have ⟨hlo, hhi⟩ := checkerTabMini_wordPos_bounds hs
      have hArr64 : (loadMemMini inBytes pins (fun _ => abiWords) modeVal).arr64 s = Array.replicate abiWords 0 := by
        dsimp only [loadMemMini, _root_.L.Mem.arr64]
      have hszEq : ((loadMemMini inBytes pins (fun _ => abiWords) modeVal).arr64 s).size = abiWords := by
        rw [hArr64, Array.size_replicate]
      have hcapEq : LA.cap64 s = abiWords := by simp [LA, checkerLayoutA, hs]
      have hbaseEq : LA.base64 s = regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.pos64 s) := by
        simp [LA, checkerLayoutA, hs]
      refine ⟨by rw [hszEq, hcapEq]; exact Nat.le_refl _, by rw [hszEq]; simp [abiWords], ?_, ?_, ?_⟩
      · rw [hszEq]
        change readWord64 m7 (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen (checkerTabMini.pos64 s))) =
          BitVec.ofNat 64 abiWords
        have hLenInt : BitVec.ofInt 64 (checkerTabMini.dlen (checkerTabMini.pos64 s)) =
            BitVec.ofNat 64 (16 + 8 * 205 + 8 * checkerTabMini.pos64 s) := by
          rw [dlen_bv]
        have hnotlt : ¬checkerTabMini.pos64 s < 2 := by omega
        rw [hLenInt, readAfter4to7 (16 + 8 * 205 + 8 * checkerTabMini.pos64 s) (by omega) (by omega),
          ← hLenInt, hLen3 (checkerTabMini.pos64 s) (by rw [t_nb, t_nw]; omega)]
        simp only [hnotlt, ↓reduceIte]
      · rw [hbaseEq]
        change readWord64 m7 (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase (checkerTabMini.pos64 s))) = _
        have hBaseInt : BitVec.ofInt 64 (checkerTabMini.dbase (checkerTabMini.pos64 s)) =
            BitVec.ofNat 64 (16 + 8 * checkerTabMini.pos64 s) := by
          rw [dbase_bv]
        rw [hBaseInt, readAfter3to7 (16 + 8 * checkerTabMini.pos64 s) (by omega),
          ← hBaseInt, hBase2 (checkerTabMini.pos64 s) (by rw [t_nb, t_nw]; omega)]
        have hnotlt : ¬checkerTabMini.pos64 s < 2 := by omega
        have hslot : checkerTabMini.slotOf (checkerTabMini.pos64 s) = checkerTabMini.pos64 s := by
          simp [Tab.slotOf, t_nbuf]
        simp only [hnotlt, ↓reduceIte, hslot]
      · intro i hi
        have hi' : i < abiWords := by rw [hszEq] at hi; exact hi
        have helem0 : ((loadMemMini inBytes pins (fun _ => abiWords) modeVal).arr64 s)[i]'hi = 0 := by
          have hdef : ((loadMemMini inBytes pins (fun _ => abiWords) modeVal).arr64 s)[i]'hi =
              (Array.replicate abiWords (0 : _root_.L.Word))[i]'(by rw [← hArr64]; exact hi) := rfl
          rw [hdef, Array.getElem_replicate]
        rw [helem0, hbaseEq]
        change readWord64 m7 (regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.pos64 s) + BitVec.ofNat 64 (8 * i)) = 0#64
        apply readWord64_of_zero_bytes
        intro j hj
        have h8w : 8 * abiWords = abiSlot := by simp [abiWords, abiSlot]
        have hkBound : abiSlot * checkerTabMini.pos64 s + (8 * i + j) < abiNeed checkerTabMini := by
          rw [hNeedEq]
          have hm : abiSlot * (checkerTabMini.pos64 s + 1) ≤ abiSlot * 205 :=
            Nat.mul_le_mul_left abiSlot (by omega)
          rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm abiSlot 205] at hm
          omega
        have hkGe : abiSlot ≤ abiSlot * checkerTabMini.pos64 s + (8 * i + j) := by
          have hm : abiSlot * 2 ≤ abiSlot * checkerTabMini.pos64 s := Nat.mul_le_mul_left abiSlot hlo
          omega
        have haddr : regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.pos64 s) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j =
            regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.pos64 s + (8 * i + j)) := by
          rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
        rw [haddr]
        have hnot : ¬(⟨regionBase, abiSlot⟩ : MemSpan).contains
            (regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.pos64 s + (8 * i + j))) := by
          intro ⟨m, hm, hmeq⟩
          dsimp only at hm
          have hto := congrArg BitVec.toNat hmeq
          have hm64 : m < 2 ^ 64 := by simp [abiSlot] at hm; omega
          have hrm64 : regionBase.toNat + m < 2 ^ 64 := by omega
          have hrk64 : regionBase.toNat + (abiSlot * checkerTabMini.pos64 s + (8 * i + j)) < 2 ^ 64 := by omega
          rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt hm64, Nat.mod_eq_of_lt hrm64,
            Nat.mod_eq_of_lt (by omega : abiSlot * checkerTabMini.pos64 s + (8 * i + j) < 2 ^ 64),
            Nat.mod_eq_of_lt hrk64] at hto
          omega
        rw [hout7Slot0 _ hnot, hRegZero _ hkBound]
    · intro k hk
      change m7 (regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + k)) = checkerTabMini.rom[k].toBitVec
      have hk8 : k < 8 * checkerTabMini.romWords := by
        simp only [Tab.romWords]; omega
      have hR : regionBase.toNat + abiSlot ≤ 2 ^ 64 := by omega
      have e67 : m7 (regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + k)) =
          m6 (regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + k)) := by
        rw [hm7, globOff_bitvec]
        exact memEqOutside_writeWord64_tabOff m6 regionBase
          (checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + modeGVar.id))
          modeVal.toBitVec
          _ (fun hc => memSpan_offset_disjoint_contains_false hR
            (by omega : checkerTabMini.romBase.toNat + k + 1 ≤ abiSlot)
            (globOff_bound (g := modeGVar) (by decide)) (Or.inl (by omega))
            ⟨0, Nat.zero_lt_one, by rw [BitVec.add_zero]⟩ hc)
      have e56 : m6 (regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + k)) =
          m5 (regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + k)) :=
        hout6 _ (fun hc => memSpan_offset_disjoint_contains_false hR
          (by omega : checkerTabMini.romBase.toNat + k + 1 ≤ abiSlot)
          hresBounds (Or.inl (by omega)) ⟨0, Nat.zero_lt_one, by rw [BitVec.add_zero]⟩ hc)
      rw [e67, e56, hRom5 k hk]
    · intro g hg
      change readWord64 m7 (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff g)) =
        ((loadMemMini inBytes pins (fun _ => abiWords) modeVal).glob g).toBitVec
      rw [hm7]
      by_cases hgm : g = modeGVar
      · subst hgm
        rw [readWord64_writeWord64_self]
        simp [loadMemMini]
      · have hgne : g.id ≠ modeGVar.id := by
          intro heq; apply hgm; cases g; simp only at heq; subst heq; rfl
        have hdisj : (checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + g.id)) + 8 ≤
              (checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + modeGVar.id)) ∨
            (checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + modeGVar.id)) + 8 ≤
              (checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + g.id)) := by
          omega
        have hrw := readWord64_writeWord64_tabOff (m := m6) (base := regionBase) (need := abiSlot)
          (by omega) (off1 := checkerTabMini.globOff g) (off2 := checkerTabMini.globOff modeGVar)
          (by rw [globOff_eq_nat]; omega) (by rw [globOff_eq_nat]; omega)
          (by rw [globOff_eq_nat, Int.toNat_natCast]; exact globOff_bound hg)
          (by rw [globOff_eq_nat, Int.toNat_natCast]; exact globOff_bound (g := modeGVar) (by decide))
          (by rw [globOff_eq_nat, globOff_eq_nat, Int.toNat_natCast, Int.toNat_natCast]; exact hdisj)
          modeVal.toBitVec
        rw [hrw, globOff_bitvec, show regionBase + BitVec.ofNat 64 (checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + g.id)) =
          regionBase + BitVec.ofNat 64 checkerTabMini.resBase.toNat + BitVec.ofNat 64 (8 * (checkerTabMini.nxres + g.id)) from by
            rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
        rw [hZero6 (checkerTabMini.nxres + g.id) (by omega)]
        simp [loadMemMini, hgm]
  exact ⟨hout7Slot0, hm6Top, hHdr, hMemRel⟩

theorem phaseInit_drvRegsSaved
    {regionBase : BitVec 64} {initSt : RV64.State}
    (modeVal : _root_.L.Word)
    (m0 m1 m2 m3 m4 m5 m6 m7 : ByteMem)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini ≤ 2 ^ 64)
    (hsaved0 : DrvRegsSaved regionBase initSt m0)
    (hout1 : MemEqOutside ⟨regionBase, 16⟩ m0 m1)
    (hout2 : MemEqOutside ⟨regionBase + BitVec.ofNat 64 16, 8 * 205⟩ m1 m2)
    (hout3 : MemEqOutside ⟨regionBase + BitVec.ofNat 64 (16 + 8 * 205), 8 * 205⟩ m2 m3)
    (hout4 : MemEqOutside ⟨regionBase + BitVec.ofNat 64 (16 + 16 * 205), 8 * 205⟩ m3 m4)
    (hout5 : MemEqOutside ⟨regionBase + BitVec.ofNat 64 checkerTabMini.romBase.toNat,
      8 * checkerTabMini.romWords⟩ m4 m5)
    (hout6 : MemEqOutside ⟨regionBase + BitVec.ofNat 64 checkerTabMini.resBase.toNat,
      8 * (checkerTabMini.nxres + checkerTabMini.ng)⟩ m5 m6)
    (hm7 : m7 = writeWord64 m6 (regionBase + BitVec.ofInt 64 (checkerTabMini.globOff modeGVar))
      modeVal.toBitVec) :
    DrvRegsSaved regionBase initSt m7 := by
  have hresNat : checkerTabMini.resBase.toNat = 16 + 24 * 205 + 8 * checkerTabMini.romWords := by
    rw [checkerTabMini_resBase_eq, Int.toNat_natCast]
  have hromNat : checkerTabMini.romBase.toNat = 16 + 24 * 205 := by
    rw [checkerTabMini_romBase_eq, Int.toNat_natCast]
  have hargsNat : checkerTabMini.args.toNat =
      16 + 24 * 205 + 8 * checkerTabMini.romWords + 8 * 2 + 8 * 12 := by
    rw [checkerTabMini_args_eq, Int.toNat_natCast]
  have hromBaseGe : 16 + 24 * 205 ≤ checkerTabMini.romBase.toNat := by omega
  have hs1 := drvRegsSaved_of_memEqOutside_le_args hReg64 (by omega : 0 + 16 ≤ checkerTabMini.args.toNat)
    (by simpa only [BitVec.add_zero] using hout1) hsaved0
  have hs2 := drvRegsSaved_of_memEqOutside_le_args hReg64 (by omega : 16 + 8 * 205 ≤ checkerTabMini.args.toNat) hout2 hs1
  have hs3 := drvRegsSaved_of_memEqOutside_le_args hReg64 (by omega : (16 + 8 * 205) + 8 * 205 ≤ checkerTabMini.args.toNat) hout3 hs2
  have hs4 := drvRegsSaved_of_memEqOutside_le_args hReg64 (by omega : (16 + 16 * 205) + 8 * 205 ≤ checkerTabMini.args.toNat) hout4 hs3
  have hs5 := drvRegsSaved_of_memEqOutside_le_args hReg64 (by rw [hromNat, hargsNat]; omega) hout5 hs4
  have hs6 := drvRegsSaved_of_memEqOutside_le_args hReg64 (by rw [hresNat, hargsNat, t_nxres, t_ng]; omega) hout6 hs5
  rw [hm7]
  exact drvRegsSaved_of_writeWord64_lt_args hReg64
    (by rw [globOff_eq_nat]; omega)
    (by rw [globOff_eq_nat, Int.toNat_natCast, hargsNat, hresNat, t_nxres]; have := (by decide : modeGVar.id < 12); omega)
    modeVal.toBitVec hs6

theorem progMemOutside_writeWord64_of_sub {S : BitVec 64 → Prop} {m : ByteMem} {addr w : BitVec 64}
    (hsub : ∀ k, k < 8 → S (addr + BitVec.ofNat 64 k)) :
    ProgMemOutside S m (writeWord64 m addr w) :=
  ProgMemOutside.of_memEqOutside (s := ⟨addr, 8⟩)
    (fun _ ⟨k, hk, hka⟩ => hka ▸ hsub k hk)
    (MemEqOutside.writeWord64 m addr w fun _ hk => ⟨_, hk, rfl⟩)

def applyTabWrites (base : BitVec 64) (m : ByteMem) : List (Int × BitVec 64) → ByteMem
  | [] => m
  | (off, w) :: ws => applyTabWrites base (writeWord64 m (base + BitVec.ofInt 64 off) w) ws

def tabOffOk (o : Int) : Prop := 0 ≤ o ∧ o.toNat + 8 ≤ abiSlot
def tabOffDisj (o1 o2 : Int) : Prop := o1.toNat + 8 ≤ o2.toNat ∨ o2.toNat + 8 ≤ o1.toNat

theorem readWord64_applyTabWrites_disj {base : BitVec 64}
    (hR : base.toNat + abiSlot ≤ 2 ^ 64)
    {off : Int} (hoff : tabOffOk off)
    (ws : List (Int × BitVec 64))
    (hws : ∀ e ∈ ws, tabOffOk e.1 ∧ tabOffDisj off e.1)
    (m : ByteMem) :
    readWord64 (applyTabWrites base m ws) (base + BitVec.ofInt 64 off) =
      readWord64 m (base + BitVec.ofInt 64 off) := by
  induction ws generalizing m with
  | nil => rfl
  | cons e ws ih =>
    have he := hws e (List.mem_cons_self ..)
    have htail : ∀ e' ∈ ws, tabOffOk e'.1 ∧ tabOffDisj off e'.1 :=
      fun e' hmem => hws e' (List.mem_cons_of_mem _ hmem)
    dsimp only [applyTabWrites]
    rw [ih htail, readWord64_writeWord64_tabOff hR hoff.1 he.1.1 hoff.2 he.1.2 he.2]

theorem progMemOutside_applyTabWrites {S : BitVec 64 → Prop} {base : BitVec 64}
    (ws : List (Int × BitVec 64))
    (hsub : ∀ e ∈ ws, ∀ k, k < 8 → S (base + BitVec.ofInt 64 e.1 + BitVec.ofNat 64 k))
    (m : ByteMem) :
    ProgMemOutside S m (applyTabWrites base m ws) := by
  induction ws generalizing m with
  | nil => exact ProgMemOutside.refl S m
  | cons e ws ih =>
    have he := hsub e (List.mem_cons_self ..)
    have htail : ∀ e' ∈ ws, ∀ k, k < 8 → S (base + BitVec.ofInt 64 e'.1 + BitVec.ofNat 64 k) :=
      fun e' hmem => hsub e' (List.mem_cons_of_mem _ hmem)
    dsimp only [applyTabWrites]
    exact (progMemOutside_writeWord64_of_sub he).trans (ih htail _)

theorem phaseA_prefix_sim
    (initSt : RV64.State) (hpc0 : initSt.pc = 0#64)
    {inBase pinsBase regionBase : BitVec 64}
    {inBytes pins : ByteArray}
    (ha0 : initSt.getReg AbiReg.a0 = inBase)
    (ha1 : initSt.getReg AbiReg.a1 = BitVec.ofNat 64 inBytes.size)
    (ha2 : initSt.getReg AbiReg.a2 = pinsBase)
    (ha3 : initSt.getReg AbiReg.a3 = BitVec.ofNat 64 pins.size)
    (ha4 : initSt.getReg AbiReg.a4 = regionBase)
    (hin64 : inBytes.size < 2 ^ 64) (hpins64 : pins.size < 2 ^ 64)
    (hIn64 : inBase.toNat + inBytes.size ≤ 2 ^ 64)
    (hPins64 : pinsBase.toNat + pins.size ≤ 2 ^ 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (hDisjInPins : MemSpan.disjoint ⟨inBase, inBytes.size⟩ ⟨pinsBase, pins.size⟩)
    (hDisjInReg : MemSpan.disjoint ⟨inBase, inBytes.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hDisjPinsReg : MemSpan.disjoint ⟨pinsBase, pins.size⟩ ⟨regionBase, abiNeed checkerTabMini⟩)
    (hInMem : ∀ i, (hi : i < inBytes.size) → initSt.mem (inBase + BitVec.ofNat 64 i) = inBytes[i].toBitVec)
    (hPinsMem : ∀ i, (hi : i < pins.size) → initSt.mem (pinsBase + BitVec.ofNat 64 i) = pins[i].toBitVec)
    (hRegZero : ∀ k, k < abiNeed checkerTabMini → initSt.mem (regionBase + BitVec.ofNat 64 k) = 0#8)
    {fuel : Nat} {finalSt : RV64.State}
    (hRetOut : checkerRom ((initSt.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run checkerRom fuel initSt = .cont finalSt)
    (hret : finalSt.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64))
    (ha1Out : finalSt.getReg AbiReg.a1 ≠ 1#64) :
    let LA := checkerLayoutA inBase pinsBase regionBase inBytes.size pins.size
      hIn64 hPins64 hRegAlign hReg64 hDisjInPins hDisjInReg hDisjPinsReg
    let preCall := drvPfx ++ drvNeedLi checkerTabMini ++ drvBootCheck checkerTabMini ++
      [Asm.call drvInitLabel] ++ drvPhaseASetup checkerTabMini
    inBytes.size < 2 ^ 63 ∧ pins.size < 2 ^ 63 ∧
    ∃ k st,
      RV64.run checkerEnv.rom k initSt = .cont st ∧
      st.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize preCall) ∧
      st.getReg AbiReg.gp = regionBase ∧
      st.getReg AbiReg.sp = LA.stackTop ∧
      st.getReg AbiReg.s0 = BitVec.ofNat 64 (abiFuel - 2) ∧
      st.getReg AbiReg.t0 = regionBase + BitVec.ofInt 64 checkerTabMini.args ∧
      st.getReg AbiReg.t1 = 0#64 ∧
      DrvRegsSaved regionBase initSt st.mem ∧
      ProgMemRel checkerTabMini LA st.mem (phaseAInitMem inBytes pins) ∧
      TabHeaderOk LA st.mem := by
  intro LA preCall
  have hNeedEq := checkerTabMini_abiNeed_eq
  let tailAll := drvPhaseACall ++ drvPhaseBSetup checkerTabMini ++ drvPhaseBCall ++ drvDoneStub ++
    drvExhaustedStub ++ drvErrPrefix ++ drvAbortPrefix ++
    drvRetRestoreStub checkerTabMini ++ drvInitSubAsm checkerTabMini ++
    checkerCmpDriverAsm checkerTabMini ++ checkerFnsAsm
  have hlinkFull : checkerLM.linkSpec (preCall ++ tailAll) =
      .ok (checkerEnv.code, checkerEnv.labels) := by
    have h := checkerChipAsm_linkSpec
    rw [checkerChipAsm_eq', checkerDriverAsm_decomp] at h
    change checkerLM.linkSpec (preCall ++ tailAll) = .ok (checkerCode, checkerLabels)
    simpa only [drvAllBeforeEx, drvPreDone, preCall, tailAll, List.append_assoc] using h
  have hpc0' : initSt.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize ([] : List AsmItem)) := by
    simpa only [checkerLM.totalSize_nil, Nat.mul_zero] using hpc0
  have hlBoot : checkerLM.linkSpec (([] : List AsmItem) ++ drvPfx ++ drvNeedLi checkerTabMini ++ drvBootCheck checkerTabMini ++
      ([Asm.call drvInitLabel] ++ drvPhaseASetup checkerTabMini ++ tailAll)) =
      .ok (checkerEnv.code, checkerEnv.labels) := by
    simpa only [preCall, List.nil_append, List.append_assoc] using hlinkFull
  obtain ⟨k0, s0, hrun0, hpc0_s, hs0_gp, hs0_a0, hs0_a1, hs0_a2, hs0_a3, hs0_a4,
      hs0_saved, hs0_m, _, ha1Lt63, ha3Lt63⟩ :=
    drvBootCheck_sim [] _ hlBoot initSt hpc0'
      (by rw [ha4]; exact hRegAlign) (by rw [ha4]; omega) hRetOut hrun hret ha1Out
  have hin63 : inBytes.size < 2 ^ 63 := by
    rw [ha1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hin64] at ha1Lt63; exact ha1Lt63
  have hpins63 : pins.size < 2 ^ 63 := by
    rw [ha3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpins64] at ha3Lt63; exact ha3Lt63
  let pBoot := drvPfx ++ drvNeedLi checkerTabMini ++ drvBootCheck checkerTabMini
  have hpc0'' : s0.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize pBoot) := by
    simpa only [pBoot, List.nil_append, List.append_assoc] using hpc0_s
  have hlCall : checkerLM.linkSpec (pBoot ++ [Asm.call drvInitLabel] ++
      (drvPhaseASetup checkerTabMini ++ tailAll)) =
      .ok (checkerEnv.code, checkerEnv.labels) := by
    simpa only [pBoot, List.nil_append, List.append_assoc] using hlBoot
  have hpcCall64 := linkResolved_sub_pc64 checkerEnv pBoot [Asm.call drvInitLabel] _ hlCall
  have hltCall64 : 4 * (checkerLM.totalSize pBoot + checkerLM.itemSize (.call drvInitLabel)) < 2 ^ 64 := by
    simpa only [Asm.call, checkerLM.totalSize_singleton] using hpcCall64
  obtain ⟨tgtInit, kCall, sCall, _, hlkpInit, hrunCall, hpcCall, hregsCall, hmCall⟩ :=
    step_item_call_lm checkerLM checkerEnv.hrom pBoot _ drvInitLabel hlCall hltCall64 s0 hpc0''
  rw [checker_drvInit_lbl] at hlkpInit
  have htgtInit : tgtInit = checkerLM.totalSize (drvInitPre checkerTabMini) := Option.some.inj hlkpInit.symm
  have hpcInit : sCall.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize (drvInitPre checkerTabMini)) := by
    rw [hpcCall, htgtInit]
  have hlInit : checkerLM.linkSpec (drvInitPre checkerTabMini ++ drvInitSubAsm checkerTabMini ++
      (checkerCmpDriverAsm checkerTabMini ++ checkerFnsAsm)) =
      .ok (checkerEnv.code, checkerEnv.labels) := by
    simpa only [drvInitPre, List.append_assoc] using checkerChipAsm_linkSpec_decomp
  have hsCall_gp : sCall.getReg AbiReg.gp = regionBase :=
    (hregsCall.getReg_eq (by decide)).symm.trans ((getReg_setReg_ne s0 AbiReg.ra _ _ (by decide)).trans (hs0_gp.trans ha4))
  have hsCall_a0 : sCall.getReg AbiReg.a0 = inBase :=
    (hregsCall.getReg_eq (by decide)).symm.trans ((getReg_setReg_ne s0 AbiReg.ra _ _ (by decide)).trans (hs0_a0.trans ha0))
  have hsCall_a1 : sCall.getReg AbiReg.a1 = BitVec.ofNat 64 inBytes.size :=
    (hregsCall.getReg_eq (by decide)).symm.trans ((getReg_setReg_ne s0 AbiReg.ra _ _ (by decide)).trans (hs0_a1.trans ha1))
  have hsCall_a2 : sCall.getReg AbiReg.a2 = pinsBase :=
    (hregsCall.getReg_eq (by decide)).symm.trans ((getReg_setReg_ne s0 AbiReg.ra _ _ (by decide)).trans (hs0_a2.trans ha2))
  have hsCall_a3 : sCall.getReg AbiReg.a3 = BitVec.ofNat 64 pins.size :=
    (hregsCall.getReg_eq (by decide)).symm.trans ((getReg_setReg_ne s0 AbiReg.ra _ _ (by decide)).trans (hs0_a3.trans ha3))
  have hsCall_ra : sCall.getReg AbiReg.ra =
      BitVec.ofNat 64 (4 * (checkerLM.totalSize pBoot + checkerLM.itemSize (.call drvInitLabel))) :=
    (hregsCall.getReg_eq (by decide)).symm.trans (getReg_setReg_eq s0 AbiReg.ra _ (by decide))
  obtain ⟨kInit, sInit, m1, m2, m3, m4, m5, hrunInit, hpcRetInit, hothInit,
      hout1, hHdrTop1, hHdrLim1, hout2, hBase2, hout3, hLen3, hout4, hout5, hRom5, hout6, hZero6⟩ :=
    drvInitSub_sim_gen checkerEnv regionBase inBase pinsBase hRegAlign hReg64
      (drvInitPre checkerTabMini) (checkerCmpDriverAsm checkerTabMini ++ checkerFnsAsm)
      hlInit sCall hpcInit hsCall_gp hsCall_a0 hsCall_a1 hsCall_a2 hsCall_a3
  let p1 := pBoot ++ [Asm.call drvInitLabel]
  have hpc1' : sInit.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p1) := by
    rw [hpcRetInit, hsCall_ra, mul4_and_not1]
    simp only [p1, checkerLM.totalSize_append, Asm.call, checkerLM.totalSize_singleton]
  have hsInit_gp : sInit.getReg AbiReg.gp = regionBase :=
    (hothInit _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsCall_gp
  have hlPhA : checkerLM.linkSpec (p1 ++ drvPhaseASetup checkerTabMini ++ tailAll) =
      .ok (checkerEnv.code, checkerEnv.labels) := by
    simpa only [p1, List.append_assoc] using hlCall
  obtain ⟨k7, s7, hrun7, hpc7, hs7gp, hs7s0, hs7sp, _, hs7t0, hs7t1, hs7m⟩ :=
    drvPhaseASetup_sim regionBase hRegAlign hReg64 p1 tailAll hlPhA sInit hpc1' hsInit_gp
  obtain ⟨_, hs6Top, hHdr, hMemRel⟩ := phaseInit_hdr_and_rel 3
    initSt.mem s0.mem m1 m2 m3 m4 m5 sInit.mem s7.mem
    hin63 hpins63 hIn64 hPins64 hRegAlign hReg64 hDisjInPins hDisjInReg hDisjPinsReg
    hInMem hPinsMem hRegZero
    (by rw [ha4] at hs0_m; exact hs0_m) (by rw [hmCall] at hout1; exact hout1)
    hHdrTop1 hHdrLim1 hout2 hBase2 hout3 hLen3 hout4 hout5 hRom5
    hout6 hZero6 hs7m
  have hs7saved := phaseInit_drvRegsSaved 3
    s0.mem m1 m2 m3 m4 m5 sInit.mem s7.mem
    (by omega) (by rw [ha4] at hs0_saved; exact hs0_saved)
    (by rw [hmCall] at hout1; exact hout1) hout2 hout3 hout4 hout5 hout6 hs7m
  refine ⟨hin63, hpins63, k0 + kCall + kInit + k7, s7, ?_, ?_,
    hs7gp, by rw [hs7sp, hs6Top], hs7s0, hs7t0, hs7t1, hs7saved, hMemRel, hHdr⟩
  · rw [run_add, run_add, run_add, hrun0]
    dsimp only; rw [hrunCall]; dsimp only; rw [hrunInit]; exact hrun7
  · rw [hpc7]; dsimp only [p1, pBoot, preCall]
    simp only [checkerLM.totalSize_append, Nat.add_assoc]


end ConAgua.RISCV.Bridge
