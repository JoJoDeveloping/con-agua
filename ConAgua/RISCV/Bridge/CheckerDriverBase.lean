import ConAgua.RISCV.Bridge.CheckerDriverCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Phase A Driver Simulation & Comparator Driver Prefix (`ConAgua.RISCV.Bridge.CheckerDriverBase`)

Imports `ConAgua.RISCV.Bridge.CheckerDriverCore` (Sections 1–3) and provides Section 4A:
- `drvBootCheck_sim`, `drvResetStack_sim`, `drvBufBaseStores_sim_gen`, `drvBufLenStores_sim_gen`,
  `drvFillConstLoop_sim_gen`, `drvFillStrideLoop_sim_gen`, `drvRomStores_sim`,
  `drvInitSub_sim_gen`, `drvDone_returns`, `linkedCmpDrvDone_returns`,
  `cmpDrvBootCheck_sim`, `linkedCmpDrvBootCheck_sim`, `cmpDrvCallPrep_sim`, and
  `linkedCmpDrvCallPrep_sim`.
-/

namespace ConAgua.RISCV.Bridge

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Compiler
open ConAgua.RISCV.Linker

/-! ## 4A. Driver Prefix, Descriptor Loops, ROM/Global Init, Phase A Setup, and `drvDone` -/

private theorem run_raw_branch_step {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (op : BranchOp) (rs1 rs2 : Reg) (d : Nat) (hd : d ≤ 1023)
    (hlink : lkm.linkSpec (pre ++ [Asm.raw (.branch op rs1 rs2 (mkBimm (d : Int)))] ++ post) =
      .ok (env.code, env.labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre)) :
    let nextPc := if evalBranch op (st.getReg rs1) (st.getReg rs2)
                  then BitVec.ofNat 64 (4 * (lkm.totalSize pre + d))
                  else BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1))
    let st' := { st with pc := nextPc }
    RV64.run env.rom 1 st = .cont st' ∧
    st'.pc = nextPc ∧
    (∀ q, st'.getReg q = st.getReg q) ∧
    st'.mem = st.mem := by
  have hpc64 := linkResolved_sub_pc64 env pre [Asm.raw (.branch op rs1 rs2 (mkBimm (d : Int)))] post hlink
  have htw : lkm.totalSize [Asm.raw (.branch op rs1 rs2 (mkBimm (d : Int)))] = 1 := lkm.totalSize_instr _
  have hlt : 4 * lkm.totalSize pre < 2 ^ 64 := by rw [htw] at hpc64; omega
  have hstep := step_item_instr_lm lkm env.hrom pre post (.branch op rs1 rs2 (mkBimm (d : Int))) hlink hlt st hpc
  have hpcTaken : st.pc + sextImmB (mkBimm (d : Int)) = BitVec.ofNat 64 (4 * (lkm.totalSize pre + d)) := by
    rw [hpc, show (d : Int) = ((lkm.totalSize pre + d : Nat) : Int) - (lkm.totalSize pre : Int) from by omega]
    exact pc_add_sextImmB (by simp only [branchInRange, Bool.and_eq_true, decide_eq_true_eq]; omega)
  have hpcFall : st.pc + 4#64 = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)) :=
    pc_add_4_ofNat st.pc hpc
  have hrun : RV64.run env.rom 1 st =
      .cont { st with pc := if evalBranch op (st.getReg rs1) (st.getReg rs2)
                            then BitVec.ofNat 64 (4 * (lkm.totalSize pre + d))
                            else BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)) } := by
    apply run_one_cont
    rw [hstep]
    simp only [execInstr, hpcTaken, hpcFall]
  exact ⟨hrun, rfl, fun _ => rfl, rfl⟩

theorem drvBootCheck_sim
    (pre post : List AsmItem)
    (hlink : checkerLM.linkSpec
      (pre ++ drvPfx ++ drvNeedLi checkerTabMini ++ drvBootCheck checkerTabMini ++ post) =
      .ok (checkerEnv.code, checkerEnv.labels))
    (st0 : RV64.State) (hpc0 : st0.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize pre))
    (hRegAlign : isAligned (st0.getReg AbiReg.a4) 8 = true)
    (hReg64 : (st0.getReg AbiReg.a4).toNat + abiNeed checkerTabMini ≤ 2 ^ 64)
    {fuel : Nat} {x : RV64.State}
    (hRetOut : checkerEnv.rom ((st0.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run checkerEnv.rom fuel st0 = .cont x)
    (hret : x.pc = (st0.getReg AbiReg.ra &&& ~~~1#64))
    (ha1Out : x.getReg AbiReg.a1 ≠ 1#64) :
    ∃ k st',
      RV64.run checkerEnv.rom k st0 = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize
        (pre ++ drvPfx ++ drvNeedLi checkerTabMini ++ drvBootCheck checkerTabMini)) ∧
      st'.getReg AbiReg.gp = st0.getReg AbiReg.a4 ∧
      st'.getReg AbiReg.a0 = st0.getReg AbiReg.a0 ∧
      st'.getReg AbiReg.a1 = st0.getReg AbiReg.a1 ∧
      st'.getReg AbiReg.a2 = st0.getReg AbiReg.a2 ∧
      st'.getReg AbiReg.a3 = st0.getReg AbiReg.a3 ∧
      st'.getReg AbiReg.a4 = st0.getReg AbiReg.a4 ∧
      DrvRegsSaved (st0.getReg AbiReg.a4) st0 st'.mem ∧
      MemEqOutside (callerSaveSpan (st0.getReg AbiReg.a4) (checkerTabMini.saveBase 0))
        st0.mem st'.mem ∧
      abiNeed checkerTabMini ≤ (st0.getReg AbiReg.a5).toNat ∧
      (st0.getReg AbiReg.a1).toNat < 2 ^ 63 ∧
      (st0.getReg AbiReg.a3).toNat < 2 ^ 63 := by
  let p0 := pre ++ [Asm.lbl startLabel]
  have hpc0' : st0.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p0) := by
    simpa only [p0, checkerLM.totalSize_append, Asm.lbl, checkerLM.totalSize_label, Nat.add_zero] using hpc0
  have hl3 : checkerLM.linkSpec (p0 ++ drvNeedLi checkerTabMini ++ (drvBootCheck checkerTabMini ++ post)) =
      .ok (checkerEnv.code, checkerEnv.labels) := by
    simpa only [p0, drvPfx, List.append_assoc] using hlink
  have hpcLi64 := linkResolved_sub_pc64 checkerEnv p0 (drvNeedLi checkerTabMini) _ hl3
  obtain ⟨s3, hrun3, hoth3, ht0_3, hm3, hpc3⟩ :=
    li_correct_lm checkerLM checkerEnv.hrom p0 _ AbiReg.t0 (by decide)
      (BitVec.ofNat 64 (abiNeed checkerTabMini)) hl3 hpcLi64 st0 hpc0'
  let p3 := p0 ++ drvNeedLi checkerTabMini
  have hpc3' : s3.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p3) := by
    simpa only [p3, drvNeedLi, checkerLM.totalSize_append] using hpc3
  have hs3_eq : ∀ q, q ≠ AbiReg.t0 → s3.getReg q = st0.getReg q := hoth3
  have hneedLt64 : abiNeed checkerTabMini < 2 ^ 64 := by
    rw [checkerTabMini_abiNeed_eq]; simp [abiSlot]
  let b1 := Asm.raw (.branch .bltu AbiReg.a5 AbiReg.t0 (mkBimm 3))
  let b2 := Asm.raw (.branch .blt AbiReg.a1 AbiReg.zero (mkBimm 2))
  let b3 := Asm.raw (.branch .bge AbiReg.a3 AbiReg.zero (mkBimm 4))
  let d0 := Asm.addi AbiReg.a0 AbiReg.zero 0#12
  let d1 := Asm.addi AbiReg.a1 AbiReg.zero 1#12
  let d2 := Asm.ret
  let tailSv := callerSaveAsm AbiReg.a4 (checkerTabMini.saveBase 0) ++ [Asm.mv AbiReg.gp AbiReg.a4] ++ post
  have hlB1 : checkerLM.linkSpec (p3 ++ [b1] ++ ([b2, b3, d0, d1, d2] ++ tailSv)) =
      .ok (checkerEnv.code, checkerEnv.labels) := by
    simpa only [p3, drvBootCheck, b1, b2, b3, d0, d1, d2, tailSv,
      List.cons_append, List.nil_append, List.append_assoc] using hl3
  have hbr1 := run_raw_branch_step checkerEnv p3 ([b2, b3, d0, d1, d2] ++ tailSv)
    .bltu AbiReg.a5 AbiReg.t0 3 (by decide) hlB1 s3 hpc3'
  have ha5Ge : abiNeed checkerTabMini ≤ (st0.getReg AbiReg.a5).toNat := by
    by_cases hok : abiNeed checkerTabMini ≤ (st0.getReg AbiReg.a5).toNat
    · exact hok
    · exfalso
      have hev : evalBranch .bltu (s3.getReg AbiReg.a5) (s3.getReg AbiReg.t0) = true := by
        rw [hs3_eq _ (by decide), ht0_3]
        simp only [evalBranch, BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hneedLt64]
        omega
      let sd := { s3 with pc := BitVec.ofNat 64 (4 * (checkerLM.totalSize p3 + 3)) }
      have hrun1 : RV64.run checkerEnv.rom 1 s3 = .cont sd := by
        simpa only [hev, ↓reduceIte] using hbr1.1
      have hothd : ∀ q, sd.getReg q = s3.getReg q := fun _ => rfl
      have hcont : RV64.run checkerEnv.rom (checkerLM.totalSize (drvNeedLi checkerTabMini) + 1) st0 = .cont sd := by
        rw [run_add]; dsimp only [drvNeedLi]; rw [hrun3]; exact hrun1
      let pDecl1 := p3 ++ [b1, b2, b3]
      have hpcd' : sd.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize pDecl1) := by
        apply congrArg (fun n => BitVec.ofNat 64 (4 * n))
        simp [pDecl1, b1, b2, b3, Asm.raw, checkerLM.totalSize_append, checkerLM.totalSize_cons,
          checkerLM.totalSize_nil, checkerLM.itemSize_instr]
      have hlDecl1 : checkerLM.linkSpec (pDecl1 ++ [d0, d1, d2] ++ tailSv) =
          .ok (checkerEnv.code, checkerEnv.labels) := by
        simpa only [pDecl1, List.cons_append, List.nil_append, List.append_assoc] using hlB1
      obtain ⟨mR, r', hmR, hpcR, _, ha1R, _, _⟩ :=
        inline_decline_returns checkerEnv pDecl1 tailSv hlDecl1 sd hpcd'
      have hraEq : sd.getReg AbiReg.ra = st0.getReg AbiReg.ra :=
        (hothd _).trans (hs3_eq _ (by decide))
      rw [hraEq] at hpcR
      exact ret_ne_of_cont hcont hrun hret hRetOut ⟨mR, r', hmR, hpcR, ha1R⟩ ha1Out.symm
  have hev1 : evalBranch .bltu (s3.getReg AbiReg.a5) (s3.getReg AbiReg.t0) = false := by
    rw [hs3_eq _ (by decide), ht0_3]
    simp only [evalBranch, BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hneedLt64]
    omega
  let s4 := { s3 with pc := BitVec.ofNat 64 (4 * (checkerLM.totalSize p3 + 1)) }
  have hrunB1 : RV64.run checkerEnv.rom 1 s3 = .cont s4 := by
    simpa only [hev1, Bool.false_eq_true, ↓reduceIte] using hbr1.1
  have hothB1 : ∀ q, s4.getReg q = s3.getReg q := fun _ => rfl
  have hm4 : s4.mem = s3.mem := rfl
  let p4 := p3 ++ [b1]
  have hpc4' : s4.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p4) := by
    dsimp only [s4, p4, b1, Asm.raw]
    rw [checkerLM.totalSize_append p3 _, checkerLM.totalSize_instr]
  have hrunTo4 : RV64.run checkerEnv.rom (checkerLM.totalSize (drvNeedLi checkerTabMini) + 1) st0 = .cont s4 := by
    rw [run_add]; dsimp only [drvNeedLi]; rw [hrun3]; exact hrunB1
  have hlB2 : checkerLM.linkSpec (p4 ++ [b2] ++ ([b3, d0, d1, d2] ++ tailSv)) =
      .ok (checkerEnv.code, checkerEnv.labels) := by
    simpa only [p4, List.cons_append, List.nil_append, List.append_assoc] using hlB1
  have hbr2 := run_raw_branch_step checkerEnv p4 ([b3, d0, d1, d2] ++ tailSv)
    .blt AbiReg.a1 AbiReg.zero 2 (by decide) hlB2 s4 hpc4'
  have hs4_a1 : s4.getReg AbiReg.a1 = st0.getReg AbiReg.a1 :=
    (hothB1 _).trans (hs3_eq _ (by decide))
  have ha1Lt : (st0.getReg AbiReg.a1).toNat < 2 ^ 63 := by
    by_cases hok : (st0.getReg AbiReg.a1).toNat < 2 ^ 63
    · exact hok
    · exfalso
      have hle : 2 ^ 63 ≤ (st0.getReg AbiReg.a1).toNat := Nat.le_of_not_lt hok
      have hbv : BitVec.ofNat 64 (st0.getReg AbiReg.a1).toNat = st0.getReg AbiReg.a1 :=
        BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (st0.getReg AbiReg.a1).isLt])
      have hev : evalBranch .blt (s4.getReg AbiReg.a1) (s4.getReg AbiReg.zero) = true := by
        have hz : s4.getReg AbiReg.zero = 0#64 := rfl
        rw [hs4_a1, hz]; dsimp only [evalBranch]; rw [← hbv, bitvec_slt_zero_iff _ (st0.getReg AbiReg.a1).isLt]
        simp [hle]
      let sd := { s4 with pc := BitVec.ofNat 64 (4 * (checkerLM.totalSize p4 + 2)) }
      have hrun2 : RV64.run checkerEnv.rom 1 s4 = .cont sd := by
        simpa only [hev, ↓reduceIte] using hbr2.1
      have hothd : ∀ q, sd.getReg q = s4.getReg q := fun _ => rfl
      have hcont : RV64.run checkerEnv.rom ((checkerLM.totalSize (drvNeedLi checkerTabMini) + 1) + 1) st0 = .cont sd := by
        rw [run_add, hrunTo4]; exact hrun2
      let pDecl2 := p4 ++ [b2, b3]
      have hpcd' : sd.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize pDecl2) := by
        apply congrArg (fun n => BitVec.ofNat 64 (4 * n))
        simp [pDecl2, b2, b3, Asm.raw, checkerLM.totalSize_append, checkerLM.totalSize_cons,
          checkerLM.totalSize_nil, checkerLM.itemSize_instr]
      have hlDecl2 : checkerLM.linkSpec (pDecl2 ++ [d0, d1, d2] ++ tailSv) =
          .ok (checkerEnv.code, checkerEnv.labels) := by
        simpa only [pDecl2, List.cons_append, List.nil_append, List.append_assoc] using hlB2
      obtain ⟨mR, r', hmR, hpcR, _, ha1R, _, _⟩ :=
        inline_decline_returns checkerEnv pDecl2 tailSv hlDecl2 sd hpcd'
      have hraEq : sd.getReg AbiReg.ra = st0.getReg AbiReg.ra :=
        (hothd _).trans ((hothB1 _).trans (hs3_eq _ (by decide)))
      rw [hraEq] at hpcR
      exact ret_ne_of_cont hcont hrun hret hRetOut ⟨mR, r', hmR, hpcR, ha1R⟩ ha1Out.symm
  have hev2 : evalBranch .blt (s4.getReg AbiReg.a1) (s4.getReg AbiReg.zero) = false := by
    have hz : s4.getReg AbiReg.zero = 0#64 := rfl
    have hbv : BitVec.ofNat 64 (st0.getReg AbiReg.a1).toNat = st0.getReg AbiReg.a1 :=
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (st0.getReg AbiReg.a1).isLt])
    rw [hs4_a1, hz]; dsimp only [evalBranch]; rw [← hbv, bitvec_slt_zero_iff _ (st0.getReg AbiReg.a1).isLt]
    simp [ha1Lt]
  let s5 := { s4 with pc := BitVec.ofNat 64 (4 * (checkerLM.totalSize p4 + 1)) }
  have hrunB2 : RV64.run checkerEnv.rom 1 s4 = .cont s5 := by
    simpa only [hev2, Bool.false_eq_true, ↓reduceIte] using hbr2.1
  have hothB2 : ∀ q, s5.getReg q = s4.getReg q := fun _ => rfl
  have hm5 : s5.mem = s4.mem := rfl
  let p5 := p4 ++ [b2]
  have hpc5' : s5.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p5) := by
    dsimp only [s5, p5, b2, Asm.raw]
    rw [checkerLM.totalSize_append p4 _, checkerLM.totalSize_instr]
  have hrunTo5 : RV64.run checkerEnv.rom ((checkerLM.totalSize (drvNeedLi checkerTabMini) + 1) + 1) st0 = .cont s5 := by
    rw [run_add, hrunTo4]; exact hrunB2
  have hlB3 : checkerLM.linkSpec (p5 ++ [b3] ++ ([d0, d1, d2] ++ tailSv)) =
      .ok (checkerEnv.code, checkerEnv.labels) := by
    simpa only [p5, List.cons_append, List.nil_append, List.append_assoc] using hlB2
  have hbr3 := run_raw_branch_step checkerEnv p5 ([d0, d1, d2] ++ tailSv)
    .bge AbiReg.a3 AbiReg.zero 4 (by decide) hlB3 s5 hpc5'
  have hs5_a3 : s5.getReg AbiReg.a3 = st0.getReg AbiReg.a3 :=
    (hothB2 _).trans ((hothB1 _).trans (hs3_eq _ (by decide)))
  have ha3Lt : (st0.getReg AbiReg.a3).toNat < 2 ^ 63 := by
    by_cases hok : (st0.getReg AbiReg.a3).toNat < 2 ^ 63
    · exact hok
    · exfalso
      have hle : 2 ^ 63 ≤ (st0.getReg AbiReg.a3).toNat := Nat.le_of_not_lt hok
      have hbv : BitVec.ofNat 64 (st0.getReg AbiReg.a3).toNat = st0.getReg AbiReg.a3 :=
        BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (st0.getReg AbiReg.a3).isLt])
      have hev : evalBranch .bge (s5.getReg AbiReg.a3) (s5.getReg AbiReg.zero) = false := by
        have hz : s5.getReg AbiReg.zero = 0#64 := rfl
        rw [hs5_a3, hz]; dsimp only [evalBranch]; rw [← hbv, bitvec_slt_zero_iff _ (st0.getReg AbiReg.a3).isLt]
        simp [hle]
      let sd := { s5 with pc := BitVec.ofNat 64 (4 * (checkerLM.totalSize p5 + 1)) }
      have hrun3' : RV64.run checkerEnv.rom 1 s5 = .cont sd := by
        simpa only [hev, Bool.false_eq_true, ↓reduceIte] using hbr3.1
      have hothd : ∀ q, sd.getReg q = s5.getReg q := fun _ => rfl
      have hcont : RV64.run checkerEnv.rom (((checkerLM.totalSize (drvNeedLi checkerTabMini) + 1) + 1) + 1) st0 = .cont sd := by
        rw [run_add, hrunTo5]; exact hrun3'
      let pDecl3 := p5 ++ [b3]
      have hpcd' : sd.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize pDecl3) := by
        dsimp only [sd, pDecl3, b3, Asm.raw]
        rw [checkerLM.totalSize_append p5 _, checkerLM.totalSize_instr]
      have hlDecl3 : checkerLM.linkSpec (pDecl3 ++ [d0, d1, d2] ++ tailSv) =
          .ok (checkerEnv.code, checkerEnv.labels) := by
        simpa only [pDecl3, List.cons_append, List.nil_append, List.append_assoc] using hlB3
      obtain ⟨mR, r', hmR, hpcR, _, ha1R, _, _⟩ :=
        inline_decline_returns checkerEnv pDecl3 tailSv hlDecl3 sd hpcd'
      have hraEq : sd.getReg AbiReg.ra = st0.getReg AbiReg.ra :=
        (hothd _).trans ((hothB2 _).trans ((hothB1 _).trans (hs3_eq _ (by decide))))
      rw [hraEq] at hpcR
      exact ret_ne_of_cont hcont hrun hret hRetOut ⟨mR, r', hmR, hpcR, ha1R⟩ ha1Out.symm
  have hev3 : evalBranch .bge (s5.getReg AbiReg.a3) (s5.getReg AbiReg.zero) = true := by
    have hz : s5.getReg AbiReg.zero = 0#64 := rfl
    have hbv : BitVec.ofNat 64 (st0.getReg AbiReg.a3).toNat = st0.getReg AbiReg.a3 :=
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (st0.getReg AbiReg.a3).isLt])
    rw [hs5_a3, hz]; dsimp only [evalBranch]; rw [← hbv, bitvec_slt_zero_iff _ (st0.getReg AbiReg.a3).isLt]
    simp [ha3Lt]
  let s6 := { s5 with pc := BitVec.ofNat 64 (4 * (checkerLM.totalSize p5 + 4)) }
  have hrunB3 : RV64.run checkerEnv.rom 1 s5 = .cont s6 := by
    simpa only [hev3, ↓reduceIte] using hbr3.1
  have hothB3 : ∀ q, s6.getReg q = s5.getReg q := fun _ => rfl
  have hm6 : s6.mem = s5.mem := rfl
  let p6 := p5 ++ [b3, d0, d1, d2]
  have hpc6' : s6.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p6) := by
    apply congrArg (fun n => BitVec.ofNat 64 (4 * n))
    simp [p6, b3, d0, d1, d2, Asm.raw, Asm.addi, Asm.ret, checkerLM.totalSize_append,
      checkerLM.totalSize_cons, checkerLM.totalSize_nil, checkerLM.itemSize_instr]
  have hlSv : checkerLM.linkSpec (p6 ++ callerSaveAsm AbiReg.a4 (checkerTabMini.saveBase 0) ++
      ([Asm.mv AbiReg.gp AbiReg.a4] ++ post)) = .ok (checkerEnv.code, checkerEnv.labels) := by
    simpa only [p6, tailSv, List.cons_append, List.nil_append, List.append_assoc] using hlB3
  have hs6_a4 : s6.getReg AbiReg.a4 = st0.getReg AbiReg.a4 :=
    (hothB3 _).trans ((hothB2 _).trans ((hothB1 _).trans (hs3_eq _ (by decide))))
  obtain ⟨kSv, sSv, hrunSv, hpcSv, hothSv, hsavedSv, houtSv⟩ :=
    callerSave_sim checkerEnv AbiReg.a4 (by decide) (by decide) (checkerTabMini.saveBase 0)
      (st0.getReg AbiReg.a4)
      (checkerTabMini_saveBase_align (st0.getReg AbiReg.a4) hRegAlign)
      (checkerTabMini_saveBase_valid (st0.getReg AbiReg.a4) hReg64)
      p6 ([Asm.mv AbiReg.gp AbiReg.a4] ++ post) hlSv s6 hpc6' hs6_a4
  let p7 := p6 ++ callerSaveAsm AbiReg.a4 (checkerTabMini.saveBase 0)
  have hpcSv' : sSv.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize p7) := by
    simpa only [p7, checkerLM.totalSize_append] using hpcSv
  have hlMv : checkerLM.linkSpec (p7 ++ [Asm.mv AbiReg.gp AbiReg.a4] ++ post) =
      .ok (checkerEnv.code, checkerEnv.labels) := by
    simpa only [p7, List.append_assoc] using hlSv
  obtain ⟨hrMv, hpc7, hgp7, hoth7, hm7⟩ :=
    run_aluImm_rd_step checkerEnv p7 _ .addi AbiReg.gp AbiReg.a4 0#12 (by decide) hlMv sSv hpcSv'
  let s7 := stepReg sSv AbiReg.gp (evalAluImm .addi (sSv.getReg AbiReg.a4) 0#12)
    (BitVec.ofNat 64 (4 * (checkerLM.totalSize p7 + 1)))
  have hs6_keep : ∀ q, q ≠ AbiReg.t0 → s6.getReg q = st0.getReg q := by
    intro q hqt0
    exact (hothB3 q).trans ((hothB2 q).trans ((hothB1 q).trans (hs3_eq q hqt0)))
  have hs7_keep : ∀ q, q = AbiReg.a0 ∨ q = AbiReg.a1 ∨ q = AbiReg.a2 ∨
      q = AbiReg.a3 ∨ q = AbiReg.a4 → s7.getReg q = st0.getReg q := by
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;>
      exact (hoth7 _ (by decide)).trans ((hothSv _ (by decide) (by decide)).trans (hs6_keep _ (by decide)))
  have hgpEq : s7.getReg AbiReg.gp = st0.getReg AbiReg.a4 := by
    rw [hgp7]
    change sSv.getReg AbiReg.a4 + sextImm12 0#12 = st0.getReg AbiReg.a4
    have hz : sextImm12 0#12 = 0#64 := rfl
    rw [hz, BitVec.add_zero, hothSv _ (by decide) (by decide), hs6_a4]
  have hpc7' : s7.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize
      (pre ++ drvPfx ++ drvNeedLi checkerTabMini ++ drvBootCheck checkerTabMini)) := by
    have hpEq : p7 ++ [Asm.mv AbiReg.gp AbiReg.a4] =
        pre ++ drvPfx ++ drvNeedLi checkerTabMini ++ drvBootCheck checkerTabMini := by
      dsimp only [p7, p6, p5, p4, p3, p0, drvPfx, drvBootCheck, b1, b2, b3, d0, d1, d2]
      simp only [List.cons_append, List.nil_append, List.append_assoc]
    have hsz : checkerLM.totalSize (p7 ++ [Asm.mv AbiReg.gp AbiReg.a4]) =
        checkerLM.totalSize p7 + 1 := by
      rw [checkerLM.totalSize_append]
      simp [Asm.mv, checkerLM.totalSize_instr]
    rw [hpc7, ← hsz, hpEq]
  have hm60 : s6.mem = st0.mem := by rw [hm6, hm5, hm4, hm3]
  have hsaved : DrvRegsSaved (st0.getReg AbiReg.a4) st0 s7.mem := by
    intro i hi
    rw [hm7, hsavedSv i hi]
    have hnot : ∀ r ∈ callerSaveRegs, r ≠ AbiReg.t0 := by decide
    exact hs6_keep _ (hnot (callerSaveRegs[i]'hi) (List.getElem_mem hi))
  have hout : MemEqOutside (callerSaveSpan (st0.getReg AbiReg.a4) (checkerTabMini.saveBase 0))
      st0.mem s7.mem := by
    rw [hm7, ← hm60]; exact houtSv
  refine ⟨(((checkerLM.totalSize (drvNeedLi checkerTabMini) + 1) + 1) + 1) + kSv + 1, s7, ?_, hpc7',
    hgpEq,
    hs7_keep _ (Or.inl rfl),
    hs7_keep _ (Or.inr (Or.inl rfl)),
    hs7_keep _ (Or.inr (Or.inr (Or.inl rfl))),
    hs7_keep _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
    hs7_keep _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))),
    hsaved, hout, ha5Ge, ha1Lt, ha3Lt⟩
  rw [run_add, run_add, run_add, hrunTo5]; dsimp only; rw [hrunB3]; dsimp only; rw [hrunSv]; exact hrMv

theorem drvResetStack_sim_gen {lkm : LinkModel} (env : CodeEnvGen lkm)
    (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ drvResetStack ++ post) =
      .ok (env.code, env.labels))
    (st : RV64.State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize drvResetStack)) ∧
      (∀ q, q ≠ AbiReg.t1 → st'.getReg q = st.getReg q) ∧
      MemEqOutside ⟨regionBase, 16⟩ st.mem st'.mem ∧
      readWord64 st'.mem regionBase = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) ∧
      readWord64 st'.mem (regionBase + 8#64) = regionBase + BitVec.ofNat 64 abiSlot := by
  let cTopLi := li AbiReg.t1 (BitVec.ofNat 64 (abiSlot + abiStack))
  let cTopAdd := [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1]
  let cTopSd := [Asm.sd AbiReg.gp AbiReg.t1]
  let cLimLi := li AbiReg.t1 (BitVec.ofNat 64 abiSlot)
  let cLimAdd := [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1]
  let cLimSd := [Asm.sd AbiReg.gp AbiReg.t1 8#12]
  have hl1 : lkm.linkSpec (pre ++ cTopLi ++ (cTopAdd ++ cTopSd ++ cLimLi ++ cLimAdd ++ cLimSd ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [drvResetStack, cTopLi, cTopAdd, cTopSd, cLimLi, cLimAdd, cLimSd,
      List.cons_append, List.nil_append, List.append_assoc] using hlink
  have hpc1_64 := linkResolved_sub_pc64 env pre cTopLi _ hl1
  obtain ⟨s1, hrun1, hoth1, ht1_1, hm1, hpc1⟩ :=
    li_correct_lm lkm env.hrom pre _ AbiReg.t1 (by decide)
      (BitVec.ofNat 64 (abiSlot + abiStack)) hl1 hpc1_64 st hpc
  let p1 := pre ++ cTopLi
  have hpc1' : s1.pc = BitVec.ofNat 64 (4 * lkm.totalSize p1) := by
    simpa only [p1, lkm.totalSize_append] using hpc1
  have hl2 : lkm.linkSpec (p1 ++ [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1] ++
      (cTopSd ++ cLimLi ++ cLimAdd ++ cLimSd ++ post)) = .ok (env.code, env.labels) := by
    simpa only [p1, cTopAdd, List.append_assoc] using hl1
  obtain ⟨hr2, hpc2, ht1_2, hoth2, hm2⟩ :=
    run_alu_rd_step env p1 _ .add AbiReg.t1 AbiReg.gp AbiReg.t1 (by decide) hl2 s1 hpc1'
  let s2 := stepReg s1 AbiReg.t1 (evalAlu .add (s1.getReg AbiReg.gp) (s1.getReg AbiReg.t1))
    (BitVec.ofNat 64 (4 * (lkm.totalSize p1 + 1)))
  let p2 := p1 ++ cTopAdd
  have hpc2' : s2.pc = BitVec.ofNat 64 (4 * lkm.totalSize p2) := by
    simpa only [p2, cTopAdd, lkm.totalSize_append, Asm.add, lkm.totalSize_instr] using hpc2
  have hs2gp : s2.getReg AbiReg.gp = regionBase := (hoth2 _ (by decide)).trans ((hoth1 _ (by decide)).trans hgp)
  have hs2t1 : s2.getReg AbiReg.t1 = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) := by
    rw [ht1_2]; change s1.getReg AbiReg.gp + s1.getReg AbiReg.t1 = _
    rw [(hoth1 _ (by decide)).trans hgp, ht1_1]
  have hl3 : lkm.linkSpec (p2 ++ [Asm.raw (.store .sd AbiReg.gp AbiReg.t1 0#12)] ++
      (cLimLi ++ cLimAdd ++ cLimSd ++ post)) = .ok (env.code, env.labels) := by
    simpa only [p2, cTopAdd, cTopSd, Asm.sd, Asm.raw, List.cons_append, List.nil_append, List.append_assoc] using hl2
  have hpc3_64 := linkResolved_sub_pc64 env p2 [Asm.raw (.store .sd AbiReg.gp AbiReg.t1 0#12)] _ hl3
  have hlt3_64 : 4 * (lkm.totalSize p2 + 1) < 2 ^ 64 := by
    simpa only [Asm.raw, lkm.totalSize_instr] using hpc3_64
  have hal3 : isAligned (s2.getReg AbiReg.gp + sextImm12 0#12) 8 = true := by
    have hz : sextImm12 0#12 = 0#64 := rfl; rw [hs2gp, hz, BitVec.add_zero]; exact hRegAlign
  obtain ⟨hr3, hpc3, hpres3⟩ := step_sd_off env p2 _ AbiReg.gp AbiReg.t1 0#12 hl3 hlt3_64 s2 hpc2' hal3
  let s3 := { s2 with pc := s2.pc + 4#64, mem := writeWord64 s2.mem (s2.getReg AbiReg.gp + sextImm12 0#12) (s2.getReg AbiReg.t1) }
  let p3 := p2 ++ cTopSd
  have hpc3' : s3.pc = BitVec.ofNat 64 (4 * lkm.totalSize p3) := by
    simpa only [p3, cTopSd, lkm.totalSize_append, Asm.sd, Asm.raw, lkm.totalSize_instr] using hpc3
  have hl4 : lkm.linkSpec (p3 ++ cLimLi ++ (cLimAdd ++ cLimSd ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p3, cTopSd, Asm.sd, Asm.raw, List.cons_append, List.nil_append, List.append_assoc] using hl3
  have hpc4_64 := linkResolved_sub_pc64 env p3 cLimLi _ hl4
  obtain ⟨s4, hrun4, hoth4, ht1_4, hm4, hpc4⟩ :=
    li_correct_lm lkm env.hrom p3 _ AbiReg.t1 (by decide)
      (BitVec.ofNat 64 abiSlot) hl4 hpc4_64 s3 hpc3'
  let p4 := p3 ++ cLimLi
  have hpc4' : s4.pc = BitVec.ofNat 64 (4 * lkm.totalSize p4) := by
    simpa only [p4, lkm.totalSize_append] using hpc4
  have hl5 : lkm.linkSpec (p4 ++ [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1] ++ (cLimSd ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p4, cLimAdd, List.cons_append, List.nil_append, List.append_assoc] using hl4
  obtain ⟨hr5, hpc5, ht1_5, hoth5, hm5⟩ :=
    run_alu_rd_step env p4 _ .add AbiReg.t1 AbiReg.gp AbiReg.t1 (by decide) hl5 s4 hpc4'
  let s5 := stepReg s4 AbiReg.t1 (evalAlu .add (s4.getReg AbiReg.gp) (s4.getReg AbiReg.t1))
    (BitVec.ofNat 64 (4 * (lkm.totalSize p4 + 1)))
  let p5 := p4 ++ cLimAdd
  have hpc5' : s5.pc = BitVec.ofNat 64 (4 * lkm.totalSize p5) := by
    simpa only [p5, cLimAdd, lkm.totalSize_append, Asm.add, lkm.totalSize_instr] using hpc5
  have hs5gp : s5.getReg AbiReg.gp = regionBase := (hoth5 _ (by decide)).trans ((hoth4 _ (by decide)).trans hs2gp)
  have hs5t1 : s5.getReg AbiReg.t1 = regionBase + BitVec.ofNat 64 abiSlot := by
    rw [ht1_5]; change s4.getReg AbiReg.gp + s4.getReg AbiReg.t1 = _
    rw [(hoth4 _ (by decide)).trans hs2gp, ht1_4]
  have hl6 : lkm.linkSpec (p5 ++ [Asm.raw (.store .sd AbiReg.gp AbiReg.t1 8#12)] ++ post) =
      .ok (env.code, env.labels) := by
    simpa only [p5, cLimSd, Asm.sd, Asm.raw, List.append_assoc] using hl5
  have hpc6_64 := linkResolved_sub_pc64 env p5 [Asm.raw (.store .sd AbiReg.gp AbiReg.t1 8#12)] _ hl6
  have hlt6_64 : 4 * (lkm.totalSize p5 + 1) < 2 ^ 64 := by
    simpa only [Asm.raw, lkm.totalSize_instr] using hpc6_64
  have hal6 : isAligned (s5.getReg AbiReg.gp + sextImm12 8#12) 8 = true := by
    have h8 : sextImm12 8#12 = 8#64 := rfl
    rw [hs5gp, h8]
    exact isAligned8_add_nat_mul8 regionBase hRegAlign 8 (by omega)
  obtain ⟨hr6, hpc6, _⟩ := step_sd_off env p5 _ AbiReg.gp AbiReg.t1 8#12 hl6 hlt6_64 s5 hpc5' hal6
  let s6 := { s5 with pc := s5.pc + 4#64, mem := writeWord64 s5.mem (s5.getReg AbiReg.gp + sextImm12 8#12) (s5.getReg AbiReg.t1) }
  have hreg6 : ∀ q, q ≠ AbiReg.t1 → s6.getReg q = st.getReg q := by
    intro q hq
    exact (hoth5 q hq).trans ((hoth4 q hq).trans ((hoth2 q hq).trans (hoth1 q hq)))
  have hz0 : sextImm12 0#12 = 0#64 := rfl
  have hz8 : sextImm12 8#12 = 8#64 := rfl
  have hs3mem : s3.mem = writeWord64 st.mem regionBase (regionBase + BitVec.ofNat 64 (abiSlot + abiStack)) := by
    dsimp only [s3]; rw [hs2gp, hs2t1, hz0, BitVec.add_zero, hm2, hm1]
  have hs6mem : s6.mem = writeWord64 s3.mem (regionBase + 8#64) (regionBase + BitVec.ofNat 64 abiSlot) := by
    dsimp only [s6]; rw [hs5gp, hs5t1, hz8, hm5, hm4]
  have hout : MemEqOutside ⟨regionBase, 16⟩ st.mem s6.mem := by
    have hA : MemEqOutside ⟨regionBase, 16⟩ st.mem s3.mem := by
      rw [hs3mem]; apply MemEqOutside.writeWord64
      intro k hk; exact ⟨k, by dsimp; omega, rfl⟩
    have hB : MemEqOutside ⟨regionBase, 16⟩ s3.mem s6.mem := by
      rw [hs6mem]; apply MemEqOutside.writeWord64
      intro k hk; refine ⟨8 + k, by dsimp; omega, ?_⟩
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
      have hk64 : k < 2 ^ 64 := by omega
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hk64,
        Nat.mod_eq_of_lt (by omega : 8 < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 8 + k < 2 ^ 64)]
    exact hA.trans hB
  have hread0 : readWord64 s6.mem regionBase = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) := by
    rw [hs6mem]
    have hdisj : readWord64 (writeWord64 s3.mem (regionBase + 8#64) (regionBase + BitVec.ofNat 64 abiSlot)) regionBase =
        readWord64 s3.mem regionBase := by
      apply readWord64_writeWord64_disjoint
      intro i1 i2 hi1 hi2 heq
      have ha1 := congrArg BitVec.toNat heq
      have h8lt : 8 + (BitVec.ofNat 64 i2).toNat < 2 ^ 64 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      rw [BitVec.add_assoc] at ha1
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at ha1
      have h8mod : (8 : Nat) % 2 ^ 64 = 8 := rfl
      rw [h8mod, Nat.mod_eq_of_lt (by omega : i1 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : i2 < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : 8 + i2 < 2 ^ 64)] at ha1
      have hal : regionBase.toNat % 8 = 0 := (isAligned8_iff regionBase).mp hRegAlign
      have hrb := regionBase.isLt
      have hrb8 : regionBase.toNat + 8 ≤ 2 ^ 64 := by omega
      have ha1' : regionBase.toNat + i1 = (regionBase.toNat + (8 + i2)) % 2 ^ 64 := by
        rw [Nat.mod_eq_of_lt (by omega)] at ha1; exact ha1
      by_cases hwrap : regionBase.toNat + (8 + i2) < 2 ^ 64
      · rw [Nat.mod_eq_of_lt hwrap] at ha1'; omega
      · have hmod : (regionBase.toNat + (8 + i2)) % 2 ^ 64 = regionBase.toNat + (8 + i2) - 2 ^ 64 := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hmod] at ha1'; omega
    rw [hdisj, hs3mem, readWord64_writeWord64_self]
  have hread8 : readWord64 s6.mem (regionBase + 8#64) = regionBase + BitVec.ofNat 64 abiSlot := by
    rw [hs6mem, readWord64_writeWord64_self]
  refine ⟨lkm.totalSize cTopLi + 1 + 1 + lkm.totalSize cLimLi + 1 + 1, s6, ?_, ?_, hreg6, hout, hread0, hread8⟩
  · rw [run_add, run_add, run_add, run_add, run_add, hrun1]; dsimp only
    rw [hr2]; dsimp only; rw [hr3]; dsimp only; rw [hrun4]; dsimp only; rw [hr5]; exact hr6
  · simpa only [p5, p4, p3, p2, p1, drvResetStack, cTopLi, cTopAdd, cTopSd, cLimLi, cLimAdd, cLimSd,
      lkm.totalSize_append, lkm.totalSize_cons, lkm.totalSize_nil,
      Asm.add, Asm.sd, Asm.raw, lkm.itemSize_instr,
      List.cons_append, List.nil_append, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hpc6

theorem drvResetStack_sim (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (pre post : List AsmItem)
    (hlink : checkerLM.linkSpec (pre ++ drvResetStack ++ post) =
      .ok (checkerEnv.code, checkerEnv.labels))
    (st : RV64.State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase) :
    ∃ k st',
      RV64.run checkerEnv.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (checkerLM.totalSize pre + checkerLM.totalSize drvResetStack)) ∧
      (∀ q, q ≠ AbiReg.t1 → st'.getReg q = st.getReg q) ∧
      MemEqOutside ⟨regionBase, 16⟩ st.mem st'.mem ∧
      readWord64 st'.mem regionBase = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) ∧
      readWord64 st'.mem (regionBase + 8#64) = regionBase + BitVec.ofNat 64 abiSlot :=
  drvResetStack_sim_gen checkerEnv regionBase hRegAlign pre post hlink st hpc hgp

private theorem drvBufBaseStores_eq :
    drvBufBaseStores checkerTabMini =
      storeMemOff .sd AbiReg.gp AbiReg.a0 AbiReg.t0 (checkerTabMini.dbase 0) ++
      storeMemOff .sd AbiReg.gp AbiReg.a2 AbiReg.t0 (checkerTabMini.dbase 1) := by
  unfold drvBufBaseStores
  rw [t_nbuf]
  simp [List.range_succ]

private theorem drvBufLenStores_eq :
    drvBufLenStores checkerTabMini =
      storeMemOff .sd AbiReg.gp AbiReg.a1 AbiReg.t0 (checkerTabMini.dlen 0) ++
      storeMemOff .sd AbiReg.gp AbiReg.a3 AbiReg.t0 (checkerTabMini.dlen 1) := by
  unfold drvBufLenStores
  rw [t_nbuf]
  simp [List.range_succ]

theorem drvBufBaseStores_sim_gen {lkm : LinkModel} (env : CodeEnvGen lkm)
    (regionBase inBase pinsBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ drvBufBaseStores checkerTabMini ++ post) =
      .ok (env.code, env.labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase)
    (ha0 : st.getReg AbiReg.a0 = inBase)
    (ha2 : st.getReg AbiReg.a2 = pinsBase) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre +
        lkm.totalSize (drvBufBaseStores checkerTabMini))) ∧
      (∀ q, q ≠ AbiReg.t0 → st'.getReg q = st.getReg q) ∧
      MemEqOutside ⟨regionBase + BitVec.ofNat 64 16, 8 * 205⟩ st.mem st'.mem ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 0)) = inBase ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 1)) = pinsBase := by
  have hNeedEq : abiNeed checkerTabMini = 205 * abiSlot := checkerTabMini_abiNeed_eq
  have hReg205 : regionBase.toNat + 205 * abiSlot ≤ 2 ^ 64 := by omega
  have hNeedLe : 16 + 8 * 205 ≤ 205 * abiSlot := by simp [abiSlot]
  have hb0Eq : checkerTabMini.dbase 0 = (16 : Int) := by simp [Tab.dbase]
  have hb1Eq : checkerTabMini.dbase 1 = (24 : Int) := by simp [Tab.dbase]
  have hb0Bv : BitVec.ofInt 64 (checkerTabMini.dbase 0) = BitVec.ofNat 64 16 := by
    rw [hb0Eq]; rfl
  have hb1Bv : BitVec.ofInt 64 (checkerTabMini.dbase 1) = BitVec.ofNat 64 24 := by
    rw [hb1Eq]; rfl
  let c0 := storeMemOff .sd AbiReg.gp AbiReg.a0 AbiReg.t0 (checkerTabMini.dbase 0)
  let c1 := storeMemOff .sd AbiReg.gp AbiReg.a2 AbiReg.t0 (checkerTabMini.dbase 1)
  have hl0 : lkm.linkSpec (pre ++ c0 ++ (c1 ++ post)) = .ok (env.code, env.labels) := by
    have h := hlink; rw [drvBufBaseStores_eq] at h
    simpa only [c0, c1, List.append_assoc] using h
  have hpc0_64 := linkResolved_sub_pc64 env pre c0 _ hl0
  have hal0 : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.dbase 0)) 8 = true := by
    rw [hgp, hb0Bv]; exact isAligned8_add_nat_mul8 regionBase hRegAlign 16 (by decide)
  obtain ⟨s1, hrun1, hoth1, hm1, hpc1⟩ :=
    storeMemOff_sd_correct_lm lkm env.hrom pre _ AbiReg.gp AbiReg.a0 AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.dbase 0) hl0 hpc0_64 st hpc hal0
  let p1 := pre ++ c0
  have hpc1' : s1.pc = BitVec.ofNat 64 (4 * lkm.totalSize p1) := by
    simpa only [p1, lkm.totalSize_append] using hpc1
  have hs1gp : s1.getReg AbiReg.gp = regionBase := (hoth1 _ (by decide)).trans hgp
  have hs1a2 : s1.getReg AbiReg.a2 = pinsBase := (hoth1 _ (by decide)).trans ha2
  have hl1 : lkm.linkSpec (p1 ++ c1 ++ post) = .ok (env.code, env.labels) := by
    simpa only [p1, List.append_assoc] using hl0
  have hpc1_64 := linkResolved_sub_pc64 env p1 c1 post hl1
  have hal1 : isAligned (s1.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.dbase 1)) 8 = true := by
    rw [hs1gp, hb1Bv]; exact isAligned8_add_nat_mul8 regionBase hRegAlign 24 (by decide)
  obtain ⟨s2, hrun2, hoth2, hm2, hpc2⟩ :=
    storeMemOff_sd_correct_lm lkm env.hrom p1 post AbiReg.gp AbiReg.a2 AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.dbase 1) hl1 hpc1_64 s1 hpc1' hal1
  have hs1mem : s1.mem = writeWord64 st.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 0)) inBase := by
    rw [hm1, hgp, ha0]
  have hs2mem : s2.mem = writeWord64 s1.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 1)) pinsBase := by
    rw [hm2, hs1gp, hs1a2]
  have hout1 : MemEqOutside ⟨regionBase + BitVec.ofNat 64 16, 8 * 205⟩ st.mem s1.mem := by
    rw [hs1mem, hb0Bv]
    apply MemEqOutside.writeWord64
    intro k hk; exact ⟨k, by dsimp; omega, rfl⟩
  have hout2 : MemEqOutside ⟨regionBase + BitVec.ofNat 64 16, 8 * 205⟩ s1.mem s2.mem := by
    rw [hs2mem, hb1Bv]
    apply MemEqOutside.writeWord64
    intro k hk
    refine ⟨8 + k, by dsimp; omega, ?_⟩
    rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl,
      BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    apply congrArg (regionBase + ·)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 24 + k < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 16 + (8 + k) < 2 ^ 64)]
    omega
  have hr0 : readWord64 s2.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 0)) = inBase := by
    rw [hs2mem, readWord64_writeWord64_tabOff hReg205 (by rw [hb0Eq]; omega) (by rw [hb1Eq]; omega)
      (by rw [hb0Eq]; simp [abiSlot]) (by rw [hb1Eq]; simp [abiSlot])
      (Or.inl (by rw [hb0Eq, hb1Eq]; decide)), hs1mem, readWord64_writeWord64_self]
  have hr1 : readWord64 s2.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase 1)) = pinsBase := by
    rw [hs2mem, readWord64_writeWord64_self]
  refine ⟨lkm.totalSize c0 + lkm.totalSize c1, s2, by rw [run_add, hrun1]; exact hrun2, ?_,
    fun q hq => (hoth2 q hq).trans (hoth1 q hq), hout1.trans hout2, hr0, hr1⟩
  rw [hpc2, drvBufBaseStores_eq]
  simp only [p1, c0, lkm.totalSize_append, Nat.add_assoc]

theorem drvBufLenStores_sim_gen {lkm : LinkModel} (env : CodeEnvGen lkm)
    (regionBase : BitVec 64) {inLen pinsLen : Nat}
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ drvBufLenStores checkerTabMini ++ post) =
      .ok (env.code, env.labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase)
    (ha1 : st.getReg AbiReg.a1 = BitVec.ofNat 64 inLen)
    (ha3 : st.getReg AbiReg.a3 = BitVec.ofNat 64 pinsLen) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre +
        lkm.totalSize (drvBufLenStores checkerTabMini))) ∧
      (∀ q, q ≠ AbiReg.t0 → st'.getReg q = st.getReg q) ∧
      MemEqOutside ⟨regionBase + BitVec.ofNat 64 (16 + 8 * 205), 8 * 205⟩ st.mem st'.mem ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 0)) = BitVec.ofNat 64 inLen ∧
      readWord64 st'.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 1)) = BitVec.ofNat 64 pinsLen := by
  have hNeedEq : abiNeed checkerTabMini = 205 * abiSlot := checkerTabMini_abiNeed_eq
  have hReg205 : regionBase.toNat + 205 * abiSlot ≤ 2 ^ 64 := by omega
  have hl0Eq : checkerTabMini.dlen 0 = ((16 + 8 * 205 : Nat) : Int) := by simp [Tab.dlen, t_nb, t_nw]
  have hl1Eq : checkerTabMini.dlen 1 = ((16 + 8 * 205 + 8 : Nat) : Int) := by
    simp [Tab.dlen, t_nb, t_nw]
  have hl0Bv : BitVec.ofInt 64 (checkerTabMini.dlen 0) = BitVec.ofNat 64 (16 + 8 * 205) := by
    rw [hl0Eq, BitVec.ofInt_natCast]
  have hl1Bv : BitVec.ofInt 64 (checkerTabMini.dlen 1) = BitVec.ofNat 64 (16 + 8 * 205 + 8) := by
    rw [hl1Eq, BitVec.ofInt_natCast]
  let c0 := storeMemOff .sd AbiReg.gp AbiReg.a1 AbiReg.t0 (checkerTabMini.dlen 0)
  let c1 := storeMemOff .sd AbiReg.gp AbiReg.a3 AbiReg.t0 (checkerTabMini.dlen 1)
  have hl0 : lkm.linkSpec (pre ++ c0 ++ (c1 ++ post)) = .ok (env.code, env.labels) := by
    have h := hlink; rw [drvBufLenStores_eq] at h
    simpa only [c0, c1, List.append_assoc] using h
  have hpc0_64 := linkResolved_sub_pc64 env pre c0 _ hl0
  have hal0 : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.dlen 0)) 8 = true := by
    rw [hgp, hl0Bv]; exact isAligned8_add_nat_mul8 regionBase hRegAlign (16 + 8 * 205) (by decide)
  obtain ⟨s1, hrun1, hoth1, hm1, hpc1⟩ :=
    storeMemOff_sd_correct_lm lkm env.hrom pre _ AbiReg.gp AbiReg.a1 AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.dlen 0) hl0 hpc0_64 st hpc hal0
  let p1 := pre ++ c0
  have hpc1' : s1.pc = BitVec.ofNat 64 (4 * lkm.totalSize p1) := by
    simpa only [p1, lkm.totalSize_append] using hpc1
  have hs1gp : s1.getReg AbiReg.gp = regionBase := (hoth1 _ (by decide)).trans hgp
  have hs1a3 : s1.getReg AbiReg.a3 = BitVec.ofNat 64 pinsLen := (hoth1 _ (by decide)).trans ha3
  have hl1 : lkm.linkSpec (p1 ++ c1 ++ post) = .ok (env.code, env.labels) := by
    simpa only [p1, List.append_assoc] using hl0
  have hpc1_64 := linkResolved_sub_pc64 env p1 c1 post hl1
  have hal1 : isAligned (s1.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.dlen 1)) 8 = true := by
    rw [hs1gp, hl1Bv]; exact isAligned8_add_nat_mul8 regionBase hRegAlign (16 + 8 * 205 + 8) (by decide)
  obtain ⟨s2, hrun2, hoth2, hm2, hpc2⟩ :=
    storeMemOff_sd_correct_lm lkm env.hrom p1 post AbiReg.gp AbiReg.a3 AbiReg.t0
      (by decide) (by decide) (by decide) (checkerTabMini.dlen 1) hl1 hpc1_64 s1 hpc1' hal1
  have hs1mem : s1.mem = writeWord64 st.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 0))
      (BitVec.ofNat 64 inLen) := by
    rw [hm1, hgp, ha1]
  have hs2mem : s2.mem = writeWord64 s1.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 1))
      (BitVec.ofNat 64 pinsLen) := by
    rw [hm2, hs1gp, hs1a3]
  have hout1 : MemEqOutside ⟨regionBase + BitVec.ofNat 64 (16 + 8 * 205), 8 * 205⟩ st.mem s1.mem := by
    rw [hs1mem, hl0Bv]
    apply MemEqOutside.writeWord64
    intro k hk; exact ⟨k, by dsimp; omega, rfl⟩
  have hout2 : MemEqOutside ⟨regionBase + BitVec.ofNat 64 (16 + 8 * 205), 8 * 205⟩ s1.mem s2.mem := by
    rw [hs2mem, hl1Bv]
    apply MemEqOutside.writeWord64
    intro k hk
    refine ⟨8 + k, by dsimp; omega, ?_⟩
    rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    apply congrArg (regionBase + ·)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 16 + 8 * 205 + 8 + k < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 16 + 8 * 205 + (8 + k) < 2 ^ 64)]
    omega
  have hr0 : readWord64 s2.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 0)) = BitVec.ofNat 64 inLen := by
    rw [hs2mem, readWord64_writeWord64_tabOff hReg205
      (by rw [hl0Eq]; omega) (by rw [hl1Eq]; omega)
      (by rw [hl0Eq, Int.toNat_natCast]; simp [abiSlot]) (by rw [hl1Eq, Int.toNat_natCast]; simp [abiSlot])
      (Or.inl (by rw [hl0Eq, hl1Eq, Int.toNat_natCast, Int.toNat_natCast]; omega)),
      hs1mem, readWord64_writeWord64_self]
  have hr1 : readWord64 s2.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen 1)) = BitVec.ofNat 64 pinsLen := by
    rw [hs2mem, readWord64_writeWord64_self]
  refine ⟨lkm.totalSize c0 + lkm.totalSize c1, s2, by rw [run_add, hrun1]; exact hrun2, ?_,
    fun q hq => (hoth2 q hq).trans (hoth1 q hq), hout1.trans hout2, hr0, hr1⟩
  rw [hpc2, drvBufLenStores_eq]
  simp only [p1, c0, lkm.totalSize_append, Nat.add_assoc]

theorem drvFillConstLoop_sim_gen {lkm : LinkModel} (env : CodeEnvGen lkm)
    (loopLbl doneLbl : String) (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (off : Int) (hoffNn : 0 ≤ off) (hoffMod : off.toNat % 8 = 0)
    (val : BitVec 64) (count : Nat)
    (hBound : regionBase.toNat + off.toNat + 8 * count < 2 ^ 64)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ drvFillConstLoop loopLbl doneLbl off val count ++ post) =
      .ok (env.code, env.labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre +
        lkm.totalSize (drvFillConstLoop loopLbl doneLbl off val count))) ∧
      (∀ q, q ≠ AbiReg.t0 → q ≠ AbiReg.t1 → q ≠ AbiReg.t2 → q ≠ AbiReg.t4 →
        q ≠ AbiReg.t6 → q ≠ AbiReg.s1 → st'.getReg q = st.getReg q) ∧
      MemEqOutside ⟨regionBase + BitVec.ofNat 64 off.toNat, 8 * count⟩ st.mem st'.mem ∧
      (∀ i, i < count →
        readWord64 st'.mem (regionBase + BitVec.ofNat 64 off.toNat + BitVec.ofNat 64 (8 * i)) = val) := by
  by_cases hcnt : count = 0
  · subst hcnt
    have hcode : drvFillConstLoop loopLbl doneLbl off val 0 = [] := by simp [drvFillConstLoop]
    rw [hcode, lkm.totalSize_nil, Nat.add_zero]
    exact ⟨0, st, rfl, hpc, fun _ _ _ _ _ _ _ => rfl, MemEqOutside.refl _ _, fun _ hi => by omega⟩
  · have hcntNe : (count == 0) = false := beq_false_of_ne hcnt
    have hoffInt : BitVec.ofInt 64 off = BitVec.ofNat 64 off.toNat := by
      rw [← Int.toNat_of_nonneg hoffNn, BitVec.ofInt_natCast]; rfl
    let cPtr := addImmOff AbiReg.t0 AbiReg.gp AbiReg.t4 off
    let cVal := li AbiReg.t1 val
    let cCnt := li AbiReg.t2 (BitVec.ofNat 64 count)
    let cLoop := [Asm.lbl loopLbl,
      Asm.beq AbiReg.t2 AbiReg.zero doneLbl,
      Asm.sd AbiReg.t0 AbiReg.t1,
      Asm.addi AbiReg.t0 AbiReg.t0 8#12,
      Asm.addi AbiReg.t2 AbiReg.t2 (-1#12),
      Asm.j loopLbl,
      Asm.lbl doneLbl]
    have hcode : drvFillConstLoop loopLbl doneLbl off val count = cPtr ++ cVal ++ cCnt ++ cLoop := by
      dsimp only [drvFillConstLoop, cPtr, cVal, cCnt, cLoop]
      simp only [hcntNe, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
    have hlinkPtr : lkm.linkSpec (pre ++ cPtr ++ (cVal ++ cCnt ++ cLoop ++ post)) =
        .ok (env.code, env.labels) := by
      have := hlink; rw [hcode] at this; simpa only [List.append_assoc] using this
    have hpcPtr64 := linkResolved_sub_pc64 env pre cPtr _ hlinkPtr
    obtain ⟨s1, hrun1, hoth1, ht0_1, hm1, hpc1⟩ :=
      addImmOff_correct_lm lkm env.hrom pre _ AbiReg.t0 AbiReg.gp AbiReg.t4
        (by decide) (by decide) (by decide) off hlinkPtr hpcPtr64 st hpc
    let p1 := pre ++ cPtr
    have hpc1' : s1.pc = BitVec.ofNat 64 (4 * lkm.totalSize p1) := by
      simpa only [p1, lkm.totalSize_append] using hpc1
    have hlinkVal : lkm.linkSpec (p1 ++ cVal ++ (cCnt ++ cLoop ++ post)) =
        .ok (env.code, env.labels) := by
      simpa only [p1, List.append_assoc] using hlinkPtr
    have hpcVal64 := linkResolved_sub_pc64 env p1 cVal _ hlinkVal
    obtain ⟨s2, hrun2, hoth2, ht1_2, hm2, hpc2⟩ :=
      li_correct_lm lkm env.hrom p1 _ AbiReg.t1 (by decide) val hlinkVal hpcVal64 s1 hpc1'
    let p2 := p1 ++ cVal
    have hpc2' : s2.pc = BitVec.ofNat 64 (4 * lkm.totalSize p2) := by
      simpa only [p2, lkm.totalSize_append] using hpc2
    have hlinkCnt : lkm.linkSpec (p2 ++ cCnt ++ (cLoop ++ post)) =
        .ok (env.code, env.labels) := by
      simpa only [p2, List.append_assoc] using hlinkVal
    have hpcCnt64 := linkResolved_sub_pc64 env p2 cCnt _ hlinkCnt
    obtain ⟨s3, hrun3, hoth3, ht2_3, hm3, hpc3⟩ :=
      li_correct_lm lkm env.hrom p2 _ AbiReg.t2 (by decide)
        (BitVec.ofNat 64 count) hlinkCnt hpcCnt64 s2 hpc2'
    let p3 := p2 ++ cCnt
    have hpc3' : s3.pc = BitVec.ofNat 64 (4 * lkm.totalSize p3) := by
      simpa only [p3, lkm.totalSize_append] using hpc3
    have hltLoop : lookupLabel env.labels loopLbl = some (lkm.totalSize p3) :=
      linkResolved_lbl_lm lkm p3 loopLbl _
        (by simpa only [p3, cLoop, List.cons_append, List.nil_append, List.append_assoc] using hlinkCnt)
    let preL := p3 ++ [Asm.lbl loopLbl]
    let midLoop := [Asm.beq AbiReg.t2 AbiReg.zero doneLbl,
      Asm.sd AbiReg.t0 AbiReg.t1,
      Asm.addi AbiReg.t0 AbiReg.t0 8#12,
      Asm.addi AbiReg.t2 AbiReg.t2 (-1#12),
      Asm.j loopLbl]
    have hltDone : lookupLabel env.labels doneLbl = some (lkm.totalSize (preL ++ midLoop)) :=
      linkResolved_lbl_lm lkm (preL ++ midLoop) doneLbl post
        (by simpa only [preL, midLoop, p3, cLoop, List.cons_append, List.nil_append, List.append_assoc] using hlinkCnt)
    have hloopInv : ∀ (rem : Nat) (hrem : rem ≤ count) (s : RV64.State),
        s.pc = BitVec.ofNat 64 (4 * lkm.totalSize preL) →
        s.getReg AbiReg.t0 = regionBase + BitVec.ofNat 64 off.toNat + BitVec.ofNat 64 (8 * (count - rem)) →
        s.getReg AbiReg.t1 = val →
        s.getReg AbiReg.t2 = BitVec.ofNat 64 rem →
        ∃ k s',
          RV64.run env.rom k s = .cont s' ∧
          s'.pc = BitVec.ofNat 64 (4 * lkm.totalSize (preL ++ midLoop)) ∧
          (∀ q, q ≠ AbiReg.t0 → q ≠ AbiReg.t1 → q ≠ AbiReg.t2 → q ≠ AbiReg.t6 → q ≠ AbiReg.s1 → s'.getReg q = s.getReg q) ∧
          MemEqOutside ⟨regionBase + BitVec.ofNat 64 off.toNat +
            BitVec.ofNat 64 (8 * (count - rem)), 8 * rem⟩ s.mem s'.mem ∧
          (∀ j, j < rem →
            readWord64 s'.mem (regionBase + BitVec.ofNat 64 off.toNat +
              BitVec.ofNat 64 (8 * (count - rem + j))) = val) := by
      intro rem
      induction rem with
      | zero =>
        intro hrem s hspc hst0 hst1 hst2
        have hlinkBeq : lkm.linkSpec (preL ++ [Asm.beq AbiReg.t2 AbiReg.zero doneLbl] ++
            ([Asm.sd AbiReg.t0 AbiReg.t1, Asm.addi AbiReg.t0 AbiReg.t0 8#12,
              Asm.addi AbiReg.t2 AbiReg.t2 (-1#12), Asm.j loopLbl,
              Asm.lbl doneLbl] ++ post)) = .ok (env.code, env.labels) := by
          simpa only [preL, p3, cLoop, List.cons_append, List.nil_append, List.append_assoc] using hlinkCnt
        have hbr := run_br_step env preL _ .beq AbiReg.t2 AbiReg.zero doneLbl
          (lkm.totalSize (preL ++ midLoop)) hltDone (by decide) hlinkBeq s hspc
        have heval : evalBranch .beq (s.getReg AbiReg.t2) (s.getReg AbiReg.zero) = true := by
          have hz0 : s.getReg AbiReg.zero = 0#64 := rfl
          rw [hst2, hz0]; rfl
        rw [heval] at hbr
        obtain ⟨kBr, s', _, hbrRun, hpcBr, hothBr, _, hmemBr⟩ := hbr
        simp only [↓reduceIte] at hpcBr
        exact ⟨kBr, s', hbrRun, hpcBr, fun q _ _ _ hq6 hqs1 => hothBr q ⟨hq6, hqs1⟩,
          by rw [hmemBr]; exact MemEqOutside.refl _ _, fun j hj => by omega⟩
      | succ rem' ih =>
        intro hrem s hspc hst0 hst1 hst2
        have hrem64 : rem' + 1 < 2 ^ 64 := by omega
        have hlinkBeq : lkm.linkSpec (preL ++ [Asm.beq AbiReg.t2 AbiReg.zero doneLbl] ++
            ([Asm.sd AbiReg.t0 AbiReg.t1, Asm.addi AbiReg.t0 AbiReg.t0 8#12,
              Asm.addi AbiReg.t2 AbiReg.t2 (-1#12), Asm.j loopLbl,
              Asm.lbl doneLbl] ++ post)) = .ok (env.code, env.labels) := by
          simpa only [preL, p3, cLoop, List.cons_append, List.nil_append, List.append_assoc] using hlinkCnt
        have hbr := run_br_step env preL _ .beq AbiReg.t2 AbiReg.zero doneLbl
          (lkm.totalSize (preL ++ midLoop)) hltDone (by decide) hlinkBeq s hspc
        have heval : evalBranch .beq (s.getReg AbiReg.t2) (s.getReg AbiReg.zero) = false := by
          have hz0 : s.getReg AbiReg.zero = 0#64 := rfl
          rw [hst2, hz0]
          simp only [evalBranch, beq_eq_false_iff_ne]
          intro hc
          have hc' := congrArg BitVec.toNat hc
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrem64] at hc'
          have hzNat : (0#64 : BitVec 64).toNat = 0 := rfl
          rw [hzNat] at hc'; omega
        rw [heval] at hbr
        obtain ⟨kBr, sa, _, hrunBr, hpcBr, hothBr, _, hmemBr⟩ := hbr
        simp only [Bool.false_eq_true, ↓reduceIte] at hpcBr
        let preA := preL ++ [Asm.beq AbiReg.t2 AbiReg.zero doneLbl]
        have hpcA : sa.pc = BitVec.ofNat 64 (4 * lkm.totalSize preA) := by
          rw [hpcBr]
          exact congrArg (fun n => BitVec.ofNat 64 (4 * n))
            (by simp only [preA, preL, lkm.totalSize_append, Asm.beq, Asm.br, Nat.add_assoc])
        have hsaT0 : sa.getReg AbiReg.t0 = s.getReg AbiReg.t0 := hothBr _ (by decide)
        have hsaT1 : sa.getReg AbiReg.t1 = s.getReg AbiReg.t1 := hothBr _ (by decide)
        have hsaT2 : sa.getReg AbiReg.t2 = s.getReg AbiReg.t2 := hothBr _ (by decide)
        have hlinkSd : lkm.linkSpec (preA ++ [Asm.raw (.store .sd AbiReg.t0 AbiReg.t1 0#12)] ++
            ([Asm.addi AbiReg.t0 AbiReg.t0 8#12, Asm.addi AbiReg.t2 AbiReg.t2 (-1#12),
              Asm.j loopLbl, Asm.lbl doneLbl] ++ post)) = .ok (env.code, env.labels) := by
          simpa only [preA, Asm.sd, Asm.raw, List.cons_append, List.nil_append, List.append_assoc] using hlinkBeq
        have hpcSd64 : 4 * (lkm.totalSize preA + 1) < 2 ^ 64 := by
          have h := linkResolved_sub_pc64 env preA [Asm.raw (.store .sd AbiReg.t0 AbiReg.t1 0#12)] _ hlinkSd
          rw [show lkm.totalSize [Asm.raw (.store .sd AbiReg.t0 AbiReg.t1 0#12)] = 1 from by
            simp only [Asm.raw, lkm.totalSize_instr]] at h; exact h
        have hoff64 : off.toNat < 2 ^ 64 := by omega
        have hstep8_64 : 8 * (count - (rem' + 1)) < 2 ^ 64 := by omega
        have hsum_64 : off.toNat + 8 * (count - (rem' + 1)) < 2 ^ 64 := by omega
        have halSd : isAligned (sa.getReg AbiReg.t0 + sextImm12 0#12) 8 = true := by
          have hz12 : sextImm12 0#12 = 0#64 := rfl
          have haddEq : BitVec.ofNat 64 off.toNat + BitVec.ofNat 64 (8 * (count - (rem' + 1))) =
              BitVec.ofNat 64 (off.toNat + 8 * (count - (rem' + 1))) := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt hoff64, Nat.mod_eq_of_lt hstep8_64, Nat.mod_eq_of_lt hsum_64]
          rw [hz12, BitVec.add_zero, hsaT0, hst0, BitVec.add_assoc, haddEq]
          refine isAligned8_add_nat_mul8 _ hRegAlign _ ?_
          rw [Nat.add_mul_mod_self_left]; exact hoffMod
        obtain ⟨hrunSd, hpcSd, _⟩ := step_sd_off env preA _ AbiReg.t0 AbiReg.t1 0#12 hlinkSd hpcSd64 sa hpcA halSd
        let sb : RV64.State := { sa with pc := sa.pc + 4#64, mem := writeWord64 sa.mem (sa.getReg AbiReg.t0 + sextImm12 0#12) (sa.getReg AbiReg.t1) }
        let preB := preA ++ [Asm.sd AbiReg.t0 AbiReg.t1]
        have hpcB : sb.pc = BitVec.ofNat 64 (4 * lkm.totalSize preB) := by
          simpa only [preB, lkm.totalSize_append, Asm.sd, Asm.raw, lkm.totalSize_instr] using hpcSd
        have hlinkAdd1 : lkm.linkSpec (preB ++ [Asm.addi AbiReg.t0 AbiReg.t0 8#12] ++
            ([Asm.addi AbiReg.t2 AbiReg.t2 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] ++ post)) =
            .ok (env.code, env.labels) := by
          simpa only [preB, Asm.raw, Asm.sd, List.cons_append, List.nil_append, List.append_assoc] using hlinkSd
        obtain ⟨hrunAdd1, hpcAdd1, ht0Add1, hothAdd1, hmemAdd1⟩ :=
          run_aluImm_rd_step env preB _ .addi AbiReg.t0 AbiReg.t0 8#12 (by decide) hlinkAdd1 sb hpcB
        let sc := stepReg sb AbiReg.t0 (evalAluImm .addi (sb.getReg AbiReg.t0) 8#12)
          (BitVec.ofNat 64 (4 * (lkm.totalSize preB + 1)))
        let preC := preB ++ [Asm.addi AbiReg.t0 AbiReg.t0 8#12]
        have hpcC : sc.pc = BitVec.ofNat 64 (4 * lkm.totalSize preC) := by
          simpa only [preC, lkm.totalSize_append, Asm.addi, lkm.totalSize_instr] using hpcAdd1
        have hlinkAdd2 : lkm.linkSpec (preC ++ [Asm.addi AbiReg.t2 AbiReg.t2 (-1#12)] ++
            ([Asm.j loopLbl, Asm.lbl doneLbl] ++ post)) = .ok (env.code, env.labels) := by
          simpa only [preC, List.cons_append, List.nil_append, List.append_assoc] using hlinkAdd1
        obtain ⟨hrunAdd2, hpcAdd2, ht2Add2, hothAdd2, hmemAdd2⟩ :=
          run_aluImm_rd_step env preC _ .addi AbiReg.t2 AbiReg.t2 (-1#12) (by decide) hlinkAdd2 sc hpcC
        let sd := stepReg sc AbiReg.t2 (evalAluImm .addi (sc.getReg AbiReg.t2) (-1#12))
          (BitVec.ofNat 64 (4 * (lkm.totalSize preC + 1)))
        let preD := preC ++ [Asm.addi AbiReg.t2 AbiReg.t2 (-1#12)]
        have hpcD : sd.pc = BitVec.ofNat 64 (4 * lkm.totalSize preD) := by
          simpa only [preD, lkm.totalSize_append, Asm.addi, lkm.totalSize_instr] using hpcAdd2
        have hlinkJ : lkm.linkSpec (preD ++ [Asm.j loopLbl] ++ ([Asm.lbl doneLbl] ++ post)) =
            .ok (env.code, env.labels) := by
          simpa only [preD, List.cons_append, List.nil_append, List.append_assoc] using hlinkAdd2
        have hpcJ64 := linkResolved_sub_pc64 env preD [Asm.j loopLbl] _ hlinkJ
        have hltJ64 : 4 * (lkm.totalSize preD + lkm.itemSize (.j loopLbl)) < 2 ^ 64 := by
          simpa only [Asm.j, lkm.totalSize_cons, lkm.totalSize_nil, Nat.add_zero] using hpcJ64
        obtain ⟨tgtJ, kJ, se, _, hlkpJ, hrunJ, hpcJ, hregJ, hmemJ⟩ :=
          step_item_j_lm lkm env.hrom preD _ loopLbl hlinkJ hltJ64 sd hpcD
        rw [hltLoop] at hlkpJ
        have htgtEq : tgtJ = lkm.totalSize p3 := Option.some.inj hlkpJ.symm
        have hsePc : se.pc = BitVec.ofNat 64 (4 * lkm.totalSize preL) := by
          simpa only [preL, lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero, htgtEq] using hpcJ
        have hseT0 : se.getReg AbiReg.t0 = regionBase + BitVec.ofNat 64 off.toNat +
            BitVec.ofNat 64 (8 * (count - rem')) := by
          rw [← hregJ.getReg_eq (by decide), hothAdd2 _ (by decide), ht0Add1]
          change sb.getReg AbiReg.t0 + sextImm12 8#12 = _
          have hsbT0 : sb.getReg AbiReg.t0 = sa.getReg AbiReg.t0 := rfl
          rw [hsbT0, hsaT0, hst0, BitVec.add_assoc]
          refine congrArg (regionBase + BitVec.ofNat 64 off.toNat + ·) ?_
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            show (sextImm12 8#12).toNat = 8 from rfl,
            Nat.mod_eq_of_lt (by omega : 8 * (count - (rem' + 1)) < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : 8 * (count - rem') < 2 ^ 64)]
          omega
        have hseT1 : se.getReg AbiReg.t1 = val := by
          rw [← hregJ.getReg_eq (by decide), hothAdd2 _ (by decide), hothAdd1 _ (by decide)]
          exact hsaT1.trans hst1
        have hseT2 : se.getReg AbiReg.t2 = BitVec.ofNat 64 rem' := by
          rw [← hregJ.getReg_eq (by decide), ht2Add2]
          change sc.getReg AbiReg.t2 + sextImm12 (-1#12) = BitVec.ofNat 64 rem'
          have hscT2 : sc.getReg AbiReg.t2 = sb.getReg AbiReg.t2 := hothAdd1 _ (by decide)
          have hsbT2 : sb.getReg AbiReg.t2 = sa.getReg AbiReg.t2 := rfl
          rw [hscT2, hsbT2, hsaT2, hst2]
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            show (sextImm12 (-1#12)).toNat = 2 ^ 64 - 1 from rfl,
            Nat.mod_eq_of_lt hrem64, Nat.mod_eq_of_lt (by omega : rem' < 2 ^ 64)]
          omega
        obtain ⟨kRec, sf, hrunRec, hpcRec, hothRec, houtRec, hvalRec⟩ := ih (by omega) se hsePc hseT0 hseT1 hseT2
        have hseMem : se.mem = writeWord64 s.mem (regionBase + BitVec.ofNat 64 off.toNat +
            BitVec.ofNat 64 (8 * (count - (rem' + 1)))) val := by
          have h0z : sextImm12 0#12 = 0#64 := rfl
          rw [hmemJ, hmemAdd2, hmemAdd1]; dsimp only [sb]
          rw [h0z, BitVec.add_zero, hsaT0, hsaT1, hst0, hst1, hmemBr]
        have houtStep : MemEqOutside ⟨regionBase + BitVec.ofNat 64 off.toNat +
            BitVec.ofNat 64 (8 * (count - (rem' + 1))), 8 * (rem' + 1)⟩ s.mem se.mem := by
          rw [hseMem]; apply MemEqOutside.writeWord64
          intro k hk; exact ⟨k, by dsimp; omega, rfl⟩
        have houtRec' : MemEqOutside ⟨regionBase + BitVec.ofNat 64 off.toNat +
            BitVec.ofNat 64 (8 * (count - (rem' + 1))), 8 * (rem' + 1)⟩ se.mem sf.mem := by
          apply MemEqOutside.mono _ houtRec
          intro a ⟨k, hk, ha⟩
          refine ⟨8 + k, by dsimp at hk ⊢; omega, ?_⟩
          rw [ha]
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (by omega : 8 * (count - (rem' + 1)) < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : 8 * (count - rem') < 2 ^ 64),
            Nat.mod_eq_of_lt hoff64,
            Nat.mod_eq_of_lt (by omega : regionBase.toNat + off.toNat < 2 ^ 64),
            Nat.mod_eq_of_lt (by dsimp at hk; omega : k < 2 ^ 64),
            Nat.mod_eq_of_lt (by dsimp at hk; omega : 8 + k < 2 ^ 64)]
          exact congrArg (· % 2 ^ 64) (by omega)
        refine ⟨kBr + (1 + (1 + (1 + (kJ + kRec)))), sf, ?_, hpcRec, ?_, houtStep.trans houtRec', ?_⟩
        · rw [run_add, hrunBr]; dsimp only
          rw [run_add, hrunSd]; dsimp only
          rw [run_add, hrunAdd1]; dsimp only
          rw [run_add, hrunAdd2]; dsimp only
          rw [run_add, hrunJ]; exact hrunRec
        · intro q hq0 hq1 hq2 hq6 hqs1
          have hqSc : q ≠ AbiReg.t0 → sc.getReg q = s.getReg q := fun hq0' =>
            (hothAdd1 q hq0').trans (hothBr q ⟨hq6, hqs1⟩)
          exact (hothRec q hq0 hq1 hq2 hq6 hqs1).trans
            ((hregJ.getReg_eq ⟨hq6, hqs1⟩).symm.trans ((hothAdd2 q hq2).trans (hqSc hq0)))
        · intro j hj
          cases j with
          | zero =>
            simp only [Nat.add_zero]
            have hcongr : loadBytes sf.mem (regionBase + BitVec.ofNat 64 off.toNat +
                BitVec.ofNat 64 (8 * (count - (rem' + 1)))) 8 =
                loadBytes se.mem (regionBase + BitVec.ofNat 64 off.toNat +
                  BitVec.ofNat 64 (8 * (count - (rem' + 1)))) 8 := by
              apply loadBytes_congr
              intro k hk
              apply houtRec
              intro ⟨m', hm', heq⟩
              dsimp only [MemSpan.contains] at hm'
              have hcon := congrArg BitVec.toNat heq
              rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc] at hcon
              simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hcon
              have ha1 : 8 * (count - (rem' + 1)) + k < 2 ^ 64 := by omega
              have ha2 : 8 * (count - rem') + m' < 2 ^ 64 := by omega
              have hb1 : off.toNat + (8 * (count - (rem' + 1)) + k) < 2 ^ 64 := by omega
              have hb2 : off.toNat + (8 * (count - rem') + m') < 2 ^ 64 := by omega
              have hc1 : regionBase.toNat + (off.toNat + (8 * (count - (rem' + 1)) + k)) < 2 ^ 64 := by omega
              have hc2 : regionBase.toNat + (off.toNat + (8 * (count - rem') + m')) < 2 ^ 64 := by omega
              simp only [Nat.mod_eq_of_lt hoff64,
                  Nat.mod_eq_of_lt (by omega : 8 * (count - (rem' + 1)) < 2 ^ 64),
                  Nat.mod_eq_of_lt (by omega : 8 * (count - rem') < 2 ^ 64),
                  Nat.mod_eq_of_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt (by omega : m' < 2 ^ 64),
                  Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt ha2,
                  Nat.mod_eq_of_lt hb1, Nat.mod_eq_of_lt hb2,
                  Nat.mod_eq_of_lt hc1, Nat.mod_eq_of_lt hc2] at hcon
              omega
            change loadBytes sf.mem _ 8 = val
            rw [hcongr]
            change readWord64 se.mem _ = val
            rw [hseMem, readWord64_writeWord64_self]
          | succ j' =>
            have hjj : count - (rem' + 1) + (j' + 1) = count - rem' + j' := by omega
            rw [hjj]
            exact hvalRec j' (by omega)
    have hs3pc : s3.pc = BitVec.ofNat 64 (4 * lkm.totalSize preL) := by
      have htw0 : lkm.totalSize [Asm.lbl loopLbl] = 0 := by simp only [Asm.lbl, lkm.totalSize_label]
      have htwL : lkm.totalSize preL = lkm.totalSize p3 := by
        dsimp only [preL]; rw [lkm.totalSize_append, htw0, Nat.add_zero]
      rw [hpc3', htwL]
    have hs3T0 : s3.getReg AbiReg.t0 = regionBase + BitVec.ofNat 64 off.toNat +
        BitVec.ofNat 64 (8 * (count - count)) := by
      rw [hoth3 _ (by decide), hoth2 _ (by decide), ht0_1, hgp, hoffInt, Nat.sub_self, Nat.mul_zero, BitVec.add_zero]
    have hs3T1 : s3.getReg AbiReg.t1 = val := (hoth3 _ (by decide)).trans ht1_2
    obtain ⟨kLoop, s4, hrunLoop, hpcLoop, hothLoop, houtLoop, hvalLoop⟩ :=
      hloopInv count (Nat.le_refl _) s3 hs3pc hs3T0 hs3T1 ht2_3
    rw [Nat.sub_self] at houtLoop hvalLoop
    rw [Nat.mul_zero, BitVec.add_zero] at houtLoop
    refine ⟨lkm.totalSize cPtr + lkm.totalSize cVal + lkm.totalSize cCnt + kLoop, s4, ?_, ?_, ?_, ?_, ?_⟩
    · rw [run_add, run_add, run_add, hrun1]; dsimp only; rw [hrun2]; dsimp only; rw [hrun3]; exact hrunLoop
    · have hpcEnd : lkm.totalSize (preL ++ midLoop) =
          lkm.totalSize pre + lkm.totalSize (drvFillConstLoop loopLbl doneLbl off val count) := by
        rw [hcode, lkm.totalSize_append, lkm.totalSize_append, lkm.totalSize_append]
        dsimp only [preL, p3, p2, p1, cLoop, midLoop]
        simp only [lkm.totalSize_append, lkm.totalSize_cons, lkm.totalSize_nil,
          Asm.lbl, lkm.itemSize_label, Nat.zero_add, Nat.add_zero, Nat.add_assoc]
      rw [hpcLoop, hpcEnd]
    · intro q hq0 hq1 hq2 hq4 hq6 hqs1
      exact (hothLoop q hq0 hq1 hq2 hq6 hqs1).trans ((hoth3 q hq2).trans ((hoth2 q hq1).trans (hoth1 q hq0 hq4)))
    · rw [hm3, hm2, hm1] at houtLoop; exact houtLoop
    · intro i hi
      simpa only [Nat.zero_add] using hvalLoop i hi

theorem drvFillStrideLoop_sim_gen {lkm : LinkModel} (env : CodeEnvGen lkm)
    (loopLbl doneLbl : String) (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (off : Int) (hoffNn : 0 ≤ off) (hoffMod : off.toNat % 8 = 0)
    (initOff stride : BitVec 64) (count : Nat)
    (hBound : regionBase.toNat + off.toNat + 8 * count < 2 ^ 64)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ drvFillStrideLoop loopLbl doneLbl off initOff stride count ++ post) =
      .ok (env.code, env.labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre +
        lkm.totalSize (drvFillStrideLoop loopLbl doneLbl off initOff stride count))) ∧
      (∀ q, q ≠ AbiReg.t0 → q ≠ AbiReg.t1 → q ≠ AbiReg.t2 → q ≠ AbiReg.t3 → q ≠ AbiReg.t4 →
        q ≠ AbiReg.t6 → q ≠ AbiReg.s1 → st'.getReg q = st.getReg q) ∧
      MemEqOutside ⟨regionBase + BitVec.ofNat 64 off.toNat, 8 * count⟩ st.mem st'.mem ∧
      (∀ i, i < count →
        readWord64 st'.mem (regionBase + BitVec.ofNat 64 off.toNat + BitVec.ofNat 64 (8 * i)) =
          regionBase + initOff + BitVec.ofNat 64 (i * stride.toNat)) := by
  by_cases hcnt : count = 0
  · subst hcnt
    have hcode : drvFillStrideLoop loopLbl doneLbl off initOff stride 0 = [] := by simp [drvFillStrideLoop]
    rw [hcode, lkm.totalSize_nil, Nat.add_zero]
    exact ⟨0, st, rfl, hpc, fun _ _ _ _ _ _ _ _ => rfl, MemEqOutside.refl _ _, fun _ hi => by omega⟩
  · have hcntNe : (count == 0) = false := beq_false_of_ne hcnt
    have hoffInt : BitVec.ofInt 64 off = BitVec.ofNat 64 off.toNat := by
      rw [← Int.toNat_of_nonneg hoffNn, BitVec.ofInt_natCast]; rfl
    let cPtr := addImmOff AbiReg.t0 AbiReg.gp AbiReg.t4 off
    let cInit := li AbiReg.t1 initOff
    let cAddInit := [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1]
    let cStride := li AbiReg.t3 stride
    let cCnt := li AbiReg.t2 (BitVec.ofNat 64 count)
    let cLoop := [Asm.lbl loopLbl,
      Asm.beq AbiReg.t2 AbiReg.zero doneLbl,
      Asm.sd AbiReg.t0 AbiReg.t1,
      Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3,
      Asm.addi AbiReg.t0 AbiReg.t0 8#12,
      Asm.addi AbiReg.t2 AbiReg.t2 (-1#12),
      Asm.j loopLbl,
      Asm.lbl doneLbl]
    have hcode : drvFillStrideLoop loopLbl doneLbl off initOff stride count =
        cPtr ++ cInit ++ cAddInit ++ cStride ++ cCnt ++ cLoop := by
      dsimp only [drvFillStrideLoop, cPtr, cInit, cAddInit, cStride, cCnt, cLoop]
      simp only [hcntNe, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
    have hlinkPtr : lkm.linkSpec (pre ++ cPtr ++ (cInit ++ cAddInit ++ cStride ++ cCnt ++ cLoop ++ post)) =
        .ok (env.code, env.labels) := by
      have := hlink; rw [hcode] at this; simpa only [List.append_assoc] using this
    have hpcPtr64 := linkResolved_sub_pc64 env pre cPtr _ hlinkPtr
    obtain ⟨s1, hrun1, hoth1, ht0_1, hm1, hpc1⟩ :=
      addImmOff_correct_lm lkm env.hrom pre _ AbiReg.t0 AbiReg.gp AbiReg.t4
        (by decide) (by decide) (by decide) off hlinkPtr hpcPtr64 st hpc
    let p1 := pre ++ cPtr
    have hpc1' : s1.pc = BitVec.ofNat 64 (4 * lkm.totalSize p1) := by
      simpa only [p1, lkm.totalSize_append] using hpc1
    have hlinkInit : lkm.linkSpec (p1 ++ cInit ++ (cAddInit ++ cStride ++ cCnt ++ cLoop ++ post)) =
        .ok (env.code, env.labels) := by
      simpa only [p1, List.append_assoc] using hlinkPtr
    have hpcInit64 := linkResolved_sub_pc64 env p1 cInit _ hlinkInit
    obtain ⟨s2a, hrun2a, hoth2a, ht1_2a, hm2a, hpc2a⟩ :=
      li_correct_lm lkm env.hrom p1 _ AbiReg.t1 (by decide) initOff hlinkInit hpcInit64 s1 hpc1'
    let p2a := p1 ++ cInit
    have hpc2a' : s2a.pc = BitVec.ofNat 64 (4 * lkm.totalSize p2a) := by
      simpa only [p2a, lkm.totalSize_append] using hpc2a
    have hlinkAddInit : lkm.linkSpec (p2a ++ [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1] ++
        (cStride ++ cCnt ++ cLoop ++ post)) = .ok (env.code, env.labels) := by
      simpa only [p2a, cAddInit, List.append_assoc] using hlinkInit
    obtain ⟨hrun2b, hpc2b, ht1_2b, hoth2b, hm2b⟩ :=
      run_alu_rd_step env p2a _ .add AbiReg.t1 AbiReg.gp AbiReg.t1 (by decide) hlinkAddInit s2a hpc2a'
    let s2 := stepReg s2a AbiReg.t1 (evalAlu .add (s2a.getReg AbiReg.gp) (s2a.getReg AbiReg.t1))
      (BitVec.ofNat 64 (4 * (lkm.totalSize p2a + 1)))
    let p2 := p2a ++ cAddInit
    have hpc2' : s2.pc = BitVec.ofNat 64 (4 * lkm.totalSize p2) := by
      simpa only [p2, cAddInit, lkm.totalSize_append, Asm.add, lkm.totalSize_instr] using hpc2b
    have hlinkStride : lkm.linkSpec (p2 ++ cStride ++ (cCnt ++ cLoop ++ post)) =
        .ok (env.code, env.labels) := by
      simpa only [p2, cAddInit, List.append_assoc] using hlinkAddInit
    have hpcStride64 := linkResolved_sub_pc64 env p2 cStride _ hlinkStride
    obtain ⟨s3, hrun3, hoth3, ht3_3, hm3, hpc3⟩ :=
      li_correct_lm lkm env.hrom p2 _ AbiReg.t3 (by decide) stride hlinkStride hpcStride64 s2 hpc2'
    let p3 := p2 ++ cStride
    have hpc3' : s3.pc = BitVec.ofNat 64 (4 * lkm.totalSize p3) := by
      simpa only [p3, lkm.totalSize_append] using hpc3
    have hlinkCnt : lkm.linkSpec (p3 ++ cCnt ++ (cLoop ++ post)) =
        .ok (env.code, env.labels) := by
      simpa only [p3, List.append_assoc] using hlinkStride
    have hpcCnt64 := linkResolved_sub_pc64 env p3 cCnt _ hlinkCnt
    obtain ⟨s4, hrun4, hoth4, ht2_4, hm4, hpc4⟩ :=
      li_correct_lm lkm env.hrom p3 _ AbiReg.t2 (by decide)
        (BitVec.ofNat 64 count) hlinkCnt hpcCnt64 s3 hpc3'
    let p4 := p3 ++ cCnt
    have hpc4' : s4.pc = BitVec.ofNat 64 (4 * lkm.totalSize p4) := by
      simpa only [p4, lkm.totalSize_append] using hpc4
    have hltLoop : lookupLabel env.labels loopLbl = some (lkm.totalSize p4) :=
      linkResolved_lbl_lm lkm p4 loopLbl _
        (by simpa only [p4, cLoop, List.cons_append, List.nil_append, List.append_assoc] using hlinkCnt)
    let preL := p4 ++ [Asm.lbl loopLbl]
    let midLoop := [Asm.beq AbiReg.t2 AbiReg.zero doneLbl,
      Asm.sd AbiReg.t0 AbiReg.t1,
      Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3,
      Asm.addi AbiReg.t0 AbiReg.t0 8#12,
      Asm.addi AbiReg.t2 AbiReg.t2 (-1#12),
      Asm.j loopLbl]
    have hltDone : lookupLabel env.labels doneLbl = some (lkm.totalSize (preL ++ midLoop)) :=
      linkResolved_lbl_lm lkm (preL ++ midLoop) doneLbl post
        (by simpa only [preL, midLoop, p4, cLoop, List.cons_append, List.nil_append, List.append_assoc] using hlinkCnt)
    have hloopInv : ∀ (rem : Nat) (hrem : rem ≤ count) (s : RV64.State),
        s.pc = BitVec.ofNat 64 (4 * lkm.totalSize preL) →
        s.getReg AbiReg.t0 = regionBase + BitVec.ofNat 64 off.toNat + BitVec.ofNat 64 (8 * (count - rem)) →
        s.getReg AbiReg.t1 = regionBase + initOff + BitVec.ofNat 64 ((count - rem) * stride.toNat) →
        s.getReg AbiReg.t2 = BitVec.ofNat 64 rem →
        s.getReg AbiReg.t3 = stride →
        ∃ k s',
          RV64.run env.rom k s = .cont s' ∧
          s'.pc = BitVec.ofNat 64 (4 * lkm.totalSize (preL ++ midLoop)) ∧
          (∀ q, q ≠ AbiReg.t0 → q ≠ AbiReg.t1 → q ≠ AbiReg.t2 → q ≠ AbiReg.t6 → q ≠ AbiReg.s1 → s'.getReg q = s.getReg q) ∧
          MemEqOutside ⟨regionBase + BitVec.ofNat 64 off.toNat +
            BitVec.ofNat 64 (8 * (count - rem)), 8 * rem⟩ s.mem s'.mem ∧
          (∀ j, j < rem →
            readWord64 s'.mem (regionBase + BitVec.ofNat 64 off.toNat +
              BitVec.ofNat 64 (8 * (count - rem + j))) =
              regionBase + initOff + BitVec.ofNat 64 ((count - rem + j) * stride.toNat)) := by
      intro rem
      induction rem with
      | zero =>
        intro hrem s hspc hst0 hst1 hst2 hst3
        have hlinkBeq : lkm.linkSpec (preL ++ [Asm.beq AbiReg.t2 AbiReg.zero doneLbl] ++
            ([Asm.sd AbiReg.t0 AbiReg.t1, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3,
              Asm.addi AbiReg.t0 AbiReg.t0 8#12, Asm.addi AbiReg.t2 AbiReg.t2 (-1#12),
              Asm.j loopLbl, Asm.lbl doneLbl] ++ post)) = .ok (env.code, env.labels) := by
          simpa only [preL, p4, cLoop, List.cons_append, List.nil_append, List.append_assoc] using hlinkCnt
        have hbr := run_br_step env preL _ .beq AbiReg.t2 AbiReg.zero doneLbl
          (lkm.totalSize (preL ++ midLoop)) hltDone (by decide) hlinkBeq s hspc
        have heval : evalBranch .beq (s.getReg AbiReg.t2) (s.getReg AbiReg.zero) = true := by
          have hz0 : s.getReg AbiReg.zero = 0#64 := rfl
          rw [hst2, hz0]; rfl
        rw [heval] at hbr
        obtain ⟨kBr, s', _, hbrRun, hpcBr, hothBr, _, hmemBr⟩ := hbr
        simp only [↓reduceIte] at hpcBr
        exact ⟨kBr, s', hbrRun, hpcBr, fun q _ _ _ hq6 hqs1 => hothBr q ⟨hq6, hqs1⟩,
          by rw [hmemBr]; exact MemEqOutside.refl _ _, fun j hj => by omega⟩
      | succ rem' ih =>
        intro hrem s hspc hst0 hst1 hst2 hst3
        have hrem64 : rem' + 1 < 2 ^ 64 := by omega
        have hlinkBeq : lkm.linkSpec (preL ++ [Asm.beq AbiReg.t2 AbiReg.zero doneLbl] ++
            ([Asm.sd AbiReg.t0 AbiReg.t1, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3,
              Asm.addi AbiReg.t0 AbiReg.t0 8#12, Asm.addi AbiReg.t2 AbiReg.t2 (-1#12),
              Asm.j loopLbl, Asm.lbl doneLbl] ++ post)) = .ok (env.code, env.labels) := by
          simpa only [preL, p4, cLoop, List.cons_append, List.nil_append, List.append_assoc] using hlinkCnt
        have hbr := run_br_step env preL _ .beq AbiReg.t2 AbiReg.zero doneLbl
          (lkm.totalSize (preL ++ midLoop)) hltDone (by decide) hlinkBeq s hspc
        have heval : evalBranch .beq (s.getReg AbiReg.t2) (s.getReg AbiReg.zero) = false := by
          have hz0 : s.getReg AbiReg.zero = 0#64 := rfl
          rw [hst2, hz0]
          simp only [evalBranch, beq_eq_false_iff_ne]
          intro hc
          have hc' := congrArg BitVec.toNat hc
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrem64] at hc'
          have hzNat : (0#64 : BitVec 64).toNat = 0 := rfl
          rw [hzNat] at hc'; omega
        rw [heval] at hbr
        obtain ⟨kBr, sa, _, hrunBr, hpcBr, hothBr, _, hmemBr⟩ := hbr
        simp only [Bool.false_eq_true, ↓reduceIte] at hpcBr
        let preA := preL ++ [Asm.beq AbiReg.t2 AbiReg.zero doneLbl]
        have hpcA : sa.pc = BitVec.ofNat 64 (4 * lkm.totalSize preA) := by
          rw [hpcBr]
          exact congrArg (fun n => BitVec.ofNat 64 (4 * n))
            (by simp only [preA, preL, lkm.totalSize_append, Asm.beq, Asm.br, Nat.add_assoc])
        have hsaT0 : sa.getReg AbiReg.t0 = s.getReg AbiReg.t0 := hothBr _ (by decide)
        have hsaT1 : sa.getReg AbiReg.t1 = s.getReg AbiReg.t1 := hothBr _ (by decide)
        have hsaT2 : sa.getReg AbiReg.t2 = s.getReg AbiReg.t2 := hothBr _ (by decide)
        have hsaT3 : sa.getReg AbiReg.t3 = s.getReg AbiReg.t3 := hothBr _ (by decide)
        have hlinkSd : lkm.linkSpec (preA ++ [Asm.raw (.store .sd AbiReg.t0 AbiReg.t1 0#12)] ++
            ([Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3, Asm.addi AbiReg.t0 AbiReg.t0 8#12,
              Asm.addi AbiReg.t2 AbiReg.t2 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] ++ post)) =
            .ok (env.code, env.labels) := by
          simpa only [preA, Asm.sd, Asm.raw, List.cons_append, List.nil_append, List.append_assoc] using hlinkBeq
        have hpcSd64 : 4 * (lkm.totalSize preA + 1) < 2 ^ 64 := by
          have h := linkResolved_sub_pc64 env preA [Asm.raw (.store .sd AbiReg.t0 AbiReg.t1 0#12)] _ hlinkSd
          rw [show lkm.totalSize [Asm.raw (.store .sd AbiReg.t0 AbiReg.t1 0#12)] = 1 from by
            simp only [Asm.raw, lkm.totalSize_instr]] at h; exact h
        have hoff64 : off.toNat < 2 ^ 64 := by omega
        have hstep8_64 : 8 * (count - (rem' + 1)) < 2 ^ 64 := by omega
        have hsum_64 : off.toNat + 8 * (count - (rem' + 1)) < 2 ^ 64 := by omega
        have halSd : isAligned (sa.getReg AbiReg.t0 + sextImm12 0#12) 8 = true := by
          have hz12 : sextImm12 0#12 = 0#64 := rfl
          have haddEq : BitVec.ofNat 64 off.toNat + BitVec.ofNat 64 (8 * (count - (rem' + 1))) =
              BitVec.ofNat 64 (off.toNat + 8 * (count - (rem' + 1))) := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt hoff64, Nat.mod_eq_of_lt hstep8_64, Nat.mod_eq_of_lt hsum_64]
          rw [hz12, BitVec.add_zero, hsaT0, hst0, BitVec.add_assoc, haddEq]
          refine isAligned8_add_nat_mul8 _ hRegAlign _ ?_
          rw [Nat.add_mul_mod_self_left]; exact hoffMod
        obtain ⟨hrunSd, hpcSd, _⟩ := step_sd_off env preA _ AbiReg.t0 AbiReg.t1 0#12 hlinkSd hpcSd64 sa hpcA halSd
        let sb : RV64.State := { sa with pc := sa.pc + 4#64, mem := writeWord64 sa.mem (sa.getReg AbiReg.t0 + sextImm12 0#12) (sa.getReg AbiReg.t1) }
        let preB := preA ++ [Asm.sd AbiReg.t0 AbiReg.t1]
        have hpcB : sb.pc = BitVec.ofNat 64 (4 * lkm.totalSize preB) := by
          simpa only [preB, lkm.totalSize_append, Asm.sd, Asm.raw, lkm.totalSize_instr] using hpcSd
        have hlinkAddT1 : lkm.linkSpec (preB ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3] ++
            ([Asm.addi AbiReg.t0 AbiReg.t0 8#12, Asm.addi AbiReg.t2 AbiReg.t2 (-1#12),
              Asm.j loopLbl, Asm.lbl doneLbl] ++ post)) = .ok (env.code, env.labels) := by
          simpa only [preB, Asm.raw, Asm.sd, List.cons_append, List.nil_append, List.append_assoc] using hlinkSd
        obtain ⟨hrunAddT1, hpcAddT1, ht1AddT1, hothAddT1, hmemAddT1⟩ :=
          run_alu_rd_step env preB _ .add AbiReg.t1 AbiReg.t1 AbiReg.t3 (by decide) hlinkAddT1 sb hpcB
        let sc := stepReg sb AbiReg.t1 (evalAlu .add (sb.getReg AbiReg.t1) (sb.getReg AbiReg.t3))
          (BitVec.ofNat 64 (4 * (lkm.totalSize preB + 1)))
        let preC := preB ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3]
        have hpcC : sc.pc = BitVec.ofNat 64 (4 * lkm.totalSize preC) := by
          simpa only [preC, lkm.totalSize_append, Asm.add, lkm.totalSize_instr] using hpcAddT1
        have hlinkAdd1 : lkm.linkSpec (preC ++ [Asm.addi AbiReg.t0 AbiReg.t0 8#12] ++
            ([Asm.addi AbiReg.t2 AbiReg.t2 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] ++ post)) =
            .ok (env.code, env.labels) := by
          simpa only [preC, List.cons_append, List.nil_append, List.append_assoc] using hlinkAddT1
        obtain ⟨hrunAdd1, hpcAdd1, ht0Add1, hothAdd1, hmemAdd1⟩ :=
          run_aluImm_rd_step env preC _ .addi AbiReg.t0 AbiReg.t0 8#12 (by decide) hlinkAdd1 sc hpcC
        let sd := stepReg sc AbiReg.t0 (evalAluImm .addi (sc.getReg AbiReg.t0) 8#12)
          (BitVec.ofNat 64 (4 * (lkm.totalSize preC + 1)))
        let preD := preC ++ [Asm.addi AbiReg.t0 AbiReg.t0 8#12]
        have hpcD : sd.pc = BitVec.ofNat 64 (4 * lkm.totalSize preD) := by
          simpa only [preD, lkm.totalSize_append, Asm.addi, lkm.totalSize_instr] using hpcAdd1
        have hlinkAdd2 : lkm.linkSpec (preD ++ [Asm.addi AbiReg.t2 AbiReg.t2 (-1#12)] ++
            ([Asm.j loopLbl, Asm.lbl doneLbl] ++ post)) = .ok (env.code, env.labels) := by
          simpa only [preD, List.cons_append, List.nil_append, List.append_assoc] using hlinkAdd1
        obtain ⟨hrunAdd2, hpcAdd2, ht2Add2, hothAdd2, hmemAdd2⟩ :=
          run_aluImm_rd_step env preD _ .addi AbiReg.t2 AbiReg.t2 (-1#12) (by decide) hlinkAdd2 sd hpcD
        let se := stepReg sd AbiReg.t2 (evalAluImm .addi (sd.getReg AbiReg.t2) (-1#12))
          (BitVec.ofNat 64 (4 * (lkm.totalSize preD + 1)))
        let preE := preD ++ [Asm.addi AbiReg.t2 AbiReg.t2 (-1#12)]
        have hpcE : se.pc = BitVec.ofNat 64 (4 * lkm.totalSize preE) := by
          simpa only [preE, lkm.totalSize_append, Asm.addi, lkm.totalSize_instr] using hpcAdd2
        have hlinkJ : lkm.linkSpec (preE ++ [Asm.j loopLbl] ++ ([Asm.lbl doneLbl] ++ post)) =
            .ok (env.code, env.labels) := by
          simpa only [preE, List.cons_append, List.nil_append, List.append_assoc] using hlinkAdd2
        have hpcJ64 := linkResolved_sub_pc64 env preE [Asm.j loopLbl] _ hlinkJ
        have hltJ64 : 4 * (lkm.totalSize preE + lkm.itemSize (.j loopLbl)) < 2 ^ 64 := by
          simpa only [Asm.j, lkm.totalSize_cons, lkm.totalSize_nil, Nat.add_zero] using hpcJ64
        obtain ⟨tgtJ, kJ, sf', _, hlkpJ, hrunJ, hpcJ, hregJ, hmemJ⟩ :=
          step_item_j_lm lkm env.hrom preE _ loopLbl hlinkJ hltJ64 se hpcE
        rw [hltLoop] at hlkpJ
        have htgtEq : tgtJ = lkm.totalSize p4 := Option.some.inj hlkpJ.symm
        have hsf'Pc : sf'.pc = BitVec.ofNat 64 (4 * lkm.totalSize preL) := by
          simpa only [preL, lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero, htgtEq] using hpcJ
        have hsf'T0 : sf'.getReg AbiReg.t0 = regionBase + BitVec.ofNat 64 off.toNat +
            BitVec.ofNat 64 (8 * (count - rem')) := by
          rw [← hregJ.getReg_eq (by decide), hothAdd2 _ (by decide), ht0Add1]
          change sc.getReg AbiReg.t0 + sextImm12 8#12 = _
          have hscT0 : sc.getReg AbiReg.t0 = sb.getReg AbiReg.t0 := hothAddT1 _ (by decide)
          have hsbT0 : sb.getReg AbiReg.t0 = sa.getReg AbiReg.t0 := rfl
          rw [hscT0, hsbT0, hsaT0, hst0, BitVec.add_assoc]
          refine congrArg (regionBase + BitVec.ofNat 64 off.toNat + ·) ?_
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            show (sextImm12 8#12).toNat = 8 from rfl,
            Nat.mod_eq_of_lt (by omega : 8 * (count - (rem' + 1)) < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : 8 * (count - rem') < 2 ^ 64)]
          omega
        have hsf'T1 : sf'.getReg AbiReg.t1 = regionBase + initOff +
            BitVec.ofNat 64 ((count - rem') * stride.toNat) := by
          rw [← hregJ.getReg_eq (by decide), hothAdd2 _ (by decide), hothAdd1 _ (by decide), ht1AddT1]
          change sb.getReg AbiReg.t1 + sb.getReg AbiReg.t3 = _
          have hsbT1 : sb.getReg AbiReg.t1 = sa.getReg AbiReg.t1 := rfl
          have hsbT3 : sb.getReg AbiReg.t3 = sa.getReg AbiReg.t3 := rfl
          rw [hsbT1, hsbT3, hsaT1, hsaT3, hst1, hst3, BitVec.add_assoc]
          refine congrArg (regionBase + initOff + ·) ?_
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
          have hkm : count - rem' = count - (rem' + 1) + 1 := by omega
          rw [Nat.mod_add_mod, hkm, Nat.add_mul, Nat.one_mul]
        have hsf'T2 : sf'.getReg AbiReg.t2 = BitVec.ofNat 64 rem' := by
          rw [← hregJ.getReg_eq (by decide), ht2Add2]
          change sd.getReg AbiReg.t2 + sextImm12 (-1#12) = BitVec.ofNat 64 rem'
          have hsdT2 : sd.getReg AbiReg.t2 = sc.getReg AbiReg.t2 := hothAdd1 _ (by decide)
          have hscT2 : sc.getReg AbiReg.t2 = sb.getReg AbiReg.t2 := hothAddT1 _ (by decide)
          have hsbT2 : sb.getReg AbiReg.t2 = sa.getReg AbiReg.t2 := rfl
          rw [hsdT2, hscT2, hsbT2, hsaT2, hst2]
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            show (sextImm12 (-1#12)).toNat = 2 ^ 64 - 1 from rfl,
            Nat.mod_eq_of_lt hrem64, Nat.mod_eq_of_lt (by omega : rem' < 2 ^ 64)]
          omega
        have hsf'T3 : sf'.getReg AbiReg.t3 = stride := by
          rw [← hregJ.getReg_eq (by decide), hothAdd2 _ (by decide), hothAdd1 _ (by decide), hothAddT1 _ (by decide)]
          exact hsaT3.trans hst3
        obtain ⟨kRec, sg, hrunRec, hpcRec, hothRec, houtRec, hvalRec⟩ :=
          ih (by omega) sf' hsf'Pc hsf'T0 hsf'T1 hsf'T2 hsf'T3
        have hsf'Mem : sf'.mem = writeWord64 s.mem (regionBase + BitVec.ofNat 64 off.toNat +
            BitVec.ofNat 64 (8 * (count - (rem' + 1))))
            (regionBase + initOff + BitVec.ofNat 64 ((count - (rem' + 1)) * stride.toNat)) := by
          have h0z : sextImm12 0#12 = 0#64 := rfl
          rw [hmemJ, hmemAdd2, hmemAdd1, hmemAddT1]; dsimp only [sb]
          rw [h0z, BitVec.add_zero, hsaT0, hsaT1, hst0, hst1, hmemBr]
        have houtStep : MemEqOutside ⟨regionBase + BitVec.ofNat 64 off.toNat +
            BitVec.ofNat 64 (8 * (count - (rem' + 1))), 8 * (rem' + 1)⟩ s.mem sf'.mem := by
          rw [hsf'Mem]; apply MemEqOutside.writeWord64
          intro k hk; exact ⟨k, by dsimp; omega, rfl⟩
        have houtRec' : MemEqOutside ⟨regionBase + BitVec.ofNat 64 off.toNat +
            BitVec.ofNat 64 (8 * (count - (rem' + 1))), 8 * (rem' + 1)⟩ sf'.mem sg.mem := by
          apply MemEqOutside.mono _ houtRec
          intro a ⟨k, hk, ha⟩
          refine ⟨8 + k, by dsimp at hk ⊢; omega, ?_⟩
          rw [ha]
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (by omega : 8 * (count - (rem' + 1)) < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : 8 * (count - rem') < 2 ^ 64),
            Nat.mod_eq_of_lt hoff64,
            Nat.mod_eq_of_lt (by omega : regionBase.toNat + off.toNat < 2 ^ 64),
            Nat.mod_eq_of_lt (by dsimp at hk; omega : k < 2 ^ 64),
            Nat.mod_eq_of_lt (by dsimp at hk; omega : 8 + k < 2 ^ 64)]
          exact congrArg (· % 2 ^ 64) (by omega)
        refine ⟨kBr + (1 + (1 + (1 + (1 + (kJ + kRec))))), sg, ?_, hpcRec, ?_, houtStep.trans houtRec', ?_⟩
        · rw [run_add, hrunBr]; dsimp only
          rw [run_add, hrunSd]; dsimp only
          rw [run_add, hrunAddT1]; dsimp only
          rw [run_add, hrunAdd1]; dsimp only
          rw [run_add, hrunAdd2]; dsimp only
          rw [run_add, hrunJ]; exact hrunRec
        · intro q hq0 hq1 hq2 hq6 hqs1
          have hqSd : q ≠ AbiReg.t0 → q ≠ AbiReg.t1 → sd.getReg q = s.getReg q := fun hq0' hq1' =>
            (hothAdd1 q hq0').trans ((hothAddT1 q hq1').trans (hothBr q ⟨hq6, hqs1⟩))
          exact (hothRec q hq0 hq1 hq2 hq6 hqs1).trans
            ((hregJ.getReg_eq ⟨hq6, hqs1⟩).symm.trans ((hothAdd2 q hq2).trans (hqSd hq0 hq1)))
        · intro j hj
          cases j with
          | zero =>
            simp only [Nat.add_zero]
            have hcongr : loadBytes sg.mem (regionBase + BitVec.ofNat 64 off.toNat +
                BitVec.ofNat 64 (8 * (count - (rem' + 1)))) 8 =
                loadBytes sf'.mem (regionBase + BitVec.ofNat 64 off.toNat +
                  BitVec.ofNat 64 (8 * (count - (rem' + 1)))) 8 := by
              apply loadBytes_congr
              intro k hk
              apply houtRec
              intro ⟨m', hm', heq⟩
              dsimp only [MemSpan.contains] at hm'
              have hcon := congrArg BitVec.toNat heq
              rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc] at hcon
              simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hcon
              have ha1 : 8 * (count - (rem' + 1)) + k < 2 ^ 64 := by omega
              have ha2 : 8 * (count - rem') + m' < 2 ^ 64 := by omega
              have hb1 : off.toNat + (8 * (count - (rem' + 1)) + k) < 2 ^ 64 := by omega
              have hb2 : off.toNat + (8 * (count - rem') + m') < 2 ^ 64 := by omega
              have hc1 : regionBase.toNat + (off.toNat + (8 * (count - (rem' + 1)) + k)) < 2 ^ 64 := by omega
              have hc2 : regionBase.toNat + (off.toNat + (8 * (count - rem') + m')) < 2 ^ 64 := by omega
              simp only [Nat.mod_eq_of_lt hoff64,
                  Nat.mod_eq_of_lt (by omega : 8 * (count - (rem' + 1)) < 2 ^ 64),
                  Nat.mod_eq_of_lt (by omega : 8 * (count - rem') < 2 ^ 64),
                  Nat.mod_eq_of_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt (by omega : m' < 2 ^ 64),
                  Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt ha2,
                  Nat.mod_eq_of_lt hb1, Nat.mod_eq_of_lt hb2,
                  Nat.mod_eq_of_lt hc1, Nat.mod_eq_of_lt hc2] at hcon
              omega
            change loadBytes sg.mem _ 8 = _
            rw [hcongr]
            change readWord64 sf'.mem _ = _
            rw [hsf'Mem, readWord64_writeWord64_self]
          | succ j' =>
            have hjj : count - (rem' + 1) + (j' + 1) = count - rem' + j' := by omega
            rw [hjj]
            exact hvalRec j' (by omega)
    have hs4pc : s4.pc = BitVec.ofNat 64 (4 * lkm.totalSize preL) := by
      have htw0 : lkm.totalSize [Asm.lbl loopLbl] = 0 := by simp only [Asm.lbl, lkm.totalSize_label]
      have htwL : lkm.totalSize preL = lkm.totalSize p4 := by
        dsimp only [preL]; rw [lkm.totalSize_append, htw0, Nat.add_zero]
      rw [hpc4', htwL]
    have hs4T0 : s4.getReg AbiReg.t0 = regionBase + BitVec.ofNat 64 off.toNat +
        BitVec.ofNat 64 (8 * (count - count)) := by
      rw [hoth4 _ (by decide), hoth3 _ (by decide), hoth2b _ (by decide), hoth2a _ (by decide),
        ht0_1, hgp, hoffInt, Nat.sub_self, Nat.mul_zero, BitVec.add_zero]
    have hs4T1 : s4.getReg AbiReg.t1 = regionBase + initOff +
        BitVec.ofNat 64 ((count - count) * stride.toNat) := by
      rw [hoth4 _ (by decide), hoth3 _ (by decide), ht1_2b]
      change s2a.getReg AbiReg.gp + s2a.getReg AbiReg.t1 = _
      rw [hoth2a _ (by decide), hoth1 _ (by decide) (by decide), hgp, ht1_2a, Nat.sub_self, Nat.zero_mul, BitVec.add_zero]
    have hs4T3 : s4.getReg AbiReg.t3 = stride := (hoth4 _ (by decide)).trans ht3_3
    obtain ⟨kLoop, s5, hrunLoop, hpcLoop, hothLoop, houtLoop, hvalLoop⟩ :=
      hloopInv count (Nat.le_refl _) s4 hs4pc hs4T0 hs4T1 ht2_4 hs4T3
    rw [Nat.sub_self] at houtLoop hvalLoop
    rw [Nat.mul_zero, BitVec.add_zero] at houtLoop
    refine ⟨lkm.totalSize cPtr + lkm.totalSize cInit + 1 + lkm.totalSize cStride + lkm.totalSize cCnt + kLoop,
      s5, ?_, ?_, ?_, ?_, ?_⟩
    · rw [run_add, run_add, run_add, run_add, run_add, hrun1]; dsimp only
      rw [hrun2a]; dsimp only; rw [hrun2b]; dsimp only; rw [hrun3]; dsimp only; rw [hrun4]; exact hrunLoop
    · have hpcEnd : lkm.totalSize (preL ++ midLoop) =
          lkm.totalSize pre + lkm.totalSize (drvFillStrideLoop loopLbl doneLbl off initOff stride count) := by
        rw [hcode, lkm.totalSize_append, lkm.totalSize_append, lkm.totalSize_append,
          lkm.totalSize_append, lkm.totalSize_append]
        dsimp only [preL, p4, p3, p2, p2a, p1, cAddInit, cLoop, midLoop]
        simp only [lkm.totalSize_append, lkm.totalSize_cons, lkm.totalSize_nil,
          Asm.lbl, Asm.add, lkm.itemSize_label, lkm.itemSize_instr, Nat.zero_add, Nat.add_zero, Nat.add_assoc]
      rw [hpcLoop, hpcEnd]
    · intro q hq0 hq1 hq2 hq3 hq4 hq6 hqs1
      exact (hothLoop q hq0 hq1 hq2 hq6 hqs1).trans
        ((hoth4 q hq2).trans ((hoth3 q hq3).trans ((hoth2b q hq1).trans ((hoth2a q hq1).trans (hoth1 q hq0 hq4)))))
    · rw [hm4, hm3, hm2b, hm2a, hm1] at houtLoop; exact houtLoop
    · intro i hi
      simpa only [Nat.zero_add] using hvalLoop i hi

private theorem drvRomStoresGo_sim_gen {lkm : LinkModel} (env : CodeEnvGen lkm)
    (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (idx : Nat) (ws : List (BitVec 64))
    (hbound : checkerTabMini.romBase.toNat + 8 * (idx + ws.length) ≤ abiSlot)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ drvRomStoresGo checkerTabMini.romBase idx ws ++ post) =
      .ok (env.code, env.labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre +
        lkm.totalSize (drvRomStoresGo checkerTabMini.romBase idx ws))) ∧
      (∀ q, q ≠ AbiReg.t0 → q ≠ AbiReg.t1 → st'.getReg q = st.getReg q) ∧
      MemEqOutside ⟨regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + 8 * idx), 8 * ws.length⟩
        st.mem st'.mem ∧
      (∀ (j : Nat) (hj : j < ws.length) (b : Nat), b < 8 →
        st'.mem (regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + 8 * (idx + j)) + BitVec.ofNat 64 b) =
          ws[j].extractLsb' (8 * b) 8) := by
  have hNeedEq : abiNeed checkerTabMini = 205 * abiSlot := checkerTabMini_abiNeed_eq
  have hromNn : 0 ≤ checkerTabMini.romBase := by simp [Tab.romBase]; omega
  have hromMod : checkerTabMini.romBase.toNat % 8 = 0 := by
    have hr : checkerTabMini.romBase = ((16 + 24 * (checkerTabMini.nb + checkerTabMini.nw) : Nat) : Int) := by
      simp [Tab.romBase]
    rw [hr, Int.toNat_natCast]; omega
  induction ws generalizing idx pre st with
  | nil =>
    exact ⟨0, st, rfl, by simp [drvRomStoresGo, hpc], fun _ _ _ => rfl,
      MemEqOutside.refl _ _, fun j hj => by simp at hj⟩
  | cons w rest ih =>
    let cLi := li AbiReg.t1 w
    let cSt := storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (checkerTabMini.romBase + 8 * (idx : Int))
    have hlLi : lkm.linkSpec (pre ++ cLi ++ (cSt ++ drvRomStoresGo checkerTabMini.romBase (idx + 1) rest ++ post)) =
        .ok (env.code, env.labels) := by
      simpa only [drvRomStoresGo, cLi, cSt, List.append_assoc] using hlink
    have hpcLi64 := linkResolved_sub_pc64 env pre cLi _ hlLi
    obtain ⟨s1, hrun1, hoth1, ht1_1, hm1, hpc1⟩ :=
      li_correct_lm lkm env.hrom pre _ AbiReg.t1 (by decide) w hlLi hpcLi64 st hpc
    let p1 := pre ++ cLi
    have hpc1' : s1.pc = BitVec.ofNat 64 (4 * lkm.totalSize p1) := by
      simpa only [p1, lkm.totalSize_append] using hpc1
    have hs1gp : s1.getReg AbiReg.gp = regionBase := (hoth1 _ (by decide)).trans hgp
    have hlSt : lkm.linkSpec (p1 ++ cSt ++ (drvRomStoresGo checkerTabMini.romBase (idx + 1) rest ++ post)) =
        .ok (env.code, env.labels) := by
      simpa only [p1, List.append_assoc] using hlLi
    have hpcSt64 := linkResolved_sub_pc64 env p1 cSt _ hlSt
    have hIntEq : checkerTabMini.romBase + 8 * (idx : Int) = ((checkerTabMini.romBase.toNat + 8 * idx : Nat) : Int) := by omega
    have hOffEq : BitVec.ofInt 64 (checkerTabMini.romBase + 8 * (idx : Int)) = BitVec.ofNat 64 (checkerTabMini.romBase.toNat + 8 * idx) := by
      rw [hIntEq, BitVec.ofInt_natCast]
    have halSt : isAligned (s1.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.romBase + 8 * (idx : Int))) 8 = true := by
      rw [hs1gp, hOffEq]; exact isAligned8_add_nat_mul8 regionBase hRegAlign _ (by omega)
    obtain ⟨s2, hrun2, hoth2, hm2, hpc2⟩ :=
      storeMemOff_sd_correct_lm lkm env.hrom p1 _ AbiReg.gp AbiReg.t1 AbiReg.t0
        (by decide) (by decide) (by decide) (checkerTabMini.romBase + 8 * (idx : Int)) hlSt hpcSt64 s1 hpc1' halSt
    let p2 := p1 ++ cSt
    have hpc2' : s2.pc = BitVec.ofNat 64 (4 * lkm.totalSize p2) := by
      simpa only [p2, lkm.totalSize_append] using hpc2
    have hs2gp : s2.getReg AbiReg.gp = regionBase := (hoth2 _ (by decide)).trans hs1gp
    have hlRest : lkm.linkSpec (p2 ++ drvRomStoresGo checkerTabMini.romBase (idx + 1) rest ++ post) =
        .ok (env.code, env.labels) := by
      simpa only [p2, List.append_assoc] using hlSt
    obtain ⟨kR, s3, hrunR, hpcR, hothR, houtR, hbytesR⟩ :=
      ih (idx + 1) (by simp only [List.length_cons] at hbound; omega) p2 hlRest s2 hpc2' hs2gp
    have haddrEq : regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + 8 * idx) =
        s1.getReg AbiReg.gp + BitVec.ofInt 64 (checkerTabMini.romBase + 8 * (idx : Int)) := by
      rw [hs1gp, hOffEq]
    have h1out : MemEqOutside ⟨regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + 8 * idx),
        8 * (w :: rest).length⟩ st.mem s2.mem := by
      rw [hm2, ← haddrEq, hm1]
      apply MemEqOutside.writeWord64
      intro k hk
      refine ⟨k, ?_, rfl⟩
      dsimp only [MemSpan.contains] at hk ⊢; rw [List.length_cons]; omega
    have hRout : MemEqOutside ⟨regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + 8 * idx),
        8 * (w :: rest).length⟩ s2.mem s3.mem := by
      apply MemEqOutside.mono _ houtR
      intro a ⟨k, hk, ha⟩
      dsimp only [MemSpan.contains] at hk
      simp only [List.length_cons] at hbound
      have hNeedEq : abiNeed checkerTabMini = 205 * abiSlot := checkerTabMini_abiNeed_eq
      have h211 : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; simp [abiSlot]
      refine ⟨8 + k, ?_, ?_⟩
      · dsimp only [MemSpan.contains]; rw [List.length_cons]; omega
      · rw [ha, BitVec.add_assoc, BitVec.add_assoc]
        congr 1; apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        have h164 : checkerTabMini.romBase.toNat + 8 * idx < 2 ^ 64 := by omega
        have h264 : checkerTabMini.romBase.toNat + 8 * (idx + 1) < 2 ^ 64 := by omega
        have hk64 : k < 2 ^ 64 := by omega
        have hsk64 : 8 + k < 2 ^ 64 := by omega
        rw [Nat.mod_eq_of_lt h164, Nat.mod_eq_of_lt h264, Nat.mod_eq_of_lt hk64, Nat.mod_eq_of_lt hsk64]
        omega
    refine ⟨_, s3, by rw [run_add, run_add, hrun1]; dsimp only; rw [hrun2]; exact hrunR, ?_, ?_, h1out.trans hRout, ?_⟩
    · rw [hpcR]; congr 1; congr 1
      simp only [p2, p1, cLi, cSt, drvRomStoresGo, lkm.totalSize_append, Nat.add_assoc]
    · intro q hq0 hq1; exact (hothR q hq0 hq1).trans ((hoth2 q hq0).trans (hoth1 q hq1))
    · intro j hj b hb
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        have hnotIn : ¬(MemSpan.mk (regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + 8 * (idx + 1)))
            (8 * rest.length)).contains
            (regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + 8 * idx) + BitVec.ofNat 64 b) := by
          intro ⟨m', hm', heq⟩
          dsimp only [MemSpan.contains] at hm'
          have hNeedEq : abiNeed checkerTabMini = 205 * abiSlot := checkerTabMini_abiNeed_eq
          have h211 : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; simp [abiSlot]
          simp only [List.length_cons] at hbound
          have hadd1 : regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + 8 * idx) + BitVec.ofNat 64 b =
              regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + 8 * idx + b) := by
            rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
            have ha : checkerTabMini.romBase.toNat + 8 * idx < 2 ^ 64 := by omega
            have hlt : checkerTabMini.romBase.toNat + 8 * idx + b < 2 ^ 64 := by omega
            rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : b < 2 ^ 64), Nat.mod_eq_of_lt hlt]
          have hadd2 : regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + 8 * (idx + 1)) + BitVec.ofNat 64 m' =
              regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + 8 * (idx + 1) + m') := by
            rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
            have ha : checkerTabMini.romBase.toNat + 8 * (idx + 1) < 2 ^ 64 := by omega
            have hm64 : m' < 2 ^ 64 := by omega
            have hlt : checkerTabMini.romBase.toNat + 8 * (idx + 1) + m' < 2 ^ 64 := by omega
            rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hm64, Nat.mod_eq_of_lt hlt]
          rw [hadd1, hadd2] at heq
          have hcon := congrArg BitVec.toNat heq
          rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hcon
          have ha1 : checkerTabMini.romBase.toNat + 8 * idx + b < 2 ^ 64 := by omega
          have ha2 : checkerTabMini.romBase.toNat + 8 * (idx + 1) + m' < 2 ^ 64 := by omega
          have hrb1 : regionBase.toNat + (checkerTabMini.romBase.toNat + 8 * idx + b) < 2 ^ 64 := by omega
          have hrb2 : regionBase.toNat + (checkerTabMini.romBase.toNat + 8 * (idx + 1) + m') < 2 ^ 64 := by omega
          rw [Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt ha2, Nat.mod_eq_of_lt hrb1, Nat.mod_eq_of_lt hrb2] at hcon
          omega
        rw [houtR _ hnotIn, hm2, ← haddrEq, writeWord64_apply_lt_cd _ _ _ b hb, ht1_1]
      | succ j' =>
        simp only [List.getElem_cons_succ, show idx + (j' + 1) = (idx + 1) + j' from by omega]
        exact hbytesR j' (by simp only [List.length_cons] at hj; omega) b hb

theorem drvRomStores_sim_gen {lkm : LinkModel} (env : CodeEnvGen lkm)
    (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ drvRomStoresGo checkerTabMini.romBase 0 (romWords64 checkerTabMini.rom) ++ post) =
      .ok (env.code, env.labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre +
        lkm.totalSize (drvRomStoresGo checkerTabMini.romBase 0 (romWords64 checkerTabMini.rom)))) ∧
      (∀ q, q ≠ AbiReg.t0 → q ≠ AbiReg.t1 → st'.getReg q = st.getReg q) ∧
      MemEqOutside ⟨regionBase + BitVec.ofNat 64 checkerTabMini.romBase.toNat, 8 * checkerTabMini.romWords⟩
        st.mem st'.mem ∧
      (∀ m, (hm : m < checkerTabMini.rom.length) →
        st'.mem (regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + m)) = checkerTabMini.rom[m].toBitVec) := by
  have hromBounds : checkerTabMini.romBase.toNat + 8 * checkerTabMini.romWords ≤ abiSlot := by
    have hr := checkerTabMini_romWords_lt
    have hrb : checkerTabMini.romBase = ((16 + 24 * (checkerTabMini.nb + checkerTabMini.nw) : Nat) : Int) := by
      simp [Tab.romBase]
    rw [hrb, Int.toNat_natCast, t_nb, t_nw]; simp [abiSlot]; omega
  have hwsLen : (romWords64 checkerTabMini.rom).length = checkerTabMini.romWords := by
    rw [romWords64_length]; rfl
  obtain ⟨k, st', hrun, hpc', hoth, hout, hbytes⟩ :=
    drvRomStoresGo_sim_gen env regionBase hRegAlign hReg64 0 (romWords64 checkerTabMini.rom)
      (by rw [Nat.zero_add, hwsLen]; exact hromBounds) pre post hlink st hpc hgp
  rw [Nat.mul_zero, Nat.add_zero, hwsLen] at hout
  refine ⟨k, st', hrun, hpc', hoth, hout, ?_⟩
  intro m hm
  obtain ⟨hdiv, hex⟩ := romWords64_getElem checkerTabMini.rom m hm
  have hNeedEq : abiNeed checkerTabMini = 205 * abiSlot := checkerTabMini_abiNeed_eq
  have h211 : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; simp [abiSlot]
  have hadd : regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + m) =
      regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + 8 * (0 + m / 8)) + BitVec.ofNat 64 (m % 8) := by
    rw [BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have hm8 : m / 8 < checkerTabMini.romWords := by rw [← hwsLen]; exact hdiv
    have hlt1 : checkerTabMini.romBase.toNat + 8 * (0 + m / 8) < 2 ^ 64 := by omega
    have hlt2 : checkerTabMini.romBase.toNat + m < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2, Nat.mod_eq_of_lt (by omega : m % 8 < 2 ^ 64)]
    omega
  rw [hadd, hbytes (m / 8) hdiv (m % 8) (Nat.mod_lt _ (by decide)), hex]

theorem drvRomStores_sim (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (pre post : List AsmItem)
    (hlink : checkerLM.linkSpec (pre ++ drvRomStoresGo checkerTabMini.romBase 0 (romWords64 checkerTabMini.rom) ++ post) =
      .ok (checkerEnv.code, checkerEnv.labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase) :
    ∃ k st',
      RV64.run checkerEnv.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (checkerLM.totalSize pre +
        checkerLM.totalSize (drvRomStoresGo checkerTabMini.romBase 0 (romWords64 checkerTabMini.rom)))) ∧
      (∀ q, q ≠ AbiReg.t0 → q ≠ AbiReg.t1 → st'.getReg q = st.getReg q) ∧
      MemEqOutside ⟨regionBase + BitVec.ofNat 64 checkerTabMini.romBase.toNat, 8 * checkerTabMini.romWords⟩
        st.mem st'.mem ∧
      (∀ m, (hm : m < checkerTabMini.rom.length) →
        st'.mem (regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + m)) = checkerTabMini.rom[m].toBitVec) :=
  drvRomStores_sim_gen checkerEnv regionBase hRegAlign hReg64 pre post hlink st hpc hgp

theorem drvInitSub_sim_gen {lkm : LinkModel} (env : CodeEnvGen lkm)
    (regionBase inBase pinsBase : BitVec 64) {inLen pinsLen : Nat}
    (hRegAlign : isAligned regionBase 8 = true)
    (hReg64 : regionBase.toNat + abiNeed checkerTabMini < 2 ^ 64)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ drvInitSubAsm checkerTabMini ++ post) =
      .ok (env.code, env.labels))
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase)
    (ha0 : st.getReg AbiReg.a0 = inBase)
    (ha1 : st.getReg AbiReg.a1 = BitVec.ofNat 64 inLen)
    (ha2 : st.getReg AbiReg.a2 = pinsBase)
    (ha3 : st.getReg AbiReg.a3 = BitVec.ofNat 64 pinsLen) :
    ∃ k st' m1 m2 m3 m4 m5,
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = (st.getReg AbiReg.ra &&& ~~~1#64) ∧
      (∀ q, q ≠ AbiReg.t0 → q ≠ AbiReg.t1 → q ≠ AbiReg.t2 → q ≠ AbiReg.t3 →
        q ≠ AbiReg.t4 → q ≠ AbiReg.t6 → q ≠ AbiReg.s1 → st'.getReg q = st.getReg q) ∧
      MemEqOutside ⟨regionBase, 16⟩ st.mem m1 ∧
      readWord64 m1 regionBase = regionBase + BitVec.ofNat 64 (abiSlot + abiStack) ∧
      readWord64 m1 (regionBase + 8#64) = regionBase + BitVec.ofNat 64 abiSlot ∧
      MemEqOutside ⟨regionBase + BitVec.ofNat 64 16, 8 * 205⟩ m1 m2 ∧
      (∀ i, i < checkerTabMini.nb + checkerTabMini.nw →
        readWord64 m2 (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase i)) =
          if i < 2 then if (i == 0) = true then inBase else pinsBase else
            regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.slotOf i)) ∧
      MemEqOutside ⟨regionBase + BitVec.ofNat 64 (16 + 8 * 205), 8 * 205⟩ m2 m3 ∧
      (∀ i, i < checkerTabMini.nb + checkerTabMini.nw →
        readWord64 m3 (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen i)) =
          if i < 2 then if (i == 0) = true then BitVec.ofNat 64 inLen else BitVec.ofNat 64 pinsLen
          else BitVec.ofNat 64 abiWords) ∧
      MemEqOutside ⟨regionBase + BitVec.ofNat 64 (16 + 16 * 205), 8 * 205⟩ m3 m4 ∧
      MemEqOutside ⟨regionBase + BitVec.ofNat 64 checkerTabMini.romBase.toNat,
        8 * checkerTabMini.romWords⟩ m4 m5 ∧
      (∀ m, (hm : m < checkerTabMini.rom.length) →
        m5 (regionBase + BitVec.ofNat 64 (checkerTabMini.romBase.toNat + m)) =
          checkerTabMini.rom[m].toBitVec) ∧
      MemEqOutside ⟨regionBase + BitVec.ofNat 64 checkerTabMini.resBase.toNat,
        8 * (checkerTabMini.nxres + checkerTabMini.ng)⟩ m5 st'.mem ∧
      (∀ i, i < checkerTabMini.nxres + checkerTabMini.ng →
        readWord64 st'.mem (regionBase + BitVec.ofNat 64 checkerTabMini.resBase.toNat +
          BitVec.ofNat 64 (8 * i)) = 0#64) := by
  have hNeedEq : abiNeed checkerTabMini = 205 * abiSlot := checkerTabMini_abiNeed_eq
  have hSlotLe : abiSlot ≤ abiNeed checkerTabMini := by rw [hNeedEq]; simp [abiSlot]
  have hresBounds : checkerTabMini.resBase.toNat + 8 * (checkerTabMini.nxres + checkerTabMini.ng) ≤ abiSlot := by
    have hargs := checkerTabMini_args_lt
    rw [checkerTabMini_args_eq, Int.toNat_natCast] at hargs
    rw [checkerTabMini_resBase_eq, Int.toNat_natCast, t_nxres, t_ng]
    omega
  have hresMod : checkerTabMini.resBase.toNat % 8 = 0 := by
    rw [checkerTabMini_resBase_eq, Int.toNat_natCast]; omega
  have hresNn : 0 ≤ checkerTabMini.resBase := ProgLayout.resBase_nonneg checkerTabMini
  let cBloop := drvFillStrideLoop "ca_drv_bloop" "ca_drv_bdone" (checkerTabMini.dbase checkerTabMini.nbuf)
    (BitVec.ofNat 64 (2 * abiSlot)) (BitVec.ofNat 64 abiSlot)
    (checkerTabMini.nb + checkerTabMini.nw - checkerTabMini.nbuf)
  let cLbloop := drvFillConstLoop "ca_drv_lbloop" "ca_drv_lbdone" (checkerTabMini.dlen checkerTabMini.nbuf)
    (BitVec.ofNat 64 abiSlot) (checkerTabMini.nb - checkerTabMini.nbuf)
  let cLwloop := drvFillConstLoop "ca_drv_lwloop" "ca_drv_lwdone" (checkerTabMini.dlen checkerTabMini.nb)
    (BitVec.ofNat 64 abiWords) checkerTabMini.nw
  let cL32bloop := drvFillConstLoop "ca_drv_l32bloop" "ca_drv_l32bdone" (checkerTabMini.dlen32 0)
    0#64 checkerTabMini.nb
  let cL32wloop := drvFillConstLoop "ca_drv_l32wloop" "ca_drv_l32wdone" (checkerTabMini.dlen32 checkerTabMini.nb)
    (BitVec.ofNat 64 (2 * abiWords)) checkerTabMini.nw
  let cRom := drvRomStoresGo checkerTabMini.romBase 0 (romWords64 checkerTabMini.rom)
  let cZero := drvFillConstLoop "ca_drv_zloop" "ca_drv_zdone" checkerTabMini.resBase
    0#64 (checkerTabMini.nxres + checkerTabMini.ng)
  let p0 := pre ++ [Asm.lbl drvInitLabel]
  have hpc0 : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize p0) := by
    simpa only [p0, lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero] using hpc
  have hlBody : lkm.linkSpec (p0 ++ drvResetStack ++
      (drvBufBaseStores checkerTabMini ++ cBloop ++ drvBufLenStores checkerTabMini ++
       cLbloop ++ cLwloop ++ cL32bloop ++ cL32wloop ++ cRom ++ cZero ++ ([Asm.ret] ++ post))) =
      .ok (env.code, env.labels) := by
    have h := hlink
    rw [drvInitSubAsm_decomp] at h
    dsimp only [drvInitBody] at h
    simpa only [p0, cBloop, cLbloop, cLwloop, cL32bloop, cL32wloop, cRom, cZero, List.append_assoc] using h
  -- 1. drvResetStack
  obtain ⟨k1, s1, hrun1, hpc1, hoth1, hout1, hHdrTop1, hHdrLim1⟩ :=
    drvResetStack_sim_gen env regionBase hRegAlign p0 _ hlBody st hpc0 hgp
  let p1 := p0 ++ drvResetStack
  have hpc1' : s1.pc = BitVec.ofNat 64 (4 * lkm.totalSize p1) := by
    simpa only [p1, lkm.totalSize_append] using hpc1
  have hs1gp : s1.getReg AbiReg.gp = regionBase := (hoth1 _ (by decide)).trans hgp
  have hs1a0 : s1.getReg AbiReg.a0 = inBase := (hoth1 _ (by decide)).trans ha0
  have hs1a1 : s1.getReg AbiReg.a1 = BitVec.ofNat 64 inLen := (hoth1 _ (by decide)).trans ha1
  have hs1a2 : s1.getReg AbiReg.a2 = pinsBase := (hoth1 _ (by decide)).trans ha2
  have hs1a3 : s1.getReg AbiReg.a3 = BitVec.ofNat 64 pinsLen := (hoth1 _ (by decide)).trans ha3
  -- 2. drvBufBaseStores
  have hl2a : lkm.linkSpec (p1 ++ drvBufBaseStores checkerTabMini ++
      (cBloop ++ drvBufLenStores checkerTabMini ++
       cLbloop ++ cLwloop ++ cL32bloop ++ cL32wloop ++ cRom ++ cZero ++ ([Asm.ret] ++ post))) =
      .ok (env.code, env.labels) := by
    simpa only [p1, List.append_assoc] using hlBody
  obtain ⟨k2a, s2a, hrun2a, hpc2a, hoth2a, hout2a, hBase0, hBase1⟩ :=
    drvBufBaseStores_sim_gen env regionBase inBase pinsBase hRegAlign hReg64 p1 _ hl2a s1 hpc1' hs1gp hs1a0 hs1a2
  let p2a := p1 ++ drvBufBaseStores checkerTabMini
  have hpc2a' : s2a.pc = BitVec.ofNat 64 (4 * lkm.totalSize p2a) := by
    simpa only [p2a, lkm.totalSize_append] using hpc2a
  have hs2agp : s2a.getReg AbiReg.gp = regionBase := (hoth2a _ (by decide)).trans hs1gp
  -- 3. drvFillStrideLoop for remaining base descriptors
  have hl2b : lkm.linkSpec (p2a ++ cBloop ++
      (drvBufLenStores checkerTabMini ++
       cLbloop ++ cLwloop ++ cL32bloop ++ cL32wloop ++ cRom ++ cZero ++ ([Asm.ret] ++ post))) =
      .ok (env.code, env.labels) := by
    simpa only [p2a, List.append_assoc] using hl2a
  have hdb2Eq : checkerTabMini.dbase checkerTabMini.nbuf = (32 : Int) := by
    rw [t_nbuf]; simp [Tab.dbase]
  have hdb2Nn : 0 ≤ checkerTabMini.dbase checkerTabMini.nbuf := by rw [hdb2Eq]; omega
  have hdb2Nat : (checkerTabMini.dbase checkerTabMini.nbuf).toNat = 32 := by rw [hdb2Eq]; rfl
  have hdb2Mod : (checkerTabMini.dbase checkerTabMini.nbuf).toNat % 8 = 0 := by rw [hdb2Nat]
  have hcntB : checkerTabMini.nb + checkerTabMini.nw - checkerTabMini.nbuf = 203 := by
    rw [t_nb, t_nw, t_nbuf]
  have hBbound : regionBase.toNat + (checkerTabMini.dbase checkerTabMini.nbuf).toNat +
      8 * (checkerTabMini.nb + checkerTabMini.nw - checkerTabMini.nbuf) < 2 ^ 64 := by
    rw [hdb2Nat, hcntB]
    have : 32 + 8 * 203 ≤ abiSlot := by simp [abiSlot]
    omega
  obtain ⟨k2b, s2, hrun2b, hpc2b, hoth2b, hout2b, hBaseStride⟩ :=
    drvFillStrideLoop_sim_gen env "ca_drv_bloop" "ca_drv_bdone" regionBase hRegAlign
      (checkerTabMini.dbase checkerTabMini.nbuf) hdb2Nn hdb2Mod
      (BitVec.ofNat 64 (2 * abiSlot)) (BitVec.ofNat 64 abiSlot)
      (checkerTabMini.nb + checkerTabMini.nw - checkerTabMini.nbuf)
      hBbound p2a _ hl2b s2a hpc2a' hs2agp
  let p2 := p2a ++ cBloop
  have hpc2' : s2.pc = BitVec.ofNat 64 (4 * lkm.totalSize p2) := by
    simpa only [p2, cBloop, lkm.totalSize_append] using hpc2b
  have hs2gp : s2.getReg AbiReg.gp = regionBase :=
    (hoth2b _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs2agp
  -- 4. drvBufLenStores
  have hl3a : lkm.linkSpec (p2 ++ drvBufLenStores checkerTabMini ++
      (cLbloop ++ cLwloop ++ cL32bloop ++ cL32wloop ++ cRom ++ cZero ++ ([Asm.ret] ++ post))) =
      .ok (env.code, env.labels) := by
    simpa only [p2, List.append_assoc] using hl2b
  have hs2a1 : s2.getReg AbiReg.a1 = BitVec.ofNat 64 inLen :=
    (hoth2b _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hoth2a _ (by decide)).trans hs1a1)
  have hs2a3 : s2.getReg AbiReg.a3 = BitVec.ofNat 64 pinsLen :=
    (hoth2b _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hoth2a _ (by decide)).trans hs1a3)
  obtain ⟨k3a, s3a, hrun3a, hpc3a, hoth3a, hout3a, hLen0, hLen1⟩ :=
    drvBufLenStores_sim_gen env regionBase hRegAlign hReg64 p2 _ hl3a s2 hpc2' hs2gp hs2a1 hs2a3
  let p3a := p2 ++ drvBufLenStores checkerTabMini
  have hpc3a' : s3a.pc = BitVec.ofNat 64 (4 * lkm.totalSize p3a) := by
    simpa only [p3a, lkm.totalSize_append] using hpc3a
  have hs3agp : s3a.getReg AbiReg.gp = regionBase := (hoth3a _ (by decide)).trans hs2gp
  -- 5. drvFillConstLoop ca_drv_lbloop (0 iterations for checkerTabMini)
  have hl3b : lkm.linkSpec (p3a ++ cLbloop ++
      (cLwloop ++ cL32bloop ++ cL32wloop ++ cRom ++ cZero ++ ([Asm.ret] ++ post))) =
      .ok (env.code, env.labels) := by
    simpa only [p3a, List.append_assoc] using hl3a
  have hdl2Eq : checkerTabMini.dlen checkerTabMini.nbuf = ((16 + 8 * 205 + 16 : Nat) : Int) := by
    rw [t_nbuf]; simp [Tab.dlen, t_nb, t_nw]
  have hdl2Nn : 0 ≤ checkerTabMini.dlen checkerTabMini.nbuf := by rw [hdl2Eq]; omega
  have hdl2Nat : (checkerTabMini.dlen checkerTabMini.nbuf).toNat = 16 + 8 * 205 + 16 := by
    rw [hdl2Eq, Int.toNat_natCast]
  have hdl2Mod : (checkerTabMini.dlen checkerTabMini.nbuf).toNat % 8 = 0 := by rw [hdl2Nat]
  have hcntLb : checkerTabMini.nb - checkerTabMini.nbuf = 0 := by rw [t_nb, t_nbuf]
  have hLbBound : regionBase.toNat + (checkerTabMini.dlen checkerTabMini.nbuf).toNat +
      8 * (checkerTabMini.nb - checkerTabMini.nbuf) < 2 ^ 64 := by
    rw [hdl2Nat, hcntLb]
    have : 16 + 8 * 205 + 16 + 8 * 0 ≤ abiSlot := by simp [abiSlot]
    omega
  obtain ⟨k3b, s3b, hrun3b, hpc3b, hoth3b, hout3b, _⟩ :=
    drvFillConstLoop_sim_gen env "ca_drv_lbloop" "ca_drv_lbdone" regionBase hRegAlign
      (checkerTabMini.dlen checkerTabMini.nbuf) hdl2Nn hdl2Mod
      (BitVec.ofNat 64 abiSlot) (checkerTabMini.nb - checkerTabMini.nbuf)
      hLbBound p3a _ hl3b s3a hpc3a' hs3agp
  let p3b := p3a ++ cLbloop
  have hpc3b' : s3b.pc = BitVec.ofNat 64 (4 * lkm.totalSize p3b) := by
    simpa only [p3b, cLbloop, lkm.totalSize_append] using hpc3b
  have hs3bgp : s3b.getReg AbiReg.gp = regionBase :=
    (hoth3b _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs3agp
  have hs3bMem : s3b.mem = s3a.mem := by
    funext a
    exact hout3b a (fun ⟨m, hm, _⟩ => by dsimp only [MemSpan.contains] at hm; rw [hcntLb] at hm; omega)
  -- 6. drvFillConstLoop ca_drv_lwloop
  have hl3c : lkm.linkSpec (p3b ++ cLwloop ++
      (cL32bloop ++ cL32wloop ++ cRom ++ cZero ++ ([Asm.ret] ++ post))) =
      .ok (env.code, env.labels) := by
    simpa only [p3b, List.append_assoc] using hl3b
  have hdlNbEq : checkerTabMini.dlen checkerTabMini.nb = ((16 + 8 * 205 + 16 : Nat) : Int) := by
    rw [t_nb]; simp [Tab.dlen, t_nb, t_nw]
  have hdlNbNn : 0 ≤ checkerTabMini.dlen checkerTabMini.nb := by rw [hdlNbEq]; omega
  have hdlNbNat : (checkerTabMini.dlen checkerTabMini.nb).toNat = 16 + 8 * 205 + 16 := by
    rw [hdlNbEq, Int.toNat_natCast]
  have hdlNbMod : (checkerTabMini.dlen checkerTabMini.nb).toNat % 8 = 0 := by rw [hdlNbNat]
  have hLwBound : regionBase.toNat + (checkerTabMini.dlen checkerTabMini.nb).toNat + 8 * checkerTabMini.nw < 2 ^ 64 := by
    rw [hdlNbNat, t_nw]
    have : 16 + 8 * 205 + 16 + 8 * 203 ≤ abiSlot := by simp [abiSlot]
    omega
  obtain ⟨k3c, s3, hrun3c, hpc3c, hoth3c, hout3c, hLenWords⟩ :=
    drvFillConstLoop_sim_gen env "ca_drv_lwloop" "ca_drv_lwdone" regionBase hRegAlign
      (checkerTabMini.dlen checkerTabMini.nb) hdlNbNn hdlNbMod
      (BitVec.ofNat 64 abiWords) checkerTabMini.nw
      hLwBound p3b _ hl3c s3b hpc3b' hs3bgp
  let p3 := p3b ++ cLwloop
  have hpc3' : s3.pc = BitVec.ofNat 64 (4 * lkm.totalSize p3) := by
    simpa only [p3, cLwloop, lkm.totalSize_append] using hpc3c
  have hs3gp : s3.getReg AbiReg.gp = regionBase :=
    (hoth3c _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs3bgp
  -- 7. drvFillConstLoop ca_drv_l32bloop
  have hl4a : lkm.linkSpec (p3 ++ cL32bloop ++ (cL32wloop ++ cRom ++ cZero ++ ([Asm.ret] ++ post))) =
      .ok (env.code, env.labels) := by
    simpa only [p3, List.append_assoc] using hl3c
  have hd32_0Eq : checkerTabMini.dlen32 0 = ((16 + 16 * 205 : Nat) : Int) := by
    simp [Tab.dlen32, t_nb, t_nw]
  have hd32_0Nn : 0 ≤ checkerTabMini.dlen32 0 := by rw [hd32_0Eq]; omega
  have hd32_0Nat : (checkerTabMini.dlen32 0).toNat = 16 + 16 * 205 := by
    rw [hd32_0Eq, Int.toNat_natCast]
  have hd32_0Mod : (checkerTabMini.dlen32 0).toNat % 8 = 0 := by rw [hd32_0Nat]
  have hL32bBound : regionBase.toNat + (checkerTabMini.dlen32 0).toNat + 8 * checkerTabMini.nb < 2 ^ 64 := by
    rw [hd32_0Nat, t_nb]
    have : 16 + 16 * 205 + 8 * 2 ≤ abiSlot := by simp [abiSlot]
    omega
  obtain ⟨k4a, s4a, hrun4a, hpc4a, hoth4a, hout4a, _⟩ :=
    drvFillConstLoop_sim_gen env "ca_drv_l32bloop" "ca_drv_l32bdone" regionBase hRegAlign
      (checkerTabMini.dlen32 0) hd32_0Nn hd32_0Mod 0#64 checkerTabMini.nb
      hL32bBound p3 _ hl4a s3 hpc3' hs3gp
  let p4a := p3 ++ cL32bloop
  have hpc4a' : s4a.pc = BitVec.ofNat 64 (4 * lkm.totalSize p4a) := by
    simpa only [p4a, cL32bloop, lkm.totalSize_append] using hpc4a
  have hs4agp : s4a.getReg AbiReg.gp = regionBase :=
    (hoth4a _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs3gp
  -- 8. drvFillConstLoop ca_drv_l32wloop
  have hl4b : lkm.linkSpec (p4a ++ cL32wloop ++ (cRom ++ cZero ++ ([Asm.ret] ++ post))) =
      .ok (env.code, env.labels) := by
    simpa only [p4a, List.append_assoc] using hl4a
  have hd32_2Eq : checkerTabMini.dlen32 checkerTabMini.nb = ((16 + 16 * 205 + 16 : Nat) : Int) := by
    rw [t_nb]; simp [Tab.dlen32, t_nb, t_nw]
  have hd32_2Nn : 0 ≤ checkerTabMini.dlen32 checkerTabMini.nb := by rw [hd32_2Eq]; omega
  have hd32_2Nat : (checkerTabMini.dlen32 checkerTabMini.nb).toNat = 16 + 16 * 205 + 16 := by
    rw [hd32_2Eq, Int.toNat_natCast]
  have hd32_2Mod : (checkerTabMini.dlen32 checkerTabMini.nb).toNat % 8 = 0 := by rw [hd32_2Nat]
  have hL32wBound : regionBase.toNat + (checkerTabMini.dlen32 checkerTabMini.nb).toNat + 8 * checkerTabMini.nw < 2 ^ 64 := by
    rw [hd32_2Nat, t_nw]
    have : 16 + 16 * 205 + 16 + 8 * 203 ≤ abiSlot := by simp [abiSlot]
    omega
  obtain ⟨k4b, s4, hrun4b, hpc4b, hoth4b, hout4b, _⟩ :=
    drvFillConstLoop_sim_gen env "ca_drv_l32wloop" "ca_drv_l32wdone" regionBase hRegAlign
      (checkerTabMini.dlen32 checkerTabMini.nb) hd32_2Nn hd32_2Mod
      (BitVec.ofNat 64 (2 * abiWords)) checkerTabMini.nw
      hL32wBound p4a _ hl4b s4a hpc4a' hs4agp
  let p4 := p4a ++ cL32wloop
  have hpc4' : s4.pc = BitVec.ofNat 64 (4 * lkm.totalSize p4) := by
    simpa only [p4, cL32wloop, lkm.totalSize_append] using hpc4b
  have hs4gp : s4.getReg AbiReg.gp = regionBase :=
    (hoth4b _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs4agp
  -- 9. drvRomStoresGo
  have hl5 : lkm.linkSpec (p4 ++ cRom ++ (cZero ++ ([Asm.ret] ++ post))) =
      .ok (env.code, env.labels) := by
    simpa only [p4, List.append_assoc] using hl4b
  obtain ⟨k5, s5, hrun5, hpc5, hoth5, hout5, hRom5⟩ :=
    drvRomStores_sim_gen env regionBase hRegAlign hReg64 p4 _ hl5 s4 hpc4' hs4gp
  let p5 := p4 ++ cRom
  have hpc5' : s5.pc = BitVec.ofNat 64 (4 * lkm.totalSize p5) := by
    simpa only [p5, cRom, lkm.totalSize_append] using hpc5
  have hs5gp : s5.getReg AbiReg.gp = regionBase := (hoth5 _ (by decide) (by decide)).trans hs4gp
  -- 10. drvFillConstLoop ca_drv_zloop
  have hl6 : lkm.linkSpec (p5 ++ cZero ++ ([Asm.ret] ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p5, List.append_assoc] using hl5
  have hZeroBound : regionBase.toNat + checkerTabMini.resBase.toNat +
      8 * (checkerTabMini.nxres + checkerTabMini.ng) < 2 ^ 64 := by omega
  obtain ⟨k6, s6, hrun6, hpc6, hoth6, hout6, hZero6⟩ :=
    drvFillConstLoop_sim_gen env "ca_drv_zloop" "ca_drv_zdone" regionBase hRegAlign
      checkerTabMini.resBase hresNn hresMod 0#64 (checkerTabMini.nxres + checkerTabMini.ng)
      hZeroBound p5 _ hl6 s5 hpc5' hs5gp
  let p6 := p5 ++ cZero
  have hpc6' : s6.pc = BitVec.ofNat 64 (4 * lkm.totalSize p6) := by
    simpa only [p6, cZero, lkm.totalSize_append] using hpc6
  -- 11. Asm.ret
  have hlRet : lkm.linkSpec (p6 ++ [Asm.ret] ++ post) = .ok (env.code, env.labels) := by
    simpa only [p6, List.append_assoc] using hl6
  have h64Ret := linkResolved_sub_pc64 env p6 [Asm.ret] post hlRet
  have hltRet : 4 * lkm.totalSize p6 < 2 ^ 64 := by
    have htw : lkm.totalSize [Asm.ret] = 1 := by simp [Asm.ret, lkm.totalSize_instr]
    rw [htw] at h64Ret; omega
  have hstepRet := step_item_ret_lm lkm env.hrom p6 post hlRet hltRet s6 hpc6'
  let st' : RV64.State := { s6 with pc := s6.getReg AbiReg.ra &&& ~~~1#64 }
  have hrunRet : RV64.run env.rom 1 s6 = .cont st' := by
    simp only [RV64.run, hstepRet, st']
  -- Combine register preservation and memory facts
  have hregs : ∀ q, q ≠ AbiReg.t0 → q ≠ AbiReg.t1 → q ≠ AbiReg.t2 → q ≠ AbiReg.t3 →
      q ≠ AbiReg.t4 → q ≠ AbiReg.t6 → q ≠ AbiReg.s1 → st'.getReg q = st.getReg q := by
    intro q h0 h1 h2 h3 h4 h6 hs1
    change s6.getReg q = st.getReg q
    exact (hoth6 q h0 h1 h2 h4 h6 hs1).trans
      ((hoth5 q h0 h1).trans
      ((hoth4b q h0 h1 h2 h4 h6 hs1).trans
      ((hoth4a q h0 h1 h2 h4 h6 hs1).trans
      ((hoth3c q h0 h1 h2 h4 h6 hs1).trans
      ((hoth3b q h0 h1 h2 h4 h6 hs1).trans
      ((hoth3a q h0).trans
      ((hoth2b q h0 h1 h2 h3 h4 h6 hs1).trans
      ((hoth2a q h0).trans (hoth1 q h1)))))))))
  have houtM12 : MemEqOutside ⟨regionBase + BitVec.ofNat 64 16, 8 * 205⟩ s1.mem s2.mem := by
    refine hout2a.trans (MemEqOutside.mono ?_ hout2b)
    intro a ⟨k, hk, ha⟩
    dsimp only [MemSpan.contains] at hk ⊢
    rw [hcntB] at hk
    rw [hdb2Nat] at ha
    refine ⟨16 + k, by omega, ?_⟩
    rw [ha, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    exact congrArg (fun n => regionBase + BitVec.ofNat 64 n) (by omega)
  have hBaseAll : ∀ i, i < checkerTabMini.nb + checkerTabMini.nw →
      readWord64 s2.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase i)) =
        if i < 2 then if (i == 0) = true then inBase else pinsBase else
          regionBase + BitVec.ofNat 64 (abiSlot * checkerTabMini.slotOf i) := by
    intro i hi
    have hi205 : i < 205 := by rw [t_nb, t_nw] at hi; exact hi
    by_cases hi2 : i < 2
    · simp only [hi2, ↓reduceIte]
      have hpres : readWord64 s2.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase i)) =
          readWord64 s2a.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dbase i)) := by
        apply MemEqOutside.readWord64_eq hout2b
        intro k hk ⟨m, hm, heq⟩
        dsimp only [MemSpan.contains] at hm
        rw [hcntB] at hm
        rw [hdb2Nat] at heq
        have hbInt : checkerTabMini.dbase i = ((16 + 8 * i : Nat) : Int) := by
          simp [Tab.dbase]
        have hbBv : BitVec.ofInt 64 (checkerTabMini.dbase i) = BitVec.ofNat 64 (16 + 8 * i) := by
          rw [hbInt, BitVec.ofInt_natCast]
        rw [hbBv, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add] at heq
        have hcon := congrArg BitVec.toNat heq
        have ha1 : 16 + 8 * i + k < 2 ^ 64 := by omega
        have ha2 : 32 + m < 2 ^ 64 := by omega
        have hb1 : regionBase.toNat + (16 + 8 * i + k) < 2 ^ 64 := by
          have : 16 + 8 * i + k ≤ abiSlot := by simp [abiSlot]; omega
          omega
        have hb2 : regionBase.toNat + (32 + m) < 2 ^ 64 := by
          have : 32 + m ≤ abiSlot := by simp [abiSlot]; omega
          omega
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt ha2, Nat.mod_eq_of_lt hb1, Nat.mod_eq_of_lt hb2] at hcon
        omega
      rw [hpres]
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · exact hBase0
      · exact hBase1
    · simp only [hi2, ↓reduceIte]
      have hbInt : checkerTabMini.dbase i = ((16 + 8 * i : Nat) : Int) := by simp [Tab.dbase]
      have haddr : regionBase + BitVec.ofInt 64 (checkerTabMini.dbase i) =
          regionBase + BitVec.ofNat 64 (checkerTabMini.dbase checkerTabMini.nbuf).toNat +
            BitVec.ofNat 64 (8 * (i - 2)) := by
        rw [hbInt, BitVec.ofInt_natCast, hdb2Nat, BitVec.add_assoc, ← BitVec.ofNat_add]
        exact congrArg (fun n => regionBase + BitVec.ofNat 64 n) (by omega)
      rw [haddr, hBaseStride (i - 2) (by rw [hcntB]; omega), BitVec.add_assoc]
      apply congrArg (regionBase + ·)
      have hslot : checkerTabMini.slotOf i = i := by simp [Tab.slotOf, t_nbuf]
      rw [hslot]
      apply BitVec.eq_of_toNat_eq
      have hslot64 : abiSlot < 2 ^ 64 := by simp [abiSlot]
      have h2slot : 2 * abiSlot < 2 ^ 64 := by simp [abiSlot]
      have him2 : (i - 2) * abiSlot < 2 ^ 64 := by
        have : (i - 2) * abiSlot ≤ 205 * abiSlot := Nat.mul_le_mul_right abiSlot (by omega)
        simp [abiSlot] at *; omega
      have hislot : abiSlot * i < 2 ^ 64 := by
        have : abiSlot * i ≤ abiSlot * 205 := Nat.mul_le_mul_left abiSlot (by omega)
        simp [abiSlot] at *; omega
      have hsum64 : 2 * abiSlot + (i - 2) * abiSlot < 2 ^ 64 := by
        rw [← Nat.add_mul, Nat.add_sub_cancel' (by omega), Nat.mul_comm]; exact hislot
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hslot64, Nat.mod_eq_of_lt h2slot,
        Nat.mod_eq_of_lt him2, Nat.mod_eq_of_lt hislot, Nat.mod_eq_of_lt hsum64,
        Nat.mul_comm abiSlot i, ← Nat.add_mul, Nat.add_sub_cancel' (by omega)]
  have houtM23 : MemEqOutside ⟨regionBase + BitVec.ofNat 64 (16 + 8 * 205), 8 * 205⟩ s2.mem s3.mem := by
    refine hout3a.trans ?_
    rw [← hs3bMem]
    refine MemEqOutside.mono ?_ hout3c
    intro a ⟨k, hk, ha⟩
    dsimp only [MemSpan.contains] at hk ⊢
    rw [t_nw] at hk
    rw [hdlNbNat] at ha
    refine ⟨16 + k, by omega, ?_⟩
    rw [ha, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    exact congrArg (fun n => regionBase + BitVec.ofNat 64 n) (by omega)
  have hLenAll : ∀ i, i < checkerTabMini.nb + checkerTabMini.nw →
      readWord64 s3.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen i)) =
        if i < 2 then if (i == 0) = true then BitVec.ofNat 64 inLen else BitVec.ofNat 64 pinsLen
        else BitVec.ofNat 64 abiWords := by
    intro i hi
    have hi205 : i < 205 := by rw [t_nb, t_nw] at hi; exact hi
    by_cases hi2 : i < 2
    · simp only [hi2, ↓reduceIte]
      have hpres : readWord64 s3.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen i)) =
          readWord64 s3a.mem (regionBase + BitVec.ofInt 64 (checkerTabMini.dlen i)) := by
        rw [← hs3bMem]
        apply MemEqOutside.readWord64_eq hout3c
        intro k hk ⟨m, hm, heq⟩
        dsimp only [MemSpan.contains] at hm
        rw [t_nw] at hm
        rw [hdlNbNat] at heq
        have hlInt : checkerTabMini.dlen i = ((16 + 8 * 205 + 8 * i : Nat) : Int) := by
          simp [Tab.dlen, t_nb, t_nw]
        have hlBv : BitVec.ofInt 64 (checkerTabMini.dlen i) = BitVec.ofNat 64 (16 + 8 * 205 + 8 * i) := by
          rw [hlInt, BitVec.ofInt_natCast]
        rw [hlBv, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add] at heq
        have hcon := congrArg BitVec.toNat heq
        have ha1 : 16 + 8 * 205 + 8 * i + k < 2 ^ 64 := by omega
        have ha2 : 16 + 8 * 205 + 16 + m < 2 ^ 64 := by omega
        have hb1 : regionBase.toNat + (16 + 8 * 205 + 8 * i + k) < 2 ^ 64 := by
          have : 16 + 8 * 205 + 8 * i + k ≤ abiSlot := by simp [abiSlot]; omega
          omega
        have hb2 : regionBase.toNat + (16 + 8 * 205 + 16 + m) < 2 ^ 64 := by
          have : 16 + 8 * 205 + 16 + m ≤ abiSlot := by simp [abiSlot]; omega
          omega
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt ha2, Nat.mod_eq_of_lt hb1, Nat.mod_eq_of_lt hb2] at hcon
        omega
      rw [hpres]
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · exact hLen0
      · exact hLen1
    · simp only [hi2, ↓reduceIte]
      have hlInt : checkerTabMini.dlen i = ((16 + 8 * 205 + 8 * i : Nat) : Int) := by
        simp [Tab.dlen, t_nb, t_nw]
      have haddr : regionBase + BitVec.ofInt 64 (checkerTabMini.dlen i) =
          regionBase + BitVec.ofNat 64 (checkerTabMini.dlen checkerTabMini.nb).toNat +
            BitVec.ofNat 64 (8 * (i - 2)) := by
        rw [hlInt, BitVec.ofInt_natCast, hdlNbNat, BitVec.add_assoc, ← BitVec.ofNat_add]
        exact congrArg (fun n => regionBase + BitVec.ofNat 64 n) (by omega)
      rw [haddr, hLenWords (i - 2) (by rw [t_nw]; omega)]
  have houtM34 : MemEqOutside ⟨regionBase + BitVec.ofNat 64 (16 + 16 * 205), 8 * 205⟩ s3.mem s4.mem := by
    have hA : MemEqOutside ⟨regionBase + BitVec.ofNat 64 (16 + 16 * 205), 8 * 205⟩ s3.mem s4a.mem := by
      refine MemEqOutside.mono ?_ hout4a
      intro a ⟨k, hk, ha⟩
      dsimp only [MemSpan.contains] at hk ⊢
      rw [t_nb] at hk
      rw [hd32_0Nat] at ha
      exact ⟨k, by omega, ha⟩
    have hB : MemEqOutside ⟨regionBase + BitVec.ofNat 64 (16 + 16 * 205), 8 * 205⟩ s4a.mem s4.mem := by
      refine MemEqOutside.mono ?_ hout4b
      intro a ⟨k, hk, ha⟩
      dsimp only [MemSpan.contains] at hk ⊢
      rw [t_nw] at hk
      rw [hd32_2Nat] at ha
      refine ⟨16 + k, by omega, ?_⟩
      rw [ha, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
      exact congrArg (fun n => regionBase + BitVec.ofNat 64 n) (by omega)
    exact hA.trans hB
  refine ⟨k1 + k2a + k2b + k3a + k3b + k3c + k4a + k4b + k5 + k6 + 1,
    st', s1.mem, s2.mem, s3.mem, s4.mem, s5.mem, ?_, ?_, hregs,
    hout1, hHdrTop1, hHdrLim1, houtM12, hBaseAll, houtM23, hLenAll, houtM34,
    hout5, hRom5, hout6, hZero6⟩
  · rw [run_add, run_add, run_add, run_add, run_add, run_add, run_add, run_add, run_add, run_add, hrun1]
    dsimp only; rw [hrun2a]; dsimp only; rw [hrun2b]; dsimp only; rw [hrun3a]
    dsimp only; rw [hrun3b]; dsimp only; rw [hrun3c]; dsimp only; rw [hrun4a]
    dsimp only; rw [hrun4b]; dsimp only; rw [hrun5]; dsimp only; rw [hrun6]; exact hrunRet
  · exact congrArg (· &&& ~~~1#64)
      (hregs AbiReg.ra (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))

private theorem checker_done_stub_returns {lkm : LinkModel} (env : CodeEnvGen lkm)
    (pre tail : List AsmItem) (initSt : RV64.State) (T : BitVec 64)
    (halign : isAligned (T + BitVec.ofInt 64 (env.tab.saveBase 0)) 8 = true)
    (hlink : lkm.linkSpec (pre ++ drvDoneStub ++ drvExhaustedStub ++
      drvErrPrefix ++ drvAbortPrefix ++ drvRetRestoreStub env.tab ++ tail) =
      .ok (env.code, env.labels))
    (st : RV64.State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = T)
    (hsaved : ∀ i (hi : i < callerSaveRegs.length),
      readWord64 st.mem (T + BitVec.ofInt 64 (env.tab.saveBase 0) + BitVec.ofNat 64 (8 * i)) =
        initSt.getReg (callerSaveRegs[i]'hi)) :
    ∃ m r',
      RV64.run env.rom m st = .cont r' ∧
      r'.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64) ∧
      RegsRestored initSt r' ∧
      r'.getReg AbiReg.ra = initSt.getReg AbiReg.ra ∧
      r'.getReg AbiReg.a0 = st.getReg AbiReg.a0 ∧
      r'.getReg AbiReg.a1 = 0#64 ∧
      r'.mem = st.mem := by
  let p0 := pre ++ [Asm.lbl drvDoneLabel]
  have hpc0 : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize p0) := by
    simpa only [p0, lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero] using hpc
  have hl1 : lkm.linkSpec (p0 ++ [Asm.addi AbiReg.a1 AbiReg.zero 0#12] ++
      ([Asm.j retRestoreLabel] ++ drvExhaustedStub ++ drvErrPrefix ++
       drvAbortPrefix ++ drvRetRestoreStub env.tab ++ tail)) =
      .ok (env.code, env.labels) := by
    simpa only [p0, drvDoneStub, List.cons_append, List.nil_append, List.append_assoc] using hlink
  obtain ⟨hr1, hpc1, ha1_1, hoth1, hmem1⟩ :=
    run_aluImm_rd_step env p0 _ .addi AbiReg.a1 AbiReg.zero 0#12 (by decide) hl1 st hpc0
  let s1 := stepReg st AbiReg.a1 (evalAluImm .addi (st.getReg AbiReg.zero) 0#12)
    (BitVec.ofNat 64 (4 * (lkm.totalSize p0 + 1)))
  let p1 := p0 ++ [Asm.addi AbiReg.a1 AbiReg.zero 0#12]
  have hpc1' : s1.pc = BitVec.ofNat 64 (4 * lkm.totalSize p1) := by
    simpa only [p1, lkm.totalSize_append, Asm.addi, lkm.totalSize_instr] using hpc1
  have hl2 : lkm.linkSpec (p1 ++ [Asm.j retRestoreLabel] ++
      (drvExhaustedStub ++ drvErrPrefix ++ drvAbortPrefix ++
       drvRetRestoreStub env.tab ++ tail)) =
      .ok (env.code, env.labels) := by
    simpa only [p1, List.cons_append, List.nil_append, List.append_assoc] using hl1
  let retPre := pre ++ drvDoneStub ++ drvExhaustedStub ++ drvErrPrefix ++ drvAbortPrefix
  have hlinkRetLbl : lkm.linkSpec (retPre ++ [Asm.lbl retRestoreLabel] ++
      (callerRestoreRetAsm AbiReg.gp (env.tab.saveBase 0) ++ tail)) =
      .ok (env.code, env.labels) := by
    simpa only [retPre, drvRetRestoreStub, List.append_assoc] using hlink
  have htgt := linkResolved_lbl_lm lkm retPre retRestoreLabel _ hlinkRetLbl
  have h64J : 4 * (lkm.totalSize p1 + lkm.itemSize (.j retRestoreLabel)) < 2 ^ 64 := by
    simpa [Asm.j, lkm.totalSize_singleton] using
      linkResolved_sub_pc64 env p1 [Asm.j retRestoreLabel] _ hl2
  obtain ⟨kJ, s2, hrunJ, hpc2, hothJ, _, hmemJ⟩ :=
    prog_step_j env p1 _ retRestoreLabel (lkm.totalSize retPre) htgt hl2 h64J s1 hpc1'
  have hlinkRet : lkm.linkSpec (retPre ++ drvRetRestoreStub env.tab ++ tail) =
      .ok (env.code, env.labels) := by
    simpa only [retPre, List.append_assoc] using hlink
  have hgp2 : s2.getReg AbiReg.gp = T :=
    (hothJ _ (by decide)).trans ((hoth1 _ (by decide)).trans hgp)
  have hmem2 : s2.mem = st.mem := hmemJ.trans hmem1
  have hsaved2 : ∀ i (hi : i < callerSaveRegs.length),
      readWord64 s2.mem (T + BitVec.ofInt 64 (env.tab.saveBase 0) + BitVec.ofNat 64 (8 * i)) =
        initSt.getReg (callerSaveRegs[i]'hi) := by
    intro i hi; rw [hmem2]; exact hsaved i hi
  obtain ⟨mR, r', hrunR, hpcR, hrestR, hraR, hothR, hmemR⟩ :=
    checker_retRestore_returns env retPre tail initSt T halign hlinkRet s2 hpc2 hgp2 hsaved2
  have ha0Eq : r'.getReg AbiReg.a0 = st.getReg AbiReg.a0 :=
    (hothR _ (by decide) (by decide) (by decide)).trans
      ((hothJ _ (by decide)).trans (hoth1 _ (by decide)))
  have ha1Eq : r'.getReg AbiReg.a1 = 0#64 := by
    rw [hothR _ (by decide) (by decide) (by decide), hothJ _ (by decide), ha1_1]
    change st.getReg AbiReg.zero + sextImm12 0#12 = 0#64; rw [getReg_zero]; decide
  refine ⟨1 + kJ + mR, r', ?_, hpcR, hrestR, hraR, ha0Eq, ha1Eq, hmemR.trans hmem2⟩
  rw [run_add, run_add, hr1]; dsimp only; rw [hrunJ]; exact hrunR

theorem drvDone_returns (initSt : RV64.State) (T : BitVec 64)
    (halign : isAligned (T + BitVec.ofInt 64 (checkerTabMini.saveBase 0)) 8 = true)
    (st : RV64.State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize (drvPreDone checkerTabMini)))
    (hgp : st.getReg AbiReg.gp = T)
    (hsaved : DrvRegsSaved T initSt st.mem) :
    ∃ m r',
      RV64.run checkerEnv.rom m st = .cont r' ∧
      r'.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64) ∧
      RegsRestored initSt r' ∧
      r'.getReg AbiReg.ra = initSt.getReg AbiReg.ra ∧
      r'.getReg AbiReg.a0 = st.getReg AbiReg.a0 ∧
      r'.getReg AbiReg.a1 = 0#64 ∧
      r'.mem = st.mem := by
  have hlink0 : checkerLM.linkSpec (drvPreDone checkerTabMini ++ drvDoneStub ++ drvExhaustedStub ++
      drvErrPrefix ++ drvAbortPrefix ++ drvRetRestoreStub checkerTabMini ++
      (drvInitSubAsm checkerTabMini ++ checkerCmpDriverAsm checkerTabMini ++ checkerFnsAsm)) =
      .ok (checkerEnv.code, checkerEnv.labels) := by
    simpa only [List.append_assoc] using checkerChipAsm_linkSpec_decomp
  exact checker_done_stub_returns checkerEnv (drvPreDone checkerTabMini) _ initSt T halign hlink0 st hpc hgp hsaved

theorem linkedCmpDrvDone_returns (img : LinkedCmpImage) (initSt : RV64.State) (T : BitVec 64)
    (halign : isAligned (T + BitVec.ofInt 64 (checkerTabMini.saveBase 0)) 8 = true)
    (st : RV64.State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize (drvPreDone checkerTabMini)))
    (hgp : st.getReg AbiReg.gp = T)
    (hsaved : DrvRegsSaved T initSt st.mem) :
    ∃ m r',
      RV64.run (linkedCmpEnv img).rom m st = .cont r' ∧
      r'.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64) ∧
      RegsRestored initSt r' ∧
      r'.getReg AbiReg.ra = initSt.getReg AbiReg.ra ∧
      r'.getReg AbiReg.a0 = st.getReg AbiReg.a0 ∧
      r'.getReg AbiReg.a1 = 0#64 ∧
      r'.mem = st.mem := by
  have hlink0 : img.lkm.linkSpec (drvPreDone checkerTabMini ++ drvDoneStub ++ drvExhaustedStub ++
      drvErrPrefix ++ drvAbortPrefix ++ drvRetRestoreStub checkerTabMini ++
      (drvInitSubAsm checkerTabMini ++ checkerCmpDriverAsm checkerTabMini ++ linkedCmpFnsAsm img)) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels) := by
    simpa only [List.append_assoc] using linkedCmpChipAsm_linkSpec_decomp img
  exact checker_done_stub_returns (linkedCmpEnv img) (drvPreDone checkerTabMini) _ initSt T halign hlink0 st hpc hgp hsaved

private theorem cmpDrvBootCheck_sim_gen {lkm : LinkModel} (env : CodeEnvGen lkm)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec
      (pre ++ cmpDrvPfx ++ drvNeedLi checkerTabMini ++ cmpDrvBootCheck checkerTabMini ++ post) =
      .ok (env.code, env.labels))
    (st0 : RV64.State) (hpc0 : st0.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hRegAlign : isAligned (st0.getReg AbiReg.a4) 8 = true)
    (hReg64 : (st0.getReg AbiReg.a4).toNat + abiNeed checkerTabMini ≤ 2 ^ 64)
    {fuel : Nat} {x : RV64.State}
    (hRetOut : env.rom ((st0.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run env.rom fuel st0 = .cont x)
    (hret : x.pc = (st0.getReg AbiReg.ra &&& ~~~1#64))
    (ha1Out : x.getReg AbiReg.a1 ≠ 1#64) :
    ∃ k st',
      RV64.run env.rom k st0 = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * lkm.totalSize
        (pre ++ cmpDrvPfx ++ drvNeedLi checkerTabMini ++ cmpDrvBootCheck checkerTabMini)) ∧
      st'.getReg AbiReg.s3 = st0.getReg AbiReg.a6 ∧
      st'.getReg AbiReg.s4 = st0.getReg AbiReg.a7 ∧
      st'.getReg AbiReg.gp = st0.getReg AbiReg.a4 ∧
      st'.getReg AbiReg.a0 = st0.getReg AbiReg.a0 ∧
      st'.getReg AbiReg.a1 = st0.getReg AbiReg.a1 ∧
      st'.getReg AbiReg.a2 = st0.getReg AbiReg.a2 ∧
      st'.getReg AbiReg.a3 = st0.getReg AbiReg.a3 ∧
      st'.getReg AbiReg.a4 = st0.getReg AbiReg.a4 ∧
      DrvRegsSaved (st0.getReg AbiReg.a4) st0 st'.mem ∧
      MemEqOutside (callerSaveSpan (st0.getReg AbiReg.a4) (checkerTabMini.saveBase 0))
        st0.mem st'.mem ∧
      abiNeed checkerTabMini ≤ (st0.getReg AbiReg.a5).toNat ∧
      (st0.getReg AbiReg.a1).toNat < 2 ^ 63 ∧
      (st0.getReg AbiReg.a3).toNat < 2 ^ 63 ∧
      (st0.getReg AbiReg.a7).toNat < 2 ^ 63 := by
  let p0 := pre ++ [Asm.lbl cmpStartLabel]
  have hpc0' : st0.pc = BitVec.ofNat 64 (4 * lkm.totalSize p0) := by
    simpa only [p0, lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero] using hpc0
  have hl3 : lkm.linkSpec (p0 ++ drvNeedLi checkerTabMini ++ (cmpDrvBootCheck checkerTabMini ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p0, cmpDrvPfx, List.append_assoc] using hlink
  have hpcLi64 := linkResolved_sub_pc64 env p0 (drvNeedLi checkerTabMini) _ hl3
  obtain ⟨s3, hrun3, hoth3, ht0_3, hm3, hpc3⟩ :=
    li_correct_lm lkm env.hrom p0 _ AbiReg.t0 (by decide)
      (BitVec.ofNat 64 (abiNeed checkerTabMini)) hl3 hpcLi64 st0 hpc0'
  let p3 := p0 ++ drvNeedLi checkerTabMini
  have hpc3' : s3.pc = BitVec.ofNat 64 (4 * lkm.totalSize p3) := by
    simpa only [p3, drvNeedLi, lkm.totalSize_append] using hpc3
  have hs3_eq : ∀ q, q ≠ AbiReg.t0 → s3.getReg q = st0.getReg q := hoth3
  have hneedLt64 : abiNeed checkerTabMini < 2 ^ 64 := by
    rw [checkerTabMini_abiNeed_eq]; simp [abiSlot]
  let b1 := Asm.raw (.branch .bltu AbiReg.a5 AbiReg.t0 (mkBimm 4))
  let b2 := Asm.raw (.branch .blt AbiReg.a1 AbiReg.zero (mkBimm 3))
  let b3 := Asm.raw (.branch .blt AbiReg.a3 AbiReg.zero (mkBimm 2))
  let b4 := Asm.raw (.branch .bge AbiReg.a7 AbiReg.zero (mkBimm 4))
  let d0 := Asm.addi AbiReg.a0 AbiReg.zero 0#12
  let d1 := Asm.addi AbiReg.a1 AbiReg.zero 1#12
  let d2 := Asm.ret
  let tailSv := callerSaveAsm AbiReg.a4 (checkerTabMini.saveBase 0) ++
    [Asm.mv AbiReg.s3 AbiReg.a6, Asm.mv AbiReg.s4 AbiReg.a7, Asm.mv AbiReg.gp AbiReg.a4] ++ post
  have hlB1 : lkm.linkSpec (p3 ++ [b1] ++ ([b2, b3, b4, d0, d1, d2] ++ tailSv)) =
      .ok (env.code, env.labels) := by
    simpa only [p3, cmpDrvBootCheck, b1, b2, b3, b4, d0, d1, d2, tailSv,
      List.cons_append, List.nil_append, List.append_assoc] using hl3
  have hbr1 := run_raw_branch_step env p3 ([b2, b3, b4, d0, d1, d2] ++ tailSv)
    .bltu AbiReg.a5 AbiReg.t0 4 (by decide) hlB1 s3 hpc3'
  have ha5Ge : abiNeed checkerTabMini ≤ (st0.getReg AbiReg.a5).toNat := by
    by_cases hok : abiNeed checkerTabMini ≤ (st0.getReg AbiReg.a5).toNat
    · exact hok
    · exfalso
      have hev : evalBranch .bltu (s3.getReg AbiReg.a5) (s3.getReg AbiReg.t0) = true := by
        rw [hs3_eq _ (by decide), ht0_3]
        simp only [evalBranch, BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hneedLt64]
        omega
      let sd := { s3 with pc := BitVec.ofNat 64 (4 * (lkm.totalSize p3 + 4)) }
      have hrun1 : RV64.run env.rom 1 s3 = .cont sd := by
        simpa only [hev, ↓reduceIte] using hbr1.1
      have hothd : ∀ q, sd.getReg q = s3.getReg q := fun _ => rfl
      have hcont : RV64.run env.rom (lkm.totalSize (drvNeedLi checkerTabMini) + 1) st0 = .cont sd := by
        rw [run_add]; dsimp only [drvNeedLi]; rw [hrun3]; exact hrun1
      let pDecl1 := p3 ++ [b1, b2, b3, b4]
      have hpcd' : sd.pc = BitVec.ofNat 64 (4 * lkm.totalSize pDecl1) := by
        apply congrArg (fun n => BitVec.ofNat 64 (4 * n))
        simp [pDecl1, b1, b2, b3, b4, Asm.raw, lkm.totalSize_append, lkm.totalSize_cons,
          lkm.totalSize_nil, lkm.itemSize_instr]
      have hlDecl1 : lkm.linkSpec (pDecl1 ++ [d0, d1, d2] ++ tailSv) =
          .ok (env.code, env.labels) := by
        simpa only [pDecl1, List.cons_append, List.nil_append, List.append_assoc] using hlB1
      obtain ⟨mR, r', hmR, hpcR, _, ha1R, _, _⟩ :=
        inline_decline_returns env pDecl1 tailSv hlDecl1 sd hpcd'
      have hraEq : sd.getReg AbiReg.ra = st0.getReg AbiReg.ra :=
        (hothd _).trans (hs3_eq _ (by decide))
      rw [hraEq] at hpcR
      exact ret_ne_of_cont hcont hrun hret hRetOut ⟨mR, r', hmR, hpcR, ha1R⟩ ha1Out.symm
  have hev1 : evalBranch .bltu (s3.getReg AbiReg.a5) (s3.getReg AbiReg.t0) = false := by
    rw [hs3_eq _ (by decide), ht0_3]
    simp only [evalBranch, BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hneedLt64]
    omega
  let s4 := { s3 with pc := BitVec.ofNat 64 (4 * (lkm.totalSize p3 + 1)) }
  have hrunB1 : RV64.run env.rom 1 s3 = .cont s4 := by
    simpa only [hev1, Bool.false_eq_true, ↓reduceIte] using hbr1.1
  have hothB1 : ∀ q, s4.getReg q = s3.getReg q := fun _ => rfl
  have hm4 : s4.mem = s3.mem := rfl
  let p4 := p3 ++ [b1]
  have hpc4' : s4.pc = BitVec.ofNat 64 (4 * lkm.totalSize p4) := by
    dsimp only [s4, p4, b1, Asm.raw]
    rw [lkm.totalSize_append p3 _, lkm.totalSize_instr]
  have hrunTo4 : RV64.run env.rom (lkm.totalSize (drvNeedLi checkerTabMini) + 1) st0 = .cont s4 := by
    rw [run_add]; dsimp only [drvNeedLi]; rw [hrun3]; exact hrunB1
  have hlB2 : lkm.linkSpec (p4 ++ [b2] ++ ([b3, b4, d0, d1, d2] ++ tailSv)) =
      .ok (env.code, env.labels) := by
    simpa only [p4, List.cons_append, List.nil_append, List.append_assoc] using hlB1
  have hbr2 := run_raw_branch_step env p4 ([b3, b4, d0, d1, d2] ++ tailSv)
    .blt AbiReg.a1 AbiReg.zero 3 (by decide) hlB2 s4 hpc4'
  have hs4_a1 : s4.getReg AbiReg.a1 = st0.getReg AbiReg.a1 :=
    (hothB1 _).trans (hs3_eq _ (by decide))
  have ha1Lt : (st0.getReg AbiReg.a1).toNat < 2 ^ 63 := by
    by_cases hok : (st0.getReg AbiReg.a1).toNat < 2 ^ 63
    · exact hok
    · exfalso
      have hle : 2 ^ 63 ≤ (st0.getReg AbiReg.a1).toNat := Nat.le_of_not_lt hok
      have hbv : BitVec.ofNat 64 (st0.getReg AbiReg.a1).toNat = st0.getReg AbiReg.a1 :=
        BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (st0.getReg AbiReg.a1).isLt])
      have hev : evalBranch .blt (s4.getReg AbiReg.a1) (s4.getReg AbiReg.zero) = true := by
        have hz : s4.getReg AbiReg.zero = 0#64 := rfl
        rw [hs4_a1, hz]; dsimp only [evalBranch]; rw [← hbv, bitvec_slt_zero_iff _ (st0.getReg AbiReg.a1).isLt]
        simp [hle]
      let sd := { s4 with pc := BitVec.ofNat 64 (4 * (lkm.totalSize p4 + 3)) }
      have hrun2 : RV64.run env.rom 1 s4 = .cont sd := by
        simpa only [hev, ↓reduceIte] using hbr2.1
      have hothd : ∀ q, sd.getReg q = s4.getReg q := fun _ => rfl
      have hcont : RV64.run env.rom ((lkm.totalSize (drvNeedLi checkerTabMini) + 1) + 1) st0 = .cont sd := by
        rw [run_add, hrunTo4]; exact hrun2
      let pDecl2 := p4 ++ [b2, b3, b4]
      have hpcd' : sd.pc = BitVec.ofNat 64 (4 * lkm.totalSize pDecl2) := by
        apply congrArg (fun n => BitVec.ofNat 64 (4 * n))
        simp [pDecl2, b2, b3, b4, Asm.raw, lkm.totalSize_append, lkm.totalSize_cons,
          lkm.totalSize_nil, lkm.itemSize_instr]
      have hlDecl2 : lkm.linkSpec (pDecl2 ++ [d0, d1, d2] ++ tailSv) =
          .ok (env.code, env.labels) := by
        simpa only [pDecl2, List.cons_append, List.nil_append, List.append_assoc] using hlB2
      obtain ⟨mR, r', hmR, hpcR, _, ha1R, _, _⟩ :=
        inline_decline_returns env pDecl2 tailSv hlDecl2 sd hpcd'
      have hraEq : sd.getReg AbiReg.ra = st0.getReg AbiReg.ra :=
        (hothd _).trans ((hothB1 _).trans (hs3_eq _ (by decide)))
      rw [hraEq] at hpcR
      exact ret_ne_of_cont hcont hrun hret hRetOut ⟨mR, r', hmR, hpcR, ha1R⟩ ha1Out.symm
  have hev2 : evalBranch .blt (s4.getReg AbiReg.a1) (s4.getReg AbiReg.zero) = false := by
    have hz : s4.getReg AbiReg.zero = 0#64 := rfl
    have hbv : BitVec.ofNat 64 (st0.getReg AbiReg.a1).toNat = st0.getReg AbiReg.a1 :=
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (st0.getReg AbiReg.a1).isLt])
    rw [hs4_a1, hz]; dsimp only [evalBranch]; rw [← hbv, bitvec_slt_zero_iff _ (st0.getReg AbiReg.a1).isLt]
    simp [ha1Lt]
  let s5 := { s4 with pc := BitVec.ofNat 64 (4 * (lkm.totalSize p4 + 1)) }
  have hrunB2 : RV64.run env.rom 1 s4 = .cont s5 := by
    simpa only [hev2, Bool.false_eq_true, ↓reduceIte] using hbr2.1
  have hothB2 : ∀ q, s5.getReg q = s4.getReg q := fun _ => rfl
  have hm5 : s5.mem = s4.mem := rfl
  let p5 := p4 ++ [b2]
  have hpc5' : s5.pc = BitVec.ofNat 64 (4 * lkm.totalSize p5) := by
    dsimp only [s5, p5, b2, Asm.raw]
    rw [lkm.totalSize_append p4 _, lkm.totalSize_instr]
  have hrunTo5 : RV64.run env.rom ((lkm.totalSize (drvNeedLi checkerTabMini) + 1) + 1) st0 = .cont s5 := by
    rw [run_add, hrunTo4]; exact hrunB2
  have hlB3 : lkm.linkSpec (p5 ++ [b3] ++ ([b4, d0, d1, d2] ++ tailSv)) =
      .ok (env.code, env.labels) := by
    simpa only [p5, List.cons_append, List.nil_append, List.append_assoc] using hlB2
  have hbr3 := run_raw_branch_step env p5 ([b4, d0, d1, d2] ++ tailSv)
    .blt AbiReg.a3 AbiReg.zero 2 (by decide) hlB3 s5 hpc5'
  have hs5_a3 : s5.getReg AbiReg.a3 = st0.getReg AbiReg.a3 :=
    (hothB2 _).trans ((hothB1 _).trans (hs3_eq _ (by decide)))
  have ha3Lt : (st0.getReg AbiReg.a3).toNat < 2 ^ 63 := by
    by_cases hok : (st0.getReg AbiReg.a3).toNat < 2 ^ 63
    · exact hok
    · exfalso
      have hle : 2 ^ 63 ≤ (st0.getReg AbiReg.a3).toNat := Nat.le_of_not_lt hok
      have hbv : BitVec.ofNat 64 (st0.getReg AbiReg.a3).toNat = st0.getReg AbiReg.a3 :=
        BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (st0.getReg AbiReg.a3).isLt])
      have hev : evalBranch .blt (s5.getReg AbiReg.a3) (s5.getReg AbiReg.zero) = true := by
        have hz : s5.getReg AbiReg.zero = 0#64 := rfl
        rw [hs5_a3, hz]; dsimp only [evalBranch]; rw [← hbv, bitvec_slt_zero_iff _ (st0.getReg AbiReg.a3).isLt]
        simp [hle]
      let sd := { s5 with pc := BitVec.ofNat 64 (4 * (lkm.totalSize p5 + 2)) }
      have hrun3' : RV64.run env.rom 1 s5 = .cont sd := by
        simpa only [hev, ↓reduceIte] using hbr3.1
      have hothd : ∀ q, sd.getReg q = s5.getReg q := fun _ => rfl
      have hcont : RV64.run env.rom (((lkm.totalSize (drvNeedLi checkerTabMini) + 1) + 1) + 1) st0 = .cont sd := by
        rw [run_add, hrunTo5]; exact hrun3'
      let pDecl3 := p5 ++ [b3, b4]
      have hpcd' : sd.pc = BitVec.ofNat 64 (4 * lkm.totalSize pDecl3) := by
        apply congrArg (fun n => BitVec.ofNat 64 (4 * n))
        simp [pDecl3, b3, b4, Asm.raw, lkm.totalSize_append, lkm.totalSize_cons,
          lkm.totalSize_nil, lkm.itemSize_instr]
      have hlDecl3 : lkm.linkSpec (pDecl3 ++ [d0, d1, d2] ++ tailSv) =
          .ok (env.code, env.labels) := by
        simpa only [pDecl3, List.cons_append, List.nil_append, List.append_assoc] using hlB3
      obtain ⟨mR, r', hmR, hpcR, _, ha1R, _, _⟩ :=
        inline_decline_returns env pDecl3 tailSv hlDecl3 sd hpcd'
      have hraEq : sd.getReg AbiReg.ra = st0.getReg AbiReg.ra :=
        (hothd _).trans ((hothB2 _).trans ((hothB1 _).trans (hs3_eq _ (by decide))))
      rw [hraEq] at hpcR
      exact ret_ne_of_cont hcont hrun hret hRetOut ⟨mR, r', hmR, hpcR, ha1R⟩ ha1Out.symm
  have hev3 : evalBranch .blt (s5.getReg AbiReg.a3) (s5.getReg AbiReg.zero) = false := by
    have hz : s5.getReg AbiReg.zero = 0#64 := rfl
    have hbv : BitVec.ofNat 64 (st0.getReg AbiReg.a3).toNat = st0.getReg AbiReg.a3 :=
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (st0.getReg AbiReg.a3).isLt])
    rw [hs5_a3, hz]; dsimp only [evalBranch]; rw [← hbv, bitvec_slt_zero_iff _ (st0.getReg AbiReg.a3).isLt]
    simp [ha3Lt]
  let s6 := { s5 with pc := BitVec.ofNat 64 (4 * (lkm.totalSize p5 + 1)) }
  have hrunB3 : RV64.run env.rom 1 s5 = .cont s6 := by
    simpa only [hev3, Bool.false_eq_true, ↓reduceIte] using hbr3.1
  have hothB3 : ∀ q, s6.getReg q = s5.getReg q := fun _ => rfl
  have hm6 : s6.mem = s5.mem := rfl
  let p6 := p5 ++ [b3]
  have hpc6' : s6.pc = BitVec.ofNat 64 (4 * lkm.totalSize p6) := by
    dsimp only [s6, p6, b3, Asm.raw]
    rw [lkm.totalSize_append p5 _, lkm.totalSize_instr]
  have hrunTo6 : RV64.run env.rom (((lkm.totalSize (drvNeedLi checkerTabMini) + 1) + 1) + 1) st0 = .cont s6 := by
    rw [run_add, hrunTo5]; exact hrunB3
  have hlB4 : lkm.linkSpec (p6 ++ [b4] ++ ([d0, d1, d2] ++ tailSv)) =
      .ok (env.code, env.labels) := by
    simpa only [p6, List.cons_append, List.nil_append, List.append_assoc] using hlB3
  have hbr4 := run_raw_branch_step env p6 ([d0, d1, d2] ++ tailSv)
    .bge AbiReg.a7 AbiReg.zero 4 (by decide) hlB4 s6 hpc6'
  have hs6_a7 : s6.getReg AbiReg.a7 = st0.getReg AbiReg.a7 :=
    (hothB3 _).trans ((hothB2 _).trans ((hothB1 _).trans (hs3_eq _ (by decide))))
  have ha7Lt : (st0.getReg AbiReg.a7).toNat < 2 ^ 63 := by
    by_cases hok : (st0.getReg AbiReg.a7).toNat < 2 ^ 63
    · exact hok
    · exfalso
      have hle : 2 ^ 63 ≤ (st0.getReg AbiReg.a7).toNat := Nat.le_of_not_lt hok
      have hbv : BitVec.ofNat 64 (st0.getReg AbiReg.a7).toNat = st0.getReg AbiReg.a7 :=
        BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (st0.getReg AbiReg.a7).isLt])
      have hev : evalBranch .bge (s6.getReg AbiReg.a7) (s6.getReg AbiReg.zero) = false := by
        have hz : s6.getReg AbiReg.zero = 0#64 := rfl
        rw [hs6_a7, hz]; dsimp only [evalBranch]; rw [← hbv, bitvec_slt_zero_iff _ (st0.getReg AbiReg.a7).isLt]
        simp [hle]
      let sd := { s6 with pc := BitVec.ofNat 64 (4 * (lkm.totalSize p6 + 1)) }
      have hrun4' : RV64.run env.rom 1 s6 = .cont sd := by
        simpa only [hev, Bool.false_eq_true, ↓reduceIte] using hbr4.1
      have hothd : ∀ q, sd.getReg q = s6.getReg q := fun _ => rfl
      have hcont : RV64.run env.rom ((((lkm.totalSize (drvNeedLi checkerTabMini) + 1) + 1) + 1) + 1) st0 = .cont sd := by
        rw [run_add, hrunTo6]; exact hrun4'
      let pDecl4 := p6 ++ [b4]
      have hpcd' : sd.pc = BitVec.ofNat 64 (4 * lkm.totalSize pDecl4) := by
        dsimp only [sd, pDecl4, b4, Asm.raw]
        rw [lkm.totalSize_append p6 _, lkm.totalSize_instr]
      have hlDecl4 : lkm.linkSpec (pDecl4 ++ [d0, d1, d2] ++ tailSv) =
          .ok (env.code, env.labels) := by
        simpa only [pDecl4, List.cons_append, List.nil_append, List.append_assoc] using hlB4
      obtain ⟨mR, r', hmR, hpcR, _, ha1R, _, _⟩ :=
        inline_decline_returns env pDecl4 tailSv hlDecl4 sd hpcd'
      have hraEq : sd.getReg AbiReg.ra = st0.getReg AbiReg.ra :=
        (hothd _).trans ((hothB3 _).trans ((hothB2 _).trans
          ((hothB1 _).trans (hs3_eq _ (by decide)))))
      rw [hraEq] at hpcR
      exact ret_ne_of_cont hcont hrun hret hRetOut ⟨mR, r', hmR, hpcR, ha1R⟩ ha1Out.symm
  have hev4 : evalBranch .bge (s6.getReg AbiReg.a7) (s6.getReg AbiReg.zero) = true := by
    have hz : s6.getReg AbiReg.zero = 0#64 := rfl
    have hbv : BitVec.ofNat 64 (st0.getReg AbiReg.a7).toNat = st0.getReg AbiReg.a7 :=
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (st0.getReg AbiReg.a7).isLt])
    rw [hs6_a7, hz]; dsimp only [evalBranch]; rw [← hbv, bitvec_slt_zero_iff _ (st0.getReg AbiReg.a7).isLt]
    simp [ha7Lt]
  let s7 := { s6 with pc := BitVec.ofNat 64 (4 * (lkm.totalSize p6 + 4)) }
  have hrunB4 : RV64.run env.rom 1 s6 = .cont s7 := by
    simpa only [hev4, ↓reduceIte] using hbr4.1
  have hothB4 : ∀ q, s7.getReg q = s6.getReg q := fun _ => rfl
  have hm7 : s7.mem = s6.mem := rfl
  let p7 := p6 ++ [b4, d0, d1, d2]
  have hpc7' : s7.pc = BitVec.ofNat 64 (4 * lkm.totalSize p7) := by
    apply congrArg (fun n => BitVec.ofNat 64 (4 * n))
    simp [p7, b4, d0, d1, d2, Asm.raw, Asm.addi, Asm.ret, lkm.totalSize_append,
      lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
  have hlSv : lkm.linkSpec (p7 ++ callerSaveAsm AbiReg.a4 (checkerTabMini.saveBase 0) ++
      ([Asm.mv AbiReg.s3 AbiReg.a6, Asm.mv AbiReg.s4 AbiReg.a7, Asm.mv AbiReg.gp AbiReg.a4] ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p7, tailSv, List.cons_append, List.nil_append, List.append_assoc] using hlB4
  have hs7_keep : ∀ q, q ≠ AbiReg.t0 → s7.getReg q = st0.getReg q := by
    intro q hqt0
    exact (hothB4 q).trans ((hothB3 q).trans ((hothB2 q).trans ((hothB1 q).trans (hs3_eq q hqt0))))
  have hs7_a4 : s7.getReg AbiReg.a4 = st0.getReg AbiReg.a4 := hs7_keep _ (by decide)
  obtain ⟨kSv, sSv, hrunSv, hpcSv, hothSv, hsavedSv, houtSv⟩ :=
    callerSave_sim env AbiReg.a4 (by decide) (by decide) (checkerTabMini.saveBase 0)
      (st0.getReg AbiReg.a4)
      (checkerTabMini_saveBase_align (st0.getReg AbiReg.a4) hRegAlign)
      (checkerTabMini_saveBase_valid (st0.getReg AbiReg.a4) hReg64)
      p7 ([Asm.mv AbiReg.s3 AbiReg.a6, Asm.mv AbiReg.s4 AbiReg.a7, Asm.mv AbiReg.gp AbiReg.a4] ++ post)
      hlSv s7 hpc7' hs7_a4
  let pSv := p7 ++ callerSaveAsm AbiReg.a4 (checkerTabMini.saveBase 0)
  have hpcSv' : sSv.pc = BitVec.ofNat 64 (4 * lkm.totalSize pSv) := by
    simpa only [pSv, lkm.totalSize_append] using hpcSv
  have hlMv1 : lkm.linkSpec (pSv ++ [Asm.mv AbiReg.s3 AbiReg.a6] ++
      ([Asm.mv AbiReg.s4 AbiReg.a7, Asm.mv AbiReg.gp AbiReg.a4] ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [pSv, List.cons_append, List.nil_append, List.append_assoc] using hlSv
  obtain ⟨hrMv1, hpc8, hs3_8, hoth8, hm8⟩ :=
    run_aluImm_rd_step env pSv _ .addi AbiReg.s3 AbiReg.a6 0#12 (by decide) hlMv1 sSv hpcSv'
  let s8 := stepReg sSv AbiReg.s3 (evalAluImm .addi (sSv.getReg AbiReg.a6) 0#12)
    (BitVec.ofNat 64 (4 * (lkm.totalSize pSv + 1)))
  let p8 := pSv ++ [Asm.mv AbiReg.s3 AbiReg.a6]
  have hpc8' : s8.pc = BitVec.ofNat 64 (4 * lkm.totalSize p8) := by
    simpa only [p8, lkm.totalSize_append, Asm.mv, lkm.totalSize_instr] using hpc8
  have hlMv2 : lkm.linkSpec (p8 ++ [Asm.mv AbiReg.s4 AbiReg.a7] ++
      ([Asm.mv AbiReg.gp AbiReg.a4] ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p8, List.cons_append, List.nil_append, List.append_assoc] using hlMv1
  obtain ⟨hrMv2, hpc9, hs4_9, hoth9, hm9⟩ :=
    run_aluImm_rd_step env p8 _ .addi AbiReg.s4 AbiReg.a7 0#12 (by decide) hlMv2 s8 hpc8'
  let s9 := stepReg s8 AbiReg.s4 (evalAluImm .addi (s8.getReg AbiReg.a7) 0#12)
    (BitVec.ofNat 64 (4 * (lkm.totalSize p8 + 1)))
  let p9 := p8 ++ [Asm.mv AbiReg.s4 AbiReg.a7]
  have hpc9' : s9.pc = BitVec.ofNat 64 (4 * lkm.totalSize p9) := by
    simpa only [p9, lkm.totalSize_append, Asm.mv, lkm.totalSize_instr] using hpc9
  have hlMv3 : lkm.linkSpec (p9 ++ [Asm.mv AbiReg.gp AbiReg.a4] ++ post) =
      .ok (env.code, env.labels) := by
    simpa only [p9, List.cons_append, List.nil_append, List.append_assoc] using hlMv2
  obtain ⟨hrMv3, hpc10, hgp_10, hoth10, hm10⟩ :=
    run_aluImm_rd_step env p9 _ .addi AbiReg.gp AbiReg.a4 0#12 (by decide) hlMv3 s9 hpc9'
  let s10 := stepReg s9 AbiReg.gp (evalAluImm .addi (s9.getReg AbiReg.a4) 0#12)
    (BitVec.ofNat 64 (4 * (lkm.totalSize p9 + 1)))
  have hz12 : sextImm12 0#12 = 0#64 := rfl
  have hs3Eq : s10.getReg AbiReg.s3 = st0.getReg AbiReg.a6 := by
    rw [hoth10 _ (by decide), hoth9 _ (by decide), hs3_8]
    change sSv.getReg AbiReg.a6 + sextImm12 0#12 = st0.getReg AbiReg.a6
    rw [hz12, BitVec.add_zero, hothSv _ (by decide) (by decide), hs7_keep _ (by decide)]
  have hs4Eq : s10.getReg AbiReg.s4 = st0.getReg AbiReg.a7 := by
    rw [hoth10 _ (by decide), hs4_9]
    change s8.getReg AbiReg.a7 + sextImm12 0#12 = st0.getReg AbiReg.a7
    rw [hz12, BitVec.add_zero, hoth8 _ (by decide), hothSv _ (by decide) (by decide),
      hs7_keep _ (by decide)]
  have hgpEq : s10.getReg AbiReg.gp = st0.getReg AbiReg.a4 := by
    rw [hgp_10]
    change s9.getReg AbiReg.a4 + sextImm12 0#12 = st0.getReg AbiReg.a4
    rw [hz12, BitVec.add_zero, hoth9 _ (by decide), hoth8 _ (by decide),
      hothSv _ (by decide) (by decide), hs7_a4]
  have hs10_keep : ∀ q, q = AbiReg.a0 ∨ q = AbiReg.a1 ∨ q = AbiReg.a2 ∨
      q = AbiReg.a3 ∨ q = AbiReg.a4 → s10.getReg q = st0.getReg q := by
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;>
      exact (hoth10 _ (by decide)).trans ((hoth9 _ (by decide)).trans ((hoth8 _ (by decide)).trans
        ((hothSv _ (by decide) (by decide)).trans (hs7_keep _ (by decide)))))
  have hpc10' : s10.pc = BitVec.ofNat 64 (4 * lkm.totalSize
      (pre ++ cmpDrvPfx ++ drvNeedLi checkerTabMini ++ cmpDrvBootCheck checkerTabMini)) := by
    have hpEq : p9 ++ [Asm.mv AbiReg.gp AbiReg.a4] =
        pre ++ cmpDrvPfx ++ drvNeedLi checkerTabMini ++ cmpDrvBootCheck checkerTabMini := by
      dsimp only [p9, p8, pSv, p7, p6, p5, p4, p3, p0, cmpDrvPfx, cmpDrvBootCheck,
        b1, b2, b3, b4, d0, d1, d2]
      simp only [List.cons_append, List.nil_append, List.append_assoc]
    have hsz : lkm.totalSize (p9 ++ [Asm.mv AbiReg.gp AbiReg.a4]) =
        lkm.totalSize p9 + 1 := by
      rw [lkm.totalSize_append]
      simp [Asm.mv, lkm.totalSize_instr]
    rw [hpc10, ← hsz, hpEq]
  have hm70 : s7.mem = st0.mem := by rw [hm7, hm6, hm5, hm4, hm3]
  have hsaved : DrvRegsSaved (st0.getReg AbiReg.a4) st0 s10.mem := by
    intro i hi
    rw [hm10, hm9, hm8, hsavedSv i hi]
    have hnot : ∀ r ∈ callerSaveRegs, r ≠ AbiReg.t0 := by decide
    exact hs7_keep _ (hnot (callerSaveRegs[i]'hi) (List.getElem_mem hi))
  have hout : MemEqOutside (callerSaveSpan (st0.getReg AbiReg.a4) (checkerTabMini.saveBase 0))
      st0.mem s10.mem := by
    rw [hm10, hm9, hm8, ← hm70]; exact houtSv
  refine ⟨((((lkm.totalSize (drvNeedLi checkerTabMini) + 1) + 1) + 1) + 1) + kSv + 1 + 1 + 1,
    s10, ?_, hpc10',
    hs3Eq, hs4Eq, hgpEq,
    hs10_keep _ (Or.inl rfl),
    hs10_keep _ (Or.inr (Or.inl rfl)),
    hs10_keep _ (Or.inr (Or.inr (Or.inl rfl))),
    hs10_keep _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
    hs10_keep _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))),
    hsaved, hout, ha5Ge, ha1Lt, ha3Lt, ha7Lt⟩
  · rw [run_add, run_add, run_add, run_add, run_add, hrunTo6]; dsimp only
    rw [hrunB4]; dsimp only; rw [hrunSv]; dsimp only; rw [hrMv1]; dsimp only; rw [hrMv2]; exact hrMv3

theorem cmpDrvBootCheck_sim
    (pre post : List AsmItem)
    (hlink : checkerLM.linkSpec
      (pre ++ cmpDrvPfx ++ drvNeedLi checkerTabMini ++ cmpDrvBootCheck checkerTabMini ++ post) =
      .ok (checkerEnv.code, checkerEnv.labels))
    (st0 : RV64.State) (hpc0 : st0.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize pre))
    (hRegAlign : isAligned (st0.getReg AbiReg.a4) 8 = true)
    (hReg64 : (st0.getReg AbiReg.a4).toNat + abiNeed checkerTabMini ≤ 2 ^ 64)
    {fuel : Nat} {x : RV64.State}
    (hRetOut : checkerEnv.rom ((st0.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run checkerEnv.rom fuel st0 = .cont x)
    (hret : x.pc = (st0.getReg AbiReg.ra &&& ~~~1#64))
    (ha1Out : x.getReg AbiReg.a1 ≠ 1#64) :
    ∃ k st',
      RV64.run checkerEnv.rom k st0 = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize
        (pre ++ cmpDrvPfx ++ drvNeedLi checkerTabMini ++ cmpDrvBootCheck checkerTabMini)) ∧
      st'.getReg AbiReg.s3 = st0.getReg AbiReg.a6 ∧
      st'.getReg AbiReg.s4 = st0.getReg AbiReg.a7 ∧
      st'.getReg AbiReg.gp = st0.getReg AbiReg.a4 ∧
      st'.getReg AbiReg.a0 = st0.getReg AbiReg.a0 ∧
      st'.getReg AbiReg.a1 = st0.getReg AbiReg.a1 ∧
      st'.getReg AbiReg.a2 = st0.getReg AbiReg.a2 ∧
      st'.getReg AbiReg.a3 = st0.getReg AbiReg.a3 ∧
      st'.getReg AbiReg.a4 = st0.getReg AbiReg.a4 ∧
      DrvRegsSaved (st0.getReg AbiReg.a4) st0 st'.mem ∧
      MemEqOutside (callerSaveSpan (st0.getReg AbiReg.a4) (checkerTabMini.saveBase 0))
        st0.mem st'.mem ∧
      abiNeed checkerTabMini ≤ (st0.getReg AbiReg.a5).toNat ∧
      (st0.getReg AbiReg.a1).toNat < 2 ^ 63 ∧
      (st0.getReg AbiReg.a3).toNat < 2 ^ 63 ∧
      (st0.getReg AbiReg.a7).toNat < 2 ^ 63 :=
  cmpDrvBootCheck_sim_gen checkerEnv pre post hlink st0 hpc0 hRegAlign hReg64 hRetOut hrun hret ha1Out

theorem linkedCmpDrvBootCheck_sim (img : LinkedCmpImage)
    (pre post : List AsmItem)
    (hlink : img.lkm.linkSpec
      (pre ++ cmpDrvPfx ++ drvNeedLi checkerTabMini ++ cmpDrvBootCheck checkerTabMini ++ post) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels))
    (st0 : RV64.State) (hpc0 : st0.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize pre))
    (hRegAlign : isAligned (st0.getReg AbiReg.a4) 8 = true)
    (hReg64 : (st0.getReg AbiReg.a4).toNat + abiNeed checkerTabMini ≤ 2 ^ 64)
    {fuel : Nat} {x : RV64.State}
    (hRetOut : (linkedCmpEnv img).rom ((st0.getReg AbiReg.ra &&& ~~~1#64).toNat / 4) = none)
    (hrun : RV64.run (linkedCmpEnv img).rom fuel st0 = .cont x)
    (hret : x.pc = (st0.getReg AbiReg.ra &&& ~~~1#64))
    (ha1Out : x.getReg AbiReg.a1 ≠ 1#64) :
    ∃ k st',
      RV64.run (linkedCmpEnv img).rom k st0 = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize
        (pre ++ cmpDrvPfx ++ drvNeedLi checkerTabMini ++ cmpDrvBootCheck checkerTabMini)) ∧
      st'.getReg AbiReg.s3 = st0.getReg AbiReg.a6 ∧
      st'.getReg AbiReg.s4 = st0.getReg AbiReg.a7 ∧
      st'.getReg AbiReg.gp = st0.getReg AbiReg.a4 ∧
      st'.getReg AbiReg.a0 = st0.getReg AbiReg.a0 ∧
      st'.getReg AbiReg.a1 = st0.getReg AbiReg.a1 ∧
      st'.getReg AbiReg.a2 = st0.getReg AbiReg.a2 ∧
      st'.getReg AbiReg.a3 = st0.getReg AbiReg.a3 ∧
      st'.getReg AbiReg.a4 = st0.getReg AbiReg.a4 ∧
      DrvRegsSaved (st0.getReg AbiReg.a4) st0 st'.mem ∧
      MemEqOutside (callerSaveSpan (st0.getReg AbiReg.a4) (checkerTabMini.saveBase 0))
        st0.mem st'.mem ∧
      abiNeed checkerTabMini ≤ (st0.getReg AbiReg.a5).toNat ∧
      (st0.getReg AbiReg.a1).toNat < 2 ^ 63 ∧
      (st0.getReg AbiReg.a3).toNat < 2 ^ 63 ∧
      (st0.getReg AbiReg.a7).toNat < 2 ^ 63 :=
  cmpDrvBootCheck_sim_gen (linkedCmpEnv img) pre post hlink st0 hpc0 hRegAlign hReg64 hRetOut hrun hret ha1Out

private theorem cmpDrvCallPrep_sim_gen {lkm : LinkModel} (env : CodeEnvGen lkm)
    (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ cmpDrvCallPrep checkerTabMini ++ post) =
      .ok (env.code, env.labels))
    (hExLblEq : lookupLabel env.labels exhaustedLabel =
      some env.exhaustedTarget)
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre +
        lkm.totalSize (cmpDrvCallPrep checkerTabMini))) ∧
      st'.mem = st.mem ∧
      st'.getReg AbiReg.gp = regionBase ∧
      st'.getReg AbiReg.sp = readWord64 st.mem regionBase ∧
      st'.getReg AbiReg.s0 = BitVec.ofNat 64 (abiFuel - 2) ∧
      st'.getReg AbiReg.t0 = regionBase + BitVec.ofInt 64 checkerTabMini.args ∧
      st'.getReg AbiReg.t1 = 0#64 ∧
      (∀ q, q ≠ AbiReg.s0 → q ≠ AbiReg.sp → q ≠ AbiReg.t0 → q ≠ AbiReg.t1 →
        q ≠ AbiReg.t2 → q ≠ AbiReg.t6 → q ≠ AbiReg.s1 → st'.getReg q = st.getReg q) := by
  let cFuel := li AbiReg.s0 (BitVec.ofNat 64 (abiFuel - 1))
  let cLd := [Asm.ld AbiReg.sp AbiReg.gp 0#12]
  let cBeq := [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel]
  let cDec := [Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)]
  let cArgs := addImmOff AbiReg.t0 AbiReg.gp AbiReg.t2 checkerTabMini.args
  let cT1 := li AbiReg.t1 0#64
  have hl1 : lkm.linkSpec (pre ++ cFuel ++ (cLd ++ cBeq ++ cDec ++ cArgs ++ cT1 ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [cmpDrvCallPrep, cFuel, cLd, cBeq, cDec, cArgs, cT1,
      List.cons_append, List.nil_append, List.append_assoc] using hlink
  have hpc1_64 := linkResolved_sub_pc64 env pre cFuel _ hl1
  obtain ⟨s1, hrun1, hoth1, ht1, hm1, hpc1⟩ :=
    li_correct_lm lkm env.hrom pre _ AbiReg.s0 (by decide)
      (BitVec.ofNat 64 (abiFuel - 1)) hl1 hpc1_64 st hpc
  let p1 := pre ++ cFuel
  have hpc1' : s1.pc = BitVec.ofNat 64 (4 * lkm.totalSize p1) := by
    simpa only [p1, lkm.totalSize_append] using hpc1
  have hs1gp : s1.getReg AbiReg.gp = regionBase := (hoth1 _ (by decide)).trans hgp
  have hl2 : lkm.linkSpec (p1 ++ [Asm.ld AbiReg.sp AbiReg.gp 0#12] ++
      (cBeq ++ cDec ++ cArgs ++ cT1 ++ post)) = .ok (env.code, env.labels) := by
    simpa only [p1, cLd, List.append_assoc] using hl1
  have hpc2_64 := linkResolved_sub_pc64 env p1 [Asm.ld AbiReg.sp AbiReg.gp 0#12] _ hl2
  have hlt2_64 : 4 * (lkm.totalSize p1 + 1) < 2 ^ 64 := by
    simpa only [Asm.ld, Asm.raw, lkm.totalSize_instr] using hpc2_64
  have hal2 : isAligned (s1.getReg AbiReg.gp + sextImm12 0#12) 8 = true := by
    have hz : sextImm12 0#12 = 0#64 := rfl; rw [hs1gp, hz, BitVec.add_zero]; exact hRegAlign
  obtain ⟨hrun2, hpc2, hsp2, hoth2, hm2⟩ :=
    step_ld_off env p1 _ AbiReg.sp AbiReg.gp 0#12 (by decide) hl2 hlt2_64 s1 hpc1' hal2
  let s2 := stepReg s1 AbiReg.sp (readWord64 s1.mem (s1.getReg AbiReg.gp + sextImm12 0#12)) (s1.pc + 4#64)
  let p2 := p1 ++ cLd
  have hpc2' : s2.pc = BitVec.ofNat 64 (4 * lkm.totalSize p2) := by
    simpa only [p2, cLd, lkm.totalSize_append, Asm.ld, Asm.raw, lkm.totalSize_instr] using hpc2
  have hs2gp : s2.getReg AbiReg.gp = regionBase := (hoth2 _ (by decide)).trans hs1gp
  have hs2s0 : s2.getReg AbiReg.s0 = BitVec.ofNat 64 (abiFuel - 1) := (hoth2 _ (by decide)).trans ht1
  have hs2sp : s2.getReg AbiReg.sp = readWord64 st.mem regionBase := by
    have hz : sextImm12 0#12 = 0#64 := rfl
    rw [hsp2, hs1gp, hz, BitVec.add_zero, hm1]
  have hl3 : lkm.linkSpec (p2 ++ [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel] ++
      (cDec ++ cArgs ++ cT1 ++ post)) = .ok (env.code, env.labels) := by
    simpa only [p2, cBeq, List.append_assoc] using hl2
  have hbr := run_br_step env p2 _ .beq AbiReg.s0 AbiReg.zero exhaustedLabel
    env.exhaustedTarget hExLblEq (by decide) hl3 s2 hpc2'
  have hev : evalBranch .beq (s2.getReg AbiReg.s0) (s2.getReg AbiReg.zero) = false := by
    have hz : s2.getReg AbiReg.zero = 0#64 := rfl
    rw [hs2s0, hz]; decide
  rw [hev] at hbr
  obtain ⟨k3, s3, _, hrun3, hpc3, hoth3, _, hm3⟩ := hbr
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc3
  let p3 := p2 ++ cBeq
  have hpc3' : s3.pc = BitVec.ofNat 64 (4 * lkm.totalSize p3) := by
    rw [hpc3]; dsimp only [p3, cBeq]
    rw [lkm.totalSize_append p2 [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel]]
    rfl
  have hl4 : lkm.linkSpec (p3 ++ [Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++
      (cArgs ++ cT1 ++ post)) = .ok (env.code, env.labels) := by
    simpa only [p3, cDec, List.append_assoc] using hl3
  obtain ⟨hrun4, hpc4, hs0_4, hoth4, hm4⟩ :=
    run_aluImm_rd_step env p3 _ .addi AbiReg.s0 AbiReg.s0 (-1#12) (by decide) hl4 s3 hpc3'
  let s4 := stepReg s3 AbiReg.s0 (evalAluImm .addi (s3.getReg AbiReg.s0) (-1#12))
    (BitVec.ofNat 64 (4 * (lkm.totalSize p3 + 1)))
  let p4 := p3 ++ cDec
  have hpc4' : s4.pc = BitVec.ofNat 64 (4 * lkm.totalSize p4) := by
    simpa only [p4, cDec, lkm.totalSize_append, Asm.addi, lkm.totalSize_instr] using hpc4
  have hl5 : lkm.linkSpec (p4 ++ cArgs ++ (cT1 ++ post)) =
      .ok (env.code, env.labels) := by
    simpa only [p4, List.append_assoc] using hl4
  have hpc5_64 := linkResolved_sub_pc64 env p4 cArgs _ hl5
  obtain ⟨s5, hrun5, hoth5, ht0_5, hm5, hpc5⟩ :=
    addImmOff_correct_lm lkm env.hrom p4 _ AbiReg.t0 AbiReg.gp AbiReg.t2
      (by decide) (by decide) (by decide) checkerTabMini.args hl5 hpc5_64 s4 hpc4'
  let p5 := p4 ++ cArgs
  have hpc5' : s5.pc = BitVec.ofNat 64 (4 * lkm.totalSize p5) := by
    simpa only [p5, lkm.totalSize_append] using hpc5
  have hl6 : lkm.linkSpec (p5 ++ cT1 ++ post) =
      .ok (env.code, env.labels) := by
    simpa only [p5, List.append_assoc] using hl5
  have hpc6_64 := linkResolved_sub_pc64 env p5 cT1 _ hl6
  obtain ⟨s6, hrun6, hoth6, ht1_6, hm6, hpc6⟩ :=
    li_correct_lm lkm env.hrom p5 _ AbiReg.t1 (by decide) 0#64 hl6 hpc6_64 s5 hpc5'
  have hs4gp : s4.getReg AbiReg.gp = regionBase :=
    (hoth4 _ (by decide)).trans ((hoth3 _ (by decide)).trans hs2gp)
  have hs4sp : s4.getReg AbiReg.sp = readWord64 st.mem regionBase :=
    (hoth4 _ (by decide)).trans ((hoth3 _ (by decide)).trans hs2sp)
  have hs4s0 : s4.getReg AbiReg.s0 = BitVec.ofNat 64 (abiFuel - 2) := by
    rw [hs0_4]; change s3.getReg AbiReg.s0 + sextImm12 (-1#12) = _
    rw [hoth3 _ (by decide), hs2s0]; decide
  refine ⟨lkm.totalSize cFuel + 1 + k3 + 1 + lkm.totalSize cArgs + lkm.totalSize cT1, s6,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ht1_6, ?_⟩
  · rw [run_add, run_add, run_add, run_add, run_add, hrun1]; dsimp only
    rw [hrun2]; dsimp only; rw [hrun3]; dsimp only; rw [hrun4]; dsimp only; rw [hrun5]; exact hrun6
  · rw [hpc6]
    refine congrArg (fun n => BitVec.ofNat 64 (4 * n)) ?_
    dsimp only [p5, p4, p3, p2, p1, cmpDrvCallPrep, cFuel, cLd, cBeq, cDec, cArgs, cT1]
    simp only [lkm.totalSize_append, lkm.totalSize_cons, lkm.totalSize_nil,
      Asm.ld, Asm.beq, Asm.addi, lkm.itemSize_instr,
      Nat.add_zero, Nat.add_assoc]
  · exact hm6.trans (hm5.trans (hm4.trans (hm3.trans (hm2.trans hm1))))
  · exact (hoth6 _ (by decide)).trans ((hoth5 _ (by decide) (by decide)).trans hs4gp)
  · exact (hoth6 _ (by decide)).trans ((hoth5 _ (by decide) (by decide)).trans hs4sp)
  · exact (hoth6 _ (by decide)).trans ((hoth5 _ (by decide) (by decide)).trans hs4s0)
  · rw [hoth6 _ (by decide), ht0_5, hs4gp]
  · intro q hqs0 hqsp hqt0 hqt1 hqt2 hqt6 hqs1
    exact (hoth6 q hqt1).trans ((hoth5 q hqt0 hqt2).trans ((hoth4 q hqs0).trans
      ((hoth3 q ⟨hqt6, hqs1⟩).trans ((hoth2 q hqsp).trans (hoth1 q hqs0)))))

theorem cmpDrvCallPrep_sim (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (pre post : List AsmItem)
    (hlink : checkerLM.linkSpec (pre ++ cmpDrvCallPrep checkerTabMini ++ post) =
      .ok (checkerEnv.code, checkerEnv.labels))
    (hExLblEq : lookupLabel checkerEnv.labels exhaustedLabel =
      some checkerEnv.exhaustedTarget)
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * checkerLM.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase) :
    ∃ k st',
      RV64.run checkerEnv.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (checkerLM.totalSize pre +
        checkerLM.totalSize (cmpDrvCallPrep checkerTabMini))) ∧
      st'.mem = st.mem ∧
      st'.getReg AbiReg.gp = regionBase ∧
      st'.getReg AbiReg.sp = readWord64 st.mem regionBase ∧
      st'.getReg AbiReg.s0 = BitVec.ofNat 64 (abiFuel - 2) ∧
      st'.getReg AbiReg.t0 = regionBase + BitVec.ofInt 64 checkerTabMini.args ∧
      st'.getReg AbiReg.t1 = 0#64 ∧
      (∀ q, q ≠ AbiReg.s0 → q ≠ AbiReg.sp → q ≠ AbiReg.t0 → q ≠ AbiReg.t1 →
        q ≠ AbiReg.t2 → q ≠ AbiReg.t6 → q ≠ AbiReg.s1 → st'.getReg q = st.getReg q) :=
  cmpDrvCallPrep_sim_gen checkerEnv regionBase hRegAlign pre post hlink hExLblEq st hpc hgp

theorem linkedCmpDrvCallPrep_sim (img : LinkedCmpImage) (regionBase : BitVec 64)
    (hRegAlign : isAligned regionBase 8 = true)
    (pre post : List AsmItem)
    (hlink : img.lkm.linkSpec (pre ++ cmpDrvCallPrep checkerTabMini ++ post) =
      .ok ((linkedCmpEnv img).code, (linkedCmpEnv img).labels))
    (hExLblEq : lookupLabel (linkedCmpEnv img).labels exhaustedLabel =
      some (linkedCmpEnv img).exhaustedTarget)
    (st : RV64.State) (hpc : st.pc = BitVec.ofNat 64 (4 * img.lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = regionBase) :
    ∃ k st',
      RV64.run (linkedCmpEnv img).rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (img.lkm.totalSize pre +
        img.lkm.totalSize (cmpDrvCallPrep checkerTabMini))) ∧
      st'.mem = st.mem ∧
      st'.getReg AbiReg.gp = regionBase ∧
      st'.getReg AbiReg.sp = readWord64 st.mem regionBase ∧
      st'.getReg AbiReg.s0 = BitVec.ofNat 64 (abiFuel - 2) ∧
      st'.getReg AbiReg.t0 = regionBase + BitVec.ofInt 64 checkerTabMini.args ∧
      st'.getReg AbiReg.t1 = 0#64 ∧
      (∀ q, q ≠ AbiReg.s0 → q ≠ AbiReg.sp → q ≠ AbiReg.t0 → q ≠ AbiReg.t1 →
        q ≠ AbiReg.t2 → q ≠ AbiReg.t6 → q ≠ AbiReg.s1 → st'.getReg q = st.getReg q) :=
  cmpDrvCallPrep_sim_gen (linkedCmpEnv img) regionBase hRegAlign pre post hlink hExLblEq st hpc hgp

end ConAgua.RISCV.Bridge


