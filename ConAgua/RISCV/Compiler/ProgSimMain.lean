import ConAgua.RISCV.Compiler.ProgSimFn
import ConAgua.RISCV.Compiler.ProgSimCallerSave

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Program-Level Forward Simulation: Control Flow, Functions & Trampoline (`ConAgua.RISCV.Compiler.ProgSimMain`)

Trampoline simulation (`compileTrampoline`), full-program theorem (`compileProg_sim`),
`_root_.L.run` corollary (`prog_run_sim`), and `#guard_msgs` axiom checks.
Re-exports `ProgSimFrame`, `ProgSimCall`, `ProgSimFn`, and `ProgSimCallerSave`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard Lean axioms only.
-/

namespace ConAgua.RISCV.Compiler

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Linker

/-! ## 5. Trampoline (`compileTrampoline`), Full-Program (`compileProg_sim`) & `_root_.L.run` Corollary (`prog_run_sim`) -/

def ProgTrampLinkedGen {lkm : LinkModel} (env : CodeEnvGen lkm) (entry : FnName) (entryNparams : Nat) : Prop :=
  ∃ preT postT,
    lkm.linkSpec (preT ++ compileTrampoline env.tab entry entryNparams ++ postT) =
      .ok (env.code, env.labels)

def ProgTrampLinked (env : CodeEnv) (entry : FnName) (entryNparams : Nat) : Prop :=
  ProgTrampLinkedGen env.toGen entry entryNparams

private theorem Tab.args_eq_nat (tab : Tab) :
    tab.args = ((8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres + tab.ng) : Nat) : Int) := by
  simp only [Tab.args, Tab.globBase, Tab.resBase, Tab.romBase]
  omega

private theorem trampLoadArgs_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (vs : List _root_.L.Word) (entryNparams : Nat) :
    ∀ (n : Nat), n ≤ min entryNparams maxRes →
      ∀ (pre post : List AsmItem),
        lkm.linkSpec (pre ++ ((List.range n).flatMap fun i =>
          loadMemOff .ld (resReg i) AbiReg.gp AbiReg.t2 (env.tab.args + 8 * Int.ofNat i)) ++ post) =
          .ok (env.code, env.labels) →
      ∀ (st : State),
        st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
        st.getReg AbiReg.gp = L.T →
        (∀ j, j < entryNparams →
          readWord64 st.mem (L.T + BitVec.ofInt 64 env.tab.args + BitVec.ofNat 64 (8 * j)) = (vs.getD j 0).toBitVec) →
        ∃ k st',
          RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize ((List.range n).flatMap fun i =>
            loadMemOff .ld (resReg i) AbiReg.gp AbiReg.t2 (env.tab.args + 8 * Int.ofNat i)))) ∧
          PreservedRegs st st' ∧
          st'.mem = st.mem ∧
          (∀ j, j < n → st'.getReg (resReg j) = (vs.getD j 0).toBitVec) := by
  intro n
  induction n with
  | zero =>
    intro _ pre post _ st hpc _ _
    exact ⟨0, st, rfl, by simp [lkm.totalSize_nil, hpc], PreservedRegs.refl st, rfl,
      fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro hle pre post hlink st hpc hgp hargs
    have hsplit : (List.range (n + 1)).flatMap (fun i =>
          loadMemOff .ld (resReg i) AbiReg.gp AbiReg.t2 (env.tab.args + 8 * Int.ofNat i)) =
        (List.range n).flatMap (fun i =>
          loadMemOff .ld (resReg i) AbiReg.gp AbiReg.t2 (env.tab.args + 8 * Int.ofNat i)) ++
        loadMemOff .ld (resReg n) AbiReg.gp AbiReg.t2 (env.tab.args + 8 * Int.ofNat n) := by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rw [hsplit] at hlink ⊢
    have ⟨hl1, hl2⟩ := linkResolved_mid_split lkm pre _ _ post hlink
    obtain ⟨k1, st1, hrun1, hpc1, hpres1, hmem1, hregs1⟩ := ih (by omega) pre _ hl1 st hpc hgp hargs
    have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.gp.trans hgp
    have hoffEq : BitVec.ofInt 64 (env.tab.args + 8 * Int.ofNat n) =
        BitVec.ofInt 64 env.tab.args + BitVec.ofNat 64 (8 * n) := by
      have hcast : BitVec.ofInt 64 (8 * Int.ofNat n) = BitVec.ofNat 64 (8 * n) := by
        change BitVec.ofInt 64 (8 * (n : Int)) = BitVec.ofNat 64 (8 * n)
        rw [show (8 : Int) * (n : Int) = ((8 * n : Nat) : Int) from by omega, BitVec.ofInt_natCast]
      rw [BitVec.ofInt_add, hcast]
    have halN : isAligned (st1.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.args + 8 * Int.ofNat n)) 8 = true := by
      rw [hgp1, hoffEq, ← BitVec.add_assoc, Tab.args_eq_nat]
      exact isAligned8_add_mul8 _ (isAligned8_add_int_mul8 L.T L.hTAlign _) n
    have hrn := resReg_ne_preserved n
    obtain ⟨st2, hrun2, hoth2, hrd2, hmem2, hpc2⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom (pre ++ _) post (resReg n) AbiReg.gp AbiReg.t2
        (resReg_ne_zero n) (by decide) (by decide) (env.tab.args + 8 * Int.ofNat n) hl2
        (linkResolved_sub_pc64 env _ _ post hl2) st1 (by simpa [lkm.totalSize_append] using hpc1) halN
    have hpres2 : PreservedRegs st1 st2 :=
      ⟨hoth2 _ hrn.1.symm (by decide), hoth2 _ hrn.2.1.symm (by decide),
       hoth2 _ hrn.2.2.1.symm (by decide),
       hoth2 _ hrn.2.2.2.2.1.symm (by decide)⟩
    refine ⟨_, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
      by simpa [lkm.totalSize_append, Nat.add_assoc] using hpc2,
      hpres1.trans hpres2, hmem2.trans hmem1, ?_⟩
    intro j hj
    by_cases hjn : j = n
    · subst hjn
      rw [hrd2, hmem1, hgp1, hoffEq, ← BitVec.add_assoc]
      exact hargs j (by omega)
    · rw [hoth2 (resReg j) (resReg_ne_of_lt (by omega) (by omega) hjn) (resReg_ne_preserved j).2.2.2.2.2.2.2,
        hregs1 j (by omega)]


private theorem compileTrampoline_exhausted_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (entry : FnName) (entryNparams : Nat)
    (hTramp : ProgTrampLinkedGen env entry entryNparams)
    (T : BitVec 64) (halign : isAligned (T + BitVec.ofInt 64 (env.tab.saveBase entryNparams)) 8 = true)
    (initSt st : State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * env.exhaustedTarget))
    (hgp : st.getReg AbiReg.gp = T)
    (hsaved : ∀ i (hi : i < callerSaveRegs.length),
      readWord64 st.mem ((T + BitVec.ofInt 64 (env.tab.saveBase entryNparams)) + BitVec.ofNat 64 (8 * i)) =
        initSt.getReg (callerSaveRegs[i]'hi)) :
    ∃ k r',
      RV64.run env.rom k st = .cont r' ∧
      r'.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64) ∧
      r'.getReg AbiReg.a0 = 0#64 ∧
      r'.getReg AbiReg.a1 = 1#64 ∧
      RegsRestored initSt r' ∧
      r'.getReg AbiReg.ra = initSt.getReg AbiReg.ra ∧
      r'.mem = st.mem := by
  obtain ⟨preT, postT, hlink⟩ := hTramp
  let trHead :=
    [Asm.lbl enterLabel] ++
    callerSaveAsm AbiReg.a0 (env.tab.saveBase entryNparams) ++
    [Asm.mv AbiReg.s1 AbiReg.sp, Asm.mv AbiReg.s2 AbiReg.ra,
     Asm.mv AbiReg.gp AbiReg.a0, Asm.mv AbiReg.s0 AbiReg.a1, Asm.ld AbiReg.sp AbiReg.gp 0#12,
     Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel, Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++
    ((List.range (min entryNparams maxRes)).flatMap fun i =>
      loadMemOff .ld (resReg i) AbiReg.gp AbiReg.t2 (env.tab.args + 8 * Int.ofNat i)) ++
    addImmOff AbiReg.t0 AbiReg.gp AbiReg.t2
      (env.tab.args + 8 * Int.ofNat (if maxRes < entryNparams then maxRes else 0)) ++
    li AbiReg.t1 (BitVec.ofNat 64 entryNparams) ++
    [Asm.call (fnLabel entry), Asm.addi AbiReg.a1 AbiReg.zero 0#12, Asm.j retRestoreLabel]
  let trExh :=
    [Asm.lbl exhaustedLabel, Asm.addi AbiReg.a0 AbiReg.zero 0#12,
     Asm.addi AbiReg.a1 AbiReg.zero 1#12, Asm.j retRestoreLabel]
  let trMid :=
    [Asm.lbl errLabel, Asm.addi AbiReg.a0 AbiReg.zero 0#12,
     Asm.lbl abortLabel, Asm.addi AbiReg.a1 AbiReg.zero 2#12]
  let trTail := [Asm.lbl retRestoreLabel] ++ callerRestoreRetAsm AbiReg.gp (env.tab.saveBase entryNparams)
  have hExLbl : lookupLabel env.labels exhaustedLabel = some (lkm.totalSize (preT ++ trHead)) :=
    linkResolved_lbl_lm lkm (preT ++ trHead) exhaustedLabel _
      (by simpa [compileTrampoline, trHead, trExh, trMid, trTail, List.append_assoc] using hlink)
  rw [env.hexhaustedLbl] at hExLbl
  have hExEq : env.exhaustedTarget = lkm.totalSize (preT ++ trHead) := Option.some.inj hExLbl
  have hRetLbl : lookupLabel env.labels retRestoreLabel = some (lkm.totalSize (preT ++ trHead ++ trExh ++ trMid)) :=
    linkResolved_lbl_lm lkm (preT ++ trHead ++ trExh ++ trMid) retRestoreLabel _
      (by simpa [compileTrampoline, trHead, trExh, trMid, trTail, List.append_assoc] using hlink)
  let pre1 := preT ++ trHead ++ [Asm.lbl exhaustedLabel]
  have hpc0 : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by
    rw [hpc, hExEq]; simp only [pre1, lkm.totalSize_append, show lkm.totalSize [Asm.lbl exhaustedLabel] = 0 from by simp only [Asm.lbl, lkm.totalSize_label], Nat.add_zero]
  have hlink1 : lkm.linkSpec (pre1 ++ [Asm.addi AbiReg.a0 AbiReg.zero 0#12] ++
      ([Asm.addi AbiReg.a1 AbiReg.zero 1#12, Asm.j retRestoreLabel] ++ trMid ++ trTail ++ postT)) =
      .ok (env.code, env.labels) := by
    simpa [pre1, trHead, trExh, trMid, trTail, compileTrampoline, List.append_assoc] using hlink
  obtain ⟨hrun1, hpc1, ha0_1, hoth1, hmem1⟩ :=
    run_aluImm_rd_step env pre1 _ .addi AbiReg.a0 AbiReg.zero 0#12 (by decide) hlink1 st hpc0
  let st1 := stepReg st AbiReg.a0 (evalAluImm .addi (st.getReg AbiReg.zero) 0#12) (BitVec.ofNat 64 (4 * (lkm.totalSize pre1 + 1)))
  let pre2 := pre1 ++ [Asm.addi AbiReg.a0 AbiReg.zero 0#12]
  have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) := by
    rw [hpc1]; dsimp only [pre2]
    simp only [lkm.totalSize_append, show lkm.totalSize [Asm.addi AbiReg.a0 AbiReg.zero 0#12] = 1 from by simp only [Asm.addi, lkm.totalSize_instr]]
  have hlink2 : lkm.linkSpec (pre2 ++ [Asm.addi AbiReg.a1 AbiReg.zero 1#12] ++
      ([Asm.j retRestoreLabel] ++ trMid ++ trTail ++ postT)) = .ok (env.code, env.labels) := by
    simpa [pre2, List.append_assoc] using hlink1
  obtain ⟨hrun2, hpc2, ha1_2, hoth2, hmem2⟩ :=
    run_aluImm_rd_step env pre2 _ .addi AbiReg.a1 AbiReg.zero 1#12 (by decide) hlink2 st1 hpc1'
  let st2 := stepReg st1 AbiReg.a1 (evalAluImm .addi (st1.getReg AbiReg.zero) 1#12) (BitVec.ofNat 64 (4 * (lkm.totalSize pre2 + 1)))
  let pre3 := pre2 ++ [Asm.addi AbiReg.a1 AbiReg.zero 1#12]
  have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre3) := by
    rw [hpc2]; dsimp only [pre3]
    simp only [lkm.totalSize_append, show lkm.totalSize [Asm.addi AbiReg.a1 AbiReg.zero 1#12] = 1 from by simp only [Asm.addi, lkm.totalSize_instr]]
  have hlinkJ : lkm.linkSpec (pre3 ++ [Asm.j retRestoreLabel] ++ (trMid ++ trTail ++ postT)) =
      .ok (env.code, env.labels) := by
    simpa [pre3, List.append_assoc] using hlink2
  have h64J : 4 * (lkm.totalSize pre3 + lkm.itemSize (.j retRestoreLabel)) < 2 ^ 64 := by
    simpa [Asm.j, lkm.totalSize_singleton] using linkResolved_sub_pc64 env pre3 [Asm.j retRestoreLabel] _ hlinkJ
  obtain ⟨kJ, stJ, hrunJ, hpcJ, hothJ, _, hmemJ⟩ :=
    prog_step_j env pre3 (trMid ++ trTail ++ postT) retRestoreLabel _ hRetLbl hlinkJ h64J st2 hpc2'
  let preRest := preT ++ trHead ++ trExh ++ trMid ++ [Asm.lbl retRestoreLabel]
  have hlinkRest : lkm.linkSpec (preRest ++ callerRestoreRetAsm AbiReg.gp (env.tab.saveBase entryNparams) ++ postT) =
      .ok (env.code, env.labels) := by
    simpa [preRest, compileTrampoline, trHead, trExh, trMid, trTail, List.append_assoc] using hlink
  have hpcJ' : stJ.pc = BitVec.ofNat 64 (4 * lkm.totalSize preRest) := by
    rw [hpcJ]; dsimp only [preRest]
    simp only [lkm.totalSize_append, show lkm.totalSize [Asm.lbl retRestoreLabel] = 0 from by simp only [Asm.lbl, lkm.totalSize_label], Nat.add_zero]
  have hgpJ : stJ.getReg AbiReg.gp = T :=
    (hothJ _ (by decide)).trans ((hoth2 _ (by decide)).trans ((hoth1 _ (by decide)).trans hgp))
  have hmemJEq : stJ.mem = st.mem := hmemJ.trans (hmem2.trans hmem1)
  have hsavedJ : ∀ i (hi : i < callerSaveRegs.length),
      readWord64 stJ.mem ((T + BitVec.ofInt 64 (env.tab.saveBase entryNparams)) + BitVec.ofNat 64 (8 * i)) =
        initSt.getReg (callerSaveRegs[i]'hi) := by
    rw [hmemJEq]; exact hsaved
  obtain ⟨kR, r', hrunR, hpcR, hrestR, hraR, hothR, hmemR⟩ :=
    callerRestoreRet_sim env AbiReg.gp (by decide) (by decide) (env.tab.saveBase entryNparams) T initSt halign
      preRest postT hlinkRest stJ hpcJ' hgpJ hsavedJ
  have ha0J : stJ.getReg AbiReg.a0 = 0#64 := by
    rw [hothJ _ (by decide), hoth2 _ (by decide), ha0_1]
    change st.getReg AbiReg.zero + sextImm12 0#12 = 0#64
    rw [getReg_zero]; decide
  have ha1J : stJ.getReg AbiReg.a1 = 1#64 := by
    rw [hothJ _ (by decide), ha1_2]
    change st1.getReg AbiReg.zero + sextImm12 1#12 = 1#64
    rw [getReg_zero]; decide
  refine ⟨1 + 1 + kJ + kR, r',
    by rw [run_add, run_add, run_add, hrun1]; dsimp only; rw [hrun2]; dsimp only; rw [hrunJ]; exact hrunR,
    hpcR,
    (hothR AbiReg.a0 (by decide) (by decide) (by decide)).trans ha0J,
    (hothR AbiReg.a1 (by decide) (by decide) (by decide)).trans ha1J,
    hrestR, hraR, hmemR.trans hmemJEq⟩

private theorem compileTrampoline_err_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (entry : FnName) (entryNparams : Nat)
    (hTramp : ProgTrampLinkedGen env entry entryNparams)
    (T : BitVec 64) (halign : isAligned (T + BitVec.ofInt 64 (env.tab.saveBase entryNparams)) 8 = true)
    (initSt st : State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * env.errTarget))
    (hgp : st.getReg AbiReg.gp = T)
    (hsaved : ∀ i (hi : i < callerSaveRegs.length),
      readWord64 st.mem ((T + BitVec.ofInt 64 (env.tab.saveBase entryNparams)) + BitVec.ofNat 64 (8 * i)) =
        initSt.getReg (callerSaveRegs[i]'hi)) :
    ∃ k r',
      RV64.run env.rom k st = .cont r' ∧
      r'.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64) ∧
      r'.getReg AbiReg.a0 = 0#64 ∧
      r'.getReg AbiReg.a1 = 2#64 ∧
      RegsRestored initSt r' ∧
      r'.getReg AbiReg.ra = initSt.getReg AbiReg.ra ∧
      r'.mem = st.mem := by
  obtain ⟨preT, postT, hlink⟩ := hTramp
  let trHead :=
    [Asm.lbl enterLabel] ++
    callerSaveAsm AbiReg.a0 (env.tab.saveBase entryNparams) ++
    [Asm.mv AbiReg.s1 AbiReg.sp, Asm.mv AbiReg.s2 AbiReg.ra,
     Asm.mv AbiReg.gp AbiReg.a0, Asm.mv AbiReg.s0 AbiReg.a1, Asm.ld AbiReg.sp AbiReg.gp 0#12,
     Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel, Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++
    ((List.range (min entryNparams maxRes)).flatMap fun i =>
      loadMemOff .ld (resReg i) AbiReg.gp AbiReg.t2 (env.tab.args + 8 * Int.ofNat i)) ++
    addImmOff AbiReg.t0 AbiReg.gp AbiReg.t2
      (env.tab.args + 8 * Int.ofNat (if maxRes < entryNparams then maxRes else 0)) ++
    li AbiReg.t1 (BitVec.ofNat 64 entryNparams) ++
    [Asm.call (fnLabel entry), Asm.addi AbiReg.a1 AbiReg.zero 0#12, Asm.j retRestoreLabel,
     Asm.lbl exhaustedLabel, Asm.addi AbiReg.a0 AbiReg.zero 0#12,
     Asm.addi AbiReg.a1 AbiReg.zero 1#12, Asm.j retRestoreLabel]
  let trTail := [Asm.lbl retRestoreLabel] ++ callerRestoreRetAsm AbiReg.gp (env.tab.saveBase entryNparams)
  have hErrLbl : lookupLabel env.labels errLabel = some (lkm.totalSize (preT ++ trHead)) :=
    linkResolved_lbl_lm lkm (preT ++ trHead) errLabel _
      (by simpa [compileTrampoline, trHead, trTail, List.append_assoc] using hlink)
  rw [env.herrLbl] at hErrLbl
  have hErrEq : env.errTarget = lkm.totalSize (preT ++ trHead) := Option.some.inj hErrLbl
  let pre1 := preT ++ trHead ++ [Asm.lbl errLabel]
  have hpc0 : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by
    rw [hpc, hErrEq]; simp only [pre1, lkm.totalSize_append, show lkm.totalSize [Asm.lbl errLabel] = 0 from by simp only [Asm.lbl, lkm.totalSize_label], Nat.add_zero]
  have hlink1 : lkm.linkSpec (pre1 ++ [Asm.addi AbiReg.a0 AbiReg.zero 0#12] ++
      ([Asm.lbl abortLabel, Asm.addi AbiReg.a1 AbiReg.zero 2#12] ++ trTail ++ postT)) =
      .ok (env.code, env.labels) := by
    simpa [pre1, trHead, trTail, compileTrampoline, List.append_assoc] using hlink
  obtain ⟨hrun1, hpc1, ha0_1, hoth1, hmem1⟩ :=
    run_aluImm_rd_step env pre1 _ .addi AbiReg.a0 AbiReg.zero 0#12 (by decide) hlink1 st hpc0
  let st1 := stepReg st AbiReg.a0 (evalAluImm .addi (st.getReg AbiReg.zero) 0#12) (BitVec.ofNat 64 (4 * (lkm.totalSize pre1 + 1)))
  let pre2 := pre1 ++ [Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.lbl abortLabel]
  have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) := by
    rw [hpc1]
    have htw2 : lkm.totalSize [Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.lbl abortLabel] = 1 := by
      rw [show [Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.lbl abortLabel] =
          [Asm.addi AbiReg.a0 AbiReg.zero 0#12] ++ [Asm.lbl abortLabel] from rfl,
          lkm.totalSize_append, Asm.addi, lkm.totalSize_instr, Asm.lbl, lkm.totalSize_label, Nat.add_zero]
    rw [show lkm.totalSize pre2 = lkm.totalSize pre1 + lkm.totalSize [Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.lbl abortLabel] from lkm.totalSize_append _ _,
        htw2]
  have hlink2 : lkm.linkSpec (pre2 ++ [Asm.addi AbiReg.a1 AbiReg.zero 2#12] ++ (trTail ++ postT)) =
      .ok (env.code, env.labels) := by
    simpa [pre2, List.append_assoc] using hlink1
  obtain ⟨hrun2, hpc2, ha1_2, hoth2, hmem2⟩ :=
    run_aluImm_rd_step env pre2 _ .addi AbiReg.a1 AbiReg.zero 2#12 (by decide) hlink2 st1 hpc1'
  let st2 := stepReg st1 AbiReg.a1 (evalAluImm .addi (st1.getReg AbiReg.zero) 2#12) (BitVec.ofNat 64 (4 * (lkm.totalSize pre2 + 1)))
  let preRest := pre2 ++ [Asm.addi AbiReg.a1 AbiReg.zero 2#12, Asm.lbl retRestoreLabel]
  have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize preRest) := by
    rw [hpc2]
    have htw3 : lkm.totalSize [Asm.addi AbiReg.a1 AbiReg.zero 2#12, Asm.lbl retRestoreLabel] = 1 := by
      rw [show [Asm.addi AbiReg.a1 AbiReg.zero 2#12, Asm.lbl retRestoreLabel] =
          [Asm.addi AbiReg.a1 AbiReg.zero 2#12] ++ [Asm.lbl retRestoreLabel] from rfl,
          lkm.totalSize_append, Asm.addi, lkm.totalSize_instr, Asm.lbl, lkm.totalSize_label, Nat.add_zero]
    rw [show lkm.totalSize preRest = lkm.totalSize pre2 + lkm.totalSize [Asm.addi AbiReg.a1 AbiReg.zero 2#12, Asm.lbl retRestoreLabel] from lkm.totalSize_append _ _,
        htw3]
  have hlinkRest : lkm.linkSpec (preRest ++ callerRestoreRetAsm AbiReg.gp (env.tab.saveBase entryNparams) ++ postT) =
      .ok (env.code, env.labels) := by
    simpa [preRest, trTail, List.append_assoc] using hlink2
  have hgp2 : st2.getReg AbiReg.gp = T := (hoth2 _ (by decide)).trans ((hoth1 _ (by decide)).trans hgp)
  have hmem2Eq : st2.mem = st.mem := hmem2.trans hmem1
  have hsaved2 : ∀ i (hi : i < callerSaveRegs.length),
      readWord64 st2.mem ((T + BitVec.ofInt 64 (env.tab.saveBase entryNparams)) + BitVec.ofNat 64 (8 * i)) =
        initSt.getReg (callerSaveRegs[i]'hi) := by
    rw [hmem2Eq]; exact hsaved
  obtain ⟨kR, r', hrunR, hpcR, hrestR, hraR, hothR, hmemR⟩ :=
    callerRestoreRet_sim env AbiReg.gp (by decide) (by decide) (env.tab.saveBase entryNparams) T initSt halign
      preRest postT hlinkRest st2 hpc2' hgp2 hsaved2
  have ha0_2 : st2.getReg AbiReg.a0 = 0#64 := by
    rw [hoth2 _ (by decide), ha0_1]
    change st.getReg AbiReg.zero + sextImm12 0#12 = 0#64
    rw [getReg_zero]; decide
  have ha1_2' : st2.getReg AbiReg.a1 = 2#64 := by
    rw [ha1_2]
    change st1.getReg AbiReg.zero + sextImm12 2#12 = 2#64
    rw [getReg_zero]; decide
  refine ⟨1 + 1 + kR, r',
    by rw [run_add, run_add, hrun1]; dsimp only; rw [hrun2]; exact hrunR,
    hpcR,
    (hothR AbiReg.a0 (by decide) (by decide) (by decide)).trans ha0_2,
    (hothR AbiReg.a1 (by decide) (by decide) (by decide)).trans ha1_2',
    hrestR, hraR, hmemR.trans hmem2Eq⟩

private theorem compileTrampoline_abort_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (entry : FnName) (entryNparams : Nat)
    (hTramp : ProgTrampLinkedGen env entry entryNparams)
    (T : BitVec 64) (halign : isAligned (T + BitVec.ofInt 64 (env.tab.saveBase entryNparams)) 8 = true)
    (initSt st : State) {code : BitVec 64}
    (hpc : st.pc = BitVec.ofNat 64 (4 * env.abortTarget))
    (ha0 : st.getReg AbiReg.a0 = code)
    (hgp : st.getReg AbiReg.gp = T)
    (hsaved : ∀ i (hi : i < callerSaveRegs.length),
      readWord64 st.mem ((T + BitVec.ofInt 64 (env.tab.saveBase entryNparams)) + BitVec.ofNat 64 (8 * i)) =
        initSt.getReg (callerSaveRegs[i]'hi)) :
    ∃ k r',
      RV64.run env.rom k st = .cont r' ∧
      r'.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64) ∧
      r'.getReg AbiReg.a0 = code ∧
      r'.getReg AbiReg.a1 = 2#64 ∧
      RegsRestored initSt r' ∧
      r'.getReg AbiReg.ra = initSt.getReg AbiReg.ra ∧
      r'.mem = st.mem := by
  obtain ⟨preT, postT, hlink⟩ := hTramp
  let trHead :=
    [Asm.lbl enterLabel] ++
    callerSaveAsm AbiReg.a0 (env.tab.saveBase entryNparams) ++
    [Asm.mv AbiReg.s1 AbiReg.sp, Asm.mv AbiReg.s2 AbiReg.ra,
     Asm.mv AbiReg.gp AbiReg.a0, Asm.mv AbiReg.s0 AbiReg.a1, Asm.ld AbiReg.sp AbiReg.gp 0#12,
     Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel, Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++
    ((List.range (min entryNparams maxRes)).flatMap fun i =>
      loadMemOff .ld (resReg i) AbiReg.gp AbiReg.t2 (env.tab.args + 8 * Int.ofNat i)) ++
    addImmOff AbiReg.t0 AbiReg.gp AbiReg.t2
      (env.tab.args + 8 * Int.ofNat (if maxRes < entryNparams then maxRes else 0)) ++
    li AbiReg.t1 (BitVec.ofNat 64 entryNparams) ++
    [Asm.call (fnLabel entry), Asm.addi AbiReg.a1 AbiReg.zero 0#12, Asm.j retRestoreLabel,
     Asm.lbl exhaustedLabel, Asm.addi AbiReg.a0 AbiReg.zero 0#12,
     Asm.addi AbiReg.a1 AbiReg.zero 1#12, Asm.j retRestoreLabel,
     Asm.lbl errLabel, Asm.addi AbiReg.a0 AbiReg.zero 0#12]
  let trTail := [Asm.lbl retRestoreLabel] ++ callerRestoreRetAsm AbiReg.gp (env.tab.saveBase entryNparams)
  have hAbLbl : lookupLabel env.labels abortLabel = some (lkm.totalSize (preT ++ trHead)) :=
    linkResolved_lbl_lm lkm (preT ++ trHead) abortLabel _
      (by simpa [compileTrampoline, trHead, trTail, List.append_assoc] using hlink)
  rw [env.habortLbl] at hAbLbl
  have hAbEq : env.abortTarget = lkm.totalSize (preT ++ trHead) := Option.some.inj hAbLbl
  let pre1 := preT ++ trHead ++ [Asm.lbl abortLabel]
  have hpc0 : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by
    rw [hpc, hAbEq]; simp only [pre1, lkm.totalSize_append, show lkm.totalSize [Asm.lbl abortLabel] = 0 from by simp only [Asm.lbl, lkm.totalSize_label], Nat.add_zero]
  have hlink1 : lkm.linkSpec (pre1 ++ [Asm.addi AbiReg.a1 AbiReg.zero 2#12] ++ (trTail ++ postT)) =
      .ok (env.code, env.labels) := by
    simpa [pre1, trHead, trTail, compileTrampoline, List.append_assoc] using hlink
  obtain ⟨hrun1, hpc1, ha1_1, hoth1, hmem1⟩ :=
    run_aluImm_rd_step env pre1 _ .addi AbiReg.a1 AbiReg.zero 2#12 (by decide) hlink1 st hpc0
  let st1 := stepReg st AbiReg.a1 (evalAluImm .addi (st.getReg AbiReg.zero) 2#12) (BitVec.ofNat 64 (4 * (lkm.totalSize pre1 + 1)))
  let preRest := pre1 ++ [Asm.addi AbiReg.a1 AbiReg.zero 2#12, Asm.lbl retRestoreLabel]
  have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize preRest) := by
    rw [hpc1]
    have htw2 : lkm.totalSize [Asm.addi AbiReg.a1 AbiReg.zero 2#12, Asm.lbl retRestoreLabel] = 1 := by
      rw [show [Asm.addi AbiReg.a1 AbiReg.zero 2#12, Asm.lbl retRestoreLabel] =
          [Asm.addi AbiReg.a1 AbiReg.zero 2#12] ++ [Asm.lbl retRestoreLabel] from rfl,
          lkm.totalSize_append, Asm.addi, lkm.totalSize_instr, Asm.lbl, lkm.totalSize_label, Nat.add_zero]
    rw [show lkm.totalSize preRest = lkm.totalSize pre1 + lkm.totalSize [Asm.addi AbiReg.a1 AbiReg.zero 2#12, Asm.lbl retRestoreLabel] from lkm.totalSize_append _ _,
        htw2]
  have hlinkRest : lkm.linkSpec (preRest ++ callerRestoreRetAsm AbiReg.gp (env.tab.saveBase entryNparams) ++ postT) =
      .ok (env.code, env.labels) := by
    simpa [preRest, trTail, List.append_assoc] using hlink1
  have hgp1 : st1.getReg AbiReg.gp = T := (hoth1 _ (by decide)).trans hgp
  have hsaved1 : ∀ i (hi : i < callerSaveRegs.length),
      readWord64 st1.mem ((T + BitVec.ofInt 64 (env.tab.saveBase entryNparams)) + BitVec.ofNat 64 (8 * i)) =
        initSt.getReg (callerSaveRegs[i]'hi) := by
    rw [hmem1]; exact hsaved
  obtain ⟨kR, r', hrunR, hpcR, hrestR, hraR, hothR, hmemR⟩ :=
    callerRestoreRet_sim env AbiReg.gp (by decide) (by decide) (env.tab.saveBase entryNparams) T initSt halign
      preRest postT hlinkRest st1 hpc1' hgp1 hsaved1
  have ha0_1 : st1.getReg AbiReg.a0 = code := (hoth1 _ (by decide)).trans ha0
  have ha1_1' : st1.getReg AbiReg.a1 = 2#64 := by
    rw [ha1_1]
    change st.getReg AbiReg.zero + sextImm12 2#12 = 2#64
    rw [getReg_zero]; decide
  refine ⟨1 + kR, r', by rw [run_add, hrun1]; exact hrunR, hpcR,
    (hothR AbiReg.a0 (by decide) (by decide) (by decide)).trans ha0_1,
    (hothR AbiReg.a1 (by decide) (by decide) (by decide)).trans ha1_1',
    hrestR, hraR, hmemR.trans hmem1⟩

theorem compileProg_sim_gen {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab) (p : _root_.L.Prog)
    (hpOk : progOkB env.tab p = true) (hpArgs : progArgsOkB p = true)
    (hFns : ProgFnsLinkedGen env p)
    (entry : FnName) (entryFd : FunDecl) (hEntry : p.lookup entry = some entryFd)
    (hTramp : ProgTrampLinkedGen env entry entryFd.nparams)
    (b : Nat) (hb64 : b < 2 ^ 64)
    (vs : List _root_.L.Word) (hvslen : vs.length ≤ entryFd.nparams)
    (hTabSave : env.tab.saveBase entryFd.nparams + 128 ≤ (L.tabBytes : Int))
    (m : _root_.L.Mem)
    (hStack : L.stackLimit.toNat + runStackNeedB p b entry vs m ≤ L.stackTop.toNat)
    (enterPc : Nat) (st : State)
    (hEnterLbl : lookupLabel env.labels enterLabel = some enterPc)
    (hpc : st.pc = BitVec.ofNat 64 (4 * enterPc))
    (ha0 : st.getReg AbiReg.a0 = L.T)
    (ha1 : st.getReg AbiReg.a1 = BitVec.ofNat 64 b)
    (hm : ProgMemRel env.tab L st.mem m)
    (hhdr : TabHeaderOk L st.mem)
    (hargWords : ∀ j, j < entryFd.nparams →
      readWord64 st.mem (L.T + BitVec.ofInt 64 env.tab.args + BitVec.ofNat 64 (8 * j)) = (vs.getD j 0).toBitVec) :
    match runB p b entry vs m with
    | .ok (retVs, m', _) =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = (st.getReg AbiReg.ra &&& ~~~1#64) ∧
        r'.getReg AbiReg.a0 = (retVs.headD 0).toBitVec ∧
        r'.getReg AbiReg.a1 = 0#64 ∧
        RegsRestored st r' ∧
        r'.getReg AbiReg.ra = st.getReg AbiReg.ra ∧
        ProgMemRel env.tab L r'.mem m' ∧
        TabHeaderOk L r'.mem ∧
        (∀ i, i < min (min (max 1 retVs.length) env.tab.nres) maxRes → i ≠ 1 → r'.getReg (resReg i) = (retVs.getD i 0).toBitVec) ∧
        (∀ i, maxRes ≤ i → i < min (max 1 retVs.length) env.tab.nres →
          readWord64 r'.mem (L.T + BitVec.ofInt 64 (env.tab.resOff i)) = (retVs.getD i 0).toBitVec)
    | .error .outOfFuel =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = (st.getReg AbiReg.ra &&& ~~~1#64) ∧
        r'.getReg AbiReg.a0 = 0#64 ∧
        r'.getReg AbiReg.a1 = 1#64 ∧
        RegsRestored st r' ∧
        r'.getReg AbiReg.ra = st.getReg AbiReg.ra
    | .error (.abort code) =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = (st.getReg AbiReg.ra &&& ~~~1#64) ∧
        r'.getReg AbiReg.a0 = code.toBitVec ∧
        r'.getReg AbiReg.a1 = 2#64 ∧
        RegsRestored st r' ∧
        r'.getReg AbiReg.ra = st.getReg AbiReg.ra
    | .error _ =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = (st.getReg AbiReg.ra &&& ~~~1#64) ∧
        r'.getReg AbiReg.a0 = 0#64 ∧
        r'.getReg AbiReg.a1 = 2#64 ∧
        RegsRestored st r' ∧
        r'.getReg AbiReg.ra = st.getReg AbiReg.ra := by
  obtain ⟨preT, postT, hlinkT⟩ := hTramp
  have hTramp' : ProgTrampLinkedGen env entry entryFd.nparams := ⟨preT, postT, hlinkT⟩
  have hSaveAl : isAligned (L.T + BitVec.ofInt 64 (env.tab.saveBase entryFd.nparams)) 8 = true :=
    callerSaveBase_align L entryFd.nparams
  have hSaveValid : (L.T + BitVec.ofInt 64 (env.tab.saveBase entryFd.nparams)).toNat + 128 ≤ 2 ^ 64 :=
    callerSaveBase_valid L entryFd.nparams hTabSave
  let trSave := callerSaveAsm AbiReg.a0 (env.tab.saveBase entryFd.nparams)
  let trLoad := (List.range (min entryFd.nparams maxRes)).flatMap fun i =>
    loadMemOff .ld (resReg i) AbiReg.gp AbiReg.t2 (env.tab.args + 8 * Int.ofNat i)
  let trPtr := addImmOff AbiReg.t0 AbiReg.gp AbiReg.t2
    (env.tab.args + 8 * Int.ofNat (if maxRes < entryFd.nparams then maxRes else 0))
  let trCnt := li AbiReg.t1 (BitVec.ofNat 64 entryFd.nparams)
  let trRest := callerRestoreRetAsm AbiReg.gp (env.tab.saveBase entryFd.nparams)
  let trPostCall :=
    [Asm.call (fnLabel entry), Asm.addi AbiReg.a1 AbiReg.zero 0#12, Asm.j retRestoreLabel,
     Asm.lbl exhaustedLabel, Asm.addi AbiReg.a0 AbiReg.zero 0#12,
     Asm.addi AbiReg.a1 AbiReg.zero 1#12, Asm.j retRestoreLabel,
     Asm.lbl errLabel, Asm.addi AbiReg.a0 AbiReg.zero 0#12,
     Asm.lbl abortLabel, Asm.addi AbiReg.a1 AbiReg.zero 2#12,
     Asm.lbl retRestoreLabel] ++ trRest
  have hEnterLbl' : lookupLabel env.labels enterLabel = some (lkm.totalSize preT) :=
    linkResolved_lbl_lm lkm preT enterLabel _
      (by simpa [compileTrampoline, trSave, trLoad, trPtr, trCnt, trPostCall, trRest, List.append_assoc] using hlinkT)
  rw [hEnterLbl'] at hEnterLbl
  have hEnterEq : enterPc = lkm.totalSize preT := Option.some.inj hEnterLbl.symm
  let preSave := preT ++ [Asm.lbl enterLabel]
  have hpc0 : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize preSave) := by
    rw [hpc, hEnterEq]; simp only [preSave, lkm.totalSize_append, show lkm.totalSize [Asm.lbl enterLabel] = 0 from by simp only [Asm.lbl, lkm.totalSize_label], Nat.add_zero]
  have hlinkSave : lkm.linkSpec (preSave ++ trSave ++
      ([Asm.mv AbiReg.s1 AbiReg.sp, Asm.mv AbiReg.s2 AbiReg.ra,
        Asm.mv AbiReg.gp AbiReg.a0, Asm.mv AbiReg.s0 AbiReg.a1, Asm.ld AbiReg.sp AbiReg.gp 0#12,
        Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel, Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++
        trLoad ++ trPtr ++ trCnt ++ trPostCall ++ postT)) =
      .ok (env.code, env.labels) := by
    simpa [preSave, compileTrampoline, trSave, trLoad, trPtr, trCnt, trPostCall, trRest, List.append_assoc] using hlinkT
  obtain ⟨kSave, stS, hrunSave, hpcSave, hothSave, hsavedS, houtSave⟩ :=
    callerSave_sim env AbiReg.a0 (by decide) (by decide) (env.tab.saveBase entryFd.nparams) L.T
      hSaveAl hSaveValid preSave _ hlinkSave st hpc0 ha0
  have ha0S : stS.getReg AbiReg.a0 = L.T := (hothSave _ (by decide) (by decide)).trans ha0
  have ha1S : stS.getReg AbiReg.a1 = BitVec.ofNat 64 b := (hothSave _ (by decide) (by decide)).trans ha1
  have hmS : ProgMemRel env.tab L stS.mem m :=
    ProgMemRel.of_callerSave L entryFd.nparams hTabSave houtSave hm
  have hhdrS : TabHeaderOk L stS.mem :=
    TabHeaderOk.of_callerSave L entryFd.nparams hTabSave houtSave hhdr
  have hargWordsS : ∀ j, j < entryFd.nparams →
      readWord64 stS.mem (L.T + BitVec.ofInt 64 env.tab.args + BitVec.ofNat 64 (8 * j)) = (vs.getD j 0).toBitVec :=
    argWords_of_callerSave L entryFd.nparams hTabSave houtSave hargWords
  let pre1 := preSave ++ trSave
  have hpcS' : stS.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by
    simpa [pre1, lkm.totalSize_append] using hpcSave
  have hlink1 : lkm.linkSpec (pre1 ++ [Asm.mv AbiReg.s1 AbiReg.sp] ++
      ([Asm.mv AbiReg.s2 AbiReg.ra, Asm.mv AbiReg.gp AbiReg.a0, Asm.mv AbiReg.s0 AbiReg.a1,
        Asm.ld AbiReg.sp AbiReg.gp 0#12, Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
        Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++ trLoad ++ trPtr ++ trCnt ++ trPostCall ++ postT)) =
      .ok (env.code, env.labels) := by
    simpa [pre1, List.append_assoc] using hlinkSave
  obtain ⟨hrun1, hpc1, hs1_1, hoth1, hmem1⟩ :=
    run_aluImm_rd_step env pre1 _ .addi AbiReg.s1 AbiReg.sp 0#12 (by decide) hlink1 stS hpcS'
  let st1 := stepReg stS AbiReg.s1 (evalAluImm .addi (stS.getReg AbiReg.sp) 0#12) (BitVec.ofNat 64 (4 * (lkm.totalSize pre1 + 1)))
  let pre2 := pre1 ++ [Asm.mv AbiReg.s1 AbiReg.sp]
  have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) := by
    rw [hpc1]; dsimp only [pre2]
    simp only [lkm.totalSize_append, show lkm.totalSize [Asm.mv AbiReg.s1 AbiReg.sp] = 1 from by simp only [Asm.mv, lkm.totalSize_instr]]
  have hlink2 : lkm.linkSpec (pre2 ++ [Asm.mv AbiReg.s2 AbiReg.ra] ++
      ([Asm.mv AbiReg.gp AbiReg.a0, Asm.mv AbiReg.s0 AbiReg.a1,
        Asm.ld AbiReg.sp AbiReg.gp 0#12, Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
        Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++ trLoad ++ trPtr ++ trCnt ++ trPostCall ++ postT)) =
      .ok (env.code, env.labels) := by
    simpa [pre2, List.append_assoc] using hlink1
  obtain ⟨hrun2, hpc2, hs2_2, hoth2, hmem2⟩ :=
    run_aluImm_rd_step env pre2 _ .addi AbiReg.s2 AbiReg.ra 0#12 (by decide) hlink2 st1 hpc1'
  let st2 := stepReg st1 AbiReg.s2 (evalAluImm .addi (st1.getReg AbiReg.ra) 0#12) (BitVec.ofNat 64 (4 * (lkm.totalSize pre2 + 1)))
  let pre3 := pre2 ++ [Asm.mv AbiReg.s2 AbiReg.ra]
  have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre3) := by
    rw [hpc2]; dsimp only [pre3]
    simp only [lkm.totalSize_append, show lkm.totalSize [Asm.mv AbiReg.s2 AbiReg.ra] = 1 from by simp only [Asm.mv, lkm.totalSize_instr]]
  have hlink3 : lkm.linkSpec (pre3 ++ [Asm.mv AbiReg.gp AbiReg.a0] ++
      ([Asm.mv AbiReg.s0 AbiReg.a1, Asm.ld AbiReg.sp AbiReg.gp 0#12,
        Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel, Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++
        trLoad ++ trPtr ++ trCnt ++ trPostCall ++ postT)) = .ok (env.code, env.labels) := by
    simpa [pre3, List.append_assoc] using hlink2
  obtain ⟨hrun3, hpc3, hgp_3, hoth3, hmem3⟩ :=
    run_aluImm_rd_step env pre3 _ .addi AbiReg.gp AbiReg.a0 0#12 (by decide) hlink3 st2 hpc2'
  let st3 := stepReg st2 AbiReg.gp (evalAluImm .addi (st2.getReg AbiReg.a0) 0#12) (BitVec.ofNat 64 (4 * (lkm.totalSize pre3 + 1)))
  let pre4 := pre3 ++ [Asm.mv AbiReg.gp AbiReg.a0]
  have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre4) := by
    rw [hpc3]; dsimp only [pre4]
    simp only [lkm.totalSize_append, show lkm.totalSize [Asm.mv AbiReg.gp AbiReg.a0] = 1 from by simp only [Asm.mv, lkm.totalSize_instr]]
  have hlink4 : lkm.linkSpec (pre4 ++ [Asm.mv AbiReg.s0 AbiReg.a1] ++
      ([Asm.ld AbiReg.sp AbiReg.gp 0#12, Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
        Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++ trLoad ++ trPtr ++ trCnt ++ trPostCall ++ postT)) =
      .ok (env.code, env.labels) := by
    simpa [pre4, List.append_assoc] using hlink3
  obtain ⟨hrun4, hpc4, hs0_4, hoth4, hmem4⟩ :=
    run_aluImm_rd_step env pre4 _ .addi AbiReg.s0 AbiReg.a1 0#12 (by decide) hlink4 st3 hpc3'
  let st4 := stepReg st3 AbiReg.s0 (evalAluImm .addi (st3.getReg AbiReg.a1) 0#12) (BitVec.ofNat 64 (4 * (lkm.totalSize pre4 + 1)))
  let pre5 := pre4 ++ [Asm.mv AbiReg.s0 AbiReg.a1]
  have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre5) := by
    rw [hpc4]; dsimp only [pre5]
    simp only [lkm.totalSize_append, show lkm.totalSize [Asm.mv AbiReg.s0 AbiReg.a1] = 1 from by simp only [Asm.mv, lkm.totalSize_instr]]
  have hlink5 : lkm.linkSpec (pre5 ++ [Asm.raw (.load .ld AbiReg.sp AbiReg.gp 0#12)] ++
      ([Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel, Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++
        trLoad ++ trPtr ++ trCnt ++ trPostCall ++ postT)) = .ok (env.code, env.labels) := by
    simpa [pre5, Asm.raw, Asm.ld, List.append_assoc] using hlink4
  have hpc5_64 : 4 * (lkm.totalSize pre5 + 1) < 2 ^ 64 := by
    have h := linkResolved_sub_pc64 env pre5 [Asm.raw (.load .ld AbiReg.sp AbiReg.gp 0#12)] _ hlink5
    rw [show lkm.totalSize [Asm.raw (.load .ld AbiReg.sp AbiReg.gp 0#12)] = 1 from by simp only [Asm.raw, lkm.totalSize_instr]] at h; exact h
  have hgp4 : st4.getReg AbiReg.gp = L.T := by
    rw [hoth4 _ (by decide), hgp_3]
    change st2.getReg AbiReg.a0 + sextImm12 0#12 = L.T
    have hz : sextImm12 0#12 = 0#64 := rfl
    rw [hz, BitVec.add_zero, hoth2 _ (by decide), hoth1 _ (by decide), ha0S]
  have hmem4Eq : st4.mem = stS.mem := by rw [hmem4, hmem3, hmem2, hmem1]
  have halGp4 : isAligned (st4.getReg AbiReg.gp + sextImm12 0#12) 8 = true := by
    have hz : sextImm12 0#12 = 0#64 := rfl
    rw [hgp4, hz, BitVec.add_zero]; exact L.hTAlign
  obtain ⟨hrun5, hpc5, hsp_5, hoth5, hmem5⟩ :=
    step_ld_off env pre5 _ AbiReg.sp AbiReg.gp 0#12 (by decide) hlink5 hpc5_64 st4 hpc4' halGp4
  let st5 := stepReg st4 AbiReg.sp (readWord64 st4.mem (st4.getReg AbiReg.gp + sextImm12 0#12)) (st4.pc + 4#64)
  let pre6 := pre5 ++ [Asm.ld AbiReg.sp AbiReg.gp 0#12]
  have hpc5' : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre6) := by
    rw [hpc5]; dsimp only [pre6]
    simp only [lkm.totalSize_append, show lkm.totalSize [Asm.ld AbiReg.sp AbiReg.gp 0#12] = 1 from by simp only [Asm.ld, lkm.totalSize_instr]]
  have hlinkBr : lkm.linkSpec (pre6 ++ [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel] ++
      ([Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++ trLoad ++ trPtr ++ trCnt ++ trPostCall ++ postT)) =
      .ok (env.code, env.labels) := by
    simpa [pre6, Asm.raw, Asm.ld, List.append_assoc] using hlink5
  have hbr := run_br_step env pre6 _ .beq AbiReg.s0 AbiReg.zero exhaustedLabel env.exhaustedTarget env.hexhaustedLbl (by decide)
    hlinkBr st5 hpc5'
  have hs0_5 : st5.getReg AbiReg.s0 = BitVec.ofNat 64 b := by
    rw [hoth5 _ (by decide), hs0_4]
    change st3.getReg AbiReg.a1 + sextImm12 0#12 = BitVec.ofNat 64 b
    have hz : sextImm12 0#12 = 0#64 := rfl
    rw [hz, BitVec.add_zero, hoth3 _ (by decide), hoth2 _ (by decide), hoth1 _ (by decide), ha1S]
  have hgp5 : st5.getReg AbiReg.gp = L.T := (hoth5 _ (by decide)).trans hgp4
  have hmem5Eq : st5.mem = stS.mem := by rw [hmem5]; exact hmem4Eq
  have hrunPre5 : RV64.run env.rom (kSave + (1 + 1 + 1 + 1 + 1)) st = .cont st5 := by
    rw [run_add, hrunSave]; dsimp only
    rw [run_add, run_add, run_add, run_add, hrun1]
    dsimp only; rw [hrun2]; dsimp only; rw [hrun3]; dsimp only; rw [hrun4]; exact hrun5
  cases b with
  | zero =>
    unfold runB
    rw [hEntry]
    dsimp only
    have hcond0 : evalBranch .beq (st5.getReg AbiReg.s0) (st5.getReg AbiReg.zero) = true := by
      rw [hs0_5, getReg_zero]; rfl
    obtain ⟨kBr, stEx, _, hrunEx1, hpcEx1, hothEx1, _, hmemEx1⟩ := hbr
    have hpcEx1' : stEx.pc = BitVec.ofNat 64 (4 * env.exhaustedTarget) := by rw [hpcEx1, hcond0]; rfl
    have hgpEx : stEx.getReg AbiReg.gp = L.T := (hothEx1 _ (by decide)).trans hgp5
    have hsavedEx : ∀ i (hi : i < callerSaveRegs.length),
        readWord64 stEx.mem ((L.T + BitVec.ofInt 64 (env.tab.saveBase entryFd.nparams)) + BitVec.ofNat 64 (8 * i)) =
          st.getReg (callerSaveRegs[i]'hi) := by
      rw [hmemEx1, hmem5Eq]; exact hsavedS
    obtain ⟨kEx, rEx, hrunEx, hpcEx, ha0Ex, ha1Ex, hrestEx, hraEx, _⟩ :=
      compileTrampoline_exhausted_sim env entry entryFd.nparams hTramp' L.T hSaveAl st stEx hpcEx1' hgpEx hsavedEx
    exact ⟨_, rEx, by rw [run_add, run_add, hrunPre5]; dsimp only; rw [hrunEx1]; exact hrunEx,
      hpcEx, ha0Ex, ha1Ex, hrestEx, hraEx⟩
  | succ b' =>
    have hne0 : BitVec.ofNat 64 (b' + 1) ≠ 0#64 :=
      BitVec.ofNat_ne_zero_of_lt (Nat.succ_pos b') hb64
    have hcond1 : evalBranch .beq (st5.getReg AbiReg.s0) (st5.getReg AbiReg.zero) = false := by
      rw [hs0_5, getReg_zero]; simp [evalBranch, hne0]
    obtain ⟨kBr, st6, _, hrun6, hpc6Br, hoth6Br, _, hmem6Br⟩ := hbr
    let pre7 := pre6 ++ [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel]
    have hpc6' : st6.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre7) := by
      rw [hpc6Br, hcond1]; simp only [Bool.false_eq_true, ↓reduceIte]
      exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (lkm.totalSize_append pre6 _).symm
    have hlink7 : lkm.linkSpec (pre7 ++ [Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++
        (trLoad ++ trPtr ++ trCnt ++ trPostCall ++ postT)) = .ok (env.code, env.labels) := by
      simpa [pre7, List.append_assoc] using hlinkBr
    obtain ⟨hrun7, hpc7, hs0_7, hoth7, hmem7⟩ :=
      run_aluImm_rd_step env pre7 _ .addi AbiReg.s0 AbiReg.s0 (-1#12) (by decide) hlink7 st6 hpc6'
    let st7 := stepReg st6 AbiReg.s0 (evalAluImm .addi (st6.getReg AbiReg.s0) (-1#12)) (BitVec.ofNat 64 (4 * (lkm.totalSize pre7 + 1)))
    let pre8 := pre7 ++ [Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)]
    have hpc7' : st7.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre8) := by
      rw [hpc7]; dsimp only [pre8]
      simp only [lkm.totalSize_append, Asm.addi, lkm.totalSize_instr]
    have hlink7L : lkm.linkSpec (pre8 ++ trLoad ++ (trPtr ++ trCnt ++ trPostCall ++ postT)) =
        .ok (env.code, env.labels) := by
      simpa [pre8, List.append_assoc] using hlink7
    have hgp7 : st7.getReg AbiReg.gp = L.T :=
      (hoth7 _ (by decide)).trans ((hoth6Br _ (by decide)).trans hgp5)
    have hmem7Eq : st7.mem = stS.mem := hmem7.trans (hmem6Br.trans hmem5Eq)
    obtain ⟨kLoad, st7L, hrun7L, hpc7L, hpres7L, hmem7L, hregs7L⟩ :=
      trampLoadArgs_sim env L vs entryFd.nparams (min entryFd.nparams maxRes) (Nat.le_refl _)
        pre8 (trPtr ++ trCnt ++ trPostCall ++ postT) hlink7L st7 hpc7' hgp7 (by rw [hmem7Eq]; exact hargWordsS)
    let pre8L := pre8 ++ trLoad
    have hpc7L' : st7L.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre8L) := by
      rw [lkm.totalSize_append]; exact hpc7L
    have hlink8 : lkm.linkSpec (pre8L ++ trPtr ++ (trCnt ++ trPostCall ++ postT)) =
        .ok (env.code, env.labels) := by
      simpa [pre8L, List.append_assoc] using hlink7L
    have hpc8_64 := linkResolved_sub_pc64 env pre8L trPtr _ hlink8
    obtain ⟨st8, hrun8, hoth8, ht0_8, hmem8, hpc8⟩ :=
      addImmOff_correct_lm lkm env.hrom pre8L _ AbiReg.t0 AbiReg.gp AbiReg.t2 (by decide) (by decide) (by decide)
        (env.tab.args + 8 * Int.ofNat (if maxRes < entryFd.nparams then maxRes else 0)) hlink8 hpc8_64 st7L hpc7L'
    let pre9 := pre8L ++ trPtr
    have hpc8' : st8.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre9) := by
      rw [lkm.totalSize_append]; exact hpc8
    have hlink9 : lkm.linkSpec (pre9 ++ trCnt ++ (trPostCall ++ postT)) =
        .ok (env.code, env.labels) := by
      simpa [pre9, List.append_assoc] using hlink8
    have hpc9_64 := linkResolved_sub_pc64 env pre9 trCnt _ hlink9
    obtain ⟨st9, hrun9, hoth9, ht1_9, hmem9, hpc9⟩ :=
      li_correct_lm lkm env.hrom pre9 _ AbiReg.t1 (by decide) (BitVec.ofNat 64 entryFd.nparams) hlink9 hpc9_64 st8 hpc8'
    let pre10 := pre9 ++ trCnt
    have hpc9' : st9.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre10) := by
      simpa [pre10, lkm.totalSize_append] using hpc9
    have hlinkCall : lkm.linkSpec (pre10 ++ [Asm.call (fnLabel entry)] ++
        (([Asm.addi AbiReg.a1 AbiReg.zero 0#12, Asm.j retRestoreLabel,
           Asm.lbl exhaustedLabel, Asm.addi AbiReg.a0 AbiReg.zero 0#12,
           Asm.addi AbiReg.a1 AbiReg.zero 1#12, Asm.j retRestoreLabel,
           Asm.lbl errLabel, Asm.addi AbiReg.a0 AbiReg.zero 0#12,
           Asm.lbl abortLabel, Asm.addi AbiReg.a1 AbiReg.zero 2#12,
           Asm.lbl retRestoreLabel] ++ trRest) ++ postT)) =
        .ok (env.code, env.labels) := by
      simpa [pre10, trPostCall, List.append_assoc] using hlink9
    have hltCall64 : 4 * (lkm.totalSize pre10 + lkm.itemSize (.call (fnLabel entry))) < 2 ^ 64 := by
      have h := linkResolved_sub_pc64 env pre10 [Asm.call (fnLabel entry)] _ hlinkCall
      simpa [Asm.call, lkm.totalSize_singleton] using h
    obtain ⟨tgtEntry, kCall, st10, _, hlkpEntry, hrun10, hpc10', hregs10, hmem10'⟩ :=
      step_item_call_lm lkm env.hrom pre10 _ (fnLabel entry) hlinkCall hltCall64 st9 hpc9'
    let vsPad := vs ++ List.replicate (entryFd.nparams - vs.length) 0
    have hvsPadLen : vsPad.length = entryFd.nparams := by simp [vsPad]; omega
    have hlocPad : Locals.init vsPad = Locals.init vs := by
      funext x
      by_cases hx : x < vs.length
      · simp [Locals.init, vsPad, List.getD, List.getElem?_append_left hx]
      · simp only [Locals.init, vsPad, List.getD, List.getElem?_append]
        have hxle : vs.length ≤ x := Nat.le_of_not_lt hx
        simp only [hx, ↓reduceIte]
        have hnone : vs[x]? = none := List.getElem?_eq_none hxle
        simp only [hnone, Option.getD_none]
        by_cases hxi : x - vs.length < entryFd.nparams - vs.length
        · simp [hxi]
        · simp [hxi]
    have hgp10 : st10.getReg AbiReg.gp = L.T :=
      ((hregs10.getReg_eq (by decide)).symm.trans (getReg_setReg_ne st9 AbiReg.ra _ _ (by decide))).trans
        ((hoth9 _ (by decide)).trans ((hoth8 _ (by decide) (by decide)).trans (hpres7L.gp.trans hgp7)))
    have hsp10 : st10.getReg AbiReg.sp = L.stackTop := by
      rw [← hregs10.getReg_eq (by decide), getReg_setReg_ne st9 AbiReg.ra _ _ (by decide), hoth9 _ (by decide),
        hoth8 _ (by decide) (by decide), hpres7L.sp, hoth7 _ (by decide), hoth6Br _ (by decide), hsp_5]
      have hz : sextImm12 0#12 = 0#64 := rfl
      rw [hgp4, hz, BitVec.add_zero, hmem4Eq, hhdrS.1]
    have hra10 : st10.getReg AbiReg.ra = BitVec.ofNat 64 (4 * (lkm.totalSize pre10 + lkm.itemSize (.call (fnLabel entry)))) := by
      rw [← hregs10.getReg_eq (by decide), getReg_setReg_eq st9 AbiReg.ra _ (by decide)]
    have hs0_10 : st10.getReg AbiReg.s0 = BitVec.ofNat 64 b' := by
      rw [← hregs10.getReg_eq (by decide), getReg_setReg_ne st9 AbiReg.ra _ _ (by decide), hoth9 _ (by decide),
        hoth8 _ (by decide) (by decide), hpres7L.s0, hs0_7]
      change st6.getReg AbiReg.s0 + sextImm12 (-1#12) = BitVec.ofNat 64 b'
      rw [hoth6Br _ (by decide), hs0_5]
      exact BitVec.ofNat_sub_one_eq_add_neg1 hb64
    let argsPtr := L.T + BitVec.ofInt 64 (env.tab.args + 8 * Int.ofNat (if maxRes < entryFd.nparams then maxRes else 0))
    have ht0_10 : st10.getReg AbiReg.t0 = argsPtr := by
      rw [← hregs10.getReg_eq (by decide), getReg_setReg_ne st9 AbiReg.ra _ _ (by decide), hoth9 _ (by decide), ht0_8,
        hpres7L.gp, hgp7]
    have hmem10 : st10.mem = stS.mem := by
      rw [hmem10', hmem9, hmem8, hmem7L]; exact hmem7Eq
    have hargsAl : isAligned argsPtr 8 = true := by
      dsimp only [argsPtr]
      have hcast : env.tab.args + 8 * Int.ofNat (if maxRes < entryFd.nparams then maxRes else 0) =
          8 * ((2 + 3 * (env.tab.nb + env.tab.nw) + env.tab.romWords + env.tab.nxres + env.tab.ng +
            (if maxRes < entryFd.nparams then maxRes else 0) : Nat) : Int) := by
        rw [Tab.args_eq_nat]; simp only [Int.ofNat_eq_natCast]; split <;> omega
      rw [hcast]
      exact isAligned8_add_int_mul8 L.T L.hTAlign _
    have hargsGe : ∀ j, j < vsPad.length → ∀ k, k < 8 →
        L.stackTop.toNat ≤ (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)) + BitVec.ofNat 64 k).toNat ∨
        ¬L.stackSpan.contains (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)) + BitVec.ofNat 64 k) := by
      intro j hj k hk
      right
      apply (MemSpan.disjoint_to_memDisjoint L.tabSpan_valid L.stackSpan_valid L.htabDisjStack)
      have hjNp : j < entryFd.nparams := by omega
      have hnn : 0 ≤ env.tab.args := by
        rw [Tab.args_eq_nat]; exact Int.natCast_nonneg _
      have hnnSave := callerSaveBase_nonneg env.tab entryFd.nparams
      have hcoeSave : ((env.tab.saveBase entryFd.nparams).toNat : Int) = env.tab.saveBase entryFd.nparams :=
        Int.toNat_of_nonneg hnnSave
      have hargsLe : env.tab.args.toNat + 8 * entryFd.nparams ≤ L.tabBytes := by
        have hcoe : ((env.tab.args.toNat : Nat) : Int) = env.tab.args := Int.toNat_of_nonneg hnn
        have hsb : env.tab.saveBase entryFd.nparams = env.tab.args + 8 * ((max 1 entryFd.nparams : Nat) : Int) := by
          simp only [Tab.saveBase, Int.ofNat_eq_natCast]
        omega
      let baseIdx : Nat := if maxRes < entryFd.nparams then maxRes else 0
      have hidxLt : baseIdx + (j - maxRes) < entryFd.nparams := by
        dsimp only [baseIdx]; split <;> omega
      refine ⟨env.tab.args.toNat + 8 * (baseIdx + (j - maxRes)) + k, by dsimp only [ProgLayout.tabSpan]; omega, ?_⟩
      dsimp only [ProgLayout.tabSpan, argsPtr, baseIdx]
      have htabCast : BitVec.ofInt 64 (env.tab.args + 8 * Int.ofNat (if maxRes < entryFd.nparams then maxRes else 0)) =
          BitVec.ofNat 64 (env.tab.args.toNat + 8 * (if maxRes < entryFd.nparams then maxRes else 0)) := by
        have heq : env.tab.args + 8 * Int.ofNat (if maxRes < entryFd.nparams then maxRes else 0) =
            ((env.tab.args.toNat + 8 * (if maxRes < entryFd.nparams then maxRes else 0) : Nat) : Int) := by
          have hcoe : ((env.tab.args.toNat : Nat) : Int) = env.tab.args := Int.toNat_of_nonneg hnn
          simp only [Int.ofNat_eq_natCast]; split <;> omega
        rw [heq, BitVec.ofInt_natCast]
      rw [htabCast, BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega
    have hargWords10 : ∀ j, j < vsPad.length →
        (if j < maxRes then st10.getReg (resReg j)
         else readWord64 st10.mem (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)))) = (vsPad[j]!).toBitVec := by
      intro j hj
      have hpadEq : (vs.getD j 0).toBitVec = (vsPad[j]!).toBitVec := by
        congr 1
        by_cases hlt : j < vs.length
        · rw [getElem!_pos vsPad j hj]; dsimp only [vsPad]
          rw [List.getElem_append_left hlt]; simp [List.getD, List.getElem?_eq_getElem hlt]
        · simp only [List.getD]
          have hnone : vs[j]? = none := List.getElem?_eq_none (by omega)
          simp only [hnone, Option.getD_none]
          dsimp only [vsPad]
          rw [getElem!_pos (vs ++ List.replicate (entryFd.nparams - vs.length) 0) j hj,
            List.getElem_append_right (by omega : vs.length ≤ j), List.getElem_replicate]
      by_cases hjm : j < maxRes
      · simp only [hjm, ↓reduceIte]
        have hrn := resReg_ne_preserved j
        rw [← hregs10.getReg_eq ⟨resReg_ne_t6 j, hrn.2.2.2.1⟩, getReg_setReg_ne st9 AbiReg.ra (resReg j) _ (resReg_ne_ra j),
          hoth9 _ hrn.2.2.2.2.2.2.1, hoth8 _ hrn.2.2.2.2.2.1 hrn.2.2.2.2.2.2.2,
          hregs7L j (by omega), hpadEq]
      · simp only [hjm, ↓reduceIte]
        have hgt : maxRes < entryFd.nparams := by omega
        have haddr : argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)) =
            L.T + BitVec.ofInt 64 env.tab.args + BitVec.ofNat 64 (8 * j) := by
          dsimp only [argsPtr]; simp only [hgt, ↓reduceIte]
          have hcast : BitVec.ofInt 64 (env.tab.args + 8 * Int.ofNat maxRes) =
              BitVec.ofInt 64 env.tab.args + BitVec.ofNat 64 (8 * maxRes) := by
            rw [BitVec.ofInt_add]; rfl
          rw [hcast, ← BitVec.add_assoc L.T (BitVec.ofInt 64 env.tab.args),
            BitVec.add_assoc (L.T + BitVec.ofInt 64 env.tab.args), ← BitVec.ofNat_add]
          congr 2; omega
        rw [hmem10, haddr, hargWordsS j (by omega), hpadEq]
    have hstackNeed : L.stackLimit.toNat + fnFrameBytes entryFd +
        stackNeedB p b' entryFd.body { mem := m, loc := Locals.init vsPad } ≤ L.stackTop.toNat := by
      simp only [runStackNeedB, hEntry] at hStack
      rw [hlocPad]
      omega
    have hcall := compileFns_call_sim_gen env L p hpOk hpArgs hFns b'
      entry entryFd vsPad m L.stackTop (st10.getReg AbiReg.ra) argsPtr
      (lkm.totalSize pre10 + lkm.itemSize (.call (fnLabel entry)))
      hEntry hvsPadLen (by omega) hstackNeed (Nat.le_refl _) L.hTopAlign hargsAl
      (by rw [hra10]; exact mul4_and_not1 (lkm.totalSize pre10 + lkm.itemSize (.call (fnLabel entry))))
      hargsGe tgtEntry st10 hlkpEntry hpc10'
      hgp10 hsp10 rfl hs0_10 (fun _ => ht0_10) (by rw [hmem10]; exact hmS) (by rw [hmem10]; exact hhdrS) hargWords10
    let kUp : Nat := (kSave + (1 + 1 + 1 + 1 + 1)) + kBr + 1 + kLoad + lkm.totalSize trPtr + lkm.totalSize trCnt + kCall
    have hrunUp : RV64.run env.rom kUp st = .cont st10 := by
      dsimp only [kUp]
      rw [run_add, run_add, run_add, run_add, run_add, run_add, hrunPre5]
      dsimp only; rw [hrun6]; dsimp only; rw [hrun7]; dsimp only; rw [hrun7L]; dsimp only; rw [hrun8]; dsimp only; rw [hrun9]; exact hrun10
    unfold runB
    rw [hEntry]
    dsimp only
    rw [hlocPad] at hcall
    cases hx : execB p b' entryFd.body { mem := m, loc := Locals.init vs } with
    | error err =>
      rw [hx] at hcall
      cases err with
      | outOfFuel =>
        obtain ⟨kF, rF, hrunF, hpcF, hpresF, hpmF⟩ := hcall
        have hsavedF := savedWords_of_callWriteMask L entryFd.nparams L.stackTop hTabSave hpmF
          (by rw [hmem10]; exact hsavedS)
        obtain ⟨kEx, rEx, hrunEx, hpcEx, ha0Ex, ha1Ex, hrestEx, hraEx, _⟩ :=
          compileTrampoline_exhausted_sim env entry entryFd.nparams hTramp' L.T hSaveAl st rF hpcF
            (hpresF.gp.trans hgp10) hsavedF
        exact ⟨_, rEx, by rw [run_add, run_add, hrunUp]; dsimp only; rw [hrunF]; exact hrunEx,
          hpcEx, ha0Ex, ha1Ex, hrestEx, hraEx⟩
      | abort code =>
        obtain ⟨kF, rF, hrunF, hpcF, ha0F, hpresF, hpmF⟩ := hcall
        have hsavedF := savedWords_of_callWriteMask L entryFd.nparams L.stackTop hTabSave hpmF
          (by rw [hmem10]; exact hsavedS)
        obtain ⟨kAb, rAb, hrunAb, hpcAb, ha0Ab, ha1Ab, hrestAb, hraAb, _⟩ :=
          compileTrampoline_abort_sim env entry entryFd.nparams hTramp' L.T hSaveAl st rF hpcF ha0F
            (hpresF.gp.trans hgp10) hsavedF
        exact ⟨_, rAb, by rw [run_add, run_add, hrunUp]; dsimp only; rw [hrunF]; exact hrunAb,
          hpcAb, ha0Ab, ha1Ab, hrestAb, hraAb⟩
      | oob =>
        obtain ⟨kF, rF, hrunF, hpcF, hpresF, hpmF⟩ := hcall
        have hsavedF := savedWords_of_callWriteMask L entryFd.nparams L.stackTop hTabSave hpmF
          (by rw [hmem10]; exact hsavedS)
        obtain ⟨kEr, rEr, hrunEr, hpcEr, ha0Er, ha1Er, hrestEr, hraEr, _⟩ :=
          compileTrampoline_err_sim env entry entryFd.nparams hTramp' L.T hSaveAl st rF hpcF
            (hpresF.gp.trans hgp10) hsavedF
        exact ⟨_, rEr, by rw [run_add, run_add, hrunUp]; dsimp only; rw [hrunF]; exact hrunEr,
          hpcEr, ha0Er, ha1Er, hrestEr, hraEr⟩
      | noFun fn =>
        obtain ⟨kF, rF, hrunF, hpcF, hpresF, hpmF⟩ := hcall
        have hsavedF := savedWords_of_callWriteMask L entryFd.nparams L.stackTop hTabSave hpmF
          (by rw [hmem10]; exact hsavedS)
        obtain ⟨kEr, rEr, hrunEr, hpcEr, ha0Er, ha1Er, hrestEr, hraEr, _⟩ :=
          compileTrampoline_err_sim env entry entryFd.nparams hTramp' L.T hSaveAl st rF hpcF
            (hpresF.gp.trans hgp10) hsavedF
        exact ⟨_, rEr, by rw [run_add, run_add, hrunUp]; dsimp only; rw [hrunF]; exact hrunEr,
          hpcEr, ha0Er, ha1Er, hrestEr, hraEr⟩
    | ok res =>
      rcases res with ⟨sig, st', b''⟩
      rw [hx] at hcall
      dsimp only
      obtain ⟨kF, rF, hrunF, hpcF, hgpF, _, _, _, _, _, _, hmF, hhdrF, hresF, houtF⟩ := hcall
      let preA1 := pre10 ++ [Asm.call (fnLabel entry)]
      have hlinkA1 : lkm.linkSpec (preA1 ++ [Asm.addi AbiReg.a1 AbiReg.zero 0#12] ++
          (([Asm.j retRestoreLabel,
             Asm.lbl exhaustedLabel, Asm.addi AbiReg.a0 AbiReg.zero 0#12,
             Asm.addi AbiReg.a1 AbiReg.zero 1#12, Asm.j retRestoreLabel,
             Asm.lbl errLabel, Asm.addi AbiReg.a0 AbiReg.zero 0#12,
             Asm.lbl abortLabel, Asm.addi AbiReg.a1 AbiReg.zero 2#12,
             Asm.lbl retRestoreLabel] ++ trRest) ++ postT)) =
          .ok (env.code, env.labels) := by
        simpa [preA1, List.append_assoc] using hlinkCall
      have hpcF' : rF.pc = BitVec.ofNat 64 (4 * lkm.totalSize preA1) := by
        rw [hpcF]; dsimp only [preA1]
        simp only [lkm.totalSize_append, Asm.call, lkm.totalSize_singleton]
      obtain ⟨hrunA1, hpcA1, ha1_A1, hothA1, hmemA1⟩ :=
        run_aluImm_rd_step env preA1 _ .addi AbiReg.a1 AbiReg.zero 0#12 (by decide) hlinkA1 rF hpcF'
      let rA1 := stepReg rF AbiReg.a1 (evalAluImm .addi (rF.getReg AbiReg.zero) 0#12) (BitVec.ofNat 64 (4 * (lkm.totalSize preA1 + 1)))
      let preJ := preA1 ++ [Asm.addi AbiReg.a1 AbiReg.zero 0#12]
      have hpcA1' : rA1.pc = BitVec.ofNat 64 (4 * lkm.totalSize preJ) := by
        rw [hpcA1]; dsimp only [preJ]
        simp only [lkm.totalSize_append, show lkm.totalSize [Asm.addi AbiReg.a1 AbiReg.zero 0#12] = 1 from by simp only [Asm.addi, lkm.totalSize_instr]]
      let restMid :=
        [Asm.lbl exhaustedLabel, Asm.addi AbiReg.a0 AbiReg.zero 0#12,
         Asm.addi AbiReg.a1 AbiReg.zero 1#12, Asm.j retRestoreLabel,
         Asm.lbl errLabel, Asm.addi AbiReg.a0 AbiReg.zero 0#12,
         Asm.lbl abortLabel, Asm.addi AbiReg.a1 AbiReg.zero 2#12]
      have hRetLbl : lookupLabel env.labels retRestoreLabel =
          some (lkm.totalSize (preJ ++ [Asm.j retRestoreLabel] ++ restMid)) :=
        linkResolved_lbl_lm lkm (preJ ++ [Asm.j retRestoreLabel] ++ restMid) retRestoreLabel _
          (by simpa [preJ, restMid, List.append_assoc] using hlinkA1)
      have hlinkJ : lkm.linkSpec (preJ ++ [Asm.j retRestoreLabel] ++ (restMid ++ [Asm.lbl retRestoreLabel] ++ trRest ++ postT)) =
          .ok (env.code, env.labels) := by
        simpa [preJ, restMid, List.append_assoc] using hlinkA1
      have h64J : 4 * (lkm.totalSize preJ + lkm.itemSize (.j retRestoreLabel)) < 2 ^ 64 := by
        simpa [Asm.j, lkm.totalSize_singleton] using linkResolved_sub_pc64 env preJ [Asm.j retRestoreLabel] _ hlinkJ
      obtain ⟨kJ, rJ, hrunJ, hpcJ, hothJ, _, hmemJ⟩ :=
        prog_step_j env preJ (restMid ++ [Asm.lbl retRestoreLabel] ++ trRest ++ postT) retRestoreLabel _ hRetLbl hlinkJ h64J rA1 hpcA1'
      let preRest := preJ ++ [Asm.j retRestoreLabel] ++ restMid ++ [Asm.lbl retRestoreLabel]
      have hpcJ' : rJ.pc = BitVec.ofNat 64 (4 * lkm.totalSize preRest) := by
        rw [hpcJ]; dsimp only [preRest]
        simp only [lkm.totalSize_append, show lkm.totalSize [Asm.lbl retRestoreLabel] = 0 from by simp only [Asm.lbl, lkm.totalSize_label], Nat.add_zero]
      have hlinkRest : lkm.linkSpec (preRest ++ trRest ++ postT) = .ok (env.code, env.labels) := by
        simpa [preRest, List.append_assoc] using hlinkJ
      have hgpJ : rJ.getReg AbiReg.gp = L.T :=
        (hothJ _ (by decide)).trans ((hothA1 _ (by decide)).trans hgpF)
      have hmemJEq : rJ.mem = rF.mem := hmemJ.trans hmemA1
      have hsavedJ : ∀ i (hi : i < callerSaveRegs.length),
          readWord64 rJ.mem ((L.T + BitVec.ofInt 64 (env.tab.saveBase entryFd.nparams)) + BitVec.ofNat 64 (8 * i)) =
            st.getReg (callerSaveRegs[i]'hi) := by
        rw [hmemJEq]
        exact savedWords_of_callWriteMask L entryFd.nparams L.stackTop hTabSave houtF (by rw [hmem10]; exact hsavedS)
      obtain ⟨kR, rFin, hrunR, hpcR, hrestR, hraR, hothR, hmemR⟩ :=
        callerRestoreRet_sim env AbiReg.gp (by decide) (by decide) (env.tab.saveBase entryFd.nparams) L.T st hSaveAl
          preRest postT hlinkRest rJ hpcJ' hgpJ hsavedJ
      have hnresPos : 1 ≤ env.tab.nres := by
        simp only [progOkB, Bool.and_eq_true, decide_eq_true_eq] at hpOk; exact hpOk.1.1.2
      have h0min : 0 < min (min (max 1 sig.retVal.length) env.tab.nres) maxRes := by
        simp only [maxRes] at *; omega
      have ha0F' : rF.getReg AbiReg.a0 = (sig.retVal.headD 0).toBitVec := by
        have h := hresF.1 0 h0min
        change rF.getReg AbiReg.a0 = (sig.retVal.getD 0 0).toBitVec at h
        rw [h]; cases sig.retVal <;> rfl
      have ha0Eq : rFin.getReg AbiReg.a0 = (sig.retVal.headD 0).toBitVec := by
        rw [hothR AbiReg.a0 (by decide) (by decide) (by decide), hothJ _ (by decide), hothA1 _ (by decide), ha0F']
      have ha1Eq : rFin.getReg AbiReg.a1 = 0#64 := by
        rw [hothR AbiReg.a1 (by decide) (by decide) (by decide), hothJ _ (by decide), ha1_A1]
        change rF.getReg AbiReg.zero + sextImm12 0#12 = 0#64
        rw [getReg_zero]; decide
      have hmemFinEq : rFin.mem = rF.mem := hmemR.trans hmemJEq
      have hresFinReg : ∀ i, i < min (min (max 1 sig.retVal.length) env.tab.nres) maxRes → i ≠ 1 →
          rFin.getReg (resReg i) = (sig.retVal.getD i 0).toBitVec := by
        intro i hi hne1
        have hnotSave : resReg i ∉ callerSaveRegs := by
          match i with
          | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => decide
          | _ + 8 => simp [resReg]; decide
        have ha1Ne : resReg i ≠ AbiReg.a1 := by
          match i with
          | 0 => decide
          | 1 => exact absurd rfl hne1
          | 2 | 3 | 4 | 5 | 6 | 7 => decide
          | _ + 8 => simp [resReg]; decide
        have hr := resReg_ne_preserved i
        rw [hothR _ hr.2.2.2.2.2.1 hr.2.2.2.2.2.2.1 hnotSave, hothJ _ ⟨resReg_ne_t6 i, hr.2.2.2.1⟩, hothA1 _ ha1Ne]
        exact hresF.1 i hi
      have hresFinMem : ∀ i, maxRes ≤ i → i < min (max 1 sig.retVal.length) env.tab.nres →
          readWord64 rFin.mem (L.T + BitVec.ofInt 64 (env.tab.resOff i)) = (sig.retVal.getD i 0).toBitVec := by
        intro i hlo hhi
        rw [hmemFinEq]
        exact hresF.2 i hlo hhi
      exact ⟨kUp + kF + 1 + kJ + kR, rFin,
        by rw [run_add, run_add, run_add, run_add, hrunUp]; dsimp only; rw [hrunF]; dsimp only; rw [hrunA1]; dsimp only; rw [hrunJ]; exact hrunR,
        hpcR, ha0Eq, ha1Eq, hrestR, hraR,
        by rw [hmemFinEq]; exact hmF, by rw [hmemFinEq]; exact hhdrF, hresFinReg, hresFinMem⟩

theorem compileProg_sim (env : CodeEnv) (L : ProgLayout env.tab) (p : _root_.L.Prog)
    (hpOk : progOkB env.tab p = true) (hpArgs : progArgsOkB p = true)
    (hFns : ProgFnsLinked env p)
    (entry : FnName) (entryFd : FunDecl) (hEntry : p.lookup entry = some entryFd)
    (hTramp : ProgTrampLinked env entry entryFd.nparams)
    (b : Nat) (hb64 : b < 2 ^ 64)
    (vs : List _root_.L.Word) (hvslen : vs.length ≤ entryFd.nparams)
    (hTabSave : env.tab.saveBase entryFd.nparams + 128 ≤ (L.tabBytes : Int))
    (m : _root_.L.Mem)
    (hStack : L.stackLimit.toNat + runStackNeedB p b entry vs m ≤ L.stackTop.toNat)
    (enterPc : Nat) (st : State)
    (hEnterLbl : lookupLabel env.labels enterLabel = some enterPc)
    (hpc : st.pc = BitVec.ofNat 64 (4 * enterPc))
    (ha0 : st.getReg AbiReg.a0 = L.T)
    (ha1 : st.getReg AbiReg.a1 = BitVec.ofNat 64 b)
    (hm : ProgMemRel env.tab L st.mem m)
    (hhdr : TabHeaderOk L st.mem)
    (hargWords : ∀ j, j < entryFd.nparams →
      readWord64 st.mem (L.T + BitVec.ofInt 64 env.tab.args + BitVec.ofNat 64 (8 * j)) = (vs.getD j 0).toBitVec) :
    match runB p b entry vs m with
    | .ok (retVs, m', _) =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = (st.getReg AbiReg.ra &&& ~~~1#64) ∧
        r'.getReg AbiReg.a0 = (retVs.headD 0).toBitVec ∧
        r'.getReg AbiReg.a1 = 0#64 ∧
        RegsRestored st r' ∧
        r'.getReg AbiReg.ra = st.getReg AbiReg.ra ∧
        ProgMemRel env.tab L r'.mem m' ∧
        TabHeaderOk L r'.mem ∧
        (∀ i, i < min (min (max 1 retVs.length) env.tab.nres) maxRes → i ≠ 1 → r'.getReg (resReg i) = (retVs.getD i 0).toBitVec) ∧
        (∀ i, maxRes ≤ i → i < min (max 1 retVs.length) env.tab.nres →
          readWord64 r'.mem (L.T + BitVec.ofInt 64 (env.tab.resOff i)) = (retVs.getD i 0).toBitVec)
    | .error .outOfFuel =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = (st.getReg AbiReg.ra &&& ~~~1#64) ∧
        r'.getReg AbiReg.a0 = 0#64 ∧
        r'.getReg AbiReg.a1 = 1#64 ∧
        RegsRestored st r' ∧
        r'.getReg AbiReg.ra = st.getReg AbiReg.ra
    | .error (.abort code) =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = (st.getReg AbiReg.ra &&& ~~~1#64) ∧
        r'.getReg AbiReg.a0 = code.toBitVec ∧
        r'.getReg AbiReg.a1 = 2#64 ∧
        RegsRestored st r' ∧
        r'.getReg AbiReg.ra = st.getReg AbiReg.ra
    | .error _ =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = (st.getReg AbiReg.ra &&& ~~~1#64) ∧
        r'.getReg AbiReg.a0 = 0#64 ∧
        r'.getReg AbiReg.a1 = 2#64 ∧
        RegsRestored st r' ∧
        r'.getReg AbiReg.ra = st.getReg AbiReg.ra :=
  compileProg_sim_gen env.toGen L p hpOk hpArgs hFns entry entryFd hEntry hTramp
    b hb64 vs hvslen hTabSave m hStack enterPc st hEnterLbl hpc ha0 ha1 hm hhdr hargWords

theorem prog_run_sim_gen {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab) (p : _root_.L.Prog)
    (hpOk : progOkB env.tab p = true) (hpArgs : progArgsOkB p = true)
    (hFns : ProgFnsLinkedGen env p)
    (entry : FnName) (entryFd : FunDecl) (hEntry : p.lookup entry = some entryFd)
    (hTramp : ProgTrampLinkedGen env entry entryFd.nparams)
    (d : Nat) (vs : List _root_.L.Word) (hvslen : vs.length ≤ entryFd.nparams)
    (hTabSave : env.tab.saveBase entryFd.nparams + 128 ≤ (L.tabBytes : Int))
    (m : _root_.L.Mem)
    (hne : _root_.L.run p d entry vs m ≠ .error .outOfFuel)
    (extra : Nat)
    (cost : Nat) (hcost : ∀ e : Nat,
      match _root_.L.run p d entry vs m with
      | .ok (ret, m') => runB p (cost + e) entry vs m = .ok (ret, m', e)
      | .error err => runB p (cost + e) entry vs m = .error err)
    (hb64 : cost + extra < 2 ^ 64)
    (hStack : L.stackLimit.toNat + runStackNeedB p (cost + extra) entry vs m ≤ L.stackTop.toNat)
    (enterPc : Nat) (st : State)
    (hEnterLbl : lookupLabel env.labels enterLabel = some enterPc)
    (hpc : st.pc = BitVec.ofNat 64 (4 * enterPc))
    (ha0 : st.getReg AbiReg.a0 = L.T)
    (ha1 : st.getReg AbiReg.a1 = BitVec.ofNat 64 (cost + extra))
    (hm : ProgMemRel env.tab L st.mem m)
    (hhdr : TabHeaderOk L st.mem)
    (hargWords : ∀ j, j < entryFd.nparams →
      readWord64 st.mem (L.T + BitVec.ofInt 64 env.tab.args + BitVec.ofNat 64 (8 * j)) = (vs.getD j 0).toBitVec) :
    match _root_.L.run p d entry vs m with
    | .ok (retVs, m') =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = (st.getReg AbiReg.ra &&& ~~~1#64) ∧
        r'.getReg AbiReg.a0 = (retVs.headD 0).toBitVec ∧
        r'.getReg AbiReg.a1 = 0#64 ∧
        RegsRestored st r' ∧
        r'.getReg AbiReg.ra = st.getReg AbiReg.ra ∧
        ProgMemRel env.tab L r'.mem m' ∧
        TabHeaderOk L r'.mem ∧
        (∀ i, i < min (min (max 1 retVs.length) env.tab.nres) maxRes → i ≠ 1 → r'.getReg (resReg i) = (retVs.getD i 0).toBitVec) ∧
        (∀ i, maxRes ≤ i → i < min (max 1 retVs.length) env.tab.nres →
          readWord64 r'.mem (L.T + BitVec.ofInt 64 (env.tab.resOff i)) = (retVs.getD i 0).toBitVec)
    | .error (.abort code) =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = (st.getReg AbiReg.ra &&& ~~~1#64) ∧
        r'.getReg AbiReg.a0 = code.toBitVec ∧
        r'.getReg AbiReg.a1 = 2#64 ∧
        RegsRestored st r' ∧
        r'.getReg AbiReg.ra = st.getReg AbiReg.ra
    | .error _ =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = (st.getReg AbiReg.ra &&& ~~~1#64) ∧
        r'.getReg AbiReg.a0 = 0#64 ∧
        r'.getReg AbiReg.a1 = 2#64 ∧
        RegsRestored st r' ∧
        r'.getReg AbiReg.ra = st.getReg AbiReg.ra := by
  have hsim := compileProg_sim_gen env L p hpOk hpArgs hFns entry entryFd hEntry hTramp
    (cost + extra) hb64 vs hvslen hTabSave m hStack enterPc st hEnterLbl hpc ha0 ha1 hm hhdr hargWords
  have hc := hcost extra
  cases hrun : _root_.L.run p d entry vs m with
  | ok res =>
    rcases res with ⟨retVs, m'⟩
    rw [hrun] at hc
    rw [hc] at hsim
    exact hsim
  | error err =>
    rw [hrun] at hc hne
    rw [hc] at hsim
    cases err with
    | outOfFuel => exact False.elim (hne rfl)
    | abort code => exact hsim
    | oob => exact hsim
    | noFun fn => exact hsim

theorem progExecB_step (env : CodeEnv) (L : ProgLayout env.tab) (p : _root_.L.Prog)
    (hpOk : progOkB env.tab p = true)
    (hpArgs : progArgsOkB p = true)
    (hFns : ProgFnsLinked env p) :
    ∀ (b : Nat) (s : _root_.L.Stmt),
      (∀ b', b' < b → FnCallSimGenCallee env.toGen L p b') →
      ∀ (fl : FrameLayout), FrameLayoutOk fl →
      ∀ (tco : TcoCtx) (lm : _root_.L.Mem) (loc : _root_.L.Locals)
        (sp : BitVec 64) (pfx : String) (lblId : Nat)
        (brkLbl : Option String) (retLbl : String) (retPc : Nat) (isTail : Bool)
        (pre post : List AsmItem),
        stmtOkB env.tab p fl.nlocals brkLbl.isSome s = true →
        stmtArgsOkB p s = true →
        StmtVarsInFrame fl s →
        usedTempsStmtR fl.isLeaf fl.alloc s ≤ fl.usedTemps →
        (fl.isLeaf = true → stmtHasCall s = false) →
        (∀ y ry, fl.alloc.lookup y = some ry →
          (stmtVarSafe y (fun x => (x != y) && (fl.alloc.lookup x == some ry))
            (!fl.isLeaf && (ry ∈ leafExtraBank)) s false false).2 = true) →
        (fl.isLeaf = false → stmtCallResValid fl.alloc s = true) →
        (fl.useT5Gp = true → stmtHasCopyScan s = false) →
        (stmtHasAbort0 s = true → Abort0StubOk env.toGen pfx) →
        b < 2 ^ 64 →
        isAligned sp 8 = true →
        L.stackLimit.toNat + stackNeedB p b s { mem := lm, loc := loc } ≤ sp.toNat →
        sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat →
        lookupLabel env.labels retLbl = some retPc →
        (∀ tgt, brkLbl = some tgt → ∃ tgtPc, lookupLabel env.labels tgt = some tgtPc) →
        (isTail = true → totalWords pre + totalWords (compileSR env.tab fl pfx lblId brkLbl retLbl isTail s).1 = retPc) →
        linkResolved (pre ++ (compileSR env.tab fl pfx lblId brkLbl retLbl isTail s).1 ++ post) =
          .ok (env.code, env.labels) →
        ∀ st : State,
          st.pc = BitVec.ofNat 64 (4 * totalWords pre) →
          st.getReg AbiReg.gp = L.T →
          T5GpOk L fl st →
          st.getReg AbiReg.sp = sp →
          st.getReg AbiReg.s0 = BitVec.ofNat 64 b →
          ProgMemRel env.tab L st.mem lm →
          ProgFrameOkR L fl sp st loc →
          TabHeaderOk L st.mem →
          TcoStateOk fl sp tco st →
          StmtOutcomeR env.toGen L fl sp b st retLbl brkLbl
            (totalWords pre + totalWords (compileSR env.tab fl pfx lblId brkLbl retLbl isTail s).1)
            (fun _ => false) (fun _ => false) tco
            (execB p b s { mem := lm, loc := loc }) := by
  intro b s hcall fl hfl tco lm loc sp pfx lblId brkLbl retLbl retPc isTail pre post
    hsOk hsArgs hVf hTmp hLeaf hSafe hCallRes hCopyScan habort0 hb64 hal hlim htop hretLbl hbrkLbl hTail hlink
    st hpc hgp ht5 hsp hs0 hm hf hhdr htco
  rw [← near_totalSize_eq, ← near_totalSize_eq]
  exact progExecB_step_gen env.toGen L p hpOk hpArgs hFns b s hcall fl hfl tco lm loc
    sp pfx lblId brkLbl retLbl retPc isTail pre post hsOk hsArgs hVf hTmp hLeaf hSafe hCallRes hCopyScan habort0 hb64 hal hlim htop hretLbl hbrkLbl
    (by simpa [CodeEnv.toGen, near_totalSize_eq] using hTail) hlink st (by simpa [near_totalSize_eq] using hpc) hgp ht5 hsp hs0 hm hf hhdr htco

theorem prog_run_sim (env : CodeEnv) (L : ProgLayout env.tab) (p : _root_.L.Prog)
    (hpOk : progOkB env.tab p = true) (hpArgs : progArgsOkB p = true)
    (hFns : ProgFnsLinked env p)
    (entry : FnName) (entryFd : FunDecl) (hEntry : p.lookup entry = some entryFd)
    (hTramp : ProgTrampLinked env entry entryFd.nparams)
    (d : Nat) (vs : List _root_.L.Word) (hvslen : vs.length ≤ entryFd.nparams)
    (hTabSave : env.tab.saveBase entryFd.nparams + 128 ≤ (L.tabBytes : Int))
    (m : _root_.L.Mem)
    (hne : _root_.L.run p d entry vs m ≠ .error .outOfFuel)
    (extra : Nat)
    (cost : Nat) (hcost : ∀ e : Nat,
      match _root_.L.run p d entry vs m with
      | .ok (ret, m') => runB p (cost + e) entry vs m = .ok (ret, m', e)
      | .error err => runB p (cost + e) entry vs m = .error err)
    (hb64 : cost + extra < 2 ^ 64)
    (hStack : L.stackLimit.toNat + runStackNeedB p (cost + extra) entry vs m ≤ L.stackTop.toNat)
    (enterPc : Nat) (st : State)
    (hEnterLbl : lookupLabel env.labels enterLabel = some enterPc)
    (hpc : st.pc = BitVec.ofNat 64 (4 * enterPc))
    (ha0 : st.getReg AbiReg.a0 = L.T)
    (ha1 : st.getReg AbiReg.a1 = BitVec.ofNat 64 (cost + extra))
    (hm : ProgMemRel env.tab L st.mem m)
    (hhdr : TabHeaderOk L st.mem)
    (hargWords : ∀ j, j < entryFd.nparams →
      readWord64 st.mem (L.T + BitVec.ofInt 64 env.tab.args + BitVec.ofNat 64 (8 * j)) = (vs.getD j 0).toBitVec) :
    match _root_.L.run p d entry vs m with
    | .ok (retVs, m') =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = (st.getReg AbiReg.ra &&& ~~~1#64) ∧
        r'.getReg AbiReg.a0 = (retVs.headD 0).toBitVec ∧
        r'.getReg AbiReg.a1 = 0#64 ∧
        RegsRestored st r' ∧
        r'.getReg AbiReg.ra = st.getReg AbiReg.ra ∧
        ProgMemRel env.tab L r'.mem m' ∧
        TabHeaderOk L r'.mem ∧
        (∀ i, i < min (min (max 1 retVs.length) env.tab.nres) maxRes → i ≠ 1 → r'.getReg (resReg i) = (retVs.getD i 0).toBitVec) ∧
        (∀ i, maxRes ≤ i → i < min (max 1 retVs.length) env.tab.nres →
          readWord64 r'.mem (L.T + BitVec.ofInt 64 (env.tab.resOff i)) = (retVs.getD i 0).toBitVec)
    | .error (.abort code) =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = (st.getReg AbiReg.ra &&& ~~~1#64) ∧
        r'.getReg AbiReg.a0 = code.toBitVec ∧
        r'.getReg AbiReg.a1 = 2#64 ∧
        RegsRestored st r' ∧
        r'.getReg AbiReg.ra = st.getReg AbiReg.ra
    | .error _ =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = (st.getReg AbiReg.ra &&& ~~~1#64) ∧
        r'.getReg AbiReg.a0 = 0#64 ∧
        r'.getReg AbiReg.a1 = 2#64 ∧
        RegsRestored st r' ∧
        r'.getReg AbiReg.ra = st.getReg AbiReg.ra :=
  prog_run_sim_gen env.toGen L p hpOk hpArgs hFns entry entryFd hEntry hTramp
    d vs hvslen hTabSave m hne extra cost hcost hb64 hStack enterPc st hEnterLbl hpc ha0 ha1 hm hhdr hargWords

/--
info: 'ConAgua.RISCV.Compiler.progExecB_step_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms progExecB_step_gen

/--
info: 'ConAgua.RISCV.Compiler.progExecB_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms progExecB_step

/--
info: 'ConAgua.RISCV.Compiler.compileFns_call_sim_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms compileFns_call_sim_gen

/--
info: 'ConAgua.RISCV.Compiler.compileFns_call_sim' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms compileFns_call_sim

/--
info: 'ConAgua.RISCV.Compiler.compileProg_sim_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms compileProg_sim_gen

/--
info: 'ConAgua.RISCV.Compiler.compileProg_sim' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms compileProg_sim

/--
info: 'ConAgua.RISCV.Compiler.prog_run_sim_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms prog_run_sim_gen

/--
info: 'ConAgua.RISCV.Compiler.prog_run_sim' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms prog_run_sim

end ConAgua.RISCV.Compiler
