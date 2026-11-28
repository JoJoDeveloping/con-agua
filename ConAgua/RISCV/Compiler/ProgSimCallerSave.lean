import ConAgua.RISCV.Compiler.ProgSimFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Program-Level Forward Simulation: LP64 Caller-Save / Restore (`ConAgua.RISCV.Compiler.ProgSimCallerSave`)

LP64 caller-save / restore simulation helpers (`callerSave_sim`, `callerRestoreRet_sim`,
`saveArea_not_callWriteMask`).

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard Lean axioms only.
-/

namespace ConAgua.RISCV.Compiler

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Linker

/-! ## 4b. LP64 Caller-Save / Restore Helpers (`callerSave_sim`, `callerRestoreRet_sim`, `saveArea_not_callWriteMask`) -/

/-- Memory span `[T + saveOff, T + saveOff + 128)` used by `callerSaveAsm` / `callerRestoreRetAsm`. -/
def callerSaveSpan (T : BitVec 64) (saveOff : Int) : MemSpan :=
  ⟨T + BitVec.ofInt 64 saveOff, 128⟩

private theorem step_sd_off_all {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (rs1 rs2 : Reg) (imm : BitVec 12)
    (hlink : lkm.linkSpec (pre ++ [Asm.sd rs1 rs2 imm] ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + 1) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hal : isAligned (st.getReg rs1 + sextImm12 imm) 8 = true) :
    let st' := { st with pc := BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)),
                         mem := writeWord64 st.mem (st.getReg rs1 + sextImm12 imm) (st.getReg rs2) }
    RV64.run env.rom 1 st = .cont st' ∧
    st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)) ∧
    (∀ q, st'.getReg q = st.getReg q) ∧
    st'.mem = writeWord64 st.mem (st.getReg rs1 + sextImm12 imm) (st.getReg rs2) := by
  have hs := step_item_instr_lm lkm env.hrom pre post (.store .sd rs1 rs2 imm)
    (by simpa [Asm.sd] using hlink) (by omega) st hpc
  have hrun : RV64.run env.rom 1 st = .cont
      { st with pc := BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)),
                mem := writeWord64 st.mem (st.getReg rs1 + sextImm12 imm) (st.getReg rs2) } := by
    apply run_one_cont; rw [hs]
    simp only [execInstr, hal, ↓reduceIte, pc_add_4_ofNat st.pc hpc]
  exact ⟨hrun, rfl, fun _ => rfl, rfl⟩

private theorem callerSaveLoop_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (baseAddr : BitVec 64) (halign : isAligned baseAddr 8 = true)
    (hvalid : baseAddr.toNat + 128 ≤ 2 ^ 64) :
    ∀ (regs : List Reg) (start : Nat),
      start + regs.length ≤ 16 →
      (∀ r ∈ regs, r ≠ AbiReg.t0) →
      ∀ (pre post : List AsmItem),
        lkm.linkSpec (pre ++ ((regs.zipIdx start).map fun (r, i) =>
          Asm.sd AbiReg.t0 r (BitVec.ofNat 12 (8 * i))) ++ post) = .ok (env.code, env.labels) →
        ∀ (st : State),
          st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
          st.getReg AbiReg.t0 = baseAddr →
          ∃ k st',
            RV64.run env.rom k st = .cont st' ∧
            st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre +
              lkm.totalSize ((regs.zipIdx start).map fun (r, i) =>
                Asm.sd AbiReg.t0 r (BitVec.ofNat 12 (8 * i))))) ∧
            (∀ q, st'.getReg q = st.getReg q) ∧
            MemEqOutside ⟨baseAddr + BitVec.ofNat 64 (8 * start), 8 * regs.length⟩ st.mem st'.mem ∧
            ∀ i (hi : i < regs.length),
              readWord64 st'.mem (baseAddr + BitVec.ofNat 64 (8 * (start + i))) =
                st.getReg (regs[i]'hi) := by
  intro regs
  induction regs with
  | nil =>
    intro start _ _ pre post _ st hpc _
    exact ⟨0, st, rfl, by simp [lkm.totalSize_nil, hpc], fun _ => rfl, MemEqOutside.refl _ _,
      fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | cons r rest ih =>
    intro start hle hnotT0 pre post hlink st hpc ht0
    have hsplit : ((r :: rest).zipIdx start).map (fun (q, i) => Asm.sd AbiReg.t0 q (BitVec.ofNat 12 (8 * i))) =
        [Asm.sd AbiReg.t0 r (BitVec.ofNat 12 (8 * start))] ++
        (rest.zipIdx (start + 1)).map (fun (q, i) => Asm.sd AbiReg.t0 q (BitVec.ofNat 12 (8 * i))) := by
      simp [List.zipIdx_cons]
    rw [hsplit] at hlink ⊢
    have ⟨hl1, hl2⟩ := linkResolved_mid_split lkm pre _ _ post hlink
    have hpc64 := linkResolved_sub_pc64 env pre _ _ hl1
    have htw1 : lkm.totalSize [Asm.sd AbiReg.t0 r (BitVec.ofNat 12 (8 * start))] = 1 := by
      simp only [Asm.sd, lkm.totalSize_instr]
    have hlt64 : 4 * (lkm.totalSize pre + 1) < 2 ^ 64 := by rw [htw1] at hpc64; exact hpc64
    simp only [List.length_cons] at hle
    have himm : sextImm12 (BitVec.ofNat 12 (8 * start)) = BitVec.ofNat 64 (8 * start) :=
      sextImm12_of_lt2048_nat (8 * start) (by omega)
    have halS : isAligned (st.getReg AbiReg.t0 + sextImm12 (BitVec.ofNat 12 (8 * start))) 8 = true := by
      rw [ht0, himm]; exact isAligned8_add_mul8 baseAddr halign start
    obtain ⟨hrun1, hpc1, hreg1, hmem1⟩ :=
      step_sd_off_all env pre _ AbiReg.t0 r (BitVec.ofNat 12 (8 * start)) hl1 hlt64 st hpc halS
    let st1 := { st with pc := BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)),
                         mem := writeWord64 st.mem (st.getReg AbiReg.t0 + sextImm12 (BitVec.ofNat 12 (8 * start))) (st.getReg r) }
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ [Asm.sd AbiReg.t0 r (BitVec.ofNat 12 (8 * start))])) := by
      rw [hpc1, lkm.totalSize_append, htw1]
    have ht0_1 : st1.getReg AbiReg.t0 = baseAddr := (hreg1 _).trans ht0
    have hmem1' : st1.mem = writeWord64 st.mem (baseAddr + BitVec.ofNat 64 (8 * start)) (st.getReg r) := by
      rw [hmem1, ht0, himm]
    have hout1 : MemEqOutside ⟨baseAddr + BitVec.ofNat 64 (8 * start), 8 * (rest.length + 1)⟩ st.mem st1.mem := by
      rw [hmem1']
      exact MemEqOutside.writeWord64 st.mem _ _ fun k hk =>
        ⟨k, by dsimp only; omega, rfl⟩
    obtain ⟨k2, st2, hrun2, hpc2, hreg2, hout2, hsaved2⟩ :=
      ih (start + 1) (by omega) (fun q hq => hnotT0 q (List.mem_cons_of_mem _ hq))
        (pre ++ [Asm.sd AbiReg.t0 r (BitVec.ofNat 12 (8 * start))]) post hl2 st1 hpc1' ht0_1
    have hout2Wide : MemEqOutside ⟨baseAddr + BitVec.ofNat 64 (8 * start), 8 * (rest.length + 1)⟩ st1.mem st2.mem := by
      intro a ha
      apply hout2 a
      intro ⟨k, hk, hka⟩
      apply ha
      refine ⟨8 + k, by dsimp only at hk ⊢; omega, ?_⟩
      rw [hka, show 8 * (start + 1) = 8 * start + 8 from by omega, BitVec.ofNat_add,
        ← BitVec.add_assoc baseAddr, BitVec.add_assoc (baseAddr + BitVec.ofNat 64 (8 * start)), ← BitVec.ofNat_add]
    refine ⟨1 + k2, st2, by rw [run_add, hrun1]; exact hrun2,
      by simpa [lkm.totalSize_append, Nat.add_assoc] using hpc2,
      fun q => (hreg2 q).trans (hreg1 q),
      hout1.trans hout2Wide, ?_⟩
    intro i hi
    cases i with
    | zero =>
      simp only [Nat.add_zero, List.getElem_cons_zero]
      have hdisj0 : ∀ k, k < 8 →
          ¬MemSpan.contains ⟨baseAddr + BitVec.ofNat 64 (8 * (start + 1)), 8 * rest.length⟩
            (baseAddr + BitVec.ofNat 64 (8 * start) + BitVec.ofNat 64 k) := by
        intro k hk ⟨j, hj, hka⟩
        have hnat := congrArg BitVec.toNat hka
        have h8s : 8 * start + k < 128 := by omega
        have h8n : 8 * (start + 1) + j < 128 := by dsimp only at hj; omega
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add,
          BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hnat
        omega
      rw [MemEqOutside.readWord64_eq hout2 _ hdisj0, hmem1', readWord64_writeWord64_self]
    | succ i' =>
      simp only [List.getElem_cons_succ]
      rw [show start + (i' + 1) = (start + 1) + i' from by omega, hsaved2 i' (by simpa using hi), hreg1]

/-- Simulation of `callerSaveAsm`: saves all 16 `callerSaveRegs` into
    `callerSaveSpan T saveOff = [T + saveOff, T + saveOff + 128)` while modifying only `t0`, `t1`,
    and memory inside `callerSaveSpan T saveOff`. -/
theorem callerSave_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (base : Reg) (hbaseT1 : base ≠ AbiReg.t1) (hbase0 : base ≠ AbiReg.zero)
    (saveOff : Int) (T : BitVec 64)
    (halign : isAligned (T + BitVec.ofInt 64 saveOff) 8 = true)
    (hvalid : (T + BitVec.ofInt 64 saveOff).toNat + 128 ≤ 2 ^ 64)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ callerSaveAsm base saveOff ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hbase : st.getReg base = T) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (callerSaveAsm base saveOff))) ∧
      (∀ r, r ≠ AbiReg.t0 → r ≠ AbiReg.t1 → st'.getReg r = st.getReg r) ∧
      (∀ i (hi : i < callerSaveRegs.length),
        readWord64 st'.mem (T + BitVec.ofInt 64 saveOff + BitVec.ofNat 64 (8 * i)) =
          st.getReg (callerSaveRegs[i]'hi)) ∧
      MemEqOutside (callerSaveSpan T saveOff) st.mem st'.mem := by
  have _ := hbase0
  let cAddr := addImmOff AbiReg.t0 base AbiReg.t1 saveOff
  let cStores := (callerSaveRegs.zipIdx).map fun (r, i) => Asm.sd AbiReg.t0 r (BitVec.ofNat 12 (8 * i))
  have hcEq : callerSaveAsm base saveOff = cAddr ++ cStores := rfl
  rw [hcEq] at hlink ⊢
  have ⟨hl1, hl2⟩ := linkResolved_mid_split lkm pre cAddr cStores post hlink
  obtain ⟨st0, hrun0, hoth0, ht0_0, hmem0, hpc0⟩ :=
    addImmOff_correct_lm lkm env.hrom pre (cStores ++ post) AbiReg.t0 base AbiReg.t1
      (by decide) (by decide) hbaseT1.symm saveOff hl1 (linkResolved_sub_pc64 env pre cAddr _ hl1) st hpc
  have ht0Val : st0.getReg AbiReg.t0 = T + BitVec.ofInt 64 saveOff := by rw [ht0_0, hbase]
  obtain ⟨kL, st1, hrun1, hpc1, hreg1, hout1, hsaved1⟩ :=
    callerSaveLoop_sim env (T + BitVec.ofInt 64 saveOff) halign hvalid callerSaveRegs 0
      (by decide) (by decide) (pre ++ cAddr) post hl2 st0
      (by simpa [lkm.totalSize_append] using hpc0) ht0Val
  have hnotT01 : ∀ r ∈ callerSaveRegs, r ≠ AbiReg.t0 ∧ r ≠ AbiReg.t1 := by decide
  have houtSpan : MemEqOutside (callerSaveSpan T saveOff) st.mem st1.mem := by
    rw [← hmem0]
    simpa [callerSaveSpan, show callerSaveRegs.length = 16 from rfl] using hout1
  refine ⟨lkm.totalSize cAddr + kL, st1, by rw [run_add, hrun0]; exact hrun1,
    by simpa [lkm.totalSize_append, Nat.add_assoc] using hpc1,
    fun r h0 h1 => (hreg1 r).trans (hoth0 r h0 h1), ?_, houtSpan⟩
  intro i hi
  have hs := hsaved1 i hi
  simp only [Nat.zero_add] at hs
  rw [hs]
  have hne := hnotT01 (callerSaveRegs[i]'hi) (List.getElem_mem hi)
  exact hoth0 _ hne.1 hne.2

private theorem callerRestoreLoop_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (baseAddr : BitVec 64) (halign : isAligned baseAddr 8 = true) :
    ∀ (regs : List Reg) (start : Nat),
      start + regs.length ≤ 16 →
      regs.Nodup →
      (∀ r ∈ regs, r ≠ 0#5 ∧ r ≠ AbiReg.t0) →
      ∀ (pre post : List AsmItem),
        lkm.linkSpec (pre ++ ((regs.zipIdx start).map fun (r, i) =>
          Asm.ld r AbiReg.t0 (BitVec.ofNat 12 (8 * i))) ++ post) = .ok (env.code, env.labels) →
        ∀ (st : State),
          st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
          st.getReg AbiReg.t0 = baseAddr →
          ∃ k st',
            RV64.run env.rom k st = .cont st' ∧
            st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre +
              lkm.totalSize ((regs.zipIdx start).map fun (r, i) =>
                Asm.ld r AbiReg.t0 (BitVec.ofNat 12 (8 * i))))) ∧
            st'.mem = st.mem ∧
            (∀ q, q ∉ regs → st'.getReg q = st.getReg q) ∧
            ∀ i (hi : i < regs.length),
              st'.getReg (regs[i]'hi) = readWord64 st.mem (baseAddr + BitVec.ofNat 64 (8 * (start + i))) := by
  intro regs
  induction regs with
  | nil =>
    intro start _ _ _ pre post _ st hpc _
    exact ⟨0, st, rfl, by simp [lkm.totalSize_nil, hpc], rfl, fun _ _ => rfl,
      fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | cons r rest ih =>
    intro start hle hnd hne pre post hlink st hpc ht0
    rw [List.nodup_cons] at hnd
    have hsplit : ((r :: rest).zipIdx start).map (fun (q, i) => Asm.ld q AbiReg.t0 (BitVec.ofNat 12 (8 * i))) =
        [Asm.ld r AbiReg.t0 (BitVec.ofNat 12 (8 * start))] ++
        (rest.zipIdx (start + 1)).map (fun (q, i) => Asm.ld q AbiReg.t0 (BitVec.ofNat 12 (8 * i))) := by
      simp [List.zipIdx_cons]
    rw [hsplit] at hlink ⊢
    have ⟨hl1, hl2⟩ := linkResolved_mid_split lkm pre _ _ post hlink
    have hpc64 := linkResolved_sub_pc64 env pre _ _ hl1
    have htw1 : lkm.totalSize [Asm.ld r AbiReg.t0 (BitVec.ofNat 12 (8 * start))] = 1 := by
      simp only [Asm.ld, lkm.totalSize_instr]
    have hlt64 : 4 * (lkm.totalSize pre + 1) < 2 ^ 64 := by rw [htw1] at hpc64; exact hpc64
    simp only [List.length_cons] at hle
    have hr := hne r List.mem_cons_self
    have himm : sextImm12 (BitVec.ofNat 12 (8 * start)) = BitVec.ofNat 64 (8 * start) :=
      sextImm12_of_lt2048_nat (8 * start) (by omega)
    have halL : isAligned (st.getReg AbiReg.t0 + sextImm12 (BitVec.ofNat 12 (8 * start))) 8 = true := by
      rw [ht0, himm]; exact isAligned8_add_mul8 baseAddr halign start
    obtain ⟨hrun1, hpc1, hr1, hoth1, hmem1⟩ :=
      step_ld_off env pre _ r AbiReg.t0 (BitVec.ofNat 12 (8 * start)) hr.1
        (by simpa [Asm.raw, Asm.ld] using hl1) hlt64 st hpc halL
    let st1 := stepReg st r (readWord64 st.mem (st.getReg AbiReg.t0 + sextImm12 (BitVec.ofNat 12 (8 * start))))
      (st.pc + 4#64)
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ [Asm.ld r AbiReg.t0 (BitVec.ofNat 12 (8 * start))])) := by
      rw [hpc1, lkm.totalSize_append, htw1]
    have ht0_1 : st1.getReg AbiReg.t0 = baseAddr := (hoth1 _ hr.2.symm).trans ht0
    obtain ⟨k2, st2, hrun2, hpc2, hmem2, hoth2, hrest2⟩ :=
      ih (start + 1) (by omega) hnd.2 (fun q hq => hne q (List.mem_cons_of_mem _ hq))
        (pre ++ [Asm.ld r AbiReg.t0 (BitVec.ofNat 12 (8 * start))]) post hl2 st1 hpc1' ht0_1
    refine ⟨1 + k2, st2, by rw [run_add, hrun1]; exact hrun2,
      by simpa [lkm.totalSize_append, Nat.add_assoc] using hpc2,
      hmem2.trans hmem1,
      fun q hq => (hoth2 q (fun h => hq (List.mem_cons_of_mem _ h))).trans
        (hoth1 q (fun h => hq (h ▸ List.mem_cons_self))),
      ?_⟩
    intro i hi
    cases i with
    | zero =>
      simp only [Nat.add_zero, List.getElem_cons_zero]
      rw [hoth2 r hnd.1, hr1, ht0, himm]
    | succ i' =>
      simp only [List.getElem_cons_succ]
      rw [show start + (i' + 1) = (start + 1) + i' from by omega, hrest2 i' (by simpa using hi), hmem1]

private theorem callerRestoreRet_full_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (base : Reg) (hbaseT1 : base ≠ AbiReg.t1) (hbase0 : base ≠ AbiReg.zero)
    (T : BitVec 64) (saveOff : Int)
    (halign : isAligned (T + BitVec.ofInt 64 saveOff) 8 = true)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ callerRestoreRetAsm base saveOff ++ post) = .ok (env.code, env.labels))
    (st initSt : State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hbase : st.getReg base = T)
    (hsaved : ∀ i (hi : i < callerSaveRegs.length),
      readWord64 st.mem ((T + BitVec.ofInt 64 saveOff) + BitVec.ofNat 64 (8 * i)) =
        initSt.getReg (callerSaveRegs[i]'hi)) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64) ∧
      st'.getReg AbiReg.a0 = st.getReg AbiReg.a0 ∧
      st'.getReg AbiReg.a1 = st.getReg AbiReg.a1 ∧
      (∀ r, r ∉ callerSaveRegs → r ≠ AbiReg.t0 → r ≠ AbiReg.t1 → st'.getReg r = st.getReg r) ∧
      RegsRestored initSt st' ∧
      st'.getReg AbiReg.ra = initSt.getReg AbiReg.ra ∧
      st'.mem = st.mem := by
  have _ := hbase0
  let cAddr := addImmOff AbiReg.t0 base AbiReg.t1 saveOff
  let cLoads := (callerSaveRegs.zipIdx).map fun (r, i) => Asm.ld r AbiReg.t0 (BitVec.ofNat 12 (8 * i))
  have hcEq : callerRestoreRetAsm base saveOff = cAddr ++ cLoads ++ [Asm.ret] := rfl
  rw [hcEq] at hlink
  have hlink1 : lkm.linkSpec (pre ++ cAddr ++ (cLoads ++ [Asm.ret] ++ post)) = .ok (env.code, env.labels) := by
    simpa [List.append_assoc] using hlink
  obtain ⟨st0, hrun0, hoth0, ht0_0, hmem0, hpc0⟩ :=
    addImmOff_correct_lm lkm env.hrom pre (cLoads ++ [Asm.ret] ++ post) AbiReg.t0 base AbiReg.t1
      (by decide) (by decide) hbaseT1.symm saveOff hlink1 (linkResolved_sub_pc64 env pre cAddr _ hlink1) st hpc
  have ht0Val : st0.getReg AbiReg.t0 = T + BitVec.ofInt 64 saveOff := by rw [ht0_0, hbase]
  let pre1 := pre ++ cAddr
  have hlink2 : lkm.linkSpec (pre1 ++ cLoads ++ ([Asm.ret] ++ post)) = .ok (env.code, env.labels) := by
    simpa [pre1, List.append_assoc] using hlink1
  obtain ⟨kL, st1, hrun1, hpc1, hmem1, hoth1, hrest1⟩ :=
    callerRestoreLoop_sim env (T + BitVec.ofInt 64 saveOff) halign callerSaveRegs 0
      (by decide) (by decide) (by decide) pre1 ([Asm.ret] ++ post) hlink2 st0
      (by simpa [pre1, lkm.totalSize_append] using hpc0) ht0Val
  let pre2 := pre1 ++ cLoads
  have hlink3 : lkm.linkSpec (pre2 ++ [Asm.ret] ++ post) = .ok (env.code, env.labels) := by
    simpa [pre2, List.append_assoc] using hlink2
  have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) := by
    simpa [pre2, lkm.totalSize_append] using hpc1
  have hpcRet64 := linkResolved_sub_pc64 env pre2 [Asm.ret] post hlink3
  have htwRet : lkm.totalSize [Asm.ret] = 1 := by simp only [Asm.ret, lkm.totalSize_instr]
  have hltRet64 : 4 * lkm.totalSize pre2 < 2 ^ 64 := by rw [htwRet] at hpcRet64; omega
  have hstepRet := step_item_ret_lm lkm env.hrom pre2 post hlink3 hltRet64 st1 hpc1'
  let st2 : State := { st1 with pc := st1.getReg AbiReg.ra &&& ~~~1#64 }
  have hrunRet : RV64.run env.rom 1 st1 = .cont st2 := run_one_cont _ _ _ hstepRet
  have hra1 : st1.getReg AbiReg.ra = initSt.getReg AbiReg.ra := by
    have h1 : (1 : Nat) < callerSaveRegs.length := by decide
    have hraIdx : callerSaveRegs[1] = AbiReg.ra := rfl
    rw [← hraIdx, hrest1 1 h1, Nat.zero_add, hmem0, hsaved 1 h1]
  have hcalSub : ∀ r ∈ lp64CalleeSaved, r ∈ callerSaveRegs := by decide
  have hrestored2 : RegsRestored initSt st2 := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (hcalSub r hr)
    change st1.getReg (callerSaveRegs[i]'hi) = initSt.getReg (callerSaveRegs[i]'hi)
    rw [hrest1 i hi, Nat.zero_add, hmem0, hsaved i hi]
  refine ⟨lkm.totalSize cAddr + kL + 1, st2,
    by rw [run_add, run_add, hrun0]; dsimp only; rw [hrun1]; exact hrunRet,
    by change st1.getReg AbiReg.ra &&& ~~~1#64 = _; rw [hra1],
    by change st1.getReg AbiReg.a0 = _; rw [hoth1 _ (by decide), hoth0 _ (by decide) (by decide)],
    by change st1.getReg AbiReg.a1 = _; rw [hoth1 _ (by decide), hoth0 _ (by decide) (by decide)],
    fun r hr h0 h1 => by change st1.getReg r = _; rw [hoth1 r hr, hoth0 r h0 h1],
    hrestored2, hra1, hmem1.trans hmem0⟩

/-- Simulation of `callerRestoreRetAsm`: restores all 16 `callerSaveRegs` from
    `[T + saveOff, T + saveOff + 128)`, leaves all non-temp non-saved registers (`a0..a7`, etc.)
    and memory untouched, and jumps to `initSt.getReg AbiReg.ra &&& ~~~1#64` via `Asm.ret`. -/
theorem callerRestoreRet_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (base : Reg) (hbaseT1 : base ≠ AbiReg.t1) (hbase0 : base ≠ AbiReg.zero)
    (saveOff : Int) (T : BitVec 64) (initSt : State)
    (halign : isAligned (T + BitVec.ofInt 64 saveOff) 8 = true)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ callerRestoreRetAsm base saveOff ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hbase : st.getReg base = T)
    (hsaved : ∀ i (hi : i < callerSaveRegs.length),
      readWord64 st.mem (T + BitVec.ofInt 64 saveOff + BitVec.ofNat 64 (8 * i)) =
        initSt.getReg (callerSaveRegs[i]'hi)) :
    ∃ k r',
      RV64.run env.rom k st = .cont r' ∧
      r'.pc = (initSt.getReg AbiReg.ra &&& ~~~1#64) ∧
      RegsRestored initSt r' ∧
      r'.getReg AbiReg.ra = initSt.getReg AbiReg.ra ∧
      (∀ r, r ≠ AbiReg.t0 → r ≠ AbiReg.t1 → r ∉ callerSaveRegs → r'.getReg r = st.getReg r) ∧
      r'.mem = st.mem := by
  obtain ⟨k, st', hrun, hpc', _, _, hoth, hrestored, hra, hmem⟩ :=
    callerRestoreRet_full_sim env base hbaseT1 hbase0 T saveOff halign pre post hlink st initSt hpc hbase hsaved
  exact ⟨k, st', hrun, hpc', hrestored, hra, fun r h0 h1 hr => hoth r hr h0 h1, hmem⟩

theorem callerSaveBase_align {tab : Tab} (L : ProgLayout tab) (entryNparams : Nat) :
    isAligned (L.T + BitVec.ofInt 64 (tab.saveBase entryNparams)) 8 = true := by
  have hcast : tab.saveBase entryNparams =
      ((8 * ((2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres + tab.ng + max 1 entryNparams : Nat) : Int))) := by
    simp only [Tab.saveBase, Tab.args, Tab.globBase, Tab.resBase, Tab.romBase, Int.ofNat_eq_natCast]
    omega
  rw [hcast]
  exact isAligned8_add_int_mul8 L.T L.hTAlign _

theorem callerSaveBase_nonneg (tab : Tab) (entryNparams : Nat) :
    0 ≤ tab.saveBase entryNparams := by
  simp only [Tab.saveBase, Tab.args, Tab.globBase, Tab.resBase, Tab.romBase, Int.ofNat_eq_natCast]
  omega

theorem callerSaveBase_valid {tab : Tab} (L : ProgLayout tab) (entryNparams : Nat)
    (hTabSave : tab.saveBase entryNparams + 128 ≤ (L.tabBytes : Int)) :
    (L.T + BitVec.ofInt 64 (tab.saveBase entryNparams)).toNat + 128 ≤ 2 ^ 64 := by
  have hnn := callerSaveBase_nonneg tab entryNparams
  have hcoe : ((tab.saveBase entryNparams).toNat : Int) = tab.saveBase entryNparams := Int.toNat_of_nonneg hnn
  have hle : (tab.saveBase entryNparams).toNat + 128 ≤ L.tabBytes := by omega
  have hT := L.hTValid
  have hcast : BitVec.ofInt 64 (tab.saveBase entryNparams) = BitVec.ofNat 64 (tab.saveBase entryNparams).toNat := by
    rw [← BitVec.ofInt_natCast, hcoe]
  rw [hcast, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

private theorem callerSaveSpan_sub_tabSpan {tab : Tab} (L : ProgLayout tab) (entryNparams : Nat)
    (hTabSave : tab.saveBase entryNparams + 128 ≤ (L.tabBytes : Int)) :
    (callerSaveSpan L.T (tab.saveBase entryNparams)).sub L.tabSpan := by
  intro a ⟨k, hk, ha⟩
  have hnn := callerSaveBase_nonneg tab entryNparams
  have hcoe : ((tab.saveBase entryNparams).toNat : Int) = tab.saveBase entryNparams := Int.toNat_of_nonneg hnn
  have hle : (tab.saveBase entryNparams).toNat + 128 ≤ L.tabBytes := by omega
  have hcast : BitVec.ofInt 64 (tab.saveBase entryNparams) = BitVec.ofNat 64 (tab.saveBase entryNparams).toNat := by
    rw [← BitVec.ofInt_natCast, hcoe]
  dsimp only [callerSaveSpan] at hk
  refine ⟨(tab.saveBase entryNparams).toNat + k, by dsimp only [ProgLayout.tabSpan]; omega, ?_⟩
  rw [ha]; dsimp only [callerSaveSpan, ProgLayout.tabSpan]
  rw [hcast, BitVec.add_assoc, ← BitVec.ofNat_add]

private theorem callerSaveSpan_disj_tabPrefix {tab : Tab} (L : ProgLayout tab) (entryNparams : Nat)
    (hTabSave : tab.saveBase entryNparams + 128 ≤ (L.tabBytes : Int))
    {off : Nat} (hoff : off < (tab.saveBase entryNparams).toNat) :
    ¬(callerSaveSpan L.T (tab.saveBase entryNparams)).contains (L.T + BitVec.ofNat 64 off) := by
  intro ⟨k, hk, ha⟩
  have hnn := callerSaveBase_nonneg tab entryNparams
  have hcoe : ((tab.saveBase entryNparams).toNat : Int) = tab.saveBase entryNparams := Int.toNat_of_nonneg hnn
  have hle : (tab.saveBase entryNparams).toNat + 128 ≤ L.tabBytes := by omega
  have hT := L.hTValid
  have hcast : BitVec.ofInt 64 (tab.saveBase entryNparams) = BitVec.ofNat 64 (tab.saveBase entryNparams).toNat := by
    rw [← BitVec.ofInt_natCast, hcoe]
  dsimp only [callerSaveSpan] at hk ha
  rw [hcast, BitVec.add_assoc, ← BitVec.ofNat_add] at ha
  have hnat := congrArg BitVec.toNat ha
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hnat
  omega

/-- The LP64 trampoline caller-save area `[L.T + tab.saveBase entryNparams, +128)` is disjoint
    from `CallWriteMask L callerSp`. -/
theorem saveArea_not_callWriteMask {tab : Tab} (L : ProgLayout tab)
    (entryNparams : Nat) (callerSp : BitVec 64)
    (hTabSave : tab.saveBase entryNparams + 128 ≤ (L.tabBytes : Int)) :
    ∀ a, (callerSaveSpan L.T (tab.saveBase entryNparams)).contains a →
      ¬CallWriteMask L callerSp a := by
  intro a ha hm
  have haTab := callerSaveSpan_sub_tabSpan L entryNparams hTabSave a ha
  rcases hm with ⟨hs, _⟩ | hres | ⟨idx, hidx, h8⟩ | ⟨s, hs, h64⟩
  · exact (MemSpan.disjoint_to_memDisjoint L.tabSpan_valid L.stackSpan_valid L.htabDisjStack) a haTab hs
  · rcases hres with ⟨k, hk, hka⟩
    have hnnRes := ProgLayout.resBase_nonneg tab
    have hcoeRes : (tab.resBase.toNat : Int) = tab.resBase := Int.toNat_of_nonneg hnnRes
    have hnnSave := callerSaveBase_nonneg tab entryNparams
    have hcoeSave : ((tab.saveBase entryNparams).toNat : Int) = tab.saveBase entryNparams := Int.toNat_of_nonneg hnnSave
    have hltSave : tab.resBase.toNat + k < (tab.saveBase entryNparams).toNat := by
      dsimp only [ProgLayout.resGlobSpan] at hk
      have hsb : tab.saveBase entryNparams = tab.resBase + 8 * ((tab.nxres + tab.ng + max 1 entryNparams : Nat) : Int) := by
        simp only [Tab.saveBase, Tab.args, Tab.globBase, Int.ofNat_eq_natCast]; omega
      omega
    have ha' : a = L.T + BitVec.ofNat 64 (tab.resBase.toNat + k) := by
      rw [hka]; dsimp only [ProgLayout.resGlobSpan]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [ha'] at ha
    exact callerSaveSpan_disj_tabPrefix L entryNparams hTabSave hltSave ha
  · exact (MemSpan.disjoint_to_memDisjoint (L.arr8Span_valid idx) L.tabSpan_valid (L.h8DisjTab idx hidx)) a h8 haTab
  · exact (MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid s) L.tabSpan_valid (L.h64DisjTab s hs)) a h64 haTab

theorem TabHeaderOk.of_callerSave {tab : Tab} (L : ProgLayout tab) (entryNparams : Nat)
    (hTabSave : tab.saveBase entryNparams + 128 ≤ (L.tabBytes : Int))
    {m1 m2 : ByteMem}
    (heq : MemEqOutside (callerSaveSpan L.T (tab.saveBase entryNparams)) m1 m2)
    (hhdr : TabHeaderOk L m1) : TabHeaderOk L m2 := by
  have h16 : 16 ≤ (tab.saveBase entryNparams).toNat := by
    have hnn := callerSaveBase_nonneg tab entryNparams
    have hcoe : ((tab.saveBase entryNparams).toNat : Int) = tab.saveBase entryNparams := Int.toNat_of_nonneg hnn
    have hle : (16 : Int) ≤ tab.saveBase entryNparams := by
      simp only [Tab.saveBase, Tab.args, Tab.globBase, Tab.resBase, Tab.romBase, Int.ofNat_eq_natCast]; omega
    omega
  refine ⟨?_, ?_⟩
  · rw [← hhdr.1]
    exact MemEqOutside.readWord64_eq heq _ fun k hk =>
      callerSaveSpan_disj_tabPrefix L entryNparams hTabSave (by omega)
  · rw [← hhdr.2]
    exact MemEqOutside.readWord64_eq heq _ fun k hk => by
      rw [BitVec.add_assoc, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
      exact callerSaveSpan_disj_tabPrefix L entryNparams hTabSave (by omega)

theorem ProgMemRel.of_callerSave {tab : Tab} (L : ProgLayout tab) (entryNparams : Nat)
    (hTabSave : tab.saveBase entryNparams + 128 ≤ (L.tabBytes : Int))
    {m1 m2 : ByteMem} {lm : _root_.L.Mem}
    (heq : MemEqOutside (callerSaveSpan L.T (tab.saveBase entryNparams)) m1 m2)
    (hrel : ProgMemRel tab L m1 lm) : ProgMemRel tab L m2 lm := by
  have hsubTab := callerSaveSpan_sub_tabSpan L entryNparams hTabSave
  have hnnSave := callerSaveBase_nonneg tab entryNparams
  have hcoeSave : ((tab.saveBase entryNparams).toNat : Int) = tab.saveBase entryNparams := Int.toNat_of_nonneg hnnSave
  have hsaveGe : ∀ x : Nat, (x : Int) ≤ tab.resBase → x ≤ (tab.saveBase entryNparams).toNat := fun x hx => by
    have h1 : tab.resBase ≤ tab.saveBase entryNparams := by
      simp only [Tab.saveBase, Tab.args, Tab.globBase, Int.ofNat_eq_natCast]; omega
    omega
  rcases hrel with ⟨ha, hs64, hrom, hglobs⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a haOk
    rcases ha a haOk with ⟨hcap, hlt, hlen, hbase, hbytes⟩
    have hpos := (Tab.bytePosOk_lt haOk).2.1
    refine ⟨hcap, hlt, ?_, ?_, ?_⟩
    · rw [← hlen]
      apply MemEqOutside.readWord64_eq heq
      intro k hk
      rw [Tab.len8_eq_nat, int_mul8_ofInt, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact callerSaveSpan_disj_tabPrefix L entryNparams hTabSave (by
        apply hsaveGe; simp only [Tab.resBase, Tab.romBase]; omega)
    · rw [← hbase]
      apply MemEqOutside.readWord64_eq heq
      intro k hk
      rw [Tab.base8_eq_nat, int_mul8_ofInt, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact callerSaveSpan_disj_tabPrefix L entryNparams hTabSave (by
        apply hsaveGe; simp only [Tab.resBase, Tab.romBase]; omega)
    · intro i hi
      rw [← hbytes i hi]
      apply heq
      intro hc
      exact (MemSpan.disjoint_to_memDisjoint (L.arr8Span_valid a) L.tabSpan_valid (L.h8DisjTab a haOk))
        _ ⟨i, by dsimp only [ProgLayout.arr8Span]; omega, rfl⟩ (hsubTab _ hc)
  · intro s64 hsOk
    rcases hs64 s64 hsOk with ⟨hcap, hlt, hlen, hbase, hwords⟩
    have hpos := (Tab.wordPosOk_lt hsOk).2.1
    refine ⟨hcap, hlt, ?_, ?_, ?_⟩
    · rw [← hlen]
      apply MemEqOutside.readWord64_eq heq
      intro k hk
      rw [Tab.len64_eq_nat, int_mul8_ofInt, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact callerSaveSpan_disj_tabPrefix L entryNparams hTabSave (by
        apply hsaveGe; simp only [Tab.resBase, Tab.romBase]; omega)
    · rw [← hbase]
      apply MemEqOutside.readWord64_eq heq
      intro k hk
      rw [Tab.base64_eq_nat, int_mul8_ofInt, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact callerSaveSpan_disj_tabPrefix L entryNparams hTabSave (by
        apply hsaveGe; simp only [Tab.resBase, Tab.romBase]; omega)
    · intro i hi
      rw [← hwords i hi]
      apply MemEqOutside.readWord64_eq heq
      intro k hk hc
      exact (MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid s64) L.tabSpan_valid (L.h64DisjTab s64 hsOk))
        _ ⟨8 * i + k, by dsimp only [ProgLayout.arr64Span]; omega,
           by dsimp only [ProgLayout.arr64Span]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]⟩
        (hsubTab _ hc)
  · intro k hk
    rw [← hrom k hk]
    apply heq
    have hrb := ProgLayout.romBase_nonneg tab
    have hcoeRb : (tab.romBase.toNat : Int) = tab.romBase := Int.toNat_of_nonneg hrb
    exact callerSaveSpan_disj_tabPrefix L entryNparams hTabSave (by
      have hromLen : tab.rom.length ≤ 8 * tab.romWords := by simp [Tab.romWords]; omega
      have hleSave : tab.romBase + 8 * (tab.romWords : Int) ≤ tab.saveBase entryNparams := by
        simp only [Tab.saveBase, Tab.args, Tab.globBase, Tab.resBase, Int.ofNat_eq_natCast]; omega
      omega)
  · intro g hg
    rw [← hglobs g hg]
    apply MemEqOutside.readWord64_eq heq
    intro k hk
    have hgo := L.tab_globOff_bound g hg
    have hgOffNat : BitVec.ofInt 64 (tab.globOff g) =
        BitVec.ofNat 64 (8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres + g.id)) := by
      have hge : tab.globOff g = ((8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres + g.id) : Nat) : Int) := by
        simp only [Tab.globOff, Tab.globBase, Tab.resBase, Tab.romBase]; omega
      rw [hge, BitVec.ofInt_natCast]
    rw [hgOffNat, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact callerSaveSpan_disj_tabPrefix L entryNparams hTabSave (by
      have hgeArgs : ((8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres + g.id) + k : Nat) : Int) <
          tab.saveBase entryNparams := by
        simp only [Tab.saveBase, Tab.args, Tab.globBase, Tab.resBase, Tab.romBase, Int.ofNat_eq_natCast]; omega
      omega)

theorem argWords_of_callerSave {tab : Tab} (L : ProgLayout tab) (entryNparams : Nat)
    (hTabSave : tab.saveBase entryNparams + 128 ≤ (L.tabBytes : Int))
    {m1 m2 : ByteMem} {vs : List _root_.L.Word}
    (heq : MemEqOutside (callerSaveSpan L.T (tab.saveBase entryNparams)) m1 m2)
    (hargWords : ∀ j, j < entryNparams →
      readWord64 m1 (L.T + BitVec.ofInt 64 tab.args + BitVec.ofNat 64 (8 * j)) = (vs.getD j 0).toBitVec) :
    ∀ j, j < entryNparams →
      readWord64 m2 (L.T + BitVec.ofInt 64 tab.args + BitVec.ofNat 64 (8 * j)) = (vs.getD j 0).toBitVec := by
  intro j hj
  rw [← hargWords j hj]
  apply MemEqOutside.readWord64_eq heq
  intro k hk
  have hnnArgs : 0 ≤ tab.args := by
    simp only [Tab.args, Tab.globBase, Tab.resBase, Tab.romBase]; omega
  have hcoeArgs : (tab.args.toNat : Int) = tab.args := Int.toNat_of_nonneg hnnArgs
  have hnnSave := callerSaveBase_nonneg tab entryNparams
  have hcoeSave : ((tab.saveBase entryNparams).toNat : Int) = tab.saveBase entryNparams := Int.toNat_of_nonneg hnnSave
  have hltSave : tab.args.toNat + (8 * j + k) < (tab.saveBase entryNparams).toNat := by
    have hsb : tab.saveBase entryNparams = tab.args + 8 * ((max 1 entryNparams : Nat) : Int) := by
      simp only [Tab.saveBase, Int.ofNat_eq_natCast]
    omega
  have hcast : BitVec.ofInt 64 tab.args = BitVec.ofNat 64 tab.args.toNat := by
    rw [← BitVec.ofInt_natCast, hcoeArgs]
  rw [hcast, BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact callerSaveSpan_disj_tabPrefix L entryNparams hTabSave hltSave

theorem savedWords_of_callWriteMask {tab : Tab} (L : ProgLayout tab) (entryNparams : Nat)
    (callerSp : BitVec 64)
    (hTabSave : tab.saveBase entryNparams + 128 ≤ (L.tabBytes : Int))
    {m1 m2 : ByteMem} {initSt : State}
    (heq : ProgMemOutside (CallWriteMask L callerSp) m1 m2)
    (hsaved : ∀ i (hi : i < callerSaveRegs.length),
      readWord64 m1 ((L.T + BitVec.ofInt 64 (tab.saveBase entryNparams)) + BitVec.ofNat 64 (8 * i)) =
        initSt.getReg (callerSaveRegs[i]'hi)) :
    ∀ i (hi : i < callerSaveRegs.length),
      readWord64 m2 ((L.T + BitVec.ofInt 64 (tab.saveBase entryNparams)) + BitVec.ofNat 64 (8 * i)) =
        initSt.getReg (callerSaveRegs[i]'hi) := by
  intro i hi
  rw [← hsaved i hi]
  apply heq.readWord64_eq
  intro k hk
  apply saveArea_not_callWriteMask L entryNparams callerSp hTabSave
  have hlen : callerSaveRegs.length = 16 := rfl
  refine ⟨8 * i + k, by dsimp only [callerSaveSpan]; omega, ?_⟩
  dsimp only [callerSaveSpan]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

end ConAgua.RISCV.Compiler
