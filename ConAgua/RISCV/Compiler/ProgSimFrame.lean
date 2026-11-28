import ConAgua.RISCV.Compiler.ProgSimScan
import ConAgua.RISCV.Compiler.RegSimStmt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Program-Level Forward Simulation: Frame Invariants & Helpers (`ConAgua.RISCV.Compiler.ProgSimFrame`)

Write masks, live-variable frame invariant (`ProgFrameOkLive`), result-copy & tail-call helpers
for `ConAgua.RISCV.MiniL` programs compiled via `Compile.compileProgAsm`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard Lean axioms only.
-/

namespace ConAgua.RISCV.Compiler

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Linker

/-! ## 1. Header, Write Mask, Label & Single-Instruction Helpers -/

/-- Descriptor table header words: `*(T + 0) = stackTop`, `*(T + 8) = stackLimit`. -/
def TabHeaderOk {tab : Tab} (L : ProgLayout tab) (rmem : ByteMem) : Prop :=
  readWord64 rmem L.T = L.stackTop ∧
  readWord64 rmem (L.T + 8#64) = L.stackLimit

/-- Addresses a callee invocation below `callerSp` may overwrite: stack below `callerSp`,
    `resGlobSpan`, byte arrays, and word arrays. -/
def CallWriteMask {tab : Tab} (L : ProgLayout tab) (callerSp : BitVec 64)
    (a : BitVec 64) : Prop :=
  (L.stackSpan.contains a ∧ a.toNat < callerSp.toNat) ∨
  L.resGlobSpan.contains a ∨
  (∃ idx, tab.bytePosOkB idx = true ∧ (L.arr8Span idx).contains a) ∨
  (∃ s, tab.wordPosOkB s = true ∧ (L.arr64Span s).contains a)

theorem TabHeaderOk.of_progMemOutside {tab : Tab} (L : ProgLayout tab)
    {sp : BitVec 64} {nl nt : Nat} {m1 m2 : ByteMem}
    (heq : ProgMemOutside (FnWriteMask L sp nl nt) m1 m2)
    (hhdr : TabHeaderOk L m1) : TabHeaderOk L m2 := by
  have h16 : 16 ≤ tab.resBase.toNat := by
    have hm := L.tabMin_strong
    have hnn := ProgLayout.resBase_nonneg tab
    have hcoe : ((tab.resBase.toNat : Nat) : Int) = tab.resBase := Int.toNat_of_nonneg hnn
    simp only [Tab.resBase, Tab.romBase] at hnn ⊢
    omega
  refine ⟨?_, ?_⟩
  · rw [← hhdr.1]
    apply heq.readWord64_eq
    intro k hk
    rw [show L.T + BitVec.ofNat 64 k = L.T + BitVec.ofNat 64 (0 + k) from by simp]
    exact L.tabHeader_not_fnWriteMask (by omega)
  · rw [← hhdr.2]
    apply heq.readWord64_eq
    intro k hk
    rw [show L.T + 8#64 + BitVec.ofNat 64 k = L.T + BitVec.ofNat 64 (8 + k) from by
      rw [BitVec.add_assoc, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]]
    exact L.tabHeader_not_fnWriteMask (by omega)

theorem TabHeaderOk.of_callWriteMask {tab : Tab} (L : ProgLayout tab)
    {callerSp : BitVec 64} {m1 m2 : ByteMem}
    (heq : ProgMemOutside (CallWriteMask L callerSp) m1 m2)
    (hhdr : TabHeaderOk L m1) : TabHeaderOk L m2 := by
  have hdisj : ∀ off, off < 16 → ¬CallWriteMask L callerSp (L.T + BitVec.ofNat 64 off) := by
    intro off hoff hm
    have hsub := L.tabHeader_not_fnWriteMask (sp := L.stackTop) (nl := 0) (nt := 0) (off := off)
    have h16 : 16 ≤ tab.resBase.toNat := by
      simp only [Tab.resBase, Tab.romBase]; omega
    apply hsub (by omega)
    rcases hm with ⟨hs, hlt⟩ | hres | h8 | h64
    · have hc := (MemSpan.disjoint_to_memDisjoint L.tabSpan_valid L.stackSpan_valid L.htabDisjStack)
      have hmn := L.tabMin_strong
      simp only [Tab.globBase, Tab.resBase, Tab.romBase] at hmn
      exact False.elim (hc _ ⟨off, by dsimp only [ProgLayout.tabSpan]; omega, rfl⟩ hs)
    · exact Or.inr (Or.inl hres)
    · exact Or.inr (Or.inr (Or.inl h8))
    · exact Or.inr (Or.inr (Or.inr h64))
  refine ⟨?_, ?_⟩
  · rw [← hhdr.1]
    apply heq.readWord64_eq
    intro k hk
    exact hdisj k (by omega)
  · rw [← hhdr.2]
    apply heq.readWord64_eq
    intro k hk
    rw [show L.T + 8#64 + BitVec.ofNat 64 k = L.T + BitVec.ofNat 64 (8 + k) from by
      rw [BitVec.add_assoc, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]]
    exact hdisj (8 + k) (by omega)

theorem TabHeaderOk.of_memEqOutside {tab : Tab} (L : ProgLayout tab)
    {s : MemSpan} {m1 m2 : ByteMem}
    (hsub : s.sub L.stackSpan) (heq : MemEqOutside s m1 m2)
    (hhdr : TabHeaderOk L m1) : TabHeaderOk L m2 := by
  have hdisj : MemDisjoint s L.tabSpan :=
    MemDisjoint.of_sub_left hsub (MemSpan.disjoint_to_memDisjoint L.stackSpan_valid L.tabSpan_valid L.htabDisjStack.symm)
  have h16 : 16 ≤ L.tabBytes := by
    have hm := L.tabMin_strong
    simp only [Tab.globBase, Tab.resBase, Tab.romBase] at hm
    omega
  refine ⟨?_, ?_⟩
  · rw [← hhdr.1]
    exact MemEqOutside.readWord64_eq heq _ fun k hk => hdisj.symm _ ⟨k, by dsimp only [ProgLayout.tabSpan]; omega, rfl⟩
  · rw [← hhdr.2]
    exact MemEqOutside.readWord64_eq heq _ fun k hk => by
      rw [BitVec.add_assoc, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
      exact hdisj.symm _ ⟨8 + k, by dsimp only [ProgLayout.tabSpan]; omega, rfl⟩

theorem callWriteMask_sub_fnWriteMask {tab : Tab} (L : ProgLayout tab)
    (sp : BitVec 64) (nl nt : Nat) :
    ∀ a, CallWriteMask L sp a → FnWriteMask L sp nl nt a := by
  intro a ha
  rcases ha with ⟨hs, hlt⟩ | hres | h8 | h64
  · exact Or.inl ⟨hs, Or.inl hlt⟩
  · exact Or.inr (Or.inl hres)
  · exact Or.inr (Or.inr (Or.inl h8))
  · exact Or.inr (Or.inr (Or.inr h64))

theorem fnWriteMask_sub_callWriteMask {tab : Tab} (L : ProgLayout tab)
    {sp' callerSp : BitVec 64} {nl' nt' : Nat}
    (hhi : sp'.toNat + 8 * (1 + nl' + nt') ≤ callerSp.toNat) :
    ∀ a, FnWriteMask L sp' nl' nt' a → CallWriteMask L callerSp a := by
  intro a ha
  rcases ha with ⟨hs, hcase⟩ | hres | h8 | h64
  · left
    rcases hcase with hlt | ⟨_, hlt⟩
    · exact ⟨hs, by omega⟩
    · exact ⟨hs, by omega⟩
  · exact Or.inr (Or.inl hres)
  · exact Or.inr (Or.inr (Or.inl h8))
  · exact Or.inr (Or.inr (Or.inr h64))

theorem ProgFrameOk.of_callWriteMask {tab : Tab} (L : ProgLayout tab)
    {callerSp : BitVec 64} {nl nt : Nat} {m1 m2 : ByteMem} {loc : _root_.L.Locals}
    (hlo : L.stackLimit.toNat ≤ callerSp.toNat)
    (htop : callerSp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (heq : ProgMemOutside (CallWriteMask L callerSp) m1 m2)
    (hfr : ProgFrameOk L callerSp m1 nl loc) :
    ProgFrameOk L callerSp m2 nl loc := by
  have hmv : (frameSpan callerSp nl nt).valid := Nat.le_trans htop L.hStackValid
  have hsubStack := L.frame_sub_stackSpan hlo htop
  intro y hy
  rw [← hfr y hy]
  apply heq.readWord64_eq
  intro k hk hm
  have hlt64 : 8 * (1 + y) + k < 2 ^ 64 := by simp only [frameSpan, MemSpan.valid] at hmv; omega
  have ha : (callerSp + BitVec.ofInt 64 (slotOff y) + BitVec.ofNat 64 k).toNat =
      callerSp.toNat + 8 * (1 + y) + k := by
    rw [slotOff_ofInt, BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlt64, Nat.mod_eq_of_lt (by simp only [frameSpan, MemSpan.valid] at hmv; omega)]
    omega
  have hc : L.stackSpan.contains (callerSp + BitVec.ofInt 64 (slotOff y) + BitVec.ofNat 64 k) := by
    apply hsubStack
    rw [slotOff_ofInt, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨8 * (1 + y) + k, by simp only [frameSpan]; omega, rfl⟩
  rcases hm with ⟨_, hlt⟩ | hres | ⟨a, haOk, ha8⟩ | ⟨s, hsOk, hs64⟩
  · omega
  · exact (MemSpan.disjoint_to_memDisjoint L.tabSpan_valid L.stackSpan_valid L.htabDisjStack)
      _ (L.resGlob_sub_tab _ hres) hc
  · exact (MemSpan.disjoint_to_memDisjoint (L.arr8Span_valid a) L.stackSpan_valid (L.h8DisjStack a haOk))
      _ ha8 hc
  · exact (MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid s) L.stackSpan_valid (L.h64DisjStack s hsOk))
      _ hs64 hc

theorem linkResolved_lbl_lm (lkm : LinkModel) {code : Array (BitVec 32)} {labels : LabelMap}
    (pre : List AsmItem) (name : String) (post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ [Asm.lbl name] ++ post) = .ok (code, labels)) :
    lookupLabel labels name = some (lkm.totalSize pre) :=
  lookupLabel_of_lbl_lm lkm pre post name hlink

theorem linkResolved_lbl {code : Array (BitVec 32)} {labels : LabelMap}
    (pre : List AsmItem) (name : String) (post : List AsmItem)
    (hlink : linkResolved (pre ++ [Asm.lbl name] ++ post) = .ok (code, labels)) :
    lookupLabel labels name = some (totalWords pre) :=
  linkResolved_item_spec pre (Asm.lbl name) post code labels hlink

theorem run_alu_rd_step {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (op : AluOp) (rd rs1 rs2 : Reg) (hrd : rd ≠ 0#5)
    (hlink : lkm.linkSpec (pre ++ [AsmItem.instr (.alu op rd rs1 rs2)] ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre)) :
    let st' := stepReg st rd (evalAlu op (st.getReg rs1) (st.getReg rs2))
      (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
    RV64.run env.rom 1 st = .cont st' ∧
    st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)) ∧
    st'.getReg rd = evalAlu op (st.getReg rs1) (st.getReg rs2) ∧
    (∀ q, q ≠ rd → st'.getReg q = st.getReg q) ∧
    st'.mem = st.mem := by
  have hpc64 := linkResolved_sub_pc64 env pre [AsmItem.instr (.alu op rd rs1 rs2)] post hlink
  have htw : lkm.totalSize [AsmItem.instr (.alu op rd rs1 rs2)] = 1 := lkm.totalSize_instr _
  have hlt : 4 * lkm.totalSize pre < 2 ^ 64 := by rw [htw] at hpc64; omega
  have hstep := step_item_instr_lm lkm env.hrom pre post (.alu op rd rs1 rs2) hlink hlt st hpc
  let st' := stepReg st rd (evalAlu op (st.getReg rs1) (st.getReg rs2))
    (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
  have hrun : RV64.run env.rom 1 st = .cont st' := by
    apply run_one_cont; rw [hstep]
    simp only [execInstr, pc_add_4_ofNat st.pc hpc, st', stepReg, setReg_mem]
  exact ⟨hrun, rfl, getReg_stepReg_eq st rd hrd _ _,
    fun q hq => getReg_stepReg_ne st rd q hq _ _, by simp [stepReg, setReg_mem]⟩

theorem run_aluImm_rd_step {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (op : AluImmOp) (rd rs1 : Reg) (imm : BitVec 12) (hrd : rd ≠ 0#5)
    (hlink : lkm.linkSpec (pre ++ [AsmItem.instr (.aluImm op rd rs1 imm)] ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre)) :
    let st' := stepReg st rd (evalAluImm op (st.getReg rs1) imm)
      (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
    RV64.run env.rom 1 st = .cont st' ∧
    st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)) ∧
    st'.getReg rd = evalAluImm op (st.getReg rs1) imm ∧
    (∀ q, q ≠ rd → st'.getReg q = st.getReg q) ∧
    st'.mem = st.mem := by
  have hpc64 := linkResolved_sub_pc64 env pre [AsmItem.instr (.aluImm op rd rs1 imm)] post hlink
  have htw : lkm.totalSize [AsmItem.instr (.aluImm op rd rs1 imm)] = 1 := lkm.totalSize_instr _
  have hlt : 4 * lkm.totalSize pre < 2 ^ 64 := by rw [htw] at hpc64; omega
  have hstep := step_item_instr_lm lkm env.hrom pre post (.aluImm op rd rs1 imm) hlink hlt st hpc
  let st' := stepReg st rd (evalAluImm op (st.getReg rs1) imm)
    (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
  have hrun : RV64.run env.rom 1 st = .cont st' := by
    apply run_one_cont; rw [hstep]
    simp only [execInstr, pc_add_4_ofNat st.pc hpc, st', stepReg, setReg_mem]
  exact ⟨hrun, rfl, getReg_stepReg_eq st rd hrd _ _,
    fun q hq => getReg_stepReg_ne st rd q hq _ _, by simp [stepReg, setReg_mem]⟩

theorem evalE_err_eq_oob (e : _root_.L.Expr) (st : _root_.L.St) {err : _root_.L.Err}
    (h : _root_.L.evalE e st = .error err) : err = .oob := by
  rcases _root_.L.evalE_pure e st with ⟨_, hok⟩ | herr
  · rw [hok] at h; cases h
  · rw [herr] at h; exact (Except.error.inj h).symm

theorem evalC_err_eq_oob (c : _root_.L.Cond) (st : _root_.L.St) {err : _root_.L.Err}
    (h : _root_.L.evalC c st = .error err) : err = .oob := by
  rcases _root_.L.evalC_pure c st with ⟨_, hok⟩ | herr
  · rw [hok] at h; cases h
  · rw [herr] at h; exact (Except.error.inj h).symm

theorem evalArgs_err_eq_oob (es : List _root_.L.Expr) (st : _root_.L.St) {err : _root_.L.Err}
    (h : _root_.L.evalArgs es st = .error err) : err = .oob := by
  rcases _root_.L.evalArgs_pure es st with ⟨_, hok⟩ | herr
  · rw [hok] at h; cases h
  · rw [herr] at h; exact (Except.error.inj h).symm

theorem setLocs_mem (s : _root_.L.St) (xs : List _root_.L.Var) (vs : List _root_.L.Word) :
    (s.setLocs xs vs).mem = s.mem := by
  induction xs generalizing s vs with
  | nil => rfl
  | cons x xs ih => simp [_root_.L.St.setLocs, _root_.L.St.setLoc, ih]

theorem evalArgs_length (es : List _root_.L.Expr) (st : _root_.L.St) {vs : List _root_.L.Word} {st' : _root_.L.St}
    (h : _root_.L.evalArgs es st = .ok (vs, st')) : vs.length = es.length := by
  induction es generalizing st vs st' with
  | nil =>
    simp only [_root_.L.evalArgs, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; rfl
  | cons e es ih =>
    simp only [_root_.L.evalArgs, Bind.bind, StateT.bind, Except.bind] at h
    cases he : _root_.L.evalE e st with
    | error err => rw [he] at h; cases h
    | ok re =>
      rw [he] at h; dsimp only at h
      cases hes : _root_.L.evalArgs es re.2 with
      | error err => rw [hes] at h; cases h
      | ok rvs =>
        rw [hes] at h
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, _⟩
        simp [ih re.2 hes]

/-! ### 1b. Register-Allocated Frame, Write-Mask & Preservation Helpers -/

theorem TabHeaderOk.of_fnWriteMaskR {tab : Tab} (L : ProgLayout tab)
    {fl : FrameLayout} {sp : BitVec 64} {m1 m2 : ByteMem}
    (heq : ProgMemOutside (FnWriteMaskR L fl sp) m1 m2)
    (hhdr : TabHeaderOk L m1) : TabHeaderOk L m2 := by
  have hdisj : ∀ off, off < 16 → ¬FnWriteMaskR L fl sp (L.T + BitVec.ofNat 64 off) := by
    intro off hoff hm
    have hsub := L.tabHeader_not_fnWriteMask (sp := L.stackTop) (nl := 0) (nt := 0) (off := off)
    have h16 : 16 ≤ tab.resBase.toNat := by
      simp only [Tab.resBase, Tab.romBase]; omega
    apply hsub (by omega)
    rcases hm with ⟨hs, _⟩ | hres | h8 | h64
    · have hc := MemSpan.disjoint_to_memDisjoint L.tabSpan_valid L.stackSpan_valid L.htabDisjStack
      have hmn := L.tabMin_strong
      simp only [Tab.globBase, Tab.resBase, Tab.romBase] at hmn
      exact False.elim (hc _ ⟨off, by dsimp only [ProgLayout.tabSpan]; omega, rfl⟩ hs)
    · exact Or.inr (Or.inl hres)
    · exact Or.inr (Or.inr (Or.inl h8))
    · exact Or.inr (Or.inr (Or.inr h64))
  refine ⟨?_, ?_⟩
  · rw [← hhdr.1]
    apply heq.readWord64_eq
    intro k hk
    exact hdisj k (by omega)
  · rw [← hhdr.2]
    apply heq.readWord64_eq
    intro k hk
    rw [show L.T + 8#64 + BitVec.ofNat 64 k = L.T + BitVec.ofNat 64 (8 + k) from by
      rw [BitVec.add_assoc, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]]
    exact hdisj (8 + k) (by omega)

theorem callWriteMask_sub_fnWriteMaskR {tab : Tab} (L : ProgLayout tab)
    (fl : FrameLayout) (sp : BitVec 64) :
    ∀ a, CallWriteMask L sp a → FnWriteMaskR L fl sp a := by
  intro a ha
  rcases ha with ⟨hs, hlt⟩ | hres | h8 | h64
  · exact Or.inl ⟨hs, Or.inl hlt⟩
  · exact Or.inr (Or.inl hres)
  · exact Or.inr (Or.inr (Or.inl h8))
  · exact Or.inr (Or.inr (Or.inr h64))

theorem fnWriteMaskR_sub_callWriteMask {tab : Tab} (L : ProgLayout tab)
    {fl : FrameLayout} {sp' callerSp : BitVec 64}
    (hhi : sp'.toNat + 8 * fl.frameSlots ≤ callerSp.toNat) :
    ∀ a, FnWriteMaskR L fl sp' a → CallWriteMask L callerSp a := by
  intro a ha
  rcases ha with ⟨hs, hcase⟩ | hres | h8 | h64
  · left
    rcases hcase with hlt | ⟨_, hlt⟩
    · exact ⟨hs, by omega⟩
    · exact ⟨hs, by omega⟩
  · exact Or.inr (Or.inl hres)
  · exact Or.inr (Or.inr (Or.inl h8))
  · exact Or.inr (Or.inr (Or.inr h64))

theorem progMemOutside_of_resGlobR {tab : Tab} (L : ProgLayout tab)
    (fl : FrameLayout) (sp : BitVec 64) {m1 m2 : ByteMem}
    (heq : MemEqOutside L.resGlobSpan m1 m2) :
    ProgMemOutside (FnWriteMaskR L fl sp) m1 m2 :=
  ProgMemOutside.of_memEqOutside (fun _ hc => Or.inr (Or.inl hc)) heq

theorem localsTempSpanR_sub_stackSpan {tab : Tab} (L : ProgLayout tab)
    {fl : FrameLayout} {sp : BitVec 64}
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat) :
    (localsTempSpanR fl sp).sub L.stackSpan := by
  have hsub := frameSpanR_sub_stackSpan L hlo hhi
  intro a ⟨k, hk, ha⟩
  subst ha
  apply hsub
  dsimp only [localsTempSpanR] at hk
  refine ⟨8 * fl.protectedSlots + k, by dsimp only [frameSpanR, FrameLayout.frameSlots]; omega, ?_⟩
  dsimp only [localsTempSpanR, frameSpanR]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem spillSlots_of_callWriteMask {tab : Tab} (L : ProgLayout tab)
    {fl : FrameLayout} (hfl : FrameLayoutOk fl) {callerSp : BitVec 64}
    {m1 m2 : ByteMem}
    (hlo : L.stackLimit.toNat ≤ callerSp.toNat)
    (hhi : callerSp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (heq : ProgMemOutside (CallWriteMask L callerSp) m1 m2)
    {y : Var} (hmy : y ∈ fl.spilledVars) :
    readWord64 m2 (callerSp + BitVec.ofInt 64 (fl.varSlotOff y)) =
    readWord64 m1 (callerSp + BitVec.ofInt 64 (fl.varSlotOff y)) := by
  have hmv : (frameSpanR fl callerSp).valid := Nat.le_trans hhi L.hStackValid
  have hsubStack := frameSpanR_sub_stackSpan L hlo hhi
  have hsi := hfl.spillIdx_lt hmy
  apply heq.readWord64_eq
  intro k hk hm
  have hlt64 : 8 * (fl.protectedSlots + fl.spillIdx y) + k < 2 ^ 64 := by
    dsimp only [frameSpanR, MemSpan.valid, FrameLayout.frameSlots] at hmv; omega
  have ha : (callerSp + BitVec.ofInt 64 (fl.varSlotOff y) + BitVec.ofNat 64 k).toNat =
      callerSp.toNat + 8 * (fl.protectedSlots + fl.spillIdx y) + k := by
    rw [varSlotOff_ofInt, BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlt64,
      Nat.mod_eq_of_lt (by dsimp only [frameSpanR, MemSpan.valid, FrameLayout.frameSlots] at hmv; omega)]
    omega
  have hc : L.stackSpan.contains (callerSp + BitVec.ofInt 64 (fl.varSlotOff y) + BitVec.ofNat 64 k) := by
    apply hsubStack
    rw [varSlotOff_ofInt, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨8 * (fl.protectedSlots + fl.spillIdx y) + k, by dsimp only [frameSpanR, FrameLayout.frameSlots]; omega, rfl⟩
  rcases hm with ⟨_, hlt⟩ | hres | ⟨a, haOk, ha8⟩ | ⟨s, hsOk, hs64⟩
  · omega
  · exact (MemSpan.disjoint_to_memDisjoint L.tabSpan_valid L.stackSpan_valid L.htabDisjStack)
      _ (L.resGlob_sub_tab _ hres) hc
  · exact (MemSpan.disjoint_to_memDisjoint (L.arr8Span_valid a) L.stackSpan_valid (L.h8DisjStack a haOk))
      _ ha8 hc
  · exact (MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid s) L.stackSpan_valid (L.h64DisjStack s hsOk))
      _ hs64 hc

/-- Preservation across statements (excluding fuel `s0` and allocated local registers). -/
structure PreservedFrameNoS0 (fl : FrameLayout) (s1 s2 : State) : Prop where
  abi : PreservedNoS0 s1 s2
  leafRa : fl.isLeaf = true → s2.getReg AbiReg.ra = s1.getReg AbiReg.ra
  t5Gp : fl.useT5Gp = true → s2.getReg AbiReg.t5 = s1.getReg AbiReg.t5
  regs : ∀ r, r ∈ allowedRegs fl.isLeaf → r ∉ fl.alloc.map Prod.snd → s2.getReg r = s1.getReg r

theorem PreservedFrameNoS0.refl (fl : FrameLayout) (s : State) : PreservedFrameNoS0 fl s s :=
  ⟨PreservedNoS0.refl s, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

theorem PreservedFrameNoS0.trans {fl : FrameLayout} {s1 s2 s3 : State}
    (h12 : PreservedFrameNoS0 fl s1 s2) (h23 : PreservedFrameNoS0 fl s2 s3) :
    PreservedFrameNoS0 fl s1 s3 :=
  ⟨h12.abi.trans h23.abi, fun hl => (h23.leafRa hl).trans (h12.leafRa hl),
   fun ht => (h23.t5Gp ht).trans (h12.t5Gp ht),
   fun r hr hn => (h23.regs r hr hn).trans (h12.regs r hr hn)⟩

theorem PreservedFrameNoS0.toTramp {fl : FrameLayout} {s1 s2 : State}
    (h : PreservedFrameNoS0 fl s1 s2) : PreservedTramp s1 s2 :=
  h.abi.toTramp

theorem PreservedFrameRegs.toFrameNoS0 {fl : FrameLayout} {s1 s2 : State}
    (h : PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) s1 s2) :
    PreservedFrameNoS0 fl s1 s2 :=
  ⟨h.abi.toNoS0, h.leafRa, h.t5Gp, fun r hr hna => h.regs r (allowedRegs_sub_true hr) hna⟩

theorem PreservedFrameRegs.toFrameNoS0_all {fl : FrameLayout} {s1 s2 : State}
    (h : PreservedFrameRegs fl (fun _ => False) s1 s2) :
    PreservedFrameNoS0 fl s1 s2 :=
  ⟨h.abi.toNoS0, h.leafRa, h.t5Gp, fun r hr _ => h.regs r (allowedRegs_sub_true hr) (fun hf => False.elim hf)⟩

theorem T5GpOk.of_frameNoS0 {tab : Tab} {L : ProgLayout tab} {fl : FrameLayout}
    {st1 st2 : State} (hpres : PreservedFrameNoS0 fl st1 st2) (ht5 : T5GpOk L fl st1) :
    T5GpOk L fl st2 :=
  fun h => (hpres.t5Gp h).trans (ht5 h)

/-- Preservation on `.ret` exits (allows `leafExtraBank = a1..a7` to hold return values,
    while preserving ABI regs, leaf `ra`, and all unsaved `calleeSavedBank` regs). -/
structure PreservedRetRegs (fl : FrameLayout) (s1 s2 : State) : Prop where
  abi : PreservedNoS0 s1 s2
  leafRa : fl.isLeaf = true → s2.getReg AbiReg.ra = s1.getReg AbiReg.ra
  callee : ∀ r, r ∈ calleeSavedBank → r ∉ fl.savedRegs → s2.getReg r = s1.getReg r

theorem PreservedRetRegs.refl (fl : FrameLayout) (s : State) : PreservedRetRegs fl s s :=
  ⟨PreservedNoS0.refl s, fun _ => rfl, fun _ _ _ => rfl⟩

theorem PreservedRetRegs.trans {fl : FrameLayout} {s1 s2 s3 : State}
    (h12 : PreservedRetRegs fl s1 s2) (h23 : PreservedRetRegs fl s2 s3) :
    PreservedRetRegs fl s1 s3 :=
  ⟨h12.abi.trans h23.abi, fun hl => (h23.leafRa hl).trans (h12.leafRa hl),
   fun r hr hn => (h23.callee r hr hn).trans (h12.callee r hr hn)⟩

theorem PreservedFrameNoS0.toRetRegs {fl : FrameLayout} (hfl : FrameLayoutOk fl) {s1 s2 : State}
    (h : PreservedFrameNoS0 fl s1 s2) : PreservedRetRegs fl s1 s2 :=
  ⟨h.abi, h.leafRa, fun r hr hns =>
    h.regs r (calleeSaved_mem_allowed fl.isLeaf hr) fun hm =>
      hns (hfl.saved_mem_iff.mpr ⟨hr, hm⟩)⟩

theorem PreservedFrameNoS0.trans_ret {fl : FrameLayout} (hfl : FrameLayoutOk fl) {s1 s2 s3 : State}
    (h12 : PreservedFrameNoS0 fl s1 s2) (h23 : PreservedRetRegs fl s2 s3) :
    PreservedRetRegs fl s1 s3 :=
  (h12.toRetRegs hfl).trans h23

theorem PreservedFrameNoS0.of_other_t6 {fl : FrameLayout} {s1 s2 : State}
    (hoth : ∀ q, q ≠ AbiReg.t6 ∧ q ≠ AbiReg.s1 → s2.getReg q = s1.getReg q) :
    PreservedFrameNoS0 fl s1 s2 :=
  ⟨⟨hoth _ (by decide), hoth _ (by decide), hoth _ (by decide)⟩,
   fun _ => hoth _ (by decide),
   fun _ => hoth _ (by decide),
   fun r hr _ => hoth r ⟨allowedRegs_ne_t6 hr, allowedRegs_ne_s1 hr⟩⟩

theorem PreservedRetRegs.of_other_t6 {fl : FrameLayout} {s1 s2 : State}
    (hoth : ∀ q, q ≠ AbiReg.t6 ∧ q ≠ AbiReg.s1 → s2.getReg q = s1.getReg q) :
    PreservedRetRegs fl s1 s2 :=
  ⟨⟨hoth _ (by decide), hoth _ (by decide), hoth _ (by decide)⟩,
   fun _ => hoth _ (by decide),
   fun r hr _ => hoth r ⟨allowedRegs_ne_t6 (calleeSaved_mem_allowed fl.isLeaf hr),
     allowedRegs_ne_s1 (calleeSaved_mem_allowed fl.isLeaf hr)⟩⟩

theorem resReg_ne_ra (i : Nat) : resReg i ≠ AbiReg.ra := by
  match i with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | _ + 7 => simp [resReg]; decide

theorem resReg_ne_t5 (i : Nat) : resReg i ≠ AbiReg.t5 := by
  match i with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | _ + 7 => simp [resReg]; decide

theorem resReg_ne_of_lt {i j : Nat} (hi : i < maxRes) (hj : j < maxRes) (hne : i ≠ j) :
    resReg i ≠ resReg j := by
  simp only [maxRes] at hi hj
  match i, j with
  | 0, 0 | 1, 1 | 2, 2 | 3, 3 | 4, 4 | 5, 5 | 6, 6 | 7, 7 => exact absurd rfl hne
  | 0, 1 | 0, 2 | 0, 3 | 0, 4 | 0, 5 | 0, 6 | 0, 7
  | 1, 0 | 1, 2 | 1, 3 | 1, 4 | 1, 5 | 1, 6 | 1, 7
  | 2, 0 | 2, 1 | 2, 3 | 2, 4 | 2, 5 | 2, 6 | 2, 7
  | 3, 0 | 3, 1 | 3, 2 | 3, 4 | 3, 5 | 3, 6 | 3, 7
  | 4, 0 | 4, 1 | 4, 2 | 4, 3 | 4, 5 | 4, 6 | 4, 7
  | 5, 0 | 5, 1 | 5, 2 | 5, 3 | 5, 4 | 5, 6 | 5, 7
  | 6, 0 | 6, 1 | 6, 2 | 6, 3 | 6, 4 | 6, 5 | 6, 7
  | 7, 0 | 7, 1 | 7, 2 | 7, 3 | 7, 4 | 7, 5 | 7, 6 => simp [resReg]; decide
  | _ + 8, _ | _, _ + 8 => omega

theorem usedTempsExprs_ge_length (es : List _root_.L.Expr) :
    es.length ≤ usedTempsExprs es := by
  cases es with
  | nil => simp [usedTempsExprs]
  | cons e rest =>
    have hfoldl_ge : ∀ (xs : List (_root_.L.Expr × Nat)) (init : Nat),
        init ≤ xs.foldl (fun acc (e, idx) => max acc (idx + max 1 (usedTempsExpr e))) init := by
      intro xs; induction xs with
      | nil => intro init; exact Nat.le_refl _
      | cons p ps ih => intro init; simp only [List.foldl_cons]; exact Nat.le_trans (Nat.le_max_left _ _) (ih _)
    have hrec : ∀ (l : List (_root_.L.Expr × Nat)) (init : Nat),
        ∀ p ∈ l, p.2 + 1 ≤ l.foldl (fun acc (e, idx) => max acc (idx + max 1 (usedTempsExpr e))) init := by
      intro l; induction l with
      | nil => intro _ _ hp; simp at hp
      | cons hd tl ih =>
        intro init p hp
        simp only [List.foldl_cons]
        rcases List.mem_cons.mp hp with rfl | htl
        · exact Nat.le_trans (Nat.le_trans (by omega) (Nat.le_max_right init _)) (hfoldl_ge tl _)
        · exact ih _ p htl
    have hzip : ∀ (l : List _root_.L.Expr) (k : Nat), l ≠ [] →
        ∃ x, (x, k + l.length - 1) ∈ l.zipIdx k := by
      intro l; induction l with
      | nil => intro _ h; exact absurd rfl h
      | cons a tl ih =>
        intro k _
        cases tl with
        | nil => exact ⟨a, by simp [List.zipIdx_cons]⟩
        | cons b tl2 =>
          obtain ⟨x, hx⟩ := ih (k + 1) (by simp)
          refine ⟨x, ?_⟩
          rw [List.zipIdx_cons]; right
          have heq : k + 1 + (b :: tl2).length - 1 = k + (a :: b :: tl2).length - 1 := by simp; omega
          rwa [← heq]
    obtain ⟨x, hx⟩ := hzip (e :: rest) 0 (by simp)
    have hle := hrec ((e :: rest).zipIdx 0) 0 (x, 0 + (e :: rest).length - 1) hx
    change (e :: rest).length ≤ ((e :: rest).zipIdx 0).foldl (fun acc (e, idx) => max acc (idx + max 1 (usedTempsExpr e))) 0
    omega

theorem FrameLayoutOk.frameSlots_zero_props {fl : FrameLayout} (hfl : FrameLayoutOk fl)
    (h0 : fl.frameSlots = 0) :
    fl.isLeaf = true ∧ fl.savedRegs = [] ∧ fl.spilledVars = [] ∧ fl.usedTemps = 0 := by
  have _ := hfl
  unfold FrameLayout.frameSlots FrameLayout.protectedSlots FrameLayout.raSlots at h0
  have hra : (if fl.isLeaf then 0 else 1) = 0 := by omega
  have hleaf : fl.isLeaf = true := by cases hl : fl.isLeaf <;> simp [hl] at hra ⊢
  have hsr : fl.savedRegs = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hsp : fl.spilledVars = [] := List.eq_nil_of_length_eq_zero (by omega)
  exact ⟨hleaf, hsr, hsp, by omega⟩

theorem frameBytesR_toNat_eq (fl : FrameLayout) :
    BitVec.ofInt 64 fl.frameBytes = BitVec.ofNat 64 (8 * fl.frameSlots) := by
  unfold FrameLayout.frameBytes
  rw [show (8 : Int) * (fl.frameSlots : Int) = ((8 * fl.frameSlots : Nat) : Int) from by omega,
    BitVec.ofInt_natCast]

theorem callerSp_toNat_eq {tab : Tab} (L : ProgLayout tab) {fl : FrameLayout} {sp : BitVec 64}
    (htop : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat) :
    (sp + BitVec.ofInt 64 fl.frameBytes).toNat = sp.toNat + 8 * fl.frameSlots := by
  have hlt : L.stackTop.toNat < 2 ^ 64 := L.stackTop.isLt
  rw [frameBytesR_toNat_eq fl, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Caller-frame context needed for direct tail-call optimization (TCO):
    records the caller's return PC, return address `ra`, and saved `calleeSavedBank` values. -/
structure TcoCtx where
  callerRetPc : Nat
  callerRa : BitVec 64
  calleeVals : Reg → BitVec 64
  hraAl : callerRa &&& ~~~1#64 = BitVec.ofNat 64 (4 * callerRetPc)

/-- State-dependent invariant for `TcoCtx` at a point during function execution:
    `ra` and `calleeSavedBank` values remain intact in registers or protected frame slots. -/
def TcoStateOk (fl : FrameLayout) (sp : BitVec 64) (tco : TcoCtx) (st : State) : Prop :=
  (fl.isLeaf = true → st.getReg AbiReg.ra = tco.callerRa) ∧
  (fl.isLeaf = false → readWord64 st.mem sp = tco.callerRa) ∧
  (∀ r ∈ calleeSavedBank, r ∉ fl.savedRegs → st.getReg r = tco.calleeVals r) ∧
  (∀ i (hi : i < fl.savedRegs.length),
    readWord64 st.mem (sp + BitVec.ofInt 64 (fl.savedOff i)) = tco.calleeVals (fl.savedRegs[i]'hi))

theorem TcoStateOk.of_step {tab : Tab} (L : ProgLayout tab) {fl : FrameLayout} (hfl : FrameLayoutOk fl)
    {sp : BitVec 64} {tco : TcoCtx} {st1 st2 : State}
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (hpres : PreservedFrameNoS0 fl st1 st2)
    (hout : ProgMemOutside (FnWriteMaskR L fl sp) st1.mem st2.mem)
    (htco : TcoStateOk fl sp tco st1) :
    TcoStateOk fl sp tco st2 := by
  refine ⟨fun hl => (hpres.leafRa hl).trans (htco.1 hl), fun hnl => ?_,
    fun r hr hns => (hpres.regs r (calleeSaved_mem_allowed fl.isLeaf hr)
      (fun hm => hns (hfl.saved_mem_iff.mpr ⟨hr, hm⟩))).trans (htco.2.2.1 r hr hns),
    fun i hi => ?_⟩
  · have hslot0 : 0 < fl.protectedSlots := by
      dsimp only [FrameLayout.protectedSlots, FrameLayout.raSlots]; rw [hnl]
      simp only [Bool.false_eq_true, ↓reduceIte]; omega
    have hsp0 : sp = sp + BitVec.ofNat 64 (8 * 0) := (BitVec.add_zero sp).symm
    rw [← htco.2.1 hnl]
    exact hout.readWord64_eq sp fun k hk => by
      have hnp := @fnWriteMaskR_not_protected _ L fl sp hlo htop 0 hslot0 k hk
      rwa [← hsp0] at hnp
  · have hslot : fl.raSlots + i < fl.protectedSlots := by simp [FrameLayout.protectedSlots]; omega
    rw [← htco.2.2.2 i hi, savedOff_ofInt]
    exact hout.readWord64_eq _ fun k hk => fnWriteMaskR_not_protected L hlo htop hslot hk

/-! ### 1c. Live-Variable Frame Invariant & `stmtVarSafe` / `stmtVarCallFree` Soundness -/

def ghostLoc (fl : FrameLayout) (sp : BitVec 64) (st : State)
    (loc : _root_.L.Locals) (live : Var → Bool) : _root_.L.Locals :=
  fun x =>
    if live x then loc x
    else match fl.alloc.lookup x with
      | some r => UInt64.ofBitVec (st.getReg r)
      | none => UInt64.ofBitVec (readWord64 st.mem (sp + BitVec.ofInt 64 (fl.varSlotOff x)))

theorem ghostLoc_agree (fl : FrameLayout) (sp : BitVec 64) (st : State)
    (loc : _root_.L.Locals) (live : Var → Bool) :
    ∀ x, live x = true → ghostLoc fl sp st loc live x = loc x := by
  intro x hx; simp [ghostLoc, hx]

theorem ghostLoc_frameOk {tab : Tab} {L : ProgLayout tab} {fl : FrameLayout} {sp : BitVec 64}
    {st : State} {loc : _root_.L.Locals} {live : Var → Bool}
    (hf : ProgFrameOkLive L fl sp st loc live) :
    ProgFrameOkR L fl sp st (ghostLoc fl sp st loc live) := by
  intro x hx
  dsimp only [ghostLoc]
  cases hlv : live x with
  | true => simp only [↓reduceIte]; exact hf x hx hlv
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases fl.alloc.lookup x with
    | some r => rfl
    | none => intro _; rfl

theorem ProgFrameOkLive.mono {tab : Tab} {L : ProgLayout tab} {fl : FrameLayout} {sp : BitVec 64}
    {st : State} {loc : _root_.L.Locals} {live1 live2 : Var → Bool}
    (hsub : ∀ x, live2 x = true → live1 x = true)
    (hf : ProgFrameOkLive L fl sp st loc live1) :
    ProgFrameOkLive L fl sp st loc live2 :=
  fun x hx h2 => hf x hx (hsub x h2)

theorem ProgFrameOkLive.of_other_t6 {tab : Tab} {L : ProgLayout tab} {fl : FrameLayout}
    (hfl : FrameLayoutOk fl) {sp : BitVec 64} (hv : (frameSpanR fl sp).valid)
    {st1 st2 : State} {loc : _root_.L.Locals} {live : Var → Bool}
    (hoth : ∀ q, q ≠ AbiReg.t6 ∧ q ≠ AbiReg.s1 → st2.getReg q = st1.getReg q)
    (hmem : st2.mem = st1.mem)
    (hf : ProgFrameOkLive L fl sp st1 loc live) :
    ProgFrameOkLive L fl sp st2 loc live :=
  (ProgFrameOkR.of_preserved_temp hfl hv (Nat.zero_le _)
    ⟨⟨hoth _ (by decide), hoth _ (by decide), hoth _ (by decide), hoth _ (by decide)⟩,
     fun _ => hoth _ (by decide),
     fun _ => hoth _ (by decide),
     fun r hr _ => hoth r ⟨allowedRegs_ne_t6 hr, allowedRegs_ne_s1 hr⟩⟩
    (by rw [hmem]; exact MemEqOutside.refl _ _) (ghostLoc_frameOk hf)).toLive (ghostLoc_agree _ _ _ _ _)

theorem stmtVarSafe_fst (y : Var) (cl : Var → Bool) (isCS : Bool) :
    ∀ (s : Stmt) (na nb : Bool),
      (stmtVarSafe y cl isCS s na nb).1 = (stmtVarCallFree y s na nb).1
  | .skip, _, _ | .brk, _, _ | .set _ _, _, _ | .gset _ _, _, _
  | .st8 _ _ _, _, _ | .st64 _ _ _, _, _ | .st64t _ _ _ _, _, _ | .st32t _ _ _ _, _, _
  | .ret _, _, _ | .abort _, _, _ | .call _ _ _, _, _
  | .copy64 _ _ _ _ _, _, _ | .copy8w _ _ _ _ _, _, _ | .scan8 _ _ _ _ _, _, _ => rfl
  | .seq s1 s2, na, nb => by
    simp only [stmtVarSafe, stmtVarCallFree]
    rw [stmtVarSafe_fst y cl isCS s2 na nb, stmtVarSafe_fst y cl isCS s1]
  | .ite c s1 s2, na, nb => by
    simp only [stmtVarSafe, stmtVarCallFree]
    rw [stmtVarSafe_fst y cl isCS s1 na nb, stmtVarSafe_fst y cl isCS s2 na nb]
  | .while c b, na, nb => by
    simp only [stmtVarSafe, stmtVarCallFree]
    by_cases h1 : (condUsesVar y c || na) = true
    · simp [h1]
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      rw [stmtVarSafe_fst y cl isCS b false na]
      cases (stmtVarCallFree y b false na).1 <;> rfl

theorem stmtVarSafe_while_body_ok (y : Var) (cl : Var → Bool) (isCS : Bool)
    (c : Cond) (b : Stmt) (na nb : Bool) :
    (stmtVarSafe y cl isCS (.while c b) na nb).2 =
    (stmtVarSafe y cl isCS b (stmtVarCallFree y (.while c b) na nb).1 na).2 := by
  simp only [stmtVarSafe, stmtVarCallFree]
  by_cases h1 : (condUsesVar y c || na) = true
  · simp [h1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    rw [stmtVarSafe_fst y cl isCS b false na]
    cases (stmtVarCallFree y b false na).1 <;> rfl

private theorem stmtVarCallFree_imp_stmtVarLive (y : Var) :
    ∀ (s : Stmt) (na nb : Bool),
      (stmtVarCallFree y s na nb).1 = true →
      (stmtVarLive y s).1 = true ∨ (na = true ∧ (stmtVarLive y s).2 = false) ∨ nb = true
  | .skip, na, _, h => by simp [stmtVarCallFree] at h; exact Or.inr (Or.inl ⟨h, rfl⟩)
  | .brk, _, nb, h => by simp [stmtVarCallFree] at h; exact Or.inr (Or.inr h)
  | .set x e, na, _, h => by
    simp only [stmtVarCallFree, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne] at h
    rcases h with h | ⟨hna, hne⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hna, by simp [stmtVarLive, beq_false_of_ne hne]⟩)
  | .scan8 x _ i e _, na, _, h => by
    simp only [stmtVarCallFree, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne] at h
    rcases h with (h | h) | ⟨hna, hne⟩
    · exact Or.inl (by simp [stmtVarLive, h])
    · exact Or.inl (by simp [stmtVarLive, h])
    · exact Or.inr (Or.inl ⟨hna, by simp [stmtVarLive, beq_false_of_ne hne]⟩)
  | .gset _ e, na, _, h => by
    simp only [stmtVarCallFree, Bool.or_eq_true] at h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h, rfl⟩)
  | .abort e, _, _, h => Or.inl h
  | .st8 _ i e, na, _, h | .st64 _ i e, na, _, h => by
    simp only [stmtVarCallFree, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · exact Or.inl (by simp [stmtVarLive, h])
    · exact Or.inl (by simp [stmtVarLive, h])
    · exact Or.inr (Or.inl ⟨h, rfl⟩)
  | .st64t _ t i e, na, _, h | .st32t _ t i e, na, _, h => by
    simp only [stmtVarCallFree, Bool.or_eq_true] at h
    rcases h with ((h | h) | h) | h
    · exact Or.inl (by simp [stmtVarLive, h])
    · exact Or.inl (by simp [stmtVarLive, h])
    · exact Or.inl (by simp [stmtVarLive, h])
    · exact Or.inr (Or.inl ⟨h, rfl⟩)
  | .ret es, _, _, h => Or.inl h
  | .call xs _ args, na, _, h => by
    simp only [stmtVarCallFree, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases h with h | ⟨hna, hnin⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hna, by simpa [stmtVarLive] using hnin⟩)
  | .copy64 d di s si n, na, _, h => by
    simp only [stmtVarCallFree, Bool.or_eq_true] at h
    rcases h with ((((h | h) | h) | h) | h) | h
    · exact Or.inl (by simp [stmtVarLive, h])
    · exact Or.inl (by simp [stmtVarLive, h])
    · exact Or.inl (by simp [stmtVarLive, h])
    · exact Or.inl (by simp [stmtVarLive, h])
    · exact Or.inl (by simp [stmtVarLive, h])
    · exact Or.inr (Or.inl ⟨h, rfl⟩)
  | .copy8w d di _ si n, na, _, h => by
    simp only [stmtVarCallFree, Bool.or_eq_true] at h
    rcases h with (((h | h) | h) | h) | h
    · exact Or.inl (by simp [stmtVarLive, h])
    · exact Or.inl (by simp [stmtVarLive, h])
    · exact Or.inl (by simp [stmtVarLive, h])
    · exact Or.inl (by simp [stmtVarLive, h])
    · exact Or.inr (Or.inl ⟨h, rfl⟩)
  | .seq s1 s2, na, nb, h => by
    simp only [stmtVarCallFree] at h
    rcases stmtVarCallFree_imp_stmtVarLive y s1 (stmtVarCallFree y s2 na nb).1 nb h with h1 | ⟨hn2, hw1⟩ | hnb
    · exact Or.inl (by simp [stmtVarLive, h1])
    · rcases stmtVarCallFree_imp_stmtVarLive y s2 na nb hn2 with h2 | ⟨hna, hw2⟩ | hnb
      · exact Or.inl (by simp [stmtVarLive, hw1, h2])
      · exact Or.inr (Or.inl ⟨hna, by simp [stmtVarLive, hw1, hw2]⟩)
      · exact Or.inr (Or.inr hnb)
    · exact Or.inr (Or.inr hnb)
  | .ite c s1 s2, na, nb, h => by
    simp only [stmtVarCallFree, Bool.or_eq_true] at h
    rcases h with (hc | h1) | h2
    · exact Or.inl (by simp [stmtVarLive, hc])
    · rcases stmtVarCallFree_imp_stmtVarLive y s1 na nb h1 with hr | ⟨hna, hw⟩ | hnb
      · exact Or.inl (by simp [stmtVarLive, hr])
      · exact Or.inr (Or.inl ⟨hna, by simp [stmtVarLive, hw]⟩)
      · exact Or.inr (Or.inr hnb)
    · rcases stmtVarCallFree_imp_stmtVarLive y s2 na nb h2 with hr | ⟨hna, hw⟩ | hnb
      · exact Or.inl (by simp [stmtVarLive, hr])
      · exact Or.inr (Or.inl ⟨hna, by simp [stmtVarLive, hw]⟩)
      · exact Or.inr (Or.inr hnb)
  | .while c b, na, _, h => by
    simp only [stmtVarCallFree] at h
    by_cases h1 : (condUsesVar y c || na) = true
    · simp only [Bool.or_eq_true] at h1
      rcases h1 with hc | hna
      · exact Or.inl (by simp [stmtVarLive, hc])
      · exact Or.inr (Or.inl ⟨hna, rfl⟩)
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
      have hnaF : na = false := by
        cases na
        · rfl
        · simp at h1
      have hnb1 : (stmtVarCallFree y b false false).1 = true := by
        rw [hnaF] at h
        cases hb : (stmtVarCallFree y b false false).1
        · rw [hb] at h; cases h
        · rfl
      rcases stmtVarCallFree_imp_stmtVarLive y b false false hnb1 with hr | ⟨hf, _⟩ | hf
      · exact Or.inl (by simp [stmtVarLive, hr])
      · cases hf
      · cases hf

theorem stmtVarCallFree_imp_varNeedsZeroInit (fd : FunDecl) (y : Var)
    (h : (stmtVarCallFree y fd.body false false).1 = true) :
    varNeedsZeroInit fd y = true := by
  rcases stmtVarCallFree_imp_stmtVarLive y fd.body false false h with hr | ⟨hf, _⟩ | hf
  · exact hr
  · cases hf
  · cases hf

private theorem exprUsesVar_lt_of_exprOkB {tab : Tab} {nl : Nat} {x : Var} :
    ∀ {e : Expr}, exprOkB tab nl e = true → exprUsesVar x e = true → x < nl
  | .const _, _, hu => by simp [exprUsesVar] at hu
  | .var y, hok, hu => by
    simp only [exprUsesVar, beq_iff_eq] at hu; subst hu
    simpa [exprOkB] using hok
  | .len8 _, _, hu | .len64 _, _, hu | .glob _, _, hu => by simp [exprUsesVar] at hu
  | .ld8 _ i, hok, hu | .ld64 _ i, hok, hu | .ldc _ i, hok, hu | .len64t _ i, hok, hu => by
    simp only [exprOkB, Bool.and_eq_true] at hok
    exact exprUsesVar_lt_of_exprOkB hok.2 hu
  | .ld8x8 src i, hok, hu => by
    cases src <;> (simp only [exprOkB, Bool.and_eq_true] at hok; exact exprUsesVar_lt_of_exprOkB hok.2 hu)
  | .bin _ a b, hok, hu | .cmpw _ a b, hok, hu => by
    simp only [exprOkB, Bool.and_eq_true] at hok
    simp only [exprUsesVar, Bool.or_eq_true] at hu
    rcases hu with h | h
    · exact exprUsesVar_lt_of_exprOkB hok.1 h
    · exact exprUsesVar_lt_of_exprOkB hok.2 h
  | .ld64t _ t i, hok, hu | .ld32t _ t i, hok, hu | .ld32h _ t i _, hok, hu => by
    simp only [exprOkB, Bool.and_eq_true] at hok
    simp only [exprUsesVar, Bool.or_eq_true] at hu
    rcases hu with h | h
    · exact exprUsesVar_lt_of_exprOkB hok.1.2 h
    · exact exprUsesVar_lt_of_exprOkB hok.2 h

private theorem condUsesVar_lt_of_condOkB {tab : Tab} {nl : Nat} {x : Var} :
    ∀ {c : Cond}, condOkB tab nl c = true → condUsesVar x c = true → x < nl := by
  intro c
  induction c with
  | cmp _ a b =>
    intro hok hu
    simp only [condOkB, Bool.and_eq_true] at hok
    simp only [condUsesVar, Bool.or_eq_true] at hu
    rcases hu with h | h
    · exact exprUsesVar_lt_of_exprOkB hok.1 h
    · exact exprUsesVar_lt_of_exprOkB hok.2 h
  | and p q ihp ihq =>
    intro hok hu
    simp only [condOkB, Bool.and_eq_true] at hok
    simp only [condUsesVar, Bool.or_eq_true] at hu
    rcases hu with h | h
    · exact ihp hok.1 h
    · exact ihq hok.2 h
  | or p q ihp ihq =>
    intro hok hu
    simp only [condOkB, Bool.and_eq_true] at hok
    simp only [condUsesVar, Bool.or_eq_true] at hu
    rcases hu with h | h
    · exact ihp hok.1 h
    · exact ihq hok.2 h
  | not p ihp =>
    intro hok hu
    exact ihp hok hu

private theorem warrUsesVar_lt_of_warrOkB {tab : Tab} {nl : Nat} {x : Var} :
    ∀ {w : WArr}, warrOkB tab nl w = true → warrUsesVar x w = true → x < nl
  | .plain _, _, hu => by simp [warrUsesVar] at hu
  | .tier _ t, hok, hu => by
    simp only [warrOkB, Bool.and_eq_true] at hok
    exact exprUsesVar_lt_of_exprOkB hok.2 hu

private theorem exprsUsesVar_lt_of_all {tab : Tab} {nl : Nat} {x : Var} :
    ∀ {es : List Expr}, es.all (exprOkB tab nl) = true → es.any (exprUsesVar x) = true → x < nl
  | [], _, hu => by simp at hu
  | e :: rest, hok, hu => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    simp only [List.any_cons, Bool.or_eq_true] at hu
    rcases hu with h | h
    · exact exprUsesVar_lt_of_exprOkB hok.1 h
    · exact exprsUsesVar_lt_of_all hok.2 h

theorem stmtUsesVar_lt_of_stmtOkB {tab : Tab} {p : Prog} {nl : Nat} {x : Var} :
    ∀ {inLoop : Bool} {s : Stmt}, stmtOkB tab p nl inLoop s = true → stmtUsesVar x s = true → x < nl
  | _, .skip, _, hu | _, .brk, _, hu => by simp [stmtUsesVar] at hu
  | _, .set _ e, hok, hu | _, .gset _ e, hok, hu => by
    simp only [stmtOkB, Bool.and_eq_true] at hok
    exact exprUsesVar_lt_of_exprOkB hok.2 hu
  | _, .abort e, hok, hu => exprUsesVar_lt_of_exprOkB hok hu
  | _, .st8 _ _ _, hok, _ => by simp [stmtOkB] at hok
  | _, .st64 _ i e, hok, hu => by
    simp only [stmtOkB, Bool.and_eq_true] at hok
    simp only [stmtUsesVar, Bool.or_eq_true] at hu
    rcases hu with h | h
    · exact exprUsesVar_lt_of_exprOkB hok.1.2 h
    · exact exprUsesVar_lt_of_exprOkB hok.2 h
  | _, .st64t _ t i e, hok, hu | _, .st32t _ t i e, hok, hu => by
    simp only [stmtOkB, Bool.and_eq_true] at hok
    simp only [stmtUsesVar, Bool.or_eq_true] at hu
    rcases hu with (h | h) | h
    · exact exprUsesVar_lt_of_exprOkB hok.1.1.2 h
    · exact exprUsesVar_lt_of_exprOkB hok.1.2 h
    · exact exprUsesVar_lt_of_exprOkB hok.2 h
  | _, .seq s1 s2, hok, hu => by
    simp only [stmtOkB, Bool.and_eq_true] at hok
    simp only [stmtUsesVar, Bool.or_eq_true] at hu
    rcases hu with h | h
    · exact stmtUsesVar_lt_of_stmtOkB hok.1 h
    · exact stmtUsesVar_lt_of_stmtOkB hok.2 h
  | _, .ite c s1 s2, hok, hu => by
    simp only [stmtOkB, Bool.and_eq_true] at hok
    simp only [stmtUsesVar, Bool.or_eq_true] at hu
    rcases hu with (h | h) | h
    · exact condUsesVar_lt_of_condOkB hok.1.1 h
    · exact stmtUsesVar_lt_of_stmtOkB hok.1.2 h
    · exact stmtUsesVar_lt_of_stmtOkB hok.2 h
  | _, .while c b, hok, hu => by
    simp only [stmtOkB, Bool.and_eq_true] at hok
    simp only [stmtUsesVar, Bool.or_eq_true] at hu
    rcases hu with h | h
    · exact condUsesVar_lt_of_condOkB hok.1 h
    · exact stmtUsesVar_lt_of_stmtOkB hok.2 h
  | _, .ret es, hok, hu => by
    simp only [stmtOkB, Bool.and_eq_true] at hok
    exact exprsUsesVar_lt_of_all hok.2 hu
  | _, .call _ _ args, hok, hu => by
    simp only [stmtOkB, Bool.and_eq_true] at hok
    exact exprsUsesVar_lt_of_all hok.2 hu
  | _, .copy64 d di s si n, hok, hu => by
    simp only [stmtOkB, Bool.and_eq_true] at hok
    simp only [stmtUsesVar, Bool.or_eq_true] at hu
    rcases hu with (((h | h) | h) | h) | h
    · exact warrUsesVar_lt_of_warrOkB hok.1.1.1.1 h
    · exact exprUsesVar_lt_of_exprOkB hok.1.1.1.2 h
    · exact warrUsesVar_lt_of_warrOkB hok.1.1.2 h
    · exact exprUsesVar_lt_of_exprOkB hok.1.2 h
    · exact exprUsesVar_lt_of_exprOkB hok.2 h
  | _, .copy8w d di _ si n, hok, hu => by
    simp only [stmtOkB, Bool.and_eq_true] at hok
    simp only [stmtUsesVar, Bool.or_eq_true] at hu
    rcases hu with ((h | h) | h) | h
    · exact warrUsesVar_lt_of_warrOkB hok.1.1.1.1 h
    · exact exprUsesVar_lt_of_exprOkB hok.1.1.1.2 h
    · exact exprUsesVar_lt_of_exprOkB hok.1.2 h
    · exact exprUsesVar_lt_of_exprOkB hok.2 h
  | _, .scan8 _ _ i e _, hok, hu => by
    simp only [stmtOkB, Bool.and_eq_true] at hok
    simp only [stmtUsesVar, Bool.or_eq_true] at hu
    rcases hu with h | h
    · exact exprUsesVar_lt_of_exprOkB hok.1.1.1.2 h
    · exact exprUsesVar_lt_of_exprOkB hok.1.1.2 h

theorem stmtVarCallFree_while_cond (x : Var) (c : Cond) (b : Stmt) (na nb : Bool)
    (hc : condUsesVar x c = true) :
    (stmtVarCallFree x (.while c b) na nb).1 = true := by
  simp [stmtVarCallFree, hc]

theorem stmtVarCallFree_while_na (x : Var) (c : Cond) (b : Stmt) (na nb : Bool)
    (hna : na = true) :
    (stmtVarCallFree x (.while c b) na nb).1 = true := by
  simp [stmtVarCallFree, hna]

theorem stmtVarCallFree_while_body_live (x : Var) (c : Cond) (b : Stmt) (na nb : Bool) :
    (stmtVarCallFree x b (stmtVarCallFree x (.while c b) na nb).1 na).1 = true →
    (stmtVarCallFree x (.while c b) na nb).1 = true := by
  simp only [stmtVarCallFree]
  by_cases h1 : (condUsesVar x c || na) = true
  · simp [h1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases hb : (stmtVarCallFree x b false na).1 <;> simp [hb]

private theorem stmtVarCallFree_while_body_ok (x : Var) (c : Cond) (b : Stmt) (na nb : Bool) :
    (stmtVarCallFree x (.while c b) na nb).2 =
    (stmtVarCallFree x b (stmtVarCallFree x (.while c b) na nb).1 na).2 := by
  simp only [stmtVarCallFree]
  by_cases h1 : (condUsesVar x c || na) = true
  · simp [h1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases (stmtVarCallFree x b false na).1 <;> rfl

private theorem evalE_congr_uses (e : Expr) (m : _root_.L.Mem) (l1 l2 : _root_.L.Locals)
    (hag : ∀ x, exprUsesVar x e = true → l1 x = l2 x) :
    match _root_.L.evalE e ⟨m, l1⟩, _root_.L.evalE e ⟨m, l2⟩ with
    | .ok (v1, _), .ok (v2, _) => v1 = v2
    | .error e1, .error e2 => e1 = e2
    | _, _ => False := by
  induction e with
  | const _ | len8 _ | len64 _ | glob _ => rfl
  | var y => exact hag y (by simp [exprUsesVar])
  | ld8 a i ih =>
    have h := ih (fun x hx => hag x (by simpa [exprUsesVar] using hx))
    rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨v2, h2⟩ | h2 <;>
    simp only [h1, h2] at h
    · subst h
      dsimp only [_root_.L.evalE]
      simp only [Bind.bind, StateT.bind, Except.bind, h1, h2, _root_.L.ld8, get, getThe,
        MonadStateOf.get, StateT.get, Pure.pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, Function.comp_apply]
      by_cases hb : v1.toNat < (m.arr8 a).size <;> simp only [hb] <;> rfl
    · dsimp only [_root_.L.evalE]; simp only [Bind.bind, StateT.bind, Except.bind, h1, h2]
  | ld64 a i ih =>
    have h := ih (fun x hx => hag x (by simpa [exprUsesVar] using hx))
    rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨v2, h2⟩ | h2 <;>
    simp only [h1, h2] at h
    · subst h
      dsimp only [_root_.L.evalE]
      simp only [Bind.bind, StateT.bind, Except.bind, h1, h2, _root_.L.ld64, get, getThe,
        MonadStateOf.get, StateT.get, Pure.pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, Function.comp_apply]
      by_cases hb : v1.toNat < (m.arr64 (.t0 a)).size <;> simp only [hb] <;> rfl
    · dsimp only [_root_.L.evalE]; simp only [Bind.bind, StateT.bind, Except.bind, h1, h2]
  | ldc d i ih =>
    have h := ih (fun x hx => hag x (by simpa [exprUsesVar] using hx))
    rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨v2, h2⟩ | h2 <;>
    simp only [h1, h2] at h
    · subst h
      dsimp only [_root_.L.evalE]
      simp only [Bind.bind, StateT.bind, Except.bind, h1, h2, _root_.L.ldc,
        Pure.pure, throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
      by_cases hb : v1.toNat < d.length <;> simp only [hb] <;> rfl
    · dsimp only [_root_.L.evalE]; simp only [Bind.bind, StateT.bind, Except.bind, h1, h2]
  | ld8x8 src i ih =>
    have h := ih (fun x hx => hag x (by simpa [exprUsesVar] using hx))
    rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨v2, h2⟩ | h2 <;>
    simp only [h1, h2] at h
    · subst h
      dsimp only [_root_.L.evalE]
      simp only [Bind.bind, StateT.bind, Except.bind, h1, h2, _root_.L.ld8x8, get, getThe,
        MonadStateOf.get, StateT.get, Pure.pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, Function.comp_apply]
      by_cases hb : v1.toNat + 8 ≤ (m.src8 src).size <;> simp only [hb, ↓reduceIte] <;> rfl
    · dsimp only [_root_.L.evalE]; simp only [Bind.bind, StateT.bind, Except.bind, h1, h2]
  | len64t a t ih =>
    have h := ih (fun x hx => hag x (by simpa [exprUsesVar] using hx))
    rcases _root_.L.evalE_pure t ⟨m, l1⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure t ⟨m, l2⟩ with ⟨v2, h2⟩ | h2 <;>
    simp only [h1, h2] at h
    · subst h
      dsimp only [_root_.L.evalE]
      simp only [Bind.bind, StateT.bind, Except.bind, h1, h2, get, getThe,
        MonadStateOf.get, StateT.get, Pure.pure, StateT.pure, Except.pure]
    · dsimp only [_root_.L.evalE]; simp only [Bind.bind, StateT.bind, Except.bind, h1, h2]
  | bin op a b iha ihb =>
    have ha := iha (fun x hx => hag x (by simp [exprUsesVar, hx]))
    have hb := ihb (fun x hx => hag x (by simp [exprUsesVar, hx]))
    rcases _root_.L.evalE_pure a ⟨m, l1⟩ with ⟨va1, ha1⟩ | ha1 <;>
    rcases _root_.L.evalE_pure a ⟨m, l2⟩ with ⟨va2, ha2⟩ | ha2 <;>
    simp only [ha1, ha2] at ha
    · subst ha
      rcases _root_.L.evalE_pure b ⟨m, l1⟩ with ⟨vb1, hb1⟩ | hb1 <;>
      rcases _root_.L.evalE_pure b ⟨m, l2⟩ with ⟨vb2, hb2⟩ | hb2 <;>
      simp only [hb1, hb2] at hb
      · subst hb
        simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ha1, ha2, hb1, hb2, Pure.pure, StateT.pure, Except.pure]
      · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ha1, ha2, hb1, hb2]
    · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ha1, ha2]
  | cmpw c a b iha ihb =>
    have ha := iha (fun x hx => hag x (by simp [exprUsesVar, hx]))
    have hb := ihb (fun x hx => hag x (by simp [exprUsesVar, hx]))
    rcases _root_.L.evalE_pure a ⟨m, l1⟩ with ⟨va1, ha1⟩ | ha1 <;>
    rcases _root_.L.evalE_pure a ⟨m, l2⟩ with ⟨va2, ha2⟩ | ha2 <;>
    simp only [ha1, ha2] at ha
    · subst ha
      rcases _root_.L.evalE_pure b ⟨m, l1⟩ with ⟨vb1, hb1⟩ | hb1 <;>
      rcases _root_.L.evalE_pure b ⟨m, l2⟩ with ⟨vb2, hb2⟩ | hb2 <;>
      simp only [hb1, hb2] at hb
      · subst hb
        simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ha1, ha2, hb1, hb2, Pure.pure, StateT.pure, Except.pure]
      · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ha1, ha2, hb1, hb2]
    · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ha1, ha2]
  | ld64t a t i iht ihi =>
    have ht := iht (fun x hx => hag x (by simp [exprUsesVar, hx]))
    have hi := ihi (fun x hx => hag x (by simp [exprUsesVar, hx]))
    rcases _root_.L.evalE_pure t ⟨m, l1⟩ with ⟨vt1, ht1⟩ | ht1 <;>
    rcases _root_.L.evalE_pure t ⟨m, l2⟩ with ⟨vt2, ht2⟩ | ht2 <;>
    simp only [ht1, ht2] at ht
    · subst ht
      rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨vi1, hi1⟩ | hi1 <;>
      rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨vi2, hi2⟩ | hi2 <;>
      simp only [hi1, hi2] at hi
      · subst hi
        simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2, _root_.L.ld64,
          get, getThe, MonadStateOf.get, StateT.get, Pure.pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
        by_cases hb : vi1.toNat < (m.arr64 (tierA a vt1)).size <;> simp only [hb] <;> rfl
      · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2]
    · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2]
  | ld32t a t i iht ihi =>
    have ht := iht (fun x hx => hag x (by simp [exprUsesVar, hx]))
    have hi := ihi (fun x hx => hag x (by simp [exprUsesVar, hx]))
    rcases _root_.L.evalE_pure t ⟨m, l1⟩ with ⟨vt1, ht1⟩ | ht1 <;>
    rcases _root_.L.evalE_pure t ⟨m, l2⟩ with ⟨vt2, ht2⟩ | ht2 <;>
    simp only [ht1, ht2] at ht
    · subst ht
      rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨vi1, hi1⟩ | hi1 <;>
      rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨vi2, hi2⟩ | hi2 <;>
      simp only [hi1, hi2] at hi
      · subst hi
        simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2, _root_.L.ld32,
          get, getThe, MonadStateOf.get, StateT.get, Pure.pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
        by_cases hb : (vi1 / 2).toNat < (m.arr64 (tierA a vt1)).size <;> simp only [hb] <;> rfl
      · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2]
    · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2]
  | ld32h a t i hiFlag iht ihi =>
    have ht := iht (fun x hx => hag x (by simp [exprUsesVar, hx]))
    have hi := ihi (fun x hx => hag x (by simp [exprUsesVar, hx]))
    rcases _root_.L.evalE_pure t ⟨m, l1⟩ with ⟨vt1, ht1⟩ | ht1 <;>
    rcases _root_.L.evalE_pure t ⟨m, l2⟩ with ⟨vt2, ht2⟩ | ht2 <;>
    simp only [ht1, ht2] at ht
    · subst ht
      rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨vi1, hi1⟩ | hi1 <;>
      rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨vi2, hi2⟩ | hi2 <;>
      simp only [hi1, hi2] at hi
      · subst hi
        simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2, _root_.L.ld64,
          get, getThe, MonadStateOf.get, StateT.get, Pure.pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
        by_cases hb : vi1.toNat < (m.arr64 (tierA a vt1)).size <;> simp only [hb] <;> rfl
      · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2]
    · simp only [_root_.L.evalE, Bind.bind, StateT.bind, Except.bind, ht1, ht2]

theorem evalC_congr_uses (c : Cond) (m : _root_.L.Mem) (l1 l2 : _root_.L.Locals)
    (hag : ∀ x, condUsesVar x c = true → l1 x = l2 x) :
    match _root_.L.evalC c ⟨m, l1⟩, _root_.L.evalC c ⟨m, l2⟩ with
    | .ok (b1, _), .ok (b2, _) => b1 = b2
    | .error e1, .error e2 => e1 = e2
    | _, _ => False := by
  induction c with
  | cmp op a b =>
    have ha := evalE_congr_uses a m l1 l2 (fun x hx => hag x (by simp [condUsesVar, hx]))
    have hb := evalE_congr_uses b m l1 l2 (fun x hx => hag x (by simp [condUsesVar, hx]))
    rcases _root_.L.evalE_pure a ⟨m, l1⟩ with ⟨va1, ha1⟩ | ha1 <;>
    rcases _root_.L.evalE_pure a ⟨m, l2⟩ with ⟨va2, ha2⟩ | ha2 <;>
    simp only [ha1, ha2] at ha
    · subst ha
      rcases _root_.L.evalE_pure b ⟨m, l1⟩ with ⟨vb1, hb1⟩ | hb1 <;>
      rcases _root_.L.evalE_pure b ⟨m, l2⟩ with ⟨vb2, hb2⟩ | hb2 <;>
      simp only [hb1, hb2] at hb
      · subst hb
        simp only [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, ha1, ha2, hb1, hb2, Pure.pure, StateT.pure, Except.pure]
      · simp only [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, ha1, ha2, hb1, hb2]
    · simp only [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, ha1, ha2]
  | not p ih =>
    have hp := ih (fun x hx => hag x (by simpa [condUsesVar] using hx))
    rcases _root_.L.evalC_pure p ⟨m, l1⟩ with ⟨b1, h1⟩ | h1 <;>
    rcases _root_.L.evalC_pure p ⟨m, l2⟩ with ⟨b2, h2⟩ | h2 <;>
    simp only [h1, h2] at hp
    · subst hp
      simp only [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, h1, h2, Pure.pure, StateT.pure, Except.pure]
    · simp only [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, h1, h2]
  | and p q ihp ihq =>
    have hp := ihp (fun x hx => hag x (by simp [condUsesVar, hx]))
    have hq := ihq (fun x hx => hag x (by simp [condUsesVar, hx]))
    rcases _root_.L.evalC_pure p ⟨m, l1⟩ with ⟨b1, h1⟩ | h1 <;>
    rcases _root_.L.evalC_pure p ⟨m, l2⟩ with ⟨b2, h2⟩ | h2 <;>
    simp only [h1, h2] at hp
    · subst hp
      cases b1
      · simp only [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, h1, h2, Bool.false_eq_true, ↓reduceIte,
          Pure.pure, StateT.pure, Except.pure]
      · simp only [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, h1, h2, ↓reduceIte]
        exact hq
    · simp only [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, h1, h2]
  | or p q ihp ihq =>
    have hp := ihp (fun x hx => hag x (by simp [condUsesVar, hx]))
    have hq := ihq (fun x hx => hag x (by simp [condUsesVar, hx]))
    rcases _root_.L.evalC_pure p ⟨m, l1⟩ with ⟨b1, h1⟩ | h1 <;>
    rcases _root_.L.evalC_pure p ⟨m, l2⟩ with ⟨b2, h2⟩ | h2 <;>
    simp only [h1, h2] at hp
    · subst hp
      cases b1
      · simp only [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, h1, h2, Bool.false_eq_true, ↓reduceIte]
        exact hq
      · simp only [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, h1, h2, ↓reduceIte,
          Pure.pure, StateT.pure, Except.pure]
    · simp only [_root_.L.evalC, Bind.bind, StateT.bind, Except.bind, h1, h2]

theorem evalArgs_congr_uses (es : List Expr) (m : _root_.L.Mem) (l1 l2 : _root_.L.Locals)
    (hag : ∀ x, es.any (exprUsesVar x) = true → l1 x = l2 x) :
    match _root_.L.evalArgs es ⟨m, l1⟩, _root_.L.evalArgs es ⟨m, l2⟩ with
    | .ok (vs1, _), .ok (vs2, _) => vs1 = vs2
    | .error e1, .error e2 => e1 = e2
    | _, _ => False := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have he := evalE_congr_uses e m l1 l2 (fun x hx => hag x (by simp [hx]))
    have hes := ih (fun x hx => hag x (by simp [hx]))
    rcases _root_.L.evalE_pure e ⟨m, l1⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure e ⟨m, l2⟩ with ⟨v2, h2⟩ | h2 <;>
    simp only [h1, h2] at he
    · subst he
      rcases _root_.L.evalArgs_pure es ⟨m, l1⟩ with ⟨vs1, hs1⟩ | hs1 <;>
      rcases _root_.L.evalArgs_pure es ⟨m, l2⟩ with ⟨vs2, hs2⟩ | hs2 <;>
      simp only [hs1, hs2] at hes
      · subst hes
        simp only [_root_.L.evalArgs, Bind.bind, StateT.bind, Except.bind, h1, h2, hs1, hs2,
          Pure.pure, StateT.pure, Except.pure]
      · simp only [_root_.L.evalArgs, Bind.bind, StateT.bind, Except.bind, h1, h2, hs1, hs2]
    · simp only [_root_.L.evalArgs, Bind.bind, StateT.bind, Except.bind, h1, h2]

private theorem warr_congr_uses (w : WArr) (m : _root_.L.Mem) (l1 l2 : _root_.L.Locals)
    (hag : ∀ x, warrUsesVar x w = true → l1 x = l2 x) :
    match _root_.L.warr w ⟨m, l1⟩, _root_.L.warr w ⟨m, l2⟩ with
    | .ok (a1, _), .ok (a2, _) => a1 = a2
    | .error e1, .error e2 => e1 = e2
    | _, _ => False := by
  cases w with
  | plain _ => rfl
  | tier a t =>
    have ht := evalE_congr_uses t m l1 l2 (fun x hx => hag x (by simpa [warrUsesVar] using hx))
    rcases _root_.L.evalE_pure t ⟨m, l1⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure t ⟨m, l2⟩ with ⟨v2, h2⟩ | h2 <;>
    simp only [h1, h2] at ht
    · subst ht
      simp only [_root_.L.warr, Bind.bind, StateT.bind, Except.bind, h1, h2, Pure.pure, StateT.pure, Except.pure]
    · simp only [_root_.L.warr, Bind.bind, StateT.bind, Except.bind, h1, h2]

theorem setLocs_congr (xs : List Var) (vs : List _root_.L.Word) (m : _root_.L.Mem)
    (l1 l2 : _root_.L.Locals) (na : Var → Bool)
    (hag : ∀ x, (na x && !(x ∈ xs)) = true → l1 x = l2 x) :
    ∀ x, na x = true →
      (({ mem := m, loc := l1 } : _root_.L.St).setLocs xs vs).loc x =
      (({ mem := m, loc := l2 } : _root_.L.St).setLocs xs vs).loc x := by
  induction xs generalizing vs l1 l2 with
  | nil =>
    intro x hna
    exact hag x (by simp [hna])
  | cons z zs ih =>
    simp only [_root_.L.St.setLocs, _root_.L.St.setLoc]
    apply ih vs.tail (fun w => if w = z then vs.headD 0 else l1 w) (fun w => if w = z then vs.headD 0 else l2 w)
    intro w hw
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hw
    by_cases hwz : w = z
    · simp [hwz]
    · simp only [hwz, ↓reduceIte]
      exact hag w (by simp [hw.1, hwz, hw.2])

/-- Soundness of backward liveness `stmtVarCallFree`: if `l1, l2` agree on all variables live before `s`
    under exit liveness `(na, nb)`, then `stackNeedB` and `execB` agree, and post-execution locals
    agree on `na` (at `.normal`) and `nb` (at `.brk`). -/
theorem execB_congr_callFree (p : Prog) :
    ∀ (b : Nat) (s : Stmt) (na nb : Var → Bool) (m : _root_.L.Mem) (l1 l2 : _root_.L.Locals),
      (∀ x, (stmtVarCallFree x s (na x) (nb x)).1 = true → l1 x = l2 x) →
      stackNeedB p b s ⟨m, l1⟩ = stackNeedB p b s ⟨m, l2⟩ ∧
      match execB p b s ⟨m, l1⟩, execB p b s ⟨m, l2⟩ with
      | .error e1, .error e2 => e1 = e2
      | .ok (sig1, st1', b1), .ok (sig2, st2', b2) =>
        sig1 = sig2 ∧ st1'.mem = st2'.mem ∧ b1 = b2 ∧
        (sig1 = .normal → ∀ x, na x = true → st1'.loc x = st2'.loc x) ∧
        (sig1 = .brk → ∀ x, nb x = true → st1'.loc x = st2'.loc x)
      | _, _ => False := by
  refine execB_ind (P := fun b s =>
      ∀ (na nb : Var → Bool) (m : _root_.L.Mem) (l1 l2 : _root_.L.Locals),
        (∀ x, (stmtVarCallFree x s (na x) (nb x)).1 = true → l1 x = l2 x) →
        stackNeedB p b s ⟨m, l1⟩ = stackNeedB p b s ⟨m, l2⟩ ∧
        match execB p b s ⟨m, l1⟩, execB p b s ⟨m, l2⟩ with
        | .error e1, .error e2 => e1 = e2
        | .ok (sig1, st1', b1), .ok (sig2, st2', b2) =>
          sig1 = sig2 ∧ st1'.mem = st2'.mem ∧ b1 = b2 ∧
          (sig1 = .normal → ∀ x, na x = true → st1'.loc x = st2'.loc x) ∧
          (sig1 = .brk → ∀ x, nb x = true → st1'.loc x = st2'.loc x)
        | _, _ => False) fun b s ih na nb m l1 l2 hag => ?_
  cases s with
  | skip =>
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    rw [execB_skip, execB_skip]
    exact ⟨rfl, rfl, rfl, fun _ x hx => hag x hx, fun h => by cases h⟩
  | brk =>
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    rw [execB_brk, execB_brk]
    exact ⟨rfl, rfl, rfl, (fun h => by cases h), fun _ x hx => hag x hx⟩
  | set z e =>
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    have he := evalE_congr_uses e m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    rw [execB_set, execB_set]
    rcases _root_.L.evalE_pure e ⟨m, l1⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure e ⟨m, l2⟩ with ⟨v2, h2⟩ | h2
    · rw [h1, h2] at he ⊢; subst he
      refine ⟨rfl, rfl, rfl, fun _ x hna => ?_, fun h => by cases h⟩
      simp only [_root_.L.St.setLoc]
      by_cases hxz : x = z
      · simp [hxz]
      · simp only [hxz, ↓reduceIte]
        exact hag x (by simp [stmtVarCallFree, hna, bne_iff_ne.mpr (Ne.symm hxz)])
    · rw [h1, h2] at he; exact False.elim he
    · rw [h1, h2] at he; exact False.elim he
    · rw [h1, h2]
  | gset g e =>
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    have he := evalE_congr_uses e m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    rw [execB_gset, execB_gset]
    rcases _root_.L.evalE_pure e ⟨m, l1⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure e ⟨m, l2⟩ with ⟨v2, h2⟩ | h2
    · rw [h1, h2] at he ⊢; subst he
      exact ⟨rfl, rfl, rfl, fun _ x hna => hag x (by simp [stmtVarCallFree, hna]), fun h => by cases h⟩
    · rw [h1, h2] at he; exact False.elim he
    · rw [h1, h2] at he; exact False.elim he
    · rw [h1, h2]
  | abort e =>
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    have he := evalE_congr_uses e m l1 l2 (fun x hx => hag x (by simpa [stmtVarCallFree] using hx))
    rw [execB_abort, execB_abort]
    rcases _root_.L.evalE_pure e ⟨m, l1⟩ with ⟨v1, h1⟩ | h1 <;>
    rcases _root_.L.evalE_pure e ⟨m, l2⟩ with ⟨v2, h2⟩ | h2
    · rw [h1, h2] at he ⊢; subst he; rfl
    · rw [h1, h2] at he; exact False.elim he
    · rw [h1, h2] at he; exact False.elim he
    · rw [h1, h2]
  | ret es =>
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    have hes := evalArgs_congr_uses es m l1 l2 (fun x hx => hag x (by simpa [stmtVarCallFree] using hx))
    rw [execB_ret, execB_ret]
    rcases _root_.L.evalArgs_pure es ⟨m, l1⟩ with ⟨vs1, h1⟩ | h1 <;>
    rcases _root_.L.evalArgs_pure es ⟨m, l2⟩ with ⟨vs2, h2⟩ | h2
    · rw [h1, h2] at hes ⊢; subst hes
      exact ⟨rfl, rfl, rfl, (fun h => by cases h), (fun h => by cases h)⟩
    · rw [h1, h2] at hes; exact False.elim hes
    · rw [h1, h2] at hes; exact False.elim hes
    · rw [h1, h2]
  | st8 a i e =>
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    have hi := evalE_congr_uses i m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    have he := evalE_congr_uses e m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    rw [execB_st8, execB_st8]
    rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨vi1, hi1⟩ | hi1 <;>
    rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨vi2, hi2⟩ | hi2 <;>
    simp only [hi1, hi2] at hi
    · subst hi
      rcases _root_.L.evalE_pure e ⟨m, l1⟩ with ⟨ve1, he1⟩ | he1 <;>
      rcases _root_.L.evalE_pure e ⟨m, l2⟩ with ⟨ve2, he2⟩ | he2 <;>
      simp only [he1, he2] at he
      · subst he
        simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi1, hi2, he1, he2,
          _root_.L.st8, get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set,
          Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
        by_cases hb : vi1.toNat < (m.arr8 a).size
        · simp only [hb, ↓reduceIte]
          exact ⟨rfl, rfl, rfl, fun _ x hna => hag x (by simp [stmtVarCallFree, hna]), fun h => by cases h⟩
        · simp only [hb]; rfl
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi1, hi2, he1, he2]
    · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi1, hi2]
  | st64 a i e =>
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    have hi := evalE_congr_uses i m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    have he := evalE_congr_uses e m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    rw [execB_st64, execB_st64]
    rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨vi1, hi1⟩ | hi1 <;>
    rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨vi2, hi2⟩ | hi2 <;>
    simp only [hi1, hi2] at hi
    · subst hi
      rcases _root_.L.evalE_pure e ⟨m, l1⟩ with ⟨ve1, he1⟩ | he1 <;>
      rcases _root_.L.evalE_pure e ⟨m, l2⟩ with ⟨ve2, he2⟩ | he2 <;>
      simp only [he1, he2] at he
      · subst he
        simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi1, hi2, he1, he2,
          _root_.L.st64, get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set,
          Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
        by_cases hb : vi1.toNat < (m.arr64 a).size
        · simp only [hb, ↓reduceIte]
          exact ⟨rfl, rfl, rfl, fun _ x hna => hag x (by simp [stmtVarCallFree, hna]), fun h => by cases h⟩
        · simp only [hb]; rfl
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi1, hi2, he1, he2]
    · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi1, hi2]
  | st64t a t i e =>
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    have ht := evalE_congr_uses t m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    have hi := evalE_congr_uses i m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    have he := evalE_congr_uses e m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    rw [execB_st64t, execB_st64t]
    rcases _root_.L.evalE_pure t ⟨m, l1⟩ with ⟨vt1, ht1⟩ | ht1 <;>
    rcases _root_.L.evalE_pure t ⟨m, l2⟩ with ⟨vt2, ht2⟩ | ht2 <;>
    simp only [ht1, ht2] at ht
    · subst ht
      rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨vi1, hi1⟩ | hi1 <;>
      rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨vi2, hi2⟩ | hi2 <;>
      simp only [hi1, hi2] at hi
      · subst hi
        rcases _root_.L.evalE_pure e ⟨m, l1⟩ with ⟨ve1, he1⟩ | he1 <;>
        rcases _root_.L.evalE_pure e ⟨m, l2⟩ with ⟨ve2, he2⟩ | he2 <;>
        simp only [he1, he2] at he
        · subst he
          simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2, he1, he2,
            _root_.L.st64, get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set,
            Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
          by_cases hb : vi1.toNat < (m.arr64 (tierA a vt1)).size
          · simp only [hb, ↓reduceIte]
            exact ⟨rfl, rfl, rfl, fun _ x hna => hag x (by simp [stmtVarCallFree, hna]), fun h => by cases h⟩
          · simp only [hb]; rfl
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2, he1, he2]
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2]
    · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht1, ht2]
  | st32t a t i e =>
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    have ht := evalE_congr_uses t m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    have hi := evalE_congr_uses i m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    have he := evalE_congr_uses e m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    rw [execB_st32t, execB_st32t]
    rcases _root_.L.evalE_pure t ⟨m, l1⟩ with ⟨vt1, ht1⟩ | ht1 <;>
    rcases _root_.L.evalE_pure t ⟨m, l2⟩ with ⟨vt2, ht2⟩ | ht2 <;>
    simp only [ht1, ht2] at ht
    · subst ht
      rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨vi1, hi1⟩ | hi1 <;>
      rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨vi2, hi2⟩ | hi2 <;>
      simp only [hi1, hi2] at hi
      · subst hi
        rcases _root_.L.evalE_pure e ⟨m, l1⟩ with ⟨ve1, he1⟩ | he1 <;>
        rcases _root_.L.evalE_pure e ⟨m, l2⟩ with ⟨ve2, he2⟩ | he2 <;>
        simp only [he1, he2] at he
        · subst he
          simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2, he1, he2,
            _root_.L.st32, get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set,
            Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
          by_cases hb : (vi1 / 2).toNat < (m.arr64 (tierA a vt1)).size
          · simp only [hb, ↓reduceIte]
            exact ⟨rfl, rfl, rfl, fun _ x hna => hag x (by simp [stmtVarCallFree, hna]), fun h => by cases h⟩
          · simp only [hb]; rfl
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2, he1, he2]
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht1, ht2, hi1, hi2]
    · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht1, ht2]
  | copy64 d di src si n =>
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    have hd := warr_congr_uses d m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    have hdi := evalE_congr_uses di m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    have hs := warr_congr_uses src m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    have hsi := evalE_congr_uses si m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    have hn := evalE_congr_uses n m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    rw [execB_copy64, execB_copy64]
    rcases _root_.L.warr_pure d ⟨m, l1⟩ with ⟨da1, hd1⟩ | hd1 <;>
    rcases _root_.L.warr_pure d ⟨m, l2⟩ with ⟨da2, hd2⟩ | hd2 <;>
    simp only [hd1, hd2] at hd
    · subst hd
      rcases _root_.L.evalE_pure di ⟨m, l1⟩ with ⟨vdi1, hdi1⟩ | hdi1 <;>
      rcases _root_.L.evalE_pure di ⟨m, l2⟩ with ⟨vdi2, hdi2⟩ | hdi2 <;>
      simp only [hdi1, hdi2] at hdi
      · subst hdi
        rcases _root_.L.warr_pure src ⟨m, l1⟩ with ⟨sa1, hs1⟩ | hs1 <;>
        rcases _root_.L.warr_pure src ⟨m, l2⟩ with ⟨sa2, hs2⟩ | hs2 <;>
        simp only [hs1, hs2] at hs
        · subst hs
          rcases _root_.L.evalE_pure si ⟨m, l1⟩ with ⟨vsi1, hsi1⟩ | hsi1 <;>
          rcases _root_.L.evalE_pure si ⟨m, l2⟩ with ⟨vsi2, hsi2⟩ | hsi2 <;>
          simp only [hsi1, hsi2] at hsi
          · subst hsi
            rcases _root_.L.evalE_pure n ⟨m, l1⟩ with ⟨vn1, hn1⟩ | hn1 <;>
            rcases _root_.L.evalE_pure n ⟨m, l2⟩ with ⟨vn2, hn2⟩ | hn2 <;>
            simp only [hn1, hn2] at hn
            · subst hn
              simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hd1, hd2, hdi1, hdi2, hs1, hs2, hsi1, hsi2, hn1, hn2,
                get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set,
                Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
              by_cases hb : vdi1.toNat + vn1.toNat ≤ (m.arr64 da1).size ∧ vsi1.toNat + vn1.toNat ≤ (m.arr64 sa1).size
              · simp only [hb]
                exact ⟨rfl, rfl, rfl, fun _ x hna => hag x (by simp [stmtVarCallFree, hna]), fun h => by cases h⟩
              · simp only [hb]; rfl
            · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hd1, hd2, hdi1, hdi2, hs1, hs2, hsi1, hsi2, hn1, hn2]
          · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hd1, hd2, hdi1, hdi2, hs1, hs2, hsi1, hsi2]
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hd1, hd2, hdi1, hdi2, hs1, hs2]
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hd1, hd2, hdi1, hdi2]
    · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hd1, hd2]
  | copy8w d di src si n =>
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    have hd := warr_congr_uses d m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    have hdi := evalE_congr_uses di m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    have hsi := evalE_congr_uses si m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    have hn := evalE_congr_uses n m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    rw [execB_copy8w, execB_copy8w]
    rcases _root_.L.warr_pure d ⟨m, l1⟩ with ⟨da1, hd1⟩ | hd1 <;>
    rcases _root_.L.warr_pure d ⟨m, l2⟩ with ⟨da2, hd2⟩ | hd2 <;>
    simp only [hd1, hd2] at hd
    · subst hd
      rcases _root_.L.evalE_pure di ⟨m, l1⟩ with ⟨vdi1, hdi1⟩ | hdi1 <;>
      rcases _root_.L.evalE_pure di ⟨m, l2⟩ with ⟨vdi2, hdi2⟩ | hdi2 <;>
      simp only [hdi1, hdi2] at hdi
      · subst hdi
        rcases _root_.L.evalE_pure si ⟨m, l1⟩ with ⟨vsi1, hsi1⟩ | hsi1 <;>
        rcases _root_.L.evalE_pure si ⟨m, l2⟩ with ⟨vsi2, hsi2⟩ | hsi2 <;>
        simp only [hsi1, hsi2] at hsi
        · subst hsi
          rcases _root_.L.evalE_pure n ⟨m, l1⟩ with ⟨vn1, hn1⟩ | hn1 <;>
          rcases _root_.L.evalE_pure n ⟨m, l2⟩ with ⟨vn2, hn2⟩ | hn2 <;>
          simp only [hn1, hn2] at hn
          · subst hn
            simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hd1, hd2, hdi1, hdi2, hsi1, hsi2, hn1, hn2,
              get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set,
              Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
            by_cases hb : vdi1.toNat + vn1.toNat ≤ (m.arr64 da1).size ∧ vsi1.toNat + vn1.toNat ≤ (m.src8 src).size
            · simp only [hb]
              exact ⟨rfl, rfl, rfl, fun _ x hna => hag x (by simp [stmtVarCallFree, hna]), fun h => by cases h⟩
            · simp only [hb]; rfl
          · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hd1, hd2, hdi1, hdi2, hsi1, hsi2, hn1, hn2]
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hd1, hd2, hdi1, hdi2, hsi1, hsi2]
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hd1, hd2, hdi1, hdi2]
    · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hd1, hd2]
  | scan8 z src i e c =>
    refine ⟨by unfold stackNeedB; rfl, ?_⟩
    have hi := evalE_congr_uses i m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    have he := evalE_congr_uses e m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    rw [execB_scan8, execB_scan8]
    rcases _root_.L.evalE_pure i ⟨m, l1⟩ with ⟨vi1, hi1⟩ | hi1 <;>
    rcases _root_.L.evalE_pure i ⟨m, l2⟩ with ⟨vi2, hi2⟩ | hi2 <;>
    simp only [hi1, hi2] at hi
    · subst hi
      rcases _root_.L.evalE_pure e ⟨m, l1⟩ with ⟨ve1, he1⟩ | he1 <;>
      rcases _root_.L.evalE_pure e ⟨m, l2⟩ with ⟨ve2, he2⟩ | he2 <;>
      simp only [he1, he2] at he
      · subst he
        simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi1, hi2, he1, he2,
          get, getThe, MonadStateOf.get, StateT.get, _root_.L.setLoc, modify, modifyGet,
          MonadStateOf.modifyGet, Pure.pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
        by_cases hb : vi1 ≤ ve1 ∧ ve1.toNat ≤ (m.src8 src).size
        · simp only [hb]
          refine ⟨rfl, rfl, rfl, fun _ x hna => ?_, fun h => by cases h⟩
          simp only [_root_.L.St.setLoc]
          by_cases hxz : x = z
          · simp [hxz]
          · simp only [hxz, ↓reduceIte]
            exact hag x (by simp [stmtVarCallFree, hna, bne_iff_ne.mpr (Ne.symm hxz)])
        · simp only [hb]; rfl
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi1, hi2, he1, he2]
    · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi1, hi2]
  | call xs f args =>
    have hargs := evalArgs_congr_uses args m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    rw [stackNeedB_call, stackNeedB_call, execB_call, execB_call]
    rcases _root_.L.evalArgs_pure args ⟨m, l1⟩ with ⟨vs1, h1⟩ | h1 <;>
    rcases _root_.L.evalArgs_pure args ⟨m, l2⟩ with ⟨vs2, h2⟩ | h2
    · rw [h1, h2] at hargs ⊢; subst hargs
      cases hlk : p.lookup f with
      | none => exact ⟨by cases b <;> rfl, rfl⟩
      | some fd =>
        cases b with
        | zero => exact ⟨rfl, rfl⟩
        | succ b' =>
          refine ⟨rfl, ?_⟩
          cases hx : execB p b' fd.body { mem := m, loc := Locals.init vs1 } with
          | error _ => dsimp only; rw [hx]
          | ok res =>
            rcases res with ⟨sig, st2, b2⟩
            dsimp only; rw [hx]
            refine ⟨rfl, by simp only [setLocs_mem], rfl, fun _ => ?_, fun h => by cases h⟩
            exact setLocs_congr xs sig.retVal st2.mem l1 l2 na
              (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    · rw [h1, h2] at hargs; exact False.elim hargs
    · rw [h1, h2] at hargs; exact False.elim hargs
    · rw [h1, h2]; exact ⟨rfl, rfl⟩
  | seq s1 s2 =>
    let n2 : Var → Bool := fun x => (stmtVarCallFree x s2 (na x) (nb x)).1
    have h1 := ih b s1 (execBRel_seq_left b s1 s2) n2 nb m l1 l2 (fun x hx => hag x (by simpa [stmtVarCallFree, n2] using hx))
    rw [stackNeedB_seq, stackNeedB_seq, execB_seq, execB_seq]
    cases hx1 : execB p b s1 ⟨m, l1⟩ with
    | error e1 =>
      cases hx2 : execB p b s1 ⟨m, l2⟩ with
      | error e2 => rw [hx1, hx2] at h1; exact ⟨h1.1, h1.2⟩
      | ok _ => rw [hx1, hx2] at h1; exact False.elim h1.2
    | ok r1 =>
      rcases r1 with ⟨sig1, st1', b1⟩
      cases hx2 : execB p b s1 ⟨m, l2⟩ with
      | error _ => rw [hx1, hx2] at h1; exact False.elim h1.2
      | ok r2 =>
        rcases r2 with ⟨sig2, st2', b2⟩
        rw [hx1, hx2] at h1
        rcases h1 with ⟨hsn1, rfl, hmemEq, rfl, hagN1, hagB1⟩
        cases sig1 with
        | brk => exact ⟨hsn1, ⟨rfl, hmemEq, rfl, (fun h => by cases h), hagB1⟩⟩
        | ret vs => exact ⟨hsn1, ⟨rfl, hmemEq, rfl, (fun h => by cases h), (fun h => by cases h)⟩⟩
        | normal =>
          have hbLe : b1 ≤ b := execB_fuel_le hx1
          have h2 := ih b1 s2 (execBRel_seq_right hbLe s1 s2) na nb st1'.mem st1'.loc st2'.loc (hagN1 rfl)
          have hst2Eq : (⟨st1'.mem, st2'.loc⟩ : _root_.L.St) = st2' := by
            cases st2'; simp only [St.mk.injEq]; exact ⟨hmemEq, trivial⟩
          rw [hst2Eq] at h2
          exact ⟨by dsimp only; rw [hsn1, h2.1], h2.2⟩
  | ite c s1 s2 =>
    have hc := evalC_congr_uses c m l1 l2 (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    rw [stackNeedB_ite, stackNeedB_ite, execB_ite, execB_ite]
    rcases _root_.L.evalC_pure c ⟨m, l1⟩ with ⟨bc1, hc1⟩ | hc1 <;>
    rcases _root_.L.evalC_pure c ⟨m, l2⟩ with ⟨bc2, hc2⟩ | hc2 <;>
    simp only [hc1, hc2] at hc
    · rw [hc1, hc2]; subst hc
      cases bc1
      · exact ih b s2 (execBRel_ite_right b c s1 s2) na nb m l1 l2
          (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
      · exact ih b s1 (execBRel_ite_left b c s1 s2) na nb m l1 l2
          (fun x hx => hag x (by simp [stmtVarCallFree, hx]))
    · rw [hc1, hc2]; exact ⟨rfl, rfl⟩
  | «while» c body =>
    let nW : Var → Bool := fun x => (stmtVarCallFree x (.while c body) (na x) (nb x)).1
    have hc := evalC_congr_uses c m l1 l2
      (fun x hx => hag x (stmtVarCallFree_while_cond x c body (na x) (nb x) hx))
    rw [stackNeedB_while, stackNeedB_while, execB_while, execB_while]
    rcases _root_.L.evalC_pure c ⟨m, l1⟩ with ⟨bc1, hc1⟩ | hc1 <;>
    rcases _root_.L.evalC_pure c ⟨m, l2⟩ with ⟨bc2, hc2⟩ | hc2 <;>
    simp only [hc1, hc2] at hc
    · rw [hc1, hc2]; subst hc
      cases bc1
      · exact ⟨rfl, ⟨rfl, rfl, rfl, fun _ x hx => hag x (stmtVarCallFree_while_na x c body (na x) (nb x) hx),
          fun h => by cases h⟩⟩
      · dsimp only
        have hb := ih b body (execBRel_while_body b c body) nW na m l1 l2
          (fun x hx => hag x (stmtVarCallFree_while_body_live x c body (na x) (nb x) hx))
        cases hxb1 : execB p b body ⟨m, l1⟩ with
        | error e1 =>
          cases hxb2 : execB p b body ⟨m, l2⟩ with
          | error e2 => rw [hxb1, hxb2] at hb; exact ⟨hb.1, hb.2⟩
          | ok _ => rw [hxb1, hxb2] at hb; exact False.elim hb.2
        | ok rb1 =>
          rcases rb1 with ⟨sig1, st1', b1⟩
          cases hxb2 : execB p b body ⟨m, l2⟩ with
          | error _ => rw [hxb1, hxb2] at hb; exact False.elim hb.2
          | ok rb2 =>
            rcases rb2 with ⟨sig2, st2', b2⟩
            rw [hxb1, hxb2] at hb
            rcases hb with ⟨hsnB, rfl, hmemB, rfl, hagNB, hagBB⟩
            cases sig1 with
            | brk => exact ⟨hsnB, ⟨rfl, hmemB, rfl, fun _ => hagBB rfl, (fun h => by cases h)⟩⟩
            | ret vs => exact ⟨hsnB, ⟨rfl, hmemB, rfl, (fun h => by cases h), (fun h => by cases h)⟩⟩
            | normal =>
              cases b1 with
              | zero => exact ⟨hsnB, rfl⟩
              | succ b1' =>
                have hbLe : b1' < b := by have := execB_fuel_le hxb1; omega
                have hnext := ih b1' (.while c body) (execBRel_while_next hbLe c body)
                  na nb st1'.mem st1'.loc st2'.loc (hagNB rfl)
                have hst2Eq : (⟨st1'.mem, st2'.loc⟩ : _root_.L.St) = st2' := by
                  cases st2'; simp only [St.mk.injEq]; exact ⟨hmemB, trivial⟩
                rw [hst2Eq] at hnext
                exact ⟨by dsimp only; rw [hsnB, hnext.1], hnext.2⟩
    · rw [hc1, hc2]; exact ⟨rfl, rfl⟩

/-! ## 2. Result-Copy Lemmas (`copyTempsToResultsR`, `copyResultsToLocalsR`) -/

private def copyOneTempToResultR (tab : Tab) (fl : FrameLayout) (tmp i : Nat) : List AsmItem :=
  if i < maxRes then
    loadMemOff .ld (resReg i) AbiReg.sp AbiReg.t0 (fl.tempSlotOff (tmp + i))
  else
    loadMemOff .ld AbiReg.t1 AbiReg.sp AbiReg.t2 (fl.tempSlotOff (tmp + i)) ++
    storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t2 (tab.resOff i)

private theorem copyTempsToResultsR_eq_flatMap (tab : Tab) (fl : FrameLayout) (tmp count : Nat)
    (hpos : 0 < count) :
    copyTempsToResultsR tab fl tmp count =
      (List.range (min count tab.nres)).flatMap (copyOneTempToResultR tab fl tmp) := by
  have hne : (count == 0) = false := beq_false_of_ne (Nat.ne_of_gt hpos)
  simp only [copyTempsToResultsR, hne, Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem copyOneTempToResultR_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (fl : FrameLayout) {sp : BitVec 64} {tmp : Nat}
    (hal : isAligned sp 8 = true)
    (vs : List _root_.L.Word) (i : Nat) (hiVs : i < vs.length) (hiNres : i < env.tab.nres)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ copyOneTempToResultR env.tab fl tmp i ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hslot : readWord64 st.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff (tmp + i))) = (vs[i]'hiVs).toBitVec) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (copyOneTempToResultR env.tab fl tmp i))) ∧
      PreservedRegs st st' ∧
      st'.getReg AbiReg.ra = st.getReg AbiReg.ra ∧
      (∀ r ∈ calleeSavedBank, st'.getReg r = st.getReg r) ∧
      (∀ j, j < maxRes → j ≠ i → st'.getReg (resReg j) = st.getReg (resReg j)) ∧
      (i < maxRes → st'.getReg (resReg i) = (vs.getD i 0).toBitVec) ∧
      (maxRes ≤ i → readWord64 st'.mem (L.T + BitVec.ofInt 64 (env.tab.resOff i)) = (vs.getD i 0).toBitVec) ∧
      (i < maxRes → st'.mem = st.mem) ∧
      (maxRes ≤ i → st'.mem = writeWord64 st.mem (L.T + BitVec.ofInt 64 (env.tab.resOff i)) (vs.getD i 0).toBitVec) ∧
      MemEqOutside L.resOnlySpan st.mem st'.mem := by
  have hvalEq : (vs[i]'hiVs).toBitVec = (vs.getD i 0).toBitVec := by
    simp [List.getD, List.getElem?_eq_getElem hiVs]
  have halSlot : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (fl.tempSlotOff (tmp + i))) 8 = true := by
    rw [hsp, tempSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hal _
  have hpc64 := linkResolved_sub_pc64 env pre (copyOneTempToResultR env.tab fl tmp i) post hlink
  by_cases him : i < maxRes
  · have hco : copyOneTempToResultR env.tab fl tmp i =
        loadMemOff .ld (resReg i) AbiReg.sp AbiReg.t0 (fl.tempSlotOff (tmp + i)) := by
      simp [copyOneTempToResultR, him]
    rw [hco] at hlink hpc64 ⊢
    have hrn := resReg_ne_preserved i
    obtain ⟨st1, hrun1, hoth1, hval1, hmem1, hnpc1⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom pre post (resReg i) AbiReg.sp AbiReg.t0
        (resReg_ne_zero i) (by decide) (by decide) (fl.tempSlotOff (tmp + i)) hlink hpc64 st hpc halSlot
    refine ⟨lkm.totalSize (loadMemOff .ld (resReg i) AbiReg.sp AbiReg.t0 (fl.tempSlotOff (tmp + i))), st1,
      hrun1, hnpc1,
      ⟨hoth1 _ hrn.1.symm (by decide), hoth1 _ hrn.2.1.symm (by decide),
       hoth1 _ hrn.2.2.1.symm (by decide),
       hoth1 _ hrn.2.2.2.2.1.symm (by decide)⟩,
      hoth1 _ (resReg_ne_ra i).symm (by decide),
      fun r hr => hoth1 r (nonLeaf_allowed_ne_resReg hr i) (allowedRegs_ne_t0 (isLeaf := false) hr),
      fun j hj hne => hoth1 _ (resReg_ne_of_lt hj him hne) (resReg_ne_preserved j).2.2.2.2.2.1,
      fun _ => by rw [hval1, hsp, hslot, hvalEq],
      fun hge => by omega,
      fun _ => hmem1,
      fun hge => by omega,
      by rw [hmem1]; exact MemEqOutside.refl _ _⟩
  · have hge : maxRes ≤ i := by omega
    have hco : copyOneTempToResultR env.tab fl tmp i =
        loadMemOff .ld AbiReg.t1 AbiReg.sp AbiReg.t2 (fl.tempSlotOff (tmp + i)) ++
        storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t2 (env.tab.resOff i) := by
      simp [copyOneTempToResultR, him]
    rw [hco] at hlink hpc64 ⊢
    have ⟨hl1, hl2⟩ := linkResolved_mid_split lkm pre _ _ post hlink
    have hpc1 := linkResolved_sub_pc64 env pre _ _ hl1
    obtain ⟨st1, hrun1, hoth1, hval1, hmem1, hnpc1⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom pre _ AbiReg.t1 AbiReg.sp AbiReg.t2
        (by decide) (by decide) (by decide) (fl.tempSlotOff (tmp + i)) hl1 hpc1 st hpc halSlot
    have hgp1 : st1.getReg AbiReg.gp = L.T := (hoth1 _ (by decide) (by decide)).trans hgp
    have halR : isAligned (st1.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.resOff i)) 8 = true := by
      rw [hgp1]; exact isAligned8_of_resOff L hge hiNres
    have hpc2 := linkResolved_sub_pc64 env (pre ++ _) _ post hl2
    obtain ⟨st2, hrun2, hoth2, hmem2, hnpc2⟩ :=
      storeMemOff_sd_correct_lm lkm env.hrom (pre ++ _) post AbiReg.gp AbiReg.t1 AbiReg.t2
        (by decide) (by decide) (by decide) (env.tab.resOff i) hl2 hpc2 st1
        (by simpa [lkm.totalSize_append] using hnpc1) halR
    have ht1Eq : st1.getReg AbiReg.t1 = (vs.getD i 0).toBitVec := by
      rw [hval1, hsp, hslot, hvalEq]
    refine ⟨_, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
      by simpa [lkm.totalSize_append, Nat.add_assoc] using hnpc2,
      ⟨(hoth2 _ (by decide)).trans (hoth1 _ (by decide) (by decide)),
       (hoth2 _ (by decide)).trans (hoth1 _ (by decide) (by decide)),
       (hoth2 _ (by decide)).trans (hoth1 _ (by decide) (by decide)),
       (hoth2 _ (by decide)).trans (hoth1 _ (by decide) (by decide))⟩,
      (hoth2 _ (by decide)).trans (hoth1 _ (by decide) (by decide)),
      fun r hr => (hoth2 r (allowedRegs_ne_t2 (isLeaf := false) hr)).trans
        (hoth1 r (allowedRegs_ne_t1 (isLeaf := false) hr) (allowedRegs_ne_t2 (isLeaf := false) hr)),
      fun j _ _ =>
        let hrn := resReg_ne_preserved j
        (hoth2 _ hrn.2.2.2.2.2.2.2).trans (hoth1 _ hrn.2.2.2.2.2.2.1 hrn.2.2.2.2.2.2.2),
      fun hlt => by omega,
      fun _ => by rw [hmem2, hmem1, hgp1, ht1Eq]; exact readWord64_writeWord64_self _ _ _,
      fun hlt => by omega,
      fun _ => by rw [hmem2, hmem1, hgp1, ht1Eq],
      by rw [hmem2, hmem1, hgp1]
         exact MemEqOutside.writeWord64 _ _ _ (fun k hk => resOnlySpan_contains_resOff L hge hiNres hk)⟩

private theorem copyTempsToResultsR_prefix_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (fl : FrameLayout) {sp : BitVec 64} {tmp : Nat}
    (hal : isAligned sp 8 = true) (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (vs : List _root_.L.Word) (hcnt : tmp + vs.length ≤ fl.usedTemps) :
    ∀ m, m ≤ min vs.length env.tab.nres → ∀ (pre post : List AsmItem),
      lkm.linkSpec (pre ++ (List.range m).flatMap (copyOneTempToResultR env.tab fl tmp) ++ post) =
        .ok (env.code, env.labels) →
      ∀ (st : State), st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → st.getReg AbiReg.sp = sp →
      (∀ j (hj : j < vs.length),
        readWord64 st.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff (tmp + j))) = (vs[j]'hj).toBitVec) →
      ∃ k st',
        RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre +
          lkm.totalSize ((List.range m).flatMap (copyOneTempToResultR env.tab fl tmp)))) ∧
        PreservedRegs st st' ∧
        st'.getReg AbiReg.ra = st.getReg AbiReg.ra ∧
        (∀ r ∈ calleeSavedBank, st'.getReg r = st.getReg r) ∧
        (∀ i, i < min m maxRes → st'.getReg (resReg i) = (vs.getD i 0).toBitVec) ∧
        (∀ i, maxRes ≤ i → i < m →
          readWord64 st'.mem (L.T + BitVec.ofInt 64 (env.tab.resOff i)) = (vs.getD i 0).toBitVec) ∧
        MemEqOutside L.resOnlySpan st.mem st'.mem := by
  intro m
  have hfValid : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  induction m with
  | zero =>
    intro _ _ _ _ st hpc _ _ _
    refine ⟨0, st, rfl, by simp [lkm.totalSize_nil, hpc], PreservedRegs.refl st, rfl, fun _ _ => rfl,
      fun _ h => by omega, fun _ h1 h2 => by omega, MemEqOutside.refl _ _⟩
  | succ m ih =>
    intro hm pre post hlink st hpc hgp hsp hslots
    have heq : (List.range (m + 1)).flatMap (copyOneTempToResultR env.tab fl tmp) =
        (List.range m).flatMap (copyOneTempToResultR env.tab fl tmp) ++
        copyOneTempToResultR env.tab fl tmp m := by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rw [heq] at hlink ⊢
    have ⟨hl1, hl2⟩ := linkResolved_mid_split lkm pre _ _ post hlink
    obtain ⟨k1, st1, hrun1, hpc1, hpres1, hra1, hcal1, hreg1, hmem1, hout1⟩ :=
      ih (by omega) pre _ hl1 st hpc hgp hsp hslots
    have hmVs : m < vs.length := by omega
    have hmNres : m < env.tab.nres := by omega
    have hslotM : readWord64 st1.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff (tmp + m))) = (vs[m]'hmVs).toBitVec := by
      have hs1 : (tempSlotSpanR fl sp (tmp + m)).sub L.stackSpan :=
        MemSpan.sub_trans (MemSpan.sub_trans (tempSlotSpanR_sub_tempSpanR fl sp hfValid (Nat.le_refl _) (by omega))
          (tempSpanR_sub_frameSpanR fl sp (tmp + m) hfValid (by omega)))
          (frameSpanR_sub_stackSpan L hlo hhi)
      have hdisjTab := MemSpan.disjoint_to_memDisjoint L.tabSpan_valid L.stackSpan_valid L.htabDisjStack
      have hdisjRg : MemDisjoint L.resOnlySpan L.stackSpan :=
        MemDisjoint.of_sub_left (MemSpan.sub_trans (resOnlySpan_sub_resGlob L) L.resGlob_sub_tab) hdisjTab
      have hd : MemDisjoint (tempSlotSpanR fl sp (tmp + m)) L.resOnlySpan := MemDisjoint.of_sub_left hs1 hdisjRg.symm
      rw [← hslots m hmVs]
      exact MemEqOutside.readWord64_eq hout1 _ fun k hk hc =>
        hd _ ⟨k, hk, by simp [tempSlotSpanR, slotSpan, slotAddr, tempSlotOff_ofInt]⟩ hc
    obtain ⟨k2, st2, hrun2, hpc2, hpres2, hra2, hcal2, hothReg2, hcurReg2, hcurMem2, hmemEq2, hmemWr2, hout2⟩ :=
      copyOneTempToResultR_sim env L fl hal vs m hmVs hmNres
        (pre ++ (List.range m).flatMap (copyOneTempToResultR env.tab fl tmp)) post hl2
        st1 (by simpa [lkm.totalSize_append] using hpc1) (hpres1.gp.trans hgp) (hpres1.sp.trans hsp) hslotM
    refine ⟨k1 + k2, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
      by simpa [lkm.totalSize_append, Nat.add_assoc] using hpc2,
      hpres1.trans hpres2, hra2.trans hra1, fun r hr => (hcal2 r hr).trans (hcal1 r hr),
      ?_, ?_, hout1.trans hout2⟩
    · intro i hi
      by_cases him : i = m
      · subst him; exact hcurReg2 (by omega)
      · rw [hothReg2 i (by omega) him]; exact hreg1 i (by omega)
    · intro i hloI hhiI
      by_cases him : i = m
      · subst him; exact hcurMem2 hloI
      · by_cases hmx : m < maxRes
        · rw [hmemEq2 hmx]; exact hmem1 i hloI (by omega)
        · have hgeM : maxRes ≤ m := by omega
          rw [hmemWr2 hgeM]
          have hdisj : ∀ k1 k2, k1 < 8 → k2 < 8 →
              L.T + BitVec.ofInt 64 (env.tab.resOff i) + BitVec.ofNat 64 k1 ≠
              L.T + BitVec.ofInt 64 (env.tab.resOff m) + BitVec.ofNat 64 k2 := by
            intro k1 k2 hk1 hk2 heqA
            have hbi : env.tab.resBase.toNat + 8 * (i - maxRes) + 8 ≤ L.tabBytes := L.tab_resOff_bound hloI (by omega)
            have hbm : env.tab.resBase.toNat + 8 * (m - maxRes) + 8 ≤ L.tabBytes := L.tab_resOff_bound hgeM (by omega)
            have hnn := ProgLayout.resBase_nonneg env.tab
            have ht := L.hTValid
            have hri : env.tab.resOff i = ↑(env.tab.resBase.toNat + 8 * (i - maxRes)) := by simp only [Tab.resOff]; omega
            have hrm : env.tab.resOff m = ↑(env.tab.resBase.toNat + 8 * (m - maxRes)) := by simp only [Tab.resOff]; omega
            rw [hri, hrm] at heqA
            have hnat := congrArg BitVec.toNat heqA
            have hc1 : BitVec.ofInt 64 ↑(env.tab.resBase.toNat + 8 * (i - maxRes)) =
                BitVec.ofNat 64 (env.tab.resBase.toNat + 8 * (i - maxRes)) := rfl
            have hc2 : BitVec.ofInt 64 ↑(env.tab.resBase.toNat + 8 * (m - maxRes)) =
                BitVec.ofNat 64 (env.tab.resBase.toNat + 8 * (m - maxRes)) := rfl
            rw [hc1, hc2, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add] at hnat
            simp only [BitVec.toNat_ofNat] at hnat
            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
                Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
                Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hnat
            omega
          rw [readWord64_writeWord64_disjoint _ _ _ _ hdisj]
          exact hmem1 i hloI (by omega)

theorem reg_copyTempsToResultsR_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (fl : FrameLayout) {sp : BitVec 64} {tmp : Nat}
    (hal : isAligned sp 8 = true) (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (vs : List _root_.L.Word) (hcnt : tmp + vs.length ≤ fl.usedTemps)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ copyTempsToResultsR env.tab fl tmp vs.length ++ post) =
      .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hslots : ∀ j (hj : j < vs.length),
      readWord64 st.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff (tmp + j))) = (vs[j]'hj).toBitVec) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (copyTempsToResultsR env.tab fl tmp vs.length))) ∧
      PreservedRegs st st' ∧
      st'.getReg AbiReg.ra = st.getReg AbiReg.ra ∧
      (∀ r ∈ calleeSavedBank, st'.getReg r = st.getReg r) ∧
      ResultsInState env.tab L st' vs ∧
      MemEqOutside L.resOnlySpan st.mem st'.mem := by
  by_cases hlen : vs.length = 0
  · have hnil : vs = [] := List.eq_nil_of_length_eq_zero hlen
    subst hnil
    by_cases hnres : 0 < env.tab.nres
    · have hco : copyTempsToResultsR env.tab fl tmp 0 = [Asm.addi AbiReg.a0 AbiReg.zero 0#12] := by
        simp [copyTempsToResultsR, hnres]
      simp only [List.length_nil] at hlink ⊢
      rw [hco] at hlink ⊢
      have hpc64 := linkResolved_sub_pc64 env pre _ post hlink
      have htw : lkm.totalSize [Asm.addi AbiReg.a0 AbiReg.zero 0#12] = 1 := by simp only [Asm.addi, lkm.totalSize_instr]
      have hlt : 4 * lkm.totalSize pre < 2 ^ 64 := by rw [htw] at hpc64; omega
      have hstep := step_item_instr_lm lkm env.hrom pre post
        (.aluImm .addi AbiReg.a0 AbiReg.zero 0#12) hlink hlt st hpc
      let st1 := stepReg st AbiReg.a0 0#64 (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
      have hres0 : evalAluImm .addi (st.getReg AbiReg.zero) 0#12 = 0#64 := by rw [getReg_zero st]; decide
      have hrun : RV64.run env.rom 1 st = .cont st1 := by
        apply run_one_cont; rw [hstep]
        simp only [execInstr, hres0, pc_add_4_ofNat st.pc hpc, st1, stepReg]
      refine ⟨1, st1, hrun, by simp only [htw]; rfl,
        ⟨getReg_stepReg_ne st AbiReg.a0 AbiReg.gp (by decide) _ _,
         getReg_stepReg_ne st AbiReg.a0 AbiReg.sp (by decide) _ _,
         getReg_stepReg_ne st AbiReg.a0 AbiReg.s0 (by decide) _ _,
         getReg_stepReg_ne st AbiReg.a0 AbiReg.s2 (by decide) _ _⟩,
        getReg_stepReg_ne st AbiReg.a0 AbiReg.ra (by decide) _ _,
        fun r hr => getReg_stepReg_ne st AbiReg.a0 r (allowedRegs_ne_a0 (isLeaf := false) hr) _ _,
        ⟨fun i hi => by
            have hi0 : i = 0 := by simp [maxRes] at hi; omega
            subst hi0; simpa [resReg] using getReg_stepReg_eq st AbiReg.a0 (by decide) 0#64 _,
         fun i hloI hhiI => by simp [maxRes] at hloI hhiI; omega⟩,
        by have hm : st1.mem = st.mem := setReg_mem st AbiReg.a0 0#64; rw [hm]; exact MemEqOutside.refl _ _⟩
    · have hco : copyTempsToResultsR env.tab fl tmp 0 = [] := by simp [copyTempsToResultsR, hnres]
      refine ⟨0, st, rfl, by simp [hco, lkm.totalSize_nil, hpc], PreservedRegs.refl st, rfl, fun _ _ => rfl,
        ⟨fun i hi => by omega, fun i hloI hhiI => by omega⟩, MemEqOutside.refl _ _⟩
  · have hpos : 0 < vs.length := Nat.pos_of_ne_zero hlen
    rw [copyTempsToResultsR_eq_flatMap env.tab fl tmp vs.length hpos] at hlink ⊢
    obtain ⟨k, st', hrun, hpc', hpres, hra, hcal, hreg, hmem, hout⟩ :=
      copyTempsToResultsR_prefix_sim env L fl hal hlo hhi vs hcnt
        (min vs.length env.tab.nres) (Nat.le_refl _) pre post hlink st hpc hgp hsp hslots
    have hmax : max 1 vs.length = vs.length := by omega
    refine ⟨k, st', hrun, hpc', hpres, hra, hcal,
      ⟨fun i hi => hreg i (by omega), fun i hloI hhiI => hmem i hloI (by omega)⟩, hout⟩

def copyOneResultItemR (tab : Tab) (fl : FrameLayout) (p : Var × Nat) : List AsmItem :=
  match fl.alloc.lookup p.1 with
  | some rx =>
    if p.2 < tab.nres then
      if p.2 < maxRes then
        if rx == resReg p.2 then [] else [Asm.mv rx (resReg p.2)]
      else loadMemOff .ld rx AbiReg.gp AbiReg.t2 (tab.resOff p.2)
    else [Asm.addi rx AbiReg.zero 0#12]
  | none =>
    if !(p.1 ∈ fl.spilledVars) then []
    else if p.2 < tab.nres then
      if p.2 < maxRes then storeMemOff .sd AbiReg.sp (resReg p.2) AbiReg.t0 (fl.varSlotOff p.1)
      else
        loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (tab.resOff p.2) ++
        storeMemOff .sd AbiReg.sp AbiReg.t1 AbiReg.t2 (fl.varSlotOff p.1)
    else storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t0 (fl.varSlotOff p.1)

def copyResultsLoopR (tab : Tab) (fl : FrameLayout) (xs : List Var) (start : Nat) : List AsmItem :=
  (xs.zipIdx start).flatMap (copyOneResultItemR tab fl)

theorem copyResultsToLocalsR_eq_loop (tab : Tab) (fl : FrameLayout) (xs : List Var) :
    copyResultsToLocalsR tab fl xs = copyResultsLoopR tab fl xs 0 := rfl

private theorem ProgFrameOkLive.of_set_spill {tab : Tab} {L : ProgLayout tab} {fl : FrameLayout}
    (hfl : FrameLayoutOk fl) {sp : BitVec 64} {st1 st2 : State} {loc : _root_.L.Locals} {live : Var → Bool}
    (hvalid : (frameSpanR fl sp).valid)
    {x : Var} {v : _root_.L.Word} (hmx : x ∈ fl.spilledVars)
    (hpres : PreservedFrameRegs fl (· = AbiReg.a0) st1 st2)
    (hmem : st2.mem = writeWord64 st1.mem (sp + BitVec.ofInt 64 (fl.varSlotOff x)) v.toBitVec)
    (hf : ProgFrameOkLive L fl sp st1 loc live) :
    ProgFrameOkLive L fl sp st2 (fun y => if y = x then v else loc y) live := by
  have ⟨_, hxn⟩ := hfl.spilledSub x hmx
  intro y hy hlv
  by_cases hxy : y = x
  · subst hxy; rw [hxn, hmem]; simp only [↓reduceIte]
    intro _; exact readWord64_writeWord64_self st1.mem _ v.toBitVec
  · simp only [hxy, ↓reduceIte]
    have hfy := hf y hy hlv
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
        exact MemEqOutside.writeWord64 st1.mem _ v.toBitVec fun k hk => ⟨k, hk, rfl⟩
      rw [varSlotOff_ofInt]
      exact MemEqOutside.readWord64_eq hout _ fun k hk =>
        (varSlotSpanR_disj_of_ne fl hfl sp hvalid hmx hmy (Ne.symm hxy)).symm _
          ⟨k, hk, by simp [varSlotSpanR, slotSpan, slotAddr, varSlotOff_ofInt]⟩

/-- `ResultsInState` restricted to result indices `[start, hi)` (used during `copyResultsLoopR`
    when earlier `a1..a7` registers may be overwritten as destinations for call-free locals). -/
def ResultsInStateRange (tab : Tab) (L : ProgLayout tab) (st : State)
    (vs : List _root_.L.Word) (start hi : Nat) : Prop :=
  (∀ i, start ≤ i → i < min (min hi tab.nres) maxRes → st.getReg (resReg i) = (vs.getD i 0).toBitVec) ∧
  (∀ i, maxRes ≤ i → i < min hi tab.nres →
    readWord64 st.mem (L.T + BitVec.ofInt 64 (tab.resOff i)) = (vs.getD i 0).toBitVec)

theorem ResultsInState.toRange {tab : Tab} {L : ProgLayout tab} {st : State}
    {vs : List _root_.L.Word} {hi : Nat} (hhi : hi ≤ max 1 vs.length)
    (hres : ResultsInState tab L st vs) :
    ResultsInStateRange tab L st vs 0 hi :=
  ⟨fun i _ hiLt => hres.1 i (by omega), fun i hloI hhiI => hres.2 i hloI (by omega)⟩

theorem callResListValid_spec {alloc : RegAlloc} {xs : List Var}
    (h : callResListValid alloc xs = true) :
    ∀ x i, (x, i) ∈ xs.zipIdx 0 → ∀ rx, alloc.lookup x = some rx →
      ∀ j, i < j → j < min (0 + xs.length) maxRes → rx ≠ resReg j := by
  intro x i hmem rx hlk j hlt hj
  simp only [callResListValid, List.all_eq_true] at h
  have h1 := h (x, i) hmem
  simp only [hlk, List.all_eq_true, List.mem_range, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not, beq_eq_false_iff_ne] at h1
  rcases h1 j (by omega) with hnotlt | hne
  · exact absurd hlt hnotlt
  · exact hne

theorem reg_copyResultsLoopR_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    {sp : BitVec 64}
    (hal : isAligned sp 8 = true) (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (vs : List _root_.L.Word) (hvlen : vs.length ≤ env.tab.nres) (m0 : _root_.L.Mem)
    (live2 : Var → Bool) :
    ∀ (xs : List _root_.L.Var) (start : Nat), (∀ x ∈ xs, x < fl.nlocals) →
      start + xs.length ≤ max 1 vs.length →
      (∀ x i, (x, i) ∈ xs.zipIdx start → ∀ rx, fl.alloc.lookup x = some rx →
        ∀ j, i < j → j < min (start + xs.length) maxRes → rx ≠ resReg j) →
      (∀ y ry, fl.alloc.lookup y = some ry → live2 y = true →
        ∀ x ∈ xs, x ≠ y → fl.alloc.lookup x ≠ some ry) →
      ∀ (pre post : List AsmItem),
        lkm.linkSpec (pre ++ copyResultsLoopR env.tab fl xs start ++ post) = .ok (env.code, env.labels) →
      ∀ (loc : _root_.L.Locals) (st : State),
        st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
        st.getReg AbiReg.gp = L.T → st.getReg AbiReg.sp = sp →
        ResultsInStateRange env.tab L st vs start (start + xs.length) →
        ProgFrameOkLive L fl sp st loc live2 →
      ∃ k st',
        RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (copyResultsLoopR env.tab fl xs start))) ∧
        PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) st st' ∧
        ProgFrameOkLive L fl sp st' (({ mem := m0, loc := loc } : _root_.L.St).setLocs xs (vs.drop start)).loc live2 ∧
        MemEqOutside (localsTempSpanR fl sp) st.mem st'.mem := by
  have hfValid : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  have hdisjRes : ∀ i, maxRes ≤ i → i < env.tab.nres → ∀ k, k < 8 →
      ¬(localsTempSpanR fl sp).contains (L.T + BitVec.ofInt 64 (env.tab.resOff i) + BitVec.ofNat 64 k) := by
    intro i hloI hhiI k hk hc
    have hcStack := (localsTempSpanR_sub_stackSpan L hlo hhi) _ hc
    have hcTab := L.resGlob_sub_tab _ (resGlobSpan_contains_resOff L hloI hhiI hk)
    exact MemSpan.disjoint_to_memDisjoint L.tabSpan_valid L.stackSpan_valid L.htabDisjStack _ hcTab hcStack
  intro xs
  induction xs with
  | nil =>
    intro start _ _ _ _ pre post _ loc st hpc _ _ _ hf
    refine ⟨0, st, rfl, by simp [copyResultsLoopR, lkm.totalSize_nil, hpc],
      PreservedFrameRegs.refl _ _ _, by simp [_root_.L.St.setLocs]; exact hf, MemEqOutside.refl _ _⟩
  | cons x rest ih =>
    intro start hxs hxsAr hresSafe hnoClob pre post hlink loc st hpc hgp hsp hres hf
    have hcl : copyResultsLoopR env.tab fl (x :: rest) start =
        copyOneResultItemR env.tab fl (x, start) ++ copyResultsLoopR env.tab fl rest (start + 1) := by
      simp [copyResultsLoopR, List.zipIdx_cons]
    rw [hcl] at hlink ⊢
    have ⟨hl1, hl2⟩ := linkResolved_mid_split lkm pre _ _ post hlink
    have hpc1 := linkResolved_sub_pc64 env pre _ _ hl1
    have hxlt : x < fl.nlocals := hxs x (by simp)
    have hhiEq : start + 1 + rest.length = start + (x :: rest).length := by simp; omega
    have hresNeLater : ∀ {rx : Reg}, fl.alloc.lookup x = some rx →
        ∀ j, start + 1 ≤ j → j < min (start + (x :: rest).length) maxRes → rx ≠ resReg j :=
      fun {rx} hlx j hloJ hhiJ =>
        hresSafe x start (by simp [List.zipIdx_cons]) rx hlx j (by omega) hhiJ
    have hnoClobX : ∀ rx, fl.alloc.lookup x = some rx → ∀ y, y ≠ x → live2 y = true → fl.alloc.lookup y ≠ some rx :=
      fun rx hlx y hyx hly2 hly => hnoClob y rx hly hly2 x (by simp) (Ne.symm hyx) hlx
    have ⟨k1, st1, hrun1, hpc1', hpres1, hres1, hf1, hout1⟩ :
        ∃ k1 st1,
          RV64.run env.rom k1 st = .cont st1 ∧
          st1.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (copyOneResultItemR env.tab fl (x, start)))) ∧
          PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) st st1 ∧
          ResultsInStateRange env.tab L st1 vs (start + 1) (start + (x :: rest).length) ∧
          ProgFrameOkLive L fl sp st1 (fun y => if y = x then vs.getD start 0 else loc y) live2 ∧
          MemEqOutside (localsTempSpanR fl sp) st.mem st1.mem := by
      cases hlx : fl.alloc.lookup x with
      | some rx =>
        have hrxInfo := regAllocValid_lookup hfl.valid hlx
        have hrxMem : rx ∈ allowedRegs true := hrxInfo.2.1
        have hrxAlloc : rx ∈ fl.alloc.map Prod.snd := hrxInfo.2.2
        have hrxNe0 : rx ≠ 0#5 := allowedRegs_ne_zero hrxMem
        by_cases hst : start < env.tab.nres
        · by_cases hmx : start < maxRes
          · by_cases heqR : rx = resReg start
            · have hco : copyOneResultItemR env.tab fl (x, start) = [] := by
                simp [copyOneResultItemR, hlx, hst, hmx, heqR]
              rw [hco]
              have hrxVal : st.getReg rx = (vs.getD start 0).toBitVec := by
                rw [heqR]
                exact hres.1 start (Nat.le_refl _) (by simp only [List.length_cons]; omega)
              refine ⟨0, st, rfl, by simp [lkm.totalSize_nil, hpc],
                PreservedFrameRegs.refl _ _ _,
                ⟨fun i hloI hhiI => hres.1 i (by omega) hhiI, hres.2⟩,
                ProgFrameOkLive.of_set_reg hfl hfValid hlx (PreservedFrameRegs.refl _ _ _) hrxVal (MemEqOutside.refl _ _)
                  (fun _ _ h => h) (hnoClobX rx hlx) hf,
                MemEqOutside.refl _ _⟩
            · have hco : copyOneResultItemR env.tab fl (x, start) = [Asm.mv rx (resReg start)] := by
                simp [copyOneResultItemR, hlx, hst, hmx, beq_false_of_ne heqR]
              rw [hco] at hl1 hpc1 ⊢
              have htw1 : lkm.totalSize [Asm.mv rx (resReg start)] = 1 := by simp only [Asm.mv, lkm.totalSize_instr]
              obtain ⟨hrunM, hpcM, hrxM, hothM, hmemM⟩ :=
                run_aluImm_rd_step env pre _ .addi rx (resReg start) 0#12 hrxNe0
                  (by simpa [Asm.mv] using hl1) st hpc
              let st1 := stepReg st rx (evalAluImm .addi (st.getReg (resReg start)) 0#12)
                (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
              have hrxVal : st1.getReg rx = (vs.getD start 0).toBitVec := by
                rw [hrxM]; change st.getReg (resReg start) + sextImm12 0#12 = _
                rw [show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero]
                exact hres.1 start (Nat.le_refl _) (by simp only [List.length_cons]; omega)
              have hpresRx : PreservedFrameRegs fl (· = rx) st st1 :=
                PreservedFrameRegs.of_target1 rx (Or.inr hrxMem) (fun _ => rfl) hothM
              refine ⟨1, st1, hrunM, by rw [htw1]; exact hpcM,
                hpresRx.mono (fun r (hr : r = rx) => hr ▸ hrxAlloc),
                ⟨fun i hloI hhiI => (hothM (resReg i) (hresNeLater hlx i hloI (by omega)).symm).trans (hres.1 i (by omega) hhiI),
                 fun i hloI hhiI => by rw [hmemM]; exact hres.2 i hloI hhiI⟩,
                ProgFrameOkLive.of_set_reg hfl hfValid hlx hpresRx hrxVal (by rw [hmemM]; exact MemEqOutside.refl _ _)
                  (fun _ _ h => h) (hnoClobX rx hlx) hf,
                by rw [hmemM]; exact MemEqOutside.refl _ _⟩
          · have hge : maxRes ≤ start := by omega
            have hco : copyOneResultItemR env.tab fl (x, start) =
                loadMemOff .ld rx AbiReg.gp AbiReg.t2 (env.tab.resOff start) := by
              simp [copyOneResultItemR, hlx, hst, hmx]
            rw [hco] at hl1 hpc1 ⊢
            have halR : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.resOff start)) 8 = true := by
              rw [hgp]; exact isAligned8_of_resOff L hge hst
            obtain ⟨st1, hrun1, hoth1, hrx1, hmem1, hnpc1⟩ :=
              loadMemOff_ld_correct_lm lkm env.hrom pre _ rx AbiReg.gp AbiReg.t2
                hrxNe0 (by decide) (by decide) (env.tab.resOff start) hl1 hpc1 st hpc halR
            have hrxVal : st1.getReg rx = (vs.getD start 0).toBitVec := by
              rw [hrx1, hgp]; exact hres.2 start hge (by simp only [List.length_cons]; omega)
            have hpresRx : PreservedFrameRegs fl (· = rx) st st1 :=
              PreservedFrameRegs.of_target_scratch rx AbiReg.t2 (Or.inr hrxMem) (fun _ => rfl) (by decide) hoth1
            refine ⟨_, st1, hrun1, hnpc1,
              hpresRx.mono (fun r (hr : r = rx) => hr ▸ hrxAlloc),
              ⟨fun i hloI hhiI => by omega,
               fun i hloI hhiI => by rw [hmem1]; exact hres.2 i hloI hhiI⟩,
              ProgFrameOkLive.of_set_reg hfl hfValid hlx hpresRx hrxVal (by rw [hmem1]; exact MemEqOutside.refl _ _)
                (fun _ _ h => h) (hnoClobX rx hlx) hf,
              by rw [hmem1]; exact MemEqOutside.refl _ _⟩
        · have hco : copyOneResultItemR env.tab fl (x, start) = [Asm.addi rx AbiReg.zero 0#12] := by
            simp [copyOneResultItemR, hlx, hst]
          rw [hco] at hl1 hpc1 ⊢
          have htw1 : lkm.totalSize [Asm.addi rx AbiReg.zero 0#12] = 1 := by simp only [Asm.addi, lkm.totalSize_instr]
          obtain ⟨hrunM, hpcM, hrxM, hothM, hmemM⟩ :=
            run_aluImm_rd_step env pre _ .addi rx AbiReg.zero 0#12 hrxNe0
              (by simpa [Asm.addi] using hl1) st hpc
          let st1 := stepReg st rx (evalAluImm .addi (st.getReg AbiReg.zero) 0#12)
            (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
          have hzeroVal : (vs.getD start 0).toBitVec = 0#64 := by
            simp [List.getD, List.getElem?_eq_none (by omega : vs.length ≤ start)]
          have hrxVal : st1.getReg rx = (vs.getD start 0).toBitVec := by
            rw [hrxM, hzeroVal]; change st.getReg AbiReg.zero + sextImm12 0#12 = 0#64
            rw [getReg_zero]; decide
          have hpresRx : PreservedFrameRegs fl (· = rx) st st1 :=
            PreservedFrameRegs.of_target1 rx (Or.inr hrxMem) (fun _ => rfl) hothM
          refine ⟨1, st1, hrunM, by rw [htw1]; exact hpcM,
            hpresRx.mono (fun r (hr : r = rx) => hr ▸ hrxAlloc),
            ⟨fun i hloI hhiI => (hothM (resReg i) (hresNeLater hlx i hloI (by omega)).symm).trans (hres.1 i (by omega) hhiI),
             fun i hloI hhiI => by rw [hmemM]; exact hres.2 i hloI hhiI⟩,
            ProgFrameOkLive.of_set_reg hfl hfValid hlx hpresRx hrxVal (by rw [hmemM]; exact MemEqOutside.refl _ _)
              (fun _ _ h => h) (hnoClobX rx hlx) hf,
            by rw [hmemM]; exact MemEqOutside.refl _ _⟩
      | none =>
        by_cases hmxSp : x ∈ fl.spilledVars
        · have hsi := hfl.spillIdx_lt hmxSp
          have halX : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (fl.varSlotOff x)) 8 = true := by
            rw [hsp, varSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hal _
          have hltSub : (varSlotSpanR fl sp x).sub (localsTempSpanR fl sp) := by
            intro a ⟨k, hk, ha⟩; subst ha
            dsimp only [varSlotSpanR, slotSpan, slotAddr] at hk ⊢
            refine ⟨8 * fl.spillIdx x + k, by dsimp only [localsTempSpanR]; omega, ?_⟩
            dsimp only [localsTempSpanR]
            rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
            congr 2; omega
          by_cases hst : start < env.tab.nres
          · by_cases hmx : start < maxRes
            · have hco : copyOneResultItemR env.tab fl (x, start) =
                  storeMemOff .sd AbiReg.sp (resReg start) AbiReg.t0 (fl.varSlotOff x) := by
                simp [copyOneResultItemR, hlx, hmxSp, hst, hmx]
              rw [hco] at hl1 hpc1 ⊢
              have hrn := resReg_ne_preserved start
              obtain ⟨st1, hrun1, hoth1, hmem1, hnpc1⟩ :=
                storeMemOff_sd_correct_lm lkm env.hrom pre _ AbiReg.sp (resReg start) AbiReg.t0
                  (by decide) (by decide) hrn.2.2.2.2.2.1.symm (fl.varSlotOff x) hl1 hpc1 st hpc halX
              have hvalEq : st.getReg (resReg start) = (vs.getD start 0).toBitVec :=
                hres.1 start (Nat.le_refl _) (by simp only [List.length_cons]; omega)
              have houtSlot : MemEqOutside (localsTempSpanR fl sp) st.mem st1.mem := by
                rw [hmem1, hsp, hvalEq]
                exact MemEqOutside.writeWord64 _ _ _ fun k hk => hltSub _ ⟨k, hk, by
                  simp only [varSlotSpanR, slotSpan, slotAddr, varSlotOff_ofInt]⟩
              have hpres1 : PreservedFrameRegs fl (· = AbiReg.a0) st st1 :=
                PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hoth1
              refine ⟨_, st1, hrun1, hnpc1, PreservedFrameRegs.of_a0 hpres1,
                ⟨fun i hloI hhiI => (hoth1 _ (resReg_ne_preserved i).2.2.2.2.2.1).trans (hres.1 i (by omega) hhiI),
                 fun i hloI hhiI => (MemEqOutside.readWord64_eq houtSlot _ (hdisjRes i hloI (by simp [maxRes] at hloI; omega))).trans (hres.2 i hloI hhiI)⟩,
                ProgFrameOkLive.of_set_spill hfl hfValid hmxSp hpres1 (by rw [hmem1, hsp, hvalEq]) hf,
                houtSlot⟩
            · have hge : maxRes ≤ start := by omega
              have hco : copyOneResultItemR env.tab fl (x, start) =
                  loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.resOff start) ++
                  storeMemOff .sd AbiReg.sp AbiReg.t1 AbiReg.t2 (fl.varSlotOff x) := by
                simp [copyOneResultItemR, hlx, hmxSp, hst, hmx]
              rw [hco] at hl1 hpc1 ⊢
              have ⟨ha1, ha2⟩ := linkResolved_mid_split lkm pre _ _ _ hl1
              have hpa1 := linkResolved_sub_pc64 env pre _ _ ha1
              have halR : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.resOff start)) 8 = true := by
                rw [hgp]; exact isAligned8_of_resOff L hge hst
              obtain ⟨stm, hrunm, hothm, hvalm, hmemm, hnpcm⟩ :=
                loadMemOff_ld_correct_lm lkm env.hrom pre _ AbiReg.t1 AbiReg.gp AbiReg.t2
                  (by decide) (by decide) (by decide) (env.tab.resOff start) ha1 hpa1 st hpc halR
              have hspM : stm.getReg AbiReg.sp = sp := (hothm _ (by decide) (by decide)).trans hsp
              have halX' : isAligned (stm.getReg AbiReg.sp + BitVec.ofInt 64 (fl.varSlotOff x)) 8 = true := by
                rw [hspM, varSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hal _
              have hpa2 := linkResolved_sub_pc64 env (pre ++ _) _ _ ha2
              obtain ⟨st1, hrun1, hoth1, hmem1, hnpc1⟩ :=
                storeMemOff_sd_correct_lm lkm env.hrom (pre ++ _) _ AbiReg.sp AbiReg.t1 AbiReg.t2
                  (by decide) (by decide) (by decide) (fl.varSlotOff x) ha2 hpa2 stm
                  (by simpa [lkm.totalSize_append] using hnpcm) halX'
              have hvalEq : stm.getReg AbiReg.t1 = (vs.getD start 0).toBitVec := by
                rw [hvalm, hgp]; exact hres.2 start hge (by simp only [List.length_cons]; omega)
              have houtSlot : MemEqOutside (localsTempSpanR fl sp) st.mem st1.mem := by
                rw [hmem1, hmemm, hspM, hvalEq]
                exact MemEqOutside.writeWord64 _ _ _ fun k hk => hltSub _ ⟨k, hk, by
                  simp only [varSlotSpanR, slotSpan, slotAddr, varSlotOff_ofInt]⟩
              have hpres1 : PreservedFrameRegs fl (· = AbiReg.a0) st st1 :=
                (PreservedFrameRegs.of_scratch2 AbiReg.t1 AbiReg.t2 (by decide) (by decide) hothm).trans
                  (PreservedFrameRegs.of_scratch1 AbiReg.t2 (by decide) hoth1)
              refine ⟨_, st1, by rw [run_add, hrunm]; dsimp only; exact hrun1,
                by simpa [lkm.totalSize_append, Nat.add_assoc] using hnpc1,
                PreservedFrameRegs.of_a0 hpres1,
                ⟨fun i hloI hhiI => by omega,
                 fun i hloI hhiI => (MemEqOutside.readWord64_eq houtSlot _ (hdisjRes i hloI (by simp [maxRes] at hloI; omega))).trans (hres.2 i hloI hhiI)⟩,
                ProgFrameOkLive.of_set_spill hfl hfValid hmxSp hpres1 (by rw [hmem1, hmemm, hspM, hvalEq]) hf,
                houtSlot⟩
          · have hco : copyOneResultItemR env.tab fl (x, start) =
                storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t0 (fl.varSlotOff x) := by
              simp [copyOneResultItemR, hlx, hmxSp, hst]
            rw [hco] at hl1 hpc1 ⊢
            obtain ⟨st1, hrun1, hoth1, hmem1, hnpc1⟩ :=
              storeMemOff_sd_correct_lm lkm env.hrom pre _ AbiReg.sp AbiReg.zero AbiReg.t0
                (by decide) (by decide) (by decide) (fl.varSlotOff x) hl1 hpc1 st hpc halX
            have hzeroReg : st.getReg AbiReg.zero = 0#64 := getReg_zero st
            have hzeroVal : (vs.getD start 0).toBitVec = 0#64 := by
              simp [List.getD, List.getElem?_eq_none (by omega : vs.length ≤ start)]
            have houtSlot : MemEqOutside (localsTempSpanR fl sp) st.mem st1.mem := by
              rw [hmem1, hsp, hzeroReg, ← hzeroVal]
              exact MemEqOutside.writeWord64 _ _ _ fun k hk => hltSub _ ⟨k, hk, by
                simp only [varSlotSpanR, slotSpan, slotAddr, varSlotOff_ofInt]⟩
            have hpres1 : PreservedFrameRegs fl (· = AbiReg.a0) st st1 :=
              PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hoth1
            refine ⟨_, st1, hrun1, hnpc1, PreservedFrameRegs.of_a0 hpres1,
              ⟨fun i hloI hhiI => (hoth1 _ (resReg_ne_preserved i).2.2.2.2.2.1).trans (hres.1 i (by omega) hhiI),
               fun i hloI hhiI => (MemEqOutside.readWord64_eq houtSlot _ (hdisjRes i hloI (by simp [maxRes] at hloI; omega))).trans (hres.2 i hloI hhiI)⟩,
              ProgFrameOkLive.of_set_spill hfl hfValid hmxSp hpres1 (by rw [hmem1, hsp, hzeroReg, ← hzeroVal]) hf,
              houtSlot⟩
        · have hco : copyOneResultItemR env.tab fl (x, start) = [] := by
            simp [copyOneResultItemR, hlx, hmxSp]
          rw [hco]
          refine ⟨0, st, rfl, by simp [lkm.totalSize_nil, hpc],
            PreservedFrameRegs.refl _ _ _,
            ⟨fun i hloI hhiI => hres.1 i (by omega) hhiI, hres.2⟩,
            ?_, MemEqOutside.refl _ _⟩
          intro y hy hly2
          by_cases hxy : y = x
          · subst hxy; rw [hlx]; intro hm; exact absurd hm hmxSp
          · simp only [hxy, ↓reduceIte]; exact hf y hy hly2
    have hresSafeRest : ∀ x' i, (x', i) ∈ rest.zipIdx (start + 1) → ∀ rx, fl.alloc.lookup x' = some rx →
        ∀ j, i < j → j < min (start + 1 + rest.length) maxRes → rx ≠ resReg j := by
      intro x' i hmem rx hlk j hlt hj
      exact hresSafe x' i (by rw [List.zipIdx_cons]; exact List.mem_cons_of_mem _ hmem) rx hlk j hlt (by rw [← hhiEq]; exact hj)
    have hnoClobRest : ∀ y ry, fl.alloc.lookup y = some ry → live2 y = true →
        ∀ x' ∈ rest, x' ≠ y → fl.alloc.lookup x' ≠ some ry :=
      fun y ry hly hly2 x' hx' => hnoClob y ry hly hly2 x' (List.mem_cons_of_mem _ hx')
    obtain ⟨k2, st2, hrun2, hpc2, hpres2, hf2, hout2⟩ :=
      ih (start + 1) (fun y hy => hxs y (by simp [hy])) (by simp only [List.length_cons] at hxsAr; omega)
        hresSafeRest hnoClobRest
        (pre ++ copyOneResultItemR env.tab fl (x, start)) post hl2
        (fun y => if y = x then vs.getD start 0 else loc y) st1
        (by simpa [lkm.totalSize_append] using hpc1')
        (hpres1.abi.gp.trans hgp) (hpres1.abi.sp.trans hsp) (by rw [hhiEq]; exact hres1) hf1
    refine ⟨k1 + k2, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
      by simpa [lkm.totalSize_append, Nat.add_assoc] using hpc2,
      hpres1.trans hpres2, ?_, hout1.trans hout2⟩
    have hlocEq : (({ mem := m0, loc := loc } : _root_.L.St).setLocs (x :: rest) (vs.drop start)).loc =
        (({ mem := m0, loc := fun y => if y = x then vs.getD start 0 else loc y } : _root_.L.St).setLocs rest (vs.drop (start + 1))).loc := by
      simp [_root_.L.St.setLocs, _root_.L.St.setLoc]
    rwa [hlocEq]

/-! ### 2b. Frame-Pop, Cold Abort-0 Stub & Tail-Call Helpers -/

private theorem restoreCalleeRegsLoop_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (fl : FrameLayout) {sp : BitVec 64}
    (hal : isAligned sp 8 = true) :
    ∀ (regs : List Reg) (start : Nat),
      regs.Nodup →
      (∀ r ∈ regs, r ∈ calleeSavedBank) →
      ∀ (pre post : List AsmItem),
        lkm.linkSpec (pre ++ ((regs.zipIdx start).flatMap fun (r, i) =>
          loadMemOff .ld r AbiReg.sp AbiReg.t0 (fl.savedOff i)) ++ post) = .ok (env.code, env.labels) →
      ∀ (st : State),
        st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
        st.getReg AbiReg.sp = sp →
        ∃ k st',
          RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre +
            lkm.totalSize ((regs.zipIdx start).flatMap fun (r, i) =>
              loadMemOff .ld r AbiReg.sp AbiReg.t0 (fl.savedOff i)))) ∧
          st'.mem = st.mem ∧
          (∀ q, q ≠ AbiReg.t0 → q ∉ regs → st'.getReg q = st.getReg q) ∧
          (∀ i (hi : i < regs.length),
            st'.getReg (regs[i]'hi) = readWord64 st.mem (sp + BitVec.ofInt 64 (fl.savedOff (start + i)))) := by
  intro regs
  induction regs with
  | nil =>
    intro start _ _ pre post _ st hpc _
    refine ⟨0, st, rfl, by simp [lkm.totalSize_nil, hpc], rfl, fun _ _ _ => rfl,
      fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | cons r rest ih =>
    intro start hnd hcal pre post hlink st hpc hsp
    rw [List.nodup_cons] at hnd
    have hrCal : r ∈ calleeSavedBank := hcal r List.mem_cons_self
    have hsplit : ((r :: rest).zipIdx start).flatMap (fun (q, i) => loadMemOff .ld q AbiReg.sp AbiReg.t0 (fl.savedOff i)) =
        loadMemOff .ld r AbiReg.sp AbiReg.t0 (fl.savedOff start) ++
        (rest.zipIdx (start + 1)).flatMap (fun (q, i) => loadMemOff .ld q AbiReg.sp AbiReg.t0 (fl.savedOff i)) := by
      simp [List.zipIdx_cons]
    rw [hsplit] at hlink ⊢
    have ⟨hl1, hl2⟩ := linkResolved_mid_split lkm pre _ _ post hlink
    have halS : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (fl.savedOff start)) 8 = true := by
      rw [hsp, savedOff_ofInt]; exact isAligned8_add_int_mul8 sp hal _
    obtain ⟨st1, hrun1, hoth1, hr1, hmem1, hpc1⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom pre _ r AbiReg.sp AbiReg.t0
        (allowedRegs_ne_zero (isLeaf := false) hrCal) (by decide) (by decide)
        (fl.savedOff start) hl1 (linkResolved_sub_pc64 env pre _ _ hl1) st hpc halS
    have hsp1 : st1.getReg AbiReg.sp = sp := (hoth1 _ (allowedRegs_ne_sp (isLeaf := false) hrCal).symm (by decide)).trans hsp
    obtain ⟨k2, st2, hrun2, hpc2, hmem2, hoth2, hrest2⟩ :=
      ih (start + 1) hnd.2 (fun q hq => hcal q (List.mem_cons_of_mem _ hq))
        (pre ++ loadMemOff .ld r AbiReg.sp AbiReg.t0 (fl.savedOff start)) post hl2 st1
        (by simpa [lkm.totalSize_append] using hpc1) hsp1
    refine ⟨_, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
      by simpa [lkm.totalSize_append, Nat.add_assoc] using hpc2,
      hmem2.trans hmem1,
      fun q hqt0 hqnm => by
        have hqne : q ≠ r := fun h => hqnm (h ▸ List.mem_cons_self)
        have hqnr : q ∉ rest := fun h => hqnm (List.mem_cons_of_mem _ h)
        exact (hoth2 q hqt0 hqnr).trans (hoth1 q hqne hqt0),
      ?_⟩
    intro i hi
    cases i with
    | zero =>
      simp only [Nat.add_zero, List.getElem_cons_zero]
      rw [hoth2 r (allowedRegs_ne_t0 (isLeaf := false) hrCal) hnd.1, hr1, hsp]
    | succ i' =>
      simp only [List.getElem_cons_succ]
      rw [show start + (i' + 1) = (start + 1) + i' by omega, hrest2 i' (by simpa using hi), hmem1]

theorem framePopItems_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    {sp callerSp callerRa : BitVec 64} {b : Nat}
    (calleeVals : Reg → BitVec 64)
    (hal : isAligned sp 8 = true)
    (hspEq : callerSp = sp + BitVec.ofInt 64 fl.frameBytes)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ framePopItems fl ++ post) = .ok (env.code, env.labels))
    (st : State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hs0 : st.getReg AbiReg.s0 = BitVec.ofNat 64 b)
    (hraLeaf : fl.isLeaf = true → st.getReg AbiReg.ra = callerRa)
    (hraSlot : fl.isLeaf = false → readWord64 st.mem sp = callerRa)
    (hcalUnsaved : ∀ r ∈ calleeSavedBank, r ∉ fl.savedRegs → st.getReg r = calleeVals r)
    (hcalSaved : ∀ i (hi : i < fl.savedRegs.length),
      readWord64 st.mem (sp + BitVec.ofInt 64 (fl.savedOff i)) = calleeVals (fl.savedRegs[i]'hi)) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (framePopItems fl))) ∧
      st'.getReg AbiReg.gp = L.T ∧
      st'.getReg AbiReg.sp = callerSp ∧
      st'.getReg AbiReg.ra = callerRa ∧
      st'.getReg AbiReg.s0 = BitVec.ofNat 64 b ∧
      st'.getReg AbiReg.s1 = st.getReg AbiReg.s1 ∧
      st'.getReg AbiReg.s2 = st.getReg AbiReg.s2 ∧
      (∀ r ∈ calleeSavedBank, st'.getReg r = calleeVals r) ∧
      (∀ i, i < maxRes → st'.getReg (resReg i) = st.getReg (resReg i)) ∧
      st'.mem = st.mem := by
  by_cases h0 : fl.frameSlots = 0
  · obtain ⟨hleaf, hsr, _, _⟩ := hfl.frameSlots_zero_props h0
    have hfb0 : (fl.frameBytes == 0) = true := by simp [FrameLayout.frameBytes, h0]
    have hfp0 : framePopItems fl = [] := by simp [framePopItems, hfb0]
    have hspEq' : callerSp = sp := by rw [hspEq, FrameLayout.frameBytes, h0]; simp
    refine ⟨0, st, rfl, by rw [hfp0, lkm.totalSize_nil, Nat.add_zero]; exact hpc,
      hgp, by rw [hspEq']; exact hsp, hraLeaf hleaf, hs0, rfl, rfl,
      fun r hr => hcalUnsaved r hr (by rw [hsr]; simp), fun _ _ => rfl, rfl⟩
  · have hfbNe : (fl.frameBytes == 0) = false := by
      simp only [FrameLayout.frameBytes, beq_eq_false_iff_ne]; omega
    let cRest := restoreCalleeRegs fl
    let cRa := if fl.isLeaf then [] else [Asm.ld AbiReg.ra AbiReg.sp 0#12]
    let cAdd := addImmOff AbiReg.sp AbiReg.sp AbiReg.t0 fl.frameBytes
    have hfpEq : framePopItems fl = cRest ++ cRa ++ cAdd := by
      simp [framePopItems, hfbNe, cRest, cRa, cAdd, List.append_assoc]
    have hlinkRest : lkm.linkSpec (pre ++ cRest ++ (cRa ++ cAdd ++ post)) = .ok (env.code, env.labels) := by
      rw [hfpEq] at hlink; simpa [List.append_assoc] using hlink
    obtain ⟨kR, st1, hrun1, hpc1, hmem1, hoth1, hrest1⟩ :=
      restoreCalleeRegsLoop_sim env fl hal fl.savedRegs 0 hfl.saved_nodup (fun r hr => hfl.saved_mem_callee hr)
        pre (cRa ++ cAdd ++ post) hlinkRest st hpc hsp
    have hnotSaved : ∀ q, q ∈ reservedAbiRegs → q ∉ fl.savedRegs := fun q hq hm =>
      allowedRegs_disj_reserved false (hfl.saved_mem_callee hm) hq rfl
    have hsp1 : st1.getReg AbiReg.sp = sp := (hoth1 _ (by decide) (hnotSaved _ (by simp [reservedAbiRegs]))).trans hsp
    let pre2 := pre ++ cRest
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) := by
      simpa [pre2, cRest, restoreCalleeRegs, lkm.totalSize_append] using hpc1
    have hraStep :
        ∃ kRa st2,
          RV64.run env.rom kRa st1 = .cont st2 ∧
          st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre2 ++ cRa)) ∧
          st2.getReg AbiReg.ra = callerRa ∧
          (∀ q, q ≠ AbiReg.ra → st2.getReg q = st1.getReg q) ∧
          st2.mem = st1.mem := by
      cases hleaf : fl.isLeaf with
      | true =>
        have hcRaE : cRa = [] := by simp [cRa, hleaf]
        exact ⟨0, st1, rfl, by rw [hcRaE, List.append_nil]; exact hpc1',
          (hoth1 _ (by decide) (hnotSaved _ (by simp [reservedAbiRegs]))).trans (hraLeaf hleaf),
          fun _ _ => rfl, rfl⟩
      | false =>
        have hcRaE : cRa = [Asm.ld AbiReg.ra AbiReg.sp 0#12] := by simp [cRa, hleaf]
        have hlinkLd : lkm.linkSpec (pre2 ++ [Asm.raw (.load .ld AbiReg.ra AbiReg.sp 0#12)] ++ (cAdd ++ post)) =
            .ok (env.code, env.labels) := by rw [hcRaE] at hlinkRest; simpa [pre2, Asm.raw, Asm.ld, List.append_assoc] using hlinkRest
        have hpcLd64 : 4 * (lkm.totalSize pre2 + 1) < 2 ^ 64 := by
          have h := linkResolved_sub_pc64 env pre2 [Asm.raw (.load .ld AbiReg.ra AbiReg.sp 0#12)] _ hlinkLd
          rw [show lkm.totalSize [Asm.raw (.load .ld AbiReg.ra AbiReg.sp 0#12)] = 1 from by simp only [Asm.raw, lkm.totalSize_instr]] at h; exact h
        have halSp : isAligned (st1.getReg AbiReg.sp + sextImm12 0#12) 8 = true := by
          rw [hsp1, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero]; exact hal
        obtain ⟨hrunLd, hpcLd, hraLd, hothLd, hmemLd⟩ :=
          step_ld_off env pre2 _ AbiReg.ra AbiReg.sp 0#12 (by decide) hlinkLd hpcLd64 st1 hpc1' halSp
        let st2 := stepReg st1 AbiReg.ra (readWord64 st1.mem (st1.getReg AbiReg.sp + sextImm12 0#12)) (st1.pc + 4#64)
        refine ⟨1, st2, hrunLd, ?_, ?_, hothLd, hmemLd⟩
        · rw [hpcLd, hcRaE]; simp only [lkm.totalSize_append, Asm.ld, lkm.totalSize_instr]
        · rw [hraLd, hmem1, hsp1, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero]; exact hraSlot hleaf
    obtain ⟨kRa, st2, hrun2, hpc2', hra2, hoth2, hmem2⟩ := hraStep
    let pre3 := pre2 ++ cRa
    have hlinkAdd : lkm.linkSpec (pre3 ++ cAdd ++ post) = .ok (env.code, env.labels) := by
      simpa [pre3, pre2, List.append_assoc] using hlinkRest
    obtain ⟨st3, hrun3, hoth3, hsp3, hmem3, hpc3⟩ :=
      addImmOff_correct_lm lkm env.hrom pre3 post AbiReg.sp AbiReg.sp AbiReg.t0 (by decide) (by decide) (by decide)
        fl.frameBytes hlinkAdd (linkResolved_sub_pc64 env pre3 cAdd post hlinkAdd) st2 hpc2'
    have hmem3Eq : st3.mem = st.mem := hmem3.trans (hmem2.trans hmem1)
    have hcalAll : ∀ r ∈ calleeSavedBank, st3.getReg r = calleeVals r := by
      intro r hr
      rw [hoth3 r (allowedRegs_ne_sp (isLeaf := false) hr) (allowedRegs_ne_t0 (isLeaf := false) hr),
          hoth2 r (allowedRegs_ne_ra (isLeaf := false) hr)]
      by_cases hmemS : r ∈ fl.savedRegs
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmemS
        have h := hrest1 i hi; simp only [Nat.zero_add] at h
        rw [h]; exact hcalSaved i hi
      · exact (hoth1 r (allowedRegs_ne_t0 (isLeaf := false) hr) hmemS).trans (hcalUnsaved r hr hmemS)
    have hresAll : ∀ i, i < maxRes → st3.getReg (resReg i) = st.getReg (resReg i) := by
      intro i _
      have hr := resReg_ne_preserved i
      have hnotS : resReg i ∉ fl.savedRegs := fun hm =>
        nonLeaf_allowed_ne_resReg (hfl.saved_mem_callee hm) i rfl
      rw [hoth3 _ hr.2.1 hr.2.2.2.2.2.1, hoth2 _ (resReg_ne_ra i), hoth1 _ hr.2.2.2.2.2.1 hnotS]
    refine ⟨_, st3, run_trans (run_trans hrun1 hrun2) hrun3,
      by rw [hpc3, hfpEq]; dsimp only [pre3, pre2, cAdd]; simp only [lkm.totalSize_append, Nat.add_assoc],
      by rw [hoth3 _ (by decide) (by decide), hoth2 _ (by decide),
             hoth1 _ (by decide) (hnotSaved _ (by simp [reservedAbiRegs])), hgp],
      by rw [hsp3, hoth2 _ (by decide), hsp1, ← hspEq],
      by rw [hoth3 _ (by decide) (by decide), hra2],
      by rw [hoth3 _ (by decide) (by decide), hoth2 _ (by decide),
             hoth1 _ (by decide) (hnotSaved _ (by simp [reservedAbiRegs])), hs0],
      by rw [hoth3 _ (by decide) (by decide), hoth2 _ (by decide),
             hoth1 _ (by decide) (hnotSaved _ (by simp [reservedAbiRegs]))],
      by rw [hoth3 _ (by decide) (by decide), hoth2 _ (by decide),
             hoth1 _ (by decide) (hnotSaved _ (by simp [reservedAbiRegs]))],
      hcalAll, hresAll, hmem3Eq⟩

/-- Cold abort-0 stub specification: `s!"{pfx}_abort0stub"` is linked to
    `addi a0, zero, 0; j abortLabel`, reaching `env.abortTarget` with `a0 = 0` and `PreservedTramp`. -/
def Abort0StubOk {lkm : LinkModel} (env : CodeEnvGen lkm) (pfx : String) : Prop :=
  ∃ ab0Pc, lookupLabel env.labels s!"{pfx}_abort0stub" = some ab0Pc ∧
    ∀ stA : State, stA.pc = BitVec.ofNat 64 (4 * ab0Pc) →
      ∃ k r', RV64.run env.rom k stA = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.abortTarget) ∧
        r'.getReg AbiReg.a0 = 0#64 ∧
        PreservedTramp stA r' ∧
        r'.mem = stA.mem

theorem abort0Stub_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (pfx : String)
    (preAb postAb : List AsmItem)
    (hlink : lkm.linkSpec (preAb ++
      [Asm.lbl s!"{pfx}_abort0stub", Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.j abortLabel] ++ postAb) =
      .ok (env.code, env.labels)) :
    Abort0StubOk env pfx := by
  have hab0Lbl : lookupLabel env.labels s!"{pfx}_abort0stub" = some (lkm.totalSize preAb) :=
    linkResolved_lbl_lm lkm preAb s!"{pfx}_abort0stub" _ (by simpa [List.append_assoc] using hlink)
  refine ⟨lkm.totalSize preAb, hab0Lbl, fun stA hpcA => ?_⟩
  let pre1 := preAb ++ [Asm.lbl s!"{pfx}_abort0stub"]
  have hpc1 : stA.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by
    rw [hpcA]; simp only [pre1, lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero]
  have hlink1 : lkm.linkSpec (pre1 ++ [Asm.addi AbiReg.a0 AbiReg.zero 0#12] ++ ([Asm.j abortLabel] ++ postAb)) =
      .ok (env.code, env.labels) := by simpa [pre1, List.append_assoc] using hlink
  obtain ⟨hrun1, hpc1', ha0_1, hoth1, hmem1⟩ :=
    run_aluImm_rd_step env pre1 _ .addi AbiReg.a0 AbiReg.zero 0#12 (by decide) hlink1 stA hpc1
  let st1 := stepReg stA AbiReg.a0 (evalAluImm .addi (stA.getReg AbiReg.zero) 0#12)
    (BitVec.ofNat 64 (4 * (lkm.totalSize pre1 + 1)))
  have ha0Val : st1.getReg AbiReg.a0 = 0#64 := by
    rw [ha0_1]; change stA.getReg AbiReg.zero + sextImm12 0#12 = 0#64; rw [getReg_zero]; decide
  let pre2 := pre1 ++ [Asm.addi AbiReg.a0 AbiReg.zero 0#12]
  have hlink2 : lkm.linkSpec (pre2 ++ [Asm.j abortLabel] ++ postAb) = .ok (env.code, env.labels) := by
    simpa [pre2, List.append_assoc] using hlink1
  have hpc2 : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) := by
    rw [hpc1']; simp only [pre2, lkm.totalSize_append, Asm.addi, lkm.totalSize_instr]
  have h64J : 4 * (lkm.totalSize pre2 + lkm.itemSize (.j abortLabel)) < 2 ^ 64 := by
    simpa [Asm.j, lkm.totalSize_singleton] using linkResolved_sub_pc64 env pre2 [Asm.j abortLabel] postAb hlink2
  obtain ⟨kJ, r', hrunJ, hpcJ, hothJ, hpresJ, hmemJ⟩ :=
    prog_step_j env pre2 postAb abortLabel env.abortTarget env.habortLbl hlink2 h64J st1 hpc2
  have htr1 : PreservedTramp stA st1 := ⟨hoth1 _ (by decide), hoth1 _ (by decide)⟩
  exact ⟨1 + kJ, r', by rw [run_add, hrun1]; exact hrunJ, hpcJ,
    (hothJ AbiReg.a0 (by decide)).trans ha0Val, htr1.trans hpresJ.toTramp, hmemJ.trans hmem1⟩

theorem eq_abort0_of_isAbort0Stmt {s : Stmt} (h : isAbort0Stmt s = true) :
    s = .abort (.const 0) := by
  unfold isAbort0Stmt at h
  split at h
  · rfl
  · cases h

theorem tailCallRetMatch_spec {tab : Tab} {s1 s2 : Stmt}
    {xs : List Var} {f : FnName} {args es : List Expr}
    (h : tailCallRetMatch tab s1 s2 = some (xs, f, args, es)) :
    s1 = .call xs f args ∧ s2 = .ret es ∧
    xs ≠ [] ∧ isVarList xs es = true ∧ listNodupNat xs = true ∧
    args.length ≤ maxRes ∧ xs.length ≤ tab.nres ∧ xs.length ≤ maxRes := by
  cases s1 with
  | call xs' f' args' =>
    cases s2 with
    | ret es' =>
      simp only [tailCallRetMatch] at h
      split at h
      · next htc =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl, rfl⟩
        simp only [isTailCallRet, Bool.and_eq_true, Bool.not_eq_true',
          List.isEmpty_eq_false_iff, decide_eq_true_eq] at htc
        exact ⟨rfl, rfl, htc.1.1.1.1.1, htc.1.1.1.1.2, htc.1.1.1.2, htc.1.1.2, htc.1.2, htc.2⟩
      · cases h
    | _ => simp [tailCallRetMatch] at h
  | _ => simp [tailCallRetMatch] at h

private theorem setLocs_loc_of_not_mem (xs : List Var) (vs : List _root_.L.Word) (s : _root_.L.St)
    {x : Var} (hnm : x ∉ xs) :
    (s.setLocs xs vs).loc x = s.loc x := by
  induction xs generalizing s vs with
  | nil => rfl
  | cons y ys ih =>
    have hne : x ≠ y := fun h => hnm (h ▸ List.mem_cons_self)
    have hnm' : x ∉ ys := fun h => hnm (List.mem_cons_of_mem _ h)
    simp only [_root_.L.St.setLocs, _root_.L.St.setLoc]
    rw [ih vs.tail _ hnm']
    simp [hne]

theorem evalArgs_of_isVarList_setLocs (xs : List Var) :
    ∀ (es : List Expr), isVarList xs es = true → listNodupNat xs = true →
      ∀ (m : _root_.L.Mem) (loc : _root_.L.Locals) (vs : List _root_.L.Word),
        ∃ vsOut,
          _root_.L.evalArgs es (({ mem := m, loc := loc } : _root_.L.St).setLocs xs vs) =
            .ok (vsOut, ({ mem := m, loc := loc } : _root_.L.St).setLocs xs vs) ∧
          vsOut.length = xs.length ∧
          (∀ i, i < xs.length → vsOut.getD i 0 = vs.getD i 0) := by
  induction xs with
  | nil =>
    intro es hvl _ m loc vs
    cases es with
    | nil => exact ⟨[], rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    | cons _ _ => simp [isVarList] at hvl
  | cons x xs' ih =>
    intro es hvl hnd m loc vs
    cases es with
    | nil => simp [isVarList] at hvl
    | cons e es' =>
      cases e with
      | var y =>
        simp only [isVarList, Bool.and_eq_true, beq_iff_eq] at hvl
        rcases hvl with ⟨rfl, hvl'⟩
        simp only [listNodupNat, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hnd
        rcases hnd with ⟨hnm, hnd'⟩
        let loc1 : _root_.L.Locals := fun w => if w = x then vs.headD 0 else loc w
        have hstEq : (({ mem := m, loc := loc } : _root_.L.St).setLocs (x :: xs') vs) =
            (({ mem := m, loc := loc1 } : _root_.L.St).setLocs xs' vs.tail) := rfl
        obtain ⟨vsRest, heRest, hlenRest, hgetRest⟩ := ih es' hvl' hnd' m loc1 vs.tail
        rw [← hstEq] at heRest
        have hlocX : (({ mem := m, loc := loc } : _root_.L.St).setLocs (x :: xs') vs).loc x = vs.headD 0 := by
          rw [hstEq, setLocs_loc_of_not_mem xs' vs.tail ⟨m, loc1⟩ hnm]
          simp [loc1]
        have heX : _root_.L.evalE (.var x) (({ mem := m, loc := loc } : _root_.L.St).setLocs (x :: xs') vs) =
            .ok (vs.headD 0, ({ mem := m, loc := loc } : _root_.L.St).setLocs (x :: xs') vs) := by
          change Except.ok ((({ mem := m, loc := loc } : _root_.L.St).setLocs (x :: xs') vs).loc x, _) = _
          rw [hlocX]
        refine ⟨vs.headD 0 :: vsRest, ?_, by simp [hlenRest], ?_⟩
        · simp only [_root_.L.evalArgs, Bind.bind, StateT.bind, Except.bind, heX, heRest,
            Pure.pure, StateT.pure, Except.pure]
        · intro i hi
          cases i with
          | zero => cases vs <;> rfl
          | succ j =>
            simp only [List.getD, List.getElem?_cons_succ]
            have hj := hgetRest j (by simpa using hi)
            simp only [List.getD] at hj
            rw [hj]
            cases vs <;> simp
      | _ => simp [isVarList] at hvl

end ConAgua.RISCV.Compiler
