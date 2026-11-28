import ConAgua.RISCV.RV64.Roundtrip
import ConAgua.RISCV.Compiler.AsmProof
import ConAgua.RISCV.Linker.FarLinkProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Linker Abstraction Interface (`ConAgua.RISCV.Linker.LinkModel`)

Unifies near (`ConAgua.RISCV.Compiler.linkResolved`, `±1 MiB`/`±4 KiB`) and far
(`ConAgua.RISCV.Linker.linkFarSpec` / `linkFar`, `±2 GiB` via `jal t6 + lui s1 + add + jalr`)
symbolic linking behind a single `LinkModel` interface.

1. **`LinkModel`**: parameterizes `itemSize` (`.label _ ↦ 0`, `.instr _ ↦ 1`),
   `totalSize asm := (asm.map itemSize).sum`, `linkSpec`, `lookup_label_at`,
   exact 1-cycle `step_instr`, and multi-cycle (`k ≥ 1`) `step_j`, `step_call`,
   `step_br`, `step_brLong` permitting scratch clobber of `{AbiReg.t6, AbiReg.s1}` only.
2. **`RegEqExceptT6` & `AbiPreservedRegs`**: register-equality relation modulo `{t6, s1}`
   and 1-line preservation helpers for `{gp, sp, s0, s2}` across jumps/calls/branches.
3. **`nearLinkModel` & `farLinkModel`**: canonical instances backed by `AsmProof`
   and `FarLinkProof` (with `linkFar_ok_linkSpec` bridging `FarLink.linkFar`).
-/

namespace ConAgua.RISCV.Linker

open ConAgua.RISCV.RV64
open ConAgua.RISCV.Compiler

/-! ## 1. ROM Matching, `t6`-Modulo Register Equality, and Step Helpers -/

/-- A `Rom` contains the linked words `code` starting at word index `0`. -/
def RomMatches (rom : Rom) (code : Array (BitVec 32)) : Prop :=
  ∀ k, k < code.size → rom k = some code[k]!

theorem romOfArray_matches (code : Array (BitVec 32)) :
    RomMatches (romOfArray code) code := by
  intro k hk
  simp [romOfArray, hk]

theorem rom_decode_of_matches {rom : Rom} {code : Array (BitVec 32)}
    (hrom : RomMatches rom code) {k : Nat} {inst : Instr}
    (hdec : (code[k]?).bind decode = some inst) :
    (rom k).bind decode = some inst := by
  by_cases hlt : k < code.size
  · have hget : code[k]? = some code[k]! := by simp [hlt]
    rw [hget, Option.bind_some] at hdec
    rw [hrom k hlt, Option.bind_some, hdec]
  · have hget : code[k]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt hlt)
    rw [hget] at hdec
    cases hdec

theorem step_at_decoded_rom {rom : Rom} {k : Nat} (hk64 : 4 * k < 2 ^ 64)
    {inst : Instr} (hdec : (rom k).bind decode = some inst)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * k)) :
    RV64.step rom st = execInstr st inst := by
  unfold RV64.step
  have hal : isAligned st.pc 4 = true := by
    rw [hpc]
    unfold isAligned
    simp only [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb']
  simp only [hal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hpcNat : st.pc.toNat / 4 = k := by
    rw [hpc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
    omega
  rw [hpcNat]
  cases hr : rom k with
  | none => rw [hr] at hdec; cases hdec
  | some w =>
    rw [hr, Option.bind_some] at hdec
    dsimp only
    rw [hdec]

private theorem setReg_regs_zero (st : State) (r : Reg) (v : Word) :
    (st.setReg r v).regs 0#5 = st.regs 0#5 := by
  unfold State.setReg
  by_cases hr0 : r == 0#5
  · simp [hr0]
  · simp only [hr0, Bool.false_eq_true, ↓reduceIte]
    have hneq : ((0#5 : Reg) == r) = false := by
      cases heq : (0#5 : Reg) == r with
      | false => rfl
      | true =>
        exfalso
        exact hr0 (beq_iff_eq.mpr (beq_iff_eq.mp heq).symm)
    simp [hneq]

private theorem execInstr_regs_zero (st st' : State) (inst : Instr)
    (h : execInstr st inst = .cont st') :
    st'.regs 0#5 = st.regs 0#5 := by
  cases inst with
  | lui rd imm20 =>
    simp only [execInstr, StepResult.cont.injEq] at h
    subst h; exact setReg_regs_zero st rd _
  | jal rd jimm =>
    simp only [execInstr, StepResult.cont.injEq] at h
    subst h; exact setReg_regs_zero st rd _
  | jalr rd rs1 imm12 =>
    simp only [execInstr, StepResult.cont.injEq] at h
    subst h; exact setReg_regs_zero st rd _
  | branch op rs1 rs2 bimm =>
    simp only [execInstr, StepResult.cont.injEq] at h
    subst h; rfl
  | load op rd rs1 imm12 =>
    cases op with
    | lbu =>
      simp only [execInstr, StepResult.cont.injEq] at h
      subst h; exact setReg_regs_zero st rd _
    | lwu | ld =>
      simp only [execInstr] at h
      split at h
      · simp only [StepResult.cont.injEq] at h; subst h; exact setReg_regs_zero st rd _
      · cases h
  | store op rs1 rs2 imm12 =>
    cases op with
    | sw | sd =>
      simp only [execInstr] at h
      split at h
      · simp only [StepResult.cont.injEq] at h; subst h; rfl
      · cases h
  | aluImm op rd rs1 imm12 =>
    simp only [execInstr, StepResult.cont.injEq] at h
    subst h; exact setReg_regs_zero st rd _
  | shImm op rd rs1 shamt =>
    simp only [execInstr, StepResult.cont.injEq] at h
    subst h; exact setReg_regs_zero st rd _
  | alu op rd rs1 rs2 =>
    simp only [execInstr, StepResult.cont.injEq] at h
    subst h; exact setReg_regs_zero st rd _

theorem step_regs_zero {rom : Rom} {st st' : State}
    (h : RV64.step rom st = .cont st') :
    st'.regs 0#5 = st.regs 0#5 := by
  unfold RV64.step at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · exact execInstr_regs_zero st st' _ h

theorem run_regs_zero {rom : Rom} {k : Nat} {st st' : State}
    (h : RV64.run rom k st = .cont st') :
    st'.regs 0#5 = st.regs 0#5 := by
  induction k generalizing st with
  | zero =>
    simp only [RV64.run, StepResult.cont.injEq] at h
    subst h; rfl
  | succ k ih =>
    simp only [RV64.run] at h
    cases hs : RV64.step rom st with
    | cont s1 =>
      rw [hs] at h
      exact (ih h).trans (step_regs_zero hs)
    | trap => rw [hs] at h; cases h

/-- Register-file equality everywhere except possibly far-linker scratch `{AbiReg.t6, AbiReg.s1}`. -/
def RegEqExceptT6 (r1 r2 : Reg → Word) : Prop :=
  ∀ r : Reg, r ≠ AbiReg.t6 ∧ r ≠ AbiReg.s1 → r1 r = r2 r

theorem RegEqExceptT6.refl (r : Reg → Word) : RegEqExceptT6 r r :=
  fun _ _ => rfl

theorem RegEqExceptT6.symm {r1 r2 : Reg → Word} (h : RegEqExceptT6 r1 r2) :
    RegEqExceptT6 r2 r1 :=
  fun r hr => (h r hr).symm

theorem RegEqExceptT6.trans {r1 r2 r3 : Reg → Word}
    (h12 : RegEqExceptT6 r1 r2) (h23 : RegEqExceptT6 r2 r3) :
    RegEqExceptT6 r1 r3 :=
  fun r hr => (h12 r hr).trans (h23 r hr)

theorem RegEqExceptT6.of_eq {r1 r2 : Reg → Word} (h : r1 = r2) :
    RegEqExceptT6 r1 r2 := by
  subst h; exact RegEqExceptT6.refl _

theorem RegEqExceptT6.update_t6 (regs : Reg → Word) (v : Word) :
    RegEqExceptT6 regs (fun r => if r == AbiReg.t6 then v else regs r) := by
  intro r hr
  simp [beq_false_of_ne hr.1]

theorem RegEqExceptT6.getReg_eq {st1 st2 : State}
    (h : RegEqExceptT6 st1.regs st2.regs) {r : Reg} (hr : r ≠ AbiReg.t6 ∧ r ≠ AbiReg.s1) :
    st1.getReg r = st2.getReg r := by
  unfold State.getReg
  split
  · rfl
  · exact h r hr

theorem RegEqExceptT6.of_getReg_zero_eq {st1 st2 : State}
    (hzero : st1.regs 0#5 = st2.regs 0#5)
    (hget : ∀ r : Reg, r ≠ AbiReg.t6 ∧ r ≠ AbiReg.s1 → st1.getReg r = st2.getReg r) :
    RegEqExceptT6 st1.regs st2.regs := by
  intro r hr
  by_cases hr0 : r = 0#5
  · subst hr0; exact hzero
  · have hg := hget r hr
    simpa [State.getReg, beq_false_of_ne hr0] using hg

private theorem getReg_setReg_self (st : State) (r : Reg) (hr : r ≠ 0#5) (v : Word) :
    (st.setReg r v).getReg r = v := by
  simp [State.getReg, State.setReg, beq_false_of_ne hr]

private theorem getReg_setReg_other (st : State) (r q : Reg) (hne : q ≠ r) (v : Word) :
    (st.setReg r v).getReg q = st.getReg q := by
  unfold State.getReg State.setReg
  split
  · rfl
  · split
    · simp
    · simp [beq_false_of_ne hne]

/-- ABI callee-saved / frame-pointer register preservation (`gp, sp, s0, s2`),
    matching `ConAgua.RISCV.Compiler.PreservedRegs` (`s1` is reserved as far-linker scratch
    and saved/restored at entry/exit by `callerSaveAsm`/`callerRestoreRetAsm`). -/
structure AbiPreservedRegs (st0 st1 : State) : Prop where
  gp : st1.getReg AbiReg.gp = st0.getReg AbiReg.gp
  sp : st1.getReg AbiReg.sp = st0.getReg AbiReg.sp
  s0 : st1.getReg AbiReg.s0 = st0.getReg AbiReg.s0
  s2 : st1.getReg AbiReg.s2 = st0.getReg AbiReg.s2

theorem AbiPreservedRegs.refl (st : State) : AbiPreservedRegs st st :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem AbiPreservedRegs.trans {st0 st1 st2 : State}
    (h01 : AbiPreservedRegs st0 st1) (h12 : AbiPreservedRegs st1 st2) :
    AbiPreservedRegs st0 st2 :=
  ⟨h12.gp.trans h01.gp, h12.sp.trans h01.sp, h12.s0.trans h01.s0,
   h12.s2.trans h01.s2⟩

theorem AbiPreservedRegs.of_regEqExceptT6 {st0 st1 : State}
    (h : RegEqExceptT6 st0.regs st1.regs) :
    AbiPreservedRegs st0 st1 :=
  ⟨(RegEqExceptT6.getReg_eq h (by decide)).symm,
   (RegEqExceptT6.getReg_eq h (by decide)).symm,
   (RegEqExceptT6.getReg_eq h (by decide)).symm,
   (RegEqExceptT6.getReg_eq h (by decide)).symm⟩

theorem AbiPreservedRegs.of_setReg_ra_regEqExceptT6 {st0 st1 : State} {raVal : Word}
    (h : RegEqExceptT6 (st0.setReg AbiReg.ra raVal).regs st1.regs) :
    AbiPreservedRegs st0 st1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (RegEqExceptT6.getReg_eq h (by decide)).symm.trans
      (getReg_setReg_other st0 AbiReg.ra AbiReg.gp (by decide) raVal)
  · exact (RegEqExceptT6.getReg_eq h (by decide)).symm.trans
      (getReg_setReg_other st0 AbiReg.ra AbiReg.sp (by decide) raVal)
  · exact (RegEqExceptT6.getReg_eq h (by decide)).symm.trans
      (getReg_setReg_other st0 AbiReg.ra AbiReg.s0 (by decide) raVal)
  · exact (RegEqExceptT6.getReg_eq h (by decide)).symm.trans
      (getReg_setReg_other st0 AbiReg.ra AbiReg.s2 (by decide) raVal)

theorem getReg_ra_of_setReg_ra_regEqExceptT6 {st0 st1 : State} {raVal : Word}
    (h : RegEqExceptT6 (st0.setReg AbiReg.ra raVal).regs st1.regs) :
    st1.getReg AbiReg.ra = raVal :=
  (RegEqExceptT6.getReg_eq h (by decide)).symm.trans
    (getReg_setReg_self st0 AbiReg.ra (by decide) raVal)

theorem getReg_other_of_setReg_ra_regEqExceptT6 {st0 st1 : State} {raVal : Word}
    (h : RegEqExceptT6 (st0.setReg AbiReg.ra raVal).regs st1.regs)
    {r : Reg} (hra : r ≠ AbiReg.ra) (hscr : r ≠ AbiReg.t6 ∧ r ≠ AbiReg.s1) :
    st1.getReg r = st0.getReg r :=
  (RegEqExceptT6.getReg_eq h hscr).symm.trans
    (getReg_setReg_other st0 AbiReg.ra r hra raVal)

/-! ## 2. `LinkModel` Interface -/

/-- Sum of `itemSize` across an `AsmItem` list. -/
def totalSizeWith (sz : AsmItem → Nat) (asm : List AsmItem) : Nat :=
  (asm.map sz).sum

/-- Abstract linker model supporting near (`linkResolved`) and far (`linkFarSpec`/`linkFar`) linking. -/
structure LinkModel where
  itemSize : AsmItem → Nat
  itemSize_label : ∀ s, itemSize (.label s) = 0
  itemSize_instr : ∀ i, itemSize (.instr i) = 1
  linkSpec : List AsmItem → Except String (Array (BitVec 32) × LabelMap)
  linkSpec_size :
    ∀ {items code labels},
      linkSpec items = .ok (code, labels) →
      code.size = totalSizeWith itemSize items
  word_decoded :
    ∀ {items code labels},
      linkSpec items = .ok (code, labels) →
      ∀ k, k < code.size → ∃ inst : Instr, (code[k]?).bind decode = some inst
  lookup_label_at :
    ∀ {code labels pre name post},
      linkSpec (pre ++ [.label name] ++ post) = .ok (code, labels) →
      lookupLabel labels name = some (totalSizeWith itemSize pre)
  step_instr :
    ∀ {rom code labels pre post inst st},
      RomMatches rom code →
      linkSpec (pre ++ [.instr inst] ++ post) = .ok (code, labels) →
      4 * totalSizeWith itemSize pre < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * totalSizeWith itemSize pre) →
      RV64.step rom st = execInstr st inst
  step_j :
    ∀ {rom code labels pre post target st},
      RomMatches rom code →
      linkSpec (pre ++ [.j target] ++ post) = .ok (code, labels) →
      4 * (totalSizeWith itemSize pre + itemSize (.j target)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * totalSizeWith itemSize pre) →
      ∃ tgt k st', 1 ≤ k ∧
        lookupLabel labels target = some tgt ∧
        RV64.run rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * tgt) ∧
        RegEqExceptT6 st.regs st'.regs ∧
        st'.mem = st.mem
  step_call :
    ∀ {rom code labels pre post target st},
      RomMatches rom code →
      linkSpec (pre ++ [.call target] ++ post) = .ok (code, labels) →
      4 * (totalSizeWith itemSize pre + itemSize (.call target)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * totalSizeWith itemSize pre) →
      ∃ tgt k st', 1 ≤ k ∧
        lookupLabel labels target = some tgt ∧
        RV64.run rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * tgt) ∧
        RegEqExceptT6
          (st.setReg AbiReg.ra
            (BitVec.ofNat 64 (4 * (totalSizeWith itemSize pre + itemSize (.call target))))).regs
          st'.regs ∧
        st'.mem = st.mem
  step_br :
    ∀ {rom code labels pre post op rs1 rs2 target st},
      RomMatches rom code →
      linkSpec (pre ++ [.br op rs1 rs2 target] ++ post) = .ok (code, labels) →
      rs1 ≠ AbiReg.t6 ∧ rs2 ≠ AbiReg.t6 →
      4 * (totalSizeWith itemSize pre + itemSize (.br op rs1 rs2 target)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * totalSizeWith itemSize pre) →
      ∃ tgt k st', 1 ≤ k ∧
        lookupLabel labels target = some tgt ∧
        RV64.run rom k st = .cont st' ∧
        st'.pc = (if evalBranch op (st.getReg rs1) (st.getReg rs2)
                  then BitVec.ofNat 64 (4 * tgt)
                  else BitVec.ofNat 64 (4 * (totalSizeWith itemSize pre + itemSize (.br op rs1 rs2 target)))) ∧
        RegEqExceptT6 st.regs st'.regs ∧
        st'.mem = st.mem
  step_brLong :
    ∀ {rom code labels pre post op rs1 rs2 target st},
      RomMatches rom code →
      linkSpec (pre ++ [.brLong op rs1 rs2 target] ++ post) = .ok (code, labels) →
      rs1 ≠ AbiReg.t6 ∧ rs2 ≠ AbiReg.t6 →
      4 * (totalSizeWith itemSize pre + itemSize (.brLong op rs1 rs2 target)) < 2 ^ 64 →
      st.pc = BitVec.ofNat 64 (4 * totalSizeWith itemSize pre) →
      ∃ tgt k st', 1 ≤ k ∧
        lookupLabel labels target = some tgt ∧
        RV64.run rom k st = .cont st' ∧
        st'.pc = (if evalBranch op (st.getReg rs1) (st.getReg rs2)
                  then BitVec.ofNat 64 (4 * tgt)
                  else BitVec.ofNat 64 (4 * (totalSizeWith itemSize pre + itemSize (.brLong op rs1 rs2 target)))) ∧
        RegEqExceptT6 st.regs st'.regs ∧
        st'.mem = st.mem

/-! ## 3. `totalSize` Algebra & `CodeAt` Slice Helpers -/

/-- Word count of an `AsmItem` list under `lm : LinkModel`. -/
def LinkModel.totalSize (lm : LinkModel) (asm : List AsmItem) : Nat :=
  totalSizeWith lm.itemSize asm

@[simp] theorem LinkModel.totalSize_nil (lm : LinkModel) :
    lm.totalSize [] = 0 := rfl

@[simp] theorem LinkModel.totalSize_cons (lm : LinkModel) (x : AsmItem) (xs : List AsmItem) :
    lm.totalSize (x :: xs) = lm.itemSize x + lm.totalSize xs := rfl

@[simp] theorem LinkModel.totalSize_append (lm : LinkModel) (xs ys : List AsmItem) :
    lm.totalSize (xs ++ ys) = lm.totalSize xs + lm.totalSize ys := by
  simp [LinkModel.totalSize, totalSizeWith, List.map_append, List.sum_append]

@[simp] theorem LinkModel.totalSize_singleton (lm : LinkModel) (x : AsmItem) :
    lm.totalSize [x] = lm.itemSize x := by
  simp [LinkModel.totalSize, totalSizeWith]

@[simp] theorem LinkModel.totalSize_label (lm : LinkModel) (name : String) :
    lm.totalSize [.label name] = 0 := by
  simp [lm.itemSize_label]

@[simp] theorem LinkModel.totalSize_instr (lm : LinkModel) (inst : Instr) :
    lm.totalSize [.instr inst] = 1 := by
  simp [lm.itemSize_instr]

@[simp] theorem LinkModel.totalSize_instrs (lm : LinkModel) (insts : List Instr) :
    lm.totalSize (insts.map .instr) = insts.length := by
  induction insts with
  | nil => simp
  | cons i is ih =>
    simp [LinkModel.totalSize_cons, lm.itemSize_instr, ih, Nat.add_comm]

/-- Slice predicate stating that `items` is linked inside `(code, labels)` after `pre`. -/
def LinkModel.CodeAt (lm : LinkModel) (code : Array (BitVec 32)) (labels : LabelMap)
    (pre items post : List AsmItem) : Prop :=
  lm.linkSpec (pre ++ items ++ post) = .ok (code, labels)

theorem LinkModel.CodeAt.of_link {lm : LinkModel} {code : Array (BitVec 32)} {labels : LabelMap}
    {pre items post : List AsmItem}
    (h : lm.linkSpec (pre ++ items ++ post) = .ok (code, labels)) :
    lm.CodeAt code labels pre items post := h

theorem LinkModel.CodeAt.size {lm : LinkModel} {code : Array (BitVec 32)} {labels : LabelMap}
    {pre items post : List AsmItem}
    (h : lm.CodeAt code labels pre items post) :
    code.size = lm.totalSize pre + lm.totalSize items + lm.totalSize post := by
  have hsz := lm.linkSpec_size h
  simpa [LinkModel.totalSize, totalSizeWith, List.map_append, List.sum_append, Nat.add_assoc] using hsz

theorem LinkModel.CodeAt.sub_pc64 {lm : LinkModel} {code : Array (BitVec 32)} {labels : LabelMap}
    {pre items post : List AsmItem}
    (hcode64 : 4 * code.size < 2 ^ 64)
    (h : lm.CodeAt code labels pre items post) :
    4 * (lm.totalSize pre + lm.totalSize items) < 2 ^ 64 := by
  have hsz := h.size
  omega

theorem LinkModel.CodeAt.split_left {lm : LinkModel} {code : Array (BitVec 32)} {labels : LabelMap}
    {pre a b post : List AsmItem}
    (h : lm.CodeAt code labels pre (a ++ b) post) :
    lm.CodeAt code labels pre a (b ++ post) := by
  simpa [LinkModel.CodeAt, List.append_assoc] using h

theorem LinkModel.CodeAt.split_right {lm : LinkModel} {code : Array (BitVec 32)} {labels : LabelMap}
    {pre a b post : List AsmItem}
    (h : lm.CodeAt code labels pre (a ++ b) post) :
    lm.CodeAt code labels (pre ++ a) b post := by
  simpa [LinkModel.CodeAt, List.append_assoc] using h

theorem LinkModel.CodeAt.mid_split {lm : LinkModel} {code : Array (BitVec 32)} {labels : LabelMap}
    {pre a b post : List AsmItem}
    (h : lm.CodeAt code labels pre (a ++ b) post) :
    lm.CodeAt code labels pre a (b ++ post) ∧ lm.CodeAt code labels (pre ++ a) b post :=
  ⟨h.split_left, h.split_right⟩

theorem LinkModel.CodeAt.reassoc {lm : LinkModel} {code : Array (BitVec 32)} {labels : LabelMap}
    {pre mid post pre' mid' post' : List AsmItem}
    (heq : pre ++ mid ++ post = pre' ++ mid' ++ post')
    (h : lm.CodeAt code labels pre mid post) :
    lm.CodeAt code labels pre' mid' post' := by
  simpa [LinkModel.CodeAt, heq] using h

theorem LinkModel.CodeAt.lookup_label {lm : LinkModel} {code : Array (BitVec 32)} {labels : LabelMap}
    {pre : List AsmItem} {name : String} {post : List AsmItem}
    (h : lm.CodeAt code labels pre [.label name] post) :
    lookupLabel labels name = some (lm.totalSize pre) :=
  lm.lookup_label_at h

/-! ## 4. Near Linker Instance (`nearLinkModel`) -/

private theorem totalSizeWith_wordSize_eq (asm : List AsmItem) :
    totalSizeWith AsmItem.wordSize asm = totalWords asm := by
  have foldl_add : ∀ (xs : List AsmItem) (n : Nat),
      xs.foldl (fun acc item => acc + item.wordSize) n = n + (xs.map AsmItem.wordSize).sum := by
    intro xs n
    induction xs generalizing n with
    | nil => simp
    | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih (n + x.wordSize), Nat.add_assoc]
  unfold totalWords totalSizeWith
  rw [foldl_add asm 0, Nat.zero_add]

private theorem near_pc_add_4 {k : Nat} (pc : Word) (hpc : pc = BitVec.ofNat 64 (4 * k)) :
    pc + 4#64 = BitVec.ofNat 64 (4 * (k + 1)) := by
  rw [hpc, show (4#64 : Word) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
  congr 1

private theorem near_step_instr_aux {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    {pre post : List AsmItem} {inst : Instr} {st : State}
    (hrom : RomMatches rom code)
    (hlink : linkResolved (pre ++ [.instr inst] ++ post) = .ok (code, labels))
    (h64 : 4 * totalSizeWith AsmItem.wordSize pre < 2 ^ 64)
    (hpc : st.pc = BitVec.ofNat 64 (4 * totalSizeWith AsmItem.wordSize pre)) :
    RV64.step rom st = execInstr st inst := by
  rw [totalSizeWith_wordSize_eq] at h64 hpc
  have hdec := linkResolved_item_spec pre (.instr inst) post code labels hlink
  exact step_at_decoded_rom h64 (rom_decode_of_matches hrom hdec) st hpc

private theorem near_step_j_aux {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    {pre post : List AsmItem} {target : String} {st : State}
    (hrom : RomMatches rom code)
    (hlink : linkResolved (pre ++ [.j target] ++ post) = .ok (code, labels))
    (h64 : 4 * (totalSizeWith AsmItem.wordSize pre + AsmItem.wordSize (.j target)) < 2 ^ 64)
    (hpc : st.pc = BitVec.ofNat 64 (4 * totalSizeWith AsmItem.wordSize pre)) :
    ∃ tgt k st', 1 ≤ k ∧
      lookupLabel labels target = some tgt ∧
      RV64.run rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * tgt) ∧
      RegEqExceptT6 st.regs st'.regs ∧
      st'.mem = st.mem := by
  rw [totalSizeWith_wordSize_eq] at h64 hpc
  obtain ⟨tgt, jimm, hlook, hdec, hpcAdd⟩ :=
    linkResolved_item_spec pre (.j target) post code labels hlink
  have hs : RV64.step rom st = .cont { st with pc := BitVec.ofNat 64 (4 * tgt) } := by
    rw [step_at_decoded_rom (by simp [AsmItem.wordSize] at h64; omega) (rom_decode_of_matches hrom hdec) st hpc]
    simp only [execInstr, State.setReg, AbiReg.zero, beq_self_eq_true, ↓reduceIte]
    rw [hpc, hpcAdd]
  refine ⟨tgt, 1, { st with pc := BitVec.ofNat 64 (4 * tgt) }, (by omega), hlook, ?_, rfl,
    RegEqExceptT6.refl _, rfl⟩
  simp [RV64.run, hs]

private theorem near_step_call_aux {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    {pre post : List AsmItem} {target : String} {st : State}
    (hrom : RomMatches rom code)
    (hlink : linkResolved (pre ++ [.call target] ++ post) = .ok (code, labels))
    (h64 : 4 * (totalSizeWith AsmItem.wordSize pre + AsmItem.wordSize (.call target)) < 2 ^ 64)
    (hpc : st.pc = BitVec.ofNat 64 (4 * totalSizeWith AsmItem.wordSize pre)) :
    ∃ tgt k st', 1 ≤ k ∧
      lookupLabel labels target = some tgt ∧
      RV64.run rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * tgt) ∧
      RegEqExceptT6
        (st.setReg AbiReg.ra
          (BitVec.ofNat 64 (4 * (totalSizeWith AsmItem.wordSize pre + AsmItem.wordSize (.call target))))).regs
        st'.regs ∧
      st'.mem = st.mem := by
  rw [totalSizeWith_wordSize_eq] at h64 hpc ⊢
  obtain ⟨tgt, jimm, hlook, hdec, hpcAdd⟩ :=
    linkResolved_item_spec pre (.call target) post code labels hlink
  let st' : State :=
    { (st.setReg AbiReg.ra (BitVec.ofNat 64 (4 * (totalWords pre + 1)))) with
      pc := BitVec.ofNat 64 (4 * tgt) }
  have hs : RV64.step rom st = .cont st' := by
    rw [step_at_decoded_rom (by simp [AsmItem.wordSize] at h64; omega) (rom_decode_of_matches hrom hdec) st hpc]
    simp only [execInstr, st']
    rw [near_pc_add_4 st.pc hpc, hpc, hpcAdd]
  have hmem : st'.mem = st.mem := by
    dsimp only [st', State.setReg]; split <;> rfl
  refine ⟨tgt, 1, st', (by omega), hlook, ?_, rfl, ?_, hmem⟩
  · simp [RV64.run, hs]
  · simp [AsmItem.wordSize, st', RegEqExceptT6.refl]

private theorem near_step_br_aux {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    {pre post : List AsmItem} {op : BranchOp} {rs1 rs2 : Reg} {target : String} {st : State}
    (hrom : RomMatches rom code)
    (hlink : linkResolved (pre ++ [.br op rs1 rs2 target] ++ post) = .ok (code, labels))
    (h64 : 4 * (totalSizeWith AsmItem.wordSize pre + AsmItem.wordSize (.br op rs1 rs2 target)) < 2 ^ 64)
    (hpc : st.pc = BitVec.ofNat 64 (4 * totalSizeWith AsmItem.wordSize pre)) :
    ∃ tgt k st', 1 ≤ k ∧
      lookupLabel labels target = some tgt ∧
      RV64.run rom k st = .cont st' ∧
      st'.pc = (if evalBranch op (st.getReg rs1) (st.getReg rs2)
                then BitVec.ofNat 64 (4 * tgt)
                else BitVec.ofNat 64 (4 * (totalSizeWith AsmItem.wordSize pre + AsmItem.wordSize (.br op rs1 rs2 target)))) ∧
      RegEqExceptT6 st.regs st'.regs ∧
      st'.mem = st.mem := by
  rw [totalSizeWith_wordSize_eq] at h64 hpc ⊢
  obtain ⟨tgt, bimm, hlook, hdec, hpcAdd⟩ :=
    linkResolved_item_spec pre (.br op rs1 rs2 target) post code labels hlink
  let nextPc :=
    if evalBranch op (st.getReg rs1) (st.getReg rs2)
    then BitVec.ofNat 64 (4 * tgt)
    else BitVec.ofNat 64 (4 * (totalWords pre + 1))
  have hs : RV64.step rom st = .cont { st with pc := nextPc } := by
    rw [step_at_decoded_rom (by simp [AsmItem.wordSize] at h64; omega) (rom_decode_of_matches hrom hdec) st hpc]
    simp only [execInstr, nextPc]
    split
    · rw [hpc, hpcAdd]
    · rw [near_pc_add_4 st.pc hpc]
  refine ⟨tgt, 1, { st with pc := nextPc }, (by omega), hlook, ?_, ?_, RegEqExceptT6.refl _, rfl⟩
  · simp [RV64.run, hs]
  · simp [AsmItem.wordSize, nextPc]

private theorem near_step_brLong_aux {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    {pre post : List AsmItem} {op : BranchOp} {rs1 rs2 : Reg} {target : String} {st : State}
    (hrom : RomMatches rom code)
    (hlink : linkResolved (pre ++ [.brLong op rs1 rs2 target] ++ post) = .ok (code, labels))
    (h64 : 4 * (totalSizeWith AsmItem.wordSize pre + AsmItem.wordSize (.brLong op rs1 rs2 target)) < 2 ^ 64)
    (hpc : st.pc = BitVec.ofNat 64 (4 * totalSizeWith AsmItem.wordSize pre)) :
    ∃ tgt k st', 1 ≤ k ∧
      lookupLabel labels target = some tgt ∧
      RV64.run rom k st = .cont st' ∧
      st'.pc = (if evalBranch op (st.getReg rs1) (st.getReg rs2)
                then BitVec.ofNat 64 (4 * tgt)
                else BitVec.ofNat 64 (4 * (totalSizeWith AsmItem.wordSize pre + AsmItem.wordSize (.brLong op rs1 rs2 target)))) ∧
      RegEqExceptT6 st.regs st'.regs ∧
      st'.mem = st.mem := by
  rw [totalSizeWith_wordSize_eq] at h64 hpc ⊢
  obtain ⟨tgt, bimm, jimm, hlook, hdec0, hpcB, hdec1, hpcJ⟩ :=
    linkResolved_item_spec pre (.brLong op rs1 rs2 target) post code labels hlink
  simp only [AsmItem.wordSize] at h64 ⊢
  have hcond_inv : evalBranch (invertBranch op) (st.getReg rs1) (st.getReg rs2) =
      !evalBranch op (st.getReg rs1) (st.getReg rs2) :=
    evalBranch_invert op (st.getReg rs1) (st.getReg rs2)
  cases hcond : evalBranch op (st.getReg rs1) (st.getReg rs2) with
  | false =>
    have hinv : evalBranch (invertBranch op) (st.getReg rs1) (st.getReg rs2) = true := by
      rw [hcond_inv, hcond]; rfl
    let st1 : State := { st with pc := BitVec.ofNat 64 (4 * (totalWords pre + 2)) }
    have hs0 : RV64.step rom st = .cont st1 := by
      rw [step_at_decoded_rom (by omega) (rom_decode_of_matches hrom hdec0) st hpc]
      simp only [execInstr, hinv, ↓reduceIte, st1]
      rw [hpc, hpcB]
    refine ⟨tgt, 1, st1, (by omega), hlook, ?_, ?_, RegEqExceptT6.refl _, rfl⟩
    · simp [RV64.run, hs0]
    · simp [st1]
  | true =>
    have hinv : evalBranch (invertBranch op) (st.getReg rs1) (st.getReg rs2) = false := by
      rw [hcond_inv, hcond]; rfl
    let st1 : State := { st with pc := BitVec.ofNat 64 (4 * (totalWords pre + 1)) }
    have hs0 : RV64.step rom st = .cont st1 := by
      rw [step_at_decoded_rom (by omega) (rom_decode_of_matches hrom hdec0) st hpc]
      simp only [execInstr, hinv, Bool.false_eq_true, ↓reduceIte, st1]
      rw [near_pc_add_4 st.pc hpc]
    let st2 : State := { st1 with pc := BitVec.ofNat 64 (4 * tgt) }
    have hs1 : RV64.step rom st1 = .cont st2 := by
      rw [step_at_decoded_rom (by omega) (rom_decode_of_matches hrom hdec1) st1 rfl]
      simp only [execInstr, State.setReg, AbiReg.zero, beq_self_eq_true, ↓reduceIte, st2]
      rw [show st1.pc = BitVec.ofNat 64 (4 * (totalWords pre + 1)) from rfl, hpcJ]
    refine ⟨tgt, 2, st2, by omega, hlook, ?_, ?_, RegEqExceptT6.refl _, rfl⟩
    · simp [RV64.run, hs0, hs1]
    · simp [st2]

/-- Canonical near (`±1 MiB` / `±4 KiB`) `LinkModel` backed by `ConAgua.RISCV.Compiler.linkResolved`. -/
def nearLinkModel : LinkModel where
  itemSize := AsmItem.wordSize
  itemSize_label _ := rfl
  itemSize_instr _ := rfl
  linkSpec := linkResolved
  linkSpec_size hlink := by
    rw [totalSizeWith_wordSize_eq]
    exact linkResolved_size hlink
  word_decoded {items code labels} hlink k hk := by
    simp only [linkResolved, bind, Except.bind] at hlink
    cases hcol : collectLabels items with
    | error e => rw [hcol] at hlink; cases hlink
    | ok lm =>
      rw [hcol] at hlink; dsimp only at hlink
      cases hres : resolveItems lm items with
      | error e => rw [hres] at hlink; cases hlink
      | ok instrs =>
        rw [hres] at hlink
        simp only [Except.pure, pure, Except.ok.injEq, Prod.mk.injEq] at hlink
        rcases hlink with ⟨rfl, rfl⟩
        have hlt : k < instrs.size := by simpa [Array.size_map] using hk
        refine ⟨instrs[k], ?_⟩
        simp only [Array.getElem?_eq_getElem hk, Option.bind_some, Array.getElem_map]
        exact decode_encode instrs[k]
  lookup_label_at {code labels pre name post} hlink := by
    rw [totalSizeWith_wordSize_eq]
    simp only [linkResolved, bind, Except.bind] at hlink
    cases hcol : collectLabels (pre ++ [.label name] ++ post) with
    | error e => rw [hcol] at hlink; cases hlink
    | ok lm =>
      rw [hcol] at hlink; dsimp only at hlink
      cases hres : resolveItems lm (pre ++ [.label name] ++ post) with
      | error e => rw [hres] at hlink; cases hlink
      | ok instrs =>
        rw [hres] at hlink
        simp only [Except.pure, pure, Except.ok.injEq, Prod.mk.injEq] at hlink
        rcases hlink with ⟨_, rfl⟩
        exact collectLabels_label_at pre post name lm hcol
  step_instr hrom hlink h64 hpc := near_step_instr_aux hrom hlink h64 hpc
  step_j hrom hlink h64 hpc := near_step_j_aux hrom hlink h64 hpc
  step_call hrom hlink h64 hpc := near_step_call_aux hrom hlink h64 hpc
  step_br hrom hlink _ h64 hpc := near_step_br_aux hrom hlink h64 hpc
  step_brLong hrom hlink _ h64 hpc := near_step_brLong_aux hrom hlink h64 hpc

theorem near_totalSize_eq (asm : List AsmItem) :
    nearLinkModel.totalSize asm = totalWords asm :=
  totalSizeWith_wordSize_eq asm

/-! ## 5. Far Linker Instance (`farLinkModel`) -/

private theorem totalSizeWith_farWordSize_eq (asm : List AsmItem) :
    totalSizeWith farWordSize asm = farTotalWords asm := by
  have foldl_add : ∀ (xs : List AsmItem) (n : Nat),
      xs.foldl (fun acc item => acc + farWordSize item) n = n + (xs.map farWordSize).sum := by
    intro xs n
    induction xs generalizing n with
    | nil => simp
    | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih (n + farWordSize x), Nat.add_assoc]
  unfold farTotalWords totalSizeWith
  rw [foldl_add asm 0, Nat.zero_add]

private theorem far_step_instr_aux {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    {pre post : List AsmItem} {inst : Instr} {st : State}
    (hrom : RomMatches rom code)
    (hlink : linkFarSpec (pre ++ [.instr inst] ++ post) = .ok (code, labels))
    (h64 : 4 * totalSizeWith farWordSize pre < 2 ^ 64)
    (hpc : st.pc = BitVec.ofNat 64 (4 * totalSizeWith farWordSize pre)) :
    RV64.step rom st = execInstr st inst := by
  rw [totalSizeWith_farWordSize_eq] at h64 hpc
  have hdec := linkFarSpec_item_spec pre (.instr inst) post code labels hlink
  dsimp only [FarItemDecodedAt] at hdec
  exact step_at_decoded_rom h64 (rom_decode_of_matches hrom hdec) st hpc

private theorem far_step_j_aux {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    {pre post : List AsmItem} {target : String} {st : State}
    (hrom : RomMatches rom code)
    (hlink : linkFarSpec (pre ++ [.j target] ++ post) = .ok (code, labels))
    (h64 : 4 * (totalSizeWith farWordSize pre + farWordSize (.j target)) < 2 ^ 64)
    (hpc : st.pc = BitVec.ofNat 64 (4 * totalSizeWith farWordSize pre)) :
    ∃ tgt k st', 1 ≤ k ∧
      lookupLabel labels target = some tgt ∧
      RV64.run rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * tgt) ∧
      RegEqExceptT6 st.regs st'.regs ∧
      st'.mem = st.mem := by
  rw [totalSizeWith_farWordSize_eq] at h64 hpc
  obtain ⟨tgt, hlook, hrange, hd0, hd1, hd2, hd3⟩ :=
    linkFarSpec_item_spec pre (.j target) post code labels hlink
  simp only [farWordSize] at h64
  obtain ⟨_, _, _, st', _, _, _, _, hrun, hpc', _, hget, hmem⟩ :=
    step_far_jalr (rom := rom) (st := st) (pc := farTotalWords pre) (tgt := tgt)
      (rd := AbiReg.zero) (by decide) (by decide) (by omega) hpc hrange
      (rom_decode_of_matches hrom hd0) (rom_decode_of_matches hrom hd1)
      (rom_decode_of_matches hrom hd2) (rom_decode_of_matches hrom hd3)
  have hzero : st'.regs 0#5 = st.regs 0#5 := run_regs_zero hrun
  have hregEq : RegEqExceptT6 st.regs st'.regs := by
    refine RegEqExceptT6.of_getReg_zero_eq hzero.symm ?_
    intro r hr
    by_cases hr0 : r = AbiReg.zero
    · subst hr0; simp [State.getReg, AbiReg.zero]
    · exact (hget r hr0 hr.1 hr.2).symm
  exact ⟨tgt, 4, st', by omega, hlook, hrun, hpc', hregEq, hmem⟩

private theorem far_step_call_aux {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    {pre post : List AsmItem} {target : String} {st : State}
    (hrom : RomMatches rom code)
    (hlink : linkFarSpec (pre ++ [.call target] ++ post) = .ok (code, labels))
    (h64 : 4 * (totalSizeWith farWordSize pre + farWordSize (.call target)) < 2 ^ 64)
    (hpc : st.pc = BitVec.ofNat 64 (4 * totalSizeWith farWordSize pre)) :
    ∃ tgt k st', 1 ≤ k ∧
      lookupLabel labels target = some tgt ∧
      RV64.run rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * tgt) ∧
      RegEqExceptT6
        (st.setReg AbiReg.ra
          (BitVec.ofNat 64 (4 * (totalSizeWith farWordSize pre + farWordSize (.call target))))).regs
        st'.regs ∧
      st'.mem = st.mem := by
  rw [totalSizeWith_farWordSize_eq] at h64 hpc ⊢
  obtain ⟨tgt, hlook, hrange, hd0, hd1, hd2, hd3⟩ :=
    linkFarSpec_item_spec pre (.call target) post code labels hlink
  simp only [farWordSize] at h64 ⊢
  obtain ⟨_, _, _, st', _, _, _, _, hrun, hpc', hra, hget, hmem⟩ :=
    step_far_jalr (rom := rom) (st := st) (pc := farTotalWords pre) (tgt := tgt)
      (rd := AbiReg.ra) (by decide) (by decide) (by omega) hpc hrange
      (rom_decode_of_matches hrom hd0) (rom_decode_of_matches hrom hd1)
      (rom_decode_of_matches hrom hd2) (rom_decode_of_matches hrom hd3)
  have hzero : st'.regs 0#5 = st.regs 0#5 := run_regs_zero hrun
  let stRa := st.setReg AbiReg.ra (BitVec.ofNat 64 (4 * (farTotalWords pre + 4)))
  have hzeroRa : stRa.regs 0#5 = st'.regs 0#5 := by
    rw [setReg_regs_zero, hzero]
  have hregEq : RegEqExceptT6 stRa.regs st'.regs := by
    refine RegEqExceptT6.of_getReg_zero_eq hzeroRa ?_
    intro r hr
    by_cases hraEq : r = AbiReg.ra
    · subst hraEq
      rw [getReg_setReg_self st AbiReg.ra (by decide), hra (by decide)]
    · rw [getReg_setReg_other st AbiReg.ra r hraEq]
      exact (hget r hraEq hr.1 hr.2).symm
  exact ⟨tgt, 4, st', by omega, hlook, hrun, hpc', hregEq, hmem⟩

private theorem far_step_branch_core {rom : Rom} {code : Array (BitVec 32)}
    {pc tgt : Nat} {op : BranchOp} {rs1 rs2 : Reg} {st : State}
    (hrom : RomMatches rom code)
    (hrange : farInRange ((tgt : Int) - ((pc + 2 : Nat) : Int)) = true)
    (hd0 : (code[pc]?).bind decode = some (.branch (invertBranch op) rs1 rs2 (mkBimm 5)))
    (hd1 : (code[pc + 1]?).bind decode = some (.jal AbiReg.t6 (mkJimm 1)))
    (hd2 : (code[pc + 2]?).bind decode = some (.lui AbiReg.s1 (splitFarOffWords ((tgt : Int) - ((pc + 2 : Nat) : Int))).1))
    (hd3 : (code[pc + 3]?).bind decode = some (.alu .add AbiReg.t6 AbiReg.t6 AbiReg.s1))
    (hd4 : (code[pc + 4]?).bind decode = some (.jalr AbiReg.zero AbiReg.t6 (splitFarOffWords ((tgt : Int) - ((pc + 2 : Nat) : Int))).2))
    (h64 : 4 * (pc + 5) < 2 ^ 64)
    (hpc : st.pc = BitVec.ofNat 64 (4 * pc)) :
    ∃ k st', 1 ≤ k ∧
      RV64.run rom k st = .cont st' ∧
      st'.pc = (if evalBranch op (st.getReg rs1) (st.getReg rs2)
                then BitVec.ofNat 64 (4 * tgt)
                else BitVec.ofNat 64 (4 * (pc + 5))) ∧
      RegEqExceptT6 st.regs st'.regs ∧
      st'.mem = st.mem := by
  cases hcond : evalBranch op (st.getReg rs1) (st.getReg rs2) with
  | false =>
    obtain ⟨st1, _, hrun, hpc1, hregs1, hmem1⟩ :=
      step_far_branch_not_taken (rom := rom) (st := st) (pc := pc) (op := op) (rs1 := rs1) (rs2 := rs2)
        h64 hpc hcond (rom_decode_of_matches hrom hd0)
    refine ⟨1, st1, (by omega), hrun, ?_, RegEqExceptT6.of_eq hregs1.symm, hmem1⟩
    simp [hpc1]
  | true =>
    obtain ⟨st5, hrun, hpc5, hget, hmem5⟩ :=
      step_far_branch_taken (rom := rom) (st := st) (pc := pc) (tgt := tgt)
        (op := op) (rs1 := rs1) (rs2 := rs2) (by omega) hpc hrange hcond
        (rom_decode_of_matches hrom hd0) (rom_decode_of_matches hrom hd1)
        (rom_decode_of_matches hrom hd2) (rom_decode_of_matches hrom hd3)
        (rom_decode_of_matches hrom hd4)
    have hzero : st5.regs 0#5 = st.regs 0#5 := run_regs_zero hrun
    have hregEq : RegEqExceptT6 st.regs st5.regs := by
      refine RegEqExceptT6.of_getReg_zero_eq hzero.symm ?_
      intro r hr
      by_cases hr0 : r = 0#5
      · subst hr0; simp [State.getReg]
      · exact (hget r hr.1 hr.2).symm
    refine ⟨5, st5, by omega, hrun, ?_, hregEq, hmem5⟩
    simp [hpc5]

/-- Unconditional `.br` execution under `linkFarSpec` (valid even without `rs1 ≠ t6` because the
    branch instruction reads `rs1, rs2` before `jal t6` runs). -/
theorem far_step_br_any {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    {pre post : List AsmItem} {op : BranchOp} {rs1 rs2 : Reg} {target : String} {st : State}
    (hrom : RomMatches rom code)
    (hlink : linkFarSpec (pre ++ [.br op rs1 rs2 target] ++ post) = .ok (code, labels))
    (h64 : 4 * (farTotalWords pre + 5) < 2 ^ 64)
    (hpc : st.pc = BitVec.ofNat 64 (4 * farTotalWords pre)) :
    ∃ tgt k st', 1 ≤ k ∧
      lookupLabel labels target = some tgt ∧
      RV64.run rom k st = .cont st' ∧
      st'.pc = (if evalBranch op (st.getReg rs1) (st.getReg rs2)
                then BitVec.ofNat 64 (4 * tgt)
                else BitVec.ofNat 64 (4 * (farTotalWords pre + 5))) ∧
      RegEqExceptT6 st.regs st'.regs ∧
      st'.mem = st.mem := by
  obtain ⟨tgt, hlook, hrange, hd0, hd1, hd2, hd3, hd4⟩ :=
    linkFarSpec_item_spec pre (.br op rs1 rs2 target) post code labels hlink
  obtain ⟨k, st', hk, hrun, hpc', hregEq, hmem⟩ :=
    far_step_branch_core hrom hrange hd0 hd1 hd2 hd3 hd4 h64 hpc
  exact ⟨tgt, k, st', hk, hlook, hrun, hpc', hregEq, hmem⟩

/-- Unconditional `.brLong` execution under `linkFarSpec`. -/
theorem far_step_brLong_any {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    {pre post : List AsmItem} {op : BranchOp} {rs1 rs2 : Reg} {target : String} {st : State}
    (hrom : RomMatches rom code)
    (hlink : linkFarSpec (pre ++ [.brLong op rs1 rs2 target] ++ post) = .ok (code, labels))
    (h64 : 4 * (farTotalWords pre + 5) < 2 ^ 64)
    (hpc : st.pc = BitVec.ofNat 64 (4 * farTotalWords pre)) :
    ∃ tgt k st', 1 ≤ k ∧
      lookupLabel labels target = some tgt ∧
      RV64.run rom k st = .cont st' ∧
      st'.pc = (if evalBranch op (st.getReg rs1) (st.getReg rs2)
                then BitVec.ofNat 64 (4 * tgt)
                else BitVec.ofNat 64 (4 * (farTotalWords pre + 5))) ∧
      RegEqExceptT6 st.regs st'.regs ∧
      st'.mem = st.mem := by
  obtain ⟨tgt, hlook, hrange, hd0, hd1, hd2, hd3, hd4⟩ :=
    linkFarSpec_item_spec pre (.brLong op rs1 rs2 target) post code labels hlink
  obtain ⟨k, st', hk, hrun, hpc', hregEq, hmem⟩ :=
    far_step_branch_core hrom hrange hd0 hd1 hd2 hd3 hd4 h64 hpc
  exact ⟨tgt, k, st', hk, hlook, hrun, hpc', hregEq, hmem⟩

theorem pushEncoded_word_decoded (acc : Array (BitVec 32)) (is : List Instr)
    (hacc : ∀ k, k < acc.size → ∃ inst : Instr, (acc[k]?).bind decode = some inst) :
    ∀ k, k < (pushEncoded acc is).size → ∃ inst : Instr, ((pushEncoded acc is)[k]?).bind decode = some inst := by
  induction is generalizing acc with
  | nil => exact hacc
  | cons i rest ih =>
    apply ih (acc.push (encode i))
    intro k hk
    rw [Array.size_push] at hk
    by_cases hlt : k < acc.size
    · rw [Array.getElem?_push_lt hlt]
      simpa [Array.getElem?_eq_getElem hlt] using hacc k hlt
    · have heq : k = acc.size := by omega
      subst heq
      rw [Array.getElem?_push_size]
      exact ⟨i, decode_encode i⟩

private theorem resolveFarWordsGo_word_decoded (lm : LabelMap) (pc : Nat) (items : List AsmItem)
    (acc : Array (BitVec 32)) (ws : Array (BitVec 32))
    (hacc : ∀ k, k < acc.size → ∃ inst : Instr, (acc[k]?).bind decode = some inst)
    (hres : resolveFarWordsGo lm pc items acc = .ok ws) :
    ∀ k, k < ws.size → ∃ inst : Instr, (ws[k]?).bind decode = some inst := by
  induction items generalizing pc acc with
  | nil =>
    simp only [resolveFarWordsGo, Except.ok.injEq] at hres
    subst hres; exact hacc
  | cons item rest ih =>
    simp only [resolveFarWordsGo] at hres
    cases hi : resolveFarItem lm pc item with
    | error e => rw [hi] at hres; cases hres
    | ok is =>
      rw [hi] at hres
      exact ih (pc + farWordSize item) (pushEncoded acc is) (pushEncoded_word_decoded acc is hacc) hres

/-- Canonical far (`±2 GiB`) `LinkModel` backed by `ConAgua.RISCV.Linker.linkFarSpec` / `linkFar`. -/
def farLinkModel : LinkModel where
  itemSize := farWordSize
  itemSize_label _ := rfl
  itemSize_instr _ := rfl
  linkSpec := linkFarSpec
  linkSpec_size hlink := by
    rw [totalSizeWith_farWordSize_eq]
    exact linkFarSpec_size hlink
  word_decoded {items code labels} hlink k hk := by
    simp only [linkFarSpec, bind, Except.bind] at hlink
    cases hcol : collectFarLabels items with
    | error e => rw [hcol] at hlink; cases hlink
    | ok lm =>
      rw [hcol] at hlink; dsimp only at hlink
      cases hres : resolveFarWordsGo lm 0 items #[] with
      | error e => rw [hres] at hlink; cases hlink
      | ok ws =>
        rw [hres] at hlink
        simp only [Except.pure, pure, Except.ok.injEq, Prod.mk.injEq] at hlink
        rcases hlink with ⟨rfl, rfl⟩
        exact resolveFarWordsGo_word_decoded lm 0 items #[] ws (fun _ h => by simp at h) hres k hk
  lookup_label_at {code labels pre name post} hlink := by
    rw [totalSizeWith_farWordSize_eq]
    simp only [linkFarSpec, bind, Except.bind] at hlink
    cases hcol : collectFarLabels (pre ++ [.label name] ++ post) with
    | error e => rw [hcol] at hlink; cases hlink
    | ok lm =>
      rw [hcol] at hlink; dsimp only at hlink
      cases hres : resolveFarWordsGo lm 0 (pre ++ [.label name] ++ post) #[] with
      | error e => rw [hres] at hlink; cases hlink
      | ok ws =>
        rw [hres] at hlink
        simp only [Except.pure, pure, Except.ok.injEq, Prod.mk.injEq] at hlink
        rcases hlink with ⟨_, rfl⟩
        exact collectFarLabels_label_at pre post name lm hcol
  step_instr hrom hlink h64 hpc := far_step_instr_aux hrom hlink h64 hpc
  step_j hrom hlink h64 hpc := far_step_j_aux hrom hlink h64 hpc
  step_call hrom hlink h64 hpc := far_step_call_aux hrom hlink h64 hpc
  step_br hrom hlink _ h64 hpc := by
    rw [totalSizeWith_farWordSize_eq] at h64 hpc ⊢
    simpa [farWordSize] using far_step_br_any hrom hlink h64 hpc
  step_brLong hrom hlink _ h64 hpc := by
    rw [totalSizeWith_farWordSize_eq] at h64 hpc ⊢
    simpa [farWordSize] using far_step_brLong_any hrom hlink h64 hpc

theorem far_totalSize_eq (asm : List AsmItem) :
    farLinkModel.totalSize asm = farTotalWords asm :=
  totalSizeWith_farWordSize_eq asm

/-- Bridge from fast O(N) `FarLink.linkFar` output to `farLinkModel.linkSpec`. -/
theorem linkFar_ok_linkSpec {items : List AsmItem} {code : Array (BitVec 32)}
    (hlink : linkFar items = .ok code) :
    ∃ labels, farLinkModel.linkSpec items = .ok (code, labels) :=
  linkFar_ok_spec hlink

/-! ## 5b. Generic Slice-Retargeting `LinkModel` for Cold-Exit Branch Stubs -/

/-- Rewrite conditional branch target `tgt` to an in-range per-function cold trampoline label. -/
def retargetColdTarget (old1 new1 old2 : String) (new2? : Option String) (t : String) : String :=
  if t == old1 then new1
  else match new2? with
    | some new2 => if t == old2 then new2 else t
    | none => t

/-- Rewrite `.br`/`.brLong` targeting `old1`/`old2` inside an `AsmItem` (leaving `.label`/`.instr`/`.j`/`.call` untouched). -/
def retargetColdItem (old1 new1 old2 : String) (new2? : Option String) : AsmItem → AsmItem
  | .br op r1 r2 t => .br op r1 r2 (retargetColdTarget old1 new1 old2 new2? t)
  | .brLong op r1 r2 t => .brLong op r1 r2 (retargetColdTarget old1 new1 old2 new2? t)
  | it => it

private theorem totalSizeWith_map_retarget (base : LinkModel)
    (old1 new1 old2 : String) (new2? : Option String) (xs : List AsmItem) :
    totalSizeWith (fun it => base.itemSize (retargetColdItem old1 new1 old2 new2? it)) xs =
      base.totalSize (xs.map (retargetColdItem old1 new1 old2 new2?)) := by
  simp only [LinkModel.totalSize, totalSizeWith, List.map_map]
  rfl

private theorem all_instrs_totalSize (sz : AsmItem → Nat) (hsz : ∀ i, sz (.instr i) = 1)
    (xs : List Instr) : totalSizeWith sz (xs.map .instr) = xs.length := by
  induction xs with
  | nil => rfl
  | cons i rest ih =>
    simp only [totalSizeWith, List.map_cons, List.sum_cons, hsz, List.length_cons] at ih ⊢
    omega

/-- Split `a ++ [x] ++ b = p ++ m ++ q` cleanly into which of `p`, `m`, `q` contains `x`. -/
private theorem split_append3_elem {α : Type} [Inhabited α] {a b p m q : List α} {x : α}
    (h : a ++ [x] ++ b = p ++ m ++ q) :
    (∃ k : Nat, a = p.take k ∧ k < p.length ∧ x = p[k]! ∧ b = p.drop (k + 1) ++ m ++ q) ∨
    (∃ a' b', a = p ++ a' ∧ b = b' ++ q ∧ a' ++ [x] ++ b' = m) ∨
    (∃ k : Nat, a = p ++ m ++ q.take k ∧ k < q.length ∧ x = q[k]! ∧ b = q.drop (k + 1)) := by
  have split2 : ∀ {u v l r : List α}, u ++ [x] ++ v = l ++ r →
      (∃ k, u = l.take k ∧ k < l.length ∧ x = l[k]! ∧ v = l.drop (k + 1) ++ r) ∨
      (∃ u', u = l ++ u' ∧ u' ++ [x] ++ v = r) := by
    intro u v l r he
    induction u generalizing l with
    | nil =>
      cases l with
      | nil => right; exact ⟨[], rfl, by simpa using he⟩
      | cons y l' =>
        simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
        left; exact ⟨0, rfl, by simp, he.1, by simpa using he.2⟩
    | cons y u' ih =>
      cases l with
      | nil => right; exact ⟨y :: u', rfl, by simpa using he⟩
      | cons z l' =>
        simp only [List.cons_append, List.cons.injEq] at he
        rcases he with ⟨rfl, htail⟩
        rcases ih htail with ⟨k, hu, hk, hx, hv⟩ | ⟨w, hu, hw⟩
        · left; exact ⟨k + 1, by simp [hu], by simp; omega, by simpa using hx, by simpa using hv⟩
        · right; exact ⟨w, by simp [hu], hw⟩
  rcases split2 (by simpa [List.append_assoc] using h : a ++ [x] ++ b = p ++ (m ++ q)) with
      ⟨k, ha, hk, hx, hb⟩ | ⟨u', rfl, hu⟩
  · left; exact ⟨k, ha, hk, hx, by simpa [List.append_assoc] using hb⟩
  · rcases split2 hu with ⟨k, hu', hk, hx, hb⟩ | ⟨v', rfl, hv⟩
    · right; left
      have hmt := (List.take_append_drop k m).symm
      have hmd : m.drop k = m[k]! :: m.drop (k + 1) := by
        have hg : m[k]? = some m[k]! := by rw [List.getElem?_eq_getElem hk]; simp [hk]
        exact List.drop_eq_getElem_cons hk |>.trans (by simp [hk])
      refine ⟨m.take k, m.drop (k + 1), by simp [hu'], by simpa using hb, ?_⟩
      simpa [List.append_assoc, hx, hmd] using hmt.symm
    · right; right
      rcases split2 (show v' ++ [x] ++ b = q ++ [] by simpa using hv) with ⟨k, hv', hk, hx, hb⟩ | ⟨w, _, hw⟩
      · exact ⟨k, by simp [hv', List.append_assoc], hk, hx, by simpa using hb⟩
      · simp at hw

/-- Build a slice-local `LinkModel` viewing `bodyRaw` inside `base.linkSpec (preRaw ++ bodyRaw.map r ++ postRaw)`
    as if its cold conditional branches still jumped directly to `old1` (`errLabel`) / `old2` (`exhaustedLabel`),
    routing taken branches through the in-function 1-jump trampolines `new1` (`[lbl new1, j old1]`)
    and optionally `new2` (`[lbl new2, j old2]`). -/
noncomputable def retargetLinkModel (base : LinkModel)
    (code : Array (BitVec 32)) (labels : LabelMap)
    (old1 new1 old2 : String) (new2? : Option String)
    (preRaw bodyRaw postRaw : List AsmItem)
    (hlink : base.linkSpec (preRaw ++ bodyRaw.map (retargetColdItem old1 new1 old2 new2?) ++ postRaw) =
      .ok (code, labels))
    (hcode64 : 4 * code.size < 2 ^ 64)
    (hStub1 : ∃ p1 q1,
      base.linkSpec (p1 ++ [AsmItem.label new1, AsmItem.j old1] ++ q1) = .ok (code, labels))
    (hStub2 : match new2? with
      | some new2 => ∃ p2 q2,
        base.linkSpec (p2 ++ [AsmItem.label new2, AsmItem.j old2] ++ q2) = .ok (code, labels)
      | none => True) :
    LinkModel :=
  let r := retargetColdItem old1 new1 old2 new2?
  let hsz : code.size = base.totalSize preRaw + base.totalSize (bodyRaw.map r) + base.totalSize postRaw := by
    have hs := base.linkSpec_size hlink
    simpa [LinkModel.totalSize, totalSizeWith, List.map_append, List.sum_append, Nat.add_assoc] using hs
  let hdec : ∀ k, k < code.size → ∃ inst : Instr, (code[k]?).bind decode = some inst :=
    base.word_decoded hlink
  let preInstrs : List Instr := List.ofFn fun (i : Fin (base.totalSize preRaw)) =>
    Classical.choose (hdec i.val (by omega))
  let postOff := base.totalSize preRaw + base.totalSize (bodyRaw.map r)
  let postInstrs : List Instr := List.ofFn fun (i : Fin (base.totalSize postRaw)) =>
    Classical.choose (hdec (postOff + i.val) (by omega))
  let prePad := preInstrs.map AsmItem.instr
  let postPad := postInstrs.map AsmItem.instr
  let target := prePad ++ bodyRaw ++ postPad
  let sz : AsmItem → Nat := fun it => base.itemSize (r it)
  have hsz_lbl : ∀ s, sz (.label s) = 0 := fun s => base.itemSize_label s
  have hsz_inst : ∀ i, sz (.instr i) = 1 := fun i => base.itemSize_instr i
  have hpreLen : prePad.length = base.totalSize preRaw := by simp [prePad, preInstrs]
  have hpostLen : postPad.length = base.totalSize postRaw := by simp [postPad, postInstrs]
  have hpreSz : totalSizeWith sz prePad = base.totalSize preRaw := by
    rw [all_instrs_totalSize sz hsz_inst preInstrs]; simp [preInstrs]
  have hpostSz : totalSizeWith sz postPad = base.totalSize postRaw := by
    rw [all_instrs_totalSize sz hsz_inst postInstrs]; simp [postInstrs]
  have hszBody : totalSizeWith sz bodyRaw = base.totalSize (bodyRaw.map r) :=
    totalSizeWith_map_retarget base old1 new1 old2 new2? bodyRaw
  have hstepStub : ∀ {rom : Rom} (hrom : RomMatches rom code) (lblName tgtName : String)
      (p q : List AsmItem)
      (hl : base.linkSpec (p ++ [AsmItem.label lblName, AsmItem.j tgtName] ++ q) = .ok (code, labels))
      (pcStub : Nat) (hlkp : lookupLabel labels lblName = some pcStub)
      (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * pcStub)),
      ∃ tgt k st', 1 ≤ k ∧ lookupLabel labels tgtName = some tgt ∧
        RV64.run rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * tgt) ∧
        RegEqExceptT6 st.regs st'.regs ∧
        st'.mem = st.mem := by
    intro rom hrom lblName tgtName p q hl pcStub hlkp st hpc
    have hlbl : base.linkSpec (p ++ [.label lblName] ++ ([.j tgtName] ++ q)) = .ok (code, labels) := by
      simpa [List.append_assoc] using hl
    have hlkp' := base.lookup_label_at hlbl
    rw [hlkp] at hlkp'; injection hlkp' with hpcEq; subst hpcEq
    have hj : base.linkSpec ((p ++ [.label lblName]) ++ [.j tgtName] ++ q) = .ok (code, labels) := by
      simpa [List.append_assoc] using hl
    have hts : totalSizeWith base.itemSize (p ++ [.label lblName]) = totalSizeWith base.itemSize p := by
      simp [totalSizeWith, List.map_append, base.itemSize_label]
    have hszj := base.linkSpec_size hj
    have hlt64 : 4 * (totalSizeWith base.itemSize (p ++ [.label lblName]) + base.itemSize (.j tgtName)) < 2 ^ 64 := by
      simp only [totalSizeWith, List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil,
        List.append_assoc] at hszj ⊢
      omega
    exact base.step_j hrom hj hlt64 (by simpa [hts] using hpc)
  have hstubTgt : ∀ (lblName tgtName : String) (p q : List AsmItem)
      (hl : base.linkSpec (p ++ [AsmItem.label lblName, AsmItem.j tgtName] ++ q) = .ok (code, labels)),
      ∃ tgt, lookupLabel labels tgtName = some tgt := by
    intro lblName tgtName p q hl
    have hj : base.linkSpec ((p ++ [.label lblName]) ++ [.j tgtName] ++ q) = .ok (code, labels) := by
      simpa [List.append_assoc] using hl
    have hszj := base.linkSpec_size hj
    have hlt64 : 4 * (totalSizeWith base.itemSize (p ++ [.label lblName]) + base.itemSize (.j tgtName)) < 2 ^ 64 := by
      simp only [totalSizeWith, List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil,
        List.append_assoc] at hszj ⊢
      omega
    let stDummy : State :=
      { pc := BitVec.ofNat 64 (4 * totalSizeWith base.itemSize (p ++ [.label lblName]))
        regs := fun _ => 0#64
        mem := fun _ => 0#8 }
    obtain ⟨tgt, _, _, _, hlook, _⟩ := base.step_j (romOfArray_matches code) hj hlt64 rfl (st := stDummy)
    exact ⟨tgt, hlook⟩
  have hpreElem : ∀ k (hk : k < prePad.length),
      prePad[k]! = AsmItem.instr (Classical.choose (hdec k (by rw [hpreLen] at hk; omega))) := by
    intro k hk
    rw [getElem!_pos (c := prePad) (i := k) (h := hk)]
    simp [prePad, preInstrs]
  have hrun_add : ∀ {rom : Rom} {n m : Nat} {s s1 : State},
      RV64.run rom n s = .cont s1 → RV64.run rom (n + m) s = RV64.run rom m s1 := by
    intro rom n m s s1 hn
    induction n generalizing s with
    | zero =>
      simp only [RV64.run, StepResult.cont.injEq] at hn
      subst hn; simp
    | succ n ih =>
      rw [Nat.succ_add]
      simp only [RV64.run] at hn ⊢
      cases hs : RV64.step rom s with
      | cont s' => rw [hs] at hn; exact ih hn
      | trap => rw [hs] at hn; cases hn
  have hpostElem : ∀ k (hk : k < postPad.length),
      postPad[k]! = AsmItem.instr (Classical.choose (hdec (postOff + k) (by rw [hpostLen] at hk; omega))) := by
    intro k hk
    have hk' : k < postInstrs.length := by simpa [postPad] using hk
    have hk'' : k < base.totalSize postRaw := by simpa [postInstrs] using hk'
    rw [getElem!_pos (c := postPad) (i := k) (h := hk)]
    simp [postPad, postInstrs]
  have hmap_split : ∀ {a' b' : List AsmItem} {it : AsmItem}, a' ++ [it] ++ b' = bodyRaw →
      base.linkSpec ((preRaw ++ a'.map r) ++ [r it] ++ (b'.map r ++ postRaw)) = .ok (code, labels) := by
    intro a' b' it hmid
    have hmap : bodyRaw.map r = a'.map r ++ [r it] ++ b'.map r := by
      rw [← hmid, List.map_append, List.map_append, List.map_singleton]
    have hassoc : (preRaw ++ a'.map r) ++ [r it] ++ (b'.map r ++ postRaw) =
        preRaw ++ bodyRaw.map r ++ postRaw := by
      rw [hmap]; simp only [List.append_assoc]
    rw [hassoc]; exact hlink
  have hha : ∀ (a' : List AsmItem),
      totalSizeWith sz (prePad ++ a') = totalSizeWith base.itemSize (preRaw ++ a'.map r) := by
    intro a'
    simp only [totalSizeWith, List.map_append, List.sum_append]
    have h1 : (prePad.map sz).sum = (preRaw.map base.itemSize).sum := hpreSz
    have h2 : (a'.map sz).sum = ((a'.map r).map base.itemSize).sum :=
      totalSizeWith_map_retarget base old1 new1 old2 new2? a'
    omega
  { itemSize := sz
    itemSize_label := hsz_lbl
    itemSize_instr := hsz_inst
    linkSpec := fun xs =>
      @dite _ (xs = target) (Classical.propDecidable _)
        (fun _ => .ok (code, labels)) (fun _ => .error "retargetLinkModel: slice mismatch")
    linkSpec_size := by
      intro items c l h
      split at h
      · next heq =>
        cases h; rw [heq]
        simp only [target, totalSizeWith, List.map_append, List.sum_append]
        have h1 : (prePad.map sz).sum = base.totalSize preRaw := hpreSz
        have h2 : (bodyRaw.map sz).sum = base.totalSize (bodyRaw.map r) := hszBody
        have h3 : (postPad.map sz).sum = base.totalSize postRaw := hpostSz
        omega
      · cases h
    word_decoded := by
      intro items c l h k hk
      split at h
      · cases h; exact hdec k hk
      · cases h
    lookup_label_at := by
      intro c l pre name post h
      split at h
      · next heq =>
        cases h
        rcases split_append3_elem heq with ⟨k, _, hk, hxk, _⟩ | ⟨a', b', rfl, _, hmid⟩ | ⟨k, _, hk, hxk, _⟩
        · rw [hpreElem k hk] at hxk; cases hxk
        · rw [hha a']
          exact base.lookup_label_at (hmap_split hmid)
        · rw [hpostElem k hk] at hxk; cases hxk
      · cases h
    step_instr := by
      intro rom c l pre post inst st hrom h h64 hpc
      split at h
      · next heq =>
        cases h
        rcases split_append3_elem heq with ⟨k, hpre, hk, hxk, _⟩ | ⟨a', b', rfl, _, hmid⟩ | ⟨k, hpre, hk, hxk, _⟩
        · have hk'' : k < base.totalSize preRaw := by rwa [hpreLen] at hk
          have hpre_eq : pre = (preInstrs.take k).map AsmItem.instr := by
            rw [hpre]; simp [prePad, List.map_take]
          have htsz : totalSizeWith sz pre = k := by
            rw [hpre_eq, all_instrs_totalSize sz hsz_inst]; simp [preInstrs]; omega
          rw [hpreElem k hk] at hxk; injection hxk with hinst
          have hspec : (code[k]?).bind decode = some inst := by
            rw [hinst]; exact Classical.choose_spec (hdec k (by omega))
          rw [htsz] at h64 hpc
          exact step_at_decoded_rom h64 (rom_decode_of_matches hrom hspec) st hpc
        · rw [hha a'] at h64 hpc
          exact base.step_instr hrom (hmap_split hmid) h64 hpc
        · have hk'' : k < base.totalSize postRaw := by rwa [hpostLen] at hk
          have htsz : totalSizeWith sz pre = postOff + k := by
            rw [hpre]
            simp only [totalSizeWith, List.map_append, List.sum_append]
            have h1 : (prePad.map sz).sum = base.totalSize preRaw := hpreSz
            have h2 : (bodyRaw.map sz).sum = base.totalSize (bodyRaw.map r) := hszBody
            have h3 : ((postPad.take k).map sz).sum = k := by
              have : postPad.take k = (postInstrs.take k).map AsmItem.instr := by simp [postPad, List.map_take]
              rw [this, show ((postInstrs.take k).map AsmItem.instr |>.map sz).sum =
                totalSizeWith sz ((postInstrs.take k).map AsmItem.instr) from rfl,
                all_instrs_totalSize sz hsz_inst]
              simp [postInstrs]; omega
            simp only [postOff]; omega
          rw [hpostElem k hk] at hxk; injection hxk with hinst
          have hspec : (code[postOff + k]?).bind decode = some inst := by
            rw [hinst]; exact Classical.choose_spec (hdec (postOff + k) (by omega))
          rw [htsz] at h64 hpc
          exact step_at_decoded_rom h64 (rom_decode_of_matches hrom hspec) st hpc
      · cases h
    step_j := by
      intro rom c l pre post tgtName st hrom h h64 hpc
      split at h
      · next heq =>
        cases h
        rcases split_append3_elem heq with ⟨k, _, hk, hxk, _⟩ | ⟨a', b', rfl, _, hmid⟩ | ⟨k, _, hk, hxk, _⟩
        · rw [hpreElem k hk] at hxk; cases hxk
        · rw [hha a'] at h64 hpc
          exact base.step_j hrom (hmap_split hmid) h64 hpc
        · rw [hpostElem k hk] at hxk; cases hxk
      · cases h
    step_call := by
      intro rom c l pre post tgtName st hrom h h64 hpc
      split at h
      · next heq =>
        cases h
        rcases split_append3_elem heq with ⟨k, _, hk, hxk, _⟩ | ⟨a', b', rfl, _, hmid⟩ | ⟨k, _, hk, hxk, _⟩
        · rw [hpreElem k hk] at hxk; cases hxk
        · rw [hha a'] at h64 hpc ⊢
          exact base.step_call hrom (hmap_split hmid) h64 hpc
        · rw [hpostElem k hk] at hxk; cases hxk
      · cases h
    step_br := by
      intro rom c l pre post op rs1 rs2 tgtName st hrom h hreg h64 hpc
      split at h
      · next heq =>
        cases h
        rcases split_append3_elem heq with ⟨k, _, hk, hxk, _⟩ | ⟨a', b', rfl, _, hmid⟩ | ⟨k, _, hk, hxk, _⟩
        · rw [hpreElem k hk] at hxk; cases hxk
        · let tgt' := retargetColdTarget old1 new1 old2 new2? tgtName
          have hsz_eq : sz (.br op rs1 rs2 tgtName) = base.itemSize (.br op rs1 rs2 tgt') := rfl
          have hb : base.linkSpec ((preRaw ++ a'.map r) ++ [.br op rs1 rs2 tgt'] ++ (b'.map r ++ postRaw)) =
              .ok (code, labels) := hmap_split hmid
          rw [hha a'] at h64 hpc ⊢
          change 4 * (totalSizeWith base.itemSize (preRaw ++ a'.map r) + base.itemSize (.br op rs1 rs2 tgt')) < 2 ^ 64 at h64
          obtain ⟨pcStub, k1, st1, hk1, hlook1, hrun1, hpc1, hreg1, hmem1⟩ :=
            base.step_br hrom hb hreg h64 hpc
          by_cases h1 : tgtName = old1
          · subst h1
            have ht' : tgt' = new1 := by simp [tgt', retargetColdTarget]
            rw [ht'] at hlook1
            obtain ⟨p1, q1, hl1⟩ := hStub1
            cases hcond : evalBranch op (st.getReg rs1) (st.getReg rs2) with
            | false =>
              obtain ⟨tgt, hlookTgt⟩ := hstubTgt new1 tgtName p1 q1 hl1
              exact ⟨tgt, k1, st1, hk1, hlookTgt, hrun1, by simpa [hcond, hsz_eq] using hpc1, hreg1, hmem1⟩
            | true =>
              have hpc1' : st1.pc = BitVec.ofNat 64 (4 * pcStub) := by simpa [hcond] using hpc1
              obtain ⟨tgt, k2, st2, hk2, hlookTgt, hrun2, hpc2, hreg2, hmem2⟩ :=
                hstepStub hrom new1 tgtName p1 q1 hl1 pcStub hlook1 st1 hpc1'
              refine ⟨tgt, k1 + k2, st2, by omega, hlookTgt, ?_, by simpa [hcond] using hpc2,
                hreg1.trans hreg2, hmem2.trans hmem1⟩
              rw [hrun_add hrun1]; exact hrun2
          · cases hopt : new2? with
            | none =>
              have ht' : tgt' = tgtName := by simp [tgt', retargetColdTarget, hopt, beq_false_of_ne h1]
              rw [ht'] at hlook1
              exact ⟨pcStub, k1, st1, hk1, hlook1, hrun1, by simpa [hsz_eq] using hpc1, hreg1, hmem1⟩
            | some new2 =>
              by_cases h2 : tgtName = old2
              · subst h2
                have ht' : tgt' = new2 := by
                  simp [tgt', retargetColdTarget, hopt, beq_false_of_ne h1]
                rw [ht'] at hlook1
                have hS2 : ∃ p2 q2, base.linkSpec (p2 ++ [AsmItem.label new2, AsmItem.j tgtName] ++ q2) =
                    .ok (code, labels) := by simpa [hopt] using hStub2
                obtain ⟨p2, q2, hl2⟩ := hS2
                cases hcond : evalBranch op (st.getReg rs1) (st.getReg rs2) with
                | false =>
                  obtain ⟨tgt, hlookTgt⟩ := hstubTgt new2 tgtName p2 q2 hl2
                  exact ⟨tgt, k1, st1, hk1, hlookTgt, hrun1, by simpa [hcond, hsz_eq] using hpc1, hreg1, hmem1⟩
                | true =>
                  have hpc1' : st1.pc = BitVec.ofNat 64 (4 * pcStub) := by simpa [hcond] using hpc1
                  obtain ⟨tgt, k2, st2, hk2, hlookTgt, hrun2, hpc2, hreg2, hmem2⟩ :=
                    hstepStub hrom new2 tgtName p2 q2 hl2 pcStub hlook1 st1 hpc1'
                  refine ⟨tgt, k1 + k2, st2, by omega, hlookTgt, ?_, by simpa [hcond] using hpc2,
                    hreg1.trans hreg2, hmem2.trans hmem1⟩
                  rw [hrun_add hrun1]; exact hrun2
              · have ht' : tgt' = tgtName := by
                  simp [tgt', retargetColdTarget, hopt, beq_false_of_ne h1, beq_false_of_ne h2]
                rw [ht'] at hlook1
                exact ⟨pcStub, k1, st1, hk1, hlook1, hrun1, by simpa [hsz_eq] using hpc1, hreg1, hmem1⟩
        · rw [hpostElem k hk] at hxk; cases hxk
      · cases h
    step_brLong := by
      intro rom c l pre post op rs1 rs2 tgtName st hrom h hreg h64 hpc
      split at h
      · next heq =>
        cases h
        rcases split_append3_elem heq with ⟨k, _, hk, hxk, _⟩ | ⟨a', b', rfl, _, hmid⟩ | ⟨k, _, hk, hxk, _⟩
        · rw [hpreElem k hk] at hxk; cases hxk
        · let tgt' := retargetColdTarget old1 new1 old2 new2? tgtName
          have hsz_eq : sz (.brLong op rs1 rs2 tgtName) = base.itemSize (.brLong op rs1 rs2 tgt') := rfl
          have hb : base.linkSpec ((preRaw ++ a'.map r) ++ [.brLong op rs1 rs2 tgt'] ++ (b'.map r ++ postRaw)) =
              .ok (code, labels) := hmap_split hmid
          rw [hha a'] at h64 hpc ⊢
          change 4 * (totalSizeWith base.itemSize (preRaw ++ a'.map r) + base.itemSize (.brLong op rs1 rs2 tgt')) < 2 ^ 64 at h64
          obtain ⟨pcStub, k1, st1, hk1, hlook1, hrun1, hpc1, hreg1, hmem1⟩ :=
            base.step_brLong hrom hb hreg h64 hpc
          by_cases h1 : tgtName = old1
          · subst h1
            have ht' : tgt' = new1 := by simp [tgt', retargetColdTarget]
            rw [ht'] at hlook1
            obtain ⟨p1, q1, hl1⟩ := hStub1
            cases hcond : evalBranch op (st.getReg rs1) (st.getReg rs2) with
            | false =>
              obtain ⟨tgt, hlookTgt⟩ := hstubTgt new1 tgtName p1 q1 hl1
              exact ⟨tgt, k1, st1, hk1, hlookTgt, hrun1, by simpa [hcond, hsz_eq] using hpc1, hreg1, hmem1⟩
            | true =>
              have hpc1' : st1.pc = BitVec.ofNat 64 (4 * pcStub) := by simpa [hcond] using hpc1
              obtain ⟨tgt, k2, st2, hk2, hlookTgt, hrun2, hpc2, hreg2, hmem2⟩ :=
                hstepStub hrom new1 tgtName p1 q1 hl1 pcStub hlook1 st1 hpc1'
              refine ⟨tgt, k1 + k2, st2, by omega, hlookTgt, ?_, by simpa [hcond] using hpc2,
                hreg1.trans hreg2, hmem2.trans hmem1⟩
              rw [hrun_add hrun1]; exact hrun2
          · cases hopt : new2? with
            | none =>
              have ht' : tgt' = tgtName := by simp [tgt', retargetColdTarget, hopt, beq_false_of_ne h1]
              rw [ht'] at hlook1
              exact ⟨pcStub, k1, st1, hk1, hlook1, hrun1, by simpa [hsz_eq] using hpc1, hreg1, hmem1⟩
            | some new2 =>
              by_cases h2 : tgtName = old2
              · subst h2
                have ht' : tgt' = new2 := by
                  simp [tgt', retargetColdTarget, hopt, beq_false_of_ne h1]
                rw [ht'] at hlook1
                have hS2 : ∃ p2 q2, base.linkSpec (p2 ++ [AsmItem.label new2, AsmItem.j tgtName] ++ q2) =
                    .ok (code, labels) := by simpa [hopt] using hStub2
                obtain ⟨p2, q2, hl2⟩ := hS2
                cases hcond : evalBranch op (st.getReg rs1) (st.getReg rs2) with
                | false =>
                  obtain ⟨tgt, hlookTgt⟩ := hstubTgt new2 tgtName p2 q2 hl2
                  exact ⟨tgt, k1, st1, hk1, hlookTgt, hrun1, by simpa [hcond, hsz_eq] using hpc1, hreg1, hmem1⟩
                | true =>
                  have hpc1' : st1.pc = BitVec.ofNat 64 (4 * pcStub) := by simpa [hcond] using hpc1
                  obtain ⟨tgt, k2, st2, hk2, hlookTgt, hrun2, hpc2, hreg2, hmem2⟩ :=
                    hstepStub hrom new2 tgtName p2 q2 hl2 pcStub hlook1 st1 hpc1'
                  refine ⟨tgt, k1 + k2, st2, by omega, hlookTgt, ?_, by simpa [hcond] using hpc2,
                    hreg1.trans hreg2, hmem2.trans hmem1⟩
                  rw [hrun_add hrun1]; exact hrun2
              · have ht' : tgt' = tgtName := by
                  simp [tgt', retargetColdTarget, hopt, beq_false_of_ne h1, beq_false_of_ne h2]
                rw [ht'] at hlook1
                exact ⟨pcStub, k1, st1, hk1, hlook1, hrun1, by simpa [hsz_eq] using hpc1, hreg1, hmem1⟩
        · rw [hpostElem k hk] at hxk; cases hxk
      · cases h }

theorem retargetLinkModel_totalSize_pre_eq (base : LinkModel)
    (code : Array (BitVec 32)) (labels : LabelMap)
    (old1 new1 old2 : String) (new2? : Option String)
    (preRaw bodyRaw postRaw : List AsmItem)
    (hlink : base.linkSpec (preRaw ++ bodyRaw.map (retargetColdItem old1 new1 old2 new2?) ++ postRaw) =
      .ok (code, labels))
    (hcode64 : 4 * code.size < 2 ^ 64)
    (hStub1 : ∃ p1 q1,
      base.linkSpec (p1 ++ [AsmItem.label new1, AsmItem.j old1] ++ q1) = .ok (code, labels))
    (hStub2 : match new2? with
      | some new2 => ∃ p2 q2,
        base.linkSpec (p2 ++ [AsmItem.label new2, AsmItem.j old2] ++ q2) = .ok (code, labels)
      | none => True) :
    ∃ prePad postPad,
      (retargetLinkModel base code labels old1 new1 old2 new2? preRaw bodyRaw postRaw hlink hcode64 hStub1 hStub2).linkSpec
        (prePad ++ bodyRaw ++ postPad) = .ok (code, labels) ∧
      (retargetLinkModel base code labels old1 new1 old2 new2? preRaw bodyRaw postRaw hlink hcode64 hStub1 hStub2).totalSize prePad =
        base.totalSize preRaw ∧
      (∀ xs, (retargetLinkModel base code labels old1 new1 old2 new2? preRaw bodyRaw postRaw hlink hcode64 hStub1 hStub2).totalSize xs =
        base.totalSize (xs.map (retargetColdItem old1 new1 old2 new2?))) := by
  let r := retargetColdItem old1 new1 old2 new2?
  let hsz : code.size = base.totalSize preRaw + base.totalSize (bodyRaw.map r) + base.totalSize postRaw := by
    have hs := base.linkSpec_size hlink
    simpa [LinkModel.totalSize, totalSizeWith, List.map_append, List.sum_append, Nat.add_assoc] using hs
  let hdec := base.word_decoded hlink
  let preInstrs : List Instr := List.ofFn fun (i : Fin (base.totalSize preRaw)) =>
    Classical.choose (hdec i.val (by omega))
  let postOff := base.totalSize preRaw + base.totalSize (bodyRaw.map r)
  let postInstrs : List Instr := List.ofFn fun (i : Fin (base.totalSize postRaw)) =>
    Classical.choose (hdec (postOff + i.val) (by omega))
  refine ⟨preInstrs.map AsmItem.instr, postInstrs.map AsmItem.instr, ?_, ?_, ?_⟩
  · dsimp only [retargetLinkModel]
    split
    · rfl
    · next h => exact absurd rfl h
  · dsimp only [retargetLinkModel, LinkModel.totalSize]
    rw [all_instrs_totalSize (fun it => base.itemSize (retargetColdItem old1 new1 old2 new2? it))
      (fun i => base.itemSize_instr i) preInstrs]
    simp [preInstrs]; rfl
  · intro xs
    dsimp only [retargetLinkModel, LinkModel.totalSize]
    exact totalSizeWith_map_retarget base old1 new1 old2 new2? xs

/-! ## 6. Axiom Cleanliness Guards -/

/--
info: 'ConAgua.RISCV.Linker.nearLinkModel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nearLinkModel

/--
info: 'ConAgua.RISCV.Linker.farLinkModel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms farLinkModel

/--
info: 'ConAgua.RISCV.Linker.linkFar_ok_linkSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms linkFar_ok_linkSpec

/--
info: 'ConAgua.RISCV.Linker.AbiPreservedRegs.of_regEqExceptT6' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AbiPreservedRegs.of_regEqExceptT6

/--
info: 'ConAgua.RISCV.Linker.AbiPreservedRegs.of_setReg_ra_regEqExceptT6' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AbiPreservedRegs.of_setReg_ra_regEqExceptT6

/--
info: 'ConAgua.RISCV.Linker.LinkModel.CodeAt.mid_split' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LinkModel.CodeAt.mid_split

end ConAgua.RISCV.Linker
