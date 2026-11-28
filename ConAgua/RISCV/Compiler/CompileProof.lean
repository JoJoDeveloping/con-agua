import ConAgua.RISCV.Compiler.Compile
import ConAgua.RISCV.Compiler.AsmProof
import ConAgua.RISCV.Linker.LinkModel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Forward Simulation & End-to-End Smoke Verification (`ConAgua.RISCV.Compiler.CompileProof`)

Proves:
1. Single-item execution lemmas (`step_item_instr`, `step_item_j`, `step_item_call`,
   `step_item_br`) for linked code via `AsmProof.linkResolved_item_spec`.
2. Little-endian memory load/store frame lemmas (`loadBytes_storeBytes_self`,
   `loadBytes_storeBytes_disjoint`).
3. Macro correctness (`li32_correct`, `li_correct`, `addImmOff_correct`,
   `loadMemOff_ld_correct`, `storeMemOff_sd_correct`).
4. Forward simulation (`evalExpr_sim`, `evalCond_sim`, `execStmt_sim`) against
   `ConAgua.RISCV.RV64.Semantics.run`.
5. End-to-end correctness theorem `acceptOk_correct` for the `"accept iff input == OK"`
   `MiniL` program compiled with `compileProg`.
-/

namespace ConAgua.RISCV.Compiler

open ConAgua.RISCV.RV64
open ConAgua.RISCV.Linker

/-! ## 1. Register & Run Helpers -/

def stepReg (st : State) (r : Reg) (v nextPc : Word) : State :=
  { (st.setReg r v) with pc := nextPc }

theorem getReg_zero (st : State) : st.getReg AbiReg.zero = 0#64 := rfl

private theorem getReg_setReg (st : State) (r q : Reg) (v : Word) :
    (st.setReg r v).getReg q =
      if q == 0#5 then 0#64 else if q == r then v else st.getReg q := by
  unfold State.getReg State.setReg
  by_cases hr0 : r == 0#5
  · simp only [hr0, ↓reduceIte]
    by_cases hq0 : q == 0#5
    · simp [hq0]
    · have hqr : (q == r) = false := by
        rw [beq_iff_eq] at hr0; subst hr0; exact Bool.eq_false_iff.mpr (by simpa using hq0)
      simp [hq0, hqr]
  · simp only [hr0, Bool.false_eq_true, ↓reduceIte]
    by_cases hq0 : q == 0#5
    · simp [hq0]
    · by_cases hqr : q == r <;> simp [hq0, hqr]

theorem getReg_stepReg_eq (st : State) (r : Reg) (hr : r ≠ 0#5) (v nextPc : Word) :
    (stepReg st r v nextPc).getReg r = v := by
  change (st.setReg r v).getReg r = v
  rw [getReg_setReg]
  simp [beq_false_of_ne hr]

theorem getReg_stepReg_ne (st : State) (r q : Reg) (hne : q ≠ r) (v nextPc : Word) :
    (stepReg st r v nextPc).getReg q = st.getReg q := by
  change (st.setReg r v).getReg q = st.getReg q
  rw [getReg_setReg]
  simp only [beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte]
  split
  · next hq0 => simp [State.getReg, hq0]
  · rfl

theorem pc_stepReg (st : State) (r : Reg) (v nextPc : Word) :
    (stepReg st r v nextPc).pc = nextPc := rfl

theorem mem_stepReg (st : State) (r : Reg) (v nextPc : Word) :
    (stepReg st r v nextPc).mem = st.mem := by
  change (st.setReg r v).mem = st.mem
  unfold State.setReg; split <;> rfl

theorem setReg_zero (st : State) (v : Word) : st.setReg AbiReg.zero v = st := by
  simp [State.setReg, AbiReg.zero]

theorem run_add {rom : Rom} (a b : Nat) (st : State) :
    RV64.run rom (a + b) st = match RV64.run rom a st with
      | .cont st' => RV64.run rom b st'
      | res => res := by
  induction a generalizing st with
  | zero => simp [RV64.run]
  | succ a ih =>
    rw [Nat.succ_add, RV64.run, RV64.run]
    cases h : RV64.step rom st with
    | cont st' => exact ih st'
    | trap => rfl

/-! ## 2. Linked-Code Step Lemmas -/

/-- A `Rom` contains the linked words `code` starting at byte address `0`. -/
def RomMatchesCode (rom : Rom) (code : Array (BitVec 32)) : Prop :=
  ∀ k, k < code.size → rom k = some code[k]!

theorem romOfArray_matchesCode (code : Array (BitVec 32)) :
    RomMatchesCode (romOfArray code) code := by
  intro k hk
  simp [romOfArray, hk]

theorem step_at_decoded {rom : Rom} {code : Array (BitVec 32)}
    (hrom : RomMatchesCode rom code) {k : Nat} (hk : k < code.size)
    (hk64 : 4 * k < 2 ^ 64) {inst : Instr} (hdec : (code[k]?).bind decode = some inst)
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
  rw [hpcNat, hrom k hk]
  have hget : code[k]? = some code[k]! := by simp [hk]
  rw [hget, Option.bind_some] at hdec
  dsimp only
  rw [hdec]

private theorem pc_add_4_ofNat {k : Nat} (pc : Word) (hpc : pc = BitVec.ofNat 64 (4 * k)) :
    pc + 4#64 = BitVec.ofNat 64 (4 * (k + 1)) := by
  rw [hpc, show (4#64 : Word) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
  congr 1

theorem step_item_instr {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem) (inst : Instr)
    (hlink : linkResolved (pre ++ [.instr inst] ++ post) = .ok (code, labels))
    (h64 : 4 * totalWords pre < 2 ^ 64) (st : State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * totalWords pre)) :
    RV64.step rom st = execInstr st inst := by
  have hsz := linkResolved_size hlink
  have hitem := linkResolved_item_spec pre (.instr inst) post code labels hlink
  have hk : totalWords pre < code.size := by
    rw [hsz, totalWords_append, totalWords_append, totalWords_cons]
    simp [AsmItem.wordSize]; omega
  exact step_at_decoded hrom hk h64 hitem st hpc

theorem step_item_j {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem) (target : String)
    (hlink : linkResolved (pre ++ [.j target] ++ post) = .ok (code, labels))
    (h64 : 4 * totalWords pre < 2 ^ 64) (st : State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * totalWords pre)) :
    ∃ tgt, lookupLabel labels target = some tgt ∧
      RV64.step rom st = .cont { st with pc := BitVec.ofNat 64 (4 * tgt) } := by
  have hsz := linkResolved_size hlink
  obtain ⟨tgt, jimm, hlook, hdec, hpcAdd⟩ :=
    linkResolved_item_spec pre (.j target) post code labels hlink
  have hk : totalWords pre < code.size := by
    rw [hsz, totalWords_append, totalWords_append, totalWords_cons]
    simp [AsmItem.wordSize]; omega
  refine ⟨tgt, hlook, ?_⟩
  rw [step_at_decoded hrom hk h64 hdec st hpc]
  simp only [execInstr, State.setReg, AbiReg.zero, beq_self_eq_true, ↓reduceIte]
  rw [hpc, hpcAdd]

theorem step_item_call {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem) (target : String)
    (hlink : linkResolved (pre ++ [.call target] ++ post) = .ok (code, labels))
    (h64 : 4 * totalWords pre < 2 ^ 64) (st : State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * totalWords pre)) :
    ∃ tgt, lookupLabel labels target = some tgt ∧
      RV64.step rom st = .cont (stepReg st AbiReg.ra (BitVec.ofNat 64 (4 * (totalWords pre + 1))) (BitVec.ofNat 64 (4 * tgt))) := by
  have hsz := linkResolved_size hlink
  obtain ⟨tgt, jimm, hlook, hdec, hpcAdd⟩ :=
    linkResolved_item_spec pre (.call target) post code labels hlink
  have hk : totalWords pre < code.size := by
    rw [hsz, totalWords_append, totalWords_append, totalWords_cons]
    simp [AsmItem.wordSize]; omega
  refine ⟨tgt, hlook, ?_⟩
  rw [step_at_decoded hrom hk h64 hdec st hpc]
  simp only [execInstr, stepReg]
  rw [pc_add_4_ofNat st.pc hpc, hpc, hpcAdd]

theorem step_item_br {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem) (op : BranchOp)
    (rs1 rs2 : Reg) (target : String)
    (hlink : linkResolved (pre ++ [.br op rs1 rs2 target] ++ post) = .ok (code, labels))
    (h64 : 4 * totalWords pre < 2 ^ 64) (st : State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * totalWords pre)) :
    ∃ tgt, lookupLabel labels target = some tgt ∧
      RV64.step rom st = .cont { st with pc :=
        (if evalBranch op (st.getReg rs1) (st.getReg rs2)
         then BitVec.ofNat 64 (4 * tgt)
         else BitVec.ofNat 64 (4 * (totalWords pre + 1))) } := by
  have hsz := linkResolved_size hlink
  obtain ⟨tgt, bimm, hlook, hdec, hpcAdd⟩ :=
    linkResolved_item_spec pre (.br op rs1 rs2 target) post code labels hlink
  have hk : totalWords pre < code.size := by
    rw [hsz, totalWords_append, totalWords_append, totalWords_cons]
    simp [AsmItem.wordSize]; omega
  refine ⟨tgt, hlook, ?_⟩
  rw [step_at_decoded hrom hk h64 hdec st hpc]
  simp only [execInstr]
  split
  · rw [hpc, hpcAdd]
  · rw [pc_add_4_ofNat st.pc hpc]

/-! ### LinkModel-Parameterized Step Lemmas -/

theorem step_item_instr_lm (lm : LinkModel) {rom : Rom} {code : Array (BitVec 32)}
    {labels : LabelMap} (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (inst : Instr)
    (hlink : lm.linkSpec (pre ++ [.instr inst] ++ post) = .ok (code, labels))
    (h64 : 4 * lm.totalSize pre < 2 ^ 64) (st : State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre)) :
    RV64.step rom st = execInstr st inst :=
  lm.step_instr hrom hlink h64 hpc

theorem step_item_j_lm (lm : LinkModel) {rom : Rom} {code : Array (BitVec 32)}
    {labels : LabelMap} (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (target : String)
    (hlink : lm.linkSpec (pre ++ [.j target] ++ post) = .ok (code, labels))
    (h64 : 4 * (lm.totalSize pre + lm.itemSize (.j target)) < 2 ^ 64) (st : State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre)) :
    ∃ tgt k st', 1 ≤ k ∧
      lookupLabel labels target = some tgt ∧
      RV64.run rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * tgt) ∧
      RegEqExceptT6 st.regs st'.regs ∧
      st'.mem = st.mem :=
  lm.step_j hrom hlink h64 hpc

theorem step_item_call_lm (lm : LinkModel) {rom : Rom} {code : Array (BitVec 32)}
    {labels : LabelMap} (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (target : String)
    (hlink : lm.linkSpec (pre ++ [.call target] ++ post) = .ok (code, labels))
    (h64 : 4 * (lm.totalSize pre + lm.itemSize (.call target)) < 2 ^ 64) (st : State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre)) :
    ∃ tgt k st', 1 ≤ k ∧
      lookupLabel labels target = some tgt ∧
      RV64.run rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * tgt) ∧
      RegEqExceptT6
        (st.setReg AbiReg.ra (BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.itemSize (.call target))))).regs
        st'.regs ∧
      st'.mem = st.mem :=
  lm.step_call hrom hlink h64 hpc

theorem step_item_br_lm (lm : LinkModel) {rom : Rom} {code : Array (BitVec 32)}
    {labels : LabelMap} (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (op : BranchOp) (rs1 rs2 : Reg) (target : String)
    (hlink : lm.linkSpec (pre ++ [.br op rs1 rs2 target] ++ post) = .ok (code, labels))
    (hrs : rs1 ≠ AbiReg.t6 ∧ rs2 ≠ AbiReg.t6)
    (h64 : 4 * (lm.totalSize pre + lm.itemSize (.br op rs1 rs2 target)) < 2 ^ 64) (st : State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre)) :
    ∃ tgt k st', 1 ≤ k ∧
      lookupLabel labels target = some tgt ∧
      RV64.run rom k st = .cont st' ∧
      st'.pc = (if evalBranch op (st.getReg rs1) (st.getReg rs2)
                then BitVec.ofNat 64 (4 * tgt)
                else BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.itemSize (.br op rs1 rs2 target)))) ∧
      RegEqExceptT6 st.regs st'.regs ∧
      st'.mem = st.mem :=
  lm.step_br hrom hlink hrs h64 hpc

theorem step_item_brLong_lm (lm : LinkModel) {rom : Rom} {code : Array (BitVec 32)}
    {labels : LabelMap} (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (op : BranchOp) (rs1 rs2 : Reg) (target : String)
    (hlink : lm.linkSpec (pre ++ [.brLong op rs1 rs2 target] ++ post) = .ok (code, labels))
    (hrs : rs1 ≠ AbiReg.t6 ∧ rs2 ≠ AbiReg.t6)
    (h64 : 4 * (lm.totalSize pre + lm.itemSize (.brLong op rs1 rs2 target)) < 2 ^ 64) (st : State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre)) :
    ∃ tgt k st', 1 ≤ k ∧
      lookupLabel labels target = some tgt ∧
      RV64.run rom k st = .cont st' ∧
      st'.pc = (if evalBranch op (st.getReg rs1) (st.getReg rs2)
                then BitVec.ofNat 64 (4 * tgt)
                else BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.itemSize (.brLong op rs1 rs2 target)))) ∧
      RegEqExceptT6 st.regs st'.regs ∧
      st'.mem = st.mem :=
  lm.step_brLong hrom hlink hrs h64 hpc

/-! ## 3. 64-bit Memory Load/Store Lemmas -/

abbrev readWord64 (mem : Word → Byte) (addr : Word) : Word :=
  loadBytes mem addr 8

abbrev writeWord64 (mem : Word → Byte) (addr v : Word) : Word → Byte :=
  storeBytes mem addr 8 v

theorem storeBytes_apply_ne (mem : Word → Byte) (addr : Word) :
    ∀ (n : Nat) (v : BitVec (8 * n)) (a : Word),
      (∀ i, i < n → a ≠ addr + BitVec.ofNat 64 i) →
      storeBytes mem addr n v a = mem a
  | 0, _, _, _ => rfl
  | n + 1, v, a, hne => by
    simp only [storeBytes]
    have hne' : ∀ i, i < n → a ≠ (addr + 1#64) + BitVec.ofNat 64 i := by
      intro i hi
      have h := hne (i + 1) (by omega)
      have hadd : addr + BitVec.ofNat 64 (i + 1) = (addr + 1#64) + BitVec.ofNat 64 i := by
        rw [BitVec.add_assoc]; congr 1
        rw [BitVec.ofNat_add, BitVec.add_comm]
      rwa [hadd] at h
    rw [storeBytes_apply_ne _ (addr + 1#64) n _ a hne']
    have h0 := hne 0 (by omega)
    have hz : BitVec.ofNat 64 0 = 0#64 := rfl
    rw [hz, BitVec.add_zero] at h0
    simp [beq_false_of_ne h0]

theorem loadBytes_congr (mem₁ mem₂ : Word → Byte) (addr : Word) :
    ∀ (n : Nat),
      (∀ i, i < n → mem₁ (addr + BitVec.ofNat 64 i) = mem₂ (addr + BitVec.ofNat 64 i)) →
      loadBytes mem₁ addr n = loadBytes mem₂ addr n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [loadBytes]
    have h0 := h 0 (by omega)
    have hz : BitVec.ofNat 64 0 = 0#64 := rfl
    rw [hz, BitVec.add_zero] at h0
    have htail := loadBytes_congr mem₁ mem₂ (addr + 1#64) n (fun i hi => by
      have hi1 := h (i + 1) (by omega)
      have hadd : addr + BitVec.ofNat 64 (i + 1) = (addr + 1#64) + BitVec.ofNat 64 i := by
        rw [BitVec.add_assoc]; congr 1
        rw [BitVec.ofNat_add, BitVec.add_comm]
      rwa [hadd] at hi1)
    rw [h0, htail]

theorem loadBytes_storeBytes_self (mem : Word → Byte) (addr : Word) :
    ∀ (n : Nat) (_hn : n < 2 ^ 64) (v : BitVec (8 * n)),
      loadBytes (storeBytes mem addr n v) addr n = v
  | 0, _, v => by
    apply BitVec.eq_of_getLsbD_eq; intro j hj; simp at hj
  | n + 1, hn, v => by
    simp only [loadBytes, storeBytes]
    have hne0 : ∀ i, i < n → addr ≠ (addr + 1#64) + BitVec.ofNat 64 i := by
      intro i hi heq
      have hadd : addr + BitVec.ofNat 64 (1 + i) = (addr + 1#64) + BitVec.ofNat 64 i := by
        rw [BitVec.add_assoc]; congr 1
        rw [BitVec.ofNat_add]
      rw [← hadd] at heq
      have hsub := congrArg (· - addr) heq
      rw [BitVec.sub_self, BitVec.add_comm addr, BitVec.add_sub_cancel] at hsub
      have h2 := congrArg BitVec.toNat hsub
      simp only [BitVec.toNat_ofNat, Nat.zero_mod] at h2
      rw [Nat.mod_eq_of_lt (by omega)] at h2
      omega
    rw [storeBytes_apply_ne _ (addr + 1#64) n _ addr hne0]
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [loadBytes_storeBytes_self _ (addr + 1#64) n (by omega) (v.extractLsb' 8 (8 * n))]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
    by_cases h8 : j < 8
    · simp [h8]
    · have hj8 : j - 8 < 8 * n := by omega
      simp [h8, hj8, show 8 + (j - 8) = j by omega]

theorem loadBytes_storeBytes_disjoint (mem : Word → Byte) (a1 a2 : Word) (n1 n2 : Nat)
    (v : BitVec (8 * n2))
    (hdisj : ∀ i1 i2, i1 < n1 → i2 < n2 → a1 + BitVec.ofNat 64 i1 ≠ a2 + BitVec.ofNat 64 i2) :
    loadBytes (storeBytes mem a2 n2 v) a1 n1 = loadBytes mem a1 n1 :=
  loadBytes_congr _ _ a1 n1 fun i1 hi1 =>
    storeBytes_apply_ne mem a2 n2 v (a1 + BitVec.ofNat 64 i1) fun i2 hi2 => hdisj i1 i2 hi1 hi2

theorem readWord64_writeWord64_self (mem : Word → Byte) (addr v : Word) :
    readWord64 (writeWord64 mem addr v) addr = v :=
  loadBytes_storeBytes_self mem addr 8 (by decide) v

theorem readWord64_writeWord64_disjoint (mem : Word → Byte) (a1 a2 v : Word)
    (hdisj : ∀ i1 i2, i1 < 8 → i2 < 8 → a1 + BitVec.ofNat 64 i1 ≠ a2 + BitVec.ofNat 64 i2) :
    readWord64 (writeWord64 mem a2 v) a1 = readWord64 mem a1 :=
  loadBytes_storeBytes_disjoint mem a1 a2 8 8 v hdisj

/-! ## 4. Straight-Line Execution & `li` Correctness -/

theorem exec_instr_list_lm (lm : LinkModel) {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem) (is : List Instr)
    (hlink : lm.linkSpec (pre ++ is.map .instr ++ post) = .ok (code, labels))
    (h64 : 4 * (lm.totalSize pre + is.length) < 2 ^ 64)
    (stepFn : State → Instr → State)
    (hstepFn : ∀ s inst, inst ∈ is →
      execInstr s inst = .cont (stepFn s inst) ∧ (stepFn s inst).pc = s.pc + 4#64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre)) :
    RV64.run rom is.length st = .cont (is.foldl stepFn st) ∧
      (is.foldl stepFn st).pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + is.length)) := by
  induction is generalizing pre st with
  | nil =>
    simp only [List.length_nil, RV64.run, List.foldl_nil, Nat.add_zero, true_and]
    exact hpc
  | cons inst rest ih =>
    have hsplit : pre ++ (inst :: rest).map .instr ++ post =
        pre ++ [.instr inst] ++ (rest.map .instr ++ post) := by
      simp [List.append_assoc]
    have hlink' : lm.linkSpec (pre ++ [.instr inst] ++ (rest.map .instr ++ post)) =
        .ok (code, labels) := by rwa [← hsplit]
    have h64_pre : 4 * lm.totalSize pre < 2 ^ 64 := by simp at h64; omega
    have hs := step_item_instr_lm lm hrom pre (rest.map .instr ++ post) inst hlink' h64_pre st hpc
    obtain ⟨hex, hpcNext⟩ := hstepFn st inst (by simp)
    have hsplit2 : (pre ++ [.instr inst]) ++ rest.map .instr ++ post =
        pre ++ (inst :: rest).map .instr ++ post := by
      simp [List.append_assoc]
    have hlink'' : lm.linkSpec ((pre ++ [.instr inst]) ++ rest.map .instr ++ post) =
        .ok (code, labels) := by rwa [hsplit2]
    have htw : lm.totalSize (pre ++ [.instr inst]) = lm.totalSize pre + 1 := by
      rw [(lm.totalSize_append), (lm.totalSize_cons), (lm.totalSize_nil)]; simp [lm.itemSize_instr]
    have h64_rest : 4 * (lm.totalSize (pre ++ [.instr inst]) + rest.length) < 2 ^ 64 := by
      rw [htw]; simp only [List.length_cons] at h64; omega
    have hpc' : (stepFn st inst).pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ [.instr inst])) := by
      rw [hpcNext, htw]; exact pc_add_4_ofNat st.pc hpc
    have hstepFn' : ∀ s i, i ∈ rest →
        execInstr s i = .cont (stepFn s i) ∧ (stepFn s i).pc = s.pc + 4#64 :=
      fun s i hi => hstepFn s i (by simp [hi])
    obtain ⟨hrun, hpcFin⟩ := ih (pre ++ [.instr inst]) hlink'' h64_rest hstepFn' (stepFn st inst) hpc'
    simp only [List.length_cons, List.foldl_cons]
    dsimp only [RV64.run]
    rw [hs, hex]
    refine ⟨hrun, ?_⟩
    rw [hpcFin, htw]
    congr 2; omega

private theorem toInt_signExtend_le {m n : Nat} (hm : 0 < m) (h : m ≤ n) (x : BitVec m) :
    (x.signExtend n).toInt = x.toInt := by
  rw [BitVec.toInt_signExtend, Nat.min_eq_right h]
  have hlo : -(2 ^ (m - 1) : Int) ≤ x.toInt := BitVec.le_toInt x
  have hhi : x.toInt < (2 ^ (m - 1) : Int) := BitVec.toInt_lt
  rw [← BitVec.toInt_ofInt (n := m) x.toInt, BitVec.toInt_ofInt, Int.bmod_def]
  have hpow : ((2 ^ m : Nat) : Int) = 2 * (2 ^ (m - 1) : Int) := by
    cases m with
    | zero => omega
    | succ k => simp [Int.pow_succ, Int.mul_comm]
  have hmod : x.toInt % ((2 ^ m : Nat) : Int) =
      if 0 ≤ x.toInt then x.toInt else x.toInt + ((2 ^ m : Nat) : Int) := by
    split
    · next h0 => exact Int.emod_eq_of_lt h0 (by omega)
    · next h0 =>
      have h1 : 0 ≤ x.toInt + ((2 ^ m : Nat) : Int) := by omega
      have h2 : x.toInt + ((2 ^ m : Nat) : Int) < ((2 ^ m : Nat) : Int) := by omega
      have heq : (x.toInt + ((2 ^ m : Nat) : Int)) % ((2 ^ m : Nat) : Int) =
          x.toInt % ((2 ^ m : Nat) : Int) := by
        rw [Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]
      rw [← heq, Int.emod_eq_of_lt h1 h2]
  rw [hmod]
  split <;> split <;> omega

private theorem sextImmU_toInt (imm20 : BitVec 20) :
    (sextImmU imm20).toInt = imm20.toInt * 4096 := by
  unfold sextImmU
  rw [toInt_signExtend_le (by omega) (by omega), BitVec.toInt_append]
  simp; omega

private theorem sextImm12_toInt (imm12 : BitVec 12) :
    (sextImm12 imm12).toInt = imm12.toInt :=
  toInt_signExtend_le (by omega) (by omega) imm12

private theorem bitvec12_toInt_of_msb_false (x : BitVec 12) (h : x.msb = false) :
    x.toInt = x.toNat := by
  rw [BitVec.toInt_eq_msb_cond]; simp [h]

private theorem bitvec12_toInt_of_msb_true (x : BitVec 12) (h : x.msb = true) :
    x.toInt = (x.toNat : Int) - 4096 := by
  rw [BitVec.toInt_eq_msb_cond]; simp [h]

private theorem bitvec32_split_eq (w32 : BitVec 32) :
    w32.extractLsb' 12 20 ++ w32.extractLsb' 0 12 = w32 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h12 : j < 12
  · simp [h12]
  · have hj' : j - 12 < 20 := by omega
    simp [h12, hj', show 12 + (j - 12) = j by omega]

private theorem extractLsb_signExtend_12 (w32 : BitVec 32) :
    (w32.signExtend 64).extractLsb' 0 12 = w32.extractLsb' 0 12 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have hj32 : j < 32 := by omega
  have hj64 : j < 64 := by omega
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, Nat.zero_add,
    BitVec.getLsbD_signExtend, hj64, hj32, ite_true]

private theorem stepReg_mem (st : State) (r : Reg) (v npc : Word) :
    (stepReg st r v npc).mem = st.mem := by
  unfold stepReg State.setReg; split <;> rfl

/-- Generic straight-line execution lemma for instructions updating only `rd`. -/
theorem exec_rd_ops_lm (lm : LinkModel) {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (rd : Reg) (hrd : rd ≠ 0#5) (ops : List (Instr × (Word → Word)))
    (hlink : lm.linkSpec (pre ++ (ops.map (fun p => AsmItem.instr p.1)) ++ post) = .ok (code, labels))
    (h64 : 4 * (lm.totalSize pre + ops.length) < 2 ^ 64)
    (hops : ∀ s i f, (i, f) ∈ ops →
      execInstr s i = .cont (stepReg s rd (f (s.getReg rd)) (s.pc + 4#64)))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre)) :
    ∃ st', RV64.run rom ops.length st = .cont st' ∧
      (∀ q, q ≠ rd → st'.getReg q = st.getReg q) ∧
      st'.getReg rd = ops.foldl (fun v p => p.2 v) (st.getReg rd) ∧
      st'.mem = st.mem ∧
      st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + ops.length)) := by
  induction ops generalizing pre st with
  | nil =>
    simp only [List.length_nil, RV64.run, List.foldl_nil, Nat.add_zero]
    exact ⟨st, rfl, fun _ _ => rfl, rfl, rfl, hpc⟩
  | cons hd rest ih =>
    rcases hd with ⟨inst, fn⟩
    have hsplit : pre ++ ((inst, fn) :: rest).map (fun p => AsmItem.instr p.1) ++ post =
        pre ++ [.instr inst] ++ (rest.map (fun p => AsmItem.instr p.1) ++ post) := by
      simp [List.append_assoc]
    have hlink' : lm.linkSpec (pre ++ [.instr inst] ++ (rest.map (fun p => AsmItem.instr p.1) ++ post)) =
        .ok (code, labels) := by rwa [← hsplit]
    have h64_pre : 4 * lm.totalSize pre < 2 ^ 64 := by simp at h64; omega
    have hs := step_item_instr_lm lm hrom pre (rest.map (fun p => AsmItem.instr p.1) ++ post) inst hlink' h64_pre st hpc
    have hex := hops st inst fn (by simp)
    let st1 := stepReg st rd (fn (st.getReg rd)) (st.pc + 4#64)
    have hsplit2 : (pre ++ [.instr inst]) ++ rest.map (fun p => AsmItem.instr p.1) ++ post =
        pre ++ ((inst, fn) :: rest).map (fun p => AsmItem.instr p.1) ++ post := by
      simp [List.append_assoc]
    have hlink'' : lm.linkSpec ((pre ++ [.instr inst]) ++ rest.map (fun p => AsmItem.instr p.1) ++ post) =
        .ok (code, labels) := by rwa [hsplit2]
    have htw : lm.totalSize (pre ++ [.instr inst]) = lm.totalSize pre + 1 := by
      rw [(lm.totalSize_append), (lm.totalSize_cons), (lm.totalSize_nil)]; simp [lm.itemSize_instr]
    have h64_rest : 4 * (lm.totalSize (pre ++ [.instr inst]) + rest.length) < 2 ^ 64 := by
      rw [htw]; simp only [List.length_cons] at h64; omega
    have hpc1 : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ [.instr inst])) := by
      change st.pc + 4#64 = _
      rw [htw]; exact pc_add_4_ofNat st.pc hpc
    have hops' : ∀ s i f, (i, f) ∈ rest →
        execInstr s i = .cont (stepReg s rd (f (s.getReg rd)) (s.pc + 4#64)) :=
      fun s i f hf => hops s i f (by simp [hf])
    obtain ⟨st', hrun, hother, hrdFin, hmem, hpcFin⟩ :=
      ih (pre ++ [.instr inst]) hlink'' h64_rest hops' st1 hpc1
    refine ⟨st', ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_cons]
      dsimp only [RV64.run]
      rw [hs, hex]; exact hrun
    · intro q hq
      rw [hother q hq]
      exact getReg_stepReg_ne st rd q hq _ _
    · simp only [List.foldl_cons]
      rw [hrdFin, getReg_stepReg_eq st rd hrd]
    · rw [hmem]; exact stepReg_mem st rd _ _
    · rw [hpcFin, htw]; simp only [List.length_cons]; congr 2; omega

theorem li32Instrs_eval_lm (lm : LinkModel) {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (rd : Reg) (hrd : rd ≠ 0#5) (w32 : BitVec 32)
    (hlink : lm.linkSpec (pre ++ (li32Instrs rd w32).map .instr ++ post) = .ok (code, labels))
    (h64 : 4 * (lm.totalSize pre + (li32Instrs rd w32).length) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre)) :
    ∃ st', RV64.run rom (li32Instrs rd w32).length st = .cont st' ∧
      (∀ q, q ≠ rd → st'.getReg q = st.getReg q) ∧
      st'.getReg rd = w32.signExtend 64 ∧
      st'.mem = st.mem ∧
      st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + (li32Instrs rd w32).length)) := by
  have hsplit : w32.extractLsb' 12 20 ++ w32.extractLsb' 0 12 = w32 := bitvec32_split_eq w32
  have hw32Int : (w32.signExtend 64).toInt =
      (w32.extractLsb' 12 20).toInt * 4096 + (w32.extractLsb' 0 12).toNat := by
    conv => lhs; rw [← hsplit]
    rw [toInt_signExtend_le (by omega) (by omega), BitVec.toInt_append]
    simp; omega
  let lo12 := w32.extractLsb' 0 12
  let hi20 := w32.extractLsb' 12 20
  by_cases hfit : fitsImm12 (w32.signExtend 64) = true
  · let ops : List (Instr × (Word → Word)) :=
      [(.aluImm .addi rd AbiReg.zero lo12, fun _ => sextImm12 lo12)]
    have his : li32Instrs rd w32 = ops.map Prod.fst := by simp [li32Instrs, hfit, ops, lo12]
    rw [his] at hlink h64 ⊢
    rw [List.map_map] at hlink; simp only [Function.comp_def, List.length_map] at hlink h64 ⊢
    obtain ⟨st', hrun, hother, hval, hmem, hpcFin⟩ :=
      exec_rd_ops_lm lm hrom pre post rd hrd ops hlink h64 (fun s i f hf => by
        simp only [ops, List.mem_singleton, Prod.mk.injEq] at hf
        rcases hf with ⟨rfl, rfl⟩
        simp [execInstr, evalAluImm, getReg_zero, stepReg]) st hpc
    refine ⟨st', hrun, hother, ?_, hmem, hpcFin⟩
    rw [hval]
    have hf := hfit; unfold fitsImm12 at hf; rw [beq_iff_eq] at hf
    dsimp only [ops, List.foldl_cons, List.foldl_nil, sextImm12, lo12]
    rwa [← extractLsb_signExtend_12 w32]
  · have hfitF : fitsImm12 (w32.signExtend 64) = false := by revert hfit; cases fitsImm12 (w32.signExtend 64) <;> simp
    by_cases hlo0 : lo12 = 0#12
    · let ops : List (Instr × (Word → Word)) := [(.lui rd hi20, fun _ => sextImmU hi20)]
      have his : li32Instrs rd w32 = ops.map Prod.fst := by simp [li32Instrs, hfitF, lo12, hi20, hlo0, ops]
      rw [his] at hlink h64 ⊢
      rw [List.map_map] at hlink; simp only [Function.comp_def, List.length_map] at hlink h64 ⊢
      obtain ⟨st', hrun, hother, hval, hmem, hpcFin⟩ :=
        exec_rd_ops_lm lm hrom pre post rd hrd ops hlink h64 (fun s i f hf => by
          simp only [ops, List.mem_singleton, Prod.mk.injEq] at hf
          rcases hf with ⟨rfl, rfl⟩; rfl) st hpc
      refine ⟨st', hrun, hother, ?_, hmem, hpcFin⟩
      rw [hval]
      apply BitVec.eq_of_toInt_eq
      dsimp only [ops, List.foldl_cons, List.foldl_nil]
      rw [sextImmU_toInt, hw32Int]; change hi20.toInt * 4096 = hi20.toInt * 4096 + lo12.toNat
      rw [hlo0]; simp
    · have hloB : (lo12 == 0#12) = false := beq_false_of_ne hlo0
      by_cases hmsbF : lo12.msb = false
      · let ops : List (Instr × (Word → Word)) :=
          [(.lui rd hi20, fun _ => sextImmU hi20),
           (.aluImm .addi rd rd lo12, fun v => v + sextImm12 lo12)]
        have his : li32Instrs rd w32 = ops.map Prod.fst := by
          simp [li32Instrs, hfitF, lo12, hi20, hloB, hmsbF, ops]
        rw [his] at hlink h64 ⊢
        rw [List.map_map] at hlink; simp only [Function.comp_def, List.length_map] at hlink h64 ⊢
        obtain ⟨st', hrun, hother, hval, hmem, hpcFin⟩ :=
          exec_rd_ops_lm lm hrom pre post rd hrd ops hlink h64 (fun s i f hf => by
            simp only [ops, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hf
            rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl) st hpc
        refine ⟨st', hrun, hother, ?_, hmem, hpcFin⟩
        rw [hval]
        apply BitVec.eq_of_toInt_eq
        dsimp only [ops, List.foldl_cons, List.foldl_nil]
        rw [← BitVec.ofInt_toInt (x := sextImmU hi20), ← BitVec.ofInt_toInt (x := sextImm12 lo12),
            ← BitVec.ofInt_add, ← BitVec.ofInt_toInt (x := w32.signExtend 64)]
        congr 1
        rw [sextImmU_toInt, sextImm12_toInt, bitvec12_toInt_of_msb_false lo12 hmsbF, hw32Int]
      · have hmsbT : lo12.msb = true := by revert hmsbF; cases lo12.msb <;> simp
        by_cases hhiEq : hi20 = 0x7ffff#20
        · let rem := lo12 - 2048#12
          have hloGe : 2048 ≤ lo12.toNat := by
            have h := hmsbT; rw [BitVec.msb_eq_decide] at h; simp at h; omega
          have hremNat : rem.toNat = lo12.toNat - 2048 := by
            have := lo12.isLt; change (2048 + lo12.toNat) % 4096 = _; omega
          have hremMsb : rem.msb = false := by
            have := lo12.isLt; rw [BitVec.msb_eq_decide]; simp [hremNat]; omega
          have hremInt : rem.toInt = (lo12.toNat : Int) - 2048 := by
            rw [bitvec12_toInt_of_msb_false rem hremMsb, hremNat]; omega
          by_cases hrem0 : rem = 0#12
          · have hloVal : lo12.toNat = 2048 := by
              have : rem.toNat = 0 := by rw [hrem0]; rfl
              omega
            let ops : List (Instr × (Word → Word)) :=
              [(.lui rd hi20, fun _ => sextImmU hi20),
               (.aluImm .addi rd rd 1024#12, fun v => v + sextImm12 1024#12),
               (.aluImm .addi rd rd 1024#12, fun v => v + sextImm12 1024#12)]
            have his : li32Instrs rd w32 = ops.map Prod.fst := by
              simp [li32Instrs, hfitF, lo12, hi20, hloB, hmsbT, hhiEq, rem, hrem0, ops]
            rw [his] at hlink h64 ⊢
            rw [List.map_map] at hlink; simp only [Function.comp_def, List.length_map] at hlink h64 ⊢
            obtain ⟨st', hrun, hother, hval, hmem, hpcFin⟩ :=
              exec_rd_ops_lm lm hrom pre post rd hrd ops hlink h64 (fun s i f hf => by
                simp only [ops, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hf
                rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl) st hpc
            refine ⟨st', hrun, hother, ?_, hmem, hpcFin⟩
            rw [hval]
            dsimp only [ops, List.foldl_cons, List.foldl_nil]
            rw [← BitVec.ofInt_toInt (x := sextImmU hi20), ← BitVec.ofInt_toInt (x := sextImm12 1024#12),
                ← BitVec.ofInt_add, ← BitVec.ofInt_add, ← BitVec.ofInt_toInt (x := w32.signExtend 64)]
            have h1024 : (sextImm12 1024#12).toInt = 1024 := by rw [sextImm12_toInt]; rfl
            rw [sextImmU_toInt, h1024, hw32Int, hloVal]; congr 1
            dsimp only [hi20, lo12] at *; omega
          · have hremB : (rem == 0#12) = false := beq_false_of_ne hrem0
            let ops : List (Instr × (Word → Word)) :=
              [(.lui rd hi20, fun _ => sextImmU hi20),
               (.aluImm .addi rd rd 1024#12, fun v => v + sextImm12 1024#12),
               (.aluImm .addi rd rd 1024#12, fun v => v + sextImm12 1024#12),
               (.aluImm .addi rd rd rem, fun v => v + sextImm12 rem)]
            have his : li32Instrs rd w32 = ops.map Prod.fst := by
              simp [li32Instrs, hfitF, lo12, hi20, hloB, hmsbT, hhiEq, rem, hremB, ops]
            rw [his] at hlink h64 ⊢
            rw [List.map_map] at hlink; simp only [Function.comp_def, List.length_map] at hlink h64 ⊢
            obtain ⟨st', hrun, hother, hval, hmem, hpcFin⟩ :=
              exec_rd_ops_lm lm hrom pre post rd hrd ops hlink h64 (fun s i f hf => by
                simp only [ops, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hf
                rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl) st hpc
            refine ⟨st', hrun, hother, ?_, hmem, hpcFin⟩
            rw [hval]
            dsimp only [ops, List.foldl_cons, List.foldl_nil]
            rw [← BitVec.ofInt_toInt (x := sextImmU hi20), ← BitVec.ofInt_toInt (x := sextImm12 1024#12),
                ← BitVec.ofInt_toInt (x := sextImm12 rem), ← BitVec.ofInt_add, ← BitVec.ofInt_add,
                ← BitVec.ofInt_add, ← BitVec.ofInt_toInt (x := w32.signExtend 64)]
            have h1024 : (sextImm12 1024#12).toInt = 1024 := by rw [sextImm12_toInt]; rfl
            rw [sextImmU_toInt, h1024, sextImm12_toInt, hremInt, hw32Int]; congr 1
            dsimp only [hi20, lo12] at *; omega
        · have hhiNe : (hi20 != 0x7ffff#20) = true := bne_iff_ne.mpr hhiEq
          let ops : List (Instr × (Word → Word)) :=
            [(.lui rd (hi20 + 1#20), fun _ => sextImmU (hi20 + 1#20)),
             (.aluImm .addi rd rd lo12, fun v => v + sextImm12 lo12)]
          have his : li32Instrs rd w32 = ops.map Prod.fst := by
            simp [li32Instrs, hfitF, lo12, hi20, hloB, hmsbT, hhiNe, ops]
          rw [his] at hlink h64 ⊢
          rw [List.map_map] at hlink; simp only [Function.comp_def, List.length_map] at hlink h64 ⊢
          obtain ⟨st', hrun, hother, hval, hmem, hpcFin⟩ :=
            exec_rd_ops_lm lm hrom pre post rd hrd ops hlink h64 (fun s i f hf => by
              simp only [ops, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hf
              rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl) st hpc
          refine ⟨st', hrun, hother, ?_, hmem, hpcFin⟩
          rw [hval]
          dsimp only [ops, List.foldl_cons, List.foldl_nil]
          rw [← BitVec.ofInt_toInt (x := sextImmU (hi20 + 1#20)), ← BitVec.ofInt_toInt (x := sextImm12 lo12),
              ← BitVec.ofInt_add, ← BitVec.ofInt_toInt (x := w32.signExtend 64)]
          have hhi20Int : (hi20 + 1#20).toInt = hi20.toInt + 1 := by
            have hlt : hi20.toInt < 524287 := by
              have hle : hi20.toInt ≤ 524287 := by have := BitVec.toInt_lt (x := hi20); omega
              rcases Int.lt_or_eq_of_le hle with hlt | heq
              · exact hlt
              · exfalso; apply hhiEq; apply BitVec.eq_of_toInt_eq; exact heq
            have hlo : -524288 ≤ hi20.toInt := BitVec.le_toInt hi20
            have hadd20 : hi20 + 1#20 = BitVec.ofInt 20 (hi20.toInt + 1) := by
              rw [BitVec.ofInt_add, BitVec.ofInt_toInt]; rfl
            rw [hadd20, BitVec.toInt_ofInt, Int.bmod_def]
            have hmod : (hi20.toInt + 1) % ((2 ^ 20 : Nat) : Int) =
                if 0 ≤ hi20.toInt + 1 then hi20.toInt + 1 else hi20.toInt + 1 + ((2 ^ 20 : Nat) : Int) := by
              split
              · next h0 => exact Int.emod_eq_of_lt h0 (by omega)
              · next h0 =>
                have ha : 0 ≤ hi20.toInt + 1 + ((2 ^ 20 : Nat) : Int) := by omega
                have hb : hi20.toInt + 1 + ((2 ^ 20 : Nat) : Int) < ((2 ^ 20 : Nat) : Int) := by omega
                have hc : (hi20.toInt + 1 + ((2 ^ 20 : Nat) : Int)) % ((2 ^ 20 : Nat) : Int) =
                    (hi20.toInt + 1) % ((2 ^ 20 : Nat) : Int) := by
                  rw [Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]
                rw [← hc, Int.emod_eq_of_lt ha hb]
            rw [hmod]; split <;> split <;> omega
          rw [sextImmU_toInt, sextImm12_toInt, bitvec12_toInt_of_msb_true lo12 hmsbT, hhi20Int, hw32Int]
          congr 1; dsimp only [hi20, lo12] at *; omega

/-! ## 5. Run Composition & Macro Lemmas (`li`, `addImmOff`, `loadMemOff`, `storeMemOff`) -/

private theorem totalSize_map_instr (lm : LinkModel) {α : Type} (f : α → Instr) (xs : List α) :
    lm.totalSize (xs.map (fun a => AsmItem.instr (f a))) = xs.length := by
  induction xs with
  | nil => exact lm.totalSize_nil
  | cons x rest ih =>
    rw [List.map_cons, (lm.totalSize_cons), ih]
    simp [lm.itemSize_instr, Nat.add_comm]

private theorem extractLsb_signExtend_32 (w32 : BitVec 32) :
    (w32.signExtend 64).extractLsb' 0 32 = w32 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have hj64 : j < 64 := by omega
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, Nat.zero_add,
    BitVec.getLsbD_signExtend, hj64, ite_true]

private theorem signExtend_toNat_mod32 (w32 : BitVec 32) :
    (w32.signExtend 64).toNat % 2 ^ 32 = w32.toNat := by
  have h := congrArg BitVec.toNat (extractLsb_signExtend_32 w32)
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero] at h
  exact h

private theorem zeroExtend_12_64_eq {k : Nat} (hk : k ≤ 11) (x : BitVec k) :
    (x.zeroExtend 12).zeroExtend 64 = x.zeroExtend 64 := by
  apply BitVec.eq_of_toNat_eq
  change (x.setWidth 12 |>.setWidth 64).toNat = (x.setWidth 64).toNat
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have hx := x.isLt
  have hpow : 2 ^ k ≤ 2048 := Nat.pow_le_pow_right (by omega) hk
  have hx4096 : x.toNat < 2 ^ 12 := Nat.lt_of_lt_of_le hx (by omega)
  rw [Nat.mod_eq_of_lt hx4096]

private theorem sextImm12_of_zeroExtend {k : Nat} (hk : k ≤ 11) (x : BitVec k) :
    sextImm12 (x.zeroExtend 12) = x.zeroExtend 64 := by
  have hpow : 2 ^ k ≤ 2048 := Nat.pow_le_pow_right (by omega) hk
  have hx2048 : x.toNat < 2048 := Nat.lt_of_lt_of_le x.isLt hpow
  have hlt12 : (x.zeroExtend 12).toNat < 2048 := by
    change (x.setWidth 12).toNat < 2048
    rw [BitVec.toNat_setWidth]; omega
  have hmsb : (x.zeroExtend 12).msb = false := by
    rw [BitVec.msb_eq_decide]; simp; omega
  have hmsb64 : (x.zeroExtend 64).msb = false := by
    rw [BitVec.msb_eq_decide]
    change decide (2 ^ 63 ≤ (x.setWidth 64).toNat) = false
    rw [BitVec.toNat_setWidth]; simp; omega
  apply BitVec.eq_of_toInt_eq
  rw [sextImm12_toInt, bitvec12_toInt_of_msb_false _ hmsb, BitVec.toInt_eq_msb_cond, hmsb64]
  simp only [Bool.false_eq_true, ↓reduceIte, Int.natCast_inj]
  change (x.setWidth 12).toNat = (x.setWidth 64).toNat
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]; omega

private theorem sextImm12_ofInt_fits (off : Int) (hfits : fitsImm12Int off = true) :
    sextImm12 (BitVec.ofInt 12 off) = BitVec.ofInt 64 off := by
  unfold fitsImm12Int at hfits
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfits
  apply BitVec.eq_of_toInt_eq
  rw [sextImm12_toInt, BitVec.toInt_ofInt, BitVec.toInt_ofInt, Int.bmod_def, Int.bmod_def]
  have hmod12 : off % ((2 ^ 12 : Nat) : Int) = if 0 ≤ off then off else off + 4096 := by
    split
    · next h0 => exact Int.emod_eq_of_lt h0 (by omega)
    · next h0 =>
      have ha : 0 ≤ off + 4096 := by omega
      have hb : off + 4096 < ((2 ^ 12 : Nat) : Int) := by omega
      have hc : (off + 4096) % ((2 ^ 12 : Nat) : Int) = off % ((2 ^ 12 : Nat) : Int) := by
        rw [Int.add_emod, show (4096 : Int) % ((2 ^ 12 : Nat) : Int) = 0 by decide, Int.add_zero, Int.emod_emod]
      rw [← hc, Int.emod_eq_of_lt ha hb]
  have hmod64 : off % ((2 ^ 64 : Nat) : Int) =
      if 0 ≤ off then off else off + ((2 ^ 64 : Nat) : Int) := by
    split
    · next h0 => exact Int.emod_eq_of_lt h0 (by omega)
    · next h0 =>
      have ha : 0 ≤ off + ((2 ^ 64 : Nat) : Int) := by omega
      have hb : off + ((2 ^ 64 : Nat) : Int) < ((2 ^ 64 : Nat) : Int) := by omega
      have hc : (off + ((2 ^ 64 : Nat) : Int)) % ((2 ^ 64 : Nat) : Int) =
          off % ((2 ^ 64 : Nat) : Int) := by
        rw [Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]
      rw [← hc, Int.emod_eq_of_lt ha hb]
  rw [hmod12, hmod64]
  split <;> split <;> split <;> omega

private def liStepInstrs (rd : Reg) (bits : BitVec 6) {k : Nat} (x : BitVec k) : List Instr :=
  let c := x.zeroExtend 12
  [.shImm .slli rd rd bits] ++ (if c == 0#12 then [] else [.aluImm .addi rd rd c])

private theorem li_step_zeroExtend_lm (lm : LinkModel) (k : Nat) (hk : k ≤ 11) (rd : Reg) (hrd : rd ≠ 0#5)
    (bits : BitVec 6) (x : BitVec k) (v : Word)
    {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (preWords : Nat) (hpre : preWords = lm.totalSize pre)
    (hlink : lm.linkSpec (pre ++ (liStepInstrs rd bits x).map .instr ++ post) = .ok (code, labels))
    (h64 : 4 * (preWords + (liStepInstrs rd bits x).length) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * preWords)) (hst : st.getReg rd = v) :
    ∃ st', RV64.run rom (liStepInstrs rd bits x).length st = .cont st' ∧
      (∀ q, q ≠ rd → st'.getReg q = st.getReg q) ∧
      st'.getReg rd = (v <<< bits.toNat) + x.zeroExtend 64 ∧
      st'.mem = st.mem ∧
      st'.pc = BitVec.ofNat 64 (4 * (preWords + (liStepInstrs rd bits x).length)) := by
  subst hpre
  let c := x.zeroExtend 12
  by_cases hc0 : c = 0#12
  · have hx0 : x.zeroExtend 64 = 0#64 := by
      have hc_eq : (c.zeroExtend 64) = 0#64 := by rw [hc0]; rfl
      rw [← zeroExtend_12_64_eq hk x]; exact hc_eq
    let ops : List (Instr × (Word → Word)) :=
      [(.shImm .slli rd rd bits, fun u => u <<< bits.toNat)]
    have his : liStepInstrs rd bits x = ops.map Prod.fst := by
      simp [liStepInstrs, c, hc0, ops]
    rw [his] at hlink h64 ⊢
    rw [List.map_map] at hlink; simp only [Function.comp_def, List.length_map] at hlink h64 ⊢
    obtain ⟨st', hrun, hother, hval, hmem, hpcFin⟩ :=
      exec_rd_ops_lm lm hrom pre post rd hrd ops hlink h64 (fun s i f hf => by
        simp only [ops, List.mem_singleton, Prod.mk.injEq] at hf
        rcases hf with ⟨rfl, rfl⟩; rfl) st hpc
    refine ⟨st', hrun, hother, ?_, hmem, hpcFin⟩
    rw [hval, hst, hx0, BitVec.add_zero]; rfl
  · have hcB : (c == 0#12) = false := beq_false_of_ne hc0
    let ops : List (Instr × (Word → Word)) :=
      [(.shImm .slli rd rd bits, fun u => u <<< bits.toNat),
       (.aluImm .addi rd rd c, fun u => u + sextImm12 c)]
    have his : liStepInstrs rd bits x = ops.map Prod.fst := by
      simp [liStepInstrs, c, hcB, ops]
    rw [his] at hlink h64 ⊢
    rw [List.map_map] at hlink; simp only [Function.comp_def, List.length_map] at hlink h64 ⊢
    obtain ⟨st', hrun, hother, hval, hmem, hpcFin⟩ :=
      exec_rd_ops_lm lm hrom pre post rd hrd ops hlink h64 (fun s i f hf => by
        simp only [ops, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hf
        rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl) st hpc
    refine ⟨st', hrun, hother, ?_, hmem, hpcFin⟩
    rw [hval, hst]; dsimp only [ops, List.foldl_cons, List.foldl_nil, c]
    rw [sextImm12_of_zeroExtend hk x]

private theorem nat_split32 (n : Nat) :
    n / 2 ^ 21 % 2 ^ 11 * 2 ^ 21 + n / 2 ^ 10 % 2 ^ 11 * 2 ^ 10 + n % 2 ^ 10 = n % 2 ^ 32 := by
  have h10 := Nat.div_add_mod n (2 ^ 10)
  have h21 : n / 2 ^ 10 = 2 ^ 11 * (n / 2 ^ 21) + n / 2 ^ 10 % 2 ^ 11 := by
    have h := (Nat.div_add_mod (n / 2 ^ 10) (2 ^ 11)).symm
    rwa [Nat.div_div_eq_div_mul, show (2 ^ 10 : Nat) * 2 ^ 11 = 2 ^ 21 by decide] at h
  have h32 : n / 2 ^ 21 = 2 ^ 11 * (n / 2 ^ 32) + n / 2 ^ 21 % 2 ^ 11 := by
    have h := (Nat.div_add_mod (n / 2 ^ 21) (2 ^ 11)).symm
    rwa [Nat.div_div_eq_div_mul, show (2 ^ 21 : Nat) * 2 ^ 11 = 2 ^ 32 by decide] at h
  have h_all : n = n / 2 ^ 32 * 2 ^ 32 +
      (n / 2 ^ 21 % 2 ^ 11 * 2 ^ 21 + n / 2 ^ 10 % 2 ^ 11 * 2 ^ 10 + n % 2 ^ 10) := by
    rw [← h10, h21, h32]; omega
  have hlt32 : n / 2 ^ 21 % 2 ^ 11 * 2 ^ 21 + n / 2 ^ 10 % 2 ^ 11 * 2 ^ 10 + n % 2 ^ 10 < 2 ^ 32 := by
    have a := Nat.mod_lt (n / 2 ^ 21) (by decide : 0 < 2 ^ 11)
    have b := Nat.mod_lt (n / 2 ^ 10) (by decide : 0 < 2 ^ 11)
    have c := Nat.mod_lt n (by decide : 0 < 2 ^ 10)
    omega
  have hmod : n % 2 ^ 32 =
      n / 2 ^ 21 % 2 ^ 11 * 2 ^ 21 + n / 2 ^ 10 % 2 ^ 11 * 2 ^ 10 + n % 2 ^ 10 := by
    calc n % 2 ^ 32
        = (2 ^ 32 * (n / 2 ^ 32) +
            (n / 2 ^ 21 % 2 ^ 11 * 2 ^ 21 + n / 2 ^ 10 % 2 ^ 11 * 2 ^ 10 + n % 2 ^ 10)) % 2 ^ 32 := by
            rw [Nat.mul_comm (2 ^ 32), ← h_all]
      _ = (n / 2 ^ 21 % 2 ^ 11 * 2 ^ 21 + n / 2 ^ 10 % 2 ^ 11 * 2 ^ 10 + n % 2 ^ 10) % 2 ^ 32 :=
            Nat.mul_add_mod _ _ _
      _ = _ := Nat.mod_eq_of_lt hlt32
  exact hmod.symm

private theorem liLowMask_sound {w : BitVec 64} {sh : BitVec 6}
    (h : liLowMask? w = some sh) :
    sextImm12 (-1#12) >>> sh.toNat = w := by
  unfold liLowMask? at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
        rename_i hchk
        have heq := beq_iff_eq.mp hchk
        have h1 : sextImm12 (-1#12) = BitVec.ofInt 64 (-1) := rfl
        rw [h1]; exact heq
      · cases h
    · cases h

private theorem liShiftAdd_sound {w : BitVec 64} {hi32 : BitVec 32} {sh : BitVec 6} {lo : BitVec 12}
    (h : liShiftAdd? w = some (hi32, sh, lo)) :
    (hi32.signExtend 64 <<< sh.toNat) + sextImm12 lo = w := by
  have htry : ∀ (lo0 : BitVec 12),
      (let w' := w - lo0.signExtend 64
       let tz := ctz64 w'
       if 0 < tz && tz < 64 then
         let sh0 := BitVec.ofNat 6 tz
         let hi32_0 := (w' >>> tz).extractLsb' 0 32
         if (hi32_0.signExtend 64 <<< sh0.toNat) + lo0.signExtend 64 == w then
           some (hi32_0, sh0, lo0)
         else none
       else none) = some (hi32, sh, lo) →
      (hi32.signExtend 64 <<< sh.toNat) + sextImm12 lo = w := by
    intro lo0 ht
    dsimp only at ht
    split at ht
    · split at ht
      · cases ht
        rename_i hchk
        exact beq_iff_eq.mp hchk
      · cases ht
    · cases ht
  unfold liShiftAdd? at h
  dsimp only at h
  split at h
  · rename_i p hp; cases h; exact htry 0#12 hp
  · exact htry (w.extractLsb' 0 12) h

private theorem hi32_zero_slli_srli (w : BitVec 64)
    (h : w.extractLsb' 32 32 = 0#32) :
    ((w.extractLsb' 0 32).signExtend 64 <<< 32) >>> 32 = w := by
  apply BitVec.eq_of_toNat_eq
  have hhi : w.toNat / 2 ^ 32 = 0 := by
    have ht : (w.extractLsb' 32 32).toNat = (0#32).toNat := by rw [h]
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at ht
    have hlt : w.toNat < 2 ^ 64 := w.isLt
    have hdiv : w.toNat / 2 ^ 32 < 2 ^ 32 := by omega
    rw [Nat.mod_eq_of_lt hdiv] at ht
    exact ht
  have hwlt : w.toNat < 2 ^ 32 := by omega
  have hmod : ((w.extractLsb' 0 32).signExtend 64).toNat % 2 ^ 32 = w.toNat := by
    rw [signExtend_toNat_mod32, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
      Nat.mod_eq_of_lt hwlt]
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hmul : ((w.extractLsb' 0 32).signExtend 64).toNat * 2 ^ 32 % 2 ^ 64 =
      (((w.extractLsb' 0 32).signExtend 64).toNat % 2 ^ 32) * 2 ^ 32 := by
    have h64 : (2 ^ 64 : Nat) = 2 ^ 32 * 2 ^ 32 := by decide
    rw [h64, Nat.mul_mod_mul_right]
  rw [hmul, hmod, Nat.mul_div_cancel _ (by decide)]

private theorem fitsDoublePos12_add (off : Int) (h : fitsDoublePos12Int off = true) :
    sextImm12 2047#12 + sextImm12 (BitVec.ofInt 12 (off - 2047)) = BitVec.ofInt 64 off := by
  unfold fitsDoublePos12Int at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 : fitsImm12Int 2047 = true := by decide
  have h2 : fitsImm12Int (off - 2047) = true := by unfold fitsImm12Int; simp; omega
  have h2047 : (2047#12 : BitVec 12) = BitVec.ofInt 12 2047 := rfl
  rw [h2047, sextImm12_ofInt_fits 2047 h1, sextImm12_ofInt_fits (off - 2047) h2]
  rw [show (2047 : Int) = 2047 from rfl, ← BitVec.ofInt_add]
  congr 1; omega

private theorem splitMemOff32_sound {off : Int} {hi20 : BitVec 20} {lo12 : BitVec 12}
    (h : splitMemOff32? off = some (hi20, lo12)) :
    sextImmU hi20 + sextImm12 lo12 = BitVec.ofInt 64 off := by
  unfold splitMemOff32? at h
  dsimp only at h
  split at h
  · cases h; rename_i hchk; exact beq_iff_eq.mp hchk
  · cases h

private theorem liShiftAdd_exec_lm (lm : LinkModel) {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (rd : Reg) (hrd : rd ≠ 0#5) (hi32 : BitVec 32) (sh : BitVec 6) (lo : BitVec 12)
    (w : BitVec 64) (heq : (hi32.signExtend 64 <<< sh.toNat) + sextImm12 lo = w)
    (hlink : lm.linkSpec (pre ++ (li32Instrs rd hi32 ++ [Instr.shImm .slli rd rd sh] ++
        (if lo == 0#12 then [] else [Instr.aluImm .addi rd rd lo])).map .instr ++ post) =
      .ok (code, labels))
    (h64 : 4 * (lm.totalSize pre + (li32Instrs rd hi32 ++ [Instr.shImm .slli rd rd sh] ++
        (if lo == 0#12 then [] else [Instr.aluImm .addi rd rd lo])).length) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre)) :
    ∃ st', RV64.run rom ((li32Instrs rd hi32 ++ [Instr.shImm .slli rd rd sh] ++
        (if lo == 0#12 then [] else [Instr.aluImm .addi rd rd lo])).length) st = .cont st' ∧
      (∀ q, q ≠ rd → st'.getReg q = st.getReg q) ∧
      st'.getReg rd = w ∧
      st'.mem = st.mem ∧
      st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + (li32Instrs rd hi32 ++ [Instr.shImm .slli rd rd sh] ++
        (if lo == 0#12 then [] else [Instr.aluImm .addi rd rd lo])).length)) := by
  let s0 := (li32Instrs rd hi32).map AsmItem.instr
  let tail : List Instr := if lo == 0#12 then [] else [Instr.aluImm .addi rd rd lo]
  have hlen : (li32Instrs rd hi32 ++ [Instr.shImm .slli rd rd sh] ++ tail).length =
      (li32Instrs rd hi32).length + 1 + tail.length := by
    simp only [List.length_append, List.length_singleton]
  have htw0 : lm.totalSize (pre ++ s0) = lm.totalSize pre + (li32Instrs rd hi32).length := by
    rw [lm.totalSize_append, totalSize_map_instr lm]
  have hsplit : pre ++ (li32Instrs rd hi32 ++ [Instr.shImm .slli rd rd sh] ++ tail).map .instr ++ post =
      pre ++ s0 ++ ([AsmItem.instr (.shImm .slli rd rd sh)] ++ tail.map .instr ++ post) := by
    simp only [s0, List.map_append, List.map_cons, List.map_nil, List.append_assoc]
  have hlink0 : lm.linkSpec (pre ++ s0 ++ ([AsmItem.instr (.shImm .slli rd rd sh)] ++ tail.map .instr ++ post)) =
      .ok (code, labels) := by
    rw [← hsplit]; exact hlink
  obtain ⟨st1, hrun0, hoth0, hval0, hmem0, hpc0⟩ :=
    li32Instrs_eval_lm lm hrom pre ([AsmItem.instr (.shImm .slli rd rd sh)] ++ tail.map .instr ++ post)
      rd hrd hi32 hlink0 (by rw [hlen] at h64; omega) st hpc
  have hpc0' : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ s0)) := by rwa [htw0]
  have hlink1 : lm.linkSpec ((pre ++ s0) ++ [AsmItem.instr (.shImm .slli rd rd sh)] ++ (tail.map .instr ++ post)) =
      .ok (code, labels) := by simpa [List.append_assoc] using hlink0
  have hs1 := step_item_instr_lm lm hrom (pre ++ s0) (tail.map .instr ++ post) (.shImm .slli rd rd sh)
    hlink1 (by rw [htw0]; rw [hlen] at h64; omega) st1 hpc0'
  let st2 := stepReg st1 rd (st1.getReg rd <<< sh.toNat) (st1.pc + 4#64)
  have hrun1 : RV64.run rom 1 st1 = .cont st2 := by
    dsimp only [RV64.run]; rw [hs1]; rfl
  have htw1 : lm.totalSize (pre ++ s0 ++ [AsmItem.instr (.shImm .slli rd rd sh)]) =
      lm.totalSize pre + (li32Instrs rd hi32).length + 1 := by
    rw [lm.totalSize_append, htw0, lm.totalSize_instr]
  have hpc1' : st2.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + (li32Instrs rd hi32).length + 1)) := by
    change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc0', htw0]
  by_cases hlo : lo = 0#12
  · have hloB : (lo == 0#12) = true := beq_iff_eq.mpr hlo
    have htl : tail = [] := by simp [tail, hloB]
    have hlen' : (li32Instrs rd hi32 ++ [Instr.shImm .slli rd rd sh] ++ tail).length =
        (li32Instrs rd hi32).length + 1 := by rw [hlen, htl]; simp
    rw [show (if (lo == 0#12) = true then ([] : List Instr) else [Instr.aluImm .addi rd rd lo]) = tail from rfl, hlen']
    refine ⟨st2, ?_, ?_, ?_, ?_, hpc1'⟩
    · rw [run_add, hrun0]; exact hrun1
    · intro q hq; rw [getReg_stepReg_ne st1 rd q hq, hoth0 q hq]
    · rw [getReg_stepReg_eq st1 rd hrd, hval0]
      rw [hlo] at heq; have hz : sextImm12 0#12 = 0#64 := rfl
      simpa [hz] using heq
    · rw [stepReg_mem, hmem0]
  · have hloB : (lo == 0#12) = false := beq_false_of_ne hlo
    have htl : tail = [Instr.aluImm .addi rd rd lo] := by simp [tail, hloB]
    have hlen' : (li32Instrs rd hi32 ++ [Instr.shImm .slli rd rd sh] ++ tail).length =
        (li32Instrs rd hi32).length + 1 + 1 := by rw [hlen, htl]; simp
    have hlink2 : lm.linkSpec ((pre ++ s0 ++ [AsmItem.instr (.shImm .slli rd rd sh)]) ++
        [AsmItem.instr (.aluImm .addi rd rd lo)] ++ post) = .ok (code, labels) := by
      simpa [htl, List.append_assoc] using hlink1
    have hpc1'' : st2.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ s0 ++ [AsmItem.instr (.shImm .slli rd rd sh)])) := by
      rwa [htw1]
    have hs2 := step_item_instr_lm lm hrom (pre ++ s0 ++ [AsmItem.instr (.shImm .slli rd rd sh)]) post
      (.aluImm .addi rd rd lo) hlink2 (by rw [htw1]; rw [hlen'] at h64; omega) st2 hpc1''
    let st3 := stepReg st2 rd (st2.getReg rd + sextImm12 lo) (st2.pc + 4#64)
    rw [show (if (lo == 0#12) = true then ([] : List Instr) else [Instr.aluImm .addi rd rd lo]) = tail from rfl, hlen']
    refine ⟨st3, ?_, ?_, ?_, ?_, ?_⟩
    · rw [run_add, run_add, hrun0]; dsimp only; rw [hrun1]; dsimp only [RV64.run]; rw [hs2]; rfl
    · intro q hq; rw [getReg_stepReg_ne st2 rd q hq, getReg_stepReg_ne st1 rd q hq, hoth0 q hq]
    · rw [getReg_stepReg_eq st2 rd hrd, getReg_stepReg_eq st1 rd hrd, hval0]; exact heq
    · rw [stepReg_mem, stepReg_mem, hmem0]
    · change st2.pc + 4#64 = _; rw [pc_add_4_ofNat st2.pc hpc1', Nat.add_assoc, Nat.add_assoc]

private theorem liHi32Zero_exec_lm (lm : LinkModel) {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (rd : Reg) (hrd : rd ≠ 0#5) (w : BitVec 64) (hhi0 : w.extractLsb' 32 32 = 0#32)
    (hlink : lm.linkSpec (pre ++ (li32Instrs rd (w.extractLsb' 0 32) ++
        [Instr.shImm .slli rd rd 32#6, Instr.shImm .srli rd rd 32#6]).map .instr ++ post) =
      .ok (code, labels))
    (h64 : 4 * (lm.totalSize pre + (li32Instrs rd (w.extractLsb' 0 32) ++
        [Instr.shImm .slli rd rd 32#6, Instr.shImm .srli rd rd 32#6]).length) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre)) :
    ∃ st', RV64.run rom ((li32Instrs rd (w.extractLsb' 0 32) ++
        [Instr.shImm .slli rd rd 32#6, Instr.shImm .srli rd rd 32#6]).length) st = .cont st' ∧
      (∀ q, q ≠ rd → st'.getReg q = st.getReg q) ∧
      st'.getReg rd = w ∧
      st'.mem = st.mem ∧
      st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + (li32Instrs rd (w.extractLsb' 0 32) ++
        [Instr.shImm .slli rd rd 32#6, Instr.shImm .srli rd rd 32#6]).length)) := by
  let lo32 := w.extractLsb' 0 32
  let s0 := (li32Instrs rd lo32).map AsmItem.instr
  have hlen : (li32Instrs rd lo32 ++ [Instr.shImm .slli rd rd 32#6, Instr.shImm .srli rd rd 32#6]).length =
      (li32Instrs rd lo32).length + 2 := by simp [List.length_append]
  have htw0 : lm.totalSize (pre ++ s0) = lm.totalSize pre + (li32Instrs rd lo32).length := by
    rw [lm.totalSize_append, totalSize_map_instr lm]
  have hlink0 : lm.linkSpec (pre ++ s0 ++
      ([AsmItem.instr (.shImm .slli rd rd 32#6), AsmItem.instr (.shImm .srli rd rd 32#6)] ++ post)) =
      .ok (code, labels) := by
    simpa only [s0, lo32, List.map_append, List.map_cons, List.map_nil, List.append_assoc] using hlink
  obtain ⟨st1, hrun0, hoth0, hval0, hmem0, hpc0⟩ :=
    li32Instrs_eval_lm lm hrom pre
      ([AsmItem.instr (.shImm .slli rd rd 32#6), AsmItem.instr (.shImm .srli rd rd 32#6)] ++ post)
      rd hrd lo32 hlink0 (by rw [hlen] at h64; omega) st hpc
  have hpc0' : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ s0)) := by rwa [htw0]
  have hlink1 : lm.linkSpec ((pre ++ s0) ++ [AsmItem.instr (.shImm .slli rd rd 32#6)] ++
      ([AsmItem.instr (.shImm .srli rd rd 32#6)] ++ post)) = .ok (code, labels) := by
    simpa only [List.cons_append, List.nil_append, List.append_assoc] using hlink0
  have hs1 := step_item_instr_lm lm hrom (pre ++ s0)
    ([AsmItem.instr (.shImm .srli rd rd 32#6)] ++ post) (.shImm .slli rd rd 32#6)
    hlink1 (by rw [htw0]; rw [hlen] at h64; omega) st1 hpc0'
  let st2 := stepReg st1 rd (st1.getReg rd <<< 32) (st1.pc + 4#64)
  have htw1 : lm.totalSize (pre ++ s0 ++ [AsmItem.instr (.shImm .slli rd rd 32#6)]) =
      lm.totalSize pre + (li32Instrs rd lo32).length + 1 := by
    rw [lm.totalSize_append, htw0, lm.totalSize_instr]
  have hpc1' : st2.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ s0 ++ [AsmItem.instr (.shImm .slli rd rd 32#6)])) := by
    change st1.pc + 4#64 = _; rw [htw1, pc_add_4_ofNat st1.pc hpc0', htw0]
  have hlink2 : lm.linkSpec ((pre ++ s0 ++ [AsmItem.instr (.shImm .slli rd rd 32#6)]) ++
      [AsmItem.instr (.shImm .srli rd rd 32#6)] ++ post) = .ok (code, labels) := by
    simpa only [List.append_assoc] using hlink1
  have hs2 := step_item_instr_lm lm hrom (pre ++ s0 ++ [AsmItem.instr (.shImm .slli rd rd 32#6)]) post
    (.shImm .srli rd rd 32#6) hlink2 (by rw [htw1]; rw [hlen] at h64; omega) st2 hpc1'
  let st3 := stepReg st2 rd (st2.getReg rd >>> 32) (st2.pc + 4#64)
  rw [show lo32 = w.extractLsb' 0 32 from rfl] at *
  refine ⟨st3, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlen, show (2 : Nat) = 1 + 1 from rfl, ← Nat.add_assoc, run_add, run_add, hrun0]
    dsimp only [RV64.run]; rw [hs1]
    have hx1 : execInstr st1 (.shImm .slli rd rd 32#6) = .cont st2 := rfl
    rw [hx1]; dsimp only; rw [hs2]; rfl
  · intro q hq; rw [getReg_stepReg_ne st2 rd q hq, getReg_stepReg_ne st1 rd q hq, hoth0 q hq]
  · rw [getReg_stepReg_eq st2 rd hrd, getReg_stepReg_eq st1 rd hrd, hval0]
    exact hi32_zero_slli_srli w hhi0
  · rw [stepReg_mem, stepReg_mem, hmem0]
  · change st2.pc + 4#64 = _
    rw [pc_add_4_ofNat st2.pc hpc1', htw1, hlen, Nat.add_assoc]; rfl

theorem li_correct_lm (lm : LinkModel) {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (rd : Reg) (hrd : rd ≠ 0#5) (w : BitVec 64)
    (hlink : lm.linkSpec (pre ++ li rd w ++ post) = .ok (code, labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (li rd w)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre)) :
    ∃ st', RV64.run rom (lm.totalSize (li rd w)) st = .cont st' ∧
      (∀ q, q ≠ rd → st'.getReg q = st.getReg q) ∧
      st'.getReg rd = w ∧
      st'.mem = st.mem ∧
      st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (li rd w))) := by
  have hne0 : (rd == AbiReg.zero) = false := beq_false_of_ne hrd
  by_cases hfit : fitsImm12 w = true
  · let ops : List (Instr × (Word → Word)) :=
      [(.aluImm .addi rd AbiReg.zero (w.extractLsb' 0 12), fun _ => sextImm12 (w.extractLsb' 0 12))]
    have hli : li rd w = ops.map (fun p => AsmItem.instr p.1) := by simp [li, hne0, hfit, ops]
    have htw : lm.totalSize (li rd w) = ops.length := by
      rw [hli, (totalSize_map_instr lm)]
    rw [htw] at h64 ⊢
    rw [hli] at hlink
    obtain ⟨st', hrun, hother, hval, hmem, hpcFin⟩ :=
      exec_rd_ops_lm lm hrom pre post rd hrd ops hlink h64 (fun s i f hf => by
        simp only [ops, List.mem_singleton, Prod.mk.injEq] at hf
        rcases hf with ⟨rfl, rfl⟩
        simp [execInstr, evalAluImm, getReg_zero, stepReg]) st hpc
    refine ⟨st', hrun, hother, ?_, hmem, hpcFin⟩
    rw [hval]
    have hf := hfit; unfold fitsImm12 at hf; rw [beq_iff_eq] at hf
    exact hf
  · have hfitF : fitsImm12 w = false := by revert hfit; cases fitsImm12 w <;> simp
    cases hmask : liLowMask? w with
    | some sh =>
      let ops : List (Instr × (Word → Word)) :=
        [(.aluImm .addi rd AbiReg.zero (-1#12), fun _ => sextImm12 (-1#12)),
         (.shImm .srli rd rd sh, fun v => v >>> sh.toNat)]
      have hli : li rd w = ops.map (fun p => AsmItem.instr p.1) := by
        simp [li, hne0, hfitF, hmask, ops]
      have htw : lm.totalSize (li rd w) = ops.length := by
        rw [hli, (totalSize_map_instr lm)]
      rw [htw] at h64 ⊢
      rw [hli] at hlink
      obtain ⟨st', hrun, hother, hval, hmem, hpcFin⟩ :=
        exec_rd_ops_lm lm hrom pre post rd hrd ops hlink h64 (fun s i f hf => by
          simp only [ops, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hf
          rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simp [execInstr, evalAluImm, getReg_zero, stepReg]
          · simp [execInstr, evalShiftImm, stepReg]) st hpc
      refine ⟨st', hrun, hother, ?_, hmem, hpcFin⟩
      rw [hval]
      exact liLowMask_sound hmask
    | none =>
      by_cases h32 : (w.extractLsb' 0 32).signExtend 64 = w
      · have h32B : ((w.extractLsb' 0 32).signExtend 64 == w) = true := beq_iff_eq.mpr h32
        have hli : li rd w = (li32Instrs rd (w.extractLsb' 0 32)).map .instr := by
          simp [li, hne0, hfitF, hmask, h32B]
        have htw : lm.totalSize (li rd w) = (li32Instrs rd (w.extractLsb' 0 32)).length := by
          rw [hli, (totalSize_map_instr lm)]
        rw [htw] at h64 ⊢
        rw [hli] at hlink
        obtain ⟨st', hrun, hother, hval, hmem, hpcFin⟩ :=
          li32Instrs_eval_lm lm hrom pre post rd hrd (w.extractLsb' 0 32) hlink h64 st hpc
        exact ⟨st', hrun, hother, by rwa [h32] at hval, hmem, hpcFin⟩
      · have h32B : ((w.extractLsb' 0 32).signExtend 64 == w) = false := beq_false_of_ne h32
        cases hsa : liShiftAdd? w with
        | some p =>
          rcases p with ⟨hi32, sh, lo⟩
          have hli : li rd w = (li32Instrs rd hi32 ++ [Instr.shImm .slli rd rd sh] ++
              (if lo == 0#12 then [] else [Instr.aluImm .addi rd rd lo])).map .instr := by
            dsimp only [li]; rw [hne0, hfitF, hmask, h32B, hsa]; simp
          have htw : lm.totalSize (li rd w) = (li32Instrs rd hi32 ++ [Instr.shImm .slli rd rd sh] ++
              (if lo == 0#12 then [] else [Instr.aluImm .addi rd rd lo])).length := by
            rw [hli, totalSize_map_instr lm]
          rw [hli] at hlink; rw [htw] at h64 ⊢
          exact liShiftAdd_exec_lm lm hrom pre post rd hrd hi32 sh lo w (liShiftAdd_sound hsa) hlink h64 st hpc
        | none =>
          by_cases hhi0 : w.extractLsb' 32 32 = 0#32
          · have hhiB : (w.extractLsb' 32 32 == 0#32) = true := beq_iff_eq.mpr hhi0
            have hli : li rd w = (li32Instrs rd (w.extractLsb' 0 32) ++
                [Instr.shImm .slli rd rd 32#6, Instr.shImm .srli rd rd 32#6]).map .instr := by
              dsimp only [li]; rw [hne0, hfitF, hmask, h32B, hsa, hhiB]; rfl
            have htw : lm.totalSize (li rd w) = (li32Instrs rd (w.extractLsb' 0 32) ++
                [Instr.shImm .slli rd rd 32#6, Instr.shImm .srli rd rd 32#6]).length := by
              rw [hli, totalSize_map_instr lm]
            rw [hli] at hlink; rw [htw] at h64 ⊢
            exact liHi32Zero_exec_lm lm hrom pre post rd hrd w hhi0 hlink h64 st hpc
          · have hhiB : (w.extractLsb' 32 32 == 0#32) = false := beq_false_of_ne hhi0
            let hi32 := w.extractLsb' 32 32
            let x1 := w.extractLsb' 21 11
            let x2 := w.extractLsb' 10 11
            let x3 := w.extractLsb' 0 10
            let c1 := x1.zeroExtend 12
            let c2 := x2.zeroExtend 12
            let c3 := x3.zeroExtend 12
            let s0 : List Instr := li32Instrs rd hi32
            let s1 : List Instr := liStepInstrs rd 11#6 x1
            let s2 : List Instr := liStepInstrs rd 11#6 x2
            let s3 : List Instr := liStepInstrs rd 10#6 x3
            have hli : li rd w = (s0 ++ s1 ++ s2 ++ s3).map .instr := by
              simp only [li, hne0, Bool.false_eq_true, ↓reduceIte, hfitF, h32B, hmask, hsa, hhiB,
                hi32, x1, x2, x3, s0, s1, s2, s3, liStepInstrs]
            have htw : lm.totalSize (li rd w) = s0.length + s1.length + s2.length + s3.length := by
              rw [hli, (totalSize_map_instr lm)]; simp only [List.length_append, Nat.add_assoc]
            rw [hli] at hlink; rw [htw] at h64 ⊢
            have hlist0 : pre ++ s0.map .instr ++ ((s1 ++ s2 ++ s3).map .instr ++ post) =
                pre ++ (s0 ++ s1 ++ s2 ++ s3).map .instr ++ post := by
              simp only [List.map_append, List.append_assoc]
            have hlink0 : lm.linkSpec (pre ++ s0.map .instr ++ ((s1 ++ s2 ++ s3).map .instr ++ post)) = .ok (code, labels) := by
              rw [hlist0]; exact hlink
            have h64_0 : 4 * (lm.totalSize pre + s0.length) < 2 ^ 64 := by omega
            obtain ⟨st1, hrun0, hoth0, hval0, hmem0, hpc0⟩ :=
              li32Instrs_eval_lm lm hrom pre ((s1 ++ s2 ++ s3).map .instr ++ post) rd hrd hi32 hlink0 h64_0 st hpc
            have htw0 : lm.totalSize pre + s0.length = lm.totalSize (pre ++ s0.map .instr) := by
              rw [(lm.totalSize_append), (totalSize_map_instr lm)]
            have hlist1 : (pre ++ s0.map .instr) ++ s1.map .instr ++ ((s2 ++ s3).map .instr ++ post) =
                pre ++ (s0 ++ s1 ++ s2 ++ s3).map .instr ++ post := by
              simp only [List.map_append, List.append_assoc]
            have hlink1 : lm.linkSpec ((pre ++ s0.map .instr) ++ s1.map .instr ++ ((s2 ++ s3).map .instr ++ post)) =
                .ok (code, labels) := by
              rw [hlist1]; exact hlink
            have h64_1 : 4 * ((lm.totalSize pre + s0.length) + s1.length) < 2 ^ 64 := by omega
            obtain ⟨st2, hrun1, hoth1, hval1, hmem1, hpc1⟩ :=
              @li_step_zeroExtend_lm lm 11 (by decide) rd hrd 11#6 x1 (hi32.signExtend 64) rom code labels hrom
                _ _ (lm.totalSize pre + s0.length) htw0
                hlink1 h64_1 st1 hpc0 hval0
            have htw1 : lm.totalSize pre + s0.length + s1.length = lm.totalSize (pre ++ s0.map .instr ++ s1.map .instr) := by
              rw [(lm.totalSize_append), ← htw0, (totalSize_map_instr lm)]
            have hlist2 : (pre ++ s0.map .instr ++ s1.map .instr) ++ s2.map .instr ++ (s3.map .instr ++ post) =
                pre ++ (s0 ++ s1 ++ s2 ++ s3).map .instr ++ post := by
              simp only [List.map_append, List.append_assoc]
            have hlink2 : lm.linkSpec ((pre ++ s0.map .instr ++ s1.map .instr) ++ s2.map .instr ++ (s3.map .instr ++ post)) =
                .ok (code, labels) := by
              rw [hlist2]; exact hlink
            have h64_2 : 4 * ((lm.totalSize pre + s0.length + s1.length) + s2.length) < 2 ^ 64 := by omega
            obtain ⟨st3, hrun2, hoth2, hval2, hmem2, hpc2⟩ :=
              @li_step_zeroExtend_lm lm 11 (by decide) rd hrd 11#6 x2 (((hi32.signExtend 64) <<< 11) + x1.zeroExtend 64)
                rom code labels hrom _ _
                (lm.totalSize pre + s0.length + s1.length) htw1 hlink2 h64_2 st2 hpc1 hval1
            have htw2 : lm.totalSize pre + s0.length + s1.length + s2.length =
                lm.totalSize (pre ++ s0.map .instr ++ s1.map .instr ++ s2.map .instr) := by
              rw [(lm.totalSize_append), ← htw1, (totalSize_map_instr lm)]
            have hlist3 : (pre ++ s0.map .instr ++ s1.map .instr ++ s2.map .instr) ++ s3.map .instr ++ post =
                pre ++ (s0 ++ s1 ++ s2 ++ s3).map .instr ++ post := by
              simp only [List.map_append, List.append_assoc]
            have hlink3 : lm.linkSpec ((pre ++ s0.map .instr ++ s1.map .instr ++ s2.map .instr) ++ s3.map .instr ++ post) =
                .ok (code, labels) := by
              rw [hlist3]; exact hlink
            have h64_3 : 4 * ((lm.totalSize pre + s0.length + s1.length + s2.length) + s3.length) < 2 ^ 64 := by omega
            obtain ⟨st4, hrun3, hoth3, hval3, hmem3, hpc3⟩ :=
              @li_step_zeroExtend_lm lm 10 (by decide) rd hrd 10#6 x3
                (((((hi32.signExtend 64) <<< 11) + x1.zeroExtend 64) <<< 11) + x2.zeroExtend 64)
                rom code labels hrom _ _
                (lm.totalSize pre + s0.length + s1.length + s2.length) htw2 hlink3 h64_3 st3 hpc2 hval2
            refine ⟨st4, ?_, ?_, ?_, ?_, ?_⟩
            · rw [run_add (a := s0.length + s1.length + s2.length),
                  run_add (a := s0.length + s1.length),
                  run_add (a := s0.length), hrun0]
              dsimp only; rw [hrun1]; dsimp only; rw [hrun2]; dsimp only; exact hrun3
            · intro q hq
              rw [hoth3 q hq, hoth2 q hq, hoth1 q hq, hoth0 q hq]
            · rw [hval3]
              apply BitVec.eq_of_toNat_eq
              have hv10 : (10#6 : BitVec 6).toNat = 10 := rfl
              rw [hv10]
              change ((((((hi32.signExtend 64) <<< 11 + x1.setWidth 64) <<< 11 + x2.setWidth 64) <<< 10) + x3.setWidth 64).toNat) = w.toNat
              simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth]
              have hmod32 := signExtend_toNat_mod32 hi32
              have h_hi32 : hi32.toNat = w.toNat / 2 ^ 32 := by
                change (w.toNat >>> 32) % 2 ^ 32 = _; rw [Nat.shiftRight_eq_div_pow]
                exact Nat.mod_eq_of_lt (by omega)
              have h_x1 : x1.toNat = (w.toNat / 2 ^ 21) % 2 ^ 11 := by
                change (w.toNat >>> 21) % 2 ^ 11 = _; rw [Nat.shiftRight_eq_div_pow]
              have h_x2 : x2.toNat = (w.toNat / 2 ^ 10) % 2 ^ 11 := by
                change (w.toNat >>> 10) % 2 ^ 11 = _; rw [Nat.shiftRight_eq_div_pow]
              have h_x3 : x3.toNat = w.toNat % 2 ^ 10 := by
                change (w.toNat >>> 0) % 2 ^ 10 = _; rw [Nat.shiftRight_zero]
              have hx1lt : x1.toNat < 2 ^ 64 := by omega
              have hx2lt : x2.toNat < 2 ^ 64 := by omega
              have hx3lt : x3.toNat < 2 ^ 64 := by omega
              rw [Nat.mod_eq_of_lt hx1lt, Nat.mod_eq_of_lt hx2lt, Nat.mod_eq_of_lt hx3lt]
              rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
              have hs1 : (((hi32.signExtend 64).toNat * 2 ^ 11 % 2 ^ 64 + x1.toNat) % 2 ^ 64 * 2 ^ 11) % 2 ^ 64 =
                  ((hi32.signExtend 64).toNat * 2 ^ 11 + x1.toNat) * 2 ^ 11 % 2 ^ 64 := by
                simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
              have hs2 : (((((hi32.signExtend 64).toNat * 2 ^ 11 % 2 ^ 64 + x1.toNat) % 2 ^ 64 * 2 ^ 11) % 2 ^ 64 + x2.toNat) % 2 ^ 64 * 2 ^ 10) % 2 ^ 64 =
                  (((hi32.signExtend 64).toNat * 2 ^ 11 + x1.toNat) * 2 ^ 11 + x2.toNat) * 2 ^ 10 % 2 ^ 64 := by
                simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
              have hs3 : ((((((hi32.signExtend 64).toNat * 2 ^ 11 % 2 ^ 64 + x1.toNat) % 2 ^ 64 * 2 ^ 11) % 2 ^ 64 + x2.toNat) % 2 ^ 64 * 2 ^ 10) % 2 ^ 64 + x3.toNat) % 2 ^ 64 =
                  ((((hi32.signExtend 64).toNat * 2 ^ 11 + x1.toNat) * 2 ^ 11 + x2.toNat) * 2 ^ 10 + x3.toNat) % 2 ^ 64 := by
                simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
              rw [hs3]
              have hhi_eq : ((hi32.signExtend 64).toNat * 2 ^ 11 * 2 ^ 11 * 2 ^ 10) % 2 ^ 64 =
                  (hi32.toNat * 2 ^ 32) := by
                have hpow32 : 2 ^ 11 * 2 ^ 11 * 2 ^ 10 = 2 ^ 32 := by decide
                have hpow64 : 2 ^ 32 * 2 ^ 32 = 2 ^ 64 := by decide
                rw [Nat.mul_assoc _ (2 ^ 11) (2 ^ 11), Nat.mul_assoc _ (2 ^ 11 * 2 ^ 11) (2 ^ 10), hpow32]
                have hdiv : (hi32.signExtend 64).toNat = 2 ^ 32 * ((hi32.signExtend 64).toNat / 2 ^ 32) + hi32.toNat := by
                  omega
                rw [hdiv, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm ((hi32.signExtend 64).toNat / 2 ^ 32) (2 ^ 32),
                    ← Nat.mul_assoc (2 ^ 32) (2 ^ 32), hpow64]
                rw [Nat.add_mod, show (2 ^ 64 * ((hi32.signExtend 64).toNat / 2 ^ 32)) % 2 ^ 64 = 0 by
                  rw [Nat.mul_mod_right], Nat.zero_add, Nat.mod_mod]
                have hhi_lt : hi32.toNat < 2 ^ 32 := hi32.isLt
                have hlt64 : hi32.toNat * 2 ^ 32 < 2 ^ 64 := by
                  calc hi32.toNat * 2 ^ 32 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hhi_lt (by decide)
                    _ = 2 ^ 64 := hpow64
                exact Nat.mod_eq_of_lt hlt64
              have hexpand : (((hi32.signExtend 64).toNat * 2 ^ 11 + x1.toNat) * 2 ^ 11 + x2.toNat) * 2 ^ 10 + x3.toNat =
                  (hi32.signExtend 64).toNat * 2 ^ 11 * 2 ^ 11 * 2 ^ 10 +
                  (x1.toNat * 2 ^ 21 + x2.toNat * 2 ^ 10 + x3.toNat) := by omega
              have hx1_lt : x1.toNat < 2 ^ 11 := x1.isLt
              have hx2_lt : x2.toNat < 2 ^ 11 := x2.isLt
              have hx3_lt : x3.toNat < 2 ^ 10 := x3.isLt
              have hhi_lt : hi32.toNat < 2 ^ 32 := hi32.isLt
              have h_sum_lt : x1.toNat * 2 ^ 21 + x2.toNat * 2 ^ 10 + x3.toNat < 2 ^ 32 := by omega
              have h_sum_lt64 : x1.toNat * 2 ^ 21 + x2.toNat * 2 ^ 10 + x3.toNat < 2 ^ 64 :=
                Nat.lt_trans h_sum_lt (by decide)
              have h_full_lt : hi32.toNat * 2 ^ 32 + (x1.toNat * 2 ^ 21 + x2.toNat * 2 ^ 10 + x3.toNat) < 2 ^ 64 := by
                have hstep : hi32.toNat * 2 ^ 32 + (x1.toNat * 2 ^ 21 + x2.toNat * 2 ^ 10 + x3.toNat) <
                    hi32.toNat * 2 ^ 32 + 2 ^ 32 := Nat.add_lt_add_left h_sum_lt _
                have hmul : hi32.toNat * 2 ^ 32 + 2 ^ 32 = (hi32.toNat + 1) * 2 ^ 32 := by
                  rw [Nat.add_mul, Nat.one_mul]
                have hle : (hi32.toNat + 1) * 2 ^ 32 ≤ 2 ^ 32 * 2 ^ 32 :=
                  Nat.mul_le_mul_right _ hhi_lt
                have hpow64 : 2 ^ 32 * 2 ^ 32 = 2 ^ 64 := by decide
                exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_eq hstep hmul) (hpow64 ▸ hle)
              rw [hexpand, Nat.add_mod, hhi_eq, Nat.mod_eq_of_lt h_sum_lt64, Nat.mod_eq_of_lt h_full_lt,
                  h_hi32, h_x1, h_x2, h_x3]
              rw [nat_split32 w.toNat, Nat.mul_comm (w.toNat / 2 ^ 32), Nat.div_add_mod]
            · rw [hmem3, hmem2, hmem1, hmem0]
            · rw [hpc3]; congr 2
              dsimp only [s3]; simp only [Nat.add_assoc]

theorem addImmOff_correct_lm (lm : LinkModel) {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (rd rs tmp : Reg) (hrd : rd ≠ 0#5) (htmp : tmp ≠ 0#5) (htr : tmp ≠ rs) (off : Int)
    (hlink : lm.linkSpec (pre ++ addImmOff rd rs tmp off ++ post) = .ok (code, labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (addImmOff rd rs tmp off)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre)) :
    ∃ st', RV64.run rom (lm.totalSize (addImmOff rd rs tmp off)) st = .cont st' ∧
      (∀ q, q ≠ rd → q ≠ tmp → st'.getReg q = st.getReg q) ∧
      st'.getReg rd = st.getReg rs + BitVec.ofInt 64 off ∧
      st'.mem = st.mem ∧
      st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (addImmOff rd rs tmp off))) := by
  by_cases hoff0 : off = 0
  · have hadd0 : st.getReg rs + BitVec.ofInt 64 0 = st.getReg rs := by
      have hz : (BitVec.ofInt 64 0 : Word) = 0#64 := rfl
      rw [hz, BitVec.add_zero]
    by_cases hdr : rd = rs
    · have ha : addImmOff rd rs tmp off = [] := by simp [addImmOff, hoff0, hdr]
      rw [ha] at h64 ⊢
      exact ⟨st, rfl, fun _ _ _ => rfl, by rw [hoff0, hadd0, hdr], rfl,
        by simpa [(lm.totalSize_nil)] using hpc⟩
    · have hdrB : (rd == rs) = false := beq_false_of_ne hdr
      have hoffB : (off == 0) = true := beq_iff_eq.mpr hoff0
      have ha : addImmOff rd rs tmp off = [Asm.mv rd rs] := by simp [addImmOff, hoffB, hdrB]
      rw [ha] at hlink h64 ⊢
      have htw : lm.totalSize [Asm.mv rd rs] = 1 := by simp [lm.itemSize_instr, Asm.mv]
      rw [htw] at h64 ⊢
      have hs := step_item_instr_lm lm hrom pre post (.aluImm .addi rd rs 0#12) hlink (by omega) st hpc
      refine ⟨stepReg st rd (st.getReg rs) (st.pc + 4#64), ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only [RV64.run]; rw [hs]; simp [execInstr, evalAluImm, sextImm12, stepReg]
      · intro q hqd _; exact getReg_stepReg_ne st rd q hqd _ _
      · rw [getReg_stepReg_eq st rd hrd, hoff0, hadd0]
      · exact stepReg_mem st rd _ _
      · change st.pc + 4#64 = _; exact pc_add_4_ofNat st.pc hpc
  · have hoffB : (off == 0) = false := beq_false_of_ne hoff0
    by_cases hfits : fitsImm12Int off = true
    · have ha : addImmOff rd rs tmp off = [Asm.addi rd rs (BitVec.ofInt 12 off)] := by
        simp [addImmOff, hoffB, hfits]
      rw [ha] at hlink h64 ⊢
      have htw : lm.totalSize [Asm.addi rd rs (BitVec.ofInt 12 off)] = 1 := by
        simp [lm.itemSize_instr, Asm.addi]
      rw [htw] at h64 ⊢
      have hs := step_item_instr_lm lm hrom pre post (.aluImm .addi rd rs (BitVec.ofInt 12 off))
        hlink (by omega) st hpc
      let st' := stepReg st rd (st.getReg rs + sextImm12 (BitVec.ofInt 12 off)) (st.pc + 4#64)
      refine ⟨st', ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only [RV64.run]; rw [hs]; rfl
      · intro q hqd _; exact getReg_stepReg_ne st rd q hqd _ _
      · rw [getReg_stepReg_eq st rd hrd, sextImm12_ofInt_fits off hfits]
      · exact stepReg_mem st rd _ _
      · change st.pc + 4#64 = _; exact pc_add_4_ofNat st.pc hpc
    · have hfitsF : fitsImm12Int off = false := by revert hfits; cases fitsImm12Int off <;> simp
      by_cases hdbl : fitsDoublePos12Int off = true
      · have ha : addImmOff rd rs tmp off =
            [Asm.addi rd rs 2047#12, Asm.addi rd rd (BitVec.ofInt 12 (off - 2047))] := by
          simp [addImmOff, hoffB, hfitsF, hdbl]
        have htw : lm.totalSize (addImmOff rd rs tmp off) = 2 := by
          rw [ha]; simp [lm.itemSize_instr, Asm.addi]
        rw [htw] at h64 ⊢; rw [ha] at hlink
        have hlink1 : lm.linkSpec (pre ++ [.instr (.aluImm .addi rd rs 2047#12)] ++
            ([Asm.addi rd rd (BitVec.ofInt 12 (off - 2047))] ++ post)) = .ok (code, labels) := by
          simpa [List.append_assoc, Asm.addi] using hlink
        have hs1 := step_item_instr_lm lm hrom pre ([Asm.addi rd rd (BitVec.ofInt 12 (off - 2047))] ++ post)
          (.aluImm .addi rd rs 2047#12) hlink1 (by omega) st hpc
        let st1 := stepReg st rd (st.getReg rs + sextImm12 2047#12) (st.pc + 4#64)
        have htw1 : lm.totalSize (pre ++ [.instr (.aluImm .addi rd rs 2047#12)]) = lm.totalSize pre + 1 := by
          rw [lm.totalSize_append]; simp [lm.itemSize_instr]
        have hpc1 : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ [.instr (.aluImm .addi rd rs 2047#12)])) := by
          change st.pc + 4#64 = _; rw [htw1]; exact pc_add_4_ofNat st.pc hpc
        have hlink2 : lm.linkSpec ((pre ++ [.instr (.aluImm .addi rd rs 2047#12)]) ++
            [.instr (.aluImm .addi rd rd (BitVec.ofInt 12 (off - 2047)))] ++ post) = .ok (code, labels) := by
          simpa [List.append_assoc, Asm.addi] using hlink
        have hs2 := step_item_instr_lm lm hrom (pre ++ [.instr (.aluImm .addi rd rs 2047#12)]) post
          (.aluImm .addi rd rd (BitVec.ofInt 12 (off - 2047))) hlink2 (by rw [htw1]; omega) st1 hpc1
        let st2 := stepReg st1 rd (st1.getReg rd + sextImm12 (BitVec.ofInt 12 (off - 2047))) (st1.pc + 4#64)
        refine ⟨st2, ?_, ?_, ?_, ?_, ?_⟩
        · rw [show (2 : Nat) = 1 + 1 from rfl, run_add]; dsimp only [RV64.run]
          rw [hs1]; have : execInstr st (.aluImm .addi rd rs 2047#12) = .cont st1 := rfl
          rw [this]; dsimp only; rw [hs2]; rfl
        · intro q hqd _; rw [getReg_stepReg_ne st1 rd q hqd, getReg_stepReg_ne st rd q hqd]
        · rw [getReg_stepReg_eq st1 rd hrd, getReg_stepReg_eq st rd hrd, BitVec.add_assoc, fitsDoublePos12_add off hdbl]
        · rw [stepReg_mem, stepReg_mem]
        · change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1, htw1, Nat.add_assoc]
      · have hdblF : fitsDoublePos12Int off = false := by revert hdbl; cases fitsDoublePos12Int off <;> simp
        have ha : addImmOff rd rs tmp off = li tmp (BitVec.ofInt 64 off) ++ [Asm.add rd rs tmp] := by
          simp [addImmOff, hoffB, hfitsF, hdblF]
        have htw : lm.totalSize (addImmOff rd rs tmp off) = lm.totalSize (li tmp (BitVec.ofInt 64 off)) + 1 := by
          rw [ha, (lm.totalSize_append), (lm.totalSize_cons), (lm.totalSize_nil)]; simp [lm.itemSize_instr, Asm.add]
        rw [htw] at h64 ⊢
        rw [ha] at hlink
        have hlink0 : lm.linkSpec (pre ++ li tmp (BitVec.ofInt 64 off) ++ ([Asm.add rd rs tmp] ++ post)) =
            .ok (code, labels) := by simpa [List.append_assoc] using hlink
        obtain ⟨st1, hrun0, hoth0, hval0, hmem0, hpc0⟩ :=
          li_correct_lm lm hrom pre ([Asm.add rd rs tmp] ++ post) tmp htmp (BitVec.ofInt 64 off)
            hlink0 (by omega) st hpc
        have htw0 : lm.totalSize (pre ++ li tmp (BitVec.ofInt 64 off)) =
            lm.totalSize pre + lm.totalSize (li tmp (BitVec.ofInt 64 off)) := (lm.totalSize_append) _ _
        have hpc0' : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ li tmp (BitVec.ofInt 64 off))) := by
          rwa [htw0]
        have hlink1 : lm.linkSpec ((pre ++ li tmp (BitVec.ofInt 64 off)) ++ [.instr (.alu .add rd rs tmp)] ++ post) =
            .ok (code, labels) := by simpa [List.append_assoc, Asm.add] using hlink
        have hs1 := step_item_instr_lm lm hrom (pre ++ li tmp (BitVec.ofInt 64 off)) post (.alu .add rd rs tmp)
          hlink1 (by rw [htw0]; omega) st1 hpc0'
        let st2 := stepReg st1 rd (st1.getReg rs + st1.getReg tmp) (st1.pc + 4#64)
        refine ⟨st2, ?_, ?_, ?_, ?_, ?_⟩
        · rw [run_add, hrun0]; dsimp only
          dsimp only [RV64.run]; rw [hs1]; rfl
        · intro q hqd hqt
          rw [getReg_stepReg_ne st1 rd q hqd, hoth0 q hqt]
        · rw [getReg_stepReg_eq st1 rd hrd, hoth0 rs htr.symm, hval0]
        · rw [stepReg_mem, hmem0]
        · change st1.pc + 4#64 = _
          rw [pc_add_4_ofNat st1.pc hpc0', htw0, Nat.add_assoc]

private def memOffPfx (base tmp : Reg) (off : Int) : List AsmItem × BitVec 12 :=
  if fitsDoublePos12Int off then
    ([Asm.addi tmp base 2047#12], BitVec.ofInt 12 (off - 2047))
  else match splitMemOff32? off with
  | some (hi20, lo12) => ([Asm.raw (.lui tmp hi20), Asm.add tmp base tmp], lo12)
  | none => (li tmp (BitVec.ofInt 64 off) ++ [Asm.add tmp base tmp], 0#12)

private theorem loadMemOff_eq_pfx (op : LoadOp) (rd base tmp : Reg) (off : Int)
    (hfitsF : fitsImm12Int off = false) :
    loadMemOff op rd base tmp off =
      (memOffPfx base tmp off).1 ++ [Asm.raw (.load op rd tmp (memOffPfx base tmp off).2)] := by
  simp only [loadMemOff, hfitsF, Bool.false_eq_true, ↓reduceIte, memOffPfx]
  cases fitsDoublePos12Int off
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases splitMemOff32? off <;> simp [List.append_assoc]
  · simp

private theorem storeMemOff_eq_pfx (op : StoreOp) (base rs tmp : Reg) (off : Int)
    (hfitsF : fitsImm12Int off = false) :
    storeMemOff op base rs tmp off =
      (memOffPfx base tmp off).1 ++ [Asm.raw (.store op tmp rs (memOffPfx base tmp off).2)] := by
  simp only [storeMemOff, hfitsF, Bool.false_eq_true, ↓reduceIte, memOffPfx]
  cases fitsDoublePos12Int off
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases splitMemOff32? off <;> simp [List.append_assoc]
  · simp

private theorem memOffPfx_correct_lm (lm : LinkModel) {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (base tmp : Reg) (htmp : tmp ≠ 0#5) (hbt : base ≠ tmp) (off : Int)
    (hlink : lm.linkSpec (pre ++ (memOffPfx base tmp off).1 ++ post) = .ok (code, labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (memOffPfx base tmp off).1) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre)) :
    ∃ st', RV64.run rom (lm.totalSize (memOffPfx base tmp off).1) st = .cont st' ∧
      (∀ q, q ≠ tmp → st'.getReg q = st.getReg q) ∧
      st'.getReg tmp + sextImm12 (memOffPfx base tmp off).2 = st.getReg base + BitVec.ofInt 64 off ∧
      st'.mem = st.mem ∧
      st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (memOffPfx base tmp off).1)) := by
  by_cases hdbl : fitsDoublePos12Int off = true
  · have hp : (memOffPfx base tmp off).1 = [Asm.addi tmp base 2047#12] := by simp [memOffPfx, hdbl]
    have hlo : (memOffPfx base tmp off).2 = BitVec.ofInt 12 (off - 2047) := by simp [memOffPfx, hdbl]
    have htw : lm.totalSize (memOffPfx base tmp off).1 = 1 := by rw [hp]; simp [lm.itemSize_instr, Asm.addi]
    rw [htw] at h64 ⊢; rw [hp] at hlink
    have hs := step_item_instr_lm lm hrom pre post (.aluImm .addi tmp base 2047#12) hlink (by omega) st hpc
    refine ⟨stepReg st tmp (st.getReg base + sextImm12 2047#12) (st.pc + 4#64), ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [RV64.run]; rw [hs]; rfl
    · intro q hq; exact getReg_stepReg_ne st tmp q hq _ _
    · rw [hlo, getReg_stepReg_eq st tmp htmp, BitVec.add_assoc, fitsDoublePos12_add off hdbl]
    · exact stepReg_mem st tmp _ _
    · change st.pc + 4#64 = _; exact pc_add_4_ofNat st.pc hpc
  · have hdblF : fitsDoublePos12Int off = false := by revert hdbl; cases fitsDoublePos12Int off <;> simp
    cases hsp : splitMemOff32? off with
    | some p =>
      rcases p with ⟨hi20, lo12⟩
      have hp : (memOffPfx base tmp off).1 = [Asm.raw (.lui tmp hi20), Asm.add tmp base tmp] := by
        simp [memOffPfx, hdblF, hsp]
      have hlo : (memOffPfx base tmp off).2 = lo12 := by simp [memOffPfx, hdblF, hsp]
      have htw : lm.totalSize (memOffPfx base tmp off).1 = 2 := by
        rw [hp]; simp [lm.itemSize_instr, Asm.raw, Asm.add]
      rw [htw] at h64 ⊢; rw [hp] at hlink
      have hlink1 : lm.linkSpec (pre ++ [.instr (.lui tmp hi20)] ++ ([Asm.add tmp base tmp] ++ post)) =
          .ok (code, labels) := by simpa [List.append_assoc, Asm.raw] using hlink
      have hs1 := step_item_instr_lm lm hrom pre ([Asm.add tmp base tmp] ++ post) (.lui tmp hi20)
        hlink1 (by omega) st hpc
      let st1 := stepReg st tmp (sextImmU hi20) (st.pc + 4#64)
      have htw1 : lm.totalSize (pre ++ [.instr (.lui tmp hi20)]) = lm.totalSize pre + 1 := by
        rw [lm.totalSize_append]; simp [lm.itemSize_instr]
      have hpc1 : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ [.instr (.lui tmp hi20)])) := by
        change st.pc + 4#64 = _; rw [htw1]; exact pc_add_4_ofNat st.pc hpc
      have hlink2 : lm.linkSpec ((pre ++ [.instr (.lui tmp hi20)]) ++ [.instr (.alu .add tmp base tmp)] ++ post) =
          .ok (code, labels) := by simpa [List.append_assoc, Asm.raw, Asm.add] using hlink
      have hs2 := step_item_instr_lm lm hrom (pre ++ [.instr (.lui tmp hi20)]) post (.alu .add tmp base tmp)
        hlink2 (by rw [htw1]; omega) st1 hpc1
      let st2 := stepReg st1 tmp (st1.getReg base + st1.getReg tmp) (st1.pc + 4#64)
      refine ⟨st2, ?_, ?_, ?_, ?_, ?_⟩
      · rw [show (2 : Nat) = 1 + 1 from rfl, run_add]; dsimp only [RV64.run]
        rw [hs1]; have : execInstr st (.lui tmp hi20) = .cont st1 := rfl
        rw [this]; dsimp only; rw [hs2]; rfl
      · intro q hq; rw [getReg_stepReg_ne st1 tmp q hq, getReg_stepReg_ne st tmp q hq]
      · rw [hlo, getReg_stepReg_eq st1 tmp htmp, getReg_stepReg_ne st tmp base hbt,
            getReg_stepReg_eq st tmp htmp, BitVec.add_assoc, splitMemOff32_sound hsp]
      · rw [stepReg_mem, stepReg_mem]
      · change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1, htw1, Nat.add_assoc]
    | none =>
      have hp : (memOffPfx base tmp off).1 = li tmp (BitVec.ofInt 64 off) ++ [Asm.add tmp base tmp] := by
        simp [memOffPfx, hdblF, hsp]
      have hlo : (memOffPfx base tmp off).2 = 0#12 := by simp [memOffPfx, hdblF, hsp]
      have htw : lm.totalSize (memOffPfx base tmp off).1 = lm.totalSize (li tmp (BitVec.ofInt 64 off)) + 1 := by
        rw [hp, lm.totalSize_append]; simp [lm.itemSize_instr, Asm.add]
      rw [htw] at h64 ⊢; rw [hp] at hlink
      have hlink0 : lm.linkSpec (pre ++ li tmp (BitVec.ofInt 64 off) ++ ([Asm.add tmp base tmp] ++ post)) =
          .ok (code, labels) := by simpa [List.append_assoc] using hlink
      obtain ⟨st1, hrun0, hoth0, hval0, hmem0, hpc0⟩ :=
        li_correct_lm lm hrom pre ([Asm.add tmp base tmp] ++ post) tmp htmp (BitVec.ofInt 64 off)
          hlink0 (by omega) st hpc
      have htw0 : lm.totalSize (pre ++ li tmp (BitVec.ofInt 64 off)) =
          lm.totalSize pre + lm.totalSize (li tmp (BitVec.ofInt 64 off)) := lm.totalSize_append _ _
      have hpc0' : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ li tmp (BitVec.ofInt 64 off))) := by
        rwa [htw0]
      have hlink1 : lm.linkSpec ((pre ++ li tmp (BitVec.ofInt 64 off)) ++ [.instr (.alu .add tmp base tmp)] ++ post) =
          .ok (code, labels) := by simpa [List.append_assoc, Asm.add] using hlink
      have hs1 := step_item_instr_lm lm hrom (pre ++ li tmp (BitVec.ofInt 64 off)) post (.alu .add tmp base tmp)
        hlink1 (by rw [htw0]; omega) st1 hpc0'
      let st2 := stepReg st1 tmp (st1.getReg base + st1.getReg tmp) (st1.pc + 4#64)
      refine ⟨st2, ?_, ?_, ?_, ?_, ?_⟩
      · rw [run_add, hrun0]; dsimp only [RV64.run]; rw [hs1]; rfl
      · intro q hq; rw [getReg_stepReg_ne st1 tmp q hq, hoth0 q hq]
      · rw [hlo]; have hz : sextImm12 0#12 = 0#64 := rfl
        rw [hz, BitVec.add_zero, getReg_stepReg_eq st1 tmp htmp, hoth0 base hbt, hval0]
      · rw [stepReg_mem, hmem0]
      · change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc0', htw0, Nat.add_assoc]

theorem loadMemOff_ld_correct_lm (lm : LinkModel) {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (rd base tmp : Reg) (hrd : rd ≠ 0#5) (htmp : tmp ≠ 0#5) (hbt : base ≠ tmp) (off : Int)
    (hlink : lm.linkSpec (pre ++ loadMemOff .ld rd base tmp off ++ post) = .ok (code, labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (loadMemOff .ld rd base tmp off)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (halign : isAligned (st.getReg base + BitVec.ofInt 64 off) 8 = true) :
    ∃ st', RV64.run rom (lm.totalSize (loadMemOff .ld rd base tmp off)) st = .cont st' ∧
      (∀ q, q ≠ rd → q ≠ tmp → st'.getReg q = st.getReg q) ∧
      st'.getReg rd = readWord64 st.mem (st.getReg base + BitVec.ofInt 64 off) ∧
      st'.mem = st.mem ∧
      st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (loadMemOff .ld rd base tmp off))) := by
  by_cases hfits : fitsImm12Int off = true
  · have hl : loadMemOff .ld rd base tmp off = [Asm.raw (.load .ld rd base (BitVec.ofInt 12 off))] := by
      simp [loadMemOff, hfits]
    have htw : lm.totalSize (loadMemOff .ld rd base tmp off) = 1 := by
      rw [hl]; simp [lm.itemSize_instr, Asm.raw]
    rw [htw] at h64 ⊢
    rw [hl] at hlink
    have hs := step_item_instr_lm lm hrom pre post (.load .ld rd base (BitVec.ofInt 12 off))
      hlink (by omega) st hpc
    have hal : isAligned (st.getReg base + sextImm12 (BitVec.ofInt 12 off)) 8 = true := by
      rwa [sextImm12_ofInt_fits off hfits]
    refine ⟨stepReg st rd (loadBytes st.mem (st.getReg base + sextImm12 (BitVec.ofInt 12 off)) 8) (st.pc + 4#64),
        ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [RV64.run]; rw [hs]; simp [execInstr, hal, stepReg]
    · intro q hqd _; exact getReg_stepReg_ne st rd q hqd _ _
    · rw [getReg_stepReg_eq st rd hrd, sextImm12_ofInt_fits off hfits]
    · exact stepReg_mem st rd _ _
    · change st.pc + 4#64 = _; exact pc_add_4_ofNat st.pc hpc
  · have hfitsF : fitsImm12Int off = false := by revert hfits; cases fitsImm12Int off <;> simp
    have hl := loadMemOff_eq_pfx .ld rd base tmp off hfitsF
    let pfx := (memOffPfx base tmp off).1
    let lo := (memOffPfx base tmp off).2
    have htw : lm.totalSize (loadMemOff .ld rd base tmp off) = lm.totalSize pfx + 1 := by
      rw [hl, lm.totalSize_append]; simp [lm.itemSize_instr, Asm.raw, pfx]
    rw [htw] at h64 ⊢; rw [hl] at hlink
    have hlink0 : lm.linkSpec (pre ++ pfx ++ ([Asm.raw (.load .ld rd tmp lo)] ++ post)) = .ok (code, labels) := by
      simpa [List.append_assoc, pfx, lo] using hlink
    obtain ⟨st2, hrun0, hoth0, haddr2, hmem0, hpc0⟩ :=
      memOffPfx_correct_lm lm hrom pre ([Asm.raw (.load .ld rd tmp lo)] ++ post)
        base tmp htmp hbt off hlink0 (by dsimp only [pfx] at h64; omega) st hpc
    have htw0 : lm.totalSize (pre ++ pfx) = lm.totalSize pre + lm.totalSize pfx := lm.totalSize_append _ _
    have hpc0' : st2.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ pfx)) := by rwa [htw0]
    have hlink2 : lm.linkSpec ((pre ++ pfx) ++ [.instr (.load .ld rd tmp lo)] ++ post) = .ok (code, labels) := by
      simpa [List.append_assoc, Asm.raw, pfx, lo] using hlink
    have hs2 := step_item_instr_lm lm hrom (pre ++ pfx) post (.load .ld rd tmp lo)
      hlink2 (by rw [htw0]; omega) st2 hpc0'
    have hal2 : isAligned (st2.getReg tmp + sextImm12 lo) 8 = true := by
      dsimp only [lo]; rwa [haddr2]
    let st3 := stepReg st2 rd (loadBytes st2.mem (st2.getReg tmp + sextImm12 lo) 8) (st2.pc + 4#64)
    refine ⟨st3, ?_, ?_, ?_, ?_, ?_⟩
    · rw [run_add, hrun0]; dsimp only [RV64.run]; rw [hs2]; simp [execInstr, hal2, stepReg, st3]
    · intro q hqd hqt; rw [getReg_stepReg_ne st2 rd q hqd, hoth0 q hqt]
    · rw [getReg_stepReg_eq st2 rd hrd]; dsimp only [lo]; rw [haddr2, hmem0]
    · rw [stepReg_mem, hmem0]
    · change st2.pc + 4#64 = _; rw [pc_add_4_ofNat st2.pc hpc0', htw0, Nat.add_assoc]

theorem storeMemOff_sd_correct_lm (lm : LinkModel) {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (base rs tmp : Reg) (htmp : tmp ≠ 0#5) (htb : tmp ≠ base) (htr : tmp ≠ rs) (off : Int)
    (hlink : lm.linkSpec (pre ++ storeMemOff .sd base rs tmp off ++ post) = .ok (code, labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (storeMemOff .sd base rs tmp off)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (halign : isAligned (st.getReg base + BitVec.ofInt 64 off) 8 = true) :
    ∃ st', RV64.run rom (lm.totalSize (storeMemOff .sd base rs tmp off)) st = .cont st' ∧
      (∀ q, q ≠ tmp → st'.getReg q = st.getReg q) ∧
      st'.mem = writeWord64 st.mem (st.getReg base + BitVec.ofInt 64 off) (st.getReg rs) ∧
      st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (storeMemOff .sd base rs tmp off))) := by
  by_cases hfits : fitsImm12Int off = true
  · have hs_asm : storeMemOff .sd base rs tmp off = [Asm.raw (.store .sd base rs (BitVec.ofInt 12 off))] := by
      simp [storeMemOff, hfits]
    have htw : lm.totalSize (storeMemOff .sd base rs tmp off) = 1 := by
      rw [hs_asm]; simp [lm.itemSize_instr, Asm.raw]
    rw [htw] at h64 ⊢; rw [hs_asm] at hlink
    have hs := step_item_instr_lm lm hrom pre post (.store .sd base rs (BitVec.ofInt 12 off))
      hlink (by omega) st hpc
    refine ⟨{ st with pc := st.pc + 4#64, mem := writeWord64 st.mem (st.getReg base + BitVec.ofInt 64 off) (st.getReg rs) },
        ?_, fun _ _ => rfl, rfl, ?_⟩
    · have hexec : execInstr st (.store .sd base rs (BitVec.ofInt 12 off)) =
          .cont { st with pc := st.pc + 4#64, mem := writeWord64 st.mem (st.getReg base + BitVec.ofInt 64 off) (st.getReg rs) } := by
        simp only [execInstr, sextImm12_ofInt_fits off hfits, writeWord64]; rw [halign]; rfl
      dsimp only [RV64.run]; rw [hs, hexec]
    · change st.pc + 4#64 = _; exact pc_add_4_ofNat st.pc hpc
  · have hfitsF : fitsImm12Int off = false := by revert hfits; cases fitsImm12Int off <;> simp
    have hs_asm := storeMemOff_eq_pfx .sd base rs tmp off hfitsF
    let pfx := (memOffPfx base tmp off).1
    let lo := (memOffPfx base tmp off).2
    have htw : lm.totalSize (storeMemOff .sd base rs tmp off) = lm.totalSize pfx + 1 := by
      rw [hs_asm, lm.totalSize_append]; simp [lm.itemSize_instr, Asm.raw, pfx]
    rw [htw] at h64 ⊢; rw [hs_asm] at hlink
    have hlink0 : lm.linkSpec (pre ++ pfx ++ ([Asm.raw (.store .sd tmp rs lo)] ++ post)) = .ok (code, labels) := by
      simpa [List.append_assoc, pfx, lo] using hlink
    obtain ⟨st2, hrun0, hoth0, haddr2, hmem0, hpc0⟩ :=
      memOffPfx_correct_lm lm hrom pre ([Asm.raw (.store .sd tmp rs lo)] ++ post)
        base tmp htmp htb.symm off hlink0 (by dsimp only [pfx] at h64; omega) st hpc
    have htw0 : lm.totalSize (pre ++ pfx) = lm.totalSize pre + lm.totalSize pfx := lm.totalSize_append _ _
    have hpc0' : st2.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ pfx)) := by rwa [htw0]
    have hlink2 : lm.linkSpec ((pre ++ pfx) ++ [.instr (.store .sd tmp rs lo)] ++ post) = .ok (code, labels) := by
      simpa [List.append_assoc, Asm.raw, pfx, lo] using hlink
    have hs2 := step_item_instr_lm lm hrom (pre ++ pfx) post (.store .sd tmp rs lo)
      hlink2 (by rw [htw0]; omega) st2 hpc0'
    have hrs2 : st2.getReg rs = st.getReg rs := hoth0 rs htr.symm
    let st3 : State := { st2 with pc := st2.pc + 4#64, mem := writeWord64 st.mem (st.getReg base + BitVec.ofInt 64 off) (st.getReg rs) }
    refine ⟨st3, ?_, ?_, rfl, ?_⟩
    · rw [run_add, hrun0]; dsimp only [RV64.run]
      have hexec2 : execInstr st2 (.store .sd tmp rs lo) = .cont st3 := by
        dsimp only [execInstr, lo, writeWord64, st3]
        rw [haddr2, hrs2, halign, hmem0]; rfl
      rw [hs2, hexec2]
    · intro q hqt; exact hoth0 q hqt
    · change st2.pc + 4#64 = _; rw [pc_add_4_ofNat st2.pc hpc0', htw0, Nat.add_assoc]

theorem loadMemOff_lbu_correct_lm (lm : LinkModel) {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (rd base tmp : Reg) (hrd : rd ≠ 0#5) (htmp : tmp ≠ 0#5) (hbt : base ≠ tmp) (off : Int)
    (hlink : lm.linkSpec (pre ++ loadMemOff .lbu rd base tmp off ++ post) = .ok (code, labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (loadMemOff .lbu rd base tmp off)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre)) :
    ∃ st', RV64.run rom (lm.totalSize (loadMemOff .lbu rd base tmp off)) st = .cont st' ∧
      (∀ q, q ≠ rd → q ≠ tmp → st'.getReg q = st.getReg q) ∧
      st'.getReg rd = (loadBytes st.mem (st.getReg base + BitVec.ofInt 64 off) 1).zeroExtend 64 ∧
      st'.mem = st.mem ∧
      st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (loadMemOff .lbu rd base tmp off))) := by
  by_cases hfits : fitsImm12Int off = true
  · have hl : loadMemOff .lbu rd base tmp off = [Asm.raw (.load .lbu rd base (BitVec.ofInt 12 off))] := by
      simp [loadMemOff, hfits]
    have htw : lm.totalSize (loadMemOff .lbu rd base tmp off) = 1 := by
      rw [hl]; simp [lm.itemSize_instr, Asm.raw]
    rw [htw] at h64 ⊢; rw [hl] at hlink
    have hs := step_item_instr_lm lm hrom pre post (.load .lbu rd base (BitVec.ofInt 12 off))
      hlink (by omega) st hpc
    refine ⟨stepReg st rd ((loadBytes st.mem (st.getReg base + sextImm12 (BitVec.ofInt 12 off)) 1).zeroExtend 64) (st.pc + 4#64),
        ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [RV64.run]; rw [hs]; simp [execInstr, stepReg]
    · intro q hqd _; exact getReg_stepReg_ne st rd q hqd _ _
    · rw [getReg_stepReg_eq st rd hrd, sextImm12_ofInt_fits off hfits]
    · exact stepReg_mem st rd _ _
    · change st.pc + 4#64 = _; exact pc_add_4_ofNat st.pc hpc
  · have hfitsF : fitsImm12Int off = false := by revert hfits; cases fitsImm12Int off <;> simp
    have hl := loadMemOff_eq_pfx .lbu rd base tmp off hfitsF
    let pfx := (memOffPfx base tmp off).1
    let lo := (memOffPfx base tmp off).2
    have htw : lm.totalSize (loadMemOff .lbu rd base tmp off) = lm.totalSize pfx + 1 := by
      rw [hl, lm.totalSize_append]; simp [lm.itemSize_instr, Asm.raw, pfx]
    rw [htw] at h64 ⊢; rw [hl] at hlink
    have hlink0 : lm.linkSpec (pre ++ pfx ++ ([Asm.raw (.load .lbu rd tmp lo)] ++ post)) = .ok (code, labels) := by
      simpa [List.append_assoc, pfx, lo] using hlink
    obtain ⟨st2, hrun0, hoth0, haddr2, hmem0, hpc0⟩ :=
      memOffPfx_correct_lm lm hrom pre ([Asm.raw (.load .lbu rd tmp lo)] ++ post)
        base tmp htmp hbt off hlink0 (by dsimp only [pfx] at h64; omega) st hpc
    have htw0 : lm.totalSize (pre ++ pfx) = lm.totalSize pre + lm.totalSize pfx := lm.totalSize_append _ _
    have hpc0' : st2.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ pfx)) := by rwa [htw0]
    have hlink2 : lm.linkSpec ((pre ++ pfx) ++ [.instr (.load .lbu rd tmp lo)] ++ post) = .ok (code, labels) := by
      simpa [List.append_assoc, Asm.raw, pfx, lo] using hlink
    have hs2 := step_item_instr_lm lm hrom (pre ++ pfx) post (.load .lbu rd tmp lo)
      hlink2 (by rw [htw0]; omega) st2 hpc0'
    let st3 := stepReg st2 rd ((loadBytes st2.mem (st2.getReg tmp + sextImm12 lo) 1).zeroExtend 64) (st2.pc + 4#64)
    refine ⟨st3, ?_, ?_, ?_, ?_, ?_⟩
    · rw [run_add, hrun0]; dsimp only [RV64.run]; rw [hs2]; simp [execInstr, stepReg, st3]
    · intro q hqd hqt; rw [getReg_stepReg_ne st2 rd q hqd, hoth0 q hqt]
    · rw [getReg_stepReg_eq st2 rd hrd]; dsimp only [lo]; rw [haddr2, hmem0]
    · rw [stepReg_mem, hmem0]
    · change st2.pc + 4#64 = _; rw [pc_add_4_ofNat st2.pc hpc0', htw0, Nat.add_assoc]

theorem exec_instr_list {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem) (is : List Instr)
    (hlink : linkResolved (pre ++ is.map .instr ++ post) = .ok (code, labels))
    (h64 : 4 * (totalWords pre + is.length) < 2 ^ 64)
    (stepFn : State → Instr → State)
    (hstepFn : ∀ s inst, inst ∈ is →
      execInstr s inst = .cont (stepFn s inst) ∧ (stepFn s inst).pc = s.pc + 4#64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * totalWords pre)) :
    RV64.run rom is.length st = .cont (is.foldl stepFn st) ∧
      (is.foldl stepFn st).pc = BitVec.ofNat 64 (4 * (totalWords pre + is.length)) := by
  rw [← near_totalSize_eq] at h64 hpc ⊢
  exact exec_instr_list_lm nearLinkModel hrom pre post is hlink h64 stepFn hstepFn st hpc

theorem exec_rd_ops {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (rd : Reg) (hrd : rd ≠ 0#5) (ops : List (Instr × (Word → Word)))
    (hlink : linkResolved (pre ++ (ops.map (fun p => AsmItem.instr p.1)) ++ post) = .ok (code, labels))
    (h64 : 4 * (totalWords pre + ops.length) < 2 ^ 64)
    (hops : ∀ s i f, (i, f) ∈ ops →
      execInstr s i = .cont (stepReg s rd (f (s.getReg rd)) (s.pc + 4#64)))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * totalWords pre)) :
    ∃ st', RV64.run rom ops.length st = .cont st' ∧
      (∀ q, q ≠ rd → st'.getReg q = st.getReg q) ∧
      st'.getReg rd = ops.foldl (fun v p => p.2 v) (st.getReg rd) ∧
      st'.mem = st.mem ∧
      st'.pc = BitVec.ofNat 64 (4 * (totalWords pre + ops.length)) := by
  rw [← near_totalSize_eq] at h64 hpc ⊢
  exact exec_rd_ops_lm nearLinkModel hrom pre post rd hrd ops hlink h64 hops st hpc

theorem li32Instrs_eval {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (rd : Reg) (hrd : rd ≠ 0#5) (w32 : BitVec 32)
    (hlink : linkResolved (pre ++ (li32Instrs rd w32).map .instr ++ post) = .ok (code, labels))
    (h64 : 4 * (totalWords pre + (li32Instrs rd w32).length) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * totalWords pre)) :
    ∃ st', RV64.run rom (li32Instrs rd w32).length st = .cont st' ∧
      (∀ q, q ≠ rd → st'.getReg q = st.getReg q) ∧
      st'.getReg rd = w32.signExtend 64 ∧
      st'.mem = st.mem ∧
      st'.pc = BitVec.ofNat 64 (4 * (totalWords pre + (li32Instrs rd w32).length)) := by
  rw [← near_totalSize_eq] at h64 hpc ⊢
  exact li32Instrs_eval_lm nearLinkModel hrom pre post rd hrd w32 hlink h64 st hpc

theorem li_correct {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (rd : Reg) (hrd : rd ≠ 0#5) (w : BitVec 64)
    (hlink : linkResolved (pre ++ li rd w ++ post) = .ok (code, labels))
    (h64 : 4 * (totalWords pre + totalWords (li rd w)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * totalWords pre)) :
    ∃ st', RV64.run rom (totalWords (li rd w)) st = .cont st' ∧
      (∀ q, q ≠ rd → st'.getReg q = st.getReg q) ∧
      st'.getReg rd = w ∧
      st'.mem = st.mem ∧
      st'.pc = BitVec.ofNat 64 (4 * (totalWords pre + totalWords (li rd w))) := by
  simp only [← near_totalSize_eq] at h64 hpc ⊢
  exact li_correct_lm nearLinkModel hrom pre post rd hrd w hlink h64 st hpc

theorem addImmOff_correct {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (rd rs tmp : Reg) (hrd : rd ≠ 0#5) (htmp : tmp ≠ 0#5) (htr : tmp ≠ rs) (off : Int)
    (hlink : linkResolved (pre ++ addImmOff rd rs tmp off ++ post) = .ok (code, labels))
    (h64 : 4 * (totalWords pre + totalWords (addImmOff rd rs tmp off)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * totalWords pre)) :
    ∃ st', RV64.run rom (totalWords (addImmOff rd rs tmp off)) st = .cont st' ∧
      (∀ q, q ≠ rd → q ≠ tmp → st'.getReg q = st.getReg q) ∧
      st'.getReg rd = st.getReg rs + BitVec.ofInt 64 off ∧
      st'.mem = st.mem ∧
      st'.pc = BitVec.ofNat 64 (4 * (totalWords pre + totalWords (addImmOff rd rs tmp off))) := by
  simp only [← near_totalSize_eq] at h64 hpc ⊢
  exact addImmOff_correct_lm nearLinkModel hrom pre post rd rs tmp hrd htmp htr off hlink h64 st hpc

theorem loadMemOff_ld_correct {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (rd base tmp : Reg) (hrd : rd ≠ 0#5) (htmp : tmp ≠ 0#5) (hbt : base ≠ tmp) (off : Int)
    (hlink : linkResolved (pre ++ loadMemOff .ld rd base tmp off ++ post) = .ok (code, labels))
    (h64 : 4 * (totalWords pre + totalWords (loadMemOff .ld rd base tmp off)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * totalWords pre))
    (halign : isAligned (st.getReg base + BitVec.ofInt 64 off) 8 = true) :
    ∃ st', RV64.run rom (totalWords (loadMemOff .ld rd base tmp off)) st = .cont st' ∧
      (∀ q, q ≠ rd → q ≠ tmp → st'.getReg q = st.getReg q) ∧
      st'.getReg rd = readWord64 st.mem (st.getReg base + BitVec.ofInt 64 off) ∧
      st'.mem = st.mem ∧
      st'.pc = BitVec.ofNat 64 (4 * (totalWords pre + totalWords (loadMemOff .ld rd base tmp off))) := by
  simp only [← near_totalSize_eq] at h64 hpc ⊢
  exact loadMemOff_ld_correct_lm nearLinkModel hrom pre post rd base tmp hrd htmp hbt off hlink h64 st hpc halign

theorem storeMemOff_sd_correct {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (base rs tmp : Reg) (htmp : tmp ≠ 0#5) (htb : tmp ≠ base) (htr : tmp ≠ rs) (off : Int)
    (hlink : linkResolved (pre ++ storeMemOff .sd base rs tmp off ++ post) = .ok (code, labels))
    (h64 : 4 * (totalWords pre + totalWords (storeMemOff .sd base rs tmp off)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * totalWords pre))
    (halign : isAligned (st.getReg base + BitVec.ofInt 64 off) 8 = true) :
    ∃ st', RV64.run rom (totalWords (storeMemOff .sd base rs tmp off)) st = .cont st' ∧
      (∀ q, q ≠ tmp → st'.getReg q = st.getReg q) ∧
      st'.mem = writeWord64 st.mem (st.getReg base + BitVec.ofInt 64 off) (st.getReg rs) ∧
      st'.pc = BitVec.ofNat 64 (4 * (totalWords pre + totalWords (storeMemOff .sd base rs tmp off))) := by
  simp only [← near_totalSize_eq] at h64 hpc ⊢
  exact storeMemOff_sd_correct_lm nearLinkModel hrom pre post base rs tmp htmp htb htr off hlink h64 st hpc halign

theorem loadMemOff_lbu_correct {rom : Rom} {code : Array (BitVec 32)} {labels : LabelMap}
    (hrom : RomMatchesCode rom code) (pre post : List AsmItem)
    (rd base tmp : Reg) (hrd : rd ≠ 0#5) (htmp : tmp ≠ 0#5) (hbt : base ≠ tmp) (off : Int)
    (hlink : linkResolved (pre ++ loadMemOff .lbu rd base tmp off ++ post) = .ok (code, labels))
    (h64 : 4 * (totalWords pre + totalWords (loadMemOff .lbu rd base tmp off)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * totalWords pre)) :
    ∃ st', RV64.run rom (totalWords (loadMemOff .lbu rd base tmp off)) st = .cont st' ∧
      (∀ q, q ≠ rd → q ≠ tmp → st'.getReg q = st.getReg q) ∧
      st'.getReg rd = (loadBytes st.mem (st.getReg base + BitVec.ofInt 64 off) 1).zeroExtend 64 ∧
      st'.mem = st.mem ∧
      st'.pc = BitVec.ofNat 64 (4 * (totalWords pre + totalWords (loadMemOff .lbu rd base tmp off))) := by
  simp only [← near_totalSize_eq] at h64 hpc ⊢
  exact loadMemOff_lbu_correct_lm nearLinkModel hrom pre post rd base tmp hrd htmp hbt off hlink h64 st hpc

/-- info: 'ConAgua.RISCV.Compiler.li_correct_lm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms li_correct_lm

/-- info: 'ConAgua.RISCV.Compiler.loadMemOff_ld_correct_lm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loadMemOff_ld_correct_lm

/-- info: 'ConAgua.RISCV.Compiler.storeMemOff_sd_correct_lm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms storeMemOff_sd_correct_lm

/-- info: 'ConAgua.RISCV.Compiler.li_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms li_correct

/-- info: 'ConAgua.RISCV.Compiler.loadMemOff_ld_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loadMemOff_ld_correct

/-- info: 'ConAgua.RISCV.Compiler.storeMemOff_sd_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms storeMemOff_sd_correct

end ConAgua.RISCV.Compiler
