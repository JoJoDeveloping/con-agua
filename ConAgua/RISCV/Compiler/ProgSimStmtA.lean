import ConAgua.RISCV.Compiler.ProgSimExpr
import ConAgua.RISCV.Compiler.ProgSimFuel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Program Statement Simulation Helpers Part A (`ConAgua.RISCV.Compiler.ProgSimStmtA`)

First half of Section 6b statement and function simulation helpers.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard Lean axioms only.
-/

namespace ConAgua.RISCV.Compiler

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Linker

/-! ## Section 6b: Program Statement & Function Simulation Helpers -/

section ProgStmtHelpers

/-- Any sub-slice inside a linked program satisfies the 64-bit PC bound. -/
theorem linkResolved_sub_pc64 {lkm : LinkModel} (env : CodeEnvGen lkm) (pre mid post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ mid ++ post) = .ok (env.code, env.labels)) :
    4 * (lkm.totalSize pre + lkm.totalSize mid) < 2 ^ 64 :=
  LinkModel.CodeAt.sub_pc64 env.hcode64 (LinkModel.CodeAt.of_link hlink)

/-- Single `linkSpec` associativity helper for `pre ++ (a ++ b) ++ post`. -/
theorem linkResolved_mid_split (lkm : LinkModel) {code : Array (BitVec 32)} {labels : LabelMap}
    (pre a b post : List AsmItem)
    (h : lkm.linkSpec (pre ++ (a ++ b) ++ post) = .ok (code, labels)) :
    lkm.linkSpec (pre ++ a ++ (b ++ post)) = .ok (code, labels) ∧
    lkm.linkSpec ((pre ++ a) ++ b ++ post) = .ok (code, labels) :=
  LinkModel.CodeAt.mid_split (LinkModel.CodeAt.of_link h)

theorem getReg_setReg_eq (st : State) (r : Reg) (v : RV64.Word) (hr : r ≠ 0#5) :
    (st.setReg r v).getReg r = v := by
  have hbeq : (r == 0#5) = false := beq_false_of_ne hr
  simp [State.getReg, State.setReg, hbeq]

theorem getReg_setReg_ne (st : State) (r q : Reg) (v : RV64.Word) (hrq : q ≠ r) :
    (st.setReg r v).getReg q = st.getReg q := by
  by_cases hr : r == 0#5
  · simp [State.setReg, hr]
  · by_cases hq : q == 0#5
    · simp [State.getReg, hq]
    · simp only [State.getReg, State.setReg, hr, hq, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
      split
      · next h => exact absurd h hrq
      · rfl

theorem setReg_mem (st : State) (r : Reg) (v : RV64.Word) :
    (st.setReg r v).mem = st.mem := by
  by_cases hr : r == 0#5 <;> simp [State.setReg, hr]

theorem resReg_ne_zero (i : Nat) : resReg i ≠ 0#5 := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => decide
  | _ + 7 => simp [resReg]; decide

theorem BitVec.ofNat_sub_one_eq_add_neg1 {n : Nat} (hn : n + 1 < 2 ^ 64) :
    BitVec.ofNat 64 (n + 1) + BitVec.signExtend 64 (-1#12) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (BitVec.ofNat 64 (n + 1)).toNat = n + 1 := Nat.mod_eq_of_lt hn
  have h2 : (BitVec.signExtend 64 (-1#12)).toNat = 2 ^ 64 - 1 := by decide
  rw [BitVec.toNat_add, h1, h2]
  simp only [BitVec.toNat_ofNat]
  omega

theorem BitVec.ofNat_ne_zero_of_lt {n : Nat} (hn0 : 0 < n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro h
  have h' := congrArg BitVec.toNat h
  simp [Nat.mod_eq_of_lt hn] at h'
  omega

theorem resReg_ne_preserved (i : Nat) :
    resReg i ≠ AbiReg.gp ∧ resReg i ≠ AbiReg.sp ∧ resReg i ≠ AbiReg.s0 ∧
    resReg i ≠ AbiReg.s1 ∧ resReg i ≠ AbiReg.s2 ∧ resReg i ≠ AbiReg.t0 ∧
    resReg i ≠ AbiReg.t1 ∧ resReg i ≠ AbiReg.t2 := by
  match i with
  | 0 => decide | 1 => decide | 2 => decide | 3 => decide
  | 4 => decide | 5 => decide | 6 => decide
  | _ + 7 => simp [resReg]; decide

theorem resReg_inj {i j : Nat} (hi : i < maxRes) (hj : j < maxRes) (hij : i ≠ j) :
    resReg i ≠ resReg j := by
  have hi8 : i < 8 := hi
  have hj8 : j < 8 := hj
  match i, j with
  | 0, 0 => exact absurd rfl hij | 1, 1 => exact absurd rfl hij
  | 2, 2 => exact absurd rfl hij | 3, 3 => exact absurd rfl hij
  | 4, 4 => exact absurd rfl hij | 5, 5 => exact absurd rfl hij
  | 6, 6 => exact absurd rfl hij | 7, 7 => exact absurd rfl hij
  | 0, 1 | 0, 2 | 0, 3 | 0, 4 | 0, 5 | 0, 6 | 0, 7
  | 1, 0 | 1, 2 | 1, 3 | 1, 4 | 1, 5 | 1, 6 | 1, 7
  | 2, 0 | 2, 1 | 2, 3 | 2, 4 | 2, 5 | 2, 6 | 2, 7
  | 3, 0 | 3, 1 | 3, 2 | 3, 4 | 3, 5 | 3, 6 | 3, 7
  | 4, 0 | 4, 1 | 4, 2 | 4, 3 | 4, 5 | 4, 6 | 4, 7
  | 5, 0 | 5, 1 | 5, 2 | 5, 3 | 5, 4 | 5, 6 | 5, 7
  | 6, 0 | 6, 1 | 6, 2 | 6, 3 | 6, 4 | 6, 5 | 6, 7
  | 7, 0 | 7, 1 | 7, 2 | 7, 3 | 7, 4 | 7, 5 | 7, 6 => decide
  | _ + 8, _ => omega
  | _, _ + 8 => omega

theorem step_sw_zero {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (rs1 rs2 : Reg)
    (hlink : lkm.linkSpec (pre ++ [Asm.sw rs1 rs2] ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hal : isAligned (st.getReg rs1) 4 = true) :
    let st' : State :=
      { pc := BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1))
      , regs := st.regs
      , mem := storeBytes st.mem (st.getReg rs1) 4 (BitVec.extractLsb' 0 32 (st.getReg rs2)) }
    RV64.run env.rom 1 st = .cont st' := by
  have hpc64 := linkResolved_sub_pc64 env pre [Asm.sw rs1 rs2] post hlink
  have htw : lkm.totalSize [Asm.sw rs1 rs2] = 1 := by simp only [Asm.sw, lkm.totalSize_instr]
  have hlt : 4 * lkm.totalSize pre < 2 ^ 64 := by rw [htw] at hpc64; omega
  have hstep := step_item_instr_lm lkm env.hrom pre post (.store .sw rs1 rs2 0#12) hlink hlt st hpc
  have hs0 : st.getReg rs1 + sextImm12 0#12 = st.getReg rs1 := by
    have : sextImm12 0#12 = 0#64 := by decide
    rw [this]; simp
  apply run_one_cont
  rw [hstep]
  simp only [execInstr, hs0, hal, ↓reduceIte, pc_add_4_ofNat st.pc hpc]

theorem step_sd_zero {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (rs1 rs2 : Reg)
    (hlink : lkm.linkSpec (pre ++ [Asm.sd rs1 rs2] ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hal : isAligned (st.getReg rs1) 8 = true) :
    let st' : State :=
      { pc := BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1))
      , regs := st.regs
      , mem := writeWord64 st.mem (st.getReg rs1) (st.getReg rs2) }
    RV64.run env.rom 1 st = .cont st' := by
  have hpc64 := linkResolved_sub_pc64 env pre [Asm.sd rs1 rs2] post hlink
  have htw : lkm.totalSize [Asm.sd rs1 rs2] = 1 := by simp only [Asm.sd, lkm.totalSize_instr]
  have hlt : 4 * lkm.totalSize pre < 2 ^ 64 := by rw [htw] at hpc64; omega
  have hstep := step_item_instr_lm lkm env.hrom pre post (.store .sd rs1 rs2 0#12) hlink hlt st hpc
  have hs0 : st.getReg rs1 + sextImm12 0#12 = st.getReg rs1 := by
    have : sextImm12 0#12 = 0#64 := by decide
    rw [this]; simp
  apply run_one_cont
  rw [hstep]
  simp only [execInstr, hs0, hal, ↓reduceIte, pc_add_4_ofNat st.pc hpc, writeWord64]

theorem step_ld_zero {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (rd rs1 : Reg)
    (hlink : lkm.linkSpec (pre ++ [Asm.ld rd rs1] ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hal : isAligned (st.getReg rs1) 8 = true) :
    RV64.run env.rom 1 st =
      .cont (stepReg st rd (readWord64 st.mem (st.getReg rs1))
        (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))) := by
  have hpc64 := linkResolved_sub_pc64 env pre [Asm.ld rd rs1] post hlink
  have htw : lkm.totalSize [Asm.ld rd rs1] = 1 := by simp only [Asm.ld, lkm.totalSize_instr]
  have hlt : 4 * lkm.totalSize pre < 2 ^ 64 := by rw [htw] at hpc64; omega
  have hstep := step_item_instr_lm lkm env.hrom pre post (.load .ld rd rs1 0#12) hlink hlt st hpc
  have hs0 : st.getReg rs1 + sextImm12 0#12 = st.getReg rs1 := by
    have : sextImm12 0#12 = 0#64 := by decide
    rw [this]; simp
  apply run_one_cont
  rw [hstep]
  simp only [execInstr, hs0, hal, ↓reduceIte, pc_add_4_ofNat st.pc hpc, stepReg, readWord64]

theorem step_lbu_zero {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (rd rs1 : Reg)
    (hlink : lkm.linkSpec (pre ++ [Asm.lbu rd rs1] ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre)) :
    RV64.run env.rom 1 st =
      .cont (stepReg st rd (BitVec.zeroExtend 64 (st.mem (st.getReg rs1)))
        (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))) := by
  have hpc64 := linkResolved_sub_pc64 env pre [Asm.lbu rd rs1] post hlink
  have htw : lkm.totalSize [Asm.lbu rd rs1] = 1 := by simp only [Asm.lbu, lkm.totalSize_instr]
  have hlt : 4 * lkm.totalSize pre < 2 ^ 64 := by rw [htw] at hpc64; omega
  have hstep := step_item_instr_lm lkm env.hrom pre post (.load .lbu rd rs1 0#12) hlink hlt st hpc
  have hs0 : st.getReg rs1 + sextImm12 0#12 = st.getReg rs1 := by
    have : sextImm12 0#12 = 0#64 := by decide
    rw [this]; simp
  apply run_one_cont
  rw [hstep]
  simp only [execInstr, hs0, pc_add_4_ofNat st.pc hpc, stepReg, loadBytes_one]

theorem isAligned4_of_base64_add4 {tab : Tab} (L : ProgLayout tab) (s : TieredArray)
    (i : _root_.L.Word) :
    isAligned (L.base64 s + BitVec.ofNat 64 (4 * i.toNat)) 4 = true :=
  isAligned4_add_mul4 _ (L.h64Align s) i.toNat

theorem isAligned8_of_resOff {tab : Tab} (L : ProgLayout tab) {i : Nat}
    (hi : maxRes ≤ i) (_hil : i < tab.nres) :
    isAligned (L.T + BitVec.ofInt 64 (tab.resOff i)) 8 = true := by
  have hres : tab.resOff i = ↑(tab.resBase.toNat + 8 * (i - maxRes)) := by
    have hnn := ProgLayout.resBase_nonneg tab
    simp only [Tab.resOff]
    omega
  rw [hres]
  have heq : BitVec.ofInt 64 ↑(tab.resBase.toNat + 8 * (i - maxRes)) =
      BitVec.ofNat 64 (tab.resBase.toNat + 8 * (i - maxRes)) := rfl
  rw [heq]
  have hrb : ∃ k, tab.resBase.toNat = 8 * k := by
    refine ⟨2 + 3 * (tab.nb + tab.nw) + tab.romWords, ?_⟩
    simp only [Tab.resBase, Tab.romBase]
    omega
  obtain ⟨k, hk⟩ := hrb
  rw [hk, show 8 * k + 8 * (i - maxRes) = 8 * (k + (i - maxRes)) by omega]
  exact isAligned8_add_mul8 L.T L.hTAlign _

theorem isAligned8_of_globOff {tab : Tab} (L : ProgLayout tab) (g : _root_.L.GVar) :
    isAligned (L.T + BitVec.ofInt 64 (tab.globOff g)) 8 = true := by
  have hrb : ∃ k : Nat, tab.globOff g = ↑(8 * k) := by
    refine ⟨2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres + g.id, ?_⟩
    simp [Tab.globOff, Tab.globBase, Tab.resBase, Tab.romBase]
    omega
  obtain ⟨k, hk⟩ := hrb
  rw [hk]
  exact isAligned8_add_mul8 L.T L.hTAlign k

def ProgLayout.resOnlySpan {tab : Tab} (L : ProgLayout tab) : MemSpan :=
  { base := L.T + BitVec.ofNat 64 tab.resBase.toNat, size := 8 * tab.nxres }

theorem resOnlySpan_sub_resGlob {tab : Tab} (L : ProgLayout tab) :
    L.resOnlySpan.sub L.resGlobSpan :=
  fun _ ⟨k, hk, heq⟩ => ⟨k, by simp only [ProgLayout.resOnlySpan] at hk; simp only [ProgLayout.resGlobSpan]; omega, heq⟩

theorem resOnlySpan_contains_resOff {tab : Tab} (L : ProgLayout tab) {i : Nat}
    (hi : maxRes ≤ i) (hil : i < tab.nres) {k : Nat} (hk : k < 8) :
    L.resOnlySpan.contains (L.T + BitVec.ofInt 64 (tab.resOff i) + BitVec.ofNat 64 k) := by
  have hrb : tab.resBase.toNat + 8 * (i - maxRes) + 8 ≤ L.tabBytes := L.tab_resOff_bound hi hil
  have ht := L.hTValid
  have hnn := ProgLayout.resBase_nonneg tab
  have hres : tab.resOff i = ↑(tab.resBase.toNat + 8 * (i - maxRes)) := by
    simp only [Tab.resOff]; omega
  rw [hres]
  refine ⟨8 * (i - maxRes) + k, ?_, ?_⟩
  · have hnx : i - maxRes < tab.nxres := by simp only [Tab.nxres]; omega
    simp only [ProgLayout.resOnlySpan]; omega
  · simp only [ProgLayout.resOnlySpan]
    apply BitVec.eq_of_toNat_eq
    have hsum : tab.resBase.toNat + (8 * (i - maxRes) + k) < 2 ^ 64 := by omega
    have h2 : (BitVec.ofInt 64 ↑(tab.resBase.toNat + 8 * (i - maxRes))).toNat =
        tab.resBase.toNat + 8 * (i - maxRes) := by
      change (BitVec.ofNat 64 _).toNat = _; exact Nat.mod_eq_of_lt (by omega)
    have h3 : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
    have h1 : (BitVec.ofNat 64 tab.resBase.toNat).toNat = tab.resBase.toNat :=
      Nat.mod_eq_of_lt (by omega)
    have h4 : (BitVec.ofNat 64 (8 * (i - maxRes) + k)).toNat = 8 * (i - maxRes) + k :=
      Nat.mod_eq_of_lt (by omega)
    have hL : BitVec.ofInt 64 ↑(tab.resBase.toNat + 8 * (i - maxRes)) + BitVec.ofNat 64 k =
        BitVec.ofNat 64 tab.resBase.toNat + BitVec.ofNat 64 (8 * (i - maxRes) + k) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_add, h1, h2, h3, h4,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    rw [BitVec.add_assoc, BitVec.add_assoc, hL]

theorem resGlobSpan_contains_resOff {tab : Tab} (L : ProgLayout tab) {i : Nat}
    (hi : maxRes ≤ i) (hil : i < tab.nres) {k : Nat} (hk : k < 8) :
    L.resGlobSpan.contains (L.T + BitVec.ofInt 64 (tab.resOff i) + BitVec.ofNat 64 k) :=
  resOnlySpan_sub_resGlob L _ (resOnlySpan_contains_resOff L hi hil hk)

theorem tab_offset_not_in_resOnly {tab : Tab} (L : ProgLayout tab)
    {off : Nat} (hoff : off < tab.resBase.toNat ∨ tab.resBase.toNat + 8 * tab.nxres ≤ off)
    (hoffB : off < L.tabBytes) :
    ¬L.resOnlySpan.contains (L.T + BitVec.ofNat 64 off) := by
  intro ⟨j, hj, heq⟩
  simp only [ProgLayout.resOnlySpan] at hj heq
  have hrb : tab.resBase.toNat + 8 * tab.nxres ≤ L.tabBytes := by
    have : tab.resBase.toNat = 8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords) := by
      simp [Tab.resBase, Tab.romBase]; omega
    have hgb : tab.globBase.toNat ≤ L.tabBytes := by
      have hm := L.hTabMin
      have harg : tab.args = tab.globBase + 8 * ↑tab.ng := rfl
      have : tab.globBase = ↑(tab.resBase.toNat + 8 * tab.nxres) := by
        simp [Tab.globBase, Tab.resBase, Tab.romBase]; omega
      omega
    have : tab.globBase = ↑(tab.resBase.toNat + 8 * tab.nxres) := by
      simp [Tab.globBase, Tab.resBase, Tab.romBase]; omega
    omega
  have ht := L.hTValid
  rw [BitVec.add_assoc] at heq
  have hnat := congrArg BitVec.toNat heq
  have h1 : (BitVec.ofNat 64 tab.resBase.toNat + BitVec.ofNat 64 j).toNat = tab.resBase.toNat + j := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, BitVec.toNat_add, h1, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hnat
  omega

theorem ProgMemRel.of_resOnly {tab : Tab} (L : ProgLayout tab)
    {m1 m2 : ByteMem} {lm : _root_.L.Mem}
    (hm : MemEqOutside L.resOnlySpan m1 m2) (hrel : ProgMemRel tab L m1 lm) :
    ProgMemRel tab L m2 lm := by
  have hsubTab : L.resOnlySpan.sub L.tabSpan := MemSpan.sub_trans (resOnlySpan_sub_resGlob L) L.resGlob_sub_tab
  have hnot8 : ∀ a, tab.bytePosOkB a = true → ∀ i, i < (lm.arr8 a).size →
      ¬L.resOnlySpan.contains (L.base8 a + BitVec.ofNat 64 i) := by
    intro a ha i hi hc
    have hcap := Nat.lt_of_lt_of_le hi (hrel.1 a ha).1
    exact MemSpan.disjoint_to_memDisjoint L.tabSpan_valid (L.arr8Span_valid a) (L.h8DisjTab a ha).symm
      _ (hsubTab _ hc) ⟨i, hcap, rfl⟩
  have hnot64 : ∀ s, tab.wordPosOkB s = true → ∀ i, i < (lm.arr64 s).size → ∀ k, k < 8 →
      ¬L.resOnlySpan.contains (L.base64 s + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 k) := by
    intro s hs i hi k hk hc
    have hcap := Nat.lt_of_lt_of_le hi (hrel.2.1 s hs).1
    exact MemSpan.disjoint_to_memDisjoint L.tabSpan_valid (L.arr64Span_valid s) (L.h64DisjTab s hs).symm
      _ (hsubTab _ hc) ⟨8 * i + k, by simp only [ProgLayout.arr64Span]; omega,
        by simp [ProgLayout.arr64Span, BitVec.add_assoc, ← BitVec.ofNat_add]⟩
  have hresB_add : ∀ k < tab.resBase.toNat, k + 8 ≤ tab.resBase.toNat → ∀ j < 8,
      ¬L.resOnlySpan.contains (L.T + BitVec.ofNat 64 k + BitVec.ofNat 64 j) := by
    intro k hk hle j hj
    have hrb : tab.resBase.toNat ≤ L.tabBytes := by
      have : tab.resBase.toNat = 8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords) := by
        simp [Tab.resBase, Tab.romBase]; omega
      have harg : tab.args = tab.globBase + 8 * ↑tab.ng := rfl
      have hm2 := L.hTabMin
      simp only [Tab.args, Tab.globBase, Tab.resBase, Tab.romBase] at hm2
      omega
    rw [BitVec.add_assoc, show BitVec.ofNat 64 k + BitVec.ofNat 64 j = BitVec.ofNat 64 (k + j) by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]]
    exact tab_offset_not_in_resOnly L (Or.inl (by omega)) (by omega)
  refine ⟨fun a ha => ?_, fun s hs => ?_, fun k hk => ?_, fun g hg => ?_⟩
  · refine ⟨(hrel.1 a ha).1, (hrel.1 a ha).2.1, ?_, ?_, fun i hi => ?_⟩
    · rw [← (hrel.1 a ha).2.2.1]
      rw [Tab.len8_eq_nat]
      apply MemEqOutside.readWord64_eq hm
      intro j hj
      have hb := L.tab_len8_bound ha
      have hrb : 8 * (2 + (tab.nb + tab.nw) + tab.pos8 a) + 8 ≤ tab.resBase.toNat := by
        have hlt := Tab.bytePosOk_lt ha
        simp [Tab.resBase, Tab.romBase]; omega
      exact hresB_add _ (by omega) (by omega) j hj
    · rw [← (hrel.1 a ha).2.2.2.1]
      rw [Tab.base8_eq_nat]
      apply MemEqOutside.readWord64_eq hm
      intro j hj
      have hrb : 8 * (2 + tab.pos8 a) + 8 ≤ tab.resBase.toNat := by
        have hlt := Tab.bytePosOk_lt ha
        simp [Tab.resBase, Tab.romBase]; omega
      exact hresB_add _ (by omega) (by omega) j hj
    · rw [← (hrel.1 a ha).2.2.2.2 i hi]
      exact hm _ (hnot8 a ha i hi)
  · refine ⟨(hrel.2.1 s hs).1, (hrel.2.1 s hs).2.1, ?_, ?_, fun i hi => ?_⟩
    · rw [← (hrel.2.1 s hs).2.2.1]
      rw [Tab.len64_eq_nat]
      apply MemEqOutside.readWord64_eq hm
      intro j hj
      have hrb : 8 * (2 + (tab.nb + tab.nw) + tab.pos64 s) + 8 ≤ tab.resBase.toNat := by
        have hlt := Tab.wordPosOk_lt hs
        simp [Tab.resBase, Tab.romBase]; omega
      exact hresB_add _ (by omega) (by omega) j hj
    · rw [← (hrel.2.1 s hs).2.2.2.1]
      rw [Tab.base64_eq_nat]
      apply MemEqOutside.readWord64_eq hm
      intro j hj
      have hrb : 8 * (2 + tab.pos64 s) + 8 ≤ tab.resBase.toNat := by
        have hlt := Tab.wordPosOk_lt hs
        simp [Tab.resBase, Tab.romBase]; omega
      exact hresB_add _ (by omega) (by omega) j hj
    · rw [← (hrel.2.1 s hs).2.2.2.2 i hi]
      exact MemEqOutside.readWord64_eq hm _ (hnot64 s hs i hi)
  · rw [← hrel.2.2.1 k hk]
    have hb := L.tab_rom_bound
    have hnn := ProgLayout.resBase_nonneg tab
    have hrb : tab.romBase.toNat + k < tab.resBase.toNat := by
      have : tab.romBase.toNat = 16 + 24 * (tab.nb + tab.nw) := by simp [Tab.romBase]; omega
      have hle : tab.rom.length ≤ 8 * tab.romWords := by
        simp [Tab.romWords]; omega
      have : tab.resBase.toNat = tab.romBase.toNat + 8 * tab.romWords := by
        simp [Tab.resBase, Tab.romBase]; omega
      omega
    exact hm _ (tab_offset_not_in_resOnly L (Or.inl hrb) (by omega))
  · rw [← hrel.2.2.2 g hg]
    rw [Tab.globOff_eq_nat]
    apply MemEqOutside.readWord64_eq hm
    intro j hj
    have hgb := L.tab_globOff_bound g hg
    have hrb : tab.resBase.toNat + 8 * tab.nxres ≤ 8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres + g.id) + j := by
      have : tab.resBase.toNat = 8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords) := by
        simp [Tab.resBase, Tab.romBase]; omega
      omega
    have hc1 : BitVec.ofInt 64 ↑(8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres + g.id)) =
        BitVec.ofNat 64 (8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres + g.id)) := rfl
    rw [hc1, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact tab_offset_not_in_resOnly L (Or.inr hrb) (by omega)

theorem resGlobSpan_contains_globOff {tab : Tab} (L : ProgLayout tab) (g : _root_.L.GVar)
    (hg : g.id < tab.ng) {k : Nat} (hk : k < 8) :
    L.resGlobSpan.contains (L.T + BitVec.ofInt 64 (tab.globOff g) + BitVec.ofNat 64 k) := by
  have hgb := L.tab_globOff_bound g hg
  have ht := L.hTValid
  have hbase : tab.resBase.toNat = 8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords) := by
    simp only [Tab.resBase, Tab.romBase]; omega
  have hgo : tab.globOff g = ↑(tab.resBase.toNat + 8 * (tab.nxres + g.id)) := by
    simp only [Tab.globOff, Tab.globBase, Tab.resBase, Tab.romBase]; omega
  rw [hgo]
  refine ⟨8 * (tab.nxres + g.id) + k, ?_, ?_⟩
  · simp only [ProgLayout.resGlobSpan]; omega
  · simp only [ProgLayout.resGlobSpan]
    apply BitVec.eq_of_toNat_eq
    have h1 : (BitVec.ofNat 64 tab.resBase.toNat).toNat = tab.resBase.toNat :=
      Nat.mod_eq_of_lt (by omega)
    have h2 : (BitVec.ofInt 64 ↑(tab.resBase.toNat + 8 * (tab.nxres + g.id))).toNat =
        tab.resBase.toNat + 8 * (tab.nxres + g.id) := by
      change (BitVec.ofNat 64 _).toNat = _; exact Nat.mod_eq_of_lt (by omega)
    have h3 : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
    have h4 : (BitVec.ofNat 64 (8 * (tab.nxres + g.id) + k)).toNat = 8 * (tab.nxres + g.id) + k :=
      Nat.mod_eq_of_lt (by omega)
    have hL : BitVec.ofInt 64 ↑(tab.resBase.toNat + 8 * (tab.nxres + g.id)) + BitVec.ofNat 64 k =
        BitVec.ofNat 64 tab.resBase.toNat + BitVec.ofNat 64 (8 * (tab.nxres + g.id) + k) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_add, h1, h2, h3, h4,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    rw [BitVec.add_assoc, BitVec.add_assoc, hL]

theorem progMemOutside_of_resGlob {tab : Tab} (L : ProgLayout tab) (sp : BitVec 64)
    (nl nt : Nat) {m1 m2 : ByteMem} (hm : MemEqOutside L.resGlobSpan m1 m2) :
    ProgMemOutside (FnWriteMask L sp nl nt) m1 m2 :=
  ProgMemOutside.of_memEqOutside (fun _ h => Or.inr (Or.inl h)) hm

theorem progMemOutside_of_arr8 {tab : Tab} (L : ProgLayout tab) (sp : BitVec 64)
    (nl nt : Nat) (a : _root_.L.ArrId) (ha : tab.bytePosOkB a = true)
    {m1 m2 : ByteMem} (hm : MemEqOutside (L.arr8Span a) m1 m2) :
    ProgMemOutside (FnWriteMask L sp nl nt) m1 m2 :=
  ProgMemOutside.of_memEqOutside (fun _ h => Or.inr (Or.inr (Or.inl ⟨a, ha, h⟩))) hm

theorem progMemOutside_of_arr64 {tab : Tab} (L : ProgLayout tab) (sp : BitVec 64)
    (nl nt : Nat) (s : _root_.L.TieredArray) (hs : tab.wordPosOkB s = true)
    {m1 m2 : ByteMem} (hm : MemEqOutside (L.arr64Span s) m1 m2) :
    ProgMemOutside (FnWriteMask L sp nl nt) m1 m2 :=
  ProgMemOutside.of_memEqOutside (fun _ h => Or.inr (Or.inr (Or.inr ⟨s, hs, h⟩))) hm

theorem progFrameOk_of_resGlob {tab : Tab} (L : ProgLayout tab) {sp : BitVec 64}
    {nl nt : Nat}
    (hlim : L.stackLimit.toNat ≤ sp.toNat) (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    {m1 m2 : ByteMem} {loc : _root_.L.Locals} (hm : MemEqOutside L.resGlobSpan m1 m2)
    (hf : ProgFrameOk L sp m1 nl loc) : ProgFrameOk L sp m2 nl loc := by
  intro x hx
  have hs1 : (slotSpan sp (1 + x)).sub L.stackSpan :=
    MemSpan.sub_trans (slotSpan_sub_frame (by omega)) (L.frame_sub_stackSpan hlim htop)
  have hdisjTab := MemSpan.disjoint_to_memDisjoint L.tabSpan_valid L.stackSpan_valid L.htabDisjStack
  have hdisjRg : MemDisjoint L.resGlobSpan L.stackSpan := MemDisjoint.of_sub_left L.resGlob_sub_tab hdisjTab
  have hd : MemDisjoint (slotSpan sp (1 + x)) L.resGlobSpan :=
    MemDisjoint.of_sub_left hs1 hdisjRg.symm
  have haddr : sp + BitVec.ofInt 64 (slotOff x) = slotAddr sp (1 + x) := by
    simp [slotAddr, slotOff_ofInt]
  rw [haddr]
  rw [MemEqOutside.readWord64_eq hm (slotAddr sp (1 + x)) fun k hk hc => hd _ ⟨k, hk, rfl⟩ hc]
  rw [← haddr]
  exact hf x hx

theorem progFrameOk_of_arr8 {tab : Tab} (L : ProgLayout tab) {sp : BitVec 64}
    {nl nt : Nat} (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (a : _root_.L.ArrId) (ha : tab.bytePosOkB a = true)
    {m1 m2 : ByteMem} {loc : _root_.L.Locals} (hm : MemEqOutside (L.arr8Span a) m1 m2)
    (hf : ProgFrameOk L sp m1 nl loc) : ProgFrameOk L sp m2 nl loc := by
  intro x hx
  have hs1 : (slotSpan sp (1 + x)).sub L.stackSpan :=
    MemSpan.sub_trans (slotSpan_sub_frame (by omega)) (L.frame_sub_stackSpan hlim htop)
  have hdisj := MemSpan.disjoint_to_memDisjoint (L.arr8Span_valid a) L.stackSpan_valid (L.h8DisjStack a ha)
  have hd : MemDisjoint (slotSpan sp (1 + x)) (L.arr8Span a) := MemDisjoint.of_sub_left hs1 hdisj.symm
  have haddr : sp + BitVec.ofInt 64 (slotOff x) = slotAddr sp (1 + x) := by
    simp [slotAddr, slotOff_ofInt]
  rw [haddr]
  rw [MemEqOutside.readWord64_eq hm (slotAddr sp (1 + x)) fun k hk hc => hd _ ⟨k, hk, rfl⟩ hc]
  rw [← haddr]
  exact hf x hx

theorem progFrameOk_of_arr64 {tab : Tab} (L : ProgLayout tab) {sp : BitVec 64}
    {nl nt : Nat} (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (s : _root_.L.TieredArray) (hs : tab.wordPosOkB s = true)
    {m1 m2 : ByteMem} {loc : _root_.L.Locals} (hm : MemEqOutside (L.arr64Span s) m1 m2)
    (hf : ProgFrameOk L sp m1 nl loc) : ProgFrameOk L sp m2 nl loc := by
  intro x hx
  have hs1 : (slotSpan sp (1 + x)).sub L.stackSpan :=
    MemSpan.sub_trans (slotSpan_sub_frame (by omega)) (L.frame_sub_stackSpan hlim htop)
  have hdisj := MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid s) L.stackSpan_valid (L.h64DisjStack s hs)
  have hd : MemDisjoint (slotSpan sp (1 + x)) (L.arr64Span s) := MemDisjoint.of_sub_left hs1 hdisj.symm
  have haddr : sp + BitVec.ofInt 64 (slotOff x) = slotAddr sp (1 + x) := by
    simp [slotAddr, slotOff_ofInt]
  rw [haddr]
  rw [MemEqOutside.readWord64_eq hm (slotAddr sp (1 + x)) fun k hk hc => hd _ ⟨k, hk, rfl⟩ hc]
  rw [← haddr]
  exact hf x hx

/-- Argument & return-arity check on all calls inside a statement:
    every call passes exact `fd.nparams` arguments and reads at most `fnMinRet fd` results. -/
def stmtArgsOkB (p : _root_.L.Prog) : _root_.L.Stmt → Bool
  | .seq s1 s2 => stmtArgsOkB p s1 && stmtArgsOkB p s2
  | .ite _ s1 s2 => stmtArgsOkB p s1 && stmtArgsOkB p s2
  | .while _ s => stmtArgsOkB p s
  | .call xs f args =>
    match p.lookup f with
    | some fd => decide (args.length = fd.nparams) && decide (xs.length ≤ fnMinRet fd)
    | none => false
  | _ => true

def progArgsOkB (p : _root_.L.Prog) : Bool :=
  p.all fun (_, fd) => stmtArgsOkB p fd.body

private theorem evalArgs_len_aux (es : List _root_.L.Expr) (st : _root_.L.St) {vs : List _root_.L.Word} {st' : _root_.L.St}
    (h : _root_.L.evalArgs es st = .ok (vs, st')) : vs.length = es.length := by
  induction es generalizing st vs st' with
  | nil =>
    simp only [_root_.L.evalArgs, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; rfl
  | cons e es ih =>
    simp only [_root_.L.evalArgs, Bind.bind, StateT.bind, Except.bind] at h
    cases he : _root_.L.evalE e st with
    | error _ => rw [he] at h; cases h
    | ok re =>
      rw [he] at h; dsimp only at h
      cases hes : _root_.L.evalArgs es re.2 with
      | error _ => rw [hes] at h; cases h
      | ok rvs =>
        rw [hes] at h
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, _⟩
        simp [ih re.2 hes]

private theorem bind_pure_normal_ne_ret {α : Type} (m : _root_.L.M α) (st st' : _root_.L.St)
    (vs : List _root_.L.Word) :
    (m >>= fun _ => pure _root_.L.Sig.normal) st ≠ .ok (.ret vs, st') := by
  dsimp only [Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure]
  cases m st with
  | error _ => intro h; cases h
  | ok pv => intro h; cases h

private theorem bind_ne_ret {α : Type} (m : _root_.L.M α) (f : α → _root_.L.M _root_.L.Sig)
    (hf : ∀ a st1 st' vs, f a st1 ≠ .ok (.ret vs, st')) (st st' : _root_.L.St) (vs : List _root_.L.Word) :
    (m >>= f) st ≠ .ok (.ret vs, st') := by
  dsimp only [Bind.bind, StateT.bind, Except.bind]
  cases hm : m st with
  | error _ => intro h; cases h
  | ok pv => exact hf pv.1 pv.2 st' vs

theorem execB_not_normal_of_not_fallthrough (p : _root_.L.Prog) :
    ∀ (s : _root_.L.Stmt) (b : Nat) (st st' : _root_.L.St) (b' : Nat),
      stmtMayFallthrough s = false →
      execB p b s st = .ok (.normal, st', b') → False := by
  intro s
  induction s with
  | ret es =>
    intro b st st' b' _ h
    rw [execB_ret] at h
    cases ha : _root_.L.evalArgs es st with
    | error _ => rw [ha] at h; cases h
    | ok pv => rcases pv with ⟨_, _⟩; rw [ha] at h; cases h
  | abort e =>
    intro b st st' b' _ h
    rw [execB_abort] at h
    cases ha : _root_.L.evalE e st with
    | error _ => rw [ha] at h; cases h
    | ok pv => rcases pv with ⟨_, _⟩; rw [ha] at h; cases h
  | seq s1 s2 ih1 ih2 =>
    intro b st st' b' hmf h
    simp only [stmtMayFallthrough] at hmf
    rw [execB_seq] at h
    cases hf1 : stmtMayFallthrough s1 with
    | false =>
      cases h1 : execB p b s1 st with
      | error e => rw [h1] at h; cases h
      | ok res =>
        rcases res with ⟨sig, st1, b1⟩
        cases sig with
        | normal => exact ih1 b st st1 b1 hf1 h1
        | brk | ret _ => rw [h1] at h; cases h
    | true =>
      rw [hf1] at hmf; simp only [↓reduceIte] at hmf
      cases h1 : execB p b s1 st with
      | error e => rw [h1] at h; cases h
      | ok res =>
        rcases res with ⟨sig, st1, b1⟩
        cases sig with
        | normal => rw [h1] at h; exact ih2 b1 st1 st' b' hmf h
        | brk | ret _ => rw [h1] at h; cases h
  | ite c s1 s2 ih1 ih2 =>
    intro b st st' b' hmf h
    simp only [stmtMayFallthrough, Bool.or_eq_false_iff] at hmf
    rw [execB_ite] at h
    cases hc : _root_.L.evalC c st with
    | error _ => rw [hc] at h; cases h
    | ok pv =>
      rcases pv with ⟨bc, st1⟩
      cases bc <;> rw [hc] at h
      · exact ih2 b st1 st' b' hmf.2 h
      · exact ih1 b st1 st' b' hmf.1 h
  | _ => intro _ _ _ _ hmf; simp [stmtMayFallthrough] at hmf

private theorem optMin_le_left {a b : Option Nat} :
    ∀ k, a = some k →
      ∃ k', (match a, b with | none, y => y | x, none => x | some x, some y => some (min x y)) = some k' ∧ k' ≤ k := by
  intro k ha; subst ha
  cases b with
  | none => exact ⟨k, rfl, Nat.le_refl k⟩
  | some m => exact ⟨min k m, rfl, Nat.min_le_left k m⟩

private theorem optMin_le_right {a b : Option Nat} :
    ∀ k, b = some k →
      ∃ k', (match a, b with | none, y => y | x, none => x | some x, some y => some (min x y)) = some k' ∧ k' ≤ k := by
  intro k hb; subst hb
  cases a with
  | none => exact ⟨k, rfl, Nat.le_refl k⟩
  | some m => exact ⟨min m k, rfl, Nat.min_le_right m k⟩

private theorem execB_of_step_ne_ret {p : _root_.L.Prog} {b b' : Nat} {s : _root_.L.Stmt} {st st' : _root_.L.St}
    {vs : List _root_.L.Word}
    (heq : execB p b s st = match _root_.L.step p (fun _ => throw Err.outOfFuel) s st with
      | .ok (sig, st1) => .ok (sig, st1, b)
      | .error err => .error err)
    (hstep : ∀ st1, _root_.L.step p (fun _ => throw Err.outOfFuel) s st ≠ .ok (.ret vs, st1))
    (h : execB p b s st = .ok (.ret vs, st', b')) : False := by
  rw [heq] at h
  cases hm : _root_.L.step p (fun _ => throw Err.outOfFuel) s st with
  | error _ => rw [hm] at h; cases h
  | ok res =>
    rcases res with ⟨sig, st1⟩; rw [hm] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, hst, _⟩
    exact hstep st1 hm

private theorem execWhile_ret_len_ge (p : _root_.L.Prog) (c : _root_.L.Cond) (body : _root_.L.Stmt)
    (ih : ∀ b st vs st' b', execB p b body st = .ok (.ret vs, st', b') →
      ∃ k, stmtMinRetRaw body = some k ∧ k ≤ max 1 vs.length) :
    ∀ b st vs st' b', execB p b (.while c body) st = .ok (.ret vs, st', b') →
      ∃ k, stmtMinRetRaw body = some k ∧ k ≤ max 1 vs.length := by
  intro b
  induction b using Nat.strongRecOn with
  | _ b ihB =>
    intro st vs st' b' h
    rw [execB_while] at h
    cases hc : _root_.L.evalC c st with
    | error _ => rw [hc] at h; cases h
    | ok pv =>
      rcases pv with ⟨bc, st1⟩; rw [hc] at h
      cases bc with
      | false => cases h
      | true =>
        dsimp only at h
        cases hb : execB p b body st1 with
        | error _ => rw [hb] at h; cases h
        | ok res =>
          rcases res with ⟨sig, st2, b1⟩
          have hbLe : b1 ≤ b := execB_fuel_le hb
          rw [hb] at h
          cases sig with
          | brk => cases h
          | ret rv =>
            simp only [Except.ok.injEq, Prod.mk.injEq, _root_.L.Sig.ret.injEq] at h
            rcases h with ⟨hvs, hst, hb'⟩
            subst hvs; exact ih b st1 _ _ _ hb
          | normal =>
            cases b1 with
            | zero => cases h
            | succ b1' => exact ihB b1' (by omega) st2 vs st' b' h

theorem execB_ret_len_ge (p : _root_.L.Prog) (s : _root_.L.Stmt) :
    ∀ b st vs st' b', execB p b s st = .ok (.ret vs, st', b') →
      ∃ k, stmtMinRetRaw s = some k ∧ k ≤ max 1 vs.length := by
  induction s with
  | ret es =>
    intro b st vs st' b' h
    rw [execB_ret] at h
    cases ha : _root_.L.evalArgs es st with
    | error _ => rw [ha] at h; cases h
    | ok pv =>
      rcases pv with ⟨rvs, st1⟩; rw [ha] at h
      cases h
      have hlen := evalArgs_len_aux es st ha
      exact ⟨max 1 es.length, rfl, by omega⟩
  | seq s1 s2 ih1 ih2 =>
    intro b st vs st' b' h
    rw [execB_seq] at h
    cases h1 : execB p b s1 st with
    | error _ => rw [h1] at h; cases h
    | ok res =>
      rcases res with ⟨sig, st1, b1⟩; rw [h1] at h
      cases sig with
      | brk => cases h
      | normal =>
        obtain ⟨k, hk, hle⟩ := ih2 b1 st1 vs st' b' h
        cases hsm1 : stmtMinRetRaw s1 with
        | none => exact ⟨k, by simp [stmtMinRetRaw, hsm1, hk], hle⟩
        | some m => exact ⟨min m k, by simp [stmtMinRetRaw, hsm1, hk], by omega⟩
      | ret rv =>
        simp only [Except.ok.injEq, Prod.mk.injEq, _root_.L.Sig.ret.injEq] at h
        rcases h with ⟨hvs, hst, hb'⟩
        subst hvs
        obtain ⟨k, hk, hle⟩ := ih1 b st _ _ _ h1
        cases hsm2 : stmtMinRetRaw s2 with
        | none => exact ⟨k, by simp [stmtMinRetRaw, hk, hsm2], hle⟩
        | some m => exact ⟨min k m, by simp [stmtMinRetRaw, hk, hsm2], by omega⟩
  | ite c s1 s2 ih1 ih2 =>
    intro b st vs st' b' h
    rw [execB_ite] at h
    cases hc : _root_.L.evalC c st with
    | error _ => rw [hc] at h; cases h
    | ok pv =>
      rcases pv with ⟨bc, st1⟩; rw [hc] at h
      cases bc with
      | false =>
        obtain ⟨k, hk, hle⟩ := ih2 b st1 vs st' b' h
        cases hsm1 : stmtMinRetRaw s1 with
        | none => exact ⟨k, by simp [stmtMinRetRaw, hsm1, hk], hle⟩
        | some m => exact ⟨min m k, by simp [stmtMinRetRaw, hsm1, hk], by omega⟩
      | true =>
        obtain ⟨k, hk, hle⟩ := ih1 b st1 vs st' b' h
        cases hsm2 : stmtMinRetRaw s2 with
        | none => exact ⟨k, by simp [stmtMinRetRaw, hk, hsm2], hle⟩
        | some m => exact ⟨min k m, by simp [stmtMinRetRaw, hk, hsm2], by omega⟩
  | «while» c body ih => exact execWhile_ret_len_ge p c body ih
  | call xs f args =>
    intro b st vs st' b' h
    rw [execB_call] at h
    cases ha : _root_.L.evalArgs args st with
    | error _ => rw [ha] at h; cases h
    | ok pv =>
      rcases pv with ⟨rvs, st1⟩; rw [ha] at h
      cases hl : p.lookup f with
      | none => rw [hl] at h; cases h
      | some fd =>
        rw [hl] at h
        cases b with
        | zero => cases h
        | succ b0 =>
          dsimp only at h
          cases hc : execB p b0 fd.body { st1 with loc := _root_.L.Locals.init rvs } with
          | error _ => rw [hc] at h; cases h
          | ok res => rcases res with ⟨sig, st2, b2⟩; rw [hc] at h; cases h
  | skip => intro _ _ _ _ _ h; simp at h
  | brk => intro _ _ _ _ _ h; simp at h
  | set _ e =>
    intro b st _ _ _ h; rw [execB_set] at h
    cases he : _root_.L.evalE e st with
    | error _ => rw [he] at h; cases h
    | ok pv => rcases pv with ⟨_, _⟩; rw [he] at h; cases h
  | gset _ e =>
    intro b st _ _ _ h; rw [execB_gset] at h
    cases he : _root_.L.evalE e st with
    | error _ => rw [he] at h; cases h
    | ok pv => rcases pv with ⟨_, _⟩; rw [he] at h; cases h
  | abort e =>
    intro b st _ _ _ h; rw [execB_abort] at h
    cases he : _root_.L.evalE e st with
    | error _ => rw [he] at h; cases h
    | ok pv => rcases pv with ⟨_, _⟩; rw [he] at h; cases h
  | st8 a i e =>
    intro b st vs st' b' h
    refine False.elim (execB_of_step_ne_ret (execB_st8 p b a i e st) (fun st1 => ?_) h)
    exact bind_ne_ret _ _ (fun _ => bind_ne_ret _ _ (fun _ => bind_pure_normal_ne_ret _)) _ _ _
  | st64 a i e =>
    intro b st vs st' b' h
    refine False.elim (execB_of_step_ne_ret (execB_st64 p b a i e st) (fun st1 => ?_) h)
    exact bind_ne_ret _ _ (fun _ => bind_ne_ret _ _ (fun _ => bind_pure_normal_ne_ret _)) _ _ _
  | st64t a t i e =>
    intro b st vs st' b' h
    refine False.elim (execB_of_step_ne_ret (execB_st64t p b a t i e st) (fun st1 => ?_) h)
    exact bind_ne_ret _ _ (fun _ => bind_ne_ret _ _ (fun _ => bind_ne_ret _ _ (fun _ => bind_pure_normal_ne_ret _))) _ _ _
  | st32t a t i e =>
    intro b st vs st' b' h
    refine False.elim (execB_of_step_ne_ret (execB_st32t p b a t i e st) (fun st1 => ?_) h)
    exact bind_ne_ret _ _ (fun _ => bind_ne_ret _ _ (fun _ => bind_ne_ret _ _ (fun _ => bind_pure_normal_ne_ret _))) _ _ _
  | copy64 d di s si n =>
    intro b st vs st' b' h
    refine False.elim (execB_of_step_ne_ret (execB_copy64 p b d di s si n st) (fun st1 => ?_) h)
    exact bind_ne_ret _ _ (fun _ => bind_ne_ret _ _ (fun _ => bind_ne_ret _ _ (fun _ =>
      bind_ne_ret _ _ (fun _ => bind_ne_ret _ _ (fun _ => bind_ne_ret _ _ (fun _ _ _ _ => by
        split
        · exact bind_pure_normal_ne_ret _ _ _ _
        · intro he; cases he)))))) _ _ _
  | copy8w d di s si n =>
    intro b st vs st' b' h
    refine False.elim (execB_of_step_ne_ret (execB_copy8w p b d di s si n st) (fun st1 => ?_) h)
    exact bind_ne_ret _ _ (fun _ => bind_ne_ret _ _ (fun _ => bind_ne_ret _ _ (fun _ =>
      bind_ne_ret _ _ (fun _ => bind_ne_ret _ _ (fun _ _ _ _ => by
        split
        · exact bind_pure_normal_ne_ret _ _ _ _
        · intro he; cases he))))) _ _ _
  | scan8 x s i e c =>
    intro b st vs st' b' h
    refine False.elim (execB_of_step_ne_ret (execB_scan8 p b x s i e c st) (fun st1 => ?_) h)
    exact bind_ne_ret _ _ (fun _ => bind_ne_ret _ _ (fun _ => bind_ne_ret _ _ (fun _ _ _ _ => by
      split
      · exact bind_pure_normal_ne_ret _ _ _ _
      · intro he; cases he))) _ _ _

theorem fnMinRet_le_sig {p : _root_.L.Prog} {fd : _root_.L.FunDecl} {b b' : Nat} {st st' : _root_.L.St}
    {sig : _root_.L.Sig} (h : execB p b fd.body st = .ok (sig, st', b')) (hnb : sig ≠ .brk) :
    fnMinRet fd ≤ max 1 sig.retVal.length := by
  cases sig with
  | brk => exact absurd rfl hnb
  | normal =>
    cases hm : stmtMayFallthrough fd.body with
    | true => simp [fnMinRet, hm]; omega
    | false => exact False.elim (execB_not_normal_of_not_fallthrough p fd.body b st st' b' hm h)
  | ret vs =>
    dsimp only [fnMinRet, _root_.L.Sig.retVal]
    split
    · omega
    · obtain ⟨k, hk, hle⟩ := execB_ret_len_ge p fd.body b st vs st' b' h
      rw [hk]; exact hle

/-- Active return values stored in `a0..a7` and descriptor table `resOff` slots (up to `max 1 vs.length`). -/
def ResultsInState (tab : Tab) (L : ProgLayout tab) (st : State) (vs : List _root_.L.Word) : Prop :=
  (∀ i, i < min (min (max 1 vs.length) tab.nres) maxRes → st.getReg (resReg i) = (vs.getD i 0).toBitVec) ∧
  (∀ i, maxRes ≤ i → i < min (max 1 vs.length) tab.nres →
    readWord64 st.mem (L.T + BitVec.ofInt 64 (tab.resOff i)) = (vs.getD i 0).toBitVec)

theorem resultsInState_mem {tab : Tab} {L : ProgLayout tab} {st1 st2 : State}
    {vs : List _root_.L.Word} {S : MemSpan}
    (hreg : ∀ i, i < min tab.nres maxRes → st2.getReg (resReg i) = st1.getReg (resReg i))
    (hdisj : ∀ i, maxRes ≤ i → i < tab.nres →
      ∀ k, k < 8 → ¬S.contains (L.T + BitVec.ofInt 64 (tab.resOff i) + BitVec.ofNat 64 k))
    (hm : MemEqOutside S st1.mem st2.mem)
    (hr : ResultsInState tab L st1 vs) : ResultsInState tab L st2 vs := by
  refine ⟨fun i hi => (hreg i (by omega)).trans (hr.1 i hi), fun i hlo hhi => ?_⟩
  rw [← hr.2 i hlo hhi]
  exact MemEqOutside.readWord64_eq hm _ (hdisj i hlo (by omega))

def copyOneTempToResult (tab : Tab) (nl tmp count i : Nat) : List AsmItem :=
  let loadOrZero :=
    if i < count then loadMemOff .ld AbiReg.t1 AbiReg.sp AbiReg.t2 (slotOff (nl + tmp + i))
    else [Asm.addi AbiReg.t1 AbiReg.zero 0#12]
  if i < maxRes then
    if i < count then loadMemOff .ld (resReg i) AbiReg.sp AbiReg.t0 (slotOff (nl + tmp + i))
    else [Asm.addi (resReg i) AbiReg.zero 0#12]
  else
    loadOrZero ++ storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t2 (tab.resOff i)

theorem copyTempsToResults_eq_flatMap (tab : Tab) (nl tmp count : Nat) (hc : 0 < count) :
    copyTempsToResults tab nl tmp count =
      (List.range (min count tab.nres)).flatMap (copyOneTempToResult tab nl tmp count) := by
  have hne : (count == 0) = false := by cases count with | zero => omega | succ _ => rfl
  simp only [copyTempsToResults, hne, Bool.false_eq_true, ↓reduceIte]
  have hcongr : ∀ (xs : List Nat), (∀ i ∈ xs, i < min count tab.nres) →
      xs.flatMap (fun i =>
        if i < maxRes then loadMemOff .ld (resReg i) AbiReg.sp AbiReg.t0 (slotOff (nl + tmp + i))
        else loadMemOff .ld AbiReg.t1 AbiReg.sp AbiReg.t2 (slotOff (nl + tmp + i)) ++
          storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t2 (tab.resOff i)) =
      xs.flatMap (copyOneTempToResult tab nl tmp count) := by
    intro xs hxs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      have hx : x < min count tab.nres := hxs x (by simp)
      have hxc : x < count := by omega
      simp only [List.flatMap_cons, copyOneTempToResult, hxc, ↓reduceIte]
      congr 1; exact ih (fun y hy => hxs y (by simp [hy]))
  exact hcongr (List.range (min count tab.nres)) (fun i hi => List.mem_range.mp hi)

theorem copyOneTempToResult_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    {sp : BitVec 64} {nl tmp nt count : Nat}
    (hal : isAligned sp 8 = true) (_hlim : L.stackLimit.toNat ≤ sp.toNat)
    (_htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (_hcnt : tmp + count ≤ nt) (vs : List _root_.L.Word) (hlen : vs.length = count)
    (i : Nat) (hi : i < env.tab.nres)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ copyOneTempToResult env.tab nl tmp count i ++ post) =
      .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hslots : ∀ j (hj : j < count),
      readWord64 st.mem (sp + BitVec.ofInt 64 (slotOff (nl + tmp + j))) = vs[j].toBitVec) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (copyOneTempToResult env.tab nl tmp count i))) ∧
      PreservedRegs st st' ∧
      (∀ r, r < min env.tab.nres maxRes → r ≠ i → st'.getReg (resReg r) = st.getReg (resReg r)) ∧
      (i < maxRes → st'.getReg (resReg i) = (vs.getD i 0).toBitVec) ∧
      (maxRes ≤ i → readWord64 st'.mem (L.T + BitVec.ofInt 64 (env.tab.resOff i)) = (vs.getD i 0).toBitVec) ∧
      (i < maxRes → st'.mem = st.mem) ∧
      (maxRes ≤ i → st'.mem = writeWord64 st.mem (L.T + BitVec.ofInt 64 (env.tab.resOff i)) (vs.getD i 0).toBitVec) ∧
      MemEqOutside L.resOnlySpan st.mem st'.mem := by
  have hpc64 := linkResolved_sub_pc64 env pre (copyOneTempToResult env.tab nl tmp count i) post hlink
  by_cases him : i < maxRes
  · by_cases hic : i < count
    · have hco : copyOneTempToResult env.tab nl tmp count i =
          loadMemOff .ld (resReg i) AbiReg.sp AbiReg.t0 (slotOff (nl + tmp + i)) := by
        simp [copyOneTempToResult, him, hic]
      rw [hco] at hlink hpc64 ⊢
      have halS : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff (nl + tmp + i))) 8 = true := by
        rw [hsp]; exact isAligned8_add_int_mul8 sp hal (1 + (nl + tmp + i))
      have hrn := resReg_ne_preserved i
      obtain ⟨st', hrun, hother, hval, hmem, hnpc⟩ :=
        loadMemOff_ld_correct_lm lkm env.hrom pre post (resReg i) AbiReg.sp AbiReg.t0
          (resReg_ne_zero i) (by decide) (by decide) (slotOff (nl + tmp + i)) hlink hpc64 st hpc halS
      refine ⟨lkm.totalSize (loadMemOff .ld (resReg i) AbiReg.sp AbiReg.t0 (slotOff (nl + tmp + i))), st',
        hrun, hnpc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact ⟨hother _ hrn.1.symm (by decide), hother _ hrn.2.1.symm (by decide),
               hother _ hrn.2.2.1.symm (by decide),
               hother _ hrn.2.2.2.2.1.symm (by decide)⟩
      · intro r hr hne
        exact hother (resReg r) (fun h => resReg_inj (Nat.lt_of_lt_of_le hr (Nat.min_le_right _ _)) him hne h)
          (resReg_ne_preserved r).2.2.2.2.2.1
      · intro _
        rw [hval, hsp, hslots i hic]
        simp [List.getD, List.getElem?_eq_getElem (by omega : i < vs.length)]
      · intro hge; omega
      · intro _; exact hmem
      · intro hge; omega
      · rw [hmem]; exact MemEqOutside.refl _ _
    · have hco : copyOneTempToResult env.tab nl tmp count i = [Asm.addi (resReg i) AbiReg.zero 0#12] := by
        simp [copyOneTempToResult, him, hic]
      rw [hco] at hlink hpc64 ⊢
      have htw : lkm.totalSize [Asm.addi (resReg i) AbiReg.zero 0#12] = 1 := by simp only [Asm.addi, lkm.totalSize_instr]
      have hlt : 4 * lkm.totalSize pre < 2 ^ 64 := by rw [htw] at hpc64; omega
      have hstep := step_item_instr_lm lkm env.hrom pre post (.aluImm .addi (resReg i) AbiReg.zero 0#12) hlink hlt st hpc
      let st1 := stepReg st (resReg i) 0#64 (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
      have hres0 : evalAluImm .addi (st.getReg AbiReg.zero) 0#12 = 0#64 := by
        rw [getReg_zero st]; decide
      have hrun : RV64.run env.rom 1 st = .cont st1 := by
        apply run_one_cont
        rw [hstep]
        simp only [execInstr, hres0, pc_add_4_ofNat st.pc hpc, st1, stepReg, setReg_mem]
      have hrn := resReg_ne_preserved i
      have hmem1 : st1.mem = st.mem := by simp [st1, stepReg, setReg_mem]
      refine ⟨1, st1, hrun, by rw [htw]; rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact ⟨getReg_stepReg_ne st (resReg i) AbiReg.gp hrn.1.symm _ _,
               getReg_stepReg_ne st (resReg i) AbiReg.sp hrn.2.1.symm _ _,
               getReg_stepReg_ne st (resReg i) AbiReg.s0 hrn.2.2.1.symm _ _,
               getReg_stepReg_ne st (resReg i) AbiReg.s2 hrn.2.2.2.2.1.symm _ _⟩
      · intro r hr hne
        have hinj : resReg r ≠ resReg i := resReg_inj (Nat.lt_of_lt_of_le hr (Nat.min_le_right _ _)) him hne
        exact getReg_stepReg_ne st (resReg i) (resReg r) hinj _ _
      · intro _
        rw [getReg_stepReg_eq st (resReg i) (resReg_ne_zero i) 0#64 _]
        simp [List.getD, List.getElem?_eq_none (by omega : vs.length ≤ i)]
      · intro hge; omega
      · intro _; exact hmem1
      · intro hge; omega
      · rw [hmem1]; exact MemEqOutside.refl _ _
  · have hge : maxRes ≤ i := by omega
    by_cases hic : i < count
    · have hco : copyOneTempToResult env.tab nl tmp count i =
          loadMemOff .ld AbiReg.t1 AbiReg.sp AbiReg.t2 (slotOff (nl + tmp + i)) ++
          storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t2 (env.tab.resOff i) := by
        simp [copyOneTempToResult, him, hic]
      rw [hco] at hlink hpc64 ⊢
      have ⟨hl1, hl2⟩ := linkResolved_mid_split lkm pre _ _ post hlink
      have hpc1 := linkResolved_sub_pc64 env pre _ _ hl1
      have halS : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff (nl + tmp + i))) 8 = true := by
        rw [hsp]; exact isAligned8_add_int_mul8 sp hal (1 + (nl + tmp + i))
      obtain ⟨st1, hrun1, hoth1, hval1, hmem1, hnpc1⟩ :=
        loadMemOff_ld_correct_lm lkm env.hrom pre _ AbiReg.t1 AbiReg.sp AbiReg.t2
          (by decide) (by decide) (by decide) (slotOff (nl + tmp + i)) hl1 hpc1 st hpc halS
      have hgp1 : st1.getReg AbiReg.gp = L.T := (hoth1 AbiReg.gp (by decide) (by decide)).trans hgp
      have halR : isAligned (st1.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.resOff i)) 8 = true := by
        rw [hgp1]; exact isAligned8_of_resOff L hge hi
      have hpc2 := linkResolved_sub_pc64 env (pre ++ _) _ post hl2
      obtain ⟨st2, hrun2, hoth2, hmem2, hnpc2⟩ :=
        storeMemOff_sd_correct_lm lkm env.hrom (pre ++ _) post AbiReg.gp AbiReg.t1 AbiReg.t2
          (by decide) (by decide) (by decide) (env.tab.resOff i) hl2 hpc2 st1
          (by simpa [lkm.totalSize_append] using hnpc1) halR
      have hvalEq : st1.getReg AbiReg.t1 = (vs.getD i 0).toBitVec := by
        rw [hval1, hsp, hslots i hic]
        simp [List.getD, List.getElem?_eq_getElem (by omega : i < vs.length)]
      refine ⟨lkm.totalSize (loadMemOff .ld AbiReg.t1 AbiReg.sp AbiReg.t2 (slotOff (nl + tmp + i))) +
          lkm.totalSize (storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t2 (env.tab.resOff i)), st2,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [run_add, hrun1]; dsimp only; exact hrun2
      · simpa [lkm.totalSize_append, Nat.add_assoc] using hnpc2
      · exact ⟨(hoth2 _ (by decide)).trans (hoth1 _ (by decide) (by decide)),
               (hoth2 _ (by decide)).trans (hoth1 _ (by decide) (by decide)),
               (hoth2 _ (by decide)).trans (hoth1 _ (by decide) (by decide)),
               (hoth2 _ (by decide)).trans (hoth1 _ (by decide) (by decide))⟩
      · intro r hr _
        have hrn := resReg_ne_preserved r
        exact (hoth2 _ hrn.2.2.2.2.2.2.2).trans (hoth1 _ hrn.2.2.2.2.2.2.1 hrn.2.2.2.2.2.2.2)
      · intro hlt; omega
      · intro _; rw [hmem2, hmem1, hgp1, hvalEq]; exact readWord64_writeWord64_self _ _ _
      · intro hlt; omega
      · intro _; rw [hmem2, hmem1, hgp1, hvalEq]
      · rw [hmem2, hmem1, hgp1]
        exact MemEqOutside.writeWord64 _ _ _ (fun k hk => resOnlySpan_contains_resOff L hge hi hk)
    · have hco : copyOneTempToResult env.tab nl tmp count i =
          [Asm.addi AbiReg.t1 AbiReg.zero 0#12] ++
          storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t2 (env.tab.resOff i) := by
        simp [copyOneTempToResult, him, hic]
      rw [hco] at hlink hpc64 ⊢
      have ⟨hl1, hl2⟩ := linkResolved_mid_split lkm pre _ _ post hlink
      have hpc1 := linkResolved_sub_pc64 env pre _ _ hl1
      have htw1 : lkm.totalSize [Asm.addi AbiReg.t1 AbiReg.zero 0#12] = 1 := by simp only [Asm.addi, lkm.totalSize_instr]
      have hlt1 : 4 * lkm.totalSize pre < 2 ^ 64 := by rw [htw1] at hpc1; omega
      have hstep1 := step_item_instr_lm lkm env.hrom pre _ (.aluImm .addi AbiReg.t1 AbiReg.zero 0#12) hl1 hlt1 st hpc
      let st1 := stepReg st AbiReg.t1 0#64 (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
      have hres0 : evalAluImm .addi (st.getReg AbiReg.zero) 0#12 = 0#64 := by
        rw [getReg_zero st]; decide
      have hrun1 : RV64.run env.rom 1 st = .cont st1 := by
        apply run_one_cont
        rw [hstep1]
        simp only [execInstr, hres0, pc_add_4_ofNat st.pc hpc, st1, stepReg, setReg_mem]
      have hgp1 : st1.getReg AbiReg.gp = L.T := (getReg_stepReg_ne st AbiReg.t1 AbiReg.gp (by decide) 0#64 _).trans hgp
      have halR : isAligned (st1.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.resOff i)) 8 = true := by
        rw [hgp1]; exact isAligned8_of_resOff L hge hi
      have hpc2 := linkResolved_sub_pc64 env (pre ++ _) _ post hl2
      have hpc1Eq : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ [Asm.addi AbiReg.t1 AbiReg.zero 0#12])) := by
        simp [st1, stepReg, lkm.totalSize_append, htw1]
      obtain ⟨st2, hrun2, hoth2, hmem2, hnpc2⟩ :=
        storeMemOff_sd_correct_lm lkm env.hrom (pre ++ _) post AbiReg.gp AbiReg.t1 AbiReg.t2
          (by decide) (by decide) (by decide) (env.tab.resOff i) hl2 hpc2 st1 hpc1Eq halR
      have ht1Val : st1.getReg AbiReg.t1 = 0#64 := getReg_stepReg_eq st AbiReg.t1 (by decide) 0#64 _
      have hzero : (vs.getD i 0).toBitVec = 0#64 := by
        simp [List.getD, List.getElem?_eq_none (by omega : vs.length ≤ i)]
      have hmem1 : st1.mem = st.mem := by simp [st1, stepReg, setReg_mem]
      refine ⟨1 + lkm.totalSize (storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t2 (env.tab.resOff i)), st2,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [run_add, hrun1]; dsimp only; exact hrun2
      · rw [lkm.totalSize_append] at hnpc2
        rw [lkm.totalSize_append, ← Nat.add_assoc]
        exact hnpc2
      · exact ⟨(hoth2 _ (by decide)).trans (hgp1.trans hgp.symm),
               (hoth2 _ (by decide)).trans (getReg_stepReg_ne st AbiReg.t1 AbiReg.sp (by decide) 0#64 _),
               (hoth2 _ (by decide)).trans (getReg_stepReg_ne st AbiReg.t1 AbiReg.s0 (by decide) 0#64 _),
               (hoth2 _ (by decide)).trans (getReg_stepReg_ne st AbiReg.t1 AbiReg.s2 (by decide) 0#64 _)⟩
      · intro r hr _
        have hrn := resReg_ne_preserved r
        exact (hoth2 _ hrn.2.2.2.2.2.2.2).trans (getReg_stepReg_ne st AbiReg.t1 (resReg r) hrn.2.2.2.2.2.2.1 0#64 _)
      · intro hlt; omega
      · intro _; rw [hmem2, hgp1, ht1Val, hzero]; exact readWord64_writeWord64_self _ _ _
      · intro hlt; omega
      · intro _; rw [hmem2, hmem1, hgp1, ht1Val, hzero]
      · rw [hmem2, hmem1, hgp1]
        exact MemEqOutside.writeWord64 _ _ _ (fun k hk => resOnlySpan_contains_resOff L hge hi hk)

theorem copyTempsToResults_prefix_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    {sp : BitVec 64} {nl tmp nt count : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (hcnt : tmp + count ≤ nt) (vs : List _root_.L.Word) (hlen : vs.length = count) :
    ∀ m, m ≤ env.tab.nres → ∀ (pre post : List AsmItem),
      lkm.linkSpec (pre ++ (List.range m).flatMap (copyOneTempToResult env.tab nl tmp count) ++ post) =
        .ok (env.code, env.labels) →
      ∀ (st : State), st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      st.getReg AbiReg.gp = L.T → st.getReg AbiReg.sp = sp →
      (∀ j (hj : j < count),
        readWord64 st.mem (sp + BitVec.ofInt 64 (slotOff (nl + tmp + j))) = (vs[j]'(by omega)).toBitVec) →
      ∃ k st',
        RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre +
          lkm.totalSize ((List.range m).flatMap (copyOneTempToResult env.tab nl tmp count)))) ∧
        PreservedRegs st st' ∧
        (∀ i, i < min m maxRes → st'.getReg (resReg i) = (vs.getD i 0).toBitVec) ∧
        (∀ i, maxRes ≤ i → i < m →
          readWord64 st'.mem (L.T + BitVec.ofInt 64 (env.tab.resOff i)) = (vs.getD i 0).toBitVec) ∧
        MemEqOutside L.resOnlySpan st.mem st'.mem := by
  intro m
  induction m with
  | zero =>
    intro _hm _ _ _hlink st hpc _hgp _hsp _hslots
    refine ⟨0, st, by simp [RV64.run], ?_, PreservedRegs.refl st,
      fun i hi => by omega, fun i h1 h2 => by omega, MemEqOutside.refl _ _⟩
    simp [lkm.totalSize_nil, hpc]
  | succ m ih =>
    intro hm pre post hlink st hpc hgp hsp hslots
    have heq : (List.range (m + 1)).flatMap (copyOneTempToResult env.tab nl tmp count) =
        (List.range m).flatMap (copyOneTempToResult env.tab nl tmp count) ++
        copyOneTempToResult env.tab nl tmp count m := by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rw [heq] at hlink ⊢
    have ⟨hl1, hl2⟩ := linkResolved_mid_split lkm pre _ _ post hlink
    obtain ⟨k1, st1, hrun1, hpc1, hpres1, hreg1, hmem1, hout1⟩ :=
      ih (by omega) pre _ hl1 st hpc hgp hsp hslots
    have hslots1 : ∀ j (hj : j < count),
        readWord64 st1.mem (sp + BitVec.ofInt 64 (slotOff (nl + tmp + j))) = vs[j].toBitVec := by
      intro j hj
      have hs1 : (slotSpan sp (1 + (nl + tmp + j))).sub L.stackSpan :=
        MemSpan.sub_trans (slotSpan_sub_frame (by omega)) (L.frame_sub_stackSpan hlim htop)
      have hdisjTab := MemSpan.disjoint_to_memDisjoint L.tabSpan_valid L.stackSpan_valid L.htabDisjStack
      have hdisjRg : MemDisjoint L.resOnlySpan L.stackSpan :=
        MemDisjoint.of_sub_left (MemSpan.sub_trans (resOnlySpan_sub_resGlob L) L.resGlob_sub_tab) hdisjTab
      have hd : MemDisjoint (slotSpan sp (1 + (nl + tmp + j))) L.resOnlySpan := MemDisjoint.of_sub_left hs1 hdisjRg.symm
      rw [← hslots j hj]
      exact MemEqOutside.readWord64_eq hout1 _ fun k hk hc =>
        hd _ ⟨k, hk, by simp [slotSpan, slotAddr, slotOff_ofInt]⟩ hc
    obtain ⟨k2, st2, hrun2, hpc2, hpres2, hothReg2, hcurReg2, hcurMem2, hmemEq2, hmemWr2, hout2⟩ :=
      copyOneTempToResult_sim env L hal hlim htop hcnt vs hlen m (by omega)
        (pre ++ (List.range m).flatMap (copyOneTempToResult env.tab nl tmp count)) post hl2
        st1 (by simpa [lkm.totalSize_append] using hpc1) (hpres1.gp.trans hgp) (hpres1.sp.trans hsp) hslots1
    refine ⟨k1 + k2, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2, ?_,
      hpres1.trans hpres2, ?_, ?_, hout1.trans hout2⟩
    · simpa [lkm.totalSize_append, Nat.add_assoc] using hpc2
    · intro i hi
      by_cases him : i = m
      · subst him; exact hcurReg2 (by omega)
      · rw [hothReg2 i (by omega) him]
        exact hreg1 i (by omega)
    · intro i hlo hhi
      by_cases him : i = m
      · subst him; exact hcurMem2 hlo
      · by_cases hmx : m < maxRes
        · rw [hmemEq2 hmx]; exact hmem1 i hlo (by omega)
        · have hgeM : maxRes ≤ m := by omega
          rw [hmemWr2 hgeM]
          have hdisj : ∀ k1 k2, k1 < 8 → k2 < 8 →
              L.T + BitVec.ofInt 64 (env.tab.resOff i) + BitVec.ofNat 64 k1 ≠
              L.T + BitVec.ofInt 64 (env.tab.resOff m) + BitVec.ofNat 64 k2 := by
            intro k1 k2 hk1 hk2 heq
            have hbi : env.tab.resBase.toNat + 8 * (i - maxRes) + 8 ≤ L.tabBytes :=
              L.tab_resOff_bound hlo (by omega)
            have hbm : env.tab.resBase.toNat + 8 * (m - maxRes) + 8 ≤ L.tabBytes :=
              L.tab_resOff_bound hgeM (by omega)
            have hnn := ProgLayout.resBase_nonneg env.tab
            have ht := L.hTValid
            have hri : env.tab.resOff i = ↑(env.tab.resBase.toNat + 8 * (i - maxRes)) := by
              simp only [Tab.resOff]; omega
            have hrm : env.tab.resOff m = ↑(env.tab.resBase.toNat + 8 * (m - maxRes)) := by
              simp only [Tab.resOff]; omega
            rw [hri, hrm] at heq
            have hnat := congrArg BitVec.toNat heq
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
          exact hmem1 i hlo (by omega)

theorem copyTempsToResults_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    {sp : BitVec 64} {nl tmp nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (vs : List _root_.L.Word) (hcnt : tmp + vs.length ≤ nt)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ copyTempsToResults env.tab nl tmp vs.length ++ post) =
      .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hslots : ∀ j (hj : j < vs.length),
      readWord64 st.mem (sp + BitVec.ofInt 64 (slotOff (nl + tmp + j))) = vs[j].toBitVec) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (copyTempsToResults env.tab nl tmp vs.length))) ∧
      PreservedRegs st st' ∧
      ResultsInState env.tab L st' vs ∧
      MemEqOutside L.resOnlySpan st.mem st'.mem := by
  by_cases hlen : vs.length = 0
  · have hnil : vs = [] := List.eq_nil_of_length_eq_zero hlen
    subst hnil
    by_cases hnres : 0 < env.tab.nres
    · have hco : copyTempsToResults env.tab nl tmp 0 = [Asm.addi AbiReg.a0 AbiReg.zero 0#12] := by
        simp [copyTempsToResults, hnres]
      simp only [List.length_nil] at hlink ⊢
      rw [hco] at hlink ⊢
      have hpc64 := linkResolved_sub_pc64 env pre _ post hlink
      have htw : lkm.totalSize [Asm.addi AbiReg.a0 AbiReg.zero 0#12] = 1 := by
        simp only [Asm.addi, lkm.totalSize_instr]
      have hlt : 4 * lkm.totalSize pre < 2 ^ 64 := by rw [htw] at hpc64; omega
      have hstep := step_item_instr_lm lkm env.hrom pre post
        (.aluImm .addi AbiReg.a0 AbiReg.zero 0#12) hlink hlt st hpc
      let st1 := stepReg st AbiReg.a0 0#64 (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
      have hres0 : evalAluImm .addi (st.getReg AbiReg.zero) 0#12 = 0#64 := by
        rw [getReg_zero st]; decide
      have hrun : RV64.run env.rom 1 st = .cont st1 := by
        apply run_one_cont; rw [hstep]
        simp only [execInstr, hres0, pc_add_4_ofNat st.pc hpc, st1, stepReg]
      refine ⟨1, st1, hrun, ?_, ?_, ?_, ?_⟩
      · simp only [htw]; rfl
      · exact ⟨getReg_stepReg_ne st AbiReg.a0 AbiReg.gp (by decide) _ _,
               getReg_stepReg_ne st AbiReg.a0 AbiReg.sp (by decide) _ _,
               getReg_stepReg_ne st AbiReg.a0 AbiReg.s0 (by decide) _ _,
               getReg_stepReg_ne st AbiReg.a0 AbiReg.s2 (by decide) _ _⟩
      · refine ⟨fun i hi => ?_, fun i hlo hhi => by simp [maxRes] at hlo hhi; omega⟩
        have hi0 : i = 0 := by simp [maxRes] at hi; omega
        subst hi0
        simpa [resReg] using getReg_stepReg_eq st AbiReg.a0 (by decide) 0#64 _
      · have hm : st1.mem = st.mem := setReg_mem st AbiReg.a0 0#64
        rw [hm]; exact MemEqOutside.refl _ _
    · have hco : copyTempsToResults env.tab nl tmp 0 = [] := by
        simp [copyTempsToResults, hnres]
      refine ⟨0, st, by simp [RV64.run], ?_, PreservedRegs.refl st, ?_, MemEqOutside.refl _ _⟩
      · simp [hco, lkm.totalSize_nil, hpc]
      · refine ⟨fun i hi => by omega, fun i hlo hhi => by omega⟩
  · have hpos : 0 < vs.length := Nat.pos_of_ne_zero hlen
    rw [copyTempsToResults_eq_flatMap env.tab nl tmp vs.length hpos] at hlink ⊢
    obtain ⟨k, st', hrun, hpc', hpres, hreg, hmem, hout⟩ :=
      copyTempsToResults_prefix_sim env L hal hlim htop hcnt vs rfl
        (min vs.length env.tab.nres) (Nat.min_le_right _ _) pre post hlink st hpc hgp hsp hslots
    have hmax : max 1 vs.length = vs.length := by omega
    refine ⟨k, st', hrun, hpc', hpres, ⟨fun i hi => hreg i (by omega), fun i hlo hhi => hmem i hlo (by omega)⟩, hout⟩

def copyOneResultItem (tab : Tab) (p : _root_.L.Var × Nat) : List AsmItem :=
  if p.2 < tab.nres then
    if p.2 < maxRes then storeMemOff .sd AbiReg.sp (resReg p.2) AbiReg.t0 (slotOff p.1)
    else
      loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (tab.resOff p.2) ++
      storeMemOff .sd AbiReg.sp AbiReg.t1 AbiReg.t2 (slotOff p.1)
  else
    storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t0 (slotOff p.1)

def copyResultsLoop (tab : Tab) (xs : List _root_.L.Var) (start : Nat) : List AsmItem :=
  ((xs.zipIdx start).map (copyOneResultItem tab)).flatten

theorem vs_drop_headD (vs : List _root_.L.Word) (start : Nat) :
    (vs.drop start).headD 0 = vs.getD start 0 := by
  induction vs generalizing start with
  | nil => simp [List.getD]
  | cons v vs ih =>
    cases start with
    | zero => simp [List.getD]
    | succ s => exact ih s

theorem vs_drop_tail (vs : List _root_.L.Word) (start : Nat) :
    (vs.drop start).tail = vs.drop (start + 1) := by
  induction vs generalizing start with
  | nil => simp
  | cons v vs ih =>
    cases start with
    | zero => simp
    | succ s => exact ih s

theorem copyResultsLoop_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    {sp : BitVec 64} {nl nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (vs : List _root_.L.Word) (hvlen : vs.length ≤ env.tab.nres) (m0 : _root_.L.Mem) :
    ∀ (xs : List _root_.L.Var) (start : Nat), (∀ x ∈ xs, x < nl) →
      start + xs.length ≤ max 1 vs.length →
      ∀ (pre post : List AsmItem),
        lkm.linkSpec (pre ++ copyResultsLoop env.tab xs start ++ post) = .ok (env.code, env.labels) →
      ∀ (loc : _root_.L.Locals) (st : State),
        st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
        st.getReg AbiReg.gp = L.T → st.getReg AbiReg.sp = sp →
        ResultsInState env.tab L st vs → ProgFrameOk L sp st.mem nl loc →
      ∃ k st',
        RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (copyResultsLoop env.tab xs start))) ∧
        PreservedRegs st st' ∧
        ResultsInState env.tab L st' vs ∧
        ProgFrameOk L sp st'.mem nl (({ mem := m0, loc := loc } : _root_.L.St).setLocs xs (vs.drop start)).loc ∧
        MemEqOutside (frameSpan sp nl nt) st.mem st'.mem := by
  intro xs
  induction xs with
  | nil =>
    intro start _ _ pre post _ loc st hpc _ _ hres hf
    refine ⟨0, st, by simp [RV64.run], ?_, PreservedRegs.refl st, hres, ?_, MemEqOutside.refl _ _⟩
    · simp [copyResultsLoop, lkm.totalSize_nil, hpc]
    · simp [_root_.L.St.setLocs]; exact hf
  | cons x rest ih =>
    intro start hxs hxsAr pre post hlink loc st hpc hgp hsp hres hf
    have hcl : copyResultsLoop env.tab (x :: rest) start =
        copyOneResultItem env.tab (x, start) ++ copyResultsLoop env.tab rest (start + 1) := by
      simp [copyResultsLoop, List.zipIdx_cons]
    rw [hcl] at hlink ⊢
    have ⟨hl1, hl2⟩ := linkResolved_mid_split lkm pre _ _ post hlink
    have hpc1 := linkResolved_sub_pc64 env pre _ _ hl1
    have hxlt : x < nl := hxs x (by simp)
    have hxlt1 : 1 + x < 1 + nl + nt :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hxlt 1) (Nat.le_add_right (1 + nl) nt)
    have halX : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff x)) 8 = true := by
      rw [hsp]; exact isAligned8_add_int_mul8 sp hal (1 + x)
    have hframeValid : (frameSpan sp nl nt).valid := Nat.le_trans htop L.hStackValid
    have hslotSub : (slotSpan sp (1 + x)).sub (frameSpan sp nl nt) := slotSpan_sub_frame hxlt1
    have hdisjRes : ∀ i, maxRes ≤ i → i < env.tab.nres → ∀ k, k < 8 →
        ¬(frameSpan sp nl nt).contains (L.T + BitVec.ofInt 64 (env.tab.resOff i) + BitVec.ofNat 64 k) := by
      intro i hlo hhi k hk hc
      have hcStack := (L.frame_sub_stackSpan hlim htop) _ hc
      have hcTab := L.resGlob_sub_tab _ (resGlobSpan_contains_resOff L hlo hhi hk)
      exact MemSpan.disjoint_to_memDisjoint L.tabSpan_valid L.stackSpan_valid L.htabDisjStack _ hcTab hcStack
    have ⟨k1, st1, hrun1, hpc1', hpres1, hres1, hf1, hout1⟩ :
        ∃ k1 st1,
          RV64.run env.rom k1 st = .cont st1 ∧
          st1.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (copyOneResultItem env.tab (x, start)))) ∧
          PreservedRegs st st1 ∧
          ResultsInState env.tab L st1 vs ∧
          ProgFrameOk L sp st1.mem nl (fun y => if y = x then vs.getD start 0 else loc y) ∧
          MemEqOutside (frameSpan sp nl nt) st.mem st1.mem := by
      by_cases hst : start < env.tab.nres
      · by_cases hmx : start < maxRes
        · have hco : copyOneResultItem env.tab (x, start) =
              storeMemOff .sd AbiReg.sp (resReg start) AbiReg.t0 (slotOff x) := by
            simp [copyOneResultItem, hst, hmx]
          rw [hco] at hl1 hpc1 ⊢
          have hrn := resReg_ne_preserved start
          obtain ⟨st1, hrun1, hoth1, hmem1, hnpc1⟩ :=
            storeMemOff_sd_correct_lm lkm env.hrom pre _ AbiReg.sp (resReg start) AbiReg.t0
              (by decide) (by decide) hrn.2.2.2.2.2.1.symm (slotOff x) hl1 hpc1 st hpc halX
          have hvalEq : st.getReg (resReg start) = (vs.getD start 0).toBitVec :=
            hres.1 start (by simp only [List.length_cons] at hxsAr; omega)
          have houtSlot : MemEqOutside (frameSpan sp nl nt) st.mem st1.mem := by
            rw [hmem1, hsp, hvalEq]
            exact MemEqOutside.writeWord64 _ _ _ fun k hk => hslotSub _ ⟨k, hk, by
              simp only [slotSpan, slotAddr, slotOff_ofInt]⟩
          refine ⟨lkm.totalSize (storeMemOff .sd AbiReg.sp (resReg start) AbiReg.t0 (slotOff x)), st1,
            hrun1, hnpc1,
            ⟨hoth1 _ (by decide), hoth1 _ (by decide), hoth1 _ (by decide), hoth1 _ (by decide)⟩,
            resultsInState_mem (fun i hi => hoth1 _ (resReg_ne_preserved i).2.2.2.2.2.1) hdisjRes houtSlot hres,
            ?_, houtSlot⟩
          rw [hmem1, hsp, hvalEq]
          exact ProgFrameOk.of_setLoc L hframeValid x hxlt _ hf
        · have hge : maxRes ≤ start := by omega
          have hco : copyOneResultItem env.tab (x, start) =
              loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.resOff start) ++
              storeMemOff .sd AbiReg.sp AbiReg.t1 AbiReg.t2 (slotOff x) := by
            simp [copyOneResultItem, hst, hmx]
          rw [hco] at hl1 hpc1 ⊢
          have ⟨ha1, ha2⟩ := linkResolved_mid_split lkm pre _ _ _ hl1
          have hpa1 := linkResolved_sub_pc64 env pre _ _ ha1
          have halR : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.resOff start)) 8 = true := by
            rw [hgp]; exact isAligned8_of_resOff L hge hst
          obtain ⟨stm, hrunm, hothm, hvalm, hmemm, hnpcm⟩ :=
            loadMemOff_ld_correct_lm lkm env.hrom pre _ AbiReg.t1 AbiReg.gp AbiReg.t2
              (by decide) (by decide) (by decide) (env.tab.resOff start) ha1 hpa1 st hpc halR
          have hspM : stm.getReg AbiReg.sp = sp := (hothm _ (by decide) (by decide)).trans hsp
          have halX' : isAligned (stm.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff x)) 8 = true := by
            rw [hspM]; exact isAligned8_add_int_mul8 sp hal (1 + x)
          have hpa2 := linkResolved_sub_pc64 env (pre ++ _) _ _ ha2
          obtain ⟨st1, hrun1, hoth1, hmem1, hnpc1⟩ :=
            storeMemOff_sd_correct_lm lkm env.hrom (pre ++ _) _ AbiReg.sp AbiReg.t1 AbiReg.t2
              (by decide) (by decide) (by decide) (slotOff x) ha2 hpa2 stm
              (by simpa [lkm.totalSize_append] using hnpcm) halX'
          have hvalEq : stm.getReg AbiReg.t1 = (vs.getD start 0).toBitVec := by
            rw [hvalm, hgp]
            exact hres.2 start hge (by simp at hxsAr; omega)
          have houtSlot : MemEqOutside (frameSpan sp nl nt) st.mem st1.mem := by
            rw [hmem1, hmemm, hspM, hvalEq]
            exact MemEqOutside.writeWord64 _ _ _ fun k hk => hslotSub _ ⟨k, hk, by
              simp only [slotSpan, slotAddr, slotOff_ofInt]⟩
          refine ⟨lkm.totalSize (loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.resOff start)) +
              lkm.totalSize (storeMemOff .sd AbiReg.sp AbiReg.t1 AbiReg.t2 (slotOff x)), st1,
            by rw [run_add, hrunm]; dsimp only; exact hrun1,
            by simpa [lkm.totalSize_append, Nat.add_assoc] using hnpc1,
            ⟨(hoth1 _ (by decide)).trans (hothm _ (by decide) (by decide)),
             (hoth1 _ (by decide)).trans (hothm _ (by decide) (by decide)),
             (hoth1 _ (by decide)).trans (hothm _ (by decide) (by decide)),
             (hoth1 _ (by decide)).trans (hothm _ (by decide) (by decide))⟩,
            resultsInState_mem
              (fun i hi => by
                have hrn := resReg_ne_preserved i
                exact (hoth1 _ hrn.2.2.2.2.2.2.2).trans (hothm _ hrn.2.2.2.2.2.2.1 hrn.2.2.2.2.2.2.2))
              hdisjRes houtSlot hres,
            ?_, houtSlot⟩
          rw [hmem1, hmemm, hspM, hvalEq]
          exact ProgFrameOk.of_setLoc L hframeValid x hxlt _ hf
      · have hco : copyOneResultItem env.tab (x, start) =
            storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t0 (slotOff x) := by
          simp [copyOneResultItem, hst]
        rw [hco] at hl1 hpc1 ⊢
        obtain ⟨st1, hrun1, hoth1, hmem1, hnpc1⟩ :=
          storeMemOff_sd_correct_lm lkm env.hrom pre _ AbiReg.sp AbiReg.zero AbiReg.t0
            (by decide) (by decide) (by decide) (slotOff x) hl1 hpc1 st hpc halX
        have hzeroReg : st.getReg AbiReg.zero = 0#64 := getReg_zero st
        have hzeroVal : (vs.getD start 0).toBitVec = 0#64 := by
          simp [List.getD, List.getElem?_eq_none (by omega : vs.length ≤ start)]
        have houtSlot : MemEqOutside (frameSpan sp nl nt) st.mem st1.mem := by
          rw [hmem1, hsp, hzeroReg, ← hzeroVal]
          exact MemEqOutside.writeWord64 _ _ _ fun k hk => hslotSub _ ⟨k, hk, by
            simp only [slotSpan, slotAddr, slotOff_ofInt]⟩
        refine ⟨lkm.totalSize (storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t0 (slotOff x)), st1,
          hrun1, hnpc1,
          ⟨hoth1 _ (by decide), hoth1 _ (by decide), hoth1 _ (by decide), hoth1 _ (by decide)⟩,
          resultsInState_mem (fun i hi => hoth1 _ (resReg_ne_preserved i).2.2.2.2.2.1) hdisjRes houtSlot hres,
          ?_, houtSlot⟩
        rw [hmem1, hsp, hzeroReg, ← hzeroVal]
        exact ProgFrameOk.of_setLoc L hframeValid x hxlt _ hf
    obtain ⟨k2, st2, hrun2, hpc2, hpres2, hres2, hf2, hout2⟩ :=
      ih (start + 1) (fun y hy => hxs y (by simp [hy])) (by simp at hxsAr; omega)
        (pre ++ copyOneResultItem env.tab (x, start)) post hl2
        (fun y => if y = x then vs.getD start 0 else loc y) st1
        (by simpa [lkm.totalSize_append] using hpc1')
        (hpres1.gp.trans hgp) (hpres1.sp.trans hsp) hres1 hf1
    refine ⟨k1 + k2, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
      by simpa [lkm.totalSize_append, Nat.add_assoc] using hpc2,
      hpres1.trans hpres2, hres2, ?_, hout1.trans hout2⟩
    have hlocEq : (({ mem := m0, loc := loc } : _root_.L.St).setLocs (x :: rest) (vs.drop start)).loc =
        (({ mem := m0, loc := fun y => if y = x then vs.getD start 0 else loc y } : _root_.L.St).setLocs rest (vs.drop (start + 1))).loc := by
      simp [_root_.L.St.setLocs, _root_.L.St.setLoc]
    rwa [hlocEq]

def evalWArrTierAsm (tab : Tab) (nl tmp : Nat) : _root_.L.WArr → List AsmItem
  | .plain _ => storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t0 (slotOff (nl + tmp))
  | .tier _ t => compileE tab nl tmp t ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + tmp))

theorem evalWArrTierAsm_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl tmp nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (w : _root_.L.WArr) (hwOk : warrOkB env.tab nl w = true)
    (htmp : tmp + (match w with | .plain _ => 1 | .tier _ t => max 1 (maxTempsExpr t)) ≤ nt)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ evalWArrTierAsm env.tab nl tmp w ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOk L sp st.mem nl loc) :
    match w with
    | .plain a =>
      ∃ k st',
        RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (evalWArrTierAsm env.tab nl tmp (.plain a)))) ∧
        readWord64 st'.mem (sp + BitVec.ofInt 64 (slotOff (nl + tmp))) = 0#64 ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
    | .tier a t =>
      match _root_.L.evalE t { mem := lm, loc := loc } with
      | .ok (vt, _) =>
        ∃ k st',
          RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (evalWArrTierAsm env.tab nl tmp (.tier a t)))) ∧
          readWord64 st'.mem (sp + BitVec.ofInt 64 (slotOff (nl + tmp))) = vt.toBitVec ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
      | .error _ =>
        ∃ k st',
          RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem := by
  cases w with
  | plain a =>
    simp only [evalWArrTierAsm] at hlink ⊢
    have hpc64 := linkResolved_sub_pc64 env pre _ post hlink
    have halX : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff (nl + tmp))) 8 = true := by
      rw [hsp]; exact isAligned8_add_int_mul8 sp hal (1 + (nl + tmp))
    obtain ⟨st', hrun, hoth, hmem, hnpc⟩ :=
      storeMemOff_sd_correct_lm lkm env.hrom pre post AbiReg.sp AbiReg.zero AbiReg.t0
        (by decide) (by decide) (by decide) (slotOff (nl + tmp)) hlink hpc64 st hpc halX
    have hzero : st.getReg AbiReg.zero = 0#64 := getReg_zero st
    have hout : MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem := by
      rw [hmem, hsp]
      exact MemEqOutside.writeWord64 _ _ _ fun k hk => by
        rw [slotOff_ofInt]
        exact tempSpan_slot_sub (Nat.le_refl tmp) (by dsimp only at htmp; omega) k hk
    refine ⟨lkm.totalSize (storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t0 (slotOff (nl + tmp))), st',
      hrun, hnpc, ?_, ⟨hoth _ (by decide), hoth _ (by decide), hoth _ (by decide), hoth _ (by decide)⟩, hout⟩
    rw [hmem, hsp, hzero]
    exact readWord64_writeWord64_self _ _ _
  | tier a t =>
    simp only [evalWArrTierAsm] at hlink ⊢
    simp only [warrOkB, Bool.and_eq_true] at hwOk
    dsimp only at htmp
    have htmpLe : tmp + maxTempsExpr t ≤ nt := Nat.le_trans (Nat.add_le_add_left (Nat.le_max_right 1 _) tmp) htmp
    have ⟨hl1, hl2⟩ := linkResolved_mid_split lkm pre _ _ post hlink
    have hpc1 := linkResolved_sub_pc64 env pre _ _ hl1
    have hsim := progEvalExpr_sim env L lm loc hal hlim htop t pre _ tmp hwOk.2 htmpLe hl1 hpc1 st hpc hgp hsp hm hf
    cases he : _root_.L.evalE t { mem := lm, loc := loc } with
    | error err =>
      rw [he] at hsim; exact hsim
    | ok res =>
      rcases res with ⟨vt, st1'⟩
      rw [he] at hsim
      obtain ⟨k1, st1, hrun1, hpc1', ha0, hpres1, hout1⟩ := hsim
      have hsp1 : st1.getReg AbiReg.sp = sp := hpres1.sp.trans hsp
      have halX : isAligned (st1.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff (nl + tmp))) 8 = true := by
        rw [hsp1]; exact isAligned8_add_int_mul8 sp hal (1 + (nl + tmp))
      have hpc2 := linkResolved_sub_pc64 env (pre ++ _) _ post hl2
      obtain ⟨st2, hrun2, hoth2, hmem2, hnpc2⟩ :=
        storeMemOff_sd_correct_lm lkm env.hrom (pre ++ _) post AbiReg.sp AbiReg.a0 AbiReg.t0
          (by decide) (by decide) (by decide) (slotOff (nl + tmp)) hl2 hpc2 st1
          (by simpa [lkm.totalSize_append] using hpc1') halX
      have hout2 : MemEqOutside (tempSpan sp nl tmp nt) st1.mem st2.mem := by
        rw [hmem2, hsp1]
        exact MemEqOutside.writeWord64 _ _ _ fun k hk => by
          rw [slotOff_ofInt]
          exact tempSpan_slot_sub (Nat.le_refl tmp) (by omega) k hk
      refine ⟨k1 + lkm.totalSize (storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + tmp))), st2,
        by rw [run_add, hrun1]; dsimp only; exact hrun2,
        by simpa [lkm.totalSize_append, Nat.add_assoc] using hnpc2,
        ?_,
        hpres1.trans ⟨hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide)⟩,
        hout1.trans hout2⟩
      rw [hmem2, hsp1, ha0]
      exact readWord64_writeWord64_self _ _ _

theorem prog_set_zero_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (x : _root_.L.Var) (hx : x < nl) (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t0 (slotOff x) ++ post) =
      .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOk L sp st.mem nl loc) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre +
        lkm.totalSize (storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t0 (slotOff x)))) ∧
      PreservedRegs st st' ∧
      ProgMemRel env.tab L st'.mem lm ∧
      ProgFrameOk L sp st'.mem nl (fun y => if y = x then 0 else loc y) ∧
      ProgMemOutside (FnWriteMask L sp nl nt) st.mem st'.mem := by
  have halX : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff x)) 8 = true := by
    rw [hsp]; exact isAligned8_add_int_mul8 sp hal (1 + x)
  have hpc2 := linkResolved_sub_pc64 env pre _ post hlink
  obtain ⟨st2, hrun2, hoth2, hmem2, hnpc2⟩ :=
    storeMemOff_sd_correct_lm lkm env.hrom pre post AbiReg.sp AbiReg.zero AbiReg.t0
      (by decide) (by decide) (by decide) (slotOff x) hlink hpc2 st hpc halX
  have hframeValid : (frameSpan sp nl nt).valid := Nat.le_trans htop L.hStackValid
  have hxlt1 : 1 + x < 1 + nl + nt :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left hx 1) (Nat.le_add_right (1 + nl) nt)
  have houtSlot : MemEqOutside (slotSpan sp (1 + x)) st.mem st2.mem := by
    rw [hmem2, hsp]
    exact MemEqOutside.writeWord64 _ _ _ fun k hk => ⟨k, hk, by simp only [slotSpan, slotAddr, slotOff_ofInt]⟩
  have hpm2 : ProgMemOutside (FnWriteMask L sp nl nt) st.mem st2.mem :=
    ProgMemOutside.of_memEqOutside (fun a ha => by
      obtain ⟨k, hk, rfl⟩ := ha; simp only [slotSpan] at hk
      exact L.fnWriteMask_of_slot hlim htop (Nat.le_add_right 1 x) hxlt1 k hk) houtSlot
  refine ⟨lkm.totalSize (storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t0 (slotOff x)), st2,
    hrun2, hnpc2,
    ⟨hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide)⟩,
    ?_, ?_, hpm2⟩
  · rw [hmem2, hsp, show st.getReg AbiReg.zero = (0 : _root_.L.Word).toBitVec from rfl, slotOff_ofInt]
    exact ProgMemRel.of_stack_write L hlim htop hxlt1 _ hm
  · rw [hmem2, hsp, show st.getReg AbiReg.zero = (0 : _root_.L.Word).toBitVec from rfl]
    exact ProgFrameOk.of_setLoc L hframeValid x hx 0 hf

theorem prog_gset_zero_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (g : _root_.L.GVar) (hg : g.id < env.tab.ng) (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (env.tab.globOff g) ++ post) =
      .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOk L sp st.mem nl loc) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre +
        lkm.totalSize (storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (env.tab.globOff g)))) ∧
      PreservedRegs st st' ∧
      ProgMemRel env.tab L st'.mem (lm.setG g 0) ∧
      ProgFrameOk L sp st'.mem nl loc ∧
      ProgMemOutside (FnWriteMask L sp nl nt) st.mem st'.mem := by
  have halG : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.globOff g)) 8 = true := by
    rw [hgp]; exact isAligned8_of_globOff L g
  have hpc2 := linkResolved_sub_pc64 env pre _ post hlink
  obtain ⟨st2, hrun2, hoth2, hmem2, hnpc2⟩ :=
    storeMemOff_sd_correct_lm lkm env.hrom pre post AbiReg.gp AbiReg.zero AbiReg.t0
      (by decide) (by decide) (by decide) (env.tab.globOff g) hlink hpc2 st hpc halG
  have houtRg : MemEqOutside L.resGlobSpan st.mem st2.mem := by
    rw [hmem2, hgp]
    exact MemEqOutside.writeWord64 _ _ _ fun k hk => resGlobSpan_contains_globOff L g hg hk
  refine ⟨lkm.totalSize (storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (env.tab.globOff g)), st2,
    hrun2, hnpc2,
    ⟨hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide)⟩,
    ?_, progFrameOk_of_resGlob L hlim htop houtRg hf, progMemOutside_of_resGlob L sp nl nt houtRg⟩
  rw [hmem2, hgp, show st.getReg AbiReg.zero = (0 : _root_.L.Word).toBitVec from rfl]
  exact ProgMemRel.setG hm g hg 0

theorem prog_set_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (x : _root_.L.Var) (e : _root_.L.Expr) (hx : x < nl) (heOk : exprOkB env.tab nl e = true)
    (hnt : maxTempsExpr e ≤ nt) (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ (compileE env.tab nl 0 e ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff x)) ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOk L sp st.mem nl loc) :
    match _root_.L.evalE e { mem := lm, loc := loc } with
    | .ok (v, _) =>
      ∃ k st',
        RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl 0 e ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff x)))) ∧
        PreservedRegs st st' ∧
        ProgMemRel env.tab L st'.mem lm ∧
        ProgFrameOk L sp st'.mem nl (fun y => if y = x then v else loc y) ∧
        ProgMemOutside (FnWriteMask L sp nl nt) st.mem st'.mem
    | .error _ =>
      ∃ k st',
        RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' := by
  have ⟨hl1, hl2⟩ := linkResolved_mid_split lkm pre _ _ post hlink
  have hpc1 := linkResolved_sub_pc64 env pre _ _ hl1
  have hsim := progEvalExpr_sim env L lm loc hal hlim htop e pre _ 0 heOk (by omega) hl1 hpc1 st hpc hgp hsp hm hf
  cases he : _root_.L.evalE e { mem := lm, loc := loc } with
  | error err =>
    rw [he] at hsim; obtain ⟨k, st', hrun, hpc', hpres, _⟩ := hsim; exact ⟨k, st', hrun, hpc', hpres⟩
  | ok res =>
    rcases res with ⟨v, st1'⟩
    rw [he] at hsim
    obtain ⟨k1, st1, hrun1, hpc1', ha0, hpres1, hout1⟩ := hsim
    have hsp1 : st1.getReg AbiReg.sp = sp := hpres1.sp.trans hsp
    have halX : isAligned (st1.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff x)) 8 = true := by
      rw [hsp1]; exact isAligned8_add_int_mul8 sp hal (1 + x)
    have hpc2 := linkResolved_sub_pc64 env (pre ++ _) _ post hl2
    obtain ⟨st2, hrun2, hoth2, hmem2, hnpc2⟩ :=
      storeMemOff_sd_correct_lm lkm env.hrom (pre ++ _) post AbiReg.sp AbiReg.a0 AbiReg.t0
        (by decide) (by decide) (by decide) (slotOff x) hl2 hpc2 st1
        (by simpa [lkm.totalSize_append] using hpc1') halX
    have hframeValid : (frameSpan sp nl nt).valid := Nat.le_trans htop L.hStackValid
    have hm1 : ProgMemRel env.tab L st1.mem lm :=
      ProgMemRel.of_stack_eqOutside (MemSpan.sub_trans (tempSpan_sub_frame (by omega)) (L.frame_sub_stackSpan hlim htop)) hout1 hm
    have hf1 : ProgFrameOk L sp st1.mem nl loc := ProgFrameOk.of_tempSpan hframeValid (by omega) hout1 hf
    have hpm1 : ProgMemOutside (FnWriteMask L sp nl nt) st.mem st1.mem :=
      ProgMemOutside.of_memEqOutside (L.fnWriteMask_of_tempSpan hlim htop (by omega)) hout1
    have hxlt1 : 1 + x < 1 + nl + nt :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hx 1) (Nat.le_add_right (1 + nl) nt)
    have houtSlot : MemEqOutside (slotSpan sp (1 + x)) st1.mem st2.mem := by
      rw [hmem2, hsp1]
      exact MemEqOutside.writeWord64 _ _ _ fun k hk => ⟨k, hk, by
        simp only [slotSpan, slotAddr, slotOff_ofInt]⟩
    have hpm2 : ProgMemOutside (FnWriteMask L sp nl nt) st1.mem st2.mem :=
      ProgMemOutside.of_memEqOutside (fun a ha => by
        obtain ⟨k, hk, rfl⟩ := ha
        simp only [slotSpan] at hk
        exact L.fnWriteMask_of_slot hlim htop (Nat.le_add_right 1 x) hxlt1 k hk) houtSlot
    refine ⟨k1 + lkm.totalSize (storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff x)), st2,
      by rw [run_add, hrun1]; dsimp only; exact hrun2,
      by simpa [lkm.totalSize_append, Nat.add_assoc] using hnpc2,
      hpres1.trans ⟨hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide)⟩,
      ?_, ?_, hpm1.trans hpm2⟩
    · rw [hmem2, hsp1, ha0, slotOff_ofInt]
      exact ProgMemRel.of_stack_write L hlim htop hxlt1 v.toBitVec hm1
    · rw [hmem2, hsp1, ha0]
      exact ProgFrameOk.of_setLoc L hframeValid x hx v hf1

theorem prog_gset_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (g : _root_.L.GVar) (e : _root_.L.Expr) (hg : g.id < env.tab.ng) (heOk : exprOkB env.tab nl e = true)
    (hnt : maxTempsExpr e ≤ nt) (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ (compileE env.tab nl 0 e ++ storeMemOff .sd AbiReg.gp AbiReg.a0 AbiReg.t0 (env.tab.globOff g)) ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOk L sp st.mem nl loc) :
    match _root_.L.evalE e { mem := lm, loc := loc } with
    | .ok (v, _) =>
      ∃ k st',
        RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileE env.tab nl 0 e ++ storeMemOff .sd AbiReg.gp AbiReg.a0 AbiReg.t0 (env.tab.globOff g)))) ∧
        PreservedRegs st st' ∧
        ProgMemRel env.tab L st'.mem (lm.setG g v) ∧
        ProgFrameOk L sp st'.mem nl loc ∧
        ProgMemOutside (FnWriteMask L sp nl nt) st.mem st'.mem
    | .error _ =>
      ∃ k st',
        RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' := by
  have ⟨hl1, hl2⟩ := linkResolved_mid_split lkm pre _ _ post hlink
  have hpc1 := linkResolved_sub_pc64 env pre _ _ hl1
  have hsim := progEvalExpr_sim env L lm loc hal hlim htop e pre _ 0 heOk (by omega) hl1 hpc1 st hpc hgp hsp hm hf
  cases he : _root_.L.evalE e { mem := lm, loc := loc } with
  | error err =>
    rw [he] at hsim; obtain ⟨k, st', hrun, hpc', hpres, _⟩ := hsim; exact ⟨k, st', hrun, hpc', hpres⟩
  | ok res =>
    rcases res with ⟨v, st1'⟩
    rw [he] at hsim
    obtain ⟨k1, st1, hrun1, hpc1', ha0, hpres1, hout1⟩ := hsim
    have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.gp.trans hgp
    have halG : isAligned (st1.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.globOff g)) 8 = true := by
      rw [hgp1]; exact isAligned8_of_globOff L g
    have hpc2 := linkResolved_sub_pc64 env (pre ++ _) _ post hl2
    obtain ⟨st2, hrun2, hoth2, hmem2, hnpc2⟩ :=
      storeMemOff_sd_correct_lm lkm env.hrom (pre ++ _) post AbiReg.gp AbiReg.a0 AbiReg.t0
        (by decide) (by decide) (by decide) (env.tab.globOff g) hl2 hpc2 st1
        (by simpa [lkm.totalSize_append] using hpc1') halG
    have hframeValid : (frameSpan sp nl nt).valid := Nat.le_trans htop L.hStackValid
    have hm1 : ProgMemRel env.tab L st1.mem lm :=
      ProgMemRel.of_stack_eqOutside (MemSpan.sub_trans (tempSpan_sub_frame (by omega)) (L.frame_sub_stackSpan hlim htop)) hout1 hm
    have hf1 : ProgFrameOk L sp st1.mem nl loc := ProgFrameOk.of_tempSpan hframeValid (by omega) hout1 hf
    have hpm1 : ProgMemOutside (FnWriteMask L sp nl nt) st.mem st1.mem :=
      ProgMemOutside.of_memEqOutside (L.fnWriteMask_of_tempSpan hlim htop (by omega)) hout1
    have houtRg : MemEqOutside L.resGlobSpan st1.mem st2.mem := by
      rw [hmem2, hgp1]
      exact MemEqOutside.writeWord64 _ _ _ fun k hk => resGlobSpan_contains_globOff L g hg hk
    have hpm2 : ProgMemOutside (FnWriteMask L sp nl nt) st1.mem st2.mem :=
      progMemOutside_of_resGlob L sp nl nt houtRg
    refine ⟨k1 + lkm.totalSize (storeMemOff .sd AbiReg.gp AbiReg.a0 AbiReg.t0 (env.tab.globOff g)), st2,
      by rw [run_add, hrun1]; dsimp only; exact hrun2,
      by simpa [lkm.totalSize_append, Nat.add_assoc] using hnpc2,
      hpres1.trans ⟨hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide)⟩,
      ?_, progFrameOk_of_resGlob L hlim htop houtRg hf1, hpm1.trans hpm2⟩
    rw [hmem2, hgp1, ha0]
    exact ProgMemRel.setG hm1 g hg v

@[reducible] private def NonPreservedReg (r : Reg) : Prop :=
  r ≠ 0#5 ∧ r ≠ AbiReg.gp ∧ r ≠ AbiReg.sp ∧ r ≠ AbiReg.s0 ∧ r ≠ AbiReg.s1 ∧ r ≠ AbiReg.s2

theorem nonPreserved_t0 : NonPreservedReg AbiReg.t0 := by decide
theorem nonPreserved_t1 : NonPreservedReg AbiReg.t1 := by decide
theorem nonPreserved_t2 : NonPreservedReg AbiReg.t2 := by decide
theorem nonPreserved_t3 : NonPreservedReg AbiReg.t3 := by decide
theorem nonPreserved_t4 : NonPreservedReg AbiReg.t4 := by decide
theorem nonPreserved_t5 : NonPreservedReg AbiReg.t5 := by decide

theorem run_alu_step {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (op : AluOp) (rd rs1 rs2 : Reg) (hnp : NonPreservedReg rd)
    (hlink : lkm.linkSpec (pre ++ [AsmItem.instr (.alu op rd rs1 rs2)] ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre)) :
    let st' := stepReg st rd (evalAlu op (st.getReg rs1) (st.getReg rs2)) (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
    RV64.run env.rom 1 st = .cont st' ∧
    st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)) ∧
    st'.getReg rd = evalAlu op (st.getReg rs1) (st.getReg rs2) ∧
    (∀ q, q ≠ rd → st'.getReg q = st.getReg q) ∧
    st'.mem = st.mem ∧
    PreservedRegs st st' := by
  have hpc64 := linkResolved_sub_pc64 env pre [AsmItem.instr (.alu op rd rs1 rs2)] post hlink
  have htw : lkm.totalSize [AsmItem.instr (.alu op rd rs1 rs2)] = 1 := lkm.totalSize_instr _
  have hlt : 4 * lkm.totalSize pre < 2 ^ 64 := by rw [htw] at hpc64; omega
  have hstep := step_item_instr_lm lkm env.hrom pre post (.alu op rd rs1 rs2) hlink hlt st hpc
  let st' := stepReg st rd (evalAlu op (st.getReg rs1) (st.getReg rs2)) (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
  have hrun : RV64.run env.rom 1 st = .cont st' := by
    apply run_one_cont; rw [hstep]
    simp only [execInstr, pc_add_4_ofNat st.pc hpc, st', stepReg, setReg_mem]
  refine ⟨hrun, rfl, getReg_stepReg_eq st rd hnp.1 _ _,
    fun q hq => getReg_stepReg_ne st rd q hq _ _, by simp [stepReg, setReg_mem],
    ⟨getReg_stepReg_ne st rd AbiReg.gp hnp.2.1.symm _ _,
     getReg_stepReg_ne st rd AbiReg.sp hnp.2.2.1.symm _ _,
     getReg_stepReg_ne st rd AbiReg.s0 hnp.2.2.2.1.symm _ _,
     getReg_stepReg_ne st rd AbiReg.s2 hnp.2.2.2.2.2.symm _ _⟩⟩

theorem run_aluImm_step {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (op : AluImmOp) (rd rs1 : Reg) (imm : BitVec 12) (hnp : NonPreservedReg rd)
    (hlink : lkm.linkSpec (pre ++ [AsmItem.instr (.aluImm op rd rs1 imm)] ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre)) :
    let st' := stepReg st rd (evalAluImm op (st.getReg rs1) imm) (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
    RV64.run env.rom 1 st = .cont st' ∧
    st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)) ∧
    st'.getReg rd = evalAluImm op (st.getReg rs1) imm ∧
    (∀ q, q ≠ rd → st'.getReg q = st.getReg q) ∧
    st'.mem = st.mem ∧
    PreservedRegs st st' := by
  have hpc64 := linkResolved_sub_pc64 env pre [AsmItem.instr (.aluImm op rd rs1 imm)] post hlink
  have htw : lkm.totalSize [AsmItem.instr (.aluImm op rd rs1 imm)] = 1 := lkm.totalSize_instr _
  have hlt : 4 * lkm.totalSize pre < 2 ^ 64 := by rw [htw] at hpc64; omega
  have hstep := step_item_instr_lm lkm env.hrom pre post (.aluImm op rd rs1 imm) hlink hlt st hpc
  let st' := stepReg st rd (evalAluImm op (st.getReg rs1) imm) (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
  have hrun : RV64.run env.rom 1 st = .cont st' := by
    apply run_one_cont; rw [hstep]
    simp only [execInstr, pc_add_4_ofNat st.pc hpc, st', stepReg, setReg_mem]
  refine ⟨hrun, rfl, getReg_stepReg_eq st rd hnp.1 _ _,
    fun q hq => getReg_stepReg_ne st rd q hq _ _, by simp [stepReg, setReg_mem],
    ⟨getReg_stepReg_ne st rd AbiReg.gp hnp.2.1.symm _ _,
     getReg_stepReg_ne st rd AbiReg.sp hnp.2.2.1.symm _ _,
     getReg_stepReg_ne st rd AbiReg.s0 hnp.2.2.2.1.symm _ _,
     getReg_stepReg_ne st rd AbiReg.s2 hnp.2.2.2.2.2.symm _ _⟩⟩

theorem run_shImm_step {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (op : ShiftImmOp) (rd rs1 : Reg) (shamt : BitVec 6) (hnp : NonPreservedReg rd)
    (hlink : lkm.linkSpec (pre ++ [AsmItem.instr (.shImm op rd rs1 shamt)] ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre)) :
    let st' := stepReg st rd (evalShiftImm op (st.getReg rs1) shamt) (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
    RV64.run env.rom 1 st = .cont st' ∧
    st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)) ∧
    st'.getReg rd = evalShiftImm op (st.getReg rs1) shamt ∧
    (∀ q, q ≠ rd → st'.getReg q = st.getReg q) ∧
    st'.mem = st.mem ∧
    PreservedRegs st st' := by
  have hpc64 := linkResolved_sub_pc64 env pre [AsmItem.instr (.shImm op rd rs1 shamt)] post hlink
  have htw : lkm.totalSize [AsmItem.instr (.shImm op rd rs1 shamt)] = 1 := lkm.totalSize_instr _
  have hlt : 4 * lkm.totalSize pre < 2 ^ 64 := by rw [htw] at hpc64; omega
  have hstep := step_item_instr_lm lkm env.hrom pre post (.shImm op rd rs1 shamt) hlink hlt st hpc
  let st' := stepReg st rd (evalShiftImm op (st.getReg rs1) shamt) (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
  have hrun : RV64.run env.rom 1 st = .cont st' := by
    apply run_one_cont; rw [hstep]
    simp only [execInstr, pc_add_4_ofNat st.pc hpc, st', stepReg, setReg_mem]
  refine ⟨hrun, rfl, getReg_stepReg_eq st rd hnp.1 _ _,
    fun q hq => getReg_stepReg_ne st rd q hq _ _, by simp [stepReg, setReg_mem],
    ⟨getReg_stepReg_ne st rd AbiReg.gp hnp.2.1.symm _ _,
     getReg_stepReg_ne st rd AbiReg.sp hnp.2.2.1.symm _ _,
     getReg_stepReg_ne st rd AbiReg.s0 hnp.2.2.2.1.symm _ _,
     getReg_stepReg_ne st rd AbiReg.s2 hnp.2.2.2.2.2.symm _ _⟩⟩

theorem run_br_step {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (op : BranchOp) (rs1 rs2 : Reg) (target : String) (tgt : Nat)
    (hlkp : lookupLabel env.labels target = some tgt)
    (hrs : rs1 ≠ AbiReg.t6 ∧ rs2 ≠ AbiReg.t6)
    (hlink : lkm.linkSpec (pre ++ [Asm.br op rs1 rs2 target] ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre)) :
    ∃ k st', 1 ≤ k ∧
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = (if evalBranch op (st.getReg rs1) (st.getReg rs2) = true
                then BitVec.ofNat 64 (4 * tgt)
                else BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize [Asm.br op rs1 rs2 target]))) ∧
      (∀ q, q ≠ AbiReg.t6 ∧ q ≠ AbiReg.s1 → st'.getReg q = st.getReg q) ∧
      PreservedRegs st st' ∧
      st'.mem = st.mem := by
  have hpc64 := linkResolved_sub_pc64 env pre [Asm.br op rs1 rs2 target] post hlink
  have h64 : 4 * (lkm.totalSize pre + lkm.itemSize (.br op rs1 rs2 target)) < 2 ^ 64 := by
    simpa [Asm.br, lkm.totalSize_singleton] using hpc64
  obtain ⟨k, st', hk, hrun, hpc', hoth, hpres, hmem⟩ :=
    prog_step_br env pre post op rs1 rs2 target tgt hlkp hrs hlink h64 st hpc
  refine ⟨k, st', hk, hrun, ?_, hoth, hpres, hmem⟩
  simpa [Asm.br, lkm.totalSize_singleton] using hpc'

theorem run_ld_zero_step {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (rd rs1 : Reg) (hnp : NonPreservedReg rd)
    (hlink : lkm.linkSpec (pre ++ [Asm.ld rd rs1] ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hal : isAligned (st.getReg rs1) 8 = true) :
    let st' := stepReg st rd (readWord64 st.mem (st.getReg rs1)) (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
    RV64.run env.rom 1 st = .cont st' ∧
    st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)) ∧
    st'.getReg rd = readWord64 st.mem (st.getReg rs1) ∧
    (∀ q, q ≠ rd → st'.getReg q = st.getReg q) ∧
    st'.mem = st.mem ∧
    PreservedRegs st st' := by
  let st' := stepReg st rd (readWord64 st.mem (st.getReg rs1)) (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
  refine ⟨step_ld_zero env pre post rd rs1 hlink st hpc hal, rfl,
    getReg_stepReg_eq st rd hnp.1 _ _,
    fun q hq => getReg_stepReg_ne st rd q hq _ _,
    by simp [stepReg, setReg_mem],
    ⟨getReg_stepReg_ne st rd AbiReg.gp hnp.2.1.symm _ _,
     getReg_stepReg_ne st rd AbiReg.sp hnp.2.2.1.symm _ _,
     getReg_stepReg_ne st rd AbiReg.s0 hnp.2.2.2.1.symm _ _,
     getReg_stepReg_ne st rd AbiReg.s2 hnp.2.2.2.2.2.symm _ _⟩⟩

theorem run_lbu_zero_step {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (rd rs1 : Reg) (hnp : NonPreservedReg rd)
    (hlink : lkm.linkSpec (pre ++ [Asm.lbu rd rs1] ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre)) :
    let st' := stepReg st rd (BitVec.zeroExtend 64 (st.mem (st.getReg rs1))) (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
    RV64.run env.rom 1 st = .cont st' ∧
    st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)) ∧
    st'.getReg rd = BitVec.zeroExtend 64 (st.mem (st.getReg rs1)) ∧
    (∀ q, q ≠ rd → st'.getReg q = st.getReg q) ∧
    st'.mem = st.mem ∧
    PreservedRegs st st' := by
  let st' := stepReg st rd (BitVec.zeroExtend 64 (st.mem (st.getReg rs1))) (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
  refine ⟨step_lbu_zero env pre post rd rs1 hlink st hpc, rfl,
    getReg_stepReg_eq st rd hnp.1 _ _,
    fun q hq => getReg_stepReg_ne st rd q hq _ _,
    by simp [stepReg, setReg_mem],
    ⟨getReg_stepReg_ne st rd AbiReg.gp hnp.2.1.symm _ _,
     getReg_stepReg_ne st rd AbiReg.sp hnp.2.2.1.symm _ _,
     getReg_stepReg_ne st rd AbiReg.s0 hnp.2.2.2.1.symm _ _,
     getReg_stepReg_ne st rd AbiReg.s2 hnp.2.2.2.2.2.symm _ _⟩⟩

theorem prog_evalToTemp_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl tmp nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (e : _root_.L.Expr) (heOk : exprOkB env.tab nl e = true)
    (htmp : tmp + max 1 (maxTempsExpr e) ≤ nt) (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ (compileE env.tab nl tmp e ++
      storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + tmp))) ++ post) =
      .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOk L sp st.mem nl loc) :
    match _root_.L.evalE e { mem := lm, loc := loc } with
    | .ok (v, _) =>
      ∃ k st',
        RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre +
          lkm.totalSize (compileE env.tab nl tmp e ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + tmp))))) ∧
        readWord64 st'.mem (sp + BitVec.ofInt 64 (slotOff (nl + tmp))) = v.toBitVec ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem
    | .error _ =>
      ∃ k st',
        RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem := by
  have ⟨hl1, hl2⟩ := linkResolved_mid_split lkm pre _ _ post hlink
  have hpc1 := linkResolved_sub_pc64 env pre _ _ hl1
  have htmpe : tmp + maxTempsExpr e ≤ nt :=
    Nat.le_trans (Nat.add_le_add_left (Nat.le_max_right 1 _) tmp) htmp
  have hsim := progEvalExpr_sim env L lm loc hal hlim htop e pre _ tmp heOk htmpe hl1 hpc1 st hpc hgp hsp hm hf
  cases he : _root_.L.evalE e { mem := lm, loc := loc } with
  | error err =>
    rw [he] at hsim; exact hsim
  | ok res =>
    rcases res with ⟨v, st1'⟩
    rw [he] at hsim
    obtain ⟨k1, st1, hrun1, hpc1', ha0, hpres1, hout1⟩ := hsim
    have hsp1 : st1.getReg AbiReg.sp = sp := hpres1.sp.trans hsp
    have halX : isAligned (st1.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff (nl + tmp))) 8 = true := by
      rw [hsp1]; exact isAligned8_add_int_mul8 sp hal (1 + (nl + tmp))
    have hpc2 := linkResolved_sub_pc64 env (pre ++ _) _ post hl2
    obtain ⟨st2, hrun2, hoth2, hmem2, hnpc2⟩ :=
      storeMemOff_sd_correct_lm lkm env.hrom (pre ++ _) post AbiReg.sp AbiReg.a0 AbiReg.t0
        (by decide) (by decide) (by decide) (slotOff (nl + tmp)) hl2 hpc2 st1
        (by simpa [lkm.totalSize_append] using hpc1') halX
    have hout2 : MemEqOutside (tempSpan sp nl tmp nt) st1.mem st2.mem := by
      rw [hmem2, hsp1]
      exact MemEqOutside.writeWord64 _ _ _ fun k hk => by
        rw [slotOff_ofInt]
        exact tempSpan_slot_sub (Nat.le_refl tmp) (by omega) k hk
    refine ⟨k1 + lkm.totalSize (storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + tmp))), st2,
      by rw [run_add, hrun1]; dsimp only; exact hrun2,
      by simpa [lkm.totalSize_append, Nat.add_assoc] using hnpc2,
      ?_,
      hpres1.trans ⟨hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide)⟩,
      hout1.trans hout2⟩
    rw [hmem2, hsp1, ha0]
    exact readWord64_writeWord64_self _ _ _

theorem tier_off_val (u : _root_.L.Word) :
    evalShiftImm .slli (evalAluImm .andi u.toBitVec 1#12) 3#6 =
      if (u &&& 1 == 0) = true then 0#64 else 8#64 := by
  have h1 : (sextImm12 1#12) = 1#64 := by decide
  simp only [evalAluImm, evalShiftImm, h1]
  have hb : (u.toBitVec &&& 1#64) = (u &&& 1).toBitVec := (UInt64.toBitVec_and u 1).symm
  rw [hb]
  rcases Nat.mod_two_eq_zero_or_one u.toNat with h0 | h1m
  · have hu : u &&& 1 = 0 := uint64_eq_of_toNat (by
      rw [← UInt64.toNat_toBitVec, ← hb, BitVec.toNat_and, BitVec.toNat_ofNat,
          show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.and_one_is_mod, UInt64.toNat_toBitVec, h0]; rfl)
    rw [hu]
    simp only [beq_self_eq_true, ↓reduceIte]
    decide
  · have hval : (u &&& 1).toNat = 1 := by
      rw [← UInt64.toNat_toBitVec, ← hb, BitVec.toNat_and, BitVec.toNat_ofNat,
          show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.and_one_is_mod, UInt64.toNat_toBitVec, h1m]
    have hbv : (u &&& 1).toBitVec = 1#64 :=
      BitVec.eq_of_toNat_eq (by rw [UInt64.toNat_toBitVec, hval]; rfl)
    have hu : (u &&& 1 == 0) = false := by
      simp only [BEq.beq, decide_eq_false_iff_not]
      intro h; have := congrArg UInt64.toNat h; rw [hval, UInt64.toNat_zero] at this; omega
    rw [hu, hbv]
    simp only [Bool.false_eq_true, ↓reduceIte]
    decide

theorem prog_tierPtr_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (T : RV64.Word) (u : _root_.L.Word)
    (hlink : lkm.linkSpec (pre ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12,
      Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++ post) =
      .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = T) (ht0 : st.getReg AbiReg.t0 = u.toBitVec) :
    ∃ st',
      RV64.run env.rom 3 st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 3)) ∧
      st'.getReg AbiReg.t1 = T + (if (u &&& 1 == 0) = true then 0#64 else 8#64) ∧
      (∀ q, q ≠ AbiReg.t0 → q ≠ AbiReg.t1 → st'.getReg q = st.getReg q) ∧
      st'.mem = st.mem ∧
      PreservedRegs st st' := by
  have ⟨hl1, hl23⟩ := linkResolved_mid_split lkm pre [Asm.andi AbiReg.t0 AbiReg.t0 1#12]
    [Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] post hlink
  have ⟨hl2, hl3⟩ := linkResolved_mid_split lkm (pre ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12])
    [Asm.slli AbiReg.t0 AbiReg.t0 3#6] [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] post hl23
  have htw1 : lkm.totalSize [Asm.andi AbiReg.t0 AbiReg.t0 1#12] = 1 := by simp only [Asm.andi, lkm.totalSize_instr]
  have htw2 : lkm.totalSize [Asm.slli AbiReg.t0 AbiReg.t0 3#6] = 1 := by simp only [Asm.slli, lkm.totalSize_instr]
  let st1 := stepReg st AbiReg.t0 (evalAluImm .andi (st.getReg AbiReg.t0) 1#12)
    (BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)))
  obtain ⟨hrun1, hpc1, ht0_1, hoth1, hmem1, hpres1⟩ :=
    run_aluImm_step env pre _ .andi AbiReg.t0 AbiReg.t0 1#12 nonPreserved_t0 hl1 st hpc
  have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12])) := by
    rw [lkm.totalSize_append, htw1]; exact hpc1
  let st2 := stepReg st1 AbiReg.t0 (evalShiftImm .slli (st1.getReg AbiReg.t0) 3#6)
    (BitVec.ofNat 64 (4 * (lkm.totalSize (pre ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12]) + 1)))
  obtain ⟨hrun2, hpc2, ht0_2, hoth2, hmem2, hpres2⟩ :=
    run_shImm_step env (pre ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12]) _ .slli AbiReg.t0 AbiReg.t0 3#6 nonPreserved_t0 hl2 st1 hpc1'
  have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize ((pre ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12]) ++ [Asm.slli AbiReg.t0 AbiReg.t0 3#6])) := by
    rw [lkm.totalSize_append, htw2]; exact hpc2
  obtain ⟨hrun3, hpc3, ht1_3, hoth3, hmem3, hpres3⟩ :=
    run_alu_step env _ post .add AbiReg.t1 AbiReg.gp AbiReg.t0 nonPreserved_t1 hl3 st2 hpc2'
  refine ⟨_, by rw [show (3 : Nat) = 1 + (1 + 1) by rfl, run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
    by
      have hpcEq : lkm.totalSize ((pre ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12]) ++ [Asm.slli AbiReg.t0 AbiReg.t0 3#6]) + 1 =
          lkm.totalSize pre + 3 := by rw [lkm.totalSize_append, lkm.totalSize_append, htw1, htw2, Nat.add_assoc]
      exact hpc3.trans (congrArg (fun n => BitVec.ofNat 64 (4 * n)) hpcEq),
    ?_,
    fun q hqt0 hqt1 => (hoth3 q hqt1).trans ((hoth2 q hqt0).trans (hoth1 q hqt0)),
    hmem3.trans (hmem2.trans hmem1),
    hpres1.trans (hpres2.trans hpres3)⟩
  have hgp2 : st2.getReg AbiReg.gp = T := (hpres1.trans hpres2).gp.trans hgp
  rw [ht1_3, evalAlu, hgp2, ht0_2, ht0_1, ht0, tier_off_val u]

theorem maxTempsExprs_foldl_ge (xs : List (_root_.L.Expr × Nat)) (init : Nat) :
    init ≤ xs.foldl (fun acc (e, idx) => max acc (idx + max 1 (maxTempsExpr e))) init := by
  induction xs generalizing init with
  | nil => exact Nat.le_refl _
  | cons p ps ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem maxTempsExprs_ge_length (es : List _root_.L.Expr) :
    es.length ≤ maxTempsExprs es := by
  cases es with
  | nil => simp [maxTempsExprs]
  | cons e rest =>
    have hrec : ∀ (l : List (_root_.L.Expr × Nat)) (init : Nat),
        ∀ p ∈ l, p.2 + 1 ≤ l.foldl (fun acc (e, idx) => max acc (idx + max 1 (maxTempsExpr e))) init := by
      intro l
      induction l with
      | nil => intro init p hp; simp at hp
      | cons hd tl ih =>
        intro init p hp
        simp only [List.foldl_cons]
        rcases List.mem_cons.mp hp with rfl | htl
        · exact Nat.le_trans (Nat.le_trans (by omega) (Nat.le_max_right init _))
            (maxTempsExprs_foldl_ge tl _)
        · exact ih _ p htl
    have hzip : ∀ (l : List _root_.L.Expr) (k : Nat), l ≠ [] →
        ∃ x, (x, k + l.length - 1) ∈ l.zipIdx k := by
      intro l
      induction l with
      | nil => intro _ h; exact absurd rfl h
      | cons a tl ih =>
        intro k _
        cases tl with
        | nil => exact ⟨a, by simp [List.zipIdx_cons]⟩
        | cons b tl2 =>
          obtain ⟨x, hx⟩ := ih (k + 1) (by simp)
          refine ⟨x, ?_⟩
          rw [List.zipIdx_cons]
          right
          have heq : k + 1 + (b :: tl2).length - 1 = k + (a :: b :: tl2).length - 1 := by
            simp; omega
          rwa [← heq]
    obtain ⟨x, hx⟩ := hzip (e :: rest) 0 (by simp)
    have hle := hrec ((e :: rest).zipIdx 0) 0 (x, 0 + (e :: rest).length - 1) hx
    change (e :: rest).length ≤ ((e :: rest).zipIdx 0).foldl (fun acc (e, idx) => max acc (idx + max 1 (maxTempsExpr e))) 0
    omega

theorem prog_ret_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (es : List _root_.L.Expr) (hesOk : es.all (exprOkB env.tab nl) = true)
    (hnt : maxTempsExprs es ≤ nt) (retLbl : String) (retTarget : Nat)
    (hretLbl : lookupLabel env.labels retLbl = some retTarget)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ (compileEvalExprsToTemps env.tab nl 0 es ++
      copyTempsToResults env.tab nl 0 es.length ++ [Asm.j retLbl]) ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOk L sp st.mem nl loc) :
    match _root_.L.evalArgs es { mem := lm, loc := loc } with
    | .ok (vs, _) =>
      ∃ k st',
        RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * retTarget) ∧
        PreservedRegs st st' ∧
        ProgMemRel env.tab L st'.mem lm ∧
        ResultsInState env.tab L st' vs ∧
        ProgMemOutside (FnWriteMask L sp nl nt) st.mem st'.mem
    | .error _ =>
      ∃ k st',
        RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' := by
  have hlink' : lkm.linkSpec (pre ++ compileEvalExprsToTemps env.tab nl 0 es ++
      (copyTempsToResults env.tab nl 0 es.length ++ ([Asm.j retLbl] ++ post))) = .ok (env.code, env.labels) := by
    simpa [List.append_assoc] using hlink
  have hpcE := linkResolved_sub_pc64 env pre (compileEvalExprsToTemps env.tab nl 0 es) _ hlink'
  have hsim := progEvalArgs_sim env L lm loc hal hlim htop es pre _ 0 hesOk (by omega) hlink' hpcE st hpc hgp hsp hm hf
  cases hea : _root_.L.evalArgs es { mem := lm, loc := loc } with
  | error err =>
    rw [hea] at hsim; obtain ⟨k, st', hrun, hpc', hpres, _⟩ := hsim; exact ⟨k, st', hrun, hpc', hpres⟩
  | ok res =>
    rcases res with ⟨vs, st1'⟩
    rw [hea] at hsim
    obtain ⟨k1, st1, hrun1, hpc1, hlen, hslots, hpres1, hout1⟩ := hsim
    have hpm1 : ProgMemOutside (FnWriteMask L sp nl nt) st.mem st1.mem :=
      ProgMemOutside.of_memEqOutside (L.fnWriteMask_of_tempSpan hlim htop (Nat.zero_le nt)) hout1
    have hm1 : ProgMemRel env.tab L st1.mem lm :=
      ProgMemRel.of_stack_eqOutside (MemSpan.sub_trans (tempSpan_sub_frame (Nat.zero_le nt)) (L.frame_sub_stackSpan hlim htop)) hout1 hm
    let pre1 := pre ++ compileEvalExprsToTemps env.tab nl 0 es
    have hlink2 : lkm.linkSpec (pre1 ++ copyTempsToResults env.tab nl 0 vs.length ++ ([Asm.j retLbl] ++ post)) =
        .ok (env.code, env.labels) := by
      rw [hlen]; simpa [pre1, List.append_assoc] using hlink'
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by
      simpa [pre1, lkm.totalSize_append] using hpc1
    have hsp1 : st1.getReg AbiReg.sp = sp := hpres1.sp.trans hsp
    have hcnt : 0 + vs.length ≤ nt := by
      rw [hlen, Nat.zero_add]; exact Nat.le_trans (maxTempsExprs_ge_length es) hnt
    obtain ⟨k2, st2, hrun2, hpc2, hpres2, hres2, hout2⟩ :=
      copyTempsToResults_sim env L hal hlim htop vs hcnt pre1 ([Asm.j retLbl] ++ post) hlink2
        st1 hpc1' (hpres1.gp.trans hgp) hsp1 hslots
    let pre2 := pre1 ++ copyTempsToResults env.tab nl 0 vs.length
    have hlink3 : lkm.linkSpec (pre2 ++ [Asm.j retLbl] ++ post) = .ok (env.code, env.labels) := by
      simpa [pre2, List.append_assoc] using hlink2
    have hpc3 := linkResolved_sub_pc64 env pre2 [Asm.j retLbl] post hlink3
    have h64J : 4 * (lkm.totalSize pre2 + lkm.itemSize (.j retLbl)) < 2 ^ 64 := by
      simpa [Asm.j, lkm.totalSize_singleton] using hpc3
    obtain ⟨kJ, st3, hrun3, hpc3', hoth3, hpres3, hmem3⟩ :=
      prog_step_j env pre2 post retLbl retTarget hretLbl hlink3 h64J st2
        (by simpa [pre2, lkm.totalSize_append] using hpc2)
    have hpm2 : ProgMemOutside (FnWriteMask L sp nl nt) st1.mem st2.mem :=
      progMemOutside_of_resGlob L sp nl nt (MemEqOutside.mono (resOnlySpan_sub_resGlob L) hout2)
    have hm2 : ProgMemRel env.tab L st2.mem lm := ProgMemRel.of_resOnly L hout2 hm1
    refine ⟨k1 + k2 + kJ, st3,
      by rw [run_add, run_add, hrun1]; dsimp only; rw [hrun2]; dsimp only; exact hrun3,
      hpc3', (hpres1.trans hpres2).trans hpres3, by rw [hmem3]; exact hm2,
      ⟨fun i hi => (hoth3 (resReg i) (by dsimp [resReg]; split <;> decide)).trans (hres2.1 i hi),
       fun i hlo hhi => by rw [hmem3]; exact hres2.2 i hlo hhi⟩,
      by rw [hmem3]; exact hpm1.trans hpm2⟩

theorem prog_abort_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (e : _root_.L.Expr) (heOk : exprOkB env.tab nl e = true) (hnt : maxTempsExpr e ≤ nt)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ (compileE env.tab nl 0 e ++ [Asm.j abortLabel]) ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOk L sp st.mem nl loc) :
    match _root_.L.evalE e { mem := lm, loc := loc } with
    | .ok (v, _) =>
      ∃ k st',
        RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.abortTarget) ∧
        st'.getReg AbiReg.a0 = v.toBitVec ∧
        PreservedRegs st st'
    | .error _ =>
      ∃ k st',
        RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' := by
  have ⟨hl1, hl2⟩ := linkResolved_mid_split lkm pre _ _ post hlink
  have hpc1 := linkResolved_sub_pc64 env pre _ _ hl1
  have hsim := progEvalExpr_sim env L lm loc hal hlim htop e pre _ 0 heOk (by omega) hl1 hpc1 st hpc hgp hsp hm hf
  cases he : _root_.L.evalE e { mem := lm, loc := loc } with
  | error err =>
    rw [he] at hsim; obtain ⟨k, st', hrun, hpc', hpres, _⟩ := hsim; exact ⟨k, st', hrun, hpc', hpres⟩
  | ok res =>
    rcases res with ⟨v, st1'⟩
    rw [he] at hsim
    obtain ⟨k1, st1, hrun1, hpc1', ha0, hpres1, _⟩ := hsim
    have hpc2 := linkResolved_sub_pc64 env (pre ++ compileE env.tab nl 0 e) [Asm.j abortLabel] post hl2
    have h64J : 4 * (lkm.totalSize (pre ++ compileE env.tab nl 0 e) + lkm.itemSize (.j abortLabel)) < 2 ^ 64 := by
      simpa [Asm.j, lkm.totalSize_singleton] using hpc2
    obtain ⟨k2, st2, hrun2, hpc2', hoth2, hpres2, _⟩ :=
      prog_step_j env (pre ++ compileE env.tab nl 0 e) post abortLabel env.abortTarget env.habortLbl
        hl2 h64J st1 (by simpa [lkm.totalSize_append] using hpc1')
    exact ⟨k1 + k2, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2, hpc2',
      (hoth2 AbiReg.a0 (by decide)).trans ha0, hpres1.trans hpres2⟩


end ProgStmtHelpers

end ConAgua.RISCV.Compiler
