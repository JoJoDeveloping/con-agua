import ConAgua.RISCV.Compiler.ProgSimStmtA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# General Program-Level Forward Simulation (`ConAgua.RISCV.Compiler.ProgSimProof`)

Generalizes `SimProof` to full `ConAgua.RISCV.MiniL` programs compiled via `Compile.compileProg`
/ `Compile.compileProgAsm`:
- Handles both byte arrays (`pos8 < tab.nb`) and tiered word arrays (`tab.nb ≤ pos64 < tab.nb + tab.nw`),
  supporting `182+` `2^35`-byte slots.
- Covers all `_root_.L.Expr`, `_root_.L.Cond`, and `_root_.L.Stmt` constructors (`const`, `var`, `bin`,
  `ld8`, `ld64`, `len8`, `len64`, `cmpw`, `ldc`, `glob`, `ld64t`, `len64t`, `ld8x8`, `ld32t`,
  `ld32h`, `skip`, `set`, `st8`, `st64`, `seq`, `ite`, `while`, `brk`, `ret`, `call`, `abort`,
  `gset`, `st64t`, `copy64`, `copy8w`, `scan8`, `st32t`).
- Proves `compileFns_call_sim` (reusable by `ChipStub`) and headline theorem `compileProg_sim`
  from `ca_enter` to `ECALL`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard Lean axioms only.
-/

namespace ConAgua.RISCV.Compiler

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Linker

/-! ## Section 6b (continued): Batch 2b & Top-Level Axiom Checks -/

section ProgStmtHelpers

/-! ### Batch 2b: Array Stores (`st8`, `st64`, `st64t`, `st32t`), Block Copies (`copy64`, `copy8w`), and `scan8` -/

theorem tempSpan_slot_disjoint {sp : BitVec 64} {nl j k nt : Nat}
    (hjk : j < k) (hk : k ≤ nt) (hvalid : sp.toNat + 8 * (1 + nl + nt) ≤ 2 ^ 64)
    {b : Nat} (hb : b < 8) :
    ¬(tempSpan sp nl k nt).contains (sp + BitVec.ofNat 64 (8 * (1 + (nl + j))) + BitVec.ofNat 64 b) := by
  intro ⟨m, hm, heq⟩
  simp only [tempSpan] at hm heq
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add] at heq
  have hnat := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 8 * (1 + (nl + j)) + b < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show sp.toNat + (8 * (1 + (nl + j)) + b) < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 8 * (1 + nl + k) + m < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show sp.toNat + (8 * (1 + nl + k) + m) < 2 ^ 64 by omega)] at hnat
  omega

theorem progMemRel_of_tempSpan {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    {sp : BitVec 64} {nl tmp nt : Nat}
    (hlim : L.stackLimit.toNat ≤ sp.toNat) (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (htmp : tmp ≤ nt) {m1 m2 : ByteMem} {lm : _root_.L.Mem}
    (hout : MemEqOutside (tempSpan sp nl tmp nt) m1 m2) (hm : ProgMemRel env.tab L m1 lm) :
    ProgMemRel env.tab L m2 lm :=
  ProgMemRel.of_stack_eqOutside
    (MemSpan.sub_trans (tempSpan_sub_frame htmp) (L.frame_sub_stackSpan hlim htop)) hout hm

theorem progFrameOk_of_tempSpan {tab : Tab} (L : ProgLayout tab)
    {sp : BitVec 64} {nl tmp nt : Nat}
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat) (htmp : tmp ≤ nt)
    {m1 m2 : ByteMem} {loc : _root_.L.Locals}
    (hout : MemEqOutside (tempSpan sp nl tmp nt) m1 m2) (hf : ProgFrameOk L sp m1 nl loc) :
    ProgFrameOk L sp m2 nl loc :=
  ProgFrameOk.of_tempSpan (Nat.le_trans htop L.hStackValid) htmp hout hf

theorem progMemOutside_of_tempSpan {tab : Tab} (L : ProgLayout tab)
    {sp : BitVec 64} {nl tmp nt : Nat}
    (hlim : L.stackLimit.toNat ≤ sp.toNat) (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (htmp : tmp ≤ nt) {m1 m2 : ByteMem}
    (hout : MemEqOutside (tempSpan sp nl tmp nt) m1 m2) :
    ProgMemOutside (FnWriteMask L sp nl nt) m1 m2 :=
  ProgMemOutside.of_memEqOutside (L.fnWriteMask_of_tempSpan hlim htop htmp) hout

theorem progFrameOk_of_disj_stack {tab : Tab} (L : ProgLayout tab)
    {sp : BitVec 64} {nl nt : Nat}
    (hlim : L.stackLimit.toNat ≤ sp.toNat) (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (S : MemSpan) (hSvalid : S.valid) (hdisj : S.disjoint L.stackSpan)
    {m1 m2 : ByteMem} {loc : _root_.L.Locals}
    (hout : MemEqOutside S m1 m2) (hf : ProgFrameOk L sp m1 nl loc) :
    ProgFrameOk L sp m2 nl loc := by
  intro x hx
  rw [← hf x hx, slotOff_ofInt]
  apply MemEqOutside.readWord64_eq hout
  intro k hk
  have hs1 : (slotSpan sp (1 + x)).sub L.stackSpan :=
    MemSpan.sub_trans (slotSpan_sub_frame (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hx 1) (Nat.le_add_right _ _)))
      (L.frame_sub_stackSpan hlim htop)
  exact (MemSpan.disjoint_to_memDisjoint hSvalid L.stackSpan_valid hdisj).symm _
    (hs1 _ ⟨k, hk, by simp [slotSpan, slotAddr]⟩)

theorem memEqOutside_store1_arr8 {tab : Tab} (L : ProgLayout tab)
    (a : _root_.L.ArrId) (i : Nat) (hi : i < L.cap8 a) (m : ByteMem) (v : BitVec 8) :
    MemEqOutside (L.arr8Span a) m (storeBytes m (L.base8 a + BitVec.ofNat 64 i) 1 v) := by
  intro addr hnot
  apply storeBytes_apply_ne
  intro j hj heq
  have hj0 : j = 0 := by omega
  subst hj0
  apply hnot
  refine ⟨i, hi, ?_⟩
  simpa [ProgLayout.arr8Span] using heq

theorem progMemOutside_store1_arr8 {tab : Tab} (L : ProgLayout tab)
    {sp : BitVec 64} {nl nt : Nat} (a : _root_.L.ArrId) (ha : tab.bytePosOkB a = true)
    (i : Nat) (hi : i < L.cap8 a) (m : ByteMem) (v : BitVec 8) :
    ProgMemOutside (FnWriteMask L sp nl nt) m (storeBytes m (L.base8 a + BitVec.ofNat 64 i) 1 v) :=
  ProgMemOutside.of_memEqOutside
    (fun _ hc => Or.inr (Or.inr (Or.inl ⟨a, ha, hc⟩)))
    (memEqOutside_store1_arr8 L a i hi m v)

theorem progFrameOk_store1_arr8 {tab : Tab} (L : ProgLayout tab)
    {sp : BitVec 64} {nl nt : Nat}
    (hlim : L.stackLimit.toNat ≤ sp.toNat) (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (a : _root_.L.ArrId) (ha : tab.bytePosOkB a = true) (i : Nat) (hi : i < L.cap8 a)
    (m : ByteMem) (v : BitVec 8) {loc : _root_.L.Locals} (hf : ProgFrameOk L sp m nl loc) :
    ProgFrameOk L sp (storeBytes m (L.base8 a + BitVec.ofNat 64 i) 1 v) nl loc :=
  progFrameOk_of_disj_stack L hlim htop (L.arr8Span a) (L.arr8Span_valid a)
    (L.h8DisjStack a ha) (memEqOutside_store1_arr8 L a i hi m v) hf

theorem memEqOutside_writeWord64_arr64 {tab : Tab} (L : ProgLayout tab)
    (s : _root_.L.TieredArray) (i : Nat) (hi : i < L.cap64 s) (m : ByteMem) (w : BitVec 64) :
    MemEqOutside (L.arr64Span s) m (writeWord64 m (L.base64 s + BitVec.ofNat 64 (8 * i)) w) := by
  apply MemEqOutside.writeWord64
  intro k hk
  refine ⟨8 * i + k, by simp only [ProgLayout.arr64Span]; omega, ?_⟩
  simp only [ProgLayout.arr64Span, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem progMemOutside_write64_arr64 {tab : Tab} (L : ProgLayout tab)
    {sp : BitVec 64} {nl nt : Nat} (s : _root_.L.TieredArray) (hs : tab.wordPosOkB s = true)
    (i : Nat) (hi : i < L.cap64 s) (m : ByteMem) (w : BitVec 64) :
    ProgMemOutside (FnWriteMask L sp nl nt) m (writeWord64 m (L.base64 s + BitVec.ofNat 64 (8 * i)) w) :=
  ProgMemOutside.of_memEqOutside
    (fun _ hc => Or.inr (Or.inr (Or.inr ⟨s, hs, hc⟩)))
    (memEqOutside_writeWord64_arr64 L s i hi m w)

theorem progFrameOk_write64_arr64 {tab : Tab} (L : ProgLayout tab)
    {sp : BitVec 64} {nl nt : Nat}
    (hlim : L.stackLimit.toNat ≤ sp.toNat) (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (s : _root_.L.TieredArray) (hs : tab.wordPosOkB s = true) (i : Nat) (hi : i < L.cap64 s)
    (m : ByteMem) (w : BitVec 64) {loc : _root_.L.Locals} (hf : ProgFrameOk L sp m nl loc) :
    ProgFrameOk L sp (writeWord64 m (L.base64 s + BitVec.ofNat 64 (8 * i)) w) nl loc :=
  progFrameOk_of_disj_stack L hlim htop (L.arr64Span s) (L.arr64Span_valid s)
    (L.h64DisjStack s hs) (memEqOutside_writeWord64_arr64 L s i hi m w) hf

theorem memEqOutside_store4_arr32 {tab : Tab} (L : ProgLayout tab)
    (s : _root_.L.TieredArray) (i : Nat) (hi : i / 2 < L.cap64 s) (m : ByteMem) (v : BitVec 32) :
    MemEqOutside (L.arr64Span s) m (storeBytes m (L.base64 s + BitVec.ofNat 64 (4 * i)) 4 v) := by
  intro addr hnot
  apply storeBytes_apply_ne
  intro j hj heq
  apply hnot
  refine ⟨4 * i + j, by simp only [ProgLayout.arr64Span]; omega, ?_⟩
  rw [heq, BitVec.add_assoc, ← BitVec.ofNat_add]
  rfl

theorem progMemOutside_store4_arr32 {tab : Tab} (L : ProgLayout tab)
    {sp : BitVec 64} {nl nt : Nat} (s : _root_.L.TieredArray) (hs : tab.wordPosOkB s = true)
    (i : Nat) (hi : i / 2 < L.cap64 s) (m : ByteMem) (v : BitVec 32) :
    ProgMemOutside (FnWriteMask L sp nl nt) m (storeBytes m (L.base64 s + BitVec.ofNat 64 (4 * i)) 4 v) :=
  ProgMemOutside.of_memEqOutside
    (fun _ hc => Or.inr (Or.inr (Or.inr ⟨s, hs, hc⟩)))
    (memEqOutside_store4_arr32 L s i hi m v)

theorem progFrameOk_store4_arr32 {tab : Tab} (L : ProgLayout tab)
    {sp : BitVec 64} {nl nt : Nat}
    (hlim : L.stackLimit.toNat ≤ sp.toNat) (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (s : _root_.L.TieredArray) (hs : tab.wordPosOkB s = true) (i : Nat) (hi : i / 2 < L.cap64 s)
    (m : ByteMem) (v : BitVec 32) {loc : _root_.L.Locals} (hf : ProgFrameOk L sp m nl loc) :
    ProgFrameOk L sp (storeBytes m (L.base64 s + BitVec.ofNat 64 (4 * i)) 4 v) nl loc :=
  progFrameOk_of_disj_stack L hlim htop (L.arr64Span s) (L.arr64Span_valid s)
    (L.h64DisjStack s hs) (memEqOutside_store4_arr32 L s i hi m v) hf

theorem shl3_ofNat_eq (v : _root_.L.Word) (hv : 8 * v.toNat < 2 ^ 64) :
    evalShiftImm .slli v.toBitVec 3#6 = BitVec.ofNat 64 (8 * v.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [evalShiftImm, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
    Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show 3 < 64 by decide)]
  rw [Nat.mul_comm, Nat.mod_eq_of_lt hv]

theorem shl2_ofNat_eq (v : _root_.L.Word) (hv : 4 * v.toNat < 2 ^ 64) :
    evalShiftImm .slli v.toBitVec 2#6 = BitVec.ofNat 64 (4 * v.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [evalShiftImm, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
    Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show 2 < 64 by decide)]
  rw [Nat.mul_comm, Nat.mod_eq_of_lt hv]

theorem srli1_eq_div2 (v : _root_.L.Word) :
    evalShiftImm .srli v.toBitVec 1#6 = BitVec.ofNat 64 (v / 2).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [evalShiftImm, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
    Nat.shiftRight_eq_div_pow, UInt64.toNat_div]
  rw [Nat.mod_eq_of_lt (show 1 < 64 by decide)]
  simp only [Nat.pow_one, UInt64.toNat_ofNat, Nat.mod_eq_of_lt (show 2 < 2 ^ 64 by decide)]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) v.toBitVec.isLt)).symm

theorem evalBranch_bgeu_nat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    evalBranch .bgeu (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (b ≤ a) := by
  dsimp only [evalBranch]
  by_cases hlt : a < b
  · have h : (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = true := by
      rw [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
      exact hlt
    rw [h, Bool.not_true]
    exact (decide_eq_false_iff_not.mpr (by omega)).symm
  · have h : (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = false := by
      rw [Bool.eq_false_iff, Ne, BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
      exact hlt
    rw [h, Bool.not_false]
    exact (decide_eq_true_iff.mpr (by omega)).symm

theorem evalBranch_bltu_nat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    evalBranch .bltu (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  dsimp only [evalBranch]
  by_cases hlt : a < b
  · have h : (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = true := by
      rw [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
      exact hlt
    rw [h]
    exact (decide_eq_true_iff.mpr hlt).symm
  · have h : (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = false := by
      rw [Bool.eq_false_iff, Ne, BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
      exact hlt
    rw [h]
    exact (decide_eq_false_iff_not.mpr hlt).symm

theorem run_trans {rom : RV64.Rom} {k1 k2 : Nat} {s0 s1 s2 : State}
    (h1 : RV64.run rom k1 s0 = .cont s1) (h2 : RV64.run rom k2 s1 = .cont s2) :
    RV64.run rom (k1 + k2) s0 = .cont s2 := by
  rw [run_add, h1]; exact h2

theorem preservedRegs_of_regs {s1 s2 : State} (h : s2.regs = s1.regs) : PreservedRegs s1 s2 :=
  ⟨by simp [State.getReg, h], by simp [State.getReg, h], by simp [State.getReg, h],
   by simp [State.getReg, h]⟩

theorem prog_compileStorePair_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (i e : _root_.L.Expr) (hiOk : exprOkB env.tab nl i = true) (heOk : exprOkB env.tab nl e = true)
    (hnt : max (maxTempsExpr i) (1 + maxTempsExpr e) ≤ nt)
    (pre post : List AsmItem) (st : State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOk L sp st.mem nl loc)
    (hlink : lkm.linkSpec (pre ++ compileStorePair env.tab nl i e ++ post) = .ok (env.code, env.labels)) :
    match _root_.L.evalE i { mem := lm, loc := loc }, _root_.L.evalE e { mem := lm, loc := loc } with
    | .ok (vi, _), .ok (ve, _) =>
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileStorePair env.tab nl i e))) ∧
        r'.getReg AbiReg.t0 = vi.toBitVec ∧
        r'.getReg AbiReg.a0 = ve.toBitVec ∧
        PreservedRegs st r' ∧
        ProgMemRel env.tab L r'.mem lm ∧
        ProgFrameOk L sp r'.mem nl loc ∧
        ProgMemOutside (FnWriteMask L sp nl nt) st.mem r'.mem
    | _, _ =>
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st r' := by
  have h64 := linkResolved_sub_pc64 env pre (compileStorePair env.tab nl i e) post hlink
  cases hsi : emitSimpleExpr env.tab AbiReg.t0 AbiReg.t1 i with
  | some ci =>
    have hdef : compileStorePair env.tab nl i e = compileE env.tab nl 0 e ++ ci := by
      simp only [compileStorePair, hsi]
    rw [hdef] at hlink h64 ⊢
    have htw : lkm.totalSize (compileE env.tab nl 0 e ++ ci) =
        lkm.totalSize (compileE env.tab nl 0 e) + lkm.totalSize ci := lkm.totalSize_append _ _
    have hle : lkm.linkSpec (pre ++ compileE env.tab nl 0 e ++ (ci ++ post)) = .ok (env.code, env.labels) := by
      simpa only [List.append_assoc] using hlink
    have re := progEvalExpr_sim env L lm loc hal hlim htop e pre (ci ++ post) 0 heOk (by omega)
      hle (by rw [htw] at h64; omega) st hpc hgp hsp hm hf
    rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨ve, hve⟩ | hve
    · simp only [hve] at re
      obtain ⟨ke, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := re
      have hm1 := progMemRel_of_tempSpan env L hlim htop (Nat.zero_le nt) heq1 hm
      have hf1 := progFrameOk_of_tempSpan L htop (Nat.zero_le nt) heq1 hf
      have hpm1 := progMemOutside_of_tempSpan L hlim htop (Nat.zero_le nt) heq1
      have htw1 : lkm.totalSize (pre ++ compileE env.tab nl 0 e) =
          lkm.totalSize pre + lkm.totalSize (compileE env.tab nl 0 e) := lkm.totalSize_append _ _
      obtain ⟨vi, ki, st2, hvi, hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
        prog_emitSimpleExpr_sim env L lm loc hal (pre ++ compileE env.tab nl 0 e) post
          AbiReg.t0 AbiReg.t1 (by decide) (by decide) (by decide) (by decide) (by decide)
          i ci hsi hiOk (by simpa only [List.append_assoc] using hlink)
          (by rw [htw1]; rw [htw] at h64; omega) st1 (by rw [htw1]; exact hpc1)
          (hpres1.gp.trans hgp) (hpres1.sp.trans hsp) hm1 hf1
      simp only [hvi, hve]
      have hpres2 : PreservedRegs st1 st2 :=
        ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
         hoth2 _ (by decide) (by decide),
         hoth2 _ (by decide) (by decide)⟩
      exact ⟨ke + ki, st2, by rw [run_add, hrun1]; exact hrun2,
        by rw [hpc2, htw1, htw, Nat.add_assoc], ht0_2,
        (hoth2 _ (by decide) (by decide)).trans ha0_1,
        hpres1.trans hpres2, by rw [hmem2]; exact hm1, by rw [hmem2]; exact hf1,
        by rw [hmem2]; exact hpm1⟩
    · simp only [hve] at re
      have hPureI : ∃ vi, _root_.L.evalE i ⟨lm, loc⟩ = .ok (vi, ⟨lm, loc⟩) := by
        cases i <;> simp [emitSimpleExpr] at hsi <;> exact ⟨_, rfl⟩
      obtain ⟨vi, hvi⟩ := hPureI
      simp only [hvi, hve]
      obtain ⟨ke, r', hrun, hpc', hpres, _⟩ := re; exact ⟨ke, r', hrun, hpc', hpres⟩
  | none =>
    cases hse : emitSimpleExpr env.tab AbiReg.a0 AbiReg.t1 e with
    | some ce =>
      have hdef : compileStorePair env.tab nl i e =
          compileE env.tab nl 0 i ++ [Asm.mv AbiReg.t0 AbiReg.a0] ++ ce := by
        simp only [compileStorePair, hsi, hse, List.append_assoc]
      rw [hdef] at hlink h64 ⊢
      have htw_mv : lkm.totalSize [Asm.mv AbiReg.t0 AbiReg.a0] = 1 := by
        simp only [Asm.mv, lkm.totalSize_instr]
      have htw : lkm.totalSize (compileE env.tab nl 0 i ++ [Asm.mv AbiReg.t0 AbiReg.a0] ++ ce) =
          lkm.totalSize (compileE env.tab nl 0 i) + 1 + lkm.totalSize ce := by
        rw [lkm.totalSize_append, lkm.totalSize_append, htw_mv]
      have hli : lkm.linkSpec (pre ++ compileE env.tab nl 0 i ++ ([Asm.mv AbiReg.t0 AbiReg.a0] ++ ce ++ post)) =
          .ok (env.code, env.labels) := by simpa only [List.append_assoc] using hlink
      have ri := progEvalExpr_sim env L lm loc hal hlim htop i pre ([Asm.mv AbiReg.t0 AbiReg.a0] ++ ce ++ post)
        0 hiOk (by omega) hli (by rw [htw] at h64; omega) st hpc hgp hsp hm hf
      rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
      · simp only [hvi] at ri
        obtain ⟨ki, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ri
        have hm1 := progMemRel_of_tempSpan env L hlim htop (Nat.zero_le nt) heq1 hm
        have hf1 := progFrameOk_of_tempSpan L htop (Nat.zero_le nt) heq1 hf
        have hpm1 := progMemOutside_of_tempSpan L hlim htop (Nat.zero_le nt) heq1
        have htw1 : lkm.totalSize (pre ++ compileE env.tab nl 0 i) =
            lkm.totalSize pre + lkm.totalSize (compileE env.tab nl 0 i) := lkm.totalSize_append _ _
        have hsMv := step_item_instr_lm lkm env.hrom (pre ++ compileE env.tab nl 0 i) (ce ++ post)
          (.aluImm .addi AbiReg.t0 AbiReg.a0 0#12)
          (by simpa only [Asm.mv, Asm.addi, Asm.raw, List.append_assoc] using hlink)
          (by rw [htw1]; rw [htw] at h64; omega) st1 (by rw [htw1]; exact hpc1)
        let st2 := stepReg st1 AbiReg.t0 (st1.getReg AbiReg.a0 + sextImm12 0#12) (st1.pc + 4#64)
        have hpres2 : PreservedRegs st1 st2 :=
          ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
           getReg_stepReg_ne _ _ _ (by decide) _ _,
           getReg_stepReg_ne _ _ _ (by decide) _ _⟩
        have htw2 : lkm.totalSize (pre ++ compileE env.tab nl 0 i ++ [Asm.mv AbiReg.t0 AbiReg.a0]) =
            lkm.totalSize pre + lkm.totalSize (compileE env.tab nl 0 i) + 1 := by
          rw [lkm.totalSize_append, htw1, htw_mv]
        have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ compileE env.tab nl 0 i)) := by rw [htw1]; exact hpc1
        have hpc2 : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ compileE env.tab nl 0 i ++ [Asm.mv AbiReg.t0 AbiReg.a0])) := by
          change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1', htw1, htw2]
        have ht0_2 : st2.getReg AbiReg.t0 = vi.toBitVec := by
          change (stepReg st1 AbiReg.t0 _ _).getReg AbiReg.t0 = _
          rw [getReg_stepReg_eq _ _ (by decide), show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero, ha0_1]
        obtain ⟨ve, ke, st3, hve, hrun3, hpc3, ha0_3, hoth3, hmem3⟩ :=
          prog_emitSimpleExpr_sim env L lm loc hal (pre ++ compileE env.tab nl 0 i ++ [Asm.mv AbiReg.t0 AbiReg.a0])
            post AbiReg.a0 AbiReg.t1 (by decide) (by decide) (by decide) (by decide) (by decide)
            e ce hse heOk (by simpa only [List.append_assoc] using hlink)
            (by rw [htw2]; rw [htw] at h64; omega) st2 hpc2
            (hpres2.gp.trans (hpres1.gp.trans hgp)) (hpres2.sp.trans (hpres1.sp.trans hsp)) hm1 hf1
        simp only [hvi, hve]
        have hpres3 : PreservedRegs st2 st3 :=
          ⟨hoth3 _ (by decide) (by decide), hoth3 _ (by decide) (by decide),
           hoth3 _ (by decide) (by decide),
           hoth3 _ (by decide) (by decide)⟩
        exact ⟨ki + (1 + ke), st3,
          by rw [run_add, hrun1]; dsimp only; rw [run_add, run_one_cont _ _ st2 (by rw [hsMv]; rfl)]; dsimp only; exact hrun3,
          by rw [hpc3, htw2, htw]; congr 2; omega,
          (hoth3 _ (by decide) (by decide)).trans ht0_2, ha0_3,
          (hpres1.trans hpres2).trans hpres3,
          by rw [hmem3]; exact hm1, by rw [hmem3]; exact hf1, by rw [hmem3]; exact hpm1⟩
      · simp only [hvi] at ri ⊢
        obtain ⟨ki, r', hrun, hpc', hpres, _⟩ := ri; exact ⟨ki, r', hrun, hpc', hpres⟩
    | none =>
      have hdef : compileStorePair env.tab nl i e =
          compileE env.tab nl 0 i ++
          storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 0)) ++
          compileE env.tab nl 1 e ++
          loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nl + 0)) := by
        simp only [compileStorePair, hsi, hse, Nat.add_zero, List.append_assoc]
      rw [hdef] at hlink h64 ⊢
      have rpair := prog_two_exprs_pair_sim env L lm loc hal hlim htop pre post 0 i e (by omega)
        (fun p q t s ht hl h6 hpc' hgp' hsp' hm' hf' =>
          progEvalExpr_sim env L lm loc hal hlim htop i p q t hiOk ht hl h6 s hpc' hgp' hsp' hm' hf')
        (fun p q t s ht hl h6 hpc' hgp' hsp' hm' hf' =>
          progEvalExpr_sim env L lm loc hal hlim htop e p q t heOk ht hl h6 s hpc' hgp' hsp' hm' hf')
        (by omega) (by omega) hlink h64 st hpc hgp hsp hm hf
      rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
      · rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨ve, hve⟩ | hve
        · simp only [hvi, hve] at rpair ⊢
          obtain ⟨k, r', hrun, hpc', ht0, ha0, hpres, heq⟩ := rpair
          exact ⟨k, r', hrun, hpc', ht0, ha0, hpres,
            progMemRel_of_tempSpan env L hlim htop (Nat.zero_le nt) heq hm,
            progFrameOk_of_tempSpan L htop (Nat.zero_le nt) heq hf,
            progMemOutside_of_tempSpan L hlim htop (Nat.zero_le nt) heq⟩
        · simp only [hvi, hve] at rpair ⊢
          obtain ⟨k, r', hrun, hpc', hpres, _⟩ := rpair; exact ⟨k, r', hrun, hpc', hpres⟩
      · simp only [hvi] at rpair ⊢
        obtain ⟨k, r', hrun, hpc', hpres, _⟩ := rpair; exact ⟨k, r', hrun, hpc', hpres⟩

theorem prog_compileTierStoreTriple_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (t i e : _root_.L.Expr)
    (htOk : exprOkB env.tab nl t = true) (hiOk : exprOkB env.tab nl i = true)
    (heOk : exprOkB env.tab nl e = true)
    (hnt : max (maxTempsExpr t) (max (1 + maxTempsExpr i) (2 + maxTempsExpr e)) ≤ nt)
    (pre post : List AsmItem) (st : State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOk L sp st.mem nl loc)
    (hlink : lkm.linkSpec (pre ++ compileTierStoreTriple env.tab nl t i e ++ post) = .ok (env.code, env.labels)) :
    match _root_.L.evalE t { mem := lm, loc := loc },
          _root_.L.evalE i { mem := lm, loc := loc },
          _root_.L.evalE e { mem := lm, loc := loc } with
    | .ok (u, _), .ok (vi, _), .ok (ve, _) =>
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileTierStoreTriple env.tab nl t i e))) ∧
        r'.getReg AbiReg.t0 = u.toBitVec ∧
        r'.getReg AbiReg.t3 = vi.toBitVec ∧
        r'.getReg AbiReg.a0 = ve.toBitVec ∧
        PreservedRegs st r' ∧
        ProgMemRel env.tab L r'.mem lm ∧
        ProgFrameOk L sp r'.mem nl loc ∧
        ProgMemOutside (FnWriteMask L sp nl nt) st.mem r'.mem
    | _, _, _ =>
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st r' := by
  have h64 := linkResolved_sub_pc64 env pre (compileTierStoreTriple env.tab nl t i e) post hlink
  cases hst : emitSimpleExpr env.tab AbiReg.t0 AbiReg.t1 t with
  | some ct =>
    have hPureT : ∃ u, _root_.L.evalE t ⟨lm, loc⟩ = .ok (u, ⟨lm, loc⟩) := by
      cases t <;> simp [emitSimpleExpr] at hst <;> exact ⟨_, rfl⟩
    cases hsi : emitSimpleExpr env.tab AbiReg.t3 AbiReg.t4 i with
    | some ci =>
      have hPureI : ∃ vi, _root_.L.evalE i ⟨lm, loc⟩ = .ok (vi, ⟨lm, loc⟩) := by
        cases i <;> simp [emitSimpleExpr] at hsi <;> exact ⟨_, rfl⟩
      have hdef : compileTierStoreTriple env.tab nl t i e = compileE env.tab nl 0 e ++ ct ++ ci := by
        simp only [compileTierStoreTriple, hst, hsi, List.append_assoc]
      rw [hdef] at hlink h64 ⊢
      have htw : lkm.totalSize (compileE env.tab nl 0 e ++ ct ++ ci) =
          lkm.totalSize (compileE env.tab nl 0 e) + lkm.totalSize ct + lkm.totalSize ci := by
        simp only [lkm.totalSize_append]
      have re := progEvalExpr_sim env L lm loc hal hlim htop e pre (ct ++ ci ++ post) 0 heOk (by omega)
        (by simpa only [List.append_assoc] using hlink) (by rw [htw] at h64; omega) st hpc hgp hsp hm hf
      rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨ve, hve⟩ | hve
      · simp only [hve] at re
        obtain ⟨ke, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := re
        have hm1 := progMemRel_of_tempSpan env L hlim htop (Nat.zero_le nt) heq1 hm
        have hf1 := progFrameOk_of_tempSpan L htop (Nat.zero_le nt) heq1 hf
        have hpm1 := progMemOutside_of_tempSpan L hlim htop (Nat.zero_le nt) heq1
        have htw1 : lkm.totalSize (pre ++ compileE env.tab nl 0 e) =
            lkm.totalSize pre + lkm.totalSize (compileE env.tab nl 0 e) := lkm.totalSize_append _ _
        obtain ⟨u, kt, st2, hu, hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
          prog_emitSimpleExpr_sim env L lm loc hal (pre ++ compileE env.tab nl 0 e) (ci ++ post)
            AbiReg.t0 AbiReg.t1 (by decide) (by decide) (by decide) (by decide) (by decide)
            t ct hst htOk (by simpa only [List.append_assoc] using hlink)
            (by rw [htw1]; rw [htw] at h64; omega) st1 (by rw [htw1]; exact hpc1)
            (hpres1.gp.trans hgp) (hpres1.sp.trans hsp) hm1 hf1
        have hpres2 : PreservedRegs st1 st2 :=
          ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
           hoth2 _ (by decide) (by decide),
           hoth2 _ (by decide) (by decide)⟩
        have htw2 : lkm.totalSize (pre ++ compileE env.tab nl 0 e ++ ct) =
            lkm.totalSize pre + lkm.totalSize (compileE env.tab nl 0 e) + lkm.totalSize ct := by
          rw [lkm.totalSize_append, htw1]
        obtain ⟨vi, ki, st3, hvi, hrun3, hpc3, ht3_3, hoth3, hmem3⟩ :=
          prog_emitSimpleExpr_sim env L lm loc hal (pre ++ compileE env.tab nl 0 e ++ ct) post
            AbiReg.t3 AbiReg.t4 (by decide) (by decide) (by decide) (by decide) (by decide)
            i ci hsi hiOk (by simpa only [List.append_assoc] using hlink)
            (by rw [htw2]; rw [htw] at h64; omega) st2 (by rw [htw2, ← htw1]; exact hpc2)
            (hpres2.gp.trans (hpres1.gp.trans hgp)) (hpres2.sp.trans (hpres1.sp.trans hsp))
            (by rw [hmem2]; exact hm1) (by rw [hmem2]; exact hf1)
        have hpres3 : PreservedRegs st2 st3 :=
          ⟨hoth3 _ (by decide) (by decide), hoth3 _ (by decide) (by decide),
           hoth3 _ (by decide) (by decide),
           hoth3 _ (by decide) (by decide)⟩
        simp only [hu, hvi, hve]
        exact ⟨ke + (kt + ki), st3,
          by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
          by rw [hpc3, htw2, htw]; congr 2; omega,
          (hoth3 _ (by decide) (by decide)).trans ht0_2,
          ht3_3,
          (hoth3 _ (by decide) (by decide)).trans ((hoth2 _ (by decide) (by decide)).trans ha0_1),
          (hpres1.trans hpres2).trans hpres3,
          by rw [hmem3, hmem2]; exact hm1, by rw [hmem3, hmem2]; exact hf1,
          by rw [hmem3, hmem2]; exact hpm1⟩
      · obtain ⟨u, hu⟩ := hPureT; obtain ⟨vi, hvi⟩ := hPureI
        simp only [hve] at re; simp only [hu, hvi, hve]
        obtain ⟨ke, r', hrun, hpc', hpres, _⟩ := re; exact ⟨ke, r', hrun, hpc', hpres⟩
    | none =>
      cases hse : emitSimpleExpr env.tab AbiReg.a0 AbiReg.t4 e with
      | some ce =>
        have hdef : compileTierStoreTriple env.tab nl t i e =
            compileE env.tab nl 0 i ++ [Asm.mv AbiReg.t3 AbiReg.a0] ++ ct ++ ce := by
          simp only [compileTierStoreTriple, hst, hsi, hse, List.append_assoc]
        rw [hdef] at hlink h64 ⊢
        have htw_mv : lkm.totalSize [Asm.mv AbiReg.t3 AbiReg.a0] = 1 := by
          simp only [Asm.mv, lkm.totalSize_instr]
        have htw : lkm.totalSize (compileE env.tab nl 0 i ++ [Asm.mv AbiReg.t3 AbiReg.a0] ++ ct ++ ce) =
            lkm.totalSize (compileE env.tab nl 0 i) + 1 + lkm.totalSize ct + lkm.totalSize ce := by
          simp only [lkm.totalSize_append, htw_mv]
        have ri := progEvalExpr_sim env L lm loc hal hlim htop i pre
          ([Asm.mv AbiReg.t3 AbiReg.a0] ++ ct ++ ce ++ post) 0 hiOk (by omega)
          (by simpa only [List.append_assoc] using hlink) (by rw [htw] at h64; omega) st hpc hgp hsp hm hf
        rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
        · simp only [hvi] at ri
          obtain ⟨ki, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ri
          have hm1 := progMemRel_of_tempSpan env L hlim htop (Nat.zero_le nt) heq1 hm
          have hf1 := progFrameOk_of_tempSpan L htop (Nat.zero_le nt) heq1 hf
          have hpm1 := progMemOutside_of_tempSpan L hlim htop (Nat.zero_le nt) heq1
          have htw1 : lkm.totalSize (pre ++ compileE env.tab nl 0 i) =
              lkm.totalSize pre + lkm.totalSize (compileE env.tab nl 0 i) := lkm.totalSize_append _ _
          have hsMv := step_item_instr_lm lkm env.hrom (pre ++ compileE env.tab nl 0 i) (ct ++ ce ++ post)
            (.aluImm .addi AbiReg.t3 AbiReg.a0 0#12)
            (by simpa only [Asm.mv, Asm.addi, Asm.raw, List.append_assoc] using hlink)
            (by rw [htw1]; rw [htw] at h64; omega) st1 (by rw [htw1]; exact hpc1)
          let st2 := stepReg st1 AbiReg.t3 (st1.getReg AbiReg.a0 + sextImm12 0#12) (st1.pc + 4#64)
          have hpres2 : PreservedRegs st1 st2 :=
            ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
             getReg_stepReg_ne _ _ _ (by decide) _ _,
             getReg_stepReg_ne _ _ _ (by decide) _ _⟩
          have htw2 : lkm.totalSize (pre ++ compileE env.tab nl 0 i ++ [Asm.mv AbiReg.t3 AbiReg.a0]) =
              lkm.totalSize pre + lkm.totalSize (compileE env.tab nl 0 i) + 1 := by
            rw [lkm.totalSize_append, htw1, htw_mv]
          have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ compileE env.tab nl 0 i)) := by rw [htw1]; exact hpc1
          have hpc2 : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ compileE env.tab nl 0 i ++ [Asm.mv AbiReg.t3 AbiReg.a0])) := by
            change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1', htw1, htw2]
          have ht3_2 : st2.getReg AbiReg.t3 = vi.toBitVec := by
            change (stepReg st1 AbiReg.t3 _ _).getReg AbiReg.t3 = _
            rw [getReg_stepReg_eq _ _ (by decide), show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero, ha0_1]
          obtain ⟨u, kt, st3, hu, hrun3, hpc3, ht0_3, hoth3, hmem3⟩ :=
            prog_emitSimpleExpr_sim env L lm loc hal (pre ++ compileE env.tab nl 0 i ++ [Asm.mv AbiReg.t3 AbiReg.a0])
              (ce ++ post) AbiReg.t0 AbiReg.t1 (by decide) (by decide) (by decide) (by decide) (by decide)
              t ct hst htOk (by simpa only [List.append_assoc] using hlink)
              (by rw [htw2]; rw [htw] at h64; omega) st2 hpc2
              (hpres2.gp.trans (hpres1.gp.trans hgp)) (hpres2.sp.trans (hpres1.sp.trans hsp)) hm1 hf1
          have hpres3 : PreservedRegs st2 st3 :=
            ⟨hoth3 _ (by decide) (by decide), hoth3 _ (by decide) (by decide),
             hoth3 _ (by decide) (by decide),
             hoth3 _ (by decide) (by decide)⟩
          have htw3 : lkm.totalSize (pre ++ compileE env.tab nl 0 i ++ [Asm.mv AbiReg.t3 AbiReg.a0] ++ ct) =
              lkm.totalSize pre + lkm.totalSize (compileE env.tab nl 0 i) + 1 + lkm.totalSize ct := by
            rw [lkm.totalSize_append, htw2]
          obtain ⟨ve, ke, st4, hve, hrun4, hpc4, ha0_4, hoth4, hmem4⟩ :=
            prog_emitSimpleExpr_sim env L lm loc hal (pre ++ compileE env.tab nl 0 i ++ [Asm.mv AbiReg.t3 AbiReg.a0] ++ ct)
              post AbiReg.a0 AbiReg.t4 (by decide) (by decide) (by decide) (by decide) (by decide)
              e ce hse heOk (by simpa only [List.append_assoc] using hlink)
              (by rw [htw3]; rw [htw] at h64; omega) st3 (by rw [htw3, ← htw2]; exact hpc3)
              (hpres3.gp.trans (hpres2.gp.trans (hpres1.gp.trans hgp)))
              (hpres3.sp.trans (hpres2.sp.trans (hpres1.sp.trans hsp)))
              (by rw [hmem3]; exact hm1) (by rw [hmem3]; exact hf1)
          have hpres4 : PreservedRegs st3 st4 :=
            ⟨hoth4 _ (by decide) (by decide), hoth4 _ (by decide) (by decide),
             hoth4 _ (by decide) (by decide),
             hoth4 _ (by decide) (by decide)⟩
          simp only [hu, hvi, hve]
          exact ⟨ki + (1 + (kt + ke)), st4,
            by rw [run_add, hrun1]; dsimp only; rw [run_add, run_one_cont _ _ st2 (by rw [hsMv]; rfl)]; dsimp only
               rw [run_add, hrun3]; dsimp only; exact hrun4,
            by rw [hpc4, htw3, htw]; congr 2; omega,
            (hoth4 _ (by decide) (by decide)).trans ht0_3,
            (hoth4 _ (by decide) (by decide)).trans ((hoth3 _ (by decide) (by decide)).trans ht3_2),
            ha0_4,
            (hpres1.trans hpres2).trans (hpres3.trans hpres4),
            by rw [hmem4, hmem3]; exact hm1, by rw [hmem4, hmem3]; exact hf1,
            by rw [hmem4, hmem3]; exact hpm1⟩
        · obtain ⟨u, hu⟩ := hPureT
          simp only [hvi] at ri; simp only [hu, hvi]
          obtain ⟨ki, r', hrun, hpc', hpres, _⟩ := ri; exact ⟨ki, r', hrun, hpc', hpres⟩
      | none =>
        let c0 := compileE env.tab nl 0 i ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 0))
        let c1 := compileE env.tab nl 1 e
        let cl := loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t1 (slotOff nl)
        have hdef : compileTierStoreTriple env.tab nl t i e = c0 ++ c1 ++ cl ++ ct := by
          simp only [compileTierStoreTriple, hst, hsi, hse, c0, c1, cl, Nat.add_zero, List.append_assoc]
        rw [hdef] at hlink h64 ⊢
        have hlink0 : lkm.linkSpec (pre ++ c0 ++ (c1 ++ cl ++ ct ++ post)) = .ok (env.code, env.labels) := by
          simpa only [List.append_assoc] using hlink
        have hsim0 := prog_evalToTemp_sim env L lm loc hal hlim htop i hiOk (by omega) pre _ hlink0 st hpc hgp hsp hm hf
        rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
        · rw [hvi] at hsim0
          obtain ⟨k0, st1, hrun0, hpc0, hslot0, hpres0, hout0⟩ := hsim0
          have hm1 := progMemRel_of_tempSpan env L hlim htop (Nat.zero_le nt) hout0 hm
          have hf1 := progFrameOk_of_tempSpan L htop (Nat.zero_le nt) hout0 hf
          have hpm0 := progMemOutside_of_tempSpan L hlim htop (Nat.zero_le nt) hout0
          let pre1 := pre ++ c0
          have htwC0 : lkm.totalSize c0 =
              lkm.totalSize (compileE env.tab nl 0 i) + lkm.totalSize (storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 0))) :=
            lkm.totalSize_append _ _
          have htw1 : lkm.totalSize pre1 = lkm.totalSize pre + lkm.totalSize c0 := lkm.totalSize_append _ _
          have hlink1 : lkm.linkSpec (pre1 ++ c1 ++ (cl ++ ct ++ post)) = .ok (env.code, env.labels) := by
            simpa only [pre1, List.append_assoc] using hlink0
          have hsim1 := progEvalExpr_sim env L lm loc hal hlim htop e pre1 _ 1 heOk (by omega) hlink1
            (linkResolved_sub_pc64 env pre1 c1 _ hlink1) st1 (by rw [hpc0, htw1, htwC0])
            (hpres0.gp.trans hgp) (hpres0.sp.trans hsp) hm1 hf1
          rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨ve, hve⟩ | hve
          · rw [hve] at hsim1
            obtain ⟨k1, st2, hrun1, hpc2, ha0_2, hpres1, hout1⟩ := hsim1
            have hm2 := progMemRel_of_tempSpan env L hlim htop (by omega : 1 ≤ nt) hout1 hm1
            have hf2 := progFrameOk_of_tempSpan L htop (by omega : 1 ≤ nt) hout1 hf1
            have hpm1 := progMemOutside_of_tempSpan L hlim htop (by omega : 1 ≤ nt) hout1
            have hslot0_2 : readWord64 st2.mem (sp + BitVec.ofInt 64 (slotOff nl)) = vi.toBitVec := by
              rw [← show nl + 0 = nl from Nat.add_zero nl, ← hslot0]
              apply MemEqOutside.readWord64_eq hout1
              intro k hk; rw [slotOff_ofInt]
              exact tempSpan_slot_disjoint (by omega) (by omega) (Nat.le_trans htop L.hStackValid) hk
            let pre2 := pre1 ++ c1
            have htw2 : lkm.totalSize pre2 = lkm.totalSize pre1 + lkm.totalSize c1 := lkm.totalSize_append _ _
            have hlink2 : lkm.linkSpec (pre2 ++ cl ++ (ct ++ post)) = .ok (env.code, env.labels) := by
              simpa only [pre2, List.append_assoc] using hlink1
            have halL : isAligned (st2.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff nl)) 8 = true := by
              rw [hpres1.sp.trans (hpres0.sp.trans hsp)]; exact isAligned8_add_int_mul8 sp hal (1 + nl)
            obtain ⟨st3, hrunL, hothL, ht3_3, hmemL, hpc3⟩ :=
              loadMemOff_ld_correct_lm lkm env.hrom pre2 (ct ++ post) AbiReg.t3 AbiReg.sp AbiReg.t1
                (by decide) (by decide) (by decide) (slotOff nl) hlink2
                (linkResolved_sub_pc64 env pre2 cl _ hlink2) st2 (by rw [htw2]; exact hpc2) halL
            have hpresL : PreservedRegs st2 st3 :=
              ⟨hothL _ (by decide) (by decide), hothL _ (by decide) (by decide),
               hothL _ (by decide) (by decide),
               hothL _ (by decide) (by decide)⟩
            let pre3 := pre2 ++ cl
            have htw3 : lkm.totalSize pre3 = lkm.totalSize pre2 + lkm.totalSize cl := lkm.totalSize_append _ _
            have hlink3 : lkm.linkSpec (pre3 ++ ct ++ post) = .ok (env.code, env.labels) := by
              simpa only [pre3, List.append_assoc] using hlink2
            obtain ⟨u, kt, st4, hu, hrun4, hpc4, ht0_4, hoth4, hmem4⟩ :=
              prog_emitSimpleExpr_sim env L lm loc hal pre3 post AbiReg.t0 AbiReg.t1
                (by decide) (by decide) (by decide) (by decide) (by decide) t ct hst htOk hlink3
                (linkResolved_sub_pc64 env pre3 ct post hlink3) st3 (by rw [htw3]; exact hpc3)
                (hpresL.gp.trans (hpres1.gp.trans (hpres0.gp.trans hgp)))
                (hpresL.sp.trans (hpres1.sp.trans (hpres0.sp.trans hsp)))
                (by rw [hmemL]; exact hm2) (by rw [hmemL]; exact hf2)
            have hpres4 : PreservedRegs st3 st4 :=
              ⟨hoth4 _ (by decide) (by decide), hoth4 _ (by decide) (by decide),
               hoth4 _ (by decide) (by decide),
               hoth4 _ (by decide) (by decide)⟩
            have hpcEq : lkm.totalSize pre3 + lkm.totalSize ct =
                lkm.totalSize pre + lkm.totalSize (c0 ++ c1 ++ cl ++ ct) := by
              rw [htw3, htw2, htw1]; simp only [lkm.totalSize_append]; omega
            simp only [hu, hvi, hve]
            exact ⟨_, st4, run_trans (run_trans (run_trans hrun0 hrun1) hrunL) hrun4,
              by rw [hpc4, hpcEq], ht0_4,
              by rw [hoth4 _ (by decide) (by decide), ht3_3, hpres1.sp.trans (hpres0.sp.trans hsp), hslot0_2],
              (hoth4 _ (by decide) (by decide)).trans ((hothL _ (by decide) (by decide)).trans ha0_2),
              (hpres0.trans hpres1).trans (hpresL.trans hpres4),
              by rw [hmem4, hmemL]; exact hm2, by rw [hmem4, hmemL]; exact hf2,
              by rw [hmem4, hmemL]; exact hpm0.trans hpm1⟩
          · obtain ⟨u, hu⟩ := hPureT; rw [hve] at hsim1; simp only [hu, hvi, hve]
            obtain ⟨k1, r', hrun1, hpc', hpres1, _⟩ := hsim1
            exact ⟨_, r', run_trans hrun0 hrun1, hpc', hpres0.trans hpres1⟩
        · obtain ⟨u, hu⟩ := hPureT; rw [hvi] at hsim0; simp only [hu, hvi]
          obtain ⟨k0, r', hrun0, hpc', hpres0, _⟩ := hsim0
          exact ⟨k0, r', hrun0, hpc', hpres0⟩
  | none =>
    let c0 := compileE env.tab nl 0 t ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 0))
    let c1 := compileE env.tab nl 1 i ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 1))
    let c2 := compileE env.tab nl 2 e
    let cl0 := loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff nl)
    let cl1 := loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t1 (slotOff (nl + 1))
    have hdef : compileTierStoreTriple env.tab nl t i e = c0 ++ c1 ++ c2 ++ cl0 ++ cl1 := by
      simp only [compileTierStoreTriple, hst, c0, c1, c2, cl0, cl1, Nat.add_zero, List.append_assoc]
    rw [hdef] at hlink h64 ⊢
    have hlink0 : lkm.linkSpec (pre ++ c0 ++ (c1 ++ c2 ++ cl0 ++ cl1 ++ post)) = .ok (env.code, env.labels) := by
      simpa only [List.append_assoc] using hlink
    have hsim0 := prog_evalToTemp_sim env L lm loc hal hlim htop t htOk (by omega) pre _ hlink0 st hpc hgp hsp hm hf
    rcases _root_.L.evalE_pure t ⟨lm, loc⟩ with ⟨u, hu⟩ | hu
    · rw [hu] at hsim0
      obtain ⟨k0, st1, hrun0, hpc0, hslot0, hpres0, hout0⟩ := hsim0
      have hm1 := progMemRel_of_tempSpan env L hlim htop (Nat.zero_le nt) hout0 hm
      have hf1 := progFrameOk_of_tempSpan L htop (Nat.zero_le nt) hout0 hf
      have hpm0 := progMemOutside_of_tempSpan L hlim htop (Nat.zero_le nt) hout0
      let pre1 := pre ++ c0
      have htwC0 : lkm.totalSize c0 =
          lkm.totalSize (compileE env.tab nl 0 t) + lkm.totalSize (storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 0))) :=
        lkm.totalSize_append _ _
      have htw1 : lkm.totalSize pre1 = lkm.totalSize pre + lkm.totalSize c0 := lkm.totalSize_append _ _
      have hlink1 : lkm.linkSpec (pre1 ++ c1 ++ (c2 ++ cl0 ++ cl1 ++ post)) = .ok (env.code, env.labels) := by
        simpa only [pre1, List.append_assoc] using hlink0
      have hsim1 := prog_evalToTemp_sim env L lm loc hal hlim htop (tmp := 1) i hiOk (by omega)
        pre1 _ hlink1 st1 (by rw [hpc0, htw1, htwC0]) (hpres0.gp.trans hgp) (hpres0.sp.trans hsp) hm1 hf1
      rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
      · rw [hvi] at hsim1
        obtain ⟨k1, st2, hrun1, hpc1, hslot1, hpres1, hout1⟩ := hsim1
        have hm2 := progMemRel_of_tempSpan env L hlim htop (by omega : 1 ≤ nt) hout1 hm1
        have hf2 := progFrameOk_of_tempSpan L htop (by omega : 1 ≤ nt) hout1 hf1
        have hpm1 := progMemOutside_of_tempSpan L hlim htop (by omega : 1 ≤ nt) hout1
        have hslot0_2 : readWord64 st2.mem (sp + BitVec.ofInt 64 (slotOff nl)) = u.toBitVec := by
          rw [← show nl + 0 = nl from Nat.add_zero nl, ← hslot0]
          apply MemEqOutside.readWord64_eq hout1
          intro k hk; rw [slotOff_ofInt]
          exact tempSpan_slot_disjoint (by omega) (by omega) (Nat.le_trans htop L.hStackValid) hk
        let pre2 := pre1 ++ c1
        have htwC1 : lkm.totalSize c1 =
            lkm.totalSize (compileE env.tab nl 1 i) + lkm.totalSize (storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 1))) :=
          lkm.totalSize_append _ _
        have htw2 : lkm.totalSize pre2 = lkm.totalSize pre1 + lkm.totalSize c1 := lkm.totalSize_append _ _
        have hlink2 : lkm.linkSpec (pre2 ++ c2 ++ (cl0 ++ cl1 ++ post)) = .ok (env.code, env.labels) := by
          simpa only [pre2, List.append_assoc] using hlink1
        have hsim2 := progEvalExpr_sim env L lm loc hal hlim htop e pre2 _ 2 heOk (by omega) hlink2
          (linkResolved_sub_pc64 env pre2 c2 _ hlink2) st2 (by rw [hpc1, htw2, htwC1])
          (hpres1.gp.trans (hpres0.gp.trans hgp)) (hpres1.sp.trans (hpres0.sp.trans hsp)) hm2 hf2
        rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨ve, hve⟩ | hve
        · rw [hve] at hsim2
          obtain ⟨k2, st3, hrun2, hpc2, ha0_3, hpres2, hout2⟩ := hsim2
          have hm3 := progMemRel_of_tempSpan env L hlim htop (by omega : 2 ≤ nt) hout2 hm2
          have hf3 := progFrameOk_of_tempSpan L htop (by omega : 2 ≤ nt) hout2 hf2
          have hpm2 := progMemOutside_of_tempSpan L hlim htop (by omega : 2 ≤ nt) hout2
          have hslot0_3 : readWord64 st3.mem (sp + BitVec.ofInt 64 (slotOff nl)) = u.toBitVec := by
            rw [← hslot0_2]; apply MemEqOutside.readWord64_eq hout2
            intro k hk; rw [show nl = nl + 0 from (Nat.add_zero nl).symm, slotOff_ofInt]
            exact tempSpan_slot_disjoint (by omega) (by omega) (Nat.le_trans htop L.hStackValid) hk
          have hslot1_3 : readWord64 st3.mem (sp + BitVec.ofInt 64 (slotOff (nl + 1))) = vi.toBitVec := by
            rw [← hslot1]; apply MemEqOutside.readWord64_eq hout2
            intro k hk; rw [slotOff_ofInt]
            exact tempSpan_slot_disjoint (by omega) (by omega) (Nat.le_trans htop L.hStackValid) hk
          let pre3 := pre2 ++ c2
          have htw3 : lkm.totalSize pre3 = lkm.totalSize pre2 + lkm.totalSize c2 := lkm.totalSize_append _ _
          have hlink3 : lkm.linkSpec (pre3 ++ cl0 ++ (cl1 ++ post)) = .ok (env.code, env.labels) := by
            simpa only [pre3, List.append_assoc] using hlink2
          have hsp3 : st3.getReg AbiReg.sp = sp := hpres2.sp.trans (hpres1.sp.trans (hpres0.sp.trans hsp))
          have halX0 : isAligned (st3.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff nl)) 8 = true := by
            rw [hsp3]; exact isAligned8_add_int_mul8 sp hal (1 + nl)
          obtain ⟨st4, hrunL0, hothL0, ht0_4, hmemL0, hpc4⟩ :=
            loadMemOff_ld_correct_lm lkm env.hrom pre3 _ AbiReg.t0 AbiReg.sp AbiReg.t1
              (by decide) (by decide) (by decide) (slotOff nl) hlink3
              (linkResolved_sub_pc64 env pre3 cl0 _ hlink3) st3 (by rw [htw3]; exact hpc2) halX0
          have hpresL0 : PreservedRegs st3 st4 :=
            ⟨hothL0 _ (by decide) (by decide), hothL0 _ (by decide) (by decide),
             hothL0 _ (by decide) (by decide),
             hothL0 _ (by decide) (by decide)⟩
          let pre4 := pre3 ++ cl0
          have htw4 : lkm.totalSize pre4 = lkm.totalSize pre3 + lkm.totalSize cl0 := lkm.totalSize_append _ _
          have hlink4 : lkm.linkSpec (pre4 ++ cl1 ++ post) = .ok (env.code, env.labels) := by
            simpa only [pre4, List.append_assoc] using hlink3
          have halX1 : isAligned (st4.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff (nl + 1))) 8 = true := by
            rw [hpresL0.sp.trans hsp3]; exact isAligned8_add_int_mul8 sp hal (1 + (nl + 1))
          obtain ⟨st5, hrunL1, hothL1, ht3_5, hmemL1, hpc5⟩ :=
            loadMemOff_ld_correct_lm lkm env.hrom pre4 post AbiReg.t3 AbiReg.sp AbiReg.t1
              (by decide) (by decide) (by decide) (slotOff (nl + 1)) hlink4
              (linkResolved_sub_pc64 env pre4 cl1 post hlink4) st4 (by rw [htw4]; exact hpc4) halX1
          have hpresL1 : PreservedRegs st4 st5 :=
            ⟨hothL1 _ (by decide) (by decide), hothL1 _ (by decide) (by decide),
             hothL1 _ (by decide) (by decide),
             hothL1 _ (by decide) (by decide)⟩
          have hpcEq : lkm.totalSize pre4 + lkm.totalSize cl1 =
              lkm.totalSize pre + lkm.totalSize (c0 ++ c1 ++ c2 ++ cl0 ++ cl1) := by
            rw [htw4, htw3, htw2, htw1]; simp only [lkm.totalSize_append]; omega
          simp only [hu, hvi, hve]
          exact ⟨_, st5, run_trans (run_trans (run_trans (run_trans hrun0 hrun1) hrun2) hrunL0) hrunL1,
            by rw [hpc5, hpcEq],
            by rw [hothL1 _ (by decide) (by decide), ht0_4, hsp3, hslot0_3],
            by rw [ht3_5, hmemL0, hpresL0.sp.trans hsp3, hslot1_3],
            (hothL1 _ (by decide) (by decide)).trans ((hothL0 _ (by decide) (by decide)).trans ha0_3),
            ((hpres0.trans hpres1).trans hpres2).trans (hpresL0.trans hpresL1),
            by rw [hmemL1, hmemL0]; exact hm3, by rw [hmemL1, hmemL0]; exact hf3,
            by rw [hmemL1, hmemL0]; exact (hpm0.trans hpm1).trans hpm2⟩
        · rw [hve] at hsim2; simp only [hu, hvi, hve]
          obtain ⟨k2, r', hrun2, hpc', hpres2, _⟩ := hsim2
          exact ⟨_, r', run_trans (run_trans hrun0 hrun1) hrun2, hpc', (hpres0.trans hpres1).trans hpres2⟩
      · rw [hvi] at hsim1; simp only [hu, hvi]
        obtain ⟨k1, r', hrun1, hpc', hpres1, _⟩ := hsim1
        exact ⟨_, r', run_trans hrun0 hrun1, hpc', hpres0.trans hpres1⟩
    · rw [hu] at hsim0; simp only [hu]
      obtain ⟨k0, r', hrun0, hpc', hpres0, _⟩ := hsim0
      exact ⟨k0, r', hrun0, hpc', hpres0⟩

theorem prog_st64_tail_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hlim : L.stackLimit.toNat ≤ sp.toNat) (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (a : _root_.L.ArrId) (ha : env.tab.wordPosOkB (_root_.L.TieredArray.t0 a) = true)
    (vi ve : _root_.L.Word) (hbound : vi.toNat < (lm.arr64 (_root_.L.TieredArray.t0 a)).size)
    (pre5 codeTail post : List AsmItem)
    (hcTail : codeTail = loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base64 (_root_.L.TieredArray.t0 a)) ++
      [Asm.slli AbiReg.t2 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2, Asm.sd AbiReg.t1 AbiReg.a0])
    (hlink5 : lkm.linkSpec (pre5 ++ codeTail ++ post) = .ok (env.code, env.labels))
    (st5 : State) (hpc5 : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre5))
    (hgp5 : st5.getReg AbiReg.gp = L.T)
    (ht0_5 : st5.getReg AbiReg.t0 = vi.toBitVec)
    (ha0_5 : st5.getReg AbiReg.a0 = ve.toBitVec)
    (hm5 : ProgMemRel env.tab L st5.mem lm) (hf5 : ProgFrameOk L sp st5.mem nl loc) :
    ∃ k r',
      RV64.run env.rom k st5 = .cont r' ∧
      r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre5 + lkm.totalSize codeTail)) ∧
      PreservedRegs st5 r' ∧
      ProgMemRel env.tab L r'.mem (lm.set64 (_root_.L.TieredArray.t0 a) vi ve) ∧
      ProgFrameOk L sp r'.mem nl loc ∧
      ProgMemOutside (FnWriteMask L sp nl nt) st5.mem r'.mem := by
  let cl2 := loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base64 (.t0 a))
  let ctail := [Asm.slli AbiReg.t2 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2, Asm.sd AbiReg.t1 AbiReg.a0]
  have hcEq : codeTail = cl2 ++ ctail := by rw [hcTail]
  rw [hcEq] at hlink5
  have hlink5' : lkm.linkSpec (pre5 ++ cl2 ++ (ctail ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink5
  have halBase : isAligned (st5.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.base64 (.t0 a))) 8 = true := by
    rw [hgp5, Tab.base64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
  obtain ⟨st6, hrun5, hoth5, ht1_6, hmem5, hpc6⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre5 _ AbiReg.t1 AbiReg.gp AbiReg.t2
      (by decide) (by decide) (by decide) (env.tab.base64 (.t0 a)) hlink5'
      (linkResolved_sub_pc64 env pre5 cl2 _ hlink5') st5 hpc5 halBase
  have hpres5 : PreservedRegs st5 st6 :=
    ⟨hoth5 _ (by decide) (by decide), hoth5 _ (by decide) (by decide), hoth5 _ (by decide) (by decide), hoth5 _ (by decide) (by decide)⟩
  let pre6 := pre5 ++ cl2
  have htwPre6 : lkm.totalSize pre6 = lkm.totalSize pre5 + lkm.totalSize cl2 := lkm.totalSize_append pre5 cl2
  have hpc6' : st6.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre6) := by rw [hpc6, htwPre6]
  have hlink6 : lkm.linkSpec (pre6 ++ ctail ++ post) =
      .ok (env.code, env.labels) := by simpa [pre6, List.append_assoc] using hlink5'
  have ⟨hlA, hlBC⟩ := linkResolved_mid_split lkm pre6 [Asm.slli AbiReg.t2 AbiReg.t0 3#6]
    [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2, Asm.sd AbiReg.t1 AbiReg.a0] post hlink6
  have ⟨hlB, hlC⟩ := linkResolved_mid_split lkm (pre6 ++ [Asm.slli AbiReg.t2 AbiReg.t0 3#6])
    [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2] [Asm.sd AbiReg.t1 AbiReg.a0] post hlBC
  have htwA : lkm.totalSize [Asm.slli AbiReg.t2 AbiReg.t0 3#6] = 1 := by simp only [Asm.slli, lkm.totalSize_instr]
  have htwB : lkm.totalSize [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2] = 1 := by simp only [Asm.add, lkm.totalSize_instr]
  let st7 := stepReg st6 AbiReg.t2
    (evalShiftImm .slli (st6.getReg AbiReg.t0) 3#6) (BitVec.ofNat 64 (4 * (lkm.totalSize pre6 + 1)))
  obtain ⟨hrun6, hpc7, ht2_7, hoth6, hmem6, hpres6⟩ :=
    run_shImm_step env pre6 _ .slli AbiReg.t2 AbiReg.t0 3#6 nonPreserved_t2 hlA st6 hpc6'
  let st8 := stepReg st7 AbiReg.t1
    (evalAlu .add (st7.getReg AbiReg.t1) (st7.getReg AbiReg.t2))
    (BitVec.ofNat 64 (4 * (lkm.totalSize (pre6 ++ [Asm.slli AbiReg.t2 AbiReg.t0 3#6]) + 1)))
  obtain ⟨hrun7, hpc8, ht1_8, hoth7, hmem7, hpres7⟩ :=
    run_alu_step env (pre6 ++ [Asm.slli AbiReg.t2 AbiReg.t0 3#6]) _ .add AbiReg.t1 AbiReg.t1 AbiReg.t2
      nonPreserved_t1 hlB st7 (by rw [lkm.totalSize_append, htwA]; exact hpc7)
  rcases hm5.2.1 (.t0 a) ha with ⟨hcap64, _, _, hbase64, _⟩
  have ht1Addr : st8.getReg AbiReg.t1 = L.base64 (.t0 a) + BitVec.ofNat 64 (8 * vi.toNat) := by
    rw [ht1_8, evalAlu, hoth6 _ (by decide), ht1_6, hgp5, hbase64, ht2_7, hoth5 _ (by decide) (by decide)]
    change L.base64 (.t0 a) + evalShiftImm .slli (st5.getReg AbiReg.t0) 3#6 = _
    rw [ht0_5, shl3_ofNat_eq vi (by omega)]
  have halDst : isAligned (st8.getReg AbiReg.t1) 8 = true := by
    rw [ht1Addr]; exact isAligned8_add_mul8 _ (L.h64Align (.t0 a)) vi.toNat
  have hrun8 := step_sd_zero env
    ((pre6 ++ [Asm.slli AbiReg.t2 AbiReg.t0 3#6]) ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2]) post
    AbiReg.t1 AbiReg.a0 hlC st8 (by rw [lkm.totalSize_append, htwB]; exact hpc8) halDst
  let st9 : State :=
    { pc := BitVec.ofNat 64 (4 * (lkm.totalSize ((pre6 ++ [Asm.slli AbiReg.t2 AbiReg.t0 3#6]) ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2]) + 1))
    , regs := st8.regs
    , mem := writeWord64 st8.mem (st8.getReg AbiReg.t1) (st8.getReg AbiReg.a0) }
  have hpc9' : st9.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre5 + lkm.totalSize codeTail)) := by
    have htwct : lkm.totalSize ctail = 3 := by simp only [ctail, Asm.slli, Asm.add, Asm.sd, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
    have htwCT : lkm.totalSize codeTail = lkm.totalSize cl2 + 3 := by rw [hcEq, lkm.totalSize_append, htwct]
    have hpcEq : lkm.totalSize ((pre6 ++ [Asm.slli AbiReg.t2 AbiReg.t0 3#6]) ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2]) + 1 =
        lkm.totalSize pre5 + lkm.totalSize codeTail := by
      rw [lkm.totalSize_append _ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2], htwB,
          lkm.totalSize_append pre6 [Asm.slli AbiReg.t2 AbiReg.t0 3#6], htwA, htwCT, htwPre6]; omega
    dsimp only [st9]; rw [hpcEq]
  have ha0_8 : st8.getReg AbiReg.a0 = ve.toBitVec :=
    (hoth7 _ (by decide)).trans ((hoth6 _ (by decide)).trans ((hoth5 _ (by decide) (by decide)).trans ha0_5))
  have hstMem8 : st8.mem = st5.mem := by rw [hmem7, hmem6, hmem5]
  have hcapVi : vi.toNat < L.cap64 (.t0 a) := Nat.lt_of_lt_of_le hbound hcap64
  refine ⟨_, st9, run_trans (run_trans (run_trans hrun5 hrun6) hrun7) hrun8, hpc9', ?_, ?_, ?_, ?_⟩
  · exact hpres5.trans (hpres6.trans (hpres7.trans (preservedRegs_of_regs rfl)))
  · dsimp only [st9]; rw [ht1Addr, ha0_8, hstMem8]; exact ProgMemRel.set64 hm5 (.t0 a) ha vi ve hbound
  · dsimp only [st9]; rw [ht1Addr, ha0_8, hstMem8]
    exact progFrameOk_write64_arr64 L hlim htop (.t0 a) ha vi.toNat hcapVi st5.mem ve.toBitVec hf5
  · dsimp only [st9]; rw [ht1Addr, ha0_8, hstMem8]
    exact progMemOutside_write64_arr64 L (.t0 a) ha vi.toNat hcapVi st5.mem ve.toBitVec

theorem prog_st64_exec_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (a : _root_.L.ArrId) (ha : env.tab.wordPosOkB (_root_.L.TieredArray.t0 a) = true)
    (vi ve : _root_.L.Word)
    (pre2 codeRest post : List AsmItem)
    (hcRest : codeRest = loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff nl) ++
      loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.len64 (_root_.L.TieredArray.t0 a)) ++
      [Asm.bgeu AbiReg.t0 AbiReg.t1 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base64 (_root_.L.TieredArray.t0 a)) ++
      [Asm.slli AbiReg.t2 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2, Asm.sd AbiReg.t1 AbiReg.a0])
    (hlink2 : lkm.linkSpec (pre2 ++ codeRest ++ post) = .ok (env.code, env.labels))
    (st2 : State) (hpc2 : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2))
    (hgp2 : st2.getReg AbiReg.gp = L.T) (hsp2 : st2.getReg AbiReg.sp = sp)
    (ha0 : st2.getReg AbiReg.a0 = ve.toBitVec)
    (hslot0 : readWord64 st2.mem (sp + BitVec.ofInt 64 (slotOff nl)) = vi.toBitVec)
    (hm2 : ProgMemRel env.tab L st2.mem lm) (hf2 : ProgFrameOk L sp st2.mem nl loc) :
    if vi.toNat < (lm.arr64 (_root_.L.TieredArray.t0 a)).size then
      ∃ k r',
        RV64.run env.rom k st2 = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre2 + lkm.totalSize codeRest)) ∧
        PreservedRegs st2 r' ∧
        ProgMemRel env.tab L r'.mem (lm.set64 (_root_.L.TieredArray.t0 a) vi ve) ∧
        ProgFrameOk L sp r'.mem nl loc ∧
        ProgMemOutside (FnWriteMask L sp nl nt) st2.mem r'.mem
    else
      ∃ k r',
        RV64.run env.rom k st2 = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st2 r' := by
  let cl0 := loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff nl)
  let cl1 := loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.len64 (.t0 a))
  let cbr := [Asm.bgeu AbiReg.t0 AbiReg.t1 errLabel]
  let cl2 := loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base64 (.t0 a))
  let ctail := [Asm.slli AbiReg.t2 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2, Asm.sd AbiReg.t1 AbiReg.a0]
  have hcEq : codeRest = cl0 ++ cl1 ++ cbr ++ cl2 ++ ctail := by rw [hcRest]
  rw [hcEq] at hlink2
  have hlink2' : lkm.linkSpec (pre2 ++ cl0 ++ (cl1 ++ cbr ++ cl2 ++ ctail ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink2
  have halX : isAligned (st2.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff nl)) 8 = true := by
    rw [hsp2]; exact isAligned8_add_int_mul8 sp hal (1 + nl)
  obtain ⟨st3, hrun2, hoth2, ht0_3, hmem2, hpc3⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre2 _ AbiReg.t0 AbiReg.sp AbiReg.t1
      (by decide) (by decide) (by decide) (slotOff nl) hlink2'
      (linkResolved_sub_pc64 env pre2 cl0 _ hlink2') st2 hpc2 halX
  have hpres2 : PreservedRegs st2 st3 :=
    ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide)⟩
  let pre3 := pre2 ++ cl0
  have htwPre3 : lkm.totalSize pre3 = lkm.totalSize pre2 + lkm.totalSize cl0 := lkm.totalSize_append pre2 cl0
  have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre3) := by rw [hpc3, htwPre3]
  have hlink3 : lkm.linkSpec (pre3 ++ cl1 ++ (cbr ++ cl2 ++ ctail ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre3, List.append_assoc] using hlink2'
  have halLen : isAligned (st3.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.len64 (.t0 a))) 8 = true := by
    rw [hpres2.gp.trans hgp2, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
  obtain ⟨st4, hrun3, hoth3, ht1_4, hmem3, hpc4⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre3 _ AbiReg.t1 AbiReg.gp AbiReg.t2
      (by decide) (by decide) (by decide) (env.tab.len64 (.t0 a)) hlink3
      (linkResolved_sub_pc64 env pre3 cl1 _ hlink3) st3 hpc3' halLen
  have hpres3 : PreservedRegs st3 st4 :=
    ⟨hoth3 _ (by decide) (by decide), hoth3 _ (by decide) (by decide), hoth3 _ (by decide) (by decide), hoth3 _ (by decide) (by decide)⟩
  let pre4 := pre3 ++ cl1
  have htwPre4 : lkm.totalSize pre4 = lkm.totalSize pre3 + lkm.totalSize cl1 := lkm.totalSize_append pre3 cl1
  have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre4) := by rw [hpc4, htwPre4]
  have hlink4 : lkm.linkSpec (pre4 ++ cbr ++ (cl2 ++ ctail ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre4, List.append_assoc] using hlink3
  have hbr := run_br_step env pre4 _ .bgeu AbiReg.t0 AbiReg.t1 errLabel env.errTarget env.herrLbl (by decide) hlink4 st4 hpc4'
  have ht0Val : st4.getReg AbiReg.t0 = vi.toBitVec := by
    rw [hoth3 _ (by decide) (by decide), ht0_3, hsp2, hslot0]
  rcases hm2.2.1 (.t0 a) ha with ⟨_, _, hlen64, _, _⟩
  have ht1Val : st4.getReg AbiReg.t1 = BitVec.ofNat 64 (lm.arr64 (.t0 a)).size := by
    rw [ht1_4, hmem2, hpres2.gp.trans hgp2, hlen64]
  have ha0Val : st4.getReg AbiReg.a0 = ve.toBitVec :=
    (hoth3 _ (by decide) (by decide)).trans ((hoth2 _ (by decide) (by decide)).trans ha0)
  have hcondEq : evalBranch .bgeu (st4.getReg AbiReg.t0) (st4.getReg AbiReg.t1) =
      decide ((lm.arr64 (.t0 a)).size ≤ vi.toNat) := by
    rw [ht0Val, ht1Val, u64_toBitVec_eq_ofNat]
    exact evalBranch_bgeu_nat vi.toBitVec.isLt (by omega)
  obtain ⟨kBr, st5, _, hrun4, hpcBr, hoth4, hpres4, hmem4Br⟩ := hbr
  by_cases hbound : vi.toNat < (lm.arr64 (.t0 a)).size
  · simp only [hbound, ↓reduceIte]
    have hbrF : evalBranch .bgeu (st4.getReg AbiReg.t0) (st4.getReg AbiReg.t1) = false := by
      rw [hcondEq, decide_eq_false_iff_not]; omega
    let pre5 := pre4 ++ cbr
    have htwPre5 : lkm.totalSize pre5 = lkm.totalSize pre4 + lkm.totalSize cbr :=
      lkm.totalSize_append pre4 cbr
    have hpc5' : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre5) := by
      rw [hpcBr, hbrF]; simp only [Bool.false_eq_true, ↓reduceIte, htwPre5, cbr, Asm.bgeu, Asm.br, lkm.totalSize_singleton]
    have hlink5 : lkm.linkSpec (pre5 ++ (cl2 ++ ctail) ++ post) =
        .ok (env.code, env.labels) := by simpa [pre5, List.append_assoc] using hlink4
    have hmem4 : st5.mem = st2.mem := by rw [hmem4Br, hmem3, hmem2]
    obtain ⟨kTail, r', hrunTail, hpcR', hpresTail, hmR', hfR', houtR'⟩ :=
      prog_st64_tail_sim env L lm loc hlim htop a ha vi ve hbound pre5 (cl2 ++ ctail) post rfl hlink5
        st5 hpc5' ((hoth4 _ (by decide)).trans (hpres3.gp.trans (hpres2.gp.trans hgp2)))
        ((hoth4 _ (by decide)).trans ht0Val) ((hoth4 _ (by decide)).trans ha0Val)
        (hmem4 ▸ hm2) (hmem4 ▸ hf2)
    have hpcEq : lkm.totalSize pre5 + lkm.totalSize (cl2 ++ ctail) = lkm.totalSize pre2 + lkm.totalSize codeRest := by
      rw [htwPre5, htwPre4, htwPre3, hcEq,
          lkm.totalSize_append (((cl0 ++ cl1) ++ cbr) ++ cl2) ctail,
          lkm.totalSize_append ((cl0 ++ cl1) ++ cbr) cl2,
          lkm.totalSize_append (cl0 ++ cl1) cbr,
          lkm.totalSize_append cl0 cl1, lkm.totalSize_append cl2 ctail]; omega
    refine ⟨_, r', run_trans (run_trans (run_trans hrun2 hrun3) hrun4) hrunTail, by rw [hpcR', hpcEq], ?_, hmR', hfR', ?_⟩
    · exact hpres2.trans (hpres3.trans (hpres4.trans hpresTail))
    · rw [← hmem4]; exact houtR'
  · simp only [hbound, ↓reduceIte]
    have hbrT : evalBranch .bgeu (st4.getReg AbiReg.t0) (st4.getReg AbiReg.t1) = true := by
      rw [hcondEq, decide_eq_true_iff]; omega
    have hpcT : st5.pc = BitVec.ofNat 64 (4 * env.errTarget) := by
      rw [hpcBr, hbrT]; rfl
    exact ⟨_, st5, run_trans (run_trans hrun2 hrun3) hrun4, hpcT,
      hpres2.trans (hpres3.trans hpres4)⟩

theorem prog_st64_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (a : _root_.L.ArrId) (i e : _root_.L.Expr)
    (ha : env.tab.wordPosOkB (_root_.L.TieredArray.t0 a) = true)
    (hiOk : exprOkB env.tab nl i = true) (heOk : exprOkB env.tab nl e = true)
    (hnt : max (maxTempsExpr i) (1 + maxTempsExpr e) ≤ nt)
    (pre post : List AsmItem)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOk L sp st.mem nl loc)
    (hlink : lkm.linkSpec (pre ++ (compileStorePair env.tab nl i e ++
      loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.len64 (_root_.L.TieredArray.t0 a)) ++
      [Asm.bgeu AbiReg.t0 AbiReg.t1 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base64 (_root_.L.TieredArray.t0 a)) ++
      [Asm.slli AbiReg.t2 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2, Asm.sd AbiReg.t1 AbiReg.a0]) ++ post) =
      .ok (env.code, env.labels)) :
    let codeS := compileStorePair env.tab nl i e ++
      loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.len64 (_root_.L.TieredArray.t0 a)) ++
      [Asm.bgeu AbiReg.t0 AbiReg.t1 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base64 (_root_.L.TieredArray.t0 a)) ++
      [Asm.slli AbiReg.t2 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2, Asm.sd AbiReg.t1 AbiReg.a0]
    match (do let j ← _root_.L.evalE i; let v ← _root_.L.evalE e; _root_.L.st64 (_root_.L.TieredArray.t0 a) j v)
        { mem := lm, loc := loc } with
    | .ok (_, st') =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize codeS)) ∧
        PreservedRegs st r' ∧
        ProgMemRel env.tab L r'.mem st'.mem ∧
        ProgFrameOk L sp r'.mem nl st'.loc ∧
        ProgMemOutside (FnWriteMask L sp nl nt) st.mem r'.mem
    | .error _ =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st r' := by
  let cp := compileStorePair env.tab nl i e
  let cl1 := loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.len64 (.t0 a))
  let cbr := [Asm.bgeu AbiReg.t0 AbiReg.t1 errLabel]
  let cl2 := loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base64 (.t0 a))
  let ctail := [Asm.slli AbiReg.t2 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2, Asm.sd AbiReg.t1 AbiReg.a0]
  have hlinkP : lkm.linkSpec (pre ++ cp ++ (cl1 ++ cbr ++ cl2 ++ ctail ++ post)) = .ok (env.code, env.labels) := by
    simpa only [cp, cl1, cbr, cl2, ctail, List.append_assoc] using hlink
  have rp := prog_compileStorePair_sim env L lm loc hal hlim htop i e hiOk heOk hnt
    pre (cl1 ++ cbr ++ cl2 ++ ctail ++ post) st hpc hgp hsp hm hf hlinkP
  rcases _root_.L.evalE_pure i { mem := lm, loc := loc } with ⟨vi, hiE⟩ | hiE
  · rcases _root_.L.evalE_pure e { mem := lm, loc := loc } with ⟨ve, heE⟩ | heE
    · rw [hiE, heE] at rp
      obtain ⟨kp, st3, hrunP, hpc3, ht0_3, ha0_3, hpresP, hm2, hf2, hpmP⟩ := rp
      let pre3 := pre ++ cp
      have htwPre3 : lkm.totalSize pre3 = lkm.totalSize pre + lkm.totalSize cp := lkm.totalSize_append _ _
      have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre3) := by rw [hpc3, htwPre3]
      have hlink3 : lkm.linkSpec (pre3 ++ cl1 ++ (cbr ++ cl2 ++ ctail ++ post)) = .ok (env.code, env.labels) := by
        simpa only [pre3, List.append_assoc] using hlinkP
      have halLen : isAligned (st3.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.len64 (.t0 a))) 8 = true := by
        rw [hpresP.gp.trans hgp, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
      obtain ⟨st4, hrun3, hoth3, ht1_4, hmem3, hpc4⟩ :=
        loadMemOff_ld_correct_lm lkm env.hrom pre3 _ AbiReg.t1 AbiReg.gp AbiReg.t2
          (by decide) (by decide) (by decide) (env.tab.len64 (.t0 a)) hlink3
          (linkResolved_sub_pc64 env pre3 cl1 _ hlink3) st3 hpc3' halLen
      have hpres3 : PreservedRegs st3 st4 :=
        ⟨hoth3 _ (by decide) (by decide), hoth3 _ (by decide) (by decide), hoth3 _ (by decide) (by decide), hoth3 _ (by decide) (by decide)⟩
      let pre4 := pre3 ++ cl1
      have htwPre4 : lkm.totalSize pre4 = lkm.totalSize pre3 + lkm.totalSize cl1 := lkm.totalSize_append _ _
      have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre4) := by rw [hpc4, htwPre4]
      have hlink4 : lkm.linkSpec (pre4 ++ cbr ++ (cl2 ++ ctail ++ post)) = .ok (env.code, env.labels) := by
        simpa only [pre4, List.append_assoc] using hlink3
      have hbr := run_br_step env pre4 _ .bgeu AbiReg.t0 AbiReg.t1 errLabel env.errTarget env.herrLbl (by decide) hlink4 st4 hpc4'
      have ht0Val : st4.getReg AbiReg.t0 = vi.toBitVec := (hoth3 _ (by decide) (by decide)).trans ht0_3
      rcases hm2.2.1 (.t0 a) ha with ⟨_, _, hlen64, _, _⟩
      have ht1Val : st4.getReg AbiReg.t1 = BitVec.ofNat 64 (lm.arr64 (.t0 a)).size := by
        rw [ht1_4, hpresP.gp.trans hgp, hlen64]
      have ha0Val : st4.getReg AbiReg.a0 = ve.toBitVec := (hoth3 _ (by decide) (by decide)).trans ha0_3
      have hcondEq : evalBranch .bgeu (st4.getReg AbiReg.t0) (st4.getReg AbiReg.t1) =
          decide ((lm.arr64 (.t0 a)).size ≤ vi.toNat) := by
        rw [ht0Val, ht1Val, u64_toBitVec_eq_ofNat]
        exact evalBranch_bgeu_nat vi.toBitVec.isLt (by omega)
      obtain ⟨kBr, st5, _, hrun4, hpcBr, hoth4, hpres4, hmem4Br⟩ := hbr
      by_cases hbound : vi.toNat < (lm.arr64 (.t0 a)).size
      · have hbrF : evalBranch .bgeu (st4.getReg AbiReg.t0) (st4.getReg AbiReg.t1) = false := by
          rw [hcondEq, decide_eq_false_iff_not]; omega
        let pre5 := pre4 ++ cbr
        have htwPre5 : lkm.totalSize pre5 = lkm.totalSize pre4 + lkm.totalSize cbr := lkm.totalSize_append _ _
        have hpc5' : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre5) := by
          rw [hpcBr, hbrF]; simp only [Bool.false_eq_true, ↓reduceIte, htwPre5, cbr, Asm.bgeu, Asm.br, lkm.totalSize_singleton]
        have hlink5 : lkm.linkSpec (pre5 ++ (cl2 ++ ctail) ++ post) = .ok (env.code, env.labels) := by
          simpa only [pre5, List.append_assoc] using hlink4
        have hmem4 : st5.mem = st3.mem := by rw [hmem4Br, hmem3]
        obtain ⟨kTail, r', hrunTail, hpcR', hpresTail, hmR', hfR', houtR'⟩ :=
          prog_st64_tail_sim env L lm loc hlim htop a ha vi ve hbound pre5 (cl2 ++ ctail) post rfl hlink5
            st5 hpc5' ((hoth4 _ (by decide)).trans (hpres3.gp.trans (hpresP.gp.trans hgp)))
            ((hoth4 _ (by decide)).trans ht0Val) ((hoth4 _ (by decide)).trans ha0Val)
            (hmem4 ▸ hm2) (hmem4 ▸ hf2)
        have hmini : (do let j ← _root_.L.evalE i; let v ← _root_.L.evalE e; _root_.L.st64 (.t0 a) j v) { mem := lm, loc := loc } =
            .ok ((), { mem := lm.set64 (.t0 a) vi ve, loc := loc }) := by
          simp only [Bind.bind, StateT.bind, Except.bind, hiE, heE, _root_.L.st64, get, getThe,
            MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set,
            Pure.pure, Except.pure, hbound, ↓reduceIte]
        rw [hmini]
        have hpcEq : lkm.totalSize pre5 + lkm.totalSize (cl2 ++ ctail) =
            lkm.totalSize pre + lkm.totalSize (cp ++ cl1 ++ cbr ++ cl2 ++ ctail) := by
          rw [htwPre5, htwPre4, htwPre3]; simp only [lkm.totalSize_append]; omega
        exact ⟨_, r', run_trans (run_trans (run_trans hrunP hrun3) hrun4) hrunTail, by rw [hpcR', hpcEq],
          hpresP.trans (hpres3.trans (hpres4.trans hpresTail)), hmR', hfR', hpmP.trans (hmem4 ▸ houtR')⟩
      · have hbrT : evalBranch .bgeu (st4.getReg AbiReg.t0) (st4.getReg AbiReg.t1) = true := by
          rw [hcondEq, decide_eq_true_iff]; omega
        have hmini : (do let j ← _root_.L.evalE i; let v ← _root_.L.evalE e; _root_.L.st64 (.t0 a) j v) { mem := lm, loc := loc } =
            .error .oob := by
          simp only [Bind.bind, StateT.bind, Except.bind, hiE, heE, _root_.L.st64, get, getThe,
            MonadStateOf.get, StateT.get, throw, throwThe, MonadExceptOf.throw,
            Pure.pure, Except.pure, hbound, ↓reduceIte]; rfl
        rw [hmini]
        exact ⟨_, st5, run_trans (run_trans hrunP hrun3) hrun4, by rw [hpcBr, hbrT]; rfl,
          hpresP.trans (hpres3.trans hpres4)⟩
    · simp only [Bind.bind, StateT.bind, Except.bind, hiE, heE] at rp ⊢; exact rp
  · simp only [Bind.bind, StateT.bind, Except.bind, hiE] at rp ⊢; exact rp

theorem prog_st64t_tail_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hlim : L.stackLimit.toNat ≤ sp.toNat) (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (a : _root_.L.ArrId) (u vi ve : _root_.L.Word) (ha : env.tab.tieredOkB a = true)
    (pre7 codeTail post : List AsmItem)
    (hcTail : codeTail = [Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t4 (env.tab.base64 (_root_.L.TieredArray.t0 a)) ++
      [Asm.slli AbiReg.t4 AbiReg.t3 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4, Asm.sd AbiReg.t1 AbiReg.a0])
    (hlink7 : lkm.linkSpec (pre7 ++ codeTail ++ post) = .ok (env.code, env.labels))
    (st7 : State) (hpc7 : st7.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre7))
    (ht3Val : st7.getReg AbiReg.t3 = vi.toBitVec)
    (ht2Val : st7.getReg AbiReg.t2 = BitVec.ofNat 64 (lm.arr64 (_root_.L.tierA a u)).size)
    (ha0Val : st7.getReg AbiReg.a0 = ve.toBitVec)
    (ht1BaseAddr : st7.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.base64 (.t0 a)) =
      L.T + BitVec.ofInt 64 (env.tab.base64 (_root_.L.tierA a u)))
    (hm7 : ProgMemRel env.tab L st7.mem lm) (hf7 : ProgFrameOk L sp st7.mem nl loc) :
    if vi.toNat < (lm.arr64 (_root_.L.tierA a u)).size then
      ∃ k r',
        RV64.run env.rom k st7 = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre7 + lkm.totalSize codeTail)) ∧
        PreservedRegs st7 r' ∧
        ProgMemRel env.tab L r'.mem (lm.set64 (_root_.L.tierA a u) vi ve) ∧
        ProgFrameOk L sp r'.mem nl loc ∧
        ProgMemOutside (FnWriteMask L sp nl nt) st7.mem r'.mem
    else
      ∃ k r',
        RV64.run env.rom k st7 = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st7 r' := by
  let cbr := [Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel]
  let cl3 := loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t4 (env.tab.base64 (.t0 a))
  let ctail := [Asm.slli AbiReg.t4 AbiReg.t3 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4, Asm.sd AbiReg.t1 AbiReg.a0]
  have hcEq : codeTail = cbr ++ cl3 ++ ctail := by rw [hcTail]
  rw [hcEq] at hlink7
  have hlink7' : lkm.linkSpec (pre7 ++ cbr ++ (cl3 ++ ctail ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink7
  have hta := tieredOk_len64_addr_T L.T a u ha
  rcases hm7.2.1 (_root_.L.tierA a u) hta.1 with ⟨hcap64, hlt64, _, hbase64, _⟩
  have hbr := run_br_step env pre7 _ .bgeu AbiReg.t3 AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide) hlink7' st7 hpc7
  have hcondEq : evalBranch .bgeu (st7.getReg AbiReg.t3) (st7.getReg AbiReg.t2) =
      decide ((lm.arr64 (_root_.L.tierA a u)).size ≤ vi.toNat) := by
    rw [ht3Val, ht2Val, u64_toBitVec_eq_ofNat]
    exact evalBranch_bgeu_nat vi.toBitVec.isLt (by omega)
  obtain ⟨kBr, st8, _, hrun7, hpcBr, hoth7, hpres7, hmem7Br⟩ := hbr
  by_cases hbound : vi.toNat < (lm.arr64 (_root_.L.tierA a u)).size
  · simp only [hbound, ↓reduceIte]
    have hbrF : evalBranch .bgeu (st7.getReg AbiReg.t3) (st7.getReg AbiReg.t2) = false := by
      rw [hcondEq, decide_eq_false_iff_not]; omega
    let pre8 := pre7 ++ cbr
    have htwPre8 : lkm.totalSize pre8 = lkm.totalSize pre7 + lkm.totalSize cbr := lkm.totalSize_append pre7 cbr
    have hpc8' : st8.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre8) := by
      rw [hpcBr, hbrF]; simp only [Bool.false_eq_true, ↓reduceIte, htwPre8, cbr, Asm.bgeu, Asm.br, lkm.totalSize_singleton]
    have hlink8 : lkm.linkSpec (pre8 ++ cl3 ++ (ctail ++ post)) =
        .ok (env.code, env.labels) := by simpa [pre8, List.append_assoc] using hlink7'
    have halBase : isAligned (st8.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.base64 (.t0 a))) 8 = true := by
      rw [hoth7 _ (by decide), ht1BaseAddr, Tab.base64_eq_nat]
      exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨st9, hrun8, hoth8, ht1_9, hmem8, hpc9⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom pre8 _ AbiReg.t1 AbiReg.t1 AbiReg.t4
        (by decide) (by decide) (by decide) (env.tab.base64 (.t0 a)) hlink8
        (linkResolved_sub_pc64 env pre8 cl3 _ hlink8) st8 hpc8' halBase
    have hpres8 : PreservedRegs st8 st9 :=
      ⟨hoth8 _ (by decide) (by decide), hoth8 _ (by decide) (by decide), hoth8 _ (by decide) (by decide), hoth8 _ (by decide) (by decide)⟩
    let pre9 := pre8 ++ cl3
    have htwPre9 : lkm.totalSize pre9 = lkm.totalSize pre8 + lkm.totalSize cl3 := lkm.totalSize_append pre8 cl3
    have hpc9' : st9.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre9) := by rw [hpc9, htwPre9]
    have hlink9 : lkm.linkSpec (pre9 ++ ctail ++ post) =
        .ok (env.code, env.labels) := by simpa [pre9, List.append_assoc] using hlink8
    have ⟨hlA, hlBC⟩ := linkResolved_mid_split lkm pre9 [Asm.slli AbiReg.t4 AbiReg.t3 3#6]
      [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4, Asm.sd AbiReg.t1 AbiReg.a0] post hlink9
    have ⟨hlB, hlC⟩ := linkResolved_mid_split lkm (pre9 ++ [Asm.slli AbiReg.t4 AbiReg.t3 3#6])
      [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4] [Asm.sd AbiReg.t1 AbiReg.a0] post hlBC
    have htwA : lkm.totalSize [Asm.slli AbiReg.t4 AbiReg.t3 3#6] = 1 := by simp only [Asm.slli, lkm.totalSize_instr]
    have htwB : lkm.totalSize [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4] = 1 := by simp only [Asm.add, lkm.totalSize_instr]
    let st10 := stepReg st9 AbiReg.t4
      (evalShiftImm .slli (st9.getReg AbiReg.t3) 3#6) (BitVec.ofNat 64 (4 * (lkm.totalSize pre9 + 1)))
    obtain ⟨hrun9, hpc10, ht4_10, hoth9, hmem9, hpres9⟩ :=
      run_shImm_step env pre9 _ .slli AbiReg.t4 AbiReg.t3 3#6 nonPreserved_t4 hlA st9 hpc9'
    let st11 := stepReg st10 AbiReg.t1
      (evalAlu .add (st10.getReg AbiReg.t1) (st10.getReg AbiReg.t4))
      (BitVec.ofNat 64 (4 * (lkm.totalSize (pre9 ++ [Asm.slli AbiReg.t4 AbiReg.t3 3#6]) + 1)))
    obtain ⟨hrun10, hpc11, ht1_11, hoth10, hmem10, hpres10⟩ :=
      run_alu_step env (pre9 ++ [Asm.slli AbiReg.t4 AbiReg.t3 3#6]) _ .add AbiReg.t1 AbiReg.t1 AbiReg.t4
        nonPreserved_t1 hlB st10 (by rw [lkm.totalSize_append, htwA]; exact hpc10)
    have ht1Addr : st11.getReg AbiReg.t1 = L.base64 (_root_.L.tierA a u) + BitVec.ofNat 64 (8 * vi.toNat) := by
      rw [ht1_11, evalAlu, hoth9 _ (by decide), ht1_9, hmem7Br, hoth7 _ (by decide)]
      rw [ht1BaseAddr, hbase64, ht4_10, hoth8 _ (by decide) (by decide)]
      change L.base64 (_root_.L.tierA a u) + evalShiftImm .slli (st8.getReg AbiReg.t3) 3#6 = _
      rw [hoth7 _ (by decide), ht3Val, shl3_ofNat_eq vi (by omega)]
    have halDst : isAligned (st11.getReg AbiReg.t1) 8 = true := by
      rw [ht1Addr]; exact isAligned8_add_mul8 _ (L.h64Align (_root_.L.tierA a u)) vi.toNat
    have hrun11 := step_sd_zero env
      ((pre9 ++ [Asm.slli AbiReg.t4 AbiReg.t3 3#6]) ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4]) post
      AbiReg.t1 AbiReg.a0 hlC st11 (by rw [lkm.totalSize_append, htwB]; exact hpc11) halDst
    let st12 : State :=
      { pc := BitVec.ofNat 64 (4 * (lkm.totalSize ((pre9 ++ [Asm.slli AbiReg.t4 AbiReg.t3 3#6]) ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4]) + 1))
      , regs := st11.regs
      , mem := writeWord64 st11.mem (st11.getReg AbiReg.t1) (st11.getReg AbiReg.a0) }
    have hpc12' : st12.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre7 + lkm.totalSize codeTail)) := by
      have htwct : lkm.totalSize ctail = 3 := by
        simp only [ctail, Asm.slli, Asm.add, Asm.sd, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
      have htwCT : lkm.totalSize codeTail = lkm.totalSize cbr + lkm.totalSize cl3 + 3 := by
        rw [hcEq]; simp only [lkm.totalSize_append, htwct]
      have hpcEq : lkm.totalSize ((pre9 ++ [Asm.slli AbiReg.t4 AbiReg.t3 3#6]) ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4]) + 1 =
          lkm.totalSize pre7 + lkm.totalSize codeTail := by
        rw [lkm.totalSize_append, htwB, lkm.totalSize_append, htwA, htwCT, htwPre9, htwPre8]; omega
      dsimp only [st12]; rw [hpcEq]
    have ha0_11 : st11.getReg AbiReg.a0 = ve.toBitVec :=
      (hoth10 _ (by decide)).trans ((hoth9 _ (by decide)).trans ((hoth8 _ (by decide) (by decide)).trans ((hoth7 _ (by decide)).trans ha0Val)))
    have hstMem11 : st11.mem = st7.mem := by rw [hmem10, hmem9, hmem8, hmem7Br]
    have hcapVi : vi.toNat < L.cap64 (_root_.L.tierA a u) := Nat.lt_of_lt_of_le hbound hcap64
    have hrunAll := run_trans (run_trans (run_trans (run_trans hrun7 hrun8) hrun9) hrun10) hrun11
    refine ⟨_, st12, hrunAll, hpc12', ?_, ?_, ?_, ?_⟩
    · exact hpres7.trans (hpres8.trans (hpres9.trans (hpres10.trans (preservedRegs_of_regs rfl))))
    · dsimp only [st12]; rw [ht1Addr, ha0_11, hstMem11]; exact ProgMemRel.set64 hm7 (_root_.L.tierA a u) hta.1 vi ve hbound
    · dsimp only [st12]; rw [ht1Addr, ha0_11, hstMem11]
      exact progFrameOk_write64_arr64 L hlim htop (_root_.L.tierA a u) hta.1 vi.toNat hcapVi st7.mem ve.toBitVec hf7
    · dsimp only [st12]; rw [ht1Addr, ha0_11, hstMem11]
      exact progMemOutside_write64_arr64 L (_root_.L.tierA a u) hta.1 vi.toNat hcapVi st7.mem ve.toBitVec
  · simp only [hbound, ↓reduceIte]
    have hbrT : evalBranch .bgeu (st7.getReg AbiReg.t3) (st7.getReg AbiReg.t2) = true := by
      rw [hcondEq, decide_eq_true_iff]; omega
    have hpcT : st8.pc = BitVec.ofNat 64 (4 * env.errTarget) := by rw [hpcBr, hbrT]; rfl
    exact ⟨kBr, st8, hrun7, hpcT, hpres7⟩

theorem prog_st64t_exec_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (a : _root_.L.ArrId) (u vi ve : _root_.L.Word) (ha : env.tab.tieredOkB a = true)
    (pre3 codeRest post : List AsmItem)
    (hcRest : codeRest = loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff nl) ++
      loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t1 (slotOff (nl + 1)) ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t4 (env.tab.len64 (_root_.L.TieredArray.t0 a)) ++
      [Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t4 (env.tab.base64 (_root_.L.TieredArray.t0 a)) ++
      [Asm.slli AbiReg.t4 AbiReg.t3 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4, Asm.sd AbiReg.t1 AbiReg.a0])
    (hlink3 : lkm.linkSpec (pre3 ++ codeRest ++ post) = .ok (env.code, env.labels))
    (st3 : State) (hpc3 : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre3))
    (hgp3 : st3.getReg AbiReg.gp = L.T) (hsp3 : st3.getReg AbiReg.sp = sp)
    (ha0 : st3.getReg AbiReg.a0 = ve.toBitVec)
    (hslot0 : readWord64 st3.mem (sp + BitVec.ofInt 64 (slotOff nl)) = u.toBitVec)
    (hslot1 : readWord64 st3.mem (sp + BitVec.ofInt 64 (slotOff (nl + 1))) = vi.toBitVec)
    (hm3 : ProgMemRel env.tab L st3.mem lm) (hf3 : ProgFrameOk L sp st3.mem nl loc) :
    if vi.toNat < (lm.arr64 (_root_.L.tierA a u)).size then
      ∃ k r',
        RV64.run env.rom k st3 = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre3 + lkm.totalSize codeRest)) ∧
        PreservedRegs st3 r' ∧
        ProgMemRel env.tab L r'.mem (lm.set64 (_root_.L.tierA a u) vi ve) ∧
        ProgFrameOk L sp r'.mem nl loc ∧
        ProgMemOutside (FnWriteMask L sp nl nt) st3.mem r'.mem
    else
      ∃ k r',
        RV64.run env.rom k st3 = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st3 r' := by
  let cl0 := loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff nl)
  let cl1 := loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t1 (slotOff (nl + 1))
  let ctp := [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0]
  let cl2 := loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t4 (env.tab.len64 (.t0 a))
  let codeTail := [Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
    loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t4 (env.tab.base64 (_root_.L.TieredArray.t0 a)) ++
    [Asm.slli AbiReg.t4 AbiReg.t3 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4, Asm.sd AbiReg.t1 AbiReg.a0]
  have hcEq : codeRest = cl0 ++ cl1 ++ ctp ++ cl2 ++ codeTail := by
    rw [hcRest]; simp [cl0, cl1, ctp, cl2, codeTail, List.append_assoc]
  rw [hcEq] at hlink3
  have hlink3' : lkm.linkSpec (pre3 ++ cl0 ++ (cl1 ++ ctp ++ cl2 ++ codeTail ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink3
  have halX0 : isAligned (st3.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff nl)) 8 = true := by
    rw [hsp3]; exact isAligned8_add_int_mul8 sp hal (1 + nl)
  obtain ⟨st4, hrun3, hoth3, ht0_4, hmem3, hpc4⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre3 _ AbiReg.t0 AbiReg.sp AbiReg.t1
      (by decide) (by decide) (by decide) (slotOff nl) hlink3'
      (linkResolved_sub_pc64 env pre3 cl0 _ hlink3') st3 hpc3 halX0
  have hpres3 : PreservedRegs st3 st4 :=
    ⟨hoth3 _ (by decide) (by decide), hoth3 _ (by decide) (by decide), hoth3 _ (by decide) (by decide), hoth3 _ (by decide) (by decide)⟩
  let pre4 := pre3 ++ cl0
  have htwPre4 : lkm.totalSize pre4 = lkm.totalSize pre3 + lkm.totalSize cl0 := lkm.totalSize_append pre3 cl0
  have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre4) := by rw [hpc4, htwPre4]
  have hlink4 : lkm.linkSpec (pre4 ++ cl1 ++ (ctp ++ cl2 ++ codeTail ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre4, List.append_assoc] using hlink3'
  have halX1 : isAligned (st4.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff (nl + 1))) 8 = true := by
    rw [hpres3.sp.trans hsp3]; exact isAligned8_add_int_mul8 sp hal (1 + (nl + 1))
  obtain ⟨st5, hrun4, hoth4, ht3_5, hmem4, hpc5⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre4 _ AbiReg.t3 AbiReg.sp AbiReg.t1
      (by decide) (by decide) (by decide) (slotOff (nl + 1)) hlink4
      (linkResolved_sub_pc64 env pre4 cl1 _ hlink4) st4 hpc4' halX1
  have hpres4 : PreservedRegs st4 st5 :=
    ⟨hoth4 _ (by decide) (by decide), hoth4 _ (by decide) (by decide), hoth4 _ (by decide) (by decide), hoth4 _ (by decide) (by decide)⟩
  let pre5 := pre4 ++ cl1
  have htwPre5 : lkm.totalSize pre5 = lkm.totalSize pre4 + lkm.totalSize cl1 := lkm.totalSize_append pre4 cl1
  have hpc5' : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre5) := by rw [hpc5, htwPre5]
  have hlink5 : lkm.linkSpec (pre5 ++ ctp ++ (cl2 ++ codeTail ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre5, List.append_assoc] using hlink4
  have hgp5 : st5.getReg AbiReg.gp = L.T := hpres4.gp.trans (hpres3.gp.trans hgp3)
  have ht0_5 : st5.getReg AbiReg.t0 = u.toBitVec := by
    rw [hoth4 _ (by decide) (by decide), ht0_4, hsp3, hslot0]
  obtain ⟨st6, hrun5, hpc6, ht1_6, hoth5, hmem5, hpres5⟩ :=
    prog_tierPtr_sim env pre5 _ L.T u hlink5 st5 hpc5' hgp5 ht0_5
  have htwTp : lkm.totalSize ctp = 3 := by
    simp only [ctp, Asm.andi, Asm.slli, Asm.add, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
  let pre6 := pre5 ++ ctp
  have htwPre6 : lkm.totalSize pre6 = lkm.totalSize pre5 + 3 := by rw [lkm.totalSize_append, htwTp]
  have hpc6' : st6.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre6) := by rw [hpc6, htwPre6]
  have hlink6 : lkm.linkSpec (pre6 ++ cl2 ++ (codeTail ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre6, List.append_assoc] using hlink5
  have hta := tieredOk_len64_addr_T L.T a u ha
  rcases hm3.2.1 (_root_.L.tierA a u) hta.1 with ⟨hcap64, hlt64, hlen64, _, _⟩
  have ht1LenAddr : st6.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.len64 (.t0 a)) =
      L.T + BitVec.ofInt 64 (env.tab.len64 (_root_.L.tierA a u)) := by rw [ht1_6, hta.2.1]
  have halLen : isAligned (st6.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.len64 (.t0 a))) 8 = true := by
    rw [ht1LenAddr, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
  obtain ⟨st7, hrun6, hoth6, ht2_7, hmem6, hpc7⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre6 _ AbiReg.t2 AbiReg.t1 AbiReg.t4
      (by decide) (by decide) (by decide) (env.tab.len64 (.t0 a)) hlink6
      (linkResolved_sub_pc64 env pre6 cl2 _ hlink6) st6 hpc6' halLen
  have hpres6 : PreservedRegs st6 st7 :=
    ⟨hoth6 _ (by decide) (by decide), hoth6 _ (by decide) (by decide), hoth6 _ (by decide) (by decide), hoth6 _ (by decide) (by decide)⟩
  let pre7 := pre6 ++ cl2
  have htwPre7 : lkm.totalSize pre7 = lkm.totalSize pre6 + lkm.totalSize cl2 := lkm.totalSize_append pre6 cl2
  have hpc7' : st7.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre7) := by rw [hpc7, htwPre7]
  have hlink7 : lkm.linkSpec (pre7 ++ codeTail ++ post) =
      .ok (env.code, env.labels) := by simpa [pre7, List.append_assoc] using hlink6
  have ht3Val : st7.getReg AbiReg.t3 = vi.toBitVec := by
    rw [hoth6 _ (by decide) (by decide), hoth5 _ (by decide) (by decide), ht3_5, hmem3, hpres3.sp.trans hsp3, hslot1]
  have ht2Val : st7.getReg AbiReg.t2 = BitVec.ofNat 64 (lm.arr64 (_root_.L.tierA a u)).size := by
    rw [ht2_7, hmem5, hmem4, hmem3, ht1LenAddr, hlen64]
  have ha0Val : st7.getReg AbiReg.a0 = ve.toBitVec :=
    (hoth6 _ (by decide) (by decide)).trans
      ((hoth5 _ (by decide) (by decide)).trans ((hoth4 _ (by decide) (by decide)).trans ((hoth3 _ (by decide) (by decide)).trans ha0)))
  have ht1BaseAddr : st7.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.base64 (.t0 a)) =
      L.T + BitVec.ofInt 64 (env.tab.base64 (_root_.L.tierA a u)) := by
    rw [hoth6 _ (by decide) (by decide), ht1_6, hta.2.2]
  have hstMem7 : st7.mem = st3.mem := by rw [hmem6, hmem5, hmem4, hmem3]
  have htail := prog_st64t_tail_sim env L lm loc hlim htop a u vi ve ha pre7 codeTail post rfl hlink7 st7
    hpc7' ht3Val ht2Val ha0Val ht1BaseAddr (hstMem7 ▸ hm3) (hstMem7 ▸ hf3)
  have hrun0_6 := run_trans (run_trans (run_trans hrun3 hrun4) hrun5) hrun6
  have hpres0_6 : PreservedRegs st3 st7 := hpres3.trans (hpres4.trans (hpres5.trans hpres6))
  by_cases hbound : vi.toNat < (lm.arr64 (_root_.L.tierA a u)).size
  · simp only [hbound, ↓reduceIte] at htail ⊢
    obtain ⟨k, r', hrunT, hpcT, hpresT, hmT, hfT, hpmT⟩ := htail
    have hpcEq : lkm.totalSize pre7 + lkm.totalSize codeTail = lkm.totalSize pre3 + lkm.totalSize codeRest := by
      rw [htwPre7, htwPre6, htwPre5, htwPre4, hcEq,
          lkm.totalSize_append (((cl0 ++ cl1) ++ ctp) ++ cl2) codeTail,
          lkm.totalSize_append ((cl0 ++ cl1) ++ ctp) cl2,
          lkm.totalSize_append (cl0 ++ cl1) ctp,
          lkm.totalSize_append cl0 cl1, htwTp]; omega
    rw [hpcEq] at hpcT
    exact ⟨_, r', run_trans hrun0_6 hrunT, hpcT, hpres0_6.trans hpresT, hmT, hfT, hstMem7 ▸ hpmT⟩
  · simp only [hbound, ↓reduceIte] at htail ⊢
    obtain ⟨k, r', hrunT, hpcT, hpresT⟩ := htail
    exact ⟨_, r', run_trans hrun0_6 hrunT, hpcT, hpres0_6.trans hpresT⟩

theorem prog_st64t_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (a : _root_.L.ArrId) (t i e : _root_.L.Expr)
    (ha : env.tab.tieredOkB a = true)
    (htOk : exprOkB env.tab nl t = true) (hiOk : exprOkB env.tab nl i = true)
    (heOk : exprOkB env.tab nl e = true)
    (hnt : max (maxTempsExpr t) (max (1 + maxTempsExpr i) (2 + maxTempsExpr e)) ≤ nt)
    (pre post : List AsmItem)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOk L sp st.mem nl loc)
    (hlink : lkm.linkSpec (pre ++ (compileTierStoreTriple env.tab nl t i e ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t4 (env.tab.len64 (_root_.L.TieredArray.t0 a)) ++
      [Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t4 (env.tab.base64 (_root_.L.TieredArray.t0 a)) ++
      [Asm.slli AbiReg.t4 AbiReg.t3 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4, Asm.sd AbiReg.t1 AbiReg.a0]) ++ post) =
      .ok (env.code, env.labels)) :
    let codeS := compileTierStoreTriple env.tab nl t i e ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t4 (env.tab.len64 (_root_.L.TieredArray.t0 a)) ++
      [Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t4 (env.tab.base64 (_root_.L.TieredArray.t0 a)) ++
      [Asm.slli AbiReg.t4 AbiReg.t3 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4, Asm.sd AbiReg.t1 AbiReg.a0]
    match (do let u ← _root_.L.evalE t; let j ← _root_.L.evalE i; let v ← _root_.L.evalE e; _root_.L.st64 (_root_.L.tierA a u) j v)
        { mem := lm, loc := loc } with
    | .ok (_, st') =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize codeS)) ∧
        PreservedRegs st r' ∧
        ProgMemRel env.tab L r'.mem st'.mem ∧
        ProgFrameOk L sp r'.mem nl st'.loc ∧
        ProgMemOutside (FnWriteMask L sp nl nt) st.mem r'.mem
    | .error _ =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st r' := by
  let ct := compileTierStoreTriple env.tab nl t i e
  let ctp := [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0]
  let cl2 := loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t4 (env.tab.len64 (.t0 a))
  let codeTail := [Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
    loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t4 (env.tab.base64 (_root_.L.TieredArray.t0 a)) ++
    [Asm.slli AbiReg.t4 AbiReg.t3 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4, Asm.sd AbiReg.t1 AbiReg.a0]
  have hlinkP : lkm.linkSpec (pre ++ ct ++ (ctp ++ cl2 ++ codeTail ++ post)) = .ok (env.code, env.labels) := by
    simpa only [ct, ctp, cl2, codeTail, List.append_assoc] using hlink
  have rp := prog_compileTierStoreTriple_sim env L lm loc hal hlim htop t i e htOk hiOk heOk hnt
    pre (ctp ++ cl2 ++ codeTail ++ post) st hpc hgp hsp hm hf hlinkP
  rcases _root_.L.evalE_pure t { mem := lm, loc := loc } with ⟨u, htE⟩ | htE
  · rcases _root_.L.evalE_pure i { mem := lm, loc := loc } with ⟨vi, hiE⟩ | hiE
    · rcases _root_.L.evalE_pure e { mem := lm, loc := loc } with ⟨ve, heE⟩ | heE
      · rw [htE, hiE, heE] at rp
        obtain ⟨kp, st5, hrunP, hpc5, ht0_5, ht3_5, ha0_5, hpresP, hm3, hf3, hpmP⟩ := rp
        let pre5 := pre ++ ct
        have htwPre5 : lkm.totalSize pre5 = lkm.totalSize pre + lkm.totalSize ct := lkm.totalSize_append _ _
        have hpc5' : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre5) := by rw [hpc5, htwPre5]
        have hlink5 : lkm.linkSpec (pre5 ++ ctp ++ (cl2 ++ codeTail ++ post)) = .ok (env.code, env.labels) := by
          simpa only [pre5, List.append_assoc] using hlinkP
        obtain ⟨st6, hrun5, hpc6, ht1_6, hoth5, hmem5, hpres5⟩ :=
          prog_tierPtr_sim env pre5 _ L.T u hlink5 st5 hpc5' (hpresP.gp.trans hgp) ht0_5
        have htwTp : lkm.totalSize ctp = 3 := by
          simp only [ctp, Asm.andi, Asm.slli, Asm.add, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
        let pre6 := pre5 ++ ctp
        have htwPre6 : lkm.totalSize pre6 = lkm.totalSize pre5 + 3 := by rw [lkm.totalSize_append, htwTp]
        have hpc6' : st6.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre6) := by rw [hpc6, htwPre6]
        have hlink6 : lkm.linkSpec (pre6 ++ cl2 ++ (codeTail ++ post)) = .ok (env.code, env.labels) := by
          simpa only [pre6, List.append_assoc] using hlink5
        have hta := tieredOk_len64_addr_T L.T a u ha
        rcases hm3.2.1 (_root_.L.tierA a u) hta.1 with ⟨_, _, hlen64, _, _⟩
        have ht1LenAddr : st6.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.len64 (.t0 a)) =
            L.T + BitVec.ofInt 64 (env.tab.len64 (_root_.L.tierA a u)) := by rw [ht1_6, hta.2.1]
        have halLen : isAligned (st6.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.len64 (.t0 a))) 8 = true := by
          rw [ht1LenAddr, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
        obtain ⟨st7, hrun6, hoth6, ht2_7, hmem6, hpc7⟩ :=
          loadMemOff_ld_correct_lm lkm env.hrom pre6 _ AbiReg.t2 AbiReg.t1 AbiReg.t4
            (by decide) (by decide) (by decide) (env.tab.len64 (.t0 a)) hlink6
            (linkResolved_sub_pc64 env pre6 cl2 _ hlink6) st6 hpc6' halLen
        have hpres6 : PreservedRegs st6 st7 :=
          ⟨hoth6 _ (by decide) (by decide), hoth6 _ (by decide) (by decide), hoth6 _ (by decide) (by decide), hoth6 _ (by decide) (by decide)⟩
        let pre7 := pre6 ++ cl2
        have htwPre7 : lkm.totalSize pre7 = lkm.totalSize pre6 + lkm.totalSize cl2 := lkm.totalSize_append _ _
        have hpc7' : st7.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre7) := by rw [hpc7, htwPre7]
        have hlink7 : lkm.linkSpec (pre7 ++ codeTail ++ post) = .ok (env.code, env.labels) := by
          simpa only [pre7, List.append_assoc] using hlink6
        have ht3Val : st7.getReg AbiReg.t3 = vi.toBitVec :=
          (hoth6 _ (by decide) (by decide)).trans ((hoth5 _ (by decide) (by decide)).trans ht3_5)
        have ht2Val : st7.getReg AbiReg.t2 = BitVec.ofNat 64 (lm.arr64 (_root_.L.tierA a u)).size := by
          rw [ht2_7, hmem5, ht1LenAddr, hlen64]
        have ha0Val : st7.getReg AbiReg.a0 = ve.toBitVec :=
          (hoth6 _ (by decide) (by decide)).trans ((hoth5 _ (by decide) (by decide)).trans ha0_5)
        have ht1BaseAddr : st7.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.base64 (.t0 a)) =
            L.T + BitVec.ofInt 64 (env.tab.base64 (_root_.L.tierA a u)) := by
          rw [hoth6 _ (by decide) (by decide), ht1_6, hta.2.2]
        have hstMem7 : st7.mem = st5.mem := by rw [hmem6, hmem5]
        have htail := prog_st64t_tail_sim env L lm loc hlim htop a u vi ve ha pre7 codeTail post rfl hlink7 st7
          hpc7' ht3Val ht2Val ha0Val ht1BaseAddr (hstMem7 ▸ hm3) (hstMem7 ▸ hf3)
        by_cases hbound : vi.toNat < (lm.arr64 (_root_.L.tierA a u)).size
        · simp only [hbound, ↓reduceIte] at htail
          obtain ⟨k, r', hrunT, hpcT, hpresT, hmT, hfT, hpmT⟩ := htail
          have hmini : (do let u ← _root_.L.evalE t; let j ← _root_.L.evalE i; let v ← _root_.L.evalE e; _root_.L.st64 (_root_.L.tierA a u) j v)
              { mem := lm, loc := loc } = .ok ((), { mem := lm.set64 (_root_.L.tierA a u) vi ve, loc := loc }) := by
            simp only [Bind.bind, StateT.bind, Except.bind, htE, hiE, heE, _root_.L.st64, get, getThe,
              MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set,
              Pure.pure, Except.pure, hbound, ↓reduceIte]
          rw [hmini]
          have hpcEq : lkm.totalSize pre7 + lkm.totalSize codeTail =
              lkm.totalSize pre + lkm.totalSize (ct ++ ctp ++ cl2 ++ [Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
                loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t4 (env.tab.base64 (.t0 a)) ++
                [Asm.slli AbiReg.t4 AbiReg.t3 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4, Asm.sd AbiReg.t1 AbiReg.a0]) := by
            rw [htwPre7, htwPre6, htwPre5]; dsimp only [codeTail]; simp only [lkm.totalSize_append, htwTp]; omega
          exact ⟨_, r', run_trans (run_trans (run_trans hrunP hrun5) hrun6) hrunT, by rw [hpcT, hpcEq],
            hpresP.trans (hpres5.trans (hpres6.trans hpresT)), hmT, hfT, hpmP.trans (hstMem7 ▸ hpmT)⟩
        · simp only [hbound, ↓reduceIte] at htail
          obtain ⟨k, r', hrunT, hpcT, hpresT⟩ := htail
          have hmini : (do let u ← _root_.L.evalE t; let j ← _root_.L.evalE i; let v ← _root_.L.evalE e; _root_.L.st64 (_root_.L.tierA a u) j v)
              { mem := lm, loc := loc } = .error .oob := by
            simp only [Bind.bind, StateT.bind, Except.bind, htE, hiE, heE, _root_.L.st64, get, getThe,
              MonadStateOf.get, StateT.get, throw, throwThe, MonadExceptOf.throw,
              Pure.pure, Except.pure, hbound, ↓reduceIte]; rfl
          rw [hmini]
          exact ⟨_, r', run_trans (run_trans (run_trans hrunP hrun5) hrun6) hrunT, hpcT,
            hpresP.trans (hpres5.trans (hpres6.trans hpresT))⟩
      · simp only [Bind.bind, StateT.bind, Except.bind, htE, hiE, heE] at rp ⊢; exact rp
    · simp only [Bind.bind, StateT.bind, Except.bind, htE, hiE] at rp ⊢; exact rp
  · simp only [Bind.bind, StateT.bind, Except.bind, htE] at rp ⊢; exact rp

theorem prog_st32t_tail_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hlim : L.stackLimit.toNat ≤ sp.toNat) (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (a : _root_.L.ArrId) (u vi ve : _root_.L.Word) (ha : TierAddrOk env.tab a u)
    (pre7 codeTail post : List AsmItem)
    (hcTail : codeTail = [Asm.srli AbiReg.t4 AbiReg.t3 1#6, Asm.bgeu AbiReg.t4 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t4 (env.tab.base64 (_root_.L.TieredArray.t0 a)) ++
      [Asm.slli AbiReg.t4 AbiReg.t3 2#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4, Asm.sw AbiReg.t1 AbiReg.a0])
    (hlink7 : lkm.linkSpec (pre7 ++ codeTail ++ post) = .ok (env.code, env.labels))
    (st7 : State) (hpc7 : st7.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre7))
    (ht3Val : st7.getReg AbiReg.t3 = vi.toBitVec)
    (ht2Val : st7.getReg AbiReg.t2 = BitVec.ofNat 64 (lm.arr64 (_root_.L.tierA a u)).size)
    (ha0Val : st7.getReg AbiReg.a0 = ve.toBitVec)
    (ht1BaseAddr : st7.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.base64 (.t0 a)) =
      L.T + BitVec.ofInt 64 (env.tab.base64 (_root_.L.tierA a u)))
    (hm7 : ProgMemRel env.tab L st7.mem lm) (hf7 : ProgFrameOk L sp st7.mem nl loc) :
    if (vi / 2).toNat < (lm.arr64 (_root_.L.tierA a u)).size then
      ∃ k r',
        RV64.run env.rom k st7 = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre7 + lkm.totalSize codeTail)) ∧
        PreservedRegs st7 r' ∧
        ProgMemRel env.tab L r'.mem (lm.set32 (_root_.L.tierA a u) vi ve) ∧
        ProgFrameOk L sp r'.mem nl loc ∧
        ProgMemOutside (FnWriteMask L sp nl nt) st7.mem r'.mem
    else
      ∃ k r',
        RV64.run env.rom k st7 = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st7 r' := by
  let csrl := [Asm.srli AbiReg.t4 AbiReg.t3 1#6]
  let cbr := [Asm.bgeu AbiReg.t4 AbiReg.t2 errLabel]
  let cl3 := loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t4 (env.tab.base64 (.t0 a))
  let ctail := [Asm.slli AbiReg.t4 AbiReg.t3 2#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4, Asm.sw AbiReg.t1 AbiReg.a0]
  have hcEq : codeTail = csrl ++ cbr ++ cl3 ++ ctail := by
    rw [hcTail]; rfl
  rw [hcEq] at hlink7
  have hlink7' : lkm.linkSpec (pre7 ++ csrl ++ (cbr ++ cl3 ++ ctail ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink7
  have htwSrl : lkm.totalSize csrl = 1 := by simp only [csrl, Asm.srli, lkm.totalSize_instr]
  let st8 := stepReg st7 AbiReg.t4
    (evalShiftImm .srli (st7.getReg AbiReg.t3) 1#6) (BitVec.ofNat 64 (4 * (lkm.totalSize pre7 + 1)))
  obtain ⟨hrun7, hpc8, ht4_8, hoth7, hmem7, hpres7⟩ :=
    run_shImm_step env pre7 _ .srli AbiReg.t4 AbiReg.t3 1#6 nonPreserved_t4 hlink7' st7 hpc7
  let pre8 := pre7 ++ csrl
  have htwPre8 : lkm.totalSize pre8 = lkm.totalSize pre7 + 1 := by rw [lkm.totalSize_append, htwSrl]
  have hpc8' : st8.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre8) := by rw [hpc8, htwPre8]
  have hlink8 : lkm.linkSpec (pre8 ++ cbr ++ (cl3 ++ ctail ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre8, List.append_assoc] using hlink7'
  have hbr := run_br_step env pre8 _ .bgeu AbiReg.t4 AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide) hlink8 st8 hpc8'
  have ht3_8 : st8.getReg AbiReg.t3 = vi.toBitVec := (hoth7 _ (by decide)).trans ht3Val
  have ht4Val : st8.getReg AbiReg.t4 = BitVec.ofNat 64 (vi / 2).toNat := by
    rw [ht4_8, ht3Val]; exact srli1_eq_div2 vi
  have ht2_8 : st8.getReg AbiReg.t2 = BitVec.ofNat 64 (lm.arr64 (_root_.L.tierA a u)).size :=
    (hoth7 _ (by decide)).trans ht2Val
  have ha0_8 : st8.getReg AbiReg.a0 = ve.toBitVec := (hoth7 _ (by decide)).trans ha0Val
  have hta := tierAddrOk_len64_addr_T L.T a u ha
  rcases hm7.2.1 (_root_.L.tierA a u) hta.1 with ⟨hcap64, hlt64, _, hbase64, _⟩
  have hcondEq : evalBranch .bgeu (st8.getReg AbiReg.t4) (st8.getReg AbiReg.t2) =
      decide ((lm.arr64 (_root_.L.tierA a u)).size ≤ (vi / 2).toNat) := by
    rw [ht4Val, ht2_8]; exact evalBranch_bgeu_nat (vi / 2).toBitVec.isLt (by omega)
  obtain ⟨kBr, st9, _, hrun8, hpcBr, hoth8Br, hpres8Br, hmem8Br⟩ := hbr
  by_cases hbound : (vi / 2).toNat < (lm.arr64 (_root_.L.tierA a u)).size
  · simp only [hbound, ↓reduceIte]
    have hbrF : evalBranch .bgeu (st8.getReg AbiReg.t4) (st8.getReg AbiReg.t2) = false := by
      rw [hcondEq, decide_eq_false_iff_not]; omega
    let pre9 := pre8 ++ cbr
    have htwPre9 : lkm.totalSize pre9 = lkm.totalSize pre8 + lkm.totalSize cbr := lkm.totalSize_append pre8 cbr
    have hpc9' : st9.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre9) := by
      rw [hpcBr, hbrF]; simp only [Bool.false_eq_true, ↓reduceIte, htwPre9, cbr, Asm.bgeu, Asm.br, lkm.totalSize_singleton]
    have hlink9 : lkm.linkSpec (pre9 ++ cl3 ++ (ctail ++ post)) =
        .ok (env.code, env.labels) := by simpa [pre9, List.append_assoc] using hlink8
    have ht1BaseAddr9 : st9.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.base64 (.t0 a)) =
        L.T + BitVec.ofInt 64 (env.tab.base64 (_root_.L.tierA a u)) := by
      rw [hoth8Br _ (by decide)]; change st8.getReg AbiReg.t1 + _ = _; rw [hoth7 _ (by decide)]; exact ht1BaseAddr
    have halBase : isAligned (st9.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.base64 (.t0 a))) 8 = true := by
      rw [ht1BaseAddr9, Tab.base64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
    obtain ⟨st10, hrun9, hoth9, ht1_10, hmem9, hpc10⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom pre9 _ AbiReg.t1 AbiReg.t1 AbiReg.t4
        (by decide) (by decide) (by decide) (env.tab.base64 (.t0 a)) hlink9
        (linkResolved_sub_pc64 env pre9 cl3 _ hlink9) st9 hpc9' halBase
    have hpres9 : PreservedRegs st9 st10 :=
      ⟨hoth9 _ (by decide) (by decide), hoth9 _ (by decide) (by decide), hoth9 _ (by decide) (by decide), hoth9 _ (by decide) (by decide)⟩
    let pre10 := pre9 ++ cl3
    have htwPre10 : lkm.totalSize pre10 = lkm.totalSize pre9 + lkm.totalSize cl3 := lkm.totalSize_append pre9 cl3
    have hpc10' : st10.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre10) := by rw [hpc10, htwPre10]
    have hlink10 : lkm.linkSpec (pre10 ++ ctail ++ post) =
        .ok (env.code, env.labels) := by simpa [pre10, List.append_assoc] using hlink9
    have ⟨hlA, hlBC⟩ := linkResolved_mid_split lkm pre10 [Asm.slli AbiReg.t4 AbiReg.t3 2#6]
      [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4, Asm.sw AbiReg.t1 AbiReg.a0] post hlink10
    have ⟨hlB, hlC⟩ := linkResolved_mid_split lkm (pre10 ++ [Asm.slli AbiReg.t4 AbiReg.t3 2#6])
      [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4] [Asm.sw AbiReg.t1 AbiReg.a0] post hlBC
    have htwA : lkm.totalSize [Asm.slli AbiReg.t4 AbiReg.t3 2#6] = 1 := by simp only [Asm.slli, lkm.totalSize_instr]
    have htwB : lkm.totalSize [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4] = 1 := by simp only [Asm.add, lkm.totalSize_instr]
    let st11 := stepReg st10 AbiReg.t4
      (evalShiftImm .slli (st10.getReg AbiReg.t3) 2#6) (BitVec.ofNat 64 (4 * (lkm.totalSize pre10 + 1)))
    obtain ⟨hrun10, hpc11, ht4_11, hoth10, hmem10, hpres10⟩ :=
      run_shImm_step env pre10 _ .slli AbiReg.t4 AbiReg.t3 2#6 nonPreserved_t4 hlA st10 hpc10'
    let st12 := stepReg st11 AbiReg.t1
      (evalAlu .add (st11.getReg AbiReg.t1) (st11.getReg AbiReg.t4))
      (BitVec.ofNat 64 (4 * (lkm.totalSize (pre10 ++ [Asm.slli AbiReg.t4 AbiReg.t3 2#6]) + 1)))
    obtain ⟨hrun11, hpc12, ht1_12, hoth11, hmem11, hpres11⟩ :=
      run_alu_step env (pre10 ++ [Asm.slli AbiReg.t4 AbiReg.t3 2#6]) _ .add AbiReg.t1 AbiReg.t1 AbiReg.t4
        nonPreserved_t1 hlB st11 (by rw [lkm.totalSize_append, htwA]; exact hpc11)
    have hdiv2Nat : (vi / 2).toNat = vi.toNat / 2 := by simp [UInt64.toNat_div]
    have h4vi : 4 * vi.toNat < 2 ^ 64 := by
      have : vi.toNat / 2 < (lm.arr64 (_root_.L.tierA a u)).size := hdiv2Nat ▸ hbound
      omega
    have ht1Addr : st12.getReg AbiReg.t1 = L.base64 (_root_.L.tierA a u) + BitVec.ofNat 64 (4 * vi.toNat) := by
      rw [ht1_12, evalAlu, hoth10 _ (by decide), ht1_10, hmem8Br, hmem7]
      rw [ht1BaseAddr9, hbase64, ht4_11, hoth9 _ (by decide) (by decide)]
      change L.base64 (_root_.L.tierA a u) + evalShiftImm .slli (st9.getReg AbiReg.t3) 2#6 = _
      rw [hoth8Br _ (by decide), ht3_8, shl2_ofNat_eq vi h4vi]
    have halDst : isAligned (st12.getReg AbiReg.t1) 4 = true := by
      rw [ht1Addr]; exact isAligned4_of_base64_add4 L (_root_.L.tierA a u) vi
    have hrun12 := step_sw_zero env
      ((pre10 ++ [Asm.slli AbiReg.t4 AbiReg.t3 2#6]) ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4]) post
      AbiReg.t1 AbiReg.a0 hlC st12 (by rw [lkm.totalSize_append, htwB]; exact hpc12) halDst
    let st13 : State :=
      { pc := BitVec.ofNat 64 (4 * (lkm.totalSize ((pre10 ++ [Asm.slli AbiReg.t4 AbiReg.t3 2#6]) ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4]) + 1))
      , regs := st12.regs
      , mem := storeBytes st12.mem (st12.getReg AbiReg.t1) 4 (BitVec.extractLsb' 0 32 (st12.getReg AbiReg.a0)) }
    have hpc13' : st13.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre7 + lkm.totalSize codeTail)) := by
      have htwct : lkm.totalSize ctail = 3 := by
        simp only [ctail, Asm.slli, Asm.add, Asm.sw, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
      have htwCT : lkm.totalSize codeTail = 1 + lkm.totalSize cbr + lkm.totalSize cl3 + 3 := by
        rw [hcEq]; simp only [lkm.totalSize_append, htwSrl, htwct]
      have hpcEq : lkm.totalSize ((pre10 ++ [Asm.slli AbiReg.t4 AbiReg.t3 2#6]) ++ [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4]) + 1 =
          lkm.totalSize pre7 + lkm.totalSize codeTail := by
        rw [lkm.totalSize_append, htwB, lkm.totalSize_append, htwA, htwCT, htwPre10, htwPre9, htwPre8]; omega
      dsimp only [st13]; rw [hpcEq]
    have ha0_12 : st12.getReg AbiReg.a0 = ve.toBitVec :=
      (hoth11 _ (by decide)).trans ((hoth10 _ (by decide)).trans ((hoth9 _ (by decide) (by decide)).trans ((hoth8Br _ (by decide)).trans ha0_8)))
    have hstMem12 : st12.mem = st7.mem := by rw [hmem11, hmem10, hmem9, hmem8Br, hmem7]
    have hcapVi : vi.toNat / 2 < L.cap64 (_root_.L.tierA a u) :=
      Nat.lt_of_lt_of_le (hdiv2Nat ▸ hbound) hcap64
    have hrunAll := run_trans (run_trans (run_trans (run_trans (run_trans hrun7 hrun8) hrun9) hrun10) hrun11) hrun12
    refine ⟨_, st13, hrunAll, hpc13', ?_, ?_, ?_, ?_⟩
    · exact hpres7.trans (hpres8Br.trans (hpres9.trans (hpres10.trans (hpres11.trans (preservedRegs_of_regs rfl)))))
    · dsimp only [st13]; rw [ht1Addr, ha0_12, hstMem12]; exact ProgMemRel.set32 hm7 (_root_.L.tierA a u) hta.1 vi ve hbound
    · dsimp only [st13]; rw [ht1Addr, ha0_12, hstMem12]
      exact progFrameOk_store4_arr32 L hlim htop (_root_.L.tierA a u) hta.1 vi.toNat hcapVi st7.mem _ hf7
    · dsimp only [st13]; rw [ht1Addr, ha0_12, hstMem12]
      exact progMemOutside_store4_arr32 L (_root_.L.tierA a u) hta.1 vi.toNat hcapVi st7.mem _
  · simp only [hbound, ↓reduceIte]
    have hbrT : evalBranch .bgeu (st8.getReg AbiReg.t4) (st8.getReg AbiReg.t2) = true := by
      rw [hcondEq, decide_eq_true_iff]; omega
    have hpcT : st9.pc = BitVec.ofNat 64 (4 * env.errTarget) := by rw [hpcBr, hbrT]; rfl
    exact ⟨_, st9, run_trans hrun7 hrun8, hpcT, hpres7.trans hpres8Br⟩

theorem prog_st32t_exec_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (a : _root_.L.ArrId) (u vi ve : _root_.L.Word) (ha : TierAddrOk env.tab a u)
    (pre3 codeRest post : List AsmItem)
    (hcRest : codeRest = loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff nl) ++
      loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t1 (slotOff (nl + 1)) ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t4 (env.tab.len64 (_root_.L.TieredArray.t0 a)) ++
      [Asm.srli AbiReg.t4 AbiReg.t3 1#6, Asm.bgeu AbiReg.t4 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t4 (env.tab.base64 (_root_.L.TieredArray.t0 a)) ++
      [Asm.slli AbiReg.t4 AbiReg.t3 2#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4, Asm.sw AbiReg.t1 AbiReg.a0])
    (hlink3 : lkm.linkSpec (pre3 ++ codeRest ++ post) = .ok (env.code, env.labels))
    (st3 : State) (hpc3 : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre3))
    (hgp3 : st3.getReg AbiReg.gp = L.T) (hsp3 : st3.getReg AbiReg.sp = sp)
    (ha0 : st3.getReg AbiReg.a0 = ve.toBitVec)
    (hslot0 : readWord64 st3.mem (sp + BitVec.ofInt 64 (slotOff nl)) = u.toBitVec)
    (hslot1 : readWord64 st3.mem (sp + BitVec.ofInt 64 (slotOff (nl + 1))) = vi.toBitVec)
    (hm3 : ProgMemRel env.tab L st3.mem lm) (hf3 : ProgFrameOk L sp st3.mem nl loc) :
    if (vi / 2).toNat < (lm.arr64 (_root_.L.tierA a u)).size then
      ∃ k r',
        RV64.run env.rom k st3 = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre3 + lkm.totalSize codeRest)) ∧
        PreservedRegs st3 r' ∧
        ProgMemRel env.tab L r'.mem (lm.set32 (_root_.L.tierA a u) vi ve) ∧
        ProgFrameOk L sp r'.mem nl loc ∧
        ProgMemOutside (FnWriteMask L sp nl nt) st3.mem r'.mem
    else
      ∃ k r',
        RV64.run env.rom k st3 = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st3 r' := by
  let cl0 := loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff nl)
  let cl1 := loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t1 (slotOff (nl + 1))
  let ctp := [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0]
  let cl2 := loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t4 (env.tab.len64 (.t0 a))
  let codeTail := [Asm.srli AbiReg.t4 AbiReg.t3 1#6, Asm.bgeu AbiReg.t4 AbiReg.t2 errLabel] ++
    loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t4 (env.tab.base64 (_root_.L.TieredArray.t0 a)) ++
    [Asm.slli AbiReg.t4 AbiReg.t3 2#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4, Asm.sw AbiReg.t1 AbiReg.a0]
  have hcEq : codeRest = cl0 ++ cl1 ++ ctp ++ cl2 ++ codeTail := by
    rw [hcRest]; simp [cl0, cl1, ctp, cl2, codeTail, List.append_assoc]
  rw [hcEq] at hlink3
  have hlink3' : lkm.linkSpec (pre3 ++ cl0 ++ (cl1 ++ ctp ++ cl2 ++ codeTail ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink3
  have halX0 : isAligned (st3.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff nl)) 8 = true := by
    rw [hsp3]; exact isAligned8_add_int_mul8 sp hal (1 + nl)
  obtain ⟨st4, hrun3, hoth3, ht0_4, hmem3, hpc4⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre3 _ AbiReg.t0 AbiReg.sp AbiReg.t1
      (by decide) (by decide) (by decide) (slotOff nl) hlink3'
      (linkResolved_sub_pc64 env pre3 cl0 _ hlink3') st3 hpc3 halX0
  have hpres3 : PreservedRegs st3 st4 :=
    ⟨hoth3 _ (by decide) (by decide), hoth3 _ (by decide) (by decide), hoth3 _ (by decide) (by decide), hoth3 _ (by decide) (by decide)⟩
  let pre4 := pre3 ++ cl0
  have htwPre4 : lkm.totalSize pre4 = lkm.totalSize pre3 + lkm.totalSize cl0 := lkm.totalSize_append pre3 cl0
  have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre4) := by rw [hpc4, htwPre4]
  have hlink4 : lkm.linkSpec (pre4 ++ cl1 ++ (ctp ++ cl2 ++ codeTail ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre4, List.append_assoc] using hlink3'
  have halX1 : isAligned (st4.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff (nl + 1))) 8 = true := by
    rw [hpres3.sp.trans hsp3]; exact isAligned8_add_int_mul8 sp hal (1 + (nl + 1))
  obtain ⟨st5, hrun4, hoth4, ht3_5, hmem4, hpc5⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre4 _ AbiReg.t3 AbiReg.sp AbiReg.t1
      (by decide) (by decide) (by decide) (slotOff (nl + 1)) hlink4
      (linkResolved_sub_pc64 env pre4 cl1 _ hlink4) st4 hpc4' halX1
  have hpres4 : PreservedRegs st4 st5 :=
    ⟨hoth4 _ (by decide) (by decide), hoth4 _ (by decide) (by decide), hoth4 _ (by decide) (by decide), hoth4 _ (by decide) (by decide)⟩
  let pre5 := pre4 ++ cl1
  have htwPre5 : lkm.totalSize pre5 = lkm.totalSize pre4 + lkm.totalSize cl1 := lkm.totalSize_append pre4 cl1
  have hpc5' : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre5) := by rw [hpc5, htwPre5]
  have hlink5 : lkm.linkSpec (pre5 ++ ctp ++ (cl2 ++ codeTail ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre5, List.append_assoc] using hlink4
  have hgp5 : st5.getReg AbiReg.gp = L.T := hpres4.gp.trans (hpres3.gp.trans hgp3)
  have ht0_5 : st5.getReg AbiReg.t0 = u.toBitVec := by
    rw [hoth4 _ (by decide) (by decide), ht0_4, hsp3, hslot0]
  obtain ⟨st6, hrun5, hpc6, ht1_6, hoth5, hmem5, hpres5⟩ :=
    prog_tierPtr_sim env pre5 _ L.T u hlink5 st5 hpc5' hgp5 ht0_5
  have htwTp : lkm.totalSize ctp = 3 := by
    simp only [ctp, Asm.andi, Asm.slli, Asm.add, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
  let pre6 := pre5 ++ ctp
  have htwPre6 : lkm.totalSize pre6 = lkm.totalSize pre5 + 3 := by rw [lkm.totalSize_append, htwTp]
  have hpc6' : st6.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre6) := by rw [hpc6, htwPre6]
  have hlink6 : lkm.linkSpec (pre6 ++ cl2 ++ (codeTail ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre6, List.append_assoc] using hlink5
  have hta := tierAddrOk_len64_addr_T L.T a u ha
  rcases hm3.2.1 (_root_.L.tierA a u) hta.1 with ⟨hcap64, hlt64, hlen64, _, _⟩
  have ht1LenAddr : st6.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.len64 (.t0 a)) =
      L.T + BitVec.ofInt 64 (env.tab.len64 (_root_.L.tierA a u)) := by rw [ht1_6, hta.2.1]
  have halLen : isAligned (st6.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.len64 (.t0 a))) 8 = true := by
    rw [ht1LenAddr, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
  obtain ⟨st7, hrun6, hoth6, ht2_7, hmem6, hpc7⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre6 _ AbiReg.t2 AbiReg.t1 AbiReg.t4
      (by decide) (by decide) (by decide) (env.tab.len64 (.t0 a)) hlink6
      (linkResolved_sub_pc64 env pre6 cl2 _ hlink6) st6 hpc6' halLen
  have hpres6 : PreservedRegs st6 st7 :=
    ⟨hoth6 _ (by decide) (by decide), hoth6 _ (by decide) (by decide), hoth6 _ (by decide) (by decide), hoth6 _ (by decide) (by decide)⟩
  let pre7 := pre6 ++ cl2
  have htwPre7 : lkm.totalSize pre7 = lkm.totalSize pre6 + lkm.totalSize cl2 := lkm.totalSize_append pre6 cl2
  have hpc7' : st7.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre7) := by rw [hpc7, htwPre7]
  have hlink7 : lkm.linkSpec (pre7 ++ codeTail ++ post) =
      .ok (env.code, env.labels) := by simpa [pre7, List.append_assoc] using hlink6
  have ht3Val : st7.getReg AbiReg.t3 = vi.toBitVec := by
    rw [hoth6 _ (by decide) (by decide), hoth5 _ (by decide) (by decide), ht3_5, hmem3, hpres3.sp.trans hsp3, hslot1]
  have ht2Val : st7.getReg AbiReg.t2 = BitVec.ofNat 64 (lm.arr64 (_root_.L.tierA a u)).size := by
    rw [ht2_7, hmem5, hmem4, hmem3, ht1LenAddr, hlen64]
  have ha0Val : st7.getReg AbiReg.a0 = ve.toBitVec :=
    (hoth6 _ (by decide) (by decide)).trans
      ((hoth5 _ (by decide) (by decide)).trans ((hoth4 _ (by decide) (by decide)).trans ((hoth3 _ (by decide) (by decide)).trans ha0)))
  have ht1BaseAddr : st7.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.base64 (.t0 a)) =
      L.T + BitVec.ofInt 64 (env.tab.base64 (_root_.L.tierA a u)) := by
    rw [hoth6 _ (by decide) (by decide), ht1_6, hta.2.2]
  have hstMem7 : st7.mem = st3.mem := by rw [hmem6, hmem5, hmem4, hmem3]
  have htail := prog_st32t_tail_sim env L lm loc hlim htop a u vi ve ha pre7 codeTail post rfl hlink7 st7
    hpc7' ht3Val ht2Val ha0Val ht1BaseAddr (hstMem7 ▸ hm3) (hstMem7 ▸ hf3)
  have hrun0_6 := run_trans (run_trans (run_trans hrun3 hrun4) hrun5) hrun6
  have hpres0_6 : PreservedRegs st3 st7 := hpres3.trans (hpres4.trans (hpres5.trans hpres6))
  by_cases hbound : (vi / 2).toNat < (lm.arr64 (_root_.L.tierA a u)).size
  · simp only [hbound, ↓reduceIte] at htail ⊢
    obtain ⟨k, r', hrunT, hpcT, hpresT, hmT, hfT, hpmT⟩ := htail
    have hpcEq : lkm.totalSize pre7 + lkm.totalSize codeTail = lkm.totalSize pre3 + lkm.totalSize codeRest := by
      rw [htwPre7, htwPre6, htwPre5, htwPre4, hcEq,
          lkm.totalSize_append (((cl0 ++ cl1) ++ ctp) ++ cl2) codeTail,
          lkm.totalSize_append ((cl0 ++ cl1) ++ ctp) cl2,
          lkm.totalSize_append (cl0 ++ cl1) ctp,
          lkm.totalSize_append cl0 cl1, htwTp]; omega
    rw [hpcEq] at hpcT
    exact ⟨_, r', run_trans hrun0_6 hrunT, hpcT, hpres0_6.trans hpresT, hmT, hfT, hstMem7 ▸ hpmT⟩
  · simp only [hbound, ↓reduceIte] at htail ⊢
    obtain ⟨k, r', hrunT, hpcT, hpresT⟩ := htail
    exact ⟨_, r', run_trans hrun0_6 hrunT, hpcT, hpres0_6.trans hpresT⟩

theorem prog_st32t_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (a : _root_.L.ArrId) (t i e : _root_.L.Expr)
    (ha : tier32OkB env.tab a t = true)
    (htOk : exprOkB env.tab nl t = true) (hiOk : exprOkB env.tab nl i = true)
    (heOk : exprOkB env.tab nl e = true)
    (hnt : max (maxTempsExpr t) (max (1 + maxTempsExpr i) (2 + maxTempsExpr e)) ≤ nt)
    (pre post : List AsmItem)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOk L sp st.mem nl loc)
    (hlink : lkm.linkSpec (pre ++ (compileTierStoreTriple env.tab nl t i e ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t4 (env.tab.len64 (_root_.L.TieredArray.t0 a)) ++
      [Asm.srli AbiReg.t4 AbiReg.t3 1#6, Asm.bgeu AbiReg.t4 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t4 (env.tab.base64 (_root_.L.TieredArray.t0 a)) ++
      [Asm.slli AbiReg.t4 AbiReg.t3 2#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4, Asm.sw AbiReg.t1 AbiReg.a0]) ++ post) =
      .ok (env.code, env.labels)) :
    let codeS := compileTierStoreTriple env.tab nl t i e ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t4 (env.tab.len64 (_root_.L.TieredArray.t0 a)) ++
      [Asm.srli AbiReg.t4 AbiReg.t3 1#6, Asm.bgeu AbiReg.t4 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t4 (env.tab.base64 (_root_.L.TieredArray.t0 a)) ++
      [Asm.slli AbiReg.t4 AbiReg.t3 2#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4, Asm.sw AbiReg.t1 AbiReg.a0]
    match (do let u ← _root_.L.evalE t; let j ← _root_.L.evalE i; let v ← _root_.L.evalE e; _root_.L.st32 (_root_.L.tierA a u) j v)
        { mem := lm, loc := loc } with
    | .ok (_, st') =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize codeS)) ∧
        PreservedRegs st r' ∧
        ProgMemRel env.tab L r'.mem st'.mem ∧
        ProgFrameOk L sp r'.mem nl st'.loc ∧
        ProgMemOutside (FnWriteMask L sp nl nt) st.mem r'.mem
    | .error _ =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st r' := by
  let ct := compileTierStoreTriple env.tab nl t i e
  let ctp := [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0]
  let cl2 := loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t4 (env.tab.len64 (.t0 a))
  let codeTail := [Asm.srli AbiReg.t4 AbiReg.t3 1#6, Asm.bgeu AbiReg.t4 AbiReg.t2 errLabel] ++
    loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t4 (env.tab.base64 (_root_.L.TieredArray.t0 a)) ++
    [Asm.slli AbiReg.t4 AbiReg.t3 2#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4, Asm.sw AbiReg.t1 AbiReg.a0]
  have hlinkP : lkm.linkSpec (pre ++ ct ++ (ctp ++ cl2 ++ codeTail ++ post)) = .ok (env.code, env.labels) := by
    simpa only [ct, ctp, cl2, codeTail, List.append_assoc] using hlink
  have rp := prog_compileTierStoreTriple_sim env L lm loc hal hlim htop t i e htOk hiOk heOk hnt
    pre (ctp ++ cl2 ++ codeTail ++ post) st hpc hgp hsp hm hf hlinkP
  rcases _root_.L.evalE_pure t { mem := lm, loc := loc } with ⟨u, htE⟩ | htE
  · rcases _root_.L.evalE_pure i { mem := lm, loc := loc } with ⟨vi, hiE⟩ | hiE
    · rcases _root_.L.evalE_pure e { mem := lm, loc := loc } with ⟨ve, heE⟩ | heE
      · rw [htE, hiE, heE] at rp
        obtain ⟨kp, st5, hrunP, hpc5, ht0_5, ht3_5, ha0_5, hpresP, hm3, hf3, hpmP⟩ := rp
        let pre5 := pre ++ ct
        have htwPre5 : lkm.totalSize pre5 = lkm.totalSize pre + lkm.totalSize ct := lkm.totalSize_append _ _
        have hpc5' : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre5) := by rw [hpc5, htwPre5]
        have hlink5 : lkm.linkSpec (pre5 ++ ctp ++ (cl2 ++ codeTail ++ post)) = .ok (env.code, env.labels) := by
          simpa only [pre5, List.append_assoc] using hlinkP
        obtain ⟨st6, hrun5, hpc6, ht1_6, hoth5, hmem5, hpres5⟩ :=
          prog_tierPtr_sim env pre5 _ L.T u hlink5 st5 hpc5' (hpresP.gp.trans hgp) ht0_5
        have htwTp : lkm.totalSize ctp = 3 := by
          simp only [ctp, Asm.andi, Asm.slli, Asm.add, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
        let pre6 := pre5 ++ ctp
        have htwPre6 : lkm.totalSize pre6 = lkm.totalSize pre5 + 3 := by rw [lkm.totalSize_append, htwTp]
        have hpc6' : st6.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre6) := by rw [hpc6, htwPre6]
        have hlink6 : lkm.linkSpec (pre6 ++ cl2 ++ (codeTail ++ post)) = .ok (env.code, env.labels) := by
          simpa only [pre6, List.append_assoc] using hlink5
        have htaOk := tier32Ok_to_tierAddrOk ha htE
        have hta := tierAddrOk_len64_addr_T L.T a u htaOk
        rcases hm3.2.1 (_root_.L.tierA a u) hta.1 with ⟨_, _, hlen64, _, _⟩
        have ht1LenAddr : st6.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.len64 (.t0 a)) =
            L.T + BitVec.ofInt 64 (env.tab.len64 (_root_.L.tierA a u)) := by rw [ht1_6, hta.2.1]
        have halLen : isAligned (st6.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.len64 (.t0 a))) 8 = true := by
          rw [ht1LenAddr, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
        obtain ⟨st7, hrun6, hoth6, ht2_7, hmem6, hpc7⟩ :=
          loadMemOff_ld_correct_lm lkm env.hrom pre6 _ AbiReg.t2 AbiReg.t1 AbiReg.t4
            (by decide) (by decide) (by decide) (env.tab.len64 (.t0 a)) hlink6
            (linkResolved_sub_pc64 env pre6 cl2 _ hlink6) st6 hpc6' halLen
        have hpres6 : PreservedRegs st6 st7 :=
          ⟨hoth6 _ (by decide) (by decide), hoth6 _ (by decide) (by decide), hoth6 _ (by decide) (by decide), hoth6 _ (by decide) (by decide)⟩
        let pre7 := pre6 ++ cl2
        have htwPre7 : lkm.totalSize pre7 = lkm.totalSize pre6 + lkm.totalSize cl2 := lkm.totalSize_append _ _
        have hpc7' : st7.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre7) := by rw [hpc7, htwPre7]
        have hlink7 : lkm.linkSpec (pre7 ++ codeTail ++ post) = .ok (env.code, env.labels) := by
          simpa only [pre7, List.append_assoc] using hlink6
        have ht3Val : st7.getReg AbiReg.t3 = vi.toBitVec :=
          (hoth6 _ (by decide) (by decide)).trans ((hoth5 _ (by decide) (by decide)).trans ht3_5)
        have ht2Val : st7.getReg AbiReg.t2 = BitVec.ofNat 64 (lm.arr64 (_root_.L.tierA a u)).size := by
          rw [ht2_7, hmem5, ht1LenAddr, hlen64]
        have ha0Val : st7.getReg AbiReg.a0 = ve.toBitVec :=
          (hoth6 _ (by decide) (by decide)).trans ((hoth5 _ (by decide) (by decide)).trans ha0_5)
        have ht1BaseAddr : st7.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.base64 (.t0 a)) =
            L.T + BitVec.ofInt 64 (env.tab.base64 (_root_.L.tierA a u)) := by
          rw [hoth6 _ (by decide) (by decide), ht1_6, hta.2.2]
        have hstMem7 : st7.mem = st5.mem := by rw [hmem6, hmem5]
        have htail := prog_st32t_tail_sim env L lm loc hlim htop a u vi ve htaOk pre7 codeTail post rfl hlink7 st7
          hpc7' ht3Val ht2Val ha0Val ht1BaseAddr (hstMem7 ▸ hm3) (hstMem7 ▸ hf3)
        by_cases hbound : (vi / 2).toNat < (lm.arr64 (_root_.L.tierA a u)).size
        · simp only [hbound, ↓reduceIte] at htail
          obtain ⟨k, r', hrunT, hpcT, hpresT, hmT, hfT, hpmT⟩ := htail
          have hmini : (do let u ← _root_.L.evalE t; let j ← _root_.L.evalE i; let v ← _root_.L.evalE e; _root_.L.st32 (_root_.L.tierA a u) j v)
              { mem := lm, loc := loc } = .ok ((), { mem := lm.set32 (_root_.L.tierA a u) vi ve, loc := loc }) := by
            simp only [Bind.bind, StateT.bind, Except.bind, htE, hiE, heE, _root_.L.st32, get, getThe,
              MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set,
              Pure.pure, Except.pure, hbound, ↓reduceIte]
          rw [hmini]
          have hpcEq : lkm.totalSize pre7 + lkm.totalSize codeTail =
              lkm.totalSize pre + lkm.totalSize (ct ++ ctp ++ cl2 ++
                [Asm.srli AbiReg.t4 AbiReg.t3 1#6, Asm.bgeu AbiReg.t4 AbiReg.t2 errLabel] ++
                loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t4 (env.tab.base64 (.t0 a)) ++
                [Asm.slli AbiReg.t4 AbiReg.t3 2#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4, Asm.sw AbiReg.t1 AbiReg.a0]) := by
            rw [htwPre7, htwPre6, htwPre5]; dsimp only [codeTail]; simp only [lkm.totalSize_append, htwTp]; omega
          exact ⟨_, r', run_trans (run_trans (run_trans hrunP hrun5) hrun6) hrunT, by rw [hpcT, hpcEq],
            hpresP.trans (hpres5.trans (hpres6.trans hpresT)), hmT, hfT, hpmP.trans (hstMem7 ▸ hpmT)⟩
        · simp only [hbound, ↓reduceIte] at htail
          obtain ⟨k, r', hrunT, hpcT, hpresT⟩ := htail
          have hmini : (do let u ← _root_.L.evalE t; let j ← _root_.L.evalE i; let v ← _root_.L.evalE e; _root_.L.st32 (_root_.L.tierA a u) j v)
              { mem := lm, loc := loc } = .error .oob := by
            simp only [Bind.bind, StateT.bind, Except.bind, htE, hiE, heE, _root_.L.st32, get, getThe,
              MonadStateOf.get, StateT.get, throw, throwThe, MonadExceptOf.throw,
              Pure.pure, Except.pure, hbound, ↓reduceIte]; rfl
          rw [hmini]
          exact ⟨_, r', run_trans (run_trans (run_trans hrunP hrun5) hrun6) hrunT, hpcT,
            hpresP.trans (hpres5.trans (hpres6.trans hpresT))⟩
      · simp only [Bind.bind, StateT.bind, Except.bind, htE, hiE, heE] at rp ⊢; exact rp
    · simp only [Bind.bind, StateT.bind, Except.bind, htE, hiE] at rp ⊢; exact rp
  · simp only [Bind.bind, StateT.bind, Except.bind, htE] at rp ⊢; exact rp

theorem prog_warr_dst_check_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem)
    (a : _root_.L.ArrId) (u vdi vk : _root_.L.Word) (da : _root_.L.TieredArray)
    (hdaOk : env.tab.wordPosOkB da = true)
    (hOffBase : L.T + (if (u &&& 1 == 0) = true then 0#64 else 8#64) +
        BitVec.ofInt 64 (env.tab.base64 (.t0 a)) =
        L.T + BitVec.ofInt 64 (env.tab.base64 da))
    (pre5 codeTail post : List AsmItem)
    (hcodeTail : codeTail = [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3,
        Asm.bltu AbiReg.t0 AbiReg.t1 errLabel] ++
      loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (env.tab.base64 (.t0 a)) ++
      [Asm.slli AbiReg.t1 AbiReg.t1 3#6, Asm.add AbiReg.t1 AbiReg.t5 AbiReg.t1])
    (st5 : State) (hpc5 : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre5))
    (hm : ProgMemRel env.tab L st5.mem lm)
    (ht0Val : st5.getReg AbiReg.t0 = BitVec.ofNat 64 (lm.arr64 da).size)
    (ht1Val : st5.getReg AbiReg.t1 = vdi.toBitVec)
    (ht3Val : st5.getReg AbiReg.t3 = vk.toBitVec)
    (ht5Keep : st5.getReg AbiReg.t5 = L.T + (if (u &&& 1 == 0) = true then 0#64 else 8#64))
    (hlink5 : lkm.linkSpec (pre5 ++ codeTail ++ post) = .ok (env.code, env.labels)) :
    if vdi.toNat + vk.toNat ≤ (lm.arr64 da).size then
      ∃ k r',
        RV64.run env.rom k st5 = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre5 + lkm.totalSize codeTail)) ∧
        r'.getReg AbiReg.t1 = L.base64 da + BitVec.ofNat 64 (8 * vdi.toNat) ∧
        r'.getReg AbiReg.t3 = vk.toBitVec ∧
        r'.mem = st5.mem ∧
        PreservedRegs st5 r'
    else
      ∃ k r',
        RV64.run env.rom k st5 = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st5 r' := by
  let cchk := [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3, Asm.bltu AbiReg.t0 AbiReg.t1 errLabel]
  let cl4 := loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (env.tab.base64 (.t0 a))
  let ctail := [Asm.slli AbiReg.t1 AbiReg.t1 3#6, Asm.add AbiReg.t1 AbiReg.t5 AbiReg.t1]
  have hct : codeTail = cchk ++ cl4 ++ ctail := by rw [hcodeTail]
  rw [hct] at hlink5
  have hlink5' : lkm.linkSpec (pre5 ++ cchk ++ (cl4 ++ ctail ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink5
  have ⟨hlC1, hlC23⟩ := linkResolved_mid_split lkm pre5 [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel]
    [Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3, Asm.bltu AbiReg.t0 AbiReg.t1 errLabel] _ hlink5'
  have ⟨hlC2, hlC3⟩ := linkResolved_mid_split lkm (pre5 ++ [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel])
    [Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3] [Asm.bltu AbiReg.t0 AbiReg.t1 errLabel] _ hlC23
  have htwC2 : lkm.totalSize [Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3] = 1 := by
    simp only [Asm.sub, lkm.totalSize_instr]
  rcases hm.2.1 da hdaOk with ⟨_, _, _, hbase64, _⟩
  have hbr1 := run_br_step env pre5 _ .bltu AbiReg.t0 AbiReg.t3 errLabel env.errTarget env.herrLbl (by decide) hlC1 st5 hpc5
  have hcond1 : evalBranch .bltu (st5.getReg AbiReg.t0) (st5.getReg AbiReg.t3) =
      decide ((lm.arr64 da).size < vk.toNat) := by
    rw [ht0Val, ht3Val, u64_toBitVec_eq_ofNat]
    exact evalBranch_bltu_nat (by omega) vk.toBitVec.isLt
  obtain ⟨kBr1, st6, _, hrun4, hpcBr1, hoth4, hpres4, hmem4⟩ := hbr1
  by_cases h1 : vk.toNat ≤ (lm.arr64 da).size
  · have hbr1F : evalBranch .bltu (st5.getReg AbiReg.t0) (st5.getReg AbiReg.t3) = false := by
      rw [hcond1, decide_eq_false_iff_not]; omega
    have hpc6' : st6.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre5 ++ [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel])) := by
      rw [hpcBr1, hbr1F]; simp only [Bool.false_eq_true, ↓reduceIte, lkm.totalSize_append, Asm.bltu, Asm.br, lkm.totalSize_singleton]
    let st7 := stepReg st6 AbiReg.t0 (evalAlu .sub (st6.getReg AbiReg.t0) (st6.getReg AbiReg.t3))
      (BitVec.ofNat 64 (4 * (lkm.totalSize (pre5 ++ [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel]) + 1)))
    obtain ⟨hrun5, hpc7, ht0_7, hoth5, hmem5, hpres5⟩ :=
      run_alu_step env (pre5 ++ [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel]) _ .sub AbiReg.t0 AbiReg.t0 AbiReg.t3
        nonPreserved_t0 hlC2 st6 hpc6'
    have hbr2 := run_br_step env
      ((pre5 ++ [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel]) ++ [Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3]) _
      .bltu AbiReg.t0 AbiReg.t1 errLabel env.errTarget env.herrLbl (by decide) hlC3 st7
      (by rw [lkm.totalSize_append, htwC2]; exact hpc7)
    have ht0_7val : st7.getReg AbiReg.t0 = BitVec.ofNat 64 ((lm.arr64 da).size - vk.toNat) := by
      have hvkLt : vk.toNat < 2 ^ 64 := vk.toBitVec.isLt
      have hleBv : BitVec.ofNat 64 vk.toNat ≤ BitVec.ofNat 64 (lm.arr64 da).size := by
        rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt hvkLt, Nat.mod_eq_of_lt (by omega)]
        exact h1
      rw [ht0_7, evalAlu, hoth4 _ (by decide), hoth4 _ (by decide)]
      change st5.getReg AbiReg.t0 - st5.getReg AbiReg.t3 = _
      rw [ht0Val, ht3Val, u64_toBitVec_eq_ofNat]; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le hleBv, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hvkLt, Nat.mod_eq_of_lt (by omega)]
    have ht1_7val : st7.getReg AbiReg.t1 = vdi.toBitVec := by
      rw [hoth5 _ (by decide), hoth4 _ (by decide)]; exact ht1Val
    have hcond2 : evalBranch .bltu (st7.getReg AbiReg.t0) (st7.getReg AbiReg.t1) =
        decide ((lm.arr64 da).size - vk.toNat < vdi.toNat) := by
      rw [ht0_7val, ht1_7val, u64_toBitVec_eq_ofNat]
      exact evalBranch_bltu_nat (by omega) vdi.toBitVec.isLt
    obtain ⟨kBr2, st8, _, hrun6, hpcBr2, hoth6, hpres6, hmem6⟩ := hbr2
    by_cases h2 : vdi.toNat + vk.toNat ≤ (lm.arr64 da).size
    · simp only [h2, ↓reduceIte]
      have hbr2F : evalBranch .bltu (st7.getReg AbiReg.t0) (st7.getReg AbiReg.t1) = false := by
        rw [hcond2, decide_eq_false_iff_not]; omega
      let pre6 := pre5 ++ cchk
      have htwChk : lkm.totalSize cchk =
          lkm.totalSize [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel] + 1 + lkm.totalSize [Asm.bltu AbiReg.t0 AbiReg.t1 errLabel] := by
        simp only [cchk, Asm.sub, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]; omega
      have htwPre6 : lkm.totalSize pre6 = lkm.totalSize pre5 + lkm.totalSize cchk := lkm.totalSize_append pre5 cchk
      have hlink6 : lkm.linkSpec (pre6 ++ cl4 ++ (ctail ++ post)) =
          .ok (env.code, env.labels) := by simpa [pre6, List.append_assoc] using hlink5'
      have hpc8 : st8.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre6) := by
        rw [hpcBr2, hbr2F]; simp only [Bool.false_eq_true, ↓reduceIte]
        congr 2
        rw [htwPre6, htwChk, lkm.totalSize_append, lkm.totalSize_append, htwC2]
        simp only [Asm.bltu, Asm.br, lkm.totalSize_singleton]; omega
      have ht5BaseAddr : st8.getReg AbiReg.t5 + BitVec.ofInt 64 (env.tab.base64 (.t0 a)) =
          L.T + BitVec.ofInt 64 (env.tab.base64 da) := by
        rw [hoth6 _ (by decide), hoth5 _ (by decide), hoth4 _ (by decide), ht5Keep]; exact hOffBase
      have halBase : isAligned (st8.getReg AbiReg.t5 + BitVec.ofInt 64 (env.tab.base64 (.t0 a))) 8 = true := by
        rw [ht5BaseAddr, Tab.base64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
      obtain ⟨st9, hrun7, hoth7, ht5_9, hmem7, hpc9⟩ :=
        loadMemOff_ld_correct_lm lkm env.hrom pre6 _ AbiReg.t5 AbiReg.t5 AbiReg.t6
          (by decide) (by decide) (by decide) (env.tab.base64 (.t0 a)) hlink6
          (linkResolved_sub_pc64 env pre6 cl4 _ hlink6) st8 hpc8 halBase
      have hpres7 : PreservedRegs st8 st9 :=
        ⟨hoth7 _ (by decide) (by decide), hoth7 _ (by decide) (by decide), hoth7 _ (by decide) (by decide), hoth7 _ (by decide) (by decide)⟩
      let pre7 := pre6 ++ cl4
      have htwPre7 : lkm.totalSize pre7 = lkm.totalSize pre6 + lkm.totalSize cl4 := lkm.totalSize_append pre6 cl4
      have hpc9' : st9.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre7) := by rw [hpc9, htwPre7]
      have hlink7 : lkm.linkSpec (pre7 ++ ctail ++ post) =
          .ok (env.code, env.labels) := by simpa [pre7, List.append_assoc] using hlink6
      have ⟨hlA, hlB⟩ := linkResolved_mid_split lkm pre7 [Asm.slli AbiReg.t1 AbiReg.t1 3#6]
        [Asm.add AbiReg.t1 AbiReg.t5 AbiReg.t1] post hlink7
      have htwA : lkm.totalSize [Asm.slli AbiReg.t1 AbiReg.t1 3#6] = 1 := by simp only [Asm.slli, lkm.totalSize_instr]
      let st10 := stepReg st9 AbiReg.t1
        (evalShiftImm .slli (st9.getReg AbiReg.t1) 3#6) (BitVec.ofNat 64 (4 * (lkm.totalSize pre7 + 1)))
      obtain ⟨hrun8, hpc10, ht1_10, hoth8, hmem8, hpres8⟩ :=
        run_shImm_step env pre7 _ .slli AbiReg.t1 AbiReg.t1 3#6 nonPreserved_t1 hlA st9 hpc9'
      let st11 := stepReg st10 AbiReg.t1
        (evalAlu .add (st10.getReg AbiReg.t5) (st10.getReg AbiReg.t1))
        (BitVec.ofNat 64 (4 * (lkm.totalSize (pre7 ++ [Asm.slli AbiReg.t1 AbiReg.t1 3#6]) + 1)))
      obtain ⟨hrun9, hpc11, ht1_11, hoth9, hmem9, hpres9⟩ :=
        run_alu_step env (pre7 ++ [Asm.slli AbiReg.t1 AbiReg.t1 3#6]) _ .add AbiReg.t1 AbiReg.t5 AbiReg.t1
          nonPreserved_t1 hlB st10 (by rw [lkm.totalSize_append, htwA]; exact hpc10)
      have ht1Addr : st11.getReg AbiReg.t1 = L.base64 da + BitVec.ofNat 64 (8 * vdi.toNat) := by
        rw [ht1_11, evalAlu, hoth8 _ (by decide), ht5_9, hmem6, hmem5, hmem4, ht5BaseAddr, hbase64, ht1_10, hoth7 _ (by decide) (by decide), hoth6 _ (by decide)]
        change L.base64 da + evalShiftImm .slli (st7.getReg AbiReg.t1) 3#6 = _
        rw [ht1_7val, shl3_ofNat_eq vdi (by omega)]
      have ht3Keep : st11.getReg AbiReg.t3 = vk.toBitVec := by
        rw [hoth9 _ (by decide), hoth8 _ (by decide), hoth7 _ (by decide) (by decide), hoth6 _ (by decide)]
        change st7.getReg AbiReg.t3 = _; rw [hoth5 _ (by decide), hoth4 _ (by decide)]; exact ht3Val
      have hmemKeep : st11.mem = st5.mem := by rw [hmem9, hmem8, hmem7, hmem6, hmem5, hmem4]
      have hpc11' : st11.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre5 + lkm.totalSize codeTail)) := by
        have htwTail : lkm.totalSize ctail = 2 := by
          simp only [ctail, Asm.slli, Asm.add, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
        have htwCT : lkm.totalSize codeTail = lkm.totalSize cchk + lkm.totalSize cl4 + 2 := by
          rw [hct, lkm.totalSize_append, lkm.totalSize_append, htwTail]
        rw [hpc11, lkm.totalSize_append, htwA, htwPre7, htwPre6, htwCT]; congr 2; omega
      have hrunAll := run_trans (run_trans (run_trans (run_trans (run_trans hrun4 hrun5) hrun6) hrun7) hrun8) hrun9
      exact ⟨_, st11, hrunAll, hpc11', ht1Addr, ht3Keep, hmemKeep,
        hpres4.trans (hpres5.trans (hpres6.trans (hpres7.trans (hpres8.trans hpres9))))⟩
    · simp only [h2, ↓reduceIte]
      have hbr2T : evalBranch .bltu (st7.getReg AbiReg.t0) (st7.getReg AbiReg.t1) = true := by
        rw [hcond2, decide_eq_true_iff]; omega
      have hpcT : st8.pc = BitVec.ofNat 64 (4 * env.errTarget) := by rw [hpcBr2, hbr2T]; rfl
      exact ⟨_, st8, run_trans (run_trans hrun4 hrun5) hrun6, hpcT,
        hpres4.trans (hpres5.trans hpres6)⟩
  · have hnot2 : ¬ (vdi.toNat + vk.toNat ≤ (lm.arr64 da).size) := by omega
    simp only [hnot2, ↓reduceIte]
    have hbr1T : evalBranch .bltu (st5.getReg AbiReg.t0) (st5.getReg AbiReg.t3) = true := by
      rw [hcond1, decide_eq_true_iff]; omega
    have hpcT : st6.pc = BitVec.ofNat 64 (4 * env.errTarget) := by rw [hpcBr1, hbr1T]; rfl
    exact ⟨kBr1, st6, hrun4, hpcT, hpres4⟩

theorem prog_warr_dst_setup_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) {sp : BitVec 64} {nl : Nat}
    (hal : isAligned sp 8 = true)
    (a : _root_.L.ArrId) (u vdi vk : _root_.L.Word) (da : _root_.L.TieredArray)
    (hdaOk : env.tab.wordPosOkB da = true)
    (hOffLen : L.T + (if (u &&& 1 == 0) = true then 0#64 else 8#64) +
        BitVec.ofInt 64 (env.tab.len64 (.t0 a)) =
        L.T + BitVec.ofInt 64 (env.tab.len64 da))
    (hOffBase : L.T + (if (u &&& 1 == 0) = true then 0#64 else 8#64) +
        BitVec.ofInt 64 (env.tab.base64 (.t0 a)) =
        L.T + BitVec.ofInt 64 (env.tab.base64 da))
    (pre codeSetup post : List AsmItem)
    (hcodeSetup : codeSetup = loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff nl) ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (env.tab.len64 (.t0 a)) ++
      loadMemOff .ld AbiReg.t1 AbiReg.sp AbiReg.t6 (slotOff (nl + 1)) ++
      loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t6 (slotOff (nl + 4)) ++
      [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3, Asm.bltu AbiReg.t0 AbiReg.t1 errLabel] ++
      loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (env.tab.base64 (.t0 a)) ++
      [Asm.slli AbiReg.t1 AbiReg.t1 3#6, Asm.add AbiReg.t1 AbiReg.t5 AbiReg.t1])
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm)
    (hslot0 : readWord64 st.mem (sp + BitVec.ofInt 64 (slotOff nl)) = u.toBitVec)
    (hslot1 : readWord64 st.mem (sp + BitVec.ofInt 64 (slotOff (nl + 1))) = vdi.toBitVec)
    (hslot4 : readWord64 st.mem (sp + BitVec.ofInt 64 (slotOff (nl + 4))) = vk.toBitVec)
    (hlink : lkm.linkSpec (pre ++ codeSetup ++ post) = .ok (env.code, env.labels)) :
    if vdi.toNat + vk.toNat ≤ (lm.arr64 da).size then
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize codeSetup)) ∧
        r'.getReg AbiReg.t1 = L.base64 da + BitVec.ofNat 64 (8 * vdi.toNat) ∧
        r'.getReg AbiReg.t3 = vk.toBitVec ∧
        r'.mem = st.mem ∧
        PreservedRegs st r'
    else
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st r' := by
  let cl0 := loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff nl)
  let ctp := [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0]
  let cl1 := loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (env.tab.len64 (.t0 a))
  let cl2 := loadMemOff .ld AbiReg.t1 AbiReg.sp AbiReg.t6 (slotOff (nl + 1))
  let cl3 := loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t6 (slotOff (nl + 4))
  let codeTail := [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3, Asm.bltu AbiReg.t0 AbiReg.t1 errLabel] ++
    loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (env.tab.base64 (.t0 a)) ++
    [Asm.slli AbiReg.t1 AbiReg.t1 3#6, Asm.add AbiReg.t1 AbiReg.t5 AbiReg.t1]
  have hcode : codeSetup = cl0 ++ ctp ++ cl1 ++ cl2 ++ cl3 ++ codeTail := by
    rw [hcodeSetup]; simp [cl0, ctp, cl1, cl2, cl3, codeTail, List.append_assoc]
  rw [hcode] at hlink
  have hlink0 : lkm.linkSpec (pre ++ cl0 ++ (ctp ++ cl1 ++ cl2 ++ cl3 ++ codeTail ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
  have halX0 : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff nl)) 8 = true := by
    rw [hsp]; exact isAligned8_add_int_mul8 sp hal (1 + nl)
  obtain ⟨st1, hrun0, hoth0, ht0_1, hmem0, hpc1⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre _ AbiReg.t0 AbiReg.sp AbiReg.t1
      (by decide) (by decide) (by decide) (slotOff nl) hlink0
      (linkResolved_sub_pc64 env pre cl0 _ hlink0) st hpc halX0
  have hpres0 : PreservedRegs st st1 :=
    ⟨hoth0 _ (by decide) (by decide), hoth0 _ (by decide) (by decide), hoth0 _ (by decide) (by decide), hoth0 _ (by decide) (by decide)⟩
  let pre1 := pre ++ cl0
  have htwPre1 : lkm.totalSize pre1 = lkm.totalSize pre + lkm.totalSize cl0 := lkm.totalSize_append pre cl0
  have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by rw [hpc1, htwPre1]
  have hlink1 : lkm.linkSpec (pre1 ++ ctp ++ (cl1 ++ cl2 ++ cl3 ++ codeTail ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre1, List.append_assoc] using hlink0
  have ⟨hlT1, hlT23⟩ := linkResolved_mid_split lkm pre1 [Asm.andi AbiReg.t0 AbiReg.t0 1#12]
    [Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] _ hlink1
  have ⟨hlT2, hlT3⟩ := linkResolved_mid_split lkm (pre1 ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12])
    [Asm.slli AbiReg.t0 AbiReg.t0 3#6] [Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] _ hlT23
  have htw1 : lkm.totalSize [Asm.andi AbiReg.t0 AbiReg.t0 1#12] = 1 := by simp only [Asm.andi, lkm.totalSize_instr]
  have htw2 : lkm.totalSize [Asm.slli AbiReg.t0 AbiReg.t0 3#6] = 1 := by simp only [Asm.slli, lkm.totalSize_instr]
  let st1a := stepReg st1 AbiReg.t0 (evalAluImm .andi (st1.getReg AbiReg.t0) 1#12)
    (BitVec.ofNat 64 (4 * (lkm.totalSize pre1 + 1)))
  obtain ⟨hrunT1, hpcT1, ht0_T1, hothT1, hmemT1, hpresT1⟩ :=
    run_aluImm_step env pre1 _ .andi AbiReg.t0 AbiReg.t0 1#12 nonPreserved_t0 hlT1 st1 hpc1'
  let st1b := stepReg st1a AbiReg.t0 (evalShiftImm .slli (st1a.getReg AbiReg.t0) 3#6)
    (BitVec.ofNat 64 (4 * (lkm.totalSize (pre1 ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12]) + 1)))
  obtain ⟨hrunT2, hpcT2, ht0_T2, hothT2, hmemT2, hpresT2⟩ :=
    run_shImm_step env (pre1 ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12]) _ .slli AbiReg.t0 AbiReg.t0 3#6 nonPreserved_t0 hlT2 st1a
      (by rw [lkm.totalSize_append, htw1]; exact hpcT1)
  let st2 := stepReg st1b AbiReg.t5 (evalAlu .add (st1b.getReg AbiReg.gp) (st1b.getReg AbiReg.t0))
    (BitVec.ofNat 64 (4 * (lkm.totalSize ((pre1 ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12]) ++ [Asm.slli AbiReg.t0 AbiReg.t0 3#6]) + 1)))
  obtain ⟨hrunT3, hpc2, ht5_2, hothT3, hmemT3, hpresT3⟩ :=
    run_alu_step env ((pre1 ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12]) ++ [Asm.slli AbiReg.t0 AbiReg.t0 3#6]) _
      .add AbiReg.t5 AbiReg.gp AbiReg.t0 nonPreserved_t5 hlT3 st1b
      (by rw [lkm.totalSize_append, htw2]; exact hpcT2)
  have ht5Val : st2.getReg AbiReg.t5 = L.T + (if (u &&& 1 == 0) = true then 0#64 else 8#64) := by
    have hgpB : st1b.getReg AbiReg.gp = L.T := (hpresT1.trans hpresT2).gp.trans (hpres0.gp.trans hgp)
    have ht0_1eq : st1.getReg AbiReg.t0 = u.toBitVec := by rw [ht0_1, hsp, hslot0]
    rw [ht5_2, evalAlu, hgpB, ht0_T2, ht0_T1, ht0_1eq, tier_off_val u]
  have htwTp : lkm.totalSize ctp = 3 := by
    simp only [ctp, Asm.andi, Asm.slli, Asm.add, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
  let pre2 := pre1 ++ ctp
  have htwPre2 : lkm.totalSize pre2 = lkm.totalSize pre1 + 3 := by rw [lkm.totalSize_append, htwTp]
  have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) := by
    rw [hpc2, htwPre2, lkm.totalSize_append, lkm.totalSize_append, htw1, htw2, Nat.add_assoc]
  have hlink2 : lkm.linkSpec (pre2 ++ cl1 ++ (cl2 ++ cl3 ++ codeTail ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre2, List.append_assoc] using hlink1
  rcases hm.2.1 da hdaOk with ⟨_, _, hlen64, _, _⟩
  have ht5LenAddr : st2.getReg AbiReg.t5 + BitVec.ofInt 64 (env.tab.len64 (.t0 a)) =
      L.T + BitVec.ofInt 64 (env.tab.len64 da) := by rw [ht5Val]; exact hOffLen
  have halLen : isAligned (st2.getReg AbiReg.t5 + BitVec.ofInt 64 (env.tab.len64 (.t0 a))) 8 = true := by
    rw [ht5LenAddr, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
  obtain ⟨st3, hrun1, hoth1, ht0_3, hmem1, hpc3⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre2 _ AbiReg.t0 AbiReg.t5 AbiReg.t6
      (by decide) (by decide) (by decide) (env.tab.len64 (.t0 a)) hlink2
      (linkResolved_sub_pc64 env pre2 cl1 _ hlink2) st2 hpc2' halLen
  have hpres1 : PreservedRegs st2 st3 :=
    ⟨hoth1 _ (by decide) (by decide), hoth1 _ (by decide) (by decide), hoth1 _ (by decide) (by decide), hoth1 _ (by decide) (by decide)⟩
  let pre3 := pre2 ++ cl1
  have htwPre3 : lkm.totalSize pre3 = lkm.totalSize pre2 + lkm.totalSize cl1 := lkm.totalSize_append pre2 cl1
  have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre3) := by rw [hpc3, htwPre3]
  have hlink3 : lkm.linkSpec (pre3 ++ cl2 ++ (cl3 ++ codeTail ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre3, List.append_assoc] using hlink2
  have hpres0_3 : PreservedRegs st st3 := hpres0.trans (hpresT1.trans (hpresT2.trans (hpresT3.trans hpres1)))
  have hmem0_3 : st3.mem = st.mem := by rw [hmem1, hmemT3, hmemT2, hmemT1, hmem0]
  have halX1 : isAligned (st3.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff (nl + 1))) 8 = true := by
    rw [hpres0_3.sp.trans hsp]; exact isAligned8_add_int_mul8 sp hal (1 + (nl + 1))
  obtain ⟨st4, hrun2, hoth2, ht1_4, hmem2, hpc4⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre3 _ AbiReg.t1 AbiReg.sp AbiReg.t6
      (by decide) (by decide) (by decide) (slotOff (nl + 1)) hlink3
      (linkResolved_sub_pc64 env pre3 cl2 _ hlink3) st3 hpc3' halX1
  have hpres2 : PreservedRegs st3 st4 :=
    ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide)⟩
  let pre4 := pre3 ++ cl2
  have htwPre4 : lkm.totalSize pre4 = lkm.totalSize pre3 + lkm.totalSize cl2 := lkm.totalSize_append pre3 cl2
  have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre4) := by rw [hpc4, htwPre4]
  have hlink4 : lkm.linkSpec (pre4 ++ cl3 ++ (codeTail ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre4, List.append_assoc] using hlink3
  have halX4 : isAligned (st4.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff (nl + 4))) 8 = true := by
    rw [(hpres0_3.trans hpres2).sp.trans hsp]; exact isAligned8_add_int_mul8 sp hal (1 + (nl + 4))
  obtain ⟨st5, hrun3, hoth3, ht3_5, hmem3, hpc5⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre4 _ AbiReg.t3 AbiReg.sp AbiReg.t6
      (by decide) (by decide) (by decide) (slotOff (nl + 4)) hlink4
      (linkResolved_sub_pc64 env pre4 cl3 _ hlink4) st4 hpc4' halX4
  have hpres3 : PreservedRegs st4 st5 :=
    ⟨hoth3 _ (by decide) (by decide), hoth3 _ (by decide) (by decide), hoth3 _ (by decide) (by decide), hoth3 _ (by decide) (by decide)⟩
  have hpres0_5 : PreservedRegs st st5 := hpres0_3.trans (hpres2.trans hpres3)
  have hmem0_5 : st5.mem = st.mem := by rw [hmem3, hmem2, hmem0_3]
  have ht0Val : st5.getReg AbiReg.t0 = BitVec.ofNat 64 (lm.arr64 da).size := by
    rw [hoth3 _ (by decide) (by decide), hoth2 _ (by decide) (by decide), ht0_3, hmemT3, hmemT2, hmemT1, hmem0,
        ht5LenAddr, hlen64]
  have ht1Val : st5.getReg AbiReg.t1 = vdi.toBitVec := by
    rw [hoth3 _ (by decide) (by decide), ht1_4, hmem0_3, hpres0_3.sp.trans hsp, hslot1]
  have ht3Val : st5.getReg AbiReg.t3 = vk.toBitVec := by
    rw [ht3_5, hmem2, hmem0_3, (hpres0_3.trans hpres2).sp.trans hsp, hslot4]
  have ht5Keep : st5.getReg AbiReg.t5 = L.T + (if (u &&& 1 == 0) = true then 0#64 else 8#64) := by
    rw [hoth3 _ (by decide) (by decide), hoth2 _ (by decide) (by decide), hoth1 _ (by decide) (by decide), ht5Val]
  let pre5 := pre4 ++ cl3
  have htwPre5 : lkm.totalSize pre5 = lkm.totalSize pre4 + lkm.totalSize cl3 := lkm.totalSize_append pre4 cl3
  have hpc5' : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre5) := by rw [hpc5, htwPre5]
  have hlink5 : lkm.linkSpec (pre5 ++ codeTail ++ post) =
      .ok (env.code, env.labels) := by simpa [pre5, List.append_assoc] using hlink4
  have hchk := prog_warr_dst_check_sim env L lm a u vdi vk da hdaOk hOffBase pre5 codeTail post rfl
    st5 hpc5' (hmem0_5 ▸ hm) ht0Val ht1Val ht3Val ht5Keep hlink5
  have hrun0_5 := run_trans (run_trans (run_trans (run_trans (run_trans (run_trans hrun0 hrunT1) hrunT2) hrunT3) hrun1) hrun2) hrun3
  by_cases hbound : vdi.toNat + vk.toNat ≤ (lm.arr64 da).size
  · simp only [hbound, ↓reduceIte] at hchk ⊢
    obtain ⟨k, r', hrunR, hpcR, ht1R, ht3R, hmemR, hpresR⟩ := hchk
    have hpcEq : lkm.totalSize pre5 + lkm.totalSize codeTail = lkm.totalSize pre + lkm.totalSize codeSetup := by
      rw [htwPre5, htwPre4, htwPre3, htwPre2, htwPre1, hcode,
          lkm.totalSize_append ((((cl0 ++ ctp) ++ cl1) ++ cl2) ++ cl3) codeTail,
          lkm.totalSize_append (((cl0 ++ ctp) ++ cl1) ++ cl2) cl3,
          lkm.totalSize_append ((cl0 ++ ctp) ++ cl1) cl2,
          lkm.totalSize_append (cl0 ++ ctp) cl1,
          lkm.totalSize_append cl0 ctp, htwTp]; omega
    rw [hpcEq] at hpcR
    exact ⟨_, r', run_trans hrun0_5 hrunR, hpcR, ht1R, ht3R, hmemR.trans hmem0_5, hpres0_5.trans hpresR⟩
  · simp only [hbound, ↓reduceIte] at hchk ⊢
    obtain ⟨k, r', hrunR, hpcR, hpresR⟩ := hchk
    exact ⟨_, r', run_trans hrun0_5 hrunR, hpcR, hpres0_5.trans hpresR⟩

theorem copy64_loop_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (da sa : _root_.L.TieredArray) (hda : env.tab.wordPosOkB da = true) (hsa : env.tab.wordPosOkB sa = true)
    (loopLbl doneLbl : String) (loopTarget doneTarget : Nat)
    (hloopLbl : lookupLabel env.labels loopLbl = some loopTarget)
    (hdoneLbl : lookupLabel env.labels doneLbl = some doneTarget)
    (pre post : List AsmItem)
    (hltLoop : loopTarget = lkm.totalSize pre)
    (hlink : lkm.linkSpec (pre ++ [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
      Asm.ld AbiReg.t4 AbiReg.t2, Asm.sd AbiReg.t1 AbiReg.t4,
      Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 8#12,
      Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] ++ post) = .ok (env.code, env.labels)) :
    ∀ n (lm : _root_.L.Mem) (di si : _root_.L.Word) (st : State),
      st.pc = BitVec.ofNat 64 (4 * loopTarget) →
      st.getReg AbiReg.t1 = L.base64 da + BitVec.ofNat 64 (8 * di.toNat) →
      st.getReg AbiReg.t2 = L.base64 sa + BitVec.ofNat 64 (8 * si.toNat) →
      st.getReg AbiReg.t3 = BitVec.ofNat 64 n →
      di.toNat + n ≤ (lm.arr64 da).size →
      si.toNat + n ≤ (lm.arr64 sa).size →
      ProgMemRel env.tab L st.mem lm →
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * doneTarget) ∧
        PreservedRegs st r' ∧
        ProgMemRel env.tab L r'.mem (lm.copy64 da di sa si n) ∧
        MemEqOutside (L.arr64Span da) st.mem r'.mem := by
  intro n
  induction n with
  | zero =>
    intro lm di si st hpc ht1 ht2 ht3 hdi hsi hm
    have ⟨_, hl1⟩ := linkResolved_mid_split lkm pre [Asm.lbl loopLbl]
      [Asm.beq AbiReg.t3 AbiReg.zero doneLbl, Asm.ld AbiReg.t4 AbiReg.t2, Asm.sd AbiReg.t1 AbiReg.t4,
       Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 8#12,
       Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] post hlink
    have ⟨hlBeq, _⟩ := linkResolved_mid_split lkm (pre ++ [Asm.lbl loopLbl]) [Asm.beq AbiReg.t3 AbiReg.zero doneLbl] _ post hl1
    have hbr := run_br_step env (pre ++ [Asm.lbl loopLbl]) _ .beq AbiReg.t3 AbiReg.zero doneLbl doneTarget hdoneLbl (by decide)
      hlBeq st (by rw [lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero, ← hltLoop]; exact hpc)
    have hcond : evalBranch .beq (st.getReg AbiReg.t3) (st.getReg AbiReg.zero) = true := by
      rw [ht3, getReg_zero st]; decide
    obtain ⟨kBr, st', _, hrun, hpcBr, _, hpresBr, hmemBr⟩ := hbr
    have hpc' : st'.pc = BitVec.ofNat 64 (4 * doneTarget) := by rw [hpcBr, hcond]; rfl
    have hcopy : lm.copy64 da di sa si 0 = lm := by simp [_root_.L.Mem.copy64]
    rw [hcopy]
    exact ⟨kBr, st', hrun, hpc', hpresBr, by rw [hmemBr]; exact hm, fun a hc => by rw [hmemBr]⟩
  | succ n ih =>
    intro lm di si st hpc ht1 ht2 ht3 hdi hsi hm
    have hltLoopEq : lkm.totalSize (pre ++ [Asm.lbl loopLbl]) = loopTarget := by
      rw [lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero, hltLoop]
    have ⟨_, hlR0⟩ := linkResolved_mid_split lkm pre [Asm.lbl loopLbl] _ post hlink
    have ⟨hl1, hlR1⟩ := linkResolved_mid_split lkm (pre ++ [Asm.lbl loopLbl])
      [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]
      [Asm.ld AbiReg.t4 AbiReg.t2, Asm.sd AbiReg.t1 AbiReg.t4,
       Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 8#12,
       Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] post hlR0
    have ⟨hl2, hlR2⟩ := linkResolved_mid_split lkm ((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl])
      [Asm.ld AbiReg.t4 AbiReg.t2]
      [Asm.sd AbiReg.t1 AbiReg.t4, Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 8#12,
       Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] post hlR1
    have ⟨hl3, hlR3⟩ := linkResolved_mid_split lkm (((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.ld AbiReg.t4 AbiReg.t2])
      [Asm.sd AbiReg.t1 AbiReg.t4]
      [Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 8#12,
       Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] post hlR2
    have ⟨hl4, hlR4⟩ := linkResolved_mid_split lkm ((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.ld AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4])
      [Asm.addi AbiReg.t1 AbiReg.t1 8#12]
      [Asm.addi AbiReg.t2 AbiReg.t2 8#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] post hlR3
    have ⟨hl5, hlR5⟩ := linkResolved_mid_split lkm (((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.ld AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) ++ [Asm.addi AbiReg.t1 AbiReg.t1 8#12])
      [Asm.addi AbiReg.t2 AbiReg.t2 8#12]
      [Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] post hlR4
    have ⟨hl6, hlR6⟩ := linkResolved_mid_split lkm ((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.ld AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) ++ [Asm.addi AbiReg.t1 AbiReg.t1 8#12]) ++ [Asm.addi AbiReg.t2 AbiReg.t2 8#12])
      [Asm.addi AbiReg.t3 AbiReg.t3 (-1#12)] [Asm.j loopLbl, Asm.lbl doneLbl] post hlR5
    have ⟨hl7, _⟩ := linkResolved_mid_split lkm (((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.ld AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) ++ [Asm.addi AbiReg.t1 AbiReg.t1 8#12]) ++ [Asm.addi AbiReg.t2 AbiReg.t2 8#12]) ++ [Asm.addi AbiReg.t3 AbiReg.t3 (-1#12)])
      [Asm.j loopLbl] [Asm.lbl doneLbl] post hlR6
    rcases hm.2.1 da hda with ⟨hcapD, _, _, _, _⟩
    rcases hm.2.1 sa hsa with ⟨hcapS, hltS, _, _, hwordsS⟩
    have hnBound : n + 1 < 2 ^ 64 := by omega
    have hbr := run_br_step env (pre ++ [Asm.lbl loopLbl]) _ .beq AbiReg.t3 AbiReg.zero doneLbl doneTarget hdoneLbl (by decide)
      hl1 st (by rw [hltLoopEq]; exact hpc)
    have hcond : evalBranch .beq (st.getReg AbiReg.t3) (st.getReg AbiReg.zero) = false := by
      rw [ht3, getReg_zero st, evalBranch]
      exact beq_false_of_ne (BitVec.ofNat_ne_zero_of_lt (Nat.succ_pos n) hnBound)
    obtain ⟨kBr, st1, _, hrun1, hpc1Br, hoth1, hpres1, hmem1⟩ := hbr
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize ((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl])) := by
      rw [hpc1Br, hcond]; simp only [Bool.false_eq_true, ↓reduceIte, lkm.totalSize_append, Asm.beq, Asm.br, lkm.totalSize_singleton]
    have halSrc : isAligned (st1.getReg AbiReg.t2) 8 = true := by
      rw [hoth1 _ (by decide), ht2]
      exact isAligned8_add_mul8 _ (L.h64Align sa) si.toNat
    obtain ⟨hrun2, hpc2, ht4_2, hoth2, hmem2, hpres2⟩ :=
      run_ld_zero_step env _ _ AbiReg.t4 AbiReg.t2 nonPreserved_t4 hl2 st1 hpc1' halSrc
    let st2 := stepReg st1 AbiReg.t4 (readWord64 st1.mem (st1.getReg AbiReg.t2))
      (BitVec.ofNat 64 (4 * (lkm.totalSize ((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) + 1)))
    have halDst : isAligned (st2.getReg AbiReg.t1) 8 = true := by
      rw [hoth2 _ (by decide), hoth1 _ (by decide), ht1]
      exact isAligned8_add_mul8 _ (L.h64Align da) di.toNat
    have htwLd : lkm.totalSize [Asm.ld AbiReg.t4 AbiReg.t2] = 1 := by simp only [Asm.ld, lkm.totalSize_instr]
    have hrun3 := step_sd_zero env _ _ AbiReg.t1 AbiReg.t4 hl3 st2
      (by rw [lkm.totalSize_append, htwLd]; exact hpc2) halDst
    let st3 : State :=
      { pc := BitVec.ofNat 64 (4 * (lkm.totalSize (((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.ld AbiReg.t4 AbiReg.t2]) + 1))
      , regs := st2.regs
      , mem := writeWord64 st2.mem (st2.getReg AbiReg.t1) (st2.getReg AbiReg.t4) }
    have htwSd : lkm.totalSize [Asm.sd AbiReg.t1 AbiReg.t4] = 1 := by simp only [Asm.sd, lkm.totalSize_instr]
    obtain ⟨hrun4, hpc4, ht1_4, hoth4, hmem4, hpres4⟩ :=
      run_aluImm_step env _ _ .addi AbiReg.t1 AbiReg.t1 8#12 nonPreserved_t1 hl4 st3
        (by rw [lkm.totalSize_append, htwSd])
    let st4 := stepReg st3 AbiReg.t1 (evalAluImm .addi (st3.getReg AbiReg.t1) 8#12)
      (BitVec.ofNat 64 (4 * (lkm.totalSize ((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.ld AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) + 1)))
    have htwA1 : lkm.totalSize [Asm.addi AbiReg.t1 AbiReg.t1 8#12] = 1 := by simp only [Asm.addi, lkm.totalSize_instr]
    obtain ⟨hrun5, hpc5, ht2_5, hoth5, hmem5, hpres5⟩ :=
      run_aluImm_step env _ _ .addi AbiReg.t2 AbiReg.t2 8#12 nonPreserved_t2 hl5 st4
        (by rw [lkm.totalSize_append, htwA1]; exact hpc4)
    let st5 := stepReg st4 AbiReg.t2 (evalAluImm .addi (st4.getReg AbiReg.t2) 8#12)
      (BitVec.ofNat 64 (4 * (lkm.totalSize (((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.ld AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) ++ [Asm.addi AbiReg.t1 AbiReg.t1 8#12]) + 1)))
    have htwA2 : lkm.totalSize [Asm.addi AbiReg.t2 AbiReg.t2 8#12] = 1 := by simp only [Asm.addi, lkm.totalSize_instr]
    obtain ⟨hrun6, hpc6, ht3_6, hoth6, hmem6, hpres6⟩ :=
      run_aluImm_step env _ _ .addi AbiReg.t3 AbiReg.t3 (-1#12) nonPreserved_t3 hl6 st5
        (by rw [lkm.totalSize_append, htwA2]; exact hpc5)
    let st6 := stepReg st5 AbiReg.t3 (evalAluImm .addi (st5.getReg AbiReg.t3) (-1#12))
      (BitVec.ofNat 64 (4 * (lkm.totalSize ((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.ld AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) ++ [Asm.addi AbiReg.t1 AbiReg.t1 8#12]) ++ [Asm.addi AbiReg.t2 AbiReg.t2 8#12]) + 1)))
    have htwA3 : lkm.totalSize [Asm.addi AbiReg.t3 AbiReg.t3 (-1#12)] = 1 := by simp only [Asm.addi, lkm.totalSize_instr]
    have hpc64J : 4 * (lkm.totalSize (((((((pre ++ [Asm.lbl loopLbl]) ++ [Asm.beq AbiReg.t3 AbiReg.zero doneLbl]) ++ [Asm.ld AbiReg.t4 AbiReg.t2]) ++ [Asm.sd AbiReg.t1 AbiReg.t4]) ++ [Asm.addi AbiReg.t1 AbiReg.t1 8#12]) ++ [Asm.addi AbiReg.t2 AbiReg.t2 8#12]) ++ [Asm.addi AbiReg.t3 AbiReg.t3 (-1#12)]) + lkm.itemSize (.j loopLbl)) < 2 ^ 64 := by
      have h := linkResolved_sub_pc64 env _ [Asm.j loopLbl] _ hl7
      simpa [Asm.j, lkm.totalSize_singleton] using h
    obtain ⟨kJ, st7, hrun7, hpc7, hoth7, hpres7, hmem7⟩ :=
      prog_step_j env _ _ loopLbl loopTarget hloopLbl hl7 hpc64J st6
        (by rw [lkm.totalSize_append, htwA3]; exact hpc6)
    have ht4Val : st2.getReg AbiReg.t4 = (lm.arr64 sa)[si.toNat]!.toBitVec := by
      have hget : (lm.arr64 sa)[si.toNat]! = (lm.arr64 sa)[si.toNat]'(by omega) := getElem!_pos _ _ (by omega)
      rw [ht4_2, hget, hmem1]; change readWord64 st.mem (st1.getReg AbiReg.t2) = _
      rw [hoth1 _ (by decide), ht2]; exact hwordsS si.toNat (by omega)
    have ht1St2 : st2.getReg AbiReg.t1 = L.base64 da + BitVec.ofNat 64 (8 * di.toNat) := by
      rw [hoth2 _ (by decide), hoth1 _ (by decide)]; exact ht1
    have hst3Mem : st3.mem = writeWord64 st.mem (L.base64 da + BitVec.ofNat 64 (8 * di.toNat)) (lm.arr64 sa)[si.toNat]!.toBitVec := by
      dsimp only [st3]; rw [hmem2, hmem1, ht1St2, ht4Val]
    have hst7Mem : st7.mem = st3.mem := by rw [hmem7, hmem6, hmem5, hmem4]
    have hdi1 : (di + 1).toNat = di.toNat + 1 := by
      have := L.h64Valid da
      simp [UInt64.toNat_add, Nat.mod_eq_of_lt (show di.toNat + 1 < 2 ^ 64 by omega)]
    have hsi1 : (si + 1).toNat = si.toNat + 1 := by
      simp [UInt64.toNat_add, Nat.mod_eq_of_lt (show si.toNat + 1 < 2 ^ 64 by omega)]
    have h8eq : sextImm12 8#12 = BitVec.ofNat 64 8 := by decide
    have ht1_7 : st7.getReg AbiReg.t1 = L.base64 da + BitVec.ofNat 64 (8 * (di + 1).toNat) := by
      rw [hoth7 _ (by decide)]
      change st6.getReg AbiReg.t1 = _
      rw [hoth6 _ (by decide), hoth5 _ (by decide), ht1_4, evalAluImm]
      change st2.getReg AbiReg.t1 + sextImm12 8#12 = _
      rw [ht1St2, h8eq, BitVec.add_assoc, ← BitVec.ofNat_add, hdi1, show 8 * di.toNat + 8 = 8 * (di.toNat + 1) by omega]
    have ht2_7 : st7.getReg AbiReg.t2 = L.base64 sa + BitVec.ofNat 64 (8 * (si + 1).toNat) := by
      rw [hoth7 _ (by decide)]
      change st6.getReg AbiReg.t2 = _
      rw [hoth6 _ (by decide), ht2_5, evalAluImm]
      change st4.getReg AbiReg.t2 + sextImm12 8#12 = _
      rw [hoth4 _ (by decide), show st3.getReg AbiReg.t2 = st2.getReg AbiReg.t2 from rfl,
          hoth2 _ (by decide), hoth1 _ (by decide),
          ht2, h8eq, BitVec.add_assoc, ← BitVec.ofNat_add, hsi1, show 8 * si.toNat + 8 = 8 * (si.toNat + 1) by omega]
    have ht3_7 : st7.getReg AbiReg.t3 = BitVec.ofNat 64 n := by
      rw [hoth7 _ (by decide)]
      change st6.getReg AbiReg.t3 = _
      rw [ht3_6, evalAluImm]
      change st4.getReg AbiReg.t3 + sextImm12 (-1#12) = _
      rw [hoth4 _ (by decide), show st3.getReg AbiReg.t3 = st2.getReg AbiReg.t3 from rfl,
          hoth2 _ (by decide), hoth1 _ (by decide), ht3]
      exact BitVec.ofNat_sub_one_eq_add_neg1 hnBound
    let lm1 := lm.set64 da di (lm.arr64 sa)[si.toNat]!
    have hm1 : ProgMemRel env.tab L st7.mem lm1 := by
      rw [hst7Mem, hst3Mem]; exact ProgMemRel.set64 hm da hda di _ (by omega)
    have hdiSize : (di + 1).toNat + n ≤ (lm1.arr64 da).size := by
      rw [hdi1]; simp only [_root_.L.Mem.arr64] at hdi
      simp only [lm1, _root_.L.Mem.arr64, _root_.L.Mem.set64, ↓reduceIte, Array.size_set!]; omega
    have hsiSize : (si + 1).toNat + n ≤ (lm1.arr64 sa).size := by
      rw [hsi1]; simp only [_root_.L.Mem.arr64] at hsi
      by_cases hds : sa = da
      · subst hds; simp only [lm1, _root_.L.Mem.arr64, _root_.L.Mem.set64, ↓reduceIte, Array.size_set!]; omega
      · simp only [lm1, _root_.L.Mem.arr64, _root_.L.Mem.set64, hds, ↓reduceIte]; omega
    obtain ⟨kRest, stEnd, hrunRest, hpcEnd, hpresRest, hmEnd, hpmRest⟩ :=
      ih lm1 (di + 1) (si + 1) st7 hpc7
        ht1_7 ht2_7 ht3_7 hdiSize hsiSize hm1
    have hpmStep : MemEqOutside (L.arr64Span da) st.mem st7.mem := by
      rw [hst7Mem, hst3Mem]
      exact memEqOutside_writeWord64_arr64 L da di.toNat (Nat.lt_of_lt_of_le (by omega) hcapD) st.mem _
    have hpresStep : PreservedRegs st st7 :=
      hpres1.trans (hpres2.trans ((preservedRegs_of_regs rfl : PreservedRegs st2 st3).trans
        (hpres4.trans (hpres5.trans (hpres6.trans hpres7)))))
    have hcopyEq : lm.copy64 da di sa si (n + 1) = lm1.copy64 da (di + 1) sa (si + 1) n := rfl
    have hrunStep := run_trans (run_trans (run_trans (run_trans (run_trans (run_trans hrun1 hrun2) hrun3) hrun4) hrun5) hrun6) hrun7
    refine ⟨_, stEnd, run_trans hrunStep hrunRest, hpcEnd, hpresStep.trans hpresRest, ?_, hpmStep.trans hpmRest⟩
    · rw [hcopyEq]; exact hmEnd

theorem readWord64_slot_of_tempSpan {sp : BitVec 64} {nl j k nt : Nat}
    (hjk : j < k) (hk : k ≤ nt) (hvalid : sp.toNat + 8 * (1 + nl + nt) ≤ 2 ^ 64)
    {m1 m2 : ByteMem} (hout : MemEqOutside (tempSpan sp nl k nt) m1 m2) :
    readWord64 m2 (sp + BitVec.ofInt 64 (slotOff (nl + j))) =
      readWord64 m1 (sp + BitVec.ofInt 64 (slotOff (nl + j))) := by
  rw [slotOff_ofInt]
  exact MemEqOutside.readWord64_eq hout _ fun _ hm => tempSpan_slot_disjoint hjk hk hvalid hm

theorem bitvec_sub_ofNat_eq {a b : Nat} (ha : a < 2 ^ 64) (hle : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  have hb : b < 2 ^ 64 := by omega
  have hab : a - b < 2 ^ 64 := by omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hab]
  rw [show 2 ^ 64 - b + a = 2 ^ 64 + (a - b) by omega, Nat.add_mod_left, Nat.mod_eq_of_lt hab]

def warrTemps : _root_.L.WArr → Nat
  | .plain _ => 0
  | .tier _ t => maxTempsExpr t

theorem warr_pure (w : _root_.L.WArr) (st : _root_.L.St) :
    (∃ da, _root_.L.warr w st = .ok (da, st)) ∨ (_root_.L.warr w st = .error .oob) := by
  cases w with
  | plain a => left; exact ⟨a, rfl⟩
  | tier a t =>
    rcases _root_.L.evalE_pure t st with ⟨u, hok⟩ | herr
    · left; exact ⟨_root_.L.tierA a u, by simp [_root_.L.warr, Bind.bind, StateT.bind, Except.bind, hok, Pure.pure, Except.pure, StateT.pure]⟩
    · right; simp [_root_.L.warr, Bind.bind, StateT.bind, Except.bind, herr]

def copy64ArgsEval (d : _root_.L.WArr) (di : _root_.L.Expr) (s : _root_.L.WArr) (si n : _root_.L.Expr) :
    _root_.L.M (_root_.L.TieredArray × _root_.L.Word × _root_.L.TieredArray × _root_.L.Word × _root_.L.Word) := do
  let da ← _root_.L.warr d
  let vdi ← _root_.L.evalE di
  let sa ← _root_.L.warr s
  let vsi ← _root_.L.evalE si
  let vk ← _root_.L.evalE n
  pure (da, vdi, sa, vsi, vk)

def copy8wArgsEval (d : _root_.L.WArr) (di si n : _root_.L.Expr) :
    _root_.L.M (_root_.L.TieredArray × _root_.L.Word × _root_.L.Word × _root_.L.Word) := do
  let da ← _root_.L.warr d
  let vdi ← _root_.L.evalE di
  let vsi ← _root_.L.evalE si
  let vk ← _root_.L.evalE n
  pure (da, vdi, vsi, vk)

theorem eval_warr_to_temp_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl tmp nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (w : _root_.L.WArr) (hwOk : warrOkB env.tab nl w = true)
    (htmp : tmp + max 1 (warrTemps w) ≤ nt) (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ (evalWArrTierToTemp env.tab nl tmp w).2 ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOk L sp st.mem nl loc) :
    let daCode := evalWArrTierToTemp env.tab nl tmp w
    match _root_.L.warr w { mem := lm, loc := loc } with
    | .ok (da, _) =>
      ∃ k st' u,
        RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize daCode.2)) ∧
        da = _root_.L.tierA daCode.1 u ∧
        env.tab.wordPosOkB da = true ∧
        (L.T + (if (u &&& 1 == 0) = true then 0#64 else 8#64) +
            BitVec.ofInt 64 (env.tab.len64 (.t0 daCode.1)) =
            L.T + BitVec.ofInt 64 (env.tab.len64 da)) ∧
        (L.T + (if (u &&& 1 == 0) = true then 0#64 else 8#64) +
            BitVec.ofInt 64 (env.tab.base64 (.t0 daCode.1)) =
            L.T + BitVec.ofInt 64 (env.tab.base64 da)) ∧
        readWord64 st'.mem (sp + BitVec.ofInt 64 (slotOff (nl + tmp))) = u.toBitVec ∧
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
    dsimp only [evalWArrTierToTemp, _root_.L.warr, warrOkB, warrTemps] at hwOk htmp hlink ⊢
    have halX : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff (nl + tmp))) 8 = true := by
      rw [hsp]; exact isAligned8_add_int_mul8 sp hal (1 + (nl + tmp))
    have hpc64 := linkResolved_sub_pc64 env pre _ post hlink
    obtain ⟨st', hrun, hoth, hmem, hpc'⟩ :=
      storeMemOff_sd_correct_lm lkm env.hrom pre post AbiReg.sp AbiReg.zero AbiReg.t0
        (by decide) (by decide) (by decide) (slotOff (nl + tmp)) hlink hpc64 st hpc halX
    have hout : MemEqOutside (tempSpan sp nl tmp nt) st.mem st'.mem := by
      rw [hmem, hsp]
      exact MemEqOutside.writeWord64 _ _ _ fun k hk => by
        rw [slotOff_ofInt]; exact tempSpan_slot_sub (Nat.le_refl tmp) (by omega) k hk
    have h0eq : (0 : _root_.L.Word) &&& 1 = 0 := by decide
    have hta0 : _root_.L.tierA a 0 = .t0 a := by simp [_root_.L.tierA, h0eq]
    have hslot0 : readWord64 st'.mem (sp + BitVec.ofInt 64 (slotOff (nl + tmp))) = (0 : _root_.L.Word).toBitVec := by
      rw [hmem, hsp, getReg_zero]; exact readWord64_writeWord64_self _ _ _
    have hpres : PreservedRegs st st' :=
      ⟨hoth _ (by decide), hoth _ (by decide), hoth _ (by decide), hoth _ (by decide)⟩
    simp only [Pure.pure, Except.pure, StateT.pure]
    refine ⟨_, st', 0, hrun, hpc', hta0.symm, hwOk, ?_, ?_, hslot0, hpres, hout⟩
    · simp only [h0eq, beq_self_eq_true, ↓reduceIte, BitVec.add_zero]
    · simp only [h0eq, beq_self_eq_true, ↓reduceIte, BitVec.add_zero]
  | tier a t =>
    simp only [evalWArrTierToTemp, warrOkB, warrTemps, Bool.and_eq_true] at hwOk htmp hlink ⊢
    have hsim := prog_evalToTemp_sim env L lm loc hal hlim htop t hwOk.2 htmp pre post hlink st hpc hgp hsp hm hf
    cases he : _root_.L.evalE t { mem := lm, loc := loc } with
    | error err =>
      simp only [_root_.L.warr, Bind.bind, StateT.bind, Except.bind, he] at hsim ⊢; exact hsim
    | ok res =>
      rcases res with ⟨u, st1'⟩
      have hst1' : st1' = { mem := lm, loc := loc } := by
        rcases _root_.L.evalE_pure t { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
        · rw [he] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
        · rw [he] at herr; contradiction
      subst hst1'
      rw [he] at hsim
      obtain ⟨k, st', hrun, hpc', hslot, hpres, hout⟩ := hsim
      have hmini : _root_.L.warr (.tier a t) { mem := lm, loc := loc } = .ok (_root_.L.tierA a u, { mem := lm, loc := loc }) := by
        simp [_root_.L.warr, Bind.bind, StateT.bind, Except.bind, he, Pure.pure, Except.pure, StateT.pure]
      rw [hmini]
      have hta := tieredOk_len64_addr_T L.T a u hwOk.1
      exact ⟨k, st', u, hrun, hpc', rfl, hta.1, hta.2.1, hta.2.2, hslot, hpres, hout⟩

theorem prog_warr_src_tail_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (sa : _root_.L.TieredArray) (hsa : env.tab.wordPosOkB sa = true)
    (vsi vk : _root_.L.Word) (hbound : vsi.toNat + vk.toNat ≤ (lm.arr64 sa).size)
    (t1Val : BitVec 64) (pre5 codeTail post : List AsmItem)
    (hcTail : codeTail = loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (env.tab.base64 (.t0 sa.arr)) ++
      [Asm.slli AbiReg.t2 AbiReg.t2 3#6, Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2])
    (hlink5 : lkm.linkSpec (pre5 ++ codeTail ++ post) = .ok (env.code, env.labels))
    (st5 : State) (hpc5 : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre5))
    (ht1_5 : st5.getReg AbiReg.t1 = t1Val) (ht2_5 : st5.getReg AbiReg.t2 = vsi.toBitVec)
    (ht3_5 : st5.getReg AbiReg.t3 = vk.toBitVec)
    (ht5Base : st5.getReg AbiReg.t5 + BitVec.ofInt 64 (env.tab.base64 (.t0 sa.arr)) =
      L.T + BitVec.ofInt 64 (env.tab.base64 sa))
    (hm5 : ProgMemRel env.tab L st5.mem lm) :
    ∃ k r',
      RV64.run env.rom k st5 = .cont r' ∧
      r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre5 + lkm.totalSize codeTail)) ∧
      r'.getReg AbiReg.t1 = t1Val ∧
      r'.getReg AbiReg.t2 = L.base64 sa + BitVec.ofNat 64 (8 * vsi.toNat) ∧
      r'.getReg AbiReg.t3 = vk.toBitVec ∧
      r'.mem = st5.mem ∧
      PreservedRegs st5 r' := by
  let cl2 := loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (env.tab.base64 (.t0 sa.arr))
  let ctail := [Asm.slli AbiReg.t2 AbiReg.t2 3#6, Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2]
  have hcEq : codeTail = cl2 ++ ctail := by rw [hcTail]
  rw [hcEq] at hlink5
  have hlink5' : lkm.linkSpec (pre5 ++ cl2 ++ (ctail ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink5
  have halBase : isAligned (st5.getReg AbiReg.t5 + BitVec.ofInt 64 (env.tab.base64 (.t0 sa.arr))) 8 = true := by
    rw [ht5Base, Tab.base64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
  obtain ⟨st6, hrun5, hoth5, ht5_6, hmem5, hpc6⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre5 _ AbiReg.t5 AbiReg.t5 AbiReg.t6
      (by decide) (by decide) (by decide) (env.tab.base64 (.t0 sa.arr)) hlink5'
      (linkResolved_sub_pc64 env pre5 cl2 _ hlink5') st5 hpc5 halBase
  have hpres5 : PreservedRegs st5 st6 :=
    ⟨hoth5 _ (by decide) (by decide), hoth5 _ (by decide) (by decide), hoth5 _ (by decide) (by decide), hoth5 _ (by decide) (by decide)⟩
  let pre6 := pre5 ++ cl2
  have htwPre6 : lkm.totalSize pre6 = lkm.totalSize pre5 + lkm.totalSize cl2 := lkm.totalSize_append pre5 cl2
  have hpc6' : st6.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre6) := by rw [hpc6, htwPre6]
  have hlink6 : lkm.linkSpec (pre6 ++ ctail ++ post) =
      .ok (env.code, env.labels) := by simpa [pre6, List.append_assoc] using hlink5'
  have ⟨hlA, hlB⟩ := linkResolved_mid_split lkm pre6 [Asm.slli AbiReg.t2 AbiReg.t2 3#6]
    [Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2] post hlink6
  have htwA : lkm.totalSize [Asm.slli AbiReg.t2 AbiReg.t2 3#6] = 1 := by simp only [Asm.slli, lkm.totalSize_instr]
  let st7 := stepReg st6 AbiReg.t2 (evalShiftImm .slli (st6.getReg AbiReg.t2) 3#6)
    (BitVec.ofNat 64 (4 * (lkm.totalSize pre6 + 1)))
  obtain ⟨hrun6, hpc7, ht2_7, hoth6, hmem6, hpres6⟩ :=
    run_shImm_step env pre6 _ .slli AbiReg.t2 AbiReg.t2 3#6 nonPreserved_t2 hlA st6 hpc6'
  let st8 := stepReg st7 AbiReg.t2 (evalAlu .add (st7.getReg AbiReg.t5) (st7.getReg AbiReg.t2))
    (BitVec.ofNat 64 (4 * (lkm.totalSize (pre6 ++ [Asm.slli AbiReg.t2 AbiReg.t2 3#6]) + 1)))
  obtain ⟨hrun7, hpc8, ht2_8, hoth7, hmem7, hpres7⟩ :=
    run_alu_step env (pre6 ++ [Asm.slli AbiReg.t2 AbiReg.t2 3#6]) _ .add AbiReg.t2 AbiReg.t5 AbiReg.t2
      nonPreserved_t2 hlB st7 (by rw [lkm.totalSize_append, htwA]; exact hpc7)
  rcases hm5.2.1 sa hsa with ⟨_, hlt61, _, hbase64, _⟩
  have ht5_6v : st6.getReg AbiReg.t5 = L.base64 sa := by rw [ht5_6, ht5Base, hbase64]
  have ht2_8v : st8.getReg AbiReg.t2 = L.base64 sa + BitVec.ofNat 64 (8 * vsi.toNat) := by
    rw [ht2_8, evalAlu, hoth6 _ (by decide), ht5_6v, ht2_7,
        hoth5 _ (by decide) (by decide), ht2_5, shl3_ofNat_eq vsi (by omega)]
  have hpcEq : lkm.totalSize (pre6 ++ [Asm.slli AbiReg.t2 AbiReg.t2 3#6]) + 1 =
      lkm.totalSize pre5 + lkm.totalSize codeTail := by
    have htwt : lkm.totalSize ctail = 2 := by simp only [ctail, Asm.slli, Asm.add, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
    rw [lkm.totalSize_append, htwA, htwPre6, hcEq, lkm.totalSize_append cl2 ctail, htwt]; omega
  refine ⟨_, st8, run_trans hrun5 (run_trans hrun6 hrun7), by rw [hpc8, hpcEq],
    (hoth7 _ (by decide)).trans ((hoth6 _ (by decide)).trans ((hoth5 _ (by decide) (by decide)).trans ht1_5)),
    ht2_8v,
    (hoth7 _ (by decide)).trans ((hoth6 _ (by decide)).trans ((hoth5 _ (by decide) (by decide)).trans ht3_5)),
    by rw [hmem7, hmem6, hmem5],
    hpres5.trans (hpres6.trans hpres7)⟩

theorem prog_warr_src_head_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) {sp : BitVec 64} {nl : Nat} (hal : isAligned sp 8 = true)
    (sa : _root_.L.TieredArray) (hsa : env.tab.wordPosOkB sa = true)
    (vsi vk : _root_.L.Word) (t1Val : BitVec 64)
    (pre codeHead post : List AsmItem)
    (hcHead : codeHead =
      loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (env.tab.len64 (.t0 sa.arr)) ++
      loadMemOff .ld AbiReg.t2 AbiReg.sp AbiReg.t6 (slotOff (nl + 3)))
    (hlink : lkm.linkSpec (pre ++ codeHead ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hsp : st.getReg AbiReg.sp = sp) (hm : ProgMemRel env.tab L st.mem lm)
    (ht1 : st.getReg AbiReg.t1 = t1Val) (ht3 : st.getReg AbiReg.t3 = vk.toBitVec)
    (ht5Len : st.getReg AbiReg.t5 + BitVec.ofInt 64 (env.tab.len64 (.t0 sa.arr)) =
      L.T + BitVec.ofInt 64 (env.tab.len64 sa))
    (hslot3 : readWord64 st.mem (sp + BitVec.ofInt 64 (slotOff (nl + 3))) = vsi.toBitVec) :
    ∃ k st2,
      RV64.run env.rom k st = .cont st2 ∧
      st2.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize codeHead)) ∧
      st2.getReg AbiReg.t0 = BitVec.ofNat 64 (lm.arr64 sa).size ∧
      st2.getReg AbiReg.t1 = t1Val ∧
      st2.getReg AbiReg.t2 = vsi.toBitVec ∧
      st2.getReg AbiReg.t3 = vk.toBitVec ∧
      st2.getReg AbiReg.t5 = st.getReg AbiReg.t5 ∧
      st2.mem = st.mem ∧
      PreservedRegs st st2 := by
  let cl0 := loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (env.tab.len64 (.t0 sa.arr))
  let cl1 := loadMemOff .ld AbiReg.t2 AbiReg.sp AbiReg.t6 (slotOff (nl + 3))
  have hcEq : codeHead = cl0 ++ cl1 := hcHead
  rw [hcEq] at hlink
  have hlink0 : lkm.linkSpec (pre ++ cl0 ++ (cl1 ++ post)) = .ok (env.code, env.labels) := by
    simpa [List.append_assoc] using hlink
  have halLen : isAligned (st.getReg AbiReg.t5 + BitVec.ofInt 64 (env.tab.len64 (.t0 sa.arr))) 8 = true := by
    rw [ht5Len, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
  obtain ⟨st1, hrun0, hoth0, ht0_1, hmem0, hpc1⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre _ AbiReg.t0 AbiReg.t5 AbiReg.t6
      (by decide) (by decide) (by decide) (env.tab.len64 (.t0 sa.arr)) hlink0
      (linkResolved_sub_pc64 env pre cl0 _ hlink0) st hpc halLen
  let pre1 := pre ++ cl0
  have htwPre1 : lkm.totalSize pre1 = lkm.totalSize pre + lkm.totalSize cl0 := lkm.totalSize_append pre cl0
  have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by rw [hpc1, htwPre1]
  have hlink1 : lkm.linkSpec (pre1 ++ cl1 ++ post) = .ok (env.code, env.labels) := by
    simpa [pre1, List.append_assoc] using hlink0
  have halS3 : isAligned (st1.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff (nl + 3))) 8 = true := by
    rw [hoth0 _ (by decide) (by decide), hsp]; exact isAligned8_add_int_mul8 sp hal (1 + (nl + 3))
  obtain ⟨st2, hrun1, hoth1, ht2_2, hmem1, hpc2⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre1 _ AbiReg.t2 AbiReg.sp AbiReg.t6
      (by decide) (by decide) (by decide) (slotOff (nl + 3)) hlink1
      (linkResolved_sub_pc64 env pre1 cl1 _ hlink1) st1 hpc1' halS3
  rcases hm.2.1 sa hsa with ⟨_, _, hlen64, _, _⟩
  refine ⟨_, st2, run_trans hrun0 hrun1,
    by rw [hpc2, hcEq, htwPre1, lkm.totalSize_append cl0 cl1, Nat.add_assoc],
    by rw [hoth1 _ (by decide) (by decide), ht0_1, ht5Len, hlen64],
    (hoth1 _ (by decide) (by decide)).trans ((hoth0 _ (by decide) (by decide)).trans ht1),
    by rw [ht2_2, hmem0, hoth0 _ (by decide) (by decide), hsp, hslot3],
    (hoth1 _ (by decide) (by decide)).trans ((hoth0 _ (by decide) (by decide)).trans ht3),
    (hoth1 _ (by decide) (by decide)).trans (hoth0 _ (by decide) (by decide)),
    hmem1.trans hmem0,
    ⟨((hoth1 _ (by decide) (by decide)).trans (hoth0 _ (by decide) (by decide))),
     ((hoth1 _ (by decide) (by decide)).trans (hoth0 _ (by decide) (by decide))),
     ((hoth1 _ (by decide) (by decide)).trans (hoth0 _ (by decide) (by decide))),
     ((hoth1 _ (by decide) (by decide)).trans (hoth0 _ (by decide) (by decide)))⟩⟩

theorem prog_warr_src_check_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) {sp : BitVec 64} {nl : Nat} (hal : isAligned sp 8 = true)
    (sa : _root_.L.TieredArray) (hsa : env.tab.wordPosOkB sa = true)
    (vsi vk : _root_.L.Word) (t1Val : BitVec 64)
    (pre codeCheck post : List AsmItem)
    (hcodeCheck : codeCheck =
      loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (env.tab.len64 (.t0 sa.arr)) ++
      loadMemOff .ld AbiReg.t2 AbiReg.sp AbiReg.t6 (slotOff (nl + 3)) ++
      [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3, Asm.bltu AbiReg.t0 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (env.tab.base64 (.t0 sa.arr)) ++
      [Asm.slli AbiReg.t2 AbiReg.t2 3#6, Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2])
    (hlink : lkm.linkSpec (pre ++ codeCheck ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hsp : st.getReg AbiReg.sp = sp) (hm : ProgMemRel env.tab L st.mem lm)
    (ht1 : st.getReg AbiReg.t1 = t1Val) (ht3 : st.getReg AbiReg.t3 = vk.toBitVec)
    (ht5Len : st.getReg AbiReg.t5 + BitVec.ofInt 64 (env.tab.len64 (.t0 sa.arr)) =
      L.T + BitVec.ofInt 64 (env.tab.len64 sa))
    (ht5Base : st.getReg AbiReg.t5 + BitVec.ofInt 64 (env.tab.base64 (.t0 sa.arr)) =
      L.T + BitVec.ofInt 64 (env.tab.base64 sa))
    (hslot3 : readWord64 st.mem (sp + BitVec.ofInt 64 (slotOff (nl + 3))) = vsi.toBitVec) :
    if vsi.toNat + vk.toNat ≤ (lm.arr64 sa).size then
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize codeCheck)) ∧
        r'.getReg AbiReg.t1 = t1Val ∧
        r'.getReg AbiReg.t2 = L.base64 sa + BitVec.ofNat 64 (8 * vsi.toNat) ∧
        r'.getReg AbiReg.t3 = vk.toBitVec ∧
        r'.mem = st.mem ∧
        PreservedRegs st r'
    else
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st r' := by
  let cl0 := loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (env.tab.len64 (.t0 sa.arr))
  let cl1 := loadMemOff .ld AbiReg.t2 AbiReg.sp AbiReg.t6 (slotOff (nl + 3))
  let cb0 := [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel]
  let cs0 := [Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3]
  let cb1 := [Asm.bltu AbiReg.t0 AbiReg.t2 errLabel]
  let cl2 := loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (env.tab.base64 (.t0 sa.arr))
  let ctail := [Asm.slli AbiReg.t2 AbiReg.t2 3#6, Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2]
  have hcEq : codeCheck = (cl0 ++ cl1) ++ cb0 ++ cs0 ++ cb1 ++ (cl2 ++ ctail) := by
    rw [hcodeCheck]; simp [cl0, cl1, cb0, cs0, cb1, cl2, ctail, List.append_assoc]
  rw [hcEq] at hlink
  have hlink0 : lkm.linkSpec (pre ++ (cl0 ++ cl1) ++ (cb0 ++ cs0 ++ cb1 ++ (cl2 ++ ctail) ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
  obtain ⟨k01, st2, hrun01, hpc2, ht0_2, ht1_2, ht2Val, ht3_2, ht5_2, hmem01, hpres01⟩ :=
    prog_warr_src_head_sim env L lm hal sa hsa vsi vk t1Val pre (cl0 ++ cl1) _ rfl hlink0
      st hpc hsp hm ht1 ht3 ht5Len hslot3
  let pre2 := pre ++ (cl0 ++ cl1)
  have htwPre2 : lkm.totalSize pre2 = lkm.totalSize pre + lkm.totalSize (cl0 ++ cl1) := lkm.totalSize_append pre (cl0 ++ cl1)
  have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) := by rw [hpc2, htwPre2]
  have hlink2 : lkm.linkSpec (pre2 ++ cb0 ++ (cs0 ++ cb1 ++ (cl2 ++ ctail) ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre2, List.append_assoc] using hlink0
  rcases hm.2.1 sa hsa with ⟨_, hlt61, _, _, _⟩
  have hbr0 := run_br_step env pre2 _ .bltu AbiReg.t0 AbiReg.t3 errLabel env.errTarget env.herrLbl (by decide) hlink2 st2 hpc2'
  have hcond0 : evalBranch .bltu (st2.getReg AbiReg.t0) (st2.getReg AbiReg.t3) =
      decide ((lm.arr64 sa).size < vk.toNat) := by
    rw [ht0_2, ht3_2, u64_toBitVec_eq_ofNat]; exact evalBranch_bltu_nat (by omega) vk.toBitVec.isLt
  obtain ⟨kBr0, st3, _, hrun2, hpcBr0, hoth2Br, hpres2Br, hmem2Br⟩ := hbr0
  by_cases hkn : vk.toNat ≤ (lm.arr64 sa).size
  · have hbr0F : evalBranch .bltu (st2.getReg AbiReg.t0) (st2.getReg AbiReg.t3) = false := by
      rw [hcond0, decide_eq_false_iff_not]; omega
    let pre3 := pre2 ++ cb0
    have htwPre3 : lkm.totalSize pre3 = lkm.totalSize pre2 + lkm.totalSize cb0 :=
      lkm.totalSize_append pre2 cb0
    have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre3) := by
      rw [hpcBr0, hbr0F]; simp only [Bool.false_eq_true, ↓reduceIte, htwPre3, cb0, Asm.bltu, Asm.br, lkm.totalSize_singleton]
    have hlink3 : lkm.linkSpec (pre3 ++ cs0 ++ (cb1 ++ (cl2 ++ ctail) ++ post)) =
        .ok (env.code, env.labels) := by simpa [pre3, List.append_assoc] using hlink2
    let st4 := stepReg st3 AbiReg.t0 (evalAlu .sub (st3.getReg AbiReg.t0) (st3.getReg AbiReg.t3))
      (BitVec.ofNat 64 (4 * (lkm.totalSize pre3 + 1)))
    obtain ⟨hrun3, hpc4, ht0_4, hoth3, hmem3, hpres3⟩ :=
      run_alu_step env pre3 _ .sub AbiReg.t0 AbiReg.t0 AbiReg.t3 nonPreserved_t0 hlink3 st3 hpc3'
    have ht0_4v : st4.getReg AbiReg.t0 = BitVec.ofNat 64 ((lm.arr64 sa).size - vk.toNat) := by
      rw [ht0_4, evalAlu, hoth2Br _ (by decide), hoth2Br _ (by decide)]
      change st2.getReg AbiReg.t0 - st2.getReg AbiReg.t3 = _
      rw [ht0_2, ht3_2, u64_toBitVec_eq_ofNat]; exact bitvec_sub_ofNat_eq (by omega) hkn
    let pre4 := pre3 ++ cs0
    have htwPre4 : lkm.totalSize pre4 = lkm.totalSize pre3 + 1 := by
      have htws : lkm.totalSize cs0 = 1 := by simp only [cs0, Asm.sub, lkm.totalSize_instr]
      rw [lkm.totalSize_append, htws]
    have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre4) := by rw [hpc4, htwPre4]
    have hlink4 : lkm.linkSpec (pre4 ++ cb1 ++ ((cl2 ++ ctail) ++ post)) =
        .ok (env.code, env.labels) := by simpa [pre4, List.append_assoc] using hlink3
    have hbr1 := run_br_step env pre4 _ .bltu AbiReg.t0 AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide) hlink4 st4 hpc4'
    have hcond1 : evalBranch .bltu (st4.getReg AbiReg.t0) (st4.getReg AbiReg.t2) =
        decide ((lm.arr64 sa).size - vk.toNat < vsi.toNat) := by
      rw [ht0_4v, hoth3 _ (by decide), hoth2Br _ (by decide), ht2Val, u64_toBitVec_eq_ofNat]
      exact evalBranch_bltu_nat (by omega) vsi.toBitVec.isLt
    obtain ⟨kBr1, st5, _, hrun4, hpcBr1, hoth4Br, hpres4Br, hmem4Br⟩ := hbr1
    by_cases hdi : vsi.toNat ≤ (lm.arr64 sa).size - vk.toNat
    · have hbound : vsi.toNat + vk.toNat ≤ (lm.arr64 sa).size := by omega
      simp only [hbound, ↓reduceIte]
      have hbr1F : evalBranch .bltu (st4.getReg AbiReg.t0) (st4.getReg AbiReg.t2) = false := by
        rw [hcond1, decide_eq_false_iff_not]; omega
      let pre5 := pre4 ++ cb1
      have htwPre5 : lkm.totalSize pre5 = lkm.totalSize pre4 + lkm.totalSize cb1 :=
        lkm.totalSize_append pre4 cb1
      have hpc5' : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre5) := by
        rw [hpcBr1, hbr1F]; simp only [Bool.false_eq_true, ↓reduceIte, htwPre5, cb1, Asm.bltu, Asm.br, lkm.totalSize_singleton]
      have hlink5 : lkm.linkSpec (pre5 ++ (cl2 ++ ctail) ++ post) =
          .ok (env.code, env.labels) := by simpa [pre5, List.append_assoc] using hlink4
      have hmem5 : st5.mem = st.mem := hmem4Br.trans (hmem3.trans (hmem2Br.trans hmem01))
      have ht5_5 : st5.getReg AbiReg.t5 = st.getReg AbiReg.t5 :=
        (hoth4Br _ (by decide)).trans ((hoth3 _ (by decide)).trans ((hoth2Br _ (by decide)).trans ht5_2))
      obtain ⟨kTail, r', hrunTail, hpcR', ht1R, ht2R, ht3R, hmemR, hpresTail⟩ :=
        prog_warr_src_tail_sim env L lm sa hsa vsi vk hbound t1Val pre5 (cl2 ++ ctail) post rfl hlink5
          st5 hpc5' ((hoth4Br _ (by decide)).trans ((hoth3 _ (by decide)).trans ((hoth2Br _ (by decide)).trans ht1_2)))
          ((hoth4Br _ (by decide)).trans ((hoth3 _ (by decide)).trans ((hoth2Br _ (by decide)).trans ht2Val)))
          ((hoth4Br _ (by decide)).trans ((hoth3 _ (by decide)).trans ((hoth2Br _ (by decide)).trans ht3_2)))
          (by rw [ht5_5, ht5Base]) (hmem5 ▸ hm)
      have hpcEq : lkm.totalSize pre5 + lkm.totalSize (cl2 ++ ctail) = lkm.totalSize pre + lkm.totalSize codeCheck := by
        have htws0 : lkm.totalSize cs0 = 1 := by simp only [cs0, Asm.sub, lkm.totalSize_instr]
        rw [htwPre5, htwPre4, htwPre3, htwPre2, hcEq,
            lkm.totalSize_append ((((cl0 ++ cl1) ++ cb0) ++ cs0) ++ cb1) (cl2 ++ ctail),
            lkm.totalSize_append (((cl0 ++ cl1) ++ cb0) ++ cs0) cb1,
            lkm.totalSize_append ((cl0 ++ cl1) ++ cb0) cs0,
            lkm.totalSize_append (cl0 ++ cl1) cb0, htws0]; omega
      refine ⟨_, r', run_trans (run_trans (run_trans hrun01 hrun2) hrun3) (run_trans hrun4 hrunTail),
        by rw [hpcR', hpcEq], ht1R, ht2R, ht3R, hmemR.trans hmem5, ?_⟩
      exact hpres01.trans (hpres2Br.trans (hpres3.trans (hpres4Br.trans hpresTail)))
    · have hbound : ¬(vsi.toNat + vk.toNat ≤ (lm.arr64 sa).size) := by omega
      simp only [hbound, ↓reduceIte]
      have hbr1T : evalBranch .bltu (st4.getReg AbiReg.t0) (st4.getReg AbiReg.t2) = true := by
        rw [hcond1, decide_eq_true_iff]; omega
      have hpcT : st5.pc = BitVec.ofNat 64 (4 * env.errTarget) := by rw [hpcBr1, hbr1T]; rfl
      exact ⟨_, st5, run_trans (run_trans (run_trans hrun01 hrun2) hrun3) hrun4, hpcT,
        hpres01.trans (hpres2Br.trans (hpres3.trans hpres4Br))⟩
  · have hbound : ¬(vsi.toNat + vk.toNat ≤ (lm.arr64 sa).size) := by omega
    simp only [hbound, ↓reduceIte]
    have hbr0T : evalBranch .bltu (st2.getReg AbiReg.t0) (st2.getReg AbiReg.t3) = true := by
      rw [hcond0, decide_eq_true_iff]; omega
    have hpcT : st3.pc = BitVec.ofNat 64 (4 * env.errTarget) := by rw [hpcBr0, hbr0T]; rfl
    exact ⟨_, st3, run_trans hrun01 hrun2, hpcT, hpres01.trans hpres2Br⟩

theorem prog_warr_src_setup_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) {sp : BitVec 64} {nl : Nat} (hal : isAligned sp 8 = true)
    (sa : _root_.L.TieredArray) (su vsi vk : _root_.L.Word) (hsa : env.tab.wordPosOkB sa = true)
    (t1Val : BitVec 64)
    (hOffLen : L.T + (if (su &&& 1 == 0) = true then 0#64 else 8#64) +
        BitVec.ofInt 64 (env.tab.len64 (.t0 sa.arr)) =
        L.T + BitVec.ofInt 64 (env.tab.len64 sa))
    (hOffBase : L.T + (if (su &&& 1 == 0) = true then 0#64 else 8#64) +
        BitVec.ofInt 64 (env.tab.base64 (.t0 sa.arr)) =
        L.T + BitVec.ofInt 64 (env.tab.base64 sa))
    (pre codeSetup post : List AsmItem)
    (hcodeSetup : codeSetup =
      loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t2 (slotOff (nl + 2)) ++
      [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] ++
      loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (env.tab.len64 (.t0 sa.arr)) ++
      loadMemOff .ld AbiReg.t2 AbiReg.sp AbiReg.t6 (slotOff (nl + 3)) ++
      [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3, Asm.bltu AbiReg.t0 AbiReg.t2 errLabel] ++
      loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (env.tab.base64 (.t0 sa.arr)) ++
      [Asm.slli AbiReg.t2 AbiReg.t2 3#6, Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2])
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm)
    (ht1 : st.getReg AbiReg.t1 = t1Val) (ht3 : st.getReg AbiReg.t3 = vk.toBitVec)
    (hslot2 : readWord64 st.mem (sp + BitVec.ofInt 64 (slotOff (nl + 2))) = su.toBitVec)
    (hslot3 : readWord64 st.mem (sp + BitVec.ofInt 64 (slotOff (nl + 3))) = vsi.toBitVec)
    (hlink : lkm.linkSpec (pre ++ codeSetup ++ post) = .ok (env.code, env.labels)) :
    if vsi.toNat + vk.toNat ≤ (lm.arr64 sa).size then
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize codeSetup)) ∧
        r'.getReg AbiReg.t1 = t1Val ∧
        r'.getReg AbiReg.t2 = L.base64 sa + BitVec.ofNat 64 (8 * vsi.toNat) ∧
        r'.getReg AbiReg.t3 = vk.toBitVec ∧
        r'.mem = st.mem ∧
        PreservedRegs st r'
    else
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st r' := by
  let cl0 := loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t2 (slotOff (nl + 2))
  let ctp := [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0]
  let codeCheck :=
    loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (env.tab.len64 (.t0 sa.arr)) ++
    loadMemOff .ld AbiReg.t2 AbiReg.sp AbiReg.t6 (slotOff (nl + 3)) ++
    [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3, Asm.bltu AbiReg.t0 AbiReg.t2 errLabel] ++
    loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (env.tab.base64 (.t0 sa.arr)) ++
    [Asm.slli AbiReg.t2 AbiReg.t2 3#6, Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2]
  have hcEq : codeSetup = cl0 ++ ctp ++ codeCheck := by
    rw [hcodeSetup]; simp [cl0, ctp, codeCheck, List.append_assoc]
  rw [hcEq] at hlink
  have hlink0 : lkm.linkSpec (pre ++ cl0 ++ (ctp ++ codeCheck ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
  have hal2 : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff (nl + 2))) 8 = true := by
    rw [hsp]; exact isAligned8_add_int_mul8 sp hal (1 + (nl + 2))
  obtain ⟨st1, hrun0, hoth0, ht0_1, hmem0, hpc1⟩ :=
    loadMemOff_ld_correct_lm lkm env.hrom pre _ AbiReg.t0 AbiReg.sp AbiReg.t2
      (by decide) (by decide) (by decide) (slotOff (nl + 2)) hlink0
      (linkResolved_sub_pc64 env pre cl0 _ hlink0) st hpc hal2
  let pre1 := pre ++ cl0
  have htwPre1 : lkm.totalSize pre1 = lkm.totalSize pre + lkm.totalSize cl0 := lkm.totalSize_append pre cl0
  have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by rw [hpc1, htwPre1]
  have hlink1 : lkm.linkSpec (pre1 ++ ctp ++ (codeCheck ++ post)) =
      .ok (env.code, env.labels) := by simpa [pre1, List.append_assoc] using hlink0
  have ⟨hlT1, hlT23⟩ := linkResolved_mid_split lkm pre1 [Asm.andi AbiReg.t0 AbiReg.t0 1#12]
    [Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] _ hlink1
  have ⟨hlT2, hlT3⟩ := linkResolved_mid_split lkm (pre1 ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12])
    [Asm.slli AbiReg.t0 AbiReg.t0 3#6] [Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] _ hlT23
  have htw1 : lkm.totalSize [Asm.andi AbiReg.t0 AbiReg.t0 1#12] = 1 := by simp only [Asm.andi, lkm.totalSize_instr]
  have htw2 : lkm.totalSize [Asm.slli AbiReg.t0 AbiReg.t0 3#6] = 1 := by simp only [Asm.slli, lkm.totalSize_instr]
  let st1a := stepReg st1 AbiReg.t0 (evalAluImm .andi (st1.getReg AbiReg.t0) 1#12)
    (BitVec.ofNat 64 (4 * (lkm.totalSize pre1 + 1)))
  obtain ⟨hrunT1, hpcT1, ht0_T1, hothT1, hmemT1, hpresT1⟩ :=
    run_aluImm_step env pre1 _ .andi AbiReg.t0 AbiReg.t0 1#12 nonPreserved_t0 hlT1 st1 hpc1'
  let st1b := stepReg st1a AbiReg.t0 (evalShiftImm .slli (st1a.getReg AbiReg.t0) 3#6)
    (BitVec.ofNat 64 (4 * (lkm.totalSize (pre1 ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12]) + 1)))
  obtain ⟨hrunT2, hpcT2, ht0_T2, hothT2, hmemT2, hpresT2⟩ :=
    run_shImm_step env (pre1 ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12]) _ .slli AbiReg.t0 AbiReg.t0 3#6 nonPreserved_t0 hlT2 st1a
      (by rw [lkm.totalSize_append, htw1]; exact hpcT1)
  let st2 := stepReg st1b AbiReg.t5 (evalAlu .add (st1b.getReg AbiReg.gp) (st1b.getReg AbiReg.t0))
    (BitVec.ofNat 64 (4 * (lkm.totalSize ((pre1 ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12]) ++ [Asm.slli AbiReg.t0 AbiReg.t0 3#6]) + 1)))
  obtain ⟨hrunT3, hpc2, ht5_2, hothT3, hmemT3, hpresT3⟩ :=
    run_alu_step env ((pre1 ++ [Asm.andi AbiReg.t0 AbiReg.t0 1#12]) ++ [Asm.slli AbiReg.t0 AbiReg.t0 3#6]) _
      .add AbiReg.t5 AbiReg.gp AbiReg.t0 nonPreserved_t5 hlT3 st1b
      (by rw [lkm.totalSize_append, htw2]; exact hpcT2)
  have hpres0 : PreservedRegs st st1 :=
    ⟨hoth0 _ (by decide) (by decide), hoth0 _ (by decide) (by decide), hoth0 _ (by decide) (by decide), hoth0 _ (by decide) (by decide)⟩
  have ht5Val : st2.getReg AbiReg.t5 = L.T + (if (su &&& 1 == 0) = true then 0#64 else 8#64) := by
    have ht0_1eq : st1.getReg AbiReg.t0 = su.toBitVec := by rw [ht0_1, hsp, hslot2]
    rw [ht5_2, evalAlu, (hpresT1.trans hpresT2).gp.trans (hpres0.gp.trans hgp), ht0_T2, ht0_T1, ht0_1eq, tier_off_val su]
  have htwTp : lkm.totalSize ctp = 3 := by
    simp only [ctp, Asm.andi, Asm.slli, Asm.add, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
  let pre2 := pre1 ++ ctp
  have htwPre2 : lkm.totalSize pre2 = lkm.totalSize pre1 + 3 := by rw [lkm.totalSize_append, htwTp]
  have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) := by
    rw [hpc2, htwPre2, lkm.totalSize_append, lkm.totalSize_append, htw1, htw2, Nat.add_assoc]
  have hlink2 : lkm.linkSpec (pre2 ++ codeCheck ++ post) =
      .ok (env.code, env.labels) := by simpa [pre2, List.append_assoc] using hlink1
  have hmem02 : st2.mem = st.mem := hmemT3.trans (hmemT2.trans (hmemT1.trans hmem0))
  have ht1_2 : st2.getReg AbiReg.t1 = t1Val :=
    (hothT3 _ (by decide)).trans ((hothT2 _ (by decide)).trans ((hothT1 _ (by decide)).trans ((hoth0 _ (by decide) (by decide)).trans ht1)))
  have ht3_2 : st2.getReg AbiReg.t3 = vk.toBitVec :=
    (hothT3 _ (by decide)).trans ((hothT2 _ (by decide)).trans ((hothT1 _ (by decide)).trans ((hoth0 _ (by decide) (by decide)).trans ht3)))
  have hchk := prog_warr_src_check_sim env L lm hal sa hsa vsi vk t1Val pre2 codeCheck post rfl hlink2 st2 hpc2'
    (hpresT3.sp.trans (hpresT2.sp.trans (hpresT1.sp.trans (hpres0.sp.trans hsp))))
    (hmem02 ▸ hm) ht1_2 ht3_2 (by rw [ht5Val, hOffLen]) (by rw [ht5Val, hOffBase]) (by rw [hmem02, hslot3])
  have hrun0_2 := run_trans hrun0 (run_trans (run_trans hrunT1 hrunT2) hrunT3)
  have hpres0_2 := hpres0.trans (hpresT1.trans (hpresT2.trans hpresT3))
  by_cases hbound : vsi.toNat + vk.toNat ≤ (lm.arr64 sa).size
  · simp only [hbound, ↓reduceIte] at hchk ⊢
    obtain ⟨k, r', hrunR, hpcR, ht1R, ht2R, ht3R, hmemR, hpresR⟩ := hchk
    have hpcEq : lkm.totalSize pre2 + lkm.totalSize codeCheck = lkm.totalSize pre + lkm.totalSize codeSetup := by
      rw [htwPre2, htwPre1, hcEq, lkm.totalSize_append (cl0 ++ ctp) codeCheck, lkm.totalSize_append cl0 ctp, htwTp]; omega
    rw [hpcEq] at hpcR
    exact ⟨_, r', run_trans hrun0_2 hrunR, hpcR, ht1R, ht2R, ht3R, hmemR.trans hmem02, hpres0_2.trans hpresR⟩
  · simp only [hbound, ↓reduceIte] at hchk ⊢
    obtain ⟨k, r', hrunR, hpcR, hpresR⟩ := hchk
    exact ⟨_, r', run_trans hrun0_2 hrunR, hpcR, hpres0_2.trans hpresR⟩

theorem prog_copy64_args_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (d : _root_.L.WArr) (di : _root_.L.Expr) (s : _root_.L.WArr) (si n : _root_.L.Expr)
    (hdOk : warrOkB env.tab nl d = true) (hdiOk : exprOkB env.tab nl di = true)
    (hsOk : warrOkB env.tab nl s = true) (hsiOk : exprOkB env.tab nl si = true)
    (hnOk : exprOkB env.tab nl n = true)
    (hnt : max (warrTemps d) (max (1 + maxTempsExpr di)
      (max (match s with | .plain _ => 0 | .tier _ t => 2 + maxTempsExpr t)
      (max (3 + maxTempsExpr si) (4 + max 1 (maxTempsExpr n))))) ≤ nt)
    (pre codeArgs post : List AsmItem)
    (hcodeArgs : codeArgs =
      (evalWArrTierToTemp env.tab nl 0 d).2 ++
      (compileE env.tab nl 1 di ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 1))) ++
      (evalWArrTierToTemp env.tab nl 2 s).2 ++
      (compileE env.tab nl 3 si ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 3))) ++
      (compileE env.tab nl 4 n ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 4))))
    (hlink : lkm.linkSpec (pre ++ codeArgs ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOk L sp st.mem nl loc) :
    let dArr := (evalWArrTierToTemp env.tab nl 0 d).1
    let sArr := (evalWArrTierToTemp env.tab nl 2 s).1
    match copy64ArgsEval d di s si n { mem := lm, loc := loc } with
    | .ok ((da, vdi, sa, vsi, vk), _) =>
      ∃ k st' du su,
        RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize codeArgs)) ∧
        da = _root_.L.tierA dArr du ∧ sa = _root_.L.tierA sArr su ∧
        env.tab.wordPosOkB da = true ∧ env.tab.wordPosOkB sa = true ∧
        (L.T + (if (du &&& 1 == 0) = true then 0#64 else 8#64) + BitVec.ofInt 64 (env.tab.len64 (.t0 dArr)) =
          L.T + BitVec.ofInt 64 (env.tab.len64 da)) ∧
        (L.T + (if (du &&& 1 == 0) = true then 0#64 else 8#64) + BitVec.ofInt 64 (env.tab.base64 (.t0 dArr)) =
          L.T + BitVec.ofInt 64 (env.tab.base64 da)) ∧
        (L.T + (if (su &&& 1 == 0) = true then 0#64 else 8#64) + BitVec.ofInt 64 (env.tab.len64 (.t0 sArr)) =
          L.T + BitVec.ofInt 64 (env.tab.len64 sa)) ∧
        (L.T + (if (su &&& 1 == 0) = true then 0#64 else 8#64) + BitVec.ofInt 64 (env.tab.base64 (.t0 sArr)) =
          L.T + BitVec.ofInt 64 (env.tab.base64 sa)) ∧
        readWord64 st'.mem (sp + BitVec.ofInt 64 (slotOff nl)) = du.toBitVec ∧
        readWord64 st'.mem (sp + BitVec.ofInt 64 (slotOff (nl + 1))) = vdi.toBitVec ∧
        readWord64 st'.mem (sp + BitVec.ofInt 64 (slotOff (nl + 2))) = su.toBitVec ∧
        readWord64 st'.mem (sp + BitVec.ofInt 64 (slotOff (nl + 3))) = vsi.toBitVec ∧
        readWord64 st'.mem (sp + BitVec.ofInt 64 (slotOff (nl + 4))) = vk.toBitVec ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan sp nl 0 nt) st.mem st'.mem
    | .error _ =>
      ∃ k st',
        RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' := by
  let c0 := (evalWArrTierToTemp env.tab nl 0 d).2
  let c1 := compileE env.tab nl 1 di ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 1))
  let c2 := (evalWArrTierToTemp env.tab nl 2 s).2
  let c3 := compileE env.tab nl 3 si ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 3))
  let c4 := compileE env.tab nl 4 n ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 4))
  have hcEq : codeArgs = c0 ++ c1 ++ c2 ++ c3 ++ c4 := by rw [hcodeArgs]
  rw [hcEq] at hlink
  have hlink0 : lkm.linkSpec (pre ++ c0 ++ (c1 ++ c2 ++ c3 ++ c4 ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
  have hw0 : 0 + max 1 (warrTemps d) ≤ nt := by
    have := Nat.le_trans (by omega : 4 + 1 ≤ 4 + max 1 (maxTempsExpr n)) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hnt))))
    have := Nat.le_trans (Nat.le_max_left _ _) hnt
    omega
  have hsim0 := eval_warr_to_temp_sim env L lm loc hal hlim htop d hdOk hw0 pre _ hlink0 st hpc hgp hsp hm hf
  cases hdW : _root_.L.warr d { mem := lm, loc := loc } with
  | error err =>
    simp only [copy64ArgsEval, Bind.bind, StateT.bind, Except.bind, hdW] at hsim0 ⊢
    obtain ⟨k, st', hrun, hpc', hpres, _⟩ := hsim0; exact ⟨k, st', hrun, hpc', hpres⟩
  | ok r0 =>
    rcases r0 with ⟨da, st0'⟩
    have hst0' : st0' = { mem := lm, loc := loc } := by
      rcases warr_pure d { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
      · rw [hdW] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
      · rw [hdW] at herr; contradiction
    subst hst0'; rw [hdW] at hsim0
    obtain ⟨k0, st1, du, hrun0, hpc0, hdaEq, hdaOk, hdoLen, hdoBase, hslot0, hpres0, hout0⟩ := hsim0
    have hm1 := progMemRel_of_tempSpan env L hlim htop (Nat.zero_le nt) hout0 hm
    have hf1 := progFrameOk_of_tempSpan L htop (Nat.zero_le nt) hout0 hf
    let pre1 := pre ++ c0
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by
      rw [hpc0, lkm.totalSize_append pre c0]
    have hlink1 : lkm.linkSpec (pre1 ++ c1 ++ (c2 ++ c3 ++ c4 ++ post)) =
        .ok (env.code, env.labels) := by simpa [pre1, List.append_assoc] using hlink0
    have hw1 : 1 + max 1 (maxTempsExpr di) ≤ nt := by
      have h1 := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hnt)
      have h2 := Nat.le_trans (by omega : 4 + 1 ≤ 4 + max 1 (maxTempsExpr n)) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hnt))))
      omega
    have hsim1 := prog_evalToTemp_sim env L lm loc hal hlim htop di hdiOk hw1 pre1 _ hlink1 st1 hpc1' (hpres0.gp.trans hgp) (hpres0.sp.trans hsp) hm1 hf1
    cases hdiE : _root_.L.evalE di { mem := lm, loc := loc } with
    | error err =>
      simp only [copy64ArgsEval, Bind.bind, StateT.bind, Except.bind, hdW, hdiE] at hsim1 ⊢
      obtain ⟨k, st', hrun, hpc', hpres, _⟩ := hsim1
      exact ⟨_, st', run_trans hrun0 hrun, hpc', hpres0.trans hpres⟩
    | ok r1 =>
      rcases r1 with ⟨vdi, st1'⟩
      have hst1' : st1' = { mem := lm, loc := loc } := by
        rcases _root_.L.evalE_pure di { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
        · rw [hdiE] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
        · rw [hdiE] at herr; contradiction
      subst hst1'; rw [hdiE] at hsim1
      obtain ⟨k1, st2, hrun1, hpc1, hslot1, hpres1, hout1⟩ := hsim1
      have hm2 := progMemRel_of_tempSpan env L hlim htop (by omega : 1 ≤ nt) hout1 hm1
      have hf2 := progFrameOk_of_tempSpan L htop (by omega : 1 ≤ nt) hout1 hf1
      let pre2 := pre1 ++ c1
      have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) := by
        rw [hpc1, lkm.totalSize_append pre1 c1]
      have hlink2 : lkm.linkSpec (pre2 ++ c2 ++ (c3 ++ c4 ++ post)) =
          .ok (env.code, env.labels) := by simpa [pre2, List.append_assoc] using hlink1
      have hw2 : 2 + max 1 (warrTemps s) ≤ nt := by
        have h1 := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hnt))
        have h2 := Nat.le_trans (by omega : 4 + 1 ≤ 4 + max 1 (maxTempsExpr n)) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hnt))))
        cases s with
        | plain _ => dsimp [warrTemps]; omega
        | tier _ t => dsimp [warrTemps] at h1 ⊢; omega
      have hsim2 := eval_warr_to_temp_sim env L lm loc hal hlim htop s hsOk hw2 pre2 _ hlink2 st2 hpc2' ((hpres0.trans hpres1).gp.trans hgp) ((hpres0.trans hpres1).sp.trans hsp) hm2 hf2
      cases hsW : _root_.L.warr s { mem := lm, loc := loc } with
      | error err =>
        simp only [copy64ArgsEval, Bind.bind, StateT.bind, Except.bind, hdW, hdiE, hsW] at hsim2 ⊢
        obtain ⟨k, st', hrun, hpc', hpres, _⟩ := hsim2
        exact ⟨_, st', run_trans (run_trans hrun0 hrun1) hrun, hpc', (hpres0.trans hpres1).trans hpres⟩
      | ok r2 =>
        rcases r2 with ⟨sa, st2'⟩
        have hst2' : st2' = { mem := lm, loc := loc } := by
          rcases warr_pure s { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
          · rw [hsW] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
          · rw [hsW] at herr; contradiction
        subst hst2'; rw [hsW] at hsim2
        obtain ⟨k2, st3, su, hrun2, hpc2, hsaEq, hsaOk, hsoLen, hsoBase, hslot2, hpres2, hout2⟩ := hsim2
        have hm3 := progMemRel_of_tempSpan env L hlim htop (by omega : 2 ≤ nt) hout2 hm2
        have hf3 := progFrameOk_of_tempSpan L htop (by omega : 2 ≤ nt) hout2 hf2
        let pre3 := pre2 ++ c2
        have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre3) := by
          rw [hpc2, lkm.totalSize_append pre2 c2]
        have hlink3 : lkm.linkSpec (pre3 ++ c3 ++ (c4 ++ post)) =
            .ok (env.code, env.labels) := by simpa [pre3, List.append_assoc] using hlink2
        have hw3 : 3 + max 1 (maxTempsExpr si) ≤ nt := by
          have h1 := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hnt)))
          have h2 := Nat.le_trans (by omega : 4 + 1 ≤ 4 + max 1 (maxTempsExpr n)) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hnt))))
          omega
        have hsim3 := prog_evalToTemp_sim env L lm loc hal hlim htop si hsiOk hw3 pre3 _ hlink3 st3 hpc3' ((hpres0.trans (hpres1.trans hpres2)).gp.trans hgp) ((hpres0.trans (hpres1.trans hpres2)).sp.trans hsp) hm3 hf3
        cases hsiE : _root_.L.evalE si { mem := lm, loc := loc } with
        | error err =>
          simp only [copy64ArgsEval, Bind.bind, StateT.bind, Except.bind, hdW, hdiE, hsW, hsiE] at hsim3 ⊢
          obtain ⟨k, st', hrun, hpc', hpres, _⟩ := hsim3
          exact ⟨_, st', run_trans (run_trans (run_trans hrun0 hrun1) hrun2) hrun, hpc', (hpres0.trans (hpres1.trans hpres2)).trans hpres⟩
        | ok r3 =>
          rcases r3 with ⟨vsi, st3'⟩
          have hst3' : st3' = { mem := lm, loc := loc } := by
            rcases _root_.L.evalE_pure si { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
            · rw [hsiE] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
            · rw [hsiE] at herr; contradiction
          subst hst3'; rw [hsiE] at hsim3
          obtain ⟨k3, st4, hrun3, hpc3, hslot3, hpres3, hout3⟩ := hsim3
          have hm4 := progMemRel_of_tempSpan env L hlim htop (by omega : 3 ≤ nt) hout3 hm3
          have hf4 := progFrameOk_of_tempSpan L htop (by omega : 3 ≤ nt) hout3 hf3
          let pre4 := pre3 ++ c3
          have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre4) := by
            rw [hpc3, lkm.totalSize_append pre3 c3]
          have hlink4 : lkm.linkSpec (pre4 ++ c4 ++ post) =
              .ok (env.code, env.labels) := by simpa [pre4, List.append_assoc] using hlink3
          have hw4 : 4 + max 1 (maxTempsExpr n) ≤ nt :=
            Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hnt)))
          have hsim4 := prog_evalToTemp_sim env L lm loc hal hlim htop n hnOk hw4 pre4 post hlink4 st4 hpc4' ((hpres0.trans (hpres1.trans (hpres2.trans hpres3))).gp.trans hgp) ((hpres0.trans (hpres1.trans (hpres2.trans hpres3))).sp.trans hsp) hm4 hf4
          cases hnE : _root_.L.evalE n { mem := lm, loc := loc } with
          | error err =>
            simp only [copy64ArgsEval, Bind.bind, StateT.bind, Except.bind, hdW, hdiE, hsW, hsiE, hnE] at hsim4 ⊢
            obtain ⟨k, st', hrun, hpc', hpres, _⟩ := hsim4
            exact ⟨_, st', run_trans (run_trans (run_trans (run_trans hrun0 hrun1) hrun2) hrun3) hrun, hpc',
              (hpres0.trans (hpres1.trans (hpres2.trans hpres3))).trans hpres⟩
          | ok r4 =>
            rcases r4 with ⟨vk, st4'⟩
            have hst4' : st4' = { mem := lm, loc := loc } := by
              rcases _root_.L.evalE_pure n { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
              · rw [hnE] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
              · rw [hnE] at herr; contradiction
            subst hst4'; rw [hnE] at hsim4
            obtain ⟨k4, st5, hrun4, hpc4, hslot4, hpres4, hout4⟩ := hsim4
            have hminiOk : copy64ArgsEval d di s si n { mem := lm, loc := loc } =
                .ok ((da, vdi, sa, vsi, vk), { mem := lm, loc := loc }) := by
              simp [copy64ArgsEval, Bind.bind, StateT.bind, Except.bind, hdW, hdiE, hsW, hsiE, hnE, Pure.pure, Except.pure, StateT.pure]
            rw [hminiOk]
            have hvalid : sp.toNat + 8 * (1 + nl + nt) ≤ 2 ^ 64 := Nat.le_trans htop L.hStackValid
            have hs0 : readWord64 st5.mem (sp + BitVec.ofInt 64 (slotOff nl)) = du.toBitVec := by
              have hz : nl + 0 = nl := Nat.add_zero nl
              rw [← hz, readWord64_slot_of_tempSpan (by omega : 0 < 4) (by omega) hvalid hout4,
                  readWord64_slot_of_tempSpan (by omega : 0 < 3) (by omega) hvalid hout3,
                  readWord64_slot_of_tempSpan (by omega : 0 < 2) (by omega) hvalid hout2,
                  readWord64_slot_of_tempSpan (by omega : 0 < 1) (by omega) hvalid hout1, hz]
              exact hslot0
            have hs1 : readWord64 st5.mem (sp + BitVec.ofInt 64 (slotOff (nl + 1))) = vdi.toBitVec := by
              rw [readWord64_slot_of_tempSpan (by omega : 1 < 4) (by omega) hvalid hout4,
                  readWord64_slot_of_tempSpan (by omega : 1 < 3) (by omega) hvalid hout3,
                  readWord64_slot_of_tempSpan (by omega : 1 < 2) (by omega) hvalid hout2]
              exact hslot1
            have hs2 : readWord64 st5.mem (sp + BitVec.ofInt 64 (slotOff (nl + 2))) = su.toBitVec := by
              rw [readWord64_slot_of_tempSpan (by omega : 2 < 4) (by omega) hvalid hout4,
                  readWord64_slot_of_tempSpan (by omega : 2 < 3) (by omega) hvalid hout3]
              exact hslot2
            have hs3 : readWord64 st5.mem (sp + BitVec.ofInt 64 (slotOff (nl + 3))) = vsi.toBitVec := by
              rw [readWord64_slot_of_tempSpan (by omega : 3 < 4) (by omega) hvalid hout4]
              exact hslot3
            have hout01 : MemEqOutside (tempSpan sp nl 0 nt) st.mem st2.mem :=
              hout0.trans (MemEqOutside.mono (tempSpan_mono (by omega : 0 ≤ 1) (by omega)) hout1)
            have hout02 : MemEqOutside (tempSpan sp nl 0 nt) st.mem st3.mem :=
              hout01.trans (MemEqOutside.mono (tempSpan_mono (by omega : 0 ≤ 2) (by omega)) hout2)
            have hout03 : MemEqOutside (tempSpan sp nl 0 nt) st.mem st4.mem :=
              hout02.trans (MemEqOutside.mono (tempSpan_mono (by omega : 0 ≤ 3) (by omega)) hout3)
            have hout04 : MemEqOutside (tempSpan sp nl 0 nt) st.mem st5.mem :=
              hout03.trans (MemEqOutside.mono (tempSpan_mono (by omega : 0 ≤ 4) (by omega)) hout4)
            have hpcEq : lkm.totalSize pre4 + lkm.totalSize c4 = lkm.totalSize pre + lkm.totalSize codeArgs := by
              rw [lkm.totalSize_append pre3 c3, lkm.totalSize_append pre2 c2, lkm.totalSize_append pre1 c1, lkm.totalSize_append pre c0,
                  hcEq, lkm.totalSize_append (((c0 ++ c1) ++ c2) ++ c3) c4, lkm.totalSize_append ((c0 ++ c1) ++ c2) c3,
                  lkm.totalSize_append (c0 ++ c1) c2, lkm.totalSize_append c0 c1]; omega
            refine ⟨_, st5, du, su, run_trans (run_trans (run_trans (run_trans hrun0 hrun1) hrun2) hrun3) hrun4,
              by rw [hpc4, hpcEq], hdaEq, hsaEq, hdaOk, hsaOk, hdoLen, hdoBase, hsoLen, hsoBase,
              hs0, hs1, hs2, hs3, hslot4, hpres0.trans (hpres1.trans (hpres2.trans (hpres3.trans hpres4))), hout04⟩

private theorem prog_copy64_tail_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hlim : L.stackLimit.toNat ≤ sp.toNat) (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (da sa : _root_.L.TieredArray) (hdaOk : env.tab.wordPosOkB da = true) (hsaOk : env.tab.wordPosOkB sa = true)
    (vdi vsi vk : _root_.L.Word) (hbd : vdi.toNat + vk.toNat ≤ (lm.arr64 da).size)
    (hbs : vsi.toNat + vk.toNat ≤ (lm.arr64 sa).size)
    (loopLbl doneLbl : String) (pre3 post : List AsmItem)
    (st3 : State) (hpc3 : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre3))
    (ht1_3 : st3.getReg AbiReg.t1 = L.base64 da + BitVec.ofNat 64 (8 * vdi.toNat))
    (ht2_3 : st3.getReg AbiReg.t2 = L.base64 sa + BitVec.ofNat 64 (8 * vsi.toNat))
    (ht3_3 : st3.getReg AbiReg.t3 = vk.toBitVec)
    (hm3 : ProgMemRel env.tab L st3.mem lm) (hf3 : ProgFrameOk L sp st3.mem nl loc)
    (hlink3 : lkm.linkSpec (pre3 ++ [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
      Asm.ld AbiReg.t4 AbiReg.t2 0#12, Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
      Asm.addi AbiReg.t2 AbiReg.t2 8#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12),
      Asm.j loopLbl, Asm.lbl doneLbl] ++ post) = .ok (env.code, env.labels)) :
    ∃ k r',
      RV64.run env.rom k st3 = .cont r' ∧
      r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre3 + lkm.totalSize [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
        Asm.ld AbiReg.t4 AbiReg.t2 0#12, Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
        Asm.addi AbiReg.t2 AbiReg.t2 8#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl])) ∧
      PreservedRegs st3 r' ∧
      ProgMemRel env.tab L r'.mem (lm.copy64 da vdi sa vsi vk.toNat) ∧
      ProgFrameOk L sp r'.mem nl loc ∧
      ProgMemOutside (FnWriteMask L sp nl nt) st3.mem r'.mem := by
  have hloopLbl := lookupLabel_of_lbl_lm lkm pre3
    ([Asm.beq AbiReg.t3 AbiReg.zero doneLbl, Asm.ld AbiReg.t4 AbiReg.t2 0#12,
      Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
      Asm.addi AbiReg.t2 AbiReg.t2 8#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12),
      Asm.j loopLbl, Asm.lbl doneLbl] ++ post) loopLbl (by simpa [List.append_assoc] using hlink3)
  have hdoneLbl := lookupLabel_of_lbl_lm lkm
    (pre3 ++ [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl, Asm.ld AbiReg.t4 AbiReg.t2 0#12,
      Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
      Asm.addi AbiReg.t2 AbiReg.t2 8#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl])
    post doneLbl (by simpa [List.append_assoc] using hlink3)
  have htwDone : lkm.totalSize [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
      Asm.ld AbiReg.t4 AbiReg.t2 0#12, Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
      Asm.addi AbiReg.t2 AbiReg.t2 8#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] =
      lkm.totalSize [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
        Asm.ld AbiReg.t4 AbiReg.t2 0#12, Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
        Asm.addi AbiReg.t2 AbiReg.t2 8#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl] := by
    rw [show [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
      Asm.ld AbiReg.t4 AbiReg.t2 0#12, Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
      Asm.addi AbiReg.t2 AbiReg.t2 8#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] =
      [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
        Asm.ld AbiReg.t4 AbiReg.t2 0#12, Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
        Asm.addi AbiReg.t2 AbiReg.t2 8#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl] ++ [Asm.lbl doneLbl] by simp]
    simp only [lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero]
  have hdoneTgt : lkm.totalSize (pre3 ++ [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
      Asm.ld AbiReg.t4 AbiReg.t2 0#12, Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
      Asm.addi AbiReg.t2 AbiReg.t2 8#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl]) =
      lkm.totalSize pre3 + lkm.totalSize [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
        Asm.ld AbiReg.t4 AbiReg.t2 0#12, Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
        Asm.addi AbiReg.t2 AbiReg.t2 8#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] := by
    rw [lkm.totalSize_append, ← htwDone]
  have hlinkL : lkm.linkSpec (pre3 ++ [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
      Asm.ld AbiReg.t4 AbiReg.t2, Asm.sd AbiReg.t1 AbiReg.t4, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
      Asm.addi AbiReg.t2 AbiReg.t2 8#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl,
      Asm.lbl doneLbl] ++ post) = .ok (env.code, env.labels) := by
    simpa [Asm.ld, Asm.sd, List.append_assoc] using hlink3
  obtain ⟨kL, r', hrunL, hpcR, hpresL, hmR, hmeqL⟩ := copy64_loop_sim env L da sa hdaOk hsaOk loopLbl doneLbl
    (lkm.totalSize pre3) (lkm.totalSize pre3 + lkm.totalSize [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl,
      Asm.ld AbiReg.t4 AbiReg.t2 0#12, Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12,
      Asm.addi AbiReg.t2 AbiReg.t2 8#12, Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl])
    hloopLbl (by rw [← hdoneTgt]; exact hdoneLbl) pre3 post rfl hlinkL
    vk.toNat lm vdi vsi st3 hpc3 ht1_3 ht2_3 (by rw [ht3_3, u64_toBitVec_eq_ofNat]) hbd hbs hm3
  have hpmL : ProgMemOutside (FnWriteMask L sp nl nt) st3.mem r'.mem :=
    ProgMemOutside.of_memEqOutside (fun _ hc => Or.inr (Or.inr (Or.inr ⟨da, hdaOk, hc⟩))) hmeqL
  have hfR := progFrameOk_of_disj_stack L hlim htop (L.arr64Span da) (L.arr64Span_valid da)
    (L.h64DisjStack da hdaOk) hmeqL hf3
  exact ⟨kL, r', hrunL, hpcR, hpresL, hmR, hfR, hpmL⟩

theorem prog_copy64_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64} {nl nt : Nat}
    (hal : isAligned sp 8 = true) (hlim : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (d : _root_.L.WArr) (di : _root_.L.Expr) (s : _root_.L.WArr) (si n : _root_.L.Expr)
    (hdOk : warrOkB env.tab nl d = true) (hdiOk : exprOkB env.tab nl di = true)
    (hsOk : warrOkB env.tab nl s = true) (hsiOk : exprOkB env.tab nl si = true)
    (hnOk : exprOkB env.tab nl n = true)
    (hnt : max (warrTemps d) (max (1 + maxTempsExpr di)
      (max (match s with | .plain _ => 0 | .tier _ t => 2 + maxTempsExpr t)
      (max (3 + maxTempsExpr si) (4 + max 1 (maxTempsExpr n))))) ≤ nt)
    (pfx : String) (lblId : Nat) (pre post : List AsmItem)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOk L sp st.mem nl loc)
    (hlink : lkm.linkSpec (pre ++ (compileS env.tab nl pfx lblId none "" (.copy64 d di s si n)).1 ++ post) =
      .ok (env.code, env.labels))
    (p : _root_.L.Prog) :
    let codeS := (compileS env.tab nl pfx lblId none "" (.copy64 d di s si n)).1
    match _root_.L.step p (fun _ => throw .outOfFuel) (.copy64 d di s si n) { mem := lm, loc := loc } with
    | .ok (_, st') =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize codeS)) ∧
        PreservedRegs st r' ∧
        ProgMemRel env.tab L r'.mem st'.mem ∧
        ProgFrameOk L sp r'.mem nl st'.loc ∧
        ProgMemOutside (FnWriteMask L sp nl nt) st.mem r'.mem
    | .error _ =>
      ∃ k r',
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st r' := by
  let dArr := (evalWArrTierToTemp env.tab nl 0 d).1
  let sArr := (evalWArrTierToTemp env.tab nl 2 s).1
  let loopLbl := s!"{pfx}_c64_{lblId}"
  let doneLbl := s!"{pfx}_c64_done_{lblId}"
  let codeArgs :=
    (evalWArrTierToTemp env.tab nl 0 d).2 ++
    (compileE env.tab nl 1 di ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 1))) ++
    (evalWArrTierToTemp env.tab nl 2 s).2 ++
    (compileE env.tab nl 3 si ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 3))) ++
    (compileE env.tab nl 4 n ++ storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nl + 4)))
  let codeDst :=
    loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff nl) ++
    [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] ++
    loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (env.tab.len64 (.t0 dArr)) ++
    loadMemOff .ld AbiReg.t1 AbiReg.sp AbiReg.t6 (slotOff (nl + 1)) ++
    loadMemOff .ld AbiReg.t3 AbiReg.sp AbiReg.t6 (slotOff (nl + 4)) ++
    [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3, Asm.bltu AbiReg.t0 AbiReg.t1 errLabel] ++
    loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (env.tab.base64 (.t0 dArr)) ++
    [Asm.slli AbiReg.t1 AbiReg.t1 3#6, Asm.add AbiReg.t1 AbiReg.t5 AbiReg.t1]
  let codeSrc :=
    loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t2 (slotOff (nl + 2)) ++
    [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] ++
    loadMemOff .ld AbiReg.t0 AbiReg.t5 AbiReg.t6 (env.tab.len64 (.t0 sArr)) ++
    loadMemOff .ld AbiReg.t2 AbiReg.sp AbiReg.t6 (slotOff (nl + 3)) ++
    [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3, Asm.bltu AbiReg.t0 AbiReg.t2 errLabel] ++
    loadMemOff .ld AbiReg.t5 AbiReg.t5 AbiReg.t6 (env.tab.base64 (.t0 sArr)) ++
    [Asm.slli AbiReg.t2 AbiReg.t2 3#6, Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2]
  let codeLoop :=
    [Asm.lbl loopLbl, Asm.beq AbiReg.t3 AbiReg.zero doneLbl, Asm.ld AbiReg.t4 AbiReg.t2 0#12,
     Asm.sd AbiReg.t1 AbiReg.t4 0#12, Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 8#12,
     Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl]
  have hcodeEq : (compileS env.tab nl pfx lblId none "" (.copy64 d di s si n)).1 =
      codeArgs ++ codeDst ++ codeSrc ++ codeLoop := by
    cases d <;> cases s <;>
      dsimp only [compileS, dArr, sArr, evalWArrTierToTemp, codeArgs, codeDst, codeSrc, codeLoop, loopLbl, doneLbl] <;>
      simp only [List.append_assoc] <;> rfl
  rw [hcodeEq] at hlink
  have hlink0 : lkm.linkSpec (pre ++ codeArgs ++ (codeDst ++ codeSrc ++ codeLoop ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
  have hargs := prog_copy64_args_sim env L lm loc hal hlim htop d di s si n hdOk hdiOk hsOk hsiOk hnOk hnt
    pre codeArgs (codeDst ++ codeSrc ++ codeLoop ++ post) rfl hlink0 st hpc hgp hsp hm hf
  cases hdaW : _root_.L.warr d { mem := lm, loc := loc } with
  | error err =>
    simp only [copy64ArgsEval, Bind.bind, StateT.bind, Except.bind, hdaW] at hargs
    have hstepErr : _root_.L.step p (fun _ => throw .outOfFuel) (.copy64 d di s si n) { mem := lm, loc := loc } = .error err := by
      simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hdaW]
    rw [hstepErr]; exact hargs
  | ok r0 =>
    rcases r0 with ⟨da, st0'⟩
    have hst0' : st0' = { mem := lm, loc := loc } := by
      rcases warr_pure d { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
      · rw [hdaW] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
      · rw [hdaW] at herr; cases herr
    rw [hst0'] at hdaW
    cases hdiE : _root_.L.evalE di { mem := lm, loc := loc } with
    | error err =>
      simp only [copy64ArgsEval, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE] at hargs
      have hstepErr : _root_.L.step p (fun _ => throw .outOfFuel) (.copy64 d di s si n) { mem := lm, loc := loc } = .error err := by
        simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE]
      rw [hstepErr]; exact hargs
    | ok r1 =>
      rcases r1 with ⟨vdi, st1'⟩
      have hst1' : st1' = { mem := lm, loc := loc } := by
        rcases _root_.L.evalE_pure di { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
        · rw [hdiE] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
        · rw [hdiE] at herr; cases herr
      rw [hst1'] at hdiE
      cases hsaW : _root_.L.warr s { mem := lm, loc := loc } with
      | error err =>
        simp only [copy64ArgsEval, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE, hsaW] at hargs
        have hstepErr : _root_.L.step p (fun _ => throw .outOfFuel) (.copy64 d di s si n) { mem := lm, loc := loc } = .error err := by
          simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE, hsaW]
        rw [hstepErr]; exact hargs
      | ok r2 =>
        rcases r2 with ⟨sa, st2'⟩
        have hst2' : st2' = { mem := lm, loc := loc } := by
          rcases warr_pure s { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
          · rw [hsaW] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
          · rw [hsaW] at herr; cases herr
        rw [hst2'] at hsaW
        cases hsiE : _root_.L.evalE si { mem := lm, loc := loc } with
        | error err =>
          simp only [copy64ArgsEval, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE, hsaW, hsiE] at hargs
          have hstepErr : _root_.L.step p (fun _ => throw .outOfFuel) (.copy64 d di s si n) { mem := lm, loc := loc } = .error err := by
            simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE, hsaW, hsiE]
          rw [hstepErr]; exact hargs
        | ok r3 =>
          rcases r3 with ⟨vsi, st3'⟩
          have hst3' : st3' = { mem := lm, loc := loc } := by
            rcases _root_.L.evalE_pure si { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
            · rw [hsiE] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
            · rw [hsiE] at herr; cases herr
          rw [hst3'] at hsiE
          cases hnE : _root_.L.evalE n { mem := lm, loc := loc } with
          | error err =>
            simp only [copy64ArgsEval, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE, hsaW, hsiE, hnE] at hargs
            have hstepErr : _root_.L.step p (fun _ => throw .outOfFuel) (.copy64 d di s si n) { mem := lm, loc := loc } = .error err := by
              simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE, hsaW, hsiE, hnE]
            rw [hstepErr]; exact hargs
          | ok r4 =>
            rcases r4 with ⟨vk, st4'⟩
            have hst4' : st4' = { mem := lm, loc := loc } := by
              rcases _root_.L.evalE_pure n { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
              · rw [hnE] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
              · rw [hnE] at herr; cases herr
            rw [hst4'] at hnE
            have hargsEq : copy64ArgsEval d di s si n { mem := lm, loc := loc } =
                .ok ((da, vdi, sa, vsi, vk), { mem := lm, loc := loc }) := by
              simp [copy64ArgsEval, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE, hsaW, hsiE, hnE, Pure.pure, Except.pure, StateT.pure]
            rw [hargsEq] at hargs
            obtain ⟨kA, st1, du, su, hrunA, hpc1, hdaEq, hsaEq, hdaOk, hsaOk, hdoLen, hdoBase, hsoLen, hsoBase,
              hs0, hs1, hs2, hs3, hs4, hpresA, houtA⟩ := hargs
            have hm1 := progMemRel_of_tempSpan env L hlim htop (Nat.zero_le nt) houtA hm
            have hf1 := progFrameOk_of_tempSpan L htop (Nat.zero_le nt) houtA hf
            have hpmA := progMemOutside_of_tempSpan L hlim htop (Nat.zero_le nt) houtA
            let pre1 := pre ++ codeArgs
            have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by
              rw [hpc1, lkm.totalSize_append pre codeArgs]
            have hlink1 : lkm.linkSpec (pre1 ++ codeDst ++ (codeSrc ++ codeLoop ++ post)) =
                .ok (env.code, env.labels) := by simpa [pre1, List.append_assoc] using hlink0
            have hdst := prog_warr_dst_setup_sim env L lm hal dArr du vdi vk da hdaOk
              (hdaEq ▸ hdoLen) (hdaEq ▸ hdoBase) pre1 codeDst (codeSrc ++ codeLoop ++ post) rfl
              st1 hpc1' (hpresA.gp.trans hgp) (hpresA.sp.trans hsp) hm1 hs0 hs1 hs4 hlink1
            have hstepOk : _root_.L.step p (fun _ => throw .outOfFuel) (.copy64 d di s si n) { mem := lm, loc := loc } =
                if vdi.toNat + vk.toNat ≤ (lm.arr64 da).size ∧ vsi.toNat + vk.toNat ≤ (lm.arr64 sa).size then
                  .ok (Sig.normal, { mem := lm.copy64 da vdi sa vsi vk.toNat, loc := loc })
                else .error .oob := by
              simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hdaW, hdiE, hsaW, hsiE, hnE, get, getThe,
                MonadStateOf.get, StateT.get, set, MonadStateOf.set,
                throw, throwThe, MonadExceptOf.throw, Pure.pure, Except.pure]
              split <;> rfl
            rw [hstepOk]
            by_cases hbd : vdi.toNat + vk.toNat ≤ (lm.arr64 da).size
            · simp only [hbd, ↓reduceIte] at hdst
              obtain ⟨kD, st2, hrunD, hpc2, ht1_2, ht3_2, hmemD, hpresD⟩ := hdst
              let pre2 := pre1 ++ codeDst
              have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) := by
                rw [hpc2, lkm.totalSize_append pre1 codeDst]
              have hlink2 : lkm.linkSpec (pre2 ++ codeSrc ++ (codeLoop ++ post)) =
                  .ok (env.code, env.labels) := by simpa [pre2, List.append_assoc] using hlink1
              have hsrc := prog_warr_src_setup_sim env L lm hal sa su vsi vk hsaOk
                (L.base64 da + BitVec.ofNat 64 (8 * vdi.toNat)) (hsaEq ▸ hsoLen) (hsaEq ▸ hsoBase)
                pre2 codeSrc (codeLoop ++ post) (by rw [hsaEq]; rfl) st2 hpc2' (hpresD.gp.trans (hpresA.gp.trans hgp))
                (hpresD.sp.trans (hpresA.sp.trans hsp)) (hmemD ▸ hm1) ht1_2 ht3_2 (hmemD ▸ hs2) (hmemD ▸ hs3) hlink2
              by_cases hbs : vsi.toNat + vk.toNat ≤ (lm.arr64 sa).size
              · simp only [hbd, hbs, and_self, ↓reduceIte] at hsrc ⊢
                obtain ⟨kS, st3, hrunS, hpc3, ht1_3, ht2_3, ht3_3, hmemS, hpresS⟩ := hsrc
                let pre3 := pre2 ++ codeSrc
                have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre3) := by
                  rw [hpc3, lkm.totalSize_append pre2 codeSrc]
                have hlink3 : lkm.linkSpec (pre3 ++ codeLoop ++ post) =
                    .ok (env.code, env.labels) := by simpa [pre3, List.append_assoc] using hlink2
                have hmemS' : st3.mem = st1.mem := hmemS.trans hmemD
                obtain ⟨kL, r', hrunL, hpcR, hpresL, hmR, hfR, hpmL⟩ :=
                  prog_copy64_tail_sim env L lm loc hlim htop da sa hdaOk hsaOk vdi vsi vk hbd hbs
                    loopLbl doneLbl pre3 post st3 hpc3' ht1_3 ht2_3 ht3_3
                    (hmemS' ▸ hm1) (hmemS' ▸ hf1) hlink3
                have hpmL' : ProgMemOutside (FnWriteMask L sp nl nt) st1.mem r'.mem := by
                  rw [← hmemS']; exact hpmL
                have hpcEq : lkm.totalSize pre3 + lkm.totalSize codeLoop = lkm.totalSize pre + lkm.totalSize (codeArgs ++ codeDst ++ codeSrc ++ codeLoop) := by
                  rw [lkm.totalSize_append pre2 codeSrc, lkm.totalSize_append pre1 codeDst, lkm.totalSize_append pre codeArgs,
                      lkm.totalSize_append ((codeArgs ++ codeDst) ++ codeSrc) codeLoop,
                      lkm.totalSize_append (codeArgs ++ codeDst) codeSrc, lkm.totalSize_append codeArgs codeDst]; omega
                exact ⟨_, r', run_trans (run_trans (run_trans hrunA hrunD) hrunS) hrunL,
                  by rw [hpcR, hpcEq, ← hcodeEq], hpresA.trans (hpresD.trans (hpresS.trans hpresL)), hmR, hfR, hpmA.trans hpmL'⟩
              · simp only [hbd, hbs, and_false, ↓reduceIte] at hsrc ⊢
                obtain ⟨kS, r', hrunS, hpcR, hpresS⟩ := hsrc
                exact ⟨_, r', run_trans (run_trans hrunA hrunD) hrunS, hpcR, hpresA.trans (hpresD.trans hpresS)⟩
            · simp only [hbd, false_and, ↓reduceIte] at hdst ⊢
              obtain ⟨kD, r', hrunD, hpcR, hpresD⟩ := hdst
              exact ⟨_, r', run_trans hrunA hrunD, hpcR, hpresA.trans hpresD⟩

end ProgStmtHelpers

/-- info: 'ConAgua.RISCV.Compiler.progEvalExpr_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progEvalExpr_sim
/-- info: 'ConAgua.RISCV.Compiler.progEvalCond_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms progEvalCond_sim
/-- info: 'ConAgua.RISCV.Compiler.prog_st32t_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms prog_st32t_sim
/-- info: 'ConAgua.RISCV.Compiler.prog_copy64_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms prog_copy64_sim

end ConAgua.RISCV.Compiler
