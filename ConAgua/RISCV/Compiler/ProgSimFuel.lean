import ConAgua.RISCV.Compiler.ProgSimBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Program Hardware-Fuel Budget Semantics (`ConAgua.RISCV.Compiler.ProgSimFuel`)

Preserved-register relations (`PreservedNoS0`, `PreservedTramp`), store/load helpers,
and hardware-fuel budget semantics (`execB`, `runB`, `stackNeedB`).

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard Lean axioms only.
-/

namespace ConAgua.RISCV.Compiler

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Linker

/-! ## 6. Hardware-Fuel Budget Semantics & Statement Forward Simulation -/

structure PreservedNoS0 (st0 st1 : State) : Prop where
  gp : st1.getReg AbiReg.gp = st0.getReg AbiReg.gp
  sp : st1.getReg AbiReg.sp = st0.getReg AbiReg.sp
  s2 : st1.getReg AbiReg.s2 = st0.getReg AbiReg.s2

theorem PreservedNoS0.refl (st : State) : PreservedNoS0 st st := ⟨rfl, rfl, rfl⟩

theorem PreservedNoS0.trans {st0 st1 st2 : State}
    (h01 : PreservedNoS0 st0 st1) (h12 : PreservedNoS0 st1 st2) : PreservedNoS0 st0 st2 :=
  ⟨h12.gp.trans h01.gp, h12.sp.trans h01.sp, h12.s2.trans h01.s2⟩

theorem PreservedRegs.toNoS0 {st0 st1 : State} (h : PreservedRegs st0 st1) : PreservedNoS0 st0 st1 :=
  ⟨h.gp, h.sp, h.s2⟩

structure PreservedTramp (st0 st1 : State) : Prop where
  gp : st1.getReg AbiReg.gp = st0.getReg AbiReg.gp
  s2 : st1.getReg AbiReg.s2 = st0.getReg AbiReg.s2

theorem PreservedTramp.refl (st : State) : PreservedTramp st st := ⟨rfl, rfl⟩

theorem PreservedTramp.trans {st0 st1 st2 : State}
    (h01 : PreservedTramp st0 st1) (h12 : PreservedTramp st1 st2) : PreservedTramp st0 st2 :=
  ⟨h12.gp.trans h01.gp, h12.s2.trans h01.s2⟩

theorem PreservedNoS0.toTramp {st0 st1 : State} (h : PreservedNoS0 st0 st1) : PreservedTramp st0 st1 :=
  ⟨h.gp, h.s2⟩

theorem PreservedRegs.toTramp {st0 st1 : State} (h : PreservedRegs st0 st1) : PreservedTramp st0 st1 :=
  ⟨h.gp, h.s2⟩

theorem step_sd_off {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (base rs : Reg) (off : BitVec 12)
    (hlink : lkm.linkSpec (pre ++ [Asm.raw (.store .sd base rs off)] ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + 1) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hal : isAligned (st.getReg base + sextImm12 off) 8 = true) :
    let addr := st.getReg base + sextImm12 off
    let st' := { st with pc := st.pc + 4#64, mem := writeWord64 st.mem addr (st.getReg rs) }
    RV64.run env.rom 1 st = .cont st' ∧
    st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)) ∧
    PreservedRegs st st' := by
  intro addr st'
  have hs := step_item_instr_lm lkm env.hrom pre post (.store .sd base rs off) hlink (by omega) st hpc
  exact ⟨run_one_cont _ _ st' (by rw [hs]; simp only [execInstr, hal]; rfl),
         pc_add_4_ofNat st.pc hpc, ⟨rfl, rfl, rfl, rfl⟩⟩

theorem step_ld_off {lkm : LinkModel} (env : CodeEnvGen lkm) (pre post : List AsmItem)
    (rd base : Reg) (off : BitVec 12) (hrd : rd ≠ AbiReg.zero)
    (hlink : lkm.linkSpec (pre ++ [Asm.raw (.load .ld rd base off)] ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + 1) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hal : isAligned (st.getReg base + sextImm12 off) 8 = true) :
    let addr := st.getReg base + sextImm12 off
    let st' := stepReg st rd (readWord64 st.mem addr) (st.pc + 4#64)
    RV64.run env.rom 1 st = .cont st' ∧
    st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + 1)) ∧
    st'.getReg rd = readWord64 st.mem addr ∧
    (∀ r, r ≠ rd → st'.getReg r = st.getReg r) ∧
    st'.mem = st.mem := by
  intro addr st'
  have hs := step_item_instr_lm lkm env.hrom pre post (.load .ld rd base off) hlink (by omega) st hpc
  refine ⟨run_one_cont _ _ st' (by rw [hs]; simp only [execInstr, hal]; rfl),
          pc_add_4_ofNat st.pc hpc,
          getReg_stepReg_eq st rd hrd _ _,
          fun r hr => getReg_stepReg_ne st rd r hr _ _,
          by dsimp only [st', stepReg, RV64.State.setReg]; split <;> rfl⟩

theorem slotSpan_memDisjoint_slotSpan {sp : BitVec 64} {nl nt i j : Nat}
    (hf : (frameSpan sp nl nt).valid) (hi : i < 1 + nl + nt) (hj : j < 1 + nl + nt) (hne : i ≠ j) :
    MemDisjoint (slotSpan sp i) (slotSpan sp j) := by
  refine MemSpan.disjoint_to_memDisjoint ?_ ?_ ?_
  · simp only [MemSpan.valid, frameSpan, slotSpan, slotAddr] at hf ⊢
    have hi64 : 8 * i < 2 ^ 64 := by omega
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [MemSpan.valid, frameSpan, slotSpan, slotAddr] at hf ⊢
    have hj64 : 8 * j < 2 ^ 64 := by omega
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj64, Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [MemSpan.valid, frameSpan] at hf
    have hi64 : 8 * i < 2 ^ 64 := by omega
    have hj64 : 8 * j < 2 ^ 64 := by omega
    have ha : (slotSpan sp i).base.toNat = sp.toNat + 8 * i := by
      simp only [slotSpan, slotAddr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]
      exact Nat.mod_eq_of_lt (by omega)
    have hb : (slotSpan sp j).base.toNat = sp.toNat + 8 * j := by
      simp only [slotSpan, slotAddr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj64]
      exact Nat.mod_eq_of_lt (by omega)
    dsimp only [MemSpan.disjoint, slotSpan] at *
    omega

theorem ProgFrameOk.of_setLoc {tab : Tab} (L : ProgLayout tab) {sp : BitVec 64}
    {rmem : ByteMem} {nl nt : Nat} {loc : _root_.L.Locals}
    (hf : (frameSpan sp nl nt).valid) (x : Var) (hx : x < nl) (v : _root_.L.Word)
    (hfr : ProgFrameOk L sp rmem nl loc) :
    ProgFrameOk L sp (writeWord64 rmem (sp + BitVec.ofInt 64 (slotOff x)) v.toBitVec)
      nl (fun y => if y = x then v else loc y) := by
  intro y hy
  by_cases hyx : y = x
  · subst hyx; simp only [↓reduceIte]; exact readWord64_writeWord64_self rmem _ _
  · simp only [hyx, ↓reduceIte, ← hfr y hy]
    apply MemEqOutside.readWord64_eq
      (MemEqOutside.writeWord64 rmem _ _ (fun k hk => by
        rw [slotOff_ofInt]; exact ⟨k, hk, rfl⟩ :
          ∀ k, k < 8 → (slotSpan sp (1 + x)).contains
            (sp + BitVec.ofInt 64 (slotOff x) + BitVec.ofNat 64 k)))
    intro k hk
    rw [slotOff_ofInt]
    simpa only [slotSpan, slotAddr] using @slotSpan_memDisjoint_slotSpan sp nl nt (1 + y) (1 + x) hf
      (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hy 1) (Nat.le_add_right _ _))
      (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hx 1) (Nat.le_add_right _ _))
      (by intro h; apply hyx; exact Nat.add_left_cancel h) _ ⟨k, hk, rfl⟩

theorem ProgFrameOk.of_writeSlot {tab : Tab} (L : ProgLayout tab) {sp : BitVec 64}
    {rmem : ByteMem} {nl nt j : Nat} {loc : _root_.L.Locals}
    (hf : (frameSpan sp nl nt).valid) (hj1 : 1 + nl ≤ j) (hj2 : j < 1 + nl + nt) (w : BitVec 64)
    (hfr : ProgFrameOk L sp rmem nl loc) :
    ProgFrameOk L sp (writeWord64 rmem (sp + BitVec.ofNat 64 (8 * j)) w) nl loc := by
  intro y hy
  rw [← hfr y hy]
  apply MemEqOutside.readWord64_eq
    (MemEqOutside.writeWord64 rmem _ _ (fun k hk => (⟨k, hk, rfl⟩ :
      (slotSpan sp j).contains (sp + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 k))))
  intro k hk
  rw [slotOff_ofInt]
  simpa only [slotSpan, slotAddr] using @slotSpan_memDisjoint_slotSpan sp nl nt (1 + y) j hf
    (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hy 1) (Nat.le_add_right _ _))
    hj2 (by omega) _ ⟨k, hk, rfl⟩

theorem ProgFrameOk.of_progMemOutside {tab : Tab} (L : ProgLayout tab) {sp : BitVec 64}
    {S : BitVec 64 → Prop} {m1 m2 : ByteMem} {nl nt : Nat} {loc : _root_.L.Locals}
    (_hlo : L.stackLimit.toNat ≤ sp.toNat) (_hhi : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (heq : ProgMemOutside S m1 m2)
    (hdisj : ∀ y, y < nl → ∀ k, k < 8 → ¬S (sp + BitVec.ofInt 64 (slotOff y) + BitVec.ofNat 64 k))
    (hfr : ProgFrameOk L sp m1 nl loc) :
    ProgFrameOk L sp m2 nl loc := by
  intro y hy
  rw [← hfr y hy]
  exact heq.readWord64_eq _ (hdisj y hy)

theorem ProgLayout.slot_sub_stackSpan {tab : Tab} (L : ProgLayout tab)
    {sp : BitVec 64} {nl nt : Nat}
    (hlo : L.stackLimit.toNat ≤ sp.toNat) (hhi : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    {j : Nat} (hj : j < 1 + nl + nt) :
    (slotSpan sp j).sub L.stackSpan :=
  MemSpan.sub_trans (slotSpan_sub_frame hj) (L.frame_sub_stackSpan hlo hhi)

theorem ProgMemRel.of_stack_write {tab : Tab} (L : ProgLayout tab) {sp : BitVec 64}
    {rmem : ByteMem} {lm : _root_.L.Mem} {nl nt j : Nat}
    (hlo : L.stackLimit.toNat ≤ sp.toNat) (hhi : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (hj : j < 1 + nl + nt) (w : BitVec 64) (hrel : ProgMemRel tab L rmem lm) :
    ProgMemRel tab L (writeWord64 rmem (sp + BitVec.ofNat 64 (8 * j)) w) lm :=
  ProgMemRel.of_stack_eqOutside (L.slot_sub_stackSpan hlo hhi hj)
    (MemEqOutside.writeWord64 rmem _ _ (fun k hk => ⟨k, hk, rfl⟩)) hrel

theorem ProgMemRel.of_resOff_write {tab : Tab} (L : ProgLayout tab) {rmem : ByteMem} {lm : _root_.L.Mem}
    {i : Nat} (h1 : maxRes ≤ i) (h2 : i < tab.nres) (w : BitVec 64)
    (hrel : ProgMemRel tab L rmem lm) :
    ProgMemRel tab L (writeWord64 rmem (L.T + BitVec.ofInt 64 (tab.resOff i)) w) lm := by
  let addr := L.T + BitVec.ofInt 64 (tab.resOff i)
  let rSpan : MemSpan := ⟨addr, 8⟩
  have hrb_nn : 0 ≤ tab.resBase := ProgLayout.resBase_nonneg tab
  have hrb_nat : (tab.resOff i).toNat = tab.resBase.toNat + 8 * (i - maxRes) := by
    have hnn : 0 ≤ tab.resOff i := by simp only [Tab.resOff]; omega
    rw [← Int.ofNat_inj, Int.toNat_of_nonneg hnn]
    simp only [Tab.resOff]; rw [← Int.toNat_of_nonneg hrb_nn]; push_cast; omega
  have hr_eq : BitVec.ofInt 64 (tab.resOff i) = BitVec.ofNat 64 (tab.resBase.toNat + 8 * (i - maxRes)) := by
    have hnn : 0 ≤ tab.resOff i := by simp only [Tab.resOff]; omega
    rw [← Int.toNat_of_nonneg hnn, BitVec.ofInt_natCast, hrb_nat]
  have hrSub : rSpan.sub L.resGlobSpan := by
    intro a ⟨k, hk, ha⟩
    have hk8 : k < 8 := hk
    subst ha
    refine ⟨8 * (i - maxRes) + k, ?_, ?_⟩
    · dsimp only [ProgLayout.resGlobSpan, Tab.nxres]; omega
    · dsimp only [rSpan, ProgLayout.resGlobSpan, addr]
      rw [hr_eq, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
      congr 1; congr 1; omega
  have hrSubTab : rSpan.sub L.tabSpan := MemSpan.sub_trans hrSub L.resGlob_sub_tab
  have heqOut : MemEqOutside rSpan rmem (writeWord64 rmem addr w) :=
    MemEqOutside.writeWord64 rmem _ _ (fun k hk => ⟨k, hk, rfl⟩)
  have hdisj8 : ∀ a, tab.bytePosOkB a = true → MemDisjoint rSpan (L.arr8Span a) := fun a ha =>
    MemDisjoint.of_sub_left hrSubTab
      (MemSpan.disjoint_to_memDisjoint L.tabSpan_valid (L.arr8Span_valid a) (L.h8DisjTab a ha).symm)
  have hdisj64 : ∀ s, tab.wordPosOkB s = true → MemDisjoint rSpan (L.arr64Span s) := fun s hs =>
    MemDisjoint.of_sub_left hrSubTab
      (MemSpan.disjoint_to_memDisjoint L.tabSpan_valid (L.arr64Span_valid s) (L.h64DisjTab s hs).symm)
  have htab_disj : ∀ off : Nat, off + 8 ≤ tab.resBase.toNat → MemDisjoint rSpan ⟨L.T + BitVec.ofNat 64 off, 8⟩ := by
    intro off hoff x ⟨k, hk, heqk⟩ ⟨k', hk', heqx⟩
    have hk8 : k < 8 := hk; have hk'8 : k' < 8 := hk'
    have hb := L.tab_resOff_bound h1 h2
    have hv := L.hTValid
    have h1x : x.toNat = L.T.toNat + tab.resBase.toNat + 8 * (i - maxRes) + k := by
      rw [heqk]; dsimp only [rSpan, addr]; rw [hr_eq, BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.toNat_add,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    have h2x : x.toNat = L.T.toNat + off + k' := by
      rw [heqx, BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    omega
  have hglob_disj : ∀ g : GVar, g.id < tab.ng → MemDisjoint rSpan ⟨L.T + BitVec.ofInt 64 (tab.globOff g), 8⟩ := by
    intro g hg x ⟨k, hk, heqk⟩ ⟨k', hk', heqx⟩
    have hk8 : k < 8 := hk; have hk'8 : k' < 8 := hk'
    have hb1 := L.tab_resOff_bound h1 h2
    have hb2 := L.tab_globOff_bound g hg
    have hv := L.hTValid
    have hgn : 8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres + g.id) =
        tab.resBase.toNat + 8 * (tab.nxres + g.id) := by
      simp only [Tab.resBase, Tab.romBase, Tab.nxres]; omega
    have h1x : x.toNat = L.T.toNat + tab.resBase.toNat + 8 * (i - maxRes) + k := by
      rw [heqk]; dsimp only [rSpan, addr]; rw [hr_eq, BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.toNat_add,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    have h2x : x.toNat = L.T.toNat + tab.resBase.toNat + 8 * (tab.nxres + g.id) + k' := by
      rw [heqx, Tab.globOff_eq_nat, int_mul8_ofInt, hgn, BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.toNat_add,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    simp only [Tab.nxres] at h2x; omega
  rcases hrel with ⟨haR, hs64R, hromR, hgR⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases haR a ha with ⟨hcap, hlt, hlen, hbase, hbytes⟩
    refine ⟨hcap, hlt, ?_, ?_, ?_⟩
    · rw [← hlen]; apply MemEqOutside.readWord64_eq heqOut; intro k hk
      rw [Tab.len8_eq_nat, int_mul8_ofInt]
      have hd := htab_disj (8 * (2 + (tab.nb + tab.nw) + tab.pos8 a)) (by
        have := (Tab.bytePosOk_lt ha).2.1; simp only [Tab.resBase, Tab.romBase]; omega)
      exact hd.symm _ ⟨k, hk, rfl⟩
    · rw [← hbase]; apply MemEqOutside.readWord64_eq heqOut; intro k hk
      rw [Tab.base8_eq_nat, int_mul8_ofInt]
      have hd := htab_disj (8 * (2 + tab.pos8 a)) (by
        have := (Tab.bytePosOk_lt ha).2.1; simp only [Tab.resBase, Tab.romBase]; omega)
      exact hd.symm _ ⟨k, hk, rfl⟩
    · intro j hj; rw [← hbytes j hj]
      exact heqOut _ ((hdisj8 a ha).symm _ ⟨j, by dsimp only [ProgLayout.arr8Span]; omega, rfl⟩)
  · intro s hs
    rcases hs64R s hs with ⟨hcap, hlt, hlen, hbase, hwords⟩
    refine ⟨hcap, hlt, ?_, ?_, ?_⟩
    · rw [← hlen]; apply MemEqOutside.readWord64_eq heqOut; intro k hk
      rw [Tab.len64_eq_nat, int_mul8_ofInt]
      have hd := htab_disj (8 * (2 + (tab.nb + tab.nw) + tab.pos64 s)) (by
        have := (Tab.wordPosOk_lt hs).2.1; simp only [Tab.resBase, Tab.romBase]; omega)
      exact hd.symm _ ⟨k, hk, rfl⟩
    · rw [← hbase]; apply MemEqOutside.readWord64_eq heqOut; intro k hk
      rw [Tab.base64_eq_nat, int_mul8_ofInt]
      have hd := htab_disj (8 * (2 + tab.pos64 s)) (by
        have := (Tab.wordPosOk_lt hs).2.1; simp only [Tab.resBase, Tab.romBase]; omega)
      exact hd.symm _ ⟨k, hk, rfl⟩
    · intro j hj; rw [← hwords j hj]
      apply MemEqOutside.readWord64_eq heqOut; intro k hk
      exact (hdisj64 s hs).symm _
        (MemSpan.sub_range (s := L.arr64Span s) (8 * j) 8 (by dsimp only [ProgLayout.arr64Span]; omega) k hk)
  · intro k hk
    rw [← hromR k hk]; apply heqOut; intro ⟨j, hj, heqx⟩
    have hj8 : j < 8 := hj
    have hb := L.tab_resOff_bound h1 h2; have hv := L.hTValid; have hrb := L.tab_rom_bound
    have hrn : tab.romBase.toNat + k < tab.resBase.toNat := by
      simp only [Tab.resBase, Tab.romBase, Tab.romWords] at hrb ⊢; omega
    have h1x : (L.T + BitVec.ofNat 64 (tab.romBase.toNat + k)).toNat = L.T.toNat + (tab.romBase.toNat + k) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have h2x : (addr + BitVec.ofNat 64 j).toNat = L.T.toNat + tab.resBase.toNat + 8 * (i - maxRes) + j := by
      dsimp only [addr]; rw [hr_eq, BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    have hn := congrArg BitVec.toNat heqx; rw [h1x, h2x] at hn; omega
  · intro g hg
    rw [← hgR g hg]; apply MemEqOutside.readWord64_eq heqOut; intro k hk
    exact (hglob_disj g hg).symm _ ⟨k, hk, rfl⟩

theorem ProgMemRel.of_fnWriteMask_caller_mem {tab : Tab} (L : ProgLayout tab)
    {sp spCallee : BitVec 64} {nl nt nl' nt' : Nat} {m1 m2 : ByteMem} {loc : _root_.L.Locals}
    (hlo : L.stackLimit.toNat ≤ sp.toNat) (hhi : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (_hlo' : L.stackLimit.toNat ≤ spCallee.toNat)
    (hsub : spCallee.toNat + 8 * (1 + nl' + nt') ≤ sp.toNat)
    (heq : ProgMemOutside (FnWriteMask L spCallee nl' nt') m1 m2)
    (hfr : ProgFrameOk L sp m1 nl loc) :
    ProgFrameOk L sp m2 nl loc := by
  apply ProgFrameOk.of_progMemOutside L hlo hhi heq _ hfr
  intro y hy k hk
  have hsubStack := L.slot_sub_stackSpan hlo hhi (show 1 + y < 1 + nl + nt by omega)
  have hcont : L.stackSpan.contains (sp + BitVec.ofInt 64 (slotOff y) + BitVec.ofNat 64 k) := by
    apply hsubStack; rw [slotOff_ofInt]; exact ⟨k, hk, rfl⟩
  have hmv : (frameSpan sp nl nt).valid := by simp only [frameSpan, MemSpan.valid]; have := L.hStackValid; omega
  have hlt64 : 8 * (1 + y) + k < 2 ^ 64 := by simp only [frameSpan, MemSpan.valid] at hmv; omega
  have ha : (sp + BitVec.ofInt 64 (slotOff y) + BitVec.ofNat 64 k).toNat = sp.toNat + 8 * (1 + y) + k := by
    rw [slotOff_ofInt, BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hlt64, Nat.mod_eq_of_lt (by simp only [frameSpan, MemSpan.valid] at hmv; omega)]
    omega
  have h1 : spCallee.toNat ≤ (sp + BitVec.ofInt 64 (slotOff y) + BitVec.ofNat 64 k).toNat := by
    rw [ha]; omega
  have h2 : ¬(spCallee.toNat + 8 ≤ (sp + BitVec.ofInt 64 (slotOff y) + BitVec.ofNat 64 k).toNat ∧
      (sp + BitVec.ofInt 64 (slotOff y) + BitVec.ofNat 64 k).toNat < spCallee.toNat + 8 * (1 + nl' + nt')) := by
    rw [ha]; omega
  exact L.outerStack_not_fnWriteMask hcont h1 h2

theorem ProgFrameOk.of_fnWriteMask_slot {tab : Tab} (L : ProgLayout tab)
    {sp spCallee : BitVec 64} {nl nt nl' nt' j : Nat} {m1 m2 : ByteMem}
    (hlo : L.stackLimit.toNat ≤ sp.toNat) (hhi : sp.toNat + 8 * (1 + nl + nt) ≤ L.stackTop.toNat)
    (hsub : spCallee.toNat + 8 * (1 + nl' + nt') ≤ sp.toNat)
    (hj : j < 1 + nl + nt)
    (heq : ProgMemOutside (FnWriteMask L spCallee nl' nt') m1 m2) :
    readWord64 m2 (sp + BitVec.ofNat 64 (8 * j)) = readWord64 m1 (sp + BitVec.ofNat 64 (8 * j)) := by
  apply heq.readWord64_eq
  intro k hk
  have hcont : L.stackSpan.contains (sp + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 k) :=
    L.slot_sub_stackSpan hlo hhi hj _ ⟨k, hk, rfl⟩
  have hmv : (frameSpan sp nl nt).valid := by simp only [frameSpan, MemSpan.valid]; have := L.hStackValid; omega
  have hlt64 : 8 * j + k < 2 ^ 64 := by simp only [frameSpan, MemSpan.valid] at hmv; omega
  have ha : (sp + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 k).toNat = sp.toNat + 8 * j + k := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hlt64, Nat.mod_eq_of_lt (by simp only [frameSpan, MemSpan.valid] at hmv; omega)]
    omega
  exact L.outerStack_not_fnWriteMask hcont (by omega) (by omega)

/-! ### Hardware-Fuel Budget Semantics (`execB`, `runB`, `stackNeedB`) -/

def execBSub (p : Prog) : (b : Nat) → (s : Stmt) → (st : St) →
    { r : Except Err (Sig × St × Nat) // ∀ sig st' b', r = .ok (sig, st', b') → b' ≤ b }
  | b, .skip, st =>
    match _root_.L.step p (fun _ => throw Err.outOfFuel) .skip st with
    | .ok (sig, st1) => ⟨.ok (sig, st1, b), fun _ _ _ h => by cases h; exact Nat.le_refl _⟩
    | .error err => ⟨.error err, fun _ _ _ h => by cases h⟩
  | b, .set x e, st =>
    match _root_.L.step p (fun _ => throw Err.outOfFuel) (.set x e) st with
    | .ok (sig, st1) => ⟨.ok (sig, st1, b), fun _ _ _ h => by cases h; exact Nat.le_refl _⟩
    | .error err => ⟨.error err, fun _ _ _ h => by cases h⟩
  | b, .gset g e, st =>
    match _root_.L.step p (fun _ => throw Err.outOfFuel) (.gset g e) st with
    | .ok (sig, st1) => ⟨.ok (sig, st1, b), fun _ _ _ h => by cases h; exact Nat.le_refl _⟩
    | .error err => ⟨.error err, fun _ _ _ h => by cases h⟩
  | b, .st8 a i e, st =>
    match _root_.L.step p (fun _ => throw Err.outOfFuel) (.st8 a i e) st with
    | .ok (sig, st1) => ⟨.ok (sig, st1, b), fun _ _ _ h => by cases h; exact Nat.le_refl _⟩
    | .error err => ⟨.error err, fun _ _ _ h => by cases h⟩
  | b, .st64 a i e, st =>
    match _root_.L.step p (fun _ => throw Err.outOfFuel) (.st64 a i e) st with
    | .ok (sig, st1) => ⟨.ok (sig, st1, b), fun _ _ _ h => by cases h; exact Nat.le_refl _⟩
    | .error err => ⟨.error err, fun _ _ _ h => by cases h⟩
  | b, .st64t a t i e, st =>
    match _root_.L.step p (fun _ => throw Err.outOfFuel) (.st64t a t i e) st with
    | .ok (sig, st1) => ⟨.ok (sig, st1, b), fun _ _ _ h => by cases h; exact Nat.le_refl _⟩
    | .error err => ⟨.error err, fun _ _ _ h => by cases h⟩
  | b, .st32t a t i e, st =>
    match _root_.L.step p (fun _ => throw Err.outOfFuel) (.st32t a t i e) st with
    | .ok (sig, st1) => ⟨.ok (sig, st1, b), fun _ _ _ h => by cases h; exact Nat.le_refl _⟩
    | .error err => ⟨.error err, fun _ _ _ h => by cases h⟩
  | b, .brk, st =>
    match _root_.L.step p (fun _ => throw Err.outOfFuel) .brk st with
    | .ok (sig, st1) => ⟨.ok (sig, st1, b), fun _ _ _ h => by cases h; exact Nat.le_refl _⟩
    | .error err => ⟨.error err, fun _ _ _ h => by cases h⟩
  | b, .ret es, st =>
    match _root_.L.step p (fun _ => throw Err.outOfFuel) (.ret es) st with
    | .ok (sig, st1) => ⟨.ok (sig, st1, b), fun _ _ _ h => by cases h; exact Nat.le_refl _⟩
    | .error err => ⟨.error err, fun _ _ _ h => by cases h⟩
  | b, .abort e, st =>
    match _root_.L.step p (fun _ => throw Err.outOfFuel) (.abort e) st with
    | .ok (sig, st1) => ⟨.ok (sig, st1, b), fun _ _ _ h => by cases h; exact Nat.le_refl _⟩
    | .error err => ⟨.error err, fun _ _ _ h => by cases h⟩
  | b, .copy64 d di s si n, st =>
    match _root_.L.step p (fun _ => throw Err.outOfFuel) (.copy64 d di s si n) st with
    | .ok (sig, st1) => ⟨.ok (sig, st1, b), fun _ _ _ h => by cases h; exact Nat.le_refl _⟩
    | .error err => ⟨.error err, fun _ _ _ h => by cases h⟩
  | b, .copy8w d di s si n, st =>
    match _root_.L.step p (fun _ => throw Err.outOfFuel) (.copy8w d di s si n) st with
    | .ok (sig, st1) => ⟨.ok (sig, st1, b), fun _ _ _ h => by cases h; exact Nat.le_refl _⟩
    | .error err => ⟨.error err, fun _ _ _ h => by cases h⟩
  | b, .scan8 x s i e c, st =>
    match _root_.L.step p (fun _ => throw Err.outOfFuel) (.scan8 x s i e c) st with
    | .ok (sig, st1) => ⟨.ok (sig, st1, b), fun _ _ _ h => by cases h; exact Nat.le_refl _⟩
    | .error err => ⟨.error err, fun _ _ _ h => by cases h⟩
  | b, .seq s1 s2, st =>
    let r1 := execBSub p b s1 st
    match h1 : r1.1 with
    | .error err => ⟨.error err, fun _ _ _ h => by cases h⟩
    | .ok (.normal, st1, b1) =>
      let _hle : b1 ≤ b := r1.2 .normal st1 b1 h1
      let r2 := execBSub p b1 s2 st1
      ⟨r2.1, fun sig st' b' h2 => Nat.le_trans (r2.2 sig st' b' h2) _hle⟩
    | .ok (.brk, st1, b1) => ⟨.ok (.brk, st1, b1), fun _ _ _ h => by cases h; exact r1.2 .brk st1 b1 h1⟩
    | .ok (.ret vs, st1, b1) => ⟨.ok (.ret vs, st1, b1), fun _ _ _ h => by cases h; exact r1.2 (.ret vs) st1 b1 h1⟩
  | b, .ite c s1 s2, st =>
    match evalC c st with
    | .error err => ⟨.error err, fun _ _ _ h => by cases h⟩
    | .ok (true, st1) => execBSub p b s1 st1
    | .ok (false, st1) => execBSub p b s2 st1
  | b, .while c body, st =>
    match evalC c st with
    | .error err => ⟨.error err, fun _ _ _ h => by cases h⟩
    | .ok (false, st1) => ⟨.ok (.normal, st1, b), fun _ _ _ h => by cases h; exact Nat.le_refl _⟩
    | .ok (true, st1) =>
      let r1 := execBSub p b body st1
      match h1 : r1.1 with
      | .error err => ⟨.error err, fun _ _ _ h => by cases h⟩
      | .ok (.brk, st2, b1) => ⟨.ok (.normal, st2, b1), fun _ _ _ h => by cases h; exact r1.2 .brk st2 b1 h1⟩
      | .ok (.ret vs, st2, b1) => ⟨.ok (.ret vs, st2, b1), fun _ _ _ h => by cases h; exact r1.2 (.ret vs) st2 b1 h1⟩
      | .ok (.normal, st2, 0) => ⟨.error .outOfFuel, fun _ _ _ h => by cases h⟩
      | .ok (.normal, st2, b1' + 1) =>
        let _hle : b1' + 1 ≤ b := r1.2 .normal st2 (b1' + 1) h1
        let r2 := execBSub p b1' (.while c body) st2
        ⟨r2.1, fun sig st' b' h2 => Nat.le_trans (r2.2 sig st' b' h2) (by omega)⟩
  | b, .call xs f args, st =>
    match evalArgs args st with
    | .error err => ⟨.error err, fun _ _ _ h => by cases h⟩
    | .ok (vs, st1) =>
      match p.lookup f with
      | none => ⟨.error (.noFun f), fun _ _ _ h => by cases h⟩
      | some fd =>
        match b with
        | 0 => ⟨.error .outOfFuel, fun _ _ _ h => by cases h⟩
        | b' + 1 =>
          let r2 := execBSub p b' fd.body { st1 with loc := Locals.init vs }
          match h2 : r2.1 with
          | .error err => ⟨.error err, fun _ _ _ h => by cases h⟩
          | .ok (sig, st2, b2) =>
            ⟨.ok (.normal, { st2 with loc := st1.loc }.setLocs xs sig.retVal, b2), fun _ _ _ h => by
              cases h; exact Nat.le_trans (r2.2 sig st2 b2 h2) (Nat.le_succ _)⟩
termination_by b s _ => (b, sizeOf s)
decreasing_by
  · exact Prod.Lex.right _ (by simp; omega)
  · rcases Nat.lt_or_eq_of_le _hle with hlt | rfl
    · exact Prod.Lex.left _ _ hlt
    · exact Prod.Lex.right _ (by simp; omega)
  · exact Prod.Lex.right _ (by simp; omega)
  · exact Prod.Lex.right _ (by simp; omega)
  · exact Prod.Lex.right _ (by simp; omega)
  · exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.left _ _ (Nat.lt_succ_self b')

def execB (p : Prog) (b : Nat) (s : Stmt) (st : St) : Except Err (Sig × St × Nat) :=
  (execBSub p b s st).1

theorem execB_fuel_le {p : Prog} {b : Nat} {s : Stmt} {st : St} {sig : Sig} {st' : St} {b' : Nat}
    (h : execB p b s st = .ok (sig, st', b')) : b' ≤ b :=
  (execBSub p b s st).2 sig st' b' h

/-- Peak callee frame bytes beyond caller's frame during `execB p b s st`. -/
def stackNeedB (p : Prog) (b : Nat) (s : Stmt) (st : St) : Nat :=
  match s with
  | .skip | .set _ _ | .gset _ _ | .st8 _ _ _ | .st64 _ _ _ | .st64t _ _ _ _ | .st32t _ _ _ _
  | .brk | .ret _ | .abort _ | .copy64 _ _ _ _ _ | .copy8w _ _ _ _ _ | .scan8 _ _ _ _ _ => 0
  | .seq s1 s2 =>
    match h1 : execB p b s1 st with
    | .ok (.normal, st1, b1) =>
      let _hle := execB_fuel_le h1
      max (stackNeedB p b s1 st) (stackNeedB p b1 s2 st1)
    | _ => stackNeedB p b s1 st
  | .ite c s1 s2 =>
    match evalC c st with
    | .ok (true, st1) => stackNeedB p b s1 st1
    | .ok (false, st1) => stackNeedB p b s2 st1
    | .error _ => 0
  | .while c body =>
    match evalC c st with
    | .ok (true, st1) =>
      let sb := stackNeedB p b body st1
      match h1 : execB p b body st1 with
      | .ok (.normal, st2, b1' + 1) =>
        let _hle := execB_fuel_le h1
        max sb (stackNeedB p b1' (.while c body) st2)
      | _ => sb
    | _ => 0
  | .call _ f args =>
    match evalArgs args st with
    | .ok (vs, st1) =>
      match b with
      | b' + 1 =>
        match p.lookup f with
        | some fd => fnFrameBytes fd + stackNeedB p b' fd.body { st1 with loc := Locals.init vs }
        | none => 0
      | 0 => 0
    | .error _ => 0
termination_by (b, sizeOf s)
decreasing_by
  · exact Prod.Lex.right _ (by simp; omega)
  · rcases Nat.lt_or_eq_of_le _hle with hlt | rfl
    · exact Prod.Lex.left _ _ hlt
    · exact Prod.Lex.right _ (by simp; omega)
  · exact Prod.Lex.right _ (by simp; omega)
  · exact Prod.Lex.right _ (by simp; omega)
  · exact Prod.Lex.right _ (by simp; omega)
  · exact Prod.Lex.right _ (by simp; omega)
  · exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.left _ _ (Nat.lt_succ_self _)

def runB (p : Prog) (b : Nat) (f : FnName) (vs : List _root_.L.Word) (m : Mem) :
    Except Err (List _root_.L.Word × Mem × Nat) :=
  match p.lookup f with
  | none => .error (.noFun f)
  | some fd =>
    match b with
    | 0 => .error .outOfFuel
    | b' + 1 =>
      match execB p b' fd.body { mem := m, loc := Locals.init vs } with
      | .ok (sig, st', b'') => .ok (sig.retVal, st'.mem, b'')
      | .error err => .error err

def runStackNeedB (p : Prog) (b : Nat) (f : FnName) (vs : List _root_.L.Word) (m : Mem) : Nat :=
  match p.lookup f, b with
  | some fd, b' + 1 => fnFrameBytes fd + stackNeedB p b' fd.body { mem := m, loc := Locals.init vs }
  | _, _ => 0

def stmtArityOkB (p : Prog) : Stmt → Bool
  | .seq s1 s2 | .ite _ s1 s2 => stmtArityOkB p s1 && stmtArityOkB p s2
  | .while _ s => stmtArityOkB p s
  | .call _ f args =>
    match p.lookup f with
    | some fd => args.length ≤ fd.nparams
    | none => false
  | _ => true

def progArityOkB (p : Prog) : Bool :=
  p.all fun (_, fd) => stmtArityOkB p fd.body

theorem step_seq (p : Prog) (k : Stmt → _root_.L.M Sig) (s1 s2 : Stmt) (st : St) :
    _root_.L.step p k (.seq s1 s2) st =
      match _root_.L.step p k s1 st with
      | .error err => .error err
      | .ok (.normal, st1) => _root_.L.step p k s2 st1
      | .ok (.brk, st1) => .ok (.brk, st1)
      | .ok (.ret vs, st1) => .ok (.ret vs, st1) := by
  dsimp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure]
  cases _root_.L.step p k s1 st with
  | error err => rfl
  | ok res1 =>
    rcases res1 with ⟨sig1, st1⟩
    cases sig1 <;> rfl

theorem step_ite (p : Prog) (k : Stmt → _root_.L.M Sig) (c : Cond) (s1 s2 : Stmt) (st : St) :
    _root_.L.step p k (.ite c s1 s2) st =
      match evalC c st with
      | .error err => .error err
      | .ok (true, st1) => _root_.L.step p k s1 st1
      | .ok (false, st1) => _root_.L.step p k s2 st1 := by
  dsimp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind]
  cases evalC c st with
  | error err => rfl
  | ok resC =>
    rcases resC with ⟨bc, st1⟩
    cases bc <;> rfl

theorem step_while (p : Prog) (k : Stmt → _root_.L.M Sig) (c : Cond) (body : Stmt) (st : St) :
    _root_.L.step p k (.while c body) st =
      match evalC c st with
      | .error err => .error err
      | .ok (false, st1) => .ok (.normal, st1)
      | .ok (true, st1) =>
        match _root_.L.step p k body st1 with
        | .error err => .error err
        | .ok (.normal, st2) => k (.while c body) st2
        | .ok (.brk, st2) => .ok (.normal, st2)
        | .ok (.ret vs, st2) => .ok (.ret vs, st2) := by
  dsimp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure]
  cases evalC c st with
  | error err => rfl
  | ok resC =>
    rcases resC with ⟨bc, st1⟩
    cases bc with
    | false =>
      dsimp only
      simp only [Bool.false_eq_true, ite_false]
      rfl
    | true =>
      dsimp only
      simp only [ite_true]
      dsimp only [StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure]
      cases _root_.L.step p k body st1 with
      | error err => rfl
      | ok resB =>
        rcases resB with ⟨sigB, st2⟩
        cases sigB <;> rfl

theorem step_call (p : Prog) (k : Stmt → _root_.L.M Sig)
    (xs : List Var) (f : FnName) (args : List Expr) (st : St) :
    _root_.L.step p k (.call xs f args) st =
      match evalArgs args st with
      | .error err => .error err
      | .ok (vs, st1) =>
        match p.lookup f with
        | none => .error (.noFun f)
        | some fd =>
          match k fd.body { mem := st1.mem, loc := Locals.init vs } with
          | .error err => .error err
          | .ok (sig, st2) => .ok (.normal, ({ mem := st2.mem, loc := st1.loc } : St).setLocs xs sig.retVal) := by
  dsimp only [_root_.L.step, _root_.L.invoke, _root_.L.lookupFn, _root_.L.callFn,
    Bind.bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
    set, MonadStateOf.set, StateT.set, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    Pure.pure, StateT.pure, Except.pure]
  cases evalArgs args st with
  | error err => rfl
  | ok resA =>
    rcases resA with ⟨vs, st1⟩
    cases p.lookup f with
    | none => rfl
    | some fd =>
      dsimp only
      simp only [StateT.pure, Pure.pure, Except.pure]
      cases k fd.body { mem := st1.mem, loc := Locals.init vs } with
      | error err => rfl
      | ok res2 =>
        rcases res2 with ⟨sig, st2⟩
        dsimp only [_root_.L.setLocs, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
          Pure.pure, StateT.pure, Except.pure, Except.bind]

theorem step_mono (p : Prog) (k1 k2 : Stmt → _root_.L.M Sig)
    (hmono : ∀ s st, k1 s st ≠ .error .outOfFuel → k2 s st = k1 s st) :
    ∀ s st, step p k1 s st ≠ .error .outOfFuel → step p k2 s st = step p k1 s st := by
  intro s
  induction s with
  | seq s1 s2 ih1 ih2 =>
    intro st hne
    rw [step_seq] at hne
    rw [step_seq, step_seq]
    cases h1 : step p k1 s1 st with
    | error err =>
      have h1ne : step p k1 s1 st ≠ .error .outOfFuel := by
        intro h; apply hne; rw [h1] at h ⊢; exact h
      rw [ih1 st h1ne, h1]
    | ok res1 =>
      have h1ne : step p k1 s1 st ≠ .error .outOfFuel := by rw [h1]; intro h; cases h
      rw [ih1 st h1ne, h1]
      rcases res1 with ⟨sig1, st1⟩
      cases sig1 with
      | normal => exact ih2 st1 (by simpa [h1] using hne)
      | brk => rfl
      | ret vs => rfl
  | ite c s1 s2 ih1 ih2 =>
    intro st hne
    rw [step_ite] at hne
    rw [step_ite, step_ite]
    cases hc : evalC c st with
    | error err => rfl
    | ok resC =>
      rw [hc] at hne
      rcases resC with ⟨bc, st1⟩
      cases bc
      · exact ih2 st1 hne
      · exact ih1 st1 hne
  | «while» c body ih =>
    intro st hne
    rw [step_while] at hne
    rw [step_while, step_while]
    cases hc : evalC c st with
    | error err => rfl
    | ok resC =>
      rw [hc] at hne
      rcases resC with ⟨bc, st1⟩
      cases bc
      · rfl
      · dsimp only at hne ⊢
        cases hb : step p k1 body st1 with
        | error err =>
          have hbne : step p k1 body st1 ≠ .error .outOfFuel := by
            intro h; apply hne; rw [hb] at h ⊢; exact h
          rw [ih st1 hbne, hb]
        | ok resB =>
          have hbne : step p k1 body st1 ≠ .error .outOfFuel := by rw [hb]; intro h; cases h
          rw [ih st1 hbne, hb]
          rcases resB with ⟨sigB, st2⟩
          cases sigB with
          | normal => exact hmono (.while c body) st2 (by simpa [hb] using hne)
          | brk => rfl
          | ret vs => rfl
  | call xs f args =>
    intro st hne
    rw [step_call] at hne
    rw [step_call, step_call]
    cases ha : evalArgs args st with
    | error err => rfl
    | ok resA =>
      rw [ha] at hne
      rcases resA with ⟨vs, st1⟩
      cases hl : p.lookup f with
      | none => rfl
      | some fd =>
        rw [hl] at hne
        dsimp only at hne ⊢
        have hk : k1 fd.body { mem := st1.mem, loc := Locals.init vs } ≠ .error .outOfFuel := by
          intro h; apply hne; rw [h]
        rw [hmono fd.body { mem := st1.mem, loc := Locals.init vs } hk]
  | _ => intro _ _; rfl

theorem l_exec_mono (p : Prog) : ∀ {d1 d2 : Nat} (_hle : d1 ≤ d2) (s : Stmt) (st : St),
    _root_.L.exec p d1 s st ≠ .error .outOfFuel → _root_.L.exec p d2 s st = _root_.L.exec p d1 s st := by
  intro d1
  induction d1 with
  | zero => intro d2 _ s st h; exact absurd rfl h
  | succ d1 ih =>
    intro d2 _hle s st hne
    obtain ⟨d2', rfl⟩ : ∃ d2', d2 = d2' + 1 := ⟨d2 - 1, by omega⟩
    exact step_mono p (_root_.L.exec p d1) (_root_.L.exec p d2')
      (fun s' st' h' => ih (by omega) s' st' h') s st hne

theorem execB_base_step (p : Prog) (b : Nat) (s : Stmt) (st : St)
    (hs : match s with
      | .skip | .set _ _ | .gset _ _ | .st8 _ _ _ | .st64 _ _ _ | .st64t _ _ _ _ | .st32t _ _ _ _
      | .brk | .ret _ | .abort _ | .copy64 _ _ _ _ _ | .copy8w _ _ _ _ _ | .scan8 _ _ _ _ _ => True
      | _ => False) :
    execB p b s st =
      match _root_.L.step p (fun _ => throw Err.outOfFuel) s st with
      | .ok (sig, st1) => .ok (sig, st1, b)
      | .error err => .error err := by
  cases s with
  | seq _ _ | ite _ _ _ | «while» _ _ | call _ _ _ => exact False.elim hs
  | _ =>
    unfold execB; rw [execBSub.eq_def]; dsimp only
    cases _root_.L.step p (fun _ => throw Err.outOfFuel) _ st <;> rfl

theorem step_base_eq (p : Prog) (k1 k2 : Stmt → _root_.L.M Sig) (s : Stmt) (st : St)
    (hs : match s with
      | .skip | .set _ _ | .gset _ _ | .st8 _ _ _ | .st64 _ _ _ | .st64t _ _ _ _ | .st32t _ _ _ _
      | .brk | .ret _ | .abort _ | .copy64 _ _ _ _ _ | .copy8w _ _ _ _ _ | .scan8 _ _ _ _ _ => True
      | _ => False) :
    _root_.L.step p k1 s st = _root_.L.step p k2 s st := by
  cases s with
  | seq _ _ | ite _ _ _ | «while» _ _ | call _ _ _ => exact False.elim hs
  | _ => rfl

@[simp] theorem execB_skip (p : Prog) (b : Nat) (st : St) :
    execB p b .skip st = .ok (.normal, st, b) := by
  rw [execB_base_step p b .skip st trivial]; rfl

@[simp] theorem execB_brk (p : Prog) (b : Nat) (st : St) :
    execB p b .brk st = .ok (.brk, st, b) := by
  rw [execB_base_step p b .brk st trivial]; rfl

theorem execB_set (p : Prog) (b : Nat) (x : Var) (e : Expr) (st : St) :
    execB p b (.set x e) st =
      match evalE e st with
      | .ok (v, st1) => .ok (.normal, st1.setLoc x v, b)
      | .error err => .error err := by
  rw [execB_base_step p b (.set x e) st trivial]
  dsimp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure, setLoc, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet]
  cases evalE e st <;> rfl

theorem execB_gset (p : Prog) (b : Nat) (g : GVar) (e : Expr) (st : St) :
    execB p b (.gset g e) st =
      match evalE e st with
      | .ok (v, st1) => .ok (.normal, st1.setG g v, b)
      | .error err => .error err := by
  rw [execB_base_step p b (.gset g e) st trivial]
  dsimp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure, setG, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet]
  cases evalE e st <;> rfl

theorem execB_st8 (p : Prog) (b : Nat) (a : ArrId) (i e : Expr) (st : St) :
    execB p b (.st8 a i e) st =
      match _root_.L.step p (fun _ => throw Err.outOfFuel) (.st8 a i e) st with
      | .ok (sig, st1) => .ok (sig, st1, b)
      | .error err => .error err :=
  execB_base_step p b (.st8 a i e) st trivial

theorem execB_st64 (p : Prog) (b : Nat) (a : ArrId) (i e : Expr) (st : St) :
    execB p b (.st64 a i e) st =
      match _root_.L.step p (fun _ => throw Err.outOfFuel) (.st64 a i e) st with
      | .ok (sig, st1) => .ok (sig, st1, b)
      | .error err => .error err :=
  execB_base_step p b (.st64 a i e) st trivial

theorem execB_st64t (p : Prog) (b : Nat) (a : ArrId) (t i e : Expr) (st : St) :
    execB p b (.st64t a t i e) st =
      match _root_.L.step p (fun _ => throw Err.outOfFuel) (.st64t a t i e) st with
      | .ok (sig, st1) => .ok (sig, st1, b)
      | .error err => .error err :=
  execB_base_step p b (.st64t a t i e) st trivial

theorem execB_st32t (p : Prog) (b : Nat) (a : ArrId) (t i e : Expr) (st : St) :
    execB p b (.st32t a t i e) st =
      match _root_.L.step p (fun _ => throw Err.outOfFuel) (.st32t a t i e) st with
      | .ok (sig, st1) => .ok (sig, st1, b)
      | .error err => .error err :=
  execB_base_step p b (.st32t a t i e) st trivial

theorem execB_ret (p : Prog) (b : Nat) (es : List Expr) (st : St) :
    execB p b (.ret es) st =
      match evalArgs es st with
      | .ok (vs, st1) => .ok (.ret vs, st1, b)
      | .error err => .error err := by
  rw [execB_base_step p b (.ret es) st trivial]
  dsimp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure]
  cases evalArgs es st <;> rfl

theorem execB_abort (p : Prog) (b : Nat) (e : Expr) (st : St) :
    execB p b (.abort e) st =
      match evalE e st with
      | .ok (v, _) => .error (.abort v)
      | .error err => .error err := by
  rw [execB_base_step p b (.abort e) st trivial]
  dsimp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind]
  cases evalE e st with
  | error err => rfl
  | ok res => rfl

theorem execB_copy64 (p : Prog) (b : Nat) (d : WArr) (di : Expr) (s : WArr) (si n : Expr) (st : St) :
    execB p b (.copy64 d di s si n) st =
      match _root_.L.step p (fun _ => throw Err.outOfFuel) (.copy64 d di s si n) st with
      | .ok (sig, st1) => .ok (sig, st1, b)
      | .error err => .error err :=
  execB_base_step p b (.copy64 d di s si n) st trivial

theorem execB_copy8w (p : Prog) (b : Nat) (d : WArr) (di : Expr) (s : BSrc) (si n : Expr) (st : St) :
    execB p b (.copy8w d di s si n) st =
      match _root_.L.step p (fun _ => throw Err.outOfFuel) (.copy8w d di s si n) st with
      | .ok (sig, st1) => .ok (sig, st1, b)
      | .error err => .error err :=
  execB_base_step p b (.copy8w d di s si n) st trivial

theorem execB_scan8 (p : Prog) (b : Nat) (x : Var) (s : BSrc) (i e : Expr) (c : List UInt8) (st : St) :
    execB p b (.scan8 x s i e c) st =
      match _root_.L.step p (fun _ => throw Err.outOfFuel) (.scan8 x s i e c) st with
      | .ok (sig, st1) => .ok (sig, st1, b)
      | .error err => .error err :=
  execB_base_step p b (.scan8 x s i e c) st trivial

theorem execB_seq (p : Prog) (b : Nat) (s1 s2 : Stmt) (st : St) :
    execB p b (.seq s1 s2) st =
      match execB p b s1 st with
      | .error err => .error err
      | .ok (.normal, st1, b1) => execB p b1 s2 st1
      | .ok (.brk, st1, b1) => .ok (.brk, st1, b1)
      | .ok (.ret vs, st1, b1) => .ok (.ret vs, st1, b1) := by
  unfold execB; rw [execBSub.eq_def]; dsimp only
  split
  · rename_i h1; dsimp only; conv => rhs; rw [h1]
  · rename_i st1 b1 h1; dsimp only; conv => rhs; rw [h1]
  · rename_i st1 b1 h1; dsimp only; conv => rhs; rw [h1]
  · rename_i vs st1 b1 h1; dsimp only; conv => rhs; rw [h1]

theorem execB_ite (p : Prog) (b : Nat) (c : Cond) (s1 s2 : Stmt) (st : St) :
    execB p b (.ite c s1 s2) st =
      match evalC c st with
      | .error err => .error err
      | .ok (true, st1) => execB p b s1 st1
      | .ok (false, st1) => execB p b s2 st1 := by
  unfold execB; rw [execBSub.eq_def]; dsimp only
  cases evalC c st with
  | error err => rfl
  | ok res => rcases res with ⟨bc, st1⟩; cases bc <;> rfl

theorem execB_while (p : Prog) (b : Nat) (c : Cond) (body : Stmt) (st : St) :
    execB p b (.while c body) st =
      match evalC c st with
      | .error err => .error err
      | .ok (false, st1) => .ok (.normal, st1, b)
      | .ok (true, st1) =>
        match execB p b body st1 with
        | .error err => .error err
        | .ok (.brk, st2, b1) => .ok (.normal, st2, b1)
        | .ok (.ret vs, st2, b1) => .ok (.ret vs, st2, b1)
        | .ok (.normal, _st2, 0) => .error .outOfFuel
        | .ok (.normal, st2, b1' + 1) => execB p b1' (.while c body) st2 := by
  unfold execB; rw [execBSub.eq_def]; dsimp only
  cases evalC c st with
  | error err => rfl
  | ok res =>
    rcases res with ⟨bc, st1⟩
    cases bc
    · rfl
    · dsimp only
      split
      · rename_i h1; dsimp only; conv => rhs; rw [h1]
      · rename_i st2 b1 h1; dsimp only; conv => rhs; rw [h1]
      · rename_i vs st2 b1 h1; dsimp only; conv => rhs; rw [h1]
      · rename_i st2 h1; dsimp only; conv => rhs; rw [h1]
      · rename_i st2 b1' h1; dsimp only; conv => rhs; rw [h1]

theorem execB_call (p : Prog) (b : Nat) (xs : List Var) (f : FnName) (args : List Expr) (st : St) :
    execB p b (.call xs f args) st =
      match evalArgs args st with
      | .error err => .error err
      | .ok (vs, st1) =>
        match p.lookup f with
        | none => .error (.noFun f)
        | some fd =>
          match b with
          | 0 => .error .outOfFuel
          | b' + 1 =>
            match execB p b' fd.body { st1 with loc := Locals.init vs } with
            | .error err => .error err
            | .ok (sig, st2, b2) => .ok (.normal, { st2 with loc := st1.loc }.setLocs xs sig.retVal, b2) := by
  unfold execB; rw [execBSub.eq_def]; dsimp only
  cases evalArgs args st with
  | error err => rfl
  | ok res =>
    rcases res with ⟨vs, st1⟩
    cases p.lookup f with
    | none => rfl
    | some fd =>
      cases b with
      | zero => rfl
      | succ b' =>
        dsimp only
        split
        · rename_i h2; dsimp only; conv => rhs; rw [h2]
        · rename_i sig st2 b2 h2; dsimp only; conv => rhs; rw [h2]

theorem stackNeedB_seq (p : Prog) (b : Nat) (s1 s2 : Stmt) (st : St) :
    stackNeedB p b (.seq s1 s2) st =
      match execB p b s1 st with
      | .ok (.normal, st1, b1) => max (stackNeedB p b s1 st) (stackNeedB p b1 s2 st1)
      | _ => stackNeedB p b s1 st := by
  conv => lhs; unfold stackNeedB
  split
  · rename_i st1 b1 h1; conv => rhs; rw [h1]
  · rename_i h1
    split <;> first | exact False.elim (h1 _ _ ‹_›) | rfl

theorem stackNeedB_ite (p : Prog) (b : Nat) (c : Cond) (s1 s2 : Stmt) (st : St) :
    stackNeedB p b (.ite c s1 s2) st =
      match evalC c st with
      | .ok (true, st1) => stackNeedB p b s1 st1
      | .ok (false, st1) => stackNeedB p b s2 st1
      | .error _ => 0 := by
  conv => lhs; unfold stackNeedB

theorem stackNeedB_while (p : Prog) (b : Nat) (c : Cond) (body : Stmt) (st : St) :
    stackNeedB p b (.while c body) st =
      match evalC c st with
      | .ok (true, st1) =>
        match execB p b body st1 with
        | .ok (.normal, st2, b1' + 1) =>
          max (stackNeedB p b body st1) (stackNeedB p b1' (.while c body) st2)
        | _ => stackNeedB p b body st1
      | _ => 0 := by
  conv => lhs; unfold stackNeedB
  cases evalC c st with
  | error _ => rfl
  | ok res =>
    rcases res with ⟨bc, st1⟩
    cases bc
    · rfl
    · dsimp only
      split
      · rename_i st2 b1' h1; conv => rhs; rw [h1]
      · rename_i h1
        split <;> first | exact False.elim (h1 _ _ ‹_›) | rfl

theorem stackNeedB_call (p : Prog) (b : Nat) (xs : List Var) (f : FnName) (args : List Expr) (st : St) :
    stackNeedB p b (.call xs f args) st =
      match evalArgs args st with
      | .ok (vs, st1) =>
        match b with
        | b' + 1 =>
          match p.lookup f with
          | some fd => fnFrameBytes fd + stackNeedB p b' fd.body { st1 with loc := Locals.init vs }
          | none => 0
        | 0 => 0
      | .error _ => 0 := by
  conv => lhs; unfold stackNeedB

def execBRel : (Nat × Stmt) → (Nat × Stmt) → Prop :=
  Prod.Lex (· < ·) (fun a b : Stmt => sizeOf a < sizeOf b)

theorem execB_ind (P : Nat → Stmt → Prop)
    (hstep : ∀ b s, (∀ b' s', execBRel (b', s') (b, s) → P b' s') → P b s) :
    ∀ b s, P b s := by
  intro b
  induction b using Nat.strongRecOn with
  | ind b ihb =>
    intro s
    have hi : ∀ n s', sizeOf s' = n → P b s' := by
      intro n
      induction n using Nat.strongRecOn with
      | ind n ihn =>
        rintro s' rfl
        apply hstep b s'
        intro b'' s'' hrel
        cases hrel with
        | left _ hlt => exact ihb b'' (by assumption) s''
        | right _ hlt => exact ihn (sizeOf s'') hlt s'' rfl
    exact hi (sizeOf s) s rfl

theorem execBRel_seq_left (b : Nat) (s1 s2 : Stmt) :
    execBRel (b, s1) (b, .seq s1 s2) :=
  Prod.Lex.right _ (by simp; omega)

theorem execBRel_seq_right {b1 b : Nat} (hle : b1 ≤ b) (s1 s2 : Stmt) :
    execBRel (b1, s2) (b, .seq s1 s2) := by
  rcases Nat.lt_or_eq_of_le hle with hlt | rfl
  · exact Prod.Lex.left _ _ hlt
  · exact Prod.Lex.right _ (by simp; omega)

theorem execBRel_ite_left (b : Nat) (c : Cond) (s1 s2 : Stmt) :
    execBRel (b, s1) (b, .ite c s1 s2) :=
  Prod.Lex.right _ (by simp; omega)

theorem execBRel_ite_right (b : Nat) (c : Cond) (s1 s2 : Stmt) :
    execBRel (b, s2) (b, .ite c s1 s2) :=
  Prod.Lex.right _ (by simp; omega)

theorem execBRel_while_body (b : Nat) (c : Cond) (body : Stmt) :
    execBRel (b, body) (b, .while c body) :=
  Prod.Lex.right _ (by simp; omega)

theorem execBRel_while_next {b1' b : Nat} (hlt : b1' < b) (c : Cond) (body : Stmt) :
    execBRel (b1', .while c body) (b, .while c body) :=
  Prod.Lex.left _ _ hlt

theorem execBRel_call_body (b' : Nat) (xs : List Var) (f : FnName) (args : List Expr) (body : Stmt) :
    execBRel (b', body) (b' + 1, .call xs f args) :=
  Prod.Lex.left _ _ (Nat.lt_succ_self b')

theorem execB_mono (p : Prog) : ∀ (b : Nat) (s : Stmt) (st : St) (Δ : Nat),
    match execB p b s st with
    | .ok (sig, st', r) => execB p (b + Δ) s st = .ok (sig, st', r + Δ)
    | .error .outOfFuel => True
    | .error err => execB p (b + Δ) s st = .error err := by
  intro b s
  refine execB_ind (fun b s => ∀ (st : St) (Δ : Nat),
    match execB p b s st with
    | .ok (sig, st', r) => execB p (b + Δ) s st = .ok (sig, st', r + Δ)
    | .error .outOfFuel => True
    | .error err => execB p (b + Δ) s st = .error err) ?_ b s
  intro b s ih st Δ
  cases s with
  | skip | set _ _ | gset _ _ | st8 _ _ _ | st64 _ _ _ | st64t _ _ _ _ | st32t _ _ _ _
  | brk | ret _ | abort _ | copy64 _ _ _ _ _ | copy8w _ _ _ _ _ | scan8 _ _ _ _ _ =>
    rw [execB_base_step p b _ st trivial, execB_base_step p (b + Δ) _ st trivial]
    cases _root_.L.step p (fun _ => throw Err.outOfFuel) _ st with
    | error err => cases err <;> first | exact trivial | rfl
    | ok res => rfl
  | seq s1 s2 =>
    rw [execB_seq, execB_seq]
    have ih1 := ih b s1 (execBRel_seq_left b s1 s2) st Δ
    cases h1 : execB p b s1 st with
    | error err =>
      rw [h1] at ih1
      cases err with
      | outOfFuel => exact trivial
      | oob => dsimp only at ih1; rw [ih1]
      | abort v => dsimp only at ih1; rw [ih1]
      | noFun fn => dsimp only at ih1; rw [ih1]
    | ok res1 =>
      rw [h1] at ih1
      rcases res1 with ⟨sig1, st1, b1⟩
      cases sig1
      · dsimp only at ih1
        rw [ih1]
        exact ih b1 s2 (execBRel_seq_right (execB_fuel_le h1) s1 s2) st1 Δ
      · dsimp only at ih1; rw [ih1]
      · dsimp only at ih1; rw [ih1]
  | ite c s1 s2 =>
    rw [execB_ite, execB_ite]
    cases evalC c st with
    | error err => cases err with | outOfFuel => exact trivial | _ => rfl
    | ok resC =>
      rcases resC with ⟨bc, st1⟩
      cases bc
      · exact ih b s2 (execBRel_ite_right b c s1 s2) st1 Δ
      · exact ih b s1 (execBRel_ite_left b c s1 s2) st1 Δ
  | «while» c body =>
    rw [execB_while, execB_while]
    cases evalC c st with
    | error err => cases err with | outOfFuel => exact trivial | _ => rfl
    | ok resC =>
      rcases resC with ⟨bc, st1⟩
      cases bc
      · rfl
      · dsimp only
        have ih1 := ih b body (execBRel_while_body b c body) st1 Δ
        cases hb : execB p b body st1 with
        | error err =>
          rw [hb] at ih1
          cases err with
          | outOfFuel => exact trivial
          | oob => dsimp only at ih1; rw [ih1]
          | abort v => dsimp only at ih1; rw [ih1]
          | noFun fn => dsimp only at ih1; rw [ih1]
        | ok resB =>
          rw [hb] at ih1
          rcases resB with ⟨sigB, st2, b1⟩
          cases sigB with
          | normal =>
            dsimp only at ih1
            cases b1 with
            | zero => exact trivial
            | succ b1' =>
              have hlt : b1' < b := by have := execB_fuel_le hb; omega
              rw [ih1, Nat.succ_add]
              exact ih b1' (.while c body) (execBRel_while_next hlt c body) st2 Δ
          | brk => dsimp only at ih1; rw [ih1]
          | ret vs => dsimp only at ih1; rw [ih1]
  | call xs f args =>
    rw [execB_call, execB_call]
    cases evalArgs args st with
    | error err => cases err with | outOfFuel => exact trivial | _ => rfl
    | ok resA =>
      rcases resA with ⟨vs, st1⟩
      cases hl : p.lookup f with
      | none => rfl
      | some fd =>
        cases b with
        | zero => exact trivial
        | succ b' =>
          have ih2 := ih b' fd.body (execBRel_call_body b' xs f args fd.body)
            { st1 with loc := Locals.init vs } Δ
          have hadd : b' + 1 + Δ = b' + Δ + 1 := Nat.succ_add b' Δ
          rw [hadd]
          dsimp only
          cases h2 : execB p b' fd.body { st1 with loc := Locals.init vs } with
          | error err =>
            rw [h2] at ih2
            cases err with
            | outOfFuel => exact trivial
            | oob => dsimp only at ih2; rw [ih2]
            | abort v => dsimp only at ih2; rw [ih2]
            | noFun fn => dsimp only at ih2; rw [ih2]
          | ok res2 =>
            rw [h2] at ih2
            rcases res2 with ⟨sig, st2, b2⟩
            dsimp only at ih2
            rw [ih2]

theorem execB_base_sound (p : Prog) (b : Nat) (s : Stmt) (st : St)
    (hs : match s with
      | .skip | .set _ _ | .gset _ _ | .st8 _ _ _ | .st64 _ _ _ | .st64t _ _ _ _ | .st32t _ _ _ _
      | .brk | .ret _ | .abort _ | .copy64 _ _ _ _ _ | .copy8w _ _ _ _ _ | .scan8 _ _ _ _ _ => True
      | _ => False) :
    match execB p b s st with
    | .ok (sig, st', _) => _root_.L.exec p (b + 1) s st = .ok (sig, st')
    | .error .outOfFuel => True
    | .error err => _root_.L.exec p (b + 1) s st = .error err := by
  rw [execB_base_step p b s st hs]
  have he : _root_.L.exec p (b + 1) s st = _root_.L.step p (fun _ => throw Err.outOfFuel) s st :=
    step_base_eq p (_root_.L.exec p b) (fun _ => throw Err.outOfFuel) s st hs
  rw [he]
  cases _root_.L.step p (fun _ => throw Err.outOfFuel) s st with
  | error err => cases err with | outOfFuel => exact trivial | _ => rfl
  | ok res => rfl

theorem exec_base_implies_execB (p : Prog) (d' : Nat) (s : Stmt) (st : St)
    (hs : match s with
      | .skip | .set _ _ | .gset _ _ | .st8 _ _ _ | .st64 _ _ _ | .st64t _ _ _ _ | .st32t _ _ _ _
      | .brk | .ret _ | .abort _ | .copy64 _ _ _ _ _ | .copy8w _ _ _ _ _ | .scan8 _ _ _ _ _ => True
      | _ => False) :
    ∀ extra : Nat,
      match _root_.L.exec p (d' + 1) s st with
      | .ok (sig, st') => execB p (0 + extra) s st = .ok (sig, st', extra)
      | .error err => execB p (0 + extra) s st = .error err := by
  intro extra
  rw [execB_base_step p (0 + extra) s st hs]
  have he : _root_.L.exec p (d' + 1) s st = _root_.L.step p (fun _ => throw Err.outOfFuel) s st :=
    step_base_eq p (_root_.L.exec p d') (fun _ => throw Err.outOfFuel) s st hs
  rw [he]
  cases _root_.L.step p (fun _ => throw Err.outOfFuel) s st with
  | error err => rw [Nat.zero_add]
  | ok res => rw [Nat.zero_add]

theorem l_run_eq (p : Prog) (d : Nat) (f : FnName) (vs : List _root_.L.Word) (m : Mem) :
    _root_.L.run p d f vs m =
      match p.lookup f with
      | none => .error (.noFun f)
      | some fd =>
        match _root_.L.exec p d fd.body { mem := m, loc := Locals.init vs } with
        | .ok (sig, st') => .ok (sig.retVal, st'.mem)
        | .error err => .error err := by
  simp only [_root_.L.run, _root_.L.invoke, _root_.L.lookupFn, _root_.L.callFn,
    Bind.bind, StateT.bind, Except.bind, StateT.run, Except.map,
    get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    Pure.pure, StateT.pure, Except.pure]
  cases p.lookup f with
  | none => rfl
  | some fd =>
    dsimp only
    simp only [StateT.pure, Pure.pure, Except.pure]
    cases _root_.L.exec p d fd.body { mem := m, loc := Locals.init vs } <;> rfl

theorem execB_sound (p : Prog) : ∀ (b : Nat) (s : Stmt) (st : St),
    match execB p b s st with
    | .ok (sig, st', _) => _root_.L.exec p (b + 1) s st = .ok (sig, st')
    | .error .outOfFuel => True
    | .error err => _root_.L.exec p (b + 1) s st = .error err := by
  intro b s
  refine execB_ind (fun b s => ∀ (st : St),
    match execB p b s st with
    | .ok (sig, st', _) => _root_.L.exec p (b + 1) s st = .ok (sig, st')
    | .error .outOfFuel => True
    | .error err => _root_.L.exec p (b + 1) s st = .error err) ?_ b s
  intro b s ih st
  cases s with
  | skip => exact execB_base_sound p b .skip st trivial
  | set x e => exact execB_base_sound p b (.set x e) st trivial
  | gset g e => exact execB_base_sound p b (.gset g e) st trivial
  | st8 a i e => exact execB_base_sound p b (.st8 a i e) st trivial
  | st64 a i e => exact execB_base_sound p b (.st64 a i e) st trivial
  | st64t a t i e => exact execB_base_sound p b (.st64t a t i e) st trivial
  | st32t a t i e => exact execB_base_sound p b (.st32t a t i e) st trivial
  | brk => exact execB_base_sound p b .brk st trivial
  | ret es => exact execB_base_sound p b (.ret es) st trivial
  | abort e => exact execB_base_sound p b (.abort e) st trivial
  | copy64 d di s si n => exact execB_base_sound p b (.copy64 d di s si n) st trivial
  | copy8w d di s si n => exact execB_base_sound p b (.copy8w d di s si n) st trivial
  | scan8 x s i e c => exact execB_base_sound p b (.scan8 x s i e c) st trivial
  | seq s1 s2 =>
    rw [execB_seq]
    have heS : _root_.L.exec p (b + 1) (.seq s1 s2) st =
        match _root_.L.exec p (b + 1) s1 st with
        | .error err => .error err
        | .ok (.normal, st1) => _root_.L.exec p (b + 1) s2 st1
        | .ok (.brk, st1) => .ok (.brk, st1)
        | .ok (.ret vs, st1) => .ok (.ret vs, st1) := step_seq p (_root_.L.exec p b) s1 s2 st
    have ih1 := ih b s1 (execBRel_seq_left b s1 s2) st
    cases h1 : execB p b s1 st with
    | error err =>
      rw [h1] at ih1
      cases err with
      | outOfFuel => exact trivial
      | oob | abort _ | noFun _ => rw [heS, ih1]
    | ok res1 =>
      rw [h1] at ih1
      rcases res1 with ⟨sig1, st1, b1⟩
      dsimp only at ih1
      cases sig1 with
      | normal =>
        dsimp only
        have ih2 := ih b1 s2 (execBRel_seq_right (execB_fuel_le h1) s1 s2) st1
        have hle : b1 + 1 ≤ b + 1 := Nat.succ_le_succ (execB_fuel_le h1)
        cases h2 : execB p b1 s2 st1 with
        | error err =>
          rw [h2] at ih2
          cases err with
          | outOfFuel => exact trivial
          | oob | abort _ | noFun _ =>
            rw [heS, ih1]; dsimp only
            exact (l_exec_mono p hle s2 st1 (by rw [ih2]; intro h; cases h)).trans ih2
        | ok res2 =>
          rw [h2] at ih2
          rw [heS, ih1]; dsimp only
          exact (l_exec_mono p hle s2 st1 (by rw [ih2]; intro h; cases h)).trans ih2
      | brk | ret _ => rw [heS, ih1]
  | ite c s1 s2 =>
    rw [execB_ite]
    have heI : _root_.L.exec p (b + 1) (.ite c s1 s2) st =
        match evalC c st with
        | .error err => .error err
        | .ok (true, st1) => _root_.L.exec p (b + 1) s1 st1
        | .ok (false, st1) => _root_.L.exec p (b + 1) s2 st1 := step_ite p (_root_.L.exec p b) c s1 s2 st
    cases hc : evalC c st with
    | error err => cases err with | outOfFuel => exact trivial | _ => rw [heI, hc]
    | ok resC =>
      rcases resC with ⟨bc, st1⟩
      rw [heI, hc]
      cases bc
      · exact ih b s2 (execBRel_ite_right b c s1 s2) st1
      · exact ih b s1 (execBRel_ite_left b c s1 s2) st1
  | «while» c body =>
    rw [execB_while]
    have heW : _root_.L.exec p (b + 1) (.while c body) st =
        match evalC c st with
        | .error err => .error err
        | .ok (false, st1) => .ok (.normal, st1)
        | .ok (true, st1) =>
          match _root_.L.exec p (b + 1) body st1 with
          | .error err => .error err
          | .ok (.normal, st2) => _root_.L.exec p b (.while c body) st2
          | .ok (.brk, st2) => .ok (.normal, st2)
          | .ok (.ret vs, st2) => .ok (.ret vs, st2) := step_while p (_root_.L.exec p b) c body st
    cases hc : evalC c st with
    | error err => cases err with | outOfFuel => exact trivial | _ => rw [heW, hc]
    | ok resC =>
      rcases resC with ⟨bc, st1⟩
      cases bc
      · rw [heW, hc]
      · dsimp only
        have ih1 := ih b body (execBRel_while_body b c body) st1
        cases hb : execB p b body st1 with
        | error err =>
          rw [hb] at ih1
          cases err with
          | outOfFuel => exact trivial
          | oob | abort _ | noFun _ => rw [heW, hc]; dsimp only; rw [ih1]
        | ok resB =>
          rw [hb] at ih1
          rcases resB with ⟨sigB, st2, b1⟩
          cases sigB with
          | normal =>
            dsimp only at ih1 ⊢
            cases b1 with
            | zero => exact trivial
            | succ b1' =>
              dsimp only
              have hlt : b1' < b := by have := execB_fuel_le hb; omega
              have ih2 := ih b1' (.while c body) (execBRel_while_next hlt c body) st2
              have hle : b1' + 1 ≤ b := by omega
              cases hw : execB p b1' (.while c body) st2 with
              | error err =>
                rw [hw] at ih2
                cases err with
                | outOfFuel => exact trivial
                | oob | abort _ | noFun _ =>
                  rw [heW, hc]; dsimp only; rw [ih1]; dsimp only
                  exact (l_exec_mono p hle (.while c body) st2 (by rw [ih2]; intro h; cases h)).trans ih2
              | ok resW =>
                rw [hw] at ih2
                rw [heW, hc]; dsimp only; rw [ih1]; dsimp only
                exact (l_exec_mono p hle (.while c body) st2 (by rw [ih2]; intro h; cases h)).trans ih2
          | brk | ret _ => dsimp only at ih1 ⊢; rw [heW, hc]; dsimp only; rw [ih1]
  | call xs f args =>
    rw [execB_call]
    have heC : _root_.L.exec p (b + 1) (.call xs f args) st =
        match evalArgs args st with
        | .error err => .error err
        | .ok (vs, st1) =>
          match p.lookup f with
          | none => .error (.noFun f)
          | some fd =>
            match _root_.L.exec p b fd.body { mem := st1.mem, loc := Locals.init vs } with
            | .error err => .error err
            | .ok (sig, st2) => .ok (.normal, ({ mem := st2.mem, loc := st1.loc } : St).setLocs xs sig.retVal) :=
      step_call p (_root_.L.exec p b) xs f args st
    cases ha : evalArgs args st with
    | error err => cases err with | outOfFuel => exact trivial | _ => rw [heC, ha]
    | ok resA =>
      rcases resA with ⟨vs, st1⟩
      cases hl : p.lookup f with
      | none => rw [heC, ha, hl]
      | some fd =>
        cases b with
        | zero => exact trivial
        | succ b' =>
          have ih2 := ih b' fd.body (execBRel_call_body b' xs f args fd.body)
            { mem := st1.mem, loc := Locals.init vs }
          dsimp only
          cases h2 : execB p b' fd.body { mem := st1.mem, loc := Locals.init vs } with
          | error err =>
            rw [h2] at ih2
            cases err with
            | outOfFuel => exact trivial
            | oob | abort _ | noFun _ => rw [heC, ha, hl]; dsimp only; rw [ih2]
          | ok res2 =>
            rw [h2] at ih2
            rcases res2 with ⟨sig, st2, b2⟩
            dsimp only at ih2
            rw [heC, ha, hl]; dsimp only; rw [ih2]

theorem execB_sound_run (p : Prog) (b : Nat) (f : FnName) (vs : List _root_.L.Word) (m : Mem) :
    match runB p b f vs m with
    | .ok (ret, m', _) => _root_.L.run p b f vs m = .ok (ret, m')
    | .error .outOfFuel => True
    | .error err => _root_.L.run p b f vs m = .error err := by
  unfold runB
  rw [l_run_eq]
  cases hl : p.lookup f with
  | none => rfl
  | some fd =>
    dsimp only
    cases b with
    | zero => exact trivial
    | succ b' =>
      dsimp only
      have hs := execB_sound p b' fd.body { mem := m, loc := Locals.init vs }
      cases h : execB p b' fd.body { mem := m, loc := Locals.init vs } with
      | error err =>
        rw [h] at hs
        dsimp only at hs ⊢
        cases err with
        | outOfFuel => exact trivial
        | oob | abort _ | noFun _ => rw [hs]
      | ok res =>
        rw [h] at hs
        rcases res with ⟨sig, st', b''⟩
        dsimp only at hs ⊢
        rw [hs]

theorem exec_implies_execB (p : Prog) : ∀ (d : Nat) (s : Stmt) (st : St),
    _root_.L.exec p d s st ≠ .error .outOfFuel →
    ∃ cost : Nat, ∀ extra : Nat,
      match _root_.L.exec p d s st with
      | .ok (sig, st') => execB p (cost + extra) s st = .ok (sig, st', extra)
      | .error err => execB p (cost + extra) s st = .error err := by
  intro d s
  refine execB_ind (fun d s => ∀ (st : St),
    _root_.L.exec p d s st ≠ .error .outOfFuel →
    ∃ cost : Nat, ∀ extra : Nat,
      match _root_.L.exec p d s st with
      | .ok (sig, st') => execB p (cost + extra) s st = .ok (sig, st', extra)
      | .error err => execB p (cost + extra) s st = .error err) ?_ d s
  intro d s ih st hne
  cases d with
  | zero => exact absurd rfl hne
  | succ d' =>
    cases s with
    | skip => exact ⟨0, exec_base_implies_execB p d' .skip st trivial⟩
    | set x e => exact ⟨0, exec_base_implies_execB p d' (.set x e) st trivial⟩
    | gset g e => exact ⟨0, exec_base_implies_execB p d' (.gset g e) st trivial⟩
    | st8 a i e => exact ⟨0, exec_base_implies_execB p d' (.st8 a i e) st trivial⟩
    | st64 a i e => exact ⟨0, exec_base_implies_execB p d' (.st64 a i e) st trivial⟩
    | st64t a t i e => exact ⟨0, exec_base_implies_execB p d' (.st64t a t i e) st trivial⟩
    | st32t a t i e => exact ⟨0, exec_base_implies_execB p d' (.st32t a t i e) st trivial⟩
    | brk => exact ⟨0, exec_base_implies_execB p d' .brk st trivial⟩
    | ret es => exact ⟨0, exec_base_implies_execB p d' (.ret es) st trivial⟩
    | abort e => exact ⟨0, exec_base_implies_execB p d' (.abort e) st trivial⟩
    | copy64 d di s si n => exact ⟨0, exec_base_implies_execB p d' (.copy64 d di s si n) st trivial⟩
    | copy8w d di s si n => exact ⟨0, exec_base_implies_execB p d' (.copy8w d di s si n) st trivial⟩
    | scan8 x s i e c => exact ⟨0, exec_base_implies_execB p d' (.scan8 x s i e c) st trivial⟩
    | seq s1 s2 =>
      rw [show _root_.L.exec p (d' + 1) (.seq s1 s2) st = _ from step_seq p (_root_.L.exec p d') s1 s2 st] at hne ⊢
      have hstep1 : _root_.L.step p (_root_.L.exec p d') s1 st = _root_.L.exec p (d' + 1) s1 st := rfl
      rw [hstep1] at hne ⊢
      have hne1 : _root_.L.exec p (d' + 1) s1 st ≠ .error .outOfFuel := by
        intro h; apply hne; rw [h]
      obtain ⟨c1, hc1⟩ := ih (d' + 1) s1 (execBRel_seq_left (d' + 1) s1 s2) st hne1
      cases h1 : _root_.L.exec p (d' + 1) s1 st with
      | error err =>
        refine ⟨c1, fun extra => ?_⟩
        have hc1' := hc1 extra; rw [h1] at hc1'
        rw [execB_seq, hc1']
      | ok res1 =>
        rcases res1 with ⟨sig1, st1⟩
        cases sig1 with
        | normal =>
          have hstep2 : _root_.L.step p (_root_.L.exec p d') s2 st1 = _root_.L.exec p (d' + 1) s2 st1 := rfl
          have hne2 : _root_.L.exec p (d' + 1) s2 st1 ≠ .error .outOfFuel := by
            intro h; apply hne; rw [h1]; dsimp only; rw [hstep2]; exact h
          obtain ⟨c2, hc2⟩ := ih (d' + 1) s2 (execBRel_seq_right (Nat.le_refl _) s1 s2) st1 hne2
          refine ⟨c1 + c2, fun extra => ?_⟩
          have hc1' := hc1 (c2 + extra); rw [h1] at hc1'
          rw [execB_seq, Nat.add_assoc, hc1']
          dsimp only; rw [hstep2]
          exact hc2 extra
        | brk =>
          refine ⟨c1, fun extra => ?_⟩
          have hc1' := hc1 extra; rw [h1] at hc1'
          rw [execB_seq, hc1']
        | ret vs =>
          refine ⟨c1, fun extra => ?_⟩
          have hc1' := hc1 extra; rw [h1] at hc1'
          rw [execB_seq, hc1']
    | ite c s1 s2 =>
      rw [show _root_.L.exec p (d' + 1) (.ite c s1 s2) st = _ from step_ite p (_root_.L.exec p d') c s1 s2 st] at hne ⊢
      cases hc : evalC c st with
      | error err =>
        refine ⟨0, fun extra => ?_⟩
        rw [execB_ite, hc]
      | ok resC =>
        rw [hc] at hne
        rcases resC with ⟨bc, st1⟩
        cases bc with
        | false =>
          obtain ⟨c2, hc2⟩ := ih (d' + 1) s2 (execBRel_ite_right (d' + 1) c s1 s2) st1 hne
          refine ⟨c2, fun extra => ?_⟩
          rw [execB_ite, hc]
          exact hc2 extra
        | true =>
          obtain ⟨c1, hc1⟩ := ih (d' + 1) s1 (execBRel_ite_left (d' + 1) c s1 s2) st1 hne
          refine ⟨c1, fun extra => ?_⟩
          rw [execB_ite, hc]
          exact hc1 extra
    | «while» c body =>
      rw [show _root_.L.exec p (d' + 1) (.while c body) st = _ from step_while p (_root_.L.exec p d') c body st] at hne ⊢
      cases hc : evalC c st with
      | error err =>
        refine ⟨0, fun extra => ?_⟩
        rw [execB_while, hc]
      | ok resC =>
        rw [hc] at hne
        rcases resC with ⟨bc, st1⟩
        cases bc with
        | false =>
          refine ⟨0, fun extra => ?_⟩
          rw [execB_while, hc]; dsimp only; rw [Nat.zero_add]
        | true =>
          dsimp only at hne ⊢
          have hstepB : _root_.L.step p (_root_.L.exec p d') body st1 = _root_.L.exec p (d' + 1) body st1 := rfl
          rw [hstepB] at hne ⊢
          have hneB : _root_.L.exec p (d' + 1) body st1 ≠ .error .outOfFuel := by
            intro h; apply hne; rw [h]
          obtain ⟨c1, hc1⟩ := ih (d' + 1) body (execBRel_while_body (d' + 1) c body) st1 hneB
          cases hb : _root_.L.exec p (d' + 1) body st1 with
          | error err =>
            refine ⟨c1, fun extra => ?_⟩
            have hc1' := hc1 extra; rw [hb] at hc1'
            rw [execB_while, hc]; dsimp only; rw [hc1']
          | ok resB =>
            rw [hb] at hne
            rcases resB with ⟨sigB, st2⟩
            cases sigB with
            | normal =>
              obtain ⟨c2, hc2⟩ := ih d' (.while c body) (execBRel_while_next (Nat.lt_succ_self d') c body) st2 hne
              refine ⟨c1 + 1 + c2, fun extra => ?_⟩
              have hc1' := hc1 (1 + c2 + extra); rw [hb] at hc1'
              rw [execB_while, hc]; dsimp only
              rw [show c1 + 1 + c2 + extra = c1 + (1 + c2 + extra) from by omega, hc1']
              have hc2' := hc2 extra
              simpa [Nat.add_comm 1, Nat.add_assoc] using hc2'
            | brk =>
              refine ⟨c1, fun extra => ?_⟩
              have hc1' := hc1 extra; rw [hb] at hc1'
              rw [execB_while, hc]; dsimp only; rw [hc1']
            | ret vs =>
              refine ⟨c1, fun extra => ?_⟩
              have hc1' := hc1 extra; rw [hb] at hc1'
              rw [execB_while, hc]; dsimp only; rw [hc1']
    | call xs f args =>
      rw [show _root_.L.exec p (d' + 1) (.call xs f args) st = _ from step_call p (_root_.L.exec p d') xs f args st] at hne ⊢
      cases ha : evalArgs args st with
      | error err =>
        refine ⟨0, fun extra => ?_⟩
        rw [execB_call, ha]
      | ok resA =>
        rw [ha] at hne
        rcases resA with ⟨vs, st1⟩
        cases hl : p.lookup f with
        | none =>
          refine ⟨0, fun extra => ?_⟩
          rw [execB_call, ha, hl]
        | some fd =>
          rw [hl] at hne
          dsimp only at hne ⊢
          have hne2 : _root_.L.exec p d' fd.body { mem := st1.mem, loc := Locals.init vs } ≠ .error .outOfFuel := by
            intro h; apply hne; rw [h]
          obtain ⟨c2, hc2⟩ := ih d' fd.body (execBRel_call_body d' xs f args fd.body)
            { mem := st1.mem, loc := Locals.init vs } hne2
          refine ⟨1 + c2, fun extra => ?_⟩
          have hc2' := hc2 extra
          have hadd : 1 + c2 + extra = (c2 + extra) + 1 := by omega
          rw [execB_call, ha, hl, hadd]
          cases h2 : _root_.L.exec p d' fd.body { mem := st1.mem, loc := Locals.init vs } with
          | error err =>
            rw [h2] at hc2'
            dsimp only
            rw [hc2']
          | ok res2 =>
            rw [h2] at hc2'
            rcases res2 with ⟨sig, st2⟩
            dsimp only
            rw [hc2']

theorem run_implies_runB (p : Prog) (d : Nat) (f : FnName) (vs : List _root_.L.Word) (m : Mem)
    (hne : _root_.L.run p d f vs m ≠ .error .outOfFuel) :
    ∃ cost : Nat, ∀ extra : Nat,
      match _root_.L.run p d f vs m with
      | .ok (ret, m') => runB p (cost + extra) f vs m = .ok (ret, m', extra)
      | .error err => runB p (cost + extra) f vs m = .error err := by
  rw [l_run_eq] at hne ⊢
  cases hl : p.lookup f with
  | none =>
    refine ⟨0, fun extra => ?_⟩
    simp [runB, hl]
  | some fd =>
    rw [hl] at hne
    dsimp only at hne ⊢
    have hne' : _root_.L.exec p d fd.body { mem := m, loc := Locals.init vs } ≠ .error .outOfFuel := by
      intro h; apply hne; rw [h]
    obtain ⟨c, hc⟩ := exec_implies_execB p d fd.body { mem := m, loc := Locals.init vs } hne'
    refine ⟨1 + c, fun extra => ?_⟩
    unfold runB
    rw [hl]
    have hadd : 1 + c + extra = (c + extra) + 1 := by omega
    rw [hadd]
    have hc' := hc extra
    dsimp only
    cases h : _root_.L.exec p d fd.body { mem := m, loc := Locals.init vs } with
    | error err =>
      rw [h] at hc'
      dsimp only
      rw [hc']
    | ok res =>
      rw [h] at hc'
      rcases res with ⟨sig, st'⟩
      dsimp only
      rw [hc']


end ConAgua.RISCV.Compiler
