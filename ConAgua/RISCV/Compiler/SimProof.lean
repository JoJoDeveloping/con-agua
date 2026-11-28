import ConAgua.RISCV.Compiler.SimExpr

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Forward Simulation (`ConAgua.RISCV.Compiler.SimProof`)

Proves semantic forward simulation of `ConAgua.RISCV.Compiler.Compile` against
`ConAgua.RISCV.RV64.Semantics.run` and `ConAgua.RISCV.MiniL`.
-/

namespace ConAgua.RISCV.Compiler

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Linker

/-! ## 7. Forward Simulation of Statements (`execStmt_sim_gen`) -/

private theorem storeBytes_one_self (m : ByteMem) (addr : RV64.Word) (b : BitVec 8) :
    RV64.storeBytes m addr 1 b addr = b := by
  simp only [RV64.storeBytes, beq_self_eq_true, ↓reduceIte]
  apply BitVec.eq_of_toNat_eq
  simp

private theorem mem_setG_arr8 (m : _root_.L.Mem) (g : GVar) (v : _root_.L.Word) (a : ArrId) :
    (m.setG g v).arr8 a = m.arr8 a := rfl

private theorem mem_setG_arr64 (m : _root_.L.Mem) (g : GVar) (v : _root_.L.Word) (s : TieredArray) :
    (m.setG g v).arr64 s = m.arr64 s := rfl

private theorem mem_set8_arr64 (m : _root_.L.Mem) (a : ArrId) (vi vv : _root_.L.Word) (s : TieredArray) :
    (m.set8 a vi vv).arr64 s = m.arr64 s := rfl

private theorem mem_set8_glob (m : _root_.L.Mem) (a : ArrId) (vi vv : _root_.L.Word) (g : GVar) :
    (m.set8 a vi vv).glob g = m.glob g := rfl

private theorem mem_set64_arr8 (m : _root_.L.Mem) (s : TieredArray) (vi vv : _root_.L.Word) (a : ArrId) :
    (m.set64 s vi vv).arr8 a = m.arr8 a := rfl

private theorem mem_set64_glob (m : _root_.L.Mem) (s : TieredArray) (vi vv : _root_.L.Word) (g : GVar) :
    (m.set64 s vi vv).glob g = m.glob g := rfl

private theorem Layout.tabSpan_valid {tab : Tab} {nl nt : Nat} (L : Layout tab nl nt) :
    L.tabSpan.valid := L.hTValid

private theorem Layout.arr8Span_valid {tab : Tab} {nl nt : Nat} (L : Layout tab nl nt) (a : ArrId) :
    (L.arr8Span a).valid := L.h8Valid a

private theorem Layout.arr64Span_valid {tab : Tab} {nl nt : Nat} (L : Layout tab nl nt) (s : TieredArray) :
    (L.arr64Span s).valid := L.h64Valid s

private theorem FrameOk.setLoc {tab : Tab} {nl nt : Nat} {L : Layout tab nl nt}
    {rmem : ByteMem} {loc : _root_.L.Locals} {x : Var} (hx : x < nl) (v : _root_.L.Word)
    (hfr : FrameOk L rmem nl loc) :
    FrameOk L (writeWord64 rmem (L.sp + BitVec.ofInt 64 (slotOff x)) v.toBitVec) nl
      (fun y => if y = x then v else loc y) := by
  intro y hy
  dsimp only
  by_cases hxy : y = x
  · subst hxy
    simp only [ite_true]
    exact readWord64_writeWord64_self rmem _ _
  · simp only [hxy, ite_false]
    rw [← hfr y hy]
    apply MemEqOutside.readWord64_eq
      (MemEqOutside.writeWord64 rmem _ _ (s := slotSpan L.sp (1 + x))
        (fun k hk => by rw [slotOff_ofInt]; exact ⟨k, hk, rfl⟩))
    intro k hk hmem
    have hx1 : 1 + x < 1 + nl + nt := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hx 1) (Nat.le_add_right _ nt)
    have hy1 : 1 + y < 1 + nl + nt := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hy 1) (Nat.le_add_right _ nt)
    have hne : 1 + x ≠ 1 + y := fun h => hxy (Nat.add_left_cancel h).symm
    have hdisj := MemSpan.disjoint_to_memDisjoint
      (slotSpan_valid L.hFrameValid hx1)
      (slotSpan_valid L.hFrameValid hy1)
      (slotSpan_disjoint_of_ne L.hFrameValid hx1 hy1 hne)
    apply hdisj.symm (L.sp + BitVec.ofInt 64 (slotOff y) + BitVec.ofNat 64 k)
    · rw [slotOff_ofInt]; exact ⟨k, hk, rfl⟩
    · exact hmem

private def tabWordSpan (T : BitVec 64) (off : Nat) : MemSpan :=
  ⟨T + BitVec.ofNat 64 off, 8⟩

private theorem tabWordSpan_valid {tab : Tab} {nl nt : Nat} (L : Layout tab nl nt)
    {off : Nat} (hoff : off + 8 ≤ L.tabBytes) :
    (tabWordSpan L.T off).valid := by
  have hT := L.hTValid
  have ho : off < 2 ^ 64 := by omega
  dsimp only [MemSpan.valid, tabWordSpan]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem tabWordSpan_sub_tab {tab : Tab} {nl nt : Nat} (L : Layout tab nl nt)
    {off : Nat} (hoff : off + 8 ≤ L.tabBytes) :
    (tabWordSpan L.T off).sub L.tabSpan := by
  intro a ⟨k, hk, ha⟩
  subst ha
  exact MemSpan.sub_range (s := L.tabSpan) off 8 hoff k hk

private theorem tabWordSpan_memDisjoint {tab : Tab} {nl nt : Nat} (L : Layout tab nl nt)
    {off1 off2 : Nat} (h1 : off1 + 8 ≤ L.tabBytes) (h2 : off2 + 8 ≤ L.tabBytes)
    (hsep : off1 + 8 ≤ off2 ∨ off2 + 8 ≤ off1) :
    MemDisjoint (tabWordSpan L.T off1) (tabWordSpan L.T off2) := by
  apply MemSpan.disjoint_to_memDisjoint (tabWordSpan_valid L h1) (tabWordSpan_valid L h2)
  have hT := L.hTValid
  have ho1 : off1 < 2 ^ 64 := by omega
  have ho2 : off2 < 2 ^ 64 := by omega
  dsimp only [MemSpan.disjoint, tabWordSpan]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho1, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho2, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem MemRel.setG {tab : Tab} {nl nt : Nat} {L : Layout tab nl nt} (hm : TabMapOk tab)
    {rmem : ByteMem} {m : _root_.L.Mem} (hrel : MemRel tab L rmem m)
    (g : GVar) (hg : g.id < tab.ng) (v : _root_.L.Word) :
    MemRel tab L (writeWord64 rmem (L.T + BitVec.ofInt 64 (tab.globOff g)) v.toBitVec) (m.setG g v) := by
  let offG := 8 * (2 + 3 * (tab.nb + tab.nw) + tab.romWords + tab.nxres + g.id)
  let sG := tabWordSpan L.T offG
  have hboundG : offG + 8 ≤ L.tabBytes := Tab.globOff_bound_nat L g hg
  have hsubG : sG.sub L.tabSpan := tabWordSpan_sub_tab L hboundG
  have heqG : MemEqOutside sG rmem (writeWord64 rmem (L.T + BitVec.ofInt 64 (tab.globOff g)) v.toBitVec) := by
    apply MemEqOutside.writeWord64
    intro k hk
    rw [Tab.globOff_eq_nat, int_mul8_ofInt]
    exact ⟨k, hk, rfl⟩
  rcases hrel with ⟨ha8, hs64, hgOld⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a haMem
    rcases ha8 a haMem with ⟨hcap, hlt, hlen, hbase, hbytes⟩
    have hltPos := hm.pos8_lt a haMem
    simp only [mem_setG_arr8]
    refine ⟨hcap, hlt, ?_, ?_, ?_⟩
    · rw [← hlen]
      apply MemEqOutside.readWord64_eq heqG
      intro k hk
      rw [Tab.len8_eq_nat, int_mul8_ofInt]
      have hdisj := tabWordSpan_memDisjoint L hboundG (Tab.len8_bound L hm a haMem) (by omega)
      exact hdisj.symm _ ⟨k, hk, rfl⟩
    · rw [← hbase]
      apply MemEqOutside.readWord64_eq heqG
      intro k hk
      rw [Tab.base8_eq_nat, int_mul8_ofInt]
      have hdisj := tabWordSpan_memDisjoint L hboundG (Tab.base8_bound L hm a haMem) (by omega)
      exact hdisj.symm _ ⟨k, hk, rfl⟩
    · intro i hi
      rw [← hbytes i hi]
      apply heqG
      have hdisj := MemDisjoint.of_sub_left hsubG
        (MemSpan.disjoint_to_memDisjoint L.tabSpan_valid (L.arr8Span_valid a) (L.h8DisjTab a).symm)
      exact hdisj.symm _ ⟨i, by dsimp only [Layout.arr8Span]; omega, rfl⟩
  · intro s64 hsMem
    rcases hs64 s64 hsMem with ⟨hcap, hlt, hlen, hbase, hwords⟩
    have hltPos := hm.pos64_lt s64 hsMem
    simp only [mem_setG_arr64]
    refine ⟨hcap, hlt, ?_, ?_, ?_⟩
    · rw [← hlen]
      apply MemEqOutside.readWord64_eq heqG
      intro k hk
      rw [Tab.len64_eq_nat, int_mul8_ofInt]
      have hdisj := tabWordSpan_memDisjoint L hboundG (Tab.len64_bound L hm s64 hsMem) (by omega)
      exact hdisj.symm _ ⟨k, hk, rfl⟩
    · rw [← hbase]
      apply MemEqOutside.readWord64_eq heqG
      intro k hk
      rw [Tab.base64_eq_nat, int_mul8_ofInt]
      have hdisj := tabWordSpan_memDisjoint L hboundG (Tab.base64_bound L hm s64 hsMem) (by omega)
      exact hdisj.symm _ ⟨k, hk, rfl⟩
    · intro i hi
      rw [← hwords i hi]
      apply MemEqOutside.readWord64_eq heqG
      intro k hk
      have hdisj := MemDisjoint.of_sub_left hsubG
        (MemSpan.disjoint_to_memDisjoint L.tabSpan_valid (L.arr64Span_valid s64) (L.h64DisjTab s64).symm)
      exact hdisj.symm _ (MemSpan.sub_range (s := L.arr64Span s64) (8 * i) 8
        (by simp only [Layout.arr64Span]; omega) k hk)
  · intro g' hg'
    dsimp only [_root_.L.Mem.setG, _root_.L.Mem.glob]
    by_cases hgg : g' = g
    · subst hgg
      simp only [ite_true]
      exact readWord64_writeWord64_self rmem _ _
    · have hneId : g'.id ≠ g.id := by intro hid; apply hgg; cases g'; cases g; cases hid; rfl
      simp only [hgg, ite_false]
      rw [← hgOld g' hg']
      apply MemEqOutside.readWord64_eq heqG
      intro k hk
      rw [Tab.globOff_eq_nat, int_mul8_ofInt]
      have hdisj := tabWordSpan_memDisjoint L hboundG (Tab.globOff_bound_nat L g' hg')
        (by dsimp only [offG]; omega)
      exact hdisj.symm _ ⟨k, hk, rfl⟩

private theorem MemRel.set8 {tab : Tab} {nl nt : Nat} {L : Layout tab nl nt} (hm : TabMapOk tab)
    {rmem : ByteMem} {m : _root_.L.Mem} (hrel : MemRel tab L rmem m)
    (a : ArrId) (ha : (TieredArray.t0 a) ∈ tab.arrAt)
    (vi vv : _root_.L.Word) (hbound : vi.toNat < (m.arr8 a).size) :
    MemRel tab L
      (RV64.storeBytes rmem (L.base8 a + BitVec.ofNat 64 vi.toNat) 1 (vv.toBitVec.extractLsb' 0 8))
      (m.set8 a vi vv) := by
  rcases hrel with ⟨ha8, hs64, hgOld⟩
  rcases ha8 a ha with ⟨hcapA, _, _, _, _⟩
  let s1 : MemSpan := ⟨L.base8 a + BitVec.ofNat 64 vi.toNat, 1⟩
  have hsub1 : s1.sub (L.arr8Span a) := by
    rintro _ ⟨k, hk, rfl⟩
    dsimp only [s1] at hk ⊢
    have hk0 : k = 0 := by omega
    subst hk0
    refine ⟨vi.toNat, by simp only [Layout.arr8Span]; omega, ?_⟩
    dsimp only [Layout.arr8Span]
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  have heq1 : MemEqOutside s1 rmem
      (RV64.storeBytes rmem (L.base8 a + BitVec.ofNat 64 vi.toNat) 1 (vv.toBitVec.extractLsb' 0 8)) := by
    apply MemEqOutside.storeBytes
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨0, by dsimp only [s1]; omega, by dsimp only [s1]⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a' ha'
    rcases ha8 a' ha' with ⟨hcap, hlt, hlen, hbase, hbytes⟩
    by_cases haa : a' = a
    · subst haa
      have harr_eq : (m.set8 a' vi vv).arr8 a' = (m.arr8 a').set! vi.toNat vv.toUInt8 := by
        simp [_root_.L.Mem.set8, _root_.L.Mem.arr8]
      rw [harr_eq]
      have hsz : ((m.arr8 a').set! vi.toNat vv.toUInt8).size = (m.arr8 a').size := by
        simp [Array.set!]
      refine ⟨by rw [hsz]; exact hcap, by rw [hsz]; exact hlt, ?_, ?_, ?_⟩
      · rw [hsz]
        refine (MemEqOutside.readWord64_eq heq1 _ (fun k hk => ?_)).trans hlen
        have hdisj := MemDisjoint.of_sub_left hsub1
          (MemSpan.disjoint_to_memDisjoint (L.arr8Span_valid a') L.tabSpan_valid (L.h8DisjTab a'))
        rw [Tab.len8_eq_nat, int_mul8_ofInt]
        exact hdisj.symm _ (MemSpan.sub_range _ 8 (Tab.len8_bound L hm a' ha) k hk)
      · refine (MemEqOutside.readWord64_eq heq1 _ (fun k hk => ?_)).trans hbase
        have hdisj := MemDisjoint.of_sub_left hsub1
          (MemSpan.disjoint_to_memDisjoint (L.arr8Span_valid a') L.tabSpan_valid (L.h8DisjTab a'))
        rw [Tab.base8_eq_nat, int_mul8_ofInt]
        exact hdisj.symm _ (MemSpan.sub_range _ 8 (Tab.base8_bound L hm a' ha) k hk)
      · intro i hi
        have hi' : i < (m.arr8 a').size := by rwa [hsz] at hi
        by_cases hiv : i = vi.toNat
        · subst hiv
          rw [storeBytes_one_self, ← uint64_toUInt8_toBitVec]
          congr 1
          have hget : ((m.arr8 a').set! vi.toNat vv.toUInt8)[vi.toNat]'hi = vv.toUInt8 := by
            simp [Array.set!, Array.setIfInBounds, hbound]
          exact hget.symm
        · have hnot : ¬s1.contains (L.base8 a' + BitVec.ofNat 64 i) := by
            rintro ⟨k, hk, heqk⟩
            dsimp only [s1] at hk
            have hk0 : k = 0 := by omega
            subst hk0
            have hval := L.h8Valid a'
            have h64i : i < 2 ^ 64 := by omega
            have h64v : vi.toNat < 2 ^ 64 := by omega
            have heqNat := congrArg BitVec.toNat heqk
            simp only [s1, BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat] at heqNat
            rw [Nat.mod_eq_of_lt h64i, Nat.mod_eq_of_lt h64v,
                Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heqNat
            omega
          rw [heq1 _ hnot, hbytes i hi']
          congr 1
          have hget : ((m.arr8 a').set! vi.toNat vv.toUInt8)[i]'hi = (m.arr8 a')[i]'hi' := by
            simp only [Array.set!, Array.setIfInBounds, hbound, ↓reduceDIte]
            exact Array.getElem_set_ne hbound hi' (Ne.symm hiv)
          exact hget.symm
    · have harr_ne : (m.set8 a vi vv).arr8 a' = m.arr8 a' := by
        simp [_root_.L.Mem.set8, _root_.L.Mem.arr8, haa]
      rw [harr_ne]
      refine ⟨hcap, hlt, ?_, ?_, ?_⟩
      · rw [← hlen]
        apply MemEqOutside.readWord64_eq heq1
        intro k hk
        have hdisj := MemDisjoint.of_sub_left hsub1
          (MemSpan.disjoint_to_memDisjoint (L.arr8Span_valid a) L.tabSpan_valid (L.h8DisjTab a))
        rw [Tab.len8_eq_nat, int_mul8_ofInt]
        exact hdisj.symm _ (MemSpan.sub_range _ 8 (Tab.len8_bound L hm a' ha') k hk)
      · rw [← hbase]
        apply MemEqOutside.readWord64_eq heq1
        intro k hk
        have hdisj := MemDisjoint.of_sub_left hsub1
          (MemSpan.disjoint_to_memDisjoint (L.arr8Span_valid a) L.tabSpan_valid (L.h8DisjTab a))
        rw [Tab.base8_eq_nat, int_mul8_ofInt]
        exact hdisj.symm _ (MemSpan.sub_range _ 8 (Tab.base8_bound L hm a' ha') k hk)
      · intro i hi
        rw [← hbytes i hi]
        apply heq1
        have hdisj := MemDisjoint.of_sub_left hsub1
          (MemSpan.disjoint_to_memDisjoint (L.arr8Span_valid a) (L.arr8Span_valid a') (L.h8Disj8 a a' (Ne.symm haa)))
        exact hdisj.symm _ ⟨i, by dsimp only [Layout.arr8Span]; omega, rfl⟩
  · intro s64 hsMem
    rcases hs64 s64 hsMem with ⟨hcap, hlt, hlen, hbase, hwords⟩
    simp only [mem_set8_arr64]
    refine ⟨hcap, hlt, ?_, ?_, ?_⟩
    · rw [← hlen]
      apply MemEqOutside.readWord64_eq heq1
      intro k hk
      have hdisj := MemDisjoint.of_sub_left hsub1
        (MemSpan.disjoint_to_memDisjoint (L.arr8Span_valid a) L.tabSpan_valid (L.h8DisjTab a))
      rw [Tab.len64_eq_nat, int_mul8_ofInt]
      exact hdisj.symm _ (MemSpan.sub_range _ 8 (Tab.len64_bound L hm s64 hsMem) k hk)
    · rw [← hbase]
      apply MemEqOutside.readWord64_eq heq1
      intro k hk
      have hdisj := MemDisjoint.of_sub_left hsub1
        (MemSpan.disjoint_to_memDisjoint (L.arr8Span_valid a) L.tabSpan_valid (L.h8DisjTab a))
      rw [Tab.base64_eq_nat, int_mul8_ofInt]
      exact hdisj.symm _ (MemSpan.sub_range _ 8 (Tab.base64_bound L hm s64 hsMem) k hk)
    · intro i hi
      rw [← hwords i hi]
      apply MemEqOutside.readWord64_eq heq1
      intro k hk
      have hdisj := MemDisjoint.of_sub_left hsub1
        (MemSpan.disjoint_to_memDisjoint (L.arr8Span_valid a) (L.arr64Span_valid s64) (L.h8Disj64 a s64))
      exact hdisj.symm _ (MemSpan.sub_range (s := L.arr64Span s64) (8 * i) 8
        (by simp only [Layout.arr64Span]; omega) k hk)
  · intro g hgBound
    simp only [mem_set8_glob]
    rw [← hgOld g hgBound]
    apply MemEqOutside.readWord64_eq heq1
    intro k hk
    have hdisj := MemDisjoint.of_sub_left hsub1
      (MemSpan.disjoint_to_memDisjoint (L.arr8Span_valid a) L.tabSpan_valid (L.h8DisjTab a))
    rw [Tab.globOff_eq_nat, int_mul8_ofInt]
    exact hdisj.symm _ (MemSpan.sub_range _ 8 (Tab.globOff_bound_nat L g hgBound) k hk)

private theorem MemRel.set64 {tab : Tab} {nl nt : Nat} {L : Layout tab nl nt} (hm : TabMapOk tab)
    {rmem : ByteMem} {m : _root_.L.Mem} (hrel : MemRel tab L rmem m)
    (a : ArrId) (ha : (TieredArray.t0 a) ∈ tab.arrAt)
    (vi vv : _root_.L.Word) (hbound : vi.toNat < (m.arr64 (TieredArray.t0 a)).size) :
    MemRel tab L
      (writeWord64 rmem (L.base64 (TieredArray.t0 a) + BitVec.ofNat 64 (8 * vi.toNat)) vv.toBitVec)
      (m.set64 (TieredArray.t0 a) vi vv) := by
  rcases hrel with ⟨ha8, hs64, hgOld⟩
  rcases hs64 (TieredArray.t0 a) ha with ⟨hcapA, _, _, _, _⟩
  let s8 : MemSpan := ⟨L.base64 (TieredArray.t0 a) + BitVec.ofNat 64 (8 * vi.toNat), 8⟩
  have hsub8 : s8.sub (L.arr64Span (TieredArray.t0 a)) := by
    rintro _ ⟨k, hk, rfl⟩
    exact MemSpan.sub_range (s := L.arr64Span (TieredArray.t0 a)) (8 * vi.toNat) 8
      (by simp only [Layout.arr64Span]; omega) k hk
  have heq8 : MemEqOutside s8 rmem
      (writeWord64 rmem (L.base64 (TieredArray.t0 a) + BitVec.ofNat 64 (8 * vi.toNat)) vv.toBitVec) :=
    MemEqOutside.writeWord64 rmem _ _ (fun k hk => ⟨k, hk, rfl⟩)
  refine ⟨?_, ?_, ?_⟩
  · intro a' ha'
    rcases ha8 a' ha' with ⟨hcap, hlt, hlen, hbase, hbytes⟩
    simp only [mem_set64_arr8]
    refine ⟨hcap, hlt, ?_, ?_, ?_⟩
    · rw [← hlen]
      apply MemEqOutside.readWord64_eq heq8
      intro k hk
      have hdisj := MemDisjoint.of_sub_left hsub8
        (MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid (TieredArray.t0 a)) L.tabSpan_valid
          (L.h64DisjTab (TieredArray.t0 a)))
      rw [Tab.len8_eq_nat, int_mul8_ofInt]
      exact hdisj.symm _ (MemSpan.sub_range _ 8 (Tab.len8_bound L hm a' ha') k hk)
    · rw [← hbase]
      apply MemEqOutside.readWord64_eq heq8
      intro k hk
      have hdisj := MemDisjoint.of_sub_left hsub8
        (MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid (TieredArray.t0 a)) L.tabSpan_valid
          (L.h64DisjTab (TieredArray.t0 a)))
      rw [Tab.base8_eq_nat, int_mul8_ofInt]
      exact hdisj.symm _ (MemSpan.sub_range _ 8 (Tab.base8_bound L hm a' ha') k hk)
    · intro i hi
      rw [← hbytes i hi]
      apply heq8
      have hdisj := MemDisjoint.of_sub_left hsub8
        (MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid (TieredArray.t0 a)) (L.arr8Span_valid a')
          (L.h8Disj64 a' (TieredArray.t0 a)).symm)
      exact hdisj.symm _ ⟨i, by dsimp only [Layout.arr8Span]; omega, rfl⟩
  · intro s64 hsMem
    rcases hs64 s64 hsMem with ⟨hcap, hlt, hlen, hbase, hwords⟩
    by_cases hss : s64 = TieredArray.t0 a
    · have harr_eq : (m.set64 (TieredArray.t0 a) vi vv).arr64 s64 = (m.arr64 s64).set! vi.toNat vv := by
        simp [_root_.L.Mem.set64, _root_.L.Mem.arr64, hss]
      rw [harr_eq]
      have hbound' : vi.toNat < (m.arr64 s64).size := by rw [hss]; exact hbound
      have hsz : ((m.arr64 s64).set! vi.toNat vv).size = (m.arr64 s64).size := by
        simp [Array.set!]
      refine ⟨by rw [hsz]; exact hcap, by rw [hsz]; exact hlt, ?_, ?_, ?_⟩
      · rw [hsz]
        refine (MemEqOutside.readWord64_eq heq8 _ (fun k hk => ?_)).trans hlen
        have hdisj := MemDisjoint.of_sub_left hsub8
          (MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid (TieredArray.t0 a)) L.tabSpan_valid
            (L.h64DisjTab (TieredArray.t0 a)))
        rw [Tab.len64_eq_nat, int_mul8_ofInt]
        exact hdisj.symm _ (MemSpan.sub_range _ 8 (Tab.len64_bound L hm s64 hsMem) k hk)
      · refine (MemEqOutside.readWord64_eq heq8 _ (fun k hk => ?_)).trans hbase
        have hdisj := MemDisjoint.of_sub_left hsub8
          (MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid (TieredArray.t0 a)) L.tabSpan_valid
            (L.h64DisjTab (TieredArray.t0 a)))
        rw [Tab.base64_eq_nat, int_mul8_ofInt]
        exact hdisj.symm _ (MemSpan.sub_range _ 8 (Tab.base64_bound L hm s64 hsMem) k hk)
      · intro i hi
        have hi' : i < (m.arr64 s64).size := by rwa [hsz] at hi
        by_cases hiv : i = vi.toNat
        · subst hiv
          have hget : ((m.arr64 s64).set! vi.toNat vv)[vi.toNat]'hi = vv := by
            simp [Array.set!, Array.setIfInBounds, hbound']
          rw [hget, hss]
          exact readWord64_writeWord64_self rmem _ _
        · have hdisj : MemDisjoint s8 ⟨L.base64 s64 + BitVec.ofNat 64 (8 * i), 8⟩ := by
            have hv : (L.base64 s64).toNat + 8 * L.cap64 s64 ≤ 2 ^ 64 := L.h64Valid s64
            have hlt_vi : vi.toNat < L.cap64 s64 := Nat.lt_of_lt_of_le hbound' hcap
            have hlt_i : i < L.cap64 s64 := Nat.lt_of_lt_of_le hi' hcap
            have h64v : 8 * vi.toNat < 2 ^ 64 := by omega
            have h64i : 8 * i < 2 ^ 64 := by omega
            have hv1 : s8.valid := by
              dsimp only [MemSpan.valid, s8]
              rw [← hss, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64v]
              rw [Nat.mod_eq_of_lt (by omega)]
              omega
            have hv2 : (⟨L.base64 s64 + BitVec.ofNat 64 (8 * i), 8⟩ : MemSpan).valid := by
              dsimp only [MemSpan.valid]
              rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64i]
              rw [Nat.mod_eq_of_lt (by omega)]
              omega
            apply MemSpan.disjoint_to_memDisjoint hv1 hv2
            dsimp only [MemSpan.disjoint, s8]
            rw [← hss, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64v]
            rw [Nat.mod_eq_of_lt (by omega)]
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64i, Nat.mod_eq_of_lt (by omega)]
            omega
          have hmemEq : readWord64 (writeWord64 rmem (L.base64 (TieredArray.t0 a) + BitVec.ofNat 64 (8 * vi.toNat)) vv.toBitVec)
              (L.base64 s64 + BitVec.ofNat 64 (8 * i)) =
              readWord64 rmem (L.base64 s64 + BitVec.ofNat 64 (8 * i)) := by
            apply MemEqOutside.readWord64_eq heq8
            intro k hk
            exact hdisj.symm _ ⟨k, hk, rfl⟩
          rw [hmemEq, hwords i hi']
          congr 1
          have hget : ((m.arr64 s64).set! vi.toNat vv)[i]'hi = (m.arr64 s64)[i]'hi' := by
            simp only [Array.set!, Array.setIfInBounds, hbound', ↓reduceDIte]
            exact Array.getElem_set_ne hbound' hi' (Ne.symm hiv)
          exact hget.symm
    · have harr_ne : (m.set64 (TieredArray.t0 a) vi vv).arr64 s64 = m.arr64 s64 := by
        simp [_root_.L.Mem.set64, _root_.L.Mem.arr64, hss]
      rw [harr_ne]
      refine ⟨hcap, hlt, ?_, ?_, ?_⟩
      · rw [← hlen]
        apply MemEqOutside.readWord64_eq heq8
        intro k hk
        have hdisj := MemDisjoint.of_sub_left hsub8
          (MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid (TieredArray.t0 a)) L.tabSpan_valid
            (L.h64DisjTab (TieredArray.t0 a)))
        rw [Tab.len64_eq_nat, int_mul8_ofInt]
        exact hdisj.symm _ (MemSpan.sub_range _ 8 (Tab.len64_bound L hm s64 hsMem) k hk)
      · rw [← hbase]
        apply MemEqOutside.readWord64_eq heq8
        intro k hk
        have hdisj := MemDisjoint.of_sub_left hsub8
          (MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid (TieredArray.t0 a)) L.tabSpan_valid
            (L.h64DisjTab (TieredArray.t0 a)))
        rw [Tab.base64_eq_nat, int_mul8_ofInt]
        exact hdisj.symm _ (MemSpan.sub_range _ 8 (Tab.base64_bound L hm s64 hsMem) k hk)
      · intro i hi
        rw [← hwords i hi]
        apply MemEqOutside.readWord64_eq heq8
        intro k hk
        have hdisj := MemDisjoint.of_sub_left hsub8
          (MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid (TieredArray.t0 a)) (L.arr64Span_valid s64)
            (L.h64Disj64 (TieredArray.t0 a) s64 (Ne.symm hss)))
        exact hdisj.symm _ (MemSpan.sub_range (s := L.arr64Span s64) (8 * i) 8
          (by simp only [Layout.arr64Span]; omega) k hk)
  · intro g hgBound
    simp only [mem_set64_glob]
    rw [← hgOld g hgBound]
    apply MemEqOutside.readWord64_eq heq8
    intro k hk
    have hdisj := MemDisjoint.of_sub_left hsub8
      (MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid (TieredArray.t0 a)) L.tabSpan_valid
        (L.h64DisjTab (TieredArray.t0 a)))
    rw [Tab.globOff_eq_nat, int_mul8_ofInt]
    exact hdisj.symm _ (MemSpan.sub_range _ 8 (Tab.globOff_bound_nat L g hgBound) k hk)

private theorem compileStorePair_sim_gen (lm : LinkModel) (env : CodeEnvGen lm) (hm : TabMapOk env.tab)
    {nlocals ntemps : Nat} (L : Layout env.tab nlocals ntemps)
    (m : _root_.L.Mem) (loc : _root_.L.Locals)
    (pre tail : List AsmItem) (i e : Expr)
    (hi : CoreExpr env.tab i) (he : CoreExpr env.tab e)
    (hvi : exprVarsLt nlocals i) (hve : exprVarsLt nlocals e)
    (htmp : max (maxTempsExpr i) (1 + maxTempsExpr e) ≤ ntemps)
    (hlink : lm.linkSpec (pre ++ compileStorePair env.tab nlocals i e ++ tail) = .ok (env.code, env.labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (compileStorePair env.tab nlocals i e)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = L.sp)
    (hmemRel : MemRel env.tab L st.mem m) (hframeOk : FrameOk L st.mem nlocals loc) :
    match evalE i ⟨m, loc⟩ with
    | .ok (vi, _) =>
      match evalE e ⟨m, loc⟩ with
      | .ok (vv, _) =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (compileStorePair env.tab nlocals i e))) ∧
          st'.getReg AbiReg.t0 = vi.toBitVec ∧
          st'.getReg AbiReg.a0 = vv.toBitVec ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan L.sp nlocals 0 ntemps) st.mem st'.mem
      | .error _ =>
        ∃ k st', RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedRegs st st' ∧
          MemEqOutside (tempSpan L.sp nlocals 0 ntemps) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan L.sp nlocals 0 ntemps) st.mem st'.mem := by
  cases hsi : emitSimpleExpr env.tab AbiReg.t0 AbiReg.t1 i with
  | some ci =>
    have hspEq : compileStorePair env.tab nlocals i e = compileE env.tab nlocals 0 e ++ ci := by
      simp [compileStorePair, hsi]
    have htw : lm.totalSize (compileStorePair env.tab nlocals i e) =
        lm.totalSize (compileE env.tab nlocals 0 e) + lm.totalSize ci := by rw [hspEq, lm.totalSize_append]
    have hiOk : ∃ vi, evalE i ⟨m, loc⟩ = .ok (vi, ⟨m, loc⟩) := by
      cases i <;> simp [emitSimpleExpr] at hsi <;> exact ⟨_, rfl⟩
    rcases hiOk with ⟨vi0, hvi0⟩
    have re := evalExpr_sim_gen lm env hm L m loc pre (ci ++ tail) 0 e he hve (by omega)
      (by simpa only [hspEq, List.append_assoc] using hlink) (by rw [htw] at h64; omega)
      st hpc hgp hsp hmemRel hframeOk
    rcases he.evalE_pure ⟨m, loc⟩ with ⟨vv, hvv⟩ | hvv
    · simp only [hvv] at re; obtain ⟨ke, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := re
      obtain ⟨vi, ki, st2, hviE, hrun2, hpc2, ht0_2, hoth2, hmem2⟩ :=
        emitSimpleExpr_sim_gen lm env L m loc (pre ++ compileE env.tab nlocals 0 e) tail AbiReg.t0 AbiReg.t1
          (by decide) (by decide) (by decide) (by decide) (by decide) i ci hsi hi hvi
          (by simpa only [hspEq, List.append_assoc] using hlink)
          (by rw [lm.totalSize_append]; rw [htw] at h64; omega)
          st1 (show st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ _)) from by rw [lm.totalSize_append]; exact hpc1)
          (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
          (memRel_of_eqOutside_temp hm (Nat.zero_le _) heq1 hmemRel)
          (frameOk_of_eqOutside_temp (Nat.zero_le _) heq1 hframeOk)
      simp only [hviE, hvv]
      exact ⟨ke + ki, st2, by rw [run_add, hrun1]; exact hrun2,
        by rw [hpc2, lm.totalSize_append, htw, Nat.add_assoc], ht0_2,
        (hoth2 _ (by decide) (by decide)).trans ha0_1,
        hpres1.trans ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
          hoth2 _ (by decide) (by decide),
          hoth2 _ (by decide) (by decide)⟩, hmem2 ▸ heq1⟩
    · simp only [hvi0, hvv] at re ⊢; exact re
  | none =>
    cases hse : emitSimpleExpr env.tab AbiReg.a0 AbiReg.t1 e with
    | some ce =>
      have hspEq : compileStorePair env.tab nlocals i e =
          compileE env.tab nlocals 0 i ++ [Asm.mv AbiReg.t0 AbiReg.a0] ++ ce := by
        simp [compileStorePair, hsi, hse]
      have htwMv : lm.totalSize [Asm.mv AbiReg.t0 AbiReg.a0] = 1 := by simp [Asm.mv, lm.itemSize_instr]
      have htw : lm.totalSize (compileStorePair env.tab nlocals i e) =
          lm.totalSize (compileE env.tab nlocals 0 i) + 1 + lm.totalSize ce := by
        rw [hspEq, lm.totalSize_append, lm.totalSize_append, htwMv]
      have ri := evalExpr_sim_gen lm env hm L m loc pre ([Asm.mv AbiReg.t0 AbiReg.a0] ++ ce ++ tail) 0 i hi hvi (by omega)
        (by simpa only [hspEq, List.append_assoc] using hlink) (by rw [htw] at h64; omega)
        st hpc hgp hsp hmemRel hframeOk
      rcases hi.evalE_pure ⟨m, loc⟩ with ⟨vi, hviE⟩ | hviE
      · simp only [hviE] at ri; obtain ⟨ki, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := ri
        have hs := step_item_instr_lm lm env.hrom (pre ++ compileE env.tab nlocals 0 i) (ce ++ tail)
          (.aluImm .addi AbiReg.t0 AbiReg.a0 0#12)
          (by simpa only [hspEq, Asm.mv, List.append_assoc] using hlink)
          (by rw [lm.totalSize_append]; rw [htw] at h64; omega) st1 (show st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ _)) from by rw [lm.totalSize_append]; exact hpc1)
        let st2 := stepReg st1 AbiReg.t0 (st1.getReg AbiReg.a0 + sextImm12 0#12) (st1.pc + 4#64)
        have hst2_t0 : st2.getReg AbiReg.t0 = vi.toBitVec := by
          rw [getReg_stepReg_eq st1 AbiReg.t0 (by decide), ha0_1, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero]
        have hp12 : PreservedRegs st1 st2 :=
          ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
           getReg_stepReg_ne _ _ _ (by decide) _ _,
           getReg_stepReg_ne _ _ _ (by decide) _ _⟩
        have hpc2 : st2.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ compileE env.tab nlocals 0 i ++ [Asm.mv AbiReg.t0 AbiReg.a0])) := by
          change st1.pc + 4#64 = _
          rw [pc_add_4_ofNat st1.pc hpc1, lm.totalSize_append, lm.totalSize_append, htwMv]
        obtain ⟨vv, ke, st3, hvvE, hrun3, hpc3, ha0_3, hoth3, hmem3⟩ :=
          emitSimpleExpr_sim_gen lm env L m loc (pre ++ compileE env.tab nlocals 0 i ++ [Asm.mv AbiReg.t0 AbiReg.a0])
            tail AbiReg.a0 AbiReg.t1 (by decide) (by decide) (by decide) (by decide) (by decide) e ce hse he hve
            (by simpa only [hspEq, List.append_assoc] using hlink)
            (by rw [lm.totalSize_append, lm.totalSize_append, htwMv]; rw [htw] at h64; omega)
            st2 hpc2 (hp12.gp.trans (hpres1.gp.trans hgp)) (hp12.sp.trans (hpres1.sp.trans hsp))
            (memRel_of_eqOutside_temp hm (Nat.zero_le _) heq1 hmemRel)
            (frameOk_of_eqOutside_temp (Nat.zero_le _) heq1 hframeOk)
        simp only [hviE, hvvE]
        refine ⟨ki + 1 + ke, st3,
          by rw [run_add, run_add, hrun1]; dsimp only; rw [run_one_cont _ _ _ (by rw [hs]; rfl)]; exact hrun3,
          by rw [hpc3, lm.totalSize_append, lm.totalSize_append, htwMv, htw]; congr 2; omega,
          (hoth3 _ (by decide) (by decide)).trans hst2_t0, ha0_3,
          hpres1.trans (hp12.trans ⟨hoth3 _ (by decide) (by decide), hoth3 _ (by decide) (by decide),
            hoth3 _ (by decide) (by decide),
            hoth3 _ (by decide) (by decide)⟩), hmem3 ▸ heq1⟩
      · simp only [hviE] at ri ⊢; exact ri
    | none =>
      have hspEq : compileStorePair env.tab nlocals i e =
          compileE env.tab nlocals 0 i ++
          storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + 0)) ++
          compileE env.tab nlocals 1 e ++
          loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nlocals + 0)) := by
        simp [compileStorePair, hsi, hse, Nat.add_zero]
      have hszEq : lm.totalSize (compileStorePair env.tab nlocals i e) =
          lm.totalSize (compileE env.tab nlocals 0 i ++
            storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + 0)) ++
            compileE env.tab nlocals 1 e ++
            loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nlocals + 0))) := by rw [hspEq]
      have hl' : lm.linkSpec (pre ++ (compileE env.tab nlocals 0 i ++
          storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + 0)) ++
          compileE env.tab nlocals 1 e ++
          loadMemOff .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (slotOff (nlocals + 0))) ++ tail) =
          .ok (env.code, env.labels) := by rw [← hspEq]; exact hlink
      rw [hszEq]
      have rpair := two_exprs_pair_sim_gen lm env hm L m loc pre tail 0 i e hi he (by omega)
        (fun p q t s h1 h2 h3 h4 h5 h6 h7 h8 =>
          evalExpr_sim_gen lm env hm L m loc p q t i hi hvi h1 h2 h3 s h4 h5 h6 h7 h8)
        (fun p q t s h1 h2 h3 h4 h5 h6 h7 h8 =>
          evalExpr_sim_gen lm env hm L m loc p q t e he hve h1 h2 h3 s h4 h5 h6 h7 h8)
        (by omega) (by omega) hl' (by rw [← hszEq]; exact h64) st hpc hgp hsp hmemRel hframeOk
      cases h1 : evalE i ⟨m, loc⟩ <;> simp only [h1] at rpair ⊢
      · exact rpair
      · cases h2 : evalE e ⟨m, loc⟩ <;> simp only [h2] at rpair ⊢
        · exact rpair
        · exact rpair

private theorem st64_ok_tail_gen (lm : LinkModel) (env : CodeEnvGen lm) (hm : TabMapOk env.tab)
    {nlocals ntemps : Nat} (L : Layout env.tab nlocals ntemps)
    (m : _root_.L.Mem) (loc : _root_.L.Locals)
    (pre3 post : List AsmItem) (a : ArrId) (ha : (TieredArray.t0 a) ∈ env.tab.arrAt)
    (vi vv : _root_.L.Word) (st3 : State)
    (hlink3 : lm.linkSpec (pre3 ++
      (loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base64 (TieredArray.t0 a)) ++
        [Asm.slli AbiReg.t2 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2,
         Asm.sd AbiReg.t1 AbiReg.a0 0#12]) ++
      post) = .ok (env.code, env.labels))
    (h64_3 : 4 * (lm.totalSize pre3 +
      lm.totalSize (loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base64 (TieredArray.t0 a))) + 3) < 2 ^ 64)
    (hpc3 : st3.pc = BitVec.ofNat 64 (4 * lm.totalSize pre3))
    (hgp3 : st3.getReg AbiReg.gp = L.T) (_hsp3 : st3.getReg AbiReg.sp = L.sp)
    (ht0_3 : st3.getReg AbiReg.t0 = vi.toBitVec) (ha0_3 : st3.getReg AbiReg.a0 = vv.toBitVec)
    (hmemRel3 : MemRel env.tab L st3.mem m) (hframeOk3 : FrameOk L st3.mem nlocals loc)
    (hbound : vi.toNat < (m.arr64 (TieredArray.t0 a)).size) :
    ∃ k st', RV64.run env.rom k st3 = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre3 +
        lm.totalSize (loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base64 (TieredArray.t0 a))) + 3)) ∧
      PreservedRegs st3 st' ∧
      MemRel env.tab L st'.mem (m.set64 (TieredArray.t0 a) vi vv) ∧
      FrameOk L st'.mem nlocals loc := by
  let cbase := loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base64 (TieredArray.t0 a))
  have htw_cb : lm.totalSize (loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base64 (TieredArray.t0 a))) =
      lm.totalSize cbase := rfl
  let cst : List AsmItem :=
    [Asm.slli AbiReg.t2 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2,
     Asm.sd AbiReg.t1 AbiReg.a0 0#12]
  have hlistBase : pre3 ++ cbase ++ (cst ++ post) = pre3 ++ (cbase ++ cst) ++ post := by
    simp only [List.append_assoc]
  have hlinkBase : lm.linkSpec (pre3 ++ cbase ++ (cst ++ post)) = .ok (env.code, env.labels) := by
    rw [hlistBase]; exact hlink3
  have halBase : isAligned (st3.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.base64 (TieredArray.t0 a))) 8 = true := by
    rw [hgp3, Tab.base64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
  obtain ⟨st4, hrun4, hoth4, ht1_4, hmem4, hpc4⟩ :=
    loadMemOff_ld_correct_lm lm env.hrom pre3 (cst ++ post)
      AbiReg.t1 AbiReg.gp AbiReg.t2 (by decide) (by decide) (by decide)
      (env.tab.base64 (TieredArray.t0 a)) hlinkBase (by rw [htw_cb] at h64_3; omega) st3 hpc3 halBase
  have hpres34 : PreservedRegs st3 st4 :=
    ⟨hoth4 _ (by decide) (by decide), hoth4 _ (by decide) (by decide),
     hoth4 _ (by decide) (by decide), hoth4 _ (by decide) (by decide)⟩
  rcases hmemRel3.2.1 (TieredArray.t0 a) ha with ⟨hcapA, _, _, hbaseR, _⟩
  have ht1_4' : st4.getReg AbiReg.t1 = L.base64 (TieredArray.t0 a) := by rw [ht1_4, hgp3, hbaseR]
  have ht0_4 : st4.getReg AbiReg.t0 = vi.toBitVec := by rw [hoth4 AbiReg.t0 (by decide) (by decide), ht0_3]
  have ha0_4 : st4.getReg AbiReg.a0 = vv.toBitVec := by rw [hoth4 AbiReg.a0 (by decide) (by decide), ha0_3]
  have htw4 : lm.totalSize (pre3 ++ cbase) = lm.totalSize pre3 + lm.totalSize cbase := (lm.totalSize_append) _ _
  have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre3 ++ cbase)) := by
    rw [htw4]; exact hpc4
  have hlistSll : (pre3 ++ cbase) ++ [.instr (.shImm .slli AbiReg.t2 AbiReg.t0 3#6)] ++
      ([Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2, Asm.sd AbiReg.t1 AbiReg.a0 0#12] ++ post) =
      pre3 ++ (cbase ++ cst) ++ post := by
    simp only [cst, Asm.slli, Asm.add, Asm.sd, List.append_assoc, List.cons_append, List.nil_append]
  have hlinkSll : lm.linkSpec ((pre3 ++ cbase) ++ [.instr (.shImm .slli AbiReg.t2 AbiReg.t0 3#6)] ++
      ([Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2, Asm.sd AbiReg.t1 AbiReg.a0 0#12] ++ post)) =
      .ok (env.code, env.labels) := by
    rw [hlistSll]; exact hlink3
  have hs5 := step_item_instr_lm lm env.hrom (pre3 ++ cbase)
    ([Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2, Asm.sd AbiReg.t1 AbiReg.a0 0#12] ++ post)
    (.shImm .slli AbiReg.t2 AbiReg.t0 3#6) hlinkSll (by rw [htw4, ← htw_cb]; omega) st4 hpc4'
  let st5 := stepReg st4 AbiReg.t2 (st4.getReg AbiReg.t0 <<< 3) (st4.pc + 4#64)
  have hpres45 : PreservedRegs st4 st5 :=
    ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
     getReg_stepReg_ne _ _ _ (by decide) _ _,
     getReg_stepReg_ne _ _ _ (by decide) _ _⟩
  have htw5 : lm.totalSize (pre3 ++ cbase ++ [.instr (.shImm .slli AbiReg.t2 AbiReg.t0 3#6)]) =
      lm.totalSize (pre3 ++ cbase) + 1 := by
    rw [lm.totalSize_append, lm.totalSize_instr]
  have hpc5 : st5.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre3 ++ cbase ++
      [.instr (.shImm .slli AbiReg.t2 AbiReg.t0 3#6)])) := by
    change st4.pc + 4#64 = _; rw [pc_add_4_ofNat st4.pc hpc4', htw5]
  have hlistAdd : (pre3 ++ cbase ++ [.instr (.shImm .slli AbiReg.t2 AbiReg.t0 3#6)]) ++
      [.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.t2)] ++
      ([Asm.sd AbiReg.t1 AbiReg.a0 0#12] ++ post) = pre3 ++ (cbase ++ cst) ++ post := by
    simp only [cst, Asm.slli, Asm.add, Asm.sd, List.append_assoc, List.cons_append, List.nil_append]
  have hlinkAdd : lm.linkSpec ((pre3 ++ cbase ++ [.instr (.shImm .slli AbiReg.t2 AbiReg.t0 3#6)]) ++
      [.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.t2)] ++
      ([Asm.sd AbiReg.t1 AbiReg.a0 0#12] ++ post)) = .ok (env.code, env.labels) := by
    rw [hlistAdd]; exact hlink3
  have hs6 := step_item_instr_lm lm env.hrom
    (pre3 ++ cbase ++ [.instr (.shImm .slli AbiReg.t2 AbiReg.t0 3#6)])
    ([Asm.sd AbiReg.t1 AbiReg.a0 0#12] ++ post)
    (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.t2) hlinkAdd
    (by rw [htw5, htw4, ← htw_cb]; omega) st5 hpc5
  let st6 := stepReg st5 AbiReg.t1 (st5.getReg AbiReg.t1 + st5.getReg AbiReg.t2) (st5.pc + 4#64)
  have hpres56 : PreservedRegs st5 st6 :=
    ⟨getReg_stepReg_ne _ _ _ (by decide) _ _, getReg_stepReg_ne _ _ _ (by decide) _ _,
     getReg_stepReg_ne _ _ _ (by decide) _ _,
     getReg_stepReg_ne _ _ _ (by decide) _ _⟩
  have htw6 : lm.totalSize (pre3 ++ cbase ++ [.instr (.shImm .slli AbiReg.t2 AbiReg.t0 3#6)] ++
      [.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.t2)]) = lm.totalSize (pre3 ++ cbase) + 2 := by
    rw [lm.totalSize_append, htw5, lm.totalSize_instr]
  have hpc6 : st6.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre3 ++ cbase ++
      [.instr (.shImm .slli AbiReg.t2 AbiReg.t0 3#6)] ++ [.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.t2)])) := by
    change st5.pc + 4#64 = _; rw [pc_add_4_ofNat st5.pc hpc5, htw6, htw5]
  have hlistSd : (pre3 ++ cbase ++ [.instr (.shImm .slli AbiReg.t2 AbiReg.t0 3#6)] ++
      [.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.t2)]) ++
      [.instr (.store .sd AbiReg.t1 AbiReg.a0 0#12)] ++ post = pre3 ++ (cbase ++ cst) ++ post := by
    simp only [cst, Asm.slli, Asm.add, Asm.sd, List.append_assoc, List.cons_append, List.nil_append]
  have hlinkSd : lm.linkSpec ((pre3 ++ cbase ++ [.instr (.shImm .slli AbiReg.t2 AbiReg.t0 3#6)] ++
      [.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.t2)]) ++
      [.instr (.store .sd AbiReg.t1 AbiReg.a0 0#12)] ++ post) = .ok (env.code, env.labels) := by
    rw [hlistSd]; exact hlink3
  have hs7 := step_item_instr_lm lm env.hrom
    (pre3 ++ cbase ++ [.instr (.shImm .slli AbiReg.t2 AbiReg.t0 3#6)] ++
      [.instr (.alu .add AbiReg.t1 AbiReg.t1 AbiReg.t2)])
    post (.store .sd AbiReg.t1 AbiReg.a0 0#12) hlinkSd
    (by rw [htw6, htw4, ← htw_cb]; omega) st6 hpc6
  have hshift : vi.toBitVec <<< 3 = BitVec.ofNat 64 (8 * vi.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, UInt64.toNat_toBitVec, Nat.shiftLeft_eq,
        show (2 ^ 3 : Nat) = 8 by decide, Nat.mul_comm]
  have ht1_5 : st5.getReg AbiReg.t1 = L.base64 (TieredArray.t0 a) := by
    change (stepReg st4 AbiReg.t2 _ _).getReg AbiReg.t1 = _
    rw [getReg_stepReg_ne st4 AbiReg.t2 AbiReg.t1 (by decide) _ _, ht1_4']
  have ht2_5 : st5.getReg AbiReg.t2 = BitVec.ofNat 64 (8 * vi.toNat) := by
    change (stepReg st4 AbiReg.t2 _ _).getReg AbiReg.t2 = _
    rw [getReg_stepReg_eq st4 AbiReg.t2 (by decide) _ _, ht0_4, hshift]
  have haddr6 : st6.getReg AbiReg.t1 + sextImm12 0#12 =
      L.base64 (TieredArray.t0 a) + BitVec.ofNat 64 (8 * vi.toNat) := by
    have hz : sextImm12 0#12 = 0#64 := rfl
    change (stepReg st5 AbiReg.t1 _ _).getReg AbiReg.t1 + sextImm12 0#12 = _
    rw [hz, BitVec.add_zero, getReg_stepReg_eq st5 AbiReg.t1 (by decide) _ _, ht1_5, ht2_5]
  have ha0_6 : st6.getReg AbiReg.a0 = vv.toBitVec := by
    change (stepReg st5 AbiReg.t1 _ _).getReg AbiReg.a0 = _
    rw [getReg_stepReg_ne st5 AbiReg.t1 AbiReg.a0 (by decide) _ _]
    change (stepReg st4 AbiReg.t2 _ _).getReg AbiReg.a0 = _
    rw [getReg_stepReg_ne st4 AbiReg.t2 AbiReg.a0 (by decide) _ _, ha0_4]
  have hal6 : isAligned (st6.getReg AbiReg.t1 + sextImm12 0#12) 8 = true := by
    rw [haddr6]; exact isAligned8_add_mul8 _ (L.h64Align _) _
  let st7 : State :=
    { st6 with pc := st6.pc + 4#64,
               mem := writeWord64 st6.mem (L.base64 (TieredArray.t0 a) + BitVec.ofNat 64 (8 * vi.toNat)) vv.toBitVec }
  have hal6' : isAligned (L.base64 (TieredArray.t0 a) + BitVec.ofNat 64 (8 * vi.toNat)) 8 = true :=
    isAligned8_add_mul8 _ (L.h64Align _) _
  have hmem6 : st6.mem = st3.mem := by
    change st5.mem = _; change st4.mem = _; exact hmem4
  have hmemRel6 : MemRel env.tab L st6.mem m := by rwa [hmem6]
  have hframeOk6 : FrameOk L st6.mem nlocals loc := by rwa [hmem6]
  refine ⟨lm.totalSize cbase + 3, st7, ?_, ?_,
    hpres34.trans (hpres45.trans (hpres56.trans ⟨rfl, rfl, rfl, rfl⟩)), ?_, ?_⟩
  · change RV64.run env.rom (lm.totalSize cbase + (1 + (1 + 1))) st3 = _
    rw [run_add, hrun4]; dsimp only
    rw [run_add, run_one_cont _ _ st5 (by rw [hs5]; simp only [execInstr, evalShiftImm]; rfl)]; dsimp only
    rw [run_add, run_one_cont _ _ st6 (by rw [hs6]; rfl)]; dsimp only
    exact run_one_cont _ _ st7 (by
      rw [hs7]; simp only [execInstr, haddr6, ha0_6, hal6', ↓reduceIte]; rfl)
  · change st6.pc + 4#64 = _; rw [pc_add_4_ofNat st6.pc hpc6, htw6, htw4]
  · exact MemRel.set64 hm hmemRel6 a ha vi vv hbound
  · intro x hx
    rw [← hframeOk6 x hx]
    apply MemEqOutside.readWord64_eq
      (MemEqOutside.writeWord64 st6.mem _ _ (s := L.arr64Span (TieredArray.t0 a)) (fun k hk =>
        MemSpan.sub_range (s := L.arr64Span (TieredArray.t0 a)) (8 * vi.toNat) 8
          (by simp only [Layout.arr64Span]; omega) k hk))
    intro k hk
    have hdisj := MemDisjoint.of_sub_left
      (slotSpan_sub_frame (by omega : 1 + x < 1 + nlocals + ntemps))
      (MemSpan.disjoint_to_memDisjoint L.hFrameValid (L.arr64Span_valid (TieredArray.t0 a))
        (L.h64DisjFrame (TieredArray.t0 a)).symm)
    rw [slotOff_ofInt]
    exact hdisj _ ⟨k, hk, rfl⟩

private theorem st64_sim_gen (lm : LinkModel) (env : CodeEnvGen lm) (hm : TabMapOk env.tab)
    {nlocals ntemps : Nat} (L : Layout env.tab nlocals ntemps)
    (p : Prog) (kfn : Stmt → M Sig) (pfx : String) (lblId : Nat) (brkLbl : Option String) (retLbl : String) (retTgt : Nat)
    (m : _root_.L.Mem) (loc : _root_.L.Locals)
    (pre post : List AsmItem) (a : ArrId) (i e : Expr)
    (ha : (TieredArray.t0 a) ∈ env.tab.arrAt) (hi : CoreExpr env.tab i) (he : CoreExpr env.tab e)
    (hvi : exprVarsLt nlocals i) (hve : exprVarsLt nlocals e)
    (htmp : max (maxTempsExpr i) (1 + maxTempsExpr e) ≤ ntemps)
    (hlink : lm.linkSpec (pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl (.st64 a i e)).1 ++ post) =
        .ok (env.code, env.labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (compileS env.tab nlocals pfx lblId brkLbl retLbl (.st64 a i e)).1) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = L.sp)
    (hmemRel : MemRel env.tab L st.mem m) (hframeOk : FrameOk L st.mem nlocals loc) :
    match _root_.L.step p kfn (.st64 a i e) ⟨m, loc⟩ with
    | .ok (.normal, ⟨m', loc'⟩) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (compileS env.tab nlocals pfx lblId brkLbl retLbl (.st64 a i e)).1)) ∧
        PreservedRegs st st' ∧ MemRel env.tab L st'.mem m' ∧ FrameOk L st'.mem nlocals loc'
    | .ok (.ret vs, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * retTgt) ∧ PreservedRegs st st' ∧
        (∀ i, i < min (max 1 vs.length) env.tab.nres → st'.getReg (resReg i) = (vs.getD i 0).toBitVec)
    | .error .oob =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧ PreservedRegs st st'
    | .error (.abort code) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.abortTarget) ∧
        st'.getReg AbiReg.a0 = code.toBitVec ∧ PreservedRegs st st'
    | _ => False := by
  let seq := compileStorePair env.tab nlocals i e
  let clen := loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.len64 (TieredArray.t0 a))
  let cbr : List AsmItem := [Asm.bgeu AbiReg.t0 AbiReg.t1 errLabel]
  let cbase := loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base64 (TieredArray.t0 a))
  let cst : List AsmItem :=
    [Asm.slli AbiReg.t2 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2,
     Asm.sd AbiReg.t1 AbiReg.a0 0#12]
  have hcs : (compileS env.tab nlocals pfx lblId brkLbl retLbl (.st64 a i e)).1 =
      seq ++ clen ++ cbr ++ cbase ++ cst := by
    dsimp only [compileS, seq, clen, cbr, cbase, cst]
  let brSz := lm.itemSize (.br .bgeu AbiReg.t0 AbiReg.t1 errLabel)
  have htw_cs : lm.totalSize (compileS env.tab nlocals pfx lblId brkLbl retLbl (.st64 a i e)).1 =
      lm.totalSize seq + lm.totalSize clen + brSz + lm.totalSize cbase + 3 := by
    rw [hcs]; simp only [lm.totalSize_append]
    have h1 : lm.totalSize cbr = brSz := by simp [cbr, Asm.bgeu, brSz]
    have h2 : lm.totalSize cst = 3 := by simp [cst, Asm.slli, Asm.add, Asm.sd, lm.itemSize_instr]
    omega
  have htw_seq : lm.totalSize (compileStorePair env.tab nlocals i e) = lm.totalSize seq := rfl
  have hlistSeq : pre ++ compileStorePair env.tab nlocals i e ++
      (clen ++ cbr ++ cbase ++ cst ++ post) =
      pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl (.st64 a i e)).1 ++ post := by
    rw [hcs]; simp only [seq, List.append_assoc]
  have hlinkSeq : lm.linkSpec (pre ++ compileStorePair env.tab nlocals i e ++
      (clen ++ cbr ++ cbase ++ cst ++ post)) = .ok (env.code, env.labels) := by
    rw [hlistSeq]; exact hlink
  have rseq := compileStorePair_sim_gen lm env hm L m loc pre (clen ++ cbr ++ cbase ++ cst ++ post)
    i e hi he hvi hve htmp hlinkSeq (by rw [htw_cs] at h64; omega)
    st hpc hgp hsp hmemRel hframeOk
  rcases hi.evalE_pure ⟨m, loc⟩ with ⟨vi, hviE⟩ | hviE
  · rcases he.evalE_pure ⟨m, loc⟩ with ⟨vv, hvvE⟩ | hvvE
    · simp only [hviE, hvvE] at rseq
      obtain ⟨kseq, st1, hrun1, hpc1, ht0_1, ha0_1, hpres1, heq1⟩ := rseq
      have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.gp.trans hgp
      have hsp1 : st1.getReg AbiReg.sp = L.sp := hpres1.sp.trans hsp
      have hmemRel1 := memRel_of_eqOutside_temp hm (Nat.zero_le _) heq1 hmemRel
      have hframeOk1 := frameOk_of_eqOutside_temp (Nat.zero_le _) heq1 hframeOk
      rcases hmemRel1.2.1 (TieredArray.t0 a) ha with ⟨_, hlt64, hlenR, _, _⟩
      have htw_p1 : lm.totalSize (pre ++ seq) = lm.totalSize pre + lm.totalSize seq := (lm.totalSize_append) _ _
      have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ seq)) := by
        rw [htw_p1, ← htw_seq]; exact hpc1
      have hlistLen : (pre ++ seq) ++ clen ++ (cbr ++ cbase ++ cst ++ post) =
          pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl (.st64 a i e)).1 ++ post := by
        rw [hcs]; simp only [List.append_assoc]
      have hlinkLen : lm.linkSpec ((pre ++ seq) ++ clen ++ (cbr ++ cbase ++ cst ++ post)) =
          .ok (env.code, env.labels) := by
        rw [hlistLen]; exact hlink
      have halLen : isAligned (st1.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.len64 (TieredArray.t0 a))) 8 = true := by
        rw [hgp1, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
      have htw_clen : lm.totalSize (loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.len64 (TieredArray.t0 a))) = lm.totalSize clen := rfl
      obtain ⟨st2, hrun2, hoth2, ht1_2, hmem2, hpc2⟩ :=
        loadMemOff_ld_correct_lm lm env.hrom (pre ++ seq) (cbr ++ cbase ++ cst ++ post)
          AbiReg.t1 AbiReg.gp AbiReg.t2 (by decide) (by decide) (by decide)
          (env.tab.len64 (TieredArray.t0 a)) hlinkLen
          (by rw [htw_clen, htw_p1]; rw [htw_cs] at h64; omega)
          st1 hpc1' halLen
      have hpres12 : PreservedRegs st1 st2 :=
        ⟨hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide),
         hoth2 _ (by decide) (by decide), hoth2 _ (by decide) (by decide)⟩
      have hgp2 : st2.getReg AbiReg.gp = L.T := hpres12.gp.trans hgp1
      have hsp2 : st2.getReg AbiReg.sp = L.sp := hpres12.sp.trans hsp1
      have ht0_2 : st2.getReg AbiReg.t0 = vi.toBitVec := by rw [hoth2 AbiReg.t0 (by decide) (by decide), ht0_1]
      have ha0_2 : st2.getReg AbiReg.a0 = vv.toBitVec := by rw [hoth2 AbiReg.a0 (by decide) (by decide), ha0_1]
      have ht1_2' : st2.getReg AbiReg.t1 = BitVec.ofNat 64 (m.arr64 (TieredArray.t0 a)).size := by
        rw [ht1_2, hgp1, hlenR]
      have htw2 : lm.totalSize (pre ++ seq ++ clen) = lm.totalSize pre + lm.totalSize seq + lm.totalSize clen := by
        rw [(lm.totalSize_append), htw_p1]
      have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ seq ++ clen)) := by
        rw [htw2, ← htw_p1, ← htw_clen]; exact hpc2
      have hlistBr : (pre ++ seq ++ clen) ++ [Asm.bgeu AbiReg.t0 AbiReg.t1 errLabel] ++
          (cbase ++ cst ++ post) =
          pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl (.st64 a i e)).1 ++ post := by
        rw [hcs]; simp only [cbr, List.append_assoc]
      have hlinkBr : lm.linkSpec ((pre ++ seq ++ clen) ++ [Asm.bgeu AbiReg.t0 AbiReg.t1 errLabel] ++
          (cbase ++ cst ++ post)) = .ok (env.code, env.labels) := by
        rw [hlistBr]; exact hlink
      obtain ⟨tgt, kbr, st3, _, hlook, hrunBr, hpc3_raw, hreg3, hmem3⟩ :=
        step_item_br_lm lm env.hrom (pre ++ seq ++ clen) (cbase ++ cst ++ post) .bgeu AbiReg.t0 AbiReg.t1 errLabel
          hlinkBr (by decide) (by rw [htw2]; rw [htw_cs] at h64; simp only [Asm.bgeu, brSz] at *; omega)
          st2 hpc2'
      have htgt : tgt = env.errTarget := by rw [env.herrLbl] at hlook; cases hlook; rfl
      subst htgt
      by_cases hbound : vi.toNat < (m.arr64 (TieredArray.t0 a)).size
      · have hstep : _root_.L.step p kfn (.st64 a i e) ⟨m, loc⟩ =
            .ok (.normal, ⟨m.set64 (TieredArray.t0 a) vi vv, loc⟩) := by
          change (evalE i >>= fun j => evalE e >>= fun v =>
            _root_.L.st64 (TieredArray.t0 a) j v >>= fun _ => pure Sig.normal) ⟨m, loc⟩ = _
          simp only [Bind.bind, StateT.bind, Except.bind, hviE, hvvE]
          dsimp only [_root_.L.st64, get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set,
            StateT.set, Bind.bind, StateT.bind, Pure.pure, StateT.pure, Except.bind, Except.pure]
          simp only [hbound, ↓reduceIte]; rfl
        rw [hstep]
        have hbrF : evalBranch .bgeu (st2.getReg AbiReg.t0) (st2.getReg AbiReg.t1) = false := by
          rw [ht0_2, ht1_2', evalBranch, BitVec.ult]
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64, UInt64.toNat_toBitVec,
            decide_eq_true hbound, Bool.not_true]
        have hpres23 : PreservedRegs st2 st3 := PreservedRegs.of_regEqExceptT6 hreg3
        rw [hbrF] at hpc3_raw; simp only [Bool.false_eq_true, ↓reduceIte] at hpc3_raw
        have htw3 : lm.totalSize (pre ++ seq ++ clen ++ cbr) =
            lm.totalSize pre + lm.totalSize seq + lm.totalSize clen + brSz := by
          rw [lm.totalSize_append, htw2]; simp [cbr, Asm.bgeu, brSz]
        have hpc3 : st3.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ seq ++ clen ++ cbr)) := by
          rw [hpc3_raw, htw3, htw2]
        have hgp3 : st3.getReg AbiReg.gp = L.T := (hreg3.getReg_eq (by decide)).symm.trans hgp2
        have hsp3 : st3.getReg AbiReg.sp = L.sp := (hreg3.getReg_eq (by decide)).symm.trans hsp2
        have ht0_3 : st3.getReg AbiReg.t0 = vi.toBitVec := (hreg3.getReg_eq (by decide)).symm.trans ht0_2
        have ha0_3 : st3.getReg AbiReg.a0 = vv.toBitVec := (hreg3.getReg_eq (by decide)).symm.trans ha0_2
        have hlistTail : (pre ++ seq ++ clen ++ cbr) ++ (cbase ++ cst) ++ post =
            pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl (.st64 a i e)).1 ++ post := by
          rw [hcs]; simp only [List.append_assoc]
        have hlinkTail : lm.linkSpec ((pre ++ seq ++ clen ++ cbr) ++ (cbase ++ cst) ++ post) =
            .ok (env.code, env.labels) := by
          rw [hlistTail]; exact hlink
        have htw_cb : lm.totalSize (loadMemOff .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (env.tab.base64 (TieredArray.t0 a))) =
            lm.totalSize cbase := rfl
        have hmem3' : st3.mem = st1.mem := hmem3.trans hmem2
        obtain ⟨kt, st7, hrunT, hpc7, hpres37, hrel7, hfr7⟩ :=
          st64_ok_tail_gen lm env hm L m loc (pre ++ seq ++ clen ++ cbr) post a ha vi vv st3 hlinkTail
            (by rw [htw3, htw_cb]; rw [htw_cs] at h64; omega)
            hpc3 hgp3 hsp3 ht0_3 ha0_3 (by rw [hmem3']; exact hmemRel1) (by rw [hmem3']; exact hframeOk1) hbound
        refine ⟨kseq + (lm.totalSize clen + (kbr + kt)), st7, ?_, ?_,
          hpres1.trans (hpres12.trans (hpres23.trans hpres37)), hrel7, hfr7⟩
        · rw [run_add, hrun1]; dsimp only
          rw [run_add, hrun2]; dsimp only
          rw [run_add, hrunBr]; dsimp only
          exact hrunT
        · rw [hpc7, htw3, htw_cb, htw_cs]; congr 2; omega
      · have hstep : _root_.L.step p kfn (.st64 a i e) ⟨m, loc⟩ = .error .oob := by
          change (evalE i >>= fun j => evalE e >>= fun v =>
            _root_.L.st64 (TieredArray.t0 a) j v >>= fun _ => pure Sig.normal) ⟨m, loc⟩ = _
          simp only [Bind.bind, StateT.bind, Except.bind, hviE, hvvE]
          dsimp only [_root_.L.st64, get, getThe, MonadStateOf.get, StateT.get, Bind.bind, StateT.bind,
            Pure.pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, Except.pure,
            Function.comp_def]
          simp only [hbound, ↓reduceIte]; rfl
        rw [hstep]
        have hbrT : evalBranch .bgeu (st2.getReg AbiReg.t0) (st2.getReg AbiReg.t1) = true := by
          rw [ht0_2, ht1_2', evalBranch, BitVec.ult]
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64, UInt64.toNat_toBitVec,
            decide_eq_false hbound, Bool.not_false]
        have hpres23 : PreservedRegs st2 st3 := PreservedRegs.of_regEqExceptT6 hreg3
        rw [hbrT] at hpc3_raw; simp only [↓reduceIte] at hpc3_raw
        refine ⟨kseq + (lm.totalSize clen + kbr), st3, ?_, hpc3_raw, hpres1.trans (hpres12.trans hpres23)⟩
        · rw [run_add, hrun1]; dsimp only
          rw [run_add, hrun2]; dsimp only
          exact hrunBr
    · simp only [hviE, hvvE] at rseq
      have hstep : _root_.L.step p kfn (.st64 a i e) ⟨m, loc⟩ = .error .oob := by
        simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hviE, hvvE]
      rw [hstep]
      obtain ⟨ks, st1, hrun1, hpc1, hpres1, _⟩ := rseq
      exact ⟨ks, st1, hrun1, hpc1, hpres1⟩
  · simp only [hviE] at rseq
    have hstep : _root_.L.step p kfn (.st64 a i e) ⟨m, loc⟩ = .error .oob := by
      simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hviE]
    rw [hstep]
    obtain ⟨ks, st1, hrun1, hpc1, hpres1, _⟩ := rseq
    exact ⟨ks, st1, hrun1, hpc1, hpres1⟩

private theorem foldl_zipIdx_ge (es : List Expr) (k init : Nat) :
    init ≤ ((es.zipIdx k).foldl (fun acc (e, idx) => max acc (idx + max 1 (maxTempsExpr e))) init) ∧
    ∀ i (hi : i < es.length),
      k + i + max 1 (maxTempsExpr es[i]) ≤
        ((es.zipIdx k).foldl (fun acc (e, idx) => max acc (idx + max 1 (maxTempsExpr e))) init) := by
  induction es generalizing k init with
  | nil => simp
  | cons e es ih =>
    simp only [List.zipIdx_cons, List.foldl_cons]
    have ⟨hinit, hmem⟩ := ih (k + 1) (max init (k + max 1 (maxTempsExpr e)))
    constructor
    · exact Nat.le_trans (Nat.le_max_left _ _) hinit
    · intro i hi
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        exact Nat.le_trans (Nat.le_max_right _ _) hinit
      | succ i' =>
        have hi' : i' < es.length := by simpa using hi
        have h := hmem i' hi'
        rw [List.getElem_cons_succ]
        exact Nat.le_trans (by omega) h

private theorem evalArgs_pure {tab : Tab} {es : List Expr} (hes : ∀ e ∈ es, CoreExpr tab e) (st : St) :
    (∃ vs, evalArgs es st = .ok (vs, st) ∧ vs.length = es.length) ∨ evalArgs es st = .error .oob := by
  induction es with
  | nil => exact Or.inl ⟨[], rfl, rfl⟩
  | cons e es ih =>
    have he := hes e (by simp)
    rcases he.evalE_pure st with ⟨v, hv⟩ | hv
    · rcases ih (fun x hx => hes x (by simp [hx])) with ⟨vs, hvs, hlen⟩ | hvs
      · refine Or.inl ⟨v :: vs, ?_, by simp [hlen]⟩
        simp [evalArgs, Bind.bind, StateT.bind, Except.bind, hv, hvs, Pure.pure, StateT.pure, Except.pure]
      · exact Or.inr (by simp [evalArgs, Bind.bind, StateT.bind, Except.bind, hv, hvs])
    · exact Or.inr (by simp [evalArgs, Bind.bind, StateT.bind, Except.bind, hv])

private theorem evalArgs_sim_gen (lm : LinkModel) (env : CodeEnvGen lm) (hm : TabMapOk env.tab)
    {nlocals ntemps : Nat} (L : Layout env.tab nlocals ntemps)
    (m : _root_.L.Mem) (loc : _root_.L.Locals)
    (pre post : List AsmItem) (tmp : Nat) (es : List Expr)
    (hes : ∀ e ∈ es, CoreExpr env.tab e)
    (hvars : ∀ e ∈ es, exprVarsLt nlocals e)
    (htmp : ∀ i (hi : i < es.length), tmp + i + max 1 (maxTempsExpr es[i]) ≤ ntemps)
    (hlink : lm.linkSpec (pre ++ compileEvalExprsToTemps env.tab nlocals tmp es ++ post) =
        .ok (env.code, env.labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (compileEvalExprsToTemps env.tab nlocals tmp es)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = L.sp)
    (hmemRel : MemRel env.tab L st.mem m) (hframeOk : FrameOk L st.mem nlocals loc) :
    match evalArgs es ⟨m, loc⟩ with
    | .ok (vs, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (compileEvalExprsToTemps env.tab nlocals tmp es))) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem ∧
        (∀ j (hj : j < vs.length),
          readWord64 st'.mem (L.sp + BitVec.ofInt 64 (slotOff (nlocals + tmp + j))) = (vs[j]).toBitVec)
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧ PreservedRegs st st' := by
  induction es generalizing pre tmp st with
  | nil =>
    refine ⟨0, st, rfl, hpc, PreservedRegs.refl st, MemEqOutside.refl _ _, ?_⟩
    intro j hj; simp at hj
  | cons e es ih =>
    have he : CoreExpr env.tab e := hes e (by simp)
    have hes' : ∀ x ∈ es, CoreExpr env.tab x := fun x hx => hes x (by simp [hx])
    have hve : exprVarsLt nlocals e := hvars e (by simp)
    have hvs' : ∀ x ∈ es, exprVarsLt nlocals x := fun x hx => hvars x (by simp [hx])
    have htmp0_max : tmp + max 1 (maxTempsExpr e) ≤ ntemps := by
      have h := htmp 0 (by simp)
      simp only [List.getElem_cons_zero, Nat.add_zero] at h
      exact h
    have htmp0 : tmp + maxTempsExpr e ≤ ntemps := Nat.le_trans (by omega) htmp0_max
    have htmp1 : tmp + 1 ≤ ntemps := Nat.le_trans (by omega) htmp0_max
    have htmpRest : ∀ i (hi : i < es.length), (tmp + 1) + i + max 1 (maxTempsExpr es[i]) ≤ ntemps := by
      intro i hi
      have h := htmp (i + 1) (by simpa using Nat.succ_lt_succ hi)
      simp only [List.getElem_cons_succ] at h
      omega
    let cr := compileEvalExprsToTemps env.tab nlocals (tmp + 1) es
    by_cases he0 : (e.constVal? == some 0) = true
    · obtain rfl : e = .const 0 := expr_constVal_eq_some (beq_iff_eq.mp he0)
      let cs := storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t0 (slotOff (nlocals + tmp))
      have hdef : compileEvalExprsToTemps env.tab nlocals tmp (.const 0 :: es) = cs ++ cr := by
        simp [compileEvalExprsToTemps, Expr.constVal?, cs, cr]
      have htw_def : lm.totalSize (compileEvalExprsToTemps env.tab nlocals tmp (.const 0 :: es)) =
          lm.totalSize cs + lm.totalSize cr := by rw [hdef, lm.totalSize_append]
      have halS : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff (nlocals + tmp))) 8 = true := by
        rw [hsp, slotOff_ofInt]; exact isAligned8_add_mul8 L.sp L.hSpAlign _
      obtain ⟨st2, hrun2, hoth2, hmem2, hpc2⟩ :=
        storeMemOff_sd_correct_lm lm env.hrom pre (cr ++ post) AbiReg.sp AbiReg.zero AbiReg.t0
          (by decide) (by decide) (by decide) (slotOff (nlocals + tmp))
          (by rw [show pre ++ storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t0 (slotOff (nlocals + tmp)) ++ (cr ++ post) = pre ++ (cs ++ cr) ++ post by dsimp only [cs]; simp only [List.append_assoc]]; rw [← hdef]; exact hlink)
          (by rw [htw_def] at h64; dsimp only [cs, cr] at h64 ⊢; omega) st hpc halS
      have hpres12 : PreservedRegs st st2 :=
        ⟨hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide)⟩
      have hsubSlot : (slotSpan L.sp (1 + nlocals + tmp)).sub (tempSpan L.sp nlocals tmp ntemps) := by
        rintro _ ⟨k, hk, rfl⟩
        dsimp only [slotSpan] at hk
        exact ⟨k, by dsimp only [tempSpan]; omega, rfl⟩
      have heq12 : MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st2.mem := by
        rw [hmem2]; apply MemEqOutside.writeWord64; intro k hk
        apply hsubSlot; rw [hsp, slotOff_ofInt]
        exact ⟨k, hk, by dsimp only [slotSpan, slotAddr]; rw [show 1 + nlocals + tmp = 1 + (nlocals + tmp) from by omega]⟩
      have htw2 : lm.totalSize (pre ++ cs) = lm.totalSize pre + lm.totalSize cs := lm.totalSize_append _ _
      have rrest := ih (pre ++ cs) (tmp + 1) hes' hvs' htmpRest
        (by simpa only [hdef, List.append_assoc] using hlink)
        (by rw [htw2]; rw [htw_def] at h64; change 4 * (lm.totalSize pre + lm.totalSize cs + lm.totalSize cr) < 2 ^ 64; omega)
        st2 (by rw [htw2]; dsimp only [cs]; exact hpc2) (hpres12.gp.trans hgp) (hpres12.sp.trans hsp)
        (memRel_of_eqOutside_temp hm (by omega) heq12 hmemRel)
        (frameOk_of_eqOutside_temp (by omega) heq12 hframeOk)
      rcases evalArgs_pure hes' ⟨m, loc⟩ with ⟨vs, hvsE, hvsLen⟩ | hvsE
      · simp only [hvsE] at rrest
        obtain ⟨krest, st3, hrun3, hpc3, hpres23, heq23, hslots3⟩ := rrest
        rw [show evalArgs (.const 0 :: es) ⟨m, loc⟩ = .ok ((0 : _root_.L.Word) :: vs, ⟨m, loc⟩) by
          simp [evalArgs, evalE, Bind.bind, StateT.bind, Except.bind, hvsE, Pure.pure, StateT.pure, Except.pure]]
        refine ⟨lm.totalSize cs + krest, st3, by rw [run_add, hrun2]; exact hrun3,
          by rw [hpc3, htw2, htw_def]; congr 2; dsimp only [cs, cr]; omega, hpres12.trans hpres23,
          heq12.trans (MemEqOutside.mono (tempSpan_mono (by omega) htmp1) heq23), ?_⟩
        intro j hj
        cases j with
        | zero =>
          simp only [List.getElem_cons_zero, Nat.add_zero]
          have hdisj : MemDisjoint (slotSpan L.sp (1 + nlocals + tmp)) (tempSpan L.sp nlocals (tmp + 1) ntemps) :=
            slotSpan_memDisjoint_tempSpan L.hFrameValid htmp1 (by omega)
          have hread : readWord64 st3.mem (L.sp + BitVec.ofInt 64 (slotOff (nlocals + tmp))) =
              readWord64 st2.mem (L.sp + BitVec.ofInt 64 (slotOff (nlocals + tmp))) := by
            apply MemEqOutside.readWord64_eq heq23
            intro k hk
            rw [slotOff_ofInt]
            exact hdisj _ ⟨k, hk, by simp only [slotSpan, slotAddr]; rw [show 1 + nlocals + tmp = 1 + (nlocals + tmp) from by omega]⟩
          rw [hread, hmem2, hsp, getReg_zero, readWord64_writeWord64_self]; rfl
        | succ j' =>
          simp only [List.getElem_cons_succ]
          have hj' : j' < vs.length := by simpa using hj
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hslots3 j' hj'
      · simp only [hvsE] at rrest
        obtain ⟨krest, st3, hrun3, hpc3, hpres23⟩ := rrest
        rw [show evalArgs (.const 0 :: es) ⟨m, loc⟩ = .error .oob by
          simp [evalArgs, evalE, Bind.bind, StateT.bind, Except.bind, hvsE, Pure.pure, StateT.pure, Except.pure]]
        exact ⟨lm.totalSize cs + krest, st3, by rw [run_add, hrun2]; exact hrun3, hpc3, hpres12.trans hpres23⟩
    · let ce := compileE env.tab nlocals tmp e
      let cs := storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff (nlocals + tmp))
      have hdef : compileEvalExprsToTemps env.tab nlocals tmp (e :: es) = ce ++ cs ++ cr := by
        simp [compileEvalExprsToTemps, he0, ce, cs, cr, List.append_assoc]
      have htw_def : lm.totalSize (compileEvalExprsToTemps env.tab nlocals tmp (e :: es)) =
          lm.totalSize ce + lm.totalSize cs + lm.totalSize cr := by
        rw [hdef, (lm.totalSize_append), (lm.totalSize_append)]
      have hlistE : pre ++ ce ++ (cs ++ cr ++ post) =
          pre ++ compileEvalExprsToTemps env.tab nlocals tmp (e :: es) ++ post := by
        rw [hdef]; simp only [List.append_assoc]
      have hlinkE : lm.linkSpec (pre ++ ce ++ (cs ++ cr ++ post)) = .ok (env.code, env.labels) := by
        rw [hlistE]; exact hlink
      have re := evalExpr_sim_gen lm env hm L m loc pre (cs ++ cr ++ post) tmp e he hve htmp0 hlinkE
        (by rw [htw_def] at h64; dsimp only [ce, cs, cr] at h64 ⊢; omega)
        st hpc hgp hsp hmemRel hframeOk
      rcases he.evalE_pure ⟨m, loc⟩ with ⟨ve, hveE⟩ | hveE
      · simp only [hveE] at re
        obtain ⟨ke, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := re
        have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.gp.trans hgp
        have hsp1 : st1.getReg AbiReg.sp = L.sp := hpres1.sp.trans hsp
        have htw1 : lm.totalSize (pre ++ ce) = lm.totalSize pre + lm.totalSize ce := (lm.totalSize_append) _ _
        have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ ce)) := by
          rw [htw1]; exact hpc1
        have hlistS : (pre ++ ce) ++ cs ++ (cr ++ post) =
            pre ++ compileEvalExprsToTemps env.tab nlocals tmp (e :: es) ++ post := by
          rw [hdef]; simp only [List.append_assoc]
        have hlinkS : lm.linkSpec ((pre ++ ce) ++ cs ++ (cr ++ post)) = .ok (env.code, env.labels) := by
          rw [hlistS]; exact hlink
        have halS : isAligned (st1.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff (nlocals + tmp))) 8 = true := by
          rw [hsp1, slotOff_ofInt]; exact isAligned8_add_mul8 L.sp L.hSpAlign _
        obtain ⟨st2, hrun2, hoth2, hmem2, hpc2⟩ :=
          storeMemOff_sd_correct_lm lm env.hrom (pre ++ ce) (cr ++ post) AbiReg.sp AbiReg.a0 AbiReg.t0
            (by decide) (by decide) (by decide) (slotOff (nlocals + tmp)) hlinkS
            (by have := htw1; rw [htw_def] at h64; dsimp only [ce, cs, cr] at this h64 ⊢; omega)
            st1 hpc1' halS
        have hpres12 : PreservedRegs st1 st2 :=
          ⟨hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide)⟩
        have htmp_le : tmp ≤ ntemps := by omega
        have hsubSlot : (slotSpan L.sp (1 + nlocals + tmp)).sub (tempSpan L.sp nlocals tmp ntemps) := by
          rintro _ ⟨k, hk, rfl⟩
          dsimp only [slotSpan] at hk
          dsimp only [MemSpan.contains, tempSpan, slotAddr]
          exact ⟨k, by omega, rfl⟩
        have heq12 : MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st2.mem := by
          apply MemEqOutside.trans heq1
          rw [hmem2]
          apply MemEqOutside.writeWord64
          intro k hk
          apply hsubSlot
          rw [hsp1, slotOff_ofInt]
          exact ⟨k, hk, by dsimp only [slotSpan, slotAddr]; rw [show 1 + nlocals + tmp = 1 + (nlocals + tmp) from by omega]⟩
        have htw2 : lm.totalSize (pre ++ ce ++ cs) = lm.totalSize pre + lm.totalSize ce + lm.totalSize cs := by
          rw [(lm.totalSize_append), htw1]
        have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ ce ++ cs)) := by
          rw [htw2, ← htw1]; exact hpc2
        have hlistR : (pre ++ ce ++ cs) ++ cr ++ post =
            pre ++ compileEvalExprsToTemps env.tab nlocals tmp (e :: es) ++ post := by
          rw [hdef]; simp only [List.append_assoc]
        have hlinkR : lm.linkSpec ((pre ++ ce ++ cs) ++ cr ++ post) = .ok (env.code, env.labels) := by
          rw [hlistR]; exact hlink
        have hmemRel2 := memRel_of_eqOutside_temp hm htmp_le heq12 hmemRel
        have hframeOk2 := frameOk_of_eqOutside_temp htmp_le heq12 hframeOk
        have rrest := ih (pre ++ ce ++ cs) (tmp + 1) hes' hvs' htmpRest hlinkR
          (by have := htw2; rw [htw_def] at h64; dsimp only [ce, cs, cr] at this h64 ⊢; omega)
          st2 hpc2' (hpres12.gp.trans hgp1) (hpres12.sp.trans hsp1) hmemRel2 hframeOk2
        rcases evalArgs_pure hes' ⟨m, loc⟩ with ⟨vs, hvsE, hvsLen⟩ | hvsE
        · simp only [hvsE] at rrest
          obtain ⟨krest, st3, hrun3, hpc3, hpres23, heq23, hslots3⟩ := rrest
          have heval : evalArgs (e :: es) ⟨m, loc⟩ = .ok (ve :: vs, ⟨m, loc⟩) := by
            simp [evalArgs, Bind.bind, StateT.bind, Except.bind, hveE, hvsE, Pure.pure, StateT.pure, Except.pure]
          rw [heval]
          refine ⟨ke + (lm.totalSize cs + krest), st3, ?_, ?_,
            hpres1.trans (hpres12.trans hpres23),
            MemEqOutside.trans heq12 (MemEqOutside.mono (tempSpan_mono (by omega) htmp1) heq23), ?_⟩
          · rw [run_add, hrun1]; dsimp only
            rw [run_add, hrun2]; dsimp only
            exact hrun3
          · rw [hpc3, htw2, htw_def]; congr 2; dsimp only [ce, cs, cr]; omega
          · intro j hj
            cases j with
            | zero =>
              simp only [Nat.add_zero, List.getElem_cons_zero]
              have hdisj : MemDisjoint (slotSpan L.sp (1 + nlocals + tmp)) (tempSpan L.sp nlocals (tmp + 1) ntemps) :=
                slotSpan_memDisjoint_tempSpan L.hFrameValid htmp1 (by omega)
              have hreadEq : readWord64 st3.mem (L.sp + BitVec.ofInt 64 (slotOff (nlocals + tmp))) =
                  readWord64 st2.mem (L.sp + BitVec.ofInt 64 (slotOff (nlocals + tmp))) := by
                apply MemEqOutside.readWord64_eq heq23
                intro k hk
                rw [slotOff_ofInt]
                exact hdisj _ ⟨k, hk, by dsimp only [slotSpan, slotAddr]; rw [show 1 + (nlocals + tmp) = 1 + nlocals + tmp from by omega]⟩
              rw [hreadEq, hmem2, hsp1, ha0_1]
              exact readWord64_writeWord64_self st1.mem _ _
            | succ j' =>
              have hj' : j' < vs.length := by simpa using hj
              have hsl := hslots3 j' hj'
              simp only [List.getElem_cons_succ]
              rw [show nlocals + tmp + (j' + 1) = nlocals + (tmp + 1) + j' from by omega]
              exact hsl
        · simp only [hvsE] at rrest
          obtain ⟨krest, st3, hrun3, hpc3, hpres23⟩ := rrest
          have heval : evalArgs (e :: es) ⟨m, loc⟩ = .error .oob := by
            simp [evalArgs, Bind.bind, StateT.bind, Except.bind, hveE, hvsE]
          rw [heval]
          refine ⟨ke + (lm.totalSize cs + krest), st3, ?_, hpc3, hpres1.trans (hpres12.trans hpres23)⟩
          · rw [run_add, hrun1]; dsimp only
            rw [run_add, hrun2]; dsimp only
            exact hrun3
      · simp only [hveE] at re
        have heval : evalArgs (e :: es) ⟨m, loc⟩ = .error .oob := by
          simp [evalArgs, Bind.bind, StateT.bind, Except.bind, hveE]
        rw [heval]
        obtain ⟨ke, st1, hrun1, hpc1, hpres1, _⟩ := re
        exact ⟨ke, st1, hrun1, hpc1, hpres1⟩

  private def copyOneResult (nlocals tmp count i : Nat) : List AsmItem :=
    if i < count then loadMemOff .ld (resReg i) AbiReg.sp AbiReg.t0 (slotOff (nlocals + tmp + i))
    else [Asm.addi (resReg i) AbiReg.zero 0#12]

private theorem copyTempsToResults_eq_flatMap (tab : Tab) (nlocals tmp count : Nat)
    (h : tab.nres ≤ maxRes) (hc : 0 < count) :
    copyTempsToResults tab nlocals tmp count =
      (List.range (min count tab.nres)).flatMap (copyOneResult nlocals tmp count) := by
  have hne : (count == 0) = false := by cases count with | zero => omega | succ _ => rfl
  simp only [copyTempsToResults, hne, Bool.false_eq_true, ↓reduceIte]
  have hcongr : ∀ (xs : List Nat), (∀ i ∈ xs, i < min count tab.nres) →
      xs.flatMap (fun i =>
        if i < maxRes then loadMemOff .ld (resReg i) AbiReg.sp AbiReg.t0 (slotOff (nlocals + tmp + i))
        else loadMemOff .ld AbiReg.t1 AbiReg.sp AbiReg.t2 (slotOff (nlocals + tmp + i)) ++
          storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t2 (tab.resOff i)) =
      xs.flatMap (copyOneResult nlocals tmp count) := by
    intro xs hxs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      have hx : x < min count tab.nres := hxs x (by simp)
      have hxM : x < maxRes := by omega
      have hxC : x < count := by omega
      simp only [List.flatMap_cons, hxM, hxC, ↓reduceIte, copyOneResult]
      congr 1; exact ih (fun y hy => hxs y (by simp [hy]))
  exact hcongr (List.range (min count tab.nres)) (fun i hi => List.mem_range.mp hi)

private theorem resReg_ne_t6_s1 {i : Nat} (hi : i < maxRes) :
    resReg i ≠ AbiReg.t6 ∧ resReg i ≠ AbiReg.s1 := by
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    dsimp only [maxRes] at hi; omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem resReg_lt_ne_pres {i : Nat} (hi : i < maxRes) :
    resReg i ≠ AbiReg.zero ∧ resReg i ≠ AbiReg.t0 ∧
    resReg i ≠ AbiReg.gp ∧ resReg i ≠ AbiReg.sp ∧
    resReg i ≠ AbiReg.s0 ∧ resReg i ≠ AbiReg.s1 ∧ resReg i ≠ AbiReg.s2 := by
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    dsimp only [maxRes] at hi; omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem resReg_inj {i j : Nat} (hi : i < maxRes) (hj : j < maxRes) (hne : i ≠ j) :
    resReg i ≠ resReg j := by
  have h1 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    dsimp only [maxRes] at hi; omega
  have h2 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by
    dsimp only [maxRes] at hj; omega
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | contradiction | decide

private theorem copyOneList_sim_gen (lm : LinkModel) (env : CodeEnvGen lm)
    {nlocals ntemps : Nat} (L : Layout env.tab nlocals ntemps)
    (vs : List _root_.L.Word) (pre post : List AsmItem) (tmp : Nat)
    (xs : List Nat) (st : State) (hnodup : xs.Nodup) (hbound : ∀ i ∈ xs, i < maxRes)
    (hslots : ∀ j (hj : j < vs.length),
      readWord64 st.mem (L.sp + BitVec.ofInt 64 (slotOff (nlocals + tmp + j))) = (vs[j]).toBitVec)
    (hlink : lm.linkSpec (pre ++ xs.flatMap (copyOneResult nlocals tmp vs.length) ++ post) =
        .ok (env.code, env.labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (xs.flatMap (copyOneResult nlocals tmp vs.length))) < 2 ^ 64)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (hsp : st.getReg AbiReg.sp = L.sp) :
    ∃ k st', RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (xs.flatMap (copyOneResult nlocals tmp vs.length)))) ∧
      PreservedRegs st st' ∧ st'.mem = st.mem ∧
      (∀ i ∈ xs, st'.getReg (resReg i) = (vs.getD i 0).toBitVec) ∧
      (∀ k, k < maxRes → k ∉ xs → st'.getReg (resReg k) = st.getReg (resReg k)) := by
  induction xs generalizing pre st with
  | nil =>
    refine ⟨0, st, rfl, hpc, PreservedRegs.refl st, rfl, fun _ h => by simp at h, fun _ _ _ => rfl⟩
  | cons i rest ih =>
    have hi : i < maxRes := hbound i (by simp)
    have hrestB : ∀ x ∈ rest, x < maxRes := fun x hx => hbound x (by simp [hx])
    have ⟨hinot, hnodupR⟩ := List.nodup_cons.mp hnodup
    have hneProps := resReg_lt_ne_pres hi
    let c1 := copyOneResult nlocals tmp vs.length i
    let cR := rest.flatMap (copyOneResult nlocals tmp vs.length)
    have hflat : (i :: rest).flatMap (copyOneResult nlocals tmp vs.length) = c1 ++ cR := rfl
    have htw_flat : lm.totalSize ((i :: rest).flatMap (copyOneResult nlocals tmp vs.length)) =
        lm.totalSize c1 + lm.totalSize cR := by rw [hflat, (lm.totalSize_append)]
    have hlist1 : pre ++ c1 ++ (cR ++ post) =
        pre ++ (i :: rest).flatMap (copyOneResult nlocals tmp vs.length) ++ post := by
      rw [hflat]; simp only [List.append_assoc]
    have hlink1 : lm.linkSpec (pre ++ c1 ++ (cR ++ post)) = .ok (env.code, env.labels) := by
      rw [hlist1]; exact hlink
    have hstep1 : ∃ st1, RV64.run env.rom (lm.totalSize c1) st = .cont st1 ∧
        (∀ q, q ≠ resReg i → q ≠ AbiReg.t0 → st1.getReg q = st.getReg q) ∧
        st1.getReg (resReg i) = (vs.getD i 0).toBitVec ∧
        st1.mem = st.mem ∧
        st1.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize c1)) := by
      by_cases hic : i < vs.length
      · have hc1 : c1 = loadMemOff .ld (resReg i) AbiReg.sp AbiReg.t0 (slotOff (nlocals + tmp + i)) := by
          simp [c1, copyOneResult, hic]
        rw [hc1] at hlink1 ⊢
        have hal : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff (nlocals + tmp + i))) 8 = true := by
          rw [hsp, slotOff_ofInt]; exact isAligned8_add_mul8 L.sp L.hSpAlign _
        obtain ⟨st1, hrun1, hoth1, hval1, hmem1, hpc1⟩ :=
          loadMemOff_ld_correct_lm lm env.hrom pre (cR ++ post) (resReg i) AbiReg.sp AbiReg.t0
            hneProps.1 (by decide) (by decide) (slotOff (nlocals + tmp + i)) hlink1
            (by rw [htw_flat] at h64; rw [← hc1]; dsimp only [c1, cR] at h64 ⊢; omega) st hpc hal
        refine ⟨st1, hrun1, hoth1, ?_, hmem1, hpc1⟩
        rw [hval1, hsp, hslots i hic]
        simp [List.getD, List.getElem?_eq_getElem hic]
      · have hc1 : c1 = [Asm.addi (resReg i) AbiReg.zero 0#12] := by
          simp [c1, copyOneResult, hic]
        have htw1' : lm.totalSize c1 = 1 := by rw [hc1, Asm.addi, lm.totalSize_instr]
        rw [hc1] at hlink1
        have hs1 := step_item_instr_lm lm env.hrom pre (cR ++ post) (.aluImm .addi (resReg i) AbiReg.zero 0#12)
          hlink1 (by rw [htw_flat, htw1'] at h64; omega) st hpc
        let st1 := stepReg st (resReg i) 0#64 (st.pc + 4#64)
        refine ⟨st1, ?_, ?_, ?_, ?_, ?_⟩
        · rw [htw1']; exact run_one_cont _ _ st1 (by
            rw [hs1]; simp only [execInstr, evalAluImm, getReg_zero]
            rw [show sextImm12 0#12 = 0#64 from rfl]; rfl)
        · intro q hq _
          exact getReg_stepReg_ne st (resReg i) q hq _ _
        · rw [getReg_stepReg_eq st (resReg i) hneProps.1 _ _]
          have hnone : vs[i]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hic)
          simp [List.getD, hnone]
        · dsimp only [st1, stepReg, State.setReg]; split <;> rfl
        · rw [htw1']; exact pc_add_4_ofNat st.pc hpc
    obtain ⟨st1, hrun1, hoth1, hval1, hmem1, hpc1⟩ := hstep1
    have hpres01 : PreservedRegs st st1 :=
      ⟨hoth1 _ hneProps.2.2.1.symm (by decide),
       hoth1 _ hneProps.2.2.2.1.symm (by decide),
       hoth1 _ hneProps.2.2.2.2.1.symm (by decide),
       hoth1 _ hneProps.2.2.2.2.2.2.symm (by decide)⟩
    have htw1 : lm.totalSize (pre ++ c1) = lm.totalSize pre + lm.totalSize c1 := (lm.totalSize_append) _ _
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ c1)) := by rw [htw1]; exact hpc1
    have hlistR : (pre ++ c1) ++ cR ++ post =
        pre ++ (i :: rest).flatMap (copyOneResult nlocals tmp vs.length) ++ post := by
      rw [hflat]; simp only [List.append_assoc]
    have hlinkR : lm.linkSpec ((pre ++ c1) ++ cR ++ post) = .ok (env.code, env.labels) := by
      rw [hlistR]; exact hlink
    have hslots1 : ∀ j (hj : j < vs.length),
        readWord64 st1.mem (L.sp + BitVec.ofInt 64 (slotOff (nlocals + tmp + j))) = (vs[j]).toBitVec := by
      intro j hj; rw [hmem1]; exact hslots j hj
    obtain ⟨k2, st2, hrun2, hpc2, hpres12, hmem2, hgetR, hkeepR⟩ :=
      ih (pre ++ c1) st1 hnodupR hrestB hslots1 hlinkR
        (by have := htw1; rw [htw_flat] at h64; dsimp only [c1, cR] at this h64 ⊢; omega)
        hpc1' (hpres01.sp.trans hsp)
    refine ⟨lm.totalSize c1 + k2, st2, ?_, ?_, hpres01.trans hpres12, hmem2.trans hmem1, ?_, ?_⟩
    · rw [run_add, hrun1]; exact hrun2
    · rw [hpc2, htw1, htw_flat, Nat.add_assoc]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hxR
      · rw [hkeepR x hi hinot, hval1]
      · exact hgetR x hxR
    · intro k hk hknot
      have hne : i ≠ k := fun h => hknot (by simp [h])
      have hk_ne_ri : resReg k ≠ resReg i := (resReg_inj hi hk hne).symm
      have hk_ne_t0 : resReg k ≠ AbiReg.t0 := (resReg_lt_ne_pres hk).2.1
      have hknotR : k ∉ rest := fun h => hknot (by simp [h])
      rw [hkeepR k hk hknotR, hoth1 (resReg k) hk_ne_ri hk_ne_t0]

private theorem ret_sim_gen (lm : LinkModel) (env : CodeEnvGen lm) (hm : TabMapOk env.tab) (hnres : env.tab.nres ≤ maxRes)
    {nlocals ntemps : Nat} (L : Layout env.tab nlocals ntemps)
    (p : Prog) (kfn : Stmt → M Sig) (pfx : String) (lblId : Nat) (brkLbl : Option String)
    (m : _root_.L.Mem) (loc : _root_.L.Locals)
    (pre post : List AsmItem) (retLbl : String) (retTgt : Nat) (es : List Expr)
    (hes : ∀ e ∈ es, CoreExpr env.tab e)
    (hvars : ∀ e ∈ es, exprVarsLt nlocals e)
    (htmp : maxTempsExprs es ≤ ntemps)
    (hret : lookupLabel env.labels retLbl = some retTgt)
    (hlink : lm.linkSpec (pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ret es)).1 ++ post) =
        .ok (env.code, env.labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ret es)).1) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = L.sp)
    (hmemRel : MemRel env.tab L st.mem m) (hframeOk : FrameOk L st.mem nlocals loc) :
    match _root_.L.step p kfn (.ret es) ⟨m, loc⟩ with
    | .ok (.normal, ⟨m', loc'⟩) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ret es)).1)) ∧
        PreservedRegs st st' ∧ MemRel env.tab L st'.mem m' ∧ FrameOk L st'.mem nlocals loc'
    | .ok (.ret vs, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * retTgt) ∧ PreservedRegs st st' ∧
        (∀ i, i < min (max 1 vs.length) env.tab.nres → st'.getReg (resReg i) = (vs.getD i 0).toBitVec)
    | .error .oob =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧ PreservedRegs st st'
    | .error (.abort code) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.abortTarget) ∧
        st'.getReg AbiReg.a0 = code.toBitVec ∧ PreservedRegs st st'
    | _ => False := by
  cases es with
  | nil =>
    have hstep : _root_.L.step p kfn (.ret []) ⟨m, loc⟩ = .ok (.ret [], ⟨m, loc⟩) := by
      simp [_root_.L.step, _root_.L.evalArgs, Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure]
    rw [hstep]
    by_cases hnres0 : 0 < env.tab.nres
    · have hcs : (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ret [])).1 =
          [Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.j retLbl] := by
        simp [compileS, compileEvalExprsToTemps, copyTempsToResults, hnres0]
      rw [hcs] at hlink h64
      have hlinkA : lm.linkSpec (pre ++ [Asm.addi AbiReg.a0 AbiReg.zero 0#12] ++ ([Asm.j retLbl] ++ post)) =
          .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
      have hltA : 4 * lm.totalSize pre < 2 ^ 64 := by
        simp only [lm.totalSize_cons, Asm.addi, lm.itemSize_instr] at h64; omega
      have hsA := step_item_instr_lm lm env.hrom pre _ (.aluImm .addi AbiReg.a0 AbiReg.zero 0#12)
        hlinkA hltA st hpc
      let st1 : State := stepReg st AbiReg.a0 0#64 (BitVec.ofNat 64 (4 * (lm.totalSize pre + 1)))
      have hrunA : RV64.run env.rom 1 st = .cont st1 := by
        apply run_one_cont; rw [hsA]
        have h0 : evalAluImm .addi (st.getReg AbiReg.zero) 0#12 = 0#64 := by rw [getReg_zero st]; decide
        simp only [execInstr, h0, pc_add_4_ofNat st.pc hpc, st1, stepReg]
      have hpre1 : lm.totalSize (pre ++ [Asm.addi AbiReg.a0 AbiReg.zero 0#12]) = lm.totalSize pre + 1 := by
        simp [Asm.addi, lm.totalSize_append, lm.totalSize_cons, lm.totalSize_nil, lm.itemSize_instr]
      have hlinkJ : lm.linkSpec ((pre ++ [Asm.addi AbiReg.a0 AbiReg.zero 0#12]) ++ [Asm.j retLbl] ++ post) =
          .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
      have h64J : 4 * (lm.totalSize (pre ++ [Asm.addi AbiReg.a0 AbiReg.zero 0#12]) + lm.itemSize (.j retLbl)) < 2 ^ 64 := by
        simp only [lm.totalSize_cons, lm.totalSize_nil, Asm.addi, Asm.j, lm.itemSize_instr] at h64
        rw [hpre1]; omega
      obtain ⟨tgt, kj, st2, _, hlook, hrunJ, hpc2, hreg2, _⟩ :=
        step_item_j_lm lm env.hrom (pre ++ [Asm.addi AbiReg.a0 AbiReg.zero 0#12]) post retLbl hlinkJ h64J
          st1 (by change BitVec.ofNat 64 (4 * (lm.totalSize pre + 1)) = _; rw [hpre1])
      have htgt : tgt = retTgt := by rw [hret] at hlook; cases hlook; rfl
      subst htgt
      have hpresA : PreservedRegs st st1 :=
        ⟨getReg_stepReg_ne st AbiReg.a0 AbiReg.gp (by decide) _ _,
         getReg_stepReg_ne st AbiReg.a0 AbiReg.sp (by decide) _ _,
         getReg_stepReg_ne st AbiReg.a0 AbiReg.s0 (by decide) _ _,
         getReg_stepReg_ne st AbiReg.a0 AbiReg.s2 (by decide) _ _⟩
      refine ⟨1 + kj, st2, by rw [run_add, hrunA]; exact hrunJ, hpc2,
        hpresA.trans (PreservedRegs.of_regEqExceptT6 hreg2), fun i hi => ?_⟩
      have hi0 : i = 0 := by simp at hi; omega
      subst hi0
      rw [← hreg2.getReg_eq (by decide)]
      simpa [resReg] using getReg_stepReg_eq st AbiReg.a0 (by decide) 0#64 _
    · have hcs : (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ret [])).1 = [Asm.j retLbl] := by
        simp [compileS, compileEvalExprsToTemps, copyTempsToResults, hnres0]
      rw [hcs] at hlink h64
      obtain ⟨tgt, kj, st2, _, hlook, hrunJ, hpc2, hreg2, _⟩ :=
        step_item_j_lm lm env.hrom pre post retLbl hlink
          (by simpa [Asm.j] using h64) st hpc
      have htgt : tgt = retTgt := by rw [hret] at hlook; cases hlook; rfl
      subst htgt
      exact ⟨kj, st2, hrunJ, hpc2, PreservedRegs.of_regEqExceptT6 hreg2, fun i hi => by omega⟩
  | cons e es' =>
    cases es' with
    | nil =>
      let ce := compileE env.tab nlocals 0 e
      have hcs : (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ret [e])).1 =
          ce ++ [Asm.j retLbl] := rfl
      have heCore : CoreExpr env.tab e := hes e (by simp)
      have heVar : exprVarsLt nlocals e := hvars e (by simp)
      have heTmp : maxTempsExpr e ≤ ntemps := by
        have hge := (foldl_zipIdx_ge [e] 0 0).2 0 (by simp)
        simp only [Nat.zero_add, List.getElem_cons_zero] at hge
        have : max 1 (maxTempsExpr e) ≤ ntemps := Nat.le_trans hge htmp
        omega
      have hlinkE : lm.linkSpec (pre ++ ce ++ ([Asm.j retLbl] ++ post)) = .ok (env.code, env.labels) := by
        rw [hcs] at hlink; simpa [List.append_assoc] using hlink
      have htw_cs : lm.totalSize (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ret [e])).1 =
          lm.totalSize ce + lm.itemSize (.j retLbl) := by
        rw [hcs, lm.totalSize_append]; simp [Asm.j]
      have re := evalExpr_sim_gen lm env hm L m loc pre ([Asm.j retLbl] ++ post) 0 e heCore heVar
        (by omega) hlinkE (by rw [htw_cs] at h64; dsimp only [ce] at *; omega) st hpc hgp hsp hmemRel hframeOk
      rcases heCore.evalE_pure ⟨m, loc⟩ with ⟨v, hv⟩ | hv
      · simp only [hv] at re
        obtain ⟨ke, st1, hrun1, hpc1, ha0, hpres1, _⟩ := re
        have hstep : _root_.L.step p kfn (.ret [e]) ⟨m, loc⟩ = .ok (.ret [v], ⟨m, loc⟩) := by
          simp [_root_.L.step, _root_.L.evalArgs, hv, Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure]
        rw [hstep]
        have hlinkJ : lm.linkSpec ((pre ++ ce) ++ [Asm.j retLbl] ++ post) = .ok (env.code, env.labels) := by
          rw [hcs] at hlink; simpa [List.append_assoc] using hlink
        have htw1 : lm.totalSize (pre ++ ce) = lm.totalSize pre + lm.totalSize ce := lm.totalSize_append _ _
        obtain ⟨tgt, kj, st2, _, hlook, hrunJ, hpc2, hreg2, _⟩ :=
          step_item_j_lm lm env.hrom (pre ++ ce) post retLbl hlinkJ
            (by rw [htw1]; rw [htw_cs] at h64; dsimp only [ce] at *; omega) st1 (by rw [htw1]; exact hpc1)
        have htgt : tgt = retTgt := by rw [hret] at hlook; cases hlook; rfl
        subst htgt
        refine ⟨ke + kj, st2, by rw [run_add, hrun1]; exact hrunJ, hpc2,
          hpres1.trans (PreservedRegs.of_regEqExceptT6 hreg2), fun i hi => ?_⟩
        have hi0 : i = 0 := by simp at hi; omega
        subst hi0
        exact (hreg2.getReg_eq (by decide)).symm.trans (by simpa [resReg, List.getD] using ha0)
      · simp only [hv] at re
        have hstep : _root_.L.step p kfn (.ret [e]) ⟨m, loc⟩ = .error .oob := by
          simp [_root_.L.step, _root_.L.evalArgs, hv, Bind.bind, StateT.bind, Except.bind]
        rw [hstep]
        obtain ⟨ke, st1, hrun1, hpc1, hpres1, _⟩ := re
        exact ⟨ke, st1, hrun1, hpc1, hpres1⟩
    | cons e2 rest =>
      let es := e :: e2 :: rest
      let ce := compileEvalExprsToTemps env.tab nlocals 0 es
      let cc := copyTempsToResults env.tab nlocals 0 es.length
      let cj : List AsmItem := [Asm.j retLbl]
      have hcs : (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ret es)).1 = ce ++ cc ++ cj := rfl
      let jSz := lm.itemSize (.j retLbl)
      have htw_cs : lm.totalSize (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ret es)).1 =
          lm.totalSize ce + lm.totalSize cc + jSz := by
        rw [hcs, lm.totalSize_append, lm.totalSize_append]; simp [cj, Asm.j, jSz]
      have htmp' : ∀ i (hi : i < es.length), 0 + i + max 1 (maxTempsExpr es[i]) ≤ ntemps := by
        intro i hi
        have hge := (foldl_zipIdx_ge es 0 0).2 i hi
        rw [Nat.zero_add] at hge ⊢
        exact Nat.le_trans hge htmp
      have hlistE : pre ++ ce ++ (cc ++ cj ++ post) =
          pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ret es)).1 ++ post := by
        rw [hcs]; simp only [List.append_assoc]
      have hlinkE : lm.linkSpec (pre ++ ce ++ (cc ++ cj ++ post)) = .ok (env.code, env.labels) := by
        rw [hlistE]; exact hlink
      have re := evalArgs_sim_gen lm env hm L m loc pre (cc ++ cj ++ post) 0 es hes hvars htmp' hlinkE
        (by rw [htw_cs] at h64; dsimp only [ce, cc] at h64 ⊢; omega)
        st hpc hgp hsp hmemRel hframeOk
      rcases evalArgs_pure (es := es) hes ⟨m, loc⟩ with ⟨vs, hvsE, hvsLen⟩ | hvsE
      · simp only [hvsE] at re
        obtain ⟨ke, st1, hrun1, hpc1, hpres1, _, hslots1⟩ := re
        have hstep : _root_.L.step p kfn (.ret es) ⟨m, loc⟩ = .ok (.ret vs, ⟨m, loc⟩) := by
          simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvsE, Pure.pure, StateT.pure, Except.pure]
        have hgoal := hstep; rw [hgoal]
        have htw1 : lm.totalSize (pre ++ ce) = lm.totalSize pre + lm.totalSize ce := (lm.totalSize_append) _ _
        have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ ce)) := by rw [htw1]; exact hpc1
        have hpos : 0 < es.length := Nat.zero_lt_succ _
        have hccEq : cc = (List.range (min vs.length env.tab.nres)).flatMap (copyOneResult nlocals 0 vs.length) := by
          dsimp only [cc]; rw [hvsLen]; exact copyTempsToResults_eq_flatMap env.tab nlocals 0 es.length hnres hpos
        have hlistC : (pre ++ ce) ++ (List.range (min vs.length env.tab.nres)).flatMap (copyOneResult nlocals 0 vs.length) ++
            (cj ++ post) = pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ret es)).1 ++ post := by
          rw [← hccEq, hcs]; simp only [List.append_assoc]
        have hlinkC : lm.linkSpec ((pre ++ ce) ++
            (List.range (min vs.length env.tab.nres)).flatMap (copyOneResult nlocals 0 vs.length) ++ (cj ++ post)) =
            .ok (env.code, env.labels) := by
          rw [hlistC]; exact hlink
        have htw_cc : lm.totalSize ((List.range (min vs.length env.tab.nres)).flatMap (copyOneResult nlocals 0 vs.length)) =
            lm.totalSize cc := by rw [← hccEq]
        obtain ⟨kc, st2, hrun2, hpc2, hpres12, _, hget2, _⟩ :=
          copyOneList_sim_gen lm env L vs (pre ++ ce) (cj ++ post) 0 (List.range (min vs.length env.tab.nres)) st1
            List.nodup_range (fun i hi => by have := List.mem_range.mp hi; omega)
            (fun j hj => by simpa [Nat.add_zero] using hslots1 j hj)
            hlinkC (by have := htw1; have := htw_cc; rw [htw_cs] at h64; dsimp only [ce, cc] at *; omega)
            hpc1' (hpres1.sp.trans hsp)
        have htw2 : lm.totalSize (pre ++ ce ++ cc) = lm.totalSize pre + lm.totalSize ce + lm.totalSize cc := by
          rw [(lm.totalSize_append), htw1]
        have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ ce ++ cc)) := by
          rw [hpc2, htw2, htw1, htw_cc]
        have hlistJ : (pre ++ ce ++ cc) ++ [Asm.j retLbl] ++ post =
            pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ret es)).1 ++ post := by
          rw [hcs]; simp only [cj, List.append_assoc]
        have hlinkJ : lm.linkSpec ((pre ++ ce ++ cc) ++ [Asm.j retLbl] ++ post) = .ok (env.code, env.labels) := by
          rw [hlistJ]; exact hlink
        obtain ⟨tgt, kj, st3, _, hlook, hrunJ, hpc3, hreg3, _⟩ :=
          step_item_j_lm lm env.hrom (pre ++ ce ++ cc) post retLbl hlinkJ
            (by have := htw2; rw [htw_cs] at h64; dsimp only [ce, cc, jSz, Asm.j] at *; omega) st2 hpc2'
        have htgt : tgt = retTgt := by rw [hret] at hlook; cases hlook; rfl
        subst htgt
        refine ⟨ke + (kc + kj), st3, ?_, hpc3, hpres1.trans (hpres12.trans (PreservedRegs.of_regEqExceptT6 hreg3)), ?_⟩
        · rw [run_add, hrun1]; dsimp only
          rw [run_add, hrun2]; dsimp only
          exact hrunJ
        · intro i hi
          have hvsPos : 0 < vs.length := by rw [hvsLen]; exact Nat.zero_lt_succ _
          have hiMin : i < min vs.length env.tab.nres := by omega
          rw [← hreg3.getReg_eq (resReg_ne_t6_s1 (by omega))]
          exact hget2 i (List.mem_range.mpr hiMin)
      · simp only [hvsE] at re
        have hstep : _root_.L.step p kfn (.ret es) ⟨m, loc⟩ = .error .oob := by
          simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvsE]
        rw [hstep]; exact re

theorem execStmt_sim_gen (lm : LinkModel) (env : CodeEnvGen lm) (hm : TabMapOk env.tab) (hnres : env.tab.nres ≤ maxRes)
    {nlocals ntemps : Nat} (L : Layout env.tab nlocals ntemps)
    (p : Prog) (kfn : Stmt → M Sig)
    (m : _root_.L.Mem) (loc : _root_.L.Locals)
    (pre post : List AsmItem) (pfx : String) (lblId : Nat)
    (brkLbl : Option String) (retLbl : String) (retTgt : Nat) (s : Stmt)
    (hs : CoreStmt env.tab nlocals s) (hvars : stmtVarsLt nlocals s)
    (htmp : maxTempsStmt s ≤ ntemps)
    (hret : lookupLabel env.labels retLbl = some retTgt)
    (hlink : lm.linkSpec (pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl s).1 ++ post) =
        .ok (env.code, env.labels))
    (h64 : 4 * (lm.totalSize pre + lm.totalSize (compileS env.tab nlocals pfx lblId brkLbl retLbl s).1) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = L.sp)
    (hmemRel : MemRel env.tab L st.mem m) (hframeOk : FrameOk L st.mem nlocals loc) :
    match _root_.L.step p kfn s ⟨m, loc⟩ with
    | .ok (.normal, ⟨m', loc'⟩) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lm.totalSize pre + lm.totalSize (compileS env.tab nlocals pfx lblId brkLbl retLbl s).1)) ∧
        PreservedRegs st st' ∧ MemRel env.tab L st'.mem m' ∧ FrameOk L st'.mem nlocals loc'
    | .ok (.ret vs, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * retTgt) ∧ PreservedRegs st st' ∧
        (∀ i, i < min (max 1 vs.length) env.tab.nres → st'.getReg (resReg i) = (vs.getD i 0).toBitVec)
    | .error .oob =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧ PreservedRegs st st'
    | .error (.abort code) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.abortTarget) ∧
        st'.getReg AbiReg.a0 = code.toBitVec ∧ PreservedRegs st st'
    | _ => False := by
  induction hs generalizing pfx lblId brkLbl pre post st m loc with
  | skip =>
    exact ⟨0, st, rfl, hpc, PreservedRegs.refl st, hmemRel, hframeOk⟩
  | set x e hx he =>
    by_cases he0 : (e.constVal? == some 0) = true
    · obtain rfl : e = .const 0 := expr_constVal_eq_some (beq_iff_eq.mp he0)
      let cs := storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t0 (slotOff x)
      have hcs : (compileS env.tab nlocals pfx lblId brkLbl retLbl (.set x (.const 0))).1 = cs := by
        simp [compileS, Expr.constVal?, cs]
      rw [show _root_.L.step p kfn (.set x (.const 0)) ⟨m, loc⟩ =
          .ok (.normal, ⟨m, fun y => if y = x then 0 else loc y⟩) by
        simp [_root_.L.step, evalE, setLoc, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
          St.setLoc, Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure]]
      have halS : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff x)) 8 = true := by
        rw [hsp, slotOff_ofInt]; exact isAligned8_add_mul8 L.sp L.hSpAlign _
      obtain ⟨st2, hrun2, hoth2, hmem2, hpc2⟩ :=
        storeMemOff_sd_correct_lm lm env.hrom pre post AbiReg.sp AbiReg.zero AbiReg.t0
          (by decide) (by decide) (by decide) (slotOff x)
          (by change lm.linkSpec (pre ++ cs ++ post) = _; rw [← hcs]; exact hlink) (by change 4 * (lm.totalSize pre + lm.totalSize cs) < 2 ^ 64; rw [← hcs]; exact h64) st hpc halS
      have hxSlot : 1 + x < 1 + nlocals + ntemps :=
        Nat.lt_of_lt_of_le (Nat.add_lt_add_left hx 1) (Nat.le_add_right _ ntemps)
      have heqSlot : MemEqOutside (slotSpan L.sp (1 + x)) st.mem st2.mem := by
        rw [hmem2]; apply MemEqOutside.writeWord64; intro k hk
        rw [hsp, slotOff_ofInt]; exact ⟨k, hk, by dsimp only [slotSpan, slotAddr]⟩
      refine ⟨lm.totalSize cs, st2, hrun2, by rw [hcs]; exact hpc2,
        ⟨hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide)⟩,
        memRel_frame_sub_trans hm (slotSpan_sub_frame hxSlot) heqSlot hmemRel, ?_⟩
      rw [hmem2, hsp, getReg_zero]
      exact FrameOk.setLoc hx (0 : _root_.L.Word) hframeOk
    · let ce := compileE env.tab nlocals 0 e
      let cs := storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (slotOff x)
      have hcs : (compileS env.tab nlocals pfx lblId brkLbl retLbl (.set x e)).1 = ce ++ cs := by
        simp [compileS, he0, ce, cs]
      have htw_cs : lm.totalSize (compileS env.tab nlocals pfx lblId brkLbl retLbl (.set x e)).1 =
          lm.totalSize ce + lm.totalSize cs := by rw [hcs, (lm.totalSize_append)]
      have hlistE : pre ++ ce ++ (cs ++ post) =
          pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl (.set x e)).1 ++ post := by
        rw [hcs]; simp only [List.append_assoc]
      have hlinkE : lm.linkSpec (pre ++ ce ++ (cs ++ post)) = .ok (env.code, env.labels) := by
        rw [hlistE]; exact hlink
      have re := evalExpr_sim_gen lm env hm L m loc pre (cs ++ post) 0 e he hvars.2
        (by dsimp only [maxTempsStmt] at htmp; omega)
        hlinkE (by rw [htw_cs] at h64; dsimp only [ce, cs] at h64 ⊢; omega)
        st hpc hgp hsp hmemRel hframeOk
      rcases he.evalE_pure ⟨m, loc⟩ with ⟨v, hvE⟩ | hvE
      · simp only [hvE] at re
        obtain ⟨ke, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := re
        have hstep : _root_.L.step p kfn (.set x e) ⟨m, loc⟩ =
            .ok (.normal, ⟨m, fun y => if y = x then v else loc y⟩) := by
          simp [_root_.L.step, setLoc, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
            St.setLoc, Bind.bind, StateT.bind, Except.bind, hvE, Pure.pure, StateT.pure, Except.pure]
        rw [hstep]
        have hmemRel1 := memRel_of_eqOutside_temp hm (Nat.zero_le _) heq1 hmemRel
        have hframeOk1 := frameOk_of_eqOutside_temp (Nat.zero_le _) heq1 hframeOk
        have hsp1 : st1.getReg AbiReg.sp = L.sp := hpres1.sp.trans hsp
        have htw1 : lm.totalSize (pre ++ ce) = lm.totalSize pre + lm.totalSize ce := (lm.totalSize_append) _ _
        have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ ce)) := by rw [htw1]; exact hpc1
        have hlistS : (pre ++ ce) ++ cs ++ post =
            pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl (.set x e)).1 ++ post := by
          rw [hcs]; simp only [List.append_assoc]
        have hlinkS : lm.linkSpec ((pre ++ ce) ++ cs ++ post) = .ok (env.code, env.labels) := by
          rw [hlistS]; exact hlink
        have halS : isAligned (st1.getReg AbiReg.sp + BitVec.ofInt 64 (slotOff x)) 8 = true := by
          rw [hsp1, slotOff_ofInt]; exact isAligned8_add_mul8 L.sp L.hSpAlign _
        obtain ⟨st2, hrun2, hoth2, hmem2, hpc2⟩ :=
          storeMemOff_sd_correct_lm lm env.hrom (pre ++ ce) post AbiReg.sp AbiReg.a0 AbiReg.t0
            (by decide) (by decide) (by decide) (slotOff x) hlinkS
            (by have := htw1; rw [htw_cs] at h64; dsimp only [ce, cs] at this h64 ⊢; omega)
            st1 hpc1' halS
        have hpres12 : PreservedRegs st1 st2 :=
          ⟨hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide)⟩
        have hxSlot : 1 + x < 1 + nlocals + ntemps :=
          Nat.lt_of_lt_of_le (Nat.add_lt_add_left hx 1) (Nat.le_add_right _ ntemps)
        have heqSlot : MemEqOutside (slotSpan L.sp (1 + x)) st1.mem st2.mem := by
          rw [hmem2]
          apply MemEqOutside.writeWord64
          intro k hk
          rw [hsp1, slotOff_ofInt]
          exact ⟨k, hk, by dsimp only [slotSpan, slotAddr]⟩
        refine ⟨ke + lm.totalSize cs, st2, ?_, ?_, hpres1.trans hpres12, ?_, ?_⟩
        · rw [run_add, hrun1]; exact hrun2
        · rw [hpc2, htw1, htw_cs, Nat.add_assoc]
        · exact memRel_frame_sub_trans hm (slotSpan_sub_frame hxSlot) heqSlot hmemRel1
        · rw [hmem2, hsp1, ha0_1]
          exact FrameOk.setLoc hx v hframeOk1
      · simp only [hvE] at re
        have hstep : _root_.L.step p kfn (.set x e) ⟨m, loc⟩ = .error .oob := by
          simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvE]
        rw [hstep]
        obtain ⟨ke, st1, hrun1, hpc1, hpres1, _⟩ := re
        exact ⟨ke, st1, hrun1, hpc1, hpres1⟩
  | gset g e hg he =>
    by_cases he0 : (e.constVal? == some 0) = true
    · obtain rfl : e = .const 0 := expr_constVal_eq_some (beq_iff_eq.mp he0)
      let cs := storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (env.tab.globOff g)
      have hcs : (compileS env.tab nlocals pfx lblId brkLbl retLbl (.gset g (.const 0))).1 = cs := by
        simp [compileS, Expr.constVal?, cs]
      rw [show _root_.L.step p kfn (.gset g (.const 0)) ⟨m, loc⟩ = .ok (.normal, ⟨m.setG g 0, loc⟩) by
        simp [_root_.L.step, evalE, setG, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
          St.setG, Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure]]
      have halS : isAligned (st.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.globOff g)) 8 = true := by
        rw [hgp, Tab.globOff_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
      obtain ⟨st2, hrun2, hoth2, hmem2, hpc2⟩ :=
        storeMemOff_sd_correct_lm lm env.hrom pre post AbiReg.gp AbiReg.zero AbiReg.t0
          (by decide) (by decide) (by decide) (env.tab.globOff g)
          (by change lm.linkSpec (pre ++ cs ++ post) = _; rw [← hcs]; exact hlink) (by change 4 * (lm.totalSize pre + lm.totalSize cs) < 2 ^ 64; rw [← hcs]; exact h64) st hpc halS
      refine ⟨lm.totalSize cs, st2, hrun2, by rw [hcs]; exact hpc2,
        ⟨hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide)⟩,
        by rw [hmem2, hgp, getReg_zero]; exact MemRel.setG hm hmemRel g hg 0, ?_⟩
      intro x hx
      rw [← hframeOk x hx, hmem2, hgp, getReg_zero]
      apply MemEqOutside.readWord64_eq
        (MemEqOutside.writeWord64 st.mem _ _ (s := L.tabSpan) (fun k hk => by
          rw [Tab.globOff_eq_nat, int_mul8_ofInt]
          exact MemSpan.sub_range _ 8 (Tab.globOff_bound_nat L g hg) k hk))
      intro k hk
      have hdisj := MemDisjoint.of_sub_left
        (slotSpan_sub_frame (by omega : 1 + x < 1 + nlocals + ntemps))
        (MemSpan.disjoint_to_memDisjoint L.hFrameValid L.tabSpan_valid L.htabDisjFrame.symm)
      rw [slotOff_ofInt]
      exact hdisj _ ⟨k, hk, rfl⟩
    · let ce := compileE env.tab nlocals 0 e
      let cs := storeMemOff .sd AbiReg.gp AbiReg.a0 AbiReg.t0 (env.tab.globOff g)
      have hcs : (compileS env.tab nlocals pfx lblId brkLbl retLbl (.gset g e)).1 = ce ++ cs := by
        simp [compileS, he0, ce, cs]
      have htw_cs : lm.totalSize (compileS env.tab nlocals pfx lblId brkLbl retLbl (.gset g e)).1 =
          lm.totalSize ce + lm.totalSize cs := by rw [hcs, (lm.totalSize_append)]
      have hlistE : pre ++ ce ++ (cs ++ post) =
          pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl (.gset g e)).1 ++ post := by
        rw [hcs]; simp only [List.append_assoc]
      have hlinkE : lm.linkSpec (pre ++ ce ++ (cs ++ post)) = .ok (env.code, env.labels) := by
        rw [hlistE]; exact hlink
      have re := evalExpr_sim_gen lm env hm L m loc pre (cs ++ post) 0 e he hvars
        (by dsimp only [maxTempsStmt] at htmp; omega)
        hlinkE (by rw [htw_cs] at h64; dsimp only [ce, cs] at h64 ⊢; omega)
        st hpc hgp hsp hmemRel hframeOk
      rcases he.evalE_pure ⟨m, loc⟩ with ⟨v, hvE⟩ | hvE
      · simp only [hvE] at re
        obtain ⟨ke, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := re
        have hstep : _root_.L.step p kfn (.gset g e) ⟨m, loc⟩ = .ok (.normal, ⟨m.setG g v, loc⟩) := by
          simp [_root_.L.step, setG, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
            St.setG, Bind.bind, StateT.bind, Except.bind, hvE, Pure.pure, StateT.pure, Except.pure]
        rw [hstep]
        have hmemRel1 := memRel_of_eqOutside_temp hm (Nat.zero_le _) heq1 hmemRel
        have hframeOk1 := frameOk_of_eqOutside_temp (Nat.zero_le _) heq1 hframeOk
        have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.gp.trans hgp
        have htw1 : lm.totalSize (pre ++ ce) = lm.totalSize pre + lm.totalSize ce := (lm.totalSize_append) _ _
        have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ ce)) := by rw [htw1]; exact hpc1
        have hlistS : (pre ++ ce) ++ cs ++ post =
            pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl (.gset g e)).1 ++ post := by
          rw [hcs]; simp only [List.append_assoc]
        have hlinkS : lm.linkSpec ((pre ++ ce) ++ cs ++ post) = .ok (env.code, env.labels) := by
          rw [hlistS]; exact hlink
        have halS : isAligned (st1.getReg AbiReg.gp + BitVec.ofInt 64 (env.tab.globOff g)) 8 = true := by
          rw [hgp1, Tab.globOff_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
        obtain ⟨st2, hrun2, hoth2, hmem2, hpc2⟩ :=
          storeMemOff_sd_correct_lm lm env.hrom (pre ++ ce) post AbiReg.gp AbiReg.a0 AbiReg.t0
            (by decide) (by decide) (by decide) (env.tab.globOff g) hlinkS
            (by have := htw1; rw [htw_cs] at h64; dsimp only [ce, cs] at this h64 ⊢; omega)
            st1 hpc1' halS
        have hpres12 : PreservedRegs st1 st2 :=
          ⟨hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide), hoth2 _ (by decide)⟩
        refine ⟨ke + lm.totalSize cs, st2, ?_, ?_, hpres1.trans hpres12, ?_, ?_⟩
        · rw [run_add, hrun1]; exact hrun2
        · rw [hpc2, htw1, htw_cs, Nat.add_assoc]
        · rw [hmem2, hgp1, ha0_1]; exact MemRel.setG hm hmemRel1 g hg v
        · intro x hx
          rw [← hframeOk1 x hx, hmem2, hgp1, ha0_1]
          apply MemEqOutside.readWord64_eq
            (MemEqOutside.writeWord64 st1.mem _ _ (s := L.tabSpan) (fun k hk => by
              rw [Tab.globOff_eq_nat, int_mul8_ofInt]
              exact MemSpan.sub_range _ 8 (Tab.globOff_bound_nat L g hg) k hk))
          intro k hk
          have hdisj := MemDisjoint.of_sub_left
            (slotSpan_sub_frame (by omega : 1 + x < 1 + nlocals + ntemps))
            (MemSpan.disjoint_to_memDisjoint L.hFrameValid L.tabSpan_valid L.htabDisjFrame.symm)
          rw [slotOff_ofInt]
          exact hdisj _ ⟨k, hk, rfl⟩
      · simp only [hvE] at re
        have hstep : _root_.L.step p kfn (.gset g e) ⟨m, loc⟩ = .error .oob := by
          simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvE]
        rw [hstep]
        obtain ⟨ke, st1, hrun1, hpc1, hpres1, _⟩ := re
        exact ⟨ke, st1, hrun1, hpc1, hpres1⟩
  | st64 a i e ha hi he =>
    exact st64_sim_gen lm env hm L p kfn pfx lblId brkLbl retLbl retTgt m loc pre post a i e ha hi he hvars.1 hvars.2
      (by dsimp only [maxTempsStmt] at htmp; exact htmp) hlink h64 st hpc hgp hsp hmemRel hframeOk
  | seq s1 s2 hs1 hs2 ih1 ih2 =>
    dsimp only [maxTempsStmt] at htmp
    let c1 := (compileS env.tab nlocals pfx lblId brkLbl retLbl s1).1
    let id1 := (compileS env.tab nlocals pfx lblId brkLbl retLbl s1).2
    let c2 := (compileS env.tab nlocals pfx id1 brkLbl retLbl s2).1
    have hcs : (compileS env.tab nlocals pfx lblId brkLbl retLbl (.seq s1 s2)).1 = c1 ++ c2 := rfl
    have htw_cs : lm.totalSize (compileS env.tab nlocals pfx lblId brkLbl retLbl (.seq s1 s2)).1 =
        lm.totalSize c1 + lm.totalSize c2 := by rw [hcs, (lm.totalSize_append)]
    have hlist1 : pre ++ c1 ++ (c2 ++ post) =
        pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl (.seq s1 s2)).1 ++ post := by
      rw [hcs]; simp only [List.append_assoc]
    have hlink1 : lm.linkSpec (pre ++ c1 ++ (c2 ++ post)) = .ok (env.code, env.labels) := by
      rw [hlist1]; exact hlink
    have r1 := ih1 m loc pre (c2 ++ post) pfx lblId brkLbl hvars.1 (by omega) hlink1
      (by rw [htw_cs] at h64; dsimp only [c1, id1, c2] at h64 ⊢; omega)
      st hpc hgp hsp hmemRel hframeOk
    cases hst1 : _root_.L.step p kfn s1 ⟨m, loc⟩ with
    | error err =>
      rw [hst1] at r1
      have hstep : _root_.L.step p kfn (.seq s1 s2) ⟨m, loc⟩ = .error err := by
        simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hst1]
      rw [hstep]
      cases err <;> exact r1
    | ok res =>
      rcases res with ⟨sig1, ⟨m1, loc1⟩⟩
      rw [hst1] at r1
      cases sig1 with
      | brk => cases r1
      | ret vs =>
        have hstep : _root_.L.step p kfn (.seq s1 s2) ⟨m, loc⟩ = .ok (.ret vs, ⟨m1, loc1⟩) := by
          simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hst1, Pure.pure, StateT.pure, Except.pure]
        rw [hstep]; exact r1
      | normal =>
        obtain ⟨k1, st1, hrun1, hpc1, hpres1, hrel1, hfr1⟩ := r1
        have htw1 : lm.totalSize (pre ++ c1) = lm.totalSize pre + lm.totalSize c1 := (lm.totalSize_append) _ _
        have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ c1)) := by rw [htw1]; exact hpc1
        have hlist2 : (pre ++ c1) ++ c2 ++ post =
            pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl (.seq s1 s2)).1 ++ post := by
          rw [hcs]; simp only [List.append_assoc]
        have hlink2 : lm.linkSpec ((pre ++ c1) ++ c2 ++ post) = .ok (env.code, env.labels) := by
          rw [hlist2]; exact hlink
        have r2 := ih2 m1 loc1 (pre ++ c1) post pfx id1 brkLbl hvars.2 (by omega) hlink2
          (by have := htw1; rw [htw_cs] at h64; dsimp only [c1, id1, c2] at this h64 ⊢; omega)
          st1 hpc1' (hpres1.gp.trans hgp) (hpres1.sp.trans hsp) hrel1 hfr1
        have hstep : _root_.L.step p kfn (.seq s1 s2) ⟨m, loc⟩ = _root_.L.step p kfn s2 ⟨m1, loc1⟩ := by
          simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hst1]
        rw [hstep]
        cases hst2 : _root_.L.step p kfn s2 ⟨m1, loc1⟩ with
        | error err =>
          rw [hst2] at r2
          cases err with
          | oob =>
            obtain ⟨k2, st2, hrun2, hpc2, hpres2⟩ := r2
            exact ⟨k1 + k2, st2, by rw [run_add, hrun1]; exact hrun2, hpc2, hpres1.trans hpres2⟩
          | abort code =>
            obtain ⟨k2, st2, hrun2, hpc2, ha0_2, hpres2⟩ := r2
            exact ⟨k1 + k2, st2, by rw [run_add, hrun1]; exact hrun2, hpc2, ha0_2, hpres1.trans hpres2⟩
          | outOfFuel => cases r2
          | noFun _ => cases r2
        | ok res2 =>
          rcases res2 with ⟨sig2, ⟨m2, loc2⟩⟩
          rw [hst2] at r2
          cases sig2 with
          | brk => cases r2
          | ret vs =>
            obtain ⟨k2, st2, hrun2, hpc2, hpres2, hres2⟩ := r2
            exact ⟨k1 + k2, st2, by rw [run_add, hrun1]; exact hrun2, hpc2, hpres1.trans hpres2, hres2⟩
          | normal =>
            obtain ⟨k2, st2, hrun2, hpc2, hpres2, hrel2, hfr2⟩ := r2
            refine ⟨k1 + k2, st2, by rw [run_add, hrun1]; exact hrun2, ?_,
              hpres1.trans hpres2, hrel2, hfr2⟩
            rw [hpc2, htw1, htw_cs, Nat.add_assoc]
  | ite c s1 s2 hc hs1 hs2 ih1 ih2 =>
    dsimp only [maxTempsStmt] at htmp
    by_cases hs2skip : s2 = .skip
    · subst hs2skip
      let endLbl := s!"{pfx}_endif_{lblId}"
      let cc := (compileC env.tab nlocals 0 pfx (lblId + 1) c false endLbl).1
      let id1 := (compileC env.tab nlocals 0 pfx (lblId + 1) c false endLbl).2
      let c1 := (compileS env.tab nlocals pfx id1 brkLbl retLbl s1).1
      have hcs : (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ite c s1 .skip)).1 =
          cc ++ c1 ++ [Asm.lbl endLbl] := by simp [compileS, endLbl, cc, id1, c1]
      have htw_cs : lm.totalSize (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ite c s1 .skip)).1 =
          lm.totalSize cc + lm.totalSize c1 := by
        rw [hcs]; simp only [lm.totalSize_append, Asm.lbl, lm.totalSize_label, Nat.add_zero]
      have hlinkEnd : lm.linkSpec ((pre ++ cc ++ c1) ++ [Asm.lbl endLbl] ++ post) = .ok (env.code, env.labels) := by
        simpa [hcs, List.append_assoc] using hlink
      have hend := lookupLabel_of_lbl_lm lm (pre ++ cc ++ c1) post endLbl hlinkEnd
      have htw_end : lm.totalSize (pre ++ cc ++ c1) =
          lm.totalSize pre + lm.totalSize (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ite c s1 .skip)).1 := by
        rw [htw_cs]; simp only [lm.totalSize_append, Nat.add_assoc]
      have hlinkC : lm.linkSpec (pre ++ cc ++ (c1 ++ [Asm.lbl endLbl] ++ post)) = .ok (env.code, env.labels) := by
        simpa [hcs, List.append_assoc] using hlink
      have rc := evalCond_sim_gen lm env hm L m loc pre (c1 ++ [Asm.lbl endLbl] ++ post)
        0 pfx (lblId + 1) c false endLbl (lm.totalSize (pre ++ cc ++ c1))
        hc hvars.1 (by omega) hend hlinkC
        (by rw [htw_cs] at h64; dsimp only [cc, c1] at h64 ⊢; omega) st hpc hgp hsp hmemRel hframeOk
      rcases hc.evalC_pure ⟨m, loc⟩ with ⟨bc, hbc⟩ | hbc
      · cases bc
        · simp only [hbc] at rc
          obtain ⟨kc, st1, hrun1, hpc1, hpres1, heq1⟩ := rc
          have hstep : _root_.L.step p kfn (.ite c s1 .skip) ⟨m, loc⟩ = .ok (.normal, ⟨m, loc⟩) := by
            simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure, hbc]
          rw [hstep]
          exact ⟨kc, st1, hrun1, by rw [hpc1]; simp only [beq_self_eq_true, ↓reduceIte, htw_end], hpres1,
            memRel_of_eqOutside_temp hm (Nat.zero_le _) heq1 hmemRel,
            frameOk_of_eqOutside_temp (Nat.zero_le _) heq1 hframeOk⟩
        · simp only [hbc] at rc
          obtain ⟨kc, st1, hrun1, hpc1, hpres1, heq1⟩ := rc
          have hstep : _root_.L.step p kfn (.ite c s1 .skip) ⟨m, loc⟩ = _root_.L.step p kfn s1 ⟨m, loc⟩ := by
            simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hbc]
          rw [hstep]
          have htw1 : lm.totalSize (pre ++ cc) = lm.totalSize pre + lm.totalSize cc := lm.totalSize_append _ _
          have hlink1 : lm.linkSpec ((pre ++ cc) ++ c1 ++ ([Asm.lbl endLbl] ++ post)) = .ok (env.code, env.labels) := by
            simpa [hcs, List.append_assoc] using hlink
          have r1 := ih1 m loc (pre ++ cc) ([Asm.lbl endLbl] ++ post) pfx id1 brkLbl hvars.2.1 (by omega) hlink1
            (by rw [htw1]; rw [htw_cs] at h64; dsimp only [cc, c1] at h64 ⊢; omega) st1 (by rw [htw1]; simpa using hpc1)
            (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
            (memRel_of_eqOutside_temp hm (Nat.zero_le _) heq1 hmemRel)
            (frameOk_of_eqOutside_temp (Nat.zero_le _) heq1 hframeOk)
          cases hst1 : _root_.L.step p kfn s1 ⟨m, loc⟩ with
          | error err =>
            rw [hst1] at r1
            cases err with
            | oob => obtain ⟨k1, st2, hr, hp, hpr⟩ := r1; exact ⟨kc + k1, st2, by rw [run_add, hrun1]; exact hr, hp, hpres1.trans hpr⟩
            | abort code => obtain ⟨k1, st2, hr, hp, ha, hpr⟩ := r1; exact ⟨kc + k1, st2, by rw [run_add, hrun1]; exact hr, hp, ha, hpres1.trans hpr⟩
            | outOfFuel | noFun _ => cases r1
          | ok res1 =>
            rcases res1 with ⟨sig1, ⟨m1, loc1⟩⟩; rw [hst1] at r1
            cases sig1 with
            | brk => cases r1
            | ret vs => obtain ⟨k1, st2, hr, hp, hpr, hrs⟩ := r1; exact ⟨kc + k1, st2, by rw [run_add, hrun1]; exact hr, hp, hpres1.trans hpr, hrs⟩
            | normal =>
              obtain ⟨k1, st2, hr, hp, hpr, hmr, hfr⟩ := r1
              exact ⟨kc + k1, st2, by rw [run_add, hrun1]; exact hr, by rw [hp, ← lm.totalSize_append _ c1, htw_end], hpres1.trans hpr, hmr, hfr⟩
      · simp only [hbc] at rc
        have hstep : _root_.L.step p kfn (.ite c s1 .skip) ⟨m, loc⟩ = .error .oob := by
          simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hbc]
        rw [hstep]
        obtain ⟨kc, st1, hrun1, hpc1, hpres1, _⟩ := rc
        exact ⟨kc, st1, hrun1, hpc1, hpres1⟩
    · by_cases hs1skip : s1 = .skip
      · subst hs1skip
        let endLbl := s!"{pfx}_endif_{lblId}"
        let cc := (compileC env.tab nlocals 0 pfx (lblId + 1) c true endLbl).1
        let id1 := (compileC env.tab nlocals 0 pfx (lblId + 1) c true endLbl).2
        let c2 := (compileS env.tab nlocals pfx id1 brkLbl retLbl s2).1
        have hcs : (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ite c .skip s2)).1 =
            cc ++ c2 ++ [Asm.lbl endLbl] := by
          cases s2 with
          | skip => exact absurd rfl hs2skip
          | _ => rfl
        have htw_cs : lm.totalSize (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ite c .skip s2)).1 =
            lm.totalSize cc + lm.totalSize c2 := by
          rw [hcs]; simp only [lm.totalSize_append, Asm.lbl, lm.totalSize_label, Nat.add_zero]
        have hlinkEnd : lm.linkSpec ((pre ++ cc ++ c2) ++ [Asm.lbl endLbl] ++ post) = .ok (env.code, env.labels) := by
          simpa [hcs, List.append_assoc] using hlink
        have hend := lookupLabel_of_lbl_lm lm (pre ++ cc ++ c2) post endLbl hlinkEnd
        have htw_end : lm.totalSize (pre ++ cc ++ c2) =
            lm.totalSize pre + lm.totalSize (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ite c .skip s2)).1 := by
          rw [htw_cs]; simp only [lm.totalSize_append, Nat.add_assoc]
        have hlinkC : lm.linkSpec (pre ++ cc ++ (c2 ++ [Asm.lbl endLbl] ++ post)) = .ok (env.code, env.labels) := by
          simpa [hcs, List.append_assoc] using hlink
        have rc := evalCond_sim_gen lm env hm L m loc pre (c2 ++ [Asm.lbl endLbl] ++ post)
          0 pfx (lblId + 1) c true endLbl (lm.totalSize (pre ++ cc ++ c2))
          hc hvars.1 (by omega) hend hlinkC
          (by rw [htw_cs] at h64; dsimp only [cc, c2] at h64 ⊢; omega) st hpc hgp hsp hmemRel hframeOk
        rcases hc.evalC_pure ⟨m, loc⟩ with ⟨bc, hbc⟩ | hbc
        · cases bc
          · simp only [hbc] at rc
            obtain ⟨kc, st1, hrun1, hpc1, hpres1, heq1⟩ := rc
            have hstep : _root_.L.step p kfn (.ite c .skip s2) ⟨m, loc⟩ = _root_.L.step p kfn s2 ⟨m, loc⟩ := by
              simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hbc]
            rw [hstep]
            have htw1 : lm.totalSize (pre ++ cc) = lm.totalSize pre + lm.totalSize cc := lm.totalSize_append _ _
            have hlink2 : lm.linkSpec ((pre ++ cc) ++ c2 ++ ([Asm.lbl endLbl] ++ post)) = .ok (env.code, env.labels) := by
              simpa [hcs, List.append_assoc] using hlink
            have r2 := ih2 m loc (pre ++ cc) ([Asm.lbl endLbl] ++ post) pfx id1 brkLbl hvars.2.2 (by omega) hlink2
              (by rw [htw1]; rw [htw_cs] at h64; dsimp only [cc, c2] at h64 ⊢; omega) st1 (by rw [htw1]; simpa using hpc1)
              (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
              (memRel_of_eqOutside_temp hm (Nat.zero_le _) heq1 hmemRel)
              (frameOk_of_eqOutside_temp (Nat.zero_le _) heq1 hframeOk)
            cases hst2 : _root_.L.step p kfn s2 ⟨m, loc⟩ with
            | error err =>
              rw [hst2] at r2
              cases err with
              | oob => obtain ⟨k2, st2, hr, hp, hpr⟩ := r2; exact ⟨kc + k2, st2, by rw [run_add, hrun1]; exact hr, hp, hpres1.trans hpr⟩
              | abort code => obtain ⟨k2, st2, hr, hp, ha, hpr⟩ := r2; exact ⟨kc + k2, st2, by rw [run_add, hrun1]; exact hr, hp, ha, hpres1.trans hpr⟩
              | outOfFuel | noFun _ => cases r2
            | ok res2 =>
              rcases res2 with ⟨sig2, ⟨m2, loc2⟩⟩; rw [hst2] at r2
              cases sig2 with
              | brk => cases r2
              | ret vs => obtain ⟨k2, st2, hr, hp, hpr, hrs⟩ := r2; exact ⟨kc + k2, st2, by rw [run_add, hrun1]; exact hr, hp, hpres1.trans hpr, hrs⟩
              | normal =>
                obtain ⟨k2, st2, hr, hp, hpr, hmr, hfr⟩ := r2
                exact ⟨kc + k2, st2, by rw [run_add, hrun1]; exact hr, by rw [hp, ← lm.totalSize_append _ c2, htw_end], hpres1.trans hpr, hmr, hfr⟩
          · simp only [hbc] at rc
            obtain ⟨kc, st1, hrun1, hpc1, hpres1, heq1⟩ := rc
            have hstep : _root_.L.step p kfn (.ite c .skip s2) ⟨m, loc⟩ = .ok (.normal, ⟨m, loc⟩) := by
              simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure, hbc]
            rw [hstep]
            exact ⟨kc, st1, hrun1, by rw [hpc1]; simp only [beq_self_eq_true, ↓reduceIte, htw_end], hpres1,
              memRel_of_eqOutside_temp hm (Nat.zero_le _) heq1 hmemRel,
              frameOk_of_eqOutside_temp (Nat.zero_le _) heq1 hframeOk⟩
        · simp only [hbc] at rc
          have hstep : _root_.L.step p kfn (.ite c .skip s2) ⟨m, loc⟩ = .error .oob := by
            simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hbc]
          rw [hstep]
          obtain ⟨kc, st1, hrun1, hpc1, hpres1, _⟩ := rc
          exact ⟨kc, st1, hrun1, hpc1, hpres1⟩
      · let elseLbl := s!"{pfx}_else_{lblId}"
        let endLbl  := s!"{pfx}_endif_{lblId}"
        let cc := (compileC env.tab nlocals 0 pfx (lblId + 1) c false elseLbl).1
        let id1 := (compileC env.tab nlocals 0 pfx (lblId + 1) c false elseLbl).2
        let c1 := (compileS env.tab nlocals pfx id1 brkLbl retLbl s1).1
        let id2 := (compileS env.tab nlocals pfx id1 brkLbl retLbl s1).2
        let c2 := (compileS env.tab nlocals pfx id2 brkLbl retLbl s2).1
        have hcs : (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ite c s1 s2)).1 =
            cc ++ c1 ++ [Asm.j endLbl, Asm.lbl elseLbl] ++ c2 ++ [Asm.lbl endLbl] := by
          cases s2 with
          | skip => exact absurd rfl hs2skip
          | _ => cases s1 with | skip => exact absurd rfl hs1skip | _ => rfl
        let jSz := lm.itemSize (.j endLbl)
        have htw_cs : lm.totalSize (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ite c s1 s2)).1 =
            lm.totalSize cc + lm.totalSize c1 + jSz + lm.totalSize c2 := by
          rw [hcs]; simp only [lm.totalSize_append]
          have h1 : lm.totalSize [Asm.j endLbl, Asm.lbl elseLbl] = jSz := by
            simp [Asm.j, Asm.lbl, lm.itemSize_label, jSz]
          have h0 : lm.totalSize [Asm.lbl endLbl] = 0 := by simp [Asm.lbl, lm.itemSize_label]
          omega
        have hlistElse : (pre ++ cc ++ c1 ++ [Asm.j endLbl]) ++ [Asm.lbl elseLbl] ++ (c2 ++ [Asm.lbl endLbl] ++ post) =
            pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ite c s1 s2)).1 ++ post := by
          rw [hcs]; simp only [List.append_assoc, List.cons_append, List.nil_append]
        have hlinkElse : lm.linkSpec ((pre ++ cc ++ c1 ++ [Asm.j endLbl]) ++ [Asm.lbl elseLbl] ++
            (c2 ++ [Asm.lbl endLbl] ++ post)) = .ok (env.code, env.labels) := by
          rw [hlistElse]; exact hlink
        have helse := lookupLabel_of_lbl_lm lm (pre ++ cc ++ c1 ++ [Asm.j endLbl]) (c2 ++ [Asm.lbl endLbl] ++ post)
          elseLbl hlinkElse
        have hlistEnd : (pre ++ cc ++ c1 ++ [Asm.j endLbl, Asm.lbl elseLbl] ++ c2) ++ [Asm.lbl endLbl] ++ post =
            pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ite c s1 s2)).1 ++ post := by
          rw [hcs]; simp only [List.append_assoc, List.cons_append, List.nil_append]
        have hlinkEnd : lm.linkSpec ((pre ++ cc ++ c1 ++ [Asm.j endLbl, Asm.lbl elseLbl] ++ c2) ++
            [Asm.lbl endLbl] ++ post) = .ok (env.code, env.labels) := by
          rw [hlistEnd]; exact hlink
        have hend := lookupLabel_of_lbl_lm lm (pre ++ cc ++ c1 ++ [Asm.j endLbl, Asm.lbl elseLbl] ++ c2)
          post endLbl hlinkEnd
        have htw_end : lm.totalSize (pre ++ cc ++ c1 ++ [Asm.j endLbl, Asm.lbl elseLbl] ++ c2) =
            lm.totalSize pre + lm.totalSize (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ite c s1 s2)).1 := by
          rw [htw_cs]; simp only [lm.totalSize_append]
          have h1 : lm.totalSize [Asm.j endLbl, Asm.lbl elseLbl] = jSz := by
            simp [Asm.j, Asm.lbl, lm.itemSize_label, jSz]
          omega
        have hlistC : pre ++ cc ++ (c1 ++ [Asm.j endLbl, Asm.lbl elseLbl] ++ c2 ++ [Asm.lbl endLbl] ++ post) =
            pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ite c s1 s2)).1 ++ post := by
          rw [hcs]; simp only [List.append_assoc]
        have hlinkC : lm.linkSpec (pre ++ cc ++ (c1 ++ [Asm.j endLbl, Asm.lbl elseLbl] ++ c2 ++
            [Asm.lbl endLbl] ++ post)) = .ok (env.code, env.labels) := by
          rw [hlistC]; exact hlink
        have rc := evalCond_sim_gen lm env hm L m loc pre
          (c1 ++ [Asm.j endLbl, Asm.lbl elseLbl] ++ c2 ++ [Asm.lbl endLbl] ++ post)
          0 pfx (lblId + 1) c false elseLbl (lm.totalSize (pre ++ cc ++ c1 ++ [Asm.j endLbl]))
          hc hvars.1 (by omega) helse hlinkC
          (by rw [htw_cs] at h64; dsimp only [cc, id1, c1, id2, c2] at h64 ⊢; omega)
          st hpc hgp hsp hmemRel hframeOk
        rcases hc.evalC_pure ⟨m, loc⟩ with ⟨bc, hbc⟩ | hbc
        · cases bc
          · simp only [hbc] at rc
            obtain ⟨kc, st1, hrun1, hpc1, hpres1, heq1⟩ := rc
            have hstep : _root_.L.step p kfn (.ite c s1 s2) ⟨m, loc⟩ = _root_.L.step p kfn s2 ⟨m, loc⟩ := by
              simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hbc]
            rw [hstep]
            have htwElse : lm.totalSize (pre ++ cc ++ c1 ++ [Asm.j endLbl, Asm.lbl elseLbl]) =
                lm.totalSize (pre ++ cc ++ c1 ++ [Asm.j endLbl]) := by
              rw [show pre ++ cc ++ c1 ++ [Asm.j endLbl, Asm.lbl elseLbl] =
                (pre ++ cc ++ c1 ++ [Asm.j endLbl]) ++ [Asm.lbl elseLbl] by simp]
              simp [Asm.lbl, lm.itemSize_label]
            have hpc1' : st1.pc = BitVec.ofNat 64
                (4 * lm.totalSize (pre ++ cc ++ c1 ++ [Asm.j endLbl, Asm.lbl elseLbl])) := by
              rw [htwElse]; exact hpc1
            have hlist2 : (pre ++ cc ++ c1 ++ [Asm.j endLbl, Asm.lbl elseLbl]) ++ c2 ++ ([Asm.lbl endLbl] ++ post) =
                pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ite c s1 s2)).1 ++ post := by
              rw [hcs]; simp only [List.append_assoc, List.cons_append, List.nil_append]
            have hlink2 : lm.linkSpec ((pre ++ cc ++ c1 ++ [Asm.j endLbl, Asm.lbl elseLbl]) ++
                c2 ++ ([Asm.lbl endLbl] ++ post)) = .ok (env.code, env.labels) := by
              rw [hlist2]; exact hlink
            have h64_2 : 4 * (lm.totalSize (pre ++ cc ++ c1 ++ [Asm.j endLbl, Asm.lbl elseLbl]) +
                lm.totalSize c2) < 2 ^ 64 := by
              rw [htwElse]; simp only [(lm.totalSize_append)]
              have h1 : lm.totalSize [Asm.j endLbl] = jSz := by simp [Asm.j, jSz]
              rw [htw_cs] at h64; dsimp only [cc, id1, c1, id2, c2] at h64 ⊢; omega
            have r2 := ih2 m loc (pre ++ cc ++ c1 ++ [Asm.j endLbl, Asm.lbl elseLbl])
              ([Asm.lbl endLbl] ++ post) pfx id2 brkLbl hvars.2.2 (by omega) hlink2 h64_2
              st1 hpc1' (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
              (memRel_of_eqOutside_temp hm (Nat.zero_le _) heq1 hmemRel)
              (frameOk_of_eqOutside_temp (Nat.zero_le _) heq1 hframeOk)
            cases hst2 : _root_.L.step p kfn s2 ⟨m, loc⟩ with
            | error err =>
              rw [hst2] at r2
              cases err with
              | oob =>
                obtain ⟨k2, st2, hrun2, hpc2, hpres2⟩ := r2
                exact ⟨kc + k2, st2, by rw [run_add, hrun1]; exact hrun2, hpc2, hpres1.trans hpres2⟩
              | abort code =>
                obtain ⟨k2, st2, hrun2, hpc2, ha0_2, hpres2⟩ := r2
                exact ⟨kc + k2, st2, by rw [run_add, hrun1]; exact hrun2, hpc2, ha0_2, hpres1.trans hpres2⟩
              | outOfFuel => cases r2
              | noFun _ => cases r2
            | ok res2 =>
              rcases res2 with ⟨sig2, ⟨m2, loc2⟩⟩
              rw [hst2] at r2
              cases sig2 with
              | brk => cases r2
              | ret vs =>
                obtain ⟨k2, st2, hrun2, hpc2, hpres2, hres2⟩ := r2
                exact ⟨kc + k2, st2, by rw [run_add, hrun1]; exact hrun2, hpc2, hpres1.trans hpres2, hres2⟩
              | normal =>
                obtain ⟨k2, st2, hrun2, hpc2, hpres2, hrel2, hfr2⟩ := r2
                refine ⟨kc + k2, st2, by rw [run_add, hrun1]; exact hrun2, ?_,
                  hpres1.trans hpres2, hrel2, hfr2⟩
                rw [hpc2, ← (lm.totalSize_append) _ c2, htw_end]
          · simp only [hbc] at rc
            obtain ⟨kc, st1, hrun1, hpc1, hpres1, heq1⟩ := rc
            have hstep : _root_.L.step p kfn (.ite c s1 s2) ⟨m, loc⟩ = _root_.L.step p kfn s1 ⟨m, loc⟩ := by
              simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hbc]
            rw [hstep]
            have htw1 : lm.totalSize (pre ++ cc) = lm.totalSize pre + lm.totalSize cc := (lm.totalSize_append) _ _
            have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ cc)) := by rw [htw1]; exact hpc1
            have hlist1 : (pre ++ cc) ++ c1 ++ ([Asm.j endLbl, Asm.lbl elseLbl] ++ c2 ++ [Asm.lbl endLbl] ++ post) =
                pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ite c s1 s2)).1 ++ post := by
              rw [hcs]; simp only [List.append_assoc, List.cons_append, List.nil_append]
            have hlink1 : lm.linkSpec ((pre ++ cc) ++ c1 ++
                ([Asm.j endLbl, Asm.lbl elseLbl] ++ c2 ++ [Asm.lbl endLbl] ++ post)) =
                .ok (env.code, env.labels) := by
              rw [hlist1]; exact hlink
            have h64_1 : 4 * (lm.totalSize (pre ++ cc) + lm.totalSize c1) < 2 ^ 64 := by
              have := htw1; rw [htw_cs] at h64; dsimp only [cc, id1, c1, id2, c2] at this h64 ⊢; omega
            have r1 := ih1 m loc (pre ++ cc)
              ([Asm.j endLbl, Asm.lbl elseLbl] ++ c2 ++ [Asm.lbl endLbl] ++ post)
              pfx id1 brkLbl hvars.2.1 (by omega) hlink1 h64_1
              st1 hpc1' (hpres1.gp.trans hgp) (hpres1.sp.trans hsp)
              (memRel_of_eqOutside_temp hm (Nat.zero_le _) heq1 hmemRel)
              (frameOk_of_eqOutside_temp (Nat.zero_le _) heq1 hframeOk)
            cases hst1 : _root_.L.step p kfn s1 ⟨m, loc⟩ with
            | error err =>
              rw [hst1] at r1
              cases err with
              | oob =>
                obtain ⟨k1, st2, hrun2, hpc2, hpres2⟩ := r1
                exact ⟨kc + k1, st2, by rw [run_add, hrun1]; exact hrun2, hpc2, hpres1.trans hpres2⟩
              | abort code =>
                obtain ⟨k1, st2, hrun2, hpc2, ha0_2, hpres2⟩ := r1
                exact ⟨kc + k1, st2, by rw [run_add, hrun1]; exact hrun2, hpc2, ha0_2, hpres1.trans hpres2⟩
              | outOfFuel => cases r1
              | noFun _ => cases r1
            | ok res1 =>
              rcases res1 with ⟨sig1, ⟨m1, loc1⟩⟩
              rw [hst1] at r1
              cases sig1 with
              | brk => cases r1
              | ret vs =>
                obtain ⟨k1, st2, hrun2, hpc2, hpres2, hres2⟩ := r1
                exact ⟨kc + k1, st2, by rw [run_add, hrun1]; exact hrun2, hpc2, hpres1.trans hpres2, hres2⟩
              | normal =>
                obtain ⟨k1, st2, hrun2, hpc2, hpres2, hrel2, hfr2⟩ := r1
                have htw2 : lm.totalSize (pre ++ cc ++ c1) = lm.totalSize pre + lm.totalSize cc + lm.totalSize c1 := by
                  rw [(lm.totalSize_append), htw1]
                have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ cc ++ c1)) := by
                  rw [hpc2, htw2, htw1]
                have hlistJ : (pre ++ cc ++ c1) ++ [Asm.j endLbl] ++ ([Asm.lbl elseLbl] ++ c2 ++ [Asm.lbl endLbl] ++ post) =
                    pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl (.ite c s1 s2)).1 ++ post := by
                  rw [hcs]; simp only [List.append_assoc, List.cons_append, List.nil_append]
                have hlinkJ : lm.linkSpec ((pre ++ cc ++ c1) ++ [Asm.j endLbl] ++
                    ([Asm.lbl elseLbl] ++ c2 ++ [Asm.lbl endLbl] ++ post)) = .ok (env.code, env.labels) := by
                  rw [hlistJ]; exact hlink
                obtain ⟨tgt, kj, st3, _, hlook, hrunJ, hpc3, hreg3, hmem3⟩ :=
                  step_item_j_lm lm env.hrom (pre ++ cc ++ c1)
                    ([Asm.lbl elseLbl] ++ c2 ++ [Asm.lbl endLbl] ++ post) endLbl hlinkJ
                    (by have := htw2; rw [htw_cs] at h64; dsimp only [cc, id1, c1, id2, c2, Asm.j, jSz] at this h64 ⊢; omega)
                    st2 hpc2'
                have htgt : tgt = lm.totalSize (pre ++ cc ++ c1 ++ [Asm.j endLbl, Asm.lbl elseLbl] ++ c2) := by
                  rw [hend] at hlook; cases hlook; rfl
                subst htgt
                refine ⟨kc + (k1 + kj), st3, ?_, ?_, hpres1.trans (hpres2.trans (PreservedRegs.of_regEqExceptT6 hreg3)),
                  hmem3 ▸ hrel2, hmem3 ▸ hfr2⟩
                · rw [run_add, hrun1]; dsimp only
                  rw [run_add, hrun2]; dsimp only
                  exact hrunJ
                · rw [hpc3, htw_end]
        · simp only [hbc] at rc
          have hstep : _root_.L.step p kfn (.ite c s1 s2) ⟨m, loc⟩ = .error .oob := by
            simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hbc]
          rw [hstep]
          obtain ⟨kc, st1, hrun1, hpc1, hpres1, _⟩ := rc
          exact ⟨kc, st1, hrun1, hpc1, hpres1⟩
  | ret es hes =>
    exact ret_sim_gen lm env hm hnres L p kfn pfx lblId brkLbl m loc pre post retLbl retTgt es hes hvars
      (by dsimp only [maxTempsStmt] at htmp; exact htmp) hret hlink h64 st hpc hgp hsp hmemRel hframeOk
  | abort e he =>
    let ce := compileE env.tab nlocals 0 e
    let cj : List AsmItem := [Asm.j abortLabel]
    have hcs : (compileS env.tab nlocals pfx lblId brkLbl retLbl (.abort e)).1 = ce ++ cj := rfl
    let jSz := lm.itemSize (.j abortLabel)
    have htw_cs : lm.totalSize (compileS env.tab nlocals pfx lblId brkLbl retLbl (.abort e)).1 =
        lm.totalSize ce + jSz := by rw [hcs, lm.totalSize_append]; simp [cj, Asm.j, jSz]
    have hlistE : pre ++ ce ++ (cj ++ post) =
        pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl (.abort e)).1 ++ post := by
      rw [hcs]; simp only [List.append_assoc]
    have hlinkE : lm.linkSpec (pre ++ ce ++ (cj ++ post)) = .ok (env.code, env.labels) := by
      rw [hlistE]; exact hlink
    have re := evalExpr_sim_gen lm env hm L m loc pre (cj ++ post) 0 e he hvars
      (by dsimp only [maxTempsStmt] at htmp; omega)
      hlinkE (by rw [htw_cs] at h64; dsimp only [ce] at h64 ⊢; omega)
      st hpc hgp hsp hmemRel hframeOk
    rcases he.evalE_pure ⟨m, loc⟩ with ⟨v, hvE⟩ | hvE
    · simp only [hvE] at re
      obtain ⟨ke, st1, hrun1, hpc1, ha0_1, hpres1, _⟩ := re
      have hstep : _root_.L.step p kfn (.abort e) ⟨m, loc⟩ = .error (.abort v) := by
        simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvE,
          throw, throwThe, MonadExceptOf.throw, StateT.lift]
      rw [hstep]
      have htw1 : lm.totalSize (pre ++ ce) = lm.totalSize pre + lm.totalSize ce := (lm.totalSize_append) _ _
      have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lm.totalSize (pre ++ ce)) := by rw [htw1]; exact hpc1
      have hlistJ : (pre ++ ce) ++ [Asm.j abortLabel] ++ post =
          pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl (.abort e)).1 ++ post := by
        rw [hcs]; simp only [cj, List.append_assoc]
      have hlinkJ : lm.linkSpec ((pre ++ ce) ++ [Asm.j abortLabel] ++ post) = .ok (env.code, env.labels) := by
        rw [hlistJ]; exact hlink
      obtain ⟨tgt, kj, st2, _, hlook, hrunJ, hpc2, hreg2, _⟩ :=
        step_item_j_lm lm env.hrom (pre ++ ce) post abortLabel hlinkJ
          (by have := htw1; rw [htw_cs] at h64; dsimp only [ce, Asm.j, jSz] at this h64 ⊢; omega) st1 hpc1'
      have htgt : tgt = env.abortTarget := by rw [env.habortLbl] at hlook; cases hlook; rfl
      subst htgt
      refine ⟨ke + kj, st2, ?_, hpc2, (hreg2.getReg_eq (by decide)).symm.trans ha0_1,
        hpres1.trans (PreservedRegs.of_regEqExceptT6 hreg2)⟩
      · rw [run_add, hrun1]; exact hrunJ
    · simp only [hvE] at re
      have hstep : _root_.L.step p kfn (.abort e) ⟨m, loc⟩ = .error .oob := by
        simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvE]
      rw [hstep]
      obtain ⟨ke, st1, hrun1, hpc1, hpres1, _⟩ := re
      exact ⟨ke, st1, hrun1, hpc1, hpres1⟩


theorem evalExpr_sim (env : CodeEnv) (hm : TabMapOk env.tab)
    {nlocals ntemps : Nat} (L : Layout env.tab nlocals ntemps)
    (m : _root_.L.Mem) (loc : _root_.L.Locals)
    (pre post : List AsmItem) (tmp : Nat) (e : Expr)
    (he : CoreExpr env.tab e) (hvars : exprVarsLt nlocals e)
    (htmp : tmp + maxTempsExpr e ≤ ntemps)
    (hlink : linkResolved (pre ++ compileE env.tab nlocals tmp e ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (totalWords pre + totalWords (compileE env.tab nlocals tmp e)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * totalWords pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = L.sp)
    (hmemRel : MemRel env.tab L st.mem m) (hframeOk : FrameOk L st.mem nlocals loc) :
    match evalE e ⟨m, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (totalWords pre + totalWords (compileE env.tab nlocals tmp e))) ∧
        st'.getReg AbiReg.a0 = v.toBitVec ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem := by
  simp only [← near_totalSize_eq] at h64 hpc ⊢
  exact evalExpr_sim_gen nearLinkModel env.toGen hm L m loc pre post tmp e he hvars htmp hlink h64 st hpc hgp hsp hmemRel hframeOk

theorem lookupLabel_of_lbl {code : Array (BitVec 32)} {labels : LabelMap}
    (pre post : List AsmItem) (name : String)
    (hlink : linkResolved (pre ++ [Asm.lbl name] ++ post) = .ok (code, labels)) :
    lookupLabel labels name = some (totalWords pre) := by
  rw [← near_totalSize_eq]
  exact lookupLabel_of_lbl_lm nearLinkModel pre post name hlink

theorem evalCond_sim (env : CodeEnv) (hm : TabMapOk env.tab)
    {nlocals ntemps : Nat} (L : Layout env.tab nlocals ntemps)
    (m : _root_.L.Mem) (loc : _root_.L.Locals)
    (pre post : List AsmItem) (tmp : Nat) (pfx : String) (lblId : Nat)
    (c : Cond) (want : Bool) (target : String) (tgt : Nat)
    (hc : CoreCond env.tab c) (hvars : condVarsLt nlocals c)
    (htmp : tmp + maxTempsCond c ≤ ntemps)
    (htgt : lookupLabel env.labels target = some tgt)
    (hlink : linkResolved (pre ++ (compileC env.tab nlocals tmp pfx lblId c want target).1 ++ post) =
        .ok (env.code, env.labels))
    (h64 : 4 * (totalWords pre + totalWords (compileC env.tab nlocals tmp pfx lblId c want target).1) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * totalWords pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = L.sp)
    (hmemRel : MemRel env.tab L st.mem m) (hframeOk : FrameOk L st.mem nlocals loc) :
    match evalC c ⟨m, loc⟩ with
    | .ok (b, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (if b == want then tgt else
          totalWords pre + totalWords (compileC env.tab nlocals tmp pfx lblId c want target).1)) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedRegs st st' ∧
        MemEqOutside (tempSpan L.sp nlocals tmp ntemps) st.mem st'.mem := by
  simp only [← near_totalSize_eq] at h64 hpc ⊢
  exact evalCond_sim_gen nearLinkModel env.toGen hm L m loc pre post tmp pfx lblId c want target tgt hc hvars htmp htgt hlink h64 st hpc hgp hsp hmemRel hframeOk

theorem execStmt_sim (env : CodeEnv) (hm : TabMapOk env.tab) (hnres : env.tab.nres ≤ maxRes)
    {nlocals ntemps : Nat} (L : Layout env.tab nlocals ntemps)
    (p : Prog) (kfn : Stmt → M Sig)
    (m : _root_.L.Mem) (loc : _root_.L.Locals)
    (pre post : List AsmItem) (pfx : String) (lblId : Nat)
    (brkLbl : Option String) (retLbl : String) (retTgt : Nat) (s : Stmt)
    (hs : CoreStmt env.tab nlocals s) (hvars : stmtVarsLt nlocals s)
    (htmp : maxTempsStmt s ≤ ntemps)
    (hret : lookupLabel env.labels retLbl = some retTgt)
    (hlink : linkResolved (pre ++ (compileS env.tab nlocals pfx lblId brkLbl retLbl s).1 ++ post) =
        .ok (env.code, env.labels))
    (h64 : 4 * (totalWords pre + totalWords (compileS env.tab nlocals pfx lblId brkLbl retLbl s).1) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * totalWords pre))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = L.sp)
    (hmemRel : MemRel env.tab L st.mem m) (hframeOk : FrameOk L st.mem nlocals loc) :
    match _root_.L.step p kfn s ⟨m, loc⟩ with
    | .ok (.normal, ⟨m', loc'⟩) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (totalWords pre + totalWords (compileS env.tab nlocals pfx lblId brkLbl retLbl s).1)) ∧
        PreservedRegs st st' ∧ MemRel env.tab L st'.mem m' ∧ FrameOk L st'.mem nlocals loc'
    | .ok (.ret vs, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * retTgt) ∧ PreservedRegs st st' ∧
        (∀ i, i < min (max 1 vs.length) env.tab.nres → st'.getReg (resReg i) = (vs.getD i 0).toBitVec)
    | .error .oob =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧ PreservedRegs st st'
    | .error (.abort code) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.abortTarget) ∧
        st'.getReg AbiReg.a0 = code.toBitVec ∧ PreservedRegs st st'
    | _ => False := by
  simp only [← near_totalSize_eq] at h64 hpc ⊢
  exact execStmt_sim_gen nearLinkModel env.toGen hm hnres L p kfn m loc pre post pfx lblId brkLbl retLbl retTgt s hs hvars htmp hret hlink h64 st hpc hgp hsp hmemRel hframeOk

/-- info: 'ConAgua.RISCV.Compiler.evalExpr_sim_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms evalExpr_sim_gen

/-- info: 'ConAgua.RISCV.Compiler.evalCond_sim_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms evalCond_sim_gen

/-- info: 'ConAgua.RISCV.Compiler.execStmt_sim_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms execStmt_sim_gen

/-- info: 'ConAgua.RISCV.Compiler.evalExpr_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms evalExpr_sim

/-- info: 'ConAgua.RISCV.Compiler.evalCond_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms evalCond_sim

/-- info: 'ConAgua.RISCV.Compiler.execStmt_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms execStmt_sim

end ConAgua.RISCV.Compiler
