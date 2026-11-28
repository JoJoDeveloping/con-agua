import ConAgua.RISCV.Bridge.CheckerLinkWfBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Algebraic `farTotalWords` Size-Bound Lemmas (`ConAgua.RISCV.Bridge.CheckerLinkSize`)

Proves algebraic per-expression, per-statement, per-function (`compileFn_farTotalWords_le`),
and driver (`checkerDriverAsm_farTotalWords_le`, `checkerCmpDriverAsm_farTotalWords_le`)
word-count bounds.
-/

namespace ConAgua.RISCV.Bridge

open ConAgua.RISCV.RV64
open ConAgua.RISCV.Compiler
open ConAgua.RISCV.Linker
open _root_.L

/-! ## 5. Algebraic `farTotalWords` Size Bound (`< 2 ^ 22`) -/

private def ntreeAllLt (lim : Nat) : NTree → Bool
  | .leaf => true
  | .node l _ v r => v < lim && ntreeAllLt lim l && ntreeAllLt lim r

private theorem ntreeAllLt_find {lim : Nat} (t : NTree) (ht : ntreeAllLt lim t = true) :
    ∀ k v, NTree.find k t = some v → v < lim := by
  induction t with
  | leaf =>
    intro k v h
    simp only [NTree.find] at h
    cases h
  | node l _ v' r ihl ihr =>
    intro k v h
    simp only [ntreeAllLt, Bool.and_eq_true, decide_eq_true_eq] at ht
    dsimp only [NTree.find] at h
    split at h
    · exact ihl ht.1.2 _ _ h
    · split at h
      · cases h; exact ht.1.1
      · exact ihr ht.2 _ _ h

section CheckerTabCheck
set_option maxRecDepth 524288

private theorem checkerTabMini_lmap_lt : ntreeAllLt 250 checkerTabMini.lmap = true := by rfl

/-- Tab has all offsets bounded inside `[0, 2 ^ 31)`. -/
structure TabSmall32 (tab : Tab) : Prop where
  pos_lt : ∀ s : TieredArray, tab.pos64 s < 250
  pos8_lt : ∀ a : ArrId, tab.pos8 a < 250
  nb_le : tab.nb ≤ 10
  nw_le : tab.nw ≤ 250
  ng_le : tab.ng ≤ 20
  nres_le : tab.nres ≤ 10
  nxres_le : tab.nxres ≤ 20
  rom_le : tab.rom.length ≤ 40000

private theorem tab_pos64_lt_checkerTabMini (s : TieredArray) :
    checkerTabMini.pos64 s < 250 := by
  dsimp only [Tab.pos64]
  cases hf : NTree.find s.code checkerTabMini.lmap with
  | none => simp
  | some v => simpa using ntreeAllLt_find _ checkerTabMini_lmap_lt _ _ hf

theorem checkerTabMini_small32 : TabSmall32 checkerTabMini where
  pos_lt := tab_pos64_lt_checkerTabMini
  pos8_lt := fun a => tab_pos64_lt_checkerTabMini (TieredArray.t0 a)
  nb_le := by decide
  nw_le := by decide
  ng_le := by decide
  nres_le := by decide
  nxres_le := by decide
  rom_le := by decide

end CheckerTabCheck

private theorem tab_offsets_32 {tab : Tab} (ht : TabSmall32 tab) :
    (∀ a, 0 ≤ tab.len8 a ∧ tab.len8 a < 2 ^ 31) ∧
    (∀ a, 0 ≤ tab.base8 a ∧ tab.base8 a < 2 ^ 31) ∧
    (∀ s, 0 ≤ tab.len64 s ∧ tab.len64 s < 2 ^ 31) ∧
    (∀ s, 0 ≤ tab.base64 s ∧ tab.base64 s < 2 ^ 31) ∧
    (∀ g, g.id < tab.ng → 0 ≤ tab.globOff g ∧ tab.globOff g < 2 ^ 31) ∧
    (∀ i, i < tab.nres → 0 ≤ tab.resOff i ∧ tab.resOff i < 2 ^ 31) ∧
    (∀ d, 0 ≤ tab.romBase + (romIdx d tab.rom : Int) ∧
        tab.romBase + (romIdx d tab.rom : Int) < 2 ^ 31) := by
  have hnb := ht.nb_le
  have hnw := ht.nw_le
  have hng := ht.ng_le
  have hnres := ht.nres_le
  have hnxres := ht.nxres_le
  have hrom := ht.rom_le
  have hromWords : tab.romWords ≤ 5000 := by
    dsimp only [Tab.romWords]; omega
  have hromBase : 0 ≤ tab.romBase ∧ tab.romBase ≤ 7000 := by
    dsimp only [Tab.romBase]; omega
  have hresBase : 0 ≤ tab.resBase ∧ tab.resBase ≤ 50000 := by
    dsimp only [Tab.resBase]; omega
  have hglobBase : 0 ≤ tab.globBase ∧ tab.globBase ≤ 50200 := by
    dsimp only [Tab.globBase]; omega
  have hromIdx : ∀ (d r : List UInt8), romIdx d r ≤ r.length := by
    intro d r
    induction r with
    | nil => simp [romIdx]
    | cons b bs ih =>
      unfold romIdx
      split
      · exact Nat.zero_le _
      · exact Nat.succ_le_succ ih
  refine ⟨fun a => ?_, fun a => ?_, fun s => ?_, fun s => ?_, fun g hg => ?_, fun i hi => ?_, fun d => ?_⟩
  · have hp := ht.pos8_lt a; dsimp only [Tab.len8, Tab.dlen]; omega
  · have hp := ht.pos8_lt a; dsimp only [Tab.base8, Tab.dbase]; omega
  · have hp := ht.pos_lt s; dsimp only [Tab.len64, Tab.dlen]; omega
  · have hp := ht.pos_lt s; dsimp only [Tab.base64, Tab.dbase]; omega
  · dsimp only [Tab.globOff]; omega
  · dsimp only [Tab.resOff]; omega
  · have hidx := hromIdx d tab.rom; omega

private theorem slotOff_32 {x : Nat} (hx : x < 100000) :
    0 ≤ slotOff x ∧ slotOff x < 2 ^ 31 := by
  dsimp [slotOff]; omega

/-- Tight 32-bit-offset algebraic word bound for `Expr`. -/
def exprBound32 : Expr → Nat
  | .const _ => 10
  | .var _ => 6
  | .len8 _ | .len64 _ | .glob _ => 6
  | .bin _ a b => exprBound32 a + exprBound32 b + 17
  | .cmpw _ a b => exprBound32 a + exprBound32 b + 14
  | .ld8 _ i => exprBound32 i + 19
  | .ld64 _ i => exprBound32 i + 20
  | .ldc _ i => exprBound32 i + 22
  | .ld64t _ a b => exprBound32 a + exprBound32 b + 35
  | .len64t _ i => exprBound32 i + 9
  | .ld8x8 _ i => exprBound32 i + 54
  | .ld32t _ a b => exprBound32 a + exprBound32 b + 36
  | .ld32h _ a b _ => exprBound32 a + exprBound32 b + 35

def warrBound32 : WArr → Nat
  | .plain _ => 6
  | .tier _ t => exprBound32 t + 6

def condBound32 : Cond → Nat
  | .cmp _ a b => exprBound32 a + exprBound32 b + 17
  | .and p q | .or p q => condBound32 p + condBound32 q
  | .not p => condBound32 p

def exprsBound32 : List Expr → Nat
  | [] => 0
  | e :: es => exprBound32 e + 6 + exprsBound32 es

def stmtBound32 (nres : Nat) : Stmt → Nat
  | .skip => 0
  | .set _ e | .gset _ e => exprBound32 e + 6
  | .st8 _ _ _ => 0
  | .st64 _ i e => exprBound32 i + exprBound32 e + 32
  | .st64t _ t i e => exprBound32 t + exprBound32 i + exprBound32 e + 47
  | .st32t _ t i e => exprBound32 t + exprBound32 i + exprBound32 e + 48
  | .seq s1 s2 => stmtBound32 nres s1 + stmtBound32 nres s2
  | .ite c s1 s2 => condBound32 c + stmtBound32 nres s1 + stmtBound32 nres s2 + 4
  | .while c b => condBound32 c + stmtBound32 nres b + 10
  | .brk => 4
  | .ret es => exprsBound32 es + 12 * nres + 4
  | .call xs _ args => exprsBound32 args + 16 + 6 * min args.length maxRes + 12 * xs.length
  | .abort e => exprBound32 e + 4
  | .copy64 d di src si n => warrBound32 d + exprBound32 di + warrBound32 src + exprBound32 si + exprBound32 n + 120
  | .copy8w d di _ si n => warrBound32 d + exprBound32 di + exprBound32 si + exprBound32 n + 115
  | .scan8 _ _ i k _ => exprBound32 i + exprBound32 k + 70

def fnBound32 (nres : Nat) (fd : FunDecl) : Nat :=
  59 + 12 * fd.nparams + 6 * (numLocalsFn fd - fd.nparams) + stmtBound32 nres fd.body

private theorem emitSimpleExpr_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab) {nlocals : Nat}
    (hnl : nlocals < 100000) {rd tmp : Reg} {e : Expr} {cs : List AsmItem}
    (hok : exprOkConst0B tab nlocals e = true)
    (h : emitSimpleExpr tab rd tmp e = some cs) :
    farTotalWords cs ≤ exprBound32 e := by
  obtain ⟨hlen8, _, hlen64, _, hglob, _, _⟩ := tab_offsets_32 ht
  cases e with
  | const w => cases h; exact li_farTotalWords_le rd _
  | var x =>
    cases h
    simp only [exprOkConst0B, decide_eq_true_eq] at hok
    have hslot := slotOff_32 (Nat.lt_trans hok hnl)
    exact loadMemOff_farTotalWords_le_32 .ld rd AbiReg.sp tmp (slotOff x) hslot.1 hslot.2
  | len8 a =>
    cases h
    exact loadMemOff_farTotalWords_le_32 .ld rd AbiReg.gp tmp (tab.len8 a) (hlen8 a).1 (hlen8 a).2
  | len64 a =>
    cases h
    exact loadMemOff_farTotalWords_le_32 .ld rd AbiReg.gp tmp (tab.len64 (TieredArray.t0 a))
      (hlen64 (TieredArray.t0 a)).1 (hlen64 (TieredArray.t0 a)).2
  | glob g =>
    cases h
    simp only [exprOkConst0B, decide_eq_true_eq] at hok
    exact loadMemOff_farTotalWords_le_32 .ld rd AbiReg.gp tmp (tab.globOff g)
      (hglob g hok).1 (hglob g hok).2
  | bin _ _ _ | cmpw _ _ _ | ld8 _ _ | ld64 _ _ | ldc _ _ | ld64t _ _ _
  | len64t _ _ | ld8x8 _ _ | ld32t _ _ _ | ld32h _ _ _ _ => cases h

private theorem compileE_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab) (nlocals : Nat)
    (hnl : nlocals < 100000) :
    ∀ (e : Expr) (tmp : Nat),
      tmp + maxTempsExpr e < 100000 →
      exprOkConst0B tab nlocals e = true →
      farTotalWords (compileE tab nlocals tmp e) ≤ exprBound32 e := by
  intro e
  obtain ⟨hlen8, hbase8, hlen64, hbase64, hglob, _, hrom⟩ := tab_offsets_32 ht
  induction e with
  | const w =>
    intro tmp _ _
    exact li_farTotalWords_le _ _
  | var x =>
    intro tmp _ hok
    simp only [exprOkConst0B, decide_eq_true_eq] at hok
    have hslot := slotOff_32 (Nat.lt_trans hok hnl)
    exact loadMemOff_farTotalWords_le_32 _ _ _ _ _ hslot.1 hslot.2
  | len8 a =>
    intro tmp _ _
    exact loadMemOff_farTotalWords_le_32 _ _ _ _ _ (hlen8 a).1 (hlen8 a).2
  | len64 a =>
    intro tmp _ _
    exact loadMemOff_farTotalWords_le_32 _ _ _ _ _ (hlen64 (TieredArray.t0 a)).1 (hlen64 (TieredArray.t0 a)).2
  | glob g =>
    intro tmp _ hok
    simp only [exprOkConst0B, decide_eq_true_eq] at hok
    exact loadMemOff_farTotalWords_le_32 _ _ _ _ _ (hglob g hok).1 (hglob g hok).2
  | bin op a b iha ihb =>
    intro tmp htmp hok
    simp only [maxTempsExpr] at htmp
    simp only [exprOkConst0B, Bool.and_eq_true] at hok
    dsimp only [compileE, exprBound32]
    cases b.constVal? with
    | some w =>
      rw [farTotalWords_append]
      have ha := iha tmp (by omega) hok.1
      have hr := emitBinConstRhs_farTotalWords_le op w
      omega
    | none =>
      cases a.constVal? with
      | some w =>
        have hb := ihb tmp (by omega) hok.2
        cases op with
        | add | and | or | xor | mul | «mulhi» =>
          dsimp only
          rw [farTotalWords_append]
          have hr : ∀ op', farTotalWords (emitBinConstRhs op' w) ≤ 11 :=
            fun op' => emitBinConstRhs_farTotalWords_le op' w
          have h1 := hr .add; have h2 := hr .and; have h3 := hr .or
          have h4 := hr .xor; have h5 := hr .mul; have h6 := hr .mulhi
          omega
        | sub =>
          dsimp only
          split
          · rw [farTotalWords_append]
            have h1 : farTotalWords [Asm.sub AbiReg.a0 AbiReg.zero AbiReg.a0] = 1 := rfl
            omega
          · simp only [farTotalWords_append]
            have hli := li_farTotalWords_le AbiReg.t0 w.toBitVec
            have h1 : farTotalWords [Asm.sub AbiReg.a0 AbiReg.t0 AbiReg.a0] = 1 := rfl
            omega
        | shl =>
          dsimp only
          simp only [farTotalWords_append]
          have hli := li_farTotalWords_le AbiReg.t0 w.toBitVec
          have h1 : farTotalWords [Asm.sll AbiReg.a0 AbiReg.t0 AbiReg.a0] = 1 := rfl
          omega
        | shr =>
          dsimp only
          simp only [farTotalWords_append]
          have hli := li_farTotalWords_le AbiReg.t0 w.toBitVec
          have h1 : farTotalWords [Asm.srl AbiReg.a0 AbiReg.t0 AbiReg.a0] = 1 := rfl
          omega
      | none =>
        cases hsb : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 b with
        | some cb =>
          simp only [farTotalWords_append]
          have ha := iha tmp (by omega) hok.1
          have hb := emitSimpleExpr_farTotalWords_le ht hnl hok.2 hsb
          have hop := emitBinOp_farTotalWords op AbiReg.a0 AbiReg.a0 AbiReg.t0
          omega
        | none =>
          cases hsa : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 a with
          | some ca =>
            simp only [farTotalWords_append]
            have hb := ihb tmp (by omega) hok.2
            have ha := emitSimpleExpr_farTotalWords_le ht hnl hok.1 hsa
            have hop := emitBinOp_farTotalWords op AbiReg.a0 AbiReg.t0 AbiReg.a0
            omega
          | none =>
            have ha := iha tmp (by omega) hok.1
            have hb := ihb (tmp + 1) (by omega) hok.2
            have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
              (slotOff (nlocals + tmp)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
            have hld := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.sp AbiReg.t1
              (slotOff (nlocals + tmp)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
            have hop := emitBinOp_farTotalWords op AbiReg.a0 AbiReg.t0 AbiReg.a0
            simp only [farTotalWords_append]
            omega
  | cmpw c a b iha ihb =>
    intro tmp htmp hok
    simp only [maxTempsExpr] at htmp
    simp only [exprOkConst0B, Bool.and_eq_true] at hok
    dsimp only [compileE, exprBound32]
    split
    · rw [farTotalWords_append]
      have ha := iha tmp (by omega) hok.1
      have h1 : farTotalWords [Asm.sltiu AbiReg.a0 AbiReg.a0 1#12] = 1 := rfl
      omega
    · split
      · rw [farTotalWords_append]
        have hb := ihb tmp (by omega) hok.2
        have h1 : farTotalWords [Asm.sltiu AbiReg.a0 AbiReg.a0 1#12] = 1 := rfl
        omega
      · split
        · rw [farTotalWords_append]
          have ha := iha tmp (by omega) hok.1
          have h1 : farTotalWords [Asm.sltu AbiReg.a0 AbiReg.zero AbiReg.a0] = 1 := rfl
          omega
        · split
          · rw [farTotalWords_append]
            have hb := ihb tmp (by omega) hok.2
            have h1 : farTotalWords [Asm.sltu AbiReg.a0 AbiReg.zero AbiReg.a0] = 1 := rfl
            omega
          · cases hsb : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 b with
            | some cb =>
              simp only [farTotalWords_append]
              have ha := iha tmp (by omega) hok.1
              have hb := emitSimpleExpr_farTotalWords_le ht hnl hok.2 hsb
              have hc := emitCmpw_farTotalWords_le c AbiReg.a0 AbiReg.t0
              omega
            | none =>
              cases hsa : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 a with
              | some ca =>
                simp only [farTotalWords_append]
                have hb := ihb tmp (by omega) hok.2
                have ha := emitSimpleExpr_farTotalWords_le ht hnl hok.1 hsa
                have hc := emitCmpw_farTotalWords_le c AbiReg.t0 AbiReg.a0
                omega
              | none =>
                have ha := iha tmp (by omega) hok.1
                have hb := ihb (tmp + 1) (by omega) hok.2
                have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
                  (slotOff (nlocals + tmp)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
                have hld := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.sp AbiReg.t1
                  (slotOff (nlocals + tmp)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
                have hc := emitCmpw_farTotalWords_le c AbiReg.t0 AbiReg.a0
                simp only [farTotalWords_append]
                omega
  | ld8 a i ih =>
    intro tmp htmp hok
    simp only [maxTempsExpr] at htmp
    simp only [exprOkConst0B, Bool.and_eq_true] at hok
    have hi := ih tmp htmp hok.2
    have hl1 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.gp AbiReg.t1 (tab.len8 a) (hlen8 a).1 (hlen8 a).2
    have hl2 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (tab.base8 a) (hbase8 a).1 (hbase8 a).2
    have hb1 : farTotalWords [Asm.bgeu AbiReg.a0 AbiReg.t0 errLabel] = 5 := rfl
    have hb2 : farTotalWords [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.a0, Asm.lbu AbiReg.a0 AbiReg.t1 0#12] = 2 := rfl
    simp only [compileE, farTotalWords_append, exprBound32]; omega
  | ld64 a i ih =>
    intro tmp htmp hok
    simp only [maxTempsExpr] at htmp
    simp only [exprOkConst0B, Bool.and_eq_true] at hok
    have hi := ih tmp htmp hok.2
    have hl1 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.gp AbiReg.t1
      (tab.len64 (TieredArray.t0 a)) (hlen64 _).1 (hlen64 _).2
    have hl2 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.gp AbiReg.t2
      (tab.base64 (TieredArray.t0 a)) (hbase64 _).1 (hbase64 _).2
    simp only [compileE, farTotalWords_append, exprBound32]
    have h1 : farTotalWords [Asm.bgeu AbiReg.a0 AbiReg.t0 errLabel] = 5 := rfl
    have h2 : farTotalWords [Asm.slli AbiReg.t2 AbiReg.a0 3#6,
        Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2, Asm.ld AbiReg.a0 AbiReg.t1 0#12] = 3 := rfl
    omega
  | ldc d i ih =>
    intro tmp htmp hok
    simp only [maxTempsExpr] at htmp
    simp only [exprOkConst0B, Bool.and_eq_true] at hok
    have hi := ih tmp htmp hok.2
    have hli10 := li_farTotalWords_le AbiReg.t0 (BitVec.ofNat 64 d.length)
    have hadd := addImmOff_farTotalWords_le_32 AbiReg.t1 AbiReg.gp AbiReg.t2
      (tab.romBase + (romIdx d tab.rom : Int)) (hrom d).1 (hrom d).2
    have hb1 : farTotalWords [Asm.bgeu AbiReg.a0 AbiReg.t0 errLabel] = 5 := rfl
    have hb2 : farTotalWords [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.a0, Asm.lbu AbiReg.a0 AbiReg.t1 0#12] = 2 := rfl
    simp only [compileE, farTotalWords_append, exprBound32]; omega
  | ld64t a t i iht ihi =>
    intro tmp htmp hok
    simp only [maxTempsExpr] at htmp
    simp only [exprOkConst0B, Bool.and_eq_true] at hok
    dsimp only [compileE, exprBound32]
    cases t.constVal? with
    | some w =>
      have hi := ihi tmp (by omega) hok.2
      have hl1 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t2 AbiReg.gp AbiReg.t3
        (tab.len64 (tierA a w)) (hlen64 _).1 (hlen64 _).2
      have hl2 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.gp AbiReg.t3
        (tab.base64 (tierA a w)) (hbase64 _).1 (hbase64 _).2
      have h2 : farTotalWords [Asm.bgeu AbiReg.a0 AbiReg.t2 errLabel] = 5 := rfl
      have h3 : farTotalWords [Asm.slli AbiReg.t3 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3,
          Asm.ld AbiReg.a0 AbiReg.t1 0#12] = 3 := rfl
      simp only [farTotalWords_append]
      omega
    | none =>
      dsimp only
      have hl1 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t2 AbiReg.t1 AbiReg.t3
        (tab.len64 (TieredArray.t0 a)) (hlen64 _).1 (hlen64 _).2
      have hl2 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.t1 AbiReg.t3
        (tab.base64 (TieredArray.t0 a)) (hbase64 _).1 (hbase64 _).2
      have h1 : farTotalWords [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
          Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] = 3 := rfl
      have h2 : farTotalWords [Asm.bgeu AbiReg.a0 AbiReg.t2 errLabel] = 5 := rfl
      have h3 : farTotalWords [Asm.slli AbiReg.t3 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3,
          Asm.ld AbiReg.a0 AbiReg.t1 0#12] = 3 := rfl
      cases hst : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 t with
      | some ct =>
        dsimp only
        have hi := ihi tmp (by omega) hok.2
        have ht' := emitSimpleExpr_farTotalWords_le ht hnl hok.1.2 hst
        simp only [farTotalWords_append]; omega
      | none =>
        dsimp only
        have ha := iht tmp (by omega) hok.1.2
        have hb := ihi (tmp + 1) (by omega) hok.2
        have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
          (slotOff (nlocals + tmp)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
        have hld := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.sp AbiReg.t1
          (slotOff (nlocals + tmp)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
        simp only [farTotalWords_append]; omega
  | len64t a t ih =>
    intro tmp htmp hok
    simp only [maxTempsExpr] at htmp
    simp only [exprOkConst0B, Bool.and_eq_true] at hok
    dsimp only [compileE, exprBound32]
    cases t.constVal? with
    | some w =>
      dsimp only
      have hl := loadMemOff_farTotalWords_le_32 .ld AbiReg.a0 AbiReg.gp AbiReg.t2
        (tab.len64 (tierA a w)) (hlen64 _).1 (hlen64 _).2
      omega
    | none =>
      dsimp only
      have hi := ih tmp htmp hok.2
      have hl := loadMemOff_farTotalWords_le_32 .ld AbiReg.a0 AbiReg.t1 AbiReg.t2
        (tab.len64 (TieredArray.t0 a)) (hlen64 _).1 (hlen64 _).2
      have h1 : farTotalWords [Asm.andi AbiReg.t0 AbiReg.a0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
          Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] = 3 := rfl
      simp only [farTotalWords_append]; omega
  | ld8x8 src i ih =>
    intro tmp htmp hok
    simp only [maxTempsExpr] at htmp
    have hmid : farTotalWords [Asm.addi AbiReg.t2 AbiReg.zero 8#12, Asm.bltu AbiReg.t0 AbiReg.t2 errLabel,
        Asm.addi AbiReg.t0 AbiReg.t0 (-8#12), Asm.bltu AbiReg.t0 AbiReg.a0 errLabel,
        Asm.add AbiReg.t1 AbiReg.t1 AbiReg.a0] = 13 := rfl
    have hread : farTotalWords ([Asm.lbu AbiReg.a0 AbiReg.t1 7#12] ++
        List.flatMap (fun k =>
          [Asm.lbu AbiReg.t2 AbiReg.t1 (BitVec.ofInt 12 k), Asm.slli AbiReg.a0 AbiReg.a0 8#6,
           Asm.or AbiReg.a0 AbiReg.a0 AbiReg.t2]) [6, 5, 4, 3, 2, 1, 0]) = 22 := by
      decide
    cases src with
    | arr a =>
      simp only [exprOkConst0B, Bool.and_eq_true] at hok
      have hi := ih tmp htmp hok.2
      have hl1 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.gp AbiReg.t2 (tab.len8 a) (hlen8 a).1 (hlen8 a).2
      have hl2 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.gp AbiReg.t2 (tab.base8 a) (hbase8 a).1 (hbase8 a).2
      simp only [compileE, farTotalWords_append, exprBound32]
      rw [farTotalWords_append] at hread
      omega
    | rom d =>
      simp only [exprOkConst0B, Bool.and_eq_true] at hok
      have hi := ih tmp htmp hok.2
      have hli := li_farTotalWords_le AbiReg.t0 (BitVec.ofNat 64 d.length)
      have hadd := addImmOff_farTotalWords_le_32 AbiReg.t1 AbiReg.gp AbiReg.t2
        (tab.romBase + (romIdx d tab.rom : Int)) (hrom d).1 (hrom d).2
      simp only [compileE, farTotalWords_append, exprBound32]
      rw [farTotalWords_append] at hread
      omega
  | ld32t a t i iht ihi =>
    intro tmp htmp hok
    simp only [maxTempsExpr] at htmp
    simp only [exprOkConst0B, Bool.and_eq_true] at hok
    dsimp only [compileE, exprBound32]
    cases t.constVal? with
    | some w =>
      have hi := ihi tmp (by omega) hok.2
      have hl1 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t2 AbiReg.gp AbiReg.t3
        (tab.len64 (tierA a w)) (hlen64 _).1 (hlen64 _).2
      have hl2 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.gp AbiReg.t3
        (tab.base64 (tierA a w)) (hbase64 _).1 (hbase64 _).2
      have h2 : farTotalWords [Asm.srli AbiReg.t3 AbiReg.a0 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] = 6 := rfl
      have h3 : farTotalWords [Asm.slli AbiReg.t3 AbiReg.a0 2#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3,
          Asm.lwu AbiReg.a0 AbiReg.t1 0#12] = 3 := rfl
      simp only [farTotalWords_append]; omega
    | none =>
      dsimp only
      have hl1 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t2 AbiReg.t1 AbiReg.t3
        (tab.len64 (TieredArray.t0 a)) (hlen64 _).1 (hlen64 _).2
      have hl2 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.t1 AbiReg.t3
        (tab.base64 (TieredArray.t0 a)) (hbase64 _).1 (hbase64 _).2
      have h1 : farTotalWords [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
          Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] = 3 := rfl
      have h2 : farTotalWords [Asm.srli AbiReg.t3 AbiReg.a0 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] = 6 := rfl
      have h3 : farTotalWords [Asm.slli AbiReg.t3 AbiReg.a0 2#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3,
          Asm.lwu AbiReg.a0 AbiReg.t1 0#12] = 3 := rfl
      cases hst : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 t with
      | some ct =>
        dsimp only
        have hi := ihi tmp (by omega) hok.2
        have ht' := emitSimpleExpr_farTotalWords_le ht hnl hok.1.2 hst
        simp only [farTotalWords_append]; omega
      | none =>
        dsimp only
        have ha := iht tmp (by omega) hok.1.2
        have hb := ihi (tmp + 1) (by omega) hok.2
        have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
          (slotOff (nlocals + tmp)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
        have hld := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.sp AbiReg.t1
          (slotOff (nlocals + tmp)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
        simp only [farTotalWords_append]; omega
  | ld32h a t i hi iht ihi =>
    intro tmp htmp hok
    simp only [maxTempsExpr] at htmp
    simp only [exprOkConst0B, Bool.and_eq_true] at hok
    dsimp only [compileE, exprBound32]
    cases t.constVal? with
    | some w =>
      dsimp only
      have hi' := ihi tmp (by omega) hok.2
      have hl1 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t2 AbiReg.gp AbiReg.t3
        (tab.len64 (tierA a w)) (hlen64 _).1 (hlen64 _).2
      have hl2 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.gp AbiReg.t3
        (tab.base64 (tierA a w)) (hbase64 _).1 (hbase64 _).2
      have h2 : farTotalWords [Asm.bgeu AbiReg.a0 AbiReg.t2 errLabel] = 5 := rfl
      have h3 : farTotalWords [Asm.slli AbiReg.t3 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3,
          Asm.lwu AbiReg.a0 AbiReg.t1 (if hi then 4#12 else 0#12)] = 3 := by cases hi <;> rfl
      simp only [farTotalWords_append]; omega
    | none =>
      dsimp only
      have hl1 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t2 AbiReg.t1 AbiReg.t3
        (tab.len64 (TieredArray.t0 a)) (hlen64 _).1 (hlen64 _).2
      have hl2 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.t1 AbiReg.t3
        (tab.base64 (TieredArray.t0 a)) (hbase64 _).1 (hbase64 _).2
      have h1 : farTotalWords [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
          Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] = 3 := rfl
      have h2 : farTotalWords [Asm.bgeu AbiReg.a0 AbiReg.t2 errLabel] = 5 := rfl
      have h3 : farTotalWords [Asm.slli AbiReg.t3 AbiReg.a0 3#6, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3,
          Asm.lwu AbiReg.a0 AbiReg.t1 (if hi then 4#12 else 0#12)] = 3 := by cases hi <;> rfl
      cases hst : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 t with
      | some ct =>
        dsimp only
        have hi' := ihi tmp (by omega) hok.2
        have ht' := emitSimpleExpr_farTotalWords_le ht hnl hok.1.2 hst
        simp only [farTotalWords_append]; omega
      | none =>
        dsimp only
        have ha := iht tmp (by omega) hok.1.2
        have hb := ihi (tmp + 1) (by omega) hok.2
        have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
          (slotOff (nlocals + tmp)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
        have hld := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.sp AbiReg.t1
          (slotOff (nlocals + tmp)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
        simp only [farTotalWords_append]; omega

private theorem compileC_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab) (nlocals tmp : Nat)
    (hnl : nlocals < 100000) (pfx : String) :
    ∀ (c : Cond) (lblId : Nat) (want : Bool) (target : String),
      tmp + maxTempsCond c < 100000 →
      condOkConst0B tab nlocals c = true →
      farTotalWords (compileC tab nlocals tmp pfx lblId c want target).1 ≤ condBound32 c := by
  intro c
  induction c with
  | cmp op a b =>
    intro lblId want target htmp hok
    simp only [maxTempsCond] at htmp
    simp only [condOkConst0B, Bool.and_eq_true] at hok
    dsimp only [compileC, condBound32]
    split
    · rw [farTotalWords_append, brCmp_farTotalWords]
      have ha := compileE_farTotalWords_le ht nlocals hnl a tmp (by omega) hok.1
      omega
    · split
      · rw [farTotalWords_append, brCmp_farTotalWords]
        have hb := compileE_farTotalWords_le ht nlocals hnl b tmp (by omega) hok.2
        omega
      · cases hsb : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 b with
        | some cb =>
          simp only [farTotalWords_append, brCmp_farTotalWords]
          have ha := compileE_farTotalWords_le ht nlocals hnl a tmp (by omega) hok.1
          have hb := emitSimpleExpr_farTotalWords_le ht hnl hok.2 hsb
          omega
        | none =>
          cases hsa : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 a with
          | some ca =>
            simp only [farTotalWords_append, brCmp_farTotalWords]
            have hb := compileE_farTotalWords_le ht nlocals hnl b tmp (by omega) hok.2
            have ha := emitSimpleExpr_farTotalWords_le ht hnl hok.1 hsa
            omega
          | none =>
            have ha := compileE_farTotalWords_le ht nlocals hnl a tmp (by omega) hok.1
            have hb := compileE_farTotalWords_le ht nlocals hnl b (tmp + 1) (by omega) hok.2
            have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
              (slotOff (nlocals + tmp)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
            have hld := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.sp AbiReg.t1
              (slotOff (nlocals + tmp)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
            simp only [farTotalWords_append, brCmp_farTotalWords]
            omega
  | not p ih =>
    intro lblId want target htmp hok
    exact ih lblId (!want) target htmp hok
  | and p q ihp ihq =>
    intro lblId want target htmp hok
    simp only [maxTempsCond] at htmp
    simp only [condOkConst0B, Bool.and_eq_true] at hok
    dsimp only [compileC, condBound32]
    cases want
    · simp only [Bool.false_eq_true, ↓reduceIte, farTotalWords_append]
      have hp := ihp lblId false target (by omega) hok.1
      have hq := ihq (compileC tab nlocals tmp pfx lblId p false target).2 false target (by omega) hok.2
      omega
    · simp only [↓reduceIte, farTotalWords_append]
      let skipLbl := toString pfx ++ toString "_and_" ++ toString lblId
      have hp := ihp (lblId + 1) false skipLbl (by omega) hok.1
      have hq := ihq (compileC tab nlocals tmp pfx (lblId + 1) p false skipLbl).2 true target (by omega) hok.2
      have hlbl : farTotalWords [Asm.lbl skipLbl] = 0 := rfl
      dsimp only [skipLbl] at hp hq hlbl
      omega
  | or p q ihp ihq =>
    intro lblId want target htmp hok
    simp only [maxTempsCond] at htmp
    simp only [condOkConst0B, Bool.and_eq_true] at hok
    dsimp only [compileC, condBound32]
    cases want
    · simp only [Bool.false_eq_true, ↓reduceIte, farTotalWords_append]
      let skipLbl := toString pfx ++ toString "_or_" ++ toString lblId
      have hp := ihp (lblId + 1) true skipLbl (by omega) hok.1
      have hq := ihq (compileC tab nlocals tmp pfx (lblId + 1) p true skipLbl).2 false target (by omega) hok.2
      have hlbl : farTotalWords [Asm.lbl skipLbl] = 0 := rfl
      dsimp only [skipLbl] at hp hq hlbl
      omega
    · simp only [↓reduceIte, farTotalWords_append]
      have hp := ihp lblId true target (by omega) hok.1
      have hq := ihq (compileC tab nlocals tmp pfx lblId p true target).2 true target (by omega) hok.2
      omega

-- Clean maxTempsExprs bound:
private theorem foldl_max_ge_init (xs : List (Expr × Nat)) (acc : Nat) :
    acc ≤ xs.foldl (fun a (p : Expr × Nat) => max a (p.2 + max 1 (maxTempsExpr p.1))) acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons p xs ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem foldl_max_zipIdx (es : List Expr) (k init : Nat) :
    ∀ (e : Expr) (i : Nat), (e, i) ∈ es.zipIdx k →
      i + max 1 (maxTempsExpr e) ≤
        (es.zipIdx k).foldl (fun a (p : Expr × Nat) => max a (p.2 + max 1 (maxTempsExpr p.1))) init := by
  induction es generalizing k init with
  | nil => intro e i hm; simp at hm
  | cons x xs ih =>
    intro e i hm
    simp only [List.zipIdx_cons, List.mem_cons, Prod.mk.injEq] at hm
    simp only [List.zipIdx_cons, List.foldl_cons]
    rcases hm with ⟨rfl, rfl⟩ | hm'
    · exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_ge_init _ _)
    · exact ih (k + 1) _ e i hm'

private theorem compileEvalExprsToTemps_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab)
    (nlocals : Nat) (hnl : nlocals < 100000) :
    ∀ (es : List Expr) (tmp : Nat),
      tmp + maxTempsExprs es < 100000 →
      es.all (exprOkConst0B tab nlocals) = true →
      farTotalWords (compileEvalExprsToTemps tab nlocals tmp es) ≤ exprsBound32 es := by
  intro es tmp htmp hok
  induction es generalizing tmp with
  | nil => simp [compileEvalExprsToTemps, farTotalWords]
  | cons e es ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hok
    have he_lt : tmp + maxTempsExpr e < 100000 := by
      have hm := foldl_max_zipIdx (e :: es) 0 0 e 0 (by simp)
      dsimp only [maxTempsExprs] at htmp
      omega
    have hes_lt : (tmp + 1) + maxTempsExprs es < 100000 := by
      -- Every element in es.zipIdx 0 maps to (x, j + 1) in (e :: es).zipIdx 0!
      have hle : 1 + maxTempsExprs es ≤ maxTempsExprs (e :: es) := by
        dsimp only [maxTempsExprs]
        have hstep : ∀ (xs : List Expr) (k acc1 acc2 : Nat),
            acc1 + 1 ≤ acc2 →
            (xs.zipIdx k).foldl (fun a (p : Expr × Nat) => max a (p.2 + max 1 (maxTempsExpr p.1))) acc1 + 1 ≤
            (xs.zipIdx (k + 1)).foldl (fun a (p : Expr × Nat) => max a (p.2 + max 1 (maxTempsExpr p.1))) acc2 := by
          intro xs
          induction xs with
          | nil => intro k a1 a2 ha; simp [ha]
          | cons y ys ihy =>
            intro k a1 a2 ha
            simp only [List.zipIdx_cons, List.foldl_cons]
            exact ihy (k + 1) _ _ (by omega)
        have h0 := hstep es 0 0 (max 0 (0 + max 1 (maxTempsExpr e))) (by omega)
        simpa [List.zipIdx_cons, List.foldl_cons, Nat.add_comm] using h0
      omega
    have he := compileE_farTotalWords_le ht nlocals hnl e tmp he_lt hok.1
    have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
      (slotOff (nlocals + tmp)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    have hst0 := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.zero AbiReg.t0
      (slotOff (nlocals + tmp)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    have hes := ih (tmp + 1) hes_lt hok.2
    dsimp only [compileEvalExprsToTemps, exprsBound32]
    rw [farTotalWords_append]
    split
    · omega
    · rw [farTotalWords_append]; omega

private theorem copyTempsToResults_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab)
    (nlocals tmp count : Nat) (hnt : nlocals + tmp + tab.nres < 200000) :
    farTotalWords (copyTempsToResults tab nlocals tmp count) ≤ 12 * tab.nres := by
  have ⟨_, _, _, _, _, hres, _⟩ := tab_offsets_32 ht
  dsimp only [copyTempsToResults]
  split
  · split
    · have h1 : farTotalWords [Asm.addi AbiReg.a0 AbiReg.zero 0#12] = 1 := rfl
      omega
    · simp [farTotalWords]
  · refine Nat.le_trans (farTotalWords_flatMap_le _ _ (fun _ => 12) (fun i hi => ?_)) ?_
    · simp only [List.mem_range] at hi
      have hiN : i < tab.nres := Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)
      have hres_i := hres i hiN
      have hslot : 0 ≤ slotOff (nlocals + tmp + i) ∧ slotOff (nlocals + tmp + i) < 2 ^ 31 := by
        dsimp [slotOff]; omega
      split
      · have hl := loadMemOff_farTotalWords_le_32 .ld (resReg i) AbiReg.sp AbiReg.t0
          (slotOff (nlocals + tmp + i)) hslot.1 hslot.2
        omega
      · simp only [farTotalWords_append]
        have hl := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.sp AbiReg.t2
          (slotOff (nlocals + tmp + i)) hslot.1 hslot.2
        have hs := storeMemOff_farTotalWords_le_32 .sd AbiReg.gp AbiReg.t1 AbiReg.t2
          (tab.resOff i) hres_i.1 hres_i.2
        omega
    · have hsum : ∀ (xs : List Nat) (acc : Nat),
          xs.foldl (fun a _ => a + 12) acc = acc + 12 * xs.length := by
        intro xs; induction xs with | nil => simp | cons x xs ih => intro acc; simp [ih]; omega
      rw [hsum, Nat.zero_add, List.length_range]
      exact Nat.mul_le_mul_left 12 (Nat.min_le_right count tab.nres)

private theorem copyTempsToResults_zero_farTotalWords_le (tab : Tab)
    (nlocals tmp : Nat) :
    farTotalWords (copyTempsToResults tab nlocals tmp 0) ≤ 1 := by
  dsimp only [copyTempsToResults]
  simp only [beq_self_eq_true, ↓reduceIte]
  split
  · decide
  · simp [farTotalWords]

private theorem unrollCopyParams_farTotalWords_le (n : Nat) (hn : n < 100000) :
    farTotalWords (unrollCopyParams n) ≤ 12 * n := by
  dsimp only [unrollCopyParams]
  refine Nat.le_trans (farTotalWords_flatMap_le _ _ (fun _ => 12) (fun i hi => ?_)) ?_
  · simp only [List.mem_range] at hi
    simp only [farTotalWords_append]
    have h1 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t4 AbiReg.t0 AbiReg.t2
      (8 * (i : Int)) (by omega) (by omega)
    have h2 := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.t4 AbiReg.t2
      (slotOff i) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    change farTotalWords (loadMemOff .ld AbiReg.t4 AbiReg.t0 AbiReg.t2 (8 * (i : Int))) +
      farTotalWords (storeMemOff .sd AbiReg.sp AbiReg.t4 AbiReg.t2 (slotOff i)) ≤ 12
    omega
  · have hsum : ∀ (xs : List Nat) (acc : Nat), xs.foldl (fun a _ => a + 12) acc = acc + 12 * xs.length := by
      intro xs; induction xs with | nil => simp | cons x xs ih => intro acc; simp [ih]; omega
    rw [hsum, Nat.zero_add, List.length_range]; exact Nat.le_refl _

private theorem unrollZeroLocals_farTotalWords_le (lo count : Nat) (hlc : lo + count < 100000) :
    farTotalWords (unrollZeroLocals lo count) ≤ 6 * count := by
  dsimp only [unrollZeroLocals]
  refine Nat.le_trans (farTotalWords_flatMap_le _ _ (fun _ => 6) (fun i hi => ?_)) ?_
  · simp only [List.mem_range] at hi
    exact storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.zero AbiReg.t2
      (slotOff (lo + i)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
  · have hsum : ∀ (xs : List Nat) (acc : Nat), xs.foldl (fun a _ => a + 6) acc = acc + 6 * xs.length := by
      intro xs; induction xs with | nil => simp | cons x xs ih => intro acc; simp [ih]; omega
    rw [hsum, Nat.zero_add, List.length_range]; exact Nat.le_refl _

private theorem copyResultsToLocals_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab)
    (nlocals : Nat) (hnl : nlocals < 100000) (xs : List Var) (hxs : ∀ x ∈ xs, x < nlocals) :
    farTotalWords (copyResultsToLocals tab xs) ≤ 12 * xs.length := by
  have ⟨_, _, _, _, _, hres, _⟩ := tab_offsets_32 ht
  dsimp only [copyResultsToLocals]
  have hmem : ∀ {ys : List Var} {k : Nat} {x i : Nat},
      (x, i) ∈ ys.zipIdx k → x ∈ ys := by
    intro ys
    induction ys with
    | nil => intro k x i hm; simp at hm
    | cons y ys ih =>
      intro k x i hm
      simp only [List.zipIdx_cons, List.mem_cons, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | hm'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem y (ih hm')
  refine Nat.le_trans (farTotalWords_flatMap_le _ _ (fun _ => 12) (fun p hm => ?_)) ?_
  · obtain ⟨x, i⟩ := p
    dsimp only
    have hx_lt : x < nlocals := hxs x (hmem hm)
    have hslot := slotOff_32 (Nat.lt_trans hx_lt hnl)
    split
    · next hi =>
      have hres_i := hres i hi
      split
      · have hs := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp (resReg i) AbiReg.t0
          (slotOff x) hslot.1 hslot.2
        omega
      · simp only [farTotalWords_append]
        have hl := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.gp AbiReg.t2
          (tab.resOff i) hres_i.1 hres_i.2
        have hs := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.t1 AbiReg.t2
          (slotOff x) hslot.1 hslot.2
        omega
    · have hs := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.zero AbiReg.t0
        (slotOff x) hslot.1 hslot.2
      omega
  · have hsum : ∀ (ps : List (Var × Nat)) (acc : Nat),
        ps.foldl (fun a _ => a + 12) acc = acc + 12 * ps.length := by
      intro ps; induction ps with | nil => simp | cons p ps ih => intro acc; simp [ih]; omega
    rw [hsum, Nat.zero_add, List.length_zipIdx]; exact Nat.le_refl _

private theorem compileStorePair_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab)
    (nlocals : Nat) (hnl : nlocals < 100000) (i e : Expr)
    (hi_tmp : maxTempsExpr i < 100000) (he_tmp : 1 + maxTempsExpr e < 100000)
    (hi_ok : exprOkConst0B tab nlocals i = true) (he_ok : exprOkConst0B tab nlocals e = true) :
    farTotalWords (compileStorePair tab nlocals i e) ≤ exprBound32 i + exprBound32 e + 12 := by
  dsimp only [compileStorePair]
  cases hsi : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 i with
  | some ci =>
    rw [farTotalWords_append]
    have he := compileE_farTotalWords_le ht nlocals hnl e 0 (by omega) he_ok
    have hi := emitSimpleExpr_farTotalWords_le ht hnl hi_ok hsi
    omega
  | none =>
    cases hse : emitSimpleExpr tab AbiReg.a0 AbiReg.t1 e with
    | some ce =>
      simp only [farTotalWords_append]
      have hi := compileE_farTotalWords_le ht nlocals hnl i 0 (by omega) hi_ok
      have he := emitSimpleExpr_farTotalWords_le ht hnl he_ok hse
      have hmv : farTotalWords [Asm.mv AbiReg.t0 AbiReg.a0] = 1 := rfl
      omega
    | none =>
      have hi := compileE_farTotalWords_le ht nlocals hnl i 0 (by omega) hi_ok
      have he := compileE_farTotalWords_le ht nlocals hnl e 1 (by omega) he_ok
      have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
        (slotOff nlocals) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
      have hld := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.sp AbiReg.t1
        (slotOff nlocals) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
      simp only [farTotalWords_append]; omega

private theorem compileTierStoreTriple_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab)
    (nlocals : Nat) (hnl : nlocals < 100000) (t i e : Expr)
    (ht_tmp : maxTempsExpr t < 100000) (hi_tmp : 1 + maxTempsExpr i < 100000)
    (he_tmp : 2 + maxTempsExpr e < 100000)
    (ht_ok : exprOkConst0B tab nlocals t = true)
    (hi_ok : exprOkConst0B tab nlocals i = true)
    (he_ok : exprOkConst0B tab nlocals e = true) :
    farTotalWords (compileTierStoreTriple tab nlocals t i e) ≤
      exprBound32 t + exprBound32 i + exprBound32 e + 24 := by
  dsimp only [compileTierStoreTriple]
  cases hst : emitSimpleExpr tab AbiReg.t0 AbiReg.t1 t with
  | some ct =>
    have ht' := emitSimpleExpr_farTotalWords_le ht hnl ht_ok hst
    cases hsi : emitSimpleExpr tab AbiReg.t3 AbiReg.t4 i with
    | some ci =>
      have he := compileE_farTotalWords_le ht nlocals hnl e 0 (by omega) he_ok
      have hi := emitSimpleExpr_farTotalWords_le ht hnl hi_ok hsi
      simp only [farTotalWords_append]; omega
    | none =>
      cases hse : emitSimpleExpr tab AbiReg.a0 AbiReg.t4 e with
      | some ce =>
        have hi := compileE_farTotalWords_le ht nlocals hnl i 0 (by omega) hi_ok
        have he := emitSimpleExpr_farTotalWords_le ht hnl he_ok hse
        have hmv : farTotalWords [Asm.mv AbiReg.t3 AbiReg.a0] = 1 := rfl
        simp only [farTotalWords_append]; omega
      | none =>
        have hi := compileE_farTotalWords_le ht nlocals hnl i 0 (by omega) hi_ok
        have he := compileE_farTotalWords_le ht nlocals hnl e 1 (by omega) he_ok
        have hs0 := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
          (slotOff nlocals) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
        have hl0 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t3 AbiReg.sp AbiReg.t1
          (slotOff nlocals) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
        simp only [farTotalWords_append]; omega
  | none =>
    have ht0 := compileE_farTotalWords_le ht nlocals hnl t 0 (by omega) ht_ok
    have hi := compileE_farTotalWords_le ht nlocals hnl i 1 (by omega) hi_ok
    have he := compileE_farTotalWords_le ht nlocals hnl e 2 (by omega) he_ok
    have hs0 := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
      (slotOff nlocals) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    have hs1 := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
      (slotOff (nlocals + 1)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    have hl0 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.sp AbiReg.t1
      (slotOff nlocals) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    have hl1 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t3 AbiReg.sp AbiReg.t1
      (slotOff (nlocals + 1)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    simp only [farTotalWords_append]; omega

private theorem compileS_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab)
    (nlocals : Nat) (hnl : nlocals < 100000) (pfx retLbl : String) :
    ∀ (s : Stmt) (inLoop : Bool) (lblId : Nat) (brkLbl : Option String) (p : Prog),
      maxTempsStmt s + nlocals < 100000 →
      stmtOkConst0B tab p nlocals inLoop s = true →
      farTotalWords (compileS tab nlocals pfx lblId brkLbl retLbl s).1 ≤ stmtBound32 tab.nres s := by
  intro s
  have ⟨hlen8, hbase8, hlen64, hbase64, hglob, _, hrom⟩ := tab_offsets_32 ht
  induction s with
  | skip => intro _ _ _ _ _ _; exact Nat.le_refl _
  | set x e =>
    intro _ _ _ _ htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true, decide_eq_true_eq] at hok
    have hslot := slotOff_32 (Nat.lt_trans hok.1 hnl)
    dsimp only [compileS, stmtBound32]
    split
    · have hst0 := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.zero AbiReg.t0
        (slotOff x) hslot.1 hslot.2
      omega
    · have he := compileE_farTotalWords_le ht nlocals hnl e 0 (by omega) hok.2
      have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
        (slotOff x) hslot.1 hslot.2
      rw [farTotalWords_append]; omega
  | gset g e =>
    intro _ _ _ _ htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true, decide_eq_true_eq] at hok
    dsimp only [compileS, stmtBound32]
    split
    · have hst0 := storeMemOff_farTotalWords_le_32 .sd AbiReg.gp AbiReg.zero AbiReg.t0
        (tab.globOff g) (hglob g hok.1).1 (hglob g hok.1).2
      omega
    · have he := compileE_farTotalWords_le ht nlocals hnl e 0 (by omega) hok.2
      have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.gp AbiReg.a0 AbiReg.t0
        (tab.globOff g) (hglob g hok.1).1 (hglob g hok.1).2
      rw [farTotalWords_append]; omega
  | st8 _ _ _ => intro _ _ _ _ _ _; exact Nat.le_refl _
  | st64 a i e =>
    intro _ _ _ _ htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true] at hok
    have hp := compileStorePair_farTotalWords_le ht nlocals hnl i e
      (by omega) (by omega) hok.1.2 hok.2
    have hl1 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.gp AbiReg.t2
      (tab.len64 (TieredArray.t0 a)) (hlen64 _).1 (hlen64 _).2
    have hl2 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.gp AbiReg.t2
      (tab.base64 (TieredArray.t0 a)) (hbase64 _).1 (hbase64 _).2
    have hbr : farTotalWords [Asm.bgeu AbiReg.t0 AbiReg.t1 errLabel] = 5 := rfl
    have htail : farTotalWords [Asm.slli AbiReg.t2 AbiReg.t0 3#6,
        Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t2, Asm.sd AbiReg.t1 AbiReg.a0 0#12] = 3 := rfl
    simp only [compileS, farTotalWords_append, stmtBound32]; omega
  | st64t a t i e =>
    intro _ _ _ _ htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true] at hok
    have htr := compileTierStoreTriple_farTotalWords_le ht nlocals hnl t i e
      (by omega) (by omega) (by omega) hok.1.1.2 hok.1.2 hok.2
    have hl2 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t2 AbiReg.t1 AbiReg.t4
      (tab.len64 (TieredArray.t0 a)) (hlen64 _).1 (hlen64 _).2
    have hl3 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.t1 AbiReg.t4
      (tab.base64 (TieredArray.t0 a)) (hbase64 _).1 (hbase64 _).2
    have h1 : farTotalWords [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
        Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] = 3 := rfl
    have h2 : farTotalWords [Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] = 5 := rfl
    have h3 : farTotalWords [Asm.slli AbiReg.t4 AbiReg.t3 3#6,
        Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4, Asm.sd AbiReg.t1 AbiReg.a0 0#12] = 3 := rfl
    simp only [compileS, farTotalWords_append, stmtBound32]; omega
  | st32t a t i e =>
    intro _ _ _ _ htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true] at hok
    have htr := compileTierStoreTriple_farTotalWords_le ht nlocals hnl t i e
      (by omega) (by omega) (by omega) hok.1.1.2 hok.1.2 hok.2
    have hl2 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t2 AbiReg.t1 AbiReg.t4
      (tab.len64 (TieredArray.t0 a)) (hlen64 _).1 (hlen64 _).2
    have hl3 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.t1 AbiReg.t4
      (tab.base64 (TieredArray.t0 a)) (hbase64 _).1 (hbase64 _).2
    have h1 : farTotalWords [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
        Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] = 3 := rfl
    have h2 : farTotalWords [Asm.srli AbiReg.t4 AbiReg.t3 1#6, Asm.bgeu AbiReg.t4 AbiReg.t2 errLabel] = 6 := rfl
    have h3 : farTotalWords [Asm.slli AbiReg.t4 AbiReg.t3 2#6,
        Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t4, Asm.sw AbiReg.t1 AbiReg.a0 0#12] = 3 := rfl
    simp only [compileS, farTotalWords_append, stmtBound32]; omega
  | seq s1 s2 ih1 ih2 =>
    intro inLoop lblId brkLbl p htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true] at hok
    have h1 := ih1 inLoop lblId brkLbl p (by omega) hok.1
    have h2 := ih2 inLoop (compileS tab nlocals pfx lblId brkLbl retLbl s1).2 brkLbl p (by omega) hok.2
    simp only [compileS, farTotalWords_append, stmtBound32]; omega
  | ite cond s1 s2 ih1 ih2 =>
    intro inLoop lblId brkLbl p htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true] at hok
    by_cases hs2 : s2 = .skip
    · subst hs2
      let endLbl := toString pfx ++ toString "_endif_" ++ toString lblId
      let id1 := (compileC tab nlocals 0 pfx (lblId + 1) cond false endLbl).2
      have hc := compileC_farTotalWords_le ht nlocals 0 hnl pfx cond (lblId + 1) false endLbl (by omega) hok.1.1
      have h1 := ih1 inLoop id1 brkLbl p (by omega) hok.1.2
      have he : farTotalWords [Asm.lbl endLbl] = 0 := rfl
      dsimp only [endLbl, id1] at hc h1 he
      simp only [compileS, farTotalWords_append, stmtBound32]; omega
    by_cases hs1 : s1 = .skip
    · subst hs1
      have hce : (compileS tab nlocals pfx lblId brkLbl retLbl (.ite cond .skip s2)).1 =
          (compileC tab nlocals 0 pfx (lblId + 1) cond true (s!"{pfx}_endif_{lblId}")).1 ++
          (compileS tab nlocals pfx (compileC tab nlocals 0 pfx (lblId + 1) cond true (s!"{pfx}_endif_{lblId}")).2 brkLbl retLbl s2).1 ++
          [Asm.lbl s!"{pfx}_endif_{lblId}"] := by cases s2 with | skip => contradiction | _ => rfl
      rw [hce]
      have hc := compileC_farTotalWords_le ht nlocals 0 hnl pfx cond (lblId + 1) true s!"{pfx}_endif_{lblId}" (by omega) hok.1.1
      have h2 := ih2 inLoop (compileC tab nlocals 0 pfx (lblId + 1) cond true s!"{pfx}_endif_{lblId}").2 brkLbl p (by omega) hok.2
      have he : farTotalWords [Asm.lbl s!"{pfx}_endif_{lblId}"] = 0 := rfl
      simp only [farTotalWords_append, stmtBound32]; omega
    have hceGen : (compileS tab nlocals pfx lblId brkLbl retLbl (.ite cond s1 s2)).1 =
        (compileC tab nlocals 0 pfx (lblId + 1) cond false (s!"{pfx}_else_{lblId}")).1 ++
        (compileS tab nlocals pfx (compileC tab nlocals 0 pfx (lblId + 1) cond false (s!"{pfx}_else_{lblId}")).2 brkLbl retLbl s1).1 ++
        [Asm.j s!"{pfx}_endif_{lblId}", Asm.lbl s!"{pfx}_else_{lblId}"] ++
        (compileS tab nlocals pfx (compileS tab nlocals pfx (compileC tab nlocals 0 pfx (lblId + 1) cond false (s!"{pfx}_else_{lblId}")).2 brkLbl retLbl s1).2 brkLbl retLbl s2).1 ++
        [Asm.lbl s!"{pfx}_endif_{lblId}"] := by
      cases s2 with | skip => contradiction | _ => cases s1 with | skip => contradiction | _ => rfl
    rw [hceGen]
    have hc := compileC_farTotalWords_le ht nlocals 0 hnl pfx cond (lblId + 1) false s!"{pfx}_else_{lblId}" (by omega) hok.1.1
    have h1 := ih1 inLoop (compileC tab nlocals 0 pfx (lblId + 1) cond false s!"{pfx}_else_{lblId}").2 brkLbl p (by omega) hok.1.2
    have h2 := ih2 inLoop (compileS tab nlocals pfx (compileC tab nlocals 0 pfx (lblId + 1) cond false s!"{pfx}_else_{lblId}").2 brkLbl retLbl s1).2 brkLbl p (by omega) hok.2
    have hj : farTotalWords [Asm.j s!"{pfx}_endif_{lblId}", Asm.lbl s!"{pfx}_else_{lblId}"] = 4 := rfl
    have he : farTotalWords [Asm.lbl s!"{pfx}_endif_{lblId}"] = 0 := rfl
    simp only [farTotalWords_append, stmtBound32]; omega
  | «while» cond body ih =>
    intro _ lblId _ p htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true] at hok
    let loopLbl := toString pfx ++ toString "_while_" ++ toString lblId
    let endLbl := toString pfx ++ toString "_endw_" ++ toString lblId
    let id1 := (compileC tab nlocals 0 pfx (lblId + 1) cond false endLbl).2
    have hc := compileC_farTotalWords_le ht nlocals 0 hnl pfx cond (lblId + 1) false endLbl (by omega) hok.1
    have hb := ih true id1 (some endLbl) p (by omega) hok.2
    have h1 : farTotalWords [Asm.lbl loopLbl] = 0 := rfl
    have h2 : farTotalWords [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
        Asm.addi AbiReg.s0 AbiReg.s0 (-1#12), Asm.j loopLbl,
        Asm.lbl endLbl] = 10 := rfl
    dsimp only [loopLbl, endLbl, id1] at hc hb h1 h2
    simp only [compileS, farTotalWords_append, stmtBound32]; omega
  | brk =>
    intro _ _ brkLbl _ _ _
    have hj : farTotalWords [Asm.j (brkLbl.getD retLbl)] = 4 := rfl
    dsimp only [compileS, stmtBound32]
    exact Nat.le_trans (Nat.le_of_eq hj) (by omega)
  | ret es =>
    intro _ _ _ _ htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true, decide_eq_true_eq] at hok
    have hj : farTotalWords [Asm.j retLbl] = 4 := rfl
    cases es with
    | nil =>
      have hes := compileEvalExprsToTemps_farTotalWords_le ht nlocals hnl [] 0 (by omega) hok.2
      have hcopy := copyTempsToResults_farTotalWords_le ht nlocals 0 0 (by have := ht.nres_le; omega)
      simp only [compileS, List.length_nil, farTotalWords_append, stmtBound32]; omega
    | cons e rest =>
      cases rest with
      | nil =>
        simp only [List.all_cons, List.all_nil, Bool.and_true] at hok
        have he_lt : 0 + maxTempsExpr e < 100000 := by
          simp only [maxTempsExprs, List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil] at htmp; omega
        have he := compileE_farTotalWords_le ht nlocals hnl e 0 he_lt hok.2
        simp only [compileS, farTotalWords_append, stmtBound32, exprsBound32]; omega
      | cons e2 rs =>
        have hes := compileEvalExprsToTemps_farTotalWords_le ht nlocals hnl (e :: e2 :: rs) 0 (by omega) hok.2
        have hcopy := copyTempsToResults_farTotalWords_le ht nlocals 0 (e :: e2 :: rs).length (by have := ht.nres_le; omega)
        simp only [compileS, farTotalWords_append, stmtBound32]; omega
  | «call» xs f args =>
    intro _ _ _ _ htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true] at hok
    have hargs := compileEvalExprsToTemps_farTotalWords_le ht nlocals hnl args 0 (by omega) hok.2
    have hxs : ∀ x ∈ xs, x < nlocals := fun x hx => by
      have := hok.1.2
      rw [List.all_eq_true] at this
      exact decide_eq_true_eq.mp (this x hx)
    have hcopy := copyResultsToLocals_farTotalWords_le ht nlocals hnl xs hxs
    have hbr : farTotalWords [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
        Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] = 6 := rfl
    have hptr : farTotalWords (if args.isEmpty then [] else addImmOff AbiReg.t0 AbiReg.sp AbiReg.t2 (slotOff nlocals)) ≤ 5 := by
      split
      · simp [farTotalWords]
      · exact addImmOff_farTotalWords_le_32 AbiReg.t0 AbiReg.sp AbiReg.t2
          (slotOff nlocals) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    have hcall : farTotalWords [Asm.call (fnLabel f)] = 4 := rfl
    simp only [compileS, farTotalWords_append, stmtBound32]; omega
  | abort e =>
    intro _ _ _ _ htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B] at hok
    have he := compileE_farTotalWords_le ht nlocals hnl e 0 (by omega) hok
    have hj : farTotalWords [Asm.j abortLabel] = 4 := rfl
    simp only [compileS, farTotalWords_append, stmtBound32]; omega
  | copy64 d di src si n =>
    intro _ lblId _ _ htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true] at hok
    have hd : farTotalWords (evalWArrTierToTemp tab nlocals 0 d).2 ≤ warrBound32 d := by
      cases d with
      | plain a =>
        dsimp only [evalWArrTierToTemp, warrBound32]
        have hslot0 := slotOff_32 (by omega : nlocals + 0 < 100000)
        exact storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.zero AbiReg.t0
          (slotOff (nlocals + 0)) hslot0.1 hslot0.2
      | tier a t =>
        dsimp only at htmp
        have hok_t : exprOkConst0B tab nlocals t = true := by
          have := hok.1.1.1.1; simp only [warrOkConst0B, Bool.and_eq_true] at this; exact this.2
        have het := compileE_farTotalWords_le ht nlocals hnl t 0 (by omega) hok_t
        have hslot0 := slotOff_32 (by omega : nlocals + 0 < 100000)
        have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
          (slotOff (nlocals + 0)) hslot0.1 hslot0.2
        simp only [evalWArrTierToTemp, farTotalWords_append, warrBound32]; omega
    have hdi := compileE_farTotalWords_le ht nlocals hnl di 1 (by omega) hok.1.1.1.2
    have hs : farTotalWords (evalWArrTierToTemp tab nlocals 2 src).2 ≤ warrBound32 src := by
      cases src with
      | plain a =>
        dsimp only [evalWArrTierToTemp, warrBound32]
        have hslot2 := slotOff_32 (by omega : nlocals + 2 < 100000)
        exact storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.zero AbiReg.t0
          (slotOff (nlocals + 2)) hslot2.1 hslot2.2
      | tier a t =>
        dsimp only at htmp
        have hok_t : exprOkConst0B tab nlocals t = true := by
          have := hok.1.1.2; simp only [warrOkConst0B, Bool.and_eq_true] at this; exact this.2
        have het := compileE_farTotalWords_le ht nlocals hnl t 2 (by omega) hok_t
        have hslot2 := slotOff_32 (by omega : nlocals + 2 < 100000)
        have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
          (slotOff (nlocals + 2)) hslot2.1 hslot2.2
        simp only [evalWArrTierToTemp, farTotalWords_append, warrBound32]; omega
    have hsi := compileE_farTotalWords_le ht nlocals hnl si 3 (by omega) hok.1.2
    have hn := compileE_farTotalWords_le ht nlocals hnl n 4 (by omega) hok.2
    have hs1 := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
      (slotOff (nlocals + 1)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    have hs3 := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
      (slotOff (nlocals + 3)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    have hs4 := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
      (slotOff (nlocals + 4)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    have hl0 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.sp AbiReg.t1
      (slotOff nlocals) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    have hl1 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.sp AbiReg.t6
      (slotOff (nlocals + 1)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    have hl4 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t3 AbiReg.sp AbiReg.t6
      (slotOff (nlocals + 4)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    have hl2 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.sp AbiReg.t2
      (slotOff (nlocals + 2)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    have hl3 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t2 AbiReg.sp AbiReg.t6
      (slotOff (nlocals + 3)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    have hdl := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.t5 AbiReg.t6
      (tab.len64 (TieredArray.t0 (evalWArrTierToTemp tab nlocals 0 d).1)) (hlen64 _).1 (hlen64 _).2
    have hdb := loadMemOff_farTotalWords_le_32 .ld AbiReg.t5 AbiReg.t5 AbiReg.t6
      (tab.base64 (TieredArray.t0 (evalWArrTierToTemp tab nlocals 0 d).1)) (hbase64 _).1 (hbase64 _).2
    have hsl := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.t5 AbiReg.t6
      (tab.len64 (TieredArray.t0 (evalWArrTierToTemp tab nlocals 2 src).1)) (hlen64 _).1 (hlen64 _).2
    have hsb := loadMemOff_farTotalWords_le_32 .ld AbiReg.t5 AbiReg.t5 AbiReg.t6
      (tab.base64 (TieredArray.t0 (evalWArrTierToTemp tab nlocals 2 src).1)) (hbase64 _).1 (hbase64 _).2
    have hm1 : farTotalWords [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
        Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] = 3 := rfl
    have hm2 : farTotalWords [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3,
        Asm.bltu AbiReg.t0 AbiReg.t1 errLabel] = 11 := rfl
    have hm3 : farTotalWords [Asm.slli AbiReg.t1 AbiReg.t1 3#6, Asm.add AbiReg.t1 AbiReg.t5 AbiReg.t1] = 2 := rfl
    have hm4 : farTotalWords [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
        Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] = 3 := rfl
    have hm5 : farTotalWords [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3,
        Asm.bltu AbiReg.t0 AbiReg.t2 errLabel] = 11 := rfl
    have hm6 : ∀ l1 l2, farTotalWords [Asm.slli AbiReg.t2 AbiReg.t2 3#6, Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2,
        Asm.lbl l1, Asm.beq AbiReg.t3 AbiReg.zero l2,
        Asm.ld AbiReg.t4 AbiReg.t2 0#12, Asm.sd AbiReg.t1 AbiReg.t4 0#12,
        Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 8#12,
        Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j l1, Asm.lbl l2] = 16 := fun _ _ => rfl
    simp only [compileS, farTotalWords_append, stmtBound32]
    rw [hm6 _ _]
    omega
  | copy8w d di src si n =>
    intro _ lblId _ _ htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true] at hok
    have hd : farTotalWords (evalWArrTierToTemp tab nlocals 0 d).2 ≤ warrBound32 d := by
      cases d with
      | plain a =>
        exact storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.zero AbiReg.t0
          (slotOff (nlocals + 0)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
      | tier a t =>
        dsimp only at htmp
        have hok_t : exprOkConst0B tab nlocals t = true := by
          have := hok.1.1.1.1
          simp only [warrOkConst0B, Bool.and_eq_true] at this
          exact this.2
        have het := compileE_farTotalWords_le ht nlocals hnl t 0 (by omega) hok_t
        have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
          (slotOff (nlocals + 0)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
        simp only [evalWArrTierToTemp, farTotalWords_append, warrBound32]; omega
    have hdi := compileE_farTotalWords_le ht nlocals hnl di 1 (by omega) hok.1.1.1.2
    have hsi := compileE_farTotalWords_le ht nlocals hnl si 3 (by omega) hok.1.2
    have hn := compileE_farTotalWords_le ht nlocals hnl n 4 (by omega) hok.2
    have hs1 := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
      (slotOff (nlocals + 1)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    have hs3 := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
      (slotOff (nlocals + 3)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    have hs4 := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
      (slotOff (nlocals + 4)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    have hl0 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.sp AbiReg.t1
      (slotOff nlocals) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    have hl1 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.sp AbiReg.t6
      (slotOff (nlocals + 1)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    have hl4 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t3 AbiReg.sp AbiReg.t6
      (slotOff (nlocals + 4)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    have hl3 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t2 AbiReg.sp AbiReg.t6
      (slotOff (nlocals + 3)) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    have hdl := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.t5 AbiReg.t6
      (tab.len64 (TieredArray.t0 (evalWArrTierToTemp tab nlocals 0 d).1)) (hlen64 _).1 (hlen64 _).2
    have hdb := loadMemOff_farTotalWords_le_32 .ld AbiReg.t5 AbiReg.t5 AbiReg.t6
      (tab.base64 (TieredArray.t0 (evalWArrTierToTemp tab nlocals 0 d).1)) (hbase64 _).1 (hbase64 _).2
    have hm1 : farTotalWords [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
        Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] = 3 := rfl
    have hm2 : farTotalWords [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3,
        Asm.bltu AbiReg.t0 AbiReg.t1 errLabel] = 11 := rfl
    have hm3 : farTotalWords [Asm.slli AbiReg.t1 AbiReg.t1 3#6, Asm.add AbiReg.t1 AbiReg.t5 AbiReg.t1] = 2 := rfl
    have hm4 : ∀ l1 l2, farTotalWords [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3,
        Asm.bltu AbiReg.t0 AbiReg.t2 errLabel, Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2,
        Asm.lbl l1, Asm.beq AbiReg.t3 AbiReg.zero l2,
        Asm.lbu AbiReg.t4 AbiReg.t2 0#12, Asm.sd AbiReg.t1 AbiReg.t4 0#12,
        Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 1#12,
        Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j l1, Asm.lbl l2] = 26 := fun _ _ => rfl
    simp only [compileS, farTotalWords_append, stmtBound32]
    rw [hm4 _ _]
    cases src with
    | arr a =>
      simp only [farTotalWords_append]
      have hla := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.gp AbiReg.t6 (tab.len8 a) (hlen8 a).1 (hlen8 a).2
      have hba := loadMemOff_farTotalWords_le_32 .ld AbiReg.t5 AbiReg.gp AbiReg.t6 (tab.base8 a) (hbase8 a).1 (hbase8 a).2
      omega
    | rom bs =>
      simp only [farTotalWords_append]
      have hli := li_farTotalWords_le AbiReg.t0 (BitVec.ofNat 64 bs.length)
      have hadd := addImmOff_farTotalWords_le_32 AbiReg.t5 AbiReg.gp AbiReg.t6
        (tab.romBase + (romIdx bs tab.rom : Int)) (hrom bs).1 (hrom bs).2
      omega
  | scan8 x src i e c =>
    intro _ lblId _ _ htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true, decide_eq_true_eq] at hok
    have hslot := slotOff_32 (Nat.lt_trans hok.1.1.1.1.1 hnl)
    have hi := compileE_farTotalWords_le ht nlocals hnl i 0 (by omega) hok.1.1.1.2
    have he := compileE_farTotalWords_le ht nlocals hnl e 1 (by omega) hok.1.1.2
    have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
      (slotOff nlocals) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    have hl3 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t3 AbiReg.sp AbiReg.t5
      (slotOff nlocals) (by dsimp [slotOff]; omega) (by dsimp [slotOff]; omega)
    have hbr : farTotalWords [Asm.bltu AbiReg.a0 AbiReg.t3 errLabel,
        Asm.bltu AbiReg.t0 AbiReg.a0 errLabel] = 10 := rfl
    have hromC := addImmOff_farTotalWords_le_32 AbiReg.t2 AbiReg.gp AbiReg.t5
      (tab.romBase + (romIdx c tab.rom : Int)) (hrom c).1 (hrom c).2
    have hloop : ∀ l1 l2, farTotalWords [Asm.lbl l1,
        Asm.bgeu AbiReg.t3 AbiReg.a0 l2,
        Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3, Asm.lbu AbiReg.t4 AbiReg.t4 0#12,
        Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4, Asm.lbu AbiReg.t5 AbiReg.t5 0#12,
        Asm.bne AbiReg.t5 AbiReg.zero l2,
        Asm.addi AbiReg.t3 AbiReg.t3 1#12, Asm.j l1, Asm.lbl l2] = 19 := fun _ _ => rfl
    have hsx := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.t3 AbiReg.t5
      (slotOff x) hslot.1 hslot.2
    simp only [compileS, farTotalWords_append, stmtBound32]
    rw [hloop _ _]
    cases src with
    | arr a =>
      simp only [farTotalWords_append]
      have hla := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.gp AbiReg.t5 (tab.len8 a) (hlen8 a).1 (hlen8 a).2
      have hba := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.gp AbiReg.t5 (tab.base8 a) (hbase8 a).1 (hbase8 a).2
      omega
    | rom bs =>
      simp only [farTotalWords_append]
      have hli := li_farTotalWords_le AbiReg.t0 (BitVec.ofNat 64 bs.length)
      have hadd := addImmOff_farTotalWords_le_32 AbiReg.t1 AbiReg.gp AbiReg.t5
        (tab.romBase + (romIdx bs tab.rom : Int)) (hrom bs).1 (hrom bs).2
      omega

private theorem varSlotOff_32 {fl : FrameLayout}
    (hfl : fl.protectedSlots ≤ 11 ∧ fl.spilledVars.length ≤ fl.nlocals)
    (hnl : fl.nlocals < 100000) (x : Var) :
    0 ≤ fl.varSlotOff x ∧ fl.varSlotOff x < 2 ^ 31 := by
  have hidx : fl.spilledVars.idxOf x ≤ fl.spilledVars.length := List.idxOf_le_length
  dsimp only [FrameLayout.varSlotOff, FrameLayout.spillIdx]
  omega

private theorem tempSlotOff_32 {fl : FrameLayout}
    (hfl : fl.protectedSlots ≤ 11 ∧ fl.spilledVars.length ≤ fl.nlocals)
    (hnl : fl.nlocals < 100000) {tmp : Nat} (htmp : tmp < 200000) :
    0 ≤ fl.tempSlotOff tmp ∧ fl.tempSlotOff tmp < 2 ^ 31 := by
  dsimp only [FrameLayout.tempSlotOff]
  omega

private theorem emitSimpleExprR_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab)
    {fl : FrameLayout} (hfl : fl.protectedSlots ≤ 11 ∧ fl.spilledVars.length ≤ fl.nlocals)
    (hnl : fl.nlocals < 100000) {rd tmp : Reg} {e : Expr} {cs : List AsmItem}
    (hok : exprOkConst0B tab fl.nlocals e = true)
    (h : emitSimpleExprR tab fl rd tmp e = some cs) :
    farTotalWords cs ≤ exprBound32 e := by
  obtain ⟨hlen8, _, hlen64, _, hglob, _, _⟩ := tab_offsets_32 ht
  cases e with
  | const w => cases h; exact li_farTotalWords_le rd _
  | var x =>
    dsimp only [emitSimpleExprR] at h
    split at h
    · next rx _ =>
      cases h
      dsimp only [exprBound32]
      split
      · simp [farTotalWords]
      · have hmv : farTotalWords [Asm.mv rd rx] = 1 := rfl; omega
    · cases h
      have hslot := varSlotOff_32 hfl hnl x
      exact loadMemOff_farTotalWords_le_32 .ld rd AbiReg.sp tmp (fl.varSlotOff x) hslot.1 hslot.2
  | len8 a =>
    cases h
    exact loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld rd tmp (tab.len8 a) (hlen8 a).1 (hlen8 a).2
  | len64 a =>
    cases h
    exact loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld rd tmp (tab.len64 (TieredArray.t0 a))
      (hlen64 (TieredArray.t0 a)).1 (hlen64 (TieredArray.t0 a)).2
  | glob g =>
    cases h
    simp only [exprOkConst0B, decide_eq_true_eq] at hok
    exact loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld rd tmp (tab.globOff g)
      (hglob g hok).1 (hglob g hok).2
  | bin _ _ _ | cmpw _ _ _ | ld8 _ _ | ld64 _ _ | ldc _ _ | ld64t _ _ _
  | len64t _ _ | ld8x8 _ _ | ld32t _ _ _ | ld32h _ _ _ _ => cases h

private theorem emitShrMaskFrom_farTotalWords_le (fl : FrameLayout) (rd : Reg) (inner : Expr)
    (lsh : Nat) (lm : BitVec 6) (compInner : Unit → List AsmItem)
    (hi : farTotalWords (compInner ()) ≤ exprBound32 inner) :
    farTotalWords (emitShrMaskFrom fl rd inner lsh lm compInner) ≤ exprBound32 inner + 2 := by
  dsimp only [emitShrMaskFrom]
  cases exprReg? fl.alloc inner with
  | some ri =>
    dsimp only
    have hs1 : farTotalWords (if (lsh == 0) = true then (if (rd == ri) = true then [] else [Asm.mv rd ri])
        else [Asm.slli rd ri (BitVec.ofNat 6 lsh)]) ≤ 1 := by
      split
      · split
        · simp [farTotalWords]
        · exact Nat.le_refl 1
      · exact Nat.le_refl 1
    have hs2 : farTotalWords [Asm.srli rd rd lm] = 1 := rfl
    simp only [farTotalWords_append, farTotalWords_nil]; omega
  | none =>
    dsimp only
    have hs1 : farTotalWords (if (lsh == 0) = true then (if (rd == AbiReg.a0) = true then [] else [Asm.mv rd AbiReg.a0])
        else [Asm.slli rd AbiReg.a0 (BitVec.ofNat 6 lsh)]) ≤ 1 := by
      split
      · split
        · simp [farTotalWords]
        · exact Nat.le_refl 1
      · exact Nat.le_refl 1
    have hs2 : farTotalWords [Asm.srli rd rd lm] = 1 := rfl
    simp only [farTotalWords_append]; omega

private theorem emitLd32hPlainFrom_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab)
    (fl : FrameLayout) (rd : Reg) (a : ArrId) (i : Expr) (hi : Bool)
    (compI0 : Unit → List AsmItem)
    (hcomp : farTotalWords (compI0 ()) ≤ exprBound32 i) :
    farTotalWords (emitLd32hPlainFrom tab fl rd a i hi compI0) ≤ exprBound32 i + 20 := by
  obtain ⟨_, _, hlen64, hbase64, _, _, _⟩ := tab_offsets_32 ht
  have hl1 := loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld AbiReg.t0 AbiReg.t1
    (tab.len64 (TieredArray.t0 a)) (hlen64 _).1 (hlen64 _).2
  have hl2 := loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld AbiReg.t1 AbiReg.t2
    (tab.base64 (TieredArray.t0 a)) (hbase64 _).1 (hbase64 _).2
  dsimp only [emitLd32hPlainFrom]
  cases exprReg? fl.alloc i with
  | some ri =>
    dsimp only
    have h1 : farTotalWords [Asm.bgeu ri AbiReg.t0 errLabel] = 5 := rfl
    have h2 := ld32hTail_farTotalWords_le rd ri AbiReg.t2 i hi
    simp only [farTotalWords_append, farTotalWords_nil]; omega
  | none =>
    dsimp only
    have h1 : farTotalWords [Asm.bgeu AbiReg.a0 AbiReg.t0 errLabel] = 5 := rfl
    have h2 := ld32hTail_farTotalWords_le rd AbiReg.a0 AbiReg.t2 i hi
    simp only [farTotalWords_append]; omega

private theorem emitLd32hFrom_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab)
    (fl : FrameLayout) (hfl : fl.protectedSlots ≤ 11 ∧ fl.spilledVars.length ≤ fl.nlocals)
    (hnl : fl.nlocals < 100000) (tmp : Nat) (htmp : tmp < 200000) (rd : Reg) (a : ArrId)
    (t i : Expr) (hi : Bool) (hokt : exprOkConst0B tab fl.nlocals t = true)
    (compI0 compT0 compI1 : Unit → List AsmItem)
    (hi0 : farTotalWords (compI0 ()) ≤ exprBound32 i)
    (ht0 : farTotalWords (compT0 ()) ≤ exprBound32 t)
    (hi1 : farTotalWords (compI1 ()) ≤ exprBound32 i) :
    farTotalWords (emitLd32hFrom tab fl tmp rd a t i hi compI0 compT0 compI1) ≤
      exprBound32 t + exprBound32 i + 35 := by
  obtain ⟨_, _, hlen64, hbase64, _, _, _⟩ := tab_offsets_32 ht
  dsimp only [emitLd32hFrom]
  cases t.constVal? with
  | some w =>
    dsimp only
    have hl1 := loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld AbiReg.t2 AbiReg.t3
      (tab.len64 (tierA a w)) (hlen64 _).1 (hlen64 _).2
    have hl2 := loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld AbiReg.t1 AbiReg.t3
      (tab.base64 (tierA a w)) (hbase64 _).1 (hbase64 _).2
    cases exprReg? fl.alloc i with
    | some ri =>
      dsimp only
      have h2 : farTotalWords [Asm.bgeu ri AbiReg.t2 errLabel] = 5 := rfl
      have h3 := ld32hTail_farTotalWords_le rd ri AbiReg.t3 i hi
      simp only [farTotalWords_append, farTotalWords_nil]; omega
    | none =>
      dsimp only
      have h2 : farTotalWords [Asm.bgeu AbiReg.a0 AbiReg.t2 errLabel] = 5 := rfl
      have h3 := ld32hTail_farTotalWords_le rd AbiReg.a0 AbiReg.t3 i hi
      simp only [farTotalWords_append]; omega
  | none =>
    have hl1 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t2 AbiReg.t1 AbiReg.t3
      (tab.len64 (TieredArray.t0 a)) (hlen64 _).1 (hlen64 _).2
    have hl2 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.t1 AbiReg.t3
      (tab.base64 (TieredArray.t0 a)) (hbase64 _).1 (hbase64 _).2
    have htail : ∀ (head : List AsmItem) (rt ri : Reg),
        farTotalWords head ≤ exprBound32 t + exprBound32 i + 12 →
        farTotalWords (head ++
          [Asm.andi AbiReg.t0 rt 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
           Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
          loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (tab.len64 (TieredArray.t0 a)) ++
          [Asm.bgeu ri AbiReg.t2 errLabel] ++
          loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t3 (tab.base64 (TieredArray.t0 a)) ++
          ld32hTail rd ri AbiReg.t3 i hi) ≤ exprBound32 t + exprBound32 i + 35 := by
      intro head rt ri hh
      have h1 : farTotalWords [Asm.andi AbiReg.t0 rt 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
          Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] = 3 := rfl
      have h2 : farTotalWords [Asm.bgeu ri AbiReg.t2 errLabel] = 5 := rfl
      have h3 := ld32hTail_farTotalWords_le rd ri AbiReg.t3 i hi
      simp only [farTotalWords_append]; omega
    cases exprReg? fl.alloc t with
    | some rt =>
      cases exprReg? fl.alloc i with
      | some ri => exact htail [] rt ri (by simp [farTotalWords])
      | none => exact htail _ rt AbiReg.a0 (by dsimp only; omega)
    | none =>
      cases hst : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 t with
      | some ct =>
        have ht'' := emitSimpleExprR_farTotalWords_le ht hfl hnl hokt hst
        cases exprReg? fl.alloc i with
        | some ri => exact htail ct AbiReg.t0 ri (by omega)
        | none => exact htail _ AbiReg.t0 AbiReg.a0 (by dsimp only; rw [farTotalWords_append]; omega)
      | none =>
        exact htail _ AbiReg.t0 AbiReg.a0 (by
          dsimp only
          have hts := tempSlotOff_32 hfl hnl htmp
          have hst' := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp) hts.1 hts.2
          have hld' := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff tmp) hts.1 hts.2
          simp only [farTotalWords_append]; omega)

private theorem compileBinFallback_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab)
    (fl : FrameLayout) (hfl : fl.protectedSlots ≤ 11 ∧ fl.spilledVars.length ≤ fl.nlocals)
    (hnl : fl.nlocals < 100000) (tmp : Nat) (htmp : tmp < 200000) (rd : Reg) (op : BinOp)
    (a b : Expr) (hoka : exprOkConst0B tab fl.nlocals a = true)
    (hokb : exprOkConst0B tab fl.nlocals b = true)
    (compA0 compB0 compB1 : Unit → List AsmItem)
    (ha0 : farTotalWords (compA0 ()) ≤ exprBound32 a)
    (hb0 : farTotalWords (compB0 ()) ≤ exprBound32 b)
    (hb1 : farTotalWords (compB1 ()) ≤ exprBound32 b) :
    farTotalWords (compileBinFallback tab fl tmp rd op a b compA0 compB0 compB1) ≤
      exprBound32 a + exprBound32 b + 17 := by
  dsimp only [compileBinFallback]
  cases b.constVal? with
  | some w =>
    cases exprReg? fl.alloc a with
    | some ra =>
      dsimp only
      have hr := emitBinConstRhsTo_farTotalWords_le rd ra op w
      omega
    | none =>
      rw [farTotalWords_append]
      have hr := emitBinConstRhsTo_farTotalWords_le rd AbiReg.a0 op w
      omega
  | none =>
    cases a.constVal? with
    | some w =>
      cases exprReg? fl.alloc b with
      | some rb =>
        cases op with
        | add | and | or | xor | mul | «mulhi» =>
          dsimp only
          rw [List.nil_append]
          have hr : ∀ op', farTotalWords (emitBinConstRhsTo rd rb op' w) ≤ 11 :=
            fun op' => emitBinConstRhsTo_farTotalWords_le rd rb op' w
          have h1 := hr .add; have h2 := hr .and; have h3 := hr .or
          have h4 := hr .xor; have h5 := hr .mul; have h6 := hr .mulhi
          omega
        | sub =>
          dsimp only; split
          · rw [List.nil_append]
            have h1 : farTotalWords [Asm.sub rd AbiReg.zero rb] = 1 := rfl
            omega
          · simp only [List.nil_append, farTotalWords_append]
            have hli := li_farTotalWords_le AbiReg.t0 w.toBitVec
            have h1 : farTotalWords [Asm.sub rd AbiReg.t0 rb] = 1 := rfl
            omega
        | shl =>
          dsimp only
          simp only [List.nil_append, farTotalWords_append]
          have hli := li_farTotalWords_le AbiReg.t0 w.toBitVec
          have h1 : farTotalWords [Asm.sll rd AbiReg.t0 rb] = 1 := rfl
          omega
        | shr =>
          dsimp only
          simp only [List.nil_append, farTotalWords_append]
          have hli := li_farTotalWords_le AbiReg.t0 w.toBitVec
          have h1 : farTotalWords [Asm.srl rd AbiReg.t0 rb] = 1 := rfl
          omega
      | none =>
        cases op with
        | add | and | or | xor | mul | «mulhi» =>
          dsimp only
          rw [farTotalWords_append]
          have hr : ∀ op', farTotalWords (emitBinConstRhsTo rd AbiReg.a0 op' w) ≤ 11 :=
            fun op' => emitBinConstRhsTo_farTotalWords_le rd AbiReg.a0 op' w
          have h1 := hr .add; have h2 := hr .and; have h3 := hr .or
          have h4 := hr .xor; have h5 := hr .mul; have h6 := hr .mulhi
          omega
        | sub =>
          dsimp only; split
          · rw [farTotalWords_append]
            have h1 : farTotalWords [Asm.sub rd AbiReg.zero AbiReg.a0] = 1 := rfl
            omega
          · simp only [farTotalWords_append]
            have hli := li_farTotalWords_le AbiReg.t0 w.toBitVec
            have h1 : farTotalWords [Asm.sub rd AbiReg.t0 AbiReg.a0] = 1 := rfl
            omega
        | shl =>
          dsimp only
          simp only [farTotalWords_append]
          have hli := li_farTotalWords_le AbiReg.t0 w.toBitVec
          have h1 : farTotalWords [Asm.sll rd AbiReg.t0 AbiReg.a0] = 1 := rfl
          omega
        | shr =>
          dsimp only
          simp only [farTotalWords_append]
          have hli := li_farTotalWords_le AbiReg.t0 w.toBitVec
          have h1 : farTotalWords [Asm.srl rd AbiReg.t0 AbiReg.a0] = 1 := rfl
          omega
    | none =>
      cases exprReg? fl.alloc b with
      | some rb =>
        cases exprReg? fl.alloc a with
        | some ra =>
          dsimp only
          have hop := emitBinOp_farTotalWords op rd ra rb; omega
        | none =>
          rw [farTotalWords_append]
          have hop := emitBinOp_farTotalWords op rd AbiReg.a0 rb
          omega
      | none =>
        cases exprReg? fl.alloc a with
        | some ra =>
          rw [farTotalWords_append]
          have hop := emitBinOp_farTotalWords op rd ra AbiReg.a0
          omega
        | none =>
          cases hsb : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 b with
          | some cb =>
            simp only [farTotalWords_append]
            have hb := emitSimpleExprR_farTotalWords_le ht hfl hnl hokb hsb
            have hop := emitBinOp_farTotalWords op rd AbiReg.a0 AbiReg.t0
            omega
          | none =>
            cases hsa : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 a with
            | some ca =>
              simp only [farTotalWords_append]
              have ha := emitSimpleExprR_farTotalWords_le ht hfl hnl hoka hsa
              have hop := emitBinOp_farTotalWords op rd AbiReg.t0 AbiReg.a0
              omega
            | none =>
              dsimp only
              split
              · have hmv : farTotalWords [Asm.mv AbiReg.t4 AbiReg.a0] = 1 := rfl
                have hop := emitBinOp_farTotalWords op rd AbiReg.t4 AbiReg.a0
                simp only [farTotalWords_append]; omega
              · have hts := tempSlotOff_32 hfl hnl htmp
                have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
                  (fl.tempSlotOff tmp) hts.1 hts.2
                have hld := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.sp AbiReg.t1
                  (fl.tempSlotOff tmp) hts.1 hts.2
                have hop := emitBinOp_farTotalWords op rd AbiReg.t0 AbiReg.a0
                simp only [farTotalWords_append]; omega

private theorem compileETo_farTotalWords_le_aux {tab : Tab} (ht : TabSmall32 tab)
    (fl : FrameLayout) (hfl : fl.protectedSlots ≤ 11 ∧ fl.spilledVars.length ≤ fl.nlocals)
    (hnl : fl.nlocals < 100000) (e : Expr) (tmp : Nat) (rd : Reg)
    (htmp : tmp + maxTempsExpr e < 100000)
    (hok : exprOkConst0B tab fl.nlocals e = true) :
    farTotalWords (compileETo tab fl tmp rd e) ≤ exprBound32 e := by
  obtain ⟨hlen8, hbase8, hlen64, hbase64, hglob, _, hrom⟩ := tab_offsets_32 ht
  match e with
  | .const w =>
    exact li_farTotalWords_le rd _
  | .var x =>
    dsimp only [compileETo, exprBound32]
    split
    · next rx _ =>
      split
      · simp [farTotalWords]
      · have hmv : farTotalWords [Asm.mv rd rx] = 1 := rfl; omega
    · have hslot := varSlotOff_32 hfl hnl x
      exact loadMemOff_farTotalWords_le_32 _ _ _ _ _ hslot.1 hslot.2
  | .len8 a =>
    exact loadMemOffGp_farTotalWords_le_32 _ _ _ _ _ (hlen8 a).1 (hlen8 a).2
  | .len64 a =>
    exact loadMemOffGp_farTotalWords_le_32 _ _ _ _ _ (hlen64 (TieredArray.t0 a)).1 (hlen64 (TieredArray.t0 a)).2
  | .glob g =>
    simp only [exprOkConst0B, decide_eq_true_eq] at hok
    exact loadMemOffGp_farTotalWords_le_32 _ _ _ _ _ (hglob g hok).1 (hglob g hok).2
  | .bin op a b =>
    simp only [maxTempsExpr] at htmp
    simp only [exprOkConst0B, Bool.and_eq_true] at hok
    unfold compileETo
    dsimp only [exprBound32]
    split
    · next inner k mask =>
      simp only [maxTempsExpr] at htmp
      simp only [exprOkConst0B, Bool.and_eq_true] at hok
      split
      · next lm _ =>
        split
        · have hin := emitShrMaskFrom_farTotalWords_le fl rd inner (lm.toNat - k.toNat % 64) lm
            (fun () => compileETo tab fl tmp AbiReg.a0 inner)
            (compileETo_farTotalWords_le_aux ht fl hfl hnl inner tmp AbiReg.a0 (by omega) hok.1.1)
          dsimp only [exprBound32]; omega
        · exact compileBinFallback_farTotalWords_le ht fl hfl hnl tmp (by omega) rd .and _ _
            (by simp [exprOkConst0B, hok.1.1]) rfl _ _ _
            (compileETo_farTotalWords_le_aux ht fl hfl hnl (.bin .shr inner (.const k)) tmp AbiReg.a0
              (by simp only [maxTempsExpr]; omega) (by simp [exprOkConst0B, hok.1.1]))
            (compileETo_farTotalWords_le_aux ht fl hfl hnl (.const mask) tmp AbiReg.a0 (by simp [maxTempsExpr]; omega) rfl)
            (compileETo_farTotalWords_le_aux ht fl hfl hnl (.const mask) (tmp + 1) AbiReg.a0 (by simp [maxTempsExpr]; omega) rfl)
      · exact compileBinFallback_farTotalWords_le ht fl hfl hnl tmp (by omega) rd .and _ _
          (by simp [exprOkConst0B, hok.1.1]) rfl _ _ _
          (compileETo_farTotalWords_le_aux ht fl hfl hnl (.bin .shr inner (.const k)) tmp AbiReg.a0
            (by simp only [maxTempsExpr]; omega) (by simp [exprOkConst0B, hok.1.1]))
          (compileETo_farTotalWords_le_aux ht fl hfl hnl (.const mask) tmp AbiReg.a0 (by simp [maxTempsExpr]; omega) rfl)
          (compileETo_farTotalWords_le_aux ht fl hfl hnl (.const mask) (tmp + 1) AbiReg.a0 (by simp [maxTempsExpr]; omega) rfl)
    · next arr i =>
      simp only [maxTempsExpr] at htmp
      simp only [exprOkConst0B, Bool.and_eq_true] at hok
      have hld := emitLd32hPlainFrom_farTotalWords_le ht fl rd arr i false
        (fun () => compileETo tab fl tmp AbiReg.a0 i)
        (compileETo_farTotalWords_le_aux ht fl hfl hnl i tmp AbiReg.a0 (by omega) hok.1.2)
      dsimp only [exprBound32]; omega
    · next arr i =>
      simp only [maxTempsExpr] at htmp
      simp only [exprOkConst0B, Bool.and_eq_true] at hok
      have hld := emitLd32hPlainFrom_farTotalWords_le ht fl rd arr i true
        (fun () => compileETo tab fl tmp AbiReg.a0 i)
        (compileETo_farTotalWords_le_aux ht fl hfl hnl i tmp AbiReg.a0 (by omega) hok.1.2)
      dsimp only [exprBound32]; omega
    · next arr t i =>
      simp only [maxTempsExpr] at htmp
      simp only [exprOkConst0B, Bool.and_eq_true] at hok
      have hld := emitLd32hFrom_farTotalWords_le ht fl hfl hnl tmp (by omega) rd arr t i false hok.1.1.2
        (fun () => compileETo tab fl tmp AbiReg.a0 i)
        (fun () => compileETo tab fl tmp AbiReg.a0 t)
        (fun () => compileETo tab fl (tmp + 1) AbiReg.a0 i)
        (compileETo_farTotalWords_le_aux ht fl hfl hnl i tmp AbiReg.a0 (by omega) hok.1.2)
        (compileETo_farTotalWords_le_aux ht fl hfl hnl t tmp AbiReg.a0 (by omega) hok.1.1.2)
        (compileETo_farTotalWords_le_aux ht fl hfl hnl i (tmp + 1) AbiReg.a0 (by omega) hok.1.2)
      dsimp only [exprBound32]; omega
    · next arr t i =>
      simp only [maxTempsExpr] at htmp
      simp only [exprOkConst0B, Bool.and_eq_true] at hok
      have hld := emitLd32hFrom_farTotalWords_le ht fl hfl hnl tmp (by omega) rd arr t i true hok.1.1.2
        (fun () => compileETo tab fl tmp AbiReg.a0 i)
        (fun () => compileETo tab fl tmp AbiReg.a0 t)
        (fun () => compileETo tab fl (tmp + 1) AbiReg.a0 i)
        (compileETo_farTotalWords_le_aux ht fl hfl hnl i tmp AbiReg.a0 (by omega) hok.1.2)
        (compileETo_farTotalWords_le_aux ht fl hfl hnl t tmp AbiReg.a0 (by omega) hok.1.1.2)
        (compileETo_farTotalWords_le_aux ht fl hfl hnl i (tmp + 1) AbiReg.a0 (by omega) hok.1.2)
      dsimp only [exprBound32]; omega
    · exact compileBinFallback_farTotalWords_le ht fl hfl hnl tmp (by omega) rd op a b hok.1 hok.2 _ _ _
        (compileETo_farTotalWords_le_aux ht fl hfl hnl a tmp AbiReg.a0 (by omega) hok.1)
        (compileETo_farTotalWords_le_aux ht fl hfl hnl b tmp AbiReg.a0 (by omega) hok.2)
        (compileETo_farTotalWords_le_aux ht fl hfl hnl b (tmp + 1) AbiReg.a0 (by omega) hok.2)
  | .cmpw c a b =>
    have iha := fun k r hk ho => compileETo_farTotalWords_le_aux ht fl hfl hnl a k r hk ho
    have ihb := fun k r hk ho => compileETo_farTotalWords_le_aux ht fl hfl hnl b k r hk ho
    simp only [maxTempsExpr] at htmp
    simp only [exprOkConst0B, Bool.and_eq_true] at hok
    dsimp only [compileETo, exprBound32]
    split
    · cases exprReg? fl.alloc a with
      | some ra => dsimp only; have h1 : farTotalWords [Asm.sltiu rd ra 1#12] = 1 := rfl; omega
      | none =>
        rw [farTotalWords_append]
        have ha := iha tmp AbiReg.a0 (by omega) hok.1
        have h1 : farTotalWords [Asm.sltiu rd AbiReg.a0 1#12] = 1 := rfl; omega
    · split
      · cases exprReg? fl.alloc b with
        | some rb => dsimp only; have h1 : farTotalWords [Asm.sltiu rd rb 1#12] = 1 := rfl; omega
        | none =>
          rw [farTotalWords_append]
          have hb := ihb tmp AbiReg.a0 (by omega) hok.2
          have h1 : farTotalWords [Asm.sltiu rd AbiReg.a0 1#12] = 1 := rfl; omega
      · split
        · cases exprReg? fl.alloc a with
          | some ra => dsimp only; have h1 : farTotalWords [Asm.sltu rd AbiReg.zero ra] = 1 := rfl; omega
          | none =>
            rw [farTotalWords_append]
            have ha := iha tmp AbiReg.a0 (by omega) hok.1
            have h1 : farTotalWords [Asm.sltu rd AbiReg.zero AbiReg.a0] = 1 := rfl; omega
        · split
          · cases exprReg? fl.alloc b with
            | some rb => dsimp only; have h1 : farTotalWords [Asm.sltu rd AbiReg.zero rb] = 1 := rfl; omega
            | none =>
              rw [farTotalWords_append]
              have hb := ihb tmp AbiReg.a0 (by omega) hok.2
              have h1 : farTotalWords [Asm.sltu rd AbiReg.zero AbiReg.a0] = 1 := rfl; omega
          · cases exprReg? fl.alloc b with
            | some rb =>
              cases exprReg? fl.alloc a with
              | some ra => dsimp only; have hc := emitCmpwTo_farTotalWords_le rd c ra rb; omega
              | none =>
                rw [farTotalWords_append]
                have ha := iha tmp AbiReg.a0 (by omega) hok.1
                have hc := emitCmpwTo_farTotalWords_le rd c AbiReg.a0 rb; omega
            | none =>
              cases exprReg? fl.alloc a with
              | some ra =>
                rw [farTotalWords_append]
                have hb := ihb tmp AbiReg.a0 (by omega) hok.2
                have hc := emitCmpwTo_farTotalWords_le rd c ra AbiReg.a0; omega
              | none =>
                cases hsb : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 b with
                | some cb =>
                  simp only [farTotalWords_append]
                  have ha := iha tmp AbiReg.a0 (by omega) hok.1
                  have hb := emitSimpleExprR_farTotalWords_le ht hfl hnl hok.2 hsb
                  have hc := emitCmpwTo_farTotalWords_le rd c AbiReg.a0 AbiReg.t0; omega
                | none =>
                  cases hsa : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 a with
                  | some ca =>
                    simp only [farTotalWords_append]
                    have hb := ihb tmp AbiReg.a0 (by omega) hok.2
                    have ha := emitSimpleExprR_farTotalWords_le ht hfl hnl hok.1 hsa
                    have hc := emitCmpwTo_farTotalWords_le rd c AbiReg.t0 AbiReg.a0; omega
                  | none =>
                    dsimp only
                    split
                    · have ha := iha tmp AbiReg.a0 (by omega) hok.1
                      have hb := ihb tmp AbiReg.a0 (by omega) hok.2
                      have hmv : farTotalWords [Asm.mv AbiReg.t4 AbiReg.a0] = 1 := rfl
                      have hc := emitCmpwTo_farTotalWords_le rd c AbiReg.t4 AbiReg.a0
                      simp only [farTotalWords_append]; omega
                    · have ha := iha tmp AbiReg.a0 (by omega) hok.1
                      have hb := ihb (tmp + 1) AbiReg.a0 (by omega) hok.2
                      have hts := tempSlotOff_32 hfl hnl (by omega : tmp < 200000)
                      have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0
                        (fl.tempSlotOff tmp) hts.1 hts.2
                      have hld := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.sp AbiReg.t1
                        (fl.tempSlotOff tmp) hts.1 hts.2
                      have hc := emitCmpwTo_farTotalWords_le rd c AbiReg.t0 AbiReg.a0
                      simp only [farTotalWords_append]; omega
  | .ld8 a i =>
    have ih := fun k r hk ho => compileETo_farTotalWords_le_aux ht fl hfl hnl i k r hk ho
    simp only [maxTempsExpr] at htmp
    simp only [exprOkConst0B, Bool.and_eq_true] at hok
    have hl1 := loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld AbiReg.t0 AbiReg.t1 (tab.len8 a) (hlen8 a).1 (hlen8 a).2
    have hl2 := loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (tab.base8 a) (hbase8 a).1 (hbase8 a).2
    dsimp only [compileETo, exprBound32]
    cases exprReg? fl.alloc i with
    | some ri =>
      dsimp only
      have hb1 : farTotalWords [Asm.bgeu ri AbiReg.t0 errLabel] = 5 := rfl
      simp only [farTotalWords_append, farTotalWords_nil]
      cases i.constVal? with
      | none =>
        dsimp only; have hb2 : farTotalWords [Asm.add AbiReg.t1 AbiReg.t1 ri, Asm.lbu rd AbiReg.t1 0#12] = 2 := rfl; omega
      | some w =>
        dsimp only; split
        · have hb2 : farTotalWords [Asm.lbu rd AbiReg.t1 (BitVec.ofNat 12 w.toNat)] = 1 := rfl; omega
        · have hb2 : farTotalWords [Asm.add AbiReg.t1 AbiReg.t1 ri, Asm.lbu rd AbiReg.t1 0#12] = 2 := rfl; omega
    | none =>
      dsimp only
      have hi := ih tmp AbiReg.a0 htmp hok.2
      have hb1 : farTotalWords [Asm.bgeu AbiReg.a0 AbiReg.t0 errLabel] = 5 := rfl
      simp only [farTotalWords_append]
      cases i.constVal? with
      | none =>
        dsimp only; have hb2 : farTotalWords [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.a0, Asm.lbu rd AbiReg.t1 0#12] = 2 := rfl; omega
      | some w =>
        dsimp only; split
        · have hb2 : farTotalWords [Asm.lbu rd AbiReg.t1 (BitVec.ofNat 12 w.toNat)] = 1 := rfl; omega
        · have hb2 : farTotalWords [Asm.add AbiReg.t1 AbiReg.t1 AbiReg.a0, Asm.lbu rd AbiReg.t1 0#12] = 2 := rfl; omega
  | .ld64 a i =>
    have ih := fun k r hk ho => compileETo_farTotalWords_le_aux ht fl hfl hnl i k r hk ho
    simp only [maxTempsExpr] at htmp
    simp only [exprOkConst0B, Bool.and_eq_true] at hok
    have hl1 := loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld AbiReg.t0 AbiReg.t1
      (tab.len64 (TieredArray.t0 a)) (hlen64 _).1 (hlen64 _).2
    have hl2 := loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld AbiReg.t1 AbiReg.t2
      (tab.base64 (TieredArray.t0 a)) (hbase64 _).1 (hbase64 _).2
    dsimp only [compileETo, exprBound32]
    cases exprReg? fl.alloc i with
    | some ri =>
      dsimp only
      have h1 : farTotalWords [Asm.bgeu ri AbiReg.t0 errLabel] = 5 := rfl
      have h2 := ld64Tail_farTotalWords_le rd ri AbiReg.t2 i
      simp only [farTotalWords_append, farTotalWords_nil]; omega
    | none =>
      dsimp only
      have hi := ih tmp AbiReg.a0 htmp hok.2
      have h1 : farTotalWords [Asm.bgeu AbiReg.a0 AbiReg.t0 errLabel] = 5 := rfl
      have h2 := ld64Tail_farTotalWords_le rd AbiReg.a0 AbiReg.t2 i
      simp only [farTotalWords_append]; omega
  | .ldc d i =>
    have ih := fun k r hk ho => compileETo_farTotalWords_le_aux ht fl hfl hnl i k r hk ho
    simp only [maxTempsExpr] at htmp
    simp only [exprOkConst0B, Bool.and_eq_true] at hok
    have hli10 := li_farTotalWords_le AbiReg.t0 (BitVec.ofNat 64 d.length)
    have hld := loadMemOff_farTotalWords_le_32 .lbu rd AbiReg.t1 AbiReg.t2
      (tab.romBase + (romIdx d tab.rom : Int)) (hrom d).1 (hrom d).2
    dsimp only [compileETo, exprBound32]
    cases exprReg? fl.alloc i with
    | some ri =>
      dsimp only
      have hb1 : farTotalWords [Asm.bgeu ri AbiReg.t0 errLabel, Asm.add AbiReg.t1 AbiReg.gp ri] = 6 := rfl
      simp only [farTotalWords_append, farTotalWords_nil]; omega
    | none =>
      dsimp only
      have hi := ih tmp AbiReg.a0 htmp hok.2
      have hb1 : farTotalWords [Asm.bgeu AbiReg.a0 AbiReg.t0 errLabel, Asm.add AbiReg.t1 AbiReg.gp AbiReg.a0] = 6 := rfl
      simp only [farTotalWords_append]; omega
  | .ld64t a t i =>
    have iht := fun k r hk ho => compileETo_farTotalWords_le_aux ht fl hfl hnl t k r hk ho
    have ihi := fun k r hk ho => compileETo_farTotalWords_le_aux ht fl hfl hnl i k r hk ho
    simp only [maxTempsExpr] at htmp
    simp only [exprOkConst0B, Bool.and_eq_true] at hok
    dsimp only [compileETo, exprBound32]
    cases t.constVal? with
    | some w =>
      dsimp only
      have hl1 := loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld AbiReg.t2 AbiReg.t3
        (tab.len64 (tierA a w)) (hlen64 _).1 (hlen64 _).2
      have hl2 := loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld AbiReg.t1 AbiReg.t3
        (tab.base64 (tierA a w)) (hbase64 _).1 (hbase64 _).2
      cases exprReg? fl.alloc i with
      | some ri =>
        dsimp only
        have h2 : farTotalWords [Asm.bgeu ri AbiReg.t2 errLabel] = 5 := rfl
        have h3 := ld64Tail_farTotalWords_le rd ri AbiReg.t3 i
        simp only [farTotalWords_append, farTotalWords_nil]; omega
      | none =>
        dsimp only
        have hi := ihi tmp AbiReg.a0 (by omega) hok.2
        have h2 : farTotalWords [Asm.bgeu AbiReg.a0 AbiReg.t2 errLabel] = 5 := rfl
        have h3 := ld64Tail_farTotalWords_le rd AbiReg.a0 AbiReg.t3 i
        simp only [farTotalWords_append]; omega
    | none =>
      have hl1 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t2 AbiReg.t1 AbiReg.t3
        (tab.len64 (TieredArray.t0 a)) (hlen64 _).1 (hlen64 _).2
      have hl2 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.t1 AbiReg.t3
        (tab.base64 (TieredArray.t0 a)) (hbase64 _).1 (hbase64 _).2
      have htail : ∀ (head : List AsmItem) (rt ri : Reg),
          farTotalWords head ≤ exprBound32 t + exprBound32 i + 12 →
          farTotalWords (head ++
            [Asm.andi AbiReg.t0 rt 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
             Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
            loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (tab.len64 (TieredArray.t0 a)) ++
            [Asm.bgeu ri AbiReg.t2 errLabel] ++
            loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t3 (tab.base64 (TieredArray.t0 a)) ++
            ld64Tail rd ri AbiReg.t3 i) ≤ exprBound32 t + exprBound32 i + 35 := by
        intro head rt ri hh
        have h1 : farTotalWords [Asm.andi AbiReg.t0 rt 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
            Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] = 3 := rfl
        have h2 : farTotalWords [Asm.bgeu ri AbiReg.t2 errLabel] = 5 := rfl
        have h3 := ld64Tail_farTotalWords_le rd ri AbiReg.t3 i
        simp only [farTotalWords_append]; omega
      cases exprReg? fl.alloc t with
      | some rt =>
        cases exprReg? fl.alloc i with
        | some ri => exact htail [] rt ri (by simp [farTotalWords])
        | none =>
          exact htail _ rt AbiReg.a0 (by dsimp only; have hi := ihi tmp AbiReg.a0 (by omega) hok.2; omega)
      | none =>
        cases hst : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 t with
        | some ct =>
          have ht'' := emitSimpleExprR_farTotalWords_le ht hfl hnl hok.1.2 hst
          cases exprReg? fl.alloc i with
          | some ri => exact htail ct AbiReg.t0 ri (by omega)
          | none =>
            exact htail _ AbiReg.t0 AbiReg.a0 (by
              have hi := ihi tmp AbiReg.a0 (by omega) hok.2; rw [farTotalWords_append]; omega)
        | none =>
          exact htail _ AbiReg.t0 AbiReg.a0 (by
            have ha := iht tmp AbiReg.a0 (by omega) hok.1.2
            have hb := ihi (tmp + 1) AbiReg.a0 (by omega) hok.2
            have hts := tempSlotOff_32 hfl hnl (by omega : tmp < 200000)
            have hst' := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp) hts.1 hts.2
            have hld' := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff tmp) hts.1 hts.2
            simp only [farTotalWords_append]; omega)
  | .len64t a t =>
    have ih := fun k r hk ho => compileETo_farTotalWords_le_aux ht fl hfl hnl t k r hk ho
    simp only [maxTempsExpr] at htmp
    simp only [exprOkConst0B, Bool.and_eq_true] at hok
    dsimp only [compileETo, exprBound32]
    cases t.constVal? with
    | some w =>
      dsimp only
      have hl := loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld rd AbiReg.t2
        (tab.len64 (tierA a w)) (hlen64 _).1 (hlen64 _).2
      omega
    | none =>
      have hl := loadMemOff_farTotalWords_le_32 .ld rd AbiReg.t1 AbiReg.t2
        (tab.len64 (TieredArray.t0 a)) (hlen64 _).1 (hlen64 _).2
      cases exprReg? fl.alloc t with
      | some rt =>
        have h1 : farTotalWords [Asm.andi AbiReg.t0 rt 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
            Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] = 3 := rfl
        simp only [farTotalWords_append, farTotalWords_nil]; omega
      | none =>
        have hi := ih tmp AbiReg.a0 htmp hok.2
        have h1 : farTotalWords [Asm.andi AbiReg.t0 AbiReg.a0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
            Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] = 3 := rfl
        simp only [farTotalWords_append]; omega
  | .ld8x8 src i =>
    have ih := fun k r hk ho => compileETo_farTotalWords_le_aux ht fl hfl hnl i k r hk ho
    simp only [maxTempsExpr] at htmp
    have hreadAll : allInstrs ([Asm.lbu rd AbiReg.t1 7#12] ++
        List.flatMap (fun k =>
          [Asm.lbu AbiReg.t2 AbiReg.t1 (BitVec.ofInt 12 k), Asm.slli rd rd 8#6,
           Asm.or rd rd AbiReg.t2]) [6, 5, 4, 3, 2, 1, 0]) = true := by
      rw [allInstrs_append, Bool.and_eq_true]
      exact ⟨rfl, allInstrs_flatMap (fun _ _ => rfl)⟩
    have hread : farTotalWords ([Asm.lbu rd AbiReg.t1 7#12] ++
        List.flatMap (fun k =>
          [Asm.lbu AbiReg.t2 AbiReg.t1 (BitVec.ofInt 12 k), Asm.slli rd rd 8#6,
           Asm.or rd rd AbiReg.t2]) [6, 5, 4, 3, 2, 1, 0]) = 22 := by
      rw [farTotalWords_of_allInstrs hreadAll]; rfl
    have hoki : exprOkConst0B tab fl.nlocals i = true := by
      cases src <;> simp only [exprOkConst0B, Bool.and_eq_true] at hok <;> exact hok.2
    dsimp only [compileETo, exprBound32]
    cases exprReg? fl.alloc i with
    | some ri =>
      have hmid : farTotalWords [Asm.addi AbiReg.t2 AbiReg.zero 8#12, Asm.bltu AbiReg.t0 AbiReg.t2 errLabel,
          Asm.addi AbiReg.t0 AbiReg.t0 (-8#12), Asm.bltu AbiReg.t0 ri errLabel,
          Asm.add AbiReg.t1 AbiReg.t1 ri] = 13 := rfl
      cases src with
      | arr a =>
        have hl1 := loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld AbiReg.t0 AbiReg.t2 (tab.len8 a) (hlen8 a).1 (hlen8 a).2
        have hl2 := loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (tab.base8 a) (hbase8 a).1 (hbase8 a).2
        simp only [List.nil_append, farTotalWords_append] at hread ⊢; omega
      | rom d =>
        have hli := li_farTotalWords_le AbiReg.t0 (BitVec.ofNat 64 d.length)
        have hadd := addImmOff_farTotalWords_le_32 AbiReg.t1 AbiReg.gp AbiReg.t2
          (tab.romBase + (romIdx d tab.rom : Int)) (hrom d).1 (hrom d).2
        simp only [List.nil_append, farTotalWords_append] at hread ⊢; omega
    | none =>
      have hi := ih tmp AbiReg.a0 htmp hoki
      have hmid : farTotalWords [Asm.addi AbiReg.t2 AbiReg.zero 8#12, Asm.bltu AbiReg.t0 AbiReg.t2 errLabel,
          Asm.addi AbiReg.t0 AbiReg.t0 (-8#12), Asm.bltu AbiReg.t0 AbiReg.a0 errLabel,
          Asm.add AbiReg.t1 AbiReg.t1 AbiReg.a0] = 13 := rfl
      cases src with
      | arr a =>
        have hl1 := loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld AbiReg.t0 AbiReg.t2 (tab.len8 a) (hlen8 a).1 (hlen8 a).2
        have hl2 := loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (tab.base8 a) (hbase8 a).1 (hbase8 a).2
        simp only [farTotalWords_append] at hread ⊢; omega
      | rom d =>
        have hli := li_farTotalWords_le AbiReg.t0 (BitVec.ofNat 64 d.length)
        have hadd := addImmOff_farTotalWords_le_32 AbiReg.t1 AbiReg.gp AbiReg.t2
          (tab.romBase + (romIdx d tab.rom : Int)) (hrom d).1 (hrom d).2
        simp only [farTotalWords_append] at hread ⊢; omega
  | .ld32t a t i =>
    have iht := fun k r hk ho => compileETo_farTotalWords_le_aux ht fl hfl hnl t k r hk ho
    have ihi := fun k r hk ho => compileETo_farTotalWords_le_aux ht fl hfl hnl i k r hk ho
    simp only [maxTempsExpr] at htmp
    simp only [exprOkConst0B, Bool.and_eq_true] at hok
    dsimp only [compileETo, exprBound32]
    cases t.constVal? with
    | some w =>
      dsimp only
      have hl1 := loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld AbiReg.t2 AbiReg.t3
        (tab.len64 (tierA a w)) (hlen64 _).1 (hlen64 _).2
      have hl2 := loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld AbiReg.t1 AbiReg.t3
        (tab.base64 (tierA a w)) (hbase64 _).1 (hbase64 _).2
      cases exprReg? fl.alloc i with
      | some ri =>
        dsimp only
        have h2 : farTotalWords [Asm.srli AbiReg.t3 ri 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] = 6 := rfl
        have h3 := ld32tTail_farTotalWords_le rd ri i
        simp only [farTotalWords_append, farTotalWords_nil]; omega
      | none =>
        dsimp only
        have hi := ihi tmp AbiReg.a0 (by omega) hok.2
        have h2 : farTotalWords [Asm.srli AbiReg.t3 AbiReg.a0 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] = 6 := rfl
        have h3 := ld32tTail_farTotalWords_le rd AbiReg.a0 i
        simp only [farTotalWords_append]; omega
    | none =>
      have hl1 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t2 AbiReg.t1 AbiReg.t3
        (tab.len64 (TieredArray.t0 a)) (hlen64 _).1 (hlen64 _).2
      have hl2 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.t1 AbiReg.t3
        (tab.base64 (TieredArray.t0 a)) (hbase64 _).1 (hbase64 _).2
      have htail : ∀ (head : List AsmItem) (rt ri : Reg),
          farTotalWords head ≤ exprBound32 t + exprBound32 i + 12 →
          farTotalWords (head ++
            [Asm.andi AbiReg.t0 rt 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
             Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] ++
            loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t3 (tab.len64 (TieredArray.t0 a)) ++
            [Asm.srli AbiReg.t3 ri 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] ++
            loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t3 (tab.base64 (TieredArray.t0 a)) ++
            ld32tTail rd ri i) ≤ exprBound32 t + exprBound32 i + 36 := by
        intro head rt ri hh
        have h1 : farTotalWords [Asm.andi AbiReg.t0 rt 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
            Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] = 3 := rfl
        have h2 : farTotalWords [Asm.srli AbiReg.t3 ri 1#6, Asm.bgeu AbiReg.t3 AbiReg.t2 errLabel] = 6 := rfl
        have h3 := ld32tTail_farTotalWords_le rd ri i
        simp only [farTotalWords_append]; omega
      cases exprReg? fl.alloc t with
      | some rt =>
        cases exprReg? fl.alloc i with
        | some ri => exact htail [] rt ri (by simp [farTotalWords])
        | none =>
          exact htail _ rt AbiReg.a0 (by dsimp only; have hi := ihi tmp AbiReg.a0 (by omega) hok.2; omega)
      | none =>
        cases hst : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 t with
        | some ct =>
          have ht'' := emitSimpleExprR_farTotalWords_le ht hfl hnl hok.1.2 hst
          cases exprReg? fl.alloc i with
          | some ri => exact htail ct AbiReg.t0 ri (by omega)
          | none =>
            exact htail _ AbiReg.t0 AbiReg.a0 (by
              have hi := ihi tmp AbiReg.a0 (by omega) hok.2; rw [farTotalWords_append]; omega)
        | none =>
          exact htail _ AbiReg.t0 AbiReg.a0 (by
            have ha := iht tmp AbiReg.a0 (by omega) hok.1.2
            have hb := ihi (tmp + 1) AbiReg.a0 (by omega) hok.2
            have hts := tempSlotOff_32 hfl hnl (by omega : tmp < 200000)
            have hst' := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp) hts.1 hts.2
            have hld' := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff tmp) hts.1 hts.2
            simp only [farTotalWords_append]; omega)
  | .ld32h a t i hi =>
    simp only [maxTempsExpr] at htmp
    simp only [exprOkConst0B, Bool.and_eq_true] at hok
    exact emitLd32hFrom_farTotalWords_le ht fl hfl hnl tmp (by omega) rd a t i hi hok.1.2 _ _ _
      (compileETo_farTotalWords_le_aux ht fl hfl hnl i tmp AbiReg.a0 (by omega) hok.2)
      (compileETo_farTotalWords_le_aux ht fl hfl hnl t tmp AbiReg.a0 (by omega) hok.1.2)
      (compileETo_farTotalWords_le_aux ht fl hfl hnl i (tmp + 1) AbiReg.a0 (by omega) hok.2)
termination_by sizeOf e

private theorem compileETo_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab)
    (fl : FrameLayout) (hfl : fl.protectedSlots ≤ 11 ∧ fl.spilledVars.length ≤ fl.nlocals)
    (hnl : fl.nlocals < 100000) :
    ∀ (e : Expr) (tmp : Nat) (rd : Reg),
      tmp + maxTempsExpr e < 100000 →
      exprOkConst0B tab fl.nlocals e = true →
      farTotalWords (compileETo tab fl tmp rd e) ≤ exprBound32 e :=
  compileETo_farTotalWords_le_aux ht fl hfl hnl

private theorem compileCR_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab)
    (fl : FrameLayout) (hfl : fl.protectedSlots ≤ 11 ∧ fl.spilledVars.length ≤ fl.nlocals)
    (tmp : Nat) (hnl : fl.nlocals < 100000) (pfx : String) :
    ∀ (c : Cond) (lblId : Nat) (want : Bool) (target : String),
      tmp + maxTempsCond c < 100000 →
      condOkConst0B tab fl.nlocals c = true →
      farTotalWords (compileCR tab fl tmp pfx lblId c want target).1 ≤ condBound32 c := by
  intro c
  induction c with
  | cmp op a b =>
    intro lblId want target htmp hok
    simp only [maxTempsCond] at htmp
    simp only [condOkConst0B, Bool.and_eq_true] at hok
    dsimp only [compileCR, condBound32]
    cases exprReg? fl.alloc a with
    | some ra =>
      cases exprReg? fl.alloc b with
      | some rb => rw [brCmp_farTotalWords]; omega
      | none =>
        rw [farTotalWords_append, brCmp_farTotalWords]
        have hb := compileETo_farTotalWords_le ht fl hfl hnl b tmp AbiReg.a0 (by omega) hok.2
        omega
    | none =>
      cases exprReg? fl.alloc b with
      | some rb =>
        rw [farTotalWords_append, brCmp_farTotalWords]
        have ha := compileETo_farTotalWords_le ht fl hfl hnl a tmp AbiReg.a0 (by omega) hok.1
        omega
      | none =>
        cases hsb : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 b with
        | some cb =>
          simp only [farTotalWords_append, brCmp_farTotalWords]
          have ha := compileETo_farTotalWords_le ht fl hfl hnl a tmp AbiReg.a0 (by omega) hok.1
          have hb := emitSimpleExprR_farTotalWords_le ht hfl hnl hok.2 hsb
          omega
        | none =>
          cases hsa : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 a with
          | some ca =>
            simp only [farTotalWords_append, brCmp_farTotalWords]
            have hb := compileETo_farTotalWords_le ht fl hfl hnl b tmp AbiReg.a0 (by omega) hok.2
            have ha := emitSimpleExprR_farTotalWords_le ht hfl hnl hok.1 hsa
            omega
          | none =>
            dsimp only
            split
            · have ha := compileETo_farTotalWords_le ht fl hfl hnl a tmp AbiReg.a0 (by omega) hok.1
              have hb := compileETo_farTotalWords_le ht fl hfl hnl b tmp AbiReg.a0 (by omega) hok.2
              have hmv : farTotalWords [Asm.mv AbiReg.t4 AbiReg.a0] = 1 := rfl
              simp only [farTotalWords_append, brCmp_farTotalWords]; omega
            · have ha := compileETo_farTotalWords_le ht fl hfl hnl a tmp AbiReg.a0 (by omega) hok.1
              have hb := compileETo_farTotalWords_le ht fl hfl hnl b (tmp + 1) AbiReg.a0 (by omega) hok.2
              have hts := tempSlotOff_32 hfl hnl (by omega : tmp < 200000)
              have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp) hts.1 hts.2
              have hld := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff tmp) hts.1 hts.2
              simp only [farTotalWords_append, brCmp_farTotalWords]; omega
  | not p ih =>
    intro lblId want target htmp hok
    exact ih lblId (!want) target htmp hok
  | and p q ihp ihq =>
    intro lblId want target htmp hok
    simp only [maxTempsCond] at htmp
    simp only [condOkConst0B, Bool.and_eq_true] at hok
    dsimp only [compileCR, condBound32]
    cases want
    · simp only [Bool.false_eq_true, ↓reduceIte, farTotalWords_append]
      have hp := ihp lblId false target (by omega) hok.1
      have hq := ihq (compileCR tab fl tmp pfx lblId p false target).2 false target (by omega) hok.2
      omega
    · simp only [↓reduceIte, farTotalWords_append]
      let skipLbl := toString pfx ++ toString "_and_" ++ toString lblId
      have hp := ihp (lblId + 1) false skipLbl (by omega) hok.1
      have hq := ihq (compileCR tab fl tmp pfx (lblId + 1) p false skipLbl).2 true target (by omega) hok.2
      have hlbl : farTotalWords [Asm.lbl skipLbl] = 0 := rfl
      dsimp only [skipLbl] at hp hq hlbl; omega
  | or p q ihp ihq =>
    intro lblId want target htmp hok
    simp only [maxTempsCond] at htmp
    simp only [condOkConst0B, Bool.and_eq_true] at hok
    dsimp only [compileCR, condBound32]
    cases want
    · simp only [Bool.false_eq_true, ↓reduceIte, farTotalWords_append]
      let skipLbl := toString pfx ++ toString "_or_" ++ toString lblId
      have hp := ihp (lblId + 1) true skipLbl (by omega) hok.1
      have hq := ihq (compileCR tab fl tmp pfx (lblId + 1) p true skipLbl).2 false target (by omega) hok.2
      have hlbl : farTotalWords [Asm.lbl skipLbl] = 0 := rfl
      dsimp only [skipLbl] at hp hq hlbl; omega
    · simp only [↓reduceIte, farTotalWords_append]
      have hp := ihp lblId true target (by omega) hok.1
      have hq := ihq (compileCR tab fl tmp pfx lblId p true target).2 true target (by omega) hok.2
      omega

private theorem compileEvalExprsToTempsR_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab)
    (fl : FrameLayout) (hfl : fl.protectedSlots ≤ 11 ∧ fl.spilledVars.length ≤ fl.nlocals)
    (hnl : fl.nlocals < 100000) :
    ∀ (es : List Expr) (tmp : Nat),
      tmp + maxTempsExprs es < 100000 →
      es.all (exprOkConst0B tab fl.nlocals) = true →
      farTotalWords (compileEvalExprsToTempsR tab fl tmp es) ≤ exprsBound32 es := by
  intro es tmp htmp hok
  induction es generalizing tmp with
  | nil => simp [compileEvalExprsToTempsR, farTotalWords]
  | cons e es ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hok
    have he_lt : tmp + maxTempsExpr e < 100000 := by
      have hm := foldl_max_zipIdx (e :: es) 0 0 e 0 (by simp)
      dsimp only [maxTempsExprs] at htmp; omega
    have hes_lt : (tmp + 1) + maxTempsExprs es < 100000 := by
      have hle : 1 + maxTempsExprs es ≤ maxTempsExprs (e :: es) := by
        dsimp only [maxTempsExprs]
        have hstep : ∀ (xs : List Expr) (k acc1 acc2 : Nat),
            acc1 + 1 ≤ acc2 →
            (xs.zipIdx k).foldl (fun a (p : Expr × Nat) => max a (p.2 + max 1 (maxTempsExpr p.1))) acc1 + 1 ≤
            (xs.zipIdx (k + 1)).foldl (fun a (p : Expr × Nat) => max a (p.2 + max 1 (maxTempsExpr p.1))) acc2 := by
          intro xs; induction xs with
          | nil => intro k a1 a2 ha; simp [ha]
          | cons y ys ihy => intro k a1 a2 ha; simp only [List.zipIdx_cons, List.foldl_cons]; exact ihy (k + 1) _ _ (by omega)
        have h0 := hstep es 0 0 (max 0 (0 + max 1 (maxTempsExpr e))) (by omega)
        simpa [List.zipIdx_cons, List.foldl_cons, Nat.add_comm] using h0
      omega
    have hts := tempSlotOff_32 hfl hnl (by omega : tmp < 200000)
    have he := compileETo_farTotalWords_le ht fl hfl hnl e tmp AbiReg.a0 he_lt hok.1
    have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff tmp) hts.1 hts.2
    have hes := ih (tmp + 1) hes_lt hok.2
    dsimp only [compileEvalExprsToTempsR, exprsBound32]
    rw [farTotalWords_append]
    cases exprReg? fl.alloc e with
    | some r =>
      dsimp only
      have hstr := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp r AbiReg.t0 (fl.tempSlotOff tmp) hts.1 hts.2
      omega
    | none =>
      rw [farTotalWords_append]; omega

private theorem copyTempsToResultsR_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab)
    (fl : FrameLayout) (hfl : fl.protectedSlots ≤ 11 ∧ fl.spilledVars.length ≤ fl.nlocals)
    (hnl : fl.nlocals < 100000) (tmp count : Nat) (htmp : tmp + tab.nres < 200000) :
    farTotalWords (copyTempsToResultsR tab fl tmp count) ≤ 12 * tab.nres := by
  have ⟨_, _, _, _, _, hres, _⟩ := tab_offsets_32 ht
  dsimp only [copyTempsToResultsR]
  split
  · split
    · have h1 : farTotalWords [Asm.addi AbiReg.a0 AbiReg.zero 0#12] = 1 := rfl; omega
    · simp [farTotalWords]
  · refine Nat.le_trans (farTotalWords_flatMap_le _ _ (fun _ => 12) (fun i hi => ?_)) ?_
    · simp only [List.mem_range] at hi
      have hiN : i < tab.nres := Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)
      have hres_i := hres i hiN
      have hslot := tempSlotOff_32 hfl hnl (by omega : tmp + i < 200000)
      split
      · have hl := loadMemOff_farTotalWords_le_32 .ld (resReg i) AbiReg.sp AbiReg.t0
          (fl.tempSlotOff (tmp + i)) hslot.1 hslot.2
        omega
      · simp only [farTotalWords_append]
        have hl := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.sp AbiReg.t2
          (fl.tempSlotOff (tmp + i)) hslot.1 hslot.2
        have hs := storeMemOff_farTotalWords_le_32 .sd AbiReg.gp AbiReg.t1 AbiReg.t2
          (tab.resOff i) hres_i.1 hres_i.2
        omega
    · have hsum : ∀ (xs : List Nat) (acc : Nat),
          xs.foldl (fun a _ => a + 12) acc = acc + 12 * xs.length := by
        intro xs; induction xs with | nil => simp | cons x xs ih => intro acc; simp [ih]; omega
      rw [hsum, Nat.zero_add, List.length_range]
      exact Nat.mul_le_mul_left 12 (Nat.min_le_right count tab.nres)

private theorem copyTempsToResultsR_zero_farTotalWords_le (tab : Tab)
    (fl : FrameLayout) (tmp : Nat) :
    farTotalWords (copyTempsToResultsR tab fl tmp 0) ≤ 1 := by
  dsimp only [copyTempsToResultsR]
  simp only [beq_self_eq_true, ↓reduceIte]
  split
  · decide
  · simp [farTotalWords]

private theorem saveCalleeRegs_farTotalWords_le (fl : FrameLayout)
    (hs : fl.savedRegs.length ≤ 10) :
    farTotalWords (saveCalleeRegs fl) ≤ 10 := by
  have hmem : ∀ (xs : List Reg) (k : Nat) (r : Reg) (i : Nat),
      (r, i) ∈ xs.zipIdx k → i < k + xs.length := by
    intro xs; induction xs with
    | nil => intro _ _ _ h; simp at h
    | cons x xs ih =>
      intro k r i h
      simp only [List.zipIdx_cons, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h'
      · simp
      · have := ih (k + 1) r i h'; simp; omega
  dsimp only [saveCalleeRegs]
  refine Nat.le_trans (farTotalWords_flatMap_le _ _ (fun _ => 1) (fun ⟨r, i⟩ hm => ?_)) ?_
  · have hi : i < fl.savedRegs.length := by simpa using hmem fl.savedRegs 0 r i hm
    have hra : fl.raSlots ≤ 1 := by dsimp [FrameLayout.raSlots]; split <;> omega
    have hoff : -2048 ≤ fl.savedOff i ∧ fl.savedOff i ≤ 2047 := by
      dsimp only [FrameLayout.savedOff]; omega
    rw [storeMemOff_farTotalWords_imm12 .sd AbiReg.sp r AbiReg.t2 (fl.savedOff i) hoff.1 hoff.2]
    exact Nat.le_refl 1
  · have hsum : ∀ (ps : List (Reg × Nat)) (acc : Nat),
        ps.foldl (fun a _ => a + 1) acc = acc + ps.length := by
      intro ps; induction ps with | nil => simp | cons _ ps ih => intro acc; simp [ih]; omega
    rw [hsum, Nat.zero_add, List.length_zipIdx]; exact hs

private theorem restoreCalleeRegs_farTotalWords_le (fl : FrameLayout)
    (hs : fl.savedRegs.length ≤ 10) :
    farTotalWords (restoreCalleeRegs fl) ≤ 10 := by
  have hmem : ∀ (xs : List Reg) (k : Nat) (r : Reg) (i : Nat),
      (r, i) ∈ xs.zipIdx k → i < k + xs.length := by
    intro xs; induction xs with
    | nil => intro _ _ _ h; simp at h
    | cons x xs ih =>
      intro k r i h
      simp only [List.zipIdx_cons, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h'
      · simp
      · have := ih (k + 1) r i h'; simp; omega
  dsimp only [restoreCalleeRegs]
  refine Nat.le_trans (farTotalWords_flatMap_le _ _ (fun _ => 1) (fun ⟨r, i⟩ hm => ?_)) ?_
  · have hi : i < fl.savedRegs.length := by simpa using hmem fl.savedRegs 0 r i hm
    have hra : fl.raSlots ≤ 1 := by dsimp [FrameLayout.raSlots]; split <;> omega
    have hoff : -2048 ≤ fl.savedOff i ∧ fl.savedOff i ≤ 2047 := by
      dsimp only [FrameLayout.savedOff]; omega
    rw [loadMemOff_farTotalWords_imm12 .ld r AbiReg.sp AbiReg.t0 (fl.savedOff i) hoff.1 hoff.2]
    exact Nat.le_refl 1
  · have hsum : ∀ (ps : List (Reg × Nat)) (acc : Nat),
        ps.foldl (fun a _ => a + 1) acc = acc + ps.length := by
      intro ps; induction ps with | nil => simp | cons _ ps ih => intro acc; simp [ih]; omega
    rw [hsum, Nat.zero_add, List.length_zipIdx]; exact hs

private theorem copyParamsR_farTotalWords_le (fl : FrameLayout)
    (hfl : fl.protectedSlots ≤ 11 ∧ fl.spilledVars.length ≤ fl.nlocals)
    (hnl : fl.nlocals < 100000) (n : Nat) (hn : n < 100000) :
    farTotalWords (copyParamsR fl n) ≤ 12 * n := by
  dsimp only [copyParamsR]
  refine Nat.le_trans (farTotalWords_flatMap_le _ _ (fun _ => 12) (fun i hi => ?_)) ?_
  · simp only [List.mem_range] at hi
    split
    · cases fl.alloc.lookup i with
      | some rx =>
        dsimp only
        split
        · simp [farTotalWords]
        · have hmv : farTotalWords [Asm.mv rx (resReg i)] = 1 := rfl; omega
      | none =>
        dsimp only
        split
        · simp [farTotalWords]
        · have hslot := varSlotOff_32 hfl hnl i
          have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp (resReg i) AbiReg.t2
            (fl.varSlotOff i) hslot.1 hslot.2
          omega
    · have hiLo : 0 ≤ 8 * Int.ofNat (i - maxRes) := by change 0 ≤ 8 * ((i - maxRes : Nat) : Int); omega
      have hiHi : 8 * Int.ofNat (i - maxRes) < 2 ^ 31 := by change 8 * ((i - maxRes : Nat) : Int) < 2 ^ 31; omega
      cases fl.alloc.lookup i with
      | some rx =>
        dsimp only
        have h1 := loadMemOff_farTotalWords_le_32 .ld rx AbiReg.t0 AbiReg.t2 (8 * Int.ofNat (i - maxRes)) hiLo hiHi
        omega
      | none =>
        dsimp only
        split
        · simp [farTotalWords]
        · rw [farTotalWords_append]
          have h1 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t4 AbiReg.t0 AbiReg.t2 (8 * Int.ofNat (i - maxRes)) hiLo hiHi
          have hslot := varSlotOff_32 hfl hnl i
          have h2 := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.t4 AbiReg.t2 (fl.varSlotOff i) hslot.1 hslot.2
          omega
  · have hsum : ∀ (xs : List Nat) (acc : Nat), xs.foldl (fun a _ => a + 12) acc = acc + 12 * xs.length := by
      intro xs; induction xs with | nil => simp | cons _ xs ih => intro acc; simp [ih]; omega
    rw [hsum, Nat.zero_add, List.length_range]; exact Nat.le_refl _

private theorem zeroLocalsR_farTotalWords_le (fl : FrameLayout)
    (hfl : fl.protectedSlots ≤ 11 ∧ fl.spilledVars.length ≤ fl.nlocals)
    (hnl : fl.nlocals < 100000) (fd : FunDecl) :
    farTotalWords (zeroLocalsR fl fd) ≤ 6 * (fl.nlocals - fd.nparams) := by
  dsimp only [zeroLocalsR]
  refine Nat.le_trans (farTotalWords_flatMap_le _ _ (fun _ => 6) (fun j _ => ?_)) ?_
  · split
    · simp [farTotalWords]
    · split
      · next rx _ =>
        have h1 : farTotalWords [Asm.addi rx AbiReg.zero 0#12] = 1 := rfl; omega
      · split
        · simp [farTotalWords]
        · have hslot := varSlotOff_32 hfl hnl (fd.nparams + j)
          exact storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.zero AbiReg.t2
            (fl.varSlotOff (fd.nparams + j)) hslot.1 hslot.2
  · have hsum : ∀ (xs : List Nat) (acc : Nat), xs.foldl (fun a _ => a + 6) acc = acc + 6 * xs.length := by
      intro xs; induction xs with | nil => simp | cons _ xs ih => intro acc; simp [ih]; omega
    rw [hsum, Nat.zero_add, List.length_range]; exact Nat.le_refl _

private theorem copyResultsToLocalsR_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab)
    (fl : FrameLayout) (hfl : fl.protectedSlots ≤ 11 ∧ fl.spilledVars.length ≤ fl.nlocals)
    (hnl : fl.nlocals < 100000) (xs : List Var) :
    farTotalWords (copyResultsToLocalsR tab fl xs) ≤ 12 * xs.length := by
  have ⟨_, _, _, _, _, hres, _⟩ := tab_offsets_32 ht
  dsimp only [copyResultsToLocalsR]
  refine Nat.le_trans (farTotalWords_flatMap_le _ _ (fun _ => 12) (fun ⟨x, i⟩ _ => ?_)) ?_
  · have hslot := varSlotOff_32 hfl hnl x
    dsimp only [Prod.fst, Prod.snd]
    split
    · next rx _ =>
      split
      · next hi =>
        split
        · split
          · simp [farTotalWords]
          · have h1 : farTotalWords [Asm.mv rx (resReg i)] = 1 := rfl; omega
        · have hres_i := hres i hi
          have hl := loadMemOff_farTotalWords_le_32 .ld rx AbiReg.gp AbiReg.t2
            (tab.resOff i) hres_i.1 hres_i.2
          omega
      · have h1 : farTotalWords [Asm.addi rx AbiReg.zero 0#12] = 1 := rfl; omega
    · split
      · simp [farTotalWords]
      · split
        · next hi =>
          have hres_i := hres i hi
          split
          · have hs := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp (resReg i) AbiReg.t0
              (fl.varSlotOff x) hslot.1 hslot.2
            omega
          · rw [farTotalWords_append]
            have hl := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.gp AbiReg.t2
              (tab.resOff i) hres_i.1 hres_i.2
            have hs := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.t1 AbiReg.t2
              (fl.varSlotOff x) hslot.1 hslot.2
            omega
        · have hs := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.zero AbiReg.t0
            (fl.varSlotOff x) hslot.1 hslot.2
          omega
  · have hsum : ∀ (ps : List (Var × Nat)) (acc : Nat),
        ps.foldl (fun a _ => a + 12) acc = acc + 12 * ps.length := by
      intro ps; induction ps with | nil => simp | cons _ ps ih => intro acc; simp [ih]; omega
    rw [hsum, Nat.zero_add, List.length_zipIdx]; exact Nat.le_refl _

private theorem compileStorePairR_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab)
    (fl : FrameLayout) (hfl : fl.protectedSlots ≤ 11 ∧ fl.spilledVars.length ≤ fl.nlocals)
    (hnl : fl.nlocals < 100000) (i e : Expr)
    (hi_tmp : maxTempsExpr i < 100000) (he_tmp : 1 + maxTempsExpr e < 100000)
    (hi_ok : exprOkConst0B tab fl.nlocals i = true) (he_ok : exprOkConst0B tab fl.nlocals e = true) :
    farTotalWords (compileStorePairR tab fl i e).1 ≤ exprBound32 i + exprBound32 e + 12 := by
  dsimp only [compileStorePairR]
  cases exprReg? fl.alloc i with
  | some _ =>
    cases exprReg? fl.alloc e with
    | some _ => simp [farTotalWords]
    | none => dsimp only; have he := compileETo_farTotalWords_le ht fl hfl hnl e 0 AbiReg.a0 (by omega) he_ok; omega
  | none =>
    cases exprReg? fl.alloc e with
    | some _ => dsimp only; have hi := compileETo_farTotalWords_le ht fl hfl hnl i 0 AbiReg.a0 (by omega) hi_ok; omega
    | none =>
      cases hsi : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 i with
      | some ci =>
        rw [farTotalWords_append]
        have he := compileETo_farTotalWords_le ht fl hfl hnl e 0 AbiReg.a0 (by omega) he_ok
        have hi := emitSimpleExprR_farTotalWords_le ht hfl hnl hi_ok hsi
        omega
      | none =>
        cases hse : emitSimpleExprR tab fl AbiReg.a0 AbiReg.t1 e with
        | some ce =>
          simp only [farTotalWords_append]
          have hi := compileETo_farTotalWords_le ht fl hfl hnl i 0 AbiReg.a0 (by omega) hi_ok
          have he := emitSimpleExprR_farTotalWords_le ht hfl hnl he_ok hse
          have hmv : farTotalWords [Asm.mv AbiReg.t0 AbiReg.a0] = 1 := rfl
          omega
        | none =>
          have hi := compileETo_farTotalWords_le ht fl hfl hnl i 0 AbiReg.a0 (by omega) hi_ok
          have he := compileETo_farTotalWords_le ht fl hfl hnl e 1 AbiReg.a0 (by omega) he_ok
          have hts := tempSlotOff_32 hfl hnl (by omega : 0 < 200000)
          have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 0) hts.1 hts.2
          have hld := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 0) hts.1 hts.2
          simp only [farTotalWords_append]; omega

private theorem compileTierStoreTripleR_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab)
    (fl : FrameLayout) (hfl : fl.protectedSlots ≤ 11 ∧ fl.spilledVars.length ≤ fl.nlocals)
    (hnl : fl.nlocals < 100000) (t i e : Expr)
    (ht_tmp : maxTempsExpr t < 100000) (hi_tmp : 1 + maxTempsExpr i < 100000)
    (he_tmp : 2 + maxTempsExpr e < 100000)
    (ht_ok : exprOkConst0B tab fl.nlocals t = true)
    (hi_ok : exprOkConst0B tab fl.nlocals i = true)
    (he_ok : exprOkConst0B tab fl.nlocals e = true) :
    farTotalWords (compileTierStoreTripleR tab fl t i e).1 ≤
      exprBound32 t + exprBound32 i + exprBound32 e + 24 := by
  dsimp only [compileTierStoreTripleR]
  have hts0 := tempSlotOff_32 hfl hnl (by omega : 0 < 200000)
  have hts1 := tempSlotOff_32 hfl hnl (by omega : 1 < 200000)
  cases exprReg? fl.alloc t with
  | some _ =>
    cases exprReg? fl.alloc i with
    | some _ =>
      cases exprReg? fl.alloc e with
      | some _ => simp [farTotalWords]
      | none => dsimp only; have he := compileETo_farTotalWords_le ht fl hfl hnl e 0 AbiReg.a0 (by omega) he_ok; omega
    | none =>
      cases exprReg? fl.alloc e with
      | some _ => dsimp only; have hi := compileETo_farTotalWords_le ht fl hfl hnl i 0 AbiReg.a0 (by omega) hi_ok; omega
      | none =>
        cases hsi : emitSimpleExprR tab fl AbiReg.t3 AbiReg.t4 i with
        | some ci =>
          have he := compileETo_farTotalWords_le ht fl hfl hnl e 0 AbiReg.a0 (by omega) he_ok
          have hi := emitSimpleExprR_farTotalWords_le ht hfl hnl hi_ok hsi
          rw [farTotalWords_append]; omega
        | none =>
          cases hse : emitSimpleExprR tab fl AbiReg.a0 AbiReg.t4 e with
          | some ce =>
            have hi := compileETo_farTotalWords_le ht fl hfl hnl i 0 AbiReg.a0 (by omega) hi_ok
            have he := emitSimpleExprR_farTotalWords_le ht hfl hnl he_ok hse
            have hmv : farTotalWords [Asm.mv AbiReg.t3 AbiReg.a0] = 1 := rfl
            simp only [farTotalWords_append]; omega
          | none =>
            have hi := compileETo_farTotalWords_le ht fl hfl hnl i 0 AbiReg.a0 (by omega) hi_ok
            have he := compileETo_farTotalWords_le ht fl hfl hnl e 1 AbiReg.a0 (by omega) he_ok
            have hs0 := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 0) hts0.1 hts0.2
            have hl0 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t3 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 0) hts0.1 hts0.2
            simp only [farTotalWords_append]; omega
  | none =>
    cases hst : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 t with
    | some ct =>
      have ht' := emitSimpleExprR_farTotalWords_le ht hfl hnl ht_ok hst
      cases hsi : emitSimpleExprR tab fl AbiReg.t3 AbiReg.t4 i with
      | some ci =>
        have he := compileETo_farTotalWords_le ht fl hfl hnl e 0 AbiReg.a0 (by omega) he_ok
        have hi := emitSimpleExprR_farTotalWords_le ht hfl hnl hi_ok hsi
        simp only [farTotalWords_append]; omega
      | none =>
        cases hse : emitSimpleExprR tab fl AbiReg.a0 AbiReg.t4 e with
        | some ce =>
          have hi := compileETo_farTotalWords_le ht fl hfl hnl i 0 AbiReg.a0 (by omega) hi_ok
          have he := emitSimpleExprR_farTotalWords_le ht hfl hnl he_ok hse
          have hmv : farTotalWords [Asm.mv AbiReg.t3 AbiReg.a0] = 1 := rfl
          simp only [farTotalWords_append]; omega
        | none =>
          have hi := compileETo_farTotalWords_le ht fl hfl hnl i 0 AbiReg.a0 (by omega) hi_ok
          have he := compileETo_farTotalWords_le ht fl hfl hnl e 1 AbiReg.a0 (by omega) he_ok
          have hs0 := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 0) hts0.1 hts0.2
          have hl0 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t3 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 0) hts0.1 hts0.2
          simp only [farTotalWords_append]; omega
    | none =>
      have ht0 := compileETo_farTotalWords_le ht fl hfl hnl t 0 AbiReg.a0 (by omega) ht_ok
      have hi := compileETo_farTotalWords_le ht fl hfl hnl i 1 AbiReg.a0 (by omega) hi_ok
      have he := compileETo_farTotalWords_le ht fl hfl hnl e 2 AbiReg.a0 (by omega) he_ok
      have hs0 := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 0) hts0.1 hts0.2
      have hs1 := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 1) hts1.1 hts1.2
      have hl0 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 0) hts0.1 hts0.2
      have hl1 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t3 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 1) hts1.1 hts1.2
      simp only [farTotalWords_append]; omega

private theorem maxTempsExpr_mem_le_maxTempsExprs {es : List Expr} {e : Expr} (he : e ∈ es) :
    maxTempsExpr e ≤ maxTempsExprs es := by
  have hzip : ∀ (xs : List Expr) (start : Nat) (x : Expr), x ∈ xs → ∃ i, (x, i) ∈ xs.zipIdx start := by
    intro xs
    induction xs with
    | nil => intro _ _ h; cases h
    | cons a tl ih =>
      intro start x hx
      rcases List.mem_cons.mp hx with rfl | htl
      · exact ⟨start, by simp⟩
      · obtain ⟨i, hi⟩ := ih (start + 1) x htl
        exact ⟨i, by simp [hi]⟩
  obtain ⟨i, hi⟩ := hzip es 0 e he
  have hle := foldl_max_zipIdx es 0 0 e i hi
  dsimp only [maxTempsExprs]
  omega

private theorem compileEvalRevToRegs_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab)
    (fl : FrameLayout) (hfl : fl.protectedSlots ≤ 11 ∧ fl.spilledVars.length ≤ fl.nlocals)
    (hnl : fl.nlocals < 100000) :
    ∀ (es : List Expr) (idx : Nat),
      (∀ e ∈ es, maxTempsExpr e < 100000) →
      es.all (exprOkConst0B tab fl.nlocals) = true →
      farTotalWords (compileEvalRevToRegs tab fl idx es) ≤ exprsBound32 es := by
  intro es
  induction es with
  | nil => intro _ _ _; simp [compileEvalRevToRegs, farTotalWords]
  | cons e rest ih =>
    intro idx htmp hok
    simp only [List.all_cons, Bool.and_eq_true] at hok
    have he := compileETo_farTotalWords_le ht fl hfl hnl e 0 (resReg idx)
      (by have := htmp e (by simp); omega) hok.1
    have hrest := ih (idx + 1) (fun x hx => htmp x (List.mem_cons_of_mem _ hx)) hok.2
    simp only [compileEvalRevToRegs, farTotalWords_append, exprsBound32]
    omega

private theorem compileRetR_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab)
    (fl : FrameLayout) (hfl : fl.protectedSlots ≤ 11 ∧ fl.spilledVars.length ≤ fl.nlocals)
    (hnl : fl.nlocals < 100000) (retLbl : String) (isTail : Bool) (es : List Expr)
    (htmp : maxTempsExprs es + fl.nlocals < 100000)
    (hok : es.all (exprOkConst0B tab fl.nlocals) = true) :
    farTotalWords (compileRetR tab fl retLbl isTail es) ≤ exprsBound32 es + 12 * tab.nres + 4 := by
  have hj : farTotalWords (if isTail = true then []
      else if (fl.isLeaf && (fl.frameSlots == 0)) = true then [Asm.ret]
      else [Asm.j retLbl]) ≤ 4 := by
    split
    · exact Nat.zero_le 4
    · split
      · have h1 : farTotalWords [Asm.ret] = 1 := rfl; omega
      · exact Nat.le_refl 4
  cases es with
  | nil =>
    have hcopy := copyTempsToResultsR_farTotalWords_le ht fl hfl hnl 0 0 (by have := ht.nres_le; omega)
    simp only [compileRetR, farTotalWords_append, exprsBound32]; omega
  | cons e rest =>
    cases rest with
    | nil =>
      simp only [List.all_cons, List.all_nil, Bool.and_true] at hok
      have he_lt : 0 + maxTempsExpr e < 100000 := by
        simp only [maxTempsExprs, List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil] at htmp; omega
      have he := compileETo_farTotalWords_le ht fl hfl hnl e 0 AbiReg.a0 he_lt hok
      simp only [compileRetR, farTotalWords_append, exprsBound32]; omega
    | cons e2 rs =>
      dsimp only [compileRetR]
      split
      · have hrev := compileEvalRevToRegs_farTotalWords_le ht fl hfl hnl (e :: e2 :: rs) 0
          (fun x hx => Nat.lt_of_le_of_lt (maxTempsExpr_mem_le_maxTempsExprs hx) (by omega)) hok
        simp only [farTotalWords_append]; omega
      · have hes := compileEvalExprsToTempsR_farTotalWords_le ht fl hfl hnl (e :: e2 :: rs) 0 (by omega) hok
        have hcopy := copyTempsToResultsR_farTotalWords_le ht fl hfl hnl 0 (e :: e2 :: rs).length
          (by have := ht.nres_le; omega)
        simp only [farTotalWords_append]; omega

private theorem compileCallArgsR_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab)
    (fl : FrameLayout) (hfl : fl.protectedSlots ≤ 11 ∧ fl.spilledVars.length ≤ fl.nlocals)
    (hnl : fl.nlocals < 100000) (args : List Expr)
    (htmp : maxTempsExprs args + fl.nlocals < 100000)
    (hok : args.all (exprOkConst0B tab fl.nlocals) = true) :
    farTotalWords (compileCallArgsR tab fl args) ≤
      exprsBound32 args + 11 + 6 * min args.length maxRes := by
  have hbud : farTotalWords [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
      Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] = 6 := rfl
  dsimp only [compileCallArgsR]
  split
  · have hrev := compileEvalRevToRegs_farTotalWords_le ht fl hfl hnl args 0
      (fun x hx => Nat.lt_of_le_of_lt (maxTempsExpr_mem_le_maxTempsExprs hx) (by omega)) hok
    simp only [farTotalWords_append]; omega
  · have hargs := compileEvalExprsToTempsR_farTotalWords_le ht fl hfl hnl args 0 (by omega) hok
    have hlds : farTotalWords ((List.range (min args.length maxRes)).flatMap fun i =>
        loadMemOff .ld (resReg i) AbiReg.sp AbiReg.t0 (fl.tempSlotOff i)) ≤
        6 * min args.length maxRes := by
      refine Nat.le_trans (farTotalWords_flatMap_le _ _ (fun _ => 6) (fun i hi => ?_)) ?_
      · simp only [List.mem_range] at hi
        have hts := tempSlotOff_32 hfl hnl (by dsimp [maxRes] at hi; omega : i < 200000)
        exact loadMemOff_farTotalWords_le_32 .ld (resReg i) AbiReg.sp AbiReg.t0
          (fl.tempSlotOff i) hts.1 hts.2
      · have hsum : ∀ (xs : List Nat) (acc : Nat),
            xs.foldl (fun a _ => a + 6) acc = acc + 6 * xs.length := by
          intro xs; induction xs with | nil => simp | cons _ xs ih => intro acc; simp [ih]; omega
        rw [hsum, Nat.zero_add, List.length_range]; exact Nat.le_refl _
    have hptr : farTotalWords (if maxRes < args.length then
        addImmOff AbiReg.t0 AbiReg.sp AbiReg.t2 (fl.tempSlotOff maxRes) else []) ≤ 5 := by
      split
      · have hts := tempSlotOff_32 hfl hnl (by dsimp [maxRes]; omega : maxRes < 200000)
        exact addImmOff_farTotalWords_le_32 AbiReg.t0 AbiReg.sp AbiReg.t2
          (fl.tempSlotOff maxRes) hts.1 hts.2
      · simp [farTotalWords]
    simp only [farTotalWords_append]; omega

private theorem framePopItems_farTotalWords_le (fl : FrameLayout)
    (hsaved : fl.savedRegs.length ≤ 10)
    (hfb : 0 ≤ fl.frameBytes ∧ fl.frameBytes < 2 ^ 31) :
    farTotalWords (framePopItems fl) ≤ 16 := by
  dsimp only [framePopItems]
  split
  · simp [farTotalWords]
  · simp only [farTotalWords_append]
    have hrst := restoreCalleeRegs_farTotalWords_le fl hsaved
    have hra : farTotalWords (if fl.isLeaf = true then [] else [Asm.ld AbiReg.ra AbiReg.sp 0#12]) ≤ 1 := by
      split
      · exact Nat.zero_le 1
      · exact Nat.le_refl 1
    have hadd := addImmOff_farTotalWords_le_32 AbiReg.sp AbiReg.sp AbiReg.t0 fl.frameBytes hfb.1 hfb.2
    omega

private theorem compileSR_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab)
    (fl : FrameLayout) (hfl : fl.protectedSlots ≤ 11 ∧ fl.spilledVars.length ≤ fl.nlocals)
    (hsaved : fl.savedRegs.length ≤ 10)
    (hfb : 0 ≤ fl.frameBytes ∧ fl.frameBytes < 2 ^ 31)
    (hnl : fl.nlocals < 100000) (pfx retLbl : String) :
    ∀ (s : Stmt) (inLoop : Bool) (lblId : Nat) (brkLbl : Option String) (isTail : Bool) (p : Prog),
      maxTempsStmt s + fl.nlocals < 100000 →
      stmtOkConst0B tab p fl.nlocals inLoop s = true →
      farTotalWords (compileSR tab fl pfx lblId brkLbl retLbl isTail s).1 ≤ stmtBound32 tab.nres s := by
  intro s
  have ⟨hlen8, hbase8, hlen64, hbase64, hglob, _, hrom⟩ := tab_offsets_32 ht
  induction s with
  | skip => intro _ _ _ _ _ _ _; exact Nat.le_refl _
  | set x e =>
    intro _ _ _ _ _ htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true, decide_eq_true_eq] at hok
    have hslot := varSlotOff_32 hfl hnl x
    dsimp only [compileSR, stmtBound32]
    split
    · next rx _ =>
      have he := compileETo_farTotalWords_le ht fl hfl hnl e 0 rx (by omega) hok.2
      omega
    · split
      · split
        · simp [farTotalWords]
        · have he := compileETo_farTotalWords_le ht fl hfl hnl e 0 AbiReg.a0 (by omega) hok.2
          omega
      · cases exprReg? fl.alloc e with
        | some r =>
          dsimp only
          have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp r AbiReg.t0 (fl.varSlotOff x) hslot.1 hslot.2
          omega
        | none =>
          have he := compileETo_farTotalWords_le ht fl hfl hnl e 0 AbiReg.a0 (by omega) hok.2
          have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.varSlotOff x) hslot.1 hslot.2
          rw [farTotalWords_append]; omega
  | gset g e =>
    intro _ _ _ _ _ htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true, decide_eq_true_eq] at hok
    dsimp only [compileSR, stmtBound32]
    cases exprReg? fl.alloc e with
    | some r =>
      dsimp only
      have hst := storeMemOffGp_farTotalWords_le_32 fl.useT5Gp .sd r AbiReg.t0 (tab.globOff g) (hglob g hok.1).1 (hglob g hok.1).2
      omega
    | none =>
      have he := compileETo_farTotalWords_le ht fl hfl hnl e 0 AbiReg.a0 (by omega) hok.2
      have hst := storeMemOffGp_farTotalWords_le_32 fl.useT5Gp .sd AbiReg.a0 AbiReg.t0 (tab.globOff g) (hglob g hok.1).1 (hglob g hok.1).2
      rw [farTotalWords_append]; omega
  | st8 _ _ _ => intro _ _ _ _ _ _ _; exact Nat.le_refl _
  | st64 a i e =>
    intro _ _ _ _ _ htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true] at hok
    have hp := compileStorePairR_farTotalWords_le ht fl hfl hnl i e (by omega) (by omega) hok.1.2 hok.2
    rcases hpair : compileStorePairR tab fl i e with ⟨cp, ri, re⟩
    rw [hpair] at hp; dsimp only at hp
    have hl1 := loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld AbiReg.t1 AbiReg.t2
      (tab.len64 (TieredArray.t0 a)) (hlen64 _).1 (hlen64 _).2
    have hl2 := loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld AbiReg.t1 AbiReg.t2
      (tab.base64 (TieredArray.t0 a)) (hbase64 _).1 (hbase64 _).2
    have hbr : farTotalWords [Asm.bgeu ri AbiReg.t1 errLabel] = 5 := rfl
    have htail := st64Tail_farTotalWords_le re ri AbiReg.t2 i
    simp only [compileSR, hpair, farTotalWords_append, stmtBound32]; omega
  | st64t a t i e =>
    intro _ _ _ _ _ htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true] at hok
    dsimp only [compileSR, stmtBound32]
    cases t.constVal? with
    | some wt =>
      dsimp only
      have hp := compileStorePairR_farTotalWords_le ht fl hfl hnl i e (by omega) (by omega) hok.1.2 hok.2
      rcases hpair : compileStorePairR tab fl i e with ⟨cp, ri, re⟩
      rw [hpair] at hp; dsimp only at hp
      have hl1 := loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld AbiReg.t1 AbiReg.t2
        (tab.len64 (tierA a wt)) (hlen64 _).1 (hlen64 _).2
      have hl2 := loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld AbiReg.t1 AbiReg.t2
        (tab.base64 (tierA a wt)) (hbase64 _).1 (hbase64 _).2
      have hbr : farTotalWords [Asm.bgeu ri AbiReg.t1 errLabel] = 5 := rfl
      have htail := st64Tail_farTotalWords_le re ri AbiReg.t2 i
      dsimp only
      simp only [farTotalWords_append]; omega
    | none =>
      dsimp only
      have htr := compileTierStoreTripleR_farTotalWords_le ht fl hfl hnl t i e
        (by omega) (by omega) (by omega) hok.1.1.2 hok.1.2 hok.2
      rcases htp : compileTierStoreTripleR tab fl t i e with ⟨cp, rt, ri, re⟩
      rw [htp] at htr; dsimp only at htr
      have hl2 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t2 AbiReg.t1 AbiReg.t4
        (tab.len64 (TieredArray.t0 a)) (hlen64 _).1 (hlen64 _).2
      have hl3 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.t1 AbiReg.t4
        (tab.base64 (TieredArray.t0 a)) (hbase64 _).1 (hbase64 _).2
      have h1 : farTotalWords [Asm.andi AbiReg.t0 rt 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
          Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] = 3 := rfl
      have h2 : farTotalWords [Asm.bgeu ri AbiReg.t2 errLabel] = 5 := rfl
      have h3 := st64Tail_farTotalWords_le re ri AbiReg.t4 i
      dsimp only
      simp only [farTotalWords_append]; omega
  | st32t a t i e =>
    intro _ _ _ _ _ htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true] at hok
    dsimp only [compileSR, stmtBound32]
    cases t.constVal? with
    | some wt =>
      dsimp only
      have hp := compileStorePairR_farTotalWords_le ht fl hfl hnl i e (by omega) (by omega) hok.1.2 hok.2
      rcases hpair : compileStorePairR tab fl i e with ⟨cp, ri, re⟩
      rw [hpair] at hp; dsimp only at hp
      have hl1 := loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld AbiReg.t1 AbiReg.t2
        (tab.len64 (tierA a wt)) (hlen64 _).1 (hlen64 _).2
      have hl2 := loadMemOffGp_farTotalWords_le_32 fl.useT5Gp .ld AbiReg.t1 AbiReg.t2
        (tab.base64 (tierA a wt)) (hbase64 _).1 (hbase64 _).2
      have hbr : farTotalWords [Asm.srli AbiReg.t2 ri 1#6, Asm.bgeu AbiReg.t2 AbiReg.t1 errLabel] = 6 := rfl
      have htail := st32tTail_farTotalWords_le re ri AbiReg.t2 i
      dsimp only
      simp only [farTotalWords_append]; omega
    | none =>
      dsimp only
      have htr := compileTierStoreTripleR_farTotalWords_le ht fl hfl hnl t i e
        (by omega) (by omega) (by omega) hok.1.1.2 hok.1.2 hok.2
      rcases htp : compileTierStoreTripleR tab fl t i e with ⟨cp, rt, ri, re⟩
      rw [htp] at htr; dsimp only at htr
      have hl2 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t2 AbiReg.t1 AbiReg.t4
        (tab.len64 (TieredArray.t0 a)) (hlen64 _).1 (hlen64 _).2
      have hl3 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.t1 AbiReg.t4
        (tab.base64 (TieredArray.t0 a)) (hbase64 _).1 (hbase64 _).2
      have h1 : farTotalWords [Asm.andi AbiReg.t0 rt 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
          Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0] = 3 := rfl
      have h2 : farTotalWords [Asm.srli AbiReg.t4 ri 1#6, Asm.bgeu AbiReg.t4 AbiReg.t2 errLabel] = 6 := rfl
      have h3 := st32tTail_farTotalWords_le re ri AbiReg.t4 i
      dsimp only
      simp only [farTotalWords_append]; omega
  | seq s1 s2 ih1 ih2 =>
    intro inLoop lblId brkLbl isTail p htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true] at hok
    dsimp only [compileSR, stmtBound32]
    cases hmatch : tailCallRetMatch tab s1 s2 with
    | some v =>
      rcases v with ⟨xs, f, args, es⟩
      obtain ⟨rfl, rfl, htc⟩ := tailCallRetMatch_spec hmatch
      simp only [maxTempsStmt] at htmp
      simp only [stmtOkConst0B, Bool.and_eq_true] at hok
      simp only [isTailCallRet, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_true_eq] at htc
      have hxsPos : 1 ≤ xs.length := by
        cases xs with
        | nil => simp at htc
        | cons _ _ => simp
      have hargs := compileCallArgsR_farTotalWords_le ht fl hfl hnl args (by omega) hok.1.2
      have hpop := framePopItems_farTotalWords_le fl hsaved hfb
      have hj : farTotalWords [Asm.j (fnLabel f)] = 4 := rfl
      simp only [farTotalWords_append, stmtBound32]; omega
    | none =>
      have h1 := ih1 inLoop lblId brkLbl false p (by omega) hok.1
      have h2 := ih2 inLoop (compileSR tab fl pfx lblId brkLbl retLbl false s1).2 brkLbl isTail p (by omega) hok.2
      simp only [farTotalWords_append]; omega
  | ite cond s1 s2 ih1 ih2 =>
    intro inLoop lblId brkLbl isTail p htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true] at hok
    by_cases hs2 : s2 = .skip
    · subst hs2
      dsimp only [compileSR, stmtBound32]
      split
      · have hc := compileCR_farTotalWords_le ht fl hfl 0 hnl pfx cond lblId true (toString pfx ++ toString "_abort0stub") (by omega) hok.1.1
        omega
      · let endLbl := toString pfx ++ toString "_endif_" ++ toString lblId
        let id1 := (compileCR tab fl 0 pfx (lblId + 1) cond false endLbl).2
        have hc := compileCR_farTotalWords_le ht fl hfl 0 hnl pfx cond (lblId + 1) false endLbl (by omega) hok.1.1
        have h1 := ih1 inLoop id1 brkLbl false p (by omega) hok.1.2
        have he : farTotalWords [Asm.lbl endLbl] = 0 := rfl
        dsimp only [endLbl, id1] at hc h1 he
        simp only [farTotalWords_append]; omega
    by_cases hs1 : s1 = .skip
    · subst hs1
      have hce : compileSR tab fl pfx lblId brkLbl retLbl isTail (.ite cond .skip s2) =
          if isAbort0Stmt s2 then
            compileCR tab fl 0 pfx lblId cond false s!"{pfx}_abort0stub"
          else
            let endLbl := s!"{pfx}_endif_{lblId}"
            let (cc, id1) := compileCR tab fl 0 pfx (lblId + 1) cond true endLbl
            let (c2, id2) := compileSR tab fl pfx id1 brkLbl retLbl false s2
            (cc ++ c2 ++ [Asm.lbl endLbl], id2) := by cases s2 with | skip => contradiction | _ => rfl
      rw [hce]
      split
      · have hc := compileCR_farTotalWords_le ht fl hfl 0 hnl pfx cond lblId false s!"{pfx}_abort0stub" (by omega) hok.1.1
        dsimp only [stmtBound32]; omega
      · dsimp only
        have hc := compileCR_farTotalWords_le ht fl hfl 0 hnl pfx cond (lblId + 1) true s!"{pfx}_endif_{lblId}" (by omega) hok.1.1
        have h2 := ih2 inLoop (compileCR tab fl 0 pfx (lblId + 1) cond true s!"{pfx}_endif_{lblId}").2 brkLbl false p (by omega) hok.2
        have he : farTotalWords [Asm.lbl s!"{pfx}_endif_{lblId}"] = 0 := rfl
        simp only [farTotalWords_append, stmtBound32]; omega
    have hceGen : (compileSR tab fl pfx lblId brkLbl retLbl isTail (.ite cond s1 s2)).1 =
        (compileCR tab fl 0 pfx (lblId + 1) cond false (s!"{pfx}_else_{lblId}")).1 ++
        (compileSR tab fl pfx (compileCR tab fl 0 pfx (lblId + 1) cond false (s!"{pfx}_else_{lblId}")).2 brkLbl retLbl false s1).1 ++
        (if stmtMayFallthrough s1 then [Asm.j s!"{pfx}_endif_{lblId}"] else []) ++
        [Asm.lbl s!"{pfx}_else_{lblId}"] ++
        (compileSR tab fl pfx (compileSR tab fl pfx (compileCR tab fl 0 pfx (lblId + 1) cond false (s!"{pfx}_else_{lblId}")).2 brkLbl retLbl false s1).2 brkLbl retLbl isTail s2).1 ++
        [Asm.lbl s!"{pfx}_endif_{lblId}"] := by
      cases s2 with | skip => contradiction | _ => cases s1 with | skip => contradiction | _ => rfl
    rw [hceGen]
    have hc := compileCR_farTotalWords_le ht fl hfl 0 hnl pfx cond (lblId + 1) false s!"{pfx}_else_{lblId}" (by omega) hok.1.1
    have h1 := ih1 inLoop (compileCR tab fl 0 pfx (lblId + 1) cond false s!"{pfx}_else_{lblId}").2 brkLbl false p (by omega) hok.1.2
    have h2 := ih2 inLoop (compileSR tab fl pfx (compileCR tab fl 0 pfx (lblId + 1) cond false s!"{pfx}_else_{lblId}").2 brkLbl retLbl false s1).2 brkLbl isTail p (by omega) hok.2
    have hj : farTotalWords (if stmtMayFallthrough s1 = true then [Asm.j s!"{pfx}_endif_{lblId}"] else []) ≤ 4 := by
      split
      · exact Nat.le_refl 4
      · exact Nat.zero_le 4
    have hel : farTotalWords [Asm.lbl s!"{pfx}_else_{lblId}"] = 0 := rfl
    have he : farTotalWords [Asm.lbl s!"{pfx}_endif_{lblId}"] = 0 := rfl
    simp only [farTotalWords_append, stmtBound32]; omega
  | «while» cond body ih =>
    intro _ lblId _ _ p htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true] at hok
    let loopLbl := toString pfx ++ toString "_while_" ++ toString lblId
    let endLbl := toString pfx ++ toString "_endw_" ++ toString lblId
    let id1 := (compileCR tab fl 0 pfx (lblId + 1) cond false endLbl).2
    have hc := compileCR_farTotalWords_le ht fl hfl 0 hnl pfx cond (lblId + 1) false endLbl (by omega) hok.1
    have hb := ih true id1 (some endLbl) false p (by omega) hok.2
    have h1 : farTotalWords [Asm.lbl loopLbl] = 0 := rfl
    have h2 : farTotalWords [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
        Asm.addi AbiReg.s0 AbiReg.s0 (-1#12), Asm.j loopLbl, Asm.lbl endLbl] = 10 := rfl
    dsimp only [loopLbl, endLbl, id1] at hc hb h1 h2
    simp only [compileSR, farTotalWords_append, stmtBound32]; omega
  | brk =>
    intro _ _ brkLbl _ _ _ _
    have hj : farTotalWords [Asm.j (brkLbl.getD retLbl)] = 4 := rfl
    dsimp only [compileSR, stmtBound32]; omega
  | ret es =>
    intro _ _ _ isTail _ htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact compileRetR_farTotalWords_le ht fl hfl hnl retLbl isTail es htmp hok.2
  | «call» xs f args =>
    intro _ _ _ _ _ htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true] at hok
    have hargs := compileCallArgsR_farTotalWords_le ht fl hfl hnl args htmp hok.2
    have hcopy := copyResultsToLocalsR_farTotalWords_le ht fl hfl hnl xs
    have hcall : farTotalWords [Asm.call (fnLabel f)] = 4 := rfl
    have ht5 : farTotalWords (if fl.useT5Gp = true then [Asm.addi AbiReg.t5 AbiReg.gp 2047#12] else []) ≤ 1 := by
      split
      · exact Nat.le_refl 1
      · exact Nat.zero_le 1
    simp only [compileSR, farTotalWords_append, stmtBound32]; omega
  | abort e =>
    intro _ _ _ _ _ htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B] at hok
    dsimp only [compileSR, stmtBound32]
    split
    · dsimp only
      have hj : farTotalWords [Asm.j (toString pfx ++ toString "_abort0stub")] = 4 := rfl; omega
    · dsimp only
      have he := compileETo_farTotalWords_le ht fl hfl hnl e 0 AbiReg.a0 (by omega) hok
      have hj : farTotalWords [Asm.j abortLabel] = 4 := rfl
      simp only [farTotalWords_append]; omega
  | copy64 d di src si n =>
    intro _ lblId _ _ _ htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true] at hok
    have hts0 := tempSlotOff_32 hfl hnl (by omega : 0 < 200000)
    have hts1 := tempSlotOff_32 hfl hnl (by omega : 1 < 200000)
    have hts2 := tempSlotOff_32 hfl hnl (by omega : 2 < 200000)
    have hts3 := tempSlotOff_32 hfl hnl (by omega : 3 < 200000)
    have hts4 := tempSlotOff_32 hfl hnl (by omega : 4 < 200000)
    have hd : farTotalWords (evalWArrTierToTempR tab fl 0 d).2 ≤ warrBound32 d := by
      cases d with
      | plain a =>
        dsimp only [evalWArrTierToTempR, warrBound32]
        exact storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.zero AbiReg.t0 (fl.tempSlotOff 0) hts0.1 hts0.2
      | tier a t =>
        dsimp only at htmp
        have hok_t : exprOkConst0B tab fl.nlocals t = true := by
          have := hok.1.1.1.1; simp only [warrOkConst0B, Bool.and_eq_true] at this; exact this.2
        dsimp only [evalWArrTierToTempR, warrBound32]
        cases exprReg? fl.alloc t with
        | some rt =>
          dsimp only
          have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp rt AbiReg.t0 (fl.tempSlotOff 0) hts0.1 hts0.2
          omega
        | none =>
          have het := compileETo_farTotalWords_le ht fl hfl hnl t 0 AbiReg.a0 (by omega) hok_t
          have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 0) hts0.1 hts0.2
          rw [farTotalWords_append]; omega
    have hdi := compileETo_farTotalWords_le ht fl hfl hnl di 1 AbiReg.a0 (by omega) hok.1.1.1.2
    have hs : farTotalWords (evalWArrTierToTempR tab fl 2 src).2 ≤ warrBound32 src := by
      cases src with
      | plain a =>
        dsimp only [evalWArrTierToTempR, warrBound32]
        exact storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.zero AbiReg.t0 (fl.tempSlotOff 2) hts2.1 hts2.2
      | tier a t =>
        dsimp only at htmp
        have hok_t : exprOkConst0B tab fl.nlocals t = true := by
          have := hok.1.1.2; simp only [warrOkConst0B, Bool.and_eq_true] at this; exact this.2
        dsimp only [evalWArrTierToTempR, warrBound32]
        cases exprReg? fl.alloc t with
        | some rt =>
          dsimp only
          have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp rt AbiReg.t0 (fl.tempSlotOff 2) hts2.1 hts2.2
          omega
        | none =>
          have het := compileETo_farTotalWords_le ht fl hfl hnl t 2 AbiReg.a0 (by omega) hok_t
          have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 2) hts2.1 hts2.2
          rw [farTotalWords_append]; omega
    have hsi := compileETo_farTotalWords_le ht fl hfl hnl si 3 AbiReg.a0 (by omega) hok.1.2
    have hn := compileETo_farTotalWords_le ht fl hfl hnl n 4 AbiReg.a0 (by omega) hok.2
    have hs1 := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 1) hts1.1 hts1.2
    have hs3 := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 3) hts3.1 hts3.2
    have hs4 := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 4) hts4.1 hts4.2
    have hl0 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 0) hts0.1 hts0.2
    have hl1 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 1) hts1.1 hts1.2
    have hl4 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t3 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 4) hts4.1 hts4.2
    have hl2 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.sp AbiReg.t2 (fl.tempSlotOff 2) hts2.1 hts2.2
    have hl3 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t2 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 3) hts3.1 hts3.2
    have hdl := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.t5 AbiReg.t6
      (tab.len64 (TieredArray.t0 (evalWArrTierToTempR tab fl 0 d).1)) (hlen64 _).1 (hlen64 _).2
    have hdb := loadMemOff_farTotalWords_le_32 .ld AbiReg.t5 AbiReg.t5 AbiReg.t6
      (tab.base64 (TieredArray.t0 (evalWArrTierToTempR tab fl 0 d).1)) (hbase64 _).1 (hbase64 _).2
    have hsl := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.t5 AbiReg.t6
      (tab.len64 (TieredArray.t0 (evalWArrTierToTempR tab fl 2 src).1)) (hlen64 _).1 (hlen64 _).2
    have hsb := loadMemOff_farTotalWords_le_32 .ld AbiReg.t5 AbiReg.t5 AbiReg.t6
      (tab.base64 (TieredArray.t0 (evalWArrTierToTempR tab fl 2 src).1)) (hbase64 _).1 (hbase64 _).2
    have hm1 : farTotalWords [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
        Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] = 3 := rfl
    have hm2 : farTotalWords [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3,
        Asm.bltu AbiReg.t0 AbiReg.t1 errLabel] = 11 := rfl
    have hm3 : farTotalWords [Asm.slli AbiReg.t1 AbiReg.t1 3#6, Asm.add AbiReg.t1 AbiReg.t5 AbiReg.t1] = 2 := rfl
    have hm4 : farTotalWords [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
        Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] = 3 := rfl
    have hm5 : farTotalWords [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3,
        Asm.bltu AbiReg.t0 AbiReg.t2 errLabel] = 11 := rfl
    have hm6 : ∀ l1 l2, farTotalWords [Asm.slli AbiReg.t2 AbiReg.t2 3#6, Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2,
        Asm.lbl l1, Asm.beq AbiReg.t3 AbiReg.zero l2,
        Asm.ld AbiReg.t4 AbiReg.t2 0#12, Asm.sd AbiReg.t1 AbiReg.t4 0#12,
        Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 8#12,
        Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j l1, Asm.lbl l2] = 16 := fun _ _ => rfl
    simp only [compileSR, farTotalWords_append, stmtBound32]
    rw [hm6 _ _]; omega
  | copy8w d di src si n =>
    intro _ lblId _ _ _ htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true] at hok
    have hts0 := tempSlotOff_32 hfl hnl (by omega : 0 < 200000)
    have hts1 := tempSlotOff_32 hfl hnl (by omega : 1 < 200000)
    have hts3 := tempSlotOff_32 hfl hnl (by omega : 3 < 200000)
    have hts4 := tempSlotOff_32 hfl hnl (by omega : 4 < 200000)
    have hd : farTotalWords (evalWArrTierToTempR tab fl 0 d).2 ≤ warrBound32 d := by
      cases d with
      | plain a =>
        dsimp only [evalWArrTierToTempR, warrBound32]
        exact storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.zero AbiReg.t0 (fl.tempSlotOff 0) hts0.1 hts0.2
      | tier a t =>
        dsimp only at htmp
        have hok_t : exprOkConst0B tab fl.nlocals t = true := by
          have := hok.1.1.1.1; simp only [warrOkConst0B, Bool.and_eq_true] at this; exact this.2
        dsimp only [evalWArrTierToTempR, warrBound32]
        cases exprReg? fl.alloc t with
        | some rt =>
          dsimp only
          have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp rt AbiReg.t0 (fl.tempSlotOff 0) hts0.1 hts0.2
          omega
        | none =>
          have het := compileETo_farTotalWords_le ht fl hfl hnl t 0 AbiReg.a0 (by omega) hok_t
          have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 0) hts0.1 hts0.2
          rw [farTotalWords_append]; omega
    have hdi := compileETo_farTotalWords_le ht fl hfl hnl di 1 AbiReg.a0 (by omega) hok.1.1.1.2
    have hsi := compileETo_farTotalWords_le ht fl hfl hnl si 3 AbiReg.a0 (by omega) hok.1.2
    have hn := compileETo_farTotalWords_le ht fl hfl hnl n 4 AbiReg.a0 (by omega) hok.2
    have hs1 := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 1) hts1.1 hts1.2
    have hs3 := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 3) hts3.1 hts3.2
    have hs4 := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 4) hts4.1 hts4.2
    have hl0 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.sp AbiReg.t1 (fl.tempSlotOff 0) hts0.1 hts0.2
    have hl1 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 1) hts1.1 hts1.2
    have hl4 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t3 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 4) hts4.1 hts4.2
    have hl3 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t2 AbiReg.sp AbiReg.t6 (fl.tempSlotOff 3) hts3.1 hts3.2
    have hdl := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.t5 AbiReg.t6
      (tab.len64 (TieredArray.t0 (evalWArrTierToTempR tab fl 0 d).1)) (hlen64 _).1 (hlen64 _).2
    have hdb := loadMemOff_farTotalWords_le_32 .ld AbiReg.t5 AbiReg.t5 AbiReg.t6
      (tab.base64 (TieredArray.t0 (evalWArrTierToTempR tab fl 0 d).1)) (hbase64 _).1 (hbase64 _).2
    have hm1 : farTotalWords [Asm.andi AbiReg.t0 AbiReg.t0 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6,
        Asm.add AbiReg.t5 AbiReg.gp AbiReg.t0] = 3 := rfl
    have hm2 : farTotalWords [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3,
        Asm.bltu AbiReg.t0 AbiReg.t1 errLabel] = 11 := rfl
    have hm3 : farTotalWords [Asm.slli AbiReg.t1 AbiReg.t1 3#6, Asm.add AbiReg.t1 AbiReg.t5 AbiReg.t1] = 2 := rfl
    have hm4 : ∀ l1 l2, farTotalWords [Asm.bltu AbiReg.t0 AbiReg.t3 errLabel, Asm.sub AbiReg.t0 AbiReg.t0 AbiReg.t3,
        Asm.bltu AbiReg.t0 AbiReg.t2 errLabel, Asm.add AbiReg.t2 AbiReg.t5 AbiReg.t2,
        Asm.lbl l1, Asm.beq AbiReg.t3 AbiReg.zero l2,
        Asm.lbu AbiReg.t4 AbiReg.t2 0#12, Asm.sd AbiReg.t1 AbiReg.t4 0#12,
        Asm.addi AbiReg.t1 AbiReg.t1 8#12, Asm.addi AbiReg.t2 AbiReg.t2 1#12,
        Asm.addi AbiReg.t3 AbiReg.t3 (-1#12), Asm.j l1, Asm.lbl l2] = 26 := fun _ _ => rfl
    simp only [compileSR, farTotalWords_append, stmtBound32]
    rw [hm4 _ _]
    cases src with
    | arr a =>
      simp only [farTotalWords_append]
      have hla := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.gp AbiReg.t6 (tab.len8 a) (hlen8 a).1 (hlen8 a).2
      have hba := loadMemOff_farTotalWords_le_32 .ld AbiReg.t5 AbiReg.gp AbiReg.t6 (tab.base8 a) (hbase8 a).1 (hbase8 a).2
      omega
    | rom bs =>
      simp only [farTotalWords_append]
      have hli := li_farTotalWords_le AbiReg.t0 (BitVec.ofNat 64 bs.length)
      have hadd := addImmOff_farTotalWords_le_32 AbiReg.t5 AbiReg.gp AbiReg.t6
        (tab.romBase + (romIdx bs tab.rom : Int)) (hrom bs).1 (hrom bs).2
      omega
  | scan8 x src i e c =>
    intro _ lblId _ _ _ htmp hok
    simp only [maxTempsStmt] at htmp
    simp only [stmtOkConst0B, Bool.and_eq_true, decide_eq_true_eq] at hok
    have hslot := varSlotOff_32 hfl hnl x
    have hts0 := tempSlotOff_32 hfl hnl (by omega : 0 < 200000)
    have hi := compileETo_farTotalWords_le ht fl hfl hnl i 0 AbiReg.a0 (by omega) hok.1.1.1.2
    have he := compileETo_farTotalWords_le ht fl hfl hnl e 1 AbiReg.a0 (by omega) hok.1.1.2
    have hst := storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.tempSlotOff 0) hts0.1 hts0.2
    have hl3 := loadMemOff_farTotalWords_le_32 .ld AbiReg.t3 AbiReg.sp AbiReg.t5 (fl.tempSlotOff 0) hts0.1 hts0.2
    have hromC := addImmOff_farTotalWords_le_32 AbiReg.t2 AbiReg.gp AbiReg.t5
      (tab.romBase + (romIdx c tab.rom : Int)) (hrom c).1 (hrom c).2
    have hloop : ∀ l1 l2, farTotalWords [Asm.lbl l1,
        Asm.bgeu AbiReg.t3 AbiReg.a0 l2,
        Asm.add AbiReg.t4 AbiReg.t1 AbiReg.t3, Asm.lbu AbiReg.t4 AbiReg.t4 0#12,
        Asm.add AbiReg.t5 AbiReg.t2 AbiReg.t4, Asm.lbu AbiReg.t5 AbiReg.t5 0#12,
        Asm.bne AbiReg.t5 AbiReg.zero l2,
        Asm.addi AbiReg.t3 AbiReg.t3 1#12, Asm.j l1, Asm.lbl l2] = 19 := fun _ _ => rfl
    have hstx : farTotalWords (storeMemOff .sd AbiReg.sp AbiReg.t3 AbiReg.t5 (fl.varSlotOff x)) ≤ 6 :=
      storeMemOff_farTotalWords_le_32 .sd AbiReg.sp AbiReg.t3 AbiReg.t5 (fl.varSlotOff x) hslot.1 hslot.2
    have hsum : ∀ (a b c1 d e1 f : Nat),
        a ≤ exprBound32 i + exprBound32 e + 12 → b ≤ 15 → c1 = 10 → d ≤ 5 → e1 = 19 → f ≤ 6 →
        a + b + c1 + d + e1 + f ≤ exprBound32 i + exprBound32 e + 70 := by omega
    dsimp only [compileSR, stmtBound32]
    simp only [farTotalWords_append]
    refine hsum _ _ _ _ _ _ ?_ ?_ rfl hromC (hloop _ _) ?_
    · cases hse : emitSimpleExprR tab fl AbiReg.a0 AbiReg.t5 e with
      | some ce =>
        dsimp only
        have hce := emitSimpleExprR_farTotalWords_le ht hfl hnl hok.1.1.2 hse
        cases exprReg? fl.alloc i with
        | some ri =>
          dsimp only; rw [farTotalWords_append]
          have hmv : farTotalWords [Asm.mv AbiReg.t3 ri] = 1 := rfl; omega
        | none =>
          dsimp only; simp only [farTotalWords_append]
          have hmv : farTotalWords [Asm.mv AbiReg.t3 AbiReg.a0] = 1 := rfl; omega
      | none =>
        dsimp only; simp only [farTotalWords_append]; omega
    · cases src with
      | arr a =>
        dsimp only; rw [farTotalWords_append]
        have hla := loadMemOff_farTotalWords_le_32 .ld AbiReg.t0 AbiReg.gp AbiReg.t5 (tab.len8 a) (hlen8 a).1 (hlen8 a).2
        have hba := loadMemOff_farTotalWords_le_32 .ld AbiReg.t1 AbiReg.gp AbiReg.t5 (tab.base8 a) (hbase8 a).1 (hbase8 a).2
        omega
      | rom bs =>
        dsimp only; rw [farTotalWords_append]
        have hli := li_farTotalWords_le AbiReg.t0 (BitVec.ofNat 64 bs.length)
        have hadd := addImmOff_farTotalWords_le_32 AbiReg.t1 AbiReg.gp AbiReg.t5
          (tab.romBase + (romIdx bs tab.rom : Int)) (hrom bs).1 (hrom bs).2
        omega
    · cases fl.alloc.lookup x with
      | some rx => dsimp only; have h1 : farTotalWords [Asm.mv rx AbiReg.t3] = 1 := rfl; omega
      | none =>
        dsimp only
        split
        · simp [farTotalWords]
        · exact hstx

theorem compileFn_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab)
    (f : FnName) (fd : FunDecl) (p : Prog)
    (hframe : numLocalsFn fd + maxTempsStmt fd.body < 100000)
    (hok : stmtOkConst0B tab p (numLocalsFn fd) false fd.body = true) :
    farTotalWords (compileFn tab f fd) ≤ fnBound32 tab.nres fd := by
  let fl := fnFrameLayoutFor tab fd
  have hnlEq : fl.nlocals = numLocalsFn fd := fnFrameLayoutFor_nlocals tab fd
  have hsavedLe : fl.savedRegs.length ≤ 10 := fnFrameLayoutFor_savedRegs_le tab fd
  have hprotLe : fl.protectedSlots ≤ 11 := fnFrameLayoutFor_protectedSlots_le tab fd
  have hspillLe : fl.spilledVars.length ≤ fl.nlocals := fnFrameLayoutFor_spilledVars_le tab fd
  have hfl : fl.protectedSlots ≤ 11 ∧ fl.spilledVars.length ≤ fl.nlocals := ⟨hprotLe, hspillLe⟩
  have husedLe : fl.usedTemps ≤ maxTempsStmt fd.body := by
    dsimp only [fl, fnFrameLayoutFor, fnFrameLayout]
    exact usedTempsStmtR_le_maxTempsStmt _ _ fd.body
  have hfb32 : 0 ≤ fl.frameBytes ∧ fl.frameBytes < 2 ^ 31 := by
    dsimp only [FrameLayout.frameBytes, FrameLayout.frameSlots]
    omega
  have hnpLe : fd.nparams ≤ numLocalsFn fd := by
    dsimp only [numLocalsFn]; exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hst := compileSR_farTotalWords_le ht fl hfl hsavedLe hfb32 (by omega)
    (fnLabel f) (toString (fnLabel f) ++ toString "_epilogue") fd.body false 0 none
    (!stmtMayFallthrough fd.body) p (by omega) (hnlEq ▸ hok)
  rcases hcb : compileSR tab fl (fnLabel f) 0 none (toString (fnLabel f) ++ toString "_epilogue")
      (!stmtMayFallthrough fd.body) fd.body with ⟨bodyCode, idEnd⟩
  rw [hcb] at hst
  dsimp only at hst
  let framePush : List AsmItem :=
    if fl.frameBytes == 0 then []
    else
      li AbiReg.t2 (BitVec.ofInt 64 fl.frameBytes) ++
      [Asm.bltu AbiReg.sp AbiReg.t2 errLabel, Asm.sub AbiReg.sp AbiReg.sp AbiReg.t2,
       Asm.ld AbiReg.t2 AbiReg.gp 8#12, Asm.bltu AbiReg.sp AbiReg.t2 errLabel] ++
      (if fl.isLeaf then [] else [Asm.sd AbiReg.sp AbiReg.ra 0#12]) ++
      saveCalleeRegs fl
  let t5Init : List AsmItem :=
    if fl.useT5Gp then [Asm.addi AbiReg.t5 AbiReg.gp 2047#12] else []
  let prologue : List AsmItem :=
    [Asm.lbl (fnLabel f)] ++ framePush ++ copyParamsR fl fd.nparams ++ zeroLocalsR fl fd ++ t5Init
  let hasErr := hasBranchTo errLabel prologue || hasBranchTo errLabel bodyCode
  let hasExh := hasBranchTo exhaustedLabel bodyCode
  let hasAb0 := stmtHasAbort0 fd.body
  let needRetarget := hasErr || hasExh
  let rt := retargetBranchItem errLabel (toString (fnLabel f) ++ toString "_errstub") exhaustedLabel
    (if hasExh then some (toString (fnLabel f) ++ toString "_exhstub") else none)
  have hpush : farTotalWords framePush ≤ 27 := by
    dsimp only [framePush]
    split
    · simp [farTotalWords]
    · simp only [farTotalWords_append]
      have hli := li_farTotalWords_le_32 AbiReg.t2 fl.frameBytes hfb32.1 hfb32.2
      have h4 : farTotalWords [Asm.bltu AbiReg.sp AbiReg.t2 errLabel, Asm.sub AbiReg.sp AbiReg.sp AbiReg.t2,
          Asm.ld AbiReg.t2 AbiReg.gp 8#12, Asm.bltu AbiReg.sp AbiReg.t2 errLabel] = 12 := rfl
      have hra : farTotalWords (if fl.isLeaf = true then [] else [Asm.sd AbiReg.sp AbiReg.ra 0#12]) ≤ 1 := by
        split
        · exact Nat.zero_le 1
        · exact Nat.le_refl 1
      have hsv := saveCalleeRegs_farTotalWords_le fl hsavedLe
      omega
  have ht5 : farTotalWords t5Init ≤ 1 := by
    dsimp only [t5Init]
    split
    · exact Nat.le_refl 1
    · exact Nat.zero_le 1
  have hcopyP := copyParamsR_farTotalWords_le fl hfl (by omega) fd.nparams (by omega)
  have hzeroL := zeroLocalsR_farTotalWords_le fl hfl (by omega) fd
  have hpro : farTotalWords prologue ≤
      28 + 12 * fd.nparams + 6 * (numLocalsFn fd - fd.nparams) := by
    dsimp only [prologue]
    have hlbl : farTotalWords [Asm.lbl (fnLabel f)] = 0 := rfl
    simp only [farTotalWords_append]
    rw [hnlEq] at hzeroL
    omega
  have hfz : farTotalWords (if stmtMayFallthrough fd.body = true then copyTempsToResultsR tab fl 0 0 else []) ≤ 1 := by
    split
    · exact copyTempsToResultsR_zero_farTotalWords_le tab fl 0
    · simp [farTotalWords]
  have hpop : farTotalWords (framePopItems fl) ≤ 16 :=
    framePopItems_farTotalWords_le fl hsavedLe hfb32
  have hfw_rt : ∀ o1 n1 o2 n2? (xs : List AsmItem),
      farTotalWords (xs.map (retargetBranchItem o1 n1 o2 n2?)) = farTotalWords xs := by
    intro o1 n1 o2 n2? xs
    induction xs with
    | nil => rfl
    | cons x rest ih =>
      rw [List.map_cons, farTotalWords_cons, farTotalWords_cons, ih]
      cases x <;> rfl
  dsimp only [compileFn, fnBound32]
  change farTotalWords (
    (if (hasBranchTo errLabel prologue ||
        hasBranchTo errLabel (compileSR tab fl (fnLabel f) 0 none (toString (fnLabel f) ++ toString "_epilogue") (!stmtMayFallthrough fd.body) fd.body).1 ||
        hasBranchTo exhaustedLabel (compileSR tab fl (fnLabel f) 0 none (toString (fnLabel f) ++ toString "_epilogue") (!stmtMayFallthrough fd.body) fd.body).1) then
      prologue.map
        (retargetBranchItem errLabel (toString (fnLabel f) ++ toString "_errstub") exhaustedLabel
          (if hasBranchTo exhaustedLabel (compileSR tab fl (fnLabel f) 0 none (toString (fnLabel f) ++ toString "_epilogue") (!stmtMayFallthrough fd.body) fd.body).1 then some (toString (fnLabel f) ++ toString "_exhstub") else none)) ++
      (compileSR tab fl (fnLabel f) 0 none (toString (fnLabel f) ++ toString "_epilogue") (!stmtMayFallthrough fd.body) fd.body).1.map
        (retargetBranchItem errLabel (toString (fnLabel f) ++ toString "_errstub") exhaustedLabel
          (if hasBranchTo exhaustedLabel (compileSR tab fl (fnLabel f) 0 none (toString (fnLabel f) ++ toString "_epilogue") (!stmtMayFallthrough fd.body) fd.body).1 then some (toString (fnLabel f) ++ toString "_exhstub") else none))
     else prologue ++ (compileSR tab fl (fnLabel f) 0 none (toString (fnLabel f) ++ toString "_epilogue") (!stmtMayFallthrough fd.body) fd.body).1) ++
    ([Asm.lbl (toString (fnLabel f) ++ toString "_ret0")] ++
      (if stmtMayFallthrough fd.body then copyTempsToResultsR tab fl 0 0 else [])) ++
    ([Asm.lbl (toString (fnLabel f) ++ toString "_epilogue")] ++ framePopItems fl ++ [Asm.ret]) ++
    ((if (hasBranchTo errLabel prologue ||
          hasBranchTo errLabel (compileSR tab fl (fnLabel f) 0 none (toString (fnLabel f) ++ toString "_epilogue") (!stmtMayFallthrough fd.body) fd.body).1 ||
          hasBranchTo exhaustedLabel (compileSR tab fl (fnLabel f) 0 none (toString (fnLabel f) ++ toString "_epilogue") (!stmtMayFallthrough fd.body) fd.body).1) then
        [Asm.lbl (toString (fnLabel f) ++ toString "_errstub"), Asm.j errLabel] else []) ++
     (if hasBranchTo exhaustedLabel (compileSR tab fl (fnLabel f) 0 none (toString (fnLabel f) ++ toString "_epilogue") (!stmtMayFallthrough fd.body) fd.body).1 then
        [Asm.lbl (toString (fnLabel f) ++ toString "_exhstub"), Asm.j exhaustedLabel] else []) ++
     (if hasAb0 then [Asm.lbl (toString (fnLabel f) ++ toString "_abort0stub"), Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.j abortLabel] else []))) ≤ _
  rw [hcb]
  change farTotalWords (
    (if needRetarget then prologue.map rt ++ bodyCode.map rt else prologue ++ bodyCode) ++
    ([Asm.lbl (toString (fnLabel f) ++ toString "_ret0")] ++
      (if stmtMayFallthrough fd.body then copyTempsToResultsR tab fl 0 0 else [])) ++
    ([Asm.lbl (toString (fnLabel f) ++ toString "_epilogue")] ++ framePopItems fl ++ [Asm.ret]) ++
    ((if needRetarget then [Asm.lbl (toString (fnLabel f) ++ toString "_errstub"), Asm.j errLabel] else []) ++
     (if hasExh then [Asm.lbl (toString (fnLabel f) ++ toString "_exhstub"), Asm.j exhaustedLabel] else []) ++
     (if hasAb0 then [Asm.lbl (toString (fnLabel f) ++ toString "_abort0stub"), Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.j abortLabel] else []))) ≤ _
  simp only [farTotalWords_append]
  have hmain : farTotalWords (if needRetarget = true then prologue.map rt ++ bodyCode.map rt else prologue ++ bodyCode) ≤
      28 + 12 * fd.nparams + 6 * (numLocalsFn fd - fd.nparams) + stmtBound32 tab.nres fd.body := by
    split
    · rw [farTotalWords_append, hfw_rt, hfw_rt]; omega
    · rw [farTotalWords_append]; omega
  have hstE : farTotalWords (if needRetarget = true then
      [Asm.lbl (toString (fnLabel f) ++ toString "_errstub"), Asm.j errLabel] else []) ≤ 4 := by
    split
    · exact Nat.le_refl 4
    · exact Nat.zero_le 4
  have hstX : farTotalWords (if hasExh = true then
      [Asm.lbl (toString (fnLabel f) ++ toString "_exhstub"), Asm.j exhaustedLabel] else []) ≤ 4 := by
    split
    · exact Nat.le_refl 4
    · exact Nat.zero_le 4
  have hstAb0 : farTotalWords (if hasAb0 = true then
      [Asm.lbl (toString (fnLabel f) ++ toString "_abort0stub"), Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.j abortLabel] else []) ≤ 5 := by
    split
    · exact Nat.le_refl 5
    · exact Nat.zero_le 5
  have hz0 : ∀ l, farTotalWords [Asm.lbl l] = 0 := fun _ => rfl
  have he2 : farTotalWords [Asm.ret] = 1 := rfl
  rw [hz0 _, hz0 _, he2]
  omega

theorem drvFillConstLoop_farTotalWords_le (loopLbl doneLbl : String) (off : Int)
    (val : BitVec 64) (count : Nat) :
    farTotalWords (drvFillConstLoop loopLbl doneLbl off val count) ≤ 43 := by
  dsimp only [drvFillConstLoop]
  split
  · simp [farTotalWords_nil]
  · simp only [farTotalWords_append]
    have h1 := addImmOff_farTotalWords_le AbiReg.t0 AbiReg.gp AbiReg.t4 off
    have h2 := li_farTotalWords_le AbiReg.t1 val
    have h3 := li_farTotalWords_le AbiReg.t2 (BitVec.ofNat 64 count)
    have h4 : farTotalWords [Asm.lbl loopLbl, Asm.beq AbiReg.t2 AbiReg.zero doneLbl,
        Asm.sd AbiReg.t0 AbiReg.t1 0#12, Asm.addi AbiReg.t0 AbiReg.t0 8#12,
        Asm.addi AbiReg.t2 AbiReg.t2 (-1#12), Asm.j loopLbl, Asm.lbl doneLbl] = 12 := rfl
    omega

theorem drvFillStrideLoop_farTotalWords_le (loopLbl doneLbl : String) (off : Int)
    (initOff stride : BitVec 64) (count : Nat) :
    farTotalWords (drvFillStrideLoop loopLbl doneLbl off initOff stride count) ≤ 55 := by
  dsimp only [drvFillStrideLoop]
  split
  · simp [farTotalWords_nil]
  · simp only [farTotalWords_append]
    have h1 := addImmOff_farTotalWords_le AbiReg.t0 AbiReg.gp AbiReg.t4 off
    have h2 := li_farTotalWords_le AbiReg.t1 initOff
    have ha : farTotalWords [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1] = 1 := rfl
    have h3 := li_farTotalWords_le AbiReg.t3 stride
    have h4 := li_farTotalWords_le AbiReg.t2 (BitVec.ofNat 64 count)
    have h5 : farTotalWords [Asm.lbl loopLbl, Asm.beq AbiReg.t2 AbiReg.zero doneLbl,
        Asm.sd AbiReg.t0 AbiReg.t1 0#12, Asm.add AbiReg.t1 AbiReg.t1 AbiReg.t3,
        Asm.addi AbiReg.t0 AbiReg.t0 8#12, Asm.addi AbiReg.t2 AbiReg.t2 (-1#12),
        Asm.j loopLbl, Asm.lbl doneLbl] = 13 := rfl
    omega

private theorem resetStack_farTotalWords_le :
    farTotalWords (li AbiReg.t1 (BitVec.ofNat 64 (abiSlot + abiStack)) ++
      [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1, Asm.sd AbiReg.gp AbiReg.t1 0#12] ++
      li AbiReg.t1 (BitVec.ofNat 64 abiSlot) ++
      [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1, Asm.sd AbiReg.gp AbiReg.t1 8#12]) ≤ 24 := by
  simp only [farTotalWords_append]
  have h1 := li_farTotalWords_le AbiReg.t1 (BitVec.ofNat 64 (abiSlot + abiStack))
  have h2 := li_farTotalWords_le AbiReg.t1 (BitVec.ofNat 64 abiSlot)
  have ha : farTotalWords [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1, Asm.sd AbiReg.gp AbiReg.t1 0#12] = 2 := rfl
  have hb : farTotalWords [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1, Asm.sd AbiReg.gp AbiReg.t1 8#12] = 2 := rfl
  omega

theorem drvInitSubAsm_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab) :
    farTotalWords (drvInitSubAsm tab) ≤ 81000 := by
  have hnb := ht.nb_le
  have hnw := ht.nw_le
  have hrom := ht.rom_le
  have hnbuf : tab.nbuf ≤ 2 := Nat.min_le_right _ _
  have hromBase : 0 ≤ tab.romBase ∧ tab.romBase ≤ 7000 := by dsimp [Tab.romBase]; omega
  have hromLen8 : (romWords64 tab.rom).length ≤ 5001 := by
    have go : ∀ (n : Nat) (xs : List UInt8), xs.length ≤ 8 * n → (romWords64 xs).length ≤ n := by
      intro n
      induction n with
      | zero =>
        intro xs h; cases xs with | nil => simp [romWords64] | cons _ _ => simp at h
      | succ n ih =>
        intro xs h
        cases xs with
        | nil => simp [romWords64]
        | cons b bs' =>
          unfold romWords64
          split
          · next _ _ _ _ _ _ _ _ rest heq =>
            have hl : (b :: bs').length = (rest.length + 8) := by
              have := congrArg List.length heq
              simpa [List.length_cons] using this
            simp only [List.length_cons]
            exact Nat.succ_le_succ (ih rest (by omega))
          · simp
          · simp
    exact go 5001 tab.rom (by omega)
  have hsumConst : ∀ {α : Type} (xs : List α) (c acc : Nat),
      xs.foldl (fun a _ => a + c) acc = acc + c * xs.length := by
    intro α xs c
    induction xs with
    | nil => intro acc; simp
    | cons _ _ ih => intro acc; rw [List.foldl_cons, ih]; simp only [List.length_cons, Nat.mul_succ]; omega
  have hbufB : farTotalWords (List.flatMap (fun p =>
      storeMemOff .sd AbiReg.gp (if p == 0 then AbiReg.a0 else AbiReg.a2) AbiReg.t0 (tab.dbase p))
      (List.range tab.nbuf)) ≤ 12 * tab.nbuf := by
    refine Nat.le_trans (farTotalWords_flatMap_le _ _ (fun _ => 12)
      (fun p _ => storeMemOff_farTotalWords_le ..)) ?_
    rw [hsumConst, Nat.zero_add, List.length_range]; exact Nat.le_refl _
  have hbufL : farTotalWords (List.flatMap (fun p =>
      storeMemOff .sd AbiReg.gp (if p == 0 then AbiReg.a1 else AbiReg.a3) AbiReg.t0 (tab.dlen p))
      (List.range tab.nbuf)) ≤ 12 * tab.nbuf := by
    refine Nat.le_trans (farTotalWords_flatMap_le _ _ (fun _ => 12)
      (fun p _ => storeMemOff_farTotalWords_le ..)) ?_
    rw [hsumConst, Nat.zero_add, List.length_range]; exact Nat.le_refl _
  have hromS : farTotalWords (List.flatMap (fun x =>
      li AbiReg.t1 x.1 ++ storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.romBase + 8 * (x.2 : Int)))
      (romWords64 tab.rom).zipIdx) ≤ 16 * (romWords64 tab.rom).length := by
    refine Nat.le_trans (farTotalWords_flatMap_le _ _ (fun _ => 16) (fun ⟨w, i⟩ hm => ?_)) ?_
    · have hi_lt : i < (romWords64 tab.rom).length := by
        have hle : ∀ (xs : List (BitVec 64)) (k : Nat) (a : BitVec 64) (b : Nat),
            (a, b) ∈ xs.zipIdx k → b < k + xs.length := by
          intro xs; induction xs with | nil => simp | cons x xs ih =>
            intro k a b hm; simp only [List.zipIdx_cons, List.mem_cons, Prod.mk.injEq] at hm
            rcases hm with ⟨rfl, rfl⟩ | hm'
            · simp
            · have := ih (k + 1) _ _ hm'; simp; omega
        simpa using hle _ 0 w i hm
      simp only [farTotalWords_append]
      have h1 := li_farTotalWords_le AbiReg.t1 w
      have h2 := storeMemOff_farTotalWords_le_32 .sd AbiReg.gp AbiReg.t1 AbiReg.t0
        (tab.romBase + 8 * (i : Int)) (by omega) (by omega)
      omega
    · rw [hsumConst, Nat.zero_add, List.length_zipIdx]; exact Nat.le_refl _
  have hreset := resetStack_farTotalWords_le
  dsimp only [drvInitSubAsm]
  simp only [farTotalWords_append] at hreset ⊢
  have hl0 : farTotalWords [Asm.lbl drvInitLabel] = 0 := rfl
  have hr0 : farTotalWords [Asm.ret] = 1 := rfl
  have hs := drvFillStrideLoop_farTotalWords_le "ca_drv_bloop" "ca_drv_bdone" (tab.dbase tab.nbuf)
    (BitVec.ofNat 64 (2 * abiSlot)) (BitVec.ofNat 64 abiSlot) (tab.nb + tab.nw - tab.nbuf)
  have hc1 := drvFillConstLoop_farTotalWords_le "ca_drv_lbloop" "ca_drv_lbdone" (tab.dlen tab.nbuf)
    (BitVec.ofNat 64 abiSlot) (tab.nb - tab.nbuf)
  have hc2 := drvFillConstLoop_farTotalWords_le "ca_drv_lwloop" "ca_drv_lwdone" (tab.dlen tab.nb)
    (BitVec.ofNat 64 abiWords) tab.nw
  have hc3 := drvFillConstLoop_farTotalWords_le "ca_drv_l32bloop" "ca_drv_l32bdone" (tab.dlen32 0)
    0#64 tab.nb
  have hc4 := drvFillConstLoop_farTotalWords_le "ca_drv_l32wloop" "ca_drv_l32wdone" (tab.dlen32 tab.nb)
    (BitVec.ofNat 64 (2 * abiWords)) tab.nw
  have hc5 := drvFillConstLoop_farTotalWords_le "ca_drv_zloop" "ca_drv_zdone" tab.resBase
    0#64 (tab.nxres + tab.ng)
  omega

theorem checkerDriverAsm_farTotalWords_le {tab : Tab} (ht : TabSmall32 tab) :
    farTotalWords (checkerDriverAsm tab) ≤ 100000 := by
  have hreset := resetStack_farTotalWords_le
  have hinit := drvInitSubAsm_farTotalWords_le ht
  have hclear : ∀ pos, farTotalWords (storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dbase pos) ++
      storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dlen pos) ++
      storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dlen32 pos)) ≤ 36 := by
    intro pos
    simp only [farTotalWords_append]
    have s1 := storeMemOff_farTotalWords_le .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dbase pos)
    have s2 := storeMemOff_farTotalWords_le .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dlen pos)
    have s3 := storeMemOff_farTotalWords_le .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dlen32 pos)
    omega
  have hc1 := hclear (tab.pos64 (TieredArray.t0 L.Arena.OUT))
  have hc2 := hclear (tab.pos64 (TieredArray.t0 L.Arena.CTLF))
  have append_le : ∀ {xs ys : List AsmItem} {a b : Nat},
      farTotalWords xs ≤ a → farTotalWords ys ≤ b → farTotalWords (xs ++ ys) ≤ a + b := by
    intro xs ys a b hx hy; rw [farTotalWords_append]; omega
  have hphaseB : farTotalWords ([Asm.slli AbiReg.t3 AbiReg.a0 1#6, Asm.srli AbiReg.t3 AbiReg.t3 1#6] ++
      storeMemOff .sd AbiReg.gp AbiReg.t3 AbiReg.t0 (tab.globOff phiGVar) ++
      storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.globOff ploGVar) ++
      li AbiReg.t1 (BitVec.ofNat 64 2) ++
      storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.globOff modeGVar) ++
      (li AbiReg.t1 (BitVec.ofNat 64 (abiSlot + abiStack)) ++
        [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1, Asm.sd AbiReg.gp AbiReg.t1 0#12] ++
        li AbiReg.t1 (BitVec.ofNat 64 abiSlot) ++
        [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1, Asm.sd AbiReg.gp AbiReg.t1 8#12]) ++
      (storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dbase (tab.pos64 (TieredArray.t0 L.Arena.OUT))) ++
        storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dlen (tab.pos64 (TieredArray.t0 L.Arena.OUT))) ++
        storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dlen32 (tab.pos64 (TieredArray.t0 L.Arena.OUT)))) ++
      (storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dbase (tab.pos64 (TieredArray.t0 L.Arena.CTLF))) ++
        storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dlen (tab.pos64 (TieredArray.t0 L.Arena.CTLF))) ++
        storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dlen32 (tab.pos64 (TieredArray.t0 L.Arena.CTLF)))) ++
      li AbiReg.t1 (BitVec.ofNat 64 (abiSlot * tab.slotOf (tab.pos64 (TieredArray.t0 L.Arena.OUT)))) ++
      [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1] ++
      storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.dbase (tab.pos64 (TieredArray.t0 L.Arena.HDRF))) ++
      li AbiReg.t1 (BitVec.ofNat 64 L.Arena.hdrW) ++
      storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.dlen (tab.pos64 (TieredArray.t0 L.Arena.HDRF))) ++
      li AbiReg.t1 (BitVec.ofNat 64 (2 * L.Arena.hdrW)) ++
      storeMemOff .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.dlen32 (tab.pos64 (TieredArray.t0 L.Arena.HDRF))) ++
      li AbiReg.s0 (BitVec.ofNat 64 (abiFuel - 1)) ++
      [Asm.ld AbiReg.sp AbiReg.gp 0#12, Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
       Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++
      addImmOff AbiReg.t0 AbiReg.gp AbiReg.t2 tab.args ++
      li AbiReg.t1 0#64 ++
      [Asm.call (fnLabel "check")]) ≤ 290 := by
    refine Nat.le_trans
      (append_le (append_le (append_le (append_le
      (append_le (append_le (append_le (append_le
      (append_le (append_le (append_le (append_le
      (append_le (append_le (append_le (append_le
      (append_le (append_le (append_le
        (Nat.le_refl 2) (storeMemOff_farTotalWords_le ..)) (storeMemOff_farTotalWords_le ..))
        (li_farTotalWords_le ..)) (storeMemOff_farTotalWords_le ..))
        hreset) hc1) hc2) (li_farTotalWords_le ..))
        (Nat.le_refl 1)) (storeMemOff_farTotalWords_le ..)) (li_farTotalWords_le ..))
        (storeMemOff_farTotalWords_le ..)) (li_farTotalWords_le ..))
        (storeMemOff_farTotalWords_le ..)) (li_farTotalWords_le ..)) (Nat.le_refl 7))
        (addImmOff_farTotalWords_le ..)) (li_farTotalWords_le ..)) (Nat.le_refl 4)) (by omega)
  dsimp only [checkerDriverAsm]
  refine Nat.le_trans
    (append_le (append_le (append_le (append_le
    (append_le (append_le (append_le (append_le
    (append_le (append_le (append_le (append_le
    (append_le (append_le (append_le
      (Nat.le_refl 0) (li_farTotalWords_le ..)) (Nat.le_refl 6))
      (callerSaveAsm_farTotalWords_le ..)) (Nat.le_refl 5))
      (li_farTotalWords_le ..)) (storeMemOff_farTotalWords_le ..))
      (li_farTotalWords_le ..)) (Nat.le_refl 7)) (addImmOff_farTotalWords_le ..))
      (li_farTotalWords_le ..)) (Nat.le_refl 9)) hphaseB) (Nat.le_refl 13))
      (callerRestoreRetAsm_farTotalWords_le ..)) hinit) (by omega)

theorem checkerCmpDriverAsm_farTotalWords_le {tab : Tab} (_ht : TabSmall32 tab) :
    farTotalWords (checkerCmpDriverAsm tab) ≤ 100000 := by
  have hreset := resetStack_farTotalWords_le
  have hclear : ∀ pos, farTotalWords (storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dbase pos) ++
      storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dlen pos) ++
      storeMemOff .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dlen32 pos)) ≤ 36 := by
    intro pos
    simp only [farTotalWords_append]
    have s1 := storeMemOff_farTotalWords_le .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dbase pos)
    have s2 := storeMemOff_farTotalWords_le .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dlen pos)
    have s3 := storeMemOff_farTotalWords_le .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.dlen32 pos)
    omega
  have hc1 := hclear (tab.pos64 (TieredArray.t0 L.Arena.OUT))
  have hc2 := hclear (tab.pos64 (TieredArray.t0 L.Arena.CTLF))
  have hcallCheck : farTotalWords (li AbiReg.s0 (BitVec.ofNat 64 (abiFuel - 1)) ++
      [Asm.ld AbiReg.sp AbiReg.gp 0#12, Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
       Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++
      addImmOff AbiReg.t0 AbiReg.gp AbiReg.t2 tab.args ++
      li AbiReg.t1 0#64 ++
      [Asm.call (fnLabel "check")]) ≤ 42 := by
    simp only [farTotalWords_append]
    have l1 := li_farTotalWords_le AbiReg.s0 (BitVec.ofNat 64 (abiFuel - 1))
    have k1 : farTotalWords [Asm.ld AbiReg.sp AbiReg.gp 0#12,
        Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
        Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] = 7 := rfl
    have a1 := addImmOff_farTotalWords_le AbiReg.t0 AbiReg.gp AbiReg.t2 tab.args
    have l2 := li_farTotalWords_le AbiReg.t1 0#64
    have k2 : farTotalWords [Asm.call (fnLabel "check")] = 4 := rfl
    omega
  dsimp only [checkerCmpDriverAsm]
  simp only [farTotalWords_append] at hreset hc1 hc2 hcallCheck ⊢
  have htop1 : farTotalWords [Asm.lbl cmpStartLabel] = 0 := rfl
  have htop2 := li_farTotalWords_le AbiReg.t0 (BitVec.ofNat 64 (abiNeed tab))
  have htop3 : farTotalWords [Asm.raw (.branch .bltu AbiReg.a5 AbiReg.t0 (mkBimm 4)),
      Asm.raw (.branch .blt AbiReg.a1 AbiReg.zero (mkBimm 3)),
      Asm.raw (.branch .blt AbiReg.a3 AbiReg.zero (mkBimm 2)),
      Asm.raw (.branch .bge AbiReg.a7 AbiReg.zero (mkBimm 4)),
      Asm.addi AbiReg.a0 AbiReg.zero 0#12,
      Asm.addi AbiReg.a1 AbiReg.zero 1#12,
      Asm.ret] = 7 := rfl
  have htopSave := callerSaveAsm_farTotalWords_le AbiReg.a4 (tab.saveBase 0)
  have htopMv : farTotalWords [Asm.mv AbiReg.s3 AbiReg.a6,
      Asm.mv AbiReg.s4 AbiReg.a7,
      Asm.mv AbiReg.gp AbiReg.a4,
      Asm.call drvInitLabel] = 7 := rfl
  have hm4l := li_farTotalWords_le AbiReg.t1 4#64
  have hm4s := storeMemOff_farTotalWords_le .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.globOff modeGVar)
  have hm4b : farTotalWords [Asm.bge AbiReg.a0 AbiReg.zero drvDoneLabel] = 5 := rfl
  have hm5s1 := storeMemOff_farTotalWords_le .sd AbiReg.gp AbiReg.s3 AbiReg.t0 (tab.dbase 0)
  have hm5s2 := storeMemOff_farTotalWords_le .sd AbiReg.gp AbiReg.s4 AbiReg.t0 (tab.dlen 0)
  have hm5l := li_farTotalWords_le AbiReg.t1 5#64
  have hm5s3 := storeMemOff_farTotalWords_le .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.globOff modeGVar)
  have hm5b : farTotalWords [Asm.bge AbiReg.a0 AbiReg.zero drvDoneLabel,
      Asm.slli AbiReg.s5 AbiReg.a0 1#6, Asm.srli AbiReg.s5 AbiReg.s5 1#6] = 7 := rfl
  have hm6l := li_farTotalWords_le AbiReg.t1 6#64
  have hm6s := storeMemOff_farTotalWords_le .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.globOff modeGVar)
  have hm6b : farTotalWords [Asm.bge AbiReg.a0 AbiReg.zero drvDoneLabel,
      Asm.slli AbiReg.s6 AbiReg.a0 1#6, Asm.srli AbiReg.s6 AbiReg.s6 1#6] = 7 := rfl
  have hm8s1 := storeMemOff_farTotalWords_le .sd AbiReg.gp AbiReg.s5 AbiReg.t0 (tab.globOff phiGVar)
  have hm8s2 := storeMemOff_farTotalWords_le .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.globOff ploGVar)
  have hm8l1 := li_farTotalWords_le AbiReg.t1 8#64
  have hm8s3 := storeMemOff_farTotalWords_le .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.globOff modeGVar)
  have hm8l2 := li_farTotalWords_le AbiReg.t1 (BitVec.ofNat 64 (abiSlot * tab.slotOf (tab.pos64 (TieredArray.t0 L.Arena.OUT))))
  have hm8add : farTotalWords [Asm.add AbiReg.t1 AbiReg.gp AbiReg.t1] = 1 := rfl
  have hm8s4 := storeMemOff_farTotalWords_le .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.dbase (tab.pos64 (TieredArray.t0 L.Arena.HDRF)))
  have hm8l3 := li_farTotalWords_le AbiReg.t1 (BitVec.ofNat 64 hdrHw)
  have hm8s5 := storeMemOff_farTotalWords_le .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.dlen (tab.pos64 (TieredArray.t0 L.Arena.HDRF)))
  have hm8l4 := li_farTotalWords_le AbiReg.t1 (BitVec.ofNat 64 (2 * hdrHw))
  have hm8s6 := storeMemOff_farTotalWords_le .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.dlen32 (tab.pos64 (TieredArray.t0 L.Arena.HDRF)))
  have hm8l5 := li_farTotalWords_le AbiReg.t1 acceptWord.toBitVec
  have hm8b : farTotalWords [Asm.bne AbiReg.a0 AbiReg.t1 drvDoneLabel] = 5 := rfl
  have hm9s1 := storeMemOff_farTotalWords_le .sd AbiReg.gp AbiReg.s6 AbiReg.t0 (tab.globOff phiGVar)
  have hm9s2 := storeMemOff_farTotalWords_le .sd AbiReg.gp AbiReg.zero AbiReg.t0 (tab.globOff ploGVar)
  have hm9l := li_farTotalWords_le AbiReg.t1 9#64
  have hm9s3 := storeMemOff_farTotalWords_le .sd AbiReg.gp AbiReg.t1 AbiReg.t0 (tab.globOff modeGVar)
  have hbot : farTotalWords [Asm.j drvDoneLabel] = 4 := rfl
  omega

end ConAgua.RISCV.Bridge
