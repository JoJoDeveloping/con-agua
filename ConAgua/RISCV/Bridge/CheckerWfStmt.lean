import ConAgua.Checker.ProgWf
import ConAgua.Checker.ProgTree
import ConAgua.RISCV.Compiler.ProgSimMain
import ConAgua.RISCV.Bridge.CheckerIso
import ConAgua.RISCV.Bridge.CheckerWf
import ConAgua.RISCV.Bridge.CheckerProgScan
import ConAgua.RISCV.Bridge.CheckerProgIScan
import ConAgua.RISCV.Bridge.CheckerWfFast

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Algebraic Program Well-Formedness Bridge (`ConAgua.RISCV.Bridge.CheckerWfStmt`)

Lifts `L.Compiler.{Expr,Cond,Stmt}.wf` to `ConAgua.RISCV.Compiler`-compatible predicates
`exprOkTier0B`, `condOkTier0B`, `stmtOkTier0B`, and `progOkTier0B`, matching
`ConAgua.RISCV.Compiler.{exprOkB,condOkB,stmtOkB,progOkB}` everywhere **except** that
`.ld32t a t i` / `.st32t a t i e` with an even constant tier (`t = .const 0`, matching
`{expr,level,name}_{get,put}` on single-tier arrays `{64,65,66}`) only requires
`tab.wordPosOkB (.t0 a)` rather than `tab.tieredOkB a`.

Proves inside Lean's kernel (`[propext, Classical.choice, Quot.sound]`, zero `sorry`,
zero `native_decide`, zero `bv_decide`):
- `expr_wf_imp_exprOkTier0B`, `cond_wf_imp_condOkTier0B`, `stmt_wf_imp_stmtOkTier0B`
- `checkerProgMini_progOkTier0B : progOkTier0B checkerTabMini checkerProgMini = true`
- `checkerProgIMini_progOkTier0B : progOkTier0B checkerTabMini checkerProgIMini = true`
- Exact equivalence to `progOkConst0B` (checking literally `t = .const 0`) on both
  `checkerProgMini` and `checkerProgIMini`.
-/

namespace ConAgua.RISCV.Bridge

open ConAgua.RISCV.Compiler

/-! ## 1. Relaxed Tier-0 Well-Formedness Predicates -/

def tier32OkTier0B (tab : Tab) (a : L.ArrId) (t : L.Expr) : Bool :=
  match t with
  | .const w => if w.toNat % 2 == 0 then tab.wordPosOkB (.t0 a) else tab.tieredOkB a
  | _ => tab.tieredOkB a

def tier32OkConst0B (tab : Tab) (a : L.ArrId) (t : L.Expr) : Bool :=
  match t with
  | .const w => if w == 0 then tab.wordPosOkB (.t0 a) else tab.tieredOkB a
  | _ => tab.tieredOkB a

def exprOkTier0B (tab : Tab) (nl : Nat) : L.Expr → Bool
  | .const _ => true
  | .var x => x < nl
  | .bin _ a b | .cmpw _ a b => exprOkTier0B tab nl a && exprOkTier0B tab nl b
  | .ld8 a i => tab.bytePosOkB a && exprOkTier0B tab nl i
  | .ld64 a i => tab.wordPosOkB (.t0 a) && exprOkTier0B tab nl i
  | .len8 a => tab.bytePosOkB a
  | .len64 a => tab.wordPosOkB (.t0 a)
  | .ldc d i => tab.romSliceOkB d && exprOkTier0B tab nl i
  | .glob g => g.id < tab.ng
  | .ld64t a t i | .ld32h a t i _ =>
    tab.tieredOkB a && exprOkTier0B tab nl t && exprOkTier0B tab nl i
  | .ld32t a t i =>
    tier32OkTier0B tab a t && exprOkTier0B tab nl t && exprOkTier0B tab nl i
  | .len64t a t => tab.tieredOkB a && exprOkTier0B tab nl t
  | .ld8x8 (.arr a) i => tab.bytePosOkB a && exprOkTier0B tab nl i
  | .ld8x8 (.rom d) i => tab.romSliceOkB d && exprOkTier0B tab nl i

def condOkTier0B (tab : Tab) (nl : Nat) : L.Cond → Bool
  | .cmp _ a b => exprOkTier0B tab nl a && exprOkTier0B tab nl b
  | .and p q | .or p q => condOkTier0B tab nl p && condOkTier0B tab nl q
  | .not p => condOkTier0B tab nl p

def warrOkTier0B (tab : Tab) (nl : Nat) : L.WArr → Bool
  | .plain a => tab.wordPosOkB (.t0 a)
  | .tier a t => tab.tieredOkB a && exprOkTier0B tab nl t

def stmtOkTier0B (tab : Tab) (p : L.Prog) (nl : Nat) (inLoop : Bool) :
    L.Stmt → Bool
  | .skip => true
  | .brk => inLoop
  | .set x e => (x < nl) && exprOkTier0B tab nl e
  | .st8 _ _ _ => false
  | .st64 a i e => tab.wordPosOkB (.t0 a) && exprOkTier0B tab nl i && exprOkTier0B tab nl e
  | .seq s₁ s₂ => stmtOkTier0B tab p nl inLoop s₁ && stmtOkTier0B tab p nl inLoop s₂
  | .ite c s₁ s₂ =>
    condOkTier0B tab nl c && stmtOkTier0B tab p nl inLoop s₁ && stmtOkTier0B tab p nl inLoop s₂
  | .while c s => condOkTier0B tab nl c && stmtOkTier0B tab p nl true s
  | .ret es => (es.length ≤ tab.nres) && es.all (exprOkTier0B tab nl)
  | .call xs f args =>
    (p.lookup f).isSome && (xs.all (· < nl)) && args.all (exprOkTier0B tab nl)
  | .abort e => exprOkTier0B tab nl e
  | .gset g e => (g.id < tab.ng) && exprOkTier0B tab nl e
  | .st64t a t i e =>
    tab.tieredOkB a && exprOkTier0B tab nl t && exprOkTier0B tab nl i && exprOkTier0B tab nl e
  | .st32t a t i e =>
    tier32OkTier0B tab a t && exprOkTier0B tab nl t && exprOkTier0B tab nl i && exprOkTier0B tab nl e
  | .copy64 d di s si n =>
    warrOkTier0B tab nl d && exprOkTier0B tab nl di && warrOkTier0B tab nl s &&
    exprOkTier0B tab nl si && exprOkTier0B tab nl n
  | .copy8w d di s si n =>
    warrOkTier0B tab nl d && exprOkTier0B tab nl di && bsrcOkB tab s &&
    exprOkTier0B tab nl si && exprOkTier0B tab nl n
  | .scan8 x s i e c =>
    (x < nl) && bsrcOkB tab s && exprOkTier0B tab nl i && exprOkTier0B tab nl e &&
    (256 ≤ c.length) && tab.romSliceOkB c

def progOkTier0B (tab : Tab) (p : L.Prog) : Bool :=
  tab.arrAtOkB &&
  (1 ≤ tab.nres) &&
  (p.map Prod.fst).Nodup &&
  p.all fun (_, fd) => stmtOkTier0B tab p (numLocalsFn fd) false fd.body

def exprOkConst0B (tab : Tab) (nl : Nat) : L.Expr → Bool
  | .const _ => true
  | .var x => x < nl
  | .bin _ a b | .cmpw _ a b => exprOkConst0B tab nl a && exprOkConst0B tab nl b
  | .ld8 a i => tab.bytePosOkB a && exprOkConst0B tab nl i
  | .ld64 a i => tab.wordPosOkB (.t0 a) && exprOkConst0B tab nl i
  | .len8 a => tab.bytePosOkB a
  | .len64 a => tab.wordPosOkB (.t0 a)
  | .ldc d i => tab.romSliceOkB d && exprOkConst0B tab nl i
  | .glob g => g.id < tab.ng
  | .ld64t a t i | .ld32h a t i _ =>
    tab.tieredOkB a && exprOkConst0B tab nl t && exprOkConst0B tab nl i
  | .ld32t a t i =>
    tier32OkConst0B tab a t && exprOkConst0B tab nl t && exprOkConst0B tab nl i
  | .len64t a t => tab.tieredOkB a && exprOkConst0B tab nl t
  | .ld8x8 (.arr a) i => tab.bytePosOkB a && exprOkConst0B tab nl i
  | .ld8x8 (.rom d) i => tab.romSliceOkB d && exprOkConst0B tab nl i

def condOkConst0B (tab : Tab) (nl : Nat) : L.Cond → Bool
  | .cmp _ a b => exprOkConst0B tab nl a && exprOkConst0B tab nl b
  | .and p q | .or p q => condOkConst0B tab nl p && condOkConst0B tab nl q
  | .not p => condOkConst0B tab nl p

def warrOkConst0B (tab : Tab) (nl : Nat) : L.WArr → Bool
  | .plain a => tab.wordPosOkB (.t0 a)
  | .tier a t => tab.tieredOkB a && exprOkConst0B tab nl t

def stmtOkConst0B (tab : Tab) (p : L.Prog) (nl : Nat) (inLoop : Bool) :
    L.Stmt → Bool
  | .skip => true
  | .brk => inLoop
  | .set x e => (x < nl) && exprOkConst0B tab nl e
  | .st8 _ _ _ => false
  | .st64 a i e => tab.wordPosOkB (.t0 a) && exprOkConst0B tab nl i && exprOkConst0B tab nl e
  | .seq s₁ s₂ => stmtOkConst0B tab p nl inLoop s₁ && stmtOkConst0B tab p nl inLoop s₂
  | .ite c s₁ s₂ =>
    condOkConst0B tab nl c && stmtOkConst0B tab p nl inLoop s₁ && stmtOkConst0B tab p nl inLoop s₂
  | .while c s => condOkConst0B tab nl c && stmtOkConst0B tab p nl true s
  | .ret es => (es.length ≤ tab.nres) && es.all (exprOkConst0B tab nl)
  | .call xs f args =>
    (p.lookup f).isSome && (xs.all (· < nl)) && args.all (exprOkConst0B tab nl)
  | .abort e => exprOkConst0B tab nl e
  | .gset g e => (g.id < tab.ng) && exprOkConst0B tab nl e
  | .st64t a t i e =>
    tab.tieredOkB a && exprOkConst0B tab nl t && exprOkConst0B tab nl i && exprOkConst0B tab nl e
  | .st32t a t i e =>
    tier32OkConst0B tab a t && exprOkConst0B tab nl t && exprOkConst0B tab nl i && exprOkConst0B tab nl e
  | .copy64 d di s si n =>
    warrOkConst0B tab nl d && exprOkConst0B tab nl di && warrOkConst0B tab nl s &&
    exprOkConst0B tab nl si && exprOkConst0B tab nl n
  | .copy8w d di s si n =>
    warrOkConst0B tab nl d && exprOkConst0B tab nl di && bsrcOkB tab s &&
    exprOkConst0B tab nl si && exprOkConst0B tab nl n
  | .scan8 x s i e c =>
    (x < nl) && bsrcOkB tab s && exprOkConst0B tab nl i && exprOkConst0B tab nl e &&
    (256 ≤ c.length) && tab.romSliceOkB c

def progOkConst0B (tab : Tab) (p : L.Prog) : Bool :=
  tab.arrAtOkB &&
  (1 ≤ tab.nres) &&
  (p.map Prod.fst).Nodup &&
  p.all fun (_, fd) => stmtOkConst0B tab p (numLocalsFn fd) false fd.body

/-! ## 2. Monotonicity in `nl` & `Tab` Domain Translation Lemmas -/

private theorem exprOkTier0B_mono {tab : Tab} {n₁ n₂ : Nat} (hle : n₁ ≤ n₂) :
    ∀ {e : L.Expr}, exprOkTier0B tab n₁ e = true → exprOkTier0B tab n₂ e = true
  | .const _, h | .len8 _, h | .len64 _, h | .glob _, h => h
  | .var x, h => by
    simp only [exprOkTier0B] at h ⊢
    exact decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true h) hle)
  | .bin _ a b, h | .cmpw _ a b, h => by
    simp only [exprOkTier0B, Bool.and_eq_true] at h ⊢
    exact ⟨exprOkTier0B_mono hle h.1, exprOkTier0B_mono hle h.2⟩
  | .ld8 _ i, h | .ld64 _ i, h | .ldc _ i, h | .len64t _ i, h | .ld8x8 (.arr _) i, h
  | .ld8x8 (.rom _) i, h => by
    simp only [exprOkTier0B, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, exprOkTier0B_mono hle h.2⟩
  | .ld64t _ t i, h | .ld32t _ t i, h | .ld32h _ t i _, h => by
    simp only [exprOkTier0B, Bool.and_eq_true] at h ⊢
    exact ⟨⟨h.1.1, exprOkTier0B_mono hle h.1.2⟩, exprOkTier0B_mono hle h.2⟩

private theorem condOkTier0B_mono {tab : Tab} {n₁ n₂ : Nat} (hle : n₁ ≤ n₂) :
    ∀ {c : L.Cond}, condOkTier0B tab n₁ c = true → condOkTier0B tab n₂ c = true
  | .cmp _ a b, h => by
    simp only [condOkTier0B, Bool.and_eq_true] at h ⊢
    exact ⟨exprOkTier0B_mono hle h.1, exprOkTier0B_mono hle h.2⟩
  | .and p q, h | .or p q, h => by
    simp only [condOkTier0B, Bool.and_eq_true] at h ⊢
    exact ⟨condOkTier0B_mono hle h.1, condOkTier0B_mono hle h.2⟩
  | .not p, h => condOkTier0B_mono hle (c := p) h

private theorem warrOkTier0B_mono {tab : Tab} {n₁ n₂ : Nat} (hle : n₁ ≤ n₂) :
    ∀ {w : L.WArr}, warrOkTier0B tab n₁ w = true → warrOkTier0B tab n₂ w = true
  | .plain _, h => h
  | .tier _ t, h => by
    simp only [warrOkTier0B, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, exprOkTier0B_mono hle h.2⟩

private theorem exprAll_mono {tab : Tab} {n₁ n₂ : Nat} (hle : n₁ ≤ n₂) {es : List L.Expr}
    (h : es.all (exprOkTier0B tab n₁) = true) : es.all (exprOkTier0B tab n₂) = true := by
  simp only [List.all_eq_true] at h ⊢
  exact fun e he => exprOkTier0B_mono hle (h e he)

private theorem stmtOkTier0B_mono {tab : Tab} {p : L.Prog} {n₁ n₂ : Nat} (hle : n₁ ≤ n₂) :
    ∀ {inLoop : Bool} {s : L.Stmt},
      stmtOkTier0B tab p n₁ inLoop s = true → stmtOkTier0B tab p n₂ inLoop s = true
  | _, .skip, h | _, .brk, h => h
  | _, .abort e, h => exprOkTier0B_mono hle h
  | _, .set x e, h => by
    simp only [stmtOkTier0B, Bool.and_eq_true] at h ⊢
    exact ⟨decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true h.1) hle), exprOkTier0B_mono hle h.2⟩
  | _, .gset _ e, h => by
    simp only [stmtOkTier0B, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, exprOkTier0B_mono hle h.2⟩
  | _, .st8 _ _ _, h => h
  | _, .st64 _ i e, h => by
    simp only [stmtOkTier0B, Bool.and_eq_true] at h ⊢
    exact ⟨⟨h.1.1, exprOkTier0B_mono hle h.1.2⟩, exprOkTier0B_mono hle h.2⟩
  | _, .seq s₁ s₂, h => by
    simp only [stmtOkTier0B, Bool.and_eq_true] at h ⊢
    exact ⟨stmtOkTier0B_mono hle h.1, stmtOkTier0B_mono hle h.2⟩
  | _, .ite c s₁ s₂, h => by
    simp only [stmtOkTier0B, Bool.and_eq_true] at h ⊢
    exact ⟨⟨condOkTier0B_mono hle h.1.1, stmtOkTier0B_mono hle h.1.2⟩, stmtOkTier0B_mono hle h.2⟩
  | _, .while c s, h => by
    simp only [stmtOkTier0B, Bool.and_eq_true] at h ⊢
    exact ⟨condOkTier0B_mono hle h.1, stmtOkTier0B_mono hle h.2⟩
  | _, .ret es, h => by
    simp only [stmtOkTier0B, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, exprAll_mono hle h.2⟩
  | _, .call xs f args, h => by
    simp only [stmtOkTier0B, Bool.and_eq_true, List.all_eq_true] at h ⊢
    exact ⟨⟨h.1.1, fun x hx => decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true (h.1.2 x hx)) hle)⟩,
      fun e he => exprOkTier0B_mono hle (h.2 e he)⟩
  | _, .st64t _ t i e, h | _, .st32t _ t i e, h => by
    simp only [stmtOkTier0B, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨h.1.1.1, exprOkTier0B_mono hle h.1.1.2⟩, exprOkTier0B_mono hle h.1.2⟩, exprOkTier0B_mono hle h.2⟩
  | _, .copy64 d di s si n, h => by
    simp only [stmtOkTier0B, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨⟨warrOkTier0B_mono hle h.1.1.1.1, exprOkTier0B_mono hle h.1.1.1.2⟩,
      warrOkTier0B_mono hle h.1.1.2⟩, exprOkTier0B_mono hle h.1.2⟩, exprOkTier0B_mono hle h.2⟩
  | _, .copy8w d di s si n, h => by
    simp only [stmtOkTier0B, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨⟨warrOkTier0B_mono hle h.1.1.1.1, exprOkTier0B_mono hle h.1.1.1.2⟩, h.1.1.2⟩,
      exprOkTier0B_mono hle h.1.2⟩, exprOkTier0B_mono hle h.2⟩
  | _, .scan8 x s i e c, h => by
    simp only [stmtOkTier0B, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨⟨⟨decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true h.1.1.1.1.1) hle), h.1.1.1.1.2⟩,
      exprOkTier0B_mono hle h.1.1.1.2⟩, exprOkTier0B_mono hle h.1.1.2⟩, h.1.2⟩, h.2⟩

private theorem dom8_imp_bytePosOkB {t : L.Compiler.Tab} {a : L.ArrId}
    (h : t.dom8 a = true) : (toRiscvTab t).bytePosOkB a = true := by
  obtain ⟨p, hfind, hp⟩ := t.dom8_find h
  have hbound : p < t.nb + t.nw := by omega
  have hcode : t.wAt p = L.TieredArray.t0 a := t.find_code hfind
  have hlen : t.arrAt.length = t.nb + t.nw := t.layOk_spec.1
  have hpLen : p < t.arrAt.length := by omega
  have hw : t.arrAt[p] = L.TieredArray.t0 a := by
    simpa [L.Compiler.Tab.wAt, L.Compiler.arrAtD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hpLen] using hcode
  have hget : (toRiscvTab t).arrAt[p]? = some (L.TieredArray.t0 a) := by
    simp [toRiscvTab, List.getElem?_eq_getElem hpLen, hw]
  have hfindM : (toRiscvTab t).lmap.find (L.TieredArray.t0 a).code = some p := by
    dsimp [toRiscvTab]
    rw [toRiscvNTree_find]
    exact hfind
  have hpos8 : (toRiscvTab t).pos8 a = p := by simp [Tab.pos8, hfindM]
  simp only [Tab.bytePosOkB, hpos8, hfindM, hget, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, and_true]
  dsimp [toRiscvTab]; exact hp

private theorem dom64_imp_wordPosOkB {t : L.Compiler.Tab} {s : L.TieredArray}
    (h : t.dom64 s = true) : (toRiscvTab t).wordPosOkB s = true := by
  obtain ⟨p, hfind, hp⟩ := t.dom64_find h
  have hpUb := (t.find_some hfind).1
  have hcode : t.wAt p = s := t.find_code hfind
  have hlen : t.arrAt.length = t.nb + t.nw := t.layOk_spec.1
  have hpLen : p < t.arrAt.length := by omega
  have hw : t.arrAt[p] = s := by
    simpa [L.Compiler.Tab.wAt, L.Compiler.arrAtD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hpLen] using hcode
  have hget : (toRiscvTab t).arrAt[p]? = some s := by
    simp [toRiscvTab, List.getElem?_eq_getElem hpLen, hw]
  have hfindM : (toRiscvTab t).lmap.find s.code = some p := by
    dsimp [toRiscvTab]
    rw [toRiscvNTree_find]
    exact hfind
  have hpos64 : (toRiscvTab t).pos64 s = p := by simp [Tab.pos64, hfindM]
  simp only [Tab.wordPosOkB, hpos64, hfindM, hget, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, and_true]
  dsimp [toRiscvTab]; exact ⟨hp, hpUb⟩

private theorem dom64_tier1_imp_tieredOkB {t : L.Compiler.Tab} {a : L.ArrId}
    (h : t.dom64 (L.tier1 a) = true) : (toRiscvTab t).tieredOkB a = true := by
  have h0 : t.dom64 (L.TieredArray.t0 a) = true := t.dom64_tierA h 0
  have hw0 := dom64_imp_wordPosOkB h0
  have hw1 := dom64_imp_wordPosOkB h
  have hadj := t.pos64_tierA h 1
  have h1nat : UInt64.toNat ((1 : L.Word) &&& 1) = 1 := rfl
  have ht1 : L.tierA a 1 = L.tier1 a := rfl
  have ht0 : L.tierA a 0 = L.TieredArray.t0 a := rfl
  rw [ht1, h1nat] at hadj
  obtain ⟨p0, hf0, _⟩ := t.dom64_find h0
  obtain ⟨p1, hf1, _⟩ := t.dom64_find h
  have hp0 : t.pos64 (L.TieredArray.t0 a) = p0 := t.pos64_eq hf0
  have hp1 : t.pos64 (L.tier1 a) = p1 := t.pos64_eq hf1
  have hp0M : (toRiscvTab t).pos64 (L.TieredArray.t0 a) = p0 := by
    dsimp [Tab.pos64, toRiscvTab]
    rw [toRiscvNTree_find]
    exact congrArg (Option.getD · 0) hf0
  have hp1M : (toRiscvTab t).pos64 (L.tier1 a) = p1 := by
    dsimp [Tab.pos64, toRiscvTab]
    rw [toRiscvNTree_find]
    exact congrArg (Option.getD · 0) hf1
  simp only [Tab.tieredOkB, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨hw0, hw1⟩, ?_⟩
  rw [hp0M, hp1M, ← hp0, ← hp1]
  exact hadj

private theorem tierA_const_eq (a : L.ArrId) (w : L.Word) :
    L.tierA a w = if w.toNat % 2 = 0 then L.TieredArray.t0 a else L.tier1 a := by
  have hm : (w &&& 1).toNat = w.toNat % 2 := by
    simp [UInt64.toNat_and]
  have hwz : (w &&& 1 = 0) ↔ w.toNat % 2 = 0 := by
    rw [← UInt64.toNat_inj, hm]
    rfl
  simp only [L.tierA, L.tier1, L.TieredArray.t0]
  by_cases he : w.toNat % 2 = 0
  · simp [he, hwz.mpr he]
  · simp [he, (mt hwz.mp he)]

private theorem tier32Ok_imp_tier32OkTier0B {t : L.Compiler.Tab} {a : L.ArrId} {e : L.Expr}
    (h : t.tier32Ok a e = true) :
    tier32OkTier0B (toRiscvTab t) a e = true := by
  cases e with
  | const w =>
    simp only [L.Compiler.Tab.tier32Ok, L.Expr.constTier?] at h
    rw [tierA_const_eq] at h
    dsimp [tier32OkTier0B]
    by_cases he : w.toNat % 2 = 0
    · simp only [he, ↓reduceIte, beq_iff_eq] at h ⊢
      exact dom64_imp_wordPosOkB h
    · simp only [he, ↓reduceIte, beq_iff_eq] at h ⊢
      exact dom64_tier1_imp_tieredOkB h
  | var _ | len8 _ | len64 _ | glob _ | bin _ _ _ | cmpw _ _ _ | ld8 _ _
  | ld64 _ _ | ldc _ _ | ld64t _ _ _ | ld32t _ _ _ | ld32h _ _ _ _ | len64t _ _ | ld8x8 _ _ =>
    simp only [L.Compiler.Tab.tier32Ok, L.Expr.constTier?] at h
    dsimp [tier32OkTier0B]
    exact dom64_tier1_imp_tieredOkB h

/-! ## 3. Main Algebraic Lift (`L.Compiler.WF` → `*OkTier0B`) -/

private theorem riscv_romIdx_eq_agua' (d : List UInt8) :
    ∀ l : List UInt8, ConAgua.RISCV.Compiler.romIdx d l = L.Compiler.romIdx d l
  | [] => rfl
  | _ :: rest => by
    simp only [ConAgua.RISCV.Compiler.romIdx, L.Compiler.romIdx, riscv_romIdx_eq_agua' d rest]

private theorem romIdx_nil' : ∀ l : List UInt8, L.Compiler.romIdx [] l = 0
  | [] => rfl
  | _ :: _ => rfl

private theorem romOk_imp_romSliceOkB {t : L.Compiler.Tab} {d : List UInt8}
    (hok : L.Compiler.romOk t d = true) :
    (toRiscvTab t).romSliceOkB d = true := by
  cases d with
  | nil =>
    simp only [Tab.romSliceOkB, toRiscvTab, riscv_romIdx_eq_agua', romIdx_nil',
      List.length_nil, Nat.add_zero, List.range_zero, List.all_nil, Bool.and_true, decide_eq_true_eq]
    exact Nat.zero_le _
  | cons b bs =>
    have hpref : (b :: bs) <+: t.rom.drop (L.Compiler.romIdx (b :: bs) t.rom) :=
      List.isPrefixOf_iff_prefix.mp hok
    have hlen : (b :: bs).length ≤ (t.rom.drop (L.Compiler.romIdx (b :: bs) t.rom)).length := hpref.length_le
    rw [List.length_drop] at hlen
    have hpos : 0 < (b :: bs).length := by simp
    have hbound : L.Compiler.romIdx (b :: bs) t.rom + (b :: bs).length ≤ t.rom.length := by omega
    simp only [Tab.romSliceOkB, toRiscvTab, riscv_romIdx_eq_agua', Bool.and_eq_true,
      decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq]
    refine ⟨hbound, fun j hj => ?_⟩
    have hget := (hpref.getElem hj).symm
    have hidx : L.Compiler.romIdx (b :: bs) t.rom + j < t.rom.length := by omega
    simp only [List.getElem_drop] at hget
    rw [List.getElem?_eq_getElem hidx, List.getElem?_eq_getElem hj, hget]

private theorem expr_wf_imp_exprOkTier0B_aux {t : L.Compiler.Tab} {nl : Nat} :
    ∀ {e : L.Expr},
      L.Compiler.Expr.wf nl t e = true →
      exprOkTier0B (toRiscvTab t) nl e = true
  | .const _, _ | .var _, _ => by simp_all [L.Compiler.Expr.wf, exprOkTier0B]
  | .glob _, h => by
    simp only [L.Compiler.Expr.wf] at h
    simp only [exprOkTier0B]
    exact decide_eq_true (of_decide_eq_true h)
  | .bin _ a b, h | .cmpw _ a b, h => by
    simp only [L.Compiler.Expr.wf, Bool.and_eq_true] at h
    simp only [exprOkTier0B, Bool.and_eq_true]
    exact ⟨expr_wf_imp_exprOkTier0B_aux h.1, expr_wf_imp_exprOkTier0B_aux h.2⟩
  | .ld8 a i, h => by
    simp only [L.Compiler.Expr.wf, Bool.and_eq_true] at h
    simp only [exprOkTier0B, Bool.and_eq_true]
    exact ⟨dom8_imp_bytePosOkB h.1, expr_wf_imp_exprOkTier0B_aux h.2⟩
  | .ld64 a i, h => by
    simp only [L.Compiler.Expr.wf, Bool.and_eq_true] at h
    simp only [exprOkTier0B, Bool.and_eq_true]
    exact ⟨dom64_imp_wordPosOkB h.1, expr_wf_imp_exprOkTier0B_aux h.2⟩
  | .len8 a, h => by
    simpa [L.Compiler.Expr.wf, exprOkTier0B] using dom8_imp_bytePosOkB h
  | .len64 a, h => by
    simpa [L.Compiler.Expr.wf, exprOkTier0B] using dom64_imp_wordPosOkB h
  | .ldc d i, h => by
    simp only [L.Compiler.Expr.wf, Bool.and_eq_true] at h
    simp only [exprOkTier0B, Bool.and_eq_true]
    exact ⟨romOk_imp_romSliceOkB h.1, expr_wf_imp_exprOkTier0B_aux h.2⟩
  | .ld64t a tt i, h | .ld32h a tt i _, h => by
    simp only [L.Compiler.Expr.wf, Bool.and_eq_true] at h
    simp only [exprOkTier0B, Bool.and_eq_true]
    exact ⟨⟨dom64_tier1_imp_tieredOkB h.1.1, expr_wf_imp_exprOkTier0B_aux h.1.2⟩,
           expr_wf_imp_exprOkTier0B_aux h.2⟩
  | .ld32t a tt i, h => by
    simp only [L.Compiler.Expr.wf, Bool.and_eq_true] at h
    simp only [exprOkTier0B, Bool.and_eq_true]
    exact ⟨⟨tier32Ok_imp_tier32OkTier0B h.1.1, expr_wf_imp_exprOkTier0B_aux h.1.2⟩,
           expr_wf_imp_exprOkTier0B_aux h.2⟩
  | .len64t a tt, h => by
    simp only [L.Compiler.Expr.wf, Bool.and_eq_true] at h
    simp only [exprOkTier0B, Bool.and_eq_true]
    exact ⟨dom64_tier1_imp_tieredOkB h.1, expr_wf_imp_exprOkTier0B_aux h.2⟩
  | .ld8x8 s i, h => by
    simp only [L.Compiler.Expr.wf, Bool.and_eq_true] at h
    cases s with
    | arr a =>
      simp only [L.Compiler.BSrc.wf] at h
      simp only [exprOkTier0B, Bool.and_eq_true]
      exact ⟨dom8_imp_bytePosOkB h.1, expr_wf_imp_exprOkTier0B_aux h.2⟩
    | rom d₀ =>
      simp only [L.Compiler.BSrc.wf, Bool.and_eq_true] at h
      simp only [exprOkTier0B, Bool.and_eq_true]
      exact ⟨romOk_imp_romSliceOkB h.1.1, expr_wf_imp_exprOkTier0B_aux h.2⟩

theorem expr_wf_imp_exprOkTier0B {t : L.Compiler.Tab} {nl : Nat} {e : L.Expr}
    (h : L.Compiler.Expr.wf nl t e = true)
    (_hne : ∀ d ∈ L.Compiler.Expr.roms e, d ≠ []) :
    exprOkTier0B (toRiscvTab t) nl e = true :=
  expr_wf_imp_exprOkTier0B_aux h

private theorem cond_wf_imp_condOkTier0B_aux {t : L.Compiler.Tab} {nl : Nat} :
    ∀ {c : L.Cond},
      L.Compiler.Cond.wf nl t c = true →
      condOkTier0B (toRiscvTab t) nl c = true
  | .cmp _ a b, h => by
    simp only [L.Compiler.Cond.wf, Bool.and_eq_true] at h
    simp only [condOkTier0B, Bool.and_eq_true]
    exact ⟨expr_wf_imp_exprOkTier0B_aux h.1, expr_wf_imp_exprOkTier0B_aux h.2⟩
  | .and p q, h | .or p q, h => by
    simp only [L.Compiler.Cond.wf, Bool.and_eq_true] at h
    simp only [condOkTier0B, Bool.and_eq_true]
    exact ⟨cond_wf_imp_condOkTier0B_aux h.1, cond_wf_imp_condOkTier0B_aux h.2⟩
  | .not p, h => cond_wf_imp_condOkTier0B_aux (c := p) h

theorem cond_wf_imp_condOkTier0B {t : L.Compiler.Tab} {nl : Nat} {c : L.Cond}
    (h : L.Compiler.Cond.wf nl t c = true)
    (_hne : ∀ d ∈ L.Compiler.Cond.roms c, d ≠ []) :
    condOkTier0B (toRiscvTab t) nl c = true :=
  cond_wf_imp_condOkTier0B_aux h

private theorem warr_wf_imp_warrOkTier0B {t : L.Compiler.Tab} {nl : Nat} :
    ∀ {w : L.WArr},
      L.Compiler.WArr.wf nl t w = true →
      warrOkTier0B (toRiscvTab t) nl w = true
  | .plain a, h => by
    simpa [L.Compiler.WArr.wf, warrOkTier0B] using dom64_imp_wordPosOkB h
  | .tier a tt, h => by
    simp only [L.Compiler.WArr.wf, Bool.and_eq_true] at h
    simp only [warrOkTier0B, Bool.and_eq_true]
    exact ⟨dom64_tier1_imp_tieredOkB h.1.1, expr_wf_imp_exprOkTier0B_aux h.2⟩

private theorem bsrc_wf_imp_bsrcOkB {t : L.Compiler.Tab} :
    ∀ {s : L.BSrc},
      L.Compiler.BSrc.wf t s = true →
      bsrcOkB (toRiscvTab t) s = true
  | .arr a, h => by simpa [L.Compiler.BSrc.wf, bsrcOkB] using dom8_imp_bytePosOkB h
  | .rom d₀, h => by
    simp only [L.Compiler.BSrc.wf, Bool.and_eq_true] at h
    simpa [bsrcOkB] using romOk_imp_romSliceOkB h.1

private theorem opndWf_imp_exprOkTier0B {t : L.Compiler.Tab} {nl : Nat} {e : L.Expr}
    (h : L.Compiler.Expr.opndWf nl t e = true) :
    exprOkTier0B (toRiscvTab t) nl e = true := by
  simp only [L.Compiler.Expr.opndWf, Bool.and_eq_true] at h
  exact expr_wf_imp_exprOkTier0B_aux h.2

private theorem stmt_wf_imp_stmtOkTier0B_aux {t : L.Compiler.Tab} {p : L.Prog} {nl : Nat} :
    ∀ {inLoop : Bool} {s : L.Stmt},
      L.Compiler.Stmt.wf p nl t s = true →
      brkOkL inLoop s = true →
      noSt8L s = true →
      stmtOkTier0B (toRiscvTab t) p nl inLoop s = true
  | _, .skip, _, _, _ => rfl
  | _, .brk, _, hbrk, _ => by simpa [brkOkL, stmtOkTier0B] using hbrk
  | _, .abort e, h, _, _ => by
    simpa [L.Compiler.Stmt.wf, stmtOkTier0B] using expr_wf_imp_exprOkTier0B_aux h
  | _, .set _ e, h, _, _ | _, .gset _ e, h, _, _ => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true] at h
    simp only [stmtOkTier0B, Bool.and_eq_true]
    exact ⟨h.1, expr_wf_imp_exprOkTier0B_aux h.2⟩
  | _, .st8 _ _ _, _, _, hnost8 => by cases hnost8
  | _, .st64 _ i e, h, _, _ => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true] at h
    simp only [stmtOkTier0B, Bool.and_eq_true]
    exact ⟨⟨dom64_imp_wordPosOkB h.1.1, expr_wf_imp_exprOkTier0B_aux h.1.2⟩,
           expr_wf_imp_exprOkTier0B_aux h.2⟩
  | _, .seq s₁ s₂, h, hbrk, hnost8 => by
    simp only [L.Compiler.Stmt.wf, brkOkL, noSt8L, Bool.and_eq_true] at h hbrk hnost8
    simp only [stmtOkTier0B, Bool.and_eq_true]
    exact ⟨stmt_wf_imp_stmtOkTier0B_aux h.1 hbrk.1 hnost8.1,
           stmt_wf_imp_stmtOkTier0B_aux h.2 hbrk.2 hnost8.2⟩
  | _, .ite c s₁ s₂, h, hbrk, hnost8 => by
    simp only [L.Compiler.Stmt.wf, brkOkL, noSt8L, Bool.and_eq_true] at h hbrk hnost8
    simp only [stmtOkTier0B, Bool.and_eq_true]
    exact ⟨⟨cond_wf_imp_condOkTier0B_aux h.1.1, stmt_wf_imp_stmtOkTier0B_aux h.1.2 hbrk.1 hnost8.1⟩,
           stmt_wf_imp_stmtOkTier0B_aux h.2 hbrk.2 hnost8.2⟩
  | _, .while c s, h, hbrk, hnost8 => by
    simp only [L.Compiler.Stmt.wf, brkOkL, noSt8L, Bool.and_eq_true] at h hbrk hnost8
    simp only [stmtOkTier0B, Bool.and_eq_true]
    exact ⟨cond_wf_imp_condOkTier0B_aux h.1, stmt_wf_imp_stmtOkTier0B_aux h.2 hbrk hnost8⟩
  | _, .ret es, h, _, _ => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true, List.all_eq_true] at h
    simp only [stmtOkTier0B, Bool.and_eq_true, List.all_eq_true]
    refine ⟨decide_eq_true (of_decide_eq_true h.2), ?_⟩
    intro e he
    exact expr_wf_imp_exprOkTier0B_aux (h.1 e he)
  | _, .call xs f args, h, _, _ => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true, List.all_eq_true] at h
    simp only [stmtOkTier0B, Bool.and_eq_true,
      List.all_eq_true]
    rcases h with ⟨⟨⟨hxs, _hres⟩, hargs⟩, hcall⟩
    refine ⟨⟨?_, hxs⟩, ?_⟩
    · cases hlook : p.lookup f with
      | none => rw [hlook] at hcall; cases hcall
      | some fd => simp
    · intro e he
      exact expr_wf_imp_exprOkTier0B_aux (hargs e he)
  | _, .st64t a tt i e, h, _, _ => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true] at h
    simp only [stmtOkTier0B, Bool.and_eq_true]
    exact ⟨⟨⟨dom64_tier1_imp_tieredOkB h.1.1.1.1, expr_wf_imp_exprOkTier0B_aux h.1.1.2⟩,
             expr_wf_imp_exprOkTier0B_aux h.1.2⟩, expr_wf_imp_exprOkTier0B_aux h.2⟩
  | _, .st32t a tt i e, h, _, _ => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true] at h
    simp only [stmtOkTier0B, Bool.and_eq_true]
    exact ⟨⟨⟨tier32Ok_imp_tier32OkTier0B h.1.1.1.1, expr_wf_imp_exprOkTier0B_aux h.1.1.2⟩,
             expr_wf_imp_exprOkTier0B_aux h.1.2⟩, expr_wf_imp_exprOkTier0B_aux h.2⟩
  | _, .copy64 dst di src si n, h, _, _ => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true] at h
    simp only [stmtOkTier0B, Bool.and_eq_true]
    exact ⟨⟨⟨⟨warr_wf_imp_warrOkTier0B h.1.1.1.1, opndWf_imp_exprOkTier0B h.1.1.1.2⟩,
              warr_wf_imp_warrOkTier0B h.1.1.2⟩, opndWf_imp_exprOkTier0B h.1.2⟩,
              opndWf_imp_exprOkTier0B h.2⟩
  | _, .copy8w dst di src si n, h, _, _ => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true] at h
    simp only [stmtOkTier0B, Bool.and_eq_true]
    exact ⟨⟨⟨⟨warr_wf_imp_warrOkTier0B h.1.1.1.1, opndWf_imp_exprOkTier0B h.1.1.1.2⟩,
              bsrc_wf_imp_bsrcOkB h.1.1.2⟩, opndWf_imp_exprOkTier0B h.1.2⟩,
              opndWf_imp_exprOkTier0B h.2⟩
  | _, .scan8 x s i e c, h, _, _ => by
    simp only [L.Compiler.Stmt.wf, Bool.and_eq_true, beq_iff_eq] at h
    simp only [stmtOkTier0B, Bool.and_eq_true]
    have hclen : 256 ≤ c.length := by omega
    refine ⟨⟨⟨⟨⟨h.1.1.1.1.1, bsrc_wf_imp_bsrcOkB h.1.1.1.1.2⟩, opndWf_imp_exprOkTier0B h.1.1.1.2⟩,
              opndWf_imp_exprOkTier0B h.1.1.2⟩, by simpa using hclen⟩, romOk_imp_romSliceOkB h.2⟩

theorem stmt_wf_imp_stmtOkTier0B {t : L.Compiler.Tab} {p : L.Prog} {nl : Nat}
    {inLoop : Bool} {s : L.Stmt}
    (h : L.Compiler.Stmt.wf p nl t s = true)
    (hbrk : brkOkL inLoop s = true)
    (hnost8 : noSt8L s = true)
    (_hne : ∀ d ∈ L.Compiler.Stmt.roms s, d ≠ []) :
    stmtOkTier0B (toRiscvTab t) p nl inLoop s = true :=
  stmt_wf_imp_stmtOkTier0B_aux h hbrk hnost8

private theorem le_numLocalsFn (fd : L.FunDecl) :
    fd.nlocals ≤ numLocalsFn fd := by
  simp only [numLocalsFn]
  omega

/-! ## 4. Top-Level `checkerProgIMini_progOkTier0B` -/

theorem checkerProgIMini_progOkTier0B :
    progOkTier0B checkerTabMini checkerProgIMini = true := by
  have hwf := L.Checker.checkerProgI_wf
  rw [L.Compiler.Prog.wf_eq] at hwf
  simp only [L.Compiler.Prog.wfSpec, Bool.and_eq_true, List.all_eq_true] at hwf
  have hall := hwf.1.1
  have hbc := checkerProgI_brk_const0_all
  simp only [progOkTier0B, Bool.and_eq_true]
  refine ⟨⟨⟨checkerTabMini_arrAtOkB, by simpa using checkerTabMini_nres_pos⟩,
    decide_eq_true checkerProgIMini_fnNames_nodup⟩, ?_⟩
  simp only [checkerProgIMini, checkerTabMini, List.all_eq_true]
  intro x hx
  have hfx := hall x hx
  rw [L.Compiler.FunDecl.wf_eq] at hfx
  simp only [L.Compiler.FunDecl.wfSpec, Bool.and_eq_true] at hfx
  have hbcx := hbc x hx
  exact stmtOkTier0B_mono (le_numLocalsFn x.2)
    (stmt_wf_imp_stmtOkTier0B_aux hfx.1.2 hbcx.1 hbcx.2.2)

/-! ## 5. Top-Level `checkerProgMini_progOkTier0B` (via Fused `CheckerProgScan`) -/

private theorem fastDom8_sound {a : L.ArrId}
    (h : fastDom8 checkerLmapLit 2 a = true) : L.Checker.checkerTab.dom8 a = true := by
  unfold L.Compiler.Tab.dom8
  rw [checkerLmapLit_eq, checkerNb_eq]
  exact h

private theorem fastDom64_sound {s : L.TieredArray}
    (h : fastDom64 checkerLmapLit 2 s = true) : L.Checker.checkerTab.dom64 s = true := by
  unfold L.Compiler.Tab.dom64
  rw [checkerLmapLit_eq, checkerNb_eq]
  exact h

private theorem fastTier32_sound {a : L.ArrId} {e : L.Expr}
    (h : fastTier32 checkerLmapLit 2 a e = true) :
    tier32OkTier0B checkerTabMini a e = true := by
  apply tier32Ok_imp_tier32OkTier0B
  cases e with
  | const w =>
    simp only [fastTier32, Bool.and_eq_true] at h
    exact fastDom64_sound h.2
  | var _ | len8 _ | len64 _ | glob _ | bin _ _ _ | cmpw _ _ _ | ld8 _ _
  | ld64 _ _ | ldc _ _ | ld64t _ _ _ | ld32t _ _ _ | ld32h _ _ _ _ | len64t _ _ | ld8x8 _ _ =>
    exact fastDom64_sound h

private theorem fastExpr_sound {nl : Nat} : ∀ {e : L.Expr},
    fastExpr checkerLmapLit 2 12 nl e = true →
    (∀ d ∈ L.Compiler.Expr.roms e, checkerTabMini.romSliceOkB d = true) →
    exprOkTier0B checkerTabMini nl e = true
  | .const _, _, _ => rfl
  | .var x, h, _ => by simpa [fastExpr, exprOkTier0B] using h
  | .glob g, h, _ => by
    simp only [fastExpr, decide_eq_true_eq] at h
    simp only [exprOkTier0B, decide_eq_true_eq]
    rw [show checkerTabMini.ng = L.Checker.checkerTab.ng from rfl, checkerNg_eq]
    exact h
  | .bin _ a b, h, hr | .cmpw _ a b, h, hr => by
    simp only [fastExpr, Bool.and_eq_true, L.Compiler.Expr.roms, List.mem_append] at h hr
    simp only [exprOkTier0B, Bool.and_eq_true]
    exact ⟨fastExpr_sound h.1 fun d hd => hr d (.inl hd),
           fastExpr_sound h.2 fun d hd => hr d (.inr hd)⟩
  | .ld8 a i, h, hr => by
    simp only [fastExpr, Bool.and_eq_true, L.Compiler.Expr.roms] at h hr
    simp only [exprOkTier0B, Bool.and_eq_true]
    exact ⟨dom8_imp_bytePosOkB (fastDom8_sound h.1), fastExpr_sound h.2 hr⟩
  | .ld64 a i, h, hr => by
    simp only [fastExpr, Bool.and_eq_true, L.Compiler.Expr.roms] at h hr
    simp only [exprOkTier0B, Bool.and_eq_true]
    exact ⟨dom64_imp_wordPosOkB (fastDom64_sound h.1), fastExpr_sound h.2 hr⟩
  | .len8 a, h, _ => by
    simpa [checkerTabMini, exprOkTier0B] using dom8_imp_bytePosOkB (fastDom8_sound h)
  | .len64 a, h, _ => by
    simpa [checkerTabMini, exprOkTier0B] using dom64_imp_wordPosOkB (fastDom64_sound h)
  | .ldc d i, h, hr => by
    simp only [fastExpr, L.Compiler.Expr.roms, List.mem_cons] at h hr
    simp only [exprOkTier0B, Bool.and_eq_true]
    exact ⟨hr d (.inl rfl), fastExpr_sound h fun d' hd' => hr d' (.inr hd')⟩
  | .ld64t a tt i, h, hr | .ld32h a tt i _, h, hr => by
    simp only [fastExpr, Bool.and_eq_true, L.Compiler.Expr.roms, List.mem_append] at h hr
    simp only [exprOkTier0B, Bool.and_eq_true]
    exact ⟨⟨dom64_tier1_imp_tieredOkB (fastDom64_sound h.1.1),
            fastExpr_sound h.1.2 fun d hd => hr d (.inl hd)⟩,
            fastExpr_sound h.2 fun d hd => hr d (.inr hd)⟩
  | .ld32t a tt i, h, hr => by
    simp only [fastExpr, Bool.and_eq_true, L.Compiler.Expr.roms, List.mem_append] at h hr
    simp only [exprOkTier0B, Bool.and_eq_true]
    exact ⟨⟨fastTier32_sound h.1.1,
            fastExpr_sound h.1.2 fun d hd => hr d (.inl hd)⟩,
            fastExpr_sound h.2 fun d hd => hr d (.inr hd)⟩
  | .len64t a tt, h, hr => by
    simp only [fastExpr, Bool.and_eq_true, L.Compiler.Expr.roms] at h hr
    simp only [exprOkTier0B, Bool.and_eq_true]
    exact ⟨dom64_tier1_imp_tieredOkB (fastDom64_sound h.1), fastExpr_sound h.2 hr⟩
  | .ld8x8 s i, h, hr => by
    cases s with
    | arr a =>
      simp only [fastExpr, Bool.and_eq_true, L.Compiler.Expr.roms, L.Compiler.BSrc.roms, List.mem_append] at h hr
      simp only [exprOkTier0B, Bool.and_eq_true]
      exact ⟨dom8_imp_bytePosOkB (fastDom8_sound h.1), fastExpr_sound h.2 fun d hd => hr d (.inr hd)⟩
    | rom d₀ =>
      simp only [fastExpr, L.Compiler.Expr.roms, L.Compiler.BSrc.roms, List.mem_append, List.mem_singleton] at h hr
      simp only [exprOkTier0B, Bool.and_eq_true]
      exact ⟨hr d₀ (.inl rfl), fastExpr_sound h fun d hd => hr d (.inr hd)⟩

private theorem fastCond_sound {nl : Nat} : ∀ {c : L.Cond},
    fastCond checkerLmapLit 2 12 nl c = true →
    (∀ d ∈ L.Compiler.Cond.roms c, checkerTabMini.romSliceOkB d = true) →
    condOkTier0B checkerTabMini nl c = true
  | .cmp _ a b, h, hr => by
    simp only [fastCond, Bool.and_eq_true, L.Compiler.Cond.roms, List.mem_append] at h hr
    simp only [condOkTier0B, Bool.and_eq_true]
    exact ⟨fastExpr_sound h.1 fun d hd => hr d (.inl hd),
           fastExpr_sound h.2 fun d hd => hr d (.inr hd)⟩
  | .and p q, h, hr | .or p q, h, hr => by
    simp only [fastCond, Bool.and_eq_true, L.Compiler.Cond.roms, List.mem_append] at h hr
    simp only [condOkTier0B, Bool.and_eq_true]
    exact ⟨fastCond_sound h.1 fun d hd => hr d (.inl hd),
           fastCond_sound h.2 fun d hd => hr d (.inr hd)⟩
  | .not p, h, hr => fastCond_sound (c := p) h hr

private theorem fastWArr_sound {nl : Nat} : ∀ {w : L.WArr},
    fastWArr checkerLmapLit 2 12 nl w = true →
    (∀ d ∈ L.Compiler.WArr.roms w, checkerTabMini.romSliceOkB d = true) →
    warrOkTier0B checkerTabMini nl w = true
  | .plain a, h, _ => by
    simpa [checkerTabMini, warrOkTier0B] using dom64_imp_wordPosOkB (fastDom64_sound h)
  | .tier a tt, h, hr => by
    simp only [fastWArr, Bool.and_eq_true, L.Compiler.WArr.roms] at h hr
    simp only [warrOkTier0B, Bool.and_eq_true]
    exact ⟨dom64_tier1_imp_tieredOkB (fastDom64_sound h.1), fastExpr_sound h.2 hr⟩

private theorem fastBSrc_sound : ∀ {s : L.BSrc},
    fastBSrc checkerLmapLit 2 s = true →
    (∀ d ∈ L.Compiler.BSrc.roms s, checkerTabMini.romSliceOkB d = true) →
    bsrcOkB checkerTabMini s = true
  | .arr a, h, _ => by
    simpa [checkerTabMini, bsrcOkB] using dom8_imp_bytePosOkB (fastDom8_sound h)
  | .rom d₀, _, hr => by
    simp only [L.Compiler.BSrc.roms, List.mem_singleton] at hr
    simpa [bsrcOkB] using hr d₀ rfl

private theorem fastStmt_sound {nl : Nat}
    (htree : ∀ f, L.Checker.checkerProg_wf.tree.find (L.Compiler.nameCode f) =
      (L.Checker.checkerProg.lookup f).map (·.nparams)) :
    ∀ {inLoop : Bool} {s : L.Stmt},
      fastStmt checkerLmapLit 2 12 10 L.Checker.checkerProg_wf.tree nl inLoop s = true →
      (∀ d ∈ L.Compiler.Stmt.roms s, checkerTabMini.romSliceOkB d = true) →
      stmtOkTier0B checkerTabMini checkerProgMini nl inLoop s = true
  | _, .skip, _, _ => rfl
  | _, .brk, h, _ => h
  | _, .abort e, h, hr => fastExpr_sound h hr
  | _, .set x e, h, hr => by
    simp only [fastStmt, Bool.and_eq_true, L.Compiler.Stmt.roms] at h hr
    simp only [stmtOkTier0B, Bool.and_eq_true]
    exact ⟨h.1, fastExpr_sound h.2 hr⟩
  | _, .gset g e, h, hr => by
    simp only [fastStmt, Bool.and_eq_true, decide_eq_true_eq, L.Compiler.Stmt.roms] at h hr
    simp only [stmtOkTier0B, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, fastExpr_sound h.2 hr⟩
    rw [show checkerTabMini.ng = L.Checker.checkerTab.ng from rfl, checkerNg_eq]
    exact h.1
  | _, .st8 _ _ _, h, _ => by cases h
  | _, .st64 a i e, h, hr => by
    simp only [fastStmt, Bool.and_eq_true, L.Compiler.Stmt.roms, List.mem_append] at h hr
    simp only [stmtOkTier0B, Bool.and_eq_true]
    exact ⟨⟨dom64_imp_wordPosOkB (fastDom64_sound h.1.1), fastExpr_sound h.1.2 fun d hd => hr d (.inl hd)⟩,
           fastExpr_sound h.2 fun d hd => hr d (.inr hd)⟩
  | _, .seq s₁ s₂, h, hr => by
    simp only [fastStmt, Bool.and_eq_true, L.Compiler.Stmt.roms, List.mem_append] at h hr
    simp only [stmtOkTier0B, Bool.and_eq_true]
    exact ⟨fastStmt_sound htree h.1 fun d hd => hr d (.inl hd),
           fastStmt_sound htree h.2 fun d hd => hr d (.inr hd)⟩
  | _, .ite c s₁ s₂, h, hr => by
    simp only [fastStmt, Bool.and_eq_true, L.Compiler.Stmt.roms, List.mem_append] at h hr
    simp only [stmtOkTier0B, Bool.and_eq_true]
    exact ⟨⟨fastCond_sound h.1.1 fun d hd => hr d (.inl (.inl hd)),
            fastStmt_sound htree h.1.2 fun d hd => hr d (.inl (.inr hd))⟩,
           fastStmt_sound htree h.2 fun d hd => hr d (.inr hd)⟩
  | _, .while c s, h, hr => by
    simp only [fastStmt, Bool.and_eq_true, L.Compiler.Stmt.roms, List.mem_append] at h hr
    simp only [stmtOkTier0B, Bool.and_eq_true]
    exact ⟨fastCond_sound h.1 fun d hd => hr d (.inl hd),
           fastStmt_sound htree h.2 fun d hd => hr d (.inr hd)⟩
  | _, .ret es, h, hr => by
    simp only [fastStmt, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      L.Compiler.Stmt.roms, List.mem_flatMap] at h hr
    simp only [stmtOkTier0B, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true]
    refine ⟨?_, ?_⟩
    · rw [show checkerTabMini.nres = L.Checker.checkerTab.nres from rfl, checkerNres_eq]
      simpa using h.1
    · intro e he
      exact fastExpr_sound (h.2 e he) fun d hd => hr d ⟨e, he, hd⟩
  | _, .call xs f args, h, hr => by
    simp only [fastStmt, Bool.and_eq_true, List.all_eq_true,
      L.Compiler.Stmt.roms, List.mem_flatMap] at h hr
    simp only [stmtOkTier0B, checkerProgMini,
      Bool.and_eq_true, List.all_eq_true]
    rw [htree f] at h
    refine ⟨⟨?_, of_decide_eq_true h.1.2⟩, ?_⟩
    · cases hlook : L.Checker.checkerProg.lookup f with
      | none => rw [hlook] at h; cases h.1.1
      | some fd => simp
    · intro e he
      exact fastExpr_sound (h.2 e he) fun d hd => hr d ⟨e, he, hd⟩
  | _, .st64t a tt i e, h, hr => by
    simp only [fastStmt, Bool.and_eq_true, L.Compiler.Stmt.roms, List.mem_append] at h hr
    simp only [stmtOkTier0B, Bool.and_eq_true]
    exact ⟨⟨⟨dom64_tier1_imp_tieredOkB (fastDom64_sound h.1.1.1),
             fastExpr_sound h.1.1.2 fun d hd => hr d (.inl (.inl hd))⟩,
             fastExpr_sound h.1.2 fun d hd => hr d (.inl (.inr hd))⟩,
             fastExpr_sound h.2 fun d hd => hr d (.inr hd)⟩
  | _, .st32t a tt i e, h, hr => by
    simp only [fastStmt, Bool.and_eq_true, L.Compiler.Stmt.roms, List.mem_append] at h hr
    simp only [stmtOkTier0B, Bool.and_eq_true]
    exact ⟨⟨⟨fastTier32_sound h.1.1.1,
             fastExpr_sound h.1.1.2 fun d hd => hr d (.inl (.inl hd))⟩,
             fastExpr_sound h.1.2 fun d hd => hr d (.inl (.inr hd))⟩,
             fastExpr_sound h.2 fun d hd => hr d (.inr hd)⟩
  | _, .copy64 dst di src si n, h, hr => by
    simp only [fastStmt, Bool.and_eq_true, L.Compiler.Stmt.roms, List.mem_append] at h hr
    simp only [stmtOkTier0B, Bool.and_eq_true]
    exact ⟨⟨⟨⟨fastWArr_sound h.1.1.1.1 fun d hd => hr d (.inl (.inl (.inl (.inl hd)))),
              fastExpr_sound h.1.1.1.2 fun d hd => hr d (.inl (.inl (.inl (.inr hd))))⟩,
              fastWArr_sound h.1.1.2 fun d hd => hr d (.inl (.inl (.inr hd)))⟩,
              fastExpr_sound h.1.2 fun d hd => hr d (.inl (.inr hd))⟩,
              fastExpr_sound h.2 fun d hd => hr d (.inr hd)⟩
  | _, .copy8w dst di src si n, h, hr => by
    simp only [fastStmt, Bool.and_eq_true, L.Compiler.Stmt.roms, List.mem_append] at h hr
    simp only [stmtOkTier0B, Bool.and_eq_true]
    exact ⟨⟨⟨⟨fastWArr_sound h.1.1.1.1 fun d hd => hr d (.inl (.inl (.inl (.inl hd)))),
              fastExpr_sound h.1.1.1.2 fun d hd => hr d (.inl (.inl (.inl (.inr hd))))⟩,
              fastBSrc_sound h.1.1.2 fun d hd => hr d (.inl (.inl (.inr hd)))⟩,
              fastExpr_sound h.1.2 fun d hd => hr d (.inl (.inr hd))⟩,
              fastExpr_sound h.2 fun d hd => hr d (.inr hd)⟩
  | _, .scan8 x s i e c, h, hr => by
    simp only [fastStmt, Bool.and_eq_true, L.Compiler.Stmt.roms,
      List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at h hr
    simp only [stmtOkTier0B, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨h.1.1.1.1,
                fastBSrc_sound h.1.1.1.2 fun d hd => hr d (.inl (.inl (.inl hd)))⟩,
               fastExpr_sound h.1.1.2 fun d hd => hr d (.inl (.inl (.inr hd)))⟩,
              fastExpr_sound h.1.2 fun d hd => hr d (.inl (.inr hd))⟩,
             h.2⟩,
            hr c (.inr rfl)⟩

theorem checkerProgMini_progOkTier0B :
    progOkTier0B checkerTabMini checkerProgMini = true := by
  have htree := (L.Compiler.progTree_spec L.Checker.checkerProg_wf.tree_eq).2
  have hroms := checkerTabMini_romSlices_ok.1
  simp only [progOkTier0B, Bool.and_eq_true]
  refine ⟨⟨⟨checkerTabMini_arrAtOkB, by simpa using checkerTabMini_nres_pos⟩,
    decide_eq_true checkerProgMini_fnNames_nodup⟩, ?_⟩
  simp only [checkerProgMini, List.all_eq_true]
  intro x hx
  exact stmtOkTier0B_mono (le_numLocalsFn x.2)
    (fastStmt_sound htree (checkerProg_fastStmt_all x hx) (hroms x hx))

/-! ## 6. Strict `t = .const 0` Specialization (`progOkConst0B`) -/

private def const0OnlyE : L.Expr → Bool
  | .bin _ a b | .cmpw _ a b => const0OnlyE a && const0OnlyE b
  | .ld8 _ i | .ld64 _ i | .ldc _ i | .ld8x8 _ i => const0OnlyE i
  | .ld64t _ t i | .ld32h _ t i _ => const0OnlyE t && const0OnlyE i
  | .len64t _ t => const0OnlyE t
  | .ld32t _ t i =>
    (match t with | .const w => w == 0 || w.toNat % 2 == 1 | _ => true) &&
    const0OnlyE t && const0OnlyE i
  | _ => true

private def const0OnlyC : L.Cond → Bool
  | .cmp _ a b => const0OnlyE a && const0OnlyE b
  | .and p q | .or p q => const0OnlyC p && const0OnlyC q
  | .not p => const0OnlyC p

private def const0OnlyS : L.Stmt → Bool
  | .abort e | .set _ e | .gset _ e => const0OnlyE e
  | .st8 _ i e | .st64 _ i e => const0OnlyE i && const0OnlyE e
  | .seq s₁ s₂ => const0OnlyS s₁ && const0OnlyS s₂
  | .ite c s₁ s₂ => const0OnlyC c && const0OnlyS s₁ && const0OnlyS s₂
  | .while c s => const0OnlyC c && const0OnlyS s
  | .ret es | .call _ _ es => es.all const0OnlyE
  | .st64t _ t i e => const0OnlyE t && const0OnlyE i && const0OnlyE e
  | .st32t _ t i e =>
    (match t with | .const w => w == 0 || w.toNat % 2 == 1 | _ => true) &&
    const0OnlyE t && const0OnlyE i && const0OnlyE e
  | .copy64 d di s si n =>
    (match d with | .tier _ t => const0OnlyE t | _ => true) && const0OnlyE di &&
    (match s with | .tier _ t => const0OnlyE t | _ => true) && const0OnlyE si && const0OnlyE n
  | .copy8w d di _ si n =>
    (match d with | .tier _ t => const0OnlyE t | _ => true) && const0OnlyE di && const0OnlyE si && const0OnlyE n
  | .scan8 _ _ i e _ => const0OnlyE i && const0OnlyE e
  | _ => true

private theorem tier32OkTier0B_imp_const0 {tab : Tab} {a : L.ArrId} {t : L.Expr}
    (hc : (match t with | .const w => w == 0 || w.toNat % 2 == 1 | _ => true) = true)
    (h : tier32OkTier0B tab a t = true) :
    tier32OkConst0B tab a t = true := by
  cases t with
  | const w =>
    simp only [Bool.or_eq_true, beq_iff_eq] at hc
    rcases hc with rfl | hodd
    · simpa [tier32OkTier0B, tier32OkConst0B] using h
    · simp only [tier32OkTier0B, hodd, beq_iff_eq, Nat.one_ne_zero, ↓reduceIte] at h
      have hw0 : w ≠ 0 := by intro h0; subst h0; simp at hodd
      simpa [tier32OkConst0B, hw0] using h
  | var _ | len8 _ | len64 _ | glob _ | bin _ _ _ | cmpw _ _ _ | ld8 _ _
  | ld64 _ _ | ldc _ _ | ld64t _ _ _ | ld32t _ _ _ | ld32h _ _ _ _ | len64t _ _ | ld8x8 _ _ =>
    exact h

private theorem exprOkTier0B_imp_const0 {tab : Tab} {nl : Nat} :
    ∀ {e : L.Expr},
      const0OnlyE e = true → exprOkTier0B tab nl e = true → exprOkConst0B tab nl e = true
  | .const _, _, h | .var _, _, h | .len8 _, _, h | .len64 _, _, h | .glob _, _, h => h
  | .bin _ a b, hc, h | .cmpw _ a b, hc, h => by
    simp only [const0OnlyE, exprOkTier0B, exprOkConst0B, Bool.and_eq_true] at hc h ⊢
    exact ⟨exprOkTier0B_imp_const0 hc.1 h.1, exprOkTier0B_imp_const0 hc.2 h.2⟩
  | .ld8 _ i, hc, h | .ld64 _ i, hc, h | .ldc _ i, hc, h | .len64t _ i, hc, h
  | .ld8x8 (.arr _) i, hc, h | .ld8x8 (.rom _) i, hc, h => by
    simp only [const0OnlyE, exprOkTier0B, exprOkConst0B, Bool.and_eq_true] at hc h ⊢
    exact ⟨h.1, exprOkTier0B_imp_const0 hc h.2⟩
  | .ld64t _ t i, hc, h | .ld32h _ t i _, hc, h => by
    simp only [const0OnlyE, exprOkTier0B, exprOkConst0B, Bool.and_eq_true] at hc h ⊢
    exact ⟨⟨h.1.1, exprOkTier0B_imp_const0 hc.1 h.1.2⟩, exprOkTier0B_imp_const0 hc.2 h.2⟩
  | .ld32t _ t i, hc, h => by
    simp only [const0OnlyE, exprOkTier0B, exprOkConst0B, Bool.and_eq_true] at hc h ⊢
    exact ⟨⟨tier32OkTier0B_imp_const0 hc.1.1 h.1.1, exprOkTier0B_imp_const0 hc.1.2 h.1.2⟩,
           exprOkTier0B_imp_const0 hc.2 h.2⟩

private theorem condOkTier0B_imp_const0 {tab : Tab} {nl : Nat} :
    ∀ {c : L.Cond},
      const0OnlyC c = true → condOkTier0B tab nl c = true → condOkConst0B tab nl c = true
  | .cmp _ a b, hc, h => by
    simp only [const0OnlyC, condOkTier0B, condOkConst0B, Bool.and_eq_true] at hc h ⊢
    exact ⟨exprOkTier0B_imp_const0 hc.1 h.1, exprOkTier0B_imp_const0 hc.2 h.2⟩
  | .and p q, hc, h | .or p q, hc, h => by
    simp only [const0OnlyC, condOkTier0B, condOkConst0B, Bool.and_eq_true] at hc h ⊢
    exact ⟨condOkTier0B_imp_const0 hc.1 h.1, condOkTier0B_imp_const0 hc.2 h.2⟩
  | .not p, hc, h => condOkTier0B_imp_const0 (c := p) hc h

private theorem warrOkTier0B_imp_const0 {tab : Tab} {nl : Nat} :
    ∀ {w : L.WArr},
      (match w with | .tier _ t => const0OnlyE t | _ => true) = true →
      warrOkTier0B tab nl w = true → warrOkConst0B tab nl w = true
  | .plain _, _, h => h
  | .tier _ _, ht, h => by
    simp only [warrOkTier0B, warrOkConst0B, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, exprOkTier0B_imp_const0 ht h.2⟩

private theorem stmtOkTier0B_imp_const0 {tab : Tab} {p : L.Prog} {nl : Nat} :
    ∀ {inLoop : Bool} {s : L.Stmt},
      const0OnlyS s = true →
      stmtOkTier0B tab p nl inLoop s = true → stmtOkConst0B tab p nl inLoop s = true
  | _, .skip, _, h | _, .brk, _, h => h
  | _, .abort _, hc, h => exprOkTier0B_imp_const0 hc h
  | _, .set _ _, hc, h | _, .gset _ _, hc, h => by
    simp only [const0OnlyS, stmtOkTier0B, stmtOkConst0B, Bool.and_eq_true] at hc h ⊢
    exact ⟨h.1, exprOkTier0B_imp_const0 hc h.2⟩
  | _, .st8 _ _ _, _, h => h
  | _, .st64 _ _ _, hc, h => by
    simp only [const0OnlyS, stmtOkTier0B, stmtOkConst0B, Bool.and_eq_true] at hc h ⊢
    exact ⟨⟨h.1.1, exprOkTier0B_imp_const0 hc.1 h.1.2⟩, exprOkTier0B_imp_const0 hc.2 h.2⟩
  | _, .seq _ _, hc, h => by
    simp only [const0OnlyS, stmtOkTier0B, stmtOkConst0B, Bool.and_eq_true] at hc h ⊢
    exact ⟨stmtOkTier0B_imp_const0 hc.1 h.1, stmtOkTier0B_imp_const0 hc.2 h.2⟩
  | _, .ite _ _ _, hc, h => by
    simp only [const0OnlyS, stmtOkTier0B, stmtOkConst0B, Bool.and_eq_true] at hc h ⊢
    exact ⟨⟨condOkTier0B_imp_const0 hc.1.1 h.1.1, stmtOkTier0B_imp_const0 hc.1.2 h.1.2⟩,
           stmtOkTier0B_imp_const0 hc.2 h.2⟩
  | _, .while _ _, hc, h => by
    simp only [const0OnlyS, stmtOkTier0B, stmtOkConst0B, Bool.and_eq_true] at hc h ⊢
    exact ⟨condOkTier0B_imp_const0 hc.1 h.1, stmtOkTier0B_imp_const0 hc.2 h.2⟩
  | _, .ret _, hc, h => by
    simp only [const0OnlyS, stmtOkTier0B, stmtOkConst0B, Bool.and_eq_true, List.all_eq_true] at hc h ⊢
    exact ⟨h.1, fun e he => exprOkTier0B_imp_const0 (hc e he) (h.2 e he)⟩
  | _, .call _ _ _, hc, h => by
    simp only [const0OnlyS, stmtOkTier0B, stmtOkConst0B, Bool.and_eq_true, List.all_eq_true] at hc h ⊢
    exact ⟨h.1, fun e he => exprOkTier0B_imp_const0 (hc e he) (h.2 e he)⟩
  | _, .st64t _ _ _ _, hc, h => by
    simp only [const0OnlyS, stmtOkTier0B, stmtOkConst0B, Bool.and_eq_true] at hc h ⊢
    exact ⟨⟨⟨h.1.1.1, exprOkTier0B_imp_const0 hc.1.1 h.1.1.2⟩, exprOkTier0B_imp_const0 hc.1.2 h.1.2⟩,
           exprOkTier0B_imp_const0 hc.2 h.2⟩
  | _, .st32t _ _ _ _, hc, h => by
    simp only [const0OnlyS, stmtOkTier0B, stmtOkConst0B, Bool.and_eq_true] at hc h ⊢
    exact ⟨⟨⟨tier32OkTier0B_imp_const0 hc.1.1.1 h.1.1.1, exprOkTier0B_imp_const0 hc.1.1.2 h.1.1.2⟩,
            exprOkTier0B_imp_const0 hc.1.2 h.1.2⟩, exprOkTier0B_imp_const0 hc.2 h.2⟩
  | _, .copy64 _ _ _ _ _, hc, h => by
    simp only [const0OnlyS, stmtOkTier0B, stmtOkConst0B, Bool.and_eq_true] at hc h ⊢
    exact ⟨⟨⟨⟨warrOkTier0B_imp_const0 hc.1.1.1.1 h.1.1.1.1,
              exprOkTier0B_imp_const0 hc.1.1.1.2 h.1.1.1.2⟩,
              warrOkTier0B_imp_const0 hc.1.1.2 h.1.1.2⟩,
              exprOkTier0B_imp_const0 hc.1.2 h.1.2⟩,
              exprOkTier0B_imp_const0 hc.2 h.2⟩
  | _, .copy8w _ _ _ _ _, hc, h => by
    simp only [const0OnlyS, stmtOkTier0B, stmtOkConst0B, Bool.and_eq_true] at hc h ⊢
    exact ⟨⟨⟨⟨warrOkTier0B_imp_const0 hc.1.1.1 h.1.1.1.1,
              exprOkTier0B_imp_const0 hc.1.1.2 h.1.1.1.2⟩, h.1.1.2⟩,
              exprOkTier0B_imp_const0 hc.1.2 h.1.2⟩,
              exprOkTier0B_imp_const0 hc.2 h.2⟩
  | _, .scan8 _ _ _ _ _, hc, h => by
    simp only [const0OnlyS, stmtOkTier0B, stmtOkConst0B, Bool.and_eq_true] at hc h ⊢
    exact ⟨⟨⟨⟨⟨h.1.1.1.1.1, h.1.1.1.1.2⟩, exprOkTier0B_imp_const0 hc.1 h.1.1.1.2⟩,
              exprOkTier0B_imp_const0 hc.2 h.1.1.2⟩, h.1.2⟩, h.2⟩

private theorem fastExpr_const0 {nl : Nat} : ∀ {e : L.Expr},
    fastExpr checkerLmapLit 2 12 nl e = true → const0OnlyE e = true
  | .const _, _ | .var _, _ | .len8 _, _ | .len64 _, _ | .glob _, _ => rfl
  | .bin _ a b, h | .cmpw _ a b, h => by
    simp only [fastExpr, Bool.and_eq_true] at h
    simp only [const0OnlyE, Bool.and_eq_true]
    exact ⟨fastExpr_const0 (e := a) h.1, fastExpr_const0 (e := b) h.2⟩
  | .ld8 _ i, h | .ld64 _ i, h | .len64t _ i, h => by
    simp only [fastExpr, Bool.and_eq_true] at h
    exact fastExpr_const0 (e := i) h.2
  | .ldc _ i, h => fastExpr_const0 (e := i) h
  | .ld64t _ t i, h | .ld32h _ t i _, h => by
    simp only [fastExpr, Bool.and_eq_true] at h
    simp only [const0OnlyE, Bool.and_eq_true]
    exact ⟨fastExpr_const0 (e := t) h.1.2, fastExpr_const0 (e := i) h.2⟩
  | .ld32t _ t i, h => by
    simp only [fastExpr, Bool.and_eq_true] at h
    simp only [const0OnlyE, Bool.and_eq_true]
    refine ⟨⟨?_, fastExpr_const0 (e := t) h.1.2⟩, fastExpr_const0 (e := i) h.2⟩
    have h32 := h.1.1
    cases t with
    | const _ => simp only [fastTier32, Bool.and_eq_true] at h32; exact h32.1
    | _ => rfl
  | .ld8x8 (.arr _) i, h => by
    simp only [fastExpr, Bool.and_eq_true] at h
    exact fastExpr_const0 (e := i) h.2
  | .ld8x8 (.rom _) i, h => fastExpr_const0 (e := i) h

private theorem fastCond_const0 {nl : Nat} : ∀ {c : L.Cond},
    fastCond checkerLmapLit 2 12 nl c = true → const0OnlyC c = true
  | .cmp _ _ _, h => by
    simp only [fastCond, Bool.and_eq_true] at h
    simp only [const0OnlyC, Bool.and_eq_true]
    exact ⟨fastExpr_const0 h.1, fastExpr_const0 h.2⟩
  | .and p q, h | .or p q, h => by
    simp only [fastCond, Bool.and_eq_true] at h
    simp only [const0OnlyC, Bool.and_eq_true]
    exact ⟨fastCond_const0 (c := p) h.1, fastCond_const0 (c := q) h.2⟩
  | .not p, h => fastCond_const0 (c := p) h

private theorem fastWArr_const0 {nl : Nat} : ∀ {w : L.WArr},
    fastWArr checkerLmapLit 2 12 nl w = true →
    (match w with | .tier _ t => const0OnlyE t | _ => true) = true
  | .plain _, _ => rfl
  | .tier _ _, h => by
    simp only [fastWArr, Bool.and_eq_true] at h
    exact fastExpr_const0 h.2

private theorem fastStmt_const0 {nl : Nat} {inLoop : Bool} : ∀ {s : L.Stmt},
    fastStmt checkerLmapLit 2 12 10 L.Checker.checkerProg_wf.tree nl inLoop s = true →
    const0OnlyS s = true
  | .skip, _ | .brk, _ => rfl
  | .abort _, h => fastExpr_const0 h
  | .set _ _, h | .gset _ _, h => by
    simp only [fastStmt, Bool.and_eq_true] at h
    exact fastExpr_const0 h.2
  | .st8 _ _ _, h => by cases h
  | .st64 _ _ _, h => by
    simp only [fastStmt, Bool.and_eq_true] at h
    simp only [const0OnlyS, Bool.and_eq_true]
    exact ⟨fastExpr_const0 h.1.2, fastExpr_const0 h.2⟩
  | .seq _ _, h => by
    simp only [fastStmt, Bool.and_eq_true] at h
    simp only [const0OnlyS, Bool.and_eq_true]
    exact ⟨fastStmt_const0 h.1, fastStmt_const0 h.2⟩
  | .ite _ _ _, h => by
    simp only [fastStmt, Bool.and_eq_true] at h
    simp only [const0OnlyS, Bool.and_eq_true]
    exact ⟨⟨fastCond_const0 h.1.1, fastStmt_const0 h.1.2⟩, fastStmt_const0 h.2⟩
  | .while _ _, h => by
    simp only [fastStmt, Bool.and_eq_true] at h
    simp only [const0OnlyS, Bool.and_eq_true]
    exact ⟨fastCond_const0 h.1, fastStmt_const0 h.2⟩
  | .ret _, h => by
    simp only [fastStmt, Bool.and_eq_true, List.all_eq_true] at h
    simp only [const0OnlyS, List.all_eq_true]
    intro e he
    exact fastExpr_const0 (h.2 e he)
  | .call _ _ _, h => by
    simp only [fastStmt, Bool.and_eq_true, List.all_eq_true] at h
    simp only [const0OnlyS, List.all_eq_true]
    intro e he
    exact fastExpr_const0 (h.2 e he)
  | .st64t _ _ _ _, h => by
    simp only [fastStmt, Bool.and_eq_true] at h
    simp only [const0OnlyS, Bool.and_eq_true]
    exact ⟨⟨fastExpr_const0 h.1.1.2, fastExpr_const0 h.1.2⟩, fastExpr_const0 h.2⟩
  | .st32t _ t _ _, h => by
    simp only [fastStmt, Bool.and_eq_true] at h
    simp only [const0OnlyS, Bool.and_eq_true]
    refine ⟨⟨⟨?_, fastExpr_const0 h.1.1.2⟩, fastExpr_const0 h.1.2⟩, fastExpr_const0 h.2⟩
    have h32 := h.1.1.1
    cases t with
    | const _ => simp only [fastTier32, Bool.and_eq_true] at h32; exact h32.1
    | _ => rfl
  | .copy64 _ _ _ _ _, h => by
    simp only [fastStmt, Bool.and_eq_true] at h
    simp only [const0OnlyS, Bool.and_eq_true]
    exact ⟨⟨⟨⟨fastWArr_const0 h.1.1.1.1, fastExpr_const0 h.1.1.1.2⟩,
              fastWArr_const0 h.1.1.2⟩, fastExpr_const0 h.1.2⟩, fastExpr_const0 h.2⟩
  | .copy8w _ _ _ _ _, h => by
    simp only [fastStmt, Bool.and_eq_true] at h
    simp only [const0OnlyS, Bool.and_eq_true]
    exact ⟨⟨⟨fastWArr_const0 h.1.1.1.1, fastExpr_const0 h.1.1.1.2⟩,
             fastExpr_const0 h.1.2⟩, fastExpr_const0 h.2⟩
  | .scan8 _ _ _ _ _, h => by
    simp only [fastStmt, Bool.and_eq_true] at h
    simp only [const0OnlyS, Bool.and_eq_true]
    exact ⟨fastExpr_const0 h.1.1.2, fastExpr_const0 h.1.2⟩

private theorem const0OnlyL_E_sound : ∀ {e : L.Expr},
    const0OnlyL_E e = true → const0OnlyE e = true
  | .const _, _ | .var _, _ | .len8 _, _ | .len64 _, _ | .glob _, _ => rfl
  | .bin _ a b, h | .cmpw _ a b, h => by
    simp only [const0OnlyL_E, Bool.and_eq_true] at h
    simp only [const0OnlyE, Bool.and_eq_true]
    exact ⟨const0OnlyL_E_sound (e := a) h.1, const0OnlyL_E_sound (e := b) h.2⟩
  | .ld8 _ i, h | .ld64 _ i, h | .ldc _ i, h | .len64t _ i, h
  | .ld8x8 (.arr _) i, h | .ld8x8 (.rom _) i, h => by
    simp only [const0OnlyL_E] at h
    exact const0OnlyL_E_sound (e := i) h
  | .ld64t _ t i, h | .ld32h _ t i _, h => by
    simp only [const0OnlyL_E, Bool.and_eq_true] at h
    simp only [const0OnlyE, Bool.and_eq_true]
    exact ⟨const0OnlyL_E_sound (e := t) h.1, const0OnlyL_E_sound (e := i) h.2⟩
  | .ld32t _ t i, h => by
    simp only [const0OnlyL_E, Bool.and_eq_true] at h
    simp only [const0OnlyE, Bool.and_eq_true]
    refine ⟨⟨?_, const0OnlyL_E_sound (e := t) h.1.2⟩, const0OnlyL_E_sound (e := i) h.2⟩
    cases t <;> exact h.1.1

private theorem const0OnlyL_C_sound : ∀ {c : L.Cond},
    const0OnlyL_C c = true → const0OnlyC c = true
  | .cmp _ _ _, h => by
    simp only [const0OnlyL_C, Bool.and_eq_true] at h
    simp only [const0OnlyC, Bool.and_eq_true]
    exact ⟨const0OnlyL_E_sound h.1, const0OnlyL_E_sound h.2⟩
  | .and p q, h | .or p q, h => by
    simp only [const0OnlyL_C, Bool.and_eq_true] at h
    simp only [const0OnlyC, Bool.and_eq_true]
    exact ⟨const0OnlyL_C_sound (c := p) h.1, const0OnlyL_C_sound (c := q) h.2⟩
  | .not p, h => const0OnlyL_C_sound (c := p) h

private theorem const0OnlyL_S_sound : ∀ {s : L.Stmt},
    const0OnlyL_S s = true → const0OnlyS s = true
  | .skip, _ | .brk, _ => rfl
  | .abort _, h | .set _ _, h | .gset _ _, h => const0OnlyL_E_sound h
  | .st8 _ _ _, h | .st64 _ _ _, h | .scan8 _ _ _ _ _, h => by
    simp only [const0OnlyL_S, Bool.and_eq_true] at h
    simp only [const0OnlyS, Bool.and_eq_true]
    exact ⟨const0OnlyL_E_sound h.1, const0OnlyL_E_sound h.2⟩
  | .seq _ _, h => by
    simp only [const0OnlyL_S, Bool.and_eq_true] at h
    simp only [const0OnlyS, Bool.and_eq_true]
    exact ⟨const0OnlyL_S_sound h.1, const0OnlyL_S_sound h.2⟩
  | .ite _ _ _, h => by
    simp only [const0OnlyL_S, Bool.and_eq_true] at h
    simp only [const0OnlyS, Bool.and_eq_true]
    exact ⟨⟨const0OnlyL_C_sound h.1.1, const0OnlyL_S_sound h.1.2⟩, const0OnlyL_S_sound h.2⟩
  | .while _ _, h => by
    simp only [const0OnlyL_S, Bool.and_eq_true] at h
    simp only [const0OnlyS, Bool.and_eq_true]
    exact ⟨const0OnlyL_C_sound h.1, const0OnlyL_S_sound h.2⟩
  | .ret _, h | .call _ _ _, h => by
    simp only [const0OnlyL_S, List.all_eq_true] at h
    simp only [const0OnlyS, List.all_eq_true]
    intro e he
    exact const0OnlyL_E_sound (h e he)
  | .st64t _ _ _ _, h => by
    simp only [const0OnlyL_S, Bool.and_eq_true] at h
    simp only [const0OnlyS, Bool.and_eq_true]
    exact ⟨⟨const0OnlyL_E_sound h.1.1, const0OnlyL_E_sound h.1.2⟩, const0OnlyL_E_sound h.2⟩
  | .st32t _ t _ _, h => by
    simp only [const0OnlyL_S, Bool.and_eq_true] at h
    simp only [const0OnlyS, Bool.and_eq_true]
    refine ⟨⟨⟨?_, const0OnlyL_E_sound h.1.1.2⟩, const0OnlyL_E_sound h.1.2⟩, const0OnlyL_E_sound h.2⟩
    cases t <;> exact h.1.1.1
  | .copy64 d _ s _ _, h => by
    simp only [const0OnlyL_S, Bool.and_eq_true] at h
    simp only [const0OnlyS, Bool.and_eq_true]
    refine ⟨⟨⟨⟨?_, const0OnlyL_E_sound h.1.1.1.2⟩, ?_⟩, const0OnlyL_E_sound h.1.2⟩,
      const0OnlyL_E_sound h.2⟩
    · cases d with | plain _ => rfl | tier _ _ => exact const0OnlyL_E_sound h.1.1.1.1
    · cases s with | plain _ => rfl | tier _ _ => exact const0OnlyL_E_sound h.1.1.2
  | .copy8w d _ _ _ _, h => by
    simp only [const0OnlyL_S, Bool.and_eq_true] at h
    simp only [const0OnlyS, Bool.and_eq_true]
    refine ⟨⟨⟨?_, const0OnlyL_E_sound h.1.1.2⟩, const0OnlyL_E_sound h.1.2⟩,
      const0OnlyL_E_sound h.2⟩
    cases d with | plain _ => rfl | tier _ _ => exact const0OnlyL_E_sound h.1.1.1

private theorem checkerProg_const0Only :
    checkerProgMini.all (fun (_, fd) => const0OnlyS fd.body) = true := by
  simp only [checkerProgMini, List.all_eq_true]
  intro x hx
  exact fastStmt_const0 (checkerProg_fastStmt_all x hx)

private theorem checkerProgI_const0Only :
    checkerProgIMini.all (fun (_, fd) => const0OnlyS fd.body) = true := by
  simp only [checkerProgIMini, List.all_eq_true]
  intro x hx
  exact const0OnlyL_S_sound (checkerProgI_brk_const0_all x hx).2.1

theorem checkerProgMini_progOkConst0B :
    progOkConst0B checkerTabMini checkerProgMini = true := by
  have h0 := checkerProgMini_progOkTier0B
  have hc := List.all_eq_true.mp checkerProg_const0Only
  simp only [progOkTier0B, progOkConst0B, Bool.and_eq_true, List.all_eq_true] at h0 ⊢
  exact ⟨h0.1, fun x hx => stmtOkTier0B_imp_const0 (hc x hx) (h0.2 x hx)⟩

theorem checkerProgIMini_progOkConst0B :
    progOkConst0B checkerTabMini checkerProgIMini = true := by
  have h0 := checkerProgIMini_progOkTier0B
  have hc := List.all_eq_true.mp checkerProgI_const0Only
  simp only [progOkTier0B, progOkConst0B, Bool.and_eq_true, List.all_eq_true] at h0 ⊢
  exact ⟨h0.1, fun x hx => stmtOkTier0B_imp_const0 (hc x hx) (h0.2 x hx)⟩

private theorem tier32OkTier0B_eq (tab : Tab) (a : L.ArrId)
    (t : L.Expr) :
    tier32OkTier0B tab a t = ConAgua.RISCV.Compiler.tier32OkB tab a t := by
  cases t <;> rfl

private theorem exprOkTier0B_eq (tab : Tab) (nl : Nat) (e : L.Expr) :
    exprOkTier0B tab nl e = ConAgua.RISCV.Compiler.exprOkB tab nl e := by
  induction e with
  | const _ | var _ | len8 _ | len64 _ | glob _ => rfl
  | bin _ _ _ iha ihb | cmpw _ _ _ iha ihb =>
    simp only [exprOkTier0B, ConAgua.RISCV.Compiler.exprOkB, iha, ihb]
  | ld8 _ _ ih | ld64 _ _ ih | ldc _ _ ih | len64t _ _ ih =>
    simp only [exprOkTier0B, ConAgua.RISCV.Compiler.exprOkB, ih]
  | ld64t _ _ _ iht ihi | ld32h _ _ _ _ iht ihi =>
    simp only [exprOkTier0B, ConAgua.RISCV.Compiler.exprOkB, iht, ihi]
  | ld32t a t _ iht ihi =>
    simp only [exprOkTier0B, ConAgua.RISCV.Compiler.exprOkB, tier32OkTier0B_eq, iht, ihi]
  | ld8x8 src _ ih =>
    cases src <;> simp only [exprOkTier0B, ConAgua.RISCV.Compiler.exprOkB, ih]

private theorem condOkTier0B_eq (tab : Tab) (nl : Nat) (c : L.Cond) :
    condOkTier0B tab nl c = ConAgua.RISCV.Compiler.condOkB tab nl c := by
  induction c with
  | cmp _ _ _ => simp only [condOkTier0B, ConAgua.RISCV.Compiler.condOkB, exprOkTier0B_eq]
  | and _ _ ihp ihq | or _ _ ihp ihq =>
    simp only [condOkTier0B, ConAgua.RISCV.Compiler.condOkB, ihp, ihq]
  | not _ ihp => simp only [condOkTier0B, ConAgua.RISCV.Compiler.condOkB, ihp]

private theorem warrOkTier0B_eq (tab : Tab) (nl : Nat) (w : L.WArr) :
    warrOkTier0B tab nl w = ConAgua.RISCV.Compiler.warrOkB tab nl w := by
  cases w with
  | plain _ => rfl
  | tier _ _ => simp only [warrOkTier0B, ConAgua.RISCV.Compiler.warrOkB, exprOkTier0B_eq]

private theorem stmtOkTier0B_eq (tab : Tab) (p : L.Prog) (nl : Nat) :
    ∀ (inLoop : Bool) (s : L.Stmt),
      stmtOkTier0B tab p nl inLoop s = ConAgua.RISCV.Compiler.stmtOkB tab p nl inLoop s
  | _, .skip | _, .brk => rfl
  | _, .set _ _ | _, .gset _ _ | _, .abort _ => by
    simp only [stmtOkTier0B, ConAgua.RISCV.Compiler.stmtOkB, exprOkTier0B_eq]
  | _, .st8 _ _ _ => rfl
  | _, .st64 _ _ _ | _, .st64t _ _ _ _ => by
    simp only [stmtOkTier0B, ConAgua.RISCV.Compiler.stmtOkB, exprOkTier0B_eq]
  | _, .st32t _ _ _ _ => by
    simp only [stmtOkTier0B, ConAgua.RISCV.Compiler.stmtOkB, tier32OkTier0B_eq, exprOkTier0B_eq]
  | inLoop, .seq s₁ s₂ => by
    simp only [stmtOkTier0B, ConAgua.RISCV.Compiler.stmtOkB, stmtOkTier0B_eq tab p nl inLoop s₁,
      stmtOkTier0B_eq tab p nl inLoop s₂]
  | inLoop, .ite c s₁ s₂ => by
    simp only [stmtOkTier0B, ConAgua.RISCV.Compiler.stmtOkB, condOkTier0B_eq,
      stmtOkTier0B_eq tab p nl inLoop s₁, stmtOkTier0B_eq tab p nl inLoop s₂]
  | _, .while c s => by
    simp only [stmtOkTier0B, ConAgua.RISCV.Compiler.stmtOkB, condOkTier0B_eq,
      stmtOkTier0B_eq tab p nl true s]
  | _, .ret _ | _, .call _ _ _ => by
    simp only [stmtOkTier0B, ConAgua.RISCV.Compiler.stmtOkB,
      show exprOkTier0B tab nl = ConAgua.RISCV.Compiler.exprOkB tab nl from funext (exprOkTier0B_eq tab nl)]
  | _, .copy64 _ _ _ _ _ | _, .copy8w _ _ _ _ _ => by
    simp only [stmtOkTier0B, ConAgua.RISCV.Compiler.stmtOkB, warrOkTier0B_eq, exprOkTier0B_eq]
  | _, .scan8 _ _ _ _ _ => by
    simp only [stmtOkTier0B, ConAgua.RISCV.Compiler.stmtOkB, exprOkTier0B_eq]

theorem progOkTier0B_eq (tab : Tab) (p : L.Prog) :
    progOkTier0B tab p = ConAgua.RISCV.Compiler.progOkB tab p := by
  simp only [progOkTier0B, ConAgua.RISCV.Compiler.progOkB, stmtOkTier0B_eq]

theorem checkerProgMini_progOkB :
    ConAgua.RISCV.Compiler.progOkB checkerTabMini checkerProgMini = true := by
  rw [← progOkTier0B_eq]; exact checkerProgMini_progOkTier0B

theorem checkerProgIMini_progOkB :
    ConAgua.RISCV.Compiler.progOkB checkerTabMini checkerProgIMini = true := by
  rw [← progOkTier0B_eq]; exact checkerProgIMini_progOkTier0B

/-- info: 'ConAgua.RISCV.Bridge.expr_wf_imp_exprOkTier0B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms expr_wf_imp_exprOkTier0B

/-- info: 'ConAgua.RISCV.Bridge.cond_wf_imp_condOkTier0B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cond_wf_imp_condOkTier0B

/-- info: 'ConAgua.RISCV.Bridge.stmt_wf_imp_stmtOkTier0B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stmt_wf_imp_stmtOkTier0B

/-- info: 'ConAgua.RISCV.Bridge.checkerProgMini_progOkTier0B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgMini_progOkTier0B

/-- info: 'ConAgua.RISCV.Bridge.checkerProgIMini_progOkTier0B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgIMini_progOkTier0B

/-- info: 'ConAgua.RISCV.Bridge.checkerProgMini_progOkConst0B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgMini_progOkConst0B

/-- info: 'ConAgua.RISCV.Bridge.checkerProgIMini_progOkConst0B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgIMini_progOkConst0B

/-- info: 'ConAgua.RISCV.Bridge.checkerProgMini_progOkB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgMini_progOkB

/-- info: 'ConAgua.RISCV.Bridge.checkerProgIMini_progOkB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgIMini_progOkB

end ConAgua.RISCV.Bridge
