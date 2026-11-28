import ConAgua.RISCV.Bridge.EmitChecker
import ConAgua.RISCV.Bridge.CheckerWf
import ConAgua.RISCV.Bridge.CheckerWfFast
import ConAgua.RISCV.Bridge.CheckerWfStmt
import ConAgua.RISCV.Linker.LinkModel
import ConAgua.RISCV.Linker.FarLinkProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Base Primitives and Codegen Lemmas for `CheckerLinkWf` (`ConAgua.RISCV.Bridge.CheckerLinkWfBase`)

Shared `allInstrs`, `noT6Branch`, `lblNames`, `targetsIn`, `farTotalWords` primitives,
code-generation `allInstrs`/size lemmas, and register-allocation/frame-layout structural
lemmas used across `CheckerLinkNoT6`, `CheckerLinkLabels`, `CheckerLinkSize`, and `CheckerLinkWf`.
-/

namespace ConAgua.RISCV.Bridge

open ConAgua.RISCV.RV64
open ConAgua.RISCV.Compiler
open ConAgua.RISCV.Linker
open _root_.L

/-! ## 1. `allInstrs`, `noT6Branch`, and `lblNames` Primitives -/

/-- Every item is a single-word hardware `.instr` (never `.label`, `.j`, `.call`, `.br`, `.brLong`). -/
def allInstrs (items : List AsmItem) : Bool :=
  items.all fun
    | .instr _ => true
    | _ => false

/-- An `AsmItem` does not read `AbiReg.t6` in a `.br` / `.brLong` condition. -/
def asmItemNoT6Branch : AsmItem → Bool
  | .br _ rs1 rs2 _ | .brLong _ rs1 rs2 _ => rs1 != AbiReg.t6 && rs2 != AbiReg.t6
  | _ => true

/-- Every `.br` / `.brLong` item in `items` avoids `AbiReg.t6` as `rs1` and `rs2`. -/
def noT6Branch (items : List AsmItem) : Bool :=
  items.all asmItemNoT6Branch

/-- Ordered list of `.label` names emitted in `items`. -/
def lblNames (items : List AsmItem) : List String :=
  items.filterMap fun
    | .label s => some s
    | _ => none

/-- Ordered list of `.j`, `.call`, `.br`, `.brLong` target strings referenced in `items`. -/
def targetsIn (items : List AsmItem) : List String :=
  items.filterMap fun
    | .j t | .call t | .br _ _ _ t | .brLong _ _ _ t => some t
    | _ => none

theorem allInstrs_nil : allInstrs [] = true := rfl

theorem allInstrs_cons {x : AsmItem} {xs : List AsmItem} :
    allInstrs (x :: xs) = ((match x with | .instr _ => true | _ => false) && allInstrs xs) := rfl

theorem allInstrs_append {xs ys : List AsmItem} :
    allInstrs (xs ++ ys) = (allInstrs xs && allInstrs ys) := by
  simp [allInstrs, List.all_append]

theorem allInstrs_map_instr (xs : List Instr) :
    allInstrs (xs.map AsmItem.instr) = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [allInstrs_cons, ih]

theorem allInstrs_flatMap {α : Type} {xs : List α} {f : α → List AsmItem}
    (hf : ∀ x ∈ xs, allInstrs (f x) = true) :
    allInstrs (xs.flatMap f) = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, allInstrs_append, Bool.and_eq_true]
    exact ⟨hf x (by simp), ih (fun y hy => hf y (by simp [hy]))⟩

theorem noT6Branch_nil : noT6Branch [] = true := rfl

theorem noT6Branch_cons {x : AsmItem} {xs : List AsmItem} :
    noT6Branch (x :: xs) = (asmItemNoT6Branch x && noT6Branch xs) := rfl

theorem noT6Branch_append {xs ys : List AsmItem} :
    noT6Branch (xs ++ ys) = (noT6Branch xs && noT6Branch ys) := by
  simp [noT6Branch, List.all_append]

theorem noT6Branch_flatMap {α : Type} {xs : List α} {f : α → List AsmItem}
    (hf : ∀ x ∈ xs, noT6Branch (f x) = true) :
    noT6Branch (xs.flatMap f) = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, noT6Branch_append, Bool.and_eq_true]
    exact ⟨hf x (by simp), ih (fun y hy => hf y (by simp [hy]))⟩

theorem noT6Branch_of_allInstrs {xs : List AsmItem} (h : allInstrs xs = true) :
    noT6Branch xs = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [allInstrs_cons, Bool.and_eq_true] at h
    rcases h with ⟨hx, hxs⟩
    have hx' : asmItemNoT6Branch x = true := by
      cases x <;> first | rfl | contradiction
    rw [noT6Branch_cons, Bool.and_eq_true]
    exact ⟨hx', ih hxs⟩

theorem lblNames_nil : lblNames [] = [] := rfl

theorem lblNames_append {xs ys : List AsmItem} :
    lblNames (xs ++ ys) = lblNames xs ++ lblNames ys := by
  simp [lblNames, List.filterMap_append]

theorem lblNames_flatMap {α : Type} {xs : List α} {f : α → List AsmItem} :
    lblNames (xs.flatMap f) = xs.flatMap (fun x => lblNames (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, lblNames_append, ih]

theorem lblNames_of_allInstrs {xs : List AsmItem} (h : allInstrs xs = true) :
    lblNames xs = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [allInstrs_cons, Bool.and_eq_true] at h
    rcases h with ⟨hx, hxs⟩
    have hx' : (match x with | .label s => some s | _ => (none : Option String)) = none := by
      cases x <;> first | rfl | contradiction
    dsimp only [lblNames] at ih ⊢
    rw [List.filterMap_cons, hx']
    exact ih hxs

theorem targetsIn_nil : targetsIn [] = [] := rfl

theorem targetsIn_append {xs ys : List AsmItem} :
    targetsIn (xs ++ ys) = targetsIn xs ++ targetsIn ys := by
  simp [targetsIn, List.filterMap_append]

theorem targetsIn_flatMap {α : Type} {xs : List α} {f : α → List AsmItem} :
    targetsIn (xs.flatMap f) = xs.flatMap (fun x => targetsIn (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, targetsIn_append, ih]

theorem targetsIn_of_allInstrs {xs : List AsmItem} (h : allInstrs xs = true) :
    targetsIn xs = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [allInstrs_cons, Bool.and_eq_true] at h
    rcases h with ⟨hx, hxs⟩
    have hx' : (match x with
        | .j t | .call t | .br _ _ _ t | .brLong _ _ _ t => some t
        | _ => (none : Option String)) = none := by
      cases x <;> first | rfl | contradiction
    dsimp only [targetsIn] at ih ⊢
    rw [List.filterMap_cons, hx']
    exact ih hxs

private theorem foldl_farWordSize_add (acc : Nat) (xs : List AsmItem) :
    xs.foldl (fun a item => a + farWordSize item) acc = acc + farTotalWords xs := by
  induction xs generalizing acc with
  | nil => simp [farTotalWords]
  | cons x xs ih =>
    simp only [farTotalWords, List.foldl_cons, Nat.zero_add] at ih ⊢
    rw [ih (acc + farWordSize x), ih (farWordSize x)]
    omega

theorem farTotalWords_nil : farTotalWords [] = 0 := rfl

theorem farTotalWords_cons (x : AsmItem) (xs : List AsmItem) :
    farTotalWords (x :: xs) = farWordSize x + farTotalWords xs := by
  change List.foldl (fun a item => a + farWordSize item) 0 (x :: xs) = _
  rw [List.foldl_cons, Nat.zero_add, foldl_farWordSize_add]

theorem farTotalWords_append (xs ys : List AsmItem) :
    farTotalWords (xs ++ ys) = farTotalWords xs + farTotalWords ys := by
  change List.foldl (fun a item => a + farWordSize item) 0 (xs ++ ys) = _
  rw [List.foldl_append, foldl_farWordSize_add]; rfl

theorem nodup_append_disj {α : Type} {xs ys : List α}
    (hx : xs.Nodup) (hy : ys.Nodup) (hd : ∀ x ∈ xs, x ∉ ys) : (xs ++ ys).Nodup :=
  List.nodup_append.mpr ⟨hx, hy, fun x h1 _ h2 heq => hd x h1 (heq ▸ h2)⟩

theorem nodup_map_inj {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b)
    {xs : List α} (hx : xs.Nodup) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hx ⊢
    exact ⟨fun ⟨b, hb, hab⟩ => hx.1 (hf b a hab ▸ hb), ih hx.2⟩

theorem lblNames_singleton_lbl (s : String) : lblNames [Asm.lbl s] = [s] := rfl

theorem farTotalWords_flatMap_le {α : Type} (xs : List α) (f : α → List AsmItem)
    (b : α → Nat) (hb : ∀ x ∈ xs, farTotalWords (f x) ≤ b x) :
    farTotalWords (xs.flatMap f) ≤ xs.foldl (fun acc x => acc + b x) 0 := by
  have hfold : ∀ (init : Nat),
      init + farTotalWords (xs.flatMap f) ≤ xs.foldl (fun acc x => acc + b x) init := by
    induction xs with
    | nil => intro init; simp [farTotalWords]
    | cons x xs ih =>
      intro init
      simp only [List.flatMap_cons, farTotalWords_append, List.foldl_cons]
      have hx := hb x (by simp)
      have htail := ih (fun y hy => hb y (by simp [hy])) (init + b x)
      omega
  simpa using hfold 0

theorem farTotalWords_of_allInstrs {xs : List AsmItem} (h : allInstrs xs = true) :
    farTotalWords xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [allInstrs_cons, Bool.and_eq_true] at h
    rcases h with ⟨hx, hxs⟩
    have hsz : farWordSize x = 1 := by
      cases x <;> first | rfl | contradiction
    rw [farTotalWords_cons, hsz, ih hxs, List.length_cons]
    omega

/-! ## 2. `allInstrs` and Size Bounds for Codegen Primitives -/

theorem li32Instrs_length_le (rd : Reg) (w32 : BitVec 32) :
    (li32Instrs rd w32).length ≤ 4 := by
  dsimp only [li32Instrs]
  repeat' (split <;> try simp)

theorem li_allInstrs (rd : Reg) (w : BitVec 64) :
    allInstrs (li rd w) = true := by
  dsimp only [li]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · exact allInstrs_map_instr _
        · split
          · exact allInstrs_map_instr _
          · split
            · exact allInstrs_map_instr _
            · exact allInstrs_map_instr _

theorem li_length_le (rd : Reg) (w : BitVec 64) :
    (li rd w).length ≤ 10 := by
  dsimp only [li]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · split
        · rw [List.length_map]; exact Nat.le_trans (li32Instrs_length_le _ _) (by omega)
        · split
          · next hi32 sh lo _ =>
            rw [List.length_map, List.length_append, List.length_append]
            have h32 := li32Instrs_length_le rd hi32
            have ht : (if (lo == 0#12) = true then ([] : List Instr) else [Instr.aluImm AluImmOp.addi rd rd lo]).length ≤ 1 := by
              split <;> simp
            simp only [List.length_singleton]
            omega
          · split
            · rw [List.length_map, List.length_append]
              have h32 := li32Instrs_length_le rd (BitVec.extractLsb' 0 32 w)
              simp only [List.length_cons, List.length_nil]
              omega
            · rw [List.length_map, List.length_append, List.length_append, List.length_append]
              have h32 := li32Instrs_length_le rd (BitVec.extractLsb' 32 32 w)
              have hs1 : (([Instr.shImm ShiftImmOp.slli rd rd 11#6] ++
                  if (BitVec.zeroExtend 12 (BitVec.extractLsb' 21 11 w) == 0#12) = true then []
                  else [Instr.aluImm AluImmOp.addi rd rd (BitVec.zeroExtend 12 (BitVec.extractLsb' 21 11 w))]).length) ≤ 2 := by
                split <;> simp
              have hs2 : (([Instr.shImm ShiftImmOp.slli rd rd 11#6] ++
                  if (BitVec.zeroExtend 12 (BitVec.extractLsb' 10 11 w) == 0#12) = true then []
                  else [Instr.aluImm AluImmOp.addi rd rd (BitVec.zeroExtend 12 (BitVec.extractLsb' 10 11 w))]).length) ≤ 2 := by
                split <;> simp
              have hs3 : (([Instr.shImm ShiftImmOp.slli rd rd 10#6] ++
                  if (BitVec.zeroExtend 12 (BitVec.extractLsb' 0 10 w) == 0#12) = true then []
                  else [Instr.aluImm AluImmOp.addi rd rd (BitVec.zeroExtend 12 (BitVec.extractLsb' 0 10 w))]).length) ≤ 2 := by
                split <;> simp
              omega

theorem li_length_le_32 (rd : Reg) (off : Int) (hlo : 0 ≤ off) (hhi : off < 2 ^ 31) :
    (li rd (BitVec.ofInt 64 off)).length ≤ 4 := by
  dsimp only [li]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · have hse : (BitVec.signExtend 64 (BitVec.extractLsb' 0 32 (BitVec.ofInt 64 off)) ==
            BitVec.ofInt 64 off) = true := by
          rw [beq_iff_eq]
          apply BitVec.eq_of_toInt_eq
          rw [BitVec.toInt_signExtend, BitVec.toInt_extractLsb']
          have hoff : BitVec.ofInt 64 off = BitVec.ofNat 64 off.toNat := by
            apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofInt]; omega
          rw [hoff, BitVec.toInt_eq_toNat_bmod (BitVec.ofNat 64 off.toNat)]
          simp only [BitVec.toNat_ofNat, Nat.shiftRight_zero,
            Nat.mod_eq_of_lt (by omega : off.toNat < 2 ^ 64), Int.bmod_def]
          have hmin : min 64 32 = 32 := rfl
          rw [hmin]
          split <;> split <;> omega
        rw [hse]
        simp only [↓reduceIte, List.length_map]
        exact li32Instrs_length_le rd _

theorem addImmOff_allInstrs (rd rs tmp : Reg) (off : Int) :
    allInstrs (addImmOff rd rs tmp off) = true := by
  dsimp only [addImmOff]
  split
  · split <;> rfl
  · split
    · rfl
    · split
      · rfl
      · rw [allInstrs_append, Bool.and_eq_true]
        exact ⟨li_allInstrs _ _, rfl⟩

theorem addImmOff_length_le (rd rs tmp : Reg) (off : Int) :
    (addImmOff rd rs tmp off).length ≤ 11 := by
  dsimp only [addImmOff]
  split
  · split <;> simp
  · split
    · simp
    · split
      · simp
      · rw [List.length_append]; have := li_length_le tmp (BitVec.ofInt 64 off); simp; omega

theorem addImmOff_length_le_32 (rd rs tmp : Reg) (off : Int) (hlo : 0 ≤ off) (hhi : off < 2 ^ 31) :
    (addImmOff rd rs tmp off).length ≤ 5 := by
  dsimp only [addImmOff]
  split
  · split <;> simp
  · split
    · simp
    · split
      · simp
      · rw [List.length_append]; have := li_length_le_32 tmp off hlo hhi; simp; omega

theorem loadMemOff_allInstrs (op : LoadOp) (rd base tmp : Reg) (off : Int) :
    allInstrs (loadMemOff op rd base tmp off) = true := by
  dsimp only [loadMemOff]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rw [allInstrs_append, Bool.and_eq_true]
        exact ⟨li_allInstrs _ _, rfl⟩

theorem loadMemOff_length_le (op : LoadOp) (rd base tmp : Reg) (off : Int) :
    (loadMemOff op rd base tmp off).length ≤ 12 := by
  dsimp only [loadMemOff]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rw [List.length_append]; have := li_length_le tmp (BitVec.ofInt 64 off); simp; omega

theorem loadMemOff_length_le_32 (op : LoadOp) (rd base tmp : Reg) (off : Int)
    (hlo : 0 ≤ off) (hhi : off < 2 ^ 31) :
    (loadMemOff op rd base tmp off).length ≤ 6 := by
  dsimp only [loadMemOff]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rw [List.length_append]; have := li_length_le_32 tmp off hlo hhi; simp; omega

theorem storeMemOff_allInstrs (op : StoreOp) (base rs tmp : Reg) (off : Int) :
    allInstrs (storeMemOff op base rs tmp off) = true := by
  dsimp only [storeMemOff]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rw [allInstrs_append, Bool.and_eq_true]
        exact ⟨li_allInstrs _ _, rfl⟩

theorem storeMemOff_length_le (op : StoreOp) (base rs tmp : Reg) (off : Int) :
    (storeMemOff op base rs tmp off).length ≤ 12 := by
  dsimp only [storeMemOff]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rw [List.length_append]; have := li_length_le tmp (BitVec.ofInt 64 off); simp; omega

theorem storeMemOff_length_le_32 (op : StoreOp) (base rs tmp : Reg) (off : Int)
    (hlo : 0 ≤ off) (hhi : off < 2 ^ 31) :
    (storeMemOff op base rs tmp off).length ≤ 6 := by
  dsimp only [storeMemOff]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rw [List.length_append]; have := li_length_le_32 tmp off hlo hhi; simp; omega

theorem li_farTotalWords_le (rd : Reg) (w : BitVec 64) :
    farTotalWords (li rd w) ≤ 10 := by
  rw [farTotalWords_of_allInstrs (li_allInstrs rd w)]; exact li_length_le rd w

theorem li_farTotalWords_le_32 (rd : Reg) (off : Int) (hlo : 0 ≤ off) (hhi : off < 2 ^ 31) :
    farTotalWords (li rd (BitVec.ofInt 64 off)) ≤ 4 := by
  rw [farTotalWords_of_allInstrs (li_allInstrs rd _)]; exact li_length_le_32 rd off hlo hhi

theorem addImmOff_farTotalWords_le (rd rs tmp : Reg) (off : Int) :
    farTotalWords (addImmOff rd rs tmp off) ≤ 11 := by
  rw [farTotalWords_of_allInstrs (addImmOff_allInstrs rd rs tmp off)]; exact addImmOff_length_le rd rs tmp off

theorem addImmOff_farTotalWords_le_32 (rd rs tmp : Reg) (off : Int) (hlo : 0 ≤ off) (hhi : off < 2 ^ 31) :
    farTotalWords (addImmOff rd rs tmp off) ≤ 5 := by
  rw [farTotalWords_of_allInstrs (addImmOff_allInstrs rd rs tmp off)]
  exact addImmOff_length_le_32 rd rs tmp off hlo hhi

theorem loadMemOff_farTotalWords_le (op : LoadOp) (rd base tmp : Reg) (off : Int) :
    farTotalWords (loadMemOff op rd base tmp off) ≤ 12 := by
  rw [farTotalWords_of_allInstrs (loadMemOff_allInstrs op rd base tmp off)]
  exact loadMemOff_length_le op rd base tmp off

theorem loadMemOff_farTotalWords_le_32 (op : LoadOp) (rd base tmp : Reg) (off : Int)
    (hlo : 0 ≤ off) (hhi : off < 2 ^ 31) :
    farTotalWords (loadMemOff op rd base tmp off) ≤ 6 := by
  rw [farTotalWords_of_allInstrs (loadMemOff_allInstrs op rd base tmp off)]
  exact loadMemOff_length_le_32 op rd base tmp off hlo hhi

theorem storeMemOff_farTotalWords_le (op : StoreOp) (base rs tmp : Reg) (off : Int) :
    farTotalWords (storeMemOff op base rs tmp off) ≤ 12 := by
  rw [farTotalWords_of_allInstrs (storeMemOff_allInstrs op base rs tmp off)]
  exact storeMemOff_length_le op base rs tmp off

theorem storeMemOff_farTotalWords_le_32 (op : StoreOp) (base rs tmp : Reg) (off : Int)
    (hlo : 0 ≤ off) (hhi : off < 2 ^ 31) :
    farTotalWords (storeMemOff op base rs tmp off) ≤ 6 := by
  rw [farTotalWords_of_allInstrs (storeMemOff_allInstrs op base rs tmp off)]
  exact storeMemOff_length_le_32 op base rs tmp off hlo hhi

theorem loadMemOff_farTotalWords_imm12 (op : LoadOp) (rd base tmp : Reg) (off : Int)
    (hlo : -2048 ≤ off) (hhi : off ≤ 2047) :
    farTotalWords (loadMemOff op rd base tmp off) = 1 := by
  have hfit : fitsImm12Int off = true := by
    simp only [fitsImm12Int, Bool.and_eq_true, decide_eq_true_eq]; omega
  simp [loadMemOff, hfit, Asm.raw, farTotalWords, farWordSize]

theorem storeMemOff_farTotalWords_imm12 (op : StoreOp) (base rs tmp : Reg) (off : Int)
    (hlo : -2048 ≤ off) (hhi : off ≤ 2047) :
    farTotalWords (storeMemOff op base rs tmp off) = 1 := by
  have hfit : fitsImm12Int off = true := by
    simp only [fitsImm12Int, Bool.and_eq_true, decide_eq_true_eq]; omega
  simp [storeMemOff, hfit, Asm.raw, farTotalWords, farWordSize]

theorem loadMemOffGp_allInstrs (useT5 : Bool) (op : LoadOp) (rd tmp : Reg) (off : Int) :
    allInstrs (loadMemOffGp useT5 op rd tmp off) = true := by
  dsimp only [loadMemOffGp]
  split
  · rfl
  · exact loadMemOff_allInstrs _ _ _ _ _

theorem storeMemOffGp_allInstrs (useT5 : Bool) (op : StoreOp) (rs tmp : Reg) (off : Int) :
    allInstrs (storeMemOffGp useT5 op rs tmp off) = true := by
  dsimp only [storeMemOffGp]
  split
  · rfl
  · exact storeMemOff_allInstrs _ _ _ _ _

theorem loadMemOffGp_farTotalWords_le_32 (useT5 : Bool) (op : LoadOp) (rd tmp : Reg) (off : Int)
    (hlo : 0 ≤ off) (hhi : off < 2 ^ 31) :
    farTotalWords (loadMemOffGp useT5 op rd tmp off) ≤ 6 := by
  dsimp only [loadMemOffGp]
  split
  · have h1 : farTotalWords [Asm.raw (.load op rd AbiReg.t5 (BitVec.ofInt 12 (off - 2047)))] = 1 := rfl
    omega
  · exact loadMemOff_farTotalWords_le_32 op rd AbiReg.gp tmp off hlo hhi

theorem storeMemOffGp_farTotalWords_le_32 (useT5 : Bool) (op : StoreOp) (rs tmp : Reg) (off : Int)
    (hlo : 0 ≤ off) (hhi : off < 2 ^ 31) :
    farTotalWords (storeMemOffGp useT5 op rs tmp off) ≤ 6 := by
  dsimp only [storeMemOffGp]
  split
  · have h1 : farTotalWords [Asm.raw (.store op AbiReg.t5 rs (BitVec.ofInt 12 (off - 2047)))] = 1 := rfl
    omega
  · exact storeMemOff_farTotalWords_le_32 op AbiReg.gp rs tmp off hlo hhi

theorem callerSaveAsm_allInstrs (base : Reg) (saveOff : Int) :
    allInstrs (callerSaveAsm base saveOff) = true := by
  dsimp only [callerSaveAsm]
  rw [allInstrs_append, Bool.and_eq_true]
  exact ⟨addImmOff_allInstrs _ _ _ _, by rfl⟩

theorem callerRestoreRetAsm_allInstrs (base : Reg) (saveOff : Int) :
    allInstrs (callerRestoreRetAsm base saveOff) = true := by
  dsimp only [callerRestoreRetAsm]
  rw [allInstrs_append, allInstrs_append, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨addImmOff_allInstrs _ _ _ _, rfl⟩, rfl⟩

theorem callerSaveAsm_farTotalWords_le (base : Reg) (saveOff : Int) :
    farTotalWords (callerSaveAsm base saveOff) ≤ 27 := by
  rw [farTotalWords_of_allInstrs (callerSaveAsm_allInstrs base saveOff)]
  dsimp only [callerSaveAsm]
  rw [List.length_append, List.length_map, List.length_zipIdx]
  have h1 := addImmOff_length_le AbiReg.t0 base AbiReg.t1 saveOff
  have h2 : callerSaveRegs.length = 16 := rfl
  omega

theorem callerRestoreRetAsm_farTotalWords_le (base : Reg) (saveOff : Int) :
    farTotalWords (callerRestoreRetAsm base saveOff) ≤ 28 := by
  rw [farTotalWords_of_allInstrs (callerRestoreRetAsm_allInstrs base saveOff)]
  dsimp only [callerRestoreRetAsm]
  rw [List.length_append, List.length_append, List.length_map, List.length_zipIdx]
  have h1 := addImmOff_length_le AbiReg.t0 base AbiReg.t1 saveOff
  have h2 : callerSaveRegs.length = 16 := rfl
  have h3 : ([Asm.ret] : List AsmItem).length = 1 := rfl
  omega

theorem ld64Tail_allInstrs (rd ri tmp : Reg) (i : Expr) :
    allInstrs (ld64Tail rd ri tmp i) = true := by
  dsimp only [ld64Tail]
  cases i.constVal? with
  | none => rfl
  | some _ => dsimp only; split <;> rfl

theorem ld64Tail_farTotalWords_le (rd ri tmp : Reg) (i : Expr) :
    farTotalWords (ld64Tail rd ri tmp i) ≤ 3 := by
  dsimp only [ld64Tail]
  cases i.constVal? with
  | none => exact Nat.le_refl 3
  | some wi =>
    dsimp only; split
    · have h1 : farTotalWords [Asm.ld rd AbiReg.t1 (BitVec.ofNat 12 (8 * wi.toNat))] = 1 := rfl; omega
    · exact Nat.le_refl 3

theorem ld32tTail_allInstrs (rd ri : Reg) (i : Expr) :
    allInstrs (ld32tTail rd ri i) = true := by
  dsimp only [ld32tTail]
  cases i.constVal? with
  | none => rfl
  | some _ => dsimp only; split <;> rfl

theorem ld32tTail_farTotalWords_le (rd ri : Reg) (i : Expr) :
    farTotalWords (ld32tTail rd ri i) ≤ 3 := by
  dsimp only [ld32tTail]
  cases i.constVal? with
  | none => exact Nat.le_refl 3
  | some wi =>
    dsimp only; split
    · have h1 : farTotalWords [Asm.lwu rd AbiReg.t1 (BitVec.ofNat 12 (4 * wi.toNat))] = 1 := rfl; omega
    · exact Nat.le_refl 3

theorem ld32hTail_allInstrs (rd ri tmp : Reg) (i : Expr) (hi : Bool) :
    allInstrs (ld32hTail rd ri tmp i hi) = true := by
  dsimp only [ld32hTail]
  cases i.constVal? with
  | none => rfl
  | some _ => dsimp only; split <;> rfl

theorem ld32hTail_farTotalWords_le (rd ri tmp : Reg) (i : Expr) (hi : Bool) :
    farTotalWords (ld32hTail rd ri tmp i hi) ≤ 3 := by
  dsimp only [ld32hTail]
  cases i.constVal? with
  | none =>
    dsimp only
    have h3 : farTotalWords [Asm.slli tmp ri 3#6, Asm.add AbiReg.t1 AbiReg.t1 tmp,
        Asm.lwu rd AbiReg.t1 (if hi then 4#12 else 0#12)] = 3 := by cases hi <;> rfl
    omega
  | some wi =>
    dsimp only; split
    · have h1 : farTotalWords [Asm.lwu rd AbiReg.t1 (BitVec.ofNat 12 (8 * wi.toNat + if hi then 4 else 0))] = 1 := rfl
      omega
    · have h3 : farTotalWords [Asm.slli tmp ri 3#6, Asm.add AbiReg.t1 AbiReg.t1 tmp,
          Asm.lwu rd AbiReg.t1 (if hi then 4#12 else 0#12)] = 3 := by cases hi <;> rfl
      omega

theorem st64Tail_allInstrs (re ri tmp : Reg) (i : Expr) :
    allInstrs (st64Tail re ri tmp i) = true := by
  dsimp only [st64Tail]
  cases i.constVal? with
  | none => rfl
  | some _ => dsimp only; split <;> rfl

theorem st64Tail_farTotalWords_le (re ri tmp : Reg) (i : Expr) :
    farTotalWords (st64Tail re ri tmp i) ≤ 3 := by
  dsimp only [st64Tail]
  cases i.constVal? with
  | none => exact Nat.le_refl 3
  | some w =>
    dsimp only; split
    · have h1 : farTotalWords [Asm.sd AbiReg.t1 re (BitVec.ofNat 12 (8 * w.toNat))] = 1 := rfl; omega
    · exact Nat.le_refl 3

theorem st32tTail_allInstrs (re ri tmp : Reg) (i : Expr) :
    allInstrs (st32tTail re ri tmp i) = true := by
  dsimp only [st32tTail]
  cases i.constVal? with
  | none => rfl
  | some _ => dsimp only; split <;> rfl

theorem st32tTail_farTotalWords_le (re ri tmp : Reg) (i : Expr) :
    farTotalWords (st32tTail re ri tmp i) ≤ 3 := by
  dsimp only [st32tTail]
  cases i.constVal? with
  | none => exact Nat.le_refl 3
  | some w =>
    dsimp only; split
    · have h1 : farTotalWords [Asm.sw AbiReg.t1 re (BitVec.ofNat 12 (4 * w.toNat))] = 1 := rfl; omega
    · exact Nat.le_refl 3

theorem emitMulConstTo_allInstrs (rd rs tmp : Reg) (w : UInt64) :
    allInstrs (emitMulConstTo rd rs tmp w) = true := by
  dsimp only [emitMulConstTo]
  split
  · rfl
  · split
    · split <;> rfl
    · cases isPow2Shift64 w with
      | some sh => rfl
      | none =>
        dsimp only
        repeat (split; · rfl)
        rw [allInstrs_append, Bool.and_eq_true]
        exact ⟨li_allInstrs _ _, rfl⟩

theorem emitMulConst_allInstrs (rd tmp : Reg) (w : UInt64) :
    allInstrs (emitMulConst rd tmp w) = true :=
  emitMulConstTo_allInstrs rd rd tmp w

theorem emitMulConstTo_farTotalWords_le (rd rs tmp : Reg) (w : UInt64) :
    farTotalWords (emitMulConstTo rd rs tmp w) ≤ 11 := by
  dsimp only [emitMulConstTo]
  split
  · exact Nat.le_of_ble_eq_true (show (farTotalWords [Asm.addi rd AbiReg.zero 0#12]).ble 11 = true from rfl)
  · split
    · split
      · simp [farTotalWords]
      · have h : farTotalWords [Asm.mv rd rs] = 1 := rfl; omega
    · cases isPow2Shift64 w with
      | some sh =>
        dsimp only
        have h : farTotalWords [Asm.slli rd rs sh] = 1 := rfl
        omega
      | none =>
        dsimp only
        split
        · have h : farTotalWords [Asm.slli tmp rs 1#6, Asm.add rd rs tmp] = 2 := rfl; omega
        split
        · have h : farTotalWords [Asm.slli tmp rs 2#6, Asm.add rd rs tmp] = 2 := rfl; omega
        split
        · have h : farTotalWords [Asm.slli tmp rs 3#6, Asm.sub rd tmp rs] = 2 := rfl; omega
        split
        · have h : farTotalWords [Asm.slli tmp rs 3#6, Asm.add rd rs tmp] = 2 := rfl; omega
        split
        · have h : farTotalWords [Asm.slli tmp rs 4#6, Asm.sub rd tmp rs] = 2 := rfl; omega
        split
        · have h : farTotalWords [Asm.slli tmp rs 4#6, Asm.add rd rs tmp] = 2 := rfl; omega
        split
        · have h : farTotalWords [Asm.slli tmp rs 8#6, Asm.sub rd tmp rs] = 2 := rfl; omega
        split
        · have h : farTotalWords [Asm.slli tmp rs 8#6, Asm.add rd rs tmp] = 2 := rfl; omega
        rw [farTotalWords_append]
        have hli := li_farTotalWords_le tmp (BitVec.ofNat 64 w.toNat)
        have hm : farTotalWords [Asm.mul rd rs tmp] = 1 := rfl
        omega

theorem emitMulConst_farTotalWords_le (rd tmp : Reg) (w : UInt64) :
    farTotalWords (emitMulConst rd tmp w) ≤ 11 :=
  emitMulConstTo_farTotalWords_le rd rd tmp w

theorem emitBinOp_allInstrs (op : BinOp) (rd rs1 rs2 : Reg) :
    allInstrs [emitBinOp op rd rs1 rs2] = true := by
  cases op <;> rfl

theorem emitBinOp_farTotalWords (op : BinOp) (rd rs1 rs2 : Reg) :
    farTotalWords [emitBinOp op rd rs1 rs2] = 1 := by
  cases op <;> rfl

theorem emitBinConstRhsTo_allInstrs (rd rs : Reg) (op : BinOp) (w : UInt64) :
    allInstrs (emitBinConstRhsTo rd rs op w) = true := by
  have hmv : allInstrs (if rd == rs then [] else [Asm.mv rd rs]) = true := by
    split <;> rfl
  cases op with
  | add | sub | or | xor =>
    dsimp only [emitBinConstRhsTo]
    split
    · exact hmv
    · split
      · rfl
      · rw [allInstrs_append, Bool.and_eq_true]
        exact ⟨li_allInstrs _ _, rfl⟩
  | and =>
    dsimp only [emitBinConstRhsTo]
    split
    · rfl
    · split
      · exact hmv
      · split
        · rfl
        · cases lowMaskShift? w with
          | some _ => rfl
          | none =>
            rw [allInstrs_append, Bool.and_eq_true]
            exact ⟨li_allInstrs _ _, rfl⟩
  | shl | shr =>
    dsimp only [emitBinConstRhsTo]
    split
    · exact hmv
    · rfl
  | mul =>
    exact emitMulConstTo_allInstrs rd rs AbiReg.t0 w
  | «mulhi» =>
    dsimp only [emitBinConstRhsTo]
    split
    · rfl
    · rw [allInstrs_append, Bool.and_eq_true]
      exact ⟨li_allInstrs _ _, rfl⟩

theorem emitBinConstRhs_allInstrs (op : BinOp) (w : UInt64) :
    allInstrs (emitBinConstRhs op w) = true :=
  emitBinConstRhsTo_allInstrs AbiReg.a0 AbiReg.a0 op w

theorem emitBinConstRhsTo_farTotalWords_le (rd rs : Reg) (op : BinOp) (w : UInt64) :
    farTotalWords (emitBinConstRhsTo rd rs op w) ≤ 11 := by
  have hmv : farTotalWords (if rd == rs then [] else [Asm.mv rd rs]) ≤ 1 := by
    split
    · simp [farTotalWords]
    · have h : farTotalWords [Asm.mv rd rs] = 1 := rfl; omega
  cases op with
  | add =>
    dsimp only [emitBinConstRhsTo]
    split
    · omega
    · split
      · have h : farTotalWords [Asm.addi rd rs (w.toBitVec.extractLsb' 0 12)] = 1 := rfl; omega
      · rw [farTotalWords_append]
        have hli := li_farTotalWords_le AbiReg.t0 w.toBitVec
        have h1 : farTotalWords [Asm.add rd rs AbiReg.t0] = 1 := rfl
        omega
  | sub =>
    dsimp only [emitBinConstRhsTo]
    split
    · omega
    · split
      · have h : farTotalWords [Asm.addi rd rs ((-w.toBitVec).extractLsb' 0 12)] = 1 := rfl; omega
      · rw [farTotalWords_append]
        have hli := li_farTotalWords_le AbiReg.t0 w.toBitVec
        have h1 : farTotalWords [Asm.sub rd rs AbiReg.t0] = 1 := rfl
        omega
  | and =>
    dsimp only [emitBinConstRhsTo]
    split
    · have h : farTotalWords [Asm.addi rd AbiReg.zero 0#12] = 1 := rfl; omega
    · split
      · omega
      · split
        · have h : farTotalWords [Asm.andi rd rs (w.toBitVec.extractLsb' 0 12)] = 1 := rfl; omega
        · cases lowMaskShift? w with
          | some sh =>
            dsimp only
            have h : farTotalWords [Asm.slli rd rs sh, Asm.srli rd rd sh] = 2 := rfl; omega
          | none =>
            dsimp only
            rw [farTotalWords_append]
            have hli := li_farTotalWords_le AbiReg.t0 w.toBitVec
            have h1 : farTotalWords [Asm.and rd rs AbiReg.t0] = 1 := rfl
            omega
  | or =>
    dsimp only [emitBinConstRhsTo]
    split
    · omega
    · split
      · have h : farTotalWords [Asm.ori rd rs (w.toBitVec.extractLsb' 0 12)] = 1 := rfl; omega
      · rw [farTotalWords_append]
        have hli := li_farTotalWords_le AbiReg.t0 w.toBitVec
        have h1 : farTotalWords [Asm.or rd rs AbiReg.t0] = 1 := rfl
        omega
  | xor =>
    dsimp only [emitBinConstRhsTo]
    split
    · omega
    · split
      · have h : farTotalWords [Asm.xori rd rs (w.toBitVec.extractLsb' 0 12)] = 1 := rfl; omega
      · rw [farTotalWords_append]
        have hli := li_farTotalWords_le AbiReg.t0 w.toBitVec
        have h1 : farTotalWords [Asm.xor rd rs AbiReg.t0] = 1 := rfl
        omega
  | shl =>
    dsimp only [emitBinConstRhsTo]
    split
    · omega
    · have h : farTotalWords [Asm.slli rd rs (BitVec.ofNat 6 (w.toNat % 64))] = 1 := rfl; omega
  | shr =>
    dsimp only [emitBinConstRhsTo]
    split
    · omega
    · have h : farTotalWords [Asm.srli rd rs (BitVec.ofNat 6 (w.toNat % 64))] = 1 := rfl; omega
  | mul =>
    exact emitMulConstTo_farTotalWords_le rd rs AbiReg.t0 w
  | «mulhi» =>
    dsimp only [emitBinConstRhsTo]
    split
    · have h : farTotalWords [Asm.addi rd AbiReg.zero 0#12] = 1 := rfl; omega
    · rw [farTotalWords_append]
      have hli := li_farTotalWords_le AbiReg.t0 w.toBitVec
      have h1 : farTotalWords [Asm.mulhu rd rs AbiReg.t0] = 1 := rfl
      omega

theorem emitBinConstRhs_farTotalWords_le (op : BinOp) (w : UInt64) :
    farTotalWords (emitBinConstRhs op w) ≤ 11 :=
  emitBinConstRhsTo_farTotalWords_le AbiReg.a0 AbiReg.a0 op w

theorem emitSimpleExpr_allInstrs {tab : Tab} {rd tmp : Reg} {e : Expr} {cs : List AsmItem}
    (h : emitSimpleExpr tab rd tmp e = some cs) :
    allInstrs cs = true := by
  cases e with
  | const _ => cases h; exact li_allInstrs _ _
  | var _ | len8 _ | len64 _ | glob _ => cases h; exact loadMemOff_allInstrs _ _ _ _ _
  | bin _ _ _ | cmpw _ _ _ | ld8 _ _ | ld64 _ _ | ldc _ _ | ld64t _ _ _
  | len64t _ _ | ld8x8 _ _ | ld32t _ _ _ | ld32h _ _ _ _ => cases h

theorem emitSimpleExprR_allInstrs {tab : Tab} {fl : FrameLayout} {rd tmp : Reg} {e : Expr}
    {cs : List AsmItem} (h : emitSimpleExprR tab fl rd tmp e = some cs) :
    allInstrs cs = true := by
  cases e with
  | const _ => cases h; exact li_allInstrs _ _
  | var x =>
    dsimp only [emitSimpleExprR] at h
    split at h
    · cases h; split <;> rfl
    · cases h; exact loadMemOff_allInstrs _ _ _ _ _
  | len8 _ | len64 _ | glob _ => cases h; exact loadMemOffGp_allInstrs _ _ _ _ _
  | bin _ _ _ | cmpw _ _ _ | ld8 _ _ | ld64 _ _ | ldc _ _ | ld64t _ _ _
  | len64t _ _ | ld8x8 _ _ | ld32t _ _ _ | ld32h _ _ _ _ => cases h

theorem emitCmpwTo_allInstrs (rd : Reg) (c : Cmp) (rL rR : Reg) :
    allInstrs (emitCmpwTo rd c rL rR) = true := by
  cases c <;> rfl

theorem emitCmpw_allInstrs (c : Cmp) (rL rR : Reg) :
    allInstrs (emitCmpw c rL rR) = true :=
  emitCmpwTo_allInstrs AbiReg.a0 c rL rR

theorem emitCmpwTo_farTotalWords_le (rd : Reg) (c : Cmp) (rL rR : Reg) :
    farTotalWords (emitCmpwTo rd c rL rR) ≤ 2 := by
  cases c with
  | eq => have h : farTotalWords (emitCmpwTo rd .eq rL rR) = 2 := rfl; omega
  | ne => have h : farTotalWords (emitCmpwTo rd .ne rL rR) = 2 := rfl; omega
  | ult => have h : farTotalWords (emitCmpwTo rd .ult rL rR) = 1 := rfl; omega
  | ule => have h : farTotalWords (emitCmpwTo rd .ule rL rR) = 2 := rfl; omega
  | slt => have h : farTotalWords (emitCmpwTo rd .slt rL rR) = 1 := rfl; omega
  | sle => have h : farTotalWords (emitCmpwTo rd .sle rL rR) = 2 := rfl; omega

theorem emitCmpw_farTotalWords_le (c : Cmp) (rL rR : Reg) :
    farTotalWords (emitCmpw c rL rR) ≤ 2 :=
  emitCmpwTo_farTotalWords_le AbiReg.a0 c rL rR

theorem brCmp_noT6Branch (op : Cmp) (want : Bool) (rL rR : Reg)
    (hL : rL ≠ AbiReg.t6) (hR : rR ≠ AbiReg.t6) (target : String) :
    noT6Branch [brCmp op want rL rR target] = true := by
  have h1 : (rL != AbiReg.t6) = true := bne_iff_ne.mpr hL
  have h2 : (rR != AbiReg.t6) = true := bne_iff_ne.mpr hR
  cases op <;> cases want <;>
    simp [brCmp, noT6Branch, asmItemNoT6Branch, Asm.beq, Asm.bne, Asm.bltu, Asm.bgeu, Asm.blt, Asm.bge, h1, h2]

theorem brCmp_lblNames (op : Cmp) (want : Bool) (rL rR : Reg) (target : String) :
    lblNames [brCmp op want rL rR target] = [] := by
  cases op <;> cases want <;> rfl

theorem brCmp_targetsIn (op : Cmp) (want : Bool) (rL rR : Reg) (target : String) :
    targetsIn [brCmp op want rL rR target] = [target] := by
  cases op <;> cases want <;> rfl

theorem brCmp_farTotalWords (op : Cmp) (want : Bool) (rL rR : Reg) (target : String) :
    farTotalWords [brCmp op want rL rR target] = 5 := by
  cases op <;> cases want <;> rfl

/-! ### Register-Allocation & Frame-Layout Structural Lemmas -/

private theorem regAllocValid_go_spec (nlocals : Nat) (bank : List Reg) :
    ∀ (alloc : RegAlloc) (seenV : List Var),
      regAllocValid.go nlocals bank seenV alloc = true →
      ∀ p ∈ alloc, p.1 < nlocals ∧ p.2 ∈ bank := by
  intro alloc
  induction alloc with
  | nil => intro _ _ _ h; cases h
  | cons hd rest ih =>
    intro seenV h
    rcases hd with ⟨x, r⟩
    unfold regAllocValid.go at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not] at h
    obtain ⟨⟨⟨hx, hr⟩, _⟩, hrest⟩ := h
    have hall := ih (x :: seenV) hrest
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact ⟨hx, hr⟩
    · exact hall p hp'

private theorem regAllocValid_spec {isLeaf : Bool} {nlocals : Nat} {alloc : RegAlloc}
    (h : regAllocValid isLeaf nlocals alloc = true) :
    ∀ p ∈ alloc, p.1 < nlocals ∧ p.2 ∈ allowedRegs true :=
  regAllocValid_go_spec nlocals (allowedRegs true) alloc [] h

private theorem lookup_mem_of_some {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {k : α} {v : β}, l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => by simp at h
  | (a, b) :: rest, k, v, h => by
    simp only [List.lookup] at h
    split at h
    · next hka =>
      cases h
      have : k = a := beq_iff_eq.mp hka
      subst this
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem_of_some h)

private theorem allowedRegs_ne_t6 (isLeaf : Bool) :
    ∀ r ∈ allowedRegs isLeaf, r ≠ AbiReg.t6 := by
  have hall : (allowedRegs isLeaf).all (· != AbiReg.t6) = true := by
    cases isLeaf <;> decide
  rw [List.all_eq_true] at hall
  intro r hr
  exact bne_iff_ne.mp (hall r hr)

/-- Predicate: no local variable in `fl.alloc` is assigned to scratch register `t6`. -/
def AllocNoT6 (fl : FrameLayout) : Prop :=
  ∀ x r, fl.alloc.lookup x = some r → r ≠ AbiReg.t6

private theorem fnFrameLayout_alloc_valid (fd : FunDecl) :
    regAllocValid (fnFrameLayout fd).isLeaf (fnFrameLayout fd).nlocals (fnFrameLayout fd).alloc = true := by
  dsimp only [fnFrameLayout]
  split
  · next h => simp only [Bool.and_eq_true] at h; exact h.1.1
  · rfl

private theorem fnFrameLayout_allocNoT6 (fd : FunDecl) :
    AllocNoT6 (fnFrameLayout fd) := by
  intro x r hlk
  have hall := regAllocValid_spec (fnFrameLayout_alloc_valid fd)
  exact allowedRegs_ne_t6 _ r (hall (x, r) (lookup_mem_of_some hlk)).2

theorem exprReg?_ne_t6 {fl : FrameLayout} (hfl : AllocNoT6 fl) {e : Expr} {r : Reg}
    (hr : exprReg? fl.alloc e = some r) : r ≠ AbiReg.t6 := by
  cases e with
  | const w =>
    dsimp only [exprReg?] at hr
    split at hr
    · cases hr; decide
    · cases hr
  | var x => exact hfl x r hr
  | _ => cases hr

private theorem fnFrameLayout_savedRegs_le (fd : FunDecl) :
    (fnFrameLayout fd).savedRegs.length ≤ 10 := by
  dsimp only [fnFrameLayout]
  have hlen : calleeSavedBank.length = 10 := rfl
  exact hlen ▸ List.length_filter_le _ _

private theorem fnFrameLayout_protectedSlots_le (fd : FunDecl) :
    (fnFrameLayout fd).protectedSlots ≤ 11 := by
  have hs := fnFrameLayout_savedRegs_le fd
  dsimp only [FrameLayout.protectedSlots, FrameLayout.raSlots]
  split <;> omega

private theorem fnFrameLayout_spilledVars_le (fd : FunDecl) :
    (fnFrameLayout fd).spilledVars.length ≤ (fnFrameLayout fd).nlocals := by
  dsimp only [fnFrameLayout]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem fnFrameLayoutFor_nlocals (tab : Tab) (fd : FunDecl) :
    (fnFrameLayoutFor tab fd).nlocals = numLocalsFn fd := by
  dsimp only [fnFrameLayoutFor, fnFrameLayout]

theorem fnFrameLayoutFor_allocNoT6 (tab : Tab) (fd : FunDecl) :
    AllocNoT6 (fnFrameLayoutFor tab fd) := by
  dsimp only [AllocNoT6, fnFrameLayoutFor]
  exact fnFrameLayout_allocNoT6 fd

theorem fnFrameLayoutFor_savedRegs_le (tab : Tab) (fd : FunDecl) :
    (fnFrameLayoutFor tab fd).savedRegs.length ≤ 10 := by
  dsimp only [fnFrameLayoutFor]
  exact fnFrameLayout_savedRegs_le fd

theorem fnFrameLayoutFor_protectedSlots_le (tab : Tab) (fd : FunDecl) :
    (fnFrameLayoutFor tab fd).protectedSlots ≤ 11 := by
  dsimp only [FrameLayout.protectedSlots, FrameLayout.raSlots, fnFrameLayoutFor]
  exact fnFrameLayout_protectedSlots_le fd

theorem fnFrameLayoutFor_spilledVars_le (tab : Tab) (fd : FunDecl) :
    (fnFrameLayoutFor tab fd).spilledVars.length ≤ (fnFrameLayoutFor tab fd).nlocals := by
  dsimp only [fnFrameLayoutFor]
  exact fnFrameLayout_spilledVars_le fd

theorem tailCallRetMatch_spec {tab : Tab} {s1 s2 : Stmt}
    {xs : List Var} {f : FnName} {args es : List Expr}
    (h : tailCallRetMatch tab s1 s2 = some (xs, f, args, es)) :
    s1 = .call xs f args ∧ s2 = .ret es ∧ isTailCallRet tab xs es args = true := by
  cases s1 with
  | «call» xs' f' args' =>
    cases s2 with
    | ret es' =>
      dsimp only [tailCallRetMatch] at h
      split at h
      · cases h; exact ⟨rfl, rfl, ‹_›⟩
      · cases h
    | _ => cases h
  | _ => cases h

theorem isAbort0Stmt_implies_stmtHasAbort0 {s : Stmt} (h : isAbort0Stmt s = true) :
    stmtHasAbort0 s = true := by
  dsimp only [isAbort0Stmt] at h
  split at h
  · rfl
  · cases h

theorem constVal_eq_zero_implies_stmtHasAbort0 {e : Expr}
    (h : (e.constVal? == some 0) = true) :
    stmtHasAbort0 (.abort e) = true := by
  cases e with
  | const w =>
    simp only [Expr.constVal?, beq_iff_eq, Option.some.injEq] at h
    subst h; rfl
  | _ => cases h

private theorem usedTempsExpr_le_maxTempsExpr :
    ∀ e : Expr, usedTempsExpr e ≤ maxTempsExpr e
  | .const _ | .var _ | .len8 _ | .len64 _ | .glob _ => Nat.le_refl 0
  | .ld8 _ i | .ld64 _ i | .ldc _ i | .len64t _ i | .ld8x8 _ i =>
    usedTempsExpr_le_maxTempsExpr i
  | .bin _ a b | .cmpw _ a b => by
    have ha := usedTempsExpr_le_maxTempsExpr a
    have hb := usedTempsExpr_le_maxTempsExpr b
    dsimp only [usedTempsExpr, maxTempsExpr]
    split
    · omega
    · split
      · omega
      · split <;> omega
  | .ld64t _ t i | .ld32t _ t i | .ld32h _ t i _ => by
    have ht := usedTempsExpr_le_maxTempsExpr t
    have hi := usedTempsExpr_le_maxTempsExpr i
    dsimp only [usedTempsExpr, maxTempsExpr]
    split <;> omega

private theorem usedTempsCond_le_maxTempsCond :
    ∀ c : Cond, usedTempsCond c ≤ maxTempsCond c
  | .cmp _ a b => by
    have ha := usedTempsExpr_le_maxTempsExpr a
    have hb := usedTempsExpr_le_maxTempsExpr b
    dsimp only [usedTempsCond, maxTempsCond]
    split
    · omega
    · split
      · omega
      · split <;> omega
  | .and p q | .or p q => by
    have hp := usedTempsCond_le_maxTempsCond p
    have hq := usedTempsCond_le_maxTempsCond q
    dsimp only [usedTempsCond, maxTempsCond]; omega
  | .not p => usedTempsCond_le_maxTempsCond p

private theorem usedTempsExprs_le_maxTempsExprs (es : List Expr) :
    usedTempsExprs es ≤ maxTempsExprs es := by
  have go : ∀ (xs : List Expr) (k acc1 acc2 : Nat),
      acc1 ≤ acc2 →
      (xs.zipIdx k).foldl (fun a (p : Expr × Nat) => max a (p.2 + max 1 (usedTempsExpr p.1))) acc1 ≤
      (xs.zipIdx k).foldl (fun a (p : Expr × Nat) => max a (p.2 + max 1 (maxTempsExpr p.1))) acc2 := by
    intro xs
    induction xs with
    | nil => intro _ _ _ h; exact h
    | cons x xs ih =>
      intro k a1 a2 h
      simp only [List.zipIdx_cons, List.foldl_cons]
      have hx := usedTempsExpr_le_maxTempsExpr x
      exact ih (k + 1) _ _ (by omega)
  exact go es 0 0 0 (Nat.le_refl 0)

private theorem usedTempsStmt_le_maxTempsStmt :
    ∀ s : Stmt, usedTempsStmt s ≤ maxTempsStmt s
  | .skip | .brk => Nat.le_refl 0
  | .set _ e | .abort e | .gset _ e => usedTempsExpr_le_maxTempsExpr e
  | .st8 _ i e | .st64 _ i e => by
    have hi := usedTempsExpr_le_maxTempsExpr i
    have he := usedTempsExpr_le_maxTempsExpr e
    dsimp only [usedTempsStmt, maxTempsStmt]
    split
    · omega
    · split <;> omega
  | .st64t _ t i e | .st32t _ t i e => by
    have ht := usedTempsExpr_le_maxTempsExpr t
    have hi := usedTempsExpr_le_maxTempsExpr i
    have he := usedTempsExpr_le_maxTempsExpr e
    dsimp only [usedTempsStmt, maxTempsStmt]
    split
    · split
      · omega
      · split <;> omega
    · omega
  | .seq s1 s2 => by
    have h1 := usedTempsStmt_le_maxTempsStmt s1
    have h2 := usedTempsStmt_le_maxTempsStmt s2
    dsimp only [usedTempsStmt, maxTempsStmt]; omega
  | .ite c s1 s2 => by
    have hc := usedTempsCond_le_maxTempsCond c
    have h1 := usedTempsStmt_le_maxTempsStmt s1
    have h2 := usedTempsStmt_le_maxTempsStmt s2
    dsimp only [usedTempsStmt, maxTempsStmt]; omega
  | .while c b => by
    have hc := usedTempsCond_le_maxTempsCond c
    have hb := usedTempsStmt_le_maxTempsStmt b
    dsimp only [usedTempsStmt, maxTempsStmt]; omega
  | .ret es => by
    cases es with
    | nil => exact Nat.le_refl 0
    | cons e rest =>
      cases rest with
      | nil =>
        have he := usedTempsExpr_le_maxTempsExpr e
        simp only [usedTempsStmt, maxTempsStmt, maxTempsExprs,
          List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil]
        omega
      | cons e2 rs => exact usedTempsExprs_le_maxTempsExprs (e :: e2 :: rs)
  | .call _ _ args => usedTempsExprs_le_maxTempsExprs args
  | .copy64 d di src si n => by
    have hdi := usedTempsExpr_le_maxTempsExpr di
    have hsi := usedTempsExpr_le_maxTempsExpr si
    have hn := usedTempsExpr_le_maxTempsExpr n
    cases d with
    | plain _ =>
      cases src with
      | plain _ => dsimp only [usedTempsStmt, maxTempsStmt]; omega
      | tier _ st => have := usedTempsExpr_le_maxTempsExpr st; dsimp only [usedTempsStmt, maxTempsStmt]; omega
    | tier _ dt =>
      have := usedTempsExpr_le_maxTempsExpr dt
      cases src with
      | plain _ => dsimp only [usedTempsStmt, maxTempsStmt]; omega
      | tier _ st => have := usedTempsExpr_le_maxTempsExpr st; dsimp only [usedTempsStmt, maxTempsStmt]; omega
  | .copy8w d di _ si n => by
    have hdi := usedTempsExpr_le_maxTempsExpr di
    have hsi := usedTempsExpr_le_maxTempsExpr si
    have hn := usedTempsExpr_le_maxTempsExpr n
    cases d with
    | plain _ => dsimp only [usedTempsStmt, maxTempsStmt]; omega
    | tier _ dt => have := usedTempsExpr_le_maxTempsExpr dt; dsimp only [usedTempsStmt, maxTempsStmt]; omega
  | .scan8 _ _ i e _ => by
    have hi := usedTempsExpr_le_maxTempsExpr i
    have he := usedTempsExpr_le_maxTempsExpr e
    dsimp only [usedTempsStmt, maxTempsStmt]
    split <;> omega

private theorem maxUsedTempsExprs_le_maxTempsExprs (es : List Expr) :
    maxUsedTempsExprs es ≤ maxTempsExprs es := by
  have hfold_ge : ∀ (l : List (Expr × Nat)) (init : Nat),
      init ≤ l.foldl (fun acc (e, idx) => max acc (idx + max 1 (maxTempsExpr e))) init := by
    intro l; induction l with
    | nil => intro init; exact Nat.le_refl _
    | cons hd tl ih => intro init; exact Nat.le_trans (Nat.le_max_left _ _) (ih _)
  have go : ∀ (xs : List Expr) (k acc : Nat),
      maxUsedTempsExprs xs ≤
        (xs.zipIdx k).foldl (fun a (p : Expr × Nat) => max a (p.2 + max 1 (maxTempsExpr p.1))) acc := by
    intro xs
    induction xs with
    | nil => intro _ _; exact Nat.zero_le _
    | cons x xs ih =>
      intro k acc
      simp only [maxUsedTempsExprs, List.zipIdx_cons, List.foldl_cons]
      have hx := usedTempsExpr_le_maxTempsExpr x
      have h1 : usedTempsExpr x ≤ max acc (k + max 1 (maxTempsExpr x)) := by omega
      exact Nat.max_le.mpr ⟨Nat.le_trans h1 (hfold_ge _ _), ih (k + 1) _⟩
  exact go es 0 0

private theorem usedTempsCallArgs_le_maxTempsExprs (alloc : RegAlloc) (args : List Expr) :
    usedTempsCallArgs alloc args ≤ maxTempsExprs args := by
  unfold usedTempsCallArgs
  split
  · exact maxUsedTempsExprs_le_maxTempsExprs args
  · exact usedTempsExprs_le_maxTempsExprs args

private theorem usedTempsRetR_le_maxTempsExprs (isLeaf : Bool) (alloc : RegAlloc) (es : List Expr) :
    usedTempsRetR isLeaf alloc es ≤ maxTempsExprs es := by
  cases es with
  | nil => exact Nat.le_refl 0
  | cons e1 rest =>
    cases rest with
    | nil =>
      have he := usedTempsExpr_le_maxTempsExpr e1
      simp only [usedTempsRetR, maxTempsExprs, List.zipIdx_cons, List.zipIdx_nil,
        List.foldl_cons, List.foldl_nil]
      omega
    | cons e2 rest2 =>
      dsimp only [usedTempsRetR]
      split
      · exact maxUsedTempsExprs_le_maxTempsExprs _
      · exact usedTempsExprs_le_maxTempsExprs _

theorem usedTempsStmtR_le_maxTempsStmt (isLeaf : Bool) (alloc : RegAlloc) :
    ∀ s : Stmt, usedTempsStmtR isLeaf alloc s ≤ maxTempsStmt s
  | .seq s1 s2 => by
    have h1 := usedTempsStmtR_le_maxTempsStmt isLeaf alloc s1
    have h2 := usedTempsStmtR_le_maxTempsStmt isLeaf alloc s2
    dsimp only [usedTempsStmtR, maxTempsStmt]; omega
  | .ite c s1 s2 => by
    have hc := usedTempsCond_le_maxTempsCond c
    have h1 := usedTempsStmtR_le_maxTempsStmt isLeaf alloc s1
    have h2 := usedTempsStmtR_le_maxTempsStmt isLeaf alloc s2
    dsimp only [usedTempsStmtR, maxTempsStmt]; omega
  | .while c b => by
    have hc := usedTempsCond_le_maxTempsCond c
    have hb := usedTempsStmtR_le_maxTempsStmt isLeaf alloc b
    dsimp only [usedTempsStmtR, maxTempsStmt]; omega
  | .ret es => usedTempsRetR_le_maxTempsExprs isLeaf alloc es
  | .call _ _ args => usedTempsCallArgs_le_maxTempsExprs alloc args
  | .skip => usedTempsStmt_le_maxTempsStmt .skip
  | .brk => usedTempsStmt_le_maxTempsStmt .brk
  | .set x e => usedTempsStmt_le_maxTempsStmt (.set x e)
  | .gset g e => usedTempsStmt_le_maxTempsStmt (.gset g e)
  | .abort e => usedTempsStmt_le_maxTempsStmt (.abort e)
  | .st8 a i e => usedTempsStmt_le_maxTempsStmt (.st8 a i e)
  | .st64 a i e => usedTempsStmt_le_maxTempsStmt (.st64 a i e)
  | .st64t a t i e => usedTempsStmt_le_maxTempsStmt (.st64t a t i e)
  | .st32t a t i e => usedTempsStmt_le_maxTempsStmt (.st32t a t i e)
  | .copy64 d di s si n => usedTempsStmt_le_maxTempsStmt (.copy64 d di s si n)
  | .copy8w d di s si n => usedTempsStmt_le_maxTempsStmt (.copy8w d di s si n)
  | .scan8 x s i e c => usedTempsStmt_le_maxTempsStmt (.scan8 x s i e c)

theorem saveCalleeRegs_allInstrs (fl : FrameLayout) :
    allInstrs (saveCalleeRegs fl) = true := by
  dsimp only [saveCalleeRegs]
  exact allInstrs_flatMap (fun _ _ => storeMemOff_allInstrs _ _ _ _ _)

theorem restoreCalleeRegs_allInstrs (fl : FrameLayout) :
    allInstrs (restoreCalleeRegs fl) = true := by
  dsimp only [restoreCalleeRegs]
  exact allInstrs_flatMap (fun _ _ => loadMemOff_allInstrs _ _ _ _ _)

theorem framePopItems_allInstrs (fl : FrameLayout) :
    allInstrs (framePopItems fl) = true := by
  dsimp only [framePopItems]
  split
  · rfl
  · have hra : allInstrs (if fl.isLeaf = true then [] else [Asm.ld AbiReg.ra AbiReg.sp 0#12]) = true := by
      split <;> rfl
    simp only [allInstrs_append, Bool.and_eq_true, restoreCalleeRegs_allInstrs fl, hra,
      addImmOff_allInstrs _ _ _ _, and_self]

theorem copyParamsR_allInstrs (fl : FrameLayout) (nparams : Nat) :
    allInstrs (copyParamsR fl nparams) = true := by
  dsimp only [copyParamsR]
  refine allInstrs_flatMap (fun i _ => ?_)
  split
  · cases fl.alloc.lookup i with
    | some _ => dsimp only; split <;> rfl
    | none =>
      dsimp only
      split
      · rfl
      · exact storeMemOff_allInstrs _ _ _ _ _
  · cases fl.alloc.lookup i with
    | some _ => exact loadMemOff_allInstrs _ _ _ _ _
    | none =>
      dsimp only
      split
      · rfl
      · rw [allInstrs_append, Bool.and_eq_true]
        exact ⟨loadMemOff_allInstrs _ _ _ _ _, storeMemOff_allInstrs _ _ _ _ _⟩

theorem zeroLocalsR_allInstrs (fl : FrameLayout) (fd : FunDecl) :
    allInstrs (zeroLocalsR fl fd) = true := by
  dsimp only [zeroLocalsR]
  refine allInstrs_flatMap (fun j _ => ?_)
  split
  · rfl
  · cases fl.alloc.lookup (fd.nparams + j) with
    | some _ => rfl
    | none =>
      dsimp only
      split
      · rfl
      · exact storeMemOff_allInstrs _ _ _ _ _

theorem copyTempsToResultsR_allInstrs (tab : Tab) (fl : FrameLayout) (tmp count : Nat) :
    allInstrs (copyTempsToResultsR tab fl tmp count) = true := by
  dsimp only [copyTempsToResultsR]
  split
  · split <;> rfl
  · refine allInstrs_flatMap (fun i _ => ?_)
    split
    · exact loadMemOff_allInstrs _ _ _ _ _
    · rw [allInstrs_append, Bool.and_eq_true]
      exact ⟨loadMemOff_allInstrs _ _ _ _ _, storeMemOff_allInstrs _ _ _ _ _⟩

theorem copyResultsToLocalsR_allInstrs (tab : Tab) (fl : FrameLayout) (xs : List Var) :
    allInstrs (copyResultsToLocalsR tab fl xs) = true := by
  dsimp only [copyResultsToLocalsR]
  refine allInstrs_flatMap (fun ⟨x, i⟩ _ => ?_)
  dsimp only
  split
  · split
    · split
      · split <;> rfl
      · exact loadMemOff_allInstrs _ _ _ _ _
    · rfl
  · split
    · rfl
    · split
      · split
        · exact storeMemOff_allInstrs _ _ _ _ _
        · rw [allInstrs_append, Bool.and_eq_true]
          exact ⟨loadMemOff_allInstrs _ _ _ _ _, storeMemOff_allInstrs _ _ _ _ _⟩
      · exact storeMemOff_allInstrs _ _ _ _ _


theorem farTotalWords_flatMap_perm {α : Type} {xs ys : List α} (h : xs.Perm ys)
    (f : α → List AsmItem) :
    farTotalWords (xs.flatMap f) = farTotalWords (ys.flatMap f) := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.flatMap_cons, farTotalWords_append, ih]
  | swap x y l => simp only [List.flatMap_cons, farTotalWords_append]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

end ConAgua.RISCV.Bridge
