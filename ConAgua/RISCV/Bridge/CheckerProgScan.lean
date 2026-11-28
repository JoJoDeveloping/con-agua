import ConAgua.RISCV.Bridge.CheckerProgScanBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Single-Pass Fused Kernel Scan for `L.Checker.checkerProg`

Checks function names directly on raw ASCII UTF-8 bytes (`String.toByteArray.data.toList`)
instead of decoding UTF-8 via `String.toList`, reuses the same byte list for
`L.Compiler.bytesCode`, and runs a single `kernel_eq_true` pass over the full
`L.Checker.checkerProg` with free-variable-parameterized soundness lemmas.
-/

namespace ConAgua.RISCV.Bridge

/-! ## Raw-Byte Function-Name Label Safety Checker -/

def isPrefixBytes : List UInt8 → List UInt8 → Bool
  | [], _ => true
  | _ :: _, [] => false
  | ⟨⟨p, _⟩⟩ :: ps, ⟨⟨x, _⟩⟩ :: xs => p.beq x && isPrefixBytes ps xs

def fixedSufRevB : List (List UInt8) :=
  [[48, 116, 101, 114, 95],
   [101, 117, 103, 111, 108, 105, 112, 101, 95],
   [98, 117, 116, 115, 114, 114, 101, 95],
   [98, 117, 116, 115, 104, 120, 101, 95],
   [98, 117, 116, 115, 48, 116, 114, 111, 98, 97, 95]]

def dynTagRevB : List (List UInt8) :=
  [[95, 100, 110, 97, 95],
   [95, 114, 111, 95],
   [95, 101, 115, 108, 101, 95],
   [95, 102, 105, 100, 110, 101, 95],
   [95, 101, 108, 105, 104, 119, 95],
   [95, 119, 100, 110, 101, 95],
   [95, 52, 54, 99, 95],
   [95, 101, 110, 111, 100, 95, 52, 54, 99, 95],
   [95, 119, 56, 99, 95],
   [95, 101, 110, 111, 100, 95, 119, 56, 99, 95],
   [95, 110, 97, 99, 115, 95],
   [95, 101, 110, 111, 100, 95, 110, 97, 99, 115, 95]]

def dropDigitsRevB : List UInt8 → Bool → List UInt8 × Bool
  | ⟨⟨b, h⟩⟩ :: bs, seen =>
    if Nat.ble 48 b && b.ble 57 then dropDigitsRevB bs true else (⟨⟨b, h⟩⟩ :: bs, seen)
  | [], seen => ([], seen)

def revAscii : List UInt8 → List UInt8 → Option (List UInt8)
  | [], acc => some acc
  | ⟨⟨b, h⟩⟩ :: bs, acc =>
    match b.blt 128 with
    | true => revAscii bs (⟨⟨b, h⟩⟩ :: acc)
    | false => none

def fnBytesSafeFast (bs : List UInt8) : Bool :=
  match revAscii bs [] with
  | none => false
  | some [] => false
  | some (rev@((⟨⟨last, _⟩⟩) :: _)) =>
    if !(last.beq 101 || last.beq 98 || (Nat.ble 48 last && last.ble 57)) then true
    else if fixedSufRevB.any (fun sr => isPrefixBytes sr rev) then false
    else
      let (rest, seenDigit) := dropDigitsRevB rev false
      !seenDigit || !(dynTagRevB.any (fun tr => isPrefixBytes tr rest))

noncomputable def sliceFusedFastGo (xs : List (L.FnName × L.FunDecl)) (acc sumCap : Nat) : Bool :=
  match xs with
  | [] => acc.blt sumCap
  | x :: rest =>
    let bs := x.1.toByteArray.data.toList
    match fnBytesSafeFast bs with
    | false => false
    | true =>
      match stmtScanL checkerLmapLit 2 12 10 L.Checker.checkerProg_wf.tree minRetTreeLit
          (romFastOk allowedRomsWithLenLit) x.2.nlocals false 0 x.2.body with
      | .fail => false
      | .ok mf mr mt b32 =>
        let minRet := if mf then 1 else if mr == 0 then 100 else mr
        if ((minRetTreeLit.find (L.Compiler.bytesCode bs)).getD 1).ble minRet then
          sliceFusedFastGo rest (acc + fnScanBound x.2 mt b32) sumCap
        else false

section FullScan
set_option maxRecDepth 65536
set_option maxHeartbeats 800000

kernel_eq_true checkerProg_fused_all :
  sliceFusedFastGo L.Checker.checkerProg 0 3600000

end FullScan

/-! ## Soundness Proofs -/

private theorem char_toNat_ofNat_lt128 (n : Nat) (hn : n < 128) :
    (Char.ofNat n).toNat = n := by
  have hv : Nat.isValidChar n := Or.inl (by omega)
  simp only [Char.ofNat, hv, ↓reduceDIte, Char.ofNatAux, Char.toNat]
  rfl

private theorem utf8EncodeChar_ascii (b : UInt8) (hb : b.toNat < 128) :
    String.utf8EncodeChar (Char.ofNat b.toNat) = [b] := by
  have hval := char_toNat_ofNat_lt128 b.toNat hb
  simp [String.utf8EncodeChar, hval, show b.toNat ≤ 127 by omega]

private theorem list_toByteArray_eq (bs : List UInt8) :
    bs.toByteArray = ByteArray.mk ⟨bs⟩ := by
  have h : ∀ (acc : ByteArray) (l : List UInt8),
      List.toByteArray.loop l acc = ByteArray.mk ⟨acc.data.toList ++ l⟩ := by
    intro acc l
    induction l generalizing acc with
    | nil =>
      cases acc with | mk d => cases d; simp [List.toByteArray.loop]
    | cons x xs ih =>
      simp only [List.toByteArray.loop, ih]
      congr 1; congr 1
      simp [ByteArray.push, List.append_assoc]
  have he : ByteArray.empty.data.toList = [] := rfl
  have := h ByteArray.empty bs
  rw [he, List.nil_append] at this
  exact this

private theorem utf8Encode_ascii (bs : List UInt8) (h : ∀ b ∈ bs, b.toNat < 128) :
    (bs.map (fun b => Char.ofNat b.toNat)).utf8Encode = ByteArray.mk ⟨bs⟩ := by
  have hflat : (bs.map (fun b => Char.ofNat b.toNat)).flatMap String.utf8EncodeChar = bs := by
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      simp only [List.map_cons, List.flatMap_cons,
        utf8EncodeChar_ascii b (h b List.mem_cons_self), List.singleton_append]
      exact congrArg (b :: ·) (ih fun x hx => h x (List.mem_cons_of_mem b hx))
  rw [List.utf8Encode, hflat, list_toByteArray_eq]

private theorem string_toList_of_ascii (s : String)
    (h : ∀ b ∈ s.toByteArray.data.toList, b.toNat < 128) :
    s.toList = s.toByteArray.data.toList.map (fun b => Char.ofNat b.toNat) := by
  let cs := s.toByteArray.data.toList.map (fun b => Char.ofNat b.toNat)
  have hba : (String.ofList cs).toByteArray = s.toByteArray := by
    rw [String.toByteArray_ofList, utf8Encode_ascii _ h]
  have hs : s = String.ofList cs := by
    cases s
    cases hof : String.ofList cs
    rw [hof] at hba
    congr
    exact hba.symm
  conv => lhs; rw [hs]
  exact String.toList_ofList

private theorem revAscii_spec : ∀ (bs acc res : List UInt8),
    revAscii bs acc = some res →
    res = bs.reverse ++ acc ∧ ∀ b ∈ bs, b.toNat < 128
  | [], acc, res, h => by
    cases h; exact ⟨rfl, fun _ hm => nomatch hm⟩
  | ⟨⟨b, hb⟩⟩ :: bs, acc, res, h => by
    dsimp only [revAscii] at h
    cases hlt : b.blt 128 with
    | false => rw [hlt] at h; cases h
    | true =>
      rw [hlt] at h
      obtain ⟨hres, hall⟩ := revAscii_spec bs (⟨⟨b, hb⟩⟩ :: acc) res h
      have hblt : b < 128 := by simp only [Nat.blt, Nat.ble_eq] at hlt; omega
      refine ⟨by simpa [List.reverse_cons, List.append_assoc] using hres, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hblt
      · exact hall x hx'

private theorem isPrefixBytes_map_eq : ∀ (ps xs : List UInt8),
    (∀ p ∈ ps, p.toNat < 128) →
    (∀ x ∈ xs, x.toNat < 128) →
    isPrefixBytes ps xs =
      isPrefixCharsL (ps.map fun b => Char.ofNat b.toNat) (xs.map fun b => Char.ofNat b.toNat)
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | ⟨⟨p, hp⟩⟩ :: ps, ⟨⟨x, hx⟩⟩ :: xs, hps, hxs => by
    have hp128 : p < 128 := hps ⟨⟨p, hp⟩⟩ List.mem_cons_self
    have hx128 : x < 128 := hxs ⟨⟨x, hx⟩⟩ List.mem_cons_self
    have hch : (p.beq x) = (Char.ofNat p == Char.ofNat x) := by
      have h1 := char_toNat_ofNat_lt128 p hp128
      have h2 := char_toNat_ofNat_lt128 x hx128
      cases h : p.beq x with
      | true =>
        have : p = x := Nat.eq_of_beq_eq_true h
        subst this; simp
      | false =>
        have hne : p ≠ x := Nat.ne_of_beq_eq_false h
        symm; rw [beq_eq_false_iff_ne]
        intro heq; apply hne
        have := congrArg Char.toNat heq; omega
    have hih := isPrefixBytes_map_eq ps xs
      (fun a ha => hps a (List.mem_cons_of_mem _ ha))
      (fun a ha => hxs a (List.mem_cons_of_mem _ ha))
    change (p.beq x && isPrefixBytes ps xs) =
      (Char.ofNat p == Char.ofNat x &&
        isPrefixCharsL (ps.map fun b => Char.ofNat b.toNat) (xs.map fun b => Char.ofNat b.toNat))
    rw [hch, hih]

private theorem isDigit_ofNat_lt128 (b : Nat) (hb : b < 128) :
    (Nat.ble 48 b && b.ble 57) = (Char.ofNat b).isDigit := by
  have hval : (Char.ofNat b).val.toNat = b := char_toNat_ofNat_lt128 b hb
  have h0 : '0'.val.toNat = 48 := rfl
  have h9 : '9'.val.toNat = 57 := rfl
  dsimp only [Char.isDigit]
  cases h1 : Nat.ble 48 b with
  | false =>
    have hlt : ¬(48 ≤ b) := fun h => by rw [Nat.ble_eq.mpr h] at h1; cases h1
    simp only [Bool.false_and]
    symm; simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    left; intro hle; exact hlt (by have := UInt32.le_iff_toNat_le.mp hle; omega)
  | true =>
    have hge : 48 ≤ b := Nat.ble_eq.mp h1
    cases h2 : b.ble 57 with
    | false =>
      have hgt : ¬(b ≤ 57) := fun h => by rw [Nat.ble_eq.mpr h] at h2; cases h2
      simp only [Bool.true_and]
      symm; simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      right; intro hle; exact hgt (by have := UInt32.le_iff_toNat_le.mp hle; omega)
    | true =>
      have hle : b ≤ 57 := Nat.ble_eq.mp h2
      simp only [Bool.true_and]
      symm; simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨UInt32.le_iff_toNat_le.mpr (by omega), UInt32.le_iff_toNat_le.mpr (by omega)⟩

private theorem dropDigitsRevB_map_eq : ∀ (bs : List UInt8) (seen : Bool),
    (∀ b ∈ bs, b.toNat < 128) →
    ((dropDigitsRevB bs seen).1.map (fun b => Char.ofNat b.toNat), (dropDigitsRevB bs seen).2) =
      dropDigitsRevL (bs.map fun b => Char.ofNat b.toNat) seen
  | [], seen, _ => rfl
  | ⟨⟨b, hb⟩⟩ :: bs, seen, hbs => by
    have hb128 : b < 128 := hbs ⟨⟨b, hb⟩⟩ List.mem_cons_self
    have hdig := isDigit_ofNat_lt128 b hb128
    change ((if (Nat.ble 48 b && b.ble 57) = true then dropDigitsRevB bs true else (⟨⟨b, hb⟩⟩ :: bs, seen)).1.map (fun b => Char.ofNat b.toNat),
            (if (Nat.ble 48 b && b.ble 57) = true then dropDigitsRevB bs true else (⟨⟨b, hb⟩⟩ :: bs, seen)).2) =
           if (Char.ofNat b).isDigit = true then dropDigitsRevL (bs.map fun b => Char.ofNat b.toNat) true
           else (Char.ofNat b :: bs.map (fun b => Char.ofNat b.toNat), seen)
    rw [hdig]
    cases hd : (Char.ofNat b).isDigit with
    | true =>
      simp only [↓reduceIte]
      exact dropDigitsRevB_map_eq bs true (fun a ha => hbs a (List.mem_cons_of_mem _ ha))
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl

private theorem fixedSufRevB_map : fixedSufRevB.map (List.map fun b => Char.ofNat b.toNat) = fixedSufRevL := by
  decide

private theorem dynTagRevB_map : dynTagRevB.map (List.map fun b => Char.ofNat b.toNat) = dynTagRevL := by
  decide

private theorem fixedSufRevB_ascii : ∀ sr ∈ fixedSufRevB, ∀ b ∈ sr, b.toNat < 128 := by
  decide

private theorem dynTagRevB_ascii : ∀ tr ∈ dynTagRevB, ∀ b ∈ tr, b.toNat < 128 := by
  decide

private theorem nat_beq_false_of_ne {a b : Nat} (h : a ≠ b) : a.beq b = false := by
  cases hb : a.beq b with
  | false => rfl
  | true => exact False.elim (h (Nat.eq_of_beq_eq_true hb))

private theorem list_any_congr_mem {α : Type} : ∀ {l : List α} {p q : α → Bool},
    (∀ x ∈ l, p x = q x) → l.any p = l.any q
  | [], _, _, _ => rfl
  | x :: xs, p, q, h => by
    simp only [List.any_cons, h x List.mem_cons_self,
      list_any_congr_mem (fun y hy => h y (List.mem_cons_of_mem x hy))]

private theorem fnBytesSafeFast_imp_fnCharsSafeFastL (s : String)
    (h : fnBytesSafeFast s.toByteArray.data.toList = true) :
    fnCharsSafeFastL s.toList = true := by
  dsimp only [fnBytesSafeFast] at h
  cases hrev : revAscii s.toByteArray.data.toList [] with
  | none => rw [hrev] at h; cases h
  | some rev =>
    rw [hrev] at h
    obtain ⟨hrevEq, hascii⟩ := revAscii_spec s.toByteArray.data.toList [] rev hrev
    rw [List.append_nil] at hrevEq
    cases rev with
    | nil => cases h
    | cons lastB revTail =>
      cases lastB with | ofBitVec bv => cases bv with | ofFin fv => cases fv with | mk last hlast =>
      have hs : s.toList = s.toByteArray.data.toList.map (fun b => Char.ofNat b.toNat) :=
        string_toList_of_ascii s hascii
      have hne : s.toList ≠ [] := by
        intro hemp
        have hba : s.toByteArray.data.toList = [] := by
          rw [hs, List.map_eq_nil_iff] at hemp; exact hemp
        rw [hba] at hrevEq; cases hrevEq
      have hrevAscii : ∀ b ∈ (⟨⟨⟨last, hlast⟩⟩⟩ :: revTail : List UInt8), b.toNat < 128 := by
        intro b hb
        rw [hrevEq, List.mem_reverse] at hb
        exact hascii b hb
      have hrevChars : s.toList.reverse =
          (⟨⟨⟨last, hlast⟩⟩⟩ :: revTail : List UInt8).map (fun b => Char.ofNat b.toNat) := by
        rw [hs, ← List.map_reverse, ← hrevEq]
      have hfixEq : fixedSufRevB.any (fun sr => isPrefixBytes sr (⟨⟨⟨last, hlast⟩⟩⟩ :: revTail)) =
          fixedSufRevL.any (fun sr => isPrefixCharsL sr s.toList.reverse) := by
        rw [← fixedSufRevB_map, List.any_map, hrevChars]
        refine list_any_congr_mem fun sr hsr => ?_
        exact isPrefixBytes_map_eq sr _ (fixedSufRevB_ascii sr hsr) hrevAscii
      have hdrop := dropDigitsRevB_map_eq (⟨⟨⟨last, hlast⟩⟩⟩ :: revTail) false hrevAscii
      have hrestAscii : ∀ b ∈ (dropDigitsRevB (⟨⟨⟨last, hlast⟩⟩⟩ :: revTail) false).1, b.toNat < 128 := by
        have aux : ∀ (l : List UInt8) (fl : Bool), (∀ b ∈ l, b.toNat < 128) →
            ∀ b ∈ (dropDigitsRevB l fl).1, b.toNat < 128 := by
          intro l; induction l with
          | nil => intro fl _ b hb; cases hb
          | cons u us ih =>
            cases u with | ofBitVec bv => cases bv with | ofFin fv => cases fv with | mk u hu =>
            intro fl hall b hb
            dsimp only [dropDigitsRevB] at hb
            by_cases hd : (Nat.ble 48 u && u.ble 57) = true
            · simp only [hd, ↓reduceIte] at hb
              exact ih true (fun a ha => hall a (List.mem_cons_of_mem _ ha)) b hb
            · simp only [hd, Bool.false_eq_true, ↓reduceIte] at hb
              exact hall b hb
        exact aux _ false hrevAscii
      have hdynEq : dynTagRevB.any (fun tr => isPrefixBytes tr (dropDigitsRevB (⟨⟨⟨last, hlast⟩⟩⟩ :: revTail) false).1) =
          dynTagRevL.any (fun tr => isPrefixCharsL tr (dropDigitsRevL s.toList.reverse false).1) := by
        rw [← dynTagRevB_map, List.any_map, hrevChars, ← hdrop]
        refine list_any_congr_mem fun tr htr => ?_
        exact isPrefixBytes_map_eq tr _ (dynTagRevB_ascii tr htr) hrestAscii
      cases hcs : s.toList with
      | nil => exact False.elim (hne hcs)
      | cons c0 cs0 =>
        dsimp only [fnCharsSafeFastL]
        rw [← hcs, ← hfixEq]
        by_cases hfast : (last.beq 101 || last.beq 98 || (Nat.ble 48 last && last.ble 57)) = true
        · simp only [hfast, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          cases hf : fixedSufRevB.any (fun sr => isPrefixBytes sr (⟨⟨⟨last, hlast⟩⟩⟩ :: revTail)) with
          | true => simp only [hf, ↓reduceIte] at h; cases h
          | false =>
            simp only [hf, Bool.false_eq_true, ↓reduceIte] at h ⊢
            rw [← hdynEq, hrevChars, ← hdrop]
            exact h
        · have hne101 : 101 ≠ last := fun heq => by subst heq; simp at hfast
          have hne98 : 98 ≠ last := fun heq => by subst heq; simp at hfast
          have hnotdig : (Nat.ble 48 last && last.ble 57) = false := by
            cases hd : (Nat.ble 48 last && last.ble 57) with
            | false => rfl
            | true => simp [hd] at hfast
          have hne48 : 48 ≠ last := fun heq => by subst heq; simp at hnotdig
          have hf : fixedSufRevB.any (fun sr => isPrefixBytes sr (⟨⟨⟨last, hlast⟩⟩⟩ :: revTail)) = false := by
            have hb48 : (48 : Nat).beq last = false := nat_beq_false_of_ne hne48
            have hb101 : (101 : Nat).beq last = false := nat_beq_false_of_ne hne101
            have hb98 : (98 : Nat).beq last = false := nat_beq_false_of_ne hne98
            change ((48 : Nat).beq last && isPrefixBytes [116, 101, 114, 95] revTail ||
              ((101 : Nat).beq last && isPrefixBytes [117, 103, 111, 108, 105, 112, 101, 95] revTail ||
                ((98 : Nat).beq last && isPrefixBytes [117, 116, 115, 114, 114, 101, 95] revTail ||
                  ((98 : Nat).beq last && isPrefixBytes [117, 116, 115, 104, 120, 101, 95] revTail ||
                    ((98 : Nat).beq last && isPrefixBytes [117, 116, 115, 48, 116, 114, 111, 98, 97, 95] revTail ||
                      false))))) = false
            rw [hb48, hb101, hb98]; rfl
          simp only [hf, Bool.false_eq_true, ↓reduceIte]
          rw [hrevChars, ← hdrop]
          simp [dropDigitsRevB, hnotdig]

private theorem nat_blt_iff_lt_scan (a b : Nat) : a.blt b = true ↔ a < b := by
  simp only [Nat.blt, Nat.ble_eq]; omega

private theorem foldl_add_shift_scan {α : Type} (f : α → Nat) (xs : List α) (init : Nat) :
    xs.foldl (fun acc x => acc + f x) init = init + xs.foldl (fun acc x => acc + f x) 0 := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (init + f x), ih (f x), Nat.add_assoc]

private theorem bsrcRomsOk_mono {r₁ r₂ : List UInt8 → Bool}
    (hr : ∀ d, r₁ d = true → r₂ d = true) :
    ∀ {b : L.BSrc}, bsrcRomsOk r₁ b = true → bsrcRomsOk r₂ b = true
  | .arr _, h => h
  | .rom d, h => hr d h

private theorem exprRomsOk_mono {r₁ r₂ : List UInt8 → Bool}
    (hr : ∀ d, r₁ d = true → r₂ d = true) :
    ∀ {e : L.Expr}, exprRomsOk r₁ e = true → exprRomsOk r₂ e = true
  | .const _, h | .var _, h | .len8 _, h | .len64 _, h | .glob _, h => h
  | .bin _ a b, h | .cmpw _ a b, h | .ld64t _ a b, h | .ld32t _ a b, h | .ld32h _ a b _, h => by
    simp only [exprRomsOk, Bool.and_eq_true] at h ⊢
    exact ⟨exprRomsOk_mono hr h.1, exprRomsOk_mono hr h.2⟩
  | .ld8 _ i, h | .ld64 _ i, h | .len64t _ i, h => exprRomsOk_mono hr (e := i) h
  | .ldc d i, h => by
    simp only [exprRomsOk, Bool.and_eq_true] at h ⊢
    exact ⟨hr d h.1, exprRomsOk_mono hr h.2⟩
  | .ld8x8 b i, h => by
    simp only [exprRomsOk, Bool.and_eq_true] at h ⊢
    exact ⟨bsrcRomsOk_mono hr h.1, exprRomsOk_mono hr h.2⟩

private theorem condRomsOk_mono {r₁ r₂ : List UInt8 → Bool}
    (hr : ∀ d, r₁ d = true → r₂ d = true) :
    ∀ {c : L.Cond}, condRomsOk r₁ c = true → condRomsOk r₂ c = true
  | .cmp _ a b, h => by
    simp only [condRomsOk, Bool.and_eq_true] at h ⊢
    exact ⟨exprRomsOk_mono hr h.1, exprRomsOk_mono hr h.2⟩
  | .and p q, h | .or p q, h => by
    simp only [condRomsOk, Bool.and_eq_true] at h ⊢
    exact ⟨condRomsOk_mono hr h.1, condRomsOk_mono hr h.2⟩
  | .not p, h => condRomsOk_mono hr (c := p) h

private theorem warrRomsOk_mono {r₁ r₂ : List UInt8 → Bool}
    (hr : ∀ d, r₁ d = true → r₂ d = true) :
    ∀ {w : L.WArr}, warrRomsOk r₁ w = true → warrRomsOk r₂ w = true
  | .plain _, h => h
  | .tier _ t, h => exprRomsOk_mono hr (e := t) h

private theorem stmtArgsAndRomsOk_mono {t rt : L.Compiler.NTree} {r₁ r₂ : List UInt8 → Bool}
    (hr : ∀ d, r₁ d = true → r₂ d = true) :
    ∀ {s : L.Stmt}, stmtArgsAndRomsOk t rt r₁ s = true → stmtArgsAndRomsOk t rt r₂ s = true
  | .skip, h | .brk, h => h
  | .abort e, h | .set _ e, h | .gset _ e, h => exprRomsOk_mono hr (e := e) h
  | .st8 _ _ _, h | .st64 _ _ _, h => by
    simp only [stmtArgsAndRomsOk, Bool.and_eq_true] at h ⊢
    exact ⟨exprRomsOk_mono hr h.1, exprRomsOk_mono hr h.2⟩
  | .seq s₁ s₂, h => by
    simp only [stmtArgsAndRomsOk, Bool.and_eq_true] at h ⊢
    exact ⟨stmtArgsAndRomsOk_mono hr h.1, stmtArgsAndRomsOk_mono hr h.2⟩
  | .ite _ s₁ s₂, h => by
    simp only [stmtArgsAndRomsOk, Bool.and_eq_true] at h ⊢
    exact ⟨⟨condRomsOk_mono hr h.1.1, stmtArgsAndRomsOk_mono hr h.1.2⟩, stmtArgsAndRomsOk_mono hr h.2⟩
  | .while _ s, h => by
    simp only [stmtArgsAndRomsOk, Bool.and_eq_true] at h ⊢
    exact ⟨condRomsOk_mono hr h.1, stmtArgsAndRomsOk_mono hr h.2⟩
  | .ret _, h => by
    simp only [stmtArgsAndRomsOk, List.all_eq_true] at h ⊢
    exact fun e he => exprRomsOk_mono hr (h e he)
  | .call _ _ _, h => by
    simp only [stmtArgsAndRomsOk, Bool.and_eq_true, List.all_eq_true] at h ⊢
    exact ⟨h.1, fun e he => exprRomsOk_mono hr (h.2 e he)⟩
  | .st64t _ _ _ _, h | .st32t _ _ _ _, h => by
    simp only [stmtArgsAndRomsOk, Bool.and_eq_true] at h ⊢
    exact ⟨⟨exprRomsOk_mono hr h.1.1, exprRomsOk_mono hr h.1.2⟩, exprRomsOk_mono hr h.2⟩
  | .copy64 _ _ _ _ _, h => by
    simp only [stmtArgsAndRomsOk, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨⟨warrRomsOk_mono hr h.1.1.1.1, exprRomsOk_mono hr h.1.1.1.2⟩,
      warrRomsOk_mono hr h.1.1.2⟩, exprRomsOk_mono hr h.1.2⟩, exprRomsOk_mono hr h.2⟩
  | .copy8w _ _ _ _ _, h => by
    simp only [stmtArgsAndRomsOk, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨⟨warrRomsOk_mono hr h.1.1.1.1, exprRomsOk_mono hr h.1.1.1.2⟩,
      bsrcRomsOk_mono hr h.1.1.2⟩, exprRomsOk_mono hr h.1.2⟩, exprRomsOk_mono hr h.2⟩
  | .scan8 _ _ _ _ c, h => by
    simp only [stmtArgsAndRomsOk, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨bsrcRomsOk_mono hr h.1.1.1, exprRomsOk_mono hr h.1.1.2⟩,
      exprRomsOk_mono hr h.1.2⟩, hr c h.2⟩

private theorem sliceFusedFastGo_sound (xs : List (L.FnName × L.FunDecl)) (acc sumCap : Nat)
    (h : sliceFusedFastGo xs acc sumCap = true) :
    (∀ x ∈ xs, fnFusedOk x = true) ∧
    acc + xs.foldl (fun a x => a + fnBoundAndFrameL x.2) 0 < sumCap := by
  induction xs generalizing acc with
  | nil =>
    simp only [sliceFusedFastGo, List.foldl_nil, Nat.add_zero] at h ⊢
    exact ⟨fun _ hm => False.elim (by cases hm), (nat_blt_iff_lt_scan acc sumCap).mp h⟩
  | cons x xs ih =>
    dsimp only [sliceFusedFastGo] at h
    cases hsafeB : fnBytesSafeFast x.1.toByteArray.data.toList with
    | false => rw [hsafeB] at h; cases h
    | true =>
      rw [hsafeB] at h
      have hsafe : fnCharsSafeFastL x.1.toList = true :=
        fnBytesSafeFast_imp_fnCharsSafeFastL x.1 hsafeB
      cases hscan : stmtScanL checkerLmapLit 2 12 10 L.Checker.checkerProg_wf.tree minRetTreeLit
          (romFastOk allowedRomsWithLenLit) x.2.nlocals false 0 x.2.body with
      | fail => rw [hscan] at h; cases h
      | ok mf mr mt b32 =>
        rw [hscan] at h
        dsimp only at h
        cases hmr : ((minRetTreeLit.find (L.Compiler.bytesCode x.1.toByteArray.data.toList)).getD 1).ble
            (if mf then 1 else if mr == 0 then 100 else mr) with
        | false => simp only [hmr, Bool.false_eq_true, ↓reduceIte] at h
        | true =>
          simp only [hmr, ↓reduceIte] at h
          obtain ⟨har, hfast, hmf, hmrEq, hmt, hb32⟩ := stmtScanL_sound hscan
          have hminRet : fnMinRetL x.2 = (if mf then 1 else if mr == 0 then 100 else mr) := by
            dsimp only [fnMinRetL]
            rw [← hmf, ← hmrEq]
            cases mf <;> cases mr <;> rfl
          have hmrDec : decide ((minRetTreeLit.find (L.Compiler.nameCode x.1)).getD 1 ≤ fnMinRetL x.2) = true := by
            rw [hminRet]
            exact decide_eq_true (Nat.ble_eq.mp hmr)
          have harElem : stmtArgsAndRomsOk L.Checker.checkerProg_wf.tree minRetTreeLit allowedRomsLit.elem x.2.body = true :=
            stmtArgsAndRomsOk_mono (fun _ => romFastOk_imp_elem) har
          have hfn : fnFusedOk x = true := by
            simp only [fnFusedOk, Bool.and_eq_true]
            exact ⟨⟨⟨hmrDec, harElem⟩, hfast⟩, hsafe⟩
          have hbound : fnScanBound x.2 mt b32 = fnBoundAndFrameL x.2 := by
            dsimp only [fnScanBound, fnBoundAndFrameL]
            rw [← hmt, show b32 = (stmtTempsAndBoundL x.2.body).2 by omega]
          rw [hbound] at h
          obtain ⟨hxs, hsum⟩ := ih (acc + fnBoundAndFrameL x.2) h
          refine ⟨fun y hy => ?_, ?_⟩
          · rcases List.mem_cons.mp hy with rfl | hy'
            · exact hfn
            · exact hxs y hy'
          · simp only [List.foldl_cons, Nat.zero_add]
            rw [foldl_add_shift_scan (fun p : L.FnName × L.FunDecl => fnBoundAndFrameL p.2) xs (fnBoundAndFrameL x.2)]
            omega

private theorem combine_prog_single (p : L.Prog) (cap : Nat)
    (h : sliceFusedFastGo p 0 cap = true) :
    (∀ x ∈ p, fnFusedOk x = true) ∧
    p.foldl (fun acc x => acc + fnBoundAndFrameL x.2) 0 < cap := by
  simpa using sliceFusedFastGo_sound p 0 cap h

private theorem checkerProg_fused_combined :
    (∀ x ∈ L.Checker.checkerProg, fnFusedOk x = true) ∧
    L.Checker.checkerProg.foldl (fun acc x => acc + fnBoundAndFrameL x.2) 0 < 3600000 :=
  combine_prog_single L.Checker.checkerProg 3600000 checkerProg_fused_all

private theorem fnFusedOk_unpack {x : L.FnName × L.FunDecl} (h : fnFusedOk x = true) :
    ((minRetTreeLit.find (L.Compiler.nameCode x.1)).getD 1 ≤ fnMinRetL x.2 ∧
     stmtArgsAndRomsOk L.Checker.checkerProg_wf.tree minRetTreeLit allowedRomsLit.elem x.2.body = true) ∧
    fastStmt checkerLmapLit 2 12 10 L.Checker.checkerProg_wf.tree x.2.nlocals false x.2.body = true ∧
    fnCharsSafeFastL x.1.toList = true := by
  simp only [fnFusedOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨⟨h.1.1.1, h.1.1.2⟩, h.1.2, h.2⟩

theorem checkerProg_argsAndRoms_all :
    ∀ x ∈ L.Checker.checkerProg,
      (minRetTreeLit.find (L.Compiler.nameCode x.1)).getD 1 ≤ fnMinRetL x.2 ∧
      stmtArgsAndRomsOk L.Checker.checkerProg_wf.tree minRetTreeLit allowedRomsLit.elem x.2.body = true :=
  fun x hx => (fnFusedOk_unpack (checkerProg_fused_combined.1 x hx)).1

theorem checkerProg_fastStmt_all :
    ∀ x ∈ L.Checker.checkerProg,
      fastStmt checkerLmapLit 2 12 10 L.Checker.checkerProg_wf.tree x.2.nlocals false x.2.body = true :=
  fun x hx => (fnFusedOk_unpack (checkerProg_fused_combined.1 x hx)).2.1

theorem checkerProg_fnCharsSafeFastL_all :
    ∀ x ∈ L.Checker.checkerProg,
      fnCharsSafeFastL x.1.toList = true :=
  fun x hx => (fnFusedOk_unpack (checkerProg_fused_combined.1 x hx)).2.2

theorem checkerProg_fnBoundAndFrameL_sum_lt :
    L.Checker.checkerProg.foldl (fun acc x => acc + fnBoundAndFrameL x.2) 0 < 3800000 :=
  Nat.lt_trans checkerProg_fused_combined.2 (by decide : 3600000 < 3800000)

end ConAgua.RISCV.Bridge
