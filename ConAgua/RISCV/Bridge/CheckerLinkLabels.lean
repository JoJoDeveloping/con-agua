import Lean
import ConAgua.RISCV.Bridge.CheckerProgScan
import ConAgua.RISCV.Bridge.CheckerLinkLabelsSR

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Algebraic Label Distinctness for `checkerChipAsm` (`ConAgua.RISCV.Bridge.CheckerLinkLabels`)

Proves `(lblNames checkerChipAsm).Nodup`.
-/

namespace ConAgua.RISCV.Bridge

open ConAgua.RISCV.RV64
open ConAgua.RISCV.Compiler
open ConAgua.RISCV.Linker
open _root_.L

section FnNameSafetyCheck
open Lean Elab Tactic Meta

private meta def findPrivSub (root : Name) (suffix : String) : MetaM Name := do
  let env ← getEnv
  let some ci := env.find? root | throwError "not found: {root}"
  let some val := ci.value? | throwError "no val: {root}"
  let matches_ := val.getUsedConstants.filter fun n =>
    isPrivateName n && n.toString.endsWith suffix
  let some n := matches_[0]? | throwError "private {suffix} not found in {root}"
  return n

local elab "fnCharsSafeFast_eq_bridge" : tactic => do
  let nFix ← findPrivSub ``fnCharsSafeFast "fixedSufRev"
  let nDyn ← findPrivSub ``fnCharsSafeFast "dynTagRev"
  let nPre ← findPrivSub ``fnCharsSafeFast "isPrefixChars"
  let nDrop ← findPrivSub ``fnCharsSafeFast "dropDigitsRev"
  let listChar := mkApp (mkConst ``List [0]) (mkConst ``Char)
  let hFix ← mkEqRefl (mkConst ``fixedSufRevL)
  let hFixTy ← mkEq (mkConst ``fixedSufRevL) (mkConst nFix)
  let hDyn ← mkEqRefl (mkConst ``dynTagRevL)
  let hDynTy ← mkEq (mkConst ``dynTagRevL) (mkConst nDyn)
  let hPreTy ← withLocalDeclD `p listChar fun p =>
    withLocalDeclD `x listChar fun x => do
      mkForallFVars #[p, x] (← mkEq (mkApp2 (mkConst ``isPrefixCharsL) p x) (mkApp2 (mkConst nPre) p x))
  let hPre ← mkFreshExprMVar hPreTy
  let _ ← hPre.mvarId!.withContext do
    let (#[p, _x], g) ← hPre.mvarId!.introN 2 | throwError "intro"
    let (_, g) ← g.revert #[_x]
    let #[sg0, sg1] ← g.induction p ``List.rec | throwError "ind"
    let (_, g0) ← sg0.mvarId.intro1
    g0.assign (← mkEqRefl (mkConst ``Bool.true))
    let (x2, g1) ← sg1.mvarId.intro1
    let pH := sg1.fields[0]!
    let ih := sg1.fields[2]!
    let #[c0, c1] ← g1.cases x2 | throwError "cases"
    c0.mvarId.assign (← mkEqRefl (mkConst ``Bool.false))
    c1.mvarId.withContext do
      let xH := c1.fields[0]!
      let xT := c1.fields[1]!
      let f ← withLocalDeclD `b (mkConst ``Bool) fun b => do
        let beq ← mkAppM ``BEq.beq #[pH, xH]
        mkLambdaFVars #[b] (mkApp2 (mkConst ``Bool.and) beq b)
      let pf ← mkAppM ``congrArg #[f, mkApp ih xT]
      c1.mvarId.assign pf
  let hDropTy ← withLocalDeclD `xs listChar fun xs =>
    withLocalDeclD `seen (mkConst ``Bool) fun seen => do
      mkForallFVars #[xs, seen] (← mkEq (mkApp2 (mkConst ``dropDigitsRevL) xs seen) (mkApp2 (mkConst nDrop) xs seen))
  let hDrop ← mkFreshExprMVar hDropTy
  let _ ← hDrop.mvarId!.withContext do
    let (#[xs, _seen], g) ← hDrop.mvarId!.introN 2 | throwError "intro"
    let (_, g) ← g.revert #[_seen]
    let #[sg0, sg1] ← g.induction xs ``List.rec | throwError "ind"
    let (s0, g0) ← sg0.mvarId.intro1
    g0.assign (← mkEqRefl (mkApp4 (mkConst ``Prod.mk [0, 0]) listChar (mkConst ``Bool)
      (mkApp (mkConst ``List.nil [0]) (mkConst ``Char)) (mkFVar s0)))
    let (s1, g1) ← sg1.mvarId.intro1
    let cH := sg1.fields[0]!
    let cT := sg1.fields[1]!
    let ih := sg1.fields[2]!
    g1.withContext do
      let pairTy := mkApp2 (mkConst ``Prod [0, 0]) listChar (mkConst ``Bool)
      let cond := mkApp (mkConst ``Char.isDigit) cH
      let prop ← mkEq cond (mkConst ``Bool.true)
      let dec := mkApp2 (mkConst ``instDecidableEqBool) cond (mkConst ``Bool.true)
      let v := mkApp4 (mkConst ``Prod.mk [0, 0]) listChar (mkConst ``Bool)
        (mkApp3 (mkConst ``List.cons [0]) (mkConst ``Char) cH cT) (mkFVar s1)
      let pThen ← withLocalDeclD `h prop fun h => do
        let l1 ← mkAppOptM ``if_pos #[some prop, some dec, some h, some pairTy, some (mkApp2 (mkConst ``dropDigitsRevL) cT (mkConst ``Bool.true)), some v]
        let r1 ← mkAppOptM ``if_pos #[some prop, some dec, some h, some pairTy, some (mkApp2 (mkConst nDrop) cT (mkConst ``Bool.true)), some v]
        let eq ← mkEqTrans l1 (← mkEqTrans (mkApp ih (mkConst ``Bool.true)) (← mkEqSymm r1))
        mkLambdaFVars #[h] eq
      let pElse ← withLocalDeclD `h (mkNot prop) fun h => do
        let l1 ← mkAppOptM ``if_neg #[some prop, some dec, some h, some pairTy, some (mkApp2 (mkConst ``dropDigitsRevL) cT (mkConst ``Bool.true)), some v]
        let r1 ← mkAppOptM ``if_neg #[some prop, some dec, some h, some pairTy, some (mkApp2 (mkConst nDrop) cT (mkConst ``Bool.true)), some v]
        let eq ← mkEqTrans l1 (← mkEqSymm r1)
        mkLambdaFVars #[h] eq
      let pf ← mkAppM ``Or.elim #[mkApp2 (mkConst ``Decidable.em) prop dec, pThen, pElse]
      g1.assign pf
  let mvar ← getMainGoal
  let mvar ← mvar.assert `hFix hFixTy hFix
  let mvar ← mvar.assert `hDyn hDynTy hDyn
  let mvar ← mvar.assert `hPre hPreTy (← instantiateMVars hPre)
  let mvar ← mvar.assert `hDrop hDropTy (← instantiateMVars hDrop)
  replaceMainGoal [mvar]

private theorem fnCharsSafeFastL_eq (cs : List Char) :
    fnCharsSafeFastL cs = fnCharsSafeFast cs := by
  fnCharsSafeFast_eq_bridge
  intro hDrop hPre hDyn hFix
  cases cs with
  | nil => rfl
  | cons c cs =>
    dsimp only [fnCharsSafeFastL, fnCharsSafeFast]
    rw [← hFix, ← hDyn]
    simp only [hPre, hDrop]

theorem checkerProg_fnCharsSafeFast :
    (L.Checker.checkerProg.all (fun p => fnCharsSafeFast p.1.toList)) = true := by
  rw [List.all_eq_true]
  intro x hx
  rw [← fnCharsSafeFastL_eq]
  exact checkerProg_fnCharsSafeFastL_all x hx

end FnNameSafetyCheck

theorem checkerProgMini_fnCharsSafeFast :
    (checkerProgMini.all (fun p => fnCharsSafeFast p.1.toList)) = true :=
  checkerProg_fnCharsSafeFast

theorem fns_lblNames_nodup (tab : Tab) :
    (lblNames (checkerProgMini.flatMap (fun (f, fd) => compileFn tab f fd))).Nodup := by
  rw [lblNames_flatMap]
  have hnd := checkerProgMini_fnNames_nodup
  have hsafe := checkerProgMini_fnCharsSafeFast
  suffices h : ∀ (ps : List (FnName × FunDecl)) (t : Tab),
      (ps.map Prod.fst).Nodup →
      (ps.all (fun p => fnCharsSafeFast p.1.toList)) = true →
      (ps.flatMap (fun p => lblNames (compileFn t p.1 p.2))).Nodup from
    h checkerProgMini tab hnd hsafe
  intro ps t hnd hsafe
  induction ps with
  | nil => simp
  | cons hd rest ih =>
    obtain ⟨f, fd⟩ := hd
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.all_cons, Bool.and_eq_true] at hsafe
    simp only [List.flatMap_cons]
    obtain ⟨hndF, hspF⟩ := compileFn_lbls_spec t f fd
    refine nodup_append_disj hndF (ih hnd.2 hsafe.2) (fun s hs1 hs2 => ?_)
    obtain ⟨suf1, hsuf1, rfl⟩ := hspF s hs1
    rw [List.mem_flatMap] at hs2
    obtain ⟨⟨f', fd'⟩, hmem', hs2'⟩ := hs2
    obtain ⟨_, hspF'⟩ := compileFn_lbls_spec t f' fd'
    obtain ⟨suf2, hsuf2, heq⟩ := hspF' _ hs2'
    have hsf' : fnCharsSafeFast f'.toList = true := by
      rw [List.all_eq_true] at hsafe
      exact hsafe.2 (f', fd') hmem'
    have hfeq := validFnSuffix_suffix_inj hsafe.1 hsf' hsuf1 hsuf2 heq
    subst hfeq
    exact hnd.1 (List.mem_map.mpr ⟨(f, fd'), hmem', rfl⟩)

theorem drvFillConstLoop_lblNames_eq (loopLbl doneLbl : String) (off : Int) (val : BitVec 64)
    (count : Nat) :
    lblNames (drvFillConstLoop loopLbl doneLbl off val count) =
      if (count == 0) = true then [] else [loopLbl, doneLbl] := by
  dsimp only [drvFillConstLoop]
  split
  · rfl
  · simp only [lblNames_append, lblNames_of_allInstrs (addImmOff_allInstrs _ _ _ _),
      lblNames_of_allInstrs (li_allInstrs _ _), List.nil_append]
    rfl

theorem drvFillStrideLoop_lblNames_eq (loopLbl doneLbl : String) (off : Int)
    (initOff stride : BitVec 64) (count : Nat) :
    lblNames (drvFillStrideLoop loopLbl doneLbl off initOff stride count) =
      if (count == 0) = true then [] else [loopLbl, doneLbl] := by
  dsimp only [drvFillStrideLoop]
  split
  · rfl
  · simp only [lblNames_append, lblNames_of_allInstrs (addImmOff_allInstrs _ _ _ _),
      lblNames_of_allInstrs (li_allInstrs _ _), List.nil_append]
    rfl

private theorem drvRomStoresAsm_allInstrs (romBase : Int) (bs : List UInt8) :
    allInstrs (drvRomStoresAsm romBase bs) = true := by
  have hsw : ∀ (r : Reg) (slots : List Nat), allInstrs (slots.map fun (s : Nat) =>
      Asm.sw AbiReg.t0 r (BitVec.ofInt 12 (4 * Int.ofNat s - 2048))) = true := by
    intro r slots
    induction slots with
    | nil => rfl
    | cons _ _ ih =>
      rw [List.map_cons, allInstrs_cons, Bool.and_eq_true]
      exact ⟨rfl, ih⟩
  dsimp only [drvRomStoresAsm]
  refine allInstrs_flatMap fun ⟨ws, ci⟩ _ => ?_
  dsimp only [drvRomChunkAsm]
  rw [allInstrs_append, Bool.and_eq_true]
  refine ⟨addImmOff_allInstrs _ _ _ _, allInstrs_flatMap fun ⟨v, slots⟩ _ => ?_⟩
  dsimp only [drvRomGroupAsm]
  split
  · exact hsw AbiReg.zero slots
  · rw [allInstrs_append, Bool.and_eq_true]
    exact ⟨allInstrs_map_instr _, hsw AbiReg.t1 slots⟩

theorem drvInitSubAsm_lblNames_eq (tab : Tab) :
    lblNames (drvInitSubAsm tab) =
      [drvInitLabel] ++
      (if (tab.nb + tab.nw - tab.nbuf == 0) = true then [] else ["ca_drv_bloop", "ca_drv_bdone"]) ++
      (if (tab.nb - tab.nbuf == 0) = true then [] else ["ca_drv_lbloop", "ca_drv_lbdone"]) ++
      (if (tab.nw == 0) = true then [] else ["ca_drv_lwloop", "ca_drv_lwdone"]) ++
      (if (tab.nb == 0) = true then [] else ["ca_drv_l32bloop", "ca_drv_l32bdone"]) ++
      (if (tab.nw == 0) = true then [] else ["ca_drv_l32wloop", "ca_drv_l32wdone"]) ++
      (if (tab.nxres + tab.ng == 0) = true then [] else ["ca_drv_zloop", "ca_drv_zdone"]) := by
  have hbufB : lblNames (List.flatMap (fun p =>
      storeMemOff .sd AbiReg.gp (if p == 0 then AbiReg.a0 else AbiReg.a2) AbiReg.t0 (tab.dbase p))
      (List.range tab.nbuf)) = [] := by
    rw [lblNames_flatMap, List.flatMap_eq_nil_iff]
    intro _ _; exact lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)
  have hbufL : lblNames (List.flatMap (fun p =>
      storeMemOff .sd AbiReg.gp (if p == 0 then AbiReg.a1 else AbiReg.a3) AbiReg.t0 (tab.dlen p))
      (List.range tab.nbuf)) = [] := by
    rw [lblNames_flatMap, List.flatMap_eq_nil_iff]
    intro _ _; exact lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)
  have hrom : lblNames (drvRomStoresAsm tab.romBase tab.rom) = [] :=
    lblNames_of_allInstrs (drvRomStoresAsm_allInstrs _ _)
  dsimp only [drvInitSubAsm]
  simp only [lblNames_append, hbufB, hbufL, hrom,
    drvFillStrideLoop_lblNames_eq, drvFillConstLoop_lblNames_eq,
    lblNames_of_allInstrs (li_allInstrs _ _),
    List.nil_append, List.append_nil]
  simp [lblNames, Asm.lbl, Asm.add, Asm.sd, Asm.ret, List.append_assoc]

theorem checkerDriverAsm_lblNames_eq (tab : Tab) :
    lblNames (checkerDriverAsm tab) =
      [startLabel, drvDoneLabel, exhaustedLabel, errLabel, abortLabel, retRestoreLabel] ++
      lblNames (drvInitSubAsm tab) := by
  dsimp only [checkerDriverAsm]
  simp only [lblNames_append,
    lblNames_of_allInstrs (li_allInstrs _ _),
    lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
    lblNames_of_allInstrs (addImmOff_allInstrs _ _ _ _),
    lblNames_of_allInstrs (callerSaveAsm_allInstrs _ _),
    lblNames_of_allInstrs (callerRestoreRetAsm_allInstrs _ _),
    List.nil_append, List.append_nil]
  rfl

theorem checkerCmpDriverAsm_lblNames_eq (tab : Tab) :
    lblNames (checkerCmpDriverAsm tab) = [cmpStartLabel] := by
  dsimp only [checkerCmpDriverAsm]
  simp only [lblNames_append,
    lblNames_of_allInstrs (li_allInstrs _ _),
    lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
    lblNames_of_allInstrs (addImmOff_allInstrs _ _ _ _),
    lblNames_of_allInstrs (callerSaveAsm_allInstrs _ _),
    List.nil_append, List.append_nil]
  rfl

theorem checkerDriverAsm_checkerTabMini_lblNames :
    lblNames (checkerDriverAsm checkerTabMini) =
      [startLabel, drvDoneLabel, exhaustedLabel, errLabel, abortLabel, retRestoreLabel,
       drvInitLabel, "ca_drv_bloop", "ca_drv_bdone", "ca_drv_lwloop", "ca_drv_lwdone",
       "ca_drv_l32bloop", "ca_drv_l32bdone", "ca_drv_l32wloop", "ca_drv_l32wdone",
       "ca_drv_zloop", "ca_drv_zdone"] := by
  rw [checkerDriverAsm_lblNames_eq, drvInitSubAsm_lblNames_eq]
  have h1 : (checkerTabMini.nb + checkerTabMini.nw - checkerTabMini.nbuf == 0) = false := by decide
  have h2 : (checkerTabMini.nb - checkerTabMini.nbuf == 0) = true := by decide
  have h3 : (checkerTabMini.nw == 0) = false := by decide
  have h4 : (checkerTabMini.nb == 0) = false := by decide
  have h5 : (checkerTabMini.nxres + checkerTabMini.ng == 0) = false := by decide
  simp [h1, h2, h3, h4, h5]

theorem list_perm_flatMap {α β : Type} {xs ys : List α} (h : xs.Perm ys)
    (f : α → List β) : (xs.flatMap f).Perm (ys.flatMap f) := by
  induction h with
  | nil => exact List.Perm.nil
  | cons x _ ih => simpa only [List.flatMap_cons] using ih.append_left (f x)
  | swap x y l =>
    simp only [List.flatMap_cons, ← List.append_assoc]
    exact (List.perm_append_comm (l₁ := f y) (l₂ := f x)).append_right _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- **`checkerChipAsm_lblNames_nodup`:** Every label in the unified `checkerChipAsm` is unique. -/
theorem checkerChipAsm_lblNames_nodup :
    (lblNames checkerChipAsm).Nodup := by
  dsimp only [checkerChipAsm]
  rw [lblNames_append, lblNames_append]
  have hdrvAll : lblNames (checkerDriverAsm checkerTabMini) ++ lblNames (checkerCmpDriverAsm checkerTabMini) =
      [startLabel, drvDoneLabel, exhaustedLabel, errLabel, abortLabel, retRestoreLabel,
       drvInitLabel, "ca_drv_bloop", "ca_drv_bdone", "ca_drv_lwloop", "ca_drv_lwdone",
       "ca_drv_l32bloop", "ca_drv_l32bdone", "ca_drv_l32wloop", "ca_drv_l32wdone",
       "ca_drv_zloop", "ca_drv_zdone", cmpStartLabel] := by
    rw [checkerDriverAsm_checkerTabMini_lblNames, checkerCmpDriverAsm_lblNames_eq]
    rfl
  have hndDrv : (lblNames (checkerDriverAsm checkerTabMini) ++ lblNames (checkerCmpDriverAsm checkerTabMini)).Nodup := by
    rw [hdrvAll]; decide
  have hpfxDrv : ∀ s ∈ lblNames (checkerDriverAsm checkerTabMini) ++ lblNames (checkerCmpDriverAsm checkerTabMini),
      s.toList.take 3 = ['c', 'a', '_'] := by
    intro s hs; rw [hdrvAll] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hpermLbl : (lblNames ((orderProgFns checkerProgMini).flatMap fun (f, fd) => compileFn checkerTabMini f fd)).Perm
      (lblNames (checkerProgMini.flatMap fun (f, fd) => compileFn checkerTabMini f fd)) := by
    rw [lblNames_flatMap, lblNames_flatMap]
    exact list_perm_flatMap (orderProgFns_perm checkerProgMini) (fun (f, fd) => lblNames (compileFn checkerTabMini f fd))
  have hndFns : (lblNames ((orderProgFns checkerProgMini).flatMap fun (f, fd) => compileFn checkerTabMini f fd)).Nodup :=
    hpermLbl.nodup_iff.mpr (fns_lblNames_nodup checkerTabMini)
  have hpfxFns : ∀ s ∈ lblNames ((orderProgFns checkerProgMini).flatMap fun (f, fd) => compileFn checkerTabMini f fd),
      s.toList.take 3 = ['f', 'n', '_'] := by
    intro s hs
    rw [lblNames_flatMap, List.mem_flatMap] at hs
    obtain ⟨⟨f, fd⟩, _, hs'⟩ := hs
    obtain ⟨_, hsp⟩ := compileFn_lbls_spec checkerTabMini f fd
    obtain ⟨suff, _, rfl⟩ := hsp s hs'
    simp [fnLabel, String.toList_append]
  refine nodup_append_disj hndDrv hndFns (fun s h1 h2 => ?_)
  have p1 := hpfxDrv s h1
  have p2 := hpfxFns s h2
  rw [p1] at p2; simp at p2

end ConAgua.RISCV.Bridge
