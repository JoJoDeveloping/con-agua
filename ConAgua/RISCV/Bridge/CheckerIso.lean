import ConAgua.Final.DrvTwin
import ConAgua.Checker.ProgIRef
import ConAgua.RISCV.Bridge.CheckerDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Checker Program & Driver Verdict Bridge (`ConAgua` → `ConAgua.RISCV.Bridge`)

Connects `CheckerDefs` constants and driver memory predicates directly to
`ConAgua.Final.{checkerProg_drv_twinAccepts, checkerProg_drv_model, checkerProg_drv_no_False}`
and `ConAgua.Final.{checkerProg_cmpSeq_twinAccepts, checkerProg_cmpSeq_model, checkerProg_cmpSeq_no_False}`
over `L.run` (no `MiniL` duplication or `SyntaxIso` transport layer).

Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

namespace ConAgua.RISCV.Bridge

/-! ## 1. Checker Images & Constant Equalities -/

abbrev checkerProgIMini : L.Prog := L.Checker.checkerProgI

theorem acceptWord_eq : acceptWord = ConAgua.Final.ACCEPT := rfl
theorem inlineSlack_eq : inlineSlack = L.Compiler.abiInl := rfl
theorem hdrHw_eq : hdrHw = L.Arena.hdrHw := rfl
theorem abiFuel_eq : abiFuel = L.Compiler.abiFuel := rfl

abbrev sixArrMini (g : Nat) : L.TieredArray := L.Arena.sixArr g
abbrev eixArrMini (g : Nat) : L.TieredArray := L.Arena.eixArr g
abbrev stxArrMini (g : Nat) : L.TieredArray := L.Arena.stxArr g
abbrev tixArrMini (g : Nat) : L.TieredArray := L.Arena.tixArr g

abbrev phaseBSMini (s : L.TieredArray) : Bool := L.Checker.phaseBS s

def InputsOKMini (b pb : ByteArray) (sz : L.TieredArray → Nat) : Prop :=
  System.Platform.numBits = 64 ∧
    b.size < 2 ^ 63 ∧
    pb.size < 2 ^ 63 ∧
    ∀ s : L.TieredArray, sz s < 2 ^ 64

def loadMemMini (b pb : ByteArray) (sz : L.TieredArray → Nat)
    (mode : L.Word) : L.Mem :=
  { bytes := fun a => if a = inArr then b.data else if a = pbArr then pb.data else #[]
    words := fun s => Array.replicate (sz s) 0
    glob := fun g => if g = modeGVar then mode else 0 }

theorem loadMemMini_eq_loadMemM (b pb : ByteArray)
    (sz : L.TieredArray → Nat) (mode : L.Word) :
    loadMemMini b pb sz mode = L.Checker.loadMemM b pb sz mode := by
  rfl

theorem inputsOK_of_mini {b pb : ByteArray} {sz : L.TieredArray → Nat}
    (hin : InputsOKMini b pb sz) :
    L.Checker.InputsOK b pb sz :=
  ⟨hin.1, hin.2.1, hin.2.2.1, hin.2.2.2⟩

/-! ## 2. `checkerProgI_refines` Wrappers -/

theorem checkerProgIMini_lookup (f : L.FnName) (fd : L.FunDecl)
    (h : checkerProgMini.lookup f = some fd) :
    ∃ fd', checkerProgIMini.lookup f = some fd' ∧ fd'.nparams = fd.nparams :=
  L.Checker.checkerProgI_refines.lookup f fd h

theorem checkerProgIMini_refines_run (N : Nat) (f : L.FnName)
    (vs : List L.Word) (m : L.Mem)
    (r : Except L.Err (List L.Word × L.Mem))
    (hrun : L.run checkerProgIMini N f vs m = r)
    (hne : r ≠ .error .outOfFuel) :
    L.run checkerProgMini (N + inlineSlack) f vs m = r :=
  L.Checker.checkerProgI_refines.run N f vs m r hrun hne

theorem checkerProgIMini_refines_ok {N : Nat} {f : L.FnName}
    {vs : List L.Word} {m m' : L.Mem}
    {rs : List L.Word}
    (hrun : L.run checkerProgIMini N f vs m = .ok (rs, m')) :
    L.run checkerProgMini (N + inlineSlack) f vs m = .ok (rs, m') :=
  checkerProgIMini_refines_run N f vs m (.ok (rs, m')) hrun (by simp)

/-! ## 3. `DrvTwin` Theorems on `checkerProgMini` -/

theorem checkerProgMini_drv_twinAccepts (b pb : ByteArray)
    (sz : L.TieredArray → Nat) (hin : InputsOKMini b pb sz)
    (N₁ : Nat) (hN₁ : N₁ < 2 ^ 62) (rs₁ : List L.Word) (m₁ : L.Mem)
    (h₁ : L.run checkerProgMini N₁ "check" [] (loadMemMini b pb sz 3) = .ok (rs₁, m₁))
    (hge : 9223372036854775808 ≤ UInt64.toNat (rs₁.headD 0))
    (N₂ : Nat) (hN₂ : N₂ ≤ 2 ^ 62) (w : L.Mem)
    (rs₂ : List L.Word) (m₂ : L.Mem)
    (hw : ∀ a : L.TieredArray, phaseBSMini a = true → w.words a = m₁.words a)
    (hmode : w.glob modeGVar = 2)
    (hlo : w.glob ploGVar = 0)
    (hhi : w.glob phiGVar = rs₁.headD 0 - 9223372036854775808)
    (hctlf : (w.words (.t0 ctlfArr)).size = 0)
    (h₂ : L.run checkerProgMini N₂ "check" [] w = .ok (rs₂, m₂))
    (hacc : rs₂.headD 0 = acceptWord) :
    ConAgua.Final.TwinAccepts [b] :=
  ConAgua.Final.checkerProg_drv_twinAccepts b pb sz (inputsOK_of_mini hin) N₁ hN₁ rs₁ m₁ h₁ hge
    N₂ hN₂ w rs₂ m₂ hw hmode hlo hhi hctlf h₂ (hacc.trans acceptWord_eq)

theorem checkerProgMini_drv_model.{w_u} (V : Type w_u) [ConLeche.SetTheory V]
    (b pb : ByteArray) (sz : L.TieredArray → Nat) (hin : InputsOKMini b pb sz)
    (N₁ : Nat) (hN₁ : N₁ < 2 ^ 62) (rs₁ : List L.Word) (m₁ : L.Mem)
    (h₁ : L.run checkerProgMini N₁ "check" [] (loadMemMini b pb sz 3) = .ok (rs₁, m₁))
    (hge : 9223372036854775808 ≤ UInt64.toNat (rs₁.headD 0))
    (N₂ : Nat) (hN₂ : N₂ ≤ 2 ^ 62) (w : L.Mem)
    (rs₂ : List L.Word) (m₂ : L.Mem)
    (hw : ∀ a : L.TieredArray, phaseBSMini a = true → w.words a = m₁.words a)
    (hmode : w.glob modeGVar = 2)
    (hlo : w.glob ploGVar = 0)
    (hhi : w.glob phiGVar = rs₁.headD 0 - 9223372036854775808)
    (hctlf : (w.words (.t0 ctlfArr)).size = 0)
    (h₂ : L.run checkerProgMini N₂ "check" [] w = .ok (rs₂, m₂))
    (hacc : rs₂.headD 0 = acceptWord) :
    ∃ pins preC rc F env,
      ConLeche.Frontend.parseChunks [b] = Except.ok rc ∧
        ConLeche.checkDeclsPure ConLeche.CheckMode.verified
          (ConLeche.fueledOps ConLeche.CheckMode.verified F) pins
          (ConLeche.Frontend.preparePrelude preC rc.decls).toList = Except.ok env ∧
          Nonempty (ConLeche.Model V env) :=
  ConAgua.Final.checkerProg_drv_model V b pb sz (inputsOK_of_mini hin) N₁ hN₁ rs₁ m₁ h₁ hge
    N₂ hN₂ w rs₂ m₂ hw hmode hlo hhi hctlf h₂ (hacc.trans acceptWord_eq)

theorem checkerProgMini_drv_no_False.{w_u} (V : Type w_u) [ConLeche.SetTheory V]
    (b pb : ByteArray) (sz : L.TieredArray → Nat) (hin : InputsOKMini b pb sz)
    (hfalse : ConLeche.jsonWithTheoremFalse [b])
    (N₁ : Nat) (hN₁ : N₁ < 2 ^ 62) (rs₁ : List L.Word) (m₁ : L.Mem)
    (h₁ : L.run checkerProgMini N₁ "check" [] (loadMemMini b pb sz 3) = .ok (rs₁, m₁))
    (hge : 9223372036854775808 ≤ UInt64.toNat (rs₁.headD 0))
    (N₂ : Nat) (hN₂ : N₂ ≤ 2 ^ 62) (w : L.Mem)
    (rs₂ : List L.Word) (m₂ : L.Mem)
    (hw : ∀ a : L.TieredArray, phaseBSMini a = true → w.words a = m₁.words a)
    (hmode : w.glob modeGVar = 2)
    (hlo : w.glob ploGVar = 0)
    (hhi : w.glob phiGVar = rs₁.headD 0 - 9223372036854775808)
    (hctlf : (w.words (.t0 ctlfArr)).size = 0)
    (h₂ : L.run checkerProgMini N₂ "check" [] w = .ok (rs₂, m₂))
    (hacc : rs₂.headD 0 = acceptWord) :
    False :=
  ConAgua.Final.checkerProg_drv_no_False V b pb sz (inputsOK_of_mini hin) hfalse N₁ hN₁ rs₁ m₁ h₁
    hge N₂ hN₂ w rs₂ m₂ hw hmode hlo hhi hctlf h₂ (hacc.trans acceptWord_eq)

/-! ## 4. `DrvTwin` Theorems on `checkerProgIMini` (via `checkerProgI_refines`) -/

theorem checkerProgIMini_drv_twinAccepts (b pb : ByteArray)
    (sz : L.TieredArray → Nat) (hin : InputsOKMini b pb sz)
    (N₁ : Nat) (hN₁ : N₁ + inlineSlack < 2 ^ 62)
    (rs₁ : List L.Word) (m₁ : L.Mem)
    (h₁ : L.run checkerProgIMini N₁ "check" [] (loadMemMini b pb sz 3) = .ok (rs₁, m₁))
    (hge : 9223372036854775808 ≤ UInt64.toNat (rs₁.headD 0))
    (N₂ : Nat) (hN₂ : N₂ + inlineSlack ≤ 2 ^ 62) (w : L.Mem)
    (rs₂ : List L.Word) (m₂ : L.Mem)
    (hw : ∀ a : L.TieredArray, phaseBSMini a = true → w.words a = m₁.words a)
    (hmode : w.glob modeGVar = 2)
    (hlo : w.glob ploGVar = 0)
    (hhi : w.glob phiGVar = rs₁.headD 0 - 9223372036854775808)
    (hctlf : (w.words (.t0 ctlfArr)).size = 0)
    (h₂ : L.run checkerProgIMini N₂ "check" [] w = .ok (rs₂, m₂))
    (hacc : rs₂.headD 0 = acceptWord) :
    ConAgua.Final.TwinAccepts [b] :=
  checkerProgMini_drv_twinAccepts b pb sz hin (N₁ + inlineSlack) hN₁ rs₁ m₁
    (checkerProgIMini_refines_ok h₁) hge (N₂ + inlineSlack) hN₂ w rs₂ m₂
    hw hmode hlo hhi hctlf (checkerProgIMini_refines_ok h₂) hacc

theorem checkerProgIMini_drv_model.{w_u} (V : Type w_u) [ConLeche.SetTheory V]
    (b pb : ByteArray) (sz : L.TieredArray → Nat) (hin : InputsOKMini b pb sz)
    (N₁ : Nat) (hN₁ : N₁ + inlineSlack < 2 ^ 62)
    (rs₁ : List L.Word) (m₁ : L.Mem)
    (h₁ : L.run checkerProgIMini N₁ "check" [] (loadMemMini b pb sz 3) = .ok (rs₁, m₁))
    (hge : 9223372036854775808 ≤ UInt64.toNat (rs₁.headD 0))
    (N₂ : Nat) (hN₂ : N₂ + inlineSlack ≤ 2 ^ 62) (w : L.Mem)
    (rs₂ : List L.Word) (m₂ : L.Mem)
    (hw : ∀ a : L.TieredArray, phaseBSMini a = true → w.words a = m₁.words a)
    (hmode : w.glob modeGVar = 2)
    (hlo : w.glob ploGVar = 0)
    (hhi : w.glob phiGVar = rs₁.headD 0 - 9223372036854775808)
    (hctlf : (w.words (.t0 ctlfArr)).size = 0)
    (h₂ : L.run checkerProgIMini N₂ "check" [] w = .ok (rs₂, m₂))
    (hacc : rs₂.headD 0 = acceptWord) :
    ∃ pins preC rc F env,
      ConLeche.Frontend.parseChunks [b] = Except.ok rc ∧
        ConLeche.checkDeclsPure ConLeche.CheckMode.verified
          (ConLeche.fueledOps ConLeche.CheckMode.verified F) pins
          (ConLeche.Frontend.preparePrelude preC rc.decls).toList = Except.ok env ∧
          Nonempty (ConLeche.Model V env) :=
  checkerProgMini_drv_model V b pb sz hin (N₁ + inlineSlack) hN₁ rs₁ m₁
    (checkerProgIMini_refines_ok h₁) hge (N₂ + inlineSlack) hN₂ w rs₂ m₂
    hw hmode hlo hhi hctlf (checkerProgIMini_refines_ok h₂) hacc

theorem checkerProgIMini_drv_no_False.{w_u} (V : Type w_u) [ConLeche.SetTheory V]
    (b pb : ByteArray) (sz : L.TieredArray → Nat) (hin : InputsOKMini b pb sz)
    (hfalse : ConLeche.jsonWithTheoremFalse [b])
    (N₁ : Nat) (hN₁ : N₁ + inlineSlack < 2 ^ 62)
    (rs₁ : List L.Word) (m₁ : L.Mem)
    (h₁ : L.run checkerProgIMini N₁ "check" [] (loadMemMini b pb sz 3) = .ok (rs₁, m₁))
    (hge : 9223372036854775808 ≤ UInt64.toNat (rs₁.headD 0))
    (N₂ : Nat) (hN₂ : N₂ + inlineSlack ≤ 2 ^ 62) (w : L.Mem)
    (rs₂ : List L.Word) (m₂ : L.Mem)
    (hw : ∀ a : L.TieredArray, phaseBSMini a = true → w.words a = m₁.words a)
    (hmode : w.glob modeGVar = 2)
    (hlo : w.glob ploGVar = 0)
    (hhi : w.glob phiGVar = rs₁.headD 0 - 9223372036854775808)
    (hctlf : (w.words (.t0 ctlfArr)).size = 0)
    (h₂ : L.run checkerProgIMini N₂ "check" [] w = .ok (rs₂, m₂))
    (hacc : rs₂.headD 0 = acceptWord) :
    False :=
  checkerProgMini_drv_no_False V b pb sz hin hfalse (N₁ + inlineSlack) hN₁ rs₁ m₁
    (checkerProgIMini_refines_ok h₁) hge (N₂ + inlineSlack) hN₂ w rs₂ m₂
    hw hmode hlo hhi hctlf (checkerProgIMini_refines_ok h₂) hacc

/-- info: 'ConAgua.RISCV.Bridge.checkerProgIMini_refines_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgIMini_refines_run

/-- info: 'ConAgua.RISCV.Bridge.checkerProgMini_drv_twinAccepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgMini_drv_twinAccepts

/-- info: 'ConAgua.RISCV.Bridge.checkerProgMini_drv_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgMini_drv_model

/-- info: 'ConAgua.RISCV.Bridge.checkerProgMini_drv_no_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgMini_drv_no_False

/-- info: 'ConAgua.RISCV.Bridge.checkerProgIMini_drv_twinAccepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgIMini_drv_twinAccepts

/-- info: 'ConAgua.RISCV.Bridge.checkerProgIMini_drv_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgIMini_drv_model

/-- info: 'ConAgua.RISCV.Bridge.checkerProgIMini_drv_no_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgIMini_drv_no_False

/-! ## 5. `CmpSeq` Theorems on `checkerProgMini` and `checkerProgIMini` -/

def cmpInMini (m : L.Mem) (bs : ByteArray) : L.Mem :=
  { m with bytes := fun a => if a = inArr then bs.data else m.bytes a }

def seqMem0Mini (m : L.Mem) (out hdrf ctlf : L.ArrId) (hw : Nat) : L.Mem where
  bytes _ := #[]
  words s :=
    if s = .t0 out ∨ s = .t0 ctlf then #[]
    else if s = .t0 hdrf then (m.words (.t0 out)).extract 0 hw
    else m.words s
  glob := m.glob

def seqNextMini (M : L.Mem) (mode plo phi : L.GVar)
    (w lo hi : L.Word) : L.Mem :=
  ((M.setG plo lo).setG phi hi).setG mode w

def seqMemWMini (m : L.Mem) (mode plo phi : L.GVar)
    (out hdrf ctlf : L.ArrId) (hw : Nat) (w lo hi : L.Word) : L.Mem :=
  seqNextMini (seqMem0Mini m out hdrf ctlf hw) mode plo phi w lo hi

abbrev cmpRunMini (fuel : Nat) (p : L.Prog) (m : L.Mem) :
    Except L.Err (List L.Word × L.Mem) :=
  L.run p fuel "check" [] m

def cmpM4SzMini (sz : L.TieredArray → Nat) (bC pb : ByteArray) : L.Mem :=
  loadMemMini bC pb sz 4

def cmpM5Mini (m4 : L.Mem) (bS : ByteArray) : L.Mem :=
  (cmpInMini m4 bS).setG modeGVar 5

def CmpFront45SzMini (sz : L.TieredArray → Nat) (fuel : Nat)
    (p : L.Prog) (bC bS pb : ByteArray)
    (rs5 : List L.Word) (m5 : L.Mem) : Prop :=
  bC.size < 2 ^ 63 ∧ pb.size < 2 ^ 63 ∧ bS.size < 2 ^ 63 ∧
  ∃ rs4 m4, cmpRunMini fuel p (cmpM4SzMini sz bC pb) = .ok (rs4, m4) ∧
    2 ^ 63 ≤ (rs4.getD 0 0).toNat ∧
    cmpRunMini fuel p (cmpM5Mini m4 bS) = .ok (rs5, m5) ∧
    2 ^ 63 ≤ (rs5.getD 0 0).toNat

def CmpFrontAcc45SzMini (sz : L.TieredArray → Nat) (fuel : Nat)
    (p : L.Prog) (bC bS pb : ByteArray) : Prop :=
  bC.size < 2 ^ 63 ∧ pb.size < 2 ^ 63 ∧
  ∃ rs4 m4, cmpRunMini fuel p (cmpM4SzMini sz bC pb) = .ok (rs4, m4) ∧
    (rs4.getD 0 0 = acceptWord ∨ (2 ^ 63 ≤ (rs4.getD 0 0).toNat ∧ bS.size < 2 ^ 63 ∧
      ∃ rs5 m5, cmpRunMini fuel p (cmpM5Mini m4 bS) = .ok (rs5, m5) ∧ rs5.getD 0 0 = acceptWord))

def CmpAccSSzMini (sz : L.TieredArray → Nat) (fuel : Nat)
    (p : L.Prog) (bC bS pb : ByteArray) : Prop :=
  CmpFrontAcc45SzMini sz fuel p bC bS pb ∨
  ∃ rs5 m5, CmpFront45SzMini sz fuel p bC bS pb rs5 m5 ∧
    ∃ rs6 m6, cmpRunMini fuel p (m5.setG modeGVar 6) = .ok (rs6, m6) ∧
    (rs6.getD 0 0 = acceptWord ∨ (2 ^ 63 ≤ (rs6.getD 0 0).toNat ∧
      ∃ rs8 m8, cmpRunMini fuel p (seqMemWMini m6 modeGVar ploGVar phiGVar outArr hdrfArr ctlfArr hdrHw
          8 0 (rs5.getD 0 0 - 9223372036854775808)) = .ok (rs8, m8) ∧
        rs8.getD 0 0 = acceptWord ∧
      ∃ rs9 m9, cmpRunMini fuel p (seqNextMini m8 modeGVar ploGVar phiGVar
          9 0 (rs6.getD 0 0 - 9223372036854775808)) = .ok (rs9, m9) ∧
        rs9.getD 0 0 = acceptWord))

private theorem L_run_mono {p : L.Prog} {n n' : Nat} (hle : n ≤ n')
    {f : L.FnName} {vs : List L.Word} {m m' : L.Mem} {rs : List L.Word}
    (h : L.run p n f vs m = .ok (rs, m')) :
    L.run p n' f vs m = .ok (rs, m') := by
  unfold L.run at h ⊢
  cases hinv : (L.invoke p (L.exec p n) f vs).run { mem := m, loc := L.Locals.init [] } with
  | error e => simp [hinv, Except.map] at h
  | ok pair =>
    rw [hinv] at h
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rw [L.invoke_mono (L.exec_le p hle) hinv]
    rfl

private theorem cmpRun_of_mini_le {fuel : Nat} (hf : fuel ≤ abiFuel)
    {m m' : L.Mem} {rs : List L.Word}
    (h : cmpRunMini fuel checkerProgMini m = .ok (rs, m')) :
    ConAgua.Final.cmpRun L.Checker.checkerProg m = .ok (rs, m') :=
  L_run_mono hf h

private theorem seqMem0Mini_eq (m : L.Mem) (out hdrf ctlf : L.ArrId) (hw : Nat) :
    seqMem0Mini m out hdrf ctlf hw = ConAgua.Final.seqMem0 m out hdrf ctlf hw := rfl

private theorem seqNextMini_eq (M : L.Mem) (w lo hi : L.Word) :
    seqNextMini M modeGVar ploGVar phiGVar w lo hi =
      ConAgua.Final.seqNext M L.Arena.MODE L.Arena.PLO L.Arena.PHI w lo hi := rfl

private theorem seqMemWMini_eq (m : L.Mem) (w lo hi : L.Word) :
    seqMemWMini m modeGVar ploGVar phiGVar outArr hdrfArr ctlfArr hdrHw w lo hi =
      ConAgua.Final.seqMemW m L.Arena.MODE L.Arena.PLO L.Arena.PHI
        L.Arena.OUT L.Arena.HDRF L.Arena.CTLF L.Arena.hdrHw w lo hi := rfl

private theorem cmpAccSSz_of_mini (sz : L.TieredArray → Nat)
    {fuel : Nat} (hf : fuel ≤ abiFuel) {bC bS pb : ByteArray}
    (h : CmpAccSSzMini sz fuel checkerProgMini bC bS pb) :
    ConAgua.Final.CmpAccSSz sz L.Checker.checkerProg
      L.Arena.MODE L.Arena.PLO L.Arena.PHI L.Arena.OUT L.Arena.HDRF L.Arena.CTLF L.Arena.hdrHw
      bC bS pb := by
  rcases h with ⟨hbC, hpb, rs4, m4, h4, hor⟩ | ⟨rs5, m5, ⟨hbC, hpb, hbS, rs4, m4, h4, hge4, h5, hge5⟩, rs6, m6, h6, hor⟩
  · left
    refine ⟨hbC, hpb, rs4, m4, cmpRun_of_mini_le hf h4, ?_⟩
    rcases hor with hacc | ⟨hge4, hbS, rs5, m5, h5, hacc⟩
    · exact Or.inl (hacc.trans acceptWord_eq)
    · exact Or.inr ⟨hge4, hbS, rs5, m5, cmpRun_of_mini_le hf h5, hacc.trans acceptWord_eq⟩
  · right
    refine ⟨rs5, m5, ⟨hbC, hpb, hbS, rs4, m4, cmpRun_of_mini_le hf h4, hge4,
        cmpRun_of_mini_le hf h5, hge5⟩,
      rs6, m6, cmpRun_of_mini_le hf h6, ?_⟩
    rcases hor with hacc | ⟨hge6, rs8, m8, h8, hacc8, rs9, m9, h9, hacc9⟩
    · exact Or.inl (hacc.trans acceptWord_eq)
    · exact Or.inr ⟨hge6, rs8, m8, by simpa only [seqMemWMini_eq] using cmpRun_of_mini_le hf h8,
        hacc8.trans acceptWord_eq, rs9, m9,
        by simpa only [seqNextMini_eq] using cmpRun_of_mini_le hf h9,
        hacc9.trans acceptWord_eq⟩

private theorem cmpAccSSzMini_of_inline (sz : L.TieredArray → Nat)
    {fuel : Nat} {bC bS pb : ByteArray}
    (h : CmpAccSSzMini sz fuel checkerProgIMini bC bS pb) :
    CmpAccSSzMini sz (fuel + inlineSlack) checkerProgMini bC bS pb := by
  rcases h with ⟨hbC, hpb, rs4, m4, h4, hor⟩ | ⟨rs5, m5, ⟨hbC, hpb, hbS, rs4, m4, h4, hge4, h5, hge5⟩, rs6, m6, h6, hor⟩
  · left
    refine ⟨hbC, hpb, rs4, m4, checkerProgIMini_refines_ok h4, ?_⟩
    rcases hor with hacc | ⟨hge4, hbS, rs5, m5, h5, hacc⟩
    · exact Or.inl hacc
    · exact Or.inr ⟨hge4, hbS, rs5, m5, checkerProgIMini_refines_ok h5, hacc⟩
  · right
    refine ⟨rs5, m5, ⟨hbC, hpb, hbS, rs4, m4, checkerProgIMini_refines_ok h4, hge4,
        checkerProgIMini_refines_ok h5, hge5⟩,
      rs6, m6, checkerProgIMini_refines_ok h6, ?_⟩
    rcases hor with hacc | ⟨hge6, rs8, m8, h8, hacc8, rs9, m9, h9, hacc9⟩
    · exact Or.inl hacc
    · exact Or.inr ⟨hge6, rs8, m8, checkerProgIMini_refines_ok h8, hacc8,
        rs9, m9, checkerProgIMini_refines_ok h9, hacc9⟩

theorem checkerProgMini_cmpSeq_twinAccepts (sz : L.TieredArray → Nat)
    (hsz : ∀ s, sz s < 2 ^ 64)
    (hsz6 : ∀ g ≤ 2, sz (sixArrMini g) = sz (eixArrMini g) ∧ sz (stxArrMini g) = sz (tixArrMini g))
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    {fuel : Nat} (hf : fuel ≤ abiFuel)
    (h : CmpAccSSzMini sz fuel checkerProgMini bC bS pb) :
    ConAgua.Final.TwinComparesAccepts bC bS :=
  ConAgua.Final.checkerProg_cmpSeq_twinAccepts sz hsz hsz6 bC bS pb h64 (cmpAccSSz_of_mini sz hf h)

theorem checkerProgMini_cmpSeq_model.{w_u} (V : Type w_u) [ConLeche.SetTheory V]
    (sz : L.TieredArray → Nat) (hsz : ∀ s, sz s < 2 ^ 64)
    (hsz6 : ∀ g ≤ 2, sz (sixArrMini g) = sz (eixArrMini g) ∧ sz (stxArrMini g) = sz (tixArrMini g))
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    {fuel : Nat} (hf : fuel ≤ abiFuel)
    (h : CmpAccSSzMini sz fuel checkerProgMini bC bS pb) :
    ∃ (rcC : ConLeche.Frontend.ParseResultD) (preC : ConLeche.Frontend.PreludeIx),
      ConLeche.Frontend.parseChunks [bC] = .ok rcC ∧
      Nonempty (ConLeche.Model V (ConLeche.streamEnv
        ((ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map ConLeche.Cached.sideRecord))) :=
  ConAgua.Final.checkerProg_cmpSeq_model V sz hsz hsz6 bC bS pb h64 (cmpAccSSz_of_mini sz hf h)

theorem checkerProgMini_cmpSeq_no_False.{w_u} (V : Type w_u) [ConLeche.SetTheory V]
    (sz : L.TieredArray → Nat) (hsz : ∀ s, sz s < 2 ^ 64)
    (hsz6 : ∀ g ≤ 2, sz (sixArrMini g) = sz (eixArrMini g) ∧ sz (stxArrMini g) = sz (tixArrMini g))
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (hfalse : ConLeche.jsonWithTheoremFalse [bC])
    {fuel : Nat} (hf : fuel ≤ abiFuel)
    (h : CmpAccSSzMini sz fuel checkerProgMini bC bS pb) :
    False :=
  ConAgua.Final.checkerProg_cmpSeq_no_False V sz hsz hsz6 bC bS pb h64 hfalse
    (cmpAccSSz_of_mini sz hf h)

theorem checkerProgIMini_cmpSeq_twinAccepts (sz : L.TieredArray → Nat)
    (hsz : ∀ s, sz s < 2 ^ 64)
    (hsz6 : ∀ g ≤ 2, sz (sixArrMini g) = sz (eixArrMini g) ∧ sz (stxArrMini g) = sz (tixArrMini g))
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    {fuel : Nat} (hf : fuel + inlineSlack ≤ abiFuel)
    (h : CmpAccSSzMini sz fuel checkerProgIMini bC bS pb) :
    ConAgua.Final.TwinComparesAccepts bC bS :=
  checkerProgMini_cmpSeq_twinAccepts sz hsz hsz6 bC bS pb h64 hf (cmpAccSSzMini_of_inline sz h)

theorem checkerProgIMini_cmpSeq_model.{w_u} (V : Type w_u) [ConLeche.SetTheory V]
    (sz : L.TieredArray → Nat) (hsz : ∀ s, sz s < 2 ^ 64)
    (hsz6 : ∀ g ≤ 2, sz (sixArrMini g) = sz (eixArrMini g) ∧ sz (stxArrMini g) = sz (tixArrMini g))
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    {fuel : Nat} (hf : fuel + inlineSlack ≤ abiFuel)
    (h : CmpAccSSzMini sz fuel checkerProgIMini bC bS pb) :
    ∃ (rcC : ConLeche.Frontend.ParseResultD) (preC : ConLeche.Frontend.PreludeIx),
      ConLeche.Frontend.parseChunks [bC] = .ok rcC ∧
      Nonempty (ConLeche.Model V (ConLeche.streamEnv
        ((ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map ConLeche.Cached.sideRecord))) :=
  checkerProgMini_cmpSeq_model V sz hsz hsz6 bC bS pb h64 hf (cmpAccSSzMini_of_inline sz h)

theorem checkerProgIMini_cmpSeq_no_False.{w_u} (V : Type w_u) [ConLeche.SetTheory V]
    (sz : L.TieredArray → Nat) (hsz : ∀ s, sz s < 2 ^ 64)
    (hsz6 : ∀ g ≤ 2, sz (sixArrMini g) = sz (eixArrMini g) ∧ sz (stxArrMini g) = sz (tixArrMini g))
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (hfalse : ConLeche.jsonWithTheoremFalse [bC])
    {fuel : Nat} (hf : fuel + inlineSlack ≤ abiFuel)
    (h : CmpAccSSzMini sz fuel checkerProgIMini bC bS pb) :
    False :=
  checkerProgMini_cmpSeq_no_False V sz hsz hsz6 bC bS pb h64 hfalse hf (cmpAccSSzMini_of_inline sz h)

/-- info: 'ConAgua.RISCV.Bridge.checkerProgMini_cmpSeq_twinAccepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgMini_cmpSeq_twinAccepts

/-- info: 'ConAgua.RISCV.Bridge.checkerProgMini_cmpSeq_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgMini_cmpSeq_model

/-- info: 'ConAgua.RISCV.Bridge.checkerProgMini_cmpSeq_no_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgMini_cmpSeq_no_False

/-- info: 'ConAgua.RISCV.Bridge.checkerProgIMini_cmpSeq_twinAccepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgIMini_cmpSeq_twinAccepts

/-- info: 'ConAgua.RISCV.Bridge.checkerProgIMini_cmpSeq_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgIMini_cmpSeq_model

/-- info: 'ConAgua.RISCV.Bridge.checkerProgIMini_cmpSeq_no_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerProgIMini_cmpSeq_no_False

end ConAgua.RISCV.Bridge
