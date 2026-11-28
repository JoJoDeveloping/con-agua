import ConAgua.RISCV.Compiler.ProgSimFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Program-Level Forward Simulation: Statements & Calls (`ConAgua.RISCV.Compiler.ProgSimCall`)

Statement outcome specification (`StmtOutcomeR`), function linking (`ProgFnsLinkedGen`),
call simulation spec (`FnCallSimGen`), and statement simulation (`progExecB_step`).

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard Lean axioms only.
-/

namespace ConAgua.RISCV.Compiler

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Linker

/-! ## 3. Statement & Call Specification (`StmtOutcomeR`, `ProgFnsLinked`, `FnCallSim`) -/

def ProgFnsLinkedWithGen {lkm : LinkModel} (env : CodeEnvGen lkm)
    (allocOf : FnName → FunDecl → RegAlloc) (p : _root_.L.Prog) : Prop :=
  ∃ (p' : _root_.L.Prog) (preFns postFns : List AsmItem),
    (∀ f fd, p.lookup f = some fd → (f, fd) ∈ p') ∧
    lkm.linkSpec (preFns ++ (p'.flatMap fun (g, gd) => compileFnWith (allocOf g gd) env.tab g gd) ++ postFns) =
      .ok (env.code, env.labels)

def ProgFnsLinkedGen {lkm : LinkModel} (env : CodeEnvGen lkm) (p : _root_.L.Prog) : Prop :=
  ∃ (p' : _root_.L.Prog) (preFns postFns : List AsmItem),
    (∀ f fd, p.lookup f = some fd → (f, fd) ∈ p') ∧
    lkm.linkSpec (preFns ++ (p'.flatMap fun (g, gd) => compileFn env.tab g gd) ++ postFns) =
      .ok (env.code, env.labels)

private theorem prog_mem_of_lookup_eq_some {p : _root_.L.Prog} {f : FnName} {fd : FunDecl}
    (hlk : p.lookup f = some fd) : (f, fd) ∈ p := by
  induction p with
  | nil => simp [List.lookup] at hlk
  | cons hd tl ih =>
    rcases hd with ⟨g, gd⟩
    simp only [List.lookup] at hlk
    by_cases hgf : (f == g) = true
    · rw [hgf] at hlk
      have hfd : gd = fd := Option.some.inj hlk
      have hg : g = f := (eq_of_beq hgf).symm
      rw [hfd, hg]; exact List.mem_cons_self
    · rw [Bool.eq_false_iff.mpr hgf] at hlk
      exact List.mem_cons_of_mem _ (ih hlk)

theorem ProgFnsLinkedGen.of_perm {lkm : LinkModel} {env : CodeEnvGen lkm} {p p' : _root_.L.Prog}
    (hperm : p'.Perm p) (preFns postFns : List AsmItem)
    (hlink : lkm.linkSpec (preFns ++ (p'.flatMap fun (g, gd) => compileFn env.tab g gd) ++ postFns) =
      .ok (env.code, env.labels)) : ProgFnsLinkedGen env p :=
  ⟨p', preFns, postFns, fun _ _ hlk => hperm.mem_iff.mpr (prog_mem_of_lookup_eq_some hlk), hlink⟩

theorem ProgFnsLinkedWithGen.of_perm {lkm : LinkModel} {env : CodeEnvGen lkm}
    {allocOf : FnName → FunDecl → RegAlloc} {p p' : _root_.L.Prog}
    (hperm : p'.Perm p) (preFns postFns : List AsmItem)
    (hlink : lkm.linkSpec (preFns ++ (p'.flatMap fun (g, gd) => compileFnWith (allocOf g gd) env.tab g gd) ++ postFns) =
      .ok (env.code, env.labels)) : ProgFnsLinkedWithGen env allocOf p :=
  ⟨p', preFns, postFns, fun _ _ hlk => hperm.mem_iff.mpr (prog_mem_of_lookup_eq_some hlk), hlink⟩

def ProgFnsLinked (env : CodeEnv) (p : _root_.L.Prog) : Prop :=
  ProgFnsLinkedGen env.toGen p

def StmtOutcomeR {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (fl : FrameLayout) (sp : BitVec 64) (b : Nat) (st : State)
    (retLbl : String) (brkLbl : Option String) (endPC : Nat)
    (na nb : Var → Bool)
    (tco : TcoCtx)
    (res : Except Err (Sig × St × Nat)) : Prop :=
  match res with
  | .ok (.normal, st', b') =>
    ∃ k r', RV64.run env.rom k st = .cont r' ∧
      r'.pc = BitVec.ofNat 64 (4 * endPC) ∧
      PreservedFrameNoS0 fl st r' ∧
      r'.getReg AbiReg.s0 = BitVec.ofNat 64 b' ∧
      b' ≤ b ∧
      ProgMemRel env.tab L r'.mem st'.mem ∧
      ProgFrameOkLive L fl sp r' st'.loc na ∧
      ProgMemOutside (FnWriteMaskR L fl sp) st.mem r'.mem ∧
      TabHeaderOk L r'.mem
  | .ok (.brk, st', b') =>
    ∃ tgt, brkLbl = some tgt ∧
      ∃ tgtPc k r', lookupLabel env.labels tgt = some tgtPc ∧
        RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * tgtPc) ∧
        PreservedFrameNoS0 fl st r' ∧
        r'.getReg AbiReg.s0 = BitVec.ofNat 64 b' ∧
        b' ≤ b ∧
        ProgMemRel env.tab L r'.mem st'.mem ∧
        ProgFrameOkLive L fl sp r' st'.loc nb ∧
        ProgMemOutside (FnWriteMaskR L fl sp) st.mem r'.mem ∧
        TabHeaderOk L r'.mem
  | .ok (.ret vs, st', b') =>
    (∃ retPc k r', lookupLabel env.labels retLbl = some retPc ∧
      RV64.run env.rom k st = .cont r' ∧
      (r'.pc = BitVec.ofNat 64 (4 * retPc) ∨
       (fl.isLeaf = true ∧ fl.frameSlots = 0 ∧ r'.pc = (st.getReg AbiReg.ra &&& ~~~1#64))) ∧
      vs.length ≤ env.tab.nres ∧
      PreservedRetRegs fl st r' ∧
      r'.getReg AbiReg.s0 = BitVec.ofNat 64 b' ∧
      b' ≤ b ∧
      ProgMemRel env.tab L r'.mem st'.mem ∧
      ResultsInState env.tab L r' vs ∧
      ProgMemOutside (FnWriteMaskR L fl sp) st.mem r'.mem ∧
      TabHeaderOk L r'.mem) ∨
    (∃ k r', RV64.run env.rom k st = .cont r' ∧
      r'.pc = BitVec.ofNat 64 (4 * tco.callerRetPc) ∧
      r'.getReg AbiReg.gp = L.T ∧
      r'.getReg AbiReg.sp = sp + BitVec.ofInt 64 fl.frameBytes ∧
      r'.getReg AbiReg.s2 = st.getReg AbiReg.s2 ∧
      (∀ r ∈ calleeSavedBank, r'.getReg r = tco.calleeVals r) ∧
      r'.getReg AbiReg.s0 = BitVec.ofNat 64 b' ∧
      b' ≤ b ∧
      vs.length ≤ env.tab.nres ∧
      ProgMemRel env.tab L r'.mem st'.mem ∧
      ResultsInState env.tab L r' vs ∧
      ProgMemOutside (CallWriteMask L (sp + BitVec.ofInt 64 fl.frameBytes)) st.mem r'.mem ∧
      TabHeaderOk L r'.mem)
  | .error .outOfFuel =>
    ∃ k r', RV64.run env.rom k st = .cont r' ∧
      r'.pc = BitVec.ofNat 64 (4 * env.exhaustedTarget) ∧
      PreservedTramp st r' ∧
      ProgMemOutside (CallWriteMask L (sp + BitVec.ofInt 64 fl.frameBytes)) st.mem r'.mem
  | .error (.abort code) =>
    ∃ k r', RV64.run env.rom k st = .cont r' ∧
      r'.pc = BitVec.ofNat 64 (4 * env.abortTarget) ∧
      r'.getReg AbiReg.a0 = code.toBitVec ∧
      PreservedTramp st r' ∧
      ProgMemOutside (CallWriteMask L (sp + BitVec.ofInt 64 fl.frameBytes)) st.mem r'.mem
  | .error _ =>
    ∃ k r', RV64.run env.rom k st = .cont r' ∧
      r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
      PreservedTramp st r' ∧
      ProgMemOutside (CallWriteMask L (sp + BitVec.ofInt 64 fl.frameBytes)) st.mem r'.mem

def FnCallSimGen {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab) (p : _root_.L.Prog) (b : Nat) : Prop :=
  ∀ (f : FnName) (fd : FunDecl) (vs : List _root_.L.Word) (m : _root_.L.Mem)
    (callerSp callerRa argsPtr : BitVec 64) (retPc : Nat),
    p.lookup f = some fd →
    vs.length = fd.nparams →
    b < 2 ^ 64 →
    L.stackLimit.toNat + fnFrameBytes fd + stackNeedB p b fd.body { mem := m, loc := Locals.init vs } ≤ callerSp.toNat →
    callerSp.toNat ≤ L.stackTop.toNat →
    isAligned callerSp 8 = true →
    isAligned argsPtr 8 = true →
    callerRa &&& ~~~1#64 = BitVec.ofNat 64 (4 * retPc) →
    (∀ j, j < vs.length → ∀ k, k < 8 →
      callerSp.toNat ≤ (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)) + BitVec.ofNat 64 k).toNat ∨
      ¬L.stackSpan.contains (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)) + BitVec.ofNat 64 k)) →
    ∀ (entryPc : Nat) (st : State),
      lookupLabel env.labels (fnLabel f) = some entryPc →
      st.pc = BitVec.ofNat 64 (4 * entryPc) →
      st.getReg AbiReg.gp = L.T →
      st.getReg AbiReg.sp = callerSp →
      st.getReg AbiReg.ra = callerRa →
      st.getReg AbiReg.s0 = BitVec.ofNat 64 b →
      (maxRes < fd.nparams → st.getReg AbiReg.t0 = argsPtr) →
      ProgMemRel env.tab L st.mem m →
      TabHeaderOk L st.mem →
      (∀ j, j < vs.length →
        (if j < maxRes then st.getReg (resReg j)
         else readWord64 st.mem (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)))) = (vs[j]!).toBitVec) →
      match execB p b fd.body { mem := m, loc := Locals.init vs } with
      | .ok (sig, st', b') =>
        ∃ k r',
          RV64.run env.rom k st = .cont r' ∧
          r'.pc = BitVec.ofNat 64 (4 * retPc) ∧
          r'.getReg AbiReg.gp = L.T ∧
          r'.getReg AbiReg.sp = callerSp ∧
          r'.getReg AbiReg.s2 = st.getReg AbiReg.s2 ∧
          r'.getReg AbiReg.s0 = BitVec.ofNat 64 b' ∧
          b' ≤ b ∧
          sig ≠ .brk ∧
          sig.retVal.length ≤ env.tab.nres ∧
          ProgMemRel env.tab L r'.mem st'.mem ∧
          TabHeaderOk L r'.mem ∧
          ResultsInState env.tab L r' sig.retVal ∧
          ProgMemOutside (CallWriteMask L callerSp) st.mem r'.mem
      | .error .outOfFuel =>
        ∃ k r', RV64.run env.rom k st = .cont r' ∧
          r'.pc = BitVec.ofNat 64 (4 * env.exhaustedTarget) ∧
          PreservedTramp st r' ∧
          ProgMemOutside (CallWriteMask L callerSp) st.mem r'.mem
      | .error (.abort code) =>
        ∃ k r', RV64.run env.rom k st = .cont r' ∧
          r'.pc = BitVec.ofNat 64 (4 * env.abortTarget) ∧
          r'.getReg AbiReg.a0 = code.toBitVec ∧
          PreservedTramp st r' ∧
          ProgMemOutside (CallWriteMask L callerSp) st.mem r'.mem
      | .error _ =>
        ∃ k r', RV64.run env.rom k st = .cont r' ∧
          r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedTramp st r' ∧
          ProgMemOutside (CallWriteMask L callerSp) st.mem r'.mem

abbrev FnCallSim (env : CodeEnv) (L : ProgLayout env.tab) :=
  FnCallSimGen env.toGen L

/-- Strengthened call simulation also recording preservation of `calleeSavedBank` (`s3..s11, tp`). -/
def FnCallSimGenCallee {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab) (p : _root_.L.Prog) (b : Nat) : Prop :=
  ∀ (f : FnName) (fd : FunDecl) (vs : List _root_.L.Word) (m : _root_.L.Mem)
    (callerSp callerRa argsPtr : BitVec 64) (retPc : Nat),
    p.lookup f = some fd →
    vs.length = fd.nparams →
    b < 2 ^ 64 →
    L.stackLimit.toNat + fnFrameBytes fd + stackNeedB p b fd.body { mem := m, loc := Locals.init vs } ≤ callerSp.toNat →
    callerSp.toNat ≤ L.stackTop.toNat →
    isAligned callerSp 8 = true →
    isAligned argsPtr 8 = true →
    callerRa &&& ~~~1#64 = BitVec.ofNat 64 (4 * retPc) →
    (∀ j, j < vs.length → ∀ k, k < 8 →
      callerSp.toNat ≤ (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)) + BitVec.ofNat 64 k).toNat ∨
      ¬L.stackSpan.contains (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)) + BitVec.ofNat 64 k)) →
    ∀ (entryPc : Nat) (st : State),
      lookupLabel env.labels (fnLabel f) = some entryPc →
      st.pc = BitVec.ofNat 64 (4 * entryPc) →
      st.getReg AbiReg.gp = L.T →
      st.getReg AbiReg.sp = callerSp →
      st.getReg AbiReg.ra = callerRa →
      st.getReg AbiReg.s0 = BitVec.ofNat 64 b →
      (maxRes < fd.nparams → st.getReg AbiReg.t0 = argsPtr) →
      ProgMemRel env.tab L st.mem m →
      TabHeaderOk L st.mem →
      (∀ j, j < vs.length →
        (if j < maxRes then st.getReg (resReg j)
         else readWord64 st.mem (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)))) = (vs[j]!).toBitVec) →
      match execB p b fd.body { mem := m, loc := Locals.init vs } with
      | .ok (sig, st', b') =>
        ∃ k r',
          RV64.run env.rom k st = .cont r' ∧
          r'.pc = BitVec.ofNat 64 (4 * retPc) ∧
          r'.getReg AbiReg.gp = L.T ∧
          r'.getReg AbiReg.sp = callerSp ∧
          r'.getReg AbiReg.s2 = st.getReg AbiReg.s2 ∧
          (∀ r ∈ calleeSavedBank, r'.getReg r = st.getReg r) ∧
          r'.getReg AbiReg.s0 = BitVec.ofNat 64 b' ∧
          b' ≤ b ∧
          sig ≠ .brk ∧
          sig.retVal.length ≤ env.tab.nres ∧
          ProgMemRel env.tab L r'.mem st'.mem ∧
          TabHeaderOk L r'.mem ∧
          ResultsInState env.tab L r' sig.retVal ∧
          ProgMemOutside (CallWriteMask L callerSp) st.mem r'.mem
      | .error .outOfFuel =>
        ∃ k r', RV64.run env.rom k st = .cont r' ∧
          r'.pc = BitVec.ofNat 64 (4 * env.exhaustedTarget) ∧
          PreservedTramp st r' ∧
          ProgMemOutside (CallWriteMask L callerSp) st.mem r'.mem
      | .error (.abort code) =>
        ∃ k r', RV64.run env.rom k st = .cont r' ∧
          r'.pc = BitVec.ofNat 64 (4 * env.abortTarget) ∧
          r'.getReg AbiReg.a0 = code.toBitVec ∧
          PreservedTramp st r' ∧
          ProgMemOutside (CallWriteMask L callerSp) st.mem r'.mem
      | .error _ =>
        ∃ k r', RV64.run env.rom k st = .cont r' ∧
          r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedTramp st r' ∧
          ProgMemOutside (CallWriteMask L callerSp) st.mem r'.mem

private theorem StmtOutcomeR.prepend {lkm : LinkModel} {env : CodeEnvGen lkm} {L : ProgLayout env.tab}
    {fl : FrameLayout} (hfl : FrameLayoutOk fl) {sp : BitVec 64} {b1 b2 : Nat}
    {st st1 : State} {retLbl : String} {brkLbl : Option String} {endPC endPC' : Nat}
    {na nb : Var → Bool} {tco : TcoCtx}
    {res : Except Err (Sig × St × Nat)}
    (htop : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (kc : Nat) (hrunC : RV64.run env.rom kc st = .cont st1)
    (hpresC : PreservedFrameNoS0 fl st st1)
    (hpmC : ProgMemOutside (FnWriteMaskR L fl sp) st.mem st1.mem)
    (hb : b1 ≤ b2) (hend : endPC = endPC')
    (hres : StmtOutcomeR env L fl sp b1 st1 retLbl brkLbl endPC na nb tco res) :
    StmtOutcomeR env L fl sp b2 st retLbl brkLbl endPC' na nb tco res := by
  subst hend
  have hcmC : ProgMemOutside (CallWriteMask L (sp + BitVec.ofInt 64 fl.frameBytes)) st.mem st1.mem :=
    ProgMemOutside.mono (fnWriteMaskR_sub_callWriteMask L (Nat.le_of_eq (callerSp_toNat_eq L htop).symm)) hpmC
  cases res with
  | error err =>
    cases err with
    | outOfFuel =>
      obtain ⟨k2, r2', hrun2, hpc2, hpres2, hpm2⟩ := hres
      exact ⟨kc + k2, r2', by rw [run_add, hrunC]; exact hrun2, hpc2, hpresC.toTramp.trans hpres2, hcmC.trans hpm2⟩
    | abort code =>
      obtain ⟨k2, r2', hrun2, hpc2, ha0_2, hpres2, hpm2⟩ := hres
      exact ⟨kc + k2, r2', by rw [run_add, hrunC]; exact hrun2, hpc2, ha0_2, hpresC.toTramp.trans hpres2, hcmC.trans hpm2⟩
    | oob =>
      obtain ⟨k2, r2', hrun2, hpc2, hpres2, hpm2⟩ := hres
      exact ⟨kc + k2, r2', by rw [run_add, hrunC]; exact hrun2, hpc2, hpresC.toTramp.trans hpres2, hcmC.trans hpm2⟩
    | noFun fn =>
      obtain ⟨k2, r2', hrun2, hpc2, hpres2, hpm2⟩ := hres
      exact ⟨kc + k2, r2', by rw [run_add, hrunC]; exact hrun2, hpc2, hpresC.toTramp.trans hpres2, hcmC.trans hpm2⟩
  | ok r =>
    rcases r with ⟨sig, st', b'⟩
    cases sig with
    | normal =>
      obtain ⟨k2, r2', hrun2, hpc2, hpres2, hs0_2, hb2, hm2, hf2, hout2, hhdr2⟩ := hres
      exact ⟨kc + k2, r2', by rw [run_add, hrunC]; exact hrun2, hpc2,
        hpresC.trans hpres2, hs0_2, Nat.le_trans hb2 hb, hm2, hf2, hpmC.trans hout2, hhdr2⟩
    | brk =>
      obtain ⟨tgt, hbrk, tgtPc, k2, r2', hlkp, hrun2, hpc2, hpres2, hs0_2, hb2, hm2, hf2, hout2, hhdr2⟩ := hres
      exact ⟨tgt, hbrk, tgtPc, kc + k2, r2', hlkp, by rw [run_add, hrunC]; exact hrun2, hpc2,
        hpresC.trans hpres2, hs0_2, Nat.le_trans hb2 hb, hm2, hf2, hpmC.trans hout2, hhdr2⟩
    | ret vs =>
      rcases hres with ⟨retPc, k2, r2', hlkp, hrun2, hpc2, hvs, hpres2, hs0_2, hb2, hm2, hresR, hout2, hhdr2⟩ |
        ⟨k2, r2', hrun2, hpc2, hgp2, hsp2, hs2_2, hcal2, hs0_2, hb2, hvs, hm2, hresR, hout2, hhdr2⟩
      · have hpc2' : r2'.pc = BitVec.ofNat 64 (4 * retPc) ∨
            (fl.isLeaf = true ∧ fl.frameSlots = 0 ∧ r2'.pc = (st.getReg AbiReg.ra &&& ~~~1#64)) :=
          hpc2.elim Or.inl fun ⟨hl, hfr, hpcR⟩ => Or.inr ⟨hl, hfr, by rw [hpcR, hpresC.leafRa hl]⟩
        exact Or.inl ⟨retPc, kc + k2, r2', hlkp, by rw [run_add, hrunC]; exact hrun2, hpc2', hvs,
          hpresC.trans_ret hfl hpres2, hs0_2, Nat.le_trans hb2 hb, hm2, hresR, hpmC.trans hout2, hhdr2⟩
      · exact Or.inr ⟨kc + k2, r2', by rw [run_add, hrunC]; exact hrun2, hpc2,
          hgp2, hsp2, hs2_2.trans hpresC.abi.s2, hcal2, hs0_2,
          Nat.le_trans hb2 hb, hvs, hm2, hresR, hcmC.trans hout2, hhdr2⟩

private theorem StmtOutcomeR.prepend_err {lkm : LinkModel} {env : CodeEnvGen lkm} {L : ProgLayout env.tab}
    {fl : FrameLayout} {sp : BitVec 64} {b1 b2 : Nat}
    {st st1 : State} {retLbl : String} {brkLbl1 brkLbl2 : Option String} {endPC1 endPC2 : Nat}
    {na1 nb1 na2 nb2 : Var → Bool} {tco : TcoCtx}
    {err : Err}
    (htop : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (kc : Nat) (hrunC : RV64.run env.rom kc st = .cont st1)
    (hpresC : PreservedFrameNoS0 fl st st1)
    (hpmC : ProgMemOutside (FnWriteMaskR L fl sp) st.mem st1.mem)
    (hres : StmtOutcomeR env L fl sp b1 st1 retLbl brkLbl1 endPC1 na1 nb1 tco (.error err)) :
    StmtOutcomeR env L fl sp b2 st retLbl brkLbl2 endPC2 na2 nb2 tco (.error err) := by
  have hcmC : ProgMemOutside (CallWriteMask L (sp + BitVec.ofInt 64 fl.frameBytes)) st.mem st1.mem :=
    ProgMemOutside.mono (fnWriteMaskR_sub_callWriteMask L (Nat.le_of_eq (callerSp_toNat_eq L htop).symm)) hpmC
  cases err with
  | outOfFuel =>
    obtain ⟨k2, r2', hrun2, hpc2, hpres2, hpm2⟩ := hres
    exact ⟨kc + k2, r2', by rw [run_add, hrunC]; exact hrun2, hpc2, hpresC.toTramp.trans hpres2, hcmC.trans hpm2⟩
  | abort code =>
    obtain ⟨k2, r2', hrun2, hpc2, ha0_2, hpres2, hpm2⟩ := hres
    exact ⟨kc + k2, r2', by rw [run_add, hrunC]; exact hrun2, hpc2, ha0_2, hpresC.toTramp.trans hpres2, hcmC.trans hpm2⟩
  | oob =>
    obtain ⟨k2, r2', hrun2, hpc2, hpres2, hpm2⟩ := hres
    exact ⟨kc + k2, r2', by rw [run_add, hrunC]; exact hrun2, hpc2, hpresC.toTramp.trans hpres2, hcmC.trans hpm2⟩
  | noFun fn =>
    obtain ⟨k2, r2', hrun2, hpc2, hpres2, hpm2⟩ := hres
    exact ⟨kc + k2, r2', by rw [run_add, hrunC]; exact hrun2, hpc2, hpresC.toTramp.trans hpres2, hcmC.trans hpm2⟩

private theorem StmtOutcomeR.prepend_brk {lkm : LinkModel} {env : CodeEnvGen lkm} {L : ProgLayout env.tab}
    {fl : FrameLayout} {sp : BitVec 64} {b1 b2 : Nat}
    {st st1 : State} {retLbl : String} {brkLbl : Option String} {endPC1 endPC2 : Nat}
    {na1 na2 nb : Var → Bool} {tco : TcoCtx}
    {st' : St} {b' : Nat}
    (kc : Nat) (hrunC : RV64.run env.rom kc st = .cont st1)
    (hpresC : PreservedFrameNoS0 fl st st1)
    (hpmC : ProgMemOutside (FnWriteMaskR L fl sp) st.mem st1.mem)
    (hb : b1 ≤ b2)
    (hres : StmtOutcomeR env L fl sp b1 st1 retLbl brkLbl endPC1 na1 nb tco (.ok (.brk, st', b'))) :
    StmtOutcomeR env L fl sp b2 st retLbl brkLbl endPC2 na2 nb tco (.ok (.brk, st', b')) := by
  obtain ⟨tgt, hbrk, tgtPc, k2, r2', hlkp, hrun2, hpc2, hpres2, hs0_2, hb2, hm2, hf2, hout2, hhdr2⟩ := hres
  exact ⟨tgt, hbrk, tgtPc, kc + k2, r2', hlkp, by rw [run_add, hrunC]; exact hrun2, hpc2,
    hpresC.trans hpres2, hs0_2, Nat.le_trans hb2 hb, hm2, hf2, hpmC.trans hout2, hhdr2⟩

private theorem StmtOutcomeR.prepend_ret {lkm : LinkModel} {env : CodeEnvGen lkm} {L : ProgLayout env.tab}
    {fl : FrameLayout} (hfl : FrameLayoutOk fl) {sp : BitVec 64} {b1 b2 : Nat}
    {st st1 : State} {retLbl : String} {brkLbl1 brkLbl2 : Option String} {endPC1 endPC2 : Nat}
    {na1 nb1 na2 nb2 : Var → Bool} {tco : TcoCtx}
    {vs : List _root_.L.Word} {st' : St} {b' : Nat}
    (htop : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (kc : Nat) (hrunC : RV64.run env.rom kc st = .cont st1)
    (hpresC : PreservedFrameNoS0 fl st st1)
    (hpmC : ProgMemOutside (FnWriteMaskR L fl sp) st.mem st1.mem)
    (hb : b1 ≤ b2)
    (hres : StmtOutcomeR env L fl sp b1 st1 retLbl brkLbl1 endPC1 na1 nb1 tco (.ok (.ret vs, st', b'))) :
    StmtOutcomeR env L fl sp b2 st retLbl brkLbl2 endPC2 na2 nb2 tco (.ok (.ret vs, st', b')) := by
  rcases hres with ⟨retPc, k2, r2', hlkp, hrun2, hpc2, hlen, hpres2, hs0_2, hb2, hm2, hres2, hout2, hhdr2⟩ |
    ⟨k2, r2', hrun2, hpc2, hgp2, hsp2, hs2_2, hcal2, hs0_2, hb2, hlen, hm2, hres2, hout2, hhdr2⟩
  · have hpc2' : r2'.pc = BitVec.ofNat 64 (4 * retPc) ∨
        (fl.isLeaf = true ∧ fl.frameSlots = 0 ∧ r2'.pc = (st.getReg AbiReg.ra &&& ~~~1#64)) :=
      hpc2.elim Or.inl fun ⟨hl, hfr, hpcR⟩ => Or.inr ⟨hl, hfr, by rw [hpcR, hpresC.leafRa hl]⟩
    exact Or.inl ⟨retPc, kc + k2, r2', hlkp, by rw [run_add, hrunC]; exact hrun2, hpc2', hlen,
      hpresC.trans_ret hfl hpres2, hs0_2, Nat.le_trans hb2 hb, hm2, hres2, hpmC.trans hout2, hhdr2⟩
  · exact Or.inr ⟨kc + k2, r2', by rw [run_add, hrunC]; exact hrun2, hpc2,
      hgp2, hsp2, hs2_2.trans hpresC.abi.s2, hcal2, hs0_2,
      Nat.le_trans hb2 hb, hlen, hm2, hres2,
      (ProgMemOutside.mono (fnWriteMaskR_sub_callWriteMask L (Nat.le_of_eq (callerSp_toNat_eq L htop).symm)) hpmC).trans hout2,
      hhdr2⟩

private theorem stmtOutcomeR_of_base_normal {lkm : LinkModel} {env : CodeEnvGen lkm} {L : ProgLayout env.tab}
    {fl : FrameLayout} {sp : BitVec 64} {b : Nat} {st : State} {retLbl : String} {brkLbl : Option String}
    {endPC : Nat} {na nb : Var → Bool} {tco : TcoCtx} {st' : _root_.L.St}
    (hs0 : st.getReg AbiReg.s0 = BitVec.ofNat 64 b) (hhdr : TabHeaderOk L st.mem)
    (h : ∃ k r', RV64.run env.rom k st = .cont r' ∧
      r'.pc = BitVec.ofNat 64 (4 * endPC) ∧
      PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) st r' ∧
      ProgMemRel env.tab L r'.mem st'.mem ∧
      ProgFrameOkR L fl sp r' st'.loc ∧
      ProgMemOutside (FnWriteMaskR L fl sp) st.mem r'.mem) :
    StmtOutcomeR env L fl sp b st retLbl brkLbl endPC na nb tco (.ok (.normal, st', b)) := by
  obtain ⟨k, r', hrun, hpc, hpres, hmem, hfr, hout⟩ := h
  exact ⟨k, r', hrun, hpc, hpres.toFrameNoS0, hpres.abi.s0.trans hs0, Nat.le_refl b,
    hmem, hfr.toLive_self na, hout, hhdr.of_fnWriteMaskR L hout⟩

private theorem stmtOutcomeR_of_base_normal_live {lkm : LinkModel} {env : CodeEnvGen lkm} {L : ProgLayout env.tab}
    {fl : FrameLayout} {sp : BitVec 64} {b : Nat} {st : State} {retLbl : String} {brkLbl : Option String}
    {endPC : Nat} {na nb : Var → Bool} {tco : TcoCtx} {st' : _root_.L.St}
    (hs0 : st.getReg AbiReg.s0 = BitVec.ofNat 64 b) (hhdr : TabHeaderOk L st.mem)
    (h : ∃ k r', RV64.run env.rom k st = .cont r' ∧
      r'.pc = BitVec.ofNat 64 (4 * endPC) ∧
      PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) st r' ∧
      ProgMemRel env.tab L r'.mem st'.mem ∧
      ProgFrameOkLive L fl sp r' st'.loc na ∧
      ProgMemOutside (FnWriteMaskR L fl sp) st.mem r'.mem) :
    StmtOutcomeR env L fl sp b st retLbl brkLbl endPC na nb tco (.ok (.normal, st', b)) := by
  obtain ⟨k, r', hrun, hpc, hpres, hmem, hfr, hout⟩ := h
  exact ⟨k, r', hrun, hpc, hpres.toFrameNoS0, hpres.abi.s0.trans hs0, Nat.le_refl b,
    hmem, hfr, hout, hhdr.of_fnWriteMaskR L hout⟩

private theorem stmtOutcomeR_of_err_oob {lkm : LinkModel} {env : CodeEnvGen lkm} {L : ProgLayout env.tab}
    {fl : FrameLayout} {sp : BitVec 64} {b : Nat} {st : State} {retLbl : String} {brkLbl : Option String}
    {endPC : Nat} {na nb : Var → Bool} {tco : TcoCtx}
    (htop : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (h : ∃ k r', RV64.run env.rom k st = .cont r' ∧
      r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
      PreservedRegs st r' ∧
      ProgMemOutside (FnWriteMaskR L fl sp) st.mem r'.mem) :
    StmtOutcomeR env L fl sp b st retLbl brkLbl endPC na nb tco (.error .oob) := by
  obtain ⟨k, r', hrun, hpc, hpres, hpm⟩ := h
  exact ⟨k, r', hrun, hpc, hpres.toTramp,
    ProgMemOutside.mono (fnWriteMaskR_sub_callWriteMask L (Nat.le_of_eq (callerSp_toNat_eq L htop).symm)) hpm⟩

private theorem stmtOutcomeR_of_ghost {lkm : LinkModel} {env : CodeEnvGen lkm} {L : ProgLayout env.tab}
    {p : _root_.L.Prog} {fl : FrameLayout} {sp : BitVec 64} {b : Nat} {s : _root_.L.Stmt}
    {lm : _root_.L.Mem} {loc loc' : _root_.L.Locals} {st : State}
    {retLbl : String} {brkLbl : Option String} {endPC : Nat}
    {na nb : Var → Bool} {tco : TcoCtx}
    (hag : ∀ x, (stmtVarCallFree x s (na x) (nb x)).1 = true → loc' x = loc x)
    (hres : StmtOutcomeR env L fl sp b st retLbl brkLbl endPC na nb tco
      (execB p b s ⟨lm, loc'⟩)) :
    StmtOutcomeR env L fl sp b st retLbl brkLbl endPC na nb tco
      (execB p b s ⟨lm, loc⟩) := by
  have hcg := (execB_congr_callFree p b s na nb lm loc' loc hag).2
  cases hx1 : execB p b s ⟨lm, loc'⟩ with
  | error e1 =>
    cases hx2 : execB p b s ⟨lm, loc⟩ with
    | error e2 =>
      rw [hx1, hx2] at hcg; subst hcg; rw [hx1] at hres
      cases e1 <;> exact hres
    | ok _ => rw [hx1, hx2] at hcg; exact False.elim hcg
  | ok r1 =>
    rcases r1 with ⟨sig1, st1, b1⟩
    cases hx2 : execB p b s ⟨lm, loc⟩ with
    | error _ => rw [hx1, hx2] at hcg; exact False.elim hcg
    | ok r2 =>
      rcases r2 with ⟨sig2, st2, b2⟩
      rw [hx1, hx2] at hcg; rcases hcg with ⟨rfl, hmemEq, rfl, hagN, hagB⟩
      rw [hx1] at hres
      cases sig1 with
      | normal =>
        obtain ⟨k, r', hrun, hpc, hpres, hs0, hbLe, hm, hf, hout, hhdr⟩ := hres
        refine ⟨k, r', hrun, hpc, hpres, hs0, hbLe, by rw [← hmemEq]; exact hm, ?_, hout, hhdr⟩
        intro x hx hna; rw [← hagN rfl x hna]; exact hf x hx hna
      | brk =>
        obtain ⟨tgt, hbrk, tgtPc, k, r', hlkp, hrun, hpc, hpres, hs0, hbLe, hm, hf, hout, hhdr⟩ := hres
        refine ⟨tgt, hbrk, tgtPc, k, r', hlkp, hrun, hpc, hpres, hs0, hbLe, by rw [← hmemEq]; exact hm, ?_, hout, hhdr⟩
        intro x hx hnb; rw [← hagB rfl x hnb]; exact hf x hx hnb
      | ret vs =>
        rcases hres with ⟨retPc, k, r', hlkp, hrun, hpc, hvslen, hpres, hs0, hbLe, hm, hresR, hout, hhdr⟩ |
          ⟨k, r', hrun, hpc, hgp, hsp, hs2, hcal, hs0, hbLe, hvslen, hm, hresR, hout, hhdr⟩
        · exact Or.inl ⟨retPc, k, r', hlkp, hrun, hpc, hvslen, hpres, hs0, hbLe, by rw [← hmemEq]; exact hm, hresR, hout, hhdr⟩
        · exact Or.inr ⟨k, r', hrun, hpc, hgp, hsp, hs2, hcal, hs0, hbLe, hvslen, by rw [← hmemEq]; exact hm, hresR, hout, hhdr⟩

private theorem compileSR_ite_skip_l_abort0 (tab : Tab) (fl : FrameLayout) (pfx : String) (lblId : Nat)
    (brkLbl : Option String) (retLbl : String) (isTail : Bool) (c : _root_.L.Cond) :
    (compileSR tab fl pfx lblId brkLbl retLbl isTail (.ite c .skip (.abort (.const 0)))).1 =
      (compileCR tab fl 0 pfx lblId c false s!"{pfx}_abort0stub").1 := rfl

private theorem compileSR_ite_skip_l (tab : Tab) (fl : FrameLayout) (pfx : String) (lblId : Nat)
    (brkLbl : Option String) (retLbl : String) (isTail : Bool) (c : _root_.L.Cond) (s2 : _root_.L.Stmt)
    (hs2 : s2 ≠ .skip) (hab2 : isAbort0Stmt s2 = false) :
    (compileSR tab fl pfx lblId brkLbl retLbl isTail (.ite c .skip s2)).1 =
      let endLbl := s!"{pfx}_endif_{lblId}"
      let rC := compileCR tab fl 0 pfx (lblId + 1) c true endLbl
      let r2 := compileSR tab fl pfx rC.2 brkLbl retLbl false s2
      rC.1 ++ r2.1 ++ [Asm.lbl endLbl] := by
  cases s2 with
  | skip => exact absurd rfl hs2
  | _ => simp [compileSR, hab2]

private theorem compileSR_ite_general (tab : Tab) (fl : FrameLayout) (pfx : String) (lblId : Nat)
    (brkLbl : Option String) (retLbl : String) (isTail : Bool) (c : _root_.L.Cond) (s1 s2 : _root_.L.Stmt)
    (hs1 : s1 ≠ .skip) (hs2 : s2 ≠ .skip) :
    (compileSR tab fl pfx lblId brkLbl retLbl isTail (.ite c s1 s2)).1 =
      let elseLbl := s!"{pfx}_else_{lblId}"
      let endLbl := s!"{pfx}_endif_{lblId}"
      let rC := compileCR tab fl 0 pfx (lblId + 1) c false elseLbl
      let r1 := compileSR tab fl pfx rC.2 brkLbl retLbl false s1
      let r2 := compileSR tab fl pfx r1.2 brkLbl retLbl isTail s2
      let jEnd := if stmtMayFallthrough s1 then [Asm.j endLbl] else []
      rC.1 ++ r1.1 ++ jEnd ++ [Asm.lbl elseLbl] ++ r2.1 ++ [Asm.lbl endLbl] := by
  cases s2 with
  | skip => exact absurd rfl hs2
  | _ =>
    cases s1 with
    | skip => exact absurd rfl hs1
    | _ => simp [compileSR, List.append_assoc]

private theorem evalC_congr_eq_err {c : Cond} {m : _root_.L.Mem} {l1 l2 : _root_.L.Locals}
    (hag : ∀ x, condUsesVar x c = true → l1 x = l2 x) {err : Err}
    (h : _root_.L.evalC c ⟨m, l1⟩ = .error err) : _root_.L.evalC c ⟨m, l2⟩ = .error err := by
  have hc := evalC_congr_uses c m l1 l2 hag
  cases h2 : _root_.L.evalC c ⟨m, l2⟩ with
  | ok _ => rw [h, h2] at hc; exact False.elim hc
  | error err2 => rw [h, h2] at hc; subst hc; rfl

private theorem evalC_congr_eq_ok {c : Cond} {m : _root_.L.Mem} {l1 l2 : _root_.L.Locals}
    (hag : ∀ x, condUsesVar x c = true → l1 x = l2 x) {bval : Bool} {st1 : St}
    (h : _root_.L.evalC c ⟨m, l1⟩ = .ok (bval, st1)) : _root_.L.evalC c ⟨m, l2⟩ = .ok (bval, ⟨m, l2⟩) := by
  have hc := evalC_congr_uses c m l1 l2 hag
  rcases _root_.L.evalC_pure c ⟨m, l2⟩ with ⟨b2, h2⟩ | h2
  · rw [h, h2] at hc; subst hc; exact h2
  · rw [h, h2] at hc; exact False.elim hc

private theorem evalArgs_congr_eq_err {es : List Expr} {m : _root_.L.Mem} {l1 l2 : _root_.L.Locals}
    (hag : ∀ x, es.any (exprUsesVar x) = true → l1 x = l2 x) {err : Err}
    (h : _root_.L.evalArgs es ⟨m, l1⟩ = .error err) : _root_.L.evalArgs es ⟨m, l2⟩ = .error err := by
  have ha := evalArgs_congr_uses es m l1 l2 hag
  cases h2 : _root_.L.evalArgs es ⟨m, l2⟩ with
  | ok _ => rw [h, h2] at ha; exact False.elim ha
  | error err2 => rw [h, h2] at ha; subst ha; rfl

private theorem evalArgs_congr_eq_ok {es : List Expr} {m : _root_.L.Mem} {l1 l2 : _root_.L.Locals}
    (hag : ∀ x, es.any (exprUsesVar x) = true → l1 x = l2 x) {vs : List _root_.L.Word} {st1 : St}
    (h : _root_.L.evalArgs es ⟨m, l1⟩ = .ok (vs, st1)) : _root_.L.evalArgs es ⟨m, l2⟩ = .ok (vs, ⟨m, l2⟩) := by
  have ha := evalArgs_congr_uses es m l1 l2 hag
  rcases _root_.L.evalArgs_pure es ⟨m, l2⟩ with ⟨vs2, h2⟩ | h2
  · rw [h, h2] at ha; subst ha; exact h2
  · rw [h, h2] at ha; exact False.elim ha

private theorem prog_ite_step_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab) (p : _root_.L.Prog)
    (fl : FrameLayout) (hfl : FrameLayoutOk fl) (b : Nat) (lm : _root_.L.Mem) (loc : _root_.L.Locals)
    (sp : BitVec 64) (pfx : String) (lblId : Nat) (brkLbl : Option String) (retLbl : String) (retPc : Nat)
    (isTail : Bool) (c : _root_.L.Cond) (s1 s2 : _root_.L.Stmt)
    (na nb : Var → Bool) (tco : TcoCtx)
    (hcOk : condOkB env.tab fl.nlocals c = true)
    (hVfC : CondVarsInFrame fl c)
    (hs1Ok : stmtOkB env.tab p fl.nlocals brkLbl.isSome s1 = true)
    (hs2Ok : stmtOkB env.tab p fl.nlocals brkLbl.isSome s2 = true)
    (hs1Args : stmtArgsOkB p s1 = true) (hs2Args : stmtArgsOkB p s2 = true)
    (hTmp : max (usedTempsCond c) (max (usedTempsStmtR fl.isLeaf fl.alloc s1) (usedTempsStmtR fl.isLeaf fl.alloc s2)) ≤ fl.usedTemps)
    (hLeaf : fl.isLeaf = true → stmtHasCall (.ite c s1 s2) = false)
    (habort0 : stmtHasAbort0 (.ite c s1 s2) = true → Abort0StubOk env pfx)
    (_hb64 : b < 2 ^ 64) (hal : isAligned sp 8 = true)
    (hlim : L.stackLimit.toNat + stackNeedB p b (.ite c s1 s2) { mem := lm, loc := loc } ≤ sp.toNat)
    (htop : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (pre post : List AsmItem)
    (hTail : isTail = true → lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.ite c s1 s2)).1 = retPc)
    (hlink : lkm.linkSpec (pre ++ (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.ite c s1 s2)).1 ++ post) =
      .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hs0 : st.getReg AbiReg.s0 = BitVec.ofNat 64 b)
    (hm : ProgMemRel env.tab L st.mem lm)
    (hf : ProgFrameOkLive L fl sp st loc (fun x => (stmtVarCallFree x (.ite c s1 s2) (na x) (nb x)).1))
    (hhdr : TabHeaderOk L st.mem) (htco : TcoStateOk fl sp tco st)
    (ih1 : ∀ (lid : Nat) (isT : Bool) (pre1 post1 : List AsmItem) (st1 : State),
      stmtOkB env.tab p fl.nlocals brkLbl.isSome s1 = true →
      stmtArgsOkB p s1 = true →
      usedTempsStmtR fl.isLeaf fl.alloc s1 ≤ fl.usedTemps →
      (fl.isLeaf = true → stmtHasCall s1 = false) →
      L.stackLimit.toNat + stackNeedB p b s1 { mem := lm, loc := loc } ≤ sp.toNat →
      (isT = true → lkm.totalSize pre1 + lkm.totalSize (compileSR env.tab fl pfx lid brkLbl retLbl isT s1).1 = retPc) →
      lkm.linkSpec (pre1 ++ (compileSR env.tab fl pfx lid brkLbl retLbl isT s1).1 ++ post1) = .ok (env.code, env.labels) →
      st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) →
      st1.getReg AbiReg.gp = L.T → T5GpOk L fl st1 → st1.getReg AbiReg.sp = sp →
      st1.getReg AbiReg.s0 = BitVec.ofNat 64 b →
      ProgMemRel env.tab L st1.mem lm →
      ProgFrameOkLive L fl sp st1 loc (fun x => (stmtVarCallFree x s1 (na x) (nb x)).1) →
      TabHeaderOk L st1.mem → TcoStateOk fl sp tco st1 →
      StmtOutcomeR env L fl sp b st1 retLbl brkLbl
        (lkm.totalSize pre1 + lkm.totalSize (compileSR env.tab fl pfx lid brkLbl retLbl isT s1).1) na nb tco
        (execB p b s1 { mem := lm, loc := loc }))
    (ih2 : ∀ (lid : Nat) (isT : Bool) (pre2 post2 : List AsmItem) (st2 : State),
      stmtOkB env.tab p fl.nlocals brkLbl.isSome s2 = true →
      stmtArgsOkB p s2 = true →
      usedTempsStmtR fl.isLeaf fl.alloc s2 ≤ fl.usedTemps →
      (fl.isLeaf = true → stmtHasCall s2 = false) →
      L.stackLimit.toNat + stackNeedB p b s2 { mem := lm, loc := loc } ≤ sp.toNat →
      (isT = true → lkm.totalSize pre2 + lkm.totalSize (compileSR env.tab fl pfx lid brkLbl retLbl isT s2).1 = retPc) →
      lkm.linkSpec (pre2 ++ (compileSR env.tab fl pfx lid brkLbl retLbl isT s2).1 ++ post2) = .ok (env.code, env.labels) →
      st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) →
      st2.getReg AbiReg.gp = L.T → T5GpOk L fl st2 → st2.getReg AbiReg.sp = sp →
      st2.getReg AbiReg.s0 = BitVec.ofNat 64 b →
      ProgMemRel env.tab L st2.mem lm →
      ProgFrameOkLive L fl sp st2 loc (fun x => (stmtVarCallFree x s2 (na x) (nb x)).1) →
      TabHeaderOk L st2.mem → TcoStateOk fl sp tco st2 →
      StmtOutcomeR env L fl sp b st2 retLbl brkLbl
        (lkm.totalSize pre2 + lkm.totalSize (compileSR env.tab fl pfx lid brkLbl retLbl isT s2).1) na nb tco
        (execB p b s2 { mem := lm, loc := loc })) :
    StmtOutcomeR env L fl sp b st retLbl brkLbl
      (lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.ite c s1 s2)).1) na nb tco
      (execB p b (.ite c s1 s2) { mem := lm, loc := loc }) := by
  have hLeaf1 : fl.isLeaf = true → stmtHasCall s1 = false := fun hl =>
    (Bool.or_eq_false_iff.mp (by simpa [stmtHasCall] using hLeaf hl)).1
  have hLeaf2 : fl.isLeaf = true → stmtHasCall s2 = false := fun hl =>
    (Bool.or_eq_false_iff.mp (by simpa [stmtHasCall] using hLeaf hl)).2
  have hframeValid : (frameSpanR fl sp).valid := Nat.le_trans htop L.hStackValid
  let liveIte : Var → Bool := fun x => (stmtVarCallFree x (.ite c s1 s2) (na x) (nb x)).1
  let loc' := ghostLoc fl sp st loc liveIte
  have hf' : ProgFrameOkR L fl sp st loc' := ghostLoc_frameOk hf
  have hagIte : ∀ x, liveIte x = true → loc' x = loc x := ghostLoc_agree fl sp st loc liveIte
  have hcAg : ∀ x, condUsesVar x c = true → loc' x = loc x :=
    fun x hx => hagIte x (by simp [liveIte, stmtVarCallFree, hx])
  have hs1Ag : ∀ x, (stmtVarCallFree x s1 (na x) (nb x)).1 = true → loc' x = loc x :=
    fun x hx => hagIte x (by simp [liveIte, stmtVarCallFree, hx])
  have hs2Ag : ∀ x, (stmtVarCallFree x s2 (na x) (nb x)).1 = true → loc' x = loc x :=
    fun x hx => hagIte x (by simp [liveIte, stmtVarCallFree, hx])
  by_cases hs2Skip : s2 = .skip
  · subst hs2Skip
    by_cases hab1 : isAbort0Stmt s1 = true
    · have hs1Eq : s1 = .abort (.const 0) := eq_abort0_of_isAbort0Stmt hab1
      subst hs1Eq
      let abort0Lbl := s!"{pfx}_abort0stub"
      obtain ⟨ab0Pc, hab0Lbl, hstub⟩ := habort0 rfl
      have hcodeEq : (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.ite c (.abort (.const 0)) .skip)).1 =
          (compileCR env.tab fl 0 pfx lblId c true abort0Lbl).1 := rfl
      rw [hcodeEq] at hlink ⊢
      have hcond := reg_evalCond_sim env L fl hfl lm loc' hal (by omega) htop c pre post 0 pfx lblId true abort0Lbl ab0Pc
        hcOk hVfC (by omega) hab0Lbl hlink (linkResolved_sub_pc64 env pre _ post hlink) st hpc hgp ht5 hsp hm hf'
      cases hce : _root_.L.evalC c { mem := lm, loc := loc' } with
      | error err =>
        have herr := evalC_err_eq_oob c { mem := lm, loc := loc' } hce
        subst herr; rw [hce] at hcond; rw [execB_ite, evalC_congr_eq_err hcAg hce]
        obtain ⟨k, r', hrun, hpc', hpres, hout⟩ := hcond
        exact stmtOutcomeR_of_err_oob htop ⟨k, r', hrun, hpc', hpres.abi,
          ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L (by omega) htop (Nat.zero_le _)) hout⟩
      | ok rc =>
        rcases rc with ⟨bval, stc⟩
        have hce0 := evalC_congr_eq_ok hcAg hce
        rw [hce] at hcond
        obtain ⟨kc, st1, hrunC, hpc1, hpresC, houtC⟩ := hcond
        have hm1 := ProgMemRel.of_tempSpanR (by omega) htop (Nat.zero_le _) houtC hm
        have hf1' := ProgFrameOkR.of_preserved_temp hfl hframeValid (Nat.zero_le _) (hpresC.mono (fun _ h => False.elim h)) houtC hf'
        have hpmC : ProgMemOutside (FnWriteMaskR L fl sp) st.mem st1.mem :=
          ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L (by omega) htop (Nat.zero_le _)) houtC
        have hhdr1 : TabHeaderOk L st1.mem := hhdr.of_fnWriteMaskR L hpmC
        cases bval with
        | true =>
          simp only [beq_self_eq_true, ↓reduceIte] at hpc1
          obtain ⟨kA, rA, hrunA, hpcA, ha0A, hpresA, hmemA⟩ := hstub st1 hpc1
          rw [execB_ite, hce0]; dsimp only; rw [execB_abort]
          exact ⟨kc + kA, rA, by rw [run_add, hrunC]; exact hrunA, hpcA, ha0A, hpresC.abi.toTramp.trans hpresA,
            ProgMemOutside.mono (fnWriteMaskR_sub_callWriteMask L (Nat.le_of_eq (callerSp_toNat_eq L htop).symm))
              (by rw [hmemA]; exact hpmC)⟩
        | false =>
          simp only [Bool.false_beq, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc1
          rw [execB_ite, hce0]; simp only [execB_skip]
          exact ⟨kc, st1, hrunC, hpc1, hpresC.toFrameNoS0_all, hpresC.abi.s0.trans hs0, Nat.le_refl b,
            hm1, hf1'.toLive hs2Ag, hpmC, hhdr1⟩
    · have hab1F : isAbort0Stmt s1 = false := Bool.eq_false_iff.mpr hab1
      let endLbl := s!"{pfx}_endif_{lblId}"
      let rC := compileCR env.tab fl 0 pfx (lblId + 1) c false endLbl
      let r1 := compileSR env.tab fl pfx rC.2 brkLbl retLbl false s1
      have hcodeEq : (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.ite c s1 .skip)).1 =
          rC.1 ++ r1.1 ++ [Asm.lbl endLbl] := by
        simp [compileSR, hab1F, rC, r1, endLbl]
      have htwEq : lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.ite c s1 .skip)).1 =
          lkm.totalSize (rC.1 ++ r1.1) := by
        simp only [hcodeEq, lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero]
      rw [hcodeEq] at hlink
      have hendLbl : lookupLabel env.labels endLbl = some (lkm.totalSize (pre ++ rC.1 ++ r1.1)) :=
        linkResolved_lbl_lm lkm _ endLbl _ (by simpa [List.append_assoc] using hlink)
      have hlinkC : lkm.linkSpec (pre ++ rC.1 ++ (r1.1 ++ [Asm.lbl endLbl] ++ post)) =
          .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
      have hcond := reg_evalCond_sim env L fl hfl lm loc' hal (by omega) htop c pre _ 0 pfx (lblId + 1) false endLbl _
        hcOk hVfC (by omega) hendLbl hlinkC (linkResolved_sub_pc64 env pre rC.1 _ hlinkC) st hpc hgp ht5 hsp hm hf'
      cases hce : _root_.L.evalC c { mem := lm, loc := loc' } with
      | error err =>
        have herr := evalC_err_eq_oob c { mem := lm, loc := loc' } hce
        subst herr; rw [hce] at hcond; rw [execB_ite, evalC_congr_eq_err hcAg hce]
        obtain ⟨k, r', hrun, hpc', hpres, hout⟩ := hcond
        exact stmtOutcomeR_of_err_oob htop ⟨k, r', hrun, hpc', hpres.abi,
          ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L (by omega) htop (Nat.zero_le _)) hout⟩
      | ok rc =>
        rcases rc with ⟨bval, stc⟩
        have hce0 := evalC_congr_eq_ok hcAg hce
        rw [hce] at hcond
        obtain ⟨kc, st1, hrunC, hpc1, hpresC, houtC⟩ := hcond
        have hm1 := ProgMemRel.of_tempSpanR (by omega) htop (Nat.zero_le _) houtC hm
        have hf1' := ProgFrameOkR.of_preserved_temp hfl hframeValid (Nat.zero_le _) (hpresC.mono (fun _ h => False.elim h)) houtC hf'
        have hpmC : ProgMemOutside (FnWriteMaskR L fl sp) st.mem st1.mem :=
          ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L (by omega) htop (Nat.zero_le _)) houtC
        have hhdr1 : TabHeaderOk L st1.mem := hhdr.of_fnWriteMaskR L hpmC
        have hlimIte := stackNeedB_ite p b c s1 .skip { mem := lm, loc := loc }
        rw [hce0] at hlimIte
        cases bval with
        | false =>
          simp at hpc1; rw [execB_ite, hce0]; simp only [execB_skip]
          have hpcFin : st1.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.ite c s1 .skip)).1)) := by
            rw [hpc1, htwEq]; simp only [lkm.totalSize_append]
          exact ⟨kc, st1, hrunC, hpcFin, hpresC.toFrameNoS0_all, hpresC.abi.s0.trans hs0, Nat.le_refl b,
            hm1, hf1'.toLive hs2Ag, hpmC, hhdr1⟩
        | true =>
          simp at hpc1; rw [execB_ite, hce0]; dsimp only
          have hlink1 : lkm.linkSpec ((pre ++ rC.1) ++ r1.1 ++ ([Asm.lbl endLbl] ++ post)) =
              .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
          have hres1 := ih1 rC.2 false (pre ++ rC.1) _ st1 hs1Ok hs1Args (by omega) hLeaf1
            (by rw [hlimIte] at hlim; exact hlim) (fun h => by cases h)
            hlink1 (by simpa [lkm.totalSize_append] using hpc1)
            (hpresC.abi.gp.trans hgp) (ht5.of_preserved hpresC) (hpresC.abi.sp.trans hsp) (hpresC.abi.s0.trans hs0) hm1 (hf1'.toLive hs1Ag) hhdr1
            (htco.of_step L hfl (by omega) htop hpresC.toFrameNoS0_all hpmC)
          exact hres1.prepend hfl htop kc hrunC hpresC.toFrameNoS0_all hpmC (Nat.le_refl b)
            (by rw [htwEq]; dsimp only [r1, rC]; simp only [lkm.totalSize_append, Nat.add_assoc])
  by_cases hs1Skip : s1 = .skip
  · subst hs1Skip
    by_cases hab2 : isAbort0Stmt s2 = true
    · have hs2Eq : s2 = .abort (.const 0) := eq_abort0_of_isAbort0Stmt hab2
      subst hs2Eq
      let abort0Lbl := s!"{pfx}_abort0stub"
      obtain ⟨ab0Pc, hab0Lbl, hstub⟩ := habort0 rfl
      have hcodeEq := compileSR_ite_skip_l_abort0 env.tab fl pfx lblId brkLbl retLbl isTail c
      rw [hcodeEq] at hlink ⊢
      have hcond := reg_evalCond_sim env L fl hfl lm loc' hal (by omega) htop c pre post 0 pfx lblId false abort0Lbl ab0Pc
        hcOk hVfC (by omega) hab0Lbl hlink (linkResolved_sub_pc64 env pre _ post hlink) st hpc hgp ht5 hsp hm hf'
      cases hce : _root_.L.evalC c { mem := lm, loc := loc' } with
      | error err =>
        have herr := evalC_err_eq_oob c { mem := lm, loc := loc' } hce
        subst herr; rw [hce] at hcond; rw [execB_ite, evalC_congr_eq_err hcAg hce]
        obtain ⟨k, r', hrun, hpc', hpres, hout⟩ := hcond
        exact stmtOutcomeR_of_err_oob htop ⟨k, r', hrun, hpc', hpres.abi,
          ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L (by omega) htop (Nat.zero_le _)) hout⟩
      | ok rc =>
        rcases rc with ⟨bval, stc⟩
        have hce0 := evalC_congr_eq_ok hcAg hce
        rw [hce] at hcond
        obtain ⟨kc, st1, hrunC, hpc1, hpresC, houtC⟩ := hcond
        have hm1 := ProgMemRel.of_tempSpanR (by omega) htop (Nat.zero_le _) houtC hm
        have hf1' := ProgFrameOkR.of_preserved_temp hfl hframeValid (Nat.zero_le _) (hpresC.mono (fun _ h => False.elim h)) houtC hf'
        have hpmC : ProgMemOutside (FnWriteMaskR L fl sp) st.mem st1.mem :=
          ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L (by omega) htop (Nat.zero_le _)) houtC
        have hhdr1 : TabHeaderOk L st1.mem := hhdr.of_fnWriteMaskR L hpmC
        cases bval with
        | false =>
          simp only [beq_self_eq_true, ↓reduceIte] at hpc1
          obtain ⟨kA, rA, hrunA, hpcA, ha0A, hpresA, hmemA⟩ := hstub st1 hpc1
          rw [execB_ite, hce0]; dsimp only; rw [execB_abort]
          exact ⟨kc + kA, rA, by rw [run_add, hrunC]; exact hrunA, hpcA, ha0A, hpresC.abi.toTramp.trans hpresA,
            ProgMemOutside.mono (fnWriteMaskR_sub_callWriteMask L (Nat.le_of_eq (callerSp_toNat_eq L htop).symm))
              (by rw [hmemA]; exact hpmC)⟩
        | true =>
          simp only [Bool.true_beq, Bool.false_eq_true, ↓reduceIte] at hpc1
          rw [execB_ite, hce0]; simp only [execB_skip]
          exact ⟨kc, st1, hrunC, hpc1, hpresC.toFrameNoS0_all, hpresC.abi.s0.trans hs0, Nat.le_refl b,
            hm1, hf1'.toLive hs1Ag, hpmC, hhdr1⟩
    · have hab2F : isAbort0Stmt s2 = false := Bool.eq_false_iff.mpr hab2
      let endLbl := s!"{pfx}_endif_{lblId}"
      let rC := compileCR env.tab fl 0 pfx (lblId + 1) c true endLbl
      let r2 := compileSR env.tab fl pfx rC.2 brkLbl retLbl false s2
      have hcodeEq : (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.ite c .skip s2)).1 =
          rC.1 ++ r2.1 ++ [Asm.lbl endLbl] := compileSR_ite_skip_l env.tab fl pfx lblId brkLbl retLbl isTail c s2 hs2Skip hab2F
      have htwEq : lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.ite c .skip s2)).1 =
          lkm.totalSize (rC.1 ++ r2.1) := by
        simp only [hcodeEq, lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero]
      rw [hcodeEq] at hlink
      have hendLbl : lookupLabel env.labels endLbl = some (lkm.totalSize (pre ++ rC.1 ++ r2.1)) :=
        linkResolved_lbl_lm lkm _ endLbl _ (by simpa [List.append_assoc] using hlink)
      have hlinkC : lkm.linkSpec (pre ++ rC.1 ++ (r2.1 ++ [Asm.lbl endLbl] ++ post)) =
          .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
      have hcond := reg_evalCond_sim env L fl hfl lm loc' hal (by omega) htop c pre _ 0 pfx (lblId + 1) true endLbl _
        hcOk hVfC (by omega) hendLbl hlinkC (linkResolved_sub_pc64 env pre rC.1 _ hlinkC) st hpc hgp ht5 hsp hm hf'
      cases hce : _root_.L.evalC c { mem := lm, loc := loc' } with
      | error err =>
        have herr := evalC_err_eq_oob c { mem := lm, loc := loc' } hce
        subst herr; rw [hce] at hcond; rw [execB_ite, evalC_congr_eq_err hcAg hce]
        obtain ⟨k, r', hrun, hpc', hpres, hout⟩ := hcond
        exact stmtOutcomeR_of_err_oob htop ⟨k, r', hrun, hpc', hpres.abi,
          ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L (by omega) htop (Nat.zero_le _)) hout⟩
      | ok rc =>
        rcases rc with ⟨bval, stc⟩
        have hce0 := evalC_congr_eq_ok hcAg hce
        rw [hce] at hcond
        obtain ⟨kc, st1, hrunC, hpc1, hpresC, houtC⟩ := hcond
        have hm1 := ProgMemRel.of_tempSpanR (by omega) htop (Nat.zero_le _) houtC hm
        have hf1' := ProgFrameOkR.of_preserved_temp hfl hframeValid (Nat.zero_le _) (hpresC.mono (fun _ h => False.elim h)) houtC hf'
        have hpmC : ProgMemOutside (FnWriteMaskR L fl sp) st.mem st1.mem :=
          ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L (by omega) htop (Nat.zero_le _)) houtC
        have hhdr1 : TabHeaderOk L st1.mem := hhdr.of_fnWriteMaskR L hpmC
        have hlimIte := stackNeedB_ite p b c .skip s2 { mem := lm, loc := loc }
        rw [hce0] at hlimIte
        cases bval with
        | true =>
          simp at hpc1; rw [execB_ite, hce0]; simp only [execB_skip]
          have hpcFin : st1.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.ite c .skip s2)).1)) := by
            rw [hpc1, htwEq]; simp only [lkm.totalSize_append]
          exact ⟨kc, st1, hrunC, hpcFin, hpresC.toFrameNoS0_all, hpresC.abi.s0.trans hs0, Nat.le_refl b,
            hm1, hf1'.toLive hs1Ag, hpmC, hhdr1⟩
        | false =>
          simp at hpc1; rw [execB_ite, hce0]; dsimp only
          have hlink2 : lkm.linkSpec ((pre ++ rC.1) ++ r2.1 ++ ([Asm.lbl endLbl] ++ post)) =
              .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
          have hres2 := ih2 rC.2 false (pre ++ rC.1) _ st1 hs2Ok hs2Args (by omega) hLeaf2
            (by rw [hlimIte] at hlim; exact hlim) (fun h => by cases h)
            hlink2 (by simpa [lkm.totalSize_append] using hpc1)
            (hpresC.abi.gp.trans hgp) (ht5.of_preserved hpresC) (hpresC.abi.sp.trans hsp) (hpresC.abi.s0.trans hs0) hm1 (hf1'.toLive hs2Ag) hhdr1
            (htco.of_step L hfl (by omega) htop hpresC.toFrameNoS0_all hpmC)
          exact hres2.prepend hfl htop kc hrunC hpresC.toFrameNoS0_all hpmC (Nat.le_refl b)
            (by rw [htwEq]; dsimp only [r2, rC]; simp only [lkm.totalSize_append, Nat.add_assoc])
  let elseLbl := s!"{pfx}_else_{lblId}"
  let endLbl := s!"{pfx}_endif_{lblId}"
  let rC := compileCR env.tab fl 0 pfx (lblId + 1) c false elseLbl
  let r1 := compileSR env.tab fl pfx rC.2 brkLbl retLbl false s1
  let r2 := compileSR env.tab fl pfx r1.2 brkLbl retLbl isTail s2
  let jEnd := if stmtMayFallthrough s1 then [Asm.j endLbl] else []
  have hcodeEq : (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.ite c s1 s2)).1 =
      rC.1 ++ r1.1 ++ jEnd ++ [Asm.lbl elseLbl] ++ r2.1 ++ [Asm.lbl endLbl] :=
    compileSR_ite_general env.tab fl pfx lblId brkLbl retLbl isTail c s1 s2 hs1Skip hs2Skip
  have htwEq : lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.ite c s1 s2)).1 =
      lkm.totalSize (rC.1 ++ r1.1 ++ jEnd ++ [Asm.lbl elseLbl] ++ r2.1) := by
    simp only [hcodeEq, lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero]
  rw [hcodeEq] at hlink
  have helseLbl : lookupLabel env.labels elseLbl = some (lkm.totalSize (pre ++ rC.1 ++ r1.1 ++ jEnd)) :=
    linkResolved_lbl_lm lkm _ elseLbl _ (by simpa [List.append_assoc] using hlink)
  have hendLbl : lookupLabel env.labels endLbl = some (lkm.totalSize (pre ++ rC.1 ++ r1.1 ++ jEnd ++ [Asm.lbl elseLbl] ++ r2.1)) :=
    linkResolved_lbl_lm lkm _ endLbl _ (by simpa [List.append_assoc] using hlink)
  have hlinkC : lkm.linkSpec (pre ++ rC.1 ++ (r1.1 ++ jEnd ++ [Asm.lbl elseLbl] ++ r2.1 ++ [Asm.lbl endLbl] ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
  have hcond := reg_evalCond_sim env L fl hfl lm loc' hal (by omega) htop c pre _ 0 pfx (lblId + 1) false elseLbl _
    hcOk hVfC (by omega) helseLbl hlinkC (linkResolved_sub_pc64 env pre rC.1 _ hlinkC) st hpc hgp ht5 hsp hm hf'
  cases hce : _root_.L.evalC c { mem := lm, loc := loc' } with
  | error err =>
    have herr := evalC_err_eq_oob c { mem := lm, loc := loc' } hce
    subst herr; rw [hce] at hcond; rw [execB_ite, evalC_congr_eq_err hcAg hce]
    obtain ⟨k, r', hrun, hpc', hpres, hout⟩ := hcond
    exact stmtOutcomeR_of_err_oob htop ⟨k, r', hrun, hpc', hpres.abi,
      ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L (by omega) htop (Nat.zero_le _)) hout⟩
  | ok rc =>
    rcases rc with ⟨bval, stc⟩
    have hce0 := evalC_congr_eq_ok hcAg hce
    rw [hce] at hcond
    obtain ⟨kc, st1, hrunC, hpc1, hpresC, houtC⟩ := hcond
    have hm1 := ProgMemRel.of_tempSpanR (by omega) htop (Nat.zero_le _) houtC hm
    have hf1' := ProgFrameOkR.of_preserved_temp hfl hframeValid (Nat.zero_le _) (hpresC.mono (fun _ h => False.elim h)) houtC hf'
    have hpmC : ProgMemOutside (FnWriteMaskR L fl sp) st.mem st1.mem :=
      ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L (by omega) htop (Nat.zero_le _)) houtC
    have hhdr1 : TabHeaderOk L st1.mem := hhdr.of_fnWriteMaskR L hpmC
    have hlimIte := stackNeedB_ite p b c s1 s2 { mem := lm, loc := loc }
    rw [hce0] at hlimIte
    cases bval with
    | true =>
      simp at hpc1
      have hlink1 : lkm.linkSpec ((pre ++ rC.1) ++ r1.1 ++ (jEnd ++ [Asm.lbl elseLbl] ++ r2.1 ++ [Asm.lbl endLbl] ++ post)) =
          .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
      have hres1 := ih1 rC.2 false (pre ++ rC.1) _ st1 hs1Ok hs1Args (by omega) hLeaf1
        (by rw [hlimIte] at hlim; exact hlim) (fun h => by cases h)
        hlink1 (by simpa [lkm.totalSize_append] using hpc1)
        (hpresC.abi.gp.trans hgp) (ht5.of_preserved hpresC) (hpresC.abi.sp.trans hsp) (hpresC.abi.s0.trans hs0) hm1 (hf1'.toLive hs1Ag) hhdr1
        (htco.of_step L hfl (by omega) htop hpresC.toFrameNoS0_all hpmC)
      rw [execB_ite, hce0]; dsimp only
      cases hx1 : execB p b s1 { mem := lm, loc := loc } with
      | error err =>
        rw [hx1] at hres1
        exact hres1.prepend_err htop kc hrunC hpresC.toFrameNoS0_all hpmC
      | ok res1 =>
        rcases res1 with ⟨sig1, st1', b1'⟩
        rw [hx1] at hres1
        cases sig1 with
        | normal =>
          cases hmf : stmtMayFallthrough s1 with
          | false =>
            exact False.elim (execB_not_normal_of_not_fallthrough p s1 b { mem := lm, loc := loc } st1' b1' hmf hx1)
          | true =>
            obtain ⟨k1, r1', hrun1, hpc1'', hpres1, hs0_1, hb1, hm1', hf1'', hout1, hhdr1'⟩ := hres1
            have hjEq : jEnd = [Asm.j endLbl] := by simp [jEnd, hmf]
            have hpc1_mid : r1'.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ rC.1 ++ r1.1)) := by
              rw [hpc1'']; dsimp only [r1, rC, elseLbl]; simp only [lkm.totalSize_append, Nat.add_assoc]
            have hlinkJ : lkm.linkSpec ((pre ++ rC.1 ++ r1.1) ++ [Asm.j endLbl] ++ ([Asm.lbl elseLbl] ++ r2.1 ++ [Asm.lbl endLbl] ++ post)) =
                .ok (env.code, env.labels) := by rw [hjEq] at hlink; simpa [List.append_assoc] using hlink
            have hpcJ : 4 * (lkm.totalSize (pre ++ rC.1 ++ r1.1) + lkm.itemSize (.j endLbl)) < 2 ^ 64 := by
              simpa [Asm.j, lkm.totalSize_singleton] using linkResolved_sub_pc64 env (pre ++ rC.1 ++ r1.1) [Asm.j endLbl] _ hlinkJ
            obtain ⟨kJ, rJ, hrunJ, hpcJ', hothJ, _, hmemJ⟩ :=
              prog_step_j env (pre ++ rC.1 ++ r1.1) _ endLbl _ hendLbl hlinkJ hpcJ r1' hpc1_mid
            have hpcFin : rJ.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.ite c s1 s2)).1)) := by
              rw [hpcJ', htwEq]; simp only [lkm.totalSize_append, Nat.add_assoc]
            exact ⟨kc + k1 + kJ, rJ, by rw [run_add, run_add, hrunC]; dsimp only; rw [hrun1]; exact hrunJ,
              hpcFin, hpresC.toFrameNoS0_all.trans (hpres1.trans (PreservedFrameNoS0.of_other_t6 hothJ)),
              (hothJ _ (by decide)).trans hs0_1, hb1,
              (by rw [hmemJ]; exact hm1'),
              hf1''.of_other_t6 hfl hframeValid hothJ hmemJ,
              hpmC.trans (by rw [hmemJ]; exact hout1), (by rw [hmemJ]; exact hhdr1')⟩
        | brk =>
          exact hres1.prepend_brk kc hrunC hpresC.toFrameNoS0_all hpmC (Nat.le_refl b)
        | ret vs =>
          exact hres1.prepend_ret hfl htop kc hrunC hpresC.toFrameNoS0_all hpmC (Nat.le_refl b)
    | false =>
      simp at hpc1; rw [execB_ite, hce0]; dsimp only
      let pre2 := pre ++ rC.1 ++ r1.1 ++ jEnd ++ [Asm.lbl elseLbl]
      have hlink2 : lkm.linkSpec (pre2 ++ r2.1 ++ ([Asm.lbl endLbl] ++ post)) =
          .ok (env.code, env.labels) := by simpa [pre2, List.append_assoc] using hlink
      have hpc2' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre2) := by
        rw [hpc1]
        exact congrArg (fun n => BitVec.ofNat 64 (4 * n))
          (by simp only [pre2, lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero, Nat.add_assoc])
      have hpcEndEq : lkm.totalSize pre2 + lkm.totalSize r2.1 =
          lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.ite c s1 s2)).1 := by
        rw [htwEq]; dsimp only [pre2, r2, r1, rC, elseLbl, endLbl, jEnd]
        simp only [lkm.totalSize_append, Nat.add_assoc]
      have hres2 := ih2 r1.2 isTail pre2 _ st1 hs2Ok hs2Args (by omega) hLeaf2
        (by rw [hlimIte] at hlim; exact hlim)
        (fun ht => by rw [hpcEndEq]; exact hTail ht)
        hlink2 hpc2' (hpresC.abi.gp.trans hgp) (ht5.of_preserved hpresC) (hpresC.abi.sp.trans hsp) (hpresC.abi.s0.trans hs0) hm1 (hf1'.toLive hs2Ag) hhdr1
        (htco.of_step L hfl (by omega) htop hpresC.toFrameNoS0_all hpmC)
      exact hres2.prepend hfl htop kc hrunC hpresC.toFrameNoS0_all hpmC (Nat.le_refl b) hpcEndEq

private theorem prog_while_step_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab) (p : _root_.L.Prog)
    (fl : FrameLayout) (hfl : FrameLayoutOk fl) (b : Nat) (lm : _root_.L.Mem) (loc : _root_.L.Locals)
    (sp : BitVec 64) (pfx : String) (lblId : Nat) (brkLbl : Option String) (retLbl : String) (isTail : Bool)
    (c : _root_.L.Cond) (body : _root_.L.Stmt)
    (na nb : Var → Bool) (tco : TcoCtx)
    (hcOk : condOkB env.tab fl.nlocals c = true)
    (hVfC : CondVarsInFrame fl c)
    (hbOk : stmtOkB env.tab p fl.nlocals true body = true)
    (hbArgs : stmtArgsOkB p body = true)
    (hTmp : max (usedTempsCond c) (usedTempsStmtR fl.isLeaf fl.alloc body) ≤ fl.usedTemps)
    (hLeaf : fl.isLeaf = true → stmtHasCall (.while c body) = false)
    (_hb64 : b < 2 ^ 64) (hal : isAligned sp 8 = true)
    (hlim : L.stackLimit.toNat + stackNeedB p b (.while c body) { mem := lm, loc := loc } ≤ sp.toNat)
    (htop : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.while c body)).1 ++ post) =
      .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hs0 : st.getReg AbiReg.s0 = BitVec.ofNat 64 b)
    (hm : ProgMemRel env.tab L st.mem lm)
    (hf : ProgFrameOkLive L fl sp st loc (fun x => (stmtVarCallFree x (.while c body) (na x) (nb x)).1))
    (hhdr : TabHeaderOk L st.mem) (htco : TcoStateOk fl sp tco st)
    (ihBody : ∀ (preB postB : List AsmItem) (stB : State),
      stmtOkB env.tab p fl.nlocals true body = true →
      stmtArgsOkB p body = true →
      usedTempsStmtR fl.isLeaf fl.alloc body ≤ fl.usedTemps →
      (fl.isLeaf = true → stmtHasCall body = false) →
      L.stackLimit.toNat + stackNeedB p b body { mem := lm, loc := loc } ≤ sp.toNat →
      lookupLabel env.labels s!"{pfx}_endw_{lblId}" =
        some (lkm.totalSize (pre ++ [Asm.lbl s!"{pfx}_while_{lblId}"] ++
          (compileCR env.tab fl 0 pfx (lblId + 1) c false s!"{pfx}_endw_{lblId}").1 ++
          (compileSR env.tab fl pfx (compileCR env.tab fl 0 pfx (lblId + 1) c false s!"{pfx}_endw_{lblId}").2 (some s!"{pfx}_endw_{lblId}") retLbl false body).1 ++
          [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel, Asm.addi AbiReg.s0 AbiReg.s0 (-1#12), Asm.j s!"{pfx}_while_{lblId}"])) →
      lkm.linkSpec (preB ++ (compileSR env.tab fl pfx (compileCR env.tab fl 0 pfx (lblId + 1) c false s!"{pfx}_endw_{lblId}").2 (some s!"{pfx}_endw_{lblId}") retLbl false body).1 ++ postB) = .ok (env.code, env.labels) →
      stB.pc = BitVec.ofNat 64 (4 * lkm.totalSize preB) →
      stB.getReg AbiReg.gp = L.T → T5GpOk L fl stB → stB.getReg AbiReg.sp = sp →
      stB.getReg AbiReg.s0 = BitVec.ofNat 64 b →
      ProgMemRel env.tab L stB.mem lm →
      ProgFrameOkLive L fl sp stB loc (fun x => (stmtVarCallFree x body (stmtVarCallFree x (.while c body) (na x) (nb x)).1 (na x)).1) →
      TabHeaderOk L stB.mem → TcoStateOk fl sp tco stB →
      StmtOutcomeR env L fl sp b stB retLbl (some s!"{pfx}_endw_{lblId}")
        (lkm.totalSize preB + lkm.totalSize (compileSR env.tab fl pfx (compileCR env.tab fl 0 pfx (lblId + 1) c false s!"{pfx}_endw_{lblId}").2 (some s!"{pfx}_endw_{lblId}") retLbl false body).1)
        (fun x => (stmtVarCallFree x (.while c body) (na x) (nb x)).1) na tco
        (execB p b body { mem := lm, loc := loc }))
    (ihNext : ∀ (b1' : Nat) (st2 : _root_.L.St) (stLoop : State),
      b1' < b →
      L.stackLimit.toNat + stackNeedB p b1' (.while c body) st2 ≤ sp.toNat →
      stLoop.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
      stLoop.getReg AbiReg.gp = L.T → T5GpOk L fl stLoop → stLoop.getReg AbiReg.sp = sp →
      stLoop.getReg AbiReg.s0 = BitVec.ofNat 64 b1' →
      ProgMemRel env.tab L stLoop.mem st2.mem →
      ProgFrameOkLive L fl sp stLoop st2.loc (fun x => (stmtVarCallFree x (.while c body) (na x) (nb x)).1) →
      TabHeaderOk L stLoop.mem → TcoStateOk fl sp tco stLoop →
      StmtOutcomeR env L fl sp b1' stLoop retLbl brkLbl
        (lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.while c body)).1) na nb tco
        (execB p b1' (.while c body) st2)) :
    StmtOutcomeR env L fl sp b st retLbl brkLbl
      (lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.while c body)).1) na nb tco
      (execB p b (.while c body) { mem := lm, loc := loc }) := by
  let nW : Var → Bool := fun x => (stmtVarCallFree x (.while c body) (na x) (nb x)).1
  let loc' := ghostLoc fl sp st loc nW
  have hf' : ProgFrameOkR L fl sp st loc' := ghostLoc_frameOk hf
  have hagW : ∀ x, nW x = true → loc' x = loc x := ghostLoc_agree fl sp st loc nW
  have hcAg : ∀ x, condUsesVar x c = true → loc' x = loc x :=
    fun x hx => hagW x (stmtVarCallFree_while_cond x c body (na x) (nb x) hx)
  let loopLbl := s!"{pfx}_while_{lblId}"
  let endLbl := s!"{pfx}_endw_{lblId}"
  let rC := compileCR env.tab fl 0 pfx (lblId + 1) c false endLbl
  let rB := compileSR env.tab fl pfx rC.2 (some endLbl) retLbl false body
  let tailCode : List AsmItem :=
    [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
     Asm.addi AbiReg.s0 AbiReg.s0 (-1#12),
     Asm.j loopLbl,
     Asm.lbl endLbl]
  have hcodeEq : (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.while c body)).1 =
      [Asm.lbl loopLbl] ++ rC.1 ++ rB.1 ++ tailCode := by
    simp [compileSR, loopLbl, endLbl, rC, rB, tailCode, List.append_assoc]
  have htwEq : lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.while c body)).1 =
      lkm.totalSize (rC.1 ++ rB.1 ++ [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
        Asm.addi AbiReg.s0 AbiReg.s0 (-1#12), Asm.j loopLbl]) := by
    rw [hcodeEq]
    have htwLbl : lkm.totalSize [Asm.lbl loopLbl] = 0 := by simp only [Asm.lbl, lkm.totalSize_label]
    have htwTail : lkm.totalSize tailCode = lkm.totalSize [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
        Asm.addi AbiReg.s0 AbiReg.s0 (-1#12), Asm.j loopLbl] := by
      rw [show tailCode = [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
          Asm.addi AbiReg.s0 AbiReg.s0 (-1#12), Asm.j loopLbl] ++ [Asm.lbl endLbl] from rfl,
          lkm.totalSize_append, Asm.lbl, lkm.totalSize_label, Nat.add_zero]
    simp only [lkm.totalSize_append, htwLbl, htwTail, Nat.zero_add]
  rw [hcodeEq] at hlink
  have hloopLbl : lookupLabel env.labels loopLbl = some (lkm.totalSize pre) :=
    linkResolved_lbl_lm lkm pre loopLbl _ (by simpa [List.append_assoc] using hlink)
  have hendLbl : lookupLabel env.labels endLbl = some (lkm.totalSize (pre ++ [Asm.lbl loopLbl] ++ rC.1 ++ rB.1 ++
      [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel, Asm.addi AbiReg.s0 AbiReg.s0 (-1#12), Asm.j loopLbl])) :=
    linkResolved_lbl_lm lkm _ endLbl _ (by simpa [tailCode, List.append_assoc] using hlink)
  have hlinkC : lkm.linkSpec ((pre ++ [Asm.lbl loopLbl]) ++ rC.1 ++ (rB.1 ++ tailCode ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
  have hpc0' : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ [Asm.lbl loopLbl])) := by
    simpa [lkm.totalSize_append, show lkm.totalSize [Asm.lbl loopLbl] = 0 from by simp only [Asm.lbl, lkm.totalSize_label]] using hpc
  have hcond := reg_evalCond_sim env L fl hfl lm loc' hal (by omega) htop c (pre ++ [Asm.lbl loopLbl]) _ 0 pfx (lblId + 1)
    false endLbl _ hcOk hVfC (by omega) hendLbl hlinkC (linkResolved_sub_pc64 env (pre ++ [Asm.lbl loopLbl]) rC.1 _ hlinkC)
    st hpc0' hgp ht5 hsp hm hf'
  cases hce : _root_.L.evalC c { mem := lm, loc := loc' } with
  | error err =>
    have herr := evalC_err_eq_oob c { mem := lm, loc := loc' } hce
    subst herr; rw [hce] at hcond; rw [execB_while, evalC_congr_eq_err hcAg hce]
    obtain ⟨k, r', hrun, hpc', hpres, hout⟩ := hcond
    exact stmtOutcomeR_of_err_oob htop ⟨k, r', hrun, hpc', hpres.abi,
      ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L (by omega) htop (Nat.zero_le _)) hout⟩
  | ok rc =>
    rcases rc with ⟨bval, stc⟩
    have hce0 := evalC_congr_eq_ok hcAg hce
    rw [hce] at hcond
    obtain ⟨kc, st1, hrunC, hpc1, hpresC, houtC⟩ := hcond
    have hframeValid : (frameSpanR fl sp).valid := Nat.le_trans htop L.hStackValid
    have hm1 := ProgMemRel.of_tempSpanR (by omega) htop (Nat.zero_le _) houtC hm
    have hf1' := ProgFrameOkR.of_preserved_temp hfl hframeValid (Nat.zero_le _) (hpresC.mono (fun _ h => False.elim h)) houtC hf'
    have hpmC : ProgMemOutside (FnWriteMaskR L fl sp) st.mem st1.mem :=
      ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L (by omega) htop (Nat.zero_le _)) houtC
    have hhdr1 : TabHeaderOk L st1.mem := hhdr.of_fnWriteMaskR L hpmC
    cases bval with
    | false =>
      simp only [beq_self_eq_true, ↓reduceIte] at hpc1
      rw [execB_while, hce0]
      have hpcFin : st1.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.while c body)).1)) := by
        rw [hpc1, htwEq]
        simp only [lkm.totalSize_append, show lkm.totalSize [Asm.lbl loopLbl] = 0 from by simp only [Asm.lbl, lkm.totalSize_label], Nat.add_zero, Nat.add_assoc]
      exact ⟨kc, st1, hrunC, hpcFin, hpresC.toFrameNoS0_all, hpresC.abi.s0.trans hs0, Nat.le_refl b,
        hm1, hf1'.toLive (fun x hx => hagW x (stmtVarCallFree_while_na x c body (na x) (nb x) hx)), hpmC, hhdr1⟩
    | true =>
      simp only [Bool.true_beq, Bool.false_eq_true, ↓reduceIte] at hpc1
      have hlimW := stackNeedB_while p b c body { mem := lm, loc := loc }
      rw [hce0] at hlimW
      have hlimBody : L.stackLimit.toNat + stackNeedB p b body { mem := lm, loc := loc } ≤ sp.toNat := by
        cases hxb' : execB p b body { mem := lm, loc := loc } with
        | error _ => simp only [hxb'] at hlimW; rw [hlimW] at hlim; exact hlim
        | ok resB =>
          rcases resB with ⟨sigB, stB, bB⟩
          cases sigB with
          | brk => simp only [hxb'] at hlimW; rw [hlimW] at hlim; exact hlim
          | ret _ => simp only [hxb'] at hlimW; rw [hlimW] at hlim; exact hlim
          | normal =>
            cases bB with
            | zero => simp only [hxb'] at hlimW; rw [hlimW] at hlim; exact hlim
            | succ b1' => simp only [hxb'] at hlimW; omega
      have hlinkB : lkm.linkSpec ((pre ++ [Asm.lbl loopLbl] ++ rC.1) ++ rB.1 ++ (tailCode ++ post)) =
          .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
      have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ [Asm.lbl loopLbl] ++ rC.1)) := by
        rw [hpc1]; dsimp only [rC, endLbl]
        have htwL : lkm.totalSize [Asm.lbl loopLbl] = 0 := by simp only [Asm.lbl, lkm.totalSize_label]
        simp only [lkm.totalSize_append, htwL, Nat.add_zero]
      have hresB := ihBody (pre ++ [Asm.lbl loopLbl] ++ rC.1) (tailCode ++ post) st1
        hbOk hbArgs (by omega) (fun hl => by simpa [stmtHasCall] using hLeaf hl) hlimBody hendLbl hlinkB hpc1'
        (hpresC.abi.gp.trans hgp) (ht5.of_preserved hpresC) (hpresC.abi.sp.trans hsp) (hpresC.abi.s0.trans hs0) hm1
        (hf1'.toLive (fun x hx => hagW x (stmtVarCallFree_while_body_live x c body (na x) (nb x) hx))) hhdr1
        (htco.of_step L hfl (by omega) htop hpresC.toFrameNoS0_all hpmC)
      rw [execB_while, hce0]; dsimp only
      cases hxb : execB p b body { mem := lm, loc := loc } with
      | error err =>
        rw [hxb] at hresB
        exact hresB.prepend_err htop kc hrunC hpresC.toFrameNoS0_all hpmC
      | ok resB =>
        rcases resB with ⟨sigB, st2, b1⟩
        rw [hxb] at hresB
        cases sigB with
        | brk =>
          obtain ⟨tgt, hbrkEq, tgtPc, kb, rb, hlkp, hrunB, hpcB, hpresB, hs0B, hb1, hmB, hfB, houtB, hhdrB⟩ := hresB
          simp only [Option.some.injEq] at hbrkEq; subst hbrkEq
          rw [hendLbl] at hlkp
          have htgtEq := Option.some.inj hlkp.symm
          have hpcFin : rb.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.while c body)).1)) := by
            rw [hpcB, htgtEq, htwEq]
            simp only [lkm.totalSize_append, show lkm.totalSize [Asm.lbl loopLbl] = 0 from by simp only [Asm.lbl, lkm.totalSize_label], Nat.add_zero, Nat.add_assoc]
          exact ⟨kc + kb, rb, by rw [run_add, hrunC]; exact hrunB, hpcFin,
            hpresC.toFrameNoS0_all.trans hpresB, hs0B, hb1, hmB, hfB, hpmC.trans houtB, hhdrB⟩
        | ret vs =>
          exact hresB.prepend_ret hfl htop kc hrunC hpresC.toFrameNoS0_all hpmC (Nat.le_refl b)
        | normal =>
          obtain ⟨kb, rb, hrunB, hpcB, hpresB, hs0B, hb1, hmB, hfB, houtB, hhdrB⟩ := hresB
          let preT := pre ++ [Asm.lbl loopLbl] ++ rC.1 ++ rB.1
          have hlinkBeq : lkm.linkSpec (preT ++ [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel] ++
              ([Asm.addi AbiReg.s0 AbiReg.s0 (-1#12), Asm.j loopLbl, Asm.lbl endLbl] ++ post)) =
              .ok (env.code, env.labels) := by simpa [preT, tailCode, List.append_assoc] using hlink
          have hpcB' : rb.pc = BitVec.ofNat 64 (4 * lkm.totalSize preT) := by
            rw [hpcB]; dsimp only [preT, rB, rC, loopLbl, endLbl]; simp only [lkm.totalSize_append, Nat.add_assoc]
          have hbr := run_br_step env preT _ .beq AbiReg.s0 AbiReg.zero exhaustedLabel env.exhaustedTarget
            env.hexhaustedLbl (by decide) hlinkBeq rb hpcB'
          cases b1 with
          | zero =>
            have hcond0 : evalBranch .beq (rb.getReg AbiReg.s0) (rb.getReg AbiReg.zero) = true := by
              rw [hs0B, getReg_zero]; rfl
            obtain ⟨kBr, rEx, _, hrunEx, hpcEx, _, hpresBr, hmemBr⟩ := hbr
            have hpt := (hpresC.toFrameNoS0_all.trans hpresB).toTramp
            exact ⟨kc + kb + kBr, rEx,
              by rw [run_add, run_add, hrunC]; dsimp only; rw [hrunB]; exact hrunEx,
              by rw [hpcEx, hcond0]; rfl,
              ⟨hpresBr.gp.trans hpt.gp, hpresBr.s2.trans hpt.s2⟩,
              ProgMemOutside.mono (fnWriteMaskR_sub_callWriteMask L (Nat.le_of_eq (callerSp_toNat_eq L htop).symm))
                (by rw [hmemBr]; exact hpmC.trans houtB)⟩
          | succ b1' =>
            have hlt64 : b1' + 1 < 2 ^ 64 := by omega
            have hne0 : BitVec.ofNat 64 (b1' + 1) ≠ 0#64 :=
              BitVec.ofNat_ne_zero_of_lt (Nat.succ_pos b1') hlt64
            have hcond1 : evalBranch .beq (rb.getReg AbiReg.s0) (rb.getReg AbiReg.zero) = false := by
              rw [hs0B, getReg_zero]; simp [evalBranch, hne0]
            obtain ⟨kBr, r1s, _, hrun1s, hpc1sBr, hoth1s, _, hmem1s⟩ := hbr
            let preT1 := preT ++ [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel]
            have hlinkAdd : lkm.linkSpec (preT1 ++ [Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++
                ([Asm.j loopLbl, Asm.lbl endLbl] ++ post)) = .ok (env.code, env.labels) := by
              simpa [preT1, preT, tailCode, List.append_assoc] using hlink
            have hpc1s : r1s.pc = BitVec.ofNat 64 (4 * lkm.totalSize preT1) := by
              rw [hpc1sBr, hcond1]; simp only [Bool.false_eq_true, ↓reduceIte]
              exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (lkm.totalSize_append preT _).symm
            obtain ⟨hrun2s, hpc2s, hs0_2s, hoth2s, hmem2s⟩ :=
              run_aluImm_rd_step env preT1 _ .addi AbiReg.s0 AbiReg.s0 (-1#12) (by decide) hlinkAdd r1s hpc1s
            let r2s := stepReg r1s AbiReg.s0 (evalAluImm .addi (r1s.getReg AbiReg.s0) (-1#12))
              (BitVec.ofNat 64 (4 * (lkm.totalSize preT1 + 1)))
            have hs0Val : r2s.getReg AbiReg.s0 = BitVec.ofNat 64 b1' := by
              rw [hs0_2s]; change r1s.getReg AbiReg.s0 + sextImm12 (-1#12) = BitVec.ofNat 64 b1'
              rw [hoth1s _ (by decide), hs0B]; exact BitVec.ofNat_sub_one_eq_add_neg1 hlt64
            let preT2 := preT1 ++ [Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)]
            have hlinkJ : lkm.linkSpec (preT2 ++ [Asm.j loopLbl] ++ ([Asm.lbl endLbl] ++ post)) =
                .ok (env.code, env.labels) := by
              simpa [preT2, preT1, preT, tailCode, List.append_assoc] using hlink
            have hpcJ64 : 4 * (lkm.totalSize preT2 + lkm.itemSize (.j loopLbl)) < 2 ^ 64 := by
              simpa [Asm.j, lkm.totalSize_singleton] using linkResolved_sub_pc64 env preT2 [Asm.j loopLbl] _ hlinkJ
            have hpc2s' : r2s.pc = BitVec.ofNat 64 (4 * lkm.totalSize preT2) := by
              rw [hpc2s]; dsimp only [preT2]; simp only [lkm.totalSize_append, Asm.addi, lkm.totalSize_instr]
            obtain ⟨kJ, rLoop, hrunLoop, hpcLoop, hothLoop, _, hmemLoop⟩ :=
              prog_step_j env preT2 _ loopLbl (lkm.totalSize pre) hloopLbl hlinkJ hpcJ64 r2s hpc2s'
            simp only [hxb] at hlimW
            have hothTail : ∀ r, r ∈ allowedRegs true → rLoop.getReg r = rb.getReg r := fun r hr =>
              (hothLoop r ⟨allowedRegs_ne_t6 hr, allowedRegs_ne_s1 hr⟩).trans
                ((hoth2s r (allowedRegs_ne_s0 hr)).trans (hoth1s r ⟨allowedRegs_ne_t6 hr, allowedRegs_ne_s1 hr⟩))
            have hpresTail : PreservedFrameNoS0 fl rb rLoop :=
              ⟨⟨(hothLoop _ (by decide)).trans ((hoth2s _ (by decide)).trans (hoth1s _ (by decide))),
                (hothLoop _ (by decide)).trans ((hoth2s _ (by decide)).trans (hoth1s _ (by decide))),
                (hothLoop _ (by decide)).trans ((hoth2s _ (by decide)).trans (hoth1s _ (by decide)))⟩,
               fun _ => (hothLoop _ (by decide)).trans ((hoth2s _ (by decide)).trans (hoth1s _ (by decide))),
               fun _ => (hothLoop _ (by decide)).trans ((hoth2s _ (by decide)).trans (hoth1s _ (by decide))),
               fun r hr _ => hothTail r (allowedRegs_sub_true hr)⟩
            have hpresMid : PreservedFrameNoS0 fl st rLoop :=
              (hpresC.toFrameNoS0_all.trans hpresB).trans hpresTail
            have hmemLoopEq : rLoop.mem = rb.mem := hmemLoop.trans (hmem2s.trans hmem1s)
            have hfLoop : ProgFrameOkLive L fl sp rLoop st2.loc nW := by
              intro x hx hlive
              have hfx := hfB x hx hlive
              cases hlx : fl.alloc.lookup x with
              | some r =>
                rw [hlx] at hfx; dsimp only at hfx ⊢
                rw [hothTail r (regAllocValid_lookup hfl.valid hlx).2.1, hfx]
              | none =>
                rw [hlx] at hfx; dsimp only at hfx ⊢
                rw [hmemLoopEq]; exact hfx
            have hs0Loop : rLoop.getReg AbiReg.s0 = BitVec.ofNat 64 b1' :=
              (hothLoop _ (by decide)).trans hs0Val
            have houtLoop : ProgMemOutside (FnWriteMaskR L fl sp) st.mem rLoop.mem := by
              rw [hmemLoopEq]; exact hpmC.trans houtB
            have hnext := ihNext b1' st2 rLoop (by omega) (by omega) hpcLoop
              (hpresMid.abi.gp.trans hgp) (ht5.of_frameNoS0 hpresMid) (hpresMid.abi.sp.trans hsp) hs0Loop
              (by rw [hmemLoopEq]; exact hmB) hfLoop (by rw [hmemLoopEq]; exact hhdrB)
              (htco.of_step L hfl (by omega) htop hpresMid houtLoop)
            have hrunUp : RV64.run env.rom (kc + kb + kBr + 1 + kJ) st = .cont rLoop := by
              rw [run_add, run_add, run_add, run_add, hrunC]
              dsimp only; rw [hrunB]; dsimp only; rw [hrun1s]; dsimp only; rw [hrun2s]; exact hrunLoop
            exact hnext.prepend hfl htop _ hrunUp hpresMid houtLoop (by omega) rfl

theorem resReg_ne_t6 (i : Nat) : resReg i ≠ AbiReg.t6 := by
  match i with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | _ + 7 => simp [resReg]; decide

private theorem loadTempArgsLoop_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (fl : FrameLayout) {sp : BitVec 64} (hal : isAligned sp 8 = true)
    (vs : List _root_.L.Word) :
    ∀ (n : Nat), n ≤ min vs.length maxRes →
      ∀ (pre post : List AsmItem),
        lkm.linkSpec (pre ++ ((List.range n).flatMap fun i =>
          loadMemOff .ld (resReg i) AbiReg.sp AbiReg.t0 (fl.tempSlotOff i)) ++ post) =
          .ok (env.code, env.labels) →
      ∀ (st : State),
        st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
        st.getReg AbiReg.sp = sp →
        (∀ j (hj : j < vs.length), readWord64 st.mem (sp + BitVec.ofInt 64 (fl.tempSlotOff j)) = (vs[j]'hj).toBitVec) →
        ∃ k st',
          RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize ((List.range n).flatMap fun i =>
            loadMemOff .ld (resReg i) AbiReg.sp AbiReg.t0 (fl.tempSlotOff i)))) ∧
          PreservedRegs st st' ∧
          st'.getReg AbiReg.ra = st.getReg AbiReg.ra ∧
          (∀ r ∈ calleeSavedBank, st'.getReg r = st.getReg r) ∧
          st'.mem = st.mem ∧
          (∀ j, j < n → st'.getReg (resReg j) = (vs[j]!).toBitVec) := by
  intro n
  induction n with
  | zero =>
    intro _ pre post _ st hpc _ _
    exact ⟨0, st, rfl, by simp [lkm.totalSize_nil, hpc], PreservedRegs.refl st, rfl,
      fun _ _ => rfl, rfl, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro hle pre post hlink st hpc hsp hslots
    have hsplit : (List.range (n + 1)).flatMap (fun i => loadMemOff .ld (resReg i) AbiReg.sp AbiReg.t0 (fl.tempSlotOff i)) =
        (List.range n).flatMap (fun i => loadMemOff .ld (resReg i) AbiReg.sp AbiReg.t0 (fl.tempSlotOff i)) ++
        loadMemOff .ld (resReg n) AbiReg.sp AbiReg.t0 (fl.tempSlotOff n) := by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rw [hsplit] at hlink ⊢
    have ⟨hl1, hl2⟩ := linkResolved_mid_split lkm pre _ _ post hlink
    obtain ⟨k1, st1, hrun1, hpc1, hpres1, hra1, hcal1, hmem1, hregs1⟩ :=
      ih (by omega) pre _ hl1 st hpc hsp hslots
    have hsp1 : st1.getReg AbiReg.sp = sp := hpres1.sp.trans hsp
    have halN : isAligned (st1.getReg AbiReg.sp + BitVec.ofInt 64 (fl.tempSlotOff n)) 8 = true := by
      rw [hsp1, tempSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hal _
    have hrn := resReg_ne_preserved n
    obtain ⟨st2, hrun2, hoth2, hrd2, hmem2, hpc2⟩ :=
      loadMemOff_ld_correct_lm lkm env.hrom (pre ++ _) post (resReg n) AbiReg.sp AbiReg.t0
        (resReg_ne_zero n) (by decide) (by decide) (fl.tempSlotOff n) hl2
        (linkResolved_sub_pc64 env _ _ post hl2) st1 (by simpa [lkm.totalSize_append] using hpc1) halN
    have hpres2 : PreservedRegs st1 st2 :=
      ⟨hoth2 _ hrn.1.symm (by decide), hoth2 _ hrn.2.1.symm (by decide),
       hoth2 _ hrn.2.2.1.symm (by decide),
       hoth2 _ hrn.2.2.2.2.1.symm (by decide)⟩
    refine ⟨_, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
      by simpa [lkm.totalSize_append, Nat.add_assoc] using hpc2,
      hpres1.trans hpres2, (hoth2 _ (resReg_ne_ra n).symm (by decide)).trans hra1,
      fun r hr => (hoth2 r (nonLeaf_allowed_ne_resReg hr n) (allowedRegs_ne_t0 (isLeaf := false) hr)).trans (hcal1 r hr),
      hmem2.trans hmem1, ?_⟩
    intro j hj
    by_cases hjn : j = n
    · subst hjn
      have hnv : j < vs.length := by omega
      rw [hrd2, hmem1, hsp1, hslots j hnv, getElem!_pos vs j hnv]
    · rw [hoth2 (resReg j) (resReg_ne_of_lt (by omega) (by omega) hjn) (resReg_ne_preserved j).2.2.2.2.2.1,
        hregs1 j (by omega)]


private theorem prog_call_budget_step {lkm : LinkModel} (env : CodeEnvGen lkm)
    {b : Nat} (hb64 : b < 2 ^ 64) (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
      Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hs0 : st.getReg AbiReg.s0 = BitVec.ofNat 64 b) :
    match b with
    | 0 =>
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.exhaustedTarget) ∧
        PreservedTramp st r' ∧
        r'.mem = st.mem
    | b' + 1 =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize
          [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel, Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)])) ∧
        PreservedNoS0 st st' ∧
        (∀ r ∈ calleeSavedBank, st'.getReg r = st.getReg r) ∧
        (∀ j, j < maxRes → st'.getReg (resReg j) = st.getReg (resReg j)) ∧
        st'.getReg AbiReg.s0 = BitVec.ofNat 64 b' ∧
        st'.mem = st.mem := by
  have hlinkBr : lkm.linkSpec (pre ++ [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel] ++
      ([Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++ post)) = .ok (env.code, env.labels) := by
    simpa [List.append_assoc] using hlink
  have hbr := run_br_step env pre _ .beq AbiReg.s0 AbiReg.zero exhaustedLabel env.exhaustedTarget
    env.hexhaustedLbl (by decide) hlinkBr st hpc
  cases b with
  | zero =>
    have hcond0 : evalBranch .beq (st.getReg AbiReg.s0) (st.getReg AbiReg.zero) = true := by
      rw [hs0, getReg_zero]; rfl
    obtain ⟨kBr, rEx, _, hrunEx, hpcEx, _, hpresBr, hmemEx⟩ := hbr
    exact ⟨kBr, rEx, hrunEx, by rw [hpcEx, hcond0]; rfl, hpresBr.toTramp, hmemEx⟩
  | succ b' =>
    have hne0 : BitVec.ofNat 64 (b' + 1) ≠ 0#64 := BitVec.ofNat_ne_zero_of_lt (Nat.succ_pos b') hb64
    have hcond1 : evalBranch .beq (st.getReg AbiReg.s0) (st.getReg AbiReg.zero) = false := by
      rw [hs0, getReg_zero]; simp [evalBranch, hne0]
    obtain ⟨kBr, st1, _, hrun1, hpc1, hoth1, _, hmem1⟩ := hbr
    let pre1 := pre ++ [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel]
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by
      rw [hpc1, hcond1]; simp only [Bool.false_eq_true, ↓reduceIte]
      exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (lkm.totalSize_append pre _).symm
    have hlinkAdd : lkm.linkSpec (pre1 ++ [Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] ++ post) =
        .ok (env.code, env.labels) := by simpa [pre1, List.append_assoc] using hlinkBr
    obtain ⟨hrun2, hpc2, hs0_2, hoth2, hmem2⟩ :=
      run_aluImm_rd_step env pre1 post .addi AbiReg.s0 AbiReg.s0 (-1#12) (by decide) hlinkAdd st1 hpc1'
    let st2 := stepReg st1 AbiReg.s0 (evalAluImm .addi (st1.getReg AbiReg.s0) (-1#12))
      (BitVec.ofNat 64 (4 * (lkm.totalSize pre1 + 1)))
    have hs0Val : st2.getReg AbiReg.s0 = BitVec.ofNat 64 b' := by
      rw [hs0_2]; change st1.getReg AbiReg.s0 + sextImm12 (-1#12) = BitVec.ofNat 64 b'
      rw [hoth1 _ (by decide), hs0]; exact BitVec.ofNat_sub_one_eq_add_neg1 hb64
    have hpc2' : st2.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize
        [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel, Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)])) := by
      rw [hpc2]
      have htw : lkm.totalSize [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel, Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] =
          lkm.totalSize [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel] + 1 := by
        rw [show [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel, Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] =
            [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel] ++ [Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] from rfl,
          lkm.totalSize_append]; simp only [Asm.addi, lkm.totalSize_instr]
      rw [htw]; simp only [pre1, lkm.totalSize_append, Nat.add_assoc]
    refine ⟨kBr + 1, st2, by rw [run_add, hrun1]; exact hrun2, hpc2',
      ⟨(hoth2 _ (by decide)).trans (hoth1 _ (by decide)),
       (hoth2 _ (by decide)).trans (hoth1 _ (by decide)),
       (hoth2 _ (by decide)).trans (hoth1 _ (by decide))⟩,
      fun r hr => (hoth2 r (allowedRegs_ne_s0 (isLeaf := false) hr)).trans (hoth1 r ⟨allowedRegs_ne_t6 (isLeaf := false) hr, allowedRegs_ne_s1 (isLeaf := false) hr⟩),
      fun j _ => (hoth2 (resReg j) (resReg_ne_preserved j).2.2.1).trans (hoth1 (resReg j) ⟨resReg_ne_t6 j, (resReg_ne_preserved j).2.2.2.1⟩),
      hs0Val, hmem2.trans hmem1⟩

private theorem prog_callArgs_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (fl : FrameLayout) (hfl : FrameLayoutOk fl) (b : Nat) (lm : _root_.L.Mem) (loc' : _root_.L.Locals)
    (sp : BitVec 64) (args : List _root_.L.Expr)
    (hargsOk : args.all (exprOkB env.tab fl.nlocals) = true)
    (hVfArgs : ExprsVarsInFrame fl args)
    (hTmp : usedTempsCallArgs fl.alloc args ≤ fl.usedTemps)
    (hb64 : b < 2 ^ 64) (hal : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ compileCallArgsR env.tab fl args ++ post) = .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hs0 : st.getReg AbiReg.s0 = BitVec.ofNat 64 b)
    (hm : ProgMemRel env.tab L st.mem lm) (hf' : ProgFrameOkR L fl sp st loc') :
    match _root_.L.evalArgs args { mem := lm, loc := loc' } with
    | .error _ =>
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedTramp st r' ∧
        ProgMemOutside (FnWriteMaskR L fl sp) st.mem r'.mem
    | .ok (vs, _) =>
      match b with
      | 0 =>
        ∃ k r', RV64.run env.rom k st = .cont r' ∧
          r'.pc = BitVec.ofNat 64 (4 * env.exhaustedTarget) ∧
          PreservedTramp st r' ∧
          ProgMemOutside (FnWriteMaskR L fl sp) st.mem r'.mem
      | b' + 1 =>
        ∃ k st4 argsPtr,
          RV64.run env.rom k st = .cont st4 ∧
          st4.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileCallArgsR env.tab fl args))) ∧
          vs.length = args.length ∧
          PreservedNoS0 st st4 ∧
          (∀ r ∈ calleeSavedBank, st4.getReg r = st.getReg r) ∧
          st4.getReg AbiReg.s0 = BitVec.ofNat 64 b' ∧
          MemEqOutside (tempSpanR fl sp 0) st.mem st4.mem ∧
          isAligned argsPtr 8 = true ∧
          (maxRes < args.length → st4.getReg AbiReg.t0 = argsPtr) ∧
          (∀ j, j < vs.length → ∀ kk, kk < 8 →
            sp.toNat ≤ (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)) + BitVec.ofNat 64 kk).toNat ∨
            ¬L.stackSpan.contains (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)) + BitVec.ofNat 64 kk)) ∧
          (∀ j, j < vs.length →
            (if j < maxRes then st4.getReg (resReg j)
             else readWord64 st4.mem (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)))) = (vs[j]!).toBitVec) := by
  have hframeValid : (frameSpanR fl sp).valid := Nat.le_trans htop L.hStackValid
  by_cases hrev : revDirectSafe true fl.alloc args = true
  · have hrev' : args.length ≤ maxRes ∧ revDirectSafeAux fl.alloc 0 args = true := by
      simpa [revDirectSafe, Bool.and_eq_true, decide_eq_true_eq] using hrev
    have hTmpRev : maxUsedTempsExprs args ≤ fl.usedTemps := by
      simpa [usedTempsCallArgs, hrev] using hTmp
    let cRev := compileEvalRevToRegs env.tab fl 0 args
    let cBud := [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel, Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)]
    have hcEq : compileCallArgsR env.tab fl args = cRev ++ cBud := by
      simp [compileCallArgsR, hrev, cRev, cBud]
    rw [hcEq] at hlink ⊢
    have hlinkR : lkm.linkSpec (pre ++ cRev ++ (cBud ++ post)) =
        .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
    have hsimR := reg_evalRevToRegs_sim env L fl hfl lm loc' hal hlo htop args 0 pre
      (cBud ++ post) (by omega) hrev'.2 hargsOk hVfArgs hTmpRev
      hlinkR (linkResolved_sub_pc64 env pre cRev _ hlinkR) st hpc hgp ht5 hsp hm hf'
    cases hea : _root_.L.evalArgs args { mem := lm, loc := loc' } with
    | error err =>
      rw [hea] at hsimR
      obtain ⟨kE, rE, hrunE, hpcE, hpresE, houtE⟩ := hsimR
      exact ⟨kE, rE, hrunE, hpcE, hpresE.abi.toTramp,
        ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo htop (Nat.zero_le _)) houtE⟩
    | ok resA =>
      rcases resA with ⟨vs, st1'⟩
      rw [hea] at hsimR
      obtain ⟨k1, st1, hrun1, hpc1, hvslen, hregs1, hpres1, hout1⟩ := hsimR
      have hcal1 : ∀ r ∈ calleeSavedBank, st1.getReg r = st.getReg r := fun r hr =>
        hpres1.regs r (calleeSaved_mem_allowed true hr) (fun ⟨d, _, heq⟩ => resReg_not_mem_calleeSaved (0 + d) hr heq)
      let pre1 := pre ++ cRev
      have hlinkBud : lkm.linkSpec (pre1 ++ cBud ++ post) =
          .ok (env.code, env.labels) := by simpa [pre1, List.append_assoc] using hlinkR
      have hbud := prog_call_budget_step env hb64 pre1 post hlinkBud st1
        (by simpa [pre1, lkm.totalSize_append] using hpc1) (hpres1.abi.s0.trans hs0)
      cases b with
      | zero =>
        obtain ⟨kB, rEx, hrunB, hpcB, hpresB, hmemB⟩ := hbud
        exact ⟨k1 + kB, rEx, by rw [run_add, hrun1]; exact hrunB, hpcB, hpres1.abi.toTramp.trans hpresB,
          ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo htop (Nat.zero_le _))
            (by rw [hmemB]; exact hout1)⟩
      | succ b' =>
        obtain ⟨kB, st2, hrunB, hpc2, hpres2, hcal2, hres2, hs0_2, hmem2⟩ := hbud
        have hcal12 : ∀ r ∈ calleeSavedBank, st2.getReg r = st.getReg r := fun r hr => (hcal2 r hr).trans (hcal1 r hr)
        have hargsGe : ∀ j, j < vs.length → ∀ kk, kk < 8 →
            sp.toNat ≤ (sp + BitVec.ofNat 64 (8 * (j - maxRes)) + BitVec.ofNat 64 kk).toNat ∨
            ¬L.stackSpan.contains (sp + BitVec.ofNat 64 (8 * (j - maxRes)) + BitVec.ofNat 64 kk) := by
          intro j hj kk hkk; left
          have hsub0 : j - maxRes = 0 := by omega
          have hv : sp.toNat + 8 * fl.frameSlots ≤ 2 ^ 64 := hframeValid
          have hmod := (isAligned8_iff sp).mp hal
          have hlt64 := sp.isLt
          rw [hsub0, Nat.mul_zero, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        exact ⟨k1 + kB, st2, sp, by rw [run_add, hrun1]; exact hrunB,
          by rw [hpc2]; dsimp only [pre1, cBud]; simp only [lkm.totalSize_append, Nat.add_assoc],
          hvslen, hpres1.abi.toNoS0.trans hpres2, hcal12, hs0_2,
          by rw [hmem2]; exact hout1, hal, fun h => absurd h (by omega), hargsGe,
          fun j hj => by
            have hjm : j < maxRes := by omega
            simp only [hjm, ↓reduceIte]
            rw [hres2 j hjm]
            have h := hregs1 j hj
            simp only [Nat.zero_add] at h
            rw [h, getElem!_pos vs j hj]⟩
  · have hTmpAll : usedTempsExprs args ≤ fl.usedTemps := by
      simpa [usedTempsCallArgs, hrev] using hTmp
    let cEval := compileEvalExprsToTempsR env.tab fl 0 args
    let cBud := [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel, Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)]
    let cLoad := (List.range (min args.length maxRes)).flatMap fun i =>
      loadMemOff .ld (resReg i) AbiReg.sp AbiReg.t0 (fl.tempSlotOff i)
    let cPtr := if maxRes < args.length then addImmOff AbiReg.t0 AbiReg.sp AbiReg.t2 (fl.tempSlotOff maxRes) else []
    have hcEq : compileCallArgsR env.tab fl args = cEval ++ cBud ++ cLoad ++ cPtr := by
      simp [compileCallArgsR, hrev, cEval, cBud, cLoad, cPtr, List.append_assoc]
    rw [hcEq] at hlink ⊢
    have hlinkE : lkm.linkSpec (pre ++ cEval ++ (cBud ++ cLoad ++ cPtr ++ post)) =
        .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
    have hargs := reg_evalArgs_sim env L fl hfl lm loc' hal hlo htop args pre _ 0 hargsOk hVfArgs
      (by omega) hlinkE (linkResolved_sub_pc64 env pre cEval _ hlinkE) st hpc hgp ht5 hsp hm hf'
    cases hea : _root_.L.evalArgs args { mem := lm, loc := loc' } with
    | error err =>
      rw [hea] at hargs
      obtain ⟨k, r', hrun, hpc', hpres, hout⟩ := hargs
      exact ⟨k, r', hrun, hpc', hpres.abi.toTramp,
        ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo htop (Nat.zero_le _)) hout⟩
    | ok resA =>
      rcases resA with ⟨vs, st1'⟩
      rw [hea] at hargs
      obtain ⟨k0, st1, hrun0, hpc1, hvslen, hslots, hpres0, hout0⟩ := hargs
      let pre1 := pre ++ cEval
      have hlinkBud : lkm.linkSpec (pre1 ++ cBud ++ (cLoad ++ cPtr ++ post)) =
          .ok (env.code, env.labels) := by simpa [pre1, List.append_assoc] using hlinkE
      have hbud := prog_call_budget_step env hb64 pre1 _ hlinkBud st1
        (by simpa [pre1, lkm.totalSize_append] using hpc1) (hpres0.abi.s0.trans hs0)
      cases b with
      | zero =>
        obtain ⟨kB, rEx, hrunB, hpcB, hpresB, hmemB⟩ := hbud
        exact ⟨k0 + kB, rEx, by rw [run_add, hrun0]; exact hrunB, hpcB, hpres0.abi.toTramp.trans hpresB,
          ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo htop (Nat.zero_le _))
            (by rw [hmemB]; exact hout0)⟩
      | succ b' =>
        obtain ⟨kB, st2, hrunB, hpc2, hpres2, hcal2, _, hs0_2, hmem2⟩ := hbud
        let pre2 := pre1 ++ cBud
        have hlinkLoad : lkm.linkSpec (pre2 ++ cLoad ++ (cPtr ++ post)) =
            .ok (env.code, env.labels) := by simpa [pre2, List.append_assoc] using hlinkBud
        obtain ⟨kL, st3, hrunL, hpc3, hpresL, _, hcalL, hmemL, hregs3⟩ :=
          loadTempArgsLoop_sim env fl hal vs (min args.length maxRes) (by omega) pre2 _ hlinkLoad st2
            (by rw [lkm.totalSize_append]; exact hpc2) (hpres2.sp.trans (hpres0.abi.sp.trans hsp))
            (fun j hj => by rw [hmem2]; have h := hslots j hj; simpa using h)
        let pre3 := pre2 ++ cLoad
        have hlinkPtr : lkm.linkSpec (pre3 ++ cPtr ++ post) =
            .ok (env.code, env.labels) := by simpa [pre3, List.append_assoc] using hlinkLoad
        have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre3) := by
          simpa [pre3, lkm.totalSize_append] using hpc3
        have hsp3 : st3.getReg AbiReg.sp = sp := hpresL.sp.trans (hpres2.sp.trans (hpres0.abi.sp.trans hsp))
        let argsPtr := if maxRes < args.length then sp + BitVec.ofInt 64 (fl.tempSlotOff maxRes) else sp
        have hptrStep : ∃ kP st4,
            RV64.run env.rom kP st3 = .cont st4 ∧
            st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre3 ++ cPtr)) ∧
            (∀ r, r ≠ AbiReg.t0 → r ≠ AbiReg.t2 → st4.getReg r = st3.getReg r) ∧
            (maxRes < args.length → st4.getReg AbiReg.t0 = argsPtr) ∧
            st4.mem = st3.mem := by
          by_cases hgt : maxRes < args.length
          · have hcp : cPtr = addImmOff AbiReg.t0 AbiReg.sp AbiReg.t2 (fl.tempSlotOff maxRes) := by simp [cPtr, hgt]
            rw [hcp] at hlinkPtr
            obtain ⟨st4, hrunP, hothP, ht0P, hmemP, hpcP⟩ :=
              addImmOff_correct_lm lkm env.hrom pre3 post AbiReg.t0 AbiReg.sp AbiReg.t2 (by decide) (by decide) (by decide)
                (fl.tempSlotOff maxRes) hlinkPtr (linkResolved_sub_pc64 env pre3 _ post hlinkPtr) st3 hpc3'
            exact ⟨_, st4, hrunP, by rw [hpcP, hcp]; simp only [lkm.totalSize_append], hothP,
              fun _ => by rw [ht0P, hsp3]; simp [argsPtr, hgt], hmemP⟩
          · have hcp : cPtr = [] := by simp [cPtr, hgt]
            exact ⟨0, st3, rfl, by rw [hcp, List.append_nil]; exact hpc3', fun _ _ _ => rfl,
              fun h => absurd h hgt, rfl⟩
        obtain ⟨kP, st4, hrunP, hpc4', hothP, ht0_4, hmemP⟩ := hptrStep
        have hmem14 : st4.mem = st1.mem := hmemP.trans (hmemL.trans hmem2)
        have hcal04 : ∀ r ∈ calleeSavedBank, st4.getReg r = st.getReg r := fun r hr =>
          (hothP r (allowedRegs_ne_t0 (isLeaf := false) hr) (allowedRegs_ne_t2 (isLeaf := false) hr)).trans
            ((hcalL r hr).trans ((hcal2 r hr).trans (hpres0.regs r (calleeSaved_mem_allowed true hr) (fun h => False.elim h))))
        have hargsAl : isAligned argsPtr 8 = true := by
          dsimp only [argsPtr]
          split
          · rw [tempSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hal _
          · exact hal
        have hargsGe : ∀ j, j < vs.length → ∀ kk, kk < 8 →
            sp.toNat ≤ (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)) + BitVec.ofNat 64 kk).toNat ∨
            ¬L.stackSpan.contains (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)) + BitVec.ofNat 64 kk) := by
          intro j hj kk hkk; left
          have hv : sp.toNat + 8 * fl.frameSlots ≤ 2 ^ 64 := hframeValid
          dsimp only [FrameLayout.frameSlots] at hv
          by_cases hgt : maxRes < args.length
          · have hlenLe : args.length ≤ fl.usedTemps := Nat.le_trans (usedTempsExprs_ge_length args) hTmpAll
            have hadd : maxRes + (j - maxRes) < fl.usedTemps := by omega
            dsimp only [argsPtr]; simp only [hgt, ↓reduceIte]
            rw [tempSlotOff_ofInt, BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add,
              BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
            omega
          · have hsub0 : j - maxRes = 0 := by omega
            have hmod := (isAligned8_iff sp).mp hal
            have hlt64 := sp.isLt
            dsimp only [argsPtr]; simp only [hgt, ↓reduceIte, hsub0, Nat.mul_zero, BitVec.add_zero]
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
            omega
        have hargWords4 : ∀ j, j < vs.length →
            (if j < maxRes then st4.getReg (resReg j)
             else readWord64 st4.mem (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)))) = (vs[j]!).toBitVec := by
          intro j hj
          by_cases hjm : j < maxRes
          · simp only [hjm, ↓reduceIte]
            rw [hothP (resReg j) (resReg_ne_preserved j).2.2.2.2.2.1 (resReg_ne_preserved j).2.2.2.2.2.2.2,
              hregs3 j (by omega)]
          · simp only [hjm, ↓reduceIte, hmem14]
            have hgt : maxRes < args.length := by omega
            have hEqOff : argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)) = sp + BitVec.ofInt 64 (fl.tempSlotOff (0 + j)) := by
              dsimp only [argsPtr]; simp only [hgt, ↓reduceIte]
              rw [tempSlotOff_ofInt, tempSlotOff_ofInt, BitVec.add_assoc, ← BitVec.ofNat_add]
              congr 2; omega
            rw [hEqOff, hslots j hj]; simp [hj]
        have hpres34 : PreservedNoS0 st3 st4 :=
          ⟨hothP _ (by decide) (by decide), hothP _ (by decide) (by decide),
           hothP _ (by decide) (by decide)⟩
        exact ⟨k0 + kB + kL + kP, st4, argsPtr,
          run_trans (run_trans (run_trans hrun0 hrunB) hrunL) hrunP,
          by rw [hpc4']; simp only [pre3, pre2, pre1, lkm.totalSize_append, Nat.add_assoc],
          hvslen, ((hpres0.abi.toNoS0.trans hpres2).trans hpresL.toNoS0).trans hpres34,
          hcal04, (hothP _ (by decide) (by decide)).trans (hpresL.s0.trans hs0_2),
          by rw [hmem14]; exact hout0, hargsAl, ht0_4, hargsGe, hargWords4⟩

private theorem prog_call_step_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab) (p : _root_.L.Prog)
    (fl : FrameLayout) (hfl : FrameLayoutOk fl) (b : Nat) (lm : _root_.L.Mem) (loc : _root_.L.Locals)
    (sp : BitVec 64) (pfx : String) (lblId : Nat) (brkLbl : Option String) (retLbl : String) (isTail : Bool)
    (xs : List _root_.L.Var) (f : FnName) (args : List _root_.L.Expr)
    (na nb : Var → Bool) (tco : TcoCtx)
    (hxs : xs.all (· < fl.nlocals) = true) (hargsOk : args.all (exprOkB env.tab fl.nlocals) = true)
    (hVfArgs : ExprsVarsInFrame fl args)
    (hArgsLen : ∃ fd, p.lookup f = some fd ∧ args.length = fd.nparams ∧ xs.length ≤ fnMinRet fd)
    (hTmp : usedTempsCallArgs fl.alloc args ≤ fl.usedTemps)
    (hLeaf : fl.isLeaf = true → stmtHasCall (.call xs f args) = false)
    (hCallFree : ∀ x r, fl.alloc.lookup x = some r → r ∈ leafExtraBank → (na x && !(x ∈ xs)) = false)
    (hnoClob : ∀ y ry, fl.alloc.lookup y = some ry → na y = true → ∀ x ∈ xs, x ≠ y → fl.alloc.lookup x ≠ some ry)
    (hResValid : callResListValid fl.alloc xs = true)
    (hb64 : b < 2 ^ 64) (hal : isAligned sp 8 = true)
    (hlim : L.stackLimit.toNat + stackNeedB p b (.call xs f args) { mem := lm, loc := loc } ≤ sp.toNat)
    (htop : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (hfnLbl : ∃ fnPc, lookupLabel env.labels (fnLabel f) = some fnPc)
    (hcall : ∀ b', b' < b → FnCallSimGenCallee env L p b')
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.call xs f args)).1 ++ post) =
      .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hs0 : st.getReg AbiReg.s0 = BitVec.ofNat 64 b)
    (hm : ProgMemRel env.tab L st.mem lm)
    (hf : ProgFrameOkLive L fl sp st loc (fun x => (stmtVarCallFree x (.call xs f args) (na x) (nb x)).1))
    (hhdr : TabHeaderOk L st.mem) :
    StmtOutcomeR env L fl sp b st retLbl brkLbl
      (lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.call xs f args)).1) na nb tco
      (execB p b (.call xs f args) { mem := lm, loc := loc }) := by
  have hnotLeaf : fl.isLeaf = false := by
    cases hl : fl.isLeaf with
    | false => rfl
    | true => have h := hLeaf hl; simp [stmtHasCall] at h
  have hframeValid : (frameSpanR fl sp).valid := Nat.le_trans htop L.hStackValid
  let liveCall : Var → Bool := fun x => (stmtVarCallFree x (.call xs f args) (na x) (nb x)).1
  let loc' := ghostLoc fl sp st loc liveCall
  have hf' : ProgFrameOkR L fl sp st loc' := ghostLoc_frameOk hf
  have hagCall : ∀ x, liveCall x = true → loc' x = loc x := ghostLoc_agree fl sp st loc liveCall
  have hargsAg : ∀ x, args.any (exprUsesVar x) = true → loc' x = loc x :=
    fun x hx => hagCall x (by simp [liveCall, stmtVarCallFree, hx])
  rcases hArgsLen with ⟨fd, hflook, hflen, hxsMinRet⟩
  obtain ⟨fnPc, hfnPc⟩ := hfnLbl
  let cArgsAll := compileCallArgsR env.tab fl args
  let cCall := [Asm.call (fnLabel f)]
  let cReloadT5 := if fl.useT5Gp then [Asm.addi AbiReg.t5 AbiReg.gp 2047#12] else []
  let cCopy := copyResultsToLocalsR env.tab fl xs
  have hcodeEq : (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.call xs f args)).1 =
      cArgsAll ++ cCall ++ cReloadT5 ++ cCopy := by
    simp [compileSR, cArgsAll, cCall, cReloadT5, cCopy, List.append_assoc]
  rw [hcodeEq] at hlink
  have hlink0 : lkm.linkSpec (pre ++ cArgsAll ++ (cCall ++ cReloadT5 ++ cCopy ++ post)) =
      .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
  have hargsSim := prog_callArgs_sim env L fl hfl b lm loc' sp args hargsOk hVfArgs hTmp hb64 hal (by omega) htop
    pre (cCall ++ cReloadT5 ++ cCopy ++ post) hlink0 st hpc hgp ht5 hsp hs0 hm hf'
  cases hea : _root_.L.evalArgs args { mem := lm, loc := loc' } with
  | error err =>
    have herr := evalArgs_err_eq_oob args { mem := lm, loc := loc' } hea
    subst herr; rw [hea] at hargsSim; rw [execB_call, evalArgs_congr_eq_err hargsAg hea]
    obtain ⟨k, r', hrun, hpc', hpres, hpm⟩ := hargsSim
    exact ⟨k, r', hrun, hpc', hpres,
      ProgMemOutside.mono (fnWriteMaskR_sub_callWriteMask L (Nat.le_of_eq (callerSp_toNat_eq L htop).symm)) hpm⟩
  | ok resA =>
    rcases resA with ⟨vs, _⟩
    have hea0 := evalArgs_congr_eq_ok hargsAg hea
    rw [hea] at hargsSim
    cases b with
    | zero =>
      rw [execB_call, hea0, hflook]
      obtain ⟨k, r', hrun, hpc', hpres, hpm⟩ := hargsSim
      exact ⟨k, r', hrun, hpc', hpres,
        ProgMemOutside.mono (fnWriteMaskR_sub_callWriteMask L (Nat.le_of_eq (callerSp_toNat_eq L htop).symm)) hpm⟩
    | succ b' =>
      obtain ⟨kPre, st4, argsPtr, hrunPre, hpc4, hvslen, hpres4, hcal4, hs0_4, hout4, hargsAl, ht0_4, hargsGe, hargWords4⟩ := hargsSim
      have hm4 := ProgMemRel.of_tempSpanR (by omega) htop (Nat.zero_le _) hout4 hm
      have hpm4 : ProgMemOutside (FnWriteMaskR L fl sp) st.mem st4.mem :=
        ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L (by omega) htop (Nat.zero_le _)) hout4
      have hhdr4 : TabHeaderOk L st4.mem := hhdr.of_fnWriteMaskR L hpm4
      have hspills4 : ∀ x, x < fl.nlocals → fl.alloc.lookup x = none → x ∈ fl.spilledVars →
          readWord64 st4.mem (sp + BitVec.ofInt 64 (fl.varSlotOff x)) = (loc' x).toBitVec := fun x hx hlx hmx => by
        have hfx := hf' x hx; rw [hlx] at hfx
        rw [MemEqOutside.readWord64_eq hout4 (sp + BitVec.ofInt 64 (fl.varSlotOff x)) (fun o ho =>
          (tempSpanR_disj_varSlot fl hfl sp hframeValid 0 (Nat.zero_le _) hmx).symm _
            ⟨o, ho, by rw [varSlotOff_ofInt]; rfl⟩)]
        exact hfx hmx
      let pre4 := pre ++ cArgsAll
      have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre4) := by
        simpa [pre4, cArgsAll, lkm.totalSize_append] using hpc4
      have hlinkCall : lkm.linkSpec (pre4 ++ [Asm.call (fnLabel f)] ++ (cReloadT5 ++ cCopy ++ post)) =
          .ok (env.code, env.labels) := by simpa [pre4, cCall, List.append_assoc] using hlink0
      have hltCall64 : 4 * (lkm.totalSize pre4 + lkm.itemSize (.call (fnLabel f))) < 2 ^ 64 := by
        simpa [Asm.call, lkm.totalSize_singleton] using linkResolved_sub_pc64 env pre4 [Asm.call (fnLabel f)] _ hlinkCall
      obtain ⟨tgtFn, kCall, st6, _, hlkpFn, hrun5, hpc6, hregs6, hmem6'⟩ :=
        step_item_call_lm lkm env.hrom pre4 _ (fnLabel f) hlinkCall hltCall64 st4 hpc4'
      rw [hfnPc] at hlkpFn
      have htgtFnEq : tgtFn = fnPc := Option.some.inj hlkpFn.symm
      have hpres46 : PreservedNoS0 st4 st6 :=
        ⟨(hregs6.getReg_eq (by decide)).symm.trans (getReg_setReg_ne st4 AbiReg.ra _ _ (by decide)),
         (hregs6.getReg_eq (by decide)).symm.trans (getReg_setReg_ne st4 AbiReg.ra _ _ (by decide)),
         (hregs6.getReg_eq (by decide)).symm.trans (getReg_setReg_ne st4 AbiReg.ra _ _ (by decide))⟩
      have hcal46 : ∀ r ∈ calleeSavedBank, st6.getReg r = st4.getReg r := fun r hr =>
        (hregs6.getReg_eq ⟨allowedRegs_ne_t6 (isLeaf := false) hr, allowedRegs_ne_s1 (isLeaf := false) hr⟩).symm.trans
          (getReg_setReg_ne st4 AbiReg.ra r _ (allowedRegs_ne_ra (isLeaf := false) hr))
      have hs0_6 : st6.getReg AbiReg.s0 = BitVec.ofNat 64 b' :=
        ((hregs6.getReg_eq (by decide)).symm.trans (getReg_setReg_ne st4 AbiReg.ra _ _ (by decide))).trans hs0_4
      have ht0_6 : maxRes < fd.nparams → st6.getReg AbiReg.t0 = argsPtr := fun hpos => by
        rw [← hregs6.getReg_eq (by decide), getReg_setReg_ne st4 AbiReg.ra _ _ (by decide), ht0_4 (by omega)]
      have hra_6 : st6.getReg AbiReg.ra = BitVec.ofNat 64 (4 * (lkm.totalSize pre4 + lkm.itemSize (.call (fnLabel f)))) := by
        rw [← hregs6.getReg_eq (by decide), getReg_setReg_eq st4 AbiReg.ra _ (by decide)]
      have hargWords6 : ∀ j, j < vs.length →
          (if j < maxRes then st6.getReg (resReg j)
           else readWord64 st6.mem (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)))) = (vs[j]!).toBitVec := by
        intro j hj
        by_cases hjm : j < maxRes
        · simp only [hjm, ↓reduceIte]
          rw [← hregs6.getReg_eq ⟨resReg_ne_t6 j, (resReg_ne_preserved j).2.2.2.1⟩, getReg_setReg_ne st4 AbiReg.ra (resReg j) _ (resReg_ne_ra j)]
          have h := hargWords4 j hj; simpa [hjm] using h
        · simp only [hjm, ↓reduceIte, hmem6']
          have h := hargWords4 j hj; simpa [hjm] using h
      have hlimC := stackNeedB_call p (b' + 1) xs f args { mem := lm, loc := loc }
      rw [hea0, hflook] at hlimC; dsimp only at hlimC
      have hcallF := hcall b' (Nat.lt_succ_self b') f fd vs lm sp (st6.getReg AbiReg.ra) argsPtr
        (lkm.totalSize pre4 + lkm.itemSize (.call (fnLabel f)))
        hflook (hvslen.trans hflen) (by omega) (by rw [hlimC, ← Nat.add_assoc] at hlim; exact hlim) (by omega) hal hargsAl
        (by rw [hra_6]; exact mul4_and_not1 (lkm.totalSize pre4 + lkm.itemSize (.call (fnLabel f))))
        hargsGe fnPc st6 hfnPc (by rw [hpc6, htgtFnEq])
        (hpres46.gp.trans (hpres4.gp.trans hgp)) (hpres46.sp.trans (hpres4.sp.trans hsp)) rfl
        hs0_6 ht0_6 (by rw [hmem6']; exact hm4) (by rw [hmem6']; exact hhdr4) hargWords6
      have hrunUp : RV64.run env.rom (kPre + kCall) st = .cont st6 := by
        rw [run_add, hrunPre]; exact hrun5
      rw [execB_call, hea0, hflook]; dsimp only
      cases hxF : execB p b' fd.body { mem := lm, loc := Locals.init vs } with
      | error err =>
        rw [hxF] at hcallF
        have htr06 : PreservedTramp st st6 := hpres4.toTramp.trans hpres46.toTramp
        have hcm06 : ProgMemOutside (CallWriteMask L (sp + BitVec.ofInt 64 fl.frameBytes)) st.mem st6.mem := by
          rw [hmem6']
          exact ProgMemOutside.mono (fnWriteMaskR_sub_callWriteMask L (Nat.le_of_eq (callerSp_toNat_eq L htop).symm)) hpm4
        have hsubCall : ∀ a, CallWriteMask L sp a → CallWriteMask L (sp + BitVec.ofInt 64 fl.frameBytes) a :=
          fun a ha => fnWriteMaskR_sub_callWriteMask L (Nat.le_of_eq (callerSp_toNat_eq L htop).symm) a
            (callWriteMask_sub_fnWriteMaskR L fl sp a ha)
        cases err with
        | outOfFuel =>
          obtain ⟨kc, rc, hrunC, hpcC, hpresC, hpmC⟩ := hcallF
          exact ⟨_, rc, by rw [run_add, hrunUp]; exact hrunC, hpcC, htr06.trans hpresC,
            hcm06.trans (ProgMemOutside.mono hsubCall hpmC)⟩
        | abort code =>
          obtain ⟨kc, rc, hrunC, hpcC, ha0C, hpresC, hpmC⟩ := hcallF
          exact ⟨_, rc, by rw [run_add, hrunUp]; exact hrunC, hpcC, ha0C, htr06.trans hpresC,
            hcm06.trans (ProgMemOutside.mono hsubCall hpmC)⟩
        | oob =>
          obtain ⟨kc, rc, hrunC, hpcC, hpresC, hpmC⟩ := hcallF
          exact ⟨_, rc, by rw [run_add, hrunUp]; exact hrunC, hpcC, htr06.trans hpresC,
            hcm06.trans (ProgMemOutside.mono hsubCall hpmC)⟩
        | noFun fn =>
          obtain ⟨kc, rc, hrunC, hpcC, hpresC, hpmC⟩ := hcallF
          exact ⟨_, rc, by rw [run_add, hrunUp]; exact hrunC, hpcC, htr06.trans hpresC,
            hcm06.trans (ProgMemOutside.mono hsubCall hpmC)⟩
      | ok resF =>
        rcases resF with ⟨sigF, stF, bF⟩
        rw [hxF] at hcallF
        obtain ⟨kF, rF, hrunF, hpcF, hgpF, hspF, hs2F, hcalF, hs0F, hbF, hsigNb, hvlenF, hmF, hhdrF, hresF, houtF⟩ := hcallF
        have houtF6 : ProgMemOutside (CallWriteMask L sp) st4.mem rF.mem := by rw [← hmem6']; exact houtF
        have hcal4F : ∀ r ∈ calleeSavedBank, rF.getReg r = st4.getReg r := fun r hr =>
          (hcalF r hr).trans (hcal46 r hr)
        let preT5 := pre4 ++ cCall
        have hpcF' : rF.pc = BitVec.ofNat 64 (4 * lkm.totalSize preT5) := by
          rw [hpcF]; simp only [preT5, cCall, lkm.totalSize_append, Asm.call, lkm.totalSize_singleton]
        have hlinkT5 : lkm.linkSpec (preT5 ++ cReloadT5 ++ (cCopy ++ post)) = .ok (env.code, env.labels) := by
          simpa [preT5, pre4, cCall, List.append_assoc] using hlink0
        have hreloadT5 :
            ∃ kT5 rT5,
              RV64.run env.rom kT5 rF = .cont rT5 ∧
              rT5.pc = BitVec.ofNat 64 (4 * lkm.totalSize (preT5 ++ cReloadT5)) ∧
              rT5.getReg AbiReg.gp = L.T ∧
              rT5.getReg AbiReg.sp = sp ∧
              rT5.getReg AbiReg.s0 = BitVec.ofNat 64 bF ∧
              rT5.getReg AbiReg.s2 = rF.getReg AbiReg.s2 ∧
              T5GpOk L fl rT5 ∧
              (∀ r ∈ calleeSavedBank, rT5.getReg r = rF.getReg r) ∧
              ResultsInState env.tab L rT5 sigF.retVal ∧
              rT5.mem = rF.mem := by
          cases ht5u : fl.useT5Gp with
          | false =>
            have hc : cReloadT5 = [] := by simp [cReloadT5, ht5u]
            refine ⟨0, rF, rfl, by rw [hc, List.append_nil]; exact hpcF', hgpF, hspF, hs0F, rfl,
              (fun h => by rw [ht5u] at h; cases h), fun _ _ => rfl, hresF, rfl⟩
          | true =>
            have hc : cReloadT5 = [Asm.addi AbiReg.t5 AbiReg.gp 2047#12] := by simp [cReloadT5, ht5u]
            have hlinkA : lkm.linkSpec (preT5 ++ [Asm.addi AbiReg.t5 AbiReg.gp 2047#12] ++ (cCopy ++ post)) =
                .ok (env.code, env.labels) := by rw [← hc]; exact hlinkT5
            obtain ⟨hrunA, hpcA, ht5A, hothA, hmemA⟩ :=
              run_aluImm_rd_step env preT5 (cCopy ++ post) .addi AbiReg.t5 AbiReg.gp 2047#12 (by decide) hlinkA rF hpcF'
            let rT5 := stepReg rF AbiReg.t5 (evalAluImm .addi (rF.getReg AbiReg.gp) 2047#12)
              (BitVec.ofNat 64 (4 * (lkm.totalSize preT5 + 1)))
            have ht5Val : rT5.getReg AbiReg.t5 = L.T + 2047#64 := by
              rw [ht5A]; change rF.getReg AbiReg.gp + sextImm12 2047#12 = L.T + 2047#64
              rw [hgpF, sextImm12_ofNat_lt 2047 (by omega)]
            refine ⟨1, rT5, hrunA, by rw [hpcA, hc]; simp only [lkm.totalSize_append, Asm.addi, lkm.totalSize_instr],
              (hothA _ (by decide)).trans hgpF, (hothA _ (by decide)).trans hspF,
              (hothA _ (by decide)).trans hs0F, hothA _ (by decide),
              fun _ => ht5Val, fun r hr => hothA r (allowedRegs_ne_t5 (isLeaf := false) hr),
              ⟨fun i hi => (hothA (resReg i) (resReg_ne_t5 i)).trans (hresF.1 i hi),
               fun i hloI hhiI => by rw [hmemA]; exact hresF.2 i hloI hhiI⟩,
              hmemA⟩
        obtain ⟨kT5, rT5, hrunT5, hpcT5, hgpT5, hspT5, hs0T5, hs2T5, ht5T5, hcalT5, hresT5, hmemT5⟩ := hreloadT5
        -- Construct ghost locals `locAfter` updating `x ∈ xs` to match `rT5` while preserving live `x ∉ xs`
        let locAfter : _root_.L.Locals := fun x =>
          if x ∈ xs then
            match fl.alloc.lookup x with
            | some r => UInt64.ofBitVec (rT5.getReg r)
            | none => UInt64.ofBitVec (readWord64 rT5.mem (sp + BitVec.ofInt 64 (fl.varSlotOff x)))
          else loc' x
        have hfAfter : ProgFrameOkLive L fl sp rT5 locAfter na := by
          intro x hx hna
          dsimp only [locAfter]
          by_cases hxin : x ∈ xs
          · simp only [hxin, ↓reduceIte]
            cases fl.alloc.lookup x with
            | some r => rfl
            | none => intro _; rfl
          · simp only [hxin, ↓reduceIte]
            cases hlx : fl.alloc.lookup x with
            | some r =>
              have hrNotL : r ∉ leafExtraBank := fun hrL => by
                have hcf := hCallFree x r hlx hrL
                simp [hna, hxin] at hcf
              have hrCal : r ∈ calleeSavedBank := by
                have hm := (regAllocValid_lookup hfl.valid hlx).2.1
                simp only [allowedRegs, ↓reduceIte, List.mem_append] at hm
                exact hm.resolve_left hrNotL
              have hfx := hf' x hx; rw [hlx] at hfx
              dsimp only at hfx ⊢
              rw [hcalT5 r hrCal, hcal4F r hrCal, hcal4 r hrCal]; exact hfx
            | none =>
              intro hmx
              rw [hmemT5, spillSlots_of_callWriteMask L hfl (by omega) htop houtF6 hmx]
              exact hspills4 x hx hlx hmx
        let pre5 := preT5 ++ cReloadT5
        have hlinkCopy : lkm.linkSpec (pre5 ++ copyResultsLoopR env.tab fl xs 0 ++ post) =
            .ok (env.code, env.labels) := by
          rw [← copyResultsToLocalsR_eq_loop]
          simpa [pre5, preT5, pre4, cCall, cReloadT5, cCopy, List.append_assoc] using hlink0
        have hxs' : ∀ x ∈ xs, x < fl.nlocals := fun x hx => by
          simp only [List.all_eq_true, decide_eq_true_eq] at hxs; exact hxs x hx
        have hminRet : fnMinRet fd ≤ max 1 sigF.retVal.length := fnMinRet_le_sig hxF hsigNb
        obtain ⟨kCopy, rCopy, hrunCopy, hpcCopy, hpresCopy, hfCopy, houtCopy⟩ :=
          reg_copyResultsLoopR_sim env L fl hfl hal (by omega) htop sigF.retVal hvlenF stF.mem na xs 0 hxs'
            (by omega) (callResListValid_spec hResValid) hnoClob pre5 post hlinkCopy locAfter rT5 hpcT5 hgpT5 hspT5
            (hresT5.toRange (by omega)) hfAfter
        have hmCopy : ProgMemRel env.tab L rCopy.mem stF.mem :=
          ProgMemRel.of_stack_eqOutside (localsTempSpanR_sub_stackSpan L (by omega) htop) houtCopy (by rw [hmemT5]; exact hmF)
        have houtCopyMask : ProgMemOutside (FnWriteMaskR L fl sp) rF.mem rCopy.mem := by
          rw [← hmemT5]
          exact ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_localsTempSpanR L (by omega) htop) houtCopy
        have hhdrCopy : TabHeaderOk L rCopy.mem := hhdrF.of_fnWriteMaskR L houtCopyMask
        have houtAll : ProgMemOutside (FnWriteMaskR L fl sp) st.mem rCopy.mem :=
          (hpm4.trans (ProgMemOutside.mono (callWriteMask_sub_fnWriteMaskR L fl sp) houtF6)).trans houtCopyMask
        have hpresAll : PreservedFrameNoS0 fl st rCopy := by
          refine ⟨⟨(hpresCopy.abi.gp.trans hgpT5).trans hgp.symm,
            (hpresCopy.abi.sp.trans hspT5).trans hsp.symm,
            (hpresCopy.abi.s2.trans hs2T5).trans (hs2F.trans (hpres46.s2.trans hpres4.s2))⟩,
            (fun hl => by rw [hnotLeaf] at hl; cases hl),
            fun ht => (hpresCopy.t5Gp ht).trans ((ht5T5 ht).trans (ht5 ht).symm),
            fun r hr hna => ?_⟩
          have hrCal : r ∈ calleeSavedBank := by rwa [hnotLeaf] at hr
          exact (hpresCopy.regs r (allowedRegs_sub_true hr) hna).trans ((hcalT5 r hrCal).trans ((hcal4F r hrCal).trans (hcal4 r hrCal)))
        have hs0All : rCopy.getReg AbiReg.s0 = BitVec.ofNat 64 bF := hpresCopy.abi.s0.trans hs0T5
        have hpcFin : rCopy.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.call xs f args)).1)) := by
          rw [hpcCopy, hcodeEq, ← copyResultsToLocalsR_eq_loop]
          dsimp only [pre5, preT5, pre4, cCopy]
          simp only [lkm.totalSize_append, Nat.add_assoc]
        have hlocEq : (({ mem := stF.mem, loc := locAfter } : _root_.L.St).setLocs xs sigF.retVal).loc =
            (({ mem := stF.mem, loc := locAfter } : _root_.L.St).setLocs xs (sigF.retVal.drop 0)).loc := by simp
        have hmCopy' : ProgMemRel env.tab L rCopy.mem (({ mem := stF.mem, loc := loc } : _root_.L.St).setLocs xs sigF.retVal).mem := by
          rw [setLocs_mem]; exact hmCopy
        rw [← hlocEq] at hfCopy
        have hfLive : ProgFrameOkLive L fl sp rCopy (({ mem := stF.mem, loc := loc } : _root_.L.St).setLocs xs sigF.retVal).loc na := by
          have hlocEqNa := setLocs_congr xs sigF.retVal stF.mem locAfter loc na fun x hx => by
            simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hx
            dsimp only [locAfter]
            simp only [hx.2, ↓reduceIte]
            exact hagCall x (by simp [liveCall, stmtVarCallFree, hx.1, hx.2])
          intro x hx hna
          rw [← hlocEqNa x hna]
          exact hfCopy x hx hna
        exact ⟨_, rCopy, run_trans (run_trans (run_trans hrunUp hrunF) hrunT5) hrunCopy,
          hpcFin, hpresAll, hs0All, by omega, hmCopy', hfLive, houtAll, hhdrCopy⟩


private theorem compileFnWith_head (rawAlloc : RegAlloc) (tab : Tab) (f : FnName) (fd : FunDecl) :
    ∃ rest, compileFnWith rawAlloc tab f fd = [Asm.lbl (fnLabel f)] ++ rest := by
  have hcons : ∀ (c : Bool) (a b d : List AsmItem),
      (∃ r, a = [Asm.lbl (fnLabel f)] ++ r) → (∃ r, b = [Asm.lbl (fnLabel f)] ++ r) →
      ∃ r, (if c = true then a else b) ++ d = [Asm.lbl (fnLabel f)] ++ r := by
    intro c a b d ⟨ra, ha⟩ ⟨rb, hb⟩
    cases c <;> simp [ha, hb]
  have hmap : ∀ (xs ys : List AsmItem) (g : AsmItem → AsmItem),
      g (Asm.lbl (fnLabel f)) = Asm.lbl (fnLabel f) →
      ∃ r, ([Asm.lbl (fnLabel f)] ++ xs).map g ++ ys = [Asm.lbl (fnLabel f)] ++ r := by
    intro xs ys g hg
    exact ⟨xs.map g ++ ys, by simp [hg]⟩
  unfold compileFnWith; dsimp only
  simp only [List.append_assoc]
  apply hcons
  · exact hmap _ _ _ rfl
  · exact ⟨_, rfl⟩

private theorem compileFn_head (tab : Tab) (f : FnName) (fd : FunDecl) :
    ∃ rest, compileFn tab f fd = [Asm.lbl (fnLabel f)] ++ rest :=
  compileFnWith_head (chooseRegAlloc fd) tab f fd

theorem ProgFnsLinkedWithGen.split_fn {lkm : LinkModel} {env : CodeEnvGen lkm}
    {allocOf : FnName → FunDecl → RegAlloc} {p : _root_.L.Prog}
    (hFns : ProgFnsLinkedWithGen env allocOf p) {f : FnName} {fd : FunDecl}
    (hflook : p.lookup f = some fd) :
    ∃ preFn postFn,
      lkm.linkSpec (preFn ++ compileFnWith (allocOf f fd) env.tab f fd ++ postFn) =
        .ok (env.code, env.labels) ∧
      lookupLabel env.labels (fnLabel f) = some (lkm.totalSize preFn) := by
  rcases hFns with ⟨p', preFns, postFns, hmem, hlink⟩
  obtain ⟨p1, p2, rfl⟩ := List.append_of_mem (hmem f fd hflook)
  let preFn := preFns ++ (p1.flatMap fun (x, y) => compileFnWith (allocOf x y) env.tab x y)
  let postFn := (p2.flatMap fun (x, y) => compileFnWith (allocOf x y) env.tab x y) ++ postFns
  have hlink' : lkm.linkSpec (preFn ++ compileFnWith (allocOf f fd) env.tab f fd ++ postFn) =
      .ok (env.code, env.labels) := by
    simpa [preFn, postFn, List.flatMap_append, List.flatMap_cons, List.append_assoc] using hlink
  refine ⟨preFn, postFn, hlink', ?_⟩
  obtain ⟨rest, hcf⟩ := compileFnWith_head (allocOf f fd) env.tab f fd
  rw [hcf] at hlink'
  exact linkResolved_lbl_lm lkm preFn (fnLabel f) _ (by simpa [List.append_assoc] using hlink')

theorem ProgFnsLinkedGen.split_fn {lkm : LinkModel} {env : CodeEnvGen lkm} {p : _root_.L.Prog}
    (hFns : ProgFnsLinkedGen env p) {f : FnName} {fd : FunDecl}
    (hflook : p.lookup f = some fd) :
    ∃ preFn postFn,
      lkm.linkSpec (preFn ++ compileFn env.tab f fd ++ postFn) = .ok (env.code, env.labels) ∧
      lookupLabel env.labels (fnLabel f) = some (lkm.totalSize preFn) :=
  ProgFnsLinkedWithGen.split_fn (allocOf := fun _ fd => chooseRegAlloc fd) hFns hflook

theorem ProgFnsLinked.split_fn {env : CodeEnv} {p : _root_.L.Prog}
    (hFns : ProgFnsLinked env p) {f : FnName} {fd : FunDecl}
    (hflook : p.lookup f = some fd) :
    ∃ preFn postFn,
      linkResolved (preFn ++ compileFn env.tab f fd ++ postFn) = .ok (env.code, env.labels) ∧
      lookupLabel env.labels (fnLabel f) = some (totalWords preFn) := by
  rcases ProgFnsLinkedGen.split_fn hFns hflook with ⟨preFn, postFn, hlink, hlkp⟩
  exact ⟨preFn, postFn, hlink, by rwa [near_totalSize_eq] at hlkp⟩

private theorem st8_run (a : ArrId) (j v : _root_.L.Word) (st : St) :
    _root_.L.st8 a j v st =
      if j.toNat < (st.mem.arr8 a).size then .ok ((), { st with mem := st.mem.set8 a j v })
      else .error .oob := by
  simp only [_root_.L.st8, Bind.bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get,
    StateT.get, set, MonadStateOf.set, pure, Except.pure,
    throw, MonadExceptOf.throw, throwThe, MonadExcept.throw, Function.comp_apply]
  by_cases hb : j.toNat < (st.mem.arr8 a).size <;> simp only [hb, ↓reduceIte] <;> rfl

private theorem st64_run (s : TieredArray) (j v : _root_.L.Word) (st : St) :
    _root_.L.st64 s j v st =
      if j.toNat < (st.mem.arr64 s).size then .ok ((), { st with mem := st.mem.set64 s j v })
      else .error .oob := by
  simp only [_root_.L.st64, Bind.bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get,
    StateT.get, set, MonadStateOf.set, pure, Except.pure,
    throw, MonadExceptOf.throw, throwThe, MonadExcept.throw, Function.comp_apply]
  by_cases hb : j.toNat < (st.mem.arr64 s).size <;> simp only [hb, ↓reduceIte] <;> rfl

private theorem st32_run (s : TieredArray) (j v : _root_.L.Word) (st : St) :
    _root_.L.st32 s j v st =
      if (j / 2).toNat < (st.mem.arr64 s).size then .ok ((), { st with mem := st.mem.set32 s j v })
      else .error .oob := by
  simp only [_root_.L.st32, Bind.bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get,
    StateT.get, set, MonadStateOf.set, pure, Except.pure,
    throw, MonadExceptOf.throw, throwThe, MonadExcept.throw, Function.comp_apply]
  by_cases hb : (j / 2).toNat < (st.mem.arr64 s).size <;> simp only [hb, ↓reduceIte] <;> rfl

private theorem step_st_sig_err {p : Prog} {s : Stmt} {st : St}
    (hs : (∃ a i e, s = .st8 a i e) ∨ (∃ a i e, s = .st64 a i e) ∨
          (∃ a t i e, s = .st64t a t i e) ∨ (∃ a t i e, s = .st32t a t i e)) :
    _root_.L.step p (fun _ => throw .outOfFuel) s st = _root_.L.step [] (fun _ => throw .outOfFuel) s st ∧
    (∀ sig st', _root_.L.step [] (fun _ => throw .outOfFuel) s st = .ok (sig, st') → sig = .normal) ∧
    (∀ err, _root_.L.step [] (fun _ => throw .outOfFuel) s st = .error err → err = .oob) := by
  rcases hs with ⟨a, i, e, rfl⟩ | ⟨a, i, e, rfl⟩ | ⟨a, t, i, e, rfl⟩ | ⟨a, t, i, e, rfl⟩
  · refine ⟨rfl, ?_, ?_⟩
    · intro sig st' h
      rcases _root_.L.evalE_pure i st with ⟨vi, hi⟩ | hi
      · rcases _root_.L.evalE_pure e st with ⟨ve, he⟩ | he
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi, he, st8_run, pure, StateT.pure, Except.pure] at h
          by_cases hb : vi.toNat < (st.mem.arr8 a).size <;> simp [hb] at h; exact h.1.symm
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi, he] at h; cases h
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi] at h; cases h
    · intro err h
      rcases _root_.L.evalE_pure i st with ⟨vi, hi⟩ | hi
      · rcases _root_.L.evalE_pure e st with ⟨ve, he⟩ | he
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi, he, st8_run, pure, StateT.pure, Except.pure] at h
          by_cases hb : vi.toNat < (st.mem.arr8 a).size <;> simp [hb] at h; exact h.symm
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi, he] at h; cases h; rfl
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi] at h; cases h; rfl
  · refine ⟨rfl, ?_, ?_⟩
    · intro sig st' h
      rcases _root_.L.evalE_pure i st with ⟨vi, hi⟩ | hi
      · rcases _root_.L.evalE_pure e st with ⟨ve, he⟩ | he
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi, he, st64_run, pure, StateT.pure, Except.pure] at h
          by_cases hb : vi.toNat < (st.mem.arr64 (.t0 a)).size <;> simp [hb] at h; exact h.1.symm
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi, he] at h; cases h
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi] at h; cases h
    · intro err h
      rcases _root_.L.evalE_pure i st with ⟨vi, hi⟩ | hi
      · rcases _root_.L.evalE_pure e st with ⟨ve, he⟩ | he
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi, he, st64_run, pure, StateT.pure, Except.pure] at h
          by_cases hb : vi.toNat < (st.mem.arr64 (.t0 a)).size <;> simp [hb] at h; exact h.symm
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi, he] at h; cases h; rfl
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hi] at h; cases h; rfl
  · refine ⟨rfl, ?_, ?_⟩
    · intro sig st' h
      rcases _root_.L.evalE_pure t st with ⟨vt, ht⟩ | ht
      · rcases _root_.L.evalE_pure i st with ⟨vi, hi⟩ | hi
        · rcases _root_.L.evalE_pure e st with ⟨ve, he⟩ | he
          · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht, hi, he, st64_run, pure, StateT.pure, Except.pure] at h
            by_cases hb : vi.toNat < (st.mem.arr64 (tierA a vt)).size <;> simp [hb] at h; exact h.1.symm
          · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht, hi, he] at h; cases h
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht, hi] at h; cases h
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht] at h; cases h
    · intro err h
      rcases _root_.L.evalE_pure t st with ⟨vt, ht⟩ | ht
      · rcases _root_.L.evalE_pure i st with ⟨vi, hi⟩ | hi
        · rcases _root_.L.evalE_pure e st with ⟨ve, he⟩ | he
          · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht, hi, he, st64_run, pure, StateT.pure, Except.pure] at h
            by_cases hb : vi.toNat < (st.mem.arr64 (tierA a vt)).size <;> simp [hb] at h; exact h.symm
          · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht, hi, he] at h; cases h; rfl
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht, hi] at h; cases h; rfl
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht] at h; cases h; rfl
  · refine ⟨rfl, ?_, ?_⟩
    · intro sig st' h
      rcases _root_.L.evalE_pure t st with ⟨vt, ht⟩ | ht
      · rcases _root_.L.evalE_pure i st with ⟨vi, hi⟩ | hi
        · rcases _root_.L.evalE_pure e st with ⟨ve, he⟩ | he
          · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht, hi, he, st32_run, pure, StateT.pure, Except.pure] at h
            by_cases hb : vi.toNat / 2 < (st.mem.arr64 (tierA a vt)).size <;> simp [hb] at h; exact h.1.symm
          · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht, hi, he] at h; cases h
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht, hi] at h; cases h
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht] at h; cases h
    · intro err h
      rcases _root_.L.evalE_pure t st with ⟨vt, ht⟩ | ht
      · rcases _root_.L.evalE_pure i st with ⟨vi, hi⟩ | hi
        · rcases _root_.L.evalE_pure e st with ⟨ve, he⟩ | he
          · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht, hi, he, st32_run, pure, StateT.pure, Except.pure] at h
            by_cases hb : vi.toNat / 2 < (st.mem.arr64 (tierA a vt)).size <;> simp [hb] at h; exact h.symm
          · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht, hi, he] at h; cases h; rfl
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht, hi] at h; cases h; rfl
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, ht] at h; cases h; rfl

private theorem step_copy64_run (p : Prog) (d : WArr) (di : Expr) (s : WArr) (si n : Expr) (st : St)
    {da sa : TieredArray} {vdi vsi vn : _root_.L.Word}
    (hda : _root_.L.warr d st = .ok (da, st)) (hvdi : _root_.L.evalE di st = .ok (vdi, st))
    (hsa : _root_.L.warr s st = .ok (sa, st)) (hvsi : _root_.L.evalE si st = .ok (vsi, st))
    (hvn : _root_.L.evalE n st = .ok (vn, st)) :
    _root_.L.step p (fun _ => throw .outOfFuel) (.copy64 d di s si n) st =
      if vdi.toNat + vn.toNat ≤ (st.mem.arr64 da).size ∧ vsi.toNat + vn.toNat ≤ (st.mem.arr64 sa).size
      then .ok (.normal, { st with mem := st.mem.copy64 da vdi sa vsi vn.toNat })
      else .error .oob := by
  simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hda, hvdi, hsa, hvsi, hvn,
    get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set, pure, Except.pure,
    throw, MonadExceptOf.throw, throwThe, MonadExcept.throw, Function.comp_apply]
  by_cases h1 : vdi.toNat + vn.toNat ≤ (st.mem.arr64 da).size ∧ vsi.toNat + vn.toNat ≤ (st.mem.arr64 sa).size <;>
    simp only [h1] <;> rfl

private theorem step_copy8w_run (p : Prog) (d : WArr) (di : Expr) (s : BSrc) (si n : Expr) (st : St)
    {da : TieredArray} {vdi vsi vn : _root_.L.Word}
    (hda : _root_.L.warr d st = .ok (da, st)) (hvdi : _root_.L.evalE di st = .ok (vdi, st))
    (hvsi : _root_.L.evalE si st = .ok (vsi, st)) (hvn : _root_.L.evalE n st = .ok (vn, st)) :
    _root_.L.step p (fun _ => throw .outOfFuel) (.copy8w d di s si n) st =
      if vdi.toNat + vn.toNat ≤ (st.mem.arr64 da).size ∧ vsi.toNat + vn.toNat ≤ (st.mem.src8 s).size
      then .ok (.normal, { st with mem := st.mem.copy8w da vdi (st.mem.src8 s) vsi vn.toNat })
      else .error .oob := by
  simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hda, hvdi, hvsi, hvn,
    get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set, pure, Except.pure,
    throw, MonadExceptOf.throw, throwThe, MonadExcept.throw, Function.comp_apply]
  by_cases h1 : vdi.toNat + vn.toNat ≤ (st.mem.arr64 da).size ∧ vsi.toNat + vn.toNat ≤ (st.mem.src8 s).size <;>
    simp only [h1] <;> rfl

private theorem step_scan8_run (p : Prog) (x : Var) (s : BSrc) (i e : Expr) (c : List UInt8) (st : St)
    {vi ve : _root_.L.Word}
    (hvi : _root_.L.evalE i st = .ok (vi, st)) (hve : _root_.L.evalE e st = .ok (ve, st)) :
    _root_.L.step p (fun _ => throw .outOfFuel) (.scan8 x s i e c) st =
      if vi ≤ ve ∧ ve.toNat ≤ (st.mem.src8 s).size
      then .ok (.normal, st.setLoc x (UInt64.ofNat (scanN (st.mem.src8 s) c vi.toNat ve.toNat)))
      else .error .oob := by
  simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvi, hve,
    get, getThe, MonadStateOf.get, StateT.get, _root_.L.setLoc, modify, modifyGet, MonadStateOf.modifyGet,
    pure, Except.pure, throw, MonadExceptOf.throw, throwThe, MonadExcept.throw, Function.comp_apply]
  by_cases h1 : vi ≤ ve ∧ ve.toNat ≤ (st.mem.src8 s).size <;> simp only [h1] <;> rfl

private theorem baseStep_sig_err_copy64 (p : Prog) (d : WArr) (di : Expr) (s : WArr) (si n : Expr) (st : St) :
    (∀ sig st', _root_.L.step p (fun _ => throw .outOfFuel) (.copy64 d di s si n) st = .ok (sig, st') → sig = .normal) ∧
    (∀ err, _root_.L.step p (fun _ => throw .outOfFuel) (.copy64 d di s si n) st = .error err → err = .oob) := by
  refine ⟨fun sig st' h => ?_, fun err h => ?_⟩
  · rcases _root_.L.warr_pure d st with ⟨da, hda⟩ | hda
    · rcases _root_.L.evalE_pure di st with ⟨vdi, hvdi⟩ | hvdi
      · rcases _root_.L.warr_pure s st with ⟨sa, hsa⟩ | hsa
        · rcases _root_.L.evalE_pure si st with ⟨vsi, hvsi⟩ | hvsi
          · rcases _root_.L.evalE_pure n st with ⟨vn, hvn⟩ | hvn
            · rw [step_copy64_run p d di s si n st hda hvdi hsa hvsi hvn] at h
              by_cases h1 : vdi.toNat + vn.toNat ≤ (st.mem.arr64 da).size ∧ vsi.toNat + vn.toNat ≤ (st.mem.arr64 sa).size <;>
                simp [h1] at h; exact h.1.symm
            · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hda, hvdi, hsa, hvsi, hvn] at h; cases h
          · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hda, hvdi, hsa, hvsi] at h; cases h
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hda, hvdi, hsa] at h; cases h
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hda, hvdi] at h; cases h
    · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hda] at h; cases h
  · rcases _root_.L.warr_pure d st with ⟨da, hda⟩ | hda
    · rcases _root_.L.evalE_pure di st with ⟨vdi, hvdi⟩ | hvdi
      · rcases _root_.L.warr_pure s st with ⟨sa, hsa⟩ | hsa
        · rcases _root_.L.evalE_pure si st with ⟨vsi, hvsi⟩ | hvsi
          · rcases _root_.L.evalE_pure n st with ⟨vn, hvn⟩ | hvn
            · rw [step_copy64_run p d di s si n st hda hvdi hsa hvsi hvn] at h
              by_cases h1 : vdi.toNat + vn.toNat ≤ (st.mem.arr64 da).size ∧ vsi.toNat + vn.toNat ≤ (st.mem.arr64 sa).size <;>
                simp [h1] at h; exact h.symm
            · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hda, hvdi, hsa, hvsi, hvn] at h; cases h; rfl
          · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hda, hvdi, hsa, hvsi] at h; cases h; rfl
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hda, hvdi, hsa] at h; cases h; rfl
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hda, hvdi] at h; cases h; rfl
    · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hda] at h; cases h; rfl

private theorem baseStep_sig_err_copy8w (p : Prog) (d : WArr) (di : Expr) (s : BSrc) (si n : Expr) (st : St) :
    (∀ sig st', _root_.L.step p (fun _ => throw .outOfFuel) (.copy8w d di s si n) st = .ok (sig, st') → sig = .normal) ∧
    (∀ err, _root_.L.step p (fun _ => throw .outOfFuel) (.copy8w d di s si n) st = .error err → err = .oob) := by
  refine ⟨fun sig st' h => ?_, fun err h => ?_⟩
  · rcases _root_.L.warr_pure d st with ⟨da, hda⟩ | hda
    · rcases _root_.L.evalE_pure di st with ⟨vdi, hvdi⟩ | hvdi
      · rcases _root_.L.evalE_pure si st with ⟨vsi, hvsi⟩ | hvsi
        · rcases _root_.L.evalE_pure n st with ⟨vn, hvn⟩ | hvn
          · rw [step_copy8w_run p d di s si n st hda hvdi hvsi hvn] at h
            by_cases h1 : vdi.toNat + vn.toNat ≤ (st.mem.arr64 da).size ∧ vsi.toNat + vn.toNat ≤ (st.mem.src8 s).size <;>
              simp [h1] at h; exact h.1.symm
          · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hda, hvdi, hvsi, hvn] at h; cases h
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hda, hvdi, hvsi] at h; cases h
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hda, hvdi] at h; cases h
    · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hda] at h; cases h
  · rcases _root_.L.warr_pure d st with ⟨da, hda⟩ | hda
    · rcases _root_.L.evalE_pure di st with ⟨vdi, hvdi⟩ | hvdi
      · rcases _root_.L.evalE_pure si st with ⟨vsi, hvsi⟩ | hvsi
        · rcases _root_.L.evalE_pure n st with ⟨vn, hvn⟩ | hvn
          · rw [step_copy8w_run p d di s si n st hda hvdi hvsi hvn] at h
            by_cases h1 : vdi.toNat + vn.toNat ≤ (st.mem.arr64 da).size ∧ vsi.toNat + vn.toNat ≤ (st.mem.src8 s).size <;>
              simp [h1] at h; exact h.symm
          · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hda, hvdi, hvsi, hvn] at h; cases h; rfl
        · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hda, hvdi, hvsi] at h; cases h; rfl
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hda, hvdi] at h; cases h; rfl
    · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hda] at h; cases h; rfl

private theorem baseStep_sig_err_scan8 (p : Prog) (x : Var) (s : BSrc) (i e : Expr) (c : List UInt8) (st : St) :
    (∀ sig st', _root_.L.step p (fun _ => throw .outOfFuel) (.scan8 x s i e c) st = .ok (sig, st') → sig = .normal) ∧
    (∀ err, _root_.L.step p (fun _ => throw .outOfFuel) (.scan8 x s i e c) st = .error err → err = .oob) := by
  refine ⟨fun sig st' h => ?_, fun err h => ?_⟩
  · rcases _root_.L.evalE_pure i st with ⟨vi, hvi⟩ | hvi
    · rcases _root_.L.evalE_pure e st with ⟨ve, hve⟩ | hve
      · rw [step_scan8_run p x s i e c st hvi hve] at h
        by_cases h1 : vi ≤ ve ∧ ve.toNat ≤ (st.mem.src8 s).size <;> simp [h1] at h; exact h.1.symm
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvi, hve] at h; cases h
    · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvi] at h; cases h
  · rcases _root_.L.evalE_pure i st with ⟨vi, hvi⟩ | hvi
    · rcases _root_.L.evalE_pure e st with ⟨ve, hve⟩ | hve
      · rw [step_scan8_run p x s i e c st hvi hve] at h
        by_cases h1 : vi ≤ ve ∧ ve.toNat ≤ (st.mem.src8 s).size <;> simp [h1] at h; exact h.symm
      · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvi, hve] at h; cases h; rfl
    · simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvi] at h; cases h; rfl

private theorem prog_ret_finish_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (fl : FrameLayout) {sp : BitVec 64} {b : Nat}
    {lm' : _root_.L.Mem} {loc' : _root_.L.Locals} {vs : List _root_.L.Word}
    (brkLbl : Option String) (retLbl : String) (retPc : Nat) (isTail : Bool)
    (na nb : Var → Bool) (tco : TcoCtx)
    (hretLbl : lookupLabel env.labels retLbl = some retPc)
    (hvsLen : vs.length ≤ env.tab.nres)
    (pre cBody post : List AsmItem)
    (hTail : isTail = true → lkm.totalSize pre + lkm.totalSize (cBody ++
      (if isTail then [] else if fl.isLeaf && fl.frameSlots == 0 then [Asm.ret] else [Asm.j retLbl])) = retPc)
    (hlink : lkm.linkSpec (pre ++ (cBody ++
      (if isTail then [] else if fl.isLeaf && fl.frameSlots == 0 then [Asm.ret] else [Asm.j retLbl])) ++ post) =
      .ok (env.code, env.labels))
    (st st1 : State) (k1 : Nat)
    (hrun1 : RV64.run env.rom k1 st = .cont st1)
    (hpc1 : st1.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize cBody)))
    (hret1 : PreservedRetRegs fl st st1)
    (hs0_1 : st1.getReg AbiReg.s0 = BitVec.ofNat 64 b)
    (hm1 : ProgMemRel env.tab L st1.mem lm')
    (hres1 : ResultsInState env.tab L st1 vs)
    (hpm1 : ProgMemOutside (FnWriteMaskR L fl sp) st.mem st1.mem)
    (hhdr : TabHeaderOk L st.mem) :
    StmtOutcomeR env L fl sp b st retLbl brkLbl
      (lkm.totalSize pre + lkm.totalSize (cBody ++
        (if isTail then [] else if fl.isLeaf && fl.frameSlots == 0 then [Asm.ret] else [Asm.j retLbl]))) na nb tco
      (.ok (.ret vs, { mem := lm', loc := loc' }, b)) := by
  cases hT : isTail with
  | true =>
    have hpcFin : st1.pc = BitVec.ofNat 64 (4 * retPc) := by
      rw [hpc1, ← hTail hT, hT]
      simp only [↓reduceIte, lkm.totalSize_append, lkm.totalSize_nil, Nat.add_zero]
    exact Or.inl ⟨retPc, k1, st1, hretLbl, hrun1, Or.inl hpcFin, hvsLen, hret1, hs0_1, Nat.le_refl b,
      hm1, hres1, hpm1, hhdr.of_fnWriteMaskR L hpm1⟩
  | false =>
    let preJ := pre ++ cBody
    by_cases hIR : fl.isLeaf = true ∧ fl.frameSlots = 0
    · have hcond : (fl.isLeaf && fl.frameSlots == 0) = true := by simp [hIR.1, hIR.2]
      have hlinkRet : lkm.linkSpec (preJ ++ [Asm.ret] ++ post) = .ok (env.code, env.labels) := by
        simpa [preJ, hT, hcond, List.append_assoc] using hlink
      have hltRet64 : 4 * lkm.totalSize preJ < 2 ^ 64 := by
        have h := linkResolved_sub_pc64 env preJ [Asm.ret] post hlinkRet
        rw [show lkm.totalSize [Asm.ret] = 1 from by simp only [Asm.ret, lkm.totalSize_instr]] at h; omega
      have hstepRet := step_item_ret_lm lkm env.hrom preJ post hlinkRet hltRet64 st1
        (by simpa [preJ, lkm.totalSize_append] using hpc1)
      let st2 : State := { st1 with pc := st1.getReg AbiReg.ra &&& ~~~1#64 }
      refine Or.inl ⟨retPc, k1 + 1, st2, hretLbl,
        by rw [run_add, hrun1]; exact run_one_cont _ _ st2 hstepRet,
        Or.inr ⟨hIR.1, hIR.2, by change st1.getReg AbiReg.ra &&& ~~~1#64 = _; rw [hret1.leafRa hIR.1]⟩,
        hvsLen, ?_, hs0_1, Nat.le_refl b, hm1, ?_, hpm1, hhdr.of_fnWriteMaskR L hpm1⟩
      · exact ⟨⟨hret1.abi.gp, hret1.abi.sp, hret1.abi.s2⟩, hret1.leafRa, hret1.callee⟩
      · exact ⟨hres1.1, hres1.2⟩
    · have hcond : (fl.isLeaf && fl.frameSlots == 0) = false := by
        cases hlf : fl.isLeaf with
        | false => rfl
        | true =>
          have hne0 : fl.frameSlots ≠ 0 := fun h0 => hIR ⟨hlf, h0⟩
          simp [beq_false_of_ne hne0]
      have hlinkJ : lkm.linkSpec (preJ ++ [Asm.j retLbl] ++ post) = .ok (env.code, env.labels) := by
        simpa [preJ, hT, hcond, List.append_assoc] using hlink
      have h64J : 4 * (lkm.totalSize preJ + lkm.itemSize (.j retLbl)) < 2 ^ 64 := by
        simpa [Asm.j, lkm.totalSize_singleton] using linkResolved_sub_pc64 env preJ [Asm.j retLbl] post hlinkJ
      obtain ⟨kJ, st2, hrunJ, hpc2, hothJ, _, hmemJ⟩ :=
        prog_step_j env preJ post retLbl retPc hretLbl hlinkJ h64J st1 (by simpa [preJ, lkm.totalSize_append] using hpc1)
      have houtAll : ProgMemOutside (FnWriteMaskR L fl sp) st.mem st2.mem := by rw [hmemJ]; exact hpm1
      exact Or.inl ⟨retPc, k1 + kJ, st2, hretLbl, by rw [run_add, hrun1]; exact hrunJ, Or.inl hpc2,
        hvsLen, hret1.trans (PreservedRetRegs.of_other_t6 hothJ),
        (hothJ _ (by decide)).trans hs0_1, Nat.le_refl b,
        (by rw [hmemJ]; exact hm1),
        ⟨fun i hi => (hothJ (resReg i) ⟨resReg_ne_t6 i, (resReg_ne_preserved i).2.2.2.1⟩).trans (hres1.1 i hi),
         fun i hloI hhiI => by rw [hmemJ]; exact hres1.2 i hloI hhiI⟩,
        houtAll, hhdr.of_fnWriteMaskR L houtAll⟩

private theorem prog_ret_step_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (fl : FrameLayout) (hfl : FrameLayoutOk fl) (b : Nat) (lm : _root_.L.Mem) (loc : _root_.L.Locals)
    (sp : BitVec 64) (brkLbl : Option String) (retLbl : String) (retPc : Nat) (isTail : Bool)
    (na nb : Var → Bool) (tco : TcoCtx)
    (es : List _root_.L.Expr) (hEsLen : es.length ≤ env.tab.nres)
    (hesOk : es.all (exprOkB env.tab fl.nlocals) = true)
    (hVfEs : ExprsVarsInFrame fl es)
    (hTmp : usedTempsRetR fl.isLeaf fl.alloc es ≤ fl.usedTemps)
    (hal : isAligned sp 8 = true) (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (htop : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (hretLbl : lookupLabel env.labels retLbl = some retPc)
    (pre post : List AsmItem)
    (hTail : isTail = true → lkm.totalSize pre +
      lkm.totalSize (compileRetR env.tab fl retLbl isTail es) = retPc)
    (hlink : lkm.linkSpec (pre ++ compileRetR env.tab fl retLbl isTail es ++ post) =
      .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hs0 : st.getReg AbiReg.s0 = BitVec.ofNat 64 b)
    (hm : ProgMemRel env.tab L st.mem lm) (hf : ProgFrameOkR L fl sp st loc)
    (hhdr : TabHeaderOk L st.mem) :
    StmtOutcomeR env L fl sp b st retLbl brkLbl
      (lkm.totalSize pre + lkm.totalSize (compileRetR env.tab fl retLbl isTail es)) na nb tco
      (match _root_.L.evalArgs es { mem := lm, loc := loc } with
       | .ok (vs, st') => .ok (.ret vs, st', b)
       | .error err => .error err) := by
  let cJ := if isTail then [] else if fl.isLeaf && fl.frameSlots == 0 then [Asm.ret] else [Asm.j retLbl]
  cases es with
  | nil =>
    have hcr : compileRetR env.tab fl retLbl isTail [] = copyTempsToResultsR env.tab fl 0 0 ++ cJ := rfl
    rw [hcr] at hlink hTail ⊢
    have hlinkC : lkm.linkSpec (pre ++ copyTempsToResultsR env.tab fl 0 ([] : List _root_.L.Word).length ++ (cJ ++ post)) =
        .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
    obtain ⟨k1, st1, hrun1, hpc1, hpres1, hra1, hcal1, hres1, hout1⟩ :=
      reg_copyTempsToResultsR_sim env L fl hal hlo htop ([] : List _root_.L.Word) (Nat.zero_le _)
        pre (cJ ++ post) hlinkC st hpc hgp hsp (fun _ h => by simp at h)
    have hpm1 : ProgMemOutside (FnWriteMaskR L fl sp) st.mem st1.mem :=
      progMemOutside_of_resGlobR L fl sp (MemEqOutside.mono (resOnlySpan_sub_resGlob L) hout1)
    have hm1 : ProgMemRel env.tab L st1.mem lm := ProgMemRel.of_resOnly L hout1 hm
    exact prog_ret_finish_sim env L fl (lm' := lm) (loc' := loc) (vs := [])
      brkLbl retLbl retPc isTail na nb tco hretLbl (Nat.zero_le _) pre (copyTempsToResultsR env.tab fl 0 0) post
      hTail hlink st st1 k1 hrun1 hpc1 ⟨hpres1.toNoS0, fun _ => hra1, fun r hr _ => hcal1 r hr⟩
      (hpres1.s0.trans hs0) hm1 hres1 hpm1 hhdr
  | cons e1 rest =>
    cases rest with
    | nil =>
      have hcr : compileRetR env.tab fl retLbl isTail [e1] = compileETo env.tab fl 0 AbiReg.a0 e1 ++ cJ := rfl
      rw [hcr] at hlink hTail ⊢
      have he1Ok : exprOkB env.tab fl.nlocals e1 = true := by simpa using hesOk
      have hlinkE : lkm.linkSpec (pre ++ compileETo env.tab fl 0 AbiReg.a0 e1 ++ (cJ ++ post)) =
          .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
      have hsim := reg_evalExpr_sim env L fl hfl lm loc hal hlo htop e1 pre _ 0 AbiReg.a0 (Or.inl rfl)
        he1Ok (fun x hx => hVfEs x (by simp [hx])) (by simpa [usedTempsRetR] using hTmp) hlinkE
        (linkResolved_sub_pc64 env pre (compileETo env.tab fl 0 AbiReg.a0 e1) _ hlinkE) st hpc hgp ht5 hsp hm hf
      cases he : _root_.L.evalE e1 { mem := lm, loc := loc } with
      | error err =>
        have herr := evalE_err_eq_oob e1 { mem := lm, loc := loc } he; subst herr
        have hargsErr : _root_.L.evalArgs [e1] { mem := lm, loc := loc } = .error .oob := by
          simp only [_root_.L.evalArgs, Bind.bind, StateT.bind, Except.bind, he]
        rw [hargsErr]; rw [he] at hsim; dsimp only
        obtain ⟨k, r', hrun, hpc', hpres, hout⟩ := hsim
        exact stmtOutcomeR_of_err_oob htop ⟨k, r', hrun, hpc', hpres.abi,
          ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo htop (Nat.zero_le _)) hout⟩
      | ok res =>
        rcases res with ⟨v, st1'⟩
        have hst1' : st1' = { mem := lm, loc := loc } := by
          rcases _root_.L.evalE_pure e1 { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
          · rw [he] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
          · rw [he] at herr; cases herr
        subst hst1'
        have hargsOk : _root_.L.evalArgs [e1] { mem := lm, loc := loc } = .ok ([v], { mem := lm, loc := loc }) := by
          simp only [_root_.L.evalArgs, Bind.bind, StateT.bind, Except.bind, he, Pure.pure, StateT.pure, Except.pure]
        rw [hargsOk]; rw [he] at hsim; dsimp only
        obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, hout1⟩ := hsim
        have hpm1 : ProgMemOutside (FnWriteMaskR L fl sp) st.mem st1.mem :=
          ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo htop (Nat.zero_le _)) hout1
        have hm1 := ProgMemRel.of_tempSpanR hlo htop (Nat.zero_le _) hout1 hm
        have hret1 : PreservedRetRegs fl st st1 := (PreservedFrameRegs.of_a0 hpres1).toFrameNoS0_all.toRetRegs hfl
        have hresR : ResultsInState env.tab L st1 [v] := by
          refine ⟨fun i hi => ?_, fun i hloI hhiI => by simp [maxRes] at hloI hhiI; omega⟩
          have hi0 : i = 0 := by simp [maxRes] at hi; omega
          subst hi0; exact ha0_1
        exact prog_ret_finish_sim env L fl (lm' := lm) (loc' := loc) (vs := [v])
          brkLbl retLbl retPc isTail na nb tco hretLbl hEsLen pre (compileETo env.tab fl 0 AbiReg.a0 e1) post
          hTail hlink st st1 k1 hrun1 hpc1 hret1 (hpres1.abi.s0.trans hs0) hm1 hresR hpm1 hhdr
    | cons e2 rest2 =>
      let es2 := e1 :: e2 :: rest2
      have hEs2Len : es2.length ≤ env.tab.nres := hEsLen
      by_cases hrev : revDirectSafe fl.isLeaf fl.alloc es2 = true
      · have hrev' : es2.length ≤ maxRes ∧ revDirectSafeAux fl.alloc 0 es2 = true := by
          simpa [revDirectSafe, Bool.and_eq_true, decide_eq_true_eq] using hrev
        have hTmpRev : maxUsedTempsExprs es2 ≤ fl.usedTemps := by
          simpa [usedTempsRetR, es2, hrev] using hTmp
        have hcr : compileRetR env.tab fl retLbl isTail es2 = compileEvalRevToRegs env.tab fl 0 es2 ++ cJ := by
          simp [compileRetR, es2, hrev, cJ]
        change StmtOutcomeR env L fl sp b st retLbl brkLbl
          (lkm.totalSize pre + lkm.totalSize (compileRetR env.tab fl retLbl isTail es2)) na nb tco _
        rw [hcr] at hlink hTail ⊢
        have hlinkR : lkm.linkSpec (pre ++ compileEvalRevToRegs env.tab fl 0 es2 ++ (cJ ++ post)) =
            .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
        have hsimR := reg_evalRevToRegs_sim env L fl hfl lm loc hal hlo htop es2 0 pre (cJ ++ post)
          (by omega) hrev'.2 hesOk hVfEs hTmpRev hlinkR (linkResolved_sub_pc64 env pre _ _ hlinkR) st hpc hgp ht5 hsp hm hf
        cases hea : _root_.L.evalArgs es2 { mem := lm, loc := loc } with
        | error err =>
          have herr := evalArgs_err_eq_oob es2 { mem := lm, loc := loc } hea
          subst herr; rw [hea] at hsimR; dsimp only
          obtain ⟨kE, rE, hrunE, hpcE, hpresE, houtE⟩ := hsimR
          exact stmtOutcomeR_of_err_oob htop ⟨kE, rE, hrunE, hpcE, hpresE.abi,
            ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo htop (Nat.zero_le _)) houtE⟩
        | ok res =>
          rcases res with ⟨vs, st1'⟩
          have hst1' : st1' = { mem := lm, loc := loc } := by
            rcases _root_.L.evalArgs_pure es2 { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
            · rw [hea] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
            · rw [hea] at herr; cases herr
          subst hst1'
          rw [hea] at hsimR; dsimp only
          obtain ⟨k1, st1, hrun1, hpc1, hvslen, hregs1, hpres1, hout1⟩ := hsimR
          have hpm1 : ProgMemOutside (FnWriteMaskR L fl sp) st.mem st1.mem :=
            ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo htop (Nat.zero_le _)) hout1
          have hm1 := ProgMemRel.of_tempSpanR hlo htop (Nat.zero_le _) hout1 hm
          have hret1 : PreservedRetRegs fl st st1 :=
            ⟨hpres1.abi.toNoS0, hpres1.leafRa, fun r hr _ =>
              hpres1.regs r (calleeSaved_mem_allowed true hr) (fun ⟨d, _, heq⟩ => resReg_not_mem_calleeSaved (0 + d) hr heq)⟩
          have hresR : ResultsInState env.tab L st1 vs := by
            have hesLe := hrev'.1
            refine ⟨fun i hi => ?_, fun i hloI hhiI => by simp only [es2, List.length_cons] at hvslen hesLe; omega⟩
            have hiLt : i < vs.length := by simp only [es2, List.length_cons] at hvslen; omega
            have h := hregs1 i hiLt
            simp only [Nat.zero_add] at h
            rw [h, List.getD, List.getElem?_eq_getElem hiLt, Option.getD_some]
          exact prog_ret_finish_sim env L fl (lm' := lm) (loc' := loc) (vs := vs)
            brkLbl retLbl retPc isTail na nb tco hretLbl (by omega) pre (compileEvalRevToRegs env.tab fl 0 es2) post
            hTail hlink st st1 k1 hrun1 hpc1 hret1 (hpres1.abi.s0.trans hs0) hm1 hresR hpm1 hhdr
      · have hTmpAll : usedTempsExprs es2 ≤ fl.usedTemps := by
          simpa [usedTempsRetR, es2, hrev] using hTmp
        let cE := compileEvalExprsToTempsR env.tab fl 0 es2
        let cC := copyTempsToResultsR env.tab fl 0 es2.length
        have hcr : compileRetR env.tab fl retLbl isTail es2 = (cE ++ cC) ++ cJ := by
          simp [compileRetR, es2, hrev, cE, cC, cJ, List.append_assoc]
        change StmtOutcomeR env L fl sp b st retLbl brkLbl
          (lkm.totalSize pre + lkm.totalSize (compileRetR env.tab fl retLbl isTail es2)) na nb tco _
        rw [hcr] at hlink hTail ⊢
        have hlinkE : lkm.linkSpec (pre ++ cE ++ (cC ++ cJ ++ post)) = .ok (env.code, env.labels) := by
          simpa [List.append_assoc] using hlink
        have hsim := reg_evalArgs_sim env L fl hfl lm loc hal hlo htop es2 pre _ 0 hesOk hVfEs (by omega)
          hlinkE (linkResolved_sub_pc64 env pre cE _ hlinkE) st hpc hgp ht5 hsp hm hf
        cases hea : _root_.L.evalArgs es2 { mem := lm, loc := loc } with
        | error err =>
          have herr := evalArgs_err_eq_oob es2 { mem := lm, loc := loc } hea
          subst herr; rw [hea] at hsim; dsimp only
          obtain ⟨k, r', hrun, hpc', hpres, hout⟩ := hsim
          exact stmtOutcomeR_of_err_oob htop ⟨k, r', hrun, hpc', hpres.abi,
            ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo htop (Nat.zero_le _)) hout⟩
        | ok res =>
          rcases res with ⟨vs, st1'⟩
          have hst1' : st1' = { mem := lm, loc := loc } := by
            rcases _root_.L.evalArgs_pure es2 { mem := lm, loc := loc } with ⟨_, hok⟩ | herr
            · rw [hea] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
            · rw [hea] at herr; cases herr
          subst hst1'
          have hvlen := evalArgs_length es2 { mem := lm, loc := loc } hea
          rw [hea] at hsim; dsimp only
          obtain ⟨k1, st1, hrun1, hpc1, _, hslots, hpres1, hout1⟩ := hsim
          have hpm1 : ProgMemOutside (FnWriteMaskR L fl sp) st.mem st1.mem :=
            ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo htop (Nat.zero_le _)) hout1
          have hm1 := ProgMemRel.of_tempSpanR hlo htop (Nat.zero_le _) hout1 hm
          let pre1 := pre ++ cE
          have hlinkC : lkm.linkSpec (pre1 ++ copyTempsToResultsR env.tab fl 0 vs.length ++ (cJ ++ post)) =
              .ok (env.code, env.labels) := by
            rw [hvlen]; simpa [pre1, cC, List.append_assoc] using hlinkE
          have hcnt : 0 + vs.length ≤ fl.usedTemps := by
            rw [hvlen, Nat.zero_add]; exact Nat.le_trans (usedTempsExprs_ge_length es2) hTmpAll
          obtain ⟨k2, st2, hrun2, hpc2, hpres2, hra2, hcal2, hres2, hout2⟩ :=
            reg_copyTempsToResultsR_sim env L fl hal hlo htop vs hcnt pre1 (cJ ++ post) hlinkC
              st1 (by simpa [pre1, lkm.totalSize_append] using hpc1)
              (hpres1.abi.gp.trans hgp) (hpres1.abi.sp.trans hsp) hslots
          have hpm2 : ProgMemOutside (FnWriteMaskR L fl sp) st1.mem st2.mem :=
            progMemOutside_of_resGlobR L fl sp (MemEqOutside.mono (resOnlySpan_sub_resGlob L) hout2)
          have hm2 : ProgMemRel env.tab L st2.mem lm := ProgMemRel.of_resOnly L hout2 hm1
          have hret12 : PreservedRetRegs fl st st2 :=
            hpres1.toFrameNoS0_all.trans_ret hfl ⟨hpres2.toNoS0, fun _ => hra2, fun r hr _ => hcal2 r hr⟩
          exact prog_ret_finish_sim env L fl (lm' := lm) (loc' := loc) (vs := vs)
            brkLbl retLbl retPc isTail na nb tco hretLbl (by omega) pre (cE ++ cC) post
            hTail hlink st st2 (k1 + k2) (by rw [run_add, hrun1]; exact hrun2)
            (by rw [hpc2, hvlen]; simp only [pre1, cC, lkm.totalSize_append, Nat.add_assoc])
            hret12 (hpres2.s0.trans (hpres1.abi.s0.trans hs0)) hm2 hres2 (hpm1.trans hpm2) hhdr


theorem regAllocGraphValid_extract {fl : FrameLayout} {fd : FunDecl}
    (hgr : regAllocGraphValid fl.isLeaf fl.nlocals fl.alloc fd = true) :
    (∀ y ry, fl.alloc.lookup y = some ry →
      (stmtVarSafe y (fun x => (x != y) && (fl.alloc.lookup x == some ry))
        (!fl.isLeaf && (ry ∈ leafExtraBank)) fd.body false false).2 = true) ∧
    (fl.isLeaf = false → stmtCallResValid fl.alloc fd.body = true) := by
  simp only [regAllocGraphValid, Bool.and_eq_true, List.all_eq_true] at hgr
  refine ⟨fun y ry hly => ?_, fun hnl => by have h1 := hgr.1; simp [hnl] at h1; exact h1⟩
  have h2 := hgr.2 (y, ry) (list_lookup_mem hly)
  exact h2.2.1

theorem progExecB_step_lbls {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab) (p : _root_.L.Prog)
    (_hpOk : progOkB env.tab p = true)
    (_hpArgs : progArgsOkB p = true)
    (hFnLbls : ∀ {f : FnName} {fd : FunDecl}, p.lookup f = some fd →
      ∃ pc, lookupLabel env.labels (fnLabel f) = some pc) :
    ∀ (b : Nat) (s : _root_.L.Stmt),
      (∀ b', b' < b → FnCallSimGenCallee env L p b') →
      ∀ (fl : FrameLayout), FrameLayoutOk fl →
      ∀ (na nb : Var → Bool) (tco : TcoCtx) (lm : _root_.L.Mem) (loc : _root_.L.Locals)
        (sp : BitVec 64) (pfx : String) (lblId : Nat)
        (brkLbl : Option String) (retLbl : String) (retPc : Nat) (isTail : Bool)
        (pre post : List AsmItem),
        stmtOkB env.tab p fl.nlocals brkLbl.isSome s = true →
        stmtArgsOkB p s = true →
        StmtVarsInFrame fl s →
        usedTempsStmtR fl.isLeaf fl.alloc s ≤ fl.usedTemps →
        (fl.isLeaf = true → stmtHasCall s = false) →
        (∀ y ry, fl.alloc.lookup y = some ry →
          (stmtVarSafe y (fun x => (x != y) && (fl.alloc.lookup x == some ry))
            (!fl.isLeaf && (ry ∈ leafExtraBank)) s (na y) (nb y)).2 = true) →
        (fl.isLeaf = false → stmtCallResValid fl.alloc s = true) →
        (fl.useT5Gp = true → stmtHasCopyScan s = false) →
        (stmtHasAbort0 s = true → Abort0StubOk env pfx) →
        b < 2 ^ 64 →
        isAligned sp 8 = true →
        L.stackLimit.toNat + stackNeedB p b s { mem := lm, loc := loc } ≤ sp.toNat →
        sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat →
        lookupLabel env.labels retLbl = some retPc →
        (∀ tgt, brkLbl = some tgt → ∃ tgtPc, lookupLabel env.labels tgt = some tgtPc) →
        (isTail = true → lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail s).1 = retPc) →
        lkm.linkSpec (pre ++ (compileSR env.tab fl pfx lblId brkLbl retLbl isTail s).1 ++ post) =
          .ok (env.code, env.labels) →
        ∀ st : State,
          st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
          st.getReg AbiReg.gp = L.T →
          T5GpOk L fl st →
          st.getReg AbiReg.sp = sp →
          st.getReg AbiReg.s0 = BitVec.ofNat 64 b →
          ProgMemRel env.tab L st.mem lm →
          ProgFrameOkLive L fl sp st loc (fun x => (stmtVarCallFree x s (na x) (nb x)).1) →
          TabHeaderOk L st.mem →
          TcoStateOk fl sp tco st →
          StmtOutcomeR env L fl sp b st retLbl brkLbl
            (lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail s).1) na nb tco
            (execB p b s { mem := lm, loc := loc }) := by
  refine execB_ind (fun b s =>
    (∀ b', b' < b → FnCallSimGenCallee env L p b') →
    ∀ (fl : FrameLayout), FrameLayoutOk fl →
    ∀ (na nb : Var → Bool) (tco : TcoCtx) (lm : _root_.L.Mem) (loc : _root_.L.Locals)
      (sp : BitVec 64) (pfx : String) (lblId : Nat)
      (brkLbl : Option String) (retLbl : String) (retPc : Nat) (isTail : Bool)
      (pre post : List AsmItem),
      stmtOkB env.tab p fl.nlocals brkLbl.isSome s = true →
      stmtArgsOkB p s = true →
      StmtVarsInFrame fl s →
      usedTempsStmtR fl.isLeaf fl.alloc s ≤ fl.usedTemps →
      (fl.isLeaf = true → stmtHasCall s = false) →
      (∀ y ry, fl.alloc.lookup y = some ry →
        (stmtVarSafe y (fun x => (x != y) && (fl.alloc.lookup x == some ry))
          (!fl.isLeaf && (ry ∈ leafExtraBank)) s (na y) (nb y)).2 = true) →
      (fl.isLeaf = false → stmtCallResValid fl.alloc s = true) →
      (fl.useT5Gp = true → stmtHasCopyScan s = false) →
      (stmtHasAbort0 s = true → Abort0StubOk env pfx) →
      b < 2 ^ 64 →
      isAligned sp 8 = true →
      L.stackLimit.toNat + stackNeedB p b s { mem := lm, loc := loc } ≤ sp.toNat →
      sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat →
      lookupLabel env.labels retLbl = some retPc →
      (∀ tgt, brkLbl = some tgt → ∃ tgtPc, lookupLabel env.labels tgt = some tgtPc) →
      (isTail = true → lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail s).1 = retPc) →
      lkm.linkSpec (pre ++ (compileSR env.tab fl pfx lblId brkLbl retLbl isTail s).1 ++ post) =
        .ok (env.code, env.labels) →
      ∀ st : State,
        st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
        st.getReg AbiReg.gp = L.T →
        T5GpOk L fl st →
        st.getReg AbiReg.sp = sp →
        st.getReg AbiReg.s0 = BitVec.ofNat 64 b →
        ProgMemRel env.tab L st.mem lm →
        ProgFrameOkLive L fl sp st loc (fun x => (stmtVarCallFree x s (na x) (nb x)).1) →
        TabHeaderOk L st.mem →
        TcoStateOk fl sp tco st →
        StmtOutcomeR env L fl sp b st retLbl brkLbl
          (lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail s).1) na nb tco
          (execB p b s { mem := lm, loc := loc })) ?_
  intro b s ih hcall fl hfl na nb tco lm loc sp pfx lblId brkLbl retLbl retPc isTail pre post
    hsOk hsArgs hVf hTmp hLeaf hSafe hCallRes hCopyScan habort0 hb64 hal hlim htop hretLbl hbrkLbl hTail hlink
    st hpc hgp ht5 hsp hs0 hm hf hhdr htco
  cases s with
  | skip =>
    rw [execB_base_step p b .skip _ (by simp)]
    simp only [_root_.L.step, pure, StateT.pure, Except.pure, compileSR, lkm.totalSize_nil, Nat.add_zero]
    exact ⟨0, st, rfl, hpc, PreservedFrameNoS0.refl fl st, hs0, Nat.le_refl b,
      hm, hf, ProgMemOutside.refl _ _, hhdr⟩
  | brk =>
    simp only [stmtOkB] at hsOk
    cases hbrk : brkLbl with
    | none => simp [hbrk] at hsOk
    | some tgt =>
      obtain ⟨tgtPc, htgtPc⟩ := hbrkLbl tgt hbrk
      have hce : (compileSR env.tab fl pfx lblId (some tgt) retLbl isTail .brk).1 = [Asm.j tgt] := by simp [compileSR]
      rw [hbrk, hce] at hlink
      have hpcJ : 4 * (lkm.totalSize pre + lkm.itemSize (.j tgt)) < 2 ^ 64 := by
        simpa [Asm.j, lkm.totalSize_singleton] using linkResolved_sub_pc64 env pre [Asm.j tgt] post hlink
      obtain ⟨kJ, r', hrunJ, hpc', hothJ, _, hmemJ⟩ :=
        prog_step_j env pre post tgt tgtPc htgtPc hlink hpcJ st hpc
      rw [execB_base_step p b .brk _ (by simp)]
      simp only [_root_.L.step, pure, StateT.pure, Except.pure]
      have hframeValid : (frameSpanR fl sp).valid := Nat.le_trans htop L.hStackValid
      exact ⟨tgt, rfl, tgtPc, kJ, r', htgtPc, hrunJ, hpc',
        PreservedFrameNoS0.of_other_t6 hothJ, (hothJ _ (by decide)).trans hs0, Nat.le_refl b,
        (by rw [hmemJ]; exact hm),
        hf.of_other_t6 hfl hframeValid hothJ hmemJ,
        (by rw [hmemJ]; exact ProgMemOutside.refl _ _), (by rw [hmemJ]; exact hhdr)⟩
  | set x e =>
    let loc' := ghostLoc fl sp st loc (fun y => (stmtVarCallFree y (.set x e) (na y) (nb y)).1)
    have hf' := ghostLoc_frameOk hf
    apply stmtOutcomeR_of_ghost (loc' := loc') (ghostLoc_agree _ _ _ _ _)
    simp only [stmtOkB, Bool.and_eq_true, decide_eq_true_eq] at hsOk
    dsimp only [usedTempsStmtR, usedTempsStmt] at hTmp
    have hnoClob : ∀ rx, fl.alloc.lookup x = some rx → ∀ y, y ≠ x → na y = true → fl.alloc.lookup y ≠ some rx := by
      intro rx hlx y hne hnay hly
      have h := hSafe y rx hly
      simp [stmtVarSafe, hlx, hnay, Ne.symm hne] at h
    have hsim := reg_set_sim env L fl hfl lm loc' hal (by omega) htop x e pfx lblId brkLbl retLbl isTail
      pre post hsOk.1 hsOk.2 (fun z hz => hVf z (by simp [stmtUsesVar, hz])) na hnoClob hTmp hlink st hpc hgp ht5 hsp hm hf'
    rw [execB_set]
    cases he : _root_.L.evalE e { mem := lm, loc := loc' } with
    | error err =>
      have herr := evalE_err_eq_oob e { mem := lm, loc := loc' } he
      subst herr; rw [he] at hsim; dsimp only
      obtain ⟨k, r', hrun, hpc', hpres, hout⟩ := hsim
      exact stmtOutcomeR_of_err_oob htop ⟨k, r', hrun, hpc', hpres.abi, hout⟩
    | ok res =>
      rcases res with ⟨v, st1'⟩
      have hst1' : st1' = { mem := lm, loc := loc' } := by
        rcases _root_.L.evalE_pure e { mem := lm, loc := loc' } with ⟨_, hok⟩ | herr
        · rw [he] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
        · rw [he] at herr; cases herr
      subst hst1'; rw [he] at hsim; dsimp only
      exact stmtOutcomeR_of_base_normal_live hs0 hhdr hsim
  | gset g e =>
    let loc' := ghostLoc fl sp st loc (fun y => (stmtVarCallFree y (.gset g e) (na y) (nb y)).1)
    have hf' := ghostLoc_frameOk hf
    apply stmtOutcomeR_of_ghost (loc' := loc') (ghostLoc_agree _ _ _ _ _)
    simp only [stmtOkB, Bool.and_eq_true, decide_eq_true_eq] at hsOk
    dsimp only [usedTempsStmtR, usedTempsStmt] at hTmp
    have hsim := reg_gset_sim env L fl hfl lm loc' hal (by omega) htop g e pfx lblId brkLbl retLbl isTail
      pre post hsOk.1 hsOk.2 (fun z hz => hVf z (by simp [stmtUsesVar, hz])) hTmp hlink st hpc hgp ht5 hsp hm hf'
    rw [execB_gset]
    cases he : _root_.L.evalE e { mem := lm, loc := loc' } with
    | error err =>
      have herr := evalE_err_eq_oob e { mem := lm, loc := loc' } he
      subst herr; rw [he] at hsim; dsimp only
      obtain ⟨k, r', hrun, hpc', hpres, hout⟩ := hsim
      exact stmtOutcomeR_of_err_oob htop ⟨k, r', hrun, hpc', hpres.abi, hout⟩
    | ok res =>
      rcases res with ⟨v, st1'⟩
      have hst1' : st1' = { mem := lm, loc := loc' } := by
        rcases _root_.L.evalE_pure e { mem := lm, loc := loc' } with ⟨_, hok⟩ | herr
        · rw [he] at hok; exact (Prod.mk.inj (Except.ok.inj hok)).2
        · rw [he] at herr; cases herr
      subst hst1'; rw [he] at hsim; dsimp only
      exact stmtOutcomeR_of_base_normal hs0 hhdr hsim
  | st8 _ _ _ =>
    simp [stmtOkB] at hsOk
  | st64 a i e =>
    let loc' := ghostLoc fl sp st loc (fun y => (stmtVarCallFree y (.st64 a i e) (na y) (nb y)).1)
    have hf' := ghostLoc_frameOk hf
    apply stmtOutcomeR_of_ghost (loc' := loc') (ghostLoc_agree _ _ _ _ _)
    simp only [stmtOkB, Bool.and_eq_true] at hsOk
    have hsim := reg_st64_sim env L fl hfl lm loc' hal (by omega) htop a i e pfx lblId brkLbl retLbl isTail
      pre post hsOk.1.1 hsOk.1.2 hsOk.2
      (fun z hz => hVf z (by simp [stmtUsesVar, hz])) (fun z hz => hVf z (by simp [stmtUsesVar, hz]))
      hTmp hlink st hpc hgp ht5 hsp hm hf'
    have ⟨hpEq, hsigN, herrOob⟩ := step_st_sig_err (p := p) (s := .st64 a i e) (st := ⟨lm, loc'⟩) (Or.inr (Or.inl ⟨a, i, e, rfl⟩))
    rw [execB_st64, hpEq]
    cases hst : _root_.L.step [] (fun _ => throw .outOfFuel) (.st64 a i e) ⟨lm, loc'⟩ with
    | error err =>
      have herr := herrOob err hst; subst herr; rw [hst] at hsim; dsimp only
      obtain ⟨k, r', hrun, hpc', hpres, hout⟩ := hsim
      exact stmtOutcomeR_of_err_oob htop ⟨k, r', hrun, hpc', hpres.abi, hout⟩
    | ok res =>
      rcases res with ⟨sig', st'⟩
      have hsig := hsigN sig' st' hst; subst hsig; rw [hst] at hsim; dsimp only
      exact stmtOutcomeR_of_base_normal hs0 hhdr hsim
  | st64t a t i e =>
    let loc' := ghostLoc fl sp st loc (fun y => (stmtVarCallFree y (.st64t a t i e) (na y) (nb y)).1)
    have hf' := ghostLoc_frameOk hf
    apply stmtOutcomeR_of_ghost (loc' := loc') (ghostLoc_agree _ _ _ _ _)
    simp only [stmtOkB, Bool.and_eq_true] at hsOk
    have hsim := reg_st64t_sim env L fl hfl lm loc' hal (by omega) htop a t i e pfx lblId brkLbl retLbl isTail
      pre post hsOk.1.1.1 hsOk.1.1.2 hsOk.1.2 hsOk.2
      (fun z hz => hVf z (by simp [stmtUsesVar, hz]))
      (fun z hz => hVf z (by simp [stmtUsesVar, hz]))
      (fun z hz => hVf z (by simp [stmtUsesVar, hz]))
      hTmp hlink st hpc hgp ht5 hsp hm hf'
    have ⟨hpEq, hsigN, herrOob⟩ := step_st_sig_err (p := p) (s := .st64t a t i e) (st := ⟨lm, loc'⟩) (Or.inr (Or.inr (Or.inl ⟨a, t, i, e, rfl⟩)))
    rw [execB_st64t, hpEq]
    cases hst : _root_.L.step [] (fun _ => throw .outOfFuel) (.st64t a t i e) ⟨lm, loc'⟩ with
    | error err =>
      have herr := herrOob err hst; subst herr; rw [hst] at hsim; dsimp only
      obtain ⟨k, r', hrun, hpc', hpres, hout⟩ := hsim
      exact stmtOutcomeR_of_err_oob htop ⟨k, r', hrun, hpc', hpres.abi, hout⟩
    | ok res =>
      rcases res with ⟨sig', st'⟩
      have hsig := hsigN sig' st' hst; subst hsig; rw [hst] at hsim; dsimp only
      exact stmtOutcomeR_of_base_normal hs0 hhdr hsim
  | st32t a t i e =>
    let loc' := ghostLoc fl sp st loc (fun y => (stmtVarCallFree y (.st32t a t i e) (na y) (nb y)).1)
    have hf' := ghostLoc_frameOk hf
    apply stmtOutcomeR_of_ghost (loc' := loc') (ghostLoc_agree _ _ _ _ _)
    simp only [stmtOkB, Bool.and_eq_true] at hsOk
    have hsim := reg_st32t_sim env L fl hfl lm loc' hal (by omega) htop a t i e pfx lblId brkLbl retLbl isTail
      pre post hsOk.1.1.1 hsOk.1.1.2 hsOk.1.2 hsOk.2
      (fun z hz => hVf z (by simp [stmtUsesVar, hz]))
      (fun z hz => hVf z (by simp [stmtUsesVar, hz]))
      (fun z hz => hVf z (by simp [stmtUsesVar, hz]))
      hTmp hlink st hpc hgp ht5 hsp hm hf'
    have ⟨hpEq, hsigN, herrOob⟩ := step_st_sig_err (p := p) (s := .st32t a t i e) (st := ⟨lm, loc'⟩) (Or.inr (Or.inr (Or.inr ⟨a, t, i, e, rfl⟩)))
    rw [execB_st32t, hpEq]
    cases hst : _root_.L.step [] (fun _ => throw .outOfFuel) (.st32t a t i e) ⟨lm, loc'⟩ with
    | error err =>
      have herr := herrOob err hst; subst herr; rw [hst] at hsim; dsimp only
      obtain ⟨k, r', hrun, hpc', hpres, hout⟩ := hsim
      exact stmtOutcomeR_of_err_oob htop ⟨k, r', hrun, hpc', hpres.abi, hout⟩
    | ok res =>
      rcases res with ⟨sig', st'⟩
      have hsig := hsigN sig' st' hst; subst hsig; rw [hst] at hsim; dsimp only
      exact stmtOutcomeR_of_base_normal hs0 hhdr hsim
  | ret es =>
    let loc' := ghostLoc fl sp st loc (fun y => (stmtVarCallFree y (.ret es) (na y) (nb y)).1)
    have hf' := ghostLoc_frameOk hf
    apply stmtOutcomeR_of_ghost (loc' := loc') (ghostLoc_agree _ _ _ _ _)
    simp only [stmtOkB, Bool.and_eq_true, decide_eq_true_eq] at hsOk
    dsimp only [usedTempsStmtR] at hTmp
    have hce : (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.ret es)).1 =
        compileRetR env.tab fl retLbl isTail es := rfl
    rw [hce] at hlink hTail ⊢
    rw [execB_ret]
    exact prog_ret_step_sim env L fl hfl b lm loc' sp brkLbl retLbl retPc isTail na nb tco es
      hsOk.1 hsOk.2 (fun z hz => hVf z (by simp [stmtUsesVar, hz])) hTmp hal (by omega) htop hretLbl pre post hTail hlink
      st hpc hgp ht5 hsp hs0 hm hf' hhdr
  | abort e =>
    let loc' := ghostLoc fl sp st loc (fun y => (stmtVarCallFree y (.abort e) (na y) (nb y)).1)
    have hf' := ghostLoc_frameOk hf
    apply stmtOutcomeR_of_ghost (loc' := loc') (ghostLoc_agree _ _ _ _ _)
    simp only [stmtOkB] at hsOk
    dsimp only [usedTempsStmtR, usedTempsStmt] at hTmp
    by_cases h0 : (e.constVal? == some 0) = true
    · have he0 : e = .const 0 := by
        cases e with
        | const w =>
          simp only [Expr.constVal?, beq_iff_eq, Option.some.injEq] at h0
          subst h0; rfl
        | _ => simp [Expr.constVal?] at h0
      subst he0
      obtain ⟨ab0Pc, hab0Lbl, hstub⟩ := habort0 rfl
      have hce : (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.abort (.const 0))).1 =
          [Asm.j s!"{pfx}_abort0stub"] := rfl
      rw [hce] at hlink
      have h64J : 4 * (lkm.totalSize pre + lkm.itemSize (.j s!"{pfx}_abort0stub")) < 2 ^ 64 := by
        simpa [Asm.j, lkm.totalSize_singleton] using linkResolved_sub_pc64 env pre [Asm.j s!"{pfx}_abort0stub"] post hlink
      obtain ⟨kJ, st1, hrunJ, hpc1, _, hpresJ, hmemJ⟩ :=
        prog_step_j env pre post s!"{pfx}_abort0stub" ab0Pc hab0Lbl hlink h64J st hpc
      obtain ⟨kA, r', hrunA, hpcA, ha0A, hpresA, hmemA⟩ := hstub st1 hpc1
      rw [execB_abort]
      exact ⟨kJ + kA, r', by rw [run_add, hrunJ]; exact hrunA, hpcA, ha0A, hpresJ.toTramp.trans hpresA,
        by rw [hmemA, hmemJ]; exact ProgMemOutside.refl _ _⟩
    · have h0F : (e.constVal? == some 0) = false := Bool.eq_false_iff.mpr h0
      have hce : (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.abort e)).1 =
          compileETo env.tab fl 0 AbiReg.a0 e ++ [Asm.j abortLabel] := by
        simp [compileSR, h0F]
      rw [hce] at hlink
      have hlinkE : lkm.linkSpec (pre ++ compileETo env.tab fl 0 AbiReg.a0 e ++ ([Asm.j abortLabel] ++ post)) =
          .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
      have hsim := reg_evalExpr_sim env L fl hfl lm loc' hal (by omega) htop e pre _ 0 AbiReg.a0 (Or.inl rfl)
        hsOk (fun z hz => hVf z (by simp [stmtUsesVar, hz])) (by omega) hlinkE (linkResolved_sub_pc64 env pre (compileETo env.tab fl 0 AbiReg.a0 e) _ hlinkE)
        st hpc hgp ht5 hsp hm hf'
      rw [execB_abort]
      cases he : _root_.L.evalE e { mem := lm, loc := loc' } with
      | error err =>
        have herr := evalE_err_eq_oob e { mem := lm, loc := loc' } he
        subst herr; rw [he] at hsim; dsimp only
        obtain ⟨k, r', hrun, hpc', hpres, hout⟩ := hsim
        exact stmtOutcomeR_of_err_oob htop ⟨k, r', hrun, hpc', hpres.abi,
          ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L (by omega) htop (Nat.zero_le _)) hout⟩
      | ok res =>
        rcases res with ⟨v, st1'⟩; rw [he] at hsim; dsimp only
        obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, hout1⟩ := hsim
        let preJ := pre ++ compileETo env.tab fl 0 AbiReg.a0 e
        have hlinkJ : lkm.linkSpec (preJ ++ [Asm.j abortLabel] ++ post) = .ok (env.code, env.labels) := by
          simpa [preJ, List.append_assoc] using hlinkE
        have h64J : 4 * (lkm.totalSize preJ + lkm.itemSize (.j abortLabel)) < 2 ^ 64 := by
          simpa [Asm.j, lkm.totalSize_singleton] using linkResolved_sub_pc64 env preJ [Asm.j abortLabel] post hlinkJ
        obtain ⟨kJ, r', hrunJ, hpc', hothJ, hpresJ, hmemJ⟩ :=
          prog_step_j env preJ post abortLabel env.abortTarget env.habortLbl hlinkJ h64J st1
            (by simpa [preJ, lkm.totalSize_append] using hpc1)
        exact ⟨k1 + kJ, r', by rw [run_add, hrun1]; exact hrunJ, hpc',
          (hothJ AbiReg.a0 (by decide)).trans ha0_1, (hpres1.abi.trans hpresJ).toTramp,
          ProgMemOutside.mono (fnWriteMaskR_sub_callWriteMask L (Nat.le_of_eq (callerSp_toNat_eq L htop).symm))
            (ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L (by omega) htop (Nat.zero_le _))
              (by rw [hmemJ]; exact hout1))⟩
  | copy64 d di s si n =>
    let loc' := ghostLoc fl sp st loc (fun y => (stmtVarCallFree y (.copy64 d di s si n) (na y) (nb y)).1)
    have hf' := ghostLoc_frameOk hf
    apply stmtOutcomeR_of_ghost (loc' := loc') (ghostLoc_agree _ _ _ _ _)
    simp only [stmtOkB, Bool.and_eq_true] at hsOk
    have hnoT5 : fl.useT5Gp = false := by
      cases ht : fl.useT5Gp with
      | false => rfl
      | true => have h := hCopyScan ht; simp [stmtHasCopyScan] at h
    have hsim := reg_copy64_sim env L fl hfl lm loc' hal (by omega) htop d di s si n
      hsOk.1.1.1.1 hsOk.1.1.1.2 hsOk.1.1.2 hsOk.1.2 hsOk.2
      (fun z hz => hVf z (by simp [stmtUsesVar, hz]))
      (fun z hz => hVf z (by simp [stmtUsesVar, hz]))
      (fun z hz => hVf z (by simp [stmtUsesVar, hz]))
      (fun z hz => hVf z (by simp [stmtUsesVar, hz]))
      (fun z hz => hVf z (by simp [stmtUsesVar, hz]))
      hTmp pfx lblId brkLbl retLbl isTail
      pre post st hpc hgp hnoT5 hsp hm hf' hlink p
    have ⟨hsigN, herrOob⟩ := baseStep_sig_err_copy64 p d di s si n ⟨lm, loc'⟩
    rw [execB_copy64]
    cases hst64 : _root_.L.step p (fun _ => throw .outOfFuel) (.copy64 d di s si n) { mem := lm, loc := loc' } with
    | error err =>
      have herr := herrOob err hst64; subst herr; rw [hst64] at hsim; dsimp only
      obtain ⟨k, r', hrun, hpc', hpres, hout⟩ := hsim
      exact stmtOutcomeR_of_err_oob htop ⟨k, r', hrun, hpc', hpres.abi, hout⟩
    | ok res =>
      rcases res with ⟨sig', st'⟩
      have hsig := hsigN sig' st' hst64; subst hsig; rw [hst64] at hsim; dsimp only
      exact stmtOutcomeR_of_base_normal hs0 hhdr hsim
  | copy8w d di s si n =>
    let loc' := ghostLoc fl sp st loc (fun y => (stmtVarCallFree y (.copy8w d di s si n) (na y) (nb y)).1)
    have hf' := ghostLoc_frameOk hf
    apply stmtOutcomeR_of_ghost (loc' := loc') (ghostLoc_agree _ _ _ _ _)
    simp only [stmtOkB, Bool.and_eq_true] at hsOk
    have hnoT5 : fl.useT5Gp = false := by
      cases ht : fl.useT5Gp with
      | false => rfl
      | true => have h := hCopyScan ht; simp [stmtHasCopyScan] at h
    have hsim := reg_copy8w_sim env L fl hfl lm loc' hal (by omega) htop d di s si n
      hsOk.1.1.1.1 hsOk.1.1.1.2 hsOk.1.1.2 hsOk.1.2 hsOk.2
      (fun z hz => hVf z (by simp [stmtUsesVar, hz]))
      (fun z hz => hVf z (by simp [stmtUsesVar, hz]))
      (fun z hz => hVf z (by simp [stmtUsesVar, hz]))
      (fun z hz => hVf z (by simp [stmtUsesVar, hz]))
      hTmp pfx lblId brkLbl retLbl isTail
      pre post st hpc hgp hnoT5 hsp hm hf' hlink p
    have ⟨hsigN, herrOob⟩ := baseStep_sig_err_copy8w p d di s si n ⟨lm, loc'⟩
    rw [execB_copy8w]
    cases hst8w : _root_.L.step p (fun _ => throw .outOfFuel) (.copy8w d di s si n) { mem := lm, loc := loc' } with
    | error err =>
      have herr := herrOob err hst8w; subst herr; rw [hst8w] at hsim; dsimp only
      obtain ⟨k, r', hrun, hpc', hpres, hout⟩ := hsim
      exact stmtOutcomeR_of_err_oob htop ⟨k, r', hrun, hpc', hpres.abi, hout⟩
    | ok res =>
      rcases res with ⟨sig', st'⟩
      have hsig := hsigN sig' st' hst8w; subst hsig; rw [hst8w] at hsim; dsimp only
      exact stmtOutcomeR_of_base_normal hs0 hhdr hsim
  | scan8 x s i e c =>
    let loc' := ghostLoc fl sp st loc (fun y => (stmtVarCallFree y (.scan8 x s i e c) (na y) (nb y)).1)
    have hf' := ghostLoc_frameOk hf
    apply stmtOutcomeR_of_ghost (loc' := loc') (ghostLoc_agree _ _ _ _ _)
    simp only [stmtOkB, Bool.and_eq_true, decide_eq_true_eq] at hsOk
    have hnoT5 : fl.useT5Gp = false := by
      cases ht : fl.useT5Gp with
      | false => rfl
      | true => have h := hCopyScan ht; simp [stmtHasCopyScan] at h
    have hnoClob : ∀ rx, fl.alloc.lookup x = some rx → ∀ y, y ≠ x → na y = true → fl.alloc.lookup y ≠ some rx := by
      intro rx hlx y hne hnay hly
      have h := hSafe y rx hly
      simp [stmtVarSafe, hlx, hnay, Ne.symm hne] at h
    have hsim := reg_scan8_sim env L fl hfl lm loc' hal (by omega) htop x hsOk.1.1.1.1.1 s hsOk.1.1.1.1.2
      i e hsOk.1.1.1.2 hsOk.1.1.2
      (fun z hz => hVf z (by simp [stmtUsesVar, hz]))
      (fun z hz => hVf z (by simp [stmtUsesVar, hz]))
      na hnoClob c hsOk.1.2 hsOk.2 hTmp pfx lblId brkLbl retLbl isTail
      pre post st hpc hgp hnoT5 hsp hm hf' hlink p
    have ⟨hsigN, herrOob⟩ := baseStep_sig_err_scan8 p x s i e c ⟨lm, loc'⟩
    rw [execB_scan8]
    cases hstsc : _root_.L.step p (fun _ => throw .outOfFuel) (.scan8 x s i e c) { mem := lm, loc := loc' } with
    | error err =>
      have herr := herrOob err hstsc; subst herr; rw [hstsc] at hsim; dsimp only
      obtain ⟨k, r', hrun, hpc', hpres, hout⟩ := hsim
      exact stmtOutcomeR_of_err_oob htop ⟨k, r', hrun, hpc', hpres.abi, hout⟩
    | ok res =>
      rcases res with ⟨sig', st'⟩
      have hsig := hsigN sig' st' hstsc; subst hsig; rw [hstsc] at hsim; dsimp only
      exact stmtOutcomeR_of_base_normal_live hs0 hhdr hsim
  | seq s1 s2 =>
    simp only [stmtOkB, Bool.and_eq_true] at hsOk
    simp only [stmtArgsOkB, Bool.and_eq_true] at hsArgs
    dsimp only [usedTempsStmtR] at hTmp
    cases htc : tailCallRetMatch env.tab s1 s2 with
    | none =>
      have hVf1 : StmtVarsInFrame fl s1 := fun z hz => hVf z (by simp [stmtUsesVar, hz])
      have hVf2 : StmtVarsInFrame fl s2 := fun z hz => hVf z (by simp [stmtUsesVar, hz])
      have hLeaf1 : fl.isLeaf = true → stmtHasCall s1 = false := fun hl =>
        (Bool.or_eq_false_iff.mp (by simpa [stmtHasCall] using hLeaf hl)).1
      have hLeaf2 : fl.isLeaf = true → stmtHasCall s2 = false := fun hl =>
        (Bool.or_eq_false_iff.mp (by simpa [stmtHasCall] using hLeaf hl)).2
      have hCopyScan1 : fl.useT5Gp = true → stmtHasCopyScan s1 = false := fun ht =>
        (Bool.or_eq_false_iff.mp (by simpa [stmtHasCopyScan] using hCopyScan ht)).1
      have hCopyScan2 : fl.useT5Gp = true → stmtHasCopyScan s2 = false := fun ht =>
        (Bool.or_eq_false_iff.mp (by simpa [stmtHasCopyScan] using hCopyScan ht)).2
      have habort01 : stmtHasAbort0 s1 = true → Abort0StubOk env pfx := fun h =>
        habort0 (by simp [stmtHasAbort0, h])
      have habort02 : stmtHasAbort0 s2 = true → Abort0StubOk env pfx := fun h =>
        habort0 (by simp [stmtHasAbort0, h])
      let n2 : Var → Bool := fun x => (stmtVarCallFree x s2 (na x) (nb x)).1
      have hSafe1 : ∀ y ry, fl.alloc.lookup y = some ry →
          (stmtVarSafe y (fun x => (x != y) && (fl.alloc.lookup x == some ry))
            (!fl.isLeaf && (ry ∈ leafExtraBank)) s1 (n2 y) (nb y)).2 = true := fun y ry hly => by
        have h := hSafe y ry hly
        simp only [stmtVarSafe, Bool.and_eq_true] at h
        rw [stmtVarSafe_fst] at h
        exact h.1
      have hSafe2 : ∀ y ry, fl.alloc.lookup y = some ry →
          (stmtVarSafe y (fun x => (x != y) && (fl.alloc.lookup x == some ry))
            (!fl.isLeaf && (ry ∈ leafExtraBank)) s2 (na y) (nb y)).2 = true := fun y ry hly => by
        have h := hSafe y ry hly
        simp only [stmtVarSafe, Bool.and_eq_true] at h
        exact h.2
      have hCallRes1 : fl.isLeaf = false → stmtCallResValid fl.alloc s1 = true := fun hnl =>
        (Bool.and_eq_true _ _ |>.mp (by simpa [stmtCallResValid] using hCallRes hnl)).1
      have hCallRes2 : fl.isLeaf = false → stmtCallResValid fl.alloc s2 = true := fun hnl =>
        (Bool.and_eq_true _ _ |>.mp (by simpa [stmtCallResValid] using hCallRes hnl)).2
      let r1 := compileSR env.tab fl pfx lblId brkLbl retLbl false s1
      let r2 := compileSR env.tab fl pfx r1.2 brkLbl retLbl isTail s2
      have hce : (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.seq s1 s2)).1 = r1.1 ++ r2.1 := by
        simp [compileSR, htc, r1, r2]
      rw [hce] at hlink hTail ⊢
      have hlink1 : lkm.linkSpec (pre ++ r1.1 ++ (r2.1 ++ post)) = .ok (env.code, env.labels) := by
        simpa [List.append_assoc] using hlink
      have hlimSeq := stackNeedB_seq p b s1 s2 { mem := lm, loc := loc }
      have hlim1 : L.stackLimit.toNat + stackNeedB p b s1 { mem := lm, loc := loc } ≤ sp.toNat := by
        cases hx : execB p b s1 { mem := lm, loc := loc } with
        | error _ => simp only [hx] at hlimSeq; rw [hlimSeq] at hlim; exact hlim
        | ok res =>
          rcases res with ⟨sig1, st1, b1⟩
          cases sig1 with
          | normal =>
            simp only [hx] at hlimSeq
            exact Nat.le_trans (Nat.add_le_add_left (Nat.le_max_left _ _) _) (by rw [← hlimSeq]; exact hlim)
          | brk => simp only [hx] at hlimSeq; rw [hlimSeq] at hlim; exact hlim
          | ret _ => simp only [hx] at hlimSeq; rw [hlimSeq] at hlim; exact hlim
      have hres1 := ih b s1 (execBRel_seq_left b s1 s2) (fun b' hb' => hcall b' hb') fl hfl n2 nb tco lm loc
        sp pfx lblId brkLbl retLbl retPc false pre (r2.1 ++ post) hsOk.1 hsArgs.1 hVf1 (by omega) hLeaf1
        hSafe1 hCallRes1 hCopyScan1 habort01
        hb64 hal hlim1 htop hretLbl hbrkLbl (fun h => by cases h) hlink1 st hpc hgp ht5 hsp hs0 hm hf hhdr htco
      rw [execB_seq]
      cases hx1 : execB p b s1 { mem := lm, loc := loc } with
      | error err => rw [hx1] at hres1; cases err <;> exact hres1
      | ok res1 =>
        rcases res1 with ⟨sig1, st1, b1⟩
        rw [hx1] at hres1
        cases sig1 with
        | brk => dsimp only [StmtOutcomeR] at hres1 ⊢; exact hres1
        | ret vs => dsimp only [StmtOutcomeR] at hres1 ⊢; exact hres1
        | normal =>
          dsimp only
          obtain ⟨k1, r1', hrun1, hpc1, hpres1, hs0_1, hb1, hm1, hf1, hout1, hhdr1⟩ := hres1
          have hlink2 : lkm.linkSpec ((pre ++ r1.1) ++ r2.1 ++ post) = .ok (env.code, env.labels) := by
            simpa [List.append_assoc] using hlink
          have hlim2 : L.stackLimit.toNat + stackNeedB p b1 s2 st1 ≤ sp.toNat := by
            simp only [hx1] at hlimSeq
            exact Nat.le_trans (Nat.add_le_add_left (Nat.le_max_right _ _) _) (by rw [← hlimSeq]; exact hlim)
          have hpcEndEq : lkm.totalSize (pre ++ r1.1) + lkm.totalSize r2.1 =
              lkm.totalSize pre + lkm.totalSize (r1.1 ++ r2.1) := by
            simp only [lkm.totalSize_append, Nat.add_assoc]
          have hres2 := ih b1 s2 (execBRel_seq_right hb1 s1 s2) (fun b' hb' => hcall b' (by omega))
            fl hfl na nb tco st1.mem st1.loc sp pfx r1.2 brkLbl retLbl retPc isTail (pre ++ r1.1) post hsOk.2 hsArgs.2 hVf2
            (by omega) hLeaf2 hSafe2 hCallRes2 hCopyScan2 habort02 (by omega) hal hlim2 htop hretLbl hbrkLbl
            (fun ht => by rw [hpcEndEq]; exact hTail ht)
            hlink2 r1' (by simpa [lkm.totalSize_append] using hpc1)
            (hpres1.abi.gp.trans hgp) (ht5.of_frameNoS0 hpres1) (hpres1.abi.sp.trans hsp) hs0_1 hm1 hf1 hhdr1
            (htco.of_step L hfl (by omega) htop hpres1 hout1)
          exact hres2.prepend hfl htop k1 hrun1 hpres1 hout1 hb1 hpcEndEq
    | some quad =>
      rcases quad with ⟨xs, f, args, es⟩
      obtain ⟨rfl, rfl, hxsNe, hvl, hnd, hargsLe, hxsNres, hxsMax⟩ := tailCallRetMatch_spec htc
      have hnotLeaf : fl.isLeaf = false := by
        cases hl : fl.isLeaf with
        | false => rfl
        | true => have h := hLeaf hl; simp [stmtHasCall] at h
      have hOk1 := hsOk.1
      simp only [stmtOkB, Bool.and_eq_true, Option.isSome_iff_exists] at hOk1
      have hArgs1 := hsArgs.1
      simp only [stmtArgsOkB] at hArgs1
      rcases hOk1.1.1 with ⟨fd, hflook⟩
      rw [hflook] at hArgs1
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hArgs1
      rcases hArgs1 with ⟨hflen, hxsMinRet⟩
      obtain ⟨fnPc, hfnPc⟩ := hFnLbls hflook
      let liveSeq : Var → Bool := fun x => (stmtVarCallFree x (.seq (.call xs f args) (.ret es)) (na x) (nb x)).1
      let loc' := ghostLoc fl sp st loc liveSeq
      have hf' : ProgFrameOkR L fl sp st loc' := ghostLoc_frameOk hf
      have hagSeq : ∀ x, liveSeq x = true → loc' x = loc x := ghostLoc_agree fl sp st loc liveSeq
      have hargsAg : ∀ x, args.any (exprUsesVar x) = true → loc' x = loc x :=
        fun x hx => hagSeq x (by simp [liveSeq, stmtVarCallFree, hx])
      have hVfArgs : ExprsVarsInFrame fl args := fun z hz => hVf z (by simp [stmtUsesVar, hz])
      let cArgsAll := compileCallArgsR env.tab fl args
      let cPop := framePopItems fl
      let cJ := [Asm.j (fnLabel f)]
      have hcodeEq : (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.seq (.call xs f args) (.ret es))).1 =
          cArgsAll ++ cPop ++ cJ := by
        simp [compileSR, htc, cArgsAll, cPop, cJ, List.append_assoc]
      rw [hcodeEq] at hlink
      have hlink0 : lkm.linkSpec (pre ++ cArgsAll ++ (cPop ++ cJ ++ post)) =
          .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlink
      have hargsSim := prog_callArgs_sim env L fl hfl b lm loc' sp args hOk1.2 hVfArgs
        (by dsimp only [usedTempsStmtR] at hTmp; omega) hb64 hal (by omega) htop
        pre (cPop ++ cJ ++ post) hlink0 st hpc hgp ht5 hsp hs0 hm hf'
      cases hea : _root_.L.evalArgs args { mem := lm, loc := loc' } with
      | error err =>
        have herr := evalArgs_err_eq_oob args { mem := lm, loc := loc' } hea
        subst herr; rw [hea] at hargsSim
        rw [execB_seq, execB_call, evalArgs_congr_eq_err hargsAg hea]
        obtain ⟨k, r', hrun, hpc', hpres, hpm⟩ := hargsSim
        exact ⟨k, r', hrun, hpc', hpres,
          ProgMemOutside.mono (fnWriteMaskR_sub_callWriteMask L (Nat.le_of_eq (callerSp_toNat_eq L htop).symm)) hpm⟩
      | ok resA =>
        rcases resA with ⟨vs, _⟩
        have hea0 := evalArgs_congr_eq_ok hargsAg hea
        rw [hea] at hargsSim
        cases b with
        | zero =>
          rw [execB_seq, execB_call, hea0, hflook]
          obtain ⟨k, r', hrun, hpc', hpres, hpm⟩ := hargsSim
          exact ⟨k, r', hrun, hpc', hpres,
            ProgMemOutside.mono (fnWriteMaskR_sub_callWriteMask L (Nat.le_of_eq (callerSp_toNat_eq L htop).symm)) hpm⟩
        | succ b' =>
          obtain ⟨kPre, st4, _, hrunPre, hpc4, hvslen, hpres4, hcal4, hs0_4, hout4, _, _, _, hargWords4⟩ := hargsSim
          have hm4 := ProgMemRel.of_tempSpanR (by omega) htop (Nat.zero_le _) hout4 hm
          have hpm4 : ProgMemOutside (FnWriteMaskR L fl sp) st.mem st4.mem :=
            ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L (by omega) htop (Nat.zero_le _)) hout4
          have hhdr4 : TabHeaderOk L st4.mem := hhdr.of_fnWriteMaskR L hpm4
          have hraSlot4 : fl.isLeaf = false → readWord64 st4.mem sp = tco.callerRa := fun hnl => by
            have hslot0 : 0 < fl.protectedSlots := by
              dsimp only [FrameLayout.protectedSlots, FrameLayout.raSlots]; rw [hnl]
              simp only [Bool.false_eq_true, ↓reduceIte]; omega
            have hsp0 : sp = sp + BitVec.ofNat 64 (8 * 0) := (BitVec.add_zero sp).symm
            rw [← htco.2.1 hnl]
            exact hpm4.readWord64_eq sp fun k hk => by
              have hnp := @fnWriteMaskR_not_protected _ L fl sp (by omega) htop 0 hslot0 k hk
              rwa [← hsp0] at hnp
          have hcalSaved4 : ∀ i (hi : i < fl.savedRegs.length),
              readWord64 st4.mem (sp + BitVec.ofInt 64 (fl.savedOff i)) = tco.calleeVals (fl.savedRegs[i]'hi) := fun i hi => by
            have hslot : fl.raSlots + i < fl.protectedSlots := by simp [FrameLayout.protectedSlots]; omega
            rw [← htco.2.2.2 i hi, savedOff_ofInt]
            exact hpm4.readWord64_eq _ fun k hk => fnWriteMaskR_not_protected L (by omega) htop hslot hk
          let callerSp := sp + BitVec.ofInt 64 fl.frameBytes
          have hcallerSpToNat : callerSp.toNat = sp.toNat + 8 * fl.frameSlots := callerSp_toNat_eq L htop
          have hcallerAl : isAligned callerSp 8 = true := by
            dsimp only [callerSp]; rw [frameBytesR_toNat_eq fl]
            exact isAligned8_add_mul8 sp hal fl.frameSlots
          let pre4 := pre ++ cArgsAll
          have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre4) := by
            simpa [pre4, cArgsAll, lkm.totalSize_append] using hpc4
          have hlinkPop : lkm.linkSpec (pre4 ++ framePopItems fl ++ (cJ ++ post)) = .ok (env.code, env.labels) := by
            simpa [pre4, cPop, List.append_assoc] using hlink0
          obtain ⟨kPop, stPop, hrunPop, hpcPop, hgpPop, hspPop, hraPop, hs0Pop, _, hs2Pop, hcalPop, hresPop, hmemPop⟩ :=
            framePopItems_sim env L fl hfl tco.calleeVals hal rfl pre4 (cJ ++ post) hlinkPop st4 hpc4'
              (hpres4.gp.trans hgp) (hpres4.sp.trans hsp) hs0_4
              (fun hl => by rw [hnotLeaf] at hl; cases hl) hraSlot4
              (fun r hr hns => (hcal4 r hr).trans (htco.2.2.1 r hr hns)) hcalSaved4
          let prePop := pre4 ++ cPop
          have hlinkJ : lkm.linkSpec (prePop ++ [Asm.j (fnLabel f)] ++ post) = .ok (env.code, env.labels) := by
            simpa [prePop, cPop, cJ, List.append_assoc] using hlinkPop
          have h64J : 4 * (lkm.totalSize prePop + lkm.itemSize (.j (fnLabel f))) < 2 ^ 64 := by
            simpa [Asm.j, lkm.totalSize_singleton] using linkResolved_sub_pc64 env prePop [Asm.j (fnLabel f)] post hlinkJ
          obtain ⟨kJ, stJ, hrunJ, hpcJ, hothJ, hpresJ, hmemJ⟩ :=
            prog_step_j env prePop post (fnLabel f) fnPc hfnPc hlinkJ h64J stPop
              (by simpa [prePop, cPop, lkm.totalSize_append] using hpcPop)
          have hmemJ4 : stJ.mem = st4.mem := hmemJ.trans hmemPop
          have hrunUp : RV64.run env.rom (kPre + kPop + kJ) st = .cont stJ :=
            run_trans (run_trans hrunPre hrunPop) hrunJ
          have htrUp : PreservedTramp st stJ :=
            ⟨(hpresJ.gp.trans hgpPop).trans hgp.symm,
             hpresJ.s2.trans (hs2Pop.trans hpres4.s2)⟩
          have hcalJ : ∀ r ∈ calleeSavedBank, stJ.getReg r = tco.calleeVals r := fun r hr =>
            (hothJ r ⟨allowedRegs_ne_t6 (isLeaf := false) hr, allowedRegs_ne_s1 (isLeaf := false) hr⟩).trans (hcalPop r hr)
          have hargsGeCaller : ∀ j, j < vs.length → ∀ kk, kk < 8 →
              callerSp.toNat ≤ (callerSp + BitVec.ofNat 64 (8 * (j - maxRes)) + BitVec.ofNat 64 kk).toNat ∨
              ¬L.stackSpan.contains (callerSp + BitVec.ofNat 64 (8 * (j - maxRes)) + BitVec.ofNat 64 kk) := by
            intro j hj kk hkk; left
            have hsub0 : j - maxRes = 0 := by omega
            have hmod := (isAligned8_iff callerSp).mp hcallerAl
            have hlt64 := callerSp.isLt
            rw [hsub0, Nat.mul_zero, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero,
              BitVec.toNat_add callerSp (BitVec.ofNat 64 kk), BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
            omega
          have hargWordsJ : ∀ j, j < vs.length →
              (if j < maxRes then stJ.getReg (resReg j)
               else readWord64 stJ.mem (callerSp + BitVec.ofNat 64 (8 * (j - maxRes)))) = (vs[j]!).toBitVec := by
            intro j hj
            have hjm : j < maxRes := by omega
            simp only [hjm, ↓reduceIte]
            rw [hothJ (resReg j) ⟨resReg_ne_t6 j, (resReg_ne_preserved j).2.2.2.1⟩, hresPop j hjm]
            have h := hargWords4 j hj; simpa [hjm] using h
          have hlimSeq := stackNeedB_seq p (b' + 1) (.call xs f args) (.ret es) { mem := lm, loc := loc }
          have hlimCall1 : L.stackLimit.toNat + stackNeedB p (b' + 1) (.call xs f args) { mem := lm, loc := loc } ≤ sp.toNat := by
            cases hx : execB p (b' + 1) (.call xs f args) { mem := lm, loc := loc } with
            | error _ => simp only [hx] at hlimSeq; rw [hlimSeq] at hlim; exact hlim
            | ok res =>
              rcases res with ⟨sig1, st1, b1⟩
              cases sig1 with
              | normal =>
                simp only [hx] at hlimSeq
                exact Nat.le_trans (Nat.add_le_add_left (Nat.le_max_left _ _) _) (by rw [← hlimSeq]; exact hlim)
              | brk => simp only [hx] at hlimSeq; rw [hlimSeq] at hlim; exact hlim
              | ret _ => simp only [hx] at hlimSeq; rw [hlimSeq] at hlim; exact hlim
          have hlimCall2 := stackNeedB_call p (b' + 1) xs f args { mem := lm, loc := loc }
          rw [hea0, hflook] at hlimCall2; dsimp only at hlimCall2
          have hcallF := hcall b' (Nat.lt_succ_self b') f fd vs lm callerSp tco.callerRa callerSp tco.callerRetPc
            hflook (hvslen.trans hflen) (by omega)
            (by rw [hlimCall2, ← Nat.add_assoc] at hlimCall1
                exact Nat.le_trans hlimCall1 (by rw [hcallerSpToNat]; omega))
            (by rw [hcallerSpToNat]; exact htop) hcallerAl hcallerAl tco.hraAl hargsGeCaller
            fnPc stJ hfnPc hpcJ (hpresJ.gp.trans hgpPop) (hpresJ.sp.trans hspPop)
            ((hothJ AbiReg.ra (by decide)).trans hraPop) (hpresJ.s0.trans hs0Pop)
            (fun hgt => absurd hgt (by omega))
            (by rw [hmemJ4]; exact hm4) (by rw [hmemJ4]; exact hhdr4) hargWordsJ
          rw [execB_seq, execB_call, hea0, hflook]; dsimp only
          cases hxF : execB p b' fd.body { mem := lm, loc := Locals.init vs } with
          | error err =>
            rw [hxF] at hcallF
            have hcmUp : ProgMemOutside (CallWriteMask L callerSp) st.mem stJ.mem := by
              rw [hmemJ4]
              exact ProgMemOutside.mono (fnWriteMaskR_sub_callWriteMask L (Nat.le_of_eq (callerSp_toNat_eq L htop).symm)) hpm4
            cases err with
            | outOfFuel =>
              obtain ⟨kc, rc, hrunC, hpcC, hpresC, hpmC⟩ := hcallF
              exact ⟨_, rc, by rw [run_add, hrunUp]; exact hrunC, hpcC, htrUp.trans hpresC, hcmUp.trans hpmC⟩
            | abort code =>
              obtain ⟨kc, rc, hrunC, hpcC, ha0C, hpresC, hpmC⟩ := hcallF
              exact ⟨_, rc, by rw [run_add, hrunUp]; exact hrunC, hpcC, ha0C, htrUp.trans hpresC, hcmUp.trans hpmC⟩
            | oob =>
              obtain ⟨kc, rc, hrunC, hpcC, hpresC, hpmC⟩ := hcallF
              exact ⟨_, rc, by rw [run_add, hrunUp]; exact hrunC, hpcC, htrUp.trans hpresC, hcmUp.trans hpmC⟩
            | noFun fn =>
              obtain ⟨kc, rc, hrunC, hpcC, hpresC, hpmC⟩ := hcallF
              exact ⟨_, rc, by rw [run_add, hrunUp]; exact hrunC, hpcC, htrUp.trans hpresC, hcmUp.trans hpmC⟩
          | ok resF =>
            rcases resF with ⟨sigF, stF, bF⟩
            rw [hxF] at hcallF
            obtain ⟨kF, rF, hrunF, hpcF, hgpF, hspF, hs2F, hcalF, hs0F, hbF, hsigNb, _, hmF, hhdrF, hresF, houtF⟩ := hcallF
            obtain ⟨vsOut, heOut, hvsOutLen, hvsOutGet⟩ :=
              evalArgs_of_isVarList_setLocs xs es hvl hnd stF.mem loc sigF.retVal
            dsimp only
            rw [execB_ret, heOut]; dsimp only
            have hminRet : fnMinRet fd ≤ max 1 sigF.retVal.length := fnMinRet_le_sig hxF hsigNb
            have hxsPos : 1 ≤ xs.length := by
              cases xs with
              | nil => exact absurd rfl hxsNe
              | cons _ _ => simp
            have hresOut : ResultsInState env.tab L rF vsOut := by
              refine ⟨fun i hi => ?_, fun i hloI hhiI => by omega⟩
              have hiXs : i < xs.length := by omega
              have hiF : i < min (min (max 1 sigF.retVal.length) env.tab.nres) maxRes := by omega
              rw [hresF.1 i hiF, hvsOutGet i hiXs]
            have houtAll : ProgMemOutside (CallWriteMask L callerSp) st.mem rF.mem :=
              (ProgMemOutside.mono (fnWriteMaskR_sub_callWriteMask L (Nat.le_of_eq hcallerSpToNat.symm)) hpm4).trans
                (by rw [← hmemJ4]; exact houtF)
            exact Or.inr ⟨_, rF, run_trans hrunUp hrunF, hpcF, hgpF, hspF,
              hs2F.trans htrUp.s2,
              fun r hr => (hcalF r hr).trans (hcalJ r hr),
              hs0F, by omega, by omega,
              by rw [setLocs_mem]; exact hmF, hresOut, houtAll, hhdrF⟩
  | ite c s1 s2 =>
    simp only [stmtOkB, Bool.and_eq_true] at hsOk
    simp only [stmtArgsOkB, Bool.and_eq_true] at hsArgs
    dsimp only [usedTempsStmtR] at hTmp
    have hVfC : CondVarsInFrame fl c := fun z hz => hVf z (by simp [stmtUsesVar, hz])
    have hVf1 : StmtVarsInFrame fl s1 := fun z hz => hVf z (by simp [stmtUsesVar, hz])
    have hVf2 : StmtVarsInFrame fl s2 := fun z hz => hVf z (by simp [stmtUsesVar, hz])
    have hCopyScan1 : fl.useT5Gp = true → stmtHasCopyScan s1 = false := fun ht =>
      (Bool.or_eq_false_iff.mp (by simpa [stmtHasCopyScan] using hCopyScan ht)).1
    have hCopyScan2 : fl.useT5Gp = true → stmtHasCopyScan s2 = false := fun ht =>
      (Bool.or_eq_false_iff.mp (by simpa [stmtHasCopyScan] using hCopyScan ht)).2
    have habort01 : stmtHasAbort0 s1 = true → Abort0StubOk env pfx := fun h =>
      habort0 (by simp [stmtHasAbort0, h])
    have habort02 : stmtHasAbort0 s2 = true → Abort0StubOk env pfx := fun h =>
      habort0 (by simp [stmtHasAbort0, h])
    have hSafe1 : ∀ y ry, fl.alloc.lookup y = some ry →
        (stmtVarSafe y (fun x => (x != y) && (fl.alloc.lookup x == some ry))
          (!fl.isLeaf && (ry ∈ leafExtraBank)) s1 (na y) (nb y)).2 = true := fun y ry hly => by
      have h := hSafe y ry hly
      simp only [stmtVarSafe, Bool.and_eq_true] at h; exact h.1
    have hSafe2 : ∀ y ry, fl.alloc.lookup y = some ry →
        (stmtVarSafe y (fun x => (x != y) && (fl.alloc.lookup x == some ry))
          (!fl.isLeaf && (ry ∈ leafExtraBank)) s2 (na y) (nb y)).2 = true := fun y ry hly => by
      have h := hSafe y ry hly
      simp only [stmtVarSafe, Bool.and_eq_true] at h; exact h.2
    have hCallRes1 : fl.isLeaf = false → stmtCallResValid fl.alloc s1 = true := fun hnl =>
      (Bool.and_eq_true _ _ |>.mp (by simpa [stmtCallResValid] using hCallRes hnl)).1
    have hCallRes2 : fl.isLeaf = false → stmtCallResValid fl.alloc s2 = true := fun hnl =>
      (Bool.and_eq_true _ _ |>.mp (by simpa [stmtCallResValid] using hCallRes hnl)).2
    exact prog_ite_step_sim env L p fl hfl b lm loc sp pfx lblId brkLbl retLbl retPc isTail c s1 s2 na nb tco
      hsOk.1.1 hVfC hsOk.1.2 hsOk.2 hsArgs.1 hsArgs.2 hTmp hLeaf habort0 hb64 hal hlim htop pre post hTail hlink
      st hpc hgp ht5 hsp hs0 hm hf hhdr htco
      (fun lid isT pre1 post1 st1 hs1Ok' hs1Args' hTmp1 hLeaf1 hlim1 hTail1 hlink1 hpc1 hgp1 ht51 hsp1 hs01 hm1 hf1 hhdr1 htco1 =>
        ih b s1 (execBRel_ite_left b c s1 s2) (fun b' hb' => hcall b' hb') fl hfl na nb tco lm loc sp pfx lid
          brkLbl retLbl retPc isT pre1 post1 hs1Ok' hs1Args' hVf1 hTmp1 hLeaf1 hSafe1 hCallRes1 hCopyScan1 habort01
          hb64 hal hlim1 htop hretLbl hbrkLbl hTail1 hlink1 st1 hpc1 hgp1 ht51 hsp1 hs01 hm1 hf1 hhdr1 htco1)
      (fun lid isT pre2 post2 st2 hs2Ok' hs2Args' hTmp2 hLeaf2 hlim2 hTail2 hlink2 hpc2 hgp2 ht52 hsp2 hs02 hm2 hf2 hhdr2 htco2 =>
        ih b s2 (execBRel_ite_right b c s1 s2) (fun b' hb' => hcall b' hb') fl hfl na nb tco lm loc sp pfx lid
          brkLbl retLbl retPc isT pre2 post2 hs2Ok' hs2Args' hVf2 hTmp2 hLeaf2 hSafe2 hCallRes2 hCopyScan2 habort02
          hb64 hal hlim2 htop hretLbl hbrkLbl hTail2 hlink2 st2 hpc2 hgp2 ht52 hsp2 hs02 hm2 hf2 hhdr2 htco2)
  | «while» c body =>
    simp only [stmtOkB, Bool.and_eq_true] at hsOk
    dsimp only [stmtArgsOkB] at hsArgs
    dsimp only [usedTempsStmtR] at hTmp
    have hVfC : CondVarsInFrame fl c := fun z hz => hVf z (by simp [stmtUsesVar, hz])
    have hVfB : StmtVarsInFrame fl body := fun z hz => hVf z (by simp [stmtUsesVar, hz])
    have hCopyScanB : fl.useT5Gp = true → stmtHasCopyScan body = false := fun ht =>
      by simpa [stmtHasCopyScan] using hCopyScan ht
    have habort0B : stmtHasAbort0 body = true → Abort0StubOk env pfx := fun h =>
      habort0 (by simpa [stmtHasAbort0] using h)
    have hSafeB : ∀ y ry, fl.alloc.lookup y = some ry →
        (stmtVarSafe y (fun x => (x != y) && (fl.alloc.lookup x == some ry))
          (!fl.isLeaf && (ry ∈ leafExtraBank)) body (stmtVarCallFree y (.while c body) (na y) (nb y)).1 (na y)).2 = true :=
      fun y ry hly => by
        rw [← stmtVarSafe_while_body_ok y _ _ c body (na y) (nb y)]
        exact hSafe y ry hly
    have hCallResB : fl.isLeaf = false → stmtCallResValid fl.alloc body = true := fun hnl =>
      by simpa [stmtCallResValid] using hCallRes hnl
    exact prog_while_step_sim env L p fl hfl b lm loc sp pfx lblId brkLbl retLbl isTail c body na nb tco
      hsOk.1 hVfC hsOk.2 hsArgs hTmp hLeaf hb64 hal hlim htop pre post hlink st hpc hgp ht5 hsp hs0 hm hf hhdr htco
      (fun preB postB stB hbOk' hbArgs' hTmpB hLeafB hlimB hendLbl hlinkB hpcB hgpB ht5B hspB hs0B hmB hfB hhdrB htcoB =>
        ih b body (execBRel_while_body b c body) (fun b' hb' => hcall b' hb') fl hfl
          (fun x => (stmtVarCallFree x (.while c body) (na x) (nb x)).1) na tco lm loc sp pfx
          (compileCR env.tab fl 0 pfx (lblId + 1) c false s!"{pfx}_endw_{lblId}").2
          (some s!"{pfx}_endw_{lblId}") retLbl retPc false preB postB hbOk' hbArgs' hVfB hTmpB hLeafB
          hSafeB hCallResB hCopyScanB habort0B hb64 hal hlimB htop hretLbl
          (fun tgt ht => by simp only [Option.some.injEq] at ht; subst ht; exact ⟨_, hendLbl⟩)
          (fun h => by cases h) hlinkB stB hpcB hgpB ht5B hspB hs0B hmB hfB hhdrB htcoB)
      (fun b1' st2 stLoop hb1' hlimNext hpcLoop hgpLoop ht5Loop hspLoop hs0Loop hmLoop hfLoop hhdrLoop htcoLoop =>
        ih b1' (.while c body) (execBRel_while_next hb1' c body)
          (fun b'' hb'' => hcall b'' (by omega)) fl hfl na nb tco st2.mem st2.loc sp pfx lblId brkLbl retLbl retPc isTail
          pre post (by simp only [stmtOkB, Bool.and_eq_true]; exact hsOk) hsArgs hVf hTmp hLeaf
          hSafe hCallRes hCopyScan habort0 (by omega) hal hlimNext htop
          hretLbl hbrkLbl hTail hlink stLoop hpcLoop hgpLoop ht5Loop hspLoop hs0Loop hmLoop hfLoop hhdrLoop htcoLoop)
  | call xs f args =>
    simp only [stmtOkB, Bool.and_eq_true, Option.isSome_iff_exists] at hsOk
    simp only [stmtArgsOkB] at hsArgs
    dsimp only [usedTempsStmtR] at hTmp
    have hnotLeaf : fl.isLeaf = false := by
      cases hl : fl.isLeaf with
      | false => rfl
      | true => have h := hLeaf hl; simp [stmtHasCall] at h
    have hArgsLen : ∃ fd, p.lookup f = some fd ∧ args.length = fd.nparams ∧ xs.length ≤ fnMinRet fd := by
      rcases hsOk.1.1 with ⟨fd, hfl'⟩
      rw [hfl'] at hsArgs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hsArgs
      exact ⟨fd, hfl', hsArgs.1, hsArgs.2⟩
    rcases hArgsLen with ⟨fd, hfl', hlen, hmin⟩
    obtain ⟨fnPc, hfnLbl⟩ := hFnLbls hfl'
    have hVfArgs : ExprsVarsInFrame fl args := fun z hz => hVf z (by simp [stmtUsesVar, hz])
    have hcfCall : ∀ x r, fl.alloc.lookup x = some r → r ∈ leafExtraBank → (na x && !(x ∈ xs)) = false :=
      fun x r hlx hrL => by
        have h := hSafe x r hlx
        simp [stmtVarSafe, hnotLeaf, hrL] at h
        rcases h.1 with h1 | h2
        · simp [h1]
        · simp [h2]
    have hnoClob : ∀ y ry, fl.alloc.lookup y = some ry → na y = true → ∀ x ∈ xs, x ≠ y → fl.alloc.lookup x ≠ some ry :=
      fun y ry hly hnay x hx hne hlx => by
        have h := hSafe y ry hly
        simp only [stmtVarSafe, hnay, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at h
        have h2 := h.2
        rw [List.any_eq_false] at h2
        have hx2 := h2 x hx
        simp [bne_iff_ne, hne, hlx] at hx2
    have hresCall : callResListValid fl.alloc xs = true := by
      simpa [stmtCallResValid] using hCallRes hnotLeaf
    exact prog_call_step_sim env L p fl hfl b lm loc sp pfx lblId brkLbl retLbl isTail xs f args na nb tco
      hsOk.1.2 hsOk.2 hVfArgs ⟨fd, hfl', hlen, hmin⟩ hTmp hLeaf hcfCall hnoClob hresCall hb64 hal hlim htop ⟨fnPc, hfnLbl⟩ hcall pre post hlink
      st hpc hgp ht5 hsp hs0 hm hf hhdr

theorem progExecB_step_gen {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab) (p : _root_.L.Prog)
    (hpOk : progOkB env.tab p = true)
    (hpArgs : progArgsOkB p = true)
    (hFns : ProgFnsLinkedGen env p) :
    ∀ (b : Nat) (s : _root_.L.Stmt),
      (∀ b', b' < b → FnCallSimGenCallee env L p b') →
      ∀ (fl : FrameLayout), FrameLayoutOk fl →
      ∀ (tco : TcoCtx) (lm : _root_.L.Mem) (loc : _root_.L.Locals)
        (sp : BitVec 64) (pfx : String) (lblId : Nat)
        (brkLbl : Option String) (retLbl : String) (retPc : Nat) (isTail : Bool)
        (pre post : List AsmItem),
        stmtOkB env.tab p fl.nlocals brkLbl.isSome s = true →
        stmtArgsOkB p s = true →
        StmtVarsInFrame fl s →
        usedTempsStmtR fl.isLeaf fl.alloc s ≤ fl.usedTemps →
        (fl.isLeaf = true → stmtHasCall s = false) →
        (∀ y ry, fl.alloc.lookup y = some ry →
          (stmtVarSafe y (fun x => (x != y) && (fl.alloc.lookup x == some ry))
            (!fl.isLeaf && (ry ∈ leafExtraBank)) s false false).2 = true) →
        (fl.isLeaf = false → stmtCallResValid fl.alloc s = true) →
        (fl.useT5Gp = true → stmtHasCopyScan s = false) →
        (stmtHasAbort0 s = true → Abort0StubOk env pfx) →
        b < 2 ^ 64 →
        isAligned sp 8 = true →
        L.stackLimit.toNat + stackNeedB p b s { mem := lm, loc := loc } ≤ sp.toNat →
        sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat →
        lookupLabel env.labels retLbl = some retPc →
        (∀ tgt, brkLbl = some tgt → ∃ tgtPc, lookupLabel env.labels tgt = some tgtPc) →
        (isTail = true → lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail s).1 = retPc) →
        lkm.linkSpec (pre ++ (compileSR env.tab fl pfx lblId brkLbl retLbl isTail s).1 ++ post) =
          .ok (env.code, env.labels) →
        ∀ st : State,
          st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
          st.getReg AbiReg.gp = L.T →
          T5GpOk L fl st →
          st.getReg AbiReg.sp = sp →
          st.getReg AbiReg.s0 = BitVec.ofNat 64 b →
          ProgMemRel env.tab L st.mem lm →
          ProgFrameOkR L fl sp st loc →
          TabHeaderOk L st.mem →
          TcoStateOk fl sp tco st →
          StmtOutcomeR env L fl sp b st retLbl brkLbl
            (lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail s).1)
            (fun _ => false) (fun _ => false) tco
            (execB p b s { mem := lm, loc := loc }) := by
  intro b s hcall fl hfl tco lm loc sp pfx lblId brkLbl retLbl retPc isTail pre post
    hsOk hsArgs hVf hTmp hLeaf hSafe hCallRes hCopyScan habort0 hb64 hal hlim htop hretLbl hbrkLbl hTail hlink
    st hpc hgp ht5 hsp hs0 hm hf hhdr htco
  exact progExecB_step_lbls env L p hpOk hpArgs
    (fun hfl' => let ⟨_, _, _, hl⟩ := ProgFnsLinkedGen.split_fn hFns hfl'; ⟨_, hl⟩)
    b s hcall fl hfl (fun _ => false) (fun _ => false) tco lm loc sp pfx lblId brkLbl retLbl retPc isTail pre post
    hsOk hsArgs hVf hTmp hLeaf hSafe hCallRes hCopyScan habort0 hb64 hal hlim htop hretLbl hbrkLbl hTail hlink
    st hpc hgp ht5 hsp hs0 hm (hf.toLive_self _) hhdr htco

end ConAgua.RISCV.Compiler
