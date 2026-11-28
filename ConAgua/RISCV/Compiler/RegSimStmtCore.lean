import ConAgua.RISCV.Compiler.RegSimStmtBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Base-Statement Simulation Core (`ConAgua.RISCV.Compiler.RegSimStmtCore`)

Forward simulation of `.set`, `.gset`, `.st8`, `.st64`, `.st64t`, `.st32t` in `compileSR`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard Lean axioms only.
-/

namespace ConAgua.RISCV.Compiler

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Linker

/-! ## 3. Base Statement Simulations (`.set`, `.gset`, `.st8`, `.st64`, `.st64t`, `.st32t`) -/

theorem reg_set_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (x : Var) (e : Expr) (pfx : String) (lblId : Nat) (brkLbl : Option String) (retLbl : String) (isTail : Bool)
    (pre post : List AsmItem)
    (_hx : x < fl.nlocals) (heOk : exprOkB env.tab fl.nlocals e = true)
    (hVfE : ExprVarsInFrame fl e)
    (live2 : Var → Bool)
    (hnoClob : ∀ rx, fl.alloc.lookup x = some rx → ∀ y, y ≠ x → live2 y = true → fl.alloc.lookup y ≠ some rx)
    (hTmp : usedTempsExpr e ≤ fl.usedTemps)
    (hlink : lkm.linkSpec (pre ++ (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.set x e)).1 ++ post) =
      .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    match _root_.L.evalE e ⟨lm, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.set x e)).1)) ∧
        PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) st st' ∧
        ProgMemRel env.tab L st'.mem lm ∧
        ProgFrameOkLive L fl sp st' (fun y => if y = x then v else loc y) live2 ∧
        ProgMemOutside (FnWriteMaskR L fl sp) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) st st' ∧
        ProgMemOutside (FnWriteMaskR L fl sp) st.mem st'.mem := by
  have hvalid : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  have h64 := linkResolved_sub_pc64 env pre (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.set x e)).1 post hlink
  cases hlx : fl.alloc.lookup x with
  | some rx =>
    have hrxMem := (regAllocValid_lookup hfl.valid hlx).2.1
    have hrxAlloc : rx ∈ fl.alloc.map Prod.snd := List.mem_map.mpr ⟨(x, rx), list_lookup_mem hlx, rfl⟩
    simp only [compileSR, hlx] at hlink h64 ⊢
    have reSim := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi e pre post 0 rx
      (Or.inr (allowedRegs_sub_true hrxMem)) heOk hVfE (by omega) hlink h64 st hpc hgp ht5 hsp hmemRel hframeOk
    rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨v, hv⟩ | hv
    · simp only [hv] at reSim ⊢
      obtain ⟨k1, st1, hrun1, hpc1, hrx1, hpres1, heq1⟩ := reSim
      exact ⟨k1, st1, hrun1, hpc1, hpres1.mono (fun r (hr : r = rx) => hr ▸ hrxAlloc),
        ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) heq1 hmemRel,
        ProgFrameOkR.of_set_reg_live hfl hvalid hlx hpres1 hrx1 heq1 (hnoClob rx hlx) hframeOk,
        ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1⟩
    · simp only [hv] at reSim ⊢
      obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := reSim
      exact ⟨k1, st1, hrun1, hpc1, hpres1.mono (fun r (hr : r = rx) => hr ▸ hrxAlloc),
        ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1⟩
  | none =>
    by_cases hmx : x ∈ fl.spilledVars
    · simp only [compileSR, hlx, hmx, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hlink h64 ⊢
      cases hre : exprReg? fl.alloc e with
      | some r =>
        obtain ⟨hrMem, _, v, hv, hgr⟩ := reg_exprReg_sim (lm := lm) hfl hframeOk heOk hre
        have hrt0 : r ≠ AbiReg.t0 := exprReg_ne_scratch hrMem (by decide)
        simp only [hre] at hlink h64 ⊢
        rw [hv]
        have halX : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (fl.varSlotOff x)) 8 = true := by
          rw [hsp, varSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hspAlign _
        obtain ⟨st1, hrun1, hoth1, hmem1, hpc1⟩ :=
          storeMemOff_sd_correct_lm lkm env.hrom pre post AbiReg.sp r AbiReg.t0
            (by decide) (by decide) hrt0.symm (fl.varSlotOff x) hlink h64 st hpc halX
        have hpres1 : PreservedFrameRegs fl (· = AbiReg.a0) st st1 :=
          PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hoth1
        have heq1 : MemEqOutside (varSlotSpanR fl sp x) st.mem st1.mem := by
          rw [hmem1, hsp, varSlotOff_ofInt]
          exact MemEqOutside.writeWord64 st.mem _ _ fun k hk => ⟨k, hk, rfl⟩
        have hvarSubStack : (varSlotSpanR fl sp x).sub L.stackSpan := by
          have hsi := hfl.spillIdx_lt hmx
          intro a ⟨k, hk, ha⟩; subst ha; apply frameSpanR_sub_stackSpan L hlo hhi
          refine ⟨8 * (fl.protectedSlots + fl.spillIdx x) + k, ?_, ?_⟩
          · dsimp only [varSlotSpanR, slotSpan, frameSpanR, FrameLayout.frameSlots] at hk ⊢; omega
          · dsimp only [varSlotSpanR, slotSpan, slotAddr, frameSpanR]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact ⟨_, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1,
          ProgMemRel.of_stack_eqOutside hvarSubStack heq1 hmemRel,
          (ProgFrameOkR.of_set_spill hfl hvalid hmx hpres1 (by rw [hmem1, hsp, hgr]) hframeOk).toLive_self live2,
          ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_varSlot L hfl hlo hhi hmx) heq1⟩
      | none =>
        simp only [hre] at hlink h64 ⊢
        let ce := compileETo env.tab fl 0 AbiReg.a0 e
        let cs := storeMemOff .sd AbiReg.sp AbiReg.a0 AbiReg.t0 (fl.varSlotOff x)
        have htw_all : lkm.totalSize (ce ++ cs) = lkm.totalSize ce + lkm.totalSize cs := lkm.totalSize_append ce cs
        have reSim := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi e pre (cs ++ post) 0
          AbiReg.a0 (Or.inl rfl) heOk hVfE (by omega)
          (by simpa only [ce, cs, List.append_assoc] using hlink)
          (by rw [htw_all] at h64; dsimp only [ce] at h64; omega) st hpc hgp ht5 hsp hmemRel hframeOk
        rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨v, hv⟩ | hv
        · simp only [hv] at reSim ⊢
          obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := reSim
          have htw1 : lkm.totalSize (pre ++ ce) = lkm.totalSize pre + lkm.totalSize ce := lkm.totalSize_append pre ce
          have halX : isAligned (st1.getReg AbiReg.sp + BitVec.ofInt 64 (fl.varSlotOff x)) 8 = true := by
            rw [hpres1.abi.sp.trans hsp, varSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hspAlign _
          obtain ⟨st2, hrunS, hothS, hmemS, hpc2⟩ :=
            storeMemOff_sd_correct_lm lkm env.hrom (pre ++ ce) post AbiReg.sp AbiReg.a0 AbiReg.t0
              (by decide) (by decide) (by decide) (fl.varSlotOff x)
              (by simpa only [ce, cs, List.append_assoc] using hlink)
              (by rw [htw1]; rw [htw_all] at h64; dsimp only [cs] at h64 ⊢; omega) st1 (by rw [htw1]; exact hpc1) halX
          have hpresS : PreservedFrameRegs fl (· = AbiReg.a0) st1 st2 :=
            PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hothS
          have heqS : MemEqOutside (varSlotSpanR fl sp x) st1.mem st2.mem := by
            rw [hmemS, hpres1.abi.sp.trans hsp, varSlotOff_ofInt]
            exact MemEqOutside.writeWord64 st1.mem _ _ fun k hk => ⟨k, hk, rfl⟩
          have hvarSubStack : (varSlotSpanR fl sp x).sub L.stackSpan := by
            have hsi := hfl.spillIdx_lt hmx
            intro a ⟨k, hk, ha⟩; subst ha; apply frameSpanR_sub_stackSpan L hlo hhi
            refine ⟨8 * (fl.protectedSlots + fl.spillIdx x) + k, ?_, ?_⟩
            · dsimp only [varSlotSpanR, slotSpan, frameSpanR, FrameLayout.frameSlots] at hk ⊢; omega
            · dsimp only [varSlotSpanR, slotSpan, slotAddr, frameSpanR]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
          have hm1 := ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) heq1 hmemRel
          have hf1 := ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) hpres1 heq1 hframeOk
          exact ⟨k1 + lkm.totalSize cs, st2,
            by rw [run_add, hrun1]; dsimp only; exact hrunS,
            by rw [hpc2, htw1, htw_all]; dsimp only [cs]; congr 2; omega,
            PreservedFrameRegs.of_a0 (hpres1.trans hpresS),
            ProgMemRel.of_stack_eqOutside hvarSubStack heqS hm1,
            (ProgFrameOkR.of_set_spill hfl hvalid hmx hpresS (by rw [hmemS, hpres1.abi.sp.trans hsp, ha0_1]) hf1).toLive_self live2,
            (ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1).trans
              (ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_varSlot L hfl hlo hhi hmx) heqS)⟩
        · simp only [hv] at reSim ⊢
          obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := reSim
          exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1,
            ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1⟩
    · simp only [compileSR, hlx, hmx, decide_false, Bool.not_false, ↓reduceIte] at hlink h64 ⊢
      cases hse : isSimpleExpr e with
      | true =>
        simp only [hse, ↓reduceIte] at hlink h64 ⊢
        have hPureE : ∃ v, _root_.L.evalE e ⟨lm, loc⟩ = .ok (v, ⟨lm, loc⟩) := by
          cases e with
          | const w => exact ⟨w, rfl⟩
          | var y => exact ⟨loc y, rfl⟩
          | len8 a => exact ⟨UInt64.ofNat (lm.arr8 a).size, rfl⟩
          | len64 a => exact ⟨UInt64.ofNat (lm.arr64 (.t0 a)).size, rfl⟩
          | glob g => exact ⟨lm.glob g, rfl⟩
          | _ => simp [isSimpleExpr] at hse
        obtain ⟨v, hv⟩ := hPureE
        rw [hv]
        exact ⟨0, st, rfl, by rw [lkm.totalSize_nil, Nat.add_zero]; exact hpc,
          PreservedFrameRegs.refl _ _ _, hmemRel,
          (ProgFrameOkR.of_set_dead hfl hvalid v hlx hmx (PreservedFrameRegs.refl _ _ _) (MemEqOutside.refl _ _) hframeOk).toLive_self live2,
          ProgMemOutside.refl _ _⟩
      | false =>
        simp only [hse, Bool.false_eq_true, ↓reduceIte] at hlink h64 ⊢
        have reSim := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi e pre post 0
          AbiReg.a0 (Or.inl rfl) heOk hVfE (by omega) hlink h64 st hpc hgp ht5 hsp hmemRel hframeOk
        rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨v, hv⟩ | hv
        · simp only [hv] at reSim ⊢
          obtain ⟨k1, st1, hrun1, hpc1, _, hpres1, heq1⟩ := reSim
          exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1,
            ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) heq1 hmemRel,
            (ProgFrameOkR.of_set_dead hfl hvalid v hlx hmx hpres1 heq1 hframeOk).toLive_self live2,
            ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1⟩
        · simp only [hv] at reSim ⊢
          obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := reSim
          exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1,
            ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1⟩

theorem reg_gset_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (g : GVar) (e : Expr) (pfx : String) (lblId : Nat) (brkLbl : Option String) (retLbl : String) (isTail : Bool)
    (pre post : List AsmItem)
    (hg : g.id < env.tab.ng) (heOk : exprOkB env.tab fl.nlocals e = true)
    (hVfE : ExprVarsInFrame fl e)
    (hTmp : usedTempsExpr e ≤ fl.usedTemps)
    (hlink : lkm.linkSpec (pre ++ (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.gset g e)).1 ++ post) =
      .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    match _root_.L.evalE e ⟨lm, loc⟩ with
    | .ok (v, _) =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.gset g e)).1)) ∧
        PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) st st' ∧
        ProgMemRel env.tab L st'.mem (lm.setG g v) ∧
        ProgFrameOkR L fl sp st' loc ∧
        ProgMemOutside (FnWriteMaskR L fl sp) st.mem st'.mem
    | .error _ =>
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) st st' ∧
        ProgMemOutside (FnWriteMaskR L fl sp) st.mem st'.mem := by
  have hvalid : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  have h64 := linkResolved_sub_pc64 env pre (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.gset g e)).1 post hlink
  have hglobSub : ∀ k, k < 8 → L.resGlobSpan.contains (L.T + BitVec.ofInt 64 (env.tab.globOff g) + BitVec.ofNat 64 k) :=
    fun k hk => resGlobSpan_contains_globOff L g hg hk
  have hresDisj : MemDisjoint L.resGlobSpan L.stackSpan :=
    MemDisjoint.of_sub_left L.resGlob_sub_tab (MemSpan.disjoint_to_memDisjoint L.tabSpan_valid L.stackSpan_valid L.htabDisjStack)
  cases hre : exprReg? fl.alloc e with
  | some r =>
    obtain ⟨hrMem, _, v, hv, hgr⟩ := reg_exprReg_sim (lm := lm) hfl hframeOk heOk hre
    have hrt0 : r ≠ AbiReg.t0 := exprReg_ne_scratch hrMem (by decide)
    simp only [compileSR, hre] at hlink h64 ⊢
    rw [hv]
    obtain ⟨st1, hrun1, hoth1, hmem1, hpc1⟩ :=
      storeMemOffGp_sd_correct_lm lkm env.hrom pre post fl.useT5Gp r AbiReg.t0
        (by decide) (by decide) (fun _ => by decide) hrt0.symm (env.tab.globOff g) L.T hlink h64 st hpc hgp ht5 (isAligned8_of_globOff L g)
    have hpres1 : PreservedFrameRegs fl (fun _ => False) st st1 :=
      PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hoth1
    have heq1 : MemEqOutside L.resGlobSpan st.mem st1.mem := by
      rw [hmem1]; exact MemEqOutside.writeWord64 st.mem _ _ hglobSub
    exact ⟨_, st1, hrun1, hpc1, hpres1.mono (fun _ h => False.elim h),
      by rw [hmem1, hgr]; exact ProgMemRel.setG hmemRel g hg v,
      ProgFrameOkR.of_mem_outside_stack hfl hlo hhi L.resGlobSpan hresDisj hpres1 heq1 hframeOk,
      ProgMemOutside.of_memEqOutside (fun _ ha => Or.inr (Or.inl ha)) heq1⟩
  | none =>
    simp only [compileSR, hre] at hlink h64 ⊢
    let ce := compileETo env.tab fl 0 AbiReg.a0 e
    let cs := storeMemOffGp fl.useT5Gp .sd AbiReg.a0 AbiReg.t0 (env.tab.globOff g)
    have htw_all : lkm.totalSize (ce ++ cs) = lkm.totalSize ce + lkm.totalSize cs := lkm.totalSize_append ce cs
    have reSim := reg_evalExpr_sim env L fl hfl lm loc hspAlign hlo hhi e pre (cs ++ post) 0
      AbiReg.a0 (Or.inl rfl) heOk hVfE (by omega)
      (by simpa only [ce, cs, List.append_assoc] using hlink)
      (by rw [htw_all] at h64; dsimp only [ce] at h64; omega) st hpc hgp ht5 hsp hmemRel hframeOk
    rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨v, hv⟩ | hv
    · simp only [hv] at reSim ⊢
      obtain ⟨k1, st1, hrun1, hpc1, ha0_1, hpres1, heq1⟩ := reSim
      have htw1 : lkm.totalSize (pre ++ ce) = lkm.totalSize pre + lkm.totalSize ce := lkm.totalSize_append pre ce
      have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.abi.gp.trans hgp
      obtain ⟨st2, hrunS, hothS, hmemS, hpc2⟩ :=
        storeMemOffGp_sd_correct_lm lkm env.hrom (pre ++ ce) post fl.useT5Gp AbiReg.a0 AbiReg.t0
          (by decide) (by decide) (fun _ => by decide) (by decide) (env.tab.globOff g) L.T
          (by simpa only [ce, cs, List.append_assoc] using hlink)
          (by rw [htw1]; rw [htw_all] at h64; dsimp only [cs] at h64 ⊢; omega) st1 (by rw [htw1]; exact hpc1)
          hgp1 (ht5.of_preserved hpres1) (isAligned8_of_globOff L g)
      have hpresS : PreservedFrameRegs fl (fun _ => False) st1 st2 :=
        PreservedFrameRegs.of_scratch1 AbiReg.t0 (by decide) hothS
      have heqS : MemEqOutside L.resGlobSpan st1.mem st2.mem := by
        rw [hmemS]; exact MemEqOutside.writeWord64 st1.mem _ _ hglobSub
      have hm1 := ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) heq1 hmemRel
      have hf1 := ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) hpres1 heq1 hframeOk
      exact ⟨k1 + lkm.totalSize cs, st2,
        by rw [run_add, hrun1]; dsimp only; exact hrunS,
        by rw [hpc2, htw1, htw_all]; dsimp only [cs]; congr 2; omega,
        (PreservedFrameRegs.of_a0 hpres1).trans (hpresS.mono (fun _ h => False.elim h)),
        by rw [hmemS, ha0_1]; exact ProgMemRel.setG hm1 g hg v,
        ProgFrameOkR.of_mem_outside_stack hfl hlo hhi L.resGlobSpan hresDisj hpresS heqS hf1,
        (ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1).trans
          (ProgMemOutside.of_memEqOutside (fun _ ha => Or.inr (Or.inl ha)) heqS)⟩
    · simp only [hv] at reSim ⊢
      obtain ⟨k1, st1, hrun1, hpc1, hpres1, heq1⟩ := reSim
      exact ⟨k1, st1, hrun1, hpc1, PreservedFrameRegs.of_a0 hpres1,
        ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1⟩

private theorem reg_st64Tail_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals)
    (s : TieredArray) (re ri tmp : Reg) (i : Expr) (vi ve : _root_.L.Word)
    (htmp0 : tmp ≠ 0#5) (htmpS : tmp ∈ scratchRegs) (htmpT1 : tmp ≠ AbiReg.t1)
    (hreTmp : re ≠ tmp) (hreT1 : re ≠ AbiReg.t1)
    (hvi : _root_.L.evalE i ⟨lm, loc⟩ = .ok (vi, ⟨lm, loc⟩))
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ st64Tail re ri tmp i ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (st64Tail re ri tmp i)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (ht1 : st.getReg AbiReg.t1 = L.base64 s)
    (hri : st.getReg ri = vi.toBitVec)
    (hre : st.getReg re = ve.toBitVec) :
    ∃ k st', RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (st64Tail re ri tmp i))) ∧
      PreservedFrameRegs fl (fun _ => False) st st' ∧
      st'.mem = writeWord64 st.mem (L.base64 s + BitVec.ofNat 64 (8 * vi.toNat)) ve.toBitVec := by
  have hDyn : st64Tail re ri tmp i = [Asm.slli tmp ri 3#6, Asm.add AbiReg.t1 AbiReg.t1 tmp, Asm.sd AbiReg.t1 re 0#12] →
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (st64Tail re ri tmp i))) ∧
        PreservedFrameRegs fl (fun _ => False) st st' ∧
        st'.mem = writeWord64 st.mem (L.base64 s + BitVec.ofNat 64 (8 * vi.toNat)) ve.toBitVec := by
    intro hT
    have htw_t : lkm.totalSize (st64Tail re ri tmp i) = 3 := by
      rw [hT]; simp [Asm.slli, Asm.add, Asm.sd, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
    have hsSlli := step_item_instr_lm lkm env.hrom pre ([Asm.add AbiReg.t1 AbiReg.t1 tmp, Asm.sd AbiReg.t1 re 0#12] ++ post)
      (.shImm .slli tmp ri 3#6)
      (by rw [hT] at hlink; simpa only [Asm.slli, List.cons_append, List.nil_append, List.append_assoc] using hlink)
      (by rw [htw_t] at h64; omega) st hpc
    let st1 := stepReg st tmp (evalShiftImm .slli (st.getReg ri) 3#6) (st.pc + 4#64)
    have hrun1 : RV64.run env.rom 1 st = .cont st1 := run_one_cont _ _ st1 (by rw [hsSlli]; rfl)
    have hpres1 : PreservedFrameRegs fl (fun _ => False) st st1 :=
      PreservedFrameRegs.of_scratch1 tmp htmpS (fun r hr => getReg_stepReg_ne st tmp r hr _ _)
    have htw1 : lkm.totalSize (pre ++ [Asm.slli tmp ri 3#6]) = lkm.totalSize pre + 1 := by
      rw [lkm.totalSize_append, Asm.slli, lkm.totalSize_instr]
    have hpc1 : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ [Asm.slli tmp ri 3#6])) := by
      change st.pc + 4#64 = _; rw [pc_add_4_ofNat st.pc hpc, htw1]
    have hsAdd := step_item_instr_lm lkm env.hrom (pre ++ [Asm.slli tmp ri 3#6])
      ([Asm.sd AbiReg.t1 re 0#12] ++ post) (.alu .add AbiReg.t1 AbiReg.t1 tmp)
      (by rw [hT] at hlink; simpa only [Asm.slli, Asm.add, List.cons_append, List.nil_append, List.append_assoc] using hlink)
      (by rw [htw1]; rw [htw_t] at h64; omega) st1 hpc1
    let st2 := stepReg st1 AbiReg.t1 (st1.getReg AbiReg.t1 + st1.getReg tmp) (st1.pc + 4#64)
    have hrun2 : RV64.run env.rom 1 st1 = .cont st2 := run_one_cont _ _ st2 (by rw [hsAdd]; rfl)
    have hpres2 : PreservedFrameRegs fl (fun _ => False) st1 st2 :=
      PreservedFrameRegs.of_scratch1 AbiReg.t1 (by decide) (fun r hr => getReg_stepReg_ne st1 AbiReg.t1 r hr _ _)
    have htw2 : lkm.totalSize (pre ++ [Asm.slli tmp ri 3#6] ++ [Asm.add AbiReg.t1 AbiReg.t1 tmp]) =
        lkm.totalSize pre + 2 := by
      rw [lkm.totalSize_append, htw1, Asm.add, lkm.totalSize_instr]
    have hpc2 : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ [Asm.slli tmp ri 3#6] ++ [Asm.add AbiReg.t1 AbiReg.t1 tmp])) := by
      change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1, htw2, htw1]
    have haddr : st2.getReg AbiReg.t1 = L.base64 s + BitVec.ofNat 64 (8 * vi.toNat) := by
      change (stepReg st1 AbiReg.t1 _ _).getReg AbiReg.t1 = _
      rw [getReg_stepReg_eq _ _ (by decide)]
      have ht1_1 : st1.getReg AbiReg.t1 = L.base64 s :=
        (getReg_stepReg_ne st tmp AbiReg.t1 htmpT1.symm _ _).trans ht1
      have htmp_1 : st1.getReg tmp = BitVec.ofNat 64 (8 * vi.toNat) := by
        change (stepReg st tmp _ _).getReg tmp = _
        rw [getReg_stepReg_eq _ _ htmp0, hri]
        apply BitVec.eq_of_toNat_eq
        simp only [evalShiftImm, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
          show (3#6 : BitVec 6).toNat = 3 from rfl, Nat.shiftLeft_eq]
        rw [show vi.toNat * 2 ^ 3 = 8 * vi.toNat by omega]
      rw [ht1_1, htmp_1]
    have halS : isAligned (st2.getReg AbiReg.t1 + sextImm12 0#12) 8 = true := by
      rw [haddr, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero]
      exact isAligned8_add_mul8 _ (L.h64Align s) vi.toNat
    have hsSd := step_item_instr_lm lkm env.hrom
      (pre ++ [Asm.slli tmp ri 3#6] ++ [Asm.add AbiReg.t1 AbiReg.t1 tmp]) post
      (.store .sd AbiReg.t1 re 0#12)
      (by rw [hT] at hlink; simpa only [Asm.slli, Asm.add, Asm.sd, List.cons_append, List.nil_append, List.append_assoc] using hlink)
      (by rw [htw2]; rw [htw_t] at h64; omega) st2 hpc2
    let st3 : State := { st2 with pc := st2.pc + 4#64, mem := writeWord64 st2.mem (st2.getReg AbiReg.t1 + sextImm12 0#12) (st2.getReg re) }
    have hrun3 : RV64.run env.rom 1 st2 = .cont st3 :=
      run_one_cont _ _ st3 (by rw [hsSd]; simp only [execInstr, halS, ↓reduceIte]; rfl)
    have hre2 : st2.getReg re = ve.toBitVec :=
      (getReg_stepReg_ne st1 AbiReg.t1 re hreT1 _ _).trans
        ((getReg_stepReg_ne st tmp re hreTmp _ _).trans hre)
    have hm2 : st2.mem = st.mem := by dsimp only [st2, st1]; rw [mem_stepReg, mem_stepReg]
    have hpres3 : PreservedFrameRegs fl (fun _ => False) st2 st3 :=
      ⟨⟨rfl, rfl, rfl, rfl⟩, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
    exact ⟨1 + (1 + 1), st3,
      by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
      by change st2.pc + 4#64 = _; rw [pc_add_4_ofNat st2.pc hpc2, htw2, htw_t],
      hpres1.trans (hpres2.trans hpres3),
      by dsimp only [st3]; rw [hm2, haddr, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero, hre2]⟩
  cases hiC : i.constVal? with
  | some w =>
    have hiEq : i = .const w := expr_constVal_eq_some hiC
    have hviEq : vi = w := by rw [hiEq] at hvi; exact (Prod.mk.inj (Except.ok.inj hvi)).1.symm
    subst hviEq
    by_cases hlt : vi.toNat < 256
    · have hT : st64Tail re ri tmp i = [Asm.sd AbiReg.t1 re (BitVec.ofNat 12 (8 * vi.toNat))] := by
        simp only [st64Tail, hiC, hlt, ↓reduceIte]
      have htw_t : lkm.totalSize (st64Tail re ri tmp i) = 1 := by rw [hT]; simp [Asm.sd, lkm.totalSize_instr]
      have haddr : st.getReg AbiReg.t1 + sextImm12 (BitVec.ofNat 12 (8 * vi.toNat)) =
          L.base64 s + BitVec.ofNat 64 (8 * vi.toNat) := by
        rw [ht1, sextImm12_ofNat_lt (8 * vi.toNat) (by omega)]
      have halS : isAligned (st.getReg AbiReg.t1 + sextImm12 (BitVec.ofNat 12 (8 * vi.toNat))) 8 = true := by
        rw [haddr]; exact isAligned8_add_mul8 _ (L.h64Align s) vi.toNat
      have hsSd := step_item_instr_lm lkm env.hrom pre post
        (.store .sd AbiReg.t1 re (BitVec.ofNat 12 (8 * vi.toNat)))
        (by rw [hT] at hlink; simpa only [Asm.sd] using hlink)
        (by rw [htw_t] at h64; omega) st hpc
      let st1 : State := { st with pc := st.pc + 4#64, mem := writeWord64 st.mem (st.getReg AbiReg.t1 + sextImm12 (BitVec.ofNat 12 (8 * vi.toNat))) (st.getReg re) }
      have hrun1 : RV64.run env.rom 1 st = .cont st1 :=
        run_one_cont _ _ st1 (by rw [hsSd]; simp only [execInstr, halS, ↓reduceIte]; rfl)
      have hpres1 : PreservedFrameRegs fl (fun _ => False) st st1 :=
        ⟨⟨rfl, rfl, rfl, rfl⟩, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
      exact ⟨1, st1, hrun1,
        by change st.pc + 4#64 = _; rw [pc_add_4_ofNat st.pc hpc, htw_t],
        hpres1, by dsimp only [st1]; rw [haddr, hre]⟩
    · exact hDyn (by simp only [st64Tail, hiC, hlt, ↓reduceIte])
  | none => exact hDyn (by simp only [st64Tail, hiC])

private theorem reg_st32tTail_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals)
    (s : TieredArray) (re ri tmp : Reg) (i : Expr) (vi ve : _root_.L.Word)
    (htmp0 : tmp ≠ 0#5) (htmpS : tmp ∈ scratchRegs) (htmpT1 : tmp ≠ AbiReg.t1)
    (hreTmp : re ≠ tmp) (hreT1 : re ≠ AbiReg.t1)
    (hvi : _root_.L.evalE i ⟨lm, loc⟩ = .ok (vi, ⟨lm, loc⟩))
    (pre post : List AsmItem)
    (hlink : lkm.linkSpec (pre ++ st32tTail re ri tmp i ++ post) = .ok (env.code, env.labels))
    (h64 : 4 * (lkm.totalSize pre + lkm.totalSize (st32tTail re ri tmp i)) < 2 ^ 64)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (ht1 : st.getReg AbiReg.t1 = L.base64 s)
    (hri : st.getReg ri = vi.toBitVec)
    (hre : st.getReg re = ve.toBitVec) :
    ∃ k st', RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (st32tTail re ri tmp i))) ∧
      PreservedFrameRegs fl (fun _ => False) st st' ∧
      st'.mem = RV64.storeBytes st.mem (L.base64 s + BitVec.ofNat 64 (4 * vi.toNat)) 4 (ve.toBitVec.extractLsb' 0 32) := by
  have hDyn : st32tTail re ri tmp i = [Asm.slli tmp ri 2#6, Asm.add AbiReg.t1 AbiReg.t1 tmp, Asm.sw AbiReg.t1 re 0#12] →
      ∃ k st', RV64.run env.rom k st = .cont st' ∧
        st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (st32tTail re ri tmp i))) ∧
        PreservedFrameRegs fl (fun _ => False) st st' ∧
        st'.mem = RV64.storeBytes st.mem (L.base64 s + BitVec.ofNat 64 (4 * vi.toNat)) 4 (ve.toBitVec.extractLsb' 0 32) := by
    intro hT
    have htw_t : lkm.totalSize (st32tTail re ri tmp i) = 3 := by
      rw [hT]; simp [Asm.slli, Asm.add, Asm.sw, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
    have hsSlli := step_item_instr_lm lkm env.hrom pre ([Asm.add AbiReg.t1 AbiReg.t1 tmp, Asm.sw AbiReg.t1 re 0#12] ++ post)
      (.shImm .slli tmp ri 2#6)
      (by rw [hT] at hlink; simpa only [Asm.slli, List.cons_append, List.nil_append, List.append_assoc] using hlink)
      (by rw [htw_t] at h64; omega) st hpc
    let st1 := stepReg st tmp (evalShiftImm .slli (st.getReg ri) 2#6) (st.pc + 4#64)
    have hrun1 : RV64.run env.rom 1 st = .cont st1 := run_one_cont _ _ st1 (by rw [hsSlli]; rfl)
    have hpres1 : PreservedFrameRegs fl (fun _ => False) st st1 :=
      PreservedFrameRegs.of_scratch1 tmp htmpS (fun r hr => getReg_stepReg_ne st tmp r hr _ _)
    have htw1 : lkm.totalSize (pre ++ [Asm.slli tmp ri 2#6]) = lkm.totalSize pre + 1 := by
      rw [lkm.totalSize_append, Asm.slli, lkm.totalSize_instr]
    have hpc1 : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ [Asm.slli tmp ri 2#6])) := by
      change st.pc + 4#64 = _; rw [pc_add_4_ofNat st.pc hpc, htw1]
    have hsAdd := step_item_instr_lm lkm env.hrom (pre ++ [Asm.slli tmp ri 2#6])
      ([Asm.sw AbiReg.t1 re 0#12] ++ post) (.alu .add AbiReg.t1 AbiReg.t1 tmp)
      (by rw [hT] at hlink; simpa only [Asm.slli, Asm.add, List.cons_append, List.nil_append, List.append_assoc] using hlink)
      (by rw [htw1]; rw [htw_t] at h64; omega) st1 hpc1
    let st2 := stepReg st1 AbiReg.t1 (st1.getReg AbiReg.t1 + st1.getReg tmp) (st1.pc + 4#64)
    have hrun2 : RV64.run env.rom 1 st1 = .cont st2 := run_one_cont _ _ st2 (by rw [hsAdd]; rfl)
    have hpres2 : PreservedFrameRegs fl (fun _ => False) st1 st2 :=
      PreservedFrameRegs.of_scratch1 AbiReg.t1 (by decide) (fun r hr => getReg_stepReg_ne st1 AbiReg.t1 r hr _ _)
    have htw2 : lkm.totalSize (pre ++ [Asm.slli tmp ri 2#6] ++ [Asm.add AbiReg.t1 AbiReg.t1 tmp]) =
        lkm.totalSize pre + 2 := by
      rw [lkm.totalSize_append, htw1, Asm.add, lkm.totalSize_instr]
    have hpc2 : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ [Asm.slli tmp ri 2#6] ++ [Asm.add AbiReg.t1 AbiReg.t1 tmp])) := by
      change st1.pc + 4#64 = _; rw [pc_add_4_ofNat st1.pc hpc1, htw2, htw1]
    have haddr : st2.getReg AbiReg.t1 + sextImm12 0#12 = L.base64 s + BitVec.ofNat 64 (4 * vi.toNat) := by
      change (stepReg st1 AbiReg.t1 _ _).getReg AbiReg.t1 + sextImm12 0#12 = _
      rw [getReg_stepReg_eq _ _ (by decide), show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero]
      have ht1_1 : st1.getReg AbiReg.t1 = L.base64 s :=
        (getReg_stepReg_ne st tmp AbiReg.t1 htmpT1.symm _ _).trans ht1
      have htmp_1 : st1.getReg tmp = BitVec.ofNat 64 (4 * vi.toNat) := by
        change (stepReg st tmp _ _).getReg tmp = _
        rw [getReg_stepReg_eq _ _ htmp0, hri]
        apply BitVec.eq_of_toNat_eq
        simp only [evalShiftImm, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
          show (2#6 : BitVec 6).toNat = 2 from rfl, Nat.shiftLeft_eq]
        rw [show vi.toNat * 2 ^ 2 = 4 * vi.toNat by omega]
      rw [ht1_1, htmp_1]
    have halS : isAligned (st2.getReg AbiReg.t1 + sextImm12 0#12) 4 = true := by
      rw [haddr]; exact isAligned4_of_base64_add4 L s vi
    obtain ⟨hrun3, hpc3, _⟩ :=
      step_sw_off_r env (pre ++ [Asm.slli tmp ri 2#6] ++ [Asm.add AbiReg.t1 AbiReg.t1 tmp]) post
        AbiReg.t1 re 0#12
        (by rw [hT] at hlink; simpa only [Asm.slli, Asm.add, Asm.sw, Asm.raw, List.cons_append, List.nil_append, List.append_assoc] using hlink)
        (by rw [htw2]; rw [htw_t] at h64; omega) st2 hpc2 halS
    let st3 : State := { st2 with pc := st2.pc + 4#64, mem := RV64.storeBytes st2.mem (st2.getReg AbiReg.t1 + sextImm12 0#12) 4 ((st2.getReg re).extractLsb' 0 32) }
    have hre2 : st2.getReg re = ve.toBitVec :=
      (getReg_stepReg_ne st1 AbiReg.t1 re hreT1 _ _).trans
        ((getReg_stepReg_ne st tmp re hreTmp _ _).trans hre)
    have hm2 : st2.mem = st.mem := by dsimp only [st2, st1]; rw [mem_stepReg, mem_stepReg]
    have hpres3 : PreservedFrameRegs fl (fun _ => False) st2 st3 :=
      ⟨⟨rfl, rfl, rfl, rfl⟩, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
    exact ⟨1 + (1 + 1), st3,
      by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
      by rw [hpc3, htw2, htw_t],
      hpres1.trans (hpres2.trans hpres3),
      by dsimp only [st3]; rw [hm2, haddr, hre2]⟩
  cases hiC : i.constVal? with
  | some w =>
    have hiEq : i = .const w := expr_constVal_eq_some hiC
    have hviEq : vi = w := by rw [hiEq] at hvi; exact (Prod.mk.inj (Except.ok.inj hvi)).1.symm
    subst hviEq
    by_cases hlt : vi.toNat < 512
    · have hT : st32tTail re ri tmp i = [Asm.sw AbiReg.t1 re (BitVec.ofNat 12 (4 * vi.toNat))] := by
        simp only [st32tTail, hiC, hlt, ↓reduceIte]
      have htw_t : lkm.totalSize (st32tTail re ri tmp i) = 1 := by rw [hT]; simp [Asm.sw, lkm.totalSize_instr]
      have haddr : st.getReg AbiReg.t1 + sextImm12 (BitVec.ofNat 12 (4 * vi.toNat)) =
          L.base64 s + BitVec.ofNat 64 (4 * vi.toNat) := by
        rw [ht1, sextImm12_ofNat_lt (4 * vi.toNat) (by omega)]
      have halS : isAligned (st.getReg AbiReg.t1 + sextImm12 (BitVec.ofNat 12 (4 * vi.toNat))) 4 = true := by
        rw [haddr]; exact isAligned4_of_base64_add4 L s vi
      obtain ⟨hrun1, hpc1, _⟩ :=
        step_sw_off_r env pre post AbiReg.t1 re (BitVec.ofNat 12 (4 * vi.toNat))
          (by rw [hT] at hlink; simpa only [Asm.sw, Asm.raw] using hlink)
          (by rw [htw_t] at h64; omega) st hpc halS
      let st1 : State := { st with pc := st.pc + 4#64, mem := RV64.storeBytes st.mem (st.getReg AbiReg.t1 + sextImm12 (BitVec.ofNat 12 (4 * vi.toNat))) 4 ((st.getReg re).extractLsb' 0 32) }
      have hpres1 : PreservedFrameRegs fl (fun _ => False) st st1 :=
        ⟨⟨rfl, rfl, rfl, rfl⟩, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
      exact ⟨1, st1, hrun1,
        by rw [hpc1, htw_t],
        hpres1, by dsimp only [st1]; rw [haddr, hre]⟩
    · exact hDyn (by simp only [st32tTail, hiC, hlt, ↓reduceIte])
  | none => exact hDyn (by simp only [st32tTail, hiC])

private theorem reg_st64_word_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (s : TieredArray) (i e : Expr)
    (pre post : List AsmItem)
    (hsOk : env.tab.wordPosOkB s = true)
    (hiOk : exprOkB env.tab fl.nlocals i = true)
    (heOk : exprOkB env.tab fl.nlocals e = true)
    (hVfI : ExprVarsInFrame fl i) (hVfE : ExprVarsInFrame fl e)
    (hTmp : (if isSimpleExpr i then usedTempsExpr e
             else if isSimpleExpr e then usedTempsExpr i
             else max (usedTempsExpr i) (1 + usedTempsExpr e)) ≤ fl.usedTemps)
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    let cpRes := compileStorePairR env.tab fl i e
    let cp := cpRes.1; let ri := cpRes.2.1; let re := cpRes.2.2
    let cS := st64Tail re ri AbiReg.t2 i
    let code :=
      cp ++
      loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (env.tab.len64 s) ++
      [Asm.bgeu ri AbiReg.t1 errLabel] ++
      loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (env.tab.base64 s) ++
      cS
    lkm.linkSpec (pre ++ code ++ post) = .ok (env.code, env.labels) →
    match _root_.L.evalE i ⟨lm, loc⟩, _root_.L.evalE e ⟨lm, loc⟩ with
    | .ok (vi, _), .ok (ve, _) =>
      if vi.toNat < (lm.arr64 s).size then
        ∃ k r', RV64.run env.rom k st = .cont r' ∧
          r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize code)) ∧
          PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) st r' ∧
          ProgMemRel env.tab L r'.mem (lm.set64 s vi ve) ∧
          ProgFrameOkR L fl sp r' loc ∧
          ProgMemOutside (FnWriteMaskR L fl sp) st.mem r'.mem
      else
        ∃ k r', RV64.run env.rom k st = .cont r' ∧
          r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
          PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) st r' ∧
          ProgMemOutside (FnWriteMaskR L fl sp) st.mem r'.mem
    | _, _ =>
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) st r' ∧
        ProgMemOutside (FnWriteMaskR L fl sp) st.mem r'.mem := by
  intro cpRes cp ri re cS code hlink
  have hvalid : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  let cL := loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (env.tab.len64 s)
  let br := [Asm.bgeu ri AbiReg.t1 errLabel]
  let cB := loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (env.tab.base64 s)
  have hcodeEq : code = cp ++ cL ++ br ++ cB ++ cS := rfl
  have h64 := linkResolved_sub_pc64 env pre (cp ++ cL ++ br ++ cB ++ cS) post hlink
  have htw_all : lkm.totalSize (cp ++ cL ++ br ++ cB ++ cS) =
      lkm.totalSize cp + lkm.totalSize cL + lkm.totalSize br + lkm.totalSize cB + lkm.totalSize cS := by
    simp only [lkm.totalSize_append]
  have hpair := reg_compileStorePairR_sim env L fl hfl lm loc hspAlign hlo hhi i e pre
    ((cL ++ br ++ cB ++ cS) ++ post) hiOk heOk hVfI hVfE hTmp
    (by simpa only [code, cp, cpRes, cL, br, cB, List.append_assoc] using hlink) st hpc hgp ht5 hsp hmemRel hframeOk
  rcases hpair with ⟨hriW, hreW, hpairSim⟩
  have hriW' : ri = AbiReg.zero ∨ ri = AbiReg.a0 ∨ ri = AbiReg.t0 ∨ ri = AbiReg.t3 ∨ ri ∈ allowedRegs true := by
    rcases hriW with h | h | h | h; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  have hreW' : re = AbiReg.zero ∨ re = AbiReg.a0 ∨ re = AbiReg.t0 ∨ re = AbiReg.t3 ∨ re ∈ allowedRegs true := by
    rcases hreW with h | h | h | h; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
  · rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨ve, hve⟩ | hve
    · simp only [hvi, hve] at hpairSim ⊢
      obtain ⟨kp, st1, hrun1, hpc1, hri1, hre1, hpres1, heq1⟩ := hpairSim
      have htw1 : lkm.totalSize (pre ++ cp) = lkm.totalSize pre + lkm.totalSize cp := lkm.totalSize_append pre cp
      have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.abi.gp.trans hgp
      have hm1 := ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) heq1 hmemRel
      have hf1 := ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) (hpres1.mono (fun _ h => False.elim h)) heq1 hframeOk
      rcases hm1.2.1 s hsOk with ⟨hcap64, hlt61, hlenR, hbaseR, _⟩
      have hlt64 : (lm.arr64 s).size < 2 ^ 64 := by omega
      have halL : isAligned (L.T + BitVec.ofInt 64 (env.tab.len64 s)) 8 = true := by
        rw [Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
      obtain ⟨st2, hrun2, hoth2, ht1_2, hmem2, hpc2⟩ :=
        loadMemOffGp_ld_correct_lm lkm env.hrom (pre ++ cp) ((br ++ cB ++ cS) ++ post) fl.useT5Gp
          AbiReg.t1 AbiReg.t2 (by decide) (by decide) (by decide) (fun _ => by decide) (env.tab.len64 s) L.T
          (by simpa only [code, cL, br, cB, List.append_assoc] using hlink)
          (by rw [htw1]; rw [htw_all] at h64; dsimp only [cL] at h64 ⊢; omega) st1 (by rw [htw1]; exact hpc1)
          hgp1 (ht5.of_preserved hpres1) halL
      have hpres2 : PreservedFrameRegs fl (fun _ => False) st1 st2 :=
        PreservedFrameRegs.of_scratch2 AbiReg.t1 AbiReg.t2 (by decide) (by decide) hoth2
      have htw2 : lkm.totalSize (pre ++ cp ++ cL) = lkm.totalSize pre + lkm.totalSize cp + lkm.totalSize cL := by
        rw [lkm.totalSize_append, htw1]
      have hri2 : st2.getReg ri = vi.toBitVec :=
        (hoth2 ri (storeReg_ne_scratch hriW' (by decide)) (storeReg_ne_scratch hriW' (by decide))).trans hri1
      have hre2 : st2.getReg re = ve.toBitVec :=
        (hoth2 re (storeReg_ne_scratch hreW' (by decide)) (storeReg_ne_scratch hreW' (by decide))).trans hre1
      have ht1Val : st2.getReg AbiReg.t1 = BitVec.ofNat 64 (lm.arr64 s).size := by rw [ht1_2, hlenR]
      have hbrSz : lkm.itemSize (.br .bgeu ri AbiReg.t1 errLabel) = lkm.totalSize br := by simp [br, Asm.bgeu, lkm.totalSize_singleton]
      by_cases hb : vi.toNat < (lm.arr64 s).size
      · simp only [hb, ↓reduceIte]
        have hcondF : evalBranch .bgeu (st2.getReg ri) (st2.getReg AbiReg.t1) = false := by
          rw [hri2, ht1Val, u64_toBitVec_eq_ofNat, evalBranch_bgeu_nat (by simpa using vi.toBitVec.isLt) hlt64]
          simp [show ¬((lm.arr64 s).size ≤ vi.toNat) by omega]
        obtain ⟨kBr, st3, hrun3, hpc3, hoth3, _, hmem3⟩ :=
          prog_step_br_fall env (pre ++ cp ++ cL) ((cB ++ cS) ++ post)
            .bgeu ri AbiReg.t1 errLabel env.errTarget env.herrLbl
            ⟨storeReg_ne_scratch hriW' (by decide), by decide⟩
            (by simpa only [code, cL, br, cB, Asm.bgeu, List.append_assoc] using hlink)
            (by rw [htw2, hbrSz]; rw [htw_all] at h64; omega) st2 (by rw [htw2, ← htw1]; exact hpc2) hcondF
        have hpres3 : PreservedFrameRegs fl (fun _ => False) st2 st3 :=
          preservedFrameRegs_of_t6_s1 hoth3
        have htw3 : lkm.totalSize (pre ++ cp ++ cL ++ br) = lkm.totalSize pre + lkm.totalSize cp + lkm.totalSize cL + lkm.totalSize br := by
          rw [lkm.totalSize_append, htw2]
        have hgp3 : st3.getReg AbiReg.gp = L.T := (hoth3 AbiReg.gp (by decide)).trans ((hoth2 AbiReg.gp (by decide) (by decide)).trans hgp1)
        have halB : isAligned (L.T + BitVec.ofInt 64 (env.tab.base64 s)) 8 = true := by
          rw [Tab.base64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
        obtain ⟨st4, hrun4, hoth4, ht1_4, hmem4, hpc4⟩ :=
          loadMemOffGp_ld_correct_lm lkm env.hrom (pre ++ cp ++ cL ++ br) (cS ++ post) fl.useT5Gp
            AbiReg.t1 AbiReg.t2 (by decide) (by decide) (by decide) (fun _ => by decide) (env.tab.base64 s) L.T
            (by simpa only [code, cL, br, cB, List.append_assoc] using hlink)
            (by rw [htw3]; rw [htw_all] at h64; dsimp only [cB] at h64 ⊢; omega) st3 (by rw [htw3, ← htw2, ← hbrSz]; exact hpc3)
            hgp3 (ht5.of_preserved (hpres1.trans (hpres2.trans hpres3))) halB
        have hpres4 : PreservedFrameRegs fl (fun _ => False) st3 st4 :=
          PreservedFrameRegs.of_scratch2 AbiReg.t1 AbiReg.t2 (by decide) (by decide) hoth4
        have htw4 : lkm.totalSize (pre ++ cp ++ cL ++ br ++ cB) =
            lkm.totalSize pre + lkm.totalSize cp + lkm.totalSize cL + lkm.totalSize br + lkm.totalSize cB := by
          rw [lkm.totalSize_append, htw3]
        have ht1Val4 : st4.getReg AbiReg.t1 = L.base64 s := by rw [ht1_4, hmem3, hmem2, hbaseR]
        have hri4 : st4.getReg ri = vi.toBitVec :=
          (hoth4 ri (storeReg_ne_scratch hriW' (by decide)) (storeReg_ne_scratch hriW' (by decide))).trans
            ((hoth3 ri ⟨storeReg_ne_scratch hriW' (by decide), storeReg_ne_scratch hriW' (by decide)⟩).trans hri2)
        have hre4 : st4.getReg re = ve.toBitVec :=
          (hoth4 re (storeReg_ne_scratch hreW' (by decide)) (storeReg_ne_scratch hreW' (by decide))).trans
            ((hoth3 re ⟨storeReg_ne_scratch hreW' (by decide), storeReg_ne_scratch hreW' (by decide)⟩).trans hre2)
        have hm4 : st4.mem = st1.mem := by rw [hmem4, hmem3, hmem2]
        have h64Disj : MemDisjoint (L.arr64Span s) L.stackSpan :=
          MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid s) L.stackSpan_valid (L.h64DisjStack s hsOk)
        obtain ⟨kT, stEnd, hrunT, hpcT, hpresT, hmemT⟩ :=
          reg_st64Tail_sim env L fl lm loc s re ri AbiReg.t2 i vi ve
            (by decide) (by decide) (by decide)
            (storeReg_ne_scratch hreW' (by decide)) (storeReg_ne_scratch hreW' (by decide))
            hvi (pre ++ cp ++ cL ++ br ++ cB) post
            (by simpa only [code, cL, br, cB, cS, List.append_assoc] using hlink)
            (by rw [htw4]; rw [htw_all] at h64; dsimp only [cS] at h64 ⊢; omega)
            st4 (by rw [htw4, ← htw3]; exact hpc4) ht1Val4 hri4 hre4
        have hmemEnd : stEnd.mem = writeWord64 st1.mem (L.base64 s + BitVec.ofNat 64 (8 * vi.toNat)) ve.toBitVec := by
          rw [hmemT, hm4]
        have hpres1E : PreservedFrameRegs fl (fun _ => False) st1 stEnd :=
          hpres2.trans (hpres3.trans (hpres4.trans hpresT))
        have heq1E : MemEqOutside (L.arr64Span s) st1.mem stEnd.mem := by
          rw [hmemEnd]; apply MemEqOutside.writeWord64
          intro k hk; exact MemSpan.sub_range (s := L.arr64Span s) (8 * vi.toNat) 8
            (by dsimp only [ProgLayout.arr64Span]; omega) k hk
        exact ⟨kp + (lkm.totalSize cL + (kBr + (lkm.totalSize cB + kT))), stEnd,
          by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; rw [run_add, hrun3]; dsimp only
             rw [run_add, hrun4]; dsimp only; exact hrunT,
          by rw [hpcT, htw4, hcodeEq, htw_all]; dsimp only [cS]; congr 2; omega,
          (hpres1.trans hpres1E).mono (fun _ h => False.elim h),
          by rw [hmemEnd]; exact ProgMemRel.set64 hm1 s hsOk vi ve hb,
          ProgFrameOkR.of_mem_outside_stack hfl hlo hhi (L.arr64Span s) h64Disj hpres1E heq1E hf1,
          (ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1).trans
            (ProgMemOutside.of_memEqOutside (fun _ ha => Or.inr (Or.inr (Or.inr ⟨s, hsOk, ha⟩))) heq1E)⟩
      · simp only [hb, ↓reduceIte]
        have hcondT : evalBranch .bgeu (st2.getReg ri) (st2.getReg AbiReg.t1) = true := by
          rw [hri2, ht1Val, u64_toBitVec_eq_ofNat, evalBranch_bgeu_nat (by simpa using vi.toBitVec.isLt) hlt64]
          simp [show (lm.arr64 s).size ≤ vi.toNat by omega]
        obtain ⟨kBr, st3, hrun3, hpc3, hoth3, _, hmem3⟩ :=
          prog_step_br_taken env (pre ++ cp ++ cL) ((cB ++ cS) ++ post)
            .bgeu ri AbiReg.t1 errLabel env.errTarget env.herrLbl
            ⟨storeReg_ne_scratch hriW' (by decide), by decide⟩
            (by simpa only [code, cL, br, cB, Asm.bgeu, List.append_assoc] using hlink)
            (by rw [htw2, hbrSz]; rw [htw_all] at h64; omega) st2 (by rw [htw2, ← htw1]; exact hpc2) hcondT
        exact ⟨kp + (lkm.totalSize cL + kBr), st3,
          by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; exact hrun3,
          hpc3, (hpres1.trans (hpres2.trans (preservedFrameRegs_of_t6_s1 hoth3))).mono (fun _ h => False.elim h),
          by rw [hmem3, hmem2]; exact ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1⟩
    · simp only [hvi, hve] at hpairSim ⊢
      obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := hpairSim
      exact ⟨kp, st1, hrun1, hpc1, hpres1.mono (fun _ h => False.elim h),
        ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1⟩
  · simp only [hvi] at hpairSim ⊢
    obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := hpairSim
    exact ⟨kp, st1, hrun1, hpc1, hpres1.mono (fun _ h => False.elim h),
      ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1⟩

theorem reg_st64_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (a : ArrId) (i e : Expr) (pfx : String) (lblId : Nat) (brkLbl : Option String) (retLbl : String) (isTail : Bool)
    (pre post : List AsmItem)
    (haOk : env.tab.wordPosOkB (.t0 a) = true)
    (hiOk : exprOkB env.tab fl.nlocals i = true)
    (heOk : exprOkB env.tab fl.nlocals e = true)
    (hVfI : ExprVarsInFrame fl i) (hVfE : ExprVarsInFrame fl e)
    (hTmp : usedTempsStmt (.st64 a i e) ≤ fl.usedTemps)
    (hlink : lkm.linkSpec (pre ++ (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.st64 a i e)).1 ++ post) =
      .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    match _root_.L.step [] (fun _ => throw .outOfFuel) (.st64 a i e) ⟨lm, loc⟩ with
    | .ok (.normal, st') =>
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.st64 a i e)).1)) ∧
        PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) st r' ∧
        ProgMemRel env.tab L r'.mem st'.mem ∧
        ProgFrameOkR L fl sp r' st'.loc ∧
        ProgMemOutside (FnWriteMaskR L fl sp) st.mem r'.mem
    | .error _ =>
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) st r' ∧
        ProgMemOutside (FnWriteMaskR L fl sp) st.mem r'.mem
    | _ => True := by
  dsimp only [usedTempsStmt] at hTmp
  have hdef : (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.st64 a i e)).1 =
      (compileStorePairR env.tab fl i e).1 ++
      loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (env.tab.len64 (.t0 a)) ++
      [Asm.bgeu (compileStorePairR env.tab fl i e).2.1 AbiReg.t1 errLabel] ++
      loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (env.tab.base64 (.t0 a)) ++
      st64Tail (compileStorePairR env.tab fl i e).2.2 (compileStorePairR env.tab fl i e).2.1 AbiReg.t2 i := by
    simp [compileSR, List.append_assoc]
  rw [hdef] at hlink ⊢
  have hw := reg_st64_word_sim env L fl hfl lm loc hspAlign hlo hhi (.t0 a) i e pre post haOk hiOk heOk hVfI hVfE hTmp st hpc hgp ht5 hsp hmemRel hframeOk hlink
  rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
  · rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨ve, hve⟩ | hve
    · simp only [hvi, hve] at hw
      have hstepEq : _root_.L.step [] (fun _ => throw .outOfFuel) (.st64 a i e) ⟨lm, loc⟩ =
          if vi.toNat < (lm.arr64 (.t0 a)).size then .ok (.normal, ⟨lm.set64 (.t0 a) vi ve, loc⟩) else .error .oob := by
        simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvi, hve, _root_.L.st64, get, getThe,
          MonadStateOf.get, StateT.get, set, MonadStateOf.set, Pure.pure, StateT.pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
        by_cases hb : vi.toNat < (lm.arr64 (.t0 a)).size <;> simp only [hb, ↓reduceIte] <;> rfl
      rw [hstepEq]
      by_cases hb : vi.toNat < (lm.arr64 (.t0 a)).size <;> simp only [hb, ↓reduceIte] at hw ⊢ <;> exact hw
    · simp only [hvi, hve] at hw
      have hstepEq : _root_.L.step [] (fun _ => throw .outOfFuel) (.st64 a i e) ⟨lm, loc⟩ = .error .oob := by
        simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvi, hve]
      rw [hstepEq]; exact hw
  · simp only [hvi] at hw
    have hstepEq : _root_.L.step [] (fun _ => throw .outOfFuel) (.st64 a i e) ⟨lm, loc⟩ = .error .oob := by
      simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvi]
    rw [hstepEq]; exact hw

theorem reg_st64t_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (a : ArrId) (t i e : Expr) (pfx : String) (lblId : Nat) (brkLbl : Option String) (retLbl : String) (isTail : Bool)
    (pre post : List AsmItem)
    (haOk : env.tab.tieredOkB a = true)
    (htOk : exprOkB env.tab fl.nlocals t = true)
    (hiOk : exprOkB env.tab fl.nlocals i = true)
    (heOk : exprOkB env.tab fl.nlocals e = true)
    (hVfT : ExprVarsInFrame fl t) (hVfI : ExprVarsInFrame fl i) (hVfE : ExprVarsInFrame fl e)
    (hTmp : usedTempsStmt (.st64t a t i e) ≤ fl.usedTemps)
    (hlink : lkm.linkSpec (pre ++ (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.st64t a t i e)).1 ++ post) =
      .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    match _root_.L.step [] (fun _ => throw .outOfFuel) (.st64t a t i e) ⟨lm, loc⟩ with
    | .ok (.normal, st') =>
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.st64t a t i e)).1)) ∧
        PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) st r' ∧
        ProgMemRel env.tab L r'.mem st'.mem ∧
        ProgFrameOkR L fl sp r' st'.loc ∧
        ProgMemOutside (FnWriteMaskR L fl sp) st.mem r'.mem
    | .error _ =>
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) st r' ∧
        ProgMemOutside (FnWriteMaskR L fl sp) st.mem r'.mem
    | _ => True := by
  have hvalid : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  dsimp only [usedTempsStmt] at hTmp
  cases htC : t.constVal? with
  | some wt =>
    have hteq : t = .const wt := expr_constVal_eq_some htC
    have hvt : _root_.L.evalE t ⟨lm, loc⟩ = .ok (wt, ⟨lm, loc⟩) := by rw [hteq]; rfl
    have hst : isSimpleExpr t = true := isSimpleExpr_of_constVal htC
    simp only [hst, ↓reduceIte] at hTmp
    let sa := tierA a wt
    have hta := tieredOk_len64_addr_T L.T a wt haOk
    have hdef : (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.st64t a t i e)).1 =
        (compileStorePairR env.tab fl i e).1 ++
        loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (env.tab.len64 sa) ++
        [Asm.bgeu (compileStorePairR env.tab fl i e).2.1 AbiReg.t1 errLabel] ++
        loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (env.tab.base64 sa) ++
        st64Tail (compileStorePairR env.tab fl i e).2.2 (compileStorePairR env.tab fl i e).2.1 AbiReg.t2 i := by
      simp [compileSR, htC, sa, List.append_assoc]
    rw [hdef] at hlink ⊢
    have hw := reg_st64_word_sim env L fl hfl lm loc hspAlign hlo hhi sa i e pre post hta.1 hiOk heOk hVfI hVfE hTmp st hpc hgp ht5 hsp hmemRel hframeOk hlink
    rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
    · rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨ve, hve⟩ | hve
      · simp only [hvi, hve] at hw
        have hstepEq : _root_.L.step [] (fun _ => throw .outOfFuel) (.st64t a t i e) ⟨lm, loc⟩ =
            if vi.toNat < (lm.arr64 sa).size then .ok (.normal, ⟨lm.set64 sa vi ve, loc⟩) else .error .oob := by
          simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvt, hvi, hve, _root_.L.st64, get, getThe,
            MonadStateOf.get, StateT.get, set, MonadStateOf.set, Pure.pure, StateT.pure, Except.pure,
            throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
          by_cases hb : vi.toNat < (lm.arr64 sa).size <;> simp only [sa, hb, ↓reduceIte] <;> rfl
        rw [hstepEq]
        by_cases hb : vi.toNat < (lm.arr64 sa).size <;> simp only [hb, ↓reduceIte] at hw ⊢ <;> exact hw
      · simp only [hvi, hve] at hw
        have hstepEq : _root_.L.step [] (fun _ => throw .outOfFuel) (.st64t a t i e) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvt, hvi, hve]
        rw [hstepEq]; exact hw
    · simp only [hvi] at hw
      have hstepEq : _root_.L.step [] (fun _ => throw .outOfFuel) (.st64t a t i e) ⟨lm, loc⟩ = .error .oob := by
        simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvt, hvi]
      rw [hstepEq]; exact hw
  | none =>
    let cpRes := compileTierStoreTripleR env.tab fl t i e
    let cp := cpRes.1; let rt := cpRes.2.1; let ri := cpRes.2.2.1; let re := cpRes.2.2.2
    let chdr := [Asm.andi AbiReg.t0 rt 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0]
    let cL := loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t4 (env.tab.len64 (.t0 a))
    let br := [Asm.bgeu ri AbiReg.t2 errLabel]
    let cB := loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t4 (env.tab.base64 (.t0 a))
    let cS := st64Tail re ri AbiReg.t4 i
    have hdef : (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.st64t a t i e)).1 =
        cp ++ chdr ++ cL ++ br ++ cB ++ cS := by
      simp [compileSR, htC, cp, rt, ri, re, cpRes, chdr, cL, br, cB, cS, List.append_assoc]
    rw [hdef] at hlink ⊢
    have h64 := linkResolved_sub_pc64 env pre (cp ++ chdr ++ cL ++ br ++ cB ++ cS) post hlink
    have htw_hdr : lkm.totalSize chdr = 3 := by
      simp [chdr, Asm.andi, Asm.slli, Asm.add, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
    have htw_all : lkm.totalSize (cp ++ chdr ++ cL ++ br ++ cB ++ cS) =
        lkm.totalSize cp + 3 + lkm.totalSize cL + lkm.totalSize br + lkm.totalSize cB + lkm.totalSize cS := by
      simp only [lkm.totalSize_append, htw_hdr]
    have htr := reg_compileTierStoreTripleR_sim env L fl hfl lm loc hspAlign hlo hhi t i e pre
      ((chdr ++ cL ++ br ++ cB ++ cS) ++ post) htOk hiOk heOk hVfT hVfI hVfE hTmp
      (by simpa only [cp, cpRes, List.append_assoc] using hlink) st hpc hgp ht5 hsp hmemRel hframeOk
    rcases htr with ⟨hrtW, hriW, hreW, htrSim⟩
    rcases _root_.L.evalE_pure t ⟨lm, loc⟩ with ⟨vt, hvt⟩ | hvt
    · rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
      · rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨ve, hve⟩ | hve
        · simp only [hvt, hvi, hve] at htrSim
          obtain ⟨kp, st1, hrun1, hpc1, hrt1, hri1, hre1, hpres1, heq1⟩ := htrSim
          have htw1 : lkm.totalSize (pre ++ cp) = lkm.totalSize pre + lkm.totalSize cp := lkm.totalSize_append pre cp
          have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.abi.gp.trans hgp
          have hm1 := ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) heq1 hmemRel
          have hf1 := ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) (hpres1.mono (fun _ h => False.elim h)) heq1 hframeOk
          have hta := tieredOk_len64_addr_T L.T a vt haOk
          rcases hm1.2.1 (tierA a vt) hta.1 with ⟨hcap64, hlt61, hlenR, hbaseR, _⟩
          have hlt64 : (lm.arr64 (tierA a vt)).size < 2 ^ 64 := by omega
          obtain ⟨st2, hrun2, hpc2, ht1_2, hmem2, hpres2, hoth2⟩ :=
            step_tierHdr_r env fl (pre ++ cp) ((cL ++ br ++ cB ++ cS) ++ post) rt vt
              (by simpa only [chdr, List.append_assoc] using hlink)
              (by rw [htw1]; rw [htw_all] at h64; omega) st1 (by rw [htw1]; exact hpc1) hgp1 hrt1
          have htw2 : lkm.totalSize (pre ++ cp ++ chdr) = lkm.totalSize pre + lkm.totalSize cp + 3 := by
            rw [lkm.totalSize_append, htw1, htw_hdr]
          have hri2 : st2.getReg ri = vi.toBitVec :=
            (hoth2 ri (tierValReg_ne_scratch hriW (by decide)) (tierValReg_ne_scratch hriW (by decide))).trans hri1
          have hre2 : st2.getReg re = ve.toBitVec :=
            (hoth2 re (tierValReg_ne_scratch hreW (by decide)) (tierValReg_ne_scratch hreW (by decide))).trans hre1
          have halL : isAligned (st2.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.len64 (.t0 a))) 8 = true := by
            rw [ht1_2, hta.2.1, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
          obtain ⟨st3, hrun3, hoth3, ht2_3, hmem3, hpc3⟩ :=
            loadMemOff_ld_correct_lm lkm env.hrom (pre ++ cp ++ chdr) ((br ++ cB ++ cS) ++ post)
              AbiReg.t2 AbiReg.t1 AbiReg.t4 (by decide) (by decide) (by decide) (env.tab.len64 (.t0 a))
              (by simpa only [cL, List.append_assoc] using hlink)
              (by rw [htw2]; rw [htw_all] at h64; dsimp only [cL] at h64 ⊢; omega) st2 (by rw [htw2, ← htw1]; exact hpc2) halL
          have hpres3 : PreservedFrameRegs fl (fun _ => False) st2 st3 :=
            PreservedFrameRegs.of_scratch2 AbiReg.t2 AbiReg.t4 (by decide) (by decide) hoth3
          have htw3 : lkm.totalSize (pre ++ cp ++ chdr ++ cL) = lkm.totalSize pre + lkm.totalSize cp + 3 + lkm.totalSize cL := by
            rw [lkm.totalSize_append, htw2]
          have hri3 : st3.getReg ri = vi.toBitVec :=
            (hoth3 ri (tierValReg_ne_scratch hriW (by decide)) (tierValReg_ne_scratch hriW (by decide))).trans hri2
          have hre3 : st3.getReg re = ve.toBitVec :=
            (hoth3 re (tierValReg_ne_scratch hreW (by decide)) (tierValReg_ne_scratch hreW (by decide))).trans hre2
          have ht2Val : st3.getReg AbiReg.t2 = BitVec.ofNat 64 (lm.arr64 (tierA a vt)).size := by
            rw [ht2_3, hmem2, ht1_2, hta.2.1, hlenR]
          have hstepEq : _root_.L.step [] (fun _ => throw .outOfFuel) (.st64t a t i e) ⟨lm, loc⟩ =
              if vi.toNat < (lm.arr64 (tierA a vt)).size then .ok (.normal, ⟨lm.set64 (tierA a vt) vi ve, loc⟩) else .error .oob := by
            simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvt, hvi, hve, _root_.L.st64, get, getThe,
              MonadStateOf.get, StateT.get, set, MonadStateOf.set, Pure.pure, StateT.pure, Except.pure,
              throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
            by_cases hb : vi.toNat < (lm.arr64 (tierA a vt)).size <;> simp only [hb, ↓reduceIte] <;> rfl
          rw [hstepEq]
          have hbrSz : lkm.itemSize (.br .bgeu ri AbiReg.t2 errLabel) = lkm.totalSize br := by simp [br, Asm.bgeu, lkm.totalSize_singleton]
          by_cases hb : vi.toNat < (lm.arr64 (tierA a vt)).size
          · simp only [hb, ↓reduceIte]
            have hcondF : evalBranch .bgeu (st3.getReg ri) (st3.getReg AbiReg.t2) = false := by
              rw [hri3, ht2Val, u64_toBitVec_eq_ofNat, evalBranch_bgeu_nat (by simpa using vi.toBitVec.isLt) hlt64]
              simp [show ¬((lm.arr64 (tierA a vt)).size ≤ vi.toNat) by omega]
            obtain ⟨kBr, st4, hrun4, hpc4, hoth4, _, hmem4⟩ :=
              prog_step_br_fall env (pre ++ cp ++ chdr ++ cL) ((cB ++ cS) ++ post)
                .bgeu ri AbiReg.t2 errLabel env.errTarget env.herrLbl
                ⟨tierValReg_ne_scratch hriW (by decide), by decide⟩
                (by simpa only [br, Asm.bgeu, List.append_assoc] using hlink)
                (by rw [htw3, hbrSz]; rw [htw_all] at h64; omega) st3 (by rw [htw3, ← htw2]; exact hpc3) hcondF
            have hpres4 : PreservedFrameRegs fl (fun _ => False) st3 st4 :=
              preservedFrameRegs_of_t6_s1 hoth4
            have htw4 : lkm.totalSize (pre ++ cp ++ chdr ++ cL ++ br) =
                lkm.totalSize pre + lkm.totalSize cp + 3 + lkm.totalSize cL + lkm.totalSize br := by
              rw [lkm.totalSize_append, htw3]
            have ht1_4 : st4.getReg AbiReg.t1 = L.T + (if (vt &&& 1 == 0) = true then 0#64 else 8#64) :=
              (hoth4 AbiReg.t1 (by decide)).trans ((hoth3 AbiReg.t1 (by decide) (by decide)).trans ht1_2)
            have halB : isAligned (st4.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.base64 (.t0 a))) 8 = true := by
              rw [ht1_4, hta.2.2, Tab.base64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
            obtain ⟨st5, hrun5, hoth5, ht1_5, hmem5, hpc5⟩ :=
              loadMemOff_ld_correct_lm lkm env.hrom (pre ++ cp ++ chdr ++ cL ++ br) (cS ++ post)
                AbiReg.t1 AbiReg.t1 AbiReg.t4 (by decide) (by decide) (by decide) (env.tab.base64 (.t0 a))
                (by simpa only [cB, List.append_assoc] using hlink)
                (by rw [htw4]; rw [htw_all] at h64; dsimp only [cB] at h64 ⊢; omega) st4 (by rw [htw4, ← htw3, ← hbrSz]; exact hpc4) halB
            have hpres5 : PreservedFrameRegs fl (fun _ => False) st4 st5 :=
              PreservedFrameRegs.of_scratch2 AbiReg.t1 AbiReg.t4 (by decide) (by decide) hoth5
            have htw5 : lkm.totalSize (pre ++ cp ++ chdr ++ cL ++ br ++ cB) =
                lkm.totalSize pre + lkm.totalSize cp + 3 + lkm.totalSize cL + lkm.totalSize br + lkm.totalSize cB := by
              rw [lkm.totalSize_append, htw4]
            have ht1Val5 : st5.getReg AbiReg.t1 = L.base64 (tierA a vt) := by
              rw [ht1_5, hmem4, hmem3, hmem2, ht1_4, hta.2.2, hbaseR]
            have hri5 : st5.getReg ri = vi.toBitVec :=
              (hoth5 ri (tierValReg_ne_scratch hriW (by decide)) (tierValReg_ne_scratch hriW (by decide))).trans
                ((hoth4 ri ⟨tierValReg_ne_scratch hriW (by decide), tierValReg_ne_scratch hriW (by decide)⟩).trans hri3)
            have hre5 : st5.getReg re = ve.toBitVec :=
              (hoth5 re (tierValReg_ne_scratch hreW (by decide)) (tierValReg_ne_scratch hreW (by decide))).trans
                ((hoth4 re ⟨tierValReg_ne_scratch hreW (by decide), tierValReg_ne_scratch hreW (by decide)⟩).trans hre3)
            have hm5 : st5.mem = st1.mem := by rw [hmem5, hmem4, hmem3, hmem2]
            obtain ⟨kT, stEnd, hrunT, hpcT, hpresT, hmemT⟩ :=
              reg_st64Tail_sim env L fl lm loc (tierA a vt) re ri AbiReg.t4 i vi ve
                (by decide) (by decide) (by decide)
                (tierValReg_ne_scratch hreW (by decide)) (tierValReg_ne_scratch hreW (by decide))
                hvi (pre ++ cp ++ chdr ++ cL ++ br ++ cB) post
                (by simpa only [cS, List.append_assoc] using hlink)
                (by rw [htw5]; rw [htw_all] at h64; dsimp only [cS] at h64 ⊢; omega)
                st5 (by rw [htw5, ← htw4]; exact hpc5) ht1Val5 hri5 hre5
            have hmemEnd : stEnd.mem = writeWord64 st1.mem (L.base64 (tierA a vt) + BitVec.ofNat 64 (8 * vi.toNat)) ve.toBitVec := by
              rw [hmemT, hm5]
            have hpres1E : PreservedFrameRegs fl (fun _ => False) st1 stEnd :=
              (PreservedFrameRegs.of_a0 hpres2).trans (hpres3.trans (hpres4.trans (hpres5.trans hpresT)))
            have heq1E : MemEqOutside (L.arr64Span (tierA a vt)) st1.mem stEnd.mem := by
              rw [hmemEnd]; apply MemEqOutside.writeWord64
              intro k hk; exact MemSpan.sub_range (s := L.arr64Span (tierA a vt)) (8 * vi.toNat) 8
                (by dsimp only [ProgLayout.arr64Span]; omega) k hk
            have h64Disj : MemDisjoint (L.arr64Span (tierA a vt)) L.stackSpan :=
              MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid (tierA a vt)) L.stackSpan_valid (L.h64DisjStack (tierA a vt) hta.1)
            exact ⟨kp + (3 + (lkm.totalSize cL + (kBr + (lkm.totalSize cB + kT)))), stEnd,
              by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; rw [run_add, hrun3]; dsimp only
                 rw [run_add, hrun4]; dsimp only; rw [run_add, hrun5]; dsimp only; exact hrunT,
              by rw [hpcT, htw5, htw_all]; dsimp only [cS]; congr 2; omega,
              (hpres1.trans hpres1E).mono (fun _ h => False.elim h),
              by rw [hmemEnd]; exact ProgMemRel.set64 hm1 (tierA a vt) hta.1 vi ve hb,
              ProgFrameOkR.of_mem_outside_stack hfl hlo hhi (L.arr64Span (tierA a vt)) h64Disj hpres1E heq1E hf1,
              (ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1).trans
                (ProgMemOutside.of_memEqOutside (fun _ ha => Or.inr (Or.inr (Or.inr ⟨tierA a vt, hta.1, ha⟩))) heq1E)⟩
          · simp only [hb, ↓reduceIte]
            have hcondT : evalBranch .bgeu (st3.getReg ri) (st3.getReg AbiReg.t2) = true := by
              rw [hri3, ht2Val, u64_toBitVec_eq_ofNat, evalBranch_bgeu_nat (by simpa using vi.toBitVec.isLt) hlt64]
              simp [show (lm.arr64 (tierA a vt)).size ≤ vi.toNat by omega]
            obtain ⟨kBr, st4, hrun4, hpc4, hoth4, _, hmem4⟩ :=
              prog_step_br_taken env (pre ++ cp ++ chdr ++ cL) ((cB ++ cS) ++ post)
                .bgeu ri AbiReg.t2 errLabel env.errTarget env.herrLbl
                ⟨tierValReg_ne_scratch hriW (by decide), by decide⟩
                (by simpa only [br, Asm.bgeu, List.append_assoc] using hlink)
                (by rw [htw3, hbrSz]; rw [htw_all] at h64; omega) st3 (by rw [htw3, ← htw2]; exact hpc3) hcondT
            exact ⟨kp + (3 + (lkm.totalSize cL + kBr)), st4,
              by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; rw [run_add, hrun3]; dsimp only; exact hrun4,
              hpc4, (hpres1.trans ((PreservedFrameRegs.of_a0 hpres2).trans
                (hpres3.trans (preservedFrameRegs_of_t6_s1 hoth4)))).mono (fun _ h => False.elim h),
              by rw [hmem4, hmem3, hmem2]; exact ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1⟩
        · simp only [hvt, hvi, hve] at htrSim
          obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := htrSim
          have hstepEq : _root_.L.step [] (fun _ => throw .outOfFuel) (.st64t a t i e) ⟨lm, loc⟩ = .error .oob := by
            simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvt, hvi, hve]
          rw [hstepEq]
          exact ⟨kp, st1, hrun1, hpc1, hpres1.mono (fun _ h => False.elim h),
            ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1⟩
      · simp only [hvt, hvi] at htrSim
        obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := htrSim
        have hstepEq : _root_.L.step [] (fun _ => throw .outOfFuel) (.st64t a t i e) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvt, hvi]
        rw [hstepEq]
        exact ⟨kp, st1, hrun1, hpc1, hpres1.mono (fun _ h => False.elim h),
          ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1⟩
    · simp only [hvt] at htrSim
      obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := htrSim
      have hstepEq : _root_.L.step [] (fun _ => throw .outOfFuel) (.st64t a t i e) ⟨lm, loc⟩ = .error .oob := by
        simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvt]
      rw [hstepEq]
      exact ⟨kp, st1, hrun1, hpc1, hpres1.mono (fun _ h => False.elim h),
        ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1⟩

theorem reg_st32t_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (L : ProgLayout env.tab) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (lm : _root_.L.Mem) (loc : _root_.L.Locals) {sp : BitVec 64}
    (hspAlign : isAligned sp 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (a : ArrId) (t i e : Expr) (pfx : String) (lblId : Nat) (brkLbl : Option String) (retLbl : String) (isTail : Bool)
    (pre post : List AsmItem)
    (haOk : tier32OkB env.tab a t = true)
    (htOk : exprOkB env.tab fl.nlocals t = true)
    (hiOk : exprOkB env.tab fl.nlocals i = true)
    (heOk : exprOkB env.tab fl.nlocals e = true)
    (hVfT : ExprVarsInFrame fl t) (hVfI : ExprVarsInFrame fl i) (hVfE : ExprVarsInFrame fl e)
    (hTmp : usedTempsStmt (.st32t a t i e) ≤ fl.usedTemps)
    (hlink : lkm.linkSpec (pre ++ (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.st32t a t i e)).1 ++ post) =
      .ok (env.code, env.labels))
    (st : State) (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre))
    (hgp : st.getReg AbiReg.gp = L.T) (ht5 : T5GpOk L fl st) (hsp : st.getReg AbiReg.sp = sp)
    (hmemRel : ProgMemRel env.tab L st.mem lm) (hframeOk : ProgFrameOkR L fl sp st loc) :
    match _root_.L.step [] (fun _ => throw .outOfFuel) (.st32t a t i e) ⟨lm, loc⟩ with
    | .ok (.normal, st') =>
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.st32t a t i e)).1)) ∧
        PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) st r' ∧
        ProgMemRel env.tab L r'.mem st'.mem ∧
        ProgFrameOkR L fl sp r' st'.loc ∧
        ProgMemOutside (FnWriteMaskR L fl sp) st.mem r'.mem
    | .error _ =>
      ∃ k r', RV64.run env.rom k st = .cont r' ∧
        r'.pc = BitVec.ofNat 64 (4 * env.errTarget) ∧
        PreservedFrameRegs fl (· ∈ fl.alloc.map Prod.snd) st r' ∧
        ProgMemOutside (FnWriteMaskR L fl sp) st.mem r'.mem
    | _ => True := by
  have hvalid : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  dsimp only [usedTempsStmt] at hTmp
  cases htC : t.constVal? with
  | some wt =>
    have hteq : t = .const wt := expr_constVal_eq_some htC
    have hvt : _root_.L.evalE t ⟨lm, loc⟩ = .ok (wt, ⟨lm, loc⟩) := by rw [hteq]; rfl
    have hst : isSimpleExpr t = true := isSimpleExpr_of_constVal htC
    simp only [hst, ↓reduceIte] at hTmp
    let sa := tierA a wt
    have hta := tierAddrOk_len64_addr_T L.T a wt (tier32Ok_to_tierAddrOk haOk hvt)
    let cpRes := compileStorePairR env.tab fl i e
    let cp := cpRes.1; let ri := cpRes.2.1; let re := cpRes.2.2
    let cL := loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (env.tab.len64 sa)
    let sr1 := [Asm.srli AbiReg.t2 ri 1#6]
    let br := [Asm.bgeu AbiReg.t2 AbiReg.t1 errLabel]
    let cB := loadMemOffGp fl.useT5Gp .ld AbiReg.t1 AbiReg.t2 (env.tab.base64 sa)
    let cS := st32tTail re ri AbiReg.t2 i
    have hdef : (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.st32t a t i e)).1 =
        cp ++ cL ++ sr1 ++ br ++ cB ++ cS := by
      simp [compileSR, htC, sa, cp, ri, re, cpRes, cL, sr1, br, cB, cS, List.append_assoc]
    rw [hdef] at hlink ⊢
    have h64 := linkResolved_sub_pc64 env pre (cp ++ cL ++ sr1 ++ br ++ cB ++ cS) post hlink
    have htw_sr1 : lkm.totalSize sr1 = 1 := by simp [sr1, Asm.srli, lkm.totalSize_instr]
    have htw_all : lkm.totalSize (cp ++ cL ++ sr1 ++ br ++ cB ++ cS) =
        lkm.totalSize cp + lkm.totalSize cL + 1 + lkm.totalSize br + lkm.totalSize cB + lkm.totalSize cS := by
      simp only [lkm.totalSize_append, htw_sr1]
    have hpair := reg_compileStorePairR_sim env L fl hfl lm loc hspAlign hlo hhi i e pre
      ((cL ++ sr1 ++ br ++ cB ++ cS) ++ post) hiOk heOk hVfI hVfE hTmp
      (by simpa only [cp, cpRes, List.append_assoc] using hlink) st hpc hgp ht5 hsp hmemRel hframeOk
    rcases hpair with ⟨hriW, hreW, hpairSim⟩
    have hriW' : ri = AbiReg.zero ∨ ri = AbiReg.a0 ∨ ri = AbiReg.t0 ∨ ri = AbiReg.t3 ∨ ri ∈ allowedRegs true := by
      rcases hriW with h | h | h | h; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    have hreW' : re = AbiReg.zero ∨ re = AbiReg.a0 ∨ re = AbiReg.t0 ∨ re = AbiReg.t3 ∨ re ∈ allowedRegs true := by
      rcases hreW with h | h | h | h; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
    · rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨ve, hve⟩ | hve
      · simp only [hvi, hve] at hpairSim
        obtain ⟨kp, st1, hrun1, hpc1, hri1, hre1, hpres1, heq1⟩ := hpairSim
        have htw1 : lkm.totalSize (pre ++ cp) = lkm.totalSize pre + lkm.totalSize cp := lkm.totalSize_append pre cp
        have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.abi.gp.trans hgp
        have hm1 := ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) heq1 hmemRel
        have hf1 := ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) (hpres1.mono (fun _ h => False.elim h)) heq1 hframeOk
        rcases hm1.2.1 sa hta.1 with ⟨hcap64, hlt61, hlenR, hbaseR, _⟩
        have hlt64 : (lm.arr64 sa).size < 2 ^ 64 := by omega
        have halL : isAligned (L.T + BitVec.ofInt 64 (env.tab.len64 sa)) 8 = true := by
          rw [Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
        obtain ⟨st2, hrun2, hoth2, ht1_2, hmem2, hpc2⟩ :=
          loadMemOffGp_ld_correct_lm lkm env.hrom (pre ++ cp) ((sr1 ++ br ++ cB ++ cS) ++ post) fl.useT5Gp
            AbiReg.t1 AbiReg.t2 (by decide) (by decide) (by decide) (fun _ => by decide) (env.tab.len64 sa) L.T
            (by simpa only [cL, List.append_assoc] using hlink)
            (by rw [htw1]; rw [htw_all] at h64; dsimp only [cL] at h64 ⊢; omega) st1 (by rw [htw1]; exact hpc1)
            hgp1 (ht5.of_preserved hpres1) halL
        have hpres2 : PreservedFrameRegs fl (fun _ => False) st1 st2 :=
          PreservedFrameRegs.of_scratch2 AbiReg.t1 AbiReg.t2 (by decide) (by decide) hoth2
        have htw2 : lkm.totalSize (pre ++ cp ++ cL) = lkm.totalSize pre + lkm.totalSize cp + lkm.totalSize cL := by
          rw [lkm.totalSize_append, htw1]
        have hri2 : st2.getReg ri = vi.toBitVec :=
          (hoth2 ri (storeReg_ne_scratch hriW' (by decide)) (storeReg_ne_scratch hriW' (by decide))).trans hri1
        have hre2 : st2.getReg re = ve.toBitVec :=
          (hoth2 re (storeReg_ne_scratch hreW' (by decide)) (storeReg_ne_scratch hreW' (by decide))).trans hre1
        have ht1Val : st2.getReg AbiReg.t1 = BitVec.ofNat 64 (lm.arr64 sa).size := by rw [ht1_2, hlenR]
        have hsSrli := step_item_instr_lm lkm env.hrom (pre ++ cp ++ cL) ((br ++ cB ++ cS) ++ post)
          (.shImm .srli AbiReg.t2 ri 1#6)
          (by simpa only [sr1, Asm.srli, List.append_assoc] using hlink)
          (by rw [htw2]; rw [htw_all] at h64; omega) st2 (by rw [htw2, ← htw1]; exact hpc2)
        let st2b := stepReg st2 AbiReg.t2 (evalShiftImm .srli (st2.getReg ri) 1#6) (st2.pc + 4#64)
        have hrun2b : RV64.run env.rom 1 st2 = .cont st2b := run_one_cont _ _ st2b (by rw [hsSrli]; rfl)
        have hpres2b : PreservedFrameRegs fl (fun _ => False) st2 st2b :=
          PreservedFrameRegs.of_scratch1 AbiReg.t2 (by decide) (fun r hr => getReg_stepReg_ne st2 AbiReg.t2 r hr _ _)
        have htw2b : lkm.totalSize (pre ++ cp ++ cL ++ sr1) = lkm.totalSize pre + lkm.totalSize cp + lkm.totalSize cL + 1 := by
          rw [lkm.totalSize_append, htw2, htw_sr1]
        have hpc2b : st2b.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ cp ++ cL ++ sr1)) := by
          change st2.pc + 4#64 = _; rw [pc_add_4_ofNat st2.pc hpc2, htw2b, htw1]
        have ht2_2b : st2b.getReg AbiReg.t2 = BitVec.ofNat 64 (vi.toNat / 2) := by
          change (stepReg st2 AbiReg.t2 _ _).getReg AbiReg.t2 = _
          rw [getReg_stepReg_eq _ _ (by decide), hri2]
          apply BitVec.eq_of_toNat_eq
          simp only [evalShiftImm, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
            show (1#6 : BitVec 6).toNat = 1 from rfl, Nat.shiftRight_eq_div_pow, Nat.pow_one]
          have hlt := vi.toBitVec.isLt; rw [UInt64.toNat_toBitVec] at hlt
          rw [Nat.mod_eq_of_lt (by omega)]
        have ht1_2b : st2b.getReg AbiReg.t1 = BitVec.ofNat 64 (lm.arr64 sa).size :=
          (getReg_stepReg_ne st2 AbiReg.t2 AbiReg.t1 (by decide) _ _).trans ht1Val
        have hstepEq : _root_.L.step [] (fun _ => throw .outOfFuel) (.st32t a t i e) ⟨lm, loc⟩ =
            if (vi / 2).toNat < (lm.arr64 sa).size then .ok (.normal, ⟨lm.set32 sa vi ve, loc⟩) else .error .oob := by
          simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvt, hvi, hve, _root_.L.st32, get, getThe,
            MonadStateOf.get, StateT.get, set, MonadStateOf.set, Pure.pure, StateT.pure, Except.pure,
            throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
          by_cases hb : (vi / 2).toNat < (lm.arr64 sa).size <;> simp only [sa, hb, ↓reduceIte] <;> rfl
        rw [hstepEq]
        have hbrSz : lkm.itemSize (.br .bgeu AbiReg.t2 AbiReg.t1 errLabel) = lkm.totalSize br := by simp [br, Asm.bgeu, lkm.totalSize_singleton]
        have hdiv2 : (vi / 2).toNat = vi.toNat / 2 := rfl
        have hdivLt64 : vi.toNat / 2 < 2 ^ 64 := by have := vi.toBitVec.isLt; rw [UInt64.toNat_toBitVec] at this; omega
        by_cases hb : (vi / 2).toNat < (lm.arr64 sa).size
        · simp only [hb, ↓reduceIte]
          have hcondF : evalBranch .bgeu (st2b.getReg AbiReg.t2) (st2b.getReg AbiReg.t1) = false := by
            rw [ht2_2b, ht1_2b, evalBranch_bgeu_nat hdivLt64 hlt64]
            simp [show ¬((lm.arr64 sa).size ≤ vi.toNat / 2) by omega]
          obtain ⟨kBr, st3, hrun3, hpc3, hoth3, _, hmem3⟩ :=
            prog_step_br_fall env (pre ++ cp ++ cL ++ sr1) ((cB ++ cS) ++ post)
              .bgeu AbiReg.t2 AbiReg.t1 errLabel env.errTarget env.herrLbl (by decide)
              (by simpa only [br, Asm.bgeu, List.append_assoc] using hlink)
              (by rw [htw2b, hbrSz]; rw [htw_all] at h64; omega) st2b hpc2b hcondF
          have hpres3 : PreservedFrameRegs fl (fun _ => False) st2b st3 :=
            preservedFrameRegs_of_t6_s1 hoth3
          have htw3 : lkm.totalSize (pre ++ cp ++ cL ++ sr1 ++ br) =
              lkm.totalSize pre + lkm.totalSize cp + lkm.totalSize cL + 1 + lkm.totalSize br := by
            rw [lkm.totalSize_append, htw2b]
          have hgp3 : st3.getReg AbiReg.gp = L.T :=
            (hoth3 AbiReg.gp (by decide)).trans
              ((getReg_stepReg_ne st2 AbiReg.t2 AbiReg.gp (by decide) _ _).trans
                ((hoth2 AbiReg.gp (by decide) (by decide)).trans hgp1))
          have halB : isAligned (L.T + BitVec.ofInt 64 (env.tab.base64 sa)) 8 = true := by
            rw [Tab.base64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
          obtain ⟨st4, hrun4, hoth4, ht1_4, hmem4, hpc4⟩ :=
            loadMemOffGp_ld_correct_lm lkm env.hrom (pre ++ cp ++ cL ++ sr1 ++ br) (cS ++ post) fl.useT5Gp
              AbiReg.t1 AbiReg.t2 (by decide) (by decide) (by decide) (fun _ => by decide) (env.tab.base64 sa) L.T
              (by simpa only [cB, List.append_assoc] using hlink)
              (by rw [htw3]; rw [htw_all] at h64; dsimp only [cB] at h64 ⊢; omega) st3 (by rw [htw3, ← htw2b, ← hbrSz]; exact hpc3)
              hgp3 (ht5.of_preserved (hpres1.trans (hpres2.trans (hpres2b.trans hpres3)))) halB
          have hpres4 : PreservedFrameRegs fl (fun _ => False) st3 st4 :=
            PreservedFrameRegs.of_scratch2 AbiReg.t1 AbiReg.t2 (by decide) (by decide) hoth4
          have htw4 : lkm.totalSize (pre ++ cp ++ cL ++ sr1 ++ br ++ cB) =
              lkm.totalSize pre + lkm.totalSize cp + lkm.totalSize cL + 1 + lkm.totalSize br + lkm.totalSize cB := by
            rw [lkm.totalSize_append, htw3]
          have ht1Val4 : st4.getReg AbiReg.t1 = L.base64 sa := by
            rw [ht1_4, hmem3, mem_stepReg, hmem2, hbaseR]
          have hri4 : st4.getReg ri = vi.toBitVec :=
            (hoth4 ri (storeReg_ne_scratch hriW' (by decide)) (storeReg_ne_scratch hriW' (by decide))).trans
              ((hoth3 ri ⟨storeReg_ne_scratch hriW' (by decide), storeReg_ne_scratch hriW' (by decide)⟩).trans
                ((getReg_stepReg_ne st2 AbiReg.t2 ri (storeReg_ne_scratch hriW' (by decide)) _ _).trans hri2))
          have hre4 : st4.getReg re = ve.toBitVec :=
            (hoth4 re (storeReg_ne_scratch hreW' (by decide)) (storeReg_ne_scratch hreW' (by decide))).trans
              ((hoth3 re ⟨storeReg_ne_scratch hreW' (by decide), storeReg_ne_scratch hreW' (by decide)⟩).trans
                ((getReg_stepReg_ne st2 AbiReg.t2 re (storeReg_ne_scratch hreW' (by decide)) _ _).trans hre2))
          have hm4 : st4.mem = st1.mem := by dsimp only [st2b] at hmem3; rw [hmem4, hmem3, mem_stepReg, hmem2]
          have h64Disj : MemDisjoint (L.arr64Span sa) L.stackSpan :=
            MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid sa) L.stackSpan_valid (L.h64DisjStack sa hta.1)
          obtain ⟨kT, stEnd, hrunT, hpcT, hpresT, hmemT⟩ :=
            reg_st32tTail_sim env L fl lm loc sa re ri AbiReg.t2 i vi ve
              (by decide) (by decide) (by decide)
              (storeReg_ne_scratch hreW' (by decide)) (storeReg_ne_scratch hreW' (by decide))
              hvi (pre ++ cp ++ cL ++ sr1 ++ br ++ cB) post
              (by simpa only [cS, List.append_assoc] using hlink)
              (by rw [htw4]; rw [htw_all] at h64; dsimp only [cS] at h64 ⊢; omega)
              st4 (by rw [htw4, ← htw3]; exact hpc4) ht1Val4 hri4 hre4
          have hmemEnd : stEnd.mem = RV64.storeBytes st1.mem (L.base64 sa + BitVec.ofNat 64 (4 * vi.toNat)) 4 (ve.toBitVec.extractLsb' 0 32) := by
            rw [hmemT, hm4]
          have hpres1E : PreservedFrameRegs fl (fun _ => False) st1 stEnd :=
            hpres2.trans (hpres2b.trans (hpres3.trans (hpres4.trans hpresT)))
          have heq1E : MemEqOutside (L.arr64Span sa) st1.mem stEnd.mem := by
            rw [hmemEnd]; apply MemEqOutside.storeBytes
            intro k hk; exact MemSpan.sub_range (s := L.arr64Span sa) (4 * vi.toNat) 4
              (by dsimp only [ProgLayout.arr64Span]; omega) k hk
          exact ⟨kp + (lkm.totalSize cL + (1 + (kBr + (lkm.totalSize cB + kT)))), stEnd,
            by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; rw [run_add, hrun2b]; dsimp only
               rw [run_add, hrun3]; dsimp only; rw [run_add, hrun4]; dsimp only; exact hrunT,
            by rw [hpcT, htw4, htw_all]; dsimp only [cS]; congr 2; omega,
            (hpres1.trans hpres1E).mono (fun _ h => False.elim h),
            by rw [hmemEnd]; exact ProgMemRel.set32 hm1 sa hta.1 vi ve hb,
            ProgFrameOkR.of_mem_outside_stack hfl hlo hhi (L.arr64Span sa) h64Disj hpres1E heq1E hf1,
            (ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1).trans
              (ProgMemOutside.of_memEqOutside (fun _ ha => Or.inr (Or.inr (Or.inr ⟨sa, hta.1, ha⟩))) heq1E)⟩
        · simp only [hb, ↓reduceIte]
          have hcondT : evalBranch .bgeu (st2b.getReg AbiReg.t2) (st2b.getReg AbiReg.t1) = true := by
            rw [ht2_2b, ht1_2b, evalBranch_bgeu_nat hdivLt64 hlt64]
            simp [show (lm.arr64 sa).size ≤ vi.toNat / 2 by omega]
          obtain ⟨kBr, st3, hrun3, hpc3, hoth3, _, hmem3⟩ :=
            prog_step_br_taken env (pre ++ cp ++ cL ++ sr1) ((cB ++ cS) ++ post)
              .bgeu AbiReg.t2 AbiReg.t1 errLabel env.errTarget env.herrLbl (by decide)
              (by simpa only [br, Asm.bgeu, List.append_assoc] using hlink)
              (by rw [htw2b, hbrSz]; rw [htw_all] at h64; omega) st2b hpc2b hcondT
          exact ⟨kp + (lkm.totalSize cL + (1 + kBr)), st3,
            by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; rw [run_add, hrun2b]; dsimp only; exact hrun3,
            hpc3, (hpres1.trans (hpres2.trans (hpres2b.trans (preservedFrameRegs_of_t6_s1 hoth3)))).mono (fun _ h => False.elim h),
            by rw [hmem3, mem_stepReg, hmem2]; exact ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1⟩
      · simp only [hvi, hve] at hpairSim
        obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := hpairSim
        have hstepEq : _root_.L.step [] (fun _ => throw .outOfFuel) (.st32t a t i e) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvt, hvi, hve]
        rw [hstepEq]
        exact ⟨kp, st1, hrun1, hpc1, hpres1.mono (fun _ h => False.elim h),
          ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1⟩
    · simp only [hvi] at hpairSim
      obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := hpairSim
      have hstepEq : _root_.L.step [] (fun _ => throw .outOfFuel) (.st32t a t i e) ⟨lm, loc⟩ = .error .oob := by
        simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvt, hvi]
      rw [hstepEq]
      exact ⟨kp, st1, hrun1, hpc1, hpres1.mono (fun _ h => False.elim h),
        ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1⟩
  | none =>
    let cpRes := compileTierStoreTripleR env.tab fl t i e
    let cp := cpRes.1; let rt := cpRes.2.1; let ri := cpRes.2.2.1; let re := cpRes.2.2.2
    let chdr := [Asm.andi AbiReg.t0 rt 1#12, Asm.slli AbiReg.t0 AbiReg.t0 3#6, Asm.add AbiReg.t1 AbiReg.gp AbiReg.t0]
    let cL := loadMemOff .ld AbiReg.t2 AbiReg.t1 AbiReg.t4 (env.tab.len64 (.t0 a))
    let sr1 := [Asm.srli AbiReg.t4 ri 1#6]
    let br := [Asm.bgeu AbiReg.t4 AbiReg.t2 errLabel]
    let cB := loadMemOff .ld AbiReg.t1 AbiReg.t1 AbiReg.t4 (env.tab.base64 (.t0 a))
    let cS := st32tTail re ri AbiReg.t4 i
    have hdef : (compileSR env.tab fl pfx lblId brkLbl retLbl isTail (.st32t a t i e)).1 =
        cp ++ chdr ++ cL ++ sr1 ++ br ++ cB ++ cS := by
      simp [compileSR, htC, cp, rt, ri, re, cpRes, chdr, cL, sr1, br, cB, cS, List.append_assoc]
    rw [hdef] at hlink ⊢
    have h64 := linkResolved_sub_pc64 env pre (cp ++ chdr ++ cL ++ sr1 ++ br ++ cB ++ cS) post hlink
    have htw_hdr : lkm.totalSize chdr = 3 := by
      simp [chdr, Asm.andi, Asm.slli, Asm.add, lkm.totalSize_cons, lkm.totalSize_nil, lkm.itemSize_instr]
    have htw_sr1 : lkm.totalSize sr1 = 1 := by simp [sr1, Asm.srli, lkm.totalSize_instr]
    have htw_all : lkm.totalSize (cp ++ chdr ++ cL ++ sr1 ++ br ++ cB ++ cS) =
        lkm.totalSize cp + 3 + lkm.totalSize cL + 1 + lkm.totalSize br + lkm.totalSize cB + lkm.totalSize cS := by
      simp only [lkm.totalSize_append, htw_hdr, htw_sr1]
    have htr := reg_compileTierStoreTripleR_sim env L fl hfl lm loc hspAlign hlo hhi t i e pre
      ((chdr ++ cL ++ sr1 ++ br ++ cB ++ cS) ++ post) htOk hiOk heOk hVfT hVfI hVfE hTmp
      (by simpa only [cp, cpRes, List.append_assoc] using hlink) st hpc hgp ht5 hsp hmemRel hframeOk
    rcases htr with ⟨hrtW, hriW, hreW, htrSim⟩
    rcases _root_.L.evalE_pure t ⟨lm, loc⟩ with ⟨vt, hvt⟩ | hvt
    · rcases _root_.L.evalE_pure i ⟨lm, loc⟩ with ⟨vi, hvi⟩ | hvi
      · rcases _root_.L.evalE_pure e ⟨lm, loc⟩ with ⟨ve, hve⟩ | hve
        · simp only [hvt, hvi, hve] at htrSim
          obtain ⟨kp, st1, hrun1, hpc1, hrt1, hri1, hre1, hpres1, heq1⟩ := htrSim
          have htw1 : lkm.totalSize (pre ++ cp) = lkm.totalSize pre + lkm.totalSize cp := lkm.totalSize_append pre cp
          have hgp1 : st1.getReg AbiReg.gp = L.T := hpres1.abi.gp.trans hgp
          have hm1 := ProgMemRel.of_tempSpanR hlo hhi (Nat.zero_le _) heq1 hmemRel
          have hf1 := ProgFrameOkR.of_preserved_temp hfl hvalid (Nat.zero_le _) (hpres1.mono (fun _ h => False.elim h)) heq1 hframeOk
          have hta := tierAddrOk_len64_addr_T L.T a vt (tier32Ok_to_tierAddrOk haOk hvt)
          rcases hm1.2.1 (tierA a vt) hta.1 with ⟨hcap64, hlt61, hlenR, hbaseR, _⟩
          have hlt64 : (lm.arr64 (tierA a vt)).size < 2 ^ 64 := by omega
          obtain ⟨st2, hrun2, hpc2, ht1_2, hmem2, hpres2, hoth2⟩ :=
            step_tierHdr_r env fl (pre ++ cp) ((cL ++ sr1 ++ br ++ cB ++ cS) ++ post) rt vt
              (by simpa only [chdr, List.append_assoc] using hlink)
              (by rw [htw1]; rw [htw_all] at h64; omega) st1 (by rw [htw1]; exact hpc1) hgp1 hrt1
          have htw2 : lkm.totalSize (pre ++ cp ++ chdr) = lkm.totalSize pre + lkm.totalSize cp + 3 := by
            rw [lkm.totalSize_append, htw1, htw_hdr]
          have hri2 : st2.getReg ri = vi.toBitVec :=
            (hoth2 ri (tierValReg_ne_scratch hriW (by decide)) (tierValReg_ne_scratch hriW (by decide))).trans hri1
          have hre2 : st2.getReg re = ve.toBitVec :=
            (hoth2 re (tierValReg_ne_scratch hreW (by decide)) (tierValReg_ne_scratch hreW (by decide))).trans hre1
          have halL : isAligned (st2.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.len64 (.t0 a))) 8 = true := by
            rw [ht1_2, hta.2.1, Tab.len64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
          obtain ⟨st3, hrun3, hoth3, ht2_3, hmem3, hpc3⟩ :=
            loadMemOff_ld_correct_lm lkm env.hrom (pre ++ cp ++ chdr) ((sr1 ++ br ++ cB ++ cS) ++ post)
              AbiReg.t2 AbiReg.t1 AbiReg.t4 (by decide) (by decide) (by decide) (env.tab.len64 (.t0 a))
              (by simpa only [cL, List.append_assoc] using hlink)
              (by rw [htw2]; rw [htw_all] at h64; dsimp only [cL] at h64 ⊢; omega) st2 (by rw [htw2, ← htw1]; exact hpc2) halL
          have hpres3 : PreservedFrameRegs fl (fun _ => False) st2 st3 :=
            PreservedFrameRegs.of_scratch2 AbiReg.t2 AbiReg.t4 (by decide) (by decide) hoth3
          have htw3 : lkm.totalSize (pre ++ cp ++ chdr ++ cL) = lkm.totalSize pre + lkm.totalSize cp + 3 + lkm.totalSize cL := by
            rw [lkm.totalSize_append, htw2]
          have hri3 : st3.getReg ri = vi.toBitVec :=
            (hoth3 ri (tierValReg_ne_scratch hriW (by decide)) (tierValReg_ne_scratch hriW (by decide))).trans hri2
          have hre3 : st3.getReg re = ve.toBitVec :=
            (hoth3 re (tierValReg_ne_scratch hreW (by decide)) (tierValReg_ne_scratch hreW (by decide))).trans hre2
          have ht2Val : st3.getReg AbiReg.t2 = BitVec.ofNat 64 (lm.arr64 (tierA a vt)).size := by
            rw [ht2_3, hmem2, ht1_2, hta.2.1, hlenR]
          have hsSrli := step_item_instr_lm lkm env.hrom (pre ++ cp ++ chdr ++ cL) ((br ++ cB ++ cS) ++ post)
            (.shImm .srli AbiReg.t4 ri 1#6)
            (by simpa only [sr1, Asm.srli, List.append_assoc] using hlink)
            (by rw [htw3]; rw [htw_all] at h64; omega) st3 (by rw [htw3, ← htw2]; exact hpc3)
          let st3b := stepReg st3 AbiReg.t4 (evalShiftImm .srli (st3.getReg ri) 1#6) (st3.pc + 4#64)
          have hrun3b : RV64.run env.rom 1 st3 = .cont st3b := run_one_cont _ _ st3b (by rw [hsSrli]; rfl)
          have hpres3b : PreservedFrameRegs fl (fun _ => False) st3 st3b :=
            PreservedFrameRegs.of_scratch1 AbiReg.t4 (by decide) (fun r hr => getReg_stepReg_ne st3 AbiReg.t4 r hr _ _)
          have htw3b : lkm.totalSize (pre ++ cp ++ chdr ++ cL ++ sr1) = lkm.totalSize pre + lkm.totalSize cp + 3 + lkm.totalSize cL + 1 := by
            rw [lkm.totalSize_append, htw3, htw_sr1]
          have hpc3b : st3b.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ cp ++ chdr ++ cL ++ sr1)) := by
            change st3.pc + 4#64 = _; rw [pc_add_4_ofNat st3.pc hpc3, htw3b, htw2]
          have ht4_3b : st3b.getReg AbiReg.t4 = BitVec.ofNat 64 (vi.toNat / 2) := by
            change (stepReg st3 AbiReg.t4 _ _).getReg AbiReg.t4 = _
            rw [getReg_stepReg_eq _ _ (by decide), hri3]
            apply BitVec.eq_of_toNat_eq
            simp only [evalShiftImm, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, UInt64.toNat_toBitVec,
              show (1#6 : BitVec 6).toNat = 1 from rfl, Nat.shiftRight_eq_div_pow, Nat.pow_one]
            have hlt := vi.toBitVec.isLt; rw [UInt64.toNat_toBitVec] at hlt
            rw [Nat.mod_eq_of_lt (by omega)]
          have ht2_3b : st3b.getReg AbiReg.t2 = BitVec.ofNat 64 (lm.arr64 (tierA a vt)).size :=
            (getReg_stepReg_ne st3 AbiReg.t4 AbiReg.t2 (by decide) _ _).trans ht2Val
          have hstepEq : _root_.L.step [] (fun _ => throw .outOfFuel) (.st32t a t i e) ⟨lm, loc⟩ =
              if (vi / 2).toNat < (lm.arr64 (tierA a vt)).size then .ok (.normal, ⟨lm.set32 (tierA a vt) vi ve, loc⟩) else .error .oob := by
            simp only [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvt, hvi, hve, _root_.L.st32, get, getThe,
              MonadStateOf.get, StateT.get, set, MonadStateOf.set, Pure.pure, StateT.pure, Except.pure,
              throw, throwThe, MonadExceptOf.throw, Function.comp_apply]
            by_cases hb : (vi / 2).toNat < (lm.arr64 (tierA a vt)).size <;> simp only [hb, ↓reduceIte] <;> rfl
          rw [hstepEq]
          have hbrSz : lkm.itemSize (.br .bgeu AbiReg.t4 AbiReg.t2 errLabel) = lkm.totalSize br := by simp [br, Asm.bgeu, lkm.totalSize_singleton]
          have hdiv2 : (vi / 2).toNat = vi.toNat / 2 := rfl
          have hdivLt64 : vi.toNat / 2 < 2 ^ 64 := by have := vi.toBitVec.isLt; rw [UInt64.toNat_toBitVec] at this; omega
          by_cases hb : (vi / 2).toNat < (lm.arr64 (tierA a vt)).size
          · simp only [hb, ↓reduceIte]
            have hcondF : evalBranch .bgeu (st3b.getReg AbiReg.t4) (st3b.getReg AbiReg.t2) = false := by
              rw [ht4_3b, ht2_3b, evalBranch_bgeu_nat hdivLt64 hlt64]
              simp [show ¬((lm.arr64 (tierA a vt)).size ≤ vi.toNat / 2) by omega]
            obtain ⟨kBr, st4, hrun4, hpc4, hoth4, _, hmem4⟩ :=
              prog_step_br_fall env (pre ++ cp ++ chdr ++ cL ++ sr1) ((cB ++ cS) ++ post)
                .bgeu AbiReg.t4 AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide)
                (by simpa only [br, Asm.bgeu, List.append_assoc] using hlink)
                (by rw [htw3b, hbrSz]; rw [htw_all] at h64; omega) st3b hpc3b hcondF
            have hpres4 : PreservedFrameRegs fl (fun _ => False) st3b st4 :=
              preservedFrameRegs_of_t6_s1 hoth4
            have htw4 : lkm.totalSize (pre ++ cp ++ chdr ++ cL ++ sr1 ++ br) =
                lkm.totalSize pre + lkm.totalSize cp + 3 + lkm.totalSize cL + 1 + lkm.totalSize br := by
              rw [lkm.totalSize_append, htw3b]
            have ht1_4 : st4.getReg AbiReg.t1 = L.T + (if (vt &&& 1 == 0) = true then 0#64 else 8#64) :=
              (hoth4 AbiReg.t1 (by decide)).trans
                ((getReg_stepReg_ne st3 AbiReg.t4 AbiReg.t1 (by decide) _ _).trans
                  ((hoth3 AbiReg.t1 (by decide) (by decide)).trans ht1_2))
            have halB : isAligned (st4.getReg AbiReg.t1 + BitVec.ofInt 64 (env.tab.base64 (.t0 a))) 8 = true := by
              rw [ht1_4, hta.2.2, Tab.base64_eq_nat]; exact isAligned8_add_int_mul8 L.T L.hTAlign _
            obtain ⟨st5, hrun5, hoth5, ht1_5, hmem5, hpc5⟩ :=
              loadMemOff_ld_correct_lm lkm env.hrom (pre ++ cp ++ chdr ++ cL ++ sr1 ++ br) (cS ++ post)
                AbiReg.t1 AbiReg.t1 AbiReg.t4 (by decide) (by decide) (by decide) (env.tab.base64 (.t0 a))
                (by simpa only [cB, List.append_assoc] using hlink)
                (by rw [htw4]; rw [htw_all] at h64; dsimp only [cB] at h64 ⊢; omega) st4 (by rw [htw4, ← htw3b, ← hbrSz]; exact hpc4) halB
            have hpres5 : PreservedFrameRegs fl (fun _ => False) st4 st5 :=
              PreservedFrameRegs.of_scratch2 AbiReg.t1 AbiReg.t4 (by decide) (by decide) hoth5
            have htw5 : lkm.totalSize (pre ++ cp ++ chdr ++ cL ++ sr1 ++ br ++ cB) =
                lkm.totalSize pre + lkm.totalSize cp + 3 + lkm.totalSize cL + 1 + lkm.totalSize br + lkm.totalSize cB := by
              rw [lkm.totalSize_append, htw4]
            have ht1Val5 : st5.getReg AbiReg.t1 = L.base64 (tierA a vt) := by
              rw [ht1_5, hmem4, mem_stepReg, hmem3, hmem2, ht1_4, hta.2.2, hbaseR]
            have hri5 : st5.getReg ri = vi.toBitVec :=
              (hoth5 ri (tierValReg_ne_scratch hriW (by decide)) (tierValReg_ne_scratch hriW (by decide))).trans
                ((hoth4 ri ⟨tierValReg_ne_scratch hriW (by decide), tierValReg_ne_scratch hriW (by decide)⟩).trans
                  ((getReg_stepReg_ne st3 AbiReg.t4 ri (tierValReg_ne_scratch hriW (by decide)) _ _).trans hri3))
            have hre5 : st5.getReg re = ve.toBitVec :=
              (hoth5 re (tierValReg_ne_scratch hreW (by decide)) (tierValReg_ne_scratch hreW (by decide))).trans
                ((hoth4 re ⟨tierValReg_ne_scratch hreW (by decide), tierValReg_ne_scratch hreW (by decide)⟩).trans
                  ((getReg_stepReg_ne st3 AbiReg.t4 re (tierValReg_ne_scratch hreW (by decide)) _ _).trans hre3))
            have hm5 : st5.mem = st1.mem := by dsimp only [st3b] at hmem4; rw [hmem5, hmem4, mem_stepReg, hmem3, hmem2]
            obtain ⟨kT, stEnd, hrunT, hpcT, hpresT, hmemT⟩ :=
              reg_st32tTail_sim env L fl lm loc (tierA a vt) re ri AbiReg.t4 i vi ve
                (by decide) (by decide) (by decide)
                (tierValReg_ne_scratch hreW (by decide)) (tierValReg_ne_scratch hreW (by decide))
                hvi (pre ++ cp ++ chdr ++ cL ++ sr1 ++ br ++ cB) post
                (by simpa only [cS, List.append_assoc] using hlink)
                (by rw [htw5]; rw [htw_all] at h64; dsimp only [cS] at h64 ⊢; omega)
                st5 (by rw [htw5, ← htw4]; exact hpc5) ht1Val5 hri5 hre5
            have hmemEnd : stEnd.mem = RV64.storeBytes st1.mem (L.base64 (tierA a vt) + BitVec.ofNat 64 (4 * vi.toNat)) 4 (ve.toBitVec.extractLsb' 0 32) := by
              rw [hmemT, hm5]
            have hpres1E : PreservedFrameRegs fl (fun _ => False) st1 stEnd :=
              (PreservedFrameRegs.of_a0 hpres2).trans (hpres3.trans (hpres3b.trans (hpres4.trans (hpres5.trans hpresT))))
            have heq1E : MemEqOutside (L.arr64Span (tierA a vt)) st1.mem stEnd.mem := by
              rw [hmemEnd]; apply MemEqOutside.storeBytes
              intro k hk; exact MemSpan.sub_range (s := L.arr64Span (tierA a vt)) (4 * vi.toNat) 4
                (by dsimp only [ProgLayout.arr64Span]; omega) k hk
            have h64Disj : MemDisjoint (L.arr64Span (tierA a vt)) L.stackSpan :=
              MemSpan.disjoint_to_memDisjoint (L.arr64Span_valid (tierA a vt)) L.stackSpan_valid (L.h64DisjStack (tierA a vt) hta.1)
            exact ⟨kp + (3 + (lkm.totalSize cL + (1 + (kBr + (lkm.totalSize cB + kT))))), stEnd,
              by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; rw [run_add, hrun3]; dsimp only
                 rw [run_add, hrun3b]; dsimp only; rw [run_add, hrun4]; dsimp only; rw [run_add, hrun5]; dsimp only; exact hrunT,
              by rw [hpcT, htw5, htw_all]; dsimp only [cS]; congr 2; omega,
              (hpres1.trans hpres1E).mono (fun _ h => False.elim h),
              by rw [hmemEnd]; exact ProgMemRel.set32 hm1 (tierA a vt) hta.1 vi ve hb,
              ProgFrameOkR.of_mem_outside_stack hfl hlo hhi (L.arr64Span (tierA a vt)) h64Disj hpres1E heq1E hf1,
              (ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1).trans
                (ProgMemOutside.of_memEqOutside (fun _ ha => Or.inr (Or.inr (Or.inr ⟨tierA a vt, hta.1, ha⟩))) heq1E)⟩
          · simp only [hb, ↓reduceIte]
            have hcondT : evalBranch .bgeu (st3b.getReg AbiReg.t4) (st3b.getReg AbiReg.t2) = true := by
              rw [ht4_3b, ht2_3b, evalBranch_bgeu_nat hdivLt64 hlt64]
              simp [show (lm.arr64 (tierA a vt)).size ≤ vi.toNat / 2 by omega]
            obtain ⟨kBr, st4, hrun4, hpc4, hoth4, _, hmem4⟩ :=
              prog_step_br_taken env (pre ++ cp ++ chdr ++ cL ++ sr1) ((cB ++ cS) ++ post)
                .bgeu AbiReg.t4 AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide)
                (by simpa only [br, Asm.bgeu, List.append_assoc] using hlink)
                (by rw [htw3b, hbrSz]; rw [htw_all] at h64; omega) st3b hpc3b hcondT
            exact ⟨kp + (3 + (lkm.totalSize cL + (1 + kBr))), st4,
              by rw [run_add, hrun1]; dsimp only; rw [run_add, hrun2]; dsimp only; rw [run_add, hrun3]; dsimp only
                 rw [run_add, hrun3b]; dsimp only; exact hrun4,
              hpc4, (hpres1.trans ((PreservedFrameRegs.of_a0 hpres2).trans
                (hpres3.trans (hpres3b.trans (preservedFrameRegs_of_t6_s1 hoth4))))).mono (fun _ h => False.elim h),
              by rw [hmem4, mem_stepReg, hmem3, hmem2]; exact ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1⟩
        · simp only [hvt, hvi, hve] at htrSim
          obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := htrSim
          have hstepEq : _root_.L.step [] (fun _ => throw .outOfFuel) (.st32t a t i e) ⟨lm, loc⟩ = .error .oob := by
            simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvt, hvi, hve]
          rw [hstepEq]
          exact ⟨kp, st1, hrun1, hpc1, hpres1.mono (fun _ h => False.elim h),
            ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1⟩
      · simp only [hvt, hvi] at htrSim
        obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := htrSim
        have hstepEq : _root_.L.step [] (fun _ => throw .outOfFuel) (.st32t a t i e) ⟨lm, loc⟩ = .error .oob := by
          simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvt, hvi]
        rw [hstepEq]
        exact ⟨kp, st1, hrun1, hpc1, hpres1.mono (fun _ h => False.elim h),
          ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1⟩
    · simp only [hvt] at htrSim
      obtain ⟨kp, st1, hrun1, hpc1, hpres1, heq1⟩ := htrSim
      have hstepEq : _root_.L.step [] (fun _ => throw .outOfFuel) (.st32t a t i e) ⟨lm, loc⟩ = .error .oob := by
        simp [_root_.L.step, Bind.bind, StateT.bind, Except.bind, hvt]
      rw [hstepEq]
      exact ⟨kp, st1, hrun1, hpc1, hpres1.mono (fun _ h => False.elim h),
        ProgMemOutside.of_memEqOutside (fnWriteMaskR_of_tempSpanR L hlo hhi (Nat.zero_le _)) heq1⟩

end ConAgua.RISCV.Compiler
