import ConAgua.RISCV.Compiler.ProgSimCall

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Program-Level Forward Simulation: Function Verification (`ConAgua.RISCV.Compiler.ProgSimFn`)

Function prologue, callee-save, body, epilogue & strong-induction theorem (`compileFns_call_sim`).

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard Lean axioms only.
-/

namespace ConAgua.RISCV.Compiler

open ConAgua.RISCV.RV64
open _root_.L
open ConAgua.RISCV.Linker

/-! ## 4. Function Prologue, Callee-Save, Body, Epilogue & Strong-Induction Theorem -/

private theorem numLocalsFn_ge_nparams (fd : FunDecl) : fd.nparams ≤ numLocalsFn fd := by
  dsimp only [numLocalsFn]
  exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

private theorem addImmOff_sub_cancel (callerSp : BitVec 64) (n : Nat) (hn : n ≤ callerSp.toNat) :
    (callerSp - BitVec.ofNat 64 n) + BitVec.ofInt 64 (n : Int) = callerSp := by
  have _ := hn
  rw [BitVec.ofInt_natCast, BitVec.sub_add_cancel]

private theorem frameSpanR_elem_lt {fl : FrameLayout} {sp' : BitVec 64}
    (hv : (frameSpanR fl sp').valid) {a : BitVec 64} (ha : (frameSpanR fl sp').contains a) :
    a.toNat < sp'.toNat + 8 * fl.frameSlots := by
  have hvalid : sp'.toNat + 8 * fl.frameSlots ≤ 2 ^ 64 := hv
  rcases ha with ⟨k, hk, rfl⟩
  dsimp only [frameSpanR] at hk ⊢
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

private theorem protected_disj_localsTempR {fl : FrameLayout} {sp' : BitVec 64}
    (hv : (frameSpanR fl sp').valid) {slot : Nat} (hslot : slot < fl.protectedSlots) :
    ∀ k, k < 8 → ¬(localsTempSpanR fl sp').contains (sp' + BitVec.ofNat 64 (8 * slot) + BitVec.ofNat 64 k) := by
  have hvalid : sp'.toNat + 8 * fl.frameSlots ≤ 2 ^ 64 := hv
  dsimp only [FrameLayout.frameSlots] at hvalid
  intro k hk ⟨l, hl, ha⟩
  dsimp only [localsTempSpanR] at hl ha
  have hnat := congrArg BitVec.toNat ha
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
    BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hnat
  omega

private theorem mem_of_lookup_some {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List (α × β)) {k : α} {v : β}, l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => by simp at h
  | (a, b) :: t, k, v, h => by
    simp only [List.lookup] at h
    by_cases hka : (k == a) = true
    · simp only [hka] at h
      cases Option.some.inj h
      rw [eq_of_beq hka]
      exact List.Mem.head _
    · have hfalse : (k == a) = false := Bool.eq_false_iff.mpr hka
      simp only [hfalse] at h
      exact List.Mem.tail _ (mem_of_lookup_some t h)

private def savedSpanR (fl : FrameLayout) (sp : BitVec 64) (start len : Nat) : MemSpan :=
  ⟨sp + BitVec.ofNat 64 (8 * (fl.raSlots + start)), 8 * len⟩

private theorem saveCalleeRegsLoop_sim {lkm : LinkModel} (env : CodeEnvGen lkm)
    (fl : FrameLayout) {sp : BitVec 64}
    (hal : isAligned sp 8 = true) (hv : (frameSpanR fl sp).valid) :
    ∀ (regs : List Reg) (start : Nat),
      start + regs.length ≤ fl.savedRegs.length →
      (∀ r ∈ regs, r ∈ calleeSavedBank) →
      ∀ (pre post : List AsmItem),
        lkm.linkSpec (pre ++ ((regs.zipIdx start).flatMap fun (r, i) =>
          storeMemOff .sd AbiReg.sp r AbiReg.t2 (fl.savedOff i)) ++ post) = .ok (env.code, env.labels) →
      ∀ (st : State),
        st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
        st.getReg AbiReg.sp = sp →
        ∃ k st',
          RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre +
            lkm.totalSize ((regs.zipIdx start).flatMap fun (r, i) =>
              storeMemOff .sd AbiReg.sp r AbiReg.t2 (fl.savedOff i)))) ∧
          (∀ r, r ≠ AbiReg.t2 → st'.getReg r = st.getReg r) ∧
          MemEqOutside (savedSpanR fl sp start regs.length) st.mem st'.mem ∧
          (∀ i (hi : i < regs.length),
            readWord64 st'.mem (sp + BitVec.ofInt 64 (fl.savedOff (start + i))) = st.getReg (regs[i]'hi)) := by
  have hvalid : sp.toNat + 8 * fl.frameSlots ≤ 2 ^ 64 := hv
  dsimp only [FrameLayout.frameSlots, FrameLayout.protectedSlots] at hvalid
  intro regs
  induction regs with
  | nil =>
    intro start _ _ pre post _ st hpc _
    refine ⟨0, st, rfl, by simp [lkm.totalSize_nil, hpc], fun _ _ => rfl, MemEqOutside.refl _ _,
      fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | cons r rest ih =>
    intro start hle hcal pre post hlink st hpc hsp
    have hrCal : r ∈ calleeSavedBank := hcal r List.mem_cons_self
    have hsplit : ((r :: rest).zipIdx start).flatMap (fun (q, i) => storeMemOff .sd AbiReg.sp q AbiReg.t2 (fl.savedOff i)) =
        storeMemOff .sd AbiReg.sp r AbiReg.t2 (fl.savedOff start) ++
        (rest.zipIdx (start + 1)).flatMap (fun (q, i) => storeMemOff .sd AbiReg.sp q AbiReg.t2 (fl.savedOff i)) := by
      simp [List.zipIdx_cons]
    rw [hsplit] at hlink ⊢
    have ⟨hl1, hl2⟩ := linkResolved_mid_split lkm pre _ _ post hlink
    have halS : isAligned (st.getReg AbiReg.sp + BitVec.ofInt 64 (fl.savedOff start)) 8 = true := by
      rw [hsp, savedOff_ofInt]; exact isAligned8_add_int_mul8 sp hal _
    obtain ⟨st1, hrun1, hoth1, hmem1, hpc1⟩ :=
      storeMemOff_sd_correct_lm lkm env.hrom pre _ AbiReg.sp r AbiReg.t2
        (by decide) (by decide) (allowedRegs_ne_t2 (isLeaf := false) hrCal).symm (fl.savedOff start) hl1
        (linkResolved_sub_pc64 env pre _ _ hl1) st hpc halS
    have hsp1 : st1.getReg AbiReg.sp = sp := (hoth1 _ (by decide)).trans hsp
    obtain ⟨k2, st2, hrun2, hpc2, hoth2, hout2, hsave2⟩ :=
      ih (start + 1) (by simp only [List.length_cons] at hle; omega) (fun q hq => hcal q (List.mem_cons_of_mem _ hq))
        (pre ++ storeMemOff .sd AbiReg.sp r AbiReg.t2 (fl.savedOff start)) post hl2 st1
        (by simpa [lkm.totalSize_append] using hpc1) hsp1
    have hout1 : MemEqOutside (savedSpanR fl sp start (r :: rest).length) st.mem st1.mem := by
      rw [hmem1, hsp, savedOff_ofInt]
      exact MemEqOutside.writeWord64 _ _ _ fun k hk => ⟨k, by dsimp only [savedSpanR]; simp only [List.length_cons]; omega, rfl⟩
    have hout2' : MemEqOutside (savedSpanR fl sp start (r :: rest).length) st1.mem st2.mem :=
      hout2.mono fun a ⟨k, hk, ha⟩ => by
        subst ha; dsimp only [savedSpanR] at hk ⊢
        refine ⟨8 + k, by simp only [List.length_cons]; omega, ?_⟩
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
        congr 2; omega
    refine ⟨_, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
      by simpa [lkm.totalSize_append, Nat.add_assoc] using hpc2,
      fun q hq => (hoth2 q hq).trans (hoth1 q hq),
      hout1.trans hout2', ?_⟩
    intro i hi
    cases i with
    | zero =>
      simp only [Nat.add_zero, List.getElem_cons_zero]
      have h1 : readWord64 st1.mem (sp + BitVec.ofInt 64 (fl.savedOff start)) = st.getReg r := by
        rw [hmem1, hsp]; exact readWord64_writeWord64_self _ _ _
      rw [← h1]
      apply MemEqOutside.readWord64_eq hout2
      intro k hk ⟨l, hl, ha⟩
      dsimp only [savedSpanR] at hl ha
      rw [savedOff_ofInt] at ha
      have hnat := congrArg BitVec.toNat ha
      simp only [List.length_cons] at hle
      rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
        BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hnat
      omega
    | succ i' =>
      simp only [List.getElem_cons_succ]
      rw [show start + (i' + 1) = (start + 1) + i' by omega, hsave2 i' (by simpa using hi)]
      exact hoth1 _ (allowedRegs_ne_t2 (isLeaf := false) (hcal _ (List.mem_cons_of_mem _ (List.getElem_mem _))))

private theorem copyParamsR_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    {sp callerSp argsPtr : BitVec 64}
    (hal : isAligned sp 8 = true) (halArgs : isAligned argsPtr 8 = true)
    (hlo : L.stackLimit.toNat ≤ sp.toNat)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (hspLe : sp.toNat + 8 * fl.frameSlots ≤ callerSp.toNat)
    (vs : List _root_.L.Word)
    (hargsValid : regAllocArgsValid fl.isLeaf vs.length fl.alloc = true)
    (liveP : Var → Bool)
    (hnoClobP : ∀ (y : Nat) (ry : Reg), fl.alloc.lookup y = some ry → liveP y = true →
      ∀ (x : Nat), y < x → x < vs.length → fl.alloc.lookup x ≠ some ry)
    (hargsGe : ∀ j, j < vs.length → ∀ k, k < 8 →
      callerSp.toNat ≤ (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)) + BitVec.ofNat 64 k).toNat ∨
      ¬L.stackSpan.contains (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)) + BitVec.ofNat 64 k)) :
    ∀ (n : Nat), n ≤ vs.length → n ≤ fl.nlocals →
      ∀ (pre post : List AsmItem),
        lkm.linkSpec (pre ++ copyParamsR fl n ++ post) = .ok (env.code, env.labels) →
      ∀ (st : State),
        st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
        st.getReg AbiReg.sp = sp →
        (maxRes < n → st.getReg AbiReg.t0 = argsPtr) →
        (∀ j, j < vs.length →
          (if j < maxRes then st.getReg (resReg j)
           else readWord64 st.mem (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)))) = (vs[j]!).toBitVec) →
        ∃ k st',
          RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize (copyParamsR fl n))) ∧
          (∀ r, r ≠ AbiReg.t2 → r ≠ AbiReg.t4 → r ∉ fl.alloc.map Prod.snd → st'.getReg r = st.getReg r) ∧
          (∀ j, n ≤ j → j < min vs.length maxRes → st'.getReg (resReg j) = st.getReg (resReg j)) ∧
          MemEqOutside (localsTempSpanR fl sp) st.mem st'.mem ∧
          (∀ x, x < n → liveP x = true →
            match fl.alloc.lookup x with
            | some r => st'.getReg r = (vs[x]!).toBitVec
            | none => x ∈ fl.spilledVars → readWord64 st'.mem (sp + BitVec.ofInt 64 (fl.varSlotOff x)) = (vs[x]!).toBitVec) := by
  have hframeValid : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  have ht0NotAlloc : AbiReg.t0 ∉ fl.alloc.map Prod.snd := fun hm => by
    obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm
    exact allowedRegs_ne_t0 ((regAllocValid_spec hfl.valid).1 p hp).2 hpe
  have hspNotAlloc : AbiReg.sp ∉ fl.alloc.map Prod.snd := fun hm => by
    obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm
    exact allowedRegs_ne_sp ((regAllocValid_spec hfl.valid).1 p hp).2 hpe
  have hrxNeFutureRes : ∀ {x : Nat} {rx : Reg} {j : Nat},
      x < min vs.length maxRes → fl.alloc.lookup x = some rx → x < j → j < min vs.length maxRes → rx ≠ resReg j := by
    intro x rx j hxlt hlx hlt hj
    exact regAllocArgsValid_ne hargsValid hxlt hlx hlt hj
  intro n
  induction n with
  | zero =>
    intro _ _ pre post _ st hpc _ _ _
    refine ⟨0, st, rfl, by simp [copyParamsR, lkm.totalSize_nil, hpc],
      fun _ _ _ _ => rfl, fun _ _ _ => rfl, MemEqOutside.refl _ _, fun _ hx _ => absurd hx (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro hleVs hleNl pre post hlink st hpc hsp ht0 hargWords
    let stepCode : List AsmItem :=
      if n < maxRes then
        let src := resReg n
        match fl.alloc.lookup n with
        | some rx => if rx == src then [] else [Asm.mv rx src]
        | none =>
          if !(n ∈ fl.spilledVars) then []
          else storeMemOff .sd AbiReg.sp src AbiReg.t2 (fl.varSlotOff n)
      else
        let off : Int := 8 * Int.ofNat (n - maxRes)
        match fl.alloc.lookup n with
        | some rx => loadMemOff .ld rx AbiReg.t0 AbiReg.t2 off
        | none =>
          if !(n ∈ fl.spilledVars) then []
          else
            loadMemOff .ld AbiReg.t4 AbiReg.t0 AbiReg.t2 off ++
            storeMemOff .sd AbiReg.sp AbiReg.t4 AbiReg.t2 (fl.varSlotOff n)
    have hsplit : copyParamsR fl (n + 1) = copyParamsR fl n ++ stepCode := by
      unfold copyParamsR
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      rfl
    rw [hsplit] at hlink ⊢
    have ⟨hl1, hl2⟩ := linkResolved_mid_split lkm pre (copyParamsR fl n) stepCode post hlink
    obtain ⟨k1, st1, hrun1, hpc1, hoth1, hres1, hout1, hsl1⟩ :=
      ih (by omega) (by omega) pre (stepCode ++ post) hl1 st hpc hsp (fun h => ht0 (by omega)) hargWords
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ copyParamsR fl n)) := by
      simpa [lkm.totalSize_append] using hpc1
    have hsp_1 : st1.getReg AbiReg.sp = sp := (hoth1 _ (by decide) (by decide) hspNotAlloc).trans hsp
    by_cases hnm : n < maxRes
    · have hsrcVal : st1.getReg (resReg n) = (vs[n]!).toBitVec := by
        rw [hres1 n (Nat.le_refl n) (by omega)]
        have h := hargWords n (by omega); simpa [hnm] using h
      cases hln : fl.alloc.lookup n with
      | some rx =>
        have hrxInfo := regAllocValid_lookup hfl.valid hln
        have hrxMem := hrxInfo.2.1
        have hrxAlloc := hrxInfo.2.2
        by_cases heqR : rx = resReg n
        · have hstEq : stepCode = [] := by simp [stepCode, hnm, hln, heqR]
          refine ⟨k1, st1, hrun1, by rw [hstEq, List.append_nil]; exact hpc1,
            hoth1, fun j hj hjm => hres1 j (by omega) hjm, hout1, ?_⟩
          intro x hx hlive
          by_cases hxeq : x = n
          · subst hxeq; rw [hln, heqR]; exact hsrcVal
          · exact hsl1 x (by omega) hlive
        · have hstEq : stepCode = [Asm.mv rx (resReg n)] := by
            simp [stepCode, hnm, hln, beq_false_of_ne heqR]
          rw [hstEq] at hl2 ⊢
          obtain ⟨hrun2, hpc2, hrx2, hoth2, hmem2⟩ :=
            run_aluImm_rd_step env (pre ++ copyParamsR fl n) post .addi rx (resReg n) 0#12
              (allowedRegs_ne_zero hrxMem) (by simpa [Asm.mv] using hl2) st1 hpc1'
          let st2 := stepReg st1 rx (evalAluImm .addi (st1.getReg (resReg n)) 0#12)
            (BitVec.ofNat 64 (4 * (lkm.totalSize (pre ++ copyParamsR fl n) + 1)))
          have hrxVal : st2.getReg rx = (vs[n]!).toBitVec := by
            rw [hrx2]; change st1.getReg (resReg n) + sextImm12 0#12 = _
            rw [hsrcVal, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero]
          refine ⟨k1 + 1, st2, by rw [run_add, hrun1]; exact hrun2,
            by rw [hpc2, lkm.totalSize_append (copyParamsR fl n), lkm.totalSize_append pre,
              show lkm.totalSize [Asm.mv rx (resReg n)] = 1 from by simp only [Asm.mv, lkm.totalSize_instr], Nat.add_assoc],
            fun r hr2 hr4 hrna => (hoth2 r (fun h => hrna (h ▸ hrxAlloc))).trans (hoth1 r hr2 hr4 hrna),
            fun j hj hjm => (hoth2 (resReg j) (hrxNeFutureRes (j := j) (by omega) hln (by omega) hjm).symm).trans (hres1 j (by omega) hjm),
            by rw [hmem2]; exact hout1, ?_⟩
          intro x hx hlive
          by_cases hxeq : x = n
          · subst hxeq; rw [hln]; exact hrxVal
          · have hsl := hsl1 x (by omega) hlive
            cases hlx : fl.alloc.lookup x with
            | some ry =>
              rw [hlx] at hsl; dsimp only at hsl ⊢
              have hne : ry ≠ rx := fun he => hnoClobP x ry hlx hlive n (by omega) (by omega) (he ▸ hln)
              rw [hoth2 ry hne, hsl]
            | none => rw [hlx] at hsl; dsimp only at hsl ⊢; intro hmx; rw [hmem2]; exact hsl hmx
      | none =>
        by_cases hmn : n ∈ fl.spilledVars
        · have hstEq : stepCode = storeMemOff .sd AbiReg.sp (resReg n) AbiReg.t2 (fl.varSlotOff n) := by
            simp [stepCode, hnm, hln, hmn]
          rw [hstEq] at hl2 ⊢
          have halSpN : isAligned (st1.getReg AbiReg.sp + BitVec.ofInt 64 (fl.varSlotOff n)) 8 = true := by
            rw [hsp_1, varSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hal _
          obtain ⟨st2, hrun2, hoth2, hmem2, hpc2⟩ :=
            storeMemOff_sd_correct_lm lkm env.hrom (pre ++ copyParamsR fl n) post
              AbiReg.sp (resReg n) AbiReg.t2 (by decide) (by decide) (resReg_ne_preserved n).2.2.2.2.2.2.2.symm
              (fl.varSlotOff n) hl2 (linkResolved_sub_pc64 env _ _ post hl2) st1 hpc1' halSpN
          have hmem2Eq : st2.mem = writeWord64 st1.mem (sp + BitVec.ofInt 64 (fl.varSlotOff n)) (vs[n]!).toBitVec := by
            rw [hmem2, hsp_1, hsrcVal]
          have hsi := hfl.spillIdx_lt hmn
          have hltSub : (varSlotSpanR fl sp n).sub (localsTempSpanR fl sp) := by
            intro a ⟨k, hk, ha⟩; subst ha
            dsimp only [varSlotSpanR, slotSpan, slotAddr] at hk ⊢
            refine ⟨8 * fl.spillIdx n + k, by dsimp only [localsTempSpanR]; omega, ?_⟩
            dsimp only [localsTempSpanR]
            rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
          have houtStep : MemEqOutside (localsTempSpanR fl sp) st1.mem st2.mem := by
            rw [hmem2Eq, varSlotOff_ofInt]
            exact MemEqOutside.writeWord64 _ _ _ fun k hk => hltSub _ ⟨k, hk, rfl⟩
          refine ⟨_, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
            by simpa [lkm.totalSize_append, Nat.add_assoc] using hpc2,
            fun r hr2 hr4 hrna => (hoth2 r hr2).trans (hoth1 r hr2 hr4 hrna),
            fun j hj hjm => (hoth2 (resReg j) (resReg_ne_preserved j).2.2.2.2.2.2.2).trans (hres1 j (by omega) hjm),
            hout1.trans houtStep, ?_⟩
          intro x hx hlive
          by_cases hxeq : x = n
          · subst hxeq; rw [hln]; intro _; rw [hmem2Eq]; exact readWord64_writeWord64_self _ _ _
          · have hsl := hsl1 x (by omega) hlive
            cases hlx : fl.alloc.lookup x with
            | some ry =>
              rw [hlx] at hsl; dsimp only at hsl ⊢
              have hryMem := (regAllocValid_lookup hfl.valid hlx).2.1
              rw [hoth2 ry (allowedRegs_ne_t2 hryMem), hsl]
            | none =>
              rw [hlx] at hsl; dsimp only at hsl ⊢; intro hmx
              have hdisj := varSlotSpanR_disj_of_ne fl hfl sp hframeValid hmn hmx (Ne.symm hxeq)
              rw [hmem2Eq, varSlotOff_ofInt, varSlotOff_ofInt]
              rw [readWord64_writeWord64_disjoint st1.mem
                (sp + BitVec.ofNat 64 (8 * (fl.protectedSlots + fl.spillIdx x)))
                (sp + BitVec.ofNat 64 (8 * (fl.protectedSlots + fl.spillIdx n)))
                (vs[n]!).toBitVec fun i1 i2 hi1 hi2 heq =>
                  hdisj _ ⟨i2, hi2, rfl⟩ ⟨i1, hi1, heq.symm⟩]
              rw [← varSlotOff_ofInt]; exact hsl hmx
        · have hstEq : stepCode = [] := by simp [stepCode, hnm, hln, hmn]
          refine ⟨k1, st1, hrun1, by rw [hstEq, List.append_nil]; exact hpc1,
            hoth1, fun j hj hjm => hres1 j (by omega) hjm, hout1, ?_⟩
          intro x hx hlive
          by_cases hxeq : x = n
          · subst hxeq; rw [hln]; intro hmem; exact absurd hmem hmn
          · exact hsl1 x (by omega) hlive
    · have ht0' : st.getReg AbiReg.t0 = argsPtr := ht0 (by omega)
      have ht0_1 : st1.getReg AbiReg.t0 = argsPtr := (hoth1 _ (by decide) (by decide) ht0NotAlloc).trans ht0'
      have hoffEq : BitVec.ofInt 64 (8 * Int.ofNat (n - maxRes)) = BitVec.ofNat 64 (8 * (n - maxRes)) := by
        change BitVec.ofInt 64 (8 * ((n - maxRes : Nat) : Int)) = BitVec.ofNat 64 (8 * (n - maxRes))
        rw [show (8 : Int) * ((n - maxRes : Nat) : Int) = ((8 * (n - maxRes) : Nat) : Int) from by omega, BitVec.ofInt_natCast]
      have halArg : isAligned (st1.getReg AbiReg.t0 + BitVec.ofInt 64 (8 * Int.ofNat (n - maxRes))) 8 = true := by
        rw [ht0_1, hoffEq]; exact isAligned8_add_mul8 argsPtr halArgs _
      have hargN : readWord64 st1.mem (argsPtr + BitVec.ofNat 64 (8 * (n - maxRes))) = (vs[n]!).toBitVec := by
        have h0 := hargWords n (by omega); simp only [hnm, ↓reduceIte] at h0
        rw [← h0]
        refine MemEqOutside.readWord64_eq hout1 _ fun k hk hc => ?_
        have hcStack := localsTempSpanR_sub_stackSpan L hlo hhi _ hc
        rcases hc with ⟨off, hoff, ha⟩
        have haLt : (argsPtr + BitVec.ofNat 64 (8 * (n - maxRes)) + BitVec.ofNat 64 k).toNat < callerSp.toNat := by
          rw [ha]; dsimp only [localsTempSpanR] at hoff ⊢
          have hv : sp.toNat + 8 * fl.frameSlots ≤ 2 ^ 64 := hframeValid
          dsimp only [FrameLayout.frameSlots] at hv hspLe
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        rcases hargsGe n (by omega) k hk with hge | hnot
        · exact Nat.not_le_of_lt haLt hge
        · exact hnot hcStack
      cases hln : fl.alloc.lookup n with
      | some rx =>
        have hrxInfo := regAllocValid_lookup hfl.valid hln
        have hrxMem := hrxInfo.2.1
        have hrxAlloc := hrxInfo.2.2
        have hstEq : stepCode = loadMemOff .ld rx AbiReg.t0 AbiReg.t2 (8 * Int.ofNat (n - maxRes)) := by
          simp [stepCode, hnm, hln]
        rw [hstEq] at hl2 ⊢
        obtain ⟨st2, hrun2, hoth2, hrx2, hmem2, hpc2⟩ :=
          loadMemOff_ld_correct_lm lkm env.hrom (pre ++ copyParamsR fl n) post
            rx AbiReg.t0 AbiReg.t2 (allowedRegs_ne_zero hrxMem) (by decide) (by decide)
            (8 * Int.ofNat (n - maxRes)) hl2 (linkResolved_sub_pc64 env _ _ post hl2) st1 hpc1' halArg
        refine ⟨_, st2, by rw [run_add, hrun1]; dsimp only; exact hrun2,
          by simpa [lkm.totalSize_append, Nat.add_assoc] using hpc2,
          fun r hr2 hr4 hrna => (hoth2 r (fun h => hrna (h ▸ hrxAlloc)) hr2).trans (hoth1 r hr2 hr4 hrna),
          fun j hj hjm => by omega,
          by rw [hmem2]; exact hout1, ?_⟩
        intro x hx hlive
        by_cases hxeq : x = n
        · subst hxeq; rw [hln]; dsimp only; rw [hrx2, ht0_1, hoffEq, hargN]
        · have hsl := hsl1 x (by omega) hlive
          cases hlx : fl.alloc.lookup x with
          | some ry =>
            rw [hlx] at hsl; dsimp only at hsl ⊢
            have hryMem := (regAllocValid_lookup hfl.valid hlx).2.1
            have hne : ry ≠ rx := fun he => hnoClobP x ry hlx hlive n (by omega) (by omega) (he ▸ hln)
            rw [hoth2 ry hne (allowedRegs_ne_t2 hryMem), hsl]
          | none => rw [hlx] at hsl; dsimp only at hsl ⊢; intro hmx; rw [hmem2]; exact hsl hmx
      | none =>
        by_cases hmn : n ∈ fl.spilledVars
        · have hstEq : stepCode =
              loadMemOff .ld AbiReg.t4 AbiReg.t0 AbiReg.t2 (8 * Int.ofNat (n - maxRes)) ++
              storeMemOff .sd AbiReg.sp AbiReg.t4 AbiReg.t2 (fl.varSlotOff n) := by simp [stepCode, hnm, hln, hmn]
          rw [hstEq] at hl2 ⊢
          have hpre1Link : lkm.linkSpec ((pre ++ copyParamsR fl n) ++
              loadMemOff .ld AbiReg.t4 AbiReg.t0 AbiReg.t2 (8 * Int.ofNat (n - maxRes)) ++
              (storeMemOff .sd AbiReg.sp AbiReg.t4 AbiReg.t2 (fl.varSlotOff n) ++ post)) =
              .ok (env.code, env.labels) := by simpa [List.append_assoc] using hl2
          obtain ⟨st2, hrun2, hoth2, ht4_2, hmem2, hpc2⟩ :=
            loadMemOff_ld_correct_lm lkm env.hrom (pre ++ copyParamsR fl n) _
              AbiReg.t4 AbiReg.t0 AbiReg.t2 (by decide) (by decide) (by decide)
              (8 * Int.ofNat (n - maxRes)) hpre1Link (linkResolved_sub_pc64 env _ _ _ hpre1Link) st1 hpc1' halArg
          have ht4Val : st2.getReg AbiReg.t4 = (vs[n]!).toBitVec := by rw [ht4_2, ht0_1, hoffEq, hargN]
          let pre2 := (pre ++ copyParamsR fl n) ++ loadMemOff .ld AbiReg.t4 AbiReg.t0 AbiReg.t2 (8 * Int.ofNat (n - maxRes))
          have hlinkSd : lkm.linkSpec (pre2 ++ storeMemOff .sd AbiReg.sp AbiReg.t4 AbiReg.t2 (fl.varSlotOff n) ++ post) =
              .ok (env.code, env.labels) := by simpa [pre2, List.append_assoc] using hpre1Link
          have hsp_2 : st2.getReg AbiReg.sp = sp := (hoth2 _ (by decide) (by decide)).trans hsp_1
          have halSpN : isAligned (st2.getReg AbiReg.sp + BitVec.ofInt 64 (fl.varSlotOff n)) 8 = true := by
            rw [hsp_2, varSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hal _
          obtain ⟨st3, hrun3, hoth3, hmem3, hpc3⟩ :=
            storeMemOff_sd_correct_lm lkm env.hrom pre2 post AbiReg.sp AbiReg.t4 AbiReg.t2
              (by decide) (by decide) (by decide) (fl.varSlotOff n) hlinkSd
              (linkResolved_sub_pc64 env pre2 _ post hlinkSd) st2 (by simpa [pre2, lkm.totalSize_append, Nat.add_assoc] using hpc2) halSpN
          have hmem3Eq : st3.mem = writeWord64 st1.mem (sp + BitVec.ofInt 64 (fl.varSlotOff n)) (vs[n]!).toBitVec := by
            rw [hmem3, hmem2, hsp_2, ht4Val]
          have hsi := hfl.spillIdx_lt hmn
          have hltSub : (varSlotSpanR fl sp n).sub (localsTempSpanR fl sp) := by
            intro a ⟨k, hk, ha⟩; subst ha
            dsimp only [varSlotSpanR, slotSpan, slotAddr] at hk ⊢
            refine ⟨8 * fl.spillIdx n + k, by dsimp only [localsTempSpanR]; omega, ?_⟩
            dsimp only [localsTempSpanR]
            rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
          have houtStep : MemEqOutside (localsTempSpanR fl sp) st1.mem st3.mem := by
            rw [hmem3Eq, varSlotOff_ofInt]
            exact MemEqOutside.writeWord64 _ _ _ fun k hk => hltSub _ ⟨k, hk, rfl⟩
          refine ⟨_, st3, by rw [run_add, run_add, hrun1]; dsimp only; rw [hrun2]; exact hrun3,
            by simpa [pre2, lkm.totalSize_append, Nat.add_assoc] using hpc3,
            fun r hr2 hr4 hrna => (hoth3 r hr2).trans ((hoth2 r hr4 hr2).trans (hoth1 r hr2 hr4 hrna)),
            fun j hj hjm => by omega,
            hout1.trans houtStep, ?_⟩
          intro x hx hlive
          by_cases hxeq : x = n
          · subst hxeq; rw [hln]; dsimp only; intro _; rw [hmem3Eq]; exact readWord64_writeWord64_self _ _ _
          · have hsl := hsl1 x (by omega) hlive
            cases hlx : fl.alloc.lookup x with
            | some ry =>
              rw [hlx] at hsl; dsimp only at hsl ⊢
              have hryMem := (regAllocValid_lookup hfl.valid hlx).2.1
              rw [hoth3 ry (allowedRegs_ne_t2 hryMem), hoth2 ry (allowedRegs_ne_t4 hryMem) (allowedRegs_ne_t2 hryMem), hsl]
            | none =>
              rw [hlx] at hsl; dsimp only at hsl ⊢; intro hmx
              have hdisj := varSlotSpanR_disj_of_ne fl hfl sp hframeValid hmn hmx (Ne.symm hxeq)
              rw [hmem3Eq, varSlotOff_ofInt, varSlotOff_ofInt]
              rw [readWord64_writeWord64_disjoint st1.mem
                (sp + BitVec.ofNat 64 (8 * (fl.protectedSlots + fl.spillIdx x)))
                (sp + BitVec.ofNat 64 (8 * (fl.protectedSlots + fl.spillIdx n)))
                (vs[n]!).toBitVec fun i1 i2 hi1 hi2 heq =>
                  hdisj _ ⟨i2, hi2, rfl⟩ ⟨i1, hi1, heq.symm⟩]
              rw [← varSlotOff_ofInt]; exact hsl hmx
        · have hstEq : stepCode = [] := by simp [stepCode, hnm, hln, hmn]
          refine ⟨k1, st1, hrun1, by rw [hstEq, List.append_nil]; exact hpc1,
            hoth1, fun j hj hjm => by omega, hout1, ?_⟩
          intro x hx hlive
          by_cases hxeq : x = n
          · subst hxeq; rw [hln]; intro hmem; exact absurd hmem hmn
          · exact hsl1 x (by omega) hlive


private theorem zeroLocalsR_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (fl : FrameLayout) (hfl : FrameLayoutOk fl) (fd : FunDecl)
    {sp : BitVec 64}
    (hal : isAligned sp 8 = true)
    (hhi : sp.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat)
    (liveE : Var → Bool)
    (hnoClobParam : ∀ y ry, y < fd.nparams → fl.alloc.lookup y = some ry → liveE y = true →
      ∀ x, fd.nparams ≤ x → x < fl.nlocals → varNeedsZeroInit fd x = true → fl.alloc.lookup x ≠ some ry)
    (hnoClobLocal : ∀ y ry, fd.nparams ≤ y → fl.alloc.lookup y = some ry → liveE y = true →
      ∀ x, y < x → x < fl.nlocals → varNeedsZeroInit fd x = true → fl.alloc.lookup x ≠ some ry) :
    ∀ (count : Nat), fd.nparams + count ≤ fl.nlocals →
      ∀ (pre post : List AsmItem),
        lkm.linkSpec (pre ++ ((List.range count).flatMap fun j =>
          let x := fd.nparams + j
          if !varNeedsZeroInit fd x then []
          else match fl.alloc.lookup x with
            | some rx => [Asm.addi rx AbiReg.zero 0#12]
            | none =>
              if !(x ∈ fl.spilledVars) then []
              else storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t2 (fl.varSlotOff x)) ++ post) =
          .ok (env.code, env.labels) →
      ∀ (st : State),
        st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre) →
        st.getReg AbiReg.sp = sp →
        ∃ k st',
          RV64.run env.rom k st = .cont st' ∧
          st'.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre +
            lkm.totalSize ((List.range count).flatMap fun j =>
              let x := fd.nparams + j
              if !varNeedsZeroInit fd x then []
              else match fl.alloc.lookup x with
                | some rx => [Asm.addi rx AbiReg.zero 0#12]
                | none =>
                  if !(x ∈ fl.spilledVars) then []
                  else storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t2 (fl.varSlotOff x)))) ∧
          (∀ r, r ≠ AbiReg.t2 → r ∉ fl.alloc.map Prod.snd → st'.getReg r = st.getReg r) ∧
          MemEqOutside (localsTempSpanR fl sp) st.mem st'.mem ∧
          (∀ x, x < fd.nparams → liveE x = true →
            match fl.alloc.lookup x with
            | some r => st'.getReg r = st.getReg r
            | none => x ∈ fl.spilledVars → readWord64 st'.mem (sp + BitVec.ofInt 64 (fl.varSlotOff x)) =
                readWord64 st.mem (sp + BitVec.ofInt 64 (fl.varSlotOff x))) ∧
          (∀ x, fd.nparams ≤ x → x < fd.nparams + count → liveE x = true → varNeedsZeroInit fd x = true →
            match fl.alloc.lookup x with
            | some r => st'.getReg r = 0#64
            | none => x ∈ fl.spilledVars → readWord64 st'.mem (sp + BitVec.ofInt 64 (fl.varSlotOff x)) = 0#64) := by
  have hframeValid : (frameSpanR fl sp).valid := Nat.le_trans hhi L.hStackValid
  have hspNotAlloc : AbiReg.sp ∉ fl.alloc.map Prod.snd := fun hm => by
    obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm
    exact allowedRegs_ne_sp ((regAllocValid_spec hfl.valid).1 p hp).2 hpe
  let itemFn : Nat → List AsmItem := fun j =>
    let x := fd.nparams + j
    if !varNeedsZeroInit fd x then []
    else match fl.alloc.lookup x with
      | some rx => [Asm.addi rx AbiReg.zero 0#12]
      | none =>
        if !(x ∈ fl.spilledVars) then []
        else storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t2 (fl.varSlotOff x)
  intro count
  induction count with
  | zero =>
    intro _ pre post _ st hpc _
    refine ⟨0, st, rfl, by simp [lkm.totalSize_nil, hpc], fun _ _ _ => rfl, MemEqOutside.refl _ _,
      fun x _ _ => by cases fl.alloc.lookup x with | some _ => rfl | none => intro _; rfl,
      fun _ h1 h2 _ _ => by omega⟩
  | succ c ih =>
    intro hle pre post hlink st hpc hsp
    have hsplit : (List.range (c + 1)).flatMap itemFn = (List.range c).flatMap itemFn ++ itemFn c := by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    change lkm.linkSpec (pre ++ (List.range (c + 1)).flatMap itemFn ++ post) = _ at hlink
    rw [hsplit] at hlink
    have ⟨hl1, hl2⟩ := linkResolved_mid_split lkm pre ((List.range c).flatMap itemFn) (itemFn c) post hlink
    obtain ⟨k1, st1, hrun1, hpc1, hoth1, hout1, hkeep1, hzero1⟩ :=
      ih (by omega) pre (itemFn c ++ post) hl1 st hpc hsp
    have hpc1' : st1.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre ++ (List.range c).flatMap itemFn)) := by
      simpa [itemFn, lkm.totalSize_append] using hpc1
    have hsp_1 : st1.getReg AbiReg.sp = sp := (hoth1 _ (by decide) hspNotAlloc).trans hsp
    let xC := fd.nparams + c
    cases hneed : varNeedsZeroInit fd xC with
    | false =>
      have hitem : itemFn c = [] := by simp [itemFn, xC, hneed]
      refine ⟨k1, st1, hrun1, ?_, hoth1, hout1, hkeep1, ?_⟩
      · change st1.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize ((List.range (c + 1)).flatMap itemFn)))
        rw [hsplit, hitem, List.append_nil]; exact hpc1
      · intro x hloX hhiX hlive hnz
        have hne : x ≠ xC := by intro he; subst he; rw [hneed] at hnz; cases hnz
        exact hzero1 x hloX (by omega) hlive hnz
    | true =>
      cases hlxC : fl.alloc.lookup xC with
      | some rx =>
        have hrxInfo := regAllocValid_lookup hfl.valid hlxC
        have hrxMem := hrxInfo.2.1
        have hrxAlloc := hrxInfo.2.2
        have hitem : itemFn c = [Asm.addi rx AbiReg.zero 0#12] := by simp [itemFn, xC, hneed, hlxC]
        rw [hitem] at hl2
        have htw1 : lkm.totalSize [Asm.addi rx AbiReg.zero 0#12] = 1 := by simp only [Asm.addi, lkm.totalSize_instr]
        obtain ⟨hrun2, hpc2, hrx2, hoth2, hmem2⟩ :=
          run_aluImm_rd_step env (pre ++ (List.range c).flatMap itemFn) post .addi rx AbiReg.zero 0#12
            (allowedRegs_ne_zero hrxMem) (by simpa [Asm.addi] using hl2) st1 hpc1'
        let st2 := stepReg st1 rx (evalAluImm .addi (st1.getReg AbiReg.zero) 0#12)
          (BitVec.ofNat 64 (4 * (lkm.totalSize (pre ++ (List.range c).flatMap itemFn) + 1)))
        have hrx0 : st2.getReg rx = 0#64 := by
          rw [hrx2]; change st1.getReg AbiReg.zero + sextImm12 0#12 = 0#64; rw [getReg_zero]; decide
        refine ⟨k1 + 1, st2, by rw [run_add, hrun1]; exact hrun2, ?_,
          fun r hr2 hrna => (hoth2 r (fun h => hrna (h ▸ hrxAlloc))).trans (hoth1 r hr2 hrna),
          by rw [hmem2]; exact hout1, ?_, ?_⟩
        · change st2.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize ((List.range (c + 1)).flatMap itemFn)))
          rw [hpc2, hsplit, hitem, lkm.totalSize_append, lkm.totalSize_append, htw1, Nat.add_assoc]
        · intro x hx hlive
          have hk := hkeep1 x hx hlive
          cases hlx : fl.alloc.lookup x with
          | some ry =>
            rw [hlx] at hk; dsimp only at hk ⊢
            have hne : ry ≠ rx := fun he =>
              hnoClobParam x ry hx hlx hlive xC (by omega) (by omega) hneed (he ▸ hlxC)
            rw [hoth2 ry hne, hk]
          | none => rw [hlx] at hk; dsimp only at hk ⊢; intro hmx; rw [hmem2]; exact hk hmx
        · intro x hloX hhiX hlive hnz
          by_cases hxeq : x = xC
          · subst hxeq; rw [hlxC]; exact hrx0
          · have hz := hzero1 x hloX (by omega) hlive hnz
            cases hlx : fl.alloc.lookup x with
            | some ry =>
              rw [hlx] at hz; dsimp only at hz ⊢
              have hne : ry ≠ rx := fun he =>
                hnoClobLocal x ry hloX hlx hlive xC (by omega) (by omega) hneed (he ▸ hlxC)
              rw [hoth2 ry hne, hz]
            | none => rw [hlx] at hz; dsimp only at hz ⊢; intro hmx; rw [hmem2]; exact hz hmx
      | none =>
        by_cases hmxC : xC ∈ fl.spilledVars
        · have hitem : itemFn c = storeMemOff .sd AbiReg.sp AbiReg.zero AbiReg.t2 (fl.varSlotOff xC) := by
            simp [itemFn, xC, hneed, hlxC, hmxC]
          rw [hitem] at hl2
          have halSpI : isAligned (st1.getReg AbiReg.sp + BitVec.ofInt 64 (fl.varSlotOff xC)) 8 = true := by
            rw [hsp_1, varSlotOff_ofInt]; exact isAligned8_add_int_mul8 sp hal _
          obtain ⟨st2, hrun2, hoth2, hmem2, hpc2⟩ :=
            storeMemOff_sd_correct_lm lkm env.hrom (pre ++ (List.range c).flatMap itemFn) post
              AbiReg.sp AbiReg.zero AbiReg.t2 (by decide) (by decide) (by decide) (fl.varSlotOff xC)
              hl2 (linkResolved_sub_pc64 env _ _ post hl2) st1 hpc1' halSpI
          have hmem2Eq : st2.mem = writeWord64 st1.mem (sp + BitVec.ofInt 64 (fl.varSlotOff xC)) 0#64 := by
            rw [hmem2, hsp_1, getReg_zero st1]
          have hsi := hfl.spillIdx_lt hmxC
          have hltSub : (varSlotSpanR fl sp xC).sub (localsTempSpanR fl sp) := by
            intro a ⟨k, hk, ha⟩; subst ha
            dsimp only [varSlotSpanR, slotSpan, slotAddr] at hk ⊢
            refine ⟨8 * fl.spillIdx xC + k, by dsimp only [localsTempSpanR]; omega, ?_⟩
            dsimp only [localsTempSpanR]
            rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
          have houtStep : MemEqOutside (localsTempSpanR fl sp) st1.mem st2.mem := by
            rw [hmem2Eq, varSlotOff_ofInt]
            exact MemEqOutside.writeWord64 _ _ _ fun k hk => hltSub _ ⟨k, hk, rfl⟩
          have hdisjSlot : ∀ (x : Nat), x ∈ fl.spilledVars → x ≠ xC →
              readWord64 st2.mem (sp + BitVec.ofInt 64 (fl.varSlotOff x)) =
              readWord64 st1.mem (sp + BitVec.ofInt 64 (fl.varSlotOff x)) := by
            intro x hmx hne
            have hdisj := varSlotSpanR_disj_of_ne fl hfl sp hframeValid hmxC hmx (Ne.symm hne)
            rw [hmem2Eq, varSlotOff_ofInt, varSlotOff_ofInt]
            exact readWord64_writeWord64_disjoint _ _ _ _ fun i1 i2 hi1 hi2 heq =>
              hdisj _ ⟨i2, hi2, rfl⟩ ⟨i1, hi1, heq.symm⟩
          refine ⟨_, st2, by rw [run_add, hrun1]; exact hrun2, ?_,
            fun r hr2 hrna => (hoth2 r hr2).trans (hoth1 r hr2 hrna),
            hout1.trans houtStep, ?_, ?_⟩
          · change st2.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize ((List.range (c + 1)).flatMap itemFn)))
            rw [hpc2, hsplit, hitem, lkm.totalSize_append, lkm.totalSize_append, Nat.add_assoc]
          · intro x hx hlive
            have hk := hkeep1 x hx hlive
            cases hlx : fl.alloc.lookup x with
            | some ry =>
              rw [hlx] at hk; dsimp only at hk ⊢
              rw [hoth2 ry (allowedRegs_ne_t2 (regAllocValid_lookup hfl.valid hlx).2.1), hk]
            | none =>
              rw [hlx] at hk; dsimp only at hk ⊢; intro hmx
              rw [hdisjSlot x hmx (by dsimp only [xC]; omega), hk hmx]
          · intro x hloX hhiX hlive hnz
            by_cases hxeq : x = xC
            · subst hxeq; rw [hlxC]; intro _; rw [hmem2Eq]; exact readWord64_writeWord64_self _ _ _
            · have hz := hzero1 x hloX (by omega) hlive hnz
              cases hlx : fl.alloc.lookup x with
              | some ry =>
                rw [hlx] at hz; dsimp only at hz ⊢
                rw [hoth2 ry (allowedRegs_ne_t2 (regAllocValid_lookup hfl.valid hlx).2.1), hz]
              | none =>
                rw [hlx] at hz; dsimp only at hz ⊢; intro hmx
                rw [hdisjSlot x hmx hxeq, hz hmx]
        · have hitem : itemFn c = [] := by simp [itemFn, xC, hneed, hlxC, hmxC]
          refine ⟨k1, st1, hrun1, ?_, hoth1, hout1, hkeep1, ?_⟩
          · change st1.pc = BitVec.ofNat 64 (4 * (lkm.totalSize pre + lkm.totalSize ((List.range (c + 1)).flatMap itemFn)))
            rw [hsplit, hitem, List.append_nil]; exact hpc1
          · intro x hloX hhiX hlive hnz
            by_cases hxeq : x = xC
            · subst hxeq; rw [hlxC]; intro hmem; exact absurd hmem hmxC
            · exact hzero1 x hloX (by omega) hlive hnz

private def fnPrologueAsmR (f : FnName) (fd : FunDecl) (fl : FrameLayout) : List AsmItem :=
  let framePush : List AsmItem :=
    if fl.frameBytes == 0 then []
    else
      li AbiReg.t2 (BitVec.ofInt 64 fl.frameBytes) ++
      [Asm.bltu AbiReg.sp AbiReg.t2 errLabel,
       Asm.sub AbiReg.sp AbiReg.sp AbiReg.t2,
       Asm.ld AbiReg.t2 AbiReg.gp 8#12,
       Asm.bltu AbiReg.sp AbiReg.t2 errLabel] ++
      (if fl.isLeaf then [] else [Asm.sd AbiReg.sp AbiReg.ra 0#12]) ++
      saveCalleeRegs fl
  let t5Init : List AsmItem :=
    if fl.useT5Gp then [Asm.addi AbiReg.t5 AbiReg.gp 2047#12] else []
  [Asm.lbl (fnLabel f)] ++ framePush ++ copyParamsR fl fd.nparams ++ zeroLocalsR fl fd ++ t5Init

private theorem compileFn_prologueR_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (f : FnName) (fd : FunDecl) (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    (hargsValid : regAllocArgsValid fl.isLeaf fd.nparams fl.alloc = true)
    (hgraphValid : regAllocGraphValid fl.isLeaf fl.nlocals fl.alloc fd = true)
    (hfbLe : 8 * fl.frameSlots ≤ fnFrameBytes fd) (hnpLeNl : fd.nparams ≤ fl.nlocals)
    (preFn tailCode : List AsmItem)
    (hlinkPro : lkm.linkSpec (preFn ++ fnPrologueAsmR f fd fl ++ tailCode) = .ok (env.code, env.labels))
    (vs : List _root_.L.Word) (m : _root_.L.Mem)
    (callerSp callerRa argsPtr : BitVec 64)
    (hvslen : vs.length = fd.nparams)
    (hlim : L.stackLimit.toNat + fnFrameBytes fd ≤ callerSp.toNat)
    (hctop : callerSp.toNat ≤ L.stackTop.toNat)
    (hcal : isAligned callerSp 8 = true) (hargAl : isAligned argsPtr 8 = true)
    (hargsGe : ∀ j, j < vs.length → ∀ k, k < 8 →
      callerSp.toNat ≤ (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)) + BitVec.ofNat 64 k).toNat ∨
      ¬L.stackSpan.contains (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)) + BitVec.ofNat 64 k))
    (entryPc : Nat) (st : State)
    (hEntryLbl : lookupLabel env.labels (fnLabel f) = some entryPc)
    (hpc : st.pc = BitVec.ofNat 64 (4 * entryPc))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = callerSp)
    (hra : st.getReg AbiReg.ra = callerRa)
    (ht0 : maxRes < fd.nparams → st.getReg AbiReg.t0 = argsPtr)
    (hm : ProgMemRel env.tab L st.mem m) (hhdr : TabHeaderOk L st.mem)
    (hargWords : ∀ j, j < vs.length →
      (if j < maxRes then st.getReg (resReg j)
       else readWord64 st.mem (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)))) = (vs[j]!).toBitVec) :
    let sp' := callerSp - BitVec.ofNat 64 (8 * fl.frameSlots)
    ∃ kPro stCL,
      RV64.run env.rom kPro st = .cont stCL ∧
      stCL.pc = BitVec.ofNat 64 (4 * lkm.totalSize (preFn ++ fnPrologueAsmR f fd fl)) ∧
      stCL.getReg AbiReg.gp = L.T ∧
      T5GpOk L fl stCL ∧
      stCL.getReg AbiReg.sp = sp' ∧
      stCL.getReg AbiReg.s0 = st.getReg AbiReg.s0 ∧
      stCL.getReg AbiReg.s2 = st.getReg AbiReg.s2 ∧
      (fl.isLeaf = true → stCL.getReg AbiReg.ra = callerRa) ∧
      (fl.isLeaf = false → readWord64 stCL.mem sp' = callerRa) ∧
      (∀ r ∈ calleeSavedBank, r ∉ fl.savedRegs → stCL.getReg r = st.getReg r) ∧
      (∀ i (hi : i < fl.savedRegs.length),
        readWord64 stCL.mem (sp' + BitVec.ofInt 64 (fl.savedOff i)) = st.getReg (fl.savedRegs[i]'hi)) ∧
      ProgMemOutside (CallWriteMask L callerSp) st.mem stCL.mem ∧
      ProgMemRel env.tab L stCL.mem m ∧
      TabHeaderOk L stCL.mem ∧
      ProgFrameOkLive L fl sp' stCL (Locals.init vs) (fun x => (stmtVarCallFree x fd.body false false).1) := by
  have hframeLeSp : 8 * fl.frameSlots ≤ callerSp.toNat := by omega
  let sp' := callerSp - BitVec.ofNat 64 (8 * fl.frameSlots)
  have hsp'ToNat : sp'.toNat = callerSp.toNat - 8 * fl.frameSlots :=
    bitvec_sub_mul8_toNat callerSp fl.frameSlots hframeLeSp
  have hlimSp' : L.stackLimit.toNat ≤ sp'.toNat := by rw [hsp'ToNat]; omega
  have htopSp' : sp'.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat := by rw [hsp'ToNat]; omega
  have hspLeFrame : sp'.toNat + 8 * fl.frameSlots ≤ callerSp.toNat := by rw [hsp'ToNat]; omega
  have hframeValid : (frameSpanR fl sp').valid := Nat.le_trans htopSp' L.hStackValid
  have halSp' : isAligned sp' 8 = true := isAligned8_sub_mul8 callerSp hcal fl.frameSlots hframeLeSp
  let pfx := fnLabel f
  let framePush : List AsmItem :=
    if fl.frameBytes == 0 then []
    else
      li AbiReg.t2 (BitVec.ofInt 64 fl.frameBytes) ++
      [Asm.bltu AbiReg.sp AbiReg.t2 errLabel,
       Asm.sub AbiReg.sp AbiReg.sp AbiReg.t2,
       Asm.ld AbiReg.t2 AbiReg.gp 8#12,
       Asm.bltu AbiReg.sp AbiReg.t2 errLabel] ++
      (if fl.isLeaf then [] else [Asm.sd AbiReg.sp AbiReg.ra 0#12]) ++
      saveCalleeRegs fl
  let cCopy := copyParamsR fl fd.nparams
  let cZero := zeroLocalsR fl fd
  let cT5 : List AsmItem := if fl.useT5Gp then [Asm.addi AbiReg.t5 AbiReg.gp 2047#12] else []
  have hcfDecomp : fnPrologueAsmR f fd fl = [Asm.lbl pfx] ++ framePush ++ cCopy ++ cZero ++ cT5 := rfl
  rw [hcfDecomp] at hlinkPro
  have hEntryLbl' : lookupLabel env.labels pfx = some (lkm.totalSize preFn) :=
    linkResolved_lbl_lm lkm preFn pfx _ (by simpa [List.append_assoc] using hlinkPro)
  rw [hEntryLbl'] at hEntryLbl
  have hEntryEq : entryPc = lkm.totalSize preFn := Option.some.inj hEntryLbl.symm
  let pre1 := preFn ++ [Asm.lbl pfx]
  have hpc0 : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by
    rw [hpc, hEntryEq]; dsimp only [pre1]
    simp only [lkm.totalSize_append, show lkm.totalSize [Asm.lbl pfx] = 0 from by simp only [Asm.lbl, lkm.totalSize_label], Nat.add_zero]
  have hnotAlloc_of_res : ∀ q, q ∈ reservedAbiRegs → q ∉ fl.alloc.map Prod.snd := fun q hq hm => by
    obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm
    exact allowedRegs_disj_reserved true ((regAllocValid_spec hfl.valid).1 p hp).2 hq hpe
  have hnotAlloc_unsaved : ∀ r ∈ calleeSavedBank, r ∉ fl.savedRegs → r ∉ fl.alloc.map Prod.snd := fun r hr hns hm =>
    hns (hfl.saved_mem_iff.mpr ⟨hr, hm⟩)
  -- Phase 1: framePush (either frameless `fl.frameSlots = 0` or full frame push + ra/callee save)
  have hpushPhase :
      ∃ kP stP,
        RV64.run env.rom kP st = .cont stP ∧
        stP.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre1 ++ framePush)) ∧
        stP.getReg AbiReg.gp = L.T ∧
        stP.getReg AbiReg.sp = sp' ∧
        stP.getReg AbiReg.ra = callerRa ∧
        stP.getReg AbiReg.s0 = st.getReg AbiReg.s0 ∧
        stP.getReg AbiReg.s2 = st.getReg AbiReg.s2 ∧
        (maxRes < fd.nparams → stP.getReg AbiReg.t0 = argsPtr) ∧
        (∀ j, j < maxRes → stP.getReg (resReg j) = st.getReg (resReg j)) ∧
        (∀ r ∈ calleeSavedBank, stP.getReg r = st.getReg r) ∧
        (fl.isLeaf = false → readWord64 stP.mem sp' = callerRa) ∧
        (∀ i (hi : i < fl.savedRegs.length),
          readWord64 stP.mem (sp' + BitVec.ofInt 64 (fl.savedOff i)) = st.getReg (fl.savedRegs[i]'hi)) ∧
        MemEqOutside (frameSpanR fl sp') st.mem stP.mem := by
    by_cases h0 : fl.frameSlots = 0
    · obtain ⟨hleaf, hsr, _, _⟩ := hfl.frameSlots_zero_props h0
      have hfb0 : (fl.frameBytes == 0) = true := by simp [FrameLayout.frameBytes, h0]
      have hfpEmpty : framePush = [] := by simp [framePush, hfb0]
      have hsp'Eq : sp' = callerSp := by dsimp only [sp']; rw [h0]; simp
      refine ⟨0, st, rfl, (by rw [hfpEmpty, List.append_nil]; exact hpc0), hgp, (by rw [hsp'Eq]; exact hsp),
        hra, rfl, rfl, ht0, (fun _ _ => rfl), (fun _ _ => rfl), (fun hf => by rw [hleaf] at hf; cases hf),
        (fun i hi => by rw [hsr] at hi; exact absurd hi (Nat.not_lt_zero _)), MemEqOutside.refl _ _⟩
    · have hfbNe : (fl.frameBytes == 0) = false := by
        simp only [FrameLayout.frameBytes, beq_eq_false_iff_ne]; omega
      let cLiF := li AbiReg.t2 (BitVec.ofInt 64 fl.frameBytes)
      let cRa := if fl.isLeaf then [] else [Asm.sd AbiReg.sp AbiReg.ra 0#12]
      let cSave := saveCalleeRegs fl
      have hfpEq : framePush = cLiF ++ [Asm.bltu AbiReg.sp AbiReg.t2 errLabel,
          Asm.sub AbiReg.sp AbiReg.sp AbiReg.t2, Asm.ld AbiReg.t2 AbiReg.gp 8#12,
          Asm.bltu AbiReg.sp AbiReg.t2 errLabel] ++ cRa ++ cSave := by
        simp [framePush, hfbNe, cLiF, cRa, cSave, List.append_assoc]
      have hlink1 : lkm.linkSpec (pre1 ++ cLiF ++ ([Asm.bltu AbiReg.sp AbiReg.t2 errLabel,
          Asm.sub AbiReg.sp AbiReg.sp AbiReg.t2, Asm.ld AbiReg.t2 AbiReg.gp 8#12,
          Asm.bltu AbiReg.sp AbiReg.t2 errLabel] ++ cRa ++ cSave ++ cCopy ++ cZero ++ cT5 ++ tailCode)) =
          .ok (env.code, env.labels) := by rw [hfpEq] at hlinkPro; simpa [pre1, List.append_assoc] using hlinkPro
      obtain ⟨st1, hrun1, hoth1, ht2_1, hmem1, hpc1⟩ :=
        li_correct_lm lkm env.hrom pre1 _ AbiReg.t2 (by decide) (BitVec.ofInt 64 fl.frameBytes) hlink1
          (linkResolved_sub_pc64 env pre1 cLiF _ hlink1) st hpc0
      let pre2 := pre1 ++ cLiF
      have hlink2 : lkm.linkSpec (pre2 ++ [Asm.bltu AbiReg.sp AbiReg.t2 errLabel] ++
          ([Asm.sub AbiReg.sp AbiReg.sp AbiReg.t2, Asm.ld AbiReg.t2 AbiReg.gp 8#12,
            Asm.bltu AbiReg.sp AbiReg.t2 errLabel] ++ cRa ++ cSave ++ cCopy ++ cZero ++ cT5 ++ tailCode)) =
          .ok (env.code, env.labels) := by simpa [pre2, List.append_assoc] using hlink1
      have hbr1 := run_br_step env pre2 _ .bltu AbiReg.sp AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide) hlink2 st1
        (by simpa [pre2, lkm.totalSize_append] using hpc1)
      have hframeLt64 : 8 * fl.frameSlots < 2 ^ 64 := Nat.lt_of_le_of_lt hframeLeSp callerSp.isLt
      have hsp1 : st1.getReg AbiReg.sp = callerSp := (hoth1 _ (by decide)).trans hsp
      have ht2Val1 : st1.getReg AbiReg.t2 = BitVec.ofNat 64 (8 * fl.frameSlots) := by
        rw [ht2_1]; exact frameBytesR_toNat_eq fl
      have hcond1 : evalBranch .bltu (st1.getReg AbiReg.sp) (st1.getReg AbiReg.t2) = false := by
        rw [hsp1, ht2Val1]
        simp only [evalBranch, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hframeLt64,
          decide_eq_false_iff_not, Nat.not_lt]; exact hframeLeSp
      obtain ⟨kBr1, st2, _, hrun2, hpc2Br, hoth2Br, _, hmem2Br⟩ := hbr1
      let pre3 := pre2 ++ [Asm.bltu AbiReg.sp AbiReg.t2 errLabel]
      have hpc2' : st2.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre3) := by
        rw [hpc2Br, hcond1]; simp only [Bool.false_eq_true, ↓reduceIte]
        exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (lkm.totalSize_append pre2 _).symm
      have hlink3 : lkm.linkSpec (pre3 ++ [Asm.sub AbiReg.sp AbiReg.sp AbiReg.t2] ++
          ([Asm.ld AbiReg.t2 AbiReg.gp 8#12, Asm.bltu AbiReg.sp AbiReg.t2 errLabel] ++ cRa ++ cSave ++ cCopy ++ cZero ++ cT5 ++ tailCode)) =
          .ok (env.code, env.labels) := by simpa [pre3, List.append_assoc] using hlink2
      obtain ⟨hrun3, hpc3, hsp3, hoth3, hmem3⟩ :=
        run_alu_rd_step env pre3 _ .sub AbiReg.sp AbiReg.sp AbiReg.t2 (by decide) hlink3 st2 hpc2'
      let st3 := stepReg st2 AbiReg.sp (evalAlu .sub (st2.getReg AbiReg.sp) (st2.getReg AbiReg.t2))
        (BitVec.ofNat 64 (4 * (lkm.totalSize pre3 + 1)))
      have hspVal3 : st3.getReg AbiReg.sp = sp' := by
        rw [hsp3]; change st2.getReg AbiReg.sp - st2.getReg AbiReg.t2 = sp'
        rw [hoth2Br _ (by decide), hoth2Br _ (by decide), hsp1, ht2Val1]
      let pre4 := pre3 ++ [Asm.sub AbiReg.sp AbiReg.sp AbiReg.t2]
      have hpc3' : st3.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre4) := by
        rw [hpc3]; dsimp only [pre4]; simp only [lkm.totalSize_append, Asm.sub, lkm.totalSize_instr]
      have hlink4 : lkm.linkSpec (pre4 ++ [Asm.raw (.load .ld AbiReg.t2 AbiReg.gp 8#12)] ++
          ([Asm.bltu AbiReg.sp AbiReg.t2 errLabel] ++ cRa ++ cSave ++ cCopy ++ cZero ++ cT5 ++ tailCode)) =
          .ok (env.code, env.labels) := by simpa [pre4, Asm.raw, Asm.ld, List.append_assoc] using hlink3
      have hpc4_64 : 4 * (lkm.totalSize pre4 + 1) < 2 ^ 64 := by
        have h := linkResolved_sub_pc64 env pre4 [Asm.raw (.load .ld AbiReg.t2 AbiReg.gp 8#12)] _ hlink4
        rw [show lkm.totalSize [Asm.raw (.load .ld AbiReg.t2 AbiReg.gp 8#12)] = 1 from by simp only [Asm.raw, lkm.totalSize_instr]] at h; exact h
      have hgp3 : st3.getReg AbiReg.gp = L.T := (hoth3 _ (by decide)).trans ((hoth2Br _ (by decide)).trans ((hoth1 _ (by decide)).trans hgp))
      have halT8 : isAligned (st3.getReg AbiReg.gp + sextImm12 8#12) 8 = true := by
        rw [hgp3, show sextImm12 8#12 = 8#64 from rfl, show (8#64 : BitVec 64) = BitVec.ofNat 64 (8 * 1) from rfl]
        exact isAligned8_add_mul8 L.T L.hTAlign 1
      obtain ⟨hrun4, hpc4, ht2_4, hoth4, hmem4⟩ :=
        step_ld_off env pre4 _ AbiReg.t2 AbiReg.gp 8#12 (by decide) hlink4 hpc4_64 st3 hpc3' halT8
      let st4 := stepReg st3 AbiReg.t2 (readWord64 st3.mem (st3.getReg AbiReg.gp + sextImm12 8#12)) (st3.pc + 4#64)
      have hmem3Eq : st3.mem = st.mem := by rw [hmem3, hmem2Br]; exact hmem1
      have ht2Val4 : st4.getReg AbiReg.t2 = L.stackLimit := by
        change st4.getReg AbiReg.t2 = L.stackLimit; rw [ht2_4, hgp3, show sextImm12 8#12 = 8#64 from rfl, hmem3Eq, hhdr.2]
      let pre5 := pre4 ++ [Asm.ld AbiReg.t2 AbiReg.gp 8#12]
      have hpc4' : st4.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre5) := by
        rw [hpc4]; dsimp only [pre5]; simp only [lkm.totalSize_append, Asm.ld, lkm.totalSize_instr]
      have hlink5 : lkm.linkSpec (pre5 ++ [Asm.bltu AbiReg.sp AbiReg.t2 errLabel] ++
          (cRa ++ cSave ++ cCopy ++ cZero ++ cT5 ++ tailCode)) = .ok (env.code, env.labels) := by
        simpa [pre5, Asm.raw, Asm.ld, List.append_assoc] using hlink4
      have hbr2 := run_br_step env pre5 _ .bltu AbiReg.sp AbiReg.t2 errLabel env.errTarget env.herrLbl (by decide) hlink5 st4 hpc4'
      have hsp4 : st4.getReg AbiReg.sp = sp' := (hoth4 _ (by decide)).trans hspVal3
      have hcond2 : evalBranch .bltu (st4.getReg AbiReg.sp) (st4.getReg AbiReg.t2) = false := by
        rw [hsp4, ht2Val4]; simp only [evalBranch, BitVec.ult, decide_eq_false_iff_not, Nat.not_lt]; exact hlimSp'
      obtain ⟨kBr2, st5, _, hrun5, hpc5Br, hoth5Br, _, hmem5Br⟩ := hbr2
      let pre6 := pre5 ++ [Asm.bltu AbiReg.sp AbiReg.t2 errLabel]
      have hpc5' : st5.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre6) := by
        rw [hpc5Br, hcond2]; simp only [Bool.false_eq_true, ↓reduceIte]
        exact congrArg (fun n => BitVec.ofNat 64 (4 * n)) (lkm.totalSize_append pre5 _).symm
      have hsp5 : st5.getReg AbiReg.sp = sp' := (hoth5Br _ (by decide)).trans hsp4
      have hmem5 : st5.mem = st.mem := hmem5Br.trans (hmem4.trans hmem3Eq)
      have hoth05 : ∀ r, r ≠ AbiReg.sp → r ≠ AbiReg.t2 → r ≠ AbiReg.t6 ∧ r ≠ AbiReg.s1 → st5.getReg r = st.getReg r := fun r hspR ht2R ht6R =>
        (hoth5Br r ht6R).trans ((hoth4 r ht2R).trans ((hoth3 r hspR).trans ((hoth2Br r ht6R).trans (hoth1 r ht2R))))
      have hrun05 : RV64.run env.rom (lkm.totalSize cLiF + kBr1 + 1 + 1 + kBr2) st = .cont st5 :=
        run_trans (run_trans (run_trans (run_trans hrun1 hrun2) hrun3) hrun4) hrun5
      -- Optional `sd sp ra 0` when `!fl.isLeaf`
      have hraStep :
          ∃ kRa st6,
            RV64.run env.rom kRa st5 = .cont st6 ∧
            st6.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre6 ++ cRa)) ∧
            (∀ r, st6.getReg r = st5.getReg r) ∧
            (fl.isLeaf = false → readWord64 st6.mem sp' = callerRa) ∧
            MemEqOutside (frameSpanR fl sp') st.mem st6.mem := by
        cases hleaf : fl.isLeaf with
        | true =>
          have hcRaE : cRa = [] := by simp [cRa, hleaf]
          exact ⟨0, st5, rfl, (by rw [hcRaE, List.append_nil]; exact hpc5'), (fun _ => rfl),
            (fun h => by cases h), (by rw [hmem5]; exact MemEqOutside.refl _ _)⟩
        | false =>
          have hcRaE : cRa = [Asm.sd AbiReg.sp AbiReg.ra 0#12] := by simp [cRa, hleaf]
          have hlink6 : lkm.linkSpec (pre6 ++ [Asm.raw (.store .sd AbiReg.sp AbiReg.ra 0#12)] ++
              (cSave ++ cCopy ++ cZero ++ cT5 ++ tailCode)) = .ok (env.code, env.labels) := by
            rw [hcRaE] at hlink5; simpa [pre6, Asm.raw, Asm.sd, List.append_assoc] using hlink5
          have hpc6_64 : 4 * (lkm.totalSize pre6 + 1) < 2 ^ 64 := by
            have h := linkResolved_sub_pc64 env pre6 [Asm.raw (.store .sd AbiReg.sp AbiReg.ra 0#12)] _ hlink6
            rw [show lkm.totalSize [Asm.raw (.store .sd AbiReg.sp AbiReg.ra 0#12)] = 1 from by simp only [Asm.raw, lkm.totalSize_instr]] at h; exact h
          have halSp5 : isAligned (st5.getReg AbiReg.sp + sextImm12 0#12) 8 = true := by
            rw [hsp5, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero]; exact halSp'
          obtain ⟨hrun6, hpc6, _⟩ := step_sd_off env pre6 _ AbiReg.sp AbiReg.ra 0#12 hlink6 hpc6_64 st5 hpc5' halSp5
          let st6 := { st5 with pc := st5.pc + 4#64, mem := writeWord64 st5.mem (st5.getReg AbiReg.sp + sextImm12 0#12) (st5.getReg AbiReg.ra) }
          have hra5 : st5.getReg AbiReg.ra = callerRa := (hoth05 _ (by decide) (by decide) (by decide)).trans hra
          have hmem6 : st6.mem = writeWord64 st.mem sp' callerRa := by
            dsimp only [st6]; rw [hmem5, hsp5, hra5, show sextImm12 0#12 = 0#64 from rfl, BitVec.add_zero]
          refine ⟨1, st6, hrun6, ?_, fun _ => rfl, fun _ => by rw [hmem6]; exact readWord64_writeWord64_self _ _ _, ?_⟩
          · rw [hpc6, hcRaE]; simp only [lkm.totalSize_append, Asm.sd, lkm.totalSize_instr]
          · rw [hmem6]
            exact MemEqOutside.writeWord64 _ _ _ fun k hk => ⟨k, by dsimp only [frameSpanR]; omega, rfl⟩
      obtain ⟨kRa, st6, hrunRa, hpc6', hreg6, hraSlot6, hmemEq6⟩ := hraStep
      let pre7 := pre6 ++ cRa
      have hlinkSave : lkm.linkSpec (pre7 ++ saveCalleeRegs fl ++ (cCopy ++ cZero ++ cT5 ++ tailCode)) = .ok (env.code, env.labels) := by
        simpa [pre7, pre6, cSave, List.append_assoc] using hlink5
      obtain ⟨kSv, st7, hrunSv, hpc7, hothSv, houtSv, hsave7⟩ :=
        saveCalleeRegsLoop_sim env fl halSp' hframeValid fl.savedRegs 0 (Nat.zero_add _ ▸ Nat.le_refl _)
          (fun r hr => hfl.saved_mem_callee hr) pre7 (cCopy ++ cZero ++ cT5 ++ tailCode) hlinkSave st6 hpc6'
          ((hreg6 _).trans hsp5)
      have hsaveSubFrame : (savedSpanR fl sp' 0 fl.savedRegs.length).sub (frameSpanR fl sp') := by
        intro a ⟨k, hk, ha⟩; subst ha
        dsimp only [savedSpanR] at hk ⊢
        refine ⟨8 * fl.raSlots + k, by dsimp only [frameSpanR, FrameLayout.frameSlots, FrameLayout.protectedSlots]; omega, ?_⟩
        dsimp only [frameSpanR]; rw [Nat.add_zero, BitVec.add_assoc, ← BitVec.ofNat_add]
      have hraSlot7 : fl.isLeaf = false → readWord64 st7.mem sp' = callerRa := fun hnl => by
        rw [← hraSlot6 hnl]
        apply MemEqOutside.readWord64_eq houtSv
        intro k hk ⟨l, hl, ha⟩
        dsimp only [savedSpanR] at hl ha
        have hra1 : fl.raSlots = 1 := by simp [FrameLayout.raSlots, hnl]
        have hv : sp'.toNat + 8 * fl.frameSlots ≤ 2 ^ 64 := hframeValid
        dsimp only [FrameLayout.frameSlots, FrameLayout.protectedSlots] at hv
        rw [hra1, Nat.add_zero] at ha
        have hnat := congrArg BitVec.toNat ha
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hnat
        omega
      have hpc7' : st7.pc = BitVec.ofNat 64 (4 * lkm.totalSize (pre1 ++ framePush)) := by
        rw [hpc7, hfpEq]
        exact congrArg (fun n => BitVec.ofNat 64 (4 * n))
          (by dsimp only [pre7, pre6, pre5, pre4, pre3, pre2, cSave, saveCalleeRegs]; simp only [lkm.totalSize_append, lkm.totalSize_cons, lkm.totalSize_nil]; omega)
      refine ⟨_, st7, run_trans (run_trans hrun05 hrunRa) hrunSv, hpc7',
        (hothSv _ (by decide)).trans ((hreg6 _).trans ((hoth05 _ (by decide) (by decide) (by decide)).trans hgp)),
        (hothSv _ (by decide)).trans ((hreg6 _).trans hsp5),
        (hothSv _ (by decide)).trans ((hreg6 _).trans ((hoth05 _ (by decide) (by decide) (by decide)).trans hra)),
        (hothSv _ (by decide)).trans ((hreg6 _).trans (hoth05 _ (by decide) (by decide) (by decide))),
        (hothSv _ (by decide)).trans ((hreg6 _).trans (hoth05 _ (by decide) (by decide) (by decide))),
        (fun hpos => (hothSv _ (by decide)).trans ((hreg6 _).trans ((hoth05 _ (by decide) (by decide) (by decide)).trans (ht0 hpos)))),
        (fun j _ => (hothSv (resReg j) (resReg_ne_preserved j).2.2.2.2.2.2.2).trans ((hreg6 _).trans
          (hoth05 (resReg j) (resReg_ne_preserved j).2.1 (resReg_ne_preserved j).2.2.2.2.2.2.2 ⟨resReg_ne_t6 j, (resReg_ne_preserved j).2.2.2.1⟩))),
        (fun r hr => (hothSv r (allowedRegs_ne_t2 (isLeaf := false) hr)).trans ((hreg6 r).trans
          (hoth05 r (allowedRegs_ne_sp (isLeaf := false) hr) (allowedRegs_ne_t2 (isLeaf := false) hr) ⟨allowedRegs_ne_t6 (isLeaf := false) hr, allowedRegs_ne_s1 (isLeaf := false) hr⟩))),
        hraSlot7,
        (fun i hi => by
          have h := hsave7 i hi; simp only [Nat.zero_add] at h
          rw [h, hreg6 _, hoth05 _ (allowedRegs_ne_sp (isLeaf := false) (hfl.saved_mem_callee (List.getElem_mem hi)))
            (allowedRegs_ne_t2 (isLeaf := false) (hfl.saved_mem_callee (List.getElem_mem hi)))
            ⟨allowedRegs_ne_t6 (isLeaf := false) (hfl.saved_mem_callee (List.getElem_mem hi)),
             allowedRegs_ne_s1 (isLeaf := false) (hfl.saved_mem_callee (List.getElem_mem hi))⟩]),
        hmemEq6.trans (houtSv.mono hsaveSubFrame)⟩
  obtain ⟨kP, stP, hrunP, hpcP, hgpP, hspP, hraP, hs0P, hs2P, ht0P, hresP, hcalP, hraSlotP, hsavedP, hmemEqP⟩ := hpushPhase
  -- Phase 2: copyParamsR + zeroLocalsR + optional t5Init
  have hargWordsP : ∀ j, j < vs.length →
      (if j < maxRes then stP.getReg (resReg j)
       else readWord64 stP.mem (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)))) = (vs[j]!).toBitVec := by
    intro j hj
    have h0 := hargWords j hj
    by_cases hjm : j < maxRes
    · simp only [hjm, ↓reduceIte] at h0 ⊢
      rw [hresP j hjm, h0]
    · simp only [hjm, ↓reduceIte] at h0 ⊢
      rw [← h0]
      refine MemEqOutside.readWord64_eq hmemEqP _ fun k hk hcFrame => ?_
      have hcStack := frameSpanR_sub_stackSpan L hlimSp' htopSp' _ hcFrame
      have haLt := Nat.lt_of_lt_of_le (frameSpanR_elem_lt hframeValid hcFrame) hspLeFrame
      rcases hargsGe j hj k hk with hge | hnot
      · exact Nat.not_le_of_lt haLt hge
      · exact hnot hcStack
  let preCp := pre1 ++ framePush
  have hlinkCp : lkm.linkSpec (preCp ++ cCopy ++ (cZero ++ cT5 ++ tailCode)) = .ok (env.code, env.labels) := by
    simpa [preCp, pre1, List.append_assoc] using hlinkPro
  let liveEntry : Var → Bool := fun x => (stmtVarCallFree x fd.body false false).1
  have hnoClobP : ∀ (y : Nat) (ry : Reg), fl.alloc.lookup y = some ry → liveEntry y = true →
      ∀ (x : Nat), y < x → x < vs.length → fl.alloc.lookup x ≠ some ry := by
    intro y ry hly hlive x hgt hlt hlx
    have hgr := hgraphValid
    simp only [regAllocGraphValid, Bool.and_eq_true, List.all_eq_true] at hgr
    have h2 := hgr.2 (y, ry) (list_lookup_mem hly)
    have hok := h2.2.2
    have hne : (stmtVarSafe y (fun x => (x != y) && (fl.alloc.lookup x == some ry))
        (!fl.isLeaf && (ry ∈ leafExtraBank)) fd.body false false).1 = true := by
      rw [stmtVarSafe_fst]; exact hlive
    have hylt : y < fd.nparams := by omega
    simp only [hne, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hylt, Bool.and_eq_true,
      List.all_eq_true, List.mem_range] at hok
    have hx := hok.1 x (by omega)
    simp [gt_iff_lt, hgt, Nat.ne_of_gt hgt, hlx] at hx
  have hnoClobParam : ∀ y ry, y < fd.nparams → fl.alloc.lookup y = some ry → liveEntry y = true →
      ∀ x, fd.nparams ≤ x → x < fl.nlocals → varNeedsZeroInit fd x = true → fl.alloc.lookup x ≠ some ry := by
    intro y ry hylt hly hlive x hxlo hxhi hnz hlx
    have hgr := hgraphValid
    simp only [regAllocGraphValid, Bool.and_eq_true, List.all_eq_true] at hgr
    have h2 := hgr.2 (y, ry) (list_lookup_mem hly)
    have hok := h2.2.2
    have hne : (stmtVarSafe y (fun x => (x != y) && (fl.alloc.lookup x == some ry))
        (!fl.isLeaf && (ry ∈ leafExtraBank)) fd.body false false).1 = true := by
      rw [stmtVarSafe_fst]; exact hlive
    simp only [hne, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hylt, Bool.and_eq_true,
      List.all_eq_true, List.mem_range] at hok
    have hx := hok.2 (x - fd.nparams) (by omega)
    have hadd : fd.nparams + (x - fd.nparams) = x := by omega
    rw [hadd] at hx
    simp [hnz, hlx] at hx
    exact Nat.not_lt_of_ge hxlo (hx ▸ hylt)
  have hnoClobLocal : ∀ y ry, fd.nparams ≤ y → fl.alloc.lookup y = some ry → liveEntry y = true →
      ∀ x, y < x → x < fl.nlocals → varNeedsZeroInit fd x = true → fl.alloc.lookup x ≠ some ry := by
    intro y ry hylo hly hlive x hgt hxhi hnz hlx
    have hgr := hgraphValid
    simp only [regAllocGraphValid, Bool.and_eq_true, List.all_eq_true] at hgr
    have h2 := hgr.2 (y, ry) (list_lookup_mem hly)
    have hok := h2.2.2
    have hne : (stmtVarSafe y (fun x => (x != y) && (fl.alloc.lookup x == some ry))
        (!fl.isLeaf && (ry ∈ leafExtraBank)) fd.body false false).1 = true := by
      rw [stmtVarSafe_fst]; exact hlive
    have hynlt : ¬(y < fd.nparams) := by omega
    simp only [hne, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hynlt, Bool.and_eq_true,
      List.all_eq_true, List.mem_range] at hok
    have hx := hok.2 (x - fd.nparams) (by omega)
    have hadd : fd.nparams + (x - fd.nparams) = x := by omega
    rw [hadd] at hx
    simp [gt_iff_lt, hgt, hnz, Nat.ne_of_gt hgt, hlx] at hx
  obtain ⟨kCp, stCp, hrunCp, hpcCp, hothCp, _, houtCp, hslCp⟩ :=
    copyParamsR_sim env L fl hfl halSp' hargAl hlimSp' htopSp' hspLeFrame vs (by rw [hvslen]; exact hargsValid)
      liveEntry hnoClobP hargsGe
      fd.nparams (by omega) hnpLeNl preCp (cZero ++ cT5 ++ tailCode) hlinkCp stP hpcP hspP ht0P hargWordsP
  let preZr := preCp ++ cCopy
  have hlinkZr : lkm.linkSpec (preZr ++ cZero ++ (cT5 ++ tailCode)) = .ok (env.code, env.labels) := by
    simpa [preZr, List.append_assoc] using hlinkCp
  have hspCp : stCp.getReg AbiReg.sp = sp' :=
    (hothCp _ (by decide) (by decide) (hnotAlloc_of_res _ (by simp [reservedAbiRegs]))).trans hspP
  obtain ⟨kZr, stZr, hrunZr, hpcZr, hothZr, houtZr, hkeepZr, hzeroZr⟩ :=
    zeroLocalsR_sim env L fl hfl fd halSp' htopSp' liveEntry hnoClobParam hnoClobLocal (fl.nlocals - fd.nparams) (by omega)
      preZr (cT5 ++ tailCode) hlinkZr stCp (by simpa [preZr, lkm.totalSize_append] using hpcCp) hspCp
  have hothPToZr : ∀ r, r ≠ AbiReg.t2 → r ≠ AbiReg.t4 → r ∉ fl.alloc.map Prod.snd → stZr.getReg r = stP.getReg r :=
    fun r hr2 hr4 hrna => (hothZr r hr2 hrna).trans (hothCp r hr2 hr4 hrna)
  have hgpZr : stZr.getReg AbiReg.gp = L.T :=
    (hothPToZr _ (by decide) (by decide) (hnotAlloc_of_res _ (by simp [reservedAbiRegs]))).trans hgpP
  let preT5 := preZr ++ cZero
  have hlinkT5 : lkm.linkSpec (preT5 ++ cT5 ++ tailCode) = .ok (env.code, env.labels) := by
    simpa [preT5, List.append_assoc] using hlinkZr
  have hpcZr' : stZr.pc = BitVec.ofNat 64 (4 * lkm.totalSize preT5) := by
    rw [lkm.totalSize_append preZr cZero]
    exact hpcZr
  have ht5Step :
      ∃ kT5 stCL,
        RV64.run env.rom kT5 stZr = .cont stCL ∧
        stCL.pc = BitVec.ofNat 64 (4 * lkm.totalSize (preT5 ++ cT5)) ∧
        T5GpOk L fl stCL ∧
        (∀ r, r ≠ AbiReg.t5 → stCL.getReg r = stZr.getReg r) ∧
        stCL.mem = stZr.mem := by
    cases ht5u : fl.useT5Gp with
    | false =>
      have hc : cT5 = [] := by simp [cT5, ht5u]
      exact ⟨0, stZr, rfl, by rw [hc, List.append_nil]; exact hpcZr',
        (fun h => by rw [ht5u] at h; cases h), fun _ _ => rfl, rfl⟩
    | true =>
      have hc : cT5 = [Asm.addi AbiReg.t5 AbiReg.gp 2047#12] := by simp [cT5, ht5u]
      have hlinkA : lkm.linkSpec (preT5 ++ [Asm.addi AbiReg.t5 AbiReg.gp 2047#12] ++ tailCode) =
          .ok (env.code, env.labels) := by rw [← hc]; exact hlinkT5
      obtain ⟨hrunA, hpcA, ht5A, hothA, hmemA⟩ :=
        run_aluImm_rd_step env preT5 tailCode .addi AbiReg.t5 AbiReg.gp 2047#12 (by decide) hlinkA stZr hpcZr'
      let stCL := stepReg stZr AbiReg.t5 (evalAluImm .addi (stZr.getReg AbiReg.gp) 2047#12)
        (BitVec.ofNat 64 (4 * (lkm.totalSize preT5 + 1)))
      have ht5Val : stCL.getReg AbiReg.t5 = L.T + 2047#64 := by
        rw [ht5A]; change stZr.getReg AbiReg.gp + sextImm12 2047#12 = L.T + 2047#64
        rw [hgpZr, sextImm12_ofNat_lt 2047 (by omega)]
      exact ⟨1, stCL, hrunA, by rw [hpcA, hc]; simp only [lkm.totalSize_append, Asm.addi, lkm.totalSize_instr],
        fun _ => ht5Val, hothA, hmemA⟩
  obtain ⟨kT5, stCL, hrunT5, hpcCL, ht5CL, hothT5, hmemT5⟩ := ht5Step
  have hpcBody : stCL.pc = BitVec.ofNat 64 (4 * lkm.totalSize (preFn ++ fnPrologueAsmR f fd fl)) := by
    have hpe : preFn ++ fnPrologueAsmR f fd fl = preT5 ++ cT5 := by
      dsimp only [preT5, preZr, preCp, pre1]; rw [hcfDecomp]; simp only [List.append_assoc]
    rw [hpe]; exact hpcCL
  have hothPToCL : ∀ r, r ≠ AbiReg.t2 → r ≠ AbiReg.t4 → r ≠ AbiReg.t5 → r ∉ fl.alloc.map Prod.snd → stCL.getReg r = stP.getReg r :=
    fun r hr2 hr4 hr5 hrna => (hothT5 r hr5).trans (hothPToZr r hr2 hr4 hrna)
  have houtCZ : MemEqOutside (localsTempSpanR fl sp') stP.mem stCL.mem := by
    rw [hmemT5]; exact houtCp.trans houtZr
  have hlocSubFrame : (localsTempSpanR fl sp').sub (frameSpanR fl sp') := by
    intro a ⟨l, hl, ha⟩; subst ha; dsimp only [localsTempSpanR] at hl ⊢
    refine ⟨8 * fl.protectedSlots + l, by dsimp only [frameSpanR, FrameLayout.frameSlots]; omega, ?_⟩
    dsimp only [frameSpanR]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have hpreToCL : MemEqOutside (frameSpanR fl sp') st.mem stCL.mem := hmemEqP.trans (houtCZ.mono hlocSubFrame)
  have hpreMaskCL : ProgMemOutside (CallWriteMask L callerSp) st.mem stCL.mem := by
    refine ProgMemOutside.of_memEqOutside ?_ hpreToCL
    intro a ha
    exact Or.inl ⟨frameSpanR_sub_stackSpan L hlimSp' htopSp' _ ha,
      Nat.lt_of_lt_of_le (frameSpanR_elem_lt hframeValid ha) hspLeFrame⟩
  have hmCL : ProgMemRel env.tab L stCL.mem m :=
    ProgMemRel.of_stack_eqOutside (frameSpanR_sub_stackSpan L hlimSp' htopSp') hpreToCL hm
  have hhdrCL : TabHeaderOk L stCL.mem := hhdr.of_callWriteMask L hpreMaskCL
  have hraSlotCL : fl.isLeaf = false → readWord64 stCL.mem sp' = callerRa := fun hnl => by
    have hslot0 : 0 < fl.protectedSlots := by
      dsimp only [FrameLayout.protectedSlots, FrameLayout.raSlots]; rw [hnl]
      simp only [Bool.false_eq_true, ↓reduceIte]; omega
    have hdisj := protected_disj_localsTempR hframeValid hslot0
    have hsp0 : sp' = sp' + BitVec.ofNat 64 (8 * 0) := (BitVec.add_zero sp').symm
    rw [hsp0, MemEqOutside.readWord64_eq houtCZ _ hdisj, ← hsp0]
    exact hraSlotP hnl
  have hsavedCL : ∀ i (hi : i < fl.savedRegs.length),
      readWord64 stCL.mem (sp' + BitVec.ofInt 64 (fl.savedOff i)) = st.getReg (fl.savedRegs[i]'hi) := by
    intro i hi
    have hslot : fl.raSlots + i < fl.protectedSlots := by simp [FrameLayout.protectedSlots]; omega
    rw [savedOff_ofInt, MemEqOutside.readWord64_eq houtCZ _ (protected_disj_localsTempR hframeValid hslot),
      ← savedOff_ofInt]
    exact hsavedP i hi
  have hfCL : ProgFrameOkLive L fl sp' stCL (Locals.init vs) liveEntry := by
    intro x hx hlive
    by_cases hxp : x < fd.nparams
    · have h1 := hslCp x hxp hlive
      have h2 := hkeepZr x hxp hlive
      have hinit : (Locals.init vs x).toBitVec = (vs[x]!).toBitVec := by
        simp [Locals.init, List.getD, show x < vs.length by omega]
      rw [hinit]
      cases hlx : fl.alloc.lookup x with
      | some r =>
        rw [hlx] at h1 h2; dsimp only at h1 h2 ⊢
        rw [hothT5 r (allowedRegs_ne_t5 (regAllocValid_lookup hfl.valid hlx).2.1)]
        exact h2.trans h1
      | none =>
        rw [hlx] at h1 h2; dsimp only at h1 h2 ⊢; intro hmx; rw [hmemT5]; exact (h2 hmx).trans (h1 hmx)
    · have hnz : varNeedsZeroInit fd x = true := stmtVarCallFree_imp_varNeedsZeroInit fd x hlive
      have hz := hzeroZr x (by omega) (by omega) hlive hnz
      have hge : vs.length ≤ x := by rw [hvslen]; exact Nat.le_of_not_lt hxp
      have hinit : (Locals.init vs x).toBitVec = 0#64 := by
        simp [Locals.init, List.getD, List.getElem?_eq_none hge]
      rw [hinit]
      cases hlx : fl.alloc.lookup x with
      | some r =>
        rw [hlx] at hz; dsimp only at hz ⊢
        rw [hothT5 r (allowedRegs_ne_t5 (regAllocValid_lookup hfl.valid hlx).2.1)]
        exact hz
      | none =>
        rw [hlx] at hz; dsimp only at hz ⊢; intro hmx; rw [hmemT5]; exact hz hmx
  exact ⟨_, stCL, run_trans (run_trans (run_trans hrunP hrunCp) hrunZr) hrunT5, hpcBody,
    (hothPToCL _ (by decide) (by decide) (by decide) (hnotAlloc_of_res _ (by simp [reservedAbiRegs]))).trans hgpP,
    ht5CL,
    (hothPToCL _ (by decide) (by decide) (by decide) (hnotAlloc_of_res _ (by simp [reservedAbiRegs]))).trans hspP,
    (hothPToCL _ (by decide) (by decide) (by decide) (hnotAlloc_of_res _ (by simp [reservedAbiRegs]))).trans hs0P,
    (hothPToCL _ (by decide) (by decide) (by decide) (hnotAlloc_of_res _ (by simp [reservedAbiRegs]))).trans hs2P,
    fun _ => (hothPToCL _ (by decide) (by decide) (by decide) (hnotAlloc_of_res _ (by simp [reservedAbiRegs]))).trans hraP,
    hraSlotCL,
    fun r hr hns => (hothPToCL r (allowedRegs_ne_t2 (isLeaf := false) hr) (allowedRegs_ne_t4 (isLeaf := false) hr)
      (allowedRegs_ne_t5 (isLeaf := false) hr) (hnotAlloc_unsaved r hr hns)).trans (hcalP r hr),
    hsavedCL, hpreMaskCL, hmCL, hhdrCL, hfCL⟩

private theorem compileFn_epilogueR_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab)
    (fl : FrameLayout) (hfl : FrameLayoutOk fl)
    {sp callerSp callerRa : BitVec 64} {retPc b : Nat}
    (calleeVals : Reg → BitVec 64)
    (hal : isAligned sp 8 = true)
    (hspEq : callerSp = sp + BitVec.ofInt 64 fl.frameBytes)
    (hraAl : callerRa &&& ~~~1#64 = BitVec.ofNat 64 (4 * retPc))
    (epilogue : String) (preE postE : List AsmItem)
    (hlink : lkm.linkSpec (preE ++ ([Asm.lbl epilogue] ++ framePopItems fl ++ [Asm.ret]) ++ postE) =
      .ok (env.code, env.labels))
    (st : State)
    (hpc : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize preE))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = sp)
    (hs0 : st.getReg AbiReg.s0 = BitVec.ofNat 64 b)
    (hraLeaf : fl.isLeaf = true → st.getReg AbiReg.ra = callerRa)
    (hraSlot : fl.isLeaf = false → readWord64 st.mem sp = callerRa)
    (hcalUnsaved : ∀ r ∈ calleeSavedBank, r ∉ fl.savedRegs → st.getReg r = calleeVals r)
    (hcalSaved : ∀ i (hi : i < fl.savedRegs.length),
      readWord64 st.mem (sp + BitVec.ofInt 64 (fl.savedOff i)) = calleeVals (fl.savedRegs[i]'hi))
    {vs : List _root_.L.Word} (hres : ResultsInState env.tab L st vs) :
    ∃ k st',
      RV64.run env.rom k st = .cont st' ∧
      st'.pc = BitVec.ofNat 64 (4 * retPc) ∧
      st'.getReg AbiReg.gp = L.T ∧
      st'.getReg AbiReg.sp = callerSp ∧
      st'.getReg AbiReg.s0 = BitVec.ofNat 64 b ∧
      st'.getReg AbiReg.s1 = st.getReg AbiReg.s1 ∧
      st'.getReg AbiReg.s2 = st.getReg AbiReg.s2 ∧
      (∀ r ∈ calleeSavedBank, st'.getReg r = calleeVals r) ∧
      st'.mem = st.mem ∧
      ResultsInState env.tab L st' vs := by
  let pre1 := preE ++ [Asm.lbl epilogue]
  have hpc0 : st.pc = BitVec.ofNat 64 (4 * lkm.totalSize pre1) := by
    rw [hpc]; dsimp only [pre1]
    simp only [lkm.totalSize_append, show lkm.totalSize [Asm.lbl epilogue] = 0 from by simp only [Asm.lbl, lkm.totalSize_label], Nat.add_zero]
  have hlinkPop : lkm.linkSpec (pre1 ++ framePopItems fl ++ ([Asm.ret] ++ postE)) = .ok (env.code, env.labels) := by
    simpa [pre1, List.append_assoc] using hlink
  obtain ⟨kPop, stPop, hrunPop, hpcPop, hgpPop, hspPop, hraPop, hs0Pop, hs1Pop, hs2Pop, hcalPop, hresPop, hmemPop⟩ :=
    framePopItems_sim env L fl hfl calleeVals hal hspEq pre1 ([Asm.ret] ++ postE) hlinkPop st hpc0
      hgp hsp hs0 hraLeaf hraSlot hcalUnsaved hcalSaved
  let preRet := pre1 ++ framePopItems fl
  have hlinkRet : lkm.linkSpec (preRet ++ [Asm.ret] ++ postE) = .ok (env.code, env.labels) := by
    simpa [preRet, List.append_assoc] using hlinkPop
  have hpcRet : stPop.pc = BitVec.ofNat 64 (4 * lkm.totalSize preRet) := by
    simpa [preRet, lkm.totalSize_append] using hpcPop
  have hltRet64 : 4 * lkm.totalSize preRet < 2 ^ 64 := by
    have h := linkResolved_sub_pc64 env preRet [Asm.ret] postE hlinkRet
    rw [show lkm.totalSize [Asm.ret] = 1 from by simp only [Asm.ret, lkm.totalSize_instr]] at h; omega
  have hstepRet := step_item_ret_lm lkm env.hrom preRet postE hlinkRet hltRet64 stPop hpcRet
  let stFin : State := { stPop with pc := stPop.getReg AbiReg.ra &&& ~~~1#64 }
  refine ⟨kPop + 1, stFin,
    by rw [run_add, hrunPop]; exact run_one_cont _ _ stFin hstepRet,
    by change stPop.getReg AbiReg.ra &&& ~~~1#64 = _; rw [hraPop, hraAl],
    hgpPop, hspPop, hs0Pop, hs1Pop, hs2Pop, hcalPop, hmemPop, ?_⟩
  refine resultsInState_mem (S := ⟨0#64, 0⟩) (fun i hi => hresPop i (Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)))
    (fun _ _ _ _ _ ⟨_, hk, _⟩ => Nat.not_lt_zero _ hk) (fun _ _ => by change stPop.mem _ = st.mem _; rw [hmemPop]) hres

private def CodeEnvGen.withLinkModel {lkm : LinkModel} (env : CodeEnvGen lkm) (lkm' : LinkModel) : CodeEnvGen lkm' :=
  { tab := env.tab
    code := env.code
    labels := env.labels
    rom := env.rom
    hrom := env.hrom
    hcode64 := env.hcode64
    errTarget := env.errTarget
    herrLbl := env.herrLbl
    abortTarget := env.abortTarget
    habortLbl := env.habortLbl
    exhaustedTarget := env.exhaustedTarget
    hexhaustedLbl := env.hexhaustedLbl }

private theorem compileFn_core_sim {lkm lkm' : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab) (p : _root_.L.Prog)
    (hpOk : progOkB env.tab p = true) (hpArgs : progArgsOkB p = true)
    (hFns : ∀ {g : FnName} {gd : FunDecl}, p.lookup g = some gd → ∃ entryPc, lookupLabel env.labels (fnLabel g) = some entryPc)
    (b : Nat) (hcall : ∀ b', b' < b → FnCallSimGenCallee env L p b')
    (f : FnName) (fd : FunDecl) (fl : FrameLayout)
    (hfl : FrameLayoutOk fl) (hargsValid : regAllocArgsValid fl.isLeaf fd.nparams fl.alloc = true)
    (hgraphValid : regAllocGraphValid fl.isLeaf fl.nlocals fl.alloc fd = true)
    (hspilledUsed : ∀ x, x < fl.nlocals → fl.alloc.lookup x = none → stmtUsesVar x fd.body = true → x ∈ fl.spilledVars)
    (hfbLe : 8 * fl.frameSlots ≤ fnFrameBytes fd)
    (hnlEq : fl.nlocals = numLocalsFn fd) (hleafEq : fl.isLeaf = !stmtHasCall fd.body)
    (hutEq : fl.usedTemps = usedTempsStmtR fl.isLeaf fl.alloc fd.body)
    (hCopyScan : fl.useT5Gp = true → stmtHasCopyScan fd.body = false)
    (habort0 : stmtHasAbort0 fd.body = true → Abort0StubOk env (fnLabel f))
    (hflook : p.lookup f = some fd)
    (prePad postPad preBodyRt bodyCodeRt postStub : List AsmItem)
    (hlinkPad : lkm'.linkSpec (prePad ++ (fnPrologueAsmR f fd fl ++
      (compileSR env.tab fl (fnLabel f) 0 none s!"{fnLabel f}_epilogue" (!stmtMayFallthrough fd.body) fd.body).1) ++ postPad) =
      .ok (env.code, env.labels))
    (hlinkBodyRt : lkm.linkSpec (preBodyRt ++ bodyCodeRt ++
      (([Asm.lbl s!"{fnLabel f}_ret0"] ++
        (if stmtMayFallthrough fd.body then copyTempsToResultsR env.tab fl 0 0 else [])) ++
       ([Asm.lbl s!"{fnLabel f}_epilogue"] ++ framePopItems fl ++ [Asm.ret]) ++ postStub)) =
      .ok (env.code, env.labels))
    (hpreBodySz : lkm'.totalSize (prePad ++ fnPrologueAsmR f fd fl) = lkm.totalSize preBodyRt)
    (hbodySz : lkm'.totalSize (compileSR env.tab fl (fnLabel f) 0 none s!"{fnLabel f}_epilogue" (!stmtMayFallthrough fd.body) fd.body).1 =
      lkm.totalSize bodyCodeRt)
    (vs : List _root_.L.Word) (m : _root_.L.Mem)
    (callerSp callerRa argsPtr : BitVec 64) (retPc : Nat)
    (hvslen : vs.length = fd.nparams) (hb64 : b < 2 ^ 64)
    (hlim : L.stackLimit.toNat + fnFrameBytes fd + stackNeedB p b fd.body { mem := m, loc := Locals.init vs } ≤ callerSp.toNat)
    (hctop : callerSp.toNat ≤ L.stackTop.toNat)
    (hcal : isAligned callerSp 8 = true) (hargAl : isAligned argsPtr 8 = true)
    (hraAl : callerRa &&& ~~~1#64 = BitVec.ofNat 64 (4 * retPc))
    (hargsGe : ∀ j, j < vs.length → ∀ k, k < 8 →
      callerSp.toNat ≤ (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)) + BitVec.ofNat 64 k).toNat ∨
      ¬L.stackSpan.contains (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)) + BitVec.ofNat 64 k))
    (entryPc : Nat) (st : State)
    (hEntryLbl : lookupLabel env.labels (fnLabel f) = some entryPc)
    (hpc : st.pc = BitVec.ofNat 64 (4 * entryPc))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = callerSp)
    (hra : st.getReg AbiReg.ra = callerRa) (hs0 : st.getReg AbiReg.s0 = BitVec.ofNat 64 b)
    (ht0 : maxRes < fd.nparams → st.getReg AbiReg.t0 = argsPtr)
    (hm : ProgMemRel env.tab L st.mem m) (hhdr : TabHeaderOk L st.mem)
    (hargWords : ∀ j, j < vs.length →
      (if j < maxRes then st.getReg (resReg j)
       else readWord64 st.mem (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)))) = (vs[j]!).toBitVec) :
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
        ProgMemOutside (CallWriteMask L callerSp) st.mem r'.mem := by
  let env' := env.withLinkModel lkm'
  let pfx := fnLabel f
  let epilogueZero := s!"{pfx}_ret0"
  let epilogue := s!"{pfx}_epilogue"
  let canTailElide := !stmtMayFallthrough fd.body
  let bodyCode := (compileSR env.tab fl pfx 0 none epilogue canTailElide fd.body).1
  let fallCode := [Asm.lbl epilogueZero] ++
    (if stmtMayFallthrough fd.body then copyTempsToResultsR env.tab fl 0 0 else [])
  let epiCode := [Asm.lbl epilogue] ++ framePopItems fl ++ [Asm.ret]
  have hlinkPro : lkm'.linkSpec (prePad ++ fnPrologueAsmR f fd fl ++ (bodyCode ++ postPad)) = .ok (env'.code, env'.labels) := by
    simpa [env', CodeEnvGen.withLinkModel, bodyCode, pfx, epilogue, canTailElide, List.append_assoc] using hlinkPad
  let preBody := prePad ++ fnPrologueAsmR f fd fl
  have hlinkBody : lkm'.linkSpec (preBody ++ bodyCode ++ postPad) = .ok (env'.code, env'.labels) := by
    simpa [preBody, env', CodeEnvGen.withLinkModel, bodyCode, pfx, epilogue, canTailElide, List.append_assoc] using hlinkPad
  have hepiLbl : lookupLabel env.labels epilogue = some (lkm.totalSize (preBodyRt ++ bodyCodeRt ++ fallCode)) :=
    linkResolved_lbl_lm lkm (preBodyRt ++ bodyCodeRt ++ fallCode) epilogue _
      (by simpa [fallCode, epiCode, pfx, epilogueZero, epilogue, List.append_assoc] using hlinkBodyRt)
  have hcall' : ∀ b', b' < b → FnCallSimGenCallee env' L p b' := fun b' hb' => hcall b' hb'
  have hFnLbls : ∀ {g : FnName} {gd : FunDecl}, p.lookup g = some gd →
      ∃ pc, lookupLabel env'.labels (fnLabel g) = some pc := fun hfl' =>
    hFns hfl'
  have hnpLeNl : fd.nparams ≤ fl.nlocals := by rw [hnlEq]; exact numLocalsFn_ge_nparams fd
  obtain ⟨kPro, stCL, hrunPreBody, hpcBody, hgpCL, ht5CL, hspCL, hs0CL', hs2CL,
      hraLeafCL, hraSlotCL, hcalUnsavedCL, hcalSavedCL, hpreMaskCL, hmCL, hhdrCL, hfCL⟩ :=
    compileFn_prologueR_sim env' L f fd fl hfl hargsValid hgraphValid hfbLe hnpLeNl prePad (bodyCode ++ postPad) hlinkPro
      vs m callerSp callerRa argsPtr hvslen (by omega) hctop hcal hargAl hargsGe entryPc st
      hEntryLbl hpc hgp hsp hra ht0 hm hhdr hargWords
  let sp' := callerSp - BitVec.ofNat 64 (8 * fl.frameSlots)
  have hframeLeSp : 8 * fl.frameSlots ≤ callerSp.toNat := by omega
  have hsp'ToNat : sp'.toNat = callerSp.toNat - 8 * fl.frameSlots :=
    bitvec_sub_mul8_toNat callerSp fl.frameSlots hframeLeSp
  have halSp' : isAligned sp' 8 = true := isAligned8_sub_mul8 callerSp hcal fl.frameSlots hframeLeSp
  have hlimSp' : L.stackLimit.toNat ≤ sp'.toNat := by rw [hsp'ToNat]; omega
  have htopSp' : sp'.toNat + 8 * fl.frameSlots ≤ L.stackTop.toNat := by rw [hsp'ToNat]; omega
  have hspLeFrame : sp'.toNat + 8 * fl.frameSlots ≤ callerSp.toNat := by rw [hsp'ToNat]; omega
  have hs0CL : stCL.getReg AbiReg.s0 = BitVec.ofNat 64 b := hs0CL'.trans hs0
  have hfdOk : stmtOkB env.tab p fl.nlocals false fd.body = true := by
    rw [hnlEq]
    simp only [progOkB, Bool.and_eq_true, List.all_eq_true] at hpOk
    exact hpOk.2 (f, fd) (mem_of_lookup_some p hflook)
  have hfdArgs : stmtArgsOkB p fd.body = true := by
    simp only [progArgsOkB, List.all_eq_true] at hpArgs
    exact hpArgs (f, fd) (mem_of_lookup_some p hflook)
  have hVfBody : StmtVarsInFrame fl fd.body := fun x hx hnone =>
    hspilledUsed x (stmtUsesVar_lt_of_stmtOkB hfdOk hx) hnone hx
  have hLeafFn : fl.isLeaf = true → stmtHasCall fd.body = false := fun hl => by
    rw [hleafEq] at hl
    simpa using hl
  have hTailBody : canTailElide = true → lkm'.totalSize preBody + lkm'.totalSize bodyCode =
      lkm.totalSize (preBodyRt ++ bodyCodeRt ++ fallCode) := by
    intro ht
    have hmfF : stmtMayFallthrough fd.body = false := by
      dsimp only [canTailElide] at ht; simpa using ht
    have hfall0 : lkm.totalSize fallCode = 0 := by
      simp [fallCode, hmfF, Asm.lbl, lkm.totalSize_label]
    rw [hpreBodySz, hbodySz, lkm.totalSize_append (preBodyRt ++ bodyCodeRt) fallCode, hfall0, Nat.add_zero,
      lkm.totalSize_append preBodyRt bodyCodeRt]
  have ⟨hSafeBody, hCallResBody⟩ := regAllocGraphValid_extract hgraphValid
  let tco : TcoCtx := ⟨retPc, callerRa, fun r => st.getReg r, hraAl⟩
  have htcoCL : TcoStateOk fl sp' tco stCL := ⟨hraLeafCL, hraSlotCL, hcalUnsavedCL, hcalSavedCL⟩
  have habort0' : stmtHasAbort0 fd.body = true → Abort0StubOk env' pfx := habort0
  have hbody := progExecB_step_lbls env' L p hpOk hpArgs hFnLbls b fd.body hcall' fl hfl
    (fun _ => false) (fun _ => false) tco m (Locals.init vs)
    sp' pfx 0 none epilogue (lkm.totalSize (preBodyRt ++ bodyCodeRt ++ fallCode)) canTailElide preBody postPad
    hfdOk hfdArgs hVfBody (Nat.le_of_eq hutEq.symm) hLeafFn hSafeBody hCallResBody hCopyScan habort0'
    hb64 halSp' (by rw [hsp'ToNat]; omega) htopSp'
    hepiLbl (fun _ h => by cases h) hTailBody hlinkBody stCL hpcBody hgpCL ht5CL hspCL hs0CL hmCL hfCL hhdrCL htcoCL
  have hpresPreTramp : PreservedTramp st stCL := ⟨hgpCL.trans hgp.symm, hs2CL⟩
  have hspEqCancel : callerSp = sp' + BitVec.ofInt 64 fl.frameBytes := by
    rw [frameBytesR_toNat_eq fl]
    exact (BitVec.sub_add_cancel callerSp (BitVec.ofNat 64 (8 * fl.frameSlots))).symm
  -- Helper: protected slots survive any `ProgMemOutside (FnWriteMaskR L fl sp')`
  have hprotSurvive : ∀ {m1 : ByteMem}, ProgMemOutside (FnWriteMaskR L fl sp') stCL.mem m1 →
      (fl.isLeaf = false → readWord64 m1 sp' = callerRa) ∧
      (∀ i (hi : i < fl.savedRegs.length),
        readWord64 m1 (sp' + BitVec.ofInt 64 (fl.savedOff i)) = st.getReg (fl.savedRegs[i]'hi)) := by
    intro m1 hout
    refine ⟨fun hnl => ?_, fun i hi => ?_⟩
    · have hslot0 : 0 < fl.protectedSlots := by
        dsimp only [FrameLayout.protectedSlots, FrameLayout.raSlots]; rw [hnl]
        simp only [Bool.false_eq_true, ↓reduceIte]; omega
      have hsp0 : sp' = sp' + BitVec.ofNat 64 (8 * 0) := (BitVec.add_zero sp').symm
      rw [← hraSlotCL hnl]
      change readWord64 m1 sp' = readWord64 stCL.mem sp'
      exact ProgMemOutside.readWord64_eq hout sp' fun k hk => by
        have hnp := @fnWriteMaskR_not_protected _ L fl sp' hlimSp' htopSp' 0 hslot0 k hk
        rwa [← hsp0] at hnp
    · have hslot : fl.raSlots + i < fl.protectedSlots := by simp [FrameLayout.protectedSlots]; omega
      rw [← hcalSavedCL i hi, savedOff_ofInt]
      exact hout.readWord64_eq _ fun k hk => fnWriteMaskR_not_protected L hlimSp' htopSp' hslot hk
  cases hxInit : execB p b fd.body { mem := m, loc := Locals.init vs } with
  | error errInit =>
    rw [hxInit] at hbody
    cases errInit with
    | outOfFuel =>
      obtain ⟨kB, rB, hrunB, hpcB, hpresB, hpmB⟩ := hbody
      exact ⟨_, rB, run_trans hrunPreBody hrunB, hpcB, hpresPreTramp.trans hpresB,
        hpreMaskCL.trans (by rw [hspEqCancel]; exact hpmB)⟩
    | abort code =>
      obtain ⟨kB, rB, hrunB, hpcB, ha0B, hpresB, hpmB⟩ := hbody
      exact ⟨_, rB, run_trans hrunPreBody hrunB, hpcB, ha0B, hpresPreTramp.trans hpresB,
        hpreMaskCL.trans (by rw [hspEqCancel]; exact hpmB)⟩
    | oob =>
      obtain ⟨kB, rB, hrunB, hpcB, hpresB, hpmB⟩ := hbody
      exact ⟨_, rB, run_trans hrunPreBody hrunB, hpcB, hpresPreTramp.trans hpresB,
        hpreMaskCL.trans (by rw [hspEqCancel]; exact hpmB)⟩
    | noFun fn =>
      obtain ⟨kB, rB, hrunB, hpcB, hpresB, hpmB⟩ := hbody
      exact ⟨_, rB, run_trans hrunPreBody hrunB, hpcB, hpresPreTramp.trans hpresB,
        hpreMaskCL.trans (by rw [hspEqCancel]; exact hpmB)⟩
  | ok resInit =>
    rcases resInit with ⟨sig, st', b'⟩
    rw [hxInit] at hbody; dsimp only
    cases sig with
    | brk =>
      obtain ⟨tgt, hnone, _⟩ := hbody; cases hnone
    | ret vsRet =>
      rcases hbody with hbody | hbody
      · obtain ⟨retPc', kB, rB, hlkpE, hrunB, hpcB, hvslenRet, hpresB, hs0B, hbLe, hmB, hresB, houtB, _⟩ := hbody
        rcases hpcB with hpcB | ⟨hl, hfr, hpcRet⟩
        · change lookupLabel env.labels epilogue = some retPc' at hlkpE
          rw [hepiLbl] at hlkpE
          have hpcBEq : rB.pc = BitVec.ofNat 64 (4 * lkm.totalSize (preBodyRt ++ bodyCodeRt ++ fallCode)) := by
            rw [hpcB, Option.some.inj hlkpE.symm]
          have hlinkE : lkm.linkSpec ((preBodyRt ++ bodyCodeRt ++ fallCode) ++ epiCode ++ postStub) = .ok (env.code, env.labels) := by
            simpa [fallCode, epiCode, pfx, epilogueZero, epilogue, List.append_assoc] using hlinkBodyRt
          have ⟨hraSlotB, hcalSavedB⟩ := hprotSurvive houtB
          obtain ⟨kE, rE, hrunE, hpcE, hgpE, hspE, hs0E, _, hs2E, hcalE, hmemE, hresE⟩ :=
            compileFn_epilogueR_sim env L fl hfl (fun r => st.getReg r) halSp' hspEqCancel hraAl epilogue
              (preBodyRt ++ bodyCodeRt ++ fallCode) postStub hlinkE rB hpcBEq
              (hpresB.abi.gp.trans hgpCL) (hpresB.abi.sp.trans hspCL) hs0B
              (fun hl => (hpresB.leafRa hl).trans (hraLeafCL hl)) hraSlotB
              (fun r hr hns => (hpresB.callee r hr hns).trans (hcalUnsavedCL r hr hns)) hcalSavedB hresB
          have houtAll : ProgMemOutside (CallWriteMask L callerSp) st.mem rE.mem := by
            rw [hmemE]; exact hpreMaskCL.trans (ProgMemOutside.mono (fnWriteMaskR_sub_callWriteMask L hspLeFrame) houtB)
          exact ⟨_, rE, run_trans (run_trans hrunPreBody hrunB) hrunE,
            hpcE, hgpE, hspE, hs2E.trans (hpresB.abi.s2.trans hs2CL),
            hcalE, hs0E, hbLe, (by intro h; cases h), hvslenRet,
            (by rw [hmemE]; exact hmB), hhdr.of_callWriteMask L houtAll, hresE, houtAll⟩
        · obtain ⟨_, hsr, _, _⟩ := hfl.frameSlots_zero_props hfr
          have hspEq' : callerSp = sp' := by
            rw [hspEqCancel, FrameLayout.frameBytes, hfr]; simp
          have hpcFin : rB.pc = BitVec.ofNat 64 (4 * retPc) := by
            rw [hpcRet, hraLeafCL hl, hraAl]
          have houtAll : ProgMemOutside (CallWriteMask L callerSp) st.mem rB.mem :=
            hpreMaskCL.trans (ProgMemOutside.mono (fnWriteMaskR_sub_callWriteMask L hspLeFrame) houtB)
          exact ⟨_, rB, run_trans hrunPreBody hrunB,
            hpcFin, hpresB.abi.gp.trans hgpCL, (hpresB.abi.sp.trans hspCL).trans hspEq'.symm,
            hpresB.abi.s2.trans hs2CL,
            (fun r hr => (hpresB.callee r hr (by rw [hsr]; simp)).trans (hcalUnsavedCL r hr (by rw [hsr]; simp))),
            hs0B, hbLe, (by intro h; cases h), hvslenRet,
            hmB, hhdr.of_callWriteMask L houtAll, hresB, houtAll⟩
      · obtain ⟨kB, rB, hrunB, hpcB, hgpB, hspB, hs2B, hcalB, hs0B, hbLe, hvslenRet, hmB, hresB, houtB, hhdrB⟩ := hbody
        have houtAll : ProgMemOutside (CallWriteMask L callerSp) st.mem rB.mem :=
          hpreMaskCL.trans (by rw [hspEqCancel]; exact houtB)
        exact ⟨_, rB, run_trans hrunPreBody hrunB, hpcB, hgpB, hspB.trans hspEqCancel.symm,
          hs2B.trans hs2CL, hcalB, hs0B, hbLe, (by intro h; cases h),
          hvslenRet, hmB, hhdrB, hresB, houtAll⟩
    | normal =>
      cases hmf : stmtMayFallthrough fd.body with
      | false =>
        exact False.elim (execB_not_normal_of_not_fallthrough p fd.body b { mem := m, loc := Locals.init vs } st' b' hmf hxInit)
      | true =>
        obtain ⟨kB, rB, hrunB, hpcB, hpresB, hs0B, hbLe, hmB, _, houtB, _⟩ := hbody
        let preFall := preBodyRt ++ bodyCodeRt
        have hfallEq : fallCode = [Asm.lbl epilogueZero] ++ copyTempsToResultsR env.tab fl 0 0 := by simp [fallCode, hmf]
        have hpcB' : rB.pc = BitVec.ofNat 64 (4 * lkm.totalSize (preFall ++ [Asm.lbl epilogueZero])) := by
          have htw : lkm.totalSize (preFall ++ [Asm.lbl epilogueZero]) = lkm'.totalSize preBody + lkm'.totalSize bodyCode := by
            dsimp only [preFall]
            rw [lkm.totalSize_append (preBodyRt ++ bodyCodeRt), lkm.totalSize_append preBodyRt bodyCodeRt,
              Asm.lbl, lkm.totalSize_label, Nat.add_zero, hpreBodySz, hbodySz]
          rw [hpcB, htw]; rfl
        have hlinkFall : lkm.linkSpec ((preFall ++ [Asm.lbl epilogueZero]) ++ copyTempsToResultsR env.tab fl 0 0 ++ (epiCode ++ postStub)) =
            .ok (env.code, env.labels) := by
          have h := hlinkBodyRt; simp only [hmf, ↓reduceIte] at h
          simpa [preFall, epiCode, pfx, epilogueZero, epilogue, List.append_assoc] using h
        obtain ⟨kF, rF, hrunF, hpcF, hpresF, hraF, hcalF, hresF, houtF⟩ :=
          reg_copyTempsToResultsR_sim env L fl halSp' hlimSp' htopSp' ([] : List _root_.L.Word) (Nat.zero_le _)
            (preFall ++ [Asm.lbl epilogueZero]) (epiCode ++ postStub) hlinkFall rB hpcB'
            (hpresB.abi.gp.trans hgpCL) (hpresB.abi.sp.trans hspCL) (fun _ hidx => by simp at hidx)
        have hpcF' : rF.pc = BitVec.ofNat 64 (4 * lkm.totalSize (preBodyRt ++ bodyCodeRt ++ fallCode)) := by
          rw [hpcF, show ([] : List _root_.L.Word).length = 0 from rfl,
            lkm.totalSize_append preFall, lkm.totalSize_append preBodyRt bodyCodeRt, hfallEq,
            lkm.totalSize_append (preBodyRt ++ bodyCodeRt), lkm.totalSize_append [Asm.lbl epilogueZero],
            lkm.totalSize_append preBodyRt bodyCodeRt, Asm.lbl, lkm.totalSize_label, Nat.add_zero, Nat.zero_add]
        have hlinkE : lkm.linkSpec ((preBodyRt ++ bodyCodeRt ++ fallCode) ++ epiCode ++ postStub) = .ok (env.code, env.labels) := by
          simpa [fallCode, epiCode, pfx, epilogueZero, epilogue, List.append_assoc] using hlinkBodyRt
        have houtFallMask : ProgMemOutside (FnWriteMaskR L fl sp') rB.mem rF.mem :=
          progMemOutside_of_resGlobR L fl sp' (MemEqOutside.mono (resOnlySpan_sub_resGlob L) houtF)
        have houtBF : ProgMemOutside (FnWriteMaskR L fl sp') stCL.mem rF.mem := houtB.trans houtFallMask
        have ⟨hraSlotF, hcalSavedF⟩ := hprotSurvive houtBF
        have hretB := hpresB.toRetRegs hfl
        obtain ⟨kE, rE, hrunE, hpcE, hgpE, hspE, hs0E, _, hs2E, hcalE, hmemE, hresE⟩ :=
          compileFn_epilogueR_sim env L fl hfl (fun r => st.getReg r) halSp' hspEqCancel hraAl epilogue
            (preBodyRt ++ bodyCodeRt ++ fallCode) postStub hlinkE rF hpcF'
            (hpresF.gp.trans (hpresB.abi.gp.trans hgpCL)) (hpresF.sp.trans (hpresB.abi.sp.trans hspCL))
            (hpresF.s0.trans hs0B)
            (fun hl => hraF.trans ((hpresB.leafRa hl).trans (hraLeafCL hl))) hraSlotF
            (fun r hr hns => (hcalF r hr).trans ((hretB.callee r hr hns).trans (hcalUnsavedCL r hr hns)))
            hcalSavedF hresF
        have houtAll : ProgMemOutside (CallWriteMask L callerSp) st.mem rE.mem := by
          rw [hmemE]; exact hpreMaskCL.trans (ProgMemOutside.mono (fnWriteMaskR_sub_callWriteMask L hspLeFrame) houtBF)
        have hmE : ProgMemRel env.tab L rE.mem st'.mem := by
          rw [hmemE]; exact ProgMemRel.of_resOnly L houtF hmB
        exact ⟨_, rE, run_trans (run_trans (run_trans hrunPreBody hrunB) hrunF) hrunE,
          hpcE, hgpE, hspE,
          hs2E.trans (hpresF.s2.trans (hpresB.abi.s2.trans hs2CL)),
          hcalE, hs0E, hbLe, (by intro h; cases h), Nat.zero_le _, hmE, hhdr.of_callWriteMask L houtAll, hresE, houtAll⟩

private theorem compileFnWith_of_body_sim {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab) (p : _root_.L.Prog)
    (allocOf : FnName → FunDecl → RegAlloc)
    (hpOk : progOkB env.tab p = true) (hpArgs : progArgsOkB p = true)
    (hFns : ProgFnsLinkedWithGen env allocOf p)
    (b : Nat) (hcall : ∀ b', b' < b → FnCallSimGenCallee env L p b')
    (f : FnName) (fd : FunDecl) (preFn postFn : List AsmItem)
    (hflook : p.lookup f = some fd)
    (hlinkFn : lkm.linkSpec (preFn ++ compileFnWith (allocOf f fd) env.tab f fd ++ postFn) =
      .ok (env.code, env.labels))
    (vs : List _root_.L.Word) (m : _root_.L.Mem)
    (callerSp callerRa argsPtr : BitVec 64) (retPc : Nat)
    (hvslen : vs.length = fd.nparams) (hb64 : b < 2 ^ 64)
    (hlim : L.stackLimit.toNat + fnFrameBytes fd + stackNeedB p b fd.body { mem := m, loc := Locals.init vs } ≤ callerSp.toNat)
    (hctop : callerSp.toNat ≤ L.stackTop.toNat)
    (hcal : isAligned callerSp 8 = true) (hargAl : isAligned argsPtr 8 = true)
    (hraAl : callerRa &&& ~~~1#64 = BitVec.ofNat 64 (4 * retPc))
    (hargsGe : ∀ j, j < vs.length → ∀ k, k < 8 →
      callerSp.toNat ≤ (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)) + BitVec.ofNat 64 k).toNat ∨
      ¬L.stackSpan.contains (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)) + BitVec.ofNat 64 k))
    (entryPc : Nat) (st : State)
    (hEntryLbl : lookupLabel env.labels (fnLabel f) = some entryPc)
    (hpc : st.pc = BitVec.ofNat 64 (4 * entryPc))
    (hgp : st.getReg AbiReg.gp = L.T) (hsp : st.getReg AbiReg.sp = callerSp)
    (hra : st.getReg AbiReg.ra = callerRa) (hs0 : st.getReg AbiReg.s0 = BitVec.ofNat 64 b)
    (ht0 : maxRes < fd.nparams → st.getReg AbiReg.t0 = argsPtr)
    (hm : ProgMemRel env.tab L st.mem m) (hhdr : TabHeaderOk L st.mem)
    (hargWords : ∀ j, j < vs.length →
      (if j < maxRes then st.getReg (resReg j)
       else readWord64 st.mem (argsPtr + BitVec.ofNat 64 (8 * (j - maxRes)))) = (vs[j]!).toBitVec) :
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
        ProgMemOutside (CallWriteMask L callerSp) st.mem r'.mem := by
  let fl := fnFrameLayoutForWith (allocOf f fd) env.tab fd
  let pfx := fnLabel f
  let epilogueZero := s!"{pfx}_ret0"
  let epilogue := s!"{pfx}_epilogue"
  let errStubLbl := s!"{pfx}_errstub"
  let exhStubLbl := s!"{pfx}_exhstub"
  let abort0Lbl := s!"{pfx}_abort0stub"
  let prologue := fnPrologueAsmR f fd fl
  let bodyCode := (compileSR env.tab fl pfx 0 none epilogue (!stmtMayFallthrough fd.body) fd.body).1
  let hasErr := hasBranchTo errLabel prologue || hasBranchTo errLabel bodyCode
  let hasExh := hasBranchTo exhaustedLabel bodyCode
  let hasAb0 := stmtHasAbort0 fd.body
  let needRetarget := hasErr || hasExh
  let exhSub? : Option String := if hasExh then some exhStubLbl else none
  let rt := retargetColdItem errLabel errStubLbl exhaustedLabel exhSub?
  let fallCode := [Asm.lbl epilogueZero] ++
    (if stmtMayFallthrough fd.body then copyTempsToResultsR env.tab fl 0 0 else [])
  let epiCode := [Asm.lbl epilogue] ++ framePopItems fl ++ [Asm.ret]
  let coldStubs :=
    (if needRetarget then [Asm.lbl errStubLbl, Asm.j errLabel] else []) ++
    (if hasExh then [Asm.lbl exhStubLbl, Asm.j exhaustedLabel] else []) ++
    (if hasAb0 then [Asm.lbl abort0Lbl, Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.j abortLabel] else [])
  let postStub := coldStubs ++ postFn
  have hcfDecomp : compileFnWith (allocOf f fd) env.tab f fd =
      (if needRetarget then (prologue ++ bodyCode).map rt else prologue ++ bodyCode) ++
        fallCode ++ epiCode ++ coldStubs := by
    have hrt_eq : retargetBranchItem errLabel errStubLbl exhaustedLabel exhSub? = rt := by
      funext it; cases it <;> rfl
    simp only [compileFnWith, fnPrologueAsmR, prologue, bodyCode, hasErr, hasExh, hasAb0, needRetarget, exhSub?,
      fallCode, epiCode, coldStubs, fl, pfx, epilogueZero, epilogue, errStubLbl, exhStubLbl, abort0Lbl,
      hrt_eq, List.map_append, List.append_assoc]
  have habort0 : stmtHasAbort0 fd.body = true → Abort0StubOk env pfx := fun hab => by
    have hlinkAb : lkm.linkSpec ((preFn ++
        (if needRetarget then (prologue ++ bodyCode).map rt else prologue ++ bodyCode) ++
        fallCode ++ epiCode ++
        (if needRetarget then [Asm.lbl errStubLbl, Asm.j errLabel] else []) ++
        (if hasExh then [Asm.lbl exhStubLbl, Asm.j exhaustedLabel] else [])) ++
        [Asm.lbl abort0Lbl, Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.j abortLabel] ++ postFn) =
        .ok (env.code, env.labels) := by
      rw [hcfDecomp] at hlinkFn
      simpa [coldStubs, hasAb0, hab, List.append_assoc] using hlinkFn
    exact abort0Stub_sim env pfx _ postFn hlinkAb
  by_cases hrt : needRetarget = true
  · have hlinkCore : lkm.linkSpec (preFn ++ (prologue ++ bodyCode).map rt ++ (fallCode ++ epiCode ++ postStub)) =
        .ok (env.code, env.labels) := by
      rw [hcfDecomp, hrt] at hlinkFn; simpa [postStub, List.append_assoc] using hlinkFn
    let preBodyRt := preFn ++ prologue.map rt
    have hlinkBodyRt : lkm.linkSpec (preBodyRt ++ bodyCode.map rt ++ (fallCode ++ epiCode ++ postStub)) =
        .ok (env.code, env.labels) := by simpa [preBodyRt, List.map_append, List.append_assoc] using hlinkCore
    have hStub1 : ∃ p1 q1, lkm.linkSpec (p1 ++ [AsmItem.label errStubLbl, AsmItem.j errLabel] ++ q1) =
        .ok (env.code, env.labels) :=
      ⟨preBodyRt ++ bodyCode.map rt ++ fallCode ++ epiCode,
       (if hasExh then [Asm.lbl exhStubLbl, Asm.j exhaustedLabel] else []) ++
       (if hasAb0 then [Asm.lbl abort0Lbl, Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.j abortLabel] else []) ++ postFn,
       by simpa [coldStubs, hrt, postStub, Asm.lbl, Asm.j, List.append_assoc] using hlinkBodyRt⟩
    have hStub2 : match exhSub? with
        | some new2 => ∃ p2 q2, lkm.linkSpec (p2 ++ [AsmItem.label new2, AsmItem.j exhaustedLabel] ++ q2) =
            .ok (env.code, env.labels)
        | none => True := by
      dsimp only [exhSub?]
      by_cases hh : hasExh = true
      · simp only [hh, ↓reduceIte]
        refine ⟨preBodyRt ++ bodyCode.map rt ++ fallCode ++ epiCode ++ [Asm.lbl errStubLbl, Asm.j errLabel],
          (if hasAb0 then [Asm.lbl abort0Lbl, Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.j abortLabel] else []) ++ postFn, ?_⟩
        simpa [coldStubs, hrt, postStub, hh, Asm.lbl, Asm.j, List.append_assoc] using hlinkBodyRt
      · simp only [hh, Bool.false_eq_true, ↓reduceIte]
    let lkm' := retargetLinkModel lkm env.code env.labels errLabel errStubLbl exhaustedLabel exhSub?
      preFn (prologue ++ bodyCode) (fallCode ++ epiCode ++ postStub) hlinkCore env.hcode64 hStub1 hStub2
    obtain ⟨prePad, postPad, hlinkPad, hprePadSz, hszRt⟩ :=
      retargetLinkModel_totalSize_pre_eq lkm env.code env.labels errLabel errStubLbl exhaustedLabel exhSub?
        preFn (prologue ++ bodyCode) (fallCode ++ epiCode ++ postStub) hlinkCore env.hcode64 hStub1 hStub2
    exact compileFn_core_sim (lkm' := lkm') env L p hpOk hpArgs
      (fun hfl' => let ⟨_, _, _, hl⟩ := ProgFnsLinkedWithGen.split_fn hFns hfl'; ⟨_, hl⟩)
      b hcall f fd fl
      (fnFrameLayoutForWith_ok (allocOf f fd) env.tab fd)
      (fnFrameLayoutForWith_args_valid (allocOf f fd) env.tab fd)
      (fnFrameLayoutForWith_graph_valid (allocOf f fd) env.tab fd)
      (fun _ hx hn hu => fnFrameLayoutForWith_spilled_of_used (allocOf f fd) env.tab fd hx hn hu)
      (fnFrameLayoutForWith_frameBytes_le (allocOf f fd) env.tab fd)
      rfl rfl rfl (fnFrameLayoutForWith_no_copyScan (allocOf f fd) env.tab fd) habort0 hflook
      prePad postPad preBodyRt (bodyCode.map rt) postStub hlinkPad hlinkBodyRt
      (by rw [lkm'.totalSize_append, hprePadSz, hszRt, lkm.totalSize_append]) (hszRt bodyCode)
      vs m callerSp callerRa argsPtr retPc hvslen hb64 hlim hctop hcal hargAl hraAl hargsGe
      entryPc st hEntryLbl hpc hgp hsp hra hs0 ht0 hm hhdr hargWords
  · have hrtF : needRetarget = false := Bool.eq_false_iff.mpr hrt
    have hlinkPad : lkm.linkSpec (preFn ++ (prologue ++ bodyCode) ++ (fallCode ++ epiCode ++ postStub)) =
        .ok (env.code, env.labels) := by
      rw [hcfDecomp, hrtF] at hlinkFn; simpa [postStub, List.append_assoc] using hlinkFn
    have hlinkBodyRt : lkm.linkSpec ((preFn ++ prologue) ++ bodyCode ++ (fallCode ++ epiCode ++ postStub)) =
        .ok (env.code, env.labels) := by simpa [List.append_assoc] using hlinkPad
    exact compileFn_core_sim (lkm' := lkm) env L p hpOk hpArgs
      (fun hfl' => let ⟨_, _, _, hl⟩ := ProgFnsLinkedWithGen.split_fn hFns hfl'; ⟨_, hl⟩)
      b hcall f fd fl
      (fnFrameLayoutForWith_ok (allocOf f fd) env.tab fd)
      (fnFrameLayoutForWith_args_valid (allocOf f fd) env.tab fd)
      (fnFrameLayoutForWith_graph_valid (allocOf f fd) env.tab fd)
      (fun _ hx hn hu => fnFrameLayoutForWith_spilled_of_used (allocOf f fd) env.tab fd hx hn hu)
      (fnFrameLayoutForWith_frameBytes_le (allocOf f fd) env.tab fd)
      rfl rfl rfl (fnFrameLayoutForWith_no_copyScan (allocOf f fd) env.tab fd) habort0 hflook
      preFn (fallCode ++ epiCode ++ postStub) (preFn ++ prologue) bodyCode postStub
      hlinkPad hlinkBodyRt rfl rfl
      vs m callerSp callerRa argsPtr retPc hvslen hb64 hlim hctop hcal hargAl hraAl hargsGe
      entryPc st hEntryLbl hpc hgp hsp hra hs0 ht0 hm hhdr hargWords

theorem compileFns_call_sim_callee_with {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab) (p : _root_.L.Prog)
    (allocOf : FnName → FunDecl → RegAlloc)
    (hpOk : progOkB env.tab p = true) (hpArgs : progArgsOkB p = true)
    (hFns : ProgFnsLinkedWithGen env allocOf p) :
    ∀ b : Nat, FnCallSimGenCallee env L p b := by
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro f fd vs m callerSp callerRa argsPtr retPc hflook hvslen hb64 hlim hctop hcal hargAl
      hraAl hargsGe entryPc st hEntryLbl hpc hgp hsp hra hs0 ht0 hm hhdr hargWords
    obtain ⟨preFn, postFn, hlinkFn, _⟩ := ProgFnsLinkedWithGen.split_fn hFns hflook
    exact compileFnWith_of_body_sim env L p allocOf hpOk hpArgs hFns b ih f fd preFn postFn hflook hlinkFn
      vs m callerSp callerRa argsPtr retPc hvslen hb64 hlim hctop hcal hargAl hraAl hargsGe
      entryPc st hEntryLbl hpc hgp hsp hra hs0 ht0 hm hhdr hargWords

theorem compileFns_call_sim_callee {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab) (p : _root_.L.Prog)
    (hpOk : progOkB env.tab p = true) (hpArgs : progArgsOkB p = true)
    (hFns : ProgFnsLinkedGen env p) :
    ∀ b : Nat, FnCallSimGenCallee env L p b :=
  compileFns_call_sim_callee_with env L p (fun _ fd => chooseRegAlloc fd) hpOk hpArgs hFns

theorem compileFns_call_sim_gen_with {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab) (p : _root_.L.Prog)
    (allocOf : FnName → FunDecl → RegAlloc)
    (hpOk : progOkB env.tab p = true) (hpArgs : progArgsOkB p = true)
    (hFns : ProgFnsLinkedWithGen env allocOf p) :
    ∀ b : Nat, FnCallSimGen env L p b := by
  intro b f fd vs m callerSp callerRa argsPtr retPc hflook hvslen hb64 hlim hctop hcal hargAl
    hraAl hargsGe entryPc st hEntryLbl hpc hgp hsp hra hs0 ht0 hm hhdr hargWords
  have h := compileFns_call_sim_callee_with env L p allocOf hpOk hpArgs hFns b
    f fd vs m callerSp callerRa argsPtr retPc hflook hvslen hb64 hlim hctop hcal hargAl
    hraAl hargsGe entryPc st hEntryLbl hpc hgp hsp hra hs0 ht0 hm hhdr hargWords
  cases hx : execB p b fd.body { mem := m, loc := Locals.init vs } with
  | error err => cases err <;> (rw [hx] at h; exact h)
  | ok res =>
    rcases res with ⟨sig, st', b'⟩
    rw [hx] at h
    obtain ⟨k, r', hrun, hpc', hgp', hsp', hs2', _, hs0', hb', hnb, hlen, hm', hhdr', hres', hout'⟩ := h
    exact ⟨k, r', hrun, hpc', hgp', hsp', hs2', hs0', hb', hnb, hlen, hm', hhdr', hres', hout'⟩

theorem compileFns_call_sim_gen {lkm : LinkModel} (env : CodeEnvGen lkm) (L : ProgLayout env.tab) (p : _root_.L.Prog)
    (hpOk : progOkB env.tab p = true) (hpArgs : progArgsOkB p = true)
    (hFns : ProgFnsLinkedGen env p) :
    ∀ b : Nat, FnCallSimGen env L p b :=
  compileFns_call_sim_gen_with env L p (fun _ fd => chooseRegAlloc fd) hpOk hpArgs hFns

theorem compileFns_call_sim (env : CodeEnv) (L : ProgLayout env.tab) (p : _root_.L.Prog)
    (hpOk : progOkB env.tab p = true) (hpArgs : progArgsOkB p = true)
    (hFns : ProgFnsLinked env p) :
    ∀ b : Nat, FnCallSim env L p b :=
  compileFns_call_sim_gen env.toGen L p hpOk hpArgs hFns

end ConAgua.RISCV.Compiler
