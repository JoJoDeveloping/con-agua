import ConAgua.RISCV.Bridge.CheckerLinkLabelsS

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Algebraic Label Distinctness (`compileSR` helpers) (`ConAgua.RISCV.Bridge.CheckerLinkLabelsSR`)

Label-distinctness helpers supporting `(lblNames checkerChipAsm).Nodup`.
-/

namespace ConAgua.RISCV.Bridge

open ConAgua.RISCV.RV64
open ConAgua.RISCV.Compiler
open ConAgua.RISCV.Linker
open _root_.L


private theorem emitShrMaskFrom_lblNames (fl : FrameLayout) (rd : Reg) (inner : Expr)
    (lsh : Nat) (lm : BitVec 6) (compInner : Unit → List AsmItem)
    (hi : lblNames (compInner ()) = []) :
    lblNames (emitShrMaskFrom fl rd inner lsh lm compInner) = [] := by
  dsimp only [emitShrMaskFrom]
  cases exprReg? fl.alloc inner with
  | some ri =>
    dsimp only
    have hs1 : lblNames (if (lsh == 0) = true then (if (rd == ri) = true then [] else [Asm.mv rd ri])
        else [Asm.slli rd ri (BitVec.ofNat 6 lsh)]) = [] := by
      split
      · split <;> rfl
      · rfl
    simp only [lblNames_append, hs1, List.nil_append]; rfl
  | none =>
    dsimp only
    have hs1 : lblNames (if (lsh == 0) = true then (if (rd == AbiReg.a0) = true then [] else [Asm.mv rd AbiReg.a0])
        else [Asm.slli rd AbiReg.a0 (BitVec.ofNat 6 lsh)]) = [] := by
      split
      · split <;> rfl
      · rfl
    simp only [lblNames_append, hi, hs1, List.nil_append]; rfl

private theorem emitLd32hPlainFrom_lblNames (tab : Tab) (fl : FrameLayout)
    (rd : Reg) (a : ArrId) (i : Expr) (hi : Bool) (compI0 : Unit → List AsmItem)
    (hcomp : lblNames (compI0 ()) = []) :
    lblNames (emitLd32hPlainFrom tab fl rd a i hi compI0) = [] := by
  dsimp only [emitLd32hPlainFrom]
  cases exprReg? fl.alloc i with
  | some _ =>
    dsimp only
    simp only [lblNames_append,
      lblNames_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
      lblNames_of_allInstrs (ld32hTail_allInstrs _ _ _ _ _), List.nil_append, List.append_nil]
    rfl
  | none =>
    dsimp only
    simp only [lblNames_append, hcomp,
      lblNames_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
      lblNames_of_allInstrs (ld32hTail_allInstrs _ _ _ _ _), List.nil_append, List.append_nil]
    rfl

private theorem emitLd32hFrom_lblNames (tab : Tab) (fl : FrameLayout)
    (tmp : Nat) (rd : Reg) (a : ArrId) (t i : Expr) (hi : Bool)
    (compI0 compT0 compI1 : Unit → List AsmItem)
    (hi0 : lblNames (compI0 ()) = []) (ht0 : lblNames (compT0 ()) = [])
    (hi1 : lblNames (compI1 ()) = []) :
    lblNames (emitLd32hFrom tab fl tmp rd a t i hi compI0 compT0 compI1) = [] := by
  dsimp only [emitLd32hFrom]
  cases t.constVal? with
  | some _ =>
    dsimp only
    cases exprReg? fl.alloc i with
    | some _ =>
      dsimp only
      simp only [lblNames_append,
        lblNames_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
        lblNames_of_allInstrs (ld32hTail_allInstrs _ _ _ _ _), List.nil_append, List.append_nil]; rfl
    | none =>
      dsimp only
      simp only [lblNames_append, hi0,
        lblNames_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
        lblNames_of_allInstrs (ld32hTail_allInstrs _ _ _ _ _), List.nil_append, List.append_nil]; rfl
  | none =>
    cases exprReg? fl.alloc t with
    | some _ =>
      cases exprReg? fl.alloc i with
      | some _ =>
        simp only [lblNames_append,
          lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (ld32hTail_allInstrs _ _ _ _ _), List.nil_append, List.append_nil]; rfl
      | none =>
        simp only [lblNames_append, hi0,
          lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (ld32hTail_allInstrs _ _ _ _ _), List.nil_append, List.append_nil]; rfl
    | none =>
      cases hst : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 t with
      | some ct =>
        cases exprReg? fl.alloc i with
        | some _ =>
          simp only [lblNames_append,
            lblNames_of_allInstrs (emitSimpleExprR_allInstrs hst),
            lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
            lblNames_of_allInstrs (ld32hTail_allInstrs _ _ _ _ _), List.nil_append, List.append_nil]; rfl
        | none =>
          simp only [lblNames_append, hi0,
            lblNames_of_allInstrs (emitSimpleExprR_allInstrs hst),
            lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
            lblNames_of_allInstrs (ld32hTail_allInstrs _ _ _ _ _), List.nil_append, List.append_nil]; rfl
      | none =>
        simp only [lblNames_append, ht0, hi1,
          lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (ld32hTail_allInstrs _ _ _ _ _), List.nil_append, List.append_nil]; rfl

private theorem compileBinFallback_lblNames (tab : Tab) (fl : FrameLayout)
    (tmp : Nat) (rd : Reg) (op : BinOp) (a b : Expr)
    (compA0 compB0 compB1 : Unit → List AsmItem)
    (ha0 : lblNames (compA0 ()) = []) (hb0 : lblNames (compB0 ()) = [])
    (hb1 : lblNames (compB1 ()) = []) :
    lblNames (compileBinFallback tab fl tmp rd op a b compA0 compB0 compB1) = [] := by
  dsimp only [compileBinFallback]
  cases b.constVal? with
  | some w =>
    cases exprReg? fl.alloc a with
    | some ra => exact lblNames_of_allInstrs (emitBinConstRhsTo_allInstrs rd ra op w)
    | none =>
      rw [lblNames_append, ha0,
        lblNames_of_allInstrs (emitBinConstRhsTo_allInstrs rd AbiReg.a0 op w), List.nil_append]
  | none =>
    cases a.constVal? with
    | some w =>
      cases exprReg? fl.alloc b with
      | some rb =>
        cases op with
        | add | and | or | xor | mul | «mulhi» =>
          dsimp only; rw [List.nil_append]
          exact lblNames_of_allInstrs (emitBinConstRhsTo_allInstrs rd rb _ w)
        | sub =>
          dsimp only; split
          · rfl
          · simp only [List.nil_append, lblNames_append,
              lblNames_of_allInstrs (li_allInstrs _ _), List.nil_append]; rfl
        | shl | shr =>
          dsimp only
          simp only [List.nil_append, lblNames_append,
            lblNames_of_allInstrs (li_allInstrs _ _), List.nil_append]; rfl
      | none =>
        cases op with
        | add | and | or | xor | mul | «mulhi» =>
          dsimp only
          rw [lblNames_append, hb0,
            lblNames_of_allInstrs (emitBinConstRhsTo_allInstrs rd AbiReg.a0 _ w), List.nil_append]
        | sub =>
          dsimp only; split
          · simp only [lblNames_append, hb0, List.nil_append]; rfl
          · simp only [lblNames_append, hb0,
              lblNames_of_allInstrs (li_allInstrs _ _), List.nil_append]; rfl
        | shl | shr =>
          dsimp only
          simp only [lblNames_append, hb0,
            lblNames_of_allInstrs (li_allInstrs _ _), List.nil_append]; rfl
    | none =>
      cases exprReg? fl.alloc b with
      | some rb =>
        cases exprReg? fl.alloc a with
        | some ra => exact lblNames_of_allInstrs (emitBinOp_allInstrs op rd ra rb)
        | none =>
          rw [lblNames_append, ha0,
            lblNames_of_allInstrs (emitBinOp_allInstrs op rd AbiReg.a0 rb), List.nil_append]
      | none =>
        cases exprReg? fl.alloc a with
        | some ra =>
          rw [lblNames_append, hb0,
            lblNames_of_allInstrs (emitBinOp_allInstrs op rd ra AbiReg.a0), List.nil_append]
        | none =>
          cases hsb : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 b with
          | some cb =>
            simp only [lblNames_append, ha0,
              lblNames_of_allInstrs (emitSimpleExprR_allInstrs hsb),
              lblNames_of_allInstrs (emitBinOp_allInstrs op _ _ _), List.nil_append]
          | none =>
            cases hsa : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 a with
            | some ca =>
              simp only [lblNames_append, hb0,
                lblNames_of_allInstrs (emitSimpleExprR_allInstrs hsa),
                lblNames_of_allInstrs (emitBinOp_allInstrs op _ _ _), List.nil_append]
            | none =>
              dsimp only
              split
              · simp only [lblNames_append, ha0, hb0,
                  lblNames_of_allInstrs (emitBinOp_allInstrs op _ _ _), List.nil_append, List.append_nil]; rfl
              · simp only [lblNames_append, ha0, hb1,
                  lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
                  lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
                  lblNames_of_allInstrs (emitBinOp_allInstrs op _ _ _), List.nil_append]

private theorem compileETo_lblNames_aux (tab : Tab) (fl : FrameLayout)
    (e : Expr) (tmp : Nat) (rd : Reg) : lblNames (compileETo tab fl tmp rd e) = [] := by
  match e with
  | .const _ => exact lblNames_of_allInstrs (li_allInstrs _ _)
  | .var x =>
    dsimp only [compileETo]
    split
    · split <;> rfl
    · exact lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _)
  | .len8 _ | .len64 _ | .glob _ =>
    exact lblNames_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _)
  | .bin op a b =>
    unfold compileETo
    dsimp only
    split
    · split
      · split
        · exact emitShrMaskFrom_lblNames fl rd _ _ _ _
            (compileETo_lblNames_aux tab fl _ tmp AbiReg.a0)
        · exact compileBinFallback_lblNames tab fl tmp rd _ _ _ _ _ _
            (compileETo_lblNames_aux tab fl _ tmp AbiReg.a0)
            (compileETo_lblNames_aux tab fl _ tmp AbiReg.a0)
            (compileETo_lblNames_aux tab fl _ (tmp + 1) AbiReg.a0)
      · exact compileBinFallback_lblNames tab fl tmp rd _ _ _ _ _ _
          (compileETo_lblNames_aux tab fl _ tmp AbiReg.a0)
          (compileETo_lblNames_aux tab fl _ tmp AbiReg.a0)
          (compileETo_lblNames_aux tab fl _ (tmp + 1) AbiReg.a0)
    · exact emitLd32hPlainFrom_lblNames tab fl rd _ _ false _
        (compileETo_lblNames_aux tab fl _ tmp AbiReg.a0)
    · exact emitLd32hPlainFrom_lblNames tab fl rd _ _ true _
        (compileETo_lblNames_aux tab fl _ tmp AbiReg.a0)
    · exact emitLd32hFrom_lblNames tab fl tmp rd _ _ _ false _ _ _
        (compileETo_lblNames_aux tab fl _ tmp AbiReg.a0)
        (compileETo_lblNames_aux tab fl _ tmp AbiReg.a0)
        (compileETo_lblNames_aux tab fl _ (tmp + 1) AbiReg.a0)
    · exact emitLd32hFrom_lblNames tab fl tmp rd _ _ _ true _ _ _
        (compileETo_lblNames_aux tab fl _ tmp AbiReg.a0)
        (compileETo_lblNames_aux tab fl _ tmp AbiReg.a0)
        (compileETo_lblNames_aux tab fl _ (tmp + 1) AbiReg.a0)
    · exact compileBinFallback_lblNames tab fl tmp rd op a b _ _ _
        (compileETo_lblNames_aux tab fl a tmp AbiReg.a0)
        (compileETo_lblNames_aux tab fl b tmp AbiReg.a0)
        (compileETo_lblNames_aux tab fl b (tmp + 1) AbiReg.a0)
  | .cmpw c a b =>
    have iha := fun k r => compileETo_lblNames_aux tab fl a k r
    have ihb := fun k r => compileETo_lblNames_aux tab fl b k r
    dsimp only [compileETo]
    split
    · cases exprReg? fl.alloc a with
      | some _ => rfl
      | none => simp only [lblNames_append, iha tmp AbiReg.a0, List.nil_append]; rfl
    · split
      · cases exprReg? fl.alloc b with
        | some _ => rfl
        | none => simp only [lblNames_append, ihb tmp AbiReg.a0, List.nil_append]; rfl
      · split
        · cases exprReg? fl.alloc a with
          | some _ => rfl
          | none => simp only [lblNames_append, iha tmp AbiReg.a0, List.nil_append]; rfl
        · split
          · cases exprReg? fl.alloc b with
            | some _ => rfl
            | none => simp only [lblNames_append, ihb tmp AbiReg.a0, List.nil_append]; rfl
          · cases exprReg? fl.alloc b with
            | some rb =>
              cases exprReg? fl.alloc a with
              | some ra => exact lblNames_of_allInstrs (emitCmpwTo_allInstrs rd c ra rb)
              | none =>
                rw [lblNames_append, iha tmp AbiReg.a0,
                  lblNames_of_allInstrs (emitCmpwTo_allInstrs rd c AbiReg.a0 rb), List.nil_append]
            | none =>
              cases exprReg? fl.alloc a with
              | some ra =>
                rw [lblNames_append, ihb tmp AbiReg.a0,
                  lblNames_of_allInstrs (emitCmpwTo_allInstrs rd c ra AbiReg.a0), List.nil_append]
              | none =>
                cases hsb : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 b with
                | some cb =>
                  simp only [lblNames_append, iha tmp AbiReg.a0,
                    lblNames_of_allInstrs (emitSimpleExprR_allInstrs hsb),
                    lblNames_of_allInstrs (emitCmpwTo_allInstrs rd c _ _), List.nil_append]
                | none =>
                  cases hsa : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 a with
                  | some ca =>
                    simp only [lblNames_append, ihb tmp AbiReg.a0,
                      lblNames_of_allInstrs (emitSimpleExprR_allInstrs hsa),
                      lblNames_of_allInstrs (emitCmpwTo_allInstrs rd c _ _), List.nil_append]
                  | none =>
                    dsimp only
                    split
                    · simp only [lblNames_append, iha tmp AbiReg.a0, ihb tmp AbiReg.a0,
                        lblNames_of_allInstrs (emitCmpwTo_allInstrs rd c _ _), List.nil_append, List.append_nil]; rfl
                    · simp only [lblNames_append, iha tmp AbiReg.a0, ihb (tmp + 1) AbiReg.a0,
                        lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
                        lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
                        lblNames_of_allInstrs (emitCmpwTo_allInstrs rd c _ _), List.nil_append]
  | .ld8 _ i =>
    have ih := fun k r => compileETo_lblNames_aux tab fl i k r
    dsimp only [compileETo]
    cases exprReg? fl.alloc i with
    | some _ =>
      dsimp only
      simp only [lblNames_append, lblNames_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
        List.nil_append, List.append_nil]
      cases i.constVal? with | none => rfl | some _ => dsimp only; split <;> rfl
    | none =>
      dsimp only
      simp only [lblNames_append, ih tmp AbiReg.a0,
        lblNames_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
        List.nil_append, List.append_nil]
      cases i.constVal? with | none => rfl | some _ => dsimp only; split <;> rfl
  | .ld64 _ i =>
    have ih := fun k r => compileETo_lblNames_aux tab fl i k r
    dsimp only [compileETo]
    cases exprReg? fl.alloc i with
    | some _ =>
      dsimp only
      simp only [lblNames_append,
        lblNames_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
        lblNames_of_allInstrs (ld64Tail_allInstrs _ _ _ _), List.nil_append, List.append_nil]; rfl
    | none =>
      dsimp only
      simp only [lblNames_append, ih tmp AbiReg.a0,
        lblNames_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
        lblNames_of_allInstrs (ld64Tail_allInstrs _ _ _ _), List.nil_append, List.append_nil]; rfl
  | .ldc _ i =>
    have ih := fun k r => compileETo_lblNames_aux tab fl i k r
    dsimp only [compileETo]
    cases exprReg? fl.alloc i with
    | some _ =>
      dsimp only
      simp only [lblNames_append, lblNames_of_allInstrs (li_allInstrs _ _),
        lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append, List.append_nil]; rfl
    | none =>
      dsimp only
      simp only [lblNames_append, ih tmp AbiReg.a0, lblNames_of_allInstrs (li_allInstrs _ _),
        lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append, List.append_nil]; rfl
  | .ld64t _ t i =>
    have iht := fun k r => compileETo_lblNames_aux tab fl t k r
    have ihi := fun k r => compileETo_lblNames_aux tab fl i k r
    dsimp only [compileETo]
    cases t.constVal? with
    | some _ =>
      dsimp only
      cases exprReg? fl.alloc i with
      | some _ =>
        dsimp only
        simp only [lblNames_append,
          lblNames_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (ld64Tail_allInstrs _ _ _ _), List.nil_append, List.append_nil]; rfl
      | none =>
        dsimp only
        simp only [lblNames_append, ihi tmp AbiReg.a0,
          lblNames_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (ld64Tail_allInstrs _ _ _ _), List.nil_append, List.append_nil]; rfl
    | none =>
      cases exprReg? fl.alloc t with
      | some rt =>
        cases exprReg? fl.alloc i with
        | some ri =>
          simp only [lblNames_append,
            lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
            lblNames_of_allInstrs (ld64Tail_allInstrs _ _ _ _), List.nil_append, List.append_nil]; rfl
        | none =>
          simp only [lblNames_append, ihi tmp AbiReg.a0,
            lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
            lblNames_of_allInstrs (ld64Tail_allInstrs _ _ _ _), List.nil_append, List.append_nil]; rfl
      | none =>
        cases hst : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 t with
        | some ct =>
          cases exprReg? fl.alloc i with
          | some ri =>
            simp only [lblNames_append,
              lblNames_of_allInstrs (emitSimpleExprR_allInstrs hst),
              lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
              lblNames_of_allInstrs (ld64Tail_allInstrs _ _ _ _), List.nil_append, List.append_nil]; rfl
          | none =>
            simp only [lblNames_append, ihi tmp AbiReg.a0,
              lblNames_of_allInstrs (emitSimpleExprR_allInstrs hst),
              lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
              lblNames_of_allInstrs (ld64Tail_allInstrs _ _ _ _), List.nil_append, List.append_nil]; rfl
        | none =>
          simp only [lblNames_append, iht tmp AbiReg.a0, ihi (tmp + 1) AbiReg.a0,
            lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
            lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
            lblNames_of_allInstrs (ld64Tail_allInstrs _ _ _ _), List.nil_append, List.append_nil]; rfl
  | .ld32t _ t i =>
    have iht := fun k r => compileETo_lblNames_aux tab fl t k r
    have ihi := fun k r => compileETo_lblNames_aux tab fl i k r
    dsimp only [compileETo]
    cases t.constVal? with
    | some _ =>
      dsimp only
      cases exprReg? fl.alloc i with
      | some _ =>
        dsimp only
        simp only [lblNames_append,
          lblNames_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (ld32tTail_allInstrs _ _ _), List.nil_append, List.append_nil]; rfl
      | none =>
        dsimp only
        simp only [lblNames_append, ihi tmp AbiReg.a0,
          lblNames_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (ld32tTail_allInstrs _ _ _), List.nil_append, List.append_nil]; rfl
    | none =>
      cases exprReg? fl.alloc t with
      | some rt =>
        cases exprReg? fl.alloc i with
        | some ri =>
          simp only [lblNames_append,
            lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
            lblNames_of_allInstrs (ld32tTail_allInstrs _ _ _), List.nil_append, List.append_nil]; rfl
        | none =>
          simp only [lblNames_append, ihi tmp AbiReg.a0,
            lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
            lblNames_of_allInstrs (ld32tTail_allInstrs _ _ _), List.nil_append, List.append_nil]; rfl
      | none =>
        cases hst : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 t with
        | some ct =>
          cases exprReg? fl.alloc i with
          | some ri =>
            simp only [lblNames_append,
              lblNames_of_allInstrs (emitSimpleExprR_allInstrs hst),
              lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
              lblNames_of_allInstrs (ld32tTail_allInstrs _ _ _), List.nil_append, List.append_nil]; rfl
          | none =>
            simp only [lblNames_append, ihi tmp AbiReg.a0,
              lblNames_of_allInstrs (emitSimpleExprR_allInstrs hst),
              lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
              lblNames_of_allInstrs (ld32tTail_allInstrs _ _ _), List.nil_append, List.append_nil]; rfl
        | none =>
          simp only [lblNames_append, iht tmp AbiReg.a0, ihi (tmp + 1) AbiReg.a0,
            lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
            lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
            lblNames_of_allInstrs (ld32tTail_allInstrs _ _ _), List.nil_append, List.append_nil]; rfl
  | .len64t _ t =>
    have ih := fun k r => compileETo_lblNames_aux tab fl t k r
    dsimp only [compileETo]
    cases t.constVal? with
    | some _ => exact lblNames_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _)
    | none =>
      cases exprReg? fl.alloc t with
      | some _ =>
        simp only [lblNames_append, lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
          List.nil_append, List.append_nil]; rfl
      | none =>
        simp only [lblNames_append, ih tmp AbiReg.a0,
          lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append, List.append_nil]; rfl
  | .ld8x8 src i =>
    have ih := fun k r => compileETo_lblNames_aux tab fl i k r
    have hread : allInstrs ([Asm.lbu rd AbiReg.t1 7#12] ++
        List.flatMap (fun k =>
          [Asm.lbu AbiReg.t2 AbiReg.t1 (BitVec.ofInt 12 k), Asm.slli rd rd 8#6,
           Asm.or rd rd AbiReg.t2]) [6, 5, 4, 3, 2, 1, 0]) = true := by
      rw [allInstrs_append, Bool.and_eq_true]
      exact ⟨rfl, allInstrs_flatMap (fun _ _ => rfl)⟩
    dsimp only [compileETo]
    cases exprReg? fl.alloc i with
    | some _ =>
      cases src <;>
        simp only [List.nil_append, lblNames_append,
          lblNames_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (li_allInstrs _ _),
          lblNames_of_allInstrs (addImmOff_allInstrs _ _ _ _),
          lblNames_of_allInstrs hread, List.nil_append, List.append_nil] <;> rfl
    | none =>
      cases src <;>
        simp only [lblNames_append, ih tmp AbiReg.a0,
          lblNames_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (li_allInstrs _ _),
          lblNames_of_allInstrs (addImmOff_allInstrs _ _ _ _),
          lblNames_of_allInstrs hread, List.nil_append, List.append_nil] <;> rfl
  | .ld32h a t i hi =>
    exact emitLd32hFrom_lblNames tab fl tmp rd a t i hi _ _ _
      (compileETo_lblNames_aux tab fl i tmp AbiReg.a0)
      (compileETo_lblNames_aux tab fl t tmp AbiReg.a0)
      (compileETo_lblNames_aux tab fl i (tmp + 1) AbiReg.a0)
termination_by sizeOf e

theorem compileETo_lblNames (tab : Tab) (fl : FrameLayout) :
    ∀ (e : Expr) (tmp : Nat) (rd : Reg), lblNames (compileETo tab fl tmp rd e) = [] :=
  compileETo_lblNames_aux tab fl

theorem compileCR_lbls_spec (tab : Tab) (fl : FrameLayout) (tmp : Nat) (pfx : String) :
    ∀ (c : Cond) (lblId : Nat) (want : Bool) (target : String),
      lblId ≤ (compileCR tab fl tmp pfx lblId c want target).2 ∧
      (lblNames (compileCR tab fl tmp pfx lblId c want target).1).Nodup ∧
      (∀ s ∈ lblNames (compileCR tab fl tmp pfx lblId c want target).1,
        isDynLbl pfx lblId (compileCR tab fl tmp pfx lblId c want target).2 s) := by
  intro c
  induction c with
  | cmp op a b =>
    intro lblId want target
    have heq : lblNames (compileCR tab fl tmp pfx lblId (.cmp op a b) want target).1 = [] := by
      dsimp only [compileCR]
      cases exprReg? fl.alloc a with
      | some ra =>
        cases exprReg? fl.alloc b with
        | some rb => exact brCmp_lblNames op want ra rb target
        | none => simp only [lblNames_append, compileETo_lblNames, brCmp_lblNames, List.nil_append]
      | none =>
        cases exprReg? fl.alloc b with
        | some rb => simp only [lblNames_append, compileETo_lblNames, brCmp_lblNames, List.nil_append]
        | none =>
          cases hsb : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 b with
          | some cb =>
            simp only [lblNames_append, compileETo_lblNames,
              lblNames_of_allInstrs (emitSimpleExprR_allInstrs hsb), brCmp_lblNames, List.nil_append]
          | none =>
            cases hsa : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 a with
            | some ca =>
              simp only [lblNames_append, compileETo_lblNames,
                lblNames_of_allInstrs (emitSimpleExprR_allInstrs hsa), brCmp_lblNames, List.nil_append]
            | none =>
              dsimp only
              split
              · simp only [lblNames_append, compileETo_lblNames, brCmp_lblNames,
                  List.nil_append, List.append_nil]; rfl
              · simp only [lblNames_append, compileETo_lblNames,
                  lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
                  lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), brCmp_lblNames, List.nil_append]
    refine ⟨Nat.le_refl _, ?_, ?_⟩
    · rw [heq]; exact List.nodup_nil
    · intro s hs; rw [heq] at hs; cases hs
  | not p ih =>
    intro lblId want target
    exact ih lblId (!want) target
  | and p q ihp ihq =>
    intro lblId want target
    dsimp only [compileCR]
    cases want
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rcases h1 : compileCR tab fl tmp pfx lblId p false target with ⟨cp, id1⟩
      rcases h2 : compileCR tab fl tmp pfx id1 q false target with ⟨cq, id2⟩
      obtain ⟨hle1, hnd1, hsp1⟩ := ihp lblId false target
      obtain ⟨hle2, hnd2, hsp2⟩ := ihq id1 false target
      rw [h1] at hle1 hnd1 hsp1; rw [h2] at hle2 hnd2 hsp2
      dsimp only at hle1 hnd1 hsp1 hle2 hnd2 hsp2 ⊢
      refine ⟨Nat.le_trans hle1 hle2, ?_, ?_⟩
      · rw [lblNames_append]
        refine nodup_append_disj hnd1 hnd2 (fun s hs1 hs2 => ?_)
        obtain ⟨t1, ht1, k1, _, hk1hi, heq1⟩ := hsp1 s hs1
        obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hsp2 s hs2
        have ⟨hk, _⟩ := dynLbl_inj ht1 ht2 (heq1.symm.trans heq2); omega
      · intro s hs
        rw [lblNames_append, List.mem_append] at hs
        rcases hs with hs | hs
        · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp1 s hs
          exact ⟨t, ht, k, hk1, Nat.lt_of_lt_of_le hk2 hle2, heq⟩
        · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp2 s hs
          exact ⟨t, ht, k, Nat.le_trans hle1 hk1, hk2, heq⟩
    · simp only [↓reduceIte]
      let skipLbl := pfx ++ "_and_" ++ toString lblId
      rcases h1 : compileCR tab fl tmp pfx (lblId + 1) p false skipLbl with ⟨cp, id1⟩
      rcases h2 : compileCR tab fl tmp pfx id1 q true target with ⟨cq, id2⟩
      obtain ⟨hle1, hnd1, hsp1⟩ := ihp (lblId + 1) false skipLbl
      obtain ⟨hle2, hnd2, hsp2⟩ := ihq id1 true target
      rw [h1] at hle1 hnd1 hsp1; rw [h2] at hle2 hnd2 hsp2
      dsimp only at hle1 hnd1 hsp1 hle2 hnd2 hsp2 ⊢
      refine ⟨by omega, ?_, ?_⟩
      · rw [lblNames_append, lblNames_append]
        refine nodup_append_disj (nodup_append_disj hnd1 hnd2 (fun s hs1 hs2 => ?_))
            (by rw [lblNames_singleton_lbl]; simp) (fun s hs12 hs3 => ?_)
        · obtain ⟨t1, ht1, k1, _, hk1hi, heq1⟩ := hsp1 s hs1
          obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hsp2 s hs2
          have ⟨hk, _⟩ := dynLbl_inj ht1 ht2 (heq1.symm.trans heq2); omega
        · rw [lblNames_singleton_lbl, List.mem_singleton] at hs3; subst hs3
          have hskip : toString pfx ++ toString "_and_" ++ toString lblId =
              pfx ++ "_" ++ "and" ++ "_" ++ Nat.repr lblId := by
            change pfx ++ ("_" ++ "and" ++ "_") ++ Nat.repr lblId = _; simp only [String.append_assoc]
          rcases List.mem_append.mp hs12 with hs1 | hs2
          · obtain ⟨t1, ht1, k1, hk1lo, _, heq1⟩ := hsp1 _ hs1
            have ⟨hk, _⟩ := dynLbl_inj ht1 (by simp [dynTags] : "and" ∈ dynTags) (hskip.symm.trans heq1).symm; omega
          · obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hsp2 _ hs2
            have ⟨hk, _⟩ := dynLbl_inj ht2 (by simp [dynTags] : "and" ∈ dynTags) (hskip.symm.trans heq2).symm; omega
      · intro s hs
        rw [lblNames_append, lblNames_append, List.mem_append, List.mem_append] at hs
        rcases hs with (hs1 | hs2) | hs3
        · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp1 s hs1
          exact ⟨t, ht, k, by omega, Nat.lt_of_lt_of_le hk2 hle2, heq⟩
        · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp2 s hs2
          exact ⟨t, ht, k, by omega, hk2, heq⟩
        · rw [lblNames_singleton_lbl, List.mem_singleton] at hs3; subst hs3
          have hskip : toString pfx ++ toString "_and_" ++ toString lblId =
              pfx ++ "_" ++ "and" ++ "_" ++ Nat.repr lblId := by
            change pfx ++ ("_" ++ "and" ++ "_") ++ Nat.repr lblId = _; simp only [String.append_assoc]
          exact ⟨"and", by simp [dynTags], lblId, Nat.le_refl _, by omega, hskip⟩
  | or p q ihp ihq =>
    intro lblId want target
    dsimp only [compileCR]
    cases want
    · simp only [Bool.false_eq_true, ↓reduceIte]
      let skipLbl := pfx ++ "_or_" ++ toString lblId
      rcases h1 : compileCR tab fl tmp pfx (lblId + 1) p true skipLbl with ⟨cp, id1⟩
      rcases h2 : compileCR tab fl tmp pfx id1 q false target with ⟨cq, id2⟩
      obtain ⟨hle1, hnd1, hsp1⟩ := ihp (lblId + 1) true skipLbl
      obtain ⟨hle2, hnd2, hsp2⟩ := ihq id1 false target
      rw [h1] at hle1 hnd1 hsp1; rw [h2] at hle2 hnd2 hsp2
      dsimp only at hle1 hnd1 hsp1 hle2 hnd2 hsp2 ⊢
      refine ⟨by omega, ?_, ?_⟩
      · rw [lblNames_append, lblNames_append]
        refine nodup_append_disj (nodup_append_disj hnd1 hnd2 (fun s hs1 hs2 => ?_))
            (by rw [lblNames_singleton_lbl]; simp) (fun s hs12 hs3 => ?_)
        · obtain ⟨t1, ht1, k1, _, hk1hi, heq1⟩ := hsp1 s hs1
          obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hsp2 s hs2
          have ⟨hk, _⟩ := dynLbl_inj ht1 ht2 (heq1.symm.trans heq2); omega
        · rw [lblNames_singleton_lbl, List.mem_singleton] at hs3; subst hs3
          have hskip : toString pfx ++ toString "_or_" ++ toString lblId =
              pfx ++ "_" ++ "or" ++ "_" ++ Nat.repr lblId := by
            change pfx ++ ("_" ++ "or" ++ "_") ++ Nat.repr lblId = _; simp only [String.append_assoc]
          rcases List.mem_append.mp hs12 with hs1 | hs2
          · obtain ⟨t1, ht1, k1, hk1lo, _, heq1⟩ := hsp1 _ hs1
            have ⟨hk, _⟩ := dynLbl_inj ht1 (by simp [dynTags] : "or" ∈ dynTags) (hskip.symm.trans heq1).symm; omega
          · obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hsp2 _ hs2
            have ⟨hk, _⟩ := dynLbl_inj ht2 (by simp [dynTags] : "or" ∈ dynTags) (hskip.symm.trans heq2).symm; omega
      · intro s hs
        rw [lblNames_append, lblNames_append, List.mem_append, List.mem_append] at hs
        rcases hs with (hs1 | hs2) | hs3
        · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp1 s hs1
          exact ⟨t, ht, k, by omega, Nat.lt_of_lt_of_le hk2 hle2, heq⟩
        · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp2 s hs2
          exact ⟨t, ht, k, by omega, hk2, heq⟩
        · rw [lblNames_singleton_lbl, List.mem_singleton] at hs3; subst hs3
          have hskip : toString pfx ++ toString "_or_" ++ toString lblId =
              pfx ++ "_" ++ "or" ++ "_" ++ Nat.repr lblId := by
            change pfx ++ ("_" ++ "or" ++ "_") ++ Nat.repr lblId = _; simp only [String.append_assoc]
          exact ⟨"or", by simp [dynTags], lblId, Nat.le_refl _, by omega, hskip⟩
    · simp only [↓reduceIte]
      rcases h1 : compileCR tab fl tmp pfx lblId p true target with ⟨cp, id1⟩
      rcases h2 : compileCR tab fl tmp pfx id1 q true target with ⟨cq, id2⟩
      obtain ⟨hle1, hnd1, hsp1⟩ := ihp lblId true target
      obtain ⟨hle2, hnd2, hsp2⟩ := ihq id1 true target
      rw [h1] at hle1 hnd1 hsp1; rw [h2] at hle2 hnd2 hsp2
      dsimp only at hle1 hnd1 hsp1 hle2 hnd2 hsp2 ⊢
      refine ⟨Nat.le_trans hle1 hle2, ?_, ?_⟩
      · rw [lblNames_append]
        refine nodup_append_disj hnd1 hnd2 (fun s hs1 hs2 => ?_)
        obtain ⟨t1, ht1, k1, _, hk1hi, heq1⟩ := hsp1 s hs1
        obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hsp2 s hs2
        have ⟨hk, _⟩ := dynLbl_inj ht1 ht2 (heq1.symm.trans heq2); omega
      · intro s hs
        rw [lblNames_append, List.mem_append] at hs
        rcases hs with hs | hs
        · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp1 s hs
          exact ⟨t, ht, k, hk1, Nat.lt_of_lt_of_le hk2 hle2, heq⟩
        · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp2 s hs
          exact ⟨t, ht, k, Nat.le_trans hle1 hk1, hk2, heq⟩

theorem compileEvalExprsToTempsR_lblNames (tab : Tab) (fl : FrameLayout) :
    ∀ (es : List Expr) (tmp : Nat), lblNames (compileEvalExprsToTempsR tab fl tmp es) = [] := by
  intro es
  induction es with
  | nil => intro _; rfl
  | cons e es ih =>
    intro tmp
    dsimp only [compileEvalExprsToTempsR]
    rw [lblNames_append, ih (tmp + 1), List.append_nil]
    cases exprReg? fl.alloc e with
    | some _ => exact lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)
    | none =>
      simp only [lblNames_append, compileETo_lblNames,
        lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _), List.nil_append]

theorem evalWArrTierToTempR_lblNames (tab : Tab) (fl : FrameLayout) (tmp : Nat) (w : WArr) :
    lblNames (evalWArrTierToTempR tab fl tmp w).2 = [] := by
  cases w with
  | plain _ => exact lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)
  | tier _ t =>
    dsimp only [evalWArrTierToTempR]
    cases exprReg? fl.alloc t with
    | some _ => exact lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)
    | none =>
      simp [lblNames_append, compileETo_lblNames,
        lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)]

theorem compileStorePairR_lblNames (tab : Tab) (fl : FrameLayout) (i e : Expr) :
    lblNames (compileStorePairR tab fl i e).1 = [] := by
  dsimp only [compileStorePairR]
  cases exprReg? fl.alloc i with
  | some _ =>
    cases exprReg? fl.alloc e with
    | some _ => rfl
    | none => exact compileETo_lblNames tab fl e 0 AbiReg.a0
  | none =>
    cases exprReg? fl.alloc e with
    | some _ => exact compileETo_lblNames tab fl i 0 AbiReg.a0
    | none =>
      cases hsi : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 i with
      | some ci =>
        simp only [lblNames_append, compileETo_lblNames,
          lblNames_of_allInstrs (emitSimpleExprR_allInstrs hsi), List.nil_append]
      | none =>
        cases hse : emitSimpleExprR tab fl AbiReg.a0 AbiReg.t1 e with
        | some ce =>
          simp only [lblNames_append, compileETo_lblNames,
            lblNames_of_allInstrs (emitSimpleExprR_allInstrs hse), List.nil_append, List.append_nil]; rfl
        | none =>
          simp only [lblNames_append, compileETo_lblNames,
            lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
            lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append]

theorem compileTierStoreTripleR_lblNames (tab : Tab) (fl : FrameLayout) (t i e : Expr) :
    lblNames (compileTierStoreTripleR tab fl t i e).1 = [] := by
  dsimp only [compileTierStoreTripleR]
  cases exprReg? fl.alloc t with
  | some _ =>
    cases exprReg? fl.alloc i with
    | some _ =>
      cases exprReg? fl.alloc e with
      | some _ => rfl
      | none => exact compileETo_lblNames tab fl e 0 AbiReg.a0
    | none =>
      cases exprReg? fl.alloc e with
      | some _ => exact compileETo_lblNames tab fl i 0 AbiReg.a0
      | none =>
        cases hsi : emitSimpleExprR tab fl AbiReg.t3 AbiReg.t4 i with
        | some ci =>
          simp only [lblNames_append, compileETo_lblNames,
            lblNames_of_allInstrs (emitSimpleExprR_allInstrs hsi), List.nil_append]
        | none =>
          cases hse : emitSimpleExprR tab fl AbiReg.a0 AbiReg.t4 e with
          | some ce =>
            simp only [lblNames_append, compileETo_lblNames,
              lblNames_of_allInstrs (emitSimpleExprR_allInstrs hse), List.nil_append, List.append_nil]; rfl
          | none =>
            simp only [lblNames_append, compileETo_lblNames,
              lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
              lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append]
  | none =>
    cases hst : emitSimpleExprR tab fl AbiReg.t0 AbiReg.t1 t with
    | some ct =>
      cases hsi : emitSimpleExprR tab fl AbiReg.t3 AbiReg.t4 i with
      | some ci =>
        simp only [lblNames_append, compileETo_lblNames,
          lblNames_of_allInstrs (emitSimpleExprR_allInstrs hst),
          lblNames_of_allInstrs (emitSimpleExprR_allInstrs hsi), List.nil_append]
      | none =>
        cases hse : emitSimpleExprR tab fl AbiReg.a0 AbiReg.t4 e with
        | some ce =>
          simp only [lblNames_append, compileETo_lblNames,
            lblNames_of_allInstrs (emitSimpleExprR_allInstrs hst),
            lblNames_of_allInstrs (emitSimpleExprR_allInstrs hse), List.nil_append, List.append_nil]; rfl
        | none =>
          simp only [lblNames_append, compileETo_lblNames,
            lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
            lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
            lblNames_of_allInstrs (emitSimpleExprR_allInstrs hst), List.nil_append]
    | none =>
      simp only [lblNames_append, compileETo_lblNames,
        lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
        lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append]

theorem compileEvalRevToRegs_lblNames (tab : Tab) (fl : FrameLayout) :
    ∀ (es : List Expr) (idx : Nat), lblNames (compileEvalRevToRegs tab fl idx es) = [] := by
  intro es
  induction es with
  | nil => intro _; rfl
  | cons e rest ih =>
    intro idx
    dsimp only [compileEvalRevToRegs]
    rw [lblNames_append, ih (idx + 1), compileETo_lblNames, List.nil_append]

theorem compileRetR_lblNames (tab : Tab) (fl : FrameLayout)
    (retLbl : String) (isTail : Bool) (es : List Expr) :
    lblNames (compileRetR tab fl retLbl isTail es) = [] := by
  have hj : lblNames (if isTail = true then []
      else if (fl.isLeaf && (fl.frameSlots == 0)) = true then [Asm.ret]
      else [Asm.j retLbl]) = [] := by
    split
    · rfl
    · split <;> rfl
  cases es with
  | nil =>
    simp only [compileRetR, lblNames_append,
      lblNames_of_allInstrs (copyTempsToResultsR_allInstrs _ _ _ _), hj, List.nil_append]
  | cons e rest =>
    cases rest with
    | nil =>
      simp only [compileRetR, lblNames_append, compileETo_lblNames, hj, List.nil_append]
    | cons e2 rs =>
      dsimp only [compileRetR]
      split
      · simp only [lblNames_append, compileEvalRevToRegs_lblNames, hj, List.nil_append]
      · simp only [lblNames_append, compileEvalExprsToTempsR_lblNames,
          lblNames_of_allInstrs (copyTempsToResultsR_allInstrs _ _ _ _), hj, List.nil_append]

theorem compileCallArgsR_lblNames (tab : Tab) (fl : FrameLayout) (args : List Expr) :
    lblNames (compileCallArgsR tab fl args) = [] := by
  have hbud : lblNames [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
      Asm.addi AbiReg.s0 AbiReg.s0 (-1#12)] = [] := rfl
  dsimp only [compileCallArgsR]
  split
  · simp only [lblNames_append, compileEvalRevToRegs_lblNames, hbud, List.nil_append]
  · have hlds : lblNames ((List.range (min args.length maxRes)).flatMap fun i =>
        loadMemOff .ld (resReg i) AbiReg.sp AbiReg.t0 (fl.tempSlotOff i)) = [] := by
      rw [lblNames_flatMap, List.flatMap_eq_nil_iff]
      intro _ _; exact lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _)
    have hptr : lblNames (if maxRes < args.length then
        addImmOff AbiReg.t0 AbiReg.sp AbiReg.t2 (fl.tempSlotOff maxRes) else []) = [] := by
      split
      · exact lblNames_of_allInstrs (addImmOff_allInstrs _ _ _ _)
      · rfl
    simp only [lblNames_append, compileEvalExprsToTempsR_lblNames, hbud, hlds, hptr, List.nil_append]

section CompileSRLblsSpec
set_option maxHeartbeats 600000

theorem compileSR_lbls_spec (tab : Tab) (fl : FrameLayout) (pfx retLbl : String) :
    ∀ (s : Stmt) (lblId : Nat) (brkLbl : Option String) (isTail : Bool),
      lblId ≤ (compileSR tab fl pfx lblId brkLbl retLbl isTail s).2 ∧
      (lblNames (compileSR tab fl pfx lblId brkLbl retLbl isTail s).1).Nodup ∧
      (∀ l ∈ lblNames (compileSR tab fl pfx lblId brkLbl retLbl isTail s).1,
        isDynLbl pfx lblId (compileSR tab fl pfx lblId brkLbl retLbl isTail s).2 l) := by
  intro s
  induction s with
  | skip =>
    intro lblId _ _; exact ⟨Nat.le_refl _, List.nodup_nil, fun _ h => by cases h⟩
  | set x e =>
    intro lblId brkLbl isTail
    have h0 : lblNames (compileSR tab fl pfx lblId brkLbl retLbl isTail (.set x e)).1 = [] := by
      dsimp only [compileSR]
      split
      · next rx _ => exact compileETo_lblNames tab fl e 0 rx
      · split
        · split
          · rfl
          · exact compileETo_lblNames tab fl e 0 AbiReg.a0
        · cases exprReg? fl.alloc e with
          | some _ => exact lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)
          | none =>
            simp only [lblNames_append, compileETo_lblNames,
              lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _), List.nil_append]
    exact ⟨Nat.le_refl _, by rw [h0]; exact List.nodup_nil, fun _ h => by rw [h0] at h; cases h⟩
  | gset g e =>
    intro lblId brkLbl isTail
    have h0 : lblNames (compileSR tab fl pfx lblId brkLbl retLbl isTail (.gset g e)).1 = [] := by
      dsimp only [compileSR]
      cases exprReg? fl.alloc e with
      | some _ => exact lblNames_of_allInstrs (storeMemOffGp_allInstrs _ _ _ _ _)
      | none =>
        simp only [lblNames_append, compileETo_lblNames,
          lblNames_of_allInstrs (storeMemOffGp_allInstrs _ _ _ _ _), List.nil_append]
    exact ⟨Nat.le_refl _, by rw [h0]; exact List.nodup_nil, fun _ h => by rw [h0] at h; cases h⟩
  | st8 _ _ _ =>
    intro lblId _ _; exact ⟨Nat.le_refl _, List.nodup_nil, fun _ h => by cases h⟩
  | st64 a i e =>
    intro lblId brkLbl isTail
    have h0 : lblNames (compileSR tab fl pfx lblId brkLbl retLbl isTail (.st64 a i e)).1 = [] := by
      have hcp := compileStorePairR_lblNames tab fl i e
      rcases hpair : compileStorePairR tab fl i e with ⟨cp, ri, re⟩
      rw [hpair] at hcp
      simp only [compileSR, hpair, lblNames_append, hcp,
        lblNames_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
        lblNames_of_allInstrs (st64Tail_allInstrs _ _ _ _), List.nil_append, List.append_nil]; rfl
    exact ⟨Nat.le_refl _, by rw [h0]; exact List.nodup_nil, fun _ h => by rw [h0] at h; cases h⟩
  | st64t a t i e =>
    intro lblId brkLbl isTail
    have h0 : lblNames (compileSR tab fl pfx lblId brkLbl retLbl isTail (.st64t a t i e)).1 = [] := by
      dsimp only [compileSR]
      cases t.constVal? with
      | some wt =>
        dsimp only
        have hcp := compileStorePairR_lblNames tab fl i e
        rcases hpair : compileStorePairR tab fl i e with ⟨cp, ri, re⟩
        rw [hpair] at hcp
        dsimp only
        simp only [lblNames_append, hcp,
          lblNames_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (st64Tail_allInstrs _ _ _ _), List.nil_append, List.append_nil]; rfl
      | none =>
        dsimp only
        have hcp := compileTierStoreTripleR_lblNames tab fl t i e
        rcases htr : compileTierStoreTripleR tab fl t i e with ⟨cp, rt, ri, re⟩
        rw [htr] at hcp
        dsimp only
        simp only [lblNames_append, hcp,
          lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (st64Tail_allInstrs _ _ _ _), List.nil_append, List.append_nil]; rfl
    have hsnd : (compileSR tab fl pfx lblId brkLbl retLbl isTail (.st64t a t i e)).2 = lblId := by
      dsimp only [compileSR]; cases t.constVal? <;> rfl
    exact ⟨by rw [hsnd]; exact Nat.le_refl _, by rw [h0]; exact List.nodup_nil, fun _ h => by rw [h0] at h; cases h⟩
  | st32t a t i e =>
    intro lblId brkLbl isTail
    have h0 : lblNames (compileSR tab fl pfx lblId brkLbl retLbl isTail (.st32t a t i e)).1 = [] := by
      dsimp only [compileSR]
      cases t.constVal? with
      | some wt =>
        dsimp only
        have hcp := compileStorePairR_lblNames tab fl i e
        rcases hpair : compileStorePairR tab fl i e with ⟨cp, ri, re⟩
        rw [hpair] at hcp
        dsimp only
        simp only [lblNames_append, hcp,
          lblNames_of_allInstrs (loadMemOffGp_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (st32tTail_allInstrs _ _ _ _), List.nil_append, List.append_nil]; rfl
      | none =>
        dsimp only
        have hcp := compileTierStoreTripleR_lblNames tab fl t i e
        rcases htr : compileTierStoreTripleR tab fl t i e with ⟨cp, rt, ri, re⟩
        rw [htr] at hcp
        dsimp only
        simp only [lblNames_append, hcp,
          lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (st32tTail_allInstrs _ _ _ _), List.nil_append, List.append_nil]; rfl
    have hsnd : (compileSR tab fl pfx lblId brkLbl retLbl isTail (.st32t a t i e)).2 = lblId := by
      dsimp only [compileSR]; cases t.constVal? <;> rfl
    exact ⟨by rw [hsnd]; exact Nat.le_refl _, by rw [h0]; exact List.nodup_nil, fun _ h => by rw [h0] at h; cases h⟩
  | brk =>
    intro lblId _ _; exact ⟨Nat.le_refl _, List.nodup_nil, fun _ h => by cases h⟩
  | abort e =>
    intro lblId brkLbl isTail
    dsimp only [compileSR]
    split
    · exact ⟨Nat.le_refl _, List.nodup_nil, fun _ h => by cases h⟩
    · have h0 : lblNames (compileETo tab fl 0 AbiReg.a0 e ++ [Asm.j abortLabel]) = [] := by
        simp only [lblNames_append, compileETo_lblNames, List.nil_append]; rfl
      exact ⟨Nat.le_refl _, by rw [h0]; exact List.nodup_nil, fun _ h => by rw [h0] at h; cases h⟩
  | ret es =>
    intro lblId brkLbl isTail
    have h0 : lblNames (compileSR tab fl pfx lblId brkLbl retLbl isTail (.ret es)).1 = [] :=
      compileRetR_lblNames tab fl retLbl isTail es
    exact ⟨Nat.le_refl _, by rw [h0]; exact List.nodup_nil, fun _ h => by rw [h0] at h; cases h⟩
  | «call» xs f args =>
    intro lblId brkLbl isTail
    have h0 : lblNames (compileSR tab fl pfx lblId brkLbl retLbl isTail (.call xs f args)).1 = [] := by
      have ht5 : lblNames (if fl.useT5Gp = true then [Asm.addi AbiReg.t5 AbiReg.gp 2047#12] else []) = [] := by
        split <;> rfl
      simp only [compileSR, lblNames_append, compileCallArgsR_lblNames, ht5,
        lblNames_of_allInstrs (copyResultsToLocalsR_allInstrs _ _ _),
        List.nil_append, List.append_nil]
      rfl
    exact ⟨Nat.le_refl _, by rw [h0]; exact List.nodup_nil, fun _ h => by rw [h0] at h; cases h⟩
  | seq s1 s2 ih1 ih2 =>
    intro lblId brkLbl isTail
    dsimp only [compileSR]
    cases tailCallRetMatch tab s1 s2 with
    | some v =>
      rcases v with ⟨xs, f, args, es⟩
      have h0 : lblNames (compileCallArgsR tab fl args ++ framePopItems fl ++ [Asm.j (fnLabel f)]) = [] := by
        simp only [lblNames_append, compileCallArgsR_lblNames,
          lblNames_of_allInstrs (framePopItems_allInstrs fl), List.nil_append]; rfl
      exact ⟨Nat.le_refl _, by rw [h0]; exact List.nodup_nil, fun _ h => by rw [h0] at h; cases h⟩
    | none =>
      rcases h1 : compileSR tab fl pfx lblId brkLbl retLbl false s1 with ⟨c1, id1⟩
      rcases h2 : compileSR tab fl pfx id1 brkLbl retLbl isTail s2 with ⟨c2, id2⟩
      obtain ⟨hle1, hnd1, hsp1⟩ := ih1 lblId brkLbl false
      obtain ⟨hle2, hnd2, hsp2⟩ := ih2 id1 brkLbl isTail
      rw [h1] at hle1 hnd1 hsp1; rw [h2] at hle2 hnd2 hsp2
      dsimp only at hle1 hnd1 hsp1 hle2 hnd2 hsp2 ⊢
      refine ⟨Nat.le_trans hle1 hle2, ?_, ?_⟩
      · rw [lblNames_append]
        refine nodup_append_disj hnd1 hnd2 (fun s hs1 hs2 => ?_)
        obtain ⟨t1, ht1, k1, _, hk1hi, heq1⟩ := hsp1 s hs1
        obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hsp2 s hs2
        have ⟨hk, _⟩ := dynLbl_inj ht1 ht2 (heq1.symm.trans heq2); omega
      · intro s hs
        rw [lblNames_append, List.mem_append] at hs
        rcases hs with hs | hs
        · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp1 s hs
          exact ⟨t, ht, k, hk1, Nat.lt_of_lt_of_le hk2 hle2, heq⟩
        · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp2 s hs
          exact ⟨t, ht, k, Nat.le_trans hle1 hk1, hk2, heq⟩
  | ite cond s1 s2 ih1 ih2 =>
    intro lblId brkLbl isTail
    by_cases hs2 : s2 = .skip
    · subst hs2
      dsimp only [compileSR]
      split
      · exact compileCR_lbls_spec tab fl 0 pfx cond lblId true _
      · let endLbl := pfx ++ "_endif_" ++ toString lblId
        rcases hc : compileCR tab fl 0 pfx (lblId + 1) cond false endLbl with ⟨cc, id1⟩
        rcases h1 : compileSR tab fl pfx id1 brkLbl retLbl false s1 with ⟨c1, id2⟩
        obtain ⟨hleC, hndC, hspC⟩ := compileCR_lbls_spec tab fl 0 pfx cond (lblId + 1) false endLbl
        obtain ⟨hle1, hnd1, hsp1⟩ := ih1 id1 brkLbl false
        rw [hc] at hleC hndC hspC; rw [h1] at hle1 hnd1 hsp1
        dsimp only at hleC hndC hspC hle1 hnd1 hsp1 ⊢
        have hend : endLbl = pfx ++ "_" ++ "endif" ++ "_" ++ Nat.repr lblId := by
          dsimp only [endLbl]; change pfx ++ ("_" ++ "endif" ++ "_") ++ Nat.repr lblId = _; simp only [String.append_assoc]
        have hlbl : lblNames (cc ++ c1 ++ [Asm.lbl (toString pfx ++ toString "_endif_" ++ toString lblId)]) =
            lblNames cc ++ lblNames c1 ++ [endLbl] := by
          simp only [lblNames_append, lblNames_singleton_lbl]; rfl
        refine ⟨by omega, ?_, ?_⟩
        · rw [hlbl]
          have hndC1 : (lblNames cc ++ lblNames c1).Nodup := by
            refine nodup_append_disj hndC hnd1 (fun s hsC hs1 => ?_)
            obtain ⟨t1, ht1, k1, _, hk1hi, heq1⟩ := hspC s hsC
            obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hsp1 s hs1
            have ⟨hk, _⟩ := dynLbl_inj ht1 ht2 (heq1.symm.trans heq2); omega
          refine nodup_append_disj hndC1 (by simp) (fun s hs hmem => ?_)
          simp only [List.mem_singleton] at hmem; subst hmem
          rcases List.mem_append.mp hs with hsC | hs1
          · obtain ⟨t, ht, k, hklo, _, heq⟩ := hspC _ hsC
            have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "endif") (by simp [dynTags]) (heq.symm.trans hend); omega
          · obtain ⟨t, ht, k, hklo, _, heq⟩ := hsp1 _ hs1
            have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "endif") (by simp [dynTags]) (heq.symm.trans hend); omega
        · intro s hs; rw [hlbl] at hs
          simp only [List.mem_append, List.mem_singleton] at hs
          rcases hs with (hsC | hs1) | rfl
          · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hspC s hsC
            exact ⟨t, ht, k, by omega, by omega, heq⟩
          · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp1 s hs1
            exact ⟨t, ht, k, by omega, hk2, heq⟩
          · exact ⟨"endif", by simp [dynTags], lblId, Nat.le_refl _, by omega, hend⟩
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
      · exact compileCR_lbls_spec tab fl 0 pfx cond lblId false _
      · let endLbl := pfx ++ "_endif_" ++ toString lblId
        rcases hc : compileCR tab fl 0 pfx (lblId + 1) cond true endLbl with ⟨cc, id1⟩
        rcases h2 : compileSR tab fl pfx id1 brkLbl retLbl false s2 with ⟨c2, id2⟩
        obtain ⟨hleC, hndC, hspC⟩ := compileCR_lbls_spec tab fl 0 pfx cond (lblId + 1) true endLbl
        obtain ⟨hle2, hnd2, hsp2⟩ := ih2 id1 brkLbl false
        rw [hc] at hleC hndC hspC; rw [h2] at hle2 hnd2 hsp2
        have hc' : compileCR tab fl 0 pfx (lblId + 1) cond true (toString pfx ++ toString "_endif_" ++ toString lblId) = (cc, id1) := hc
        dsimp only at hleC hndC hspC hle2 hnd2 hsp2 ⊢
        rw [hc']; dsimp only; rw [h2]; dsimp only
        have hend : endLbl = pfx ++ "_" ++ "endif" ++ "_" ++ Nat.repr lblId := by
          dsimp only [endLbl]; change pfx ++ ("_" ++ "endif" ++ "_") ++ Nat.repr lblId = _; simp only [String.append_assoc]
        have hlbl : lblNames (cc ++ c2 ++ [Asm.lbl (toString pfx ++ toString "_endif_" ++ toString lblId)]) =
            lblNames cc ++ lblNames c2 ++ [endLbl] := by
          simp only [lblNames_append, lblNames_singleton_lbl]; rfl
        refine ⟨by omega, ?_, ?_⟩
        · rw [hlbl]
          have hndC2 : (lblNames cc ++ lblNames c2).Nodup := by
            refine nodup_append_disj hndC hnd2 (fun s hsC hs2 => ?_)
            obtain ⟨t1, ht1, k1, _, hk1hi, heq1⟩ := hspC s hsC
            obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hsp2 s hs2
            have ⟨hk, _⟩ := dynLbl_inj ht1 ht2 (heq1.symm.trans heq2); omega
          refine nodup_append_disj hndC2 (by simp) (fun s hs hmem => ?_)
          simp only [List.mem_singleton] at hmem; subst hmem
          rcases List.mem_append.mp hs with hsC | hs2
          · obtain ⟨t, ht, k, hklo, _, heq⟩ := hspC _ hsC
            have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "endif") (by simp [dynTags]) (heq.symm.trans hend); omega
          · obtain ⟨t, ht, k, hklo, _, heq⟩ := hsp2 _ hs2
            have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "endif") (by simp [dynTags]) (heq.symm.trans hend); omega
        · intro s hs; rw [hlbl] at hs
          simp only [List.mem_append, List.mem_singleton] at hs
          rcases hs with (hsC | hs2) | rfl
          · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hspC s hsC
            exact ⟨t, ht, k, by omega, by omega, heq⟩
          · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp2 s hs2
            exact ⟨t, ht, k, by omega, hk2, heq⟩
          · exact ⟨"endif", by simp [dynTags], lblId, Nat.le_refl _, by omega, hend⟩
    have hceGen : compileSR tab fl pfx lblId brkLbl retLbl isTail (.ite cond s1 s2) =
        let elseLbl := s!"{pfx}_else_{lblId}"
        let endLbl := s!"{pfx}_endif_{lblId}"
        let (cc, id1) := compileCR tab fl 0 pfx (lblId + 1) cond false elseLbl
        let (c1, id2) := compileSR tab fl pfx id1 brkLbl retLbl false s1
        let (c2, id3) := compileSR tab fl pfx id2 brkLbl retLbl isTail s2
        let jEnd := if stmtMayFallthrough s1 then [Asm.j endLbl] else []
        (cc ++ c1 ++ jEnd ++ [Asm.lbl elseLbl] ++ c2 ++ [Asm.lbl endLbl], id3) := by
      cases s2 with | skip => contradiction | _ => cases s1 with | skip => contradiction | _ => rfl
    rw [hceGen]
    let elseLbl := pfx ++ "_else_" ++ toString lblId
    let endLbl := pfx ++ "_endif_" ++ toString lblId
    rcases hc : compileCR tab fl 0 pfx (lblId + 1) cond false elseLbl with ⟨cc, id1⟩
    rcases h1 : compileSR tab fl pfx id1 brkLbl retLbl false s1 with ⟨c1, id2⟩
    rcases h2 : compileSR tab fl pfx id2 brkLbl retLbl isTail s2 with ⟨c2, id3⟩
    obtain ⟨hleC, hndC, hspC⟩ := compileCR_lbls_spec tab fl 0 pfx cond (lblId + 1) false elseLbl
    obtain ⟨hle1, hnd1, hsp1⟩ := ih1 id1 brkLbl false
    obtain ⟨hle2, hnd2, hsp2⟩ := ih2 id2 brkLbl isTail
    rw [hc] at hleC hndC hspC; rw [h1] at hle1 hnd1 hsp1; rw [h2] at hle2 hnd2 hsp2
    have hc' : compileCR tab fl 0 pfx (lblId + 1) cond false (toString pfx ++ toString "_else_" ++ toString lblId) = (cc, id1) := hc
    dsimp only at hleC hndC hspC hle1 hnd1 hsp1 hle2 hnd2 hsp2 ⊢
    rw [hc']; dsimp only; rw [h1]; dsimp only; rw [h2]; dsimp only
    have helse : elseLbl = pfx ++ "_" ++ "else" ++ "_" ++ Nat.repr lblId := by
      dsimp only [elseLbl]; change pfx ++ ("_" ++ "else" ++ "_") ++ Nat.repr lblId = _; simp only [String.append_assoc]
    have hend : endLbl = pfx ++ "_" ++ "endif" ++ "_" ++ Nat.repr lblId := by
      dsimp only [endLbl]; change pfx ++ ("_" ++ "endif" ++ "_") ++ Nat.repr lblId = _; simp only [String.append_assoc]
    have hne : elseLbl ≠ endLbl := by
      intro heq
      rw [helse, hend] at heq
      have ⟨_, ht⟩ := dynLbl_inj (pfx := pfx) (t₁ := "else") (t₂ := "endif")
        (by simp [dynTags]) (by simp [dynTags]) heq
      simp at ht
    have hjEnd : lblNames (if stmtMayFallthrough s1 = true then
        [Asm.j (toString pfx ++ toString "_endif_" ++ toString lblId)] else []) = [] := by
      split <;> rfl
    have hlbl : lblNames (cc ++ c1 ++ (if stmtMayFallthrough s1 = true then
          [Asm.j (toString pfx ++ toString "_endif_" ++ toString lblId)] else []) ++
          [Asm.lbl (toString pfx ++ toString "_else_" ++ toString lblId)] ++ c2 ++
          [Asm.lbl (toString pfx ++ toString "_endif_" ++ toString lblId)]) =
        lblNames cc ++ lblNames c1 ++ [elseLbl] ++ lblNames c2 ++ [endLbl] := by
      simp only [lblNames_append, hjEnd, lblNames_singleton_lbl, List.append_nil]; rfl
    refine ⟨by omega, ?_, ?_⟩
    · rw [hlbl]
      have hndC1 : (lblNames cc ++ lblNames c1).Nodup := by
        refine nodup_append_disj hndC hnd1 (fun s hsC hs1 => ?_)
        obtain ⟨t1, ht1, k1, _, hk1hi, heq1⟩ := hspC s hsC
        obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hsp1 s hs1
        have ⟨hk, _⟩ := dynLbl_inj ht1 ht2 (heq1.symm.trans heq2); omega
      have hndC1e : (lblNames cc ++ lblNames c1 ++ [elseLbl]).Nodup := by
        refine nodup_append_disj hndC1 (by simp) (fun s hs hmem => ?_)
        simp only [List.mem_singleton] at hmem; subst hmem
        rcases List.mem_append.mp hs with hsC | hs1
        · obtain ⟨t, ht, k, hklo, _, heq⟩ := hspC _ hsC
          have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "else") (by simp [dynTags]) (heq.symm.trans helse); omega
        · obtain ⟨t, ht, k, hklo, _, heq⟩ := hsp1 _ hs1
          have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "else") (by simp [dynTags]) (heq.symm.trans helse); omega
      have hndC1e2 : (lblNames cc ++ lblNames c1 ++ [elseLbl] ++ lblNames c2).Nodup := by
        refine nodup_append_disj hndC1e hnd2 (fun s hs hs2 => ?_)
        obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hsp2 s hs2
        simp only [List.mem_append, List.mem_singleton] at hs
        rcases hs with (hsC | hs1) | rfl
        · obtain ⟨t, ht, k, _, hkhi, heq⟩ := hspC s hsC
          have ⟨hk, _⟩ := dynLbl_inj ht ht2 (heq.symm.trans heq2); omega
        · obtain ⟨t, ht, k, _, hkhi, heq⟩ := hsp1 s hs1
          have ⟨hk, _⟩ := dynLbl_inj ht ht2 (heq.symm.trans heq2); omega
        · have ⟨hk, _⟩ := dynLbl_inj (t₁ := "else") (by simp [dynTags]) ht2 (helse.symm.trans heq2); omega
      refine nodup_append_disj hndC1e2 (by simp) (fun s hs hmem => ?_)
      simp only [List.mem_singleton] at hmem; subst hmem
      simp only [List.mem_append, List.mem_singleton] at hs
      rcases hs with ((hsC | hs1) | hEq) | hs2
      · obtain ⟨t, ht, k, hklo, _, heq⟩ := hspC _ hsC
        have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "endif") (by simp [dynTags]) (heq.symm.trans hend); omega
      · obtain ⟨t, ht, k, hklo, _, heq⟩ := hsp1 _ hs1
        have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "endif") (by simp [dynTags]) (heq.symm.trans hend); omega
      · exact hne hEq.symm
      · obtain ⟨t, ht, k, hklo, _, heq⟩ := hsp2 _ hs2
        have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "endif") (by simp [dynTags]) (heq.symm.trans hend); omega
    · intro s hs
      rw [hlbl] at hs
      simp only [List.mem_append, List.mem_singleton] at hs
      rcases hs with (((hsC | hs1) | rfl) | hs2) | rfl
      · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hspC s hsC
        exact ⟨t, ht, k, by omega, by omega, heq⟩
      · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp1 s hs1
        exact ⟨t, ht, k, by omega, by omega, heq⟩
      · exact ⟨"else", by simp [dynTags], lblId, Nat.le_refl _, by omega, helse⟩
      · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hsp2 s hs2
        exact ⟨t, ht, k, by omega, hk2, heq⟩
      · exact ⟨"endif", by simp [dynTags], lblId, Nat.le_refl _, by omega, hend⟩
  | «while» cond body ih =>
    intro lblId _ _
    dsimp only [compileSR]
    let loopLbl := pfx ++ "_while_" ++ toString lblId
    let endLbl := pfx ++ "_endw_" ++ toString lblId
    rcases hc : compileCR tab fl 0 pfx (lblId + 1) cond false endLbl with ⟨cc, id1⟩
    rcases hb : compileSR tab fl pfx id1 (some endLbl) retLbl false body with ⟨cb, id2⟩
    obtain ⟨hleC, hndC, hspC⟩ := compileCR_lbls_spec tab fl 0 pfx cond (lblId + 1) false endLbl
    obtain ⟨hleB, hndB, hspB⟩ := ih id1 (some endLbl) false
    rw [hc] at hleC hndC hspC; rw [hb] at hleB hndB hspB
    dsimp only at hleC hndC hspC hleB hndB hspB ⊢
    have hloop : loopLbl = pfx ++ "_" ++ "while" ++ "_" ++ Nat.repr lblId := by
      dsimp only [loopLbl]; change pfx ++ ("_" ++ "while" ++ "_") ++ Nat.repr lblId = _; simp only [String.append_assoc]
    have hend : endLbl = pfx ++ "_" ++ "endw" ++ "_" ++ Nat.repr lblId := by
      dsimp only [endLbl]; change pfx ++ ("_" ++ "endw" ++ "_") ++ Nat.repr lblId = _; simp only [String.append_assoc]
    have hne : loopLbl ≠ endLbl := by
      intro heq
      rw [hloop, hend] at heq
      have ⟨_, ht⟩ := dynLbl_inj (pfx := pfx) (t₁ := "while") (t₂ := "endw")
        (by simp [dynTags]) (by simp [dynTags]) heq
      simp at ht
    have hwb : ∀ (r : Reg) (k : BitVec 12) (l1 l2 l3 : String),
        lblNames [Asm.beq r AbiReg.zero l1, Asm.addi r r k, Asm.j l2, Asm.lbl l3] = [l3] :=
      fun _ _ _ _ _ => rfl
    have hlbl : lblNames ([Asm.lbl (toString pfx ++ toString "_while_" ++ toString lblId)] ++
          cc ++ cb ++
          [Asm.beq AbiReg.s0 AbiReg.zero exhaustedLabel,
           Asm.addi AbiReg.s0 AbiReg.s0 (-1#12),
           Asm.j (toString pfx ++ toString "_while_" ++ toString lblId),
           Asm.lbl (toString pfx ++ toString "_endw_" ++ toString lblId)]) =
        [loopLbl] ++ lblNames cc ++ lblNames cb ++ [endLbl] := by
      simp only [lblNames_append, lblNames_singleton_lbl, hwb]; rfl
    refine ⟨by omega, ?_, ?_⟩
    · rw [hlbl]
      have hndCB : (lblNames cc ++ lblNames cb).Nodup := by
        refine nodup_append_disj hndC hndB (fun s hsC hsB => ?_)
        obtain ⟨t1, ht1, k1, _, hk1hi, heq1⟩ := hspC s hsC
        obtain ⟨t2, ht2, k2, hk2lo, _, heq2⟩ := hspB s hsB
        have ⟨hk, _⟩ := dynLbl_inj ht1 ht2 (heq1.symm.trans heq2); omega
      have hndLCB : ([loopLbl] ++ (lblNames cc ++ lblNames cb)).Nodup := by
        refine nodup_append_disj (by simp) hndCB (fun s hs1 hs2 => ?_)
        simp only [List.mem_singleton] at hs1; subst hs1
        rcases List.mem_append.mp hs2 with hsC | hsB
        · obtain ⟨t, ht, k, hklo, _, heq⟩ := hspC _ hsC
          have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "while") (by simp [dynTags]) (heq.symm.trans hloop); omega
        · obtain ⟨t, ht, k, hklo, _, heq⟩ := hspB _ hsB
          have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "while") (by simp [dynTags]) (heq.symm.trans hloop); omega
      have hndLCB' : ([loopLbl] ++ lblNames cc ++ lblNames cb).Nodup := by
        simpa [List.append_assoc] using hndLCB
      refine nodup_append_disj hndLCB' (by simp) (fun s hs hmem => ?_)
      simp only [List.mem_singleton] at hmem; subst hmem
      simp only [List.mem_append, List.mem_singleton] at hs
      rcases hs with (hEq | hsC) | hsB
      · exact hne hEq.symm
      · obtain ⟨t, ht, k, hklo, _, heq⟩ := hspC _ hsC
        have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "endw") (by simp [dynTags]) (heq.symm.trans hend); omega
      · obtain ⟨t, ht, k, hklo, _, heq⟩ := hspB _ hsB
        have ⟨hk, _⟩ := dynLbl_inj ht (t₂ := "endw") (by simp [dynTags]) (heq.symm.trans hend); omega
    · intro s hs
      rw [hlbl] at hs
      simp only [List.mem_append, List.mem_singleton] at hs
      rcases hs with ((rfl | hsC) | hsB) | rfl
      · exact ⟨"while", by simp [dynTags], lblId, Nat.le_refl _, by omega, hloop⟩
      · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hspC s hsC
        exact ⟨t, ht, k, by omega, by omega, heq⟩
      · obtain ⟨t, ht, k, hk1, hk2, heq⟩ := hspB s hsB
        exact ⟨t, ht, k, by omega, hk2, heq⟩
      · exact ⟨"endw", by simp [dynTags], lblId, Nat.le_refl _, by omega, hend⟩
  | copy64 d di src si n =>
    intro lblId brkLbl isTail
    let loopLbl := toString pfx ++ toString "_c64_" ++ toString lblId
    let doneLbl := toString pfx ++ toString "_c64_done_" ++ toString lblId
    have hloop : loopLbl = pfx ++ "_" ++ "c64" ++ "_" ++ Nat.repr lblId := by
      dsimp only [loopLbl]; change pfx ++ ("_" ++ "c64" ++ "_") ++ Nat.repr lblId = _; simp only [String.append_assoc]
    have hdone : doneLbl = pfx ++ "_" ++ "c64_done" ++ "_" ++ Nat.repr lblId := by
      dsimp only [doneLbl]; change pfx ++ ("_" ++ "c64_done" ++ "_") ++ Nat.repr lblId = _; simp only [String.append_assoc]
    have hne : loopLbl ≠ doneLbl := by
      intro heq
      rw [hloop, hdone] at heq
      have ⟨_, ht⟩ := dynLbl_inj (pfx := pfx) (t₁ := "c64") (t₂ := "c64_done")
        (by simp [dynTags]) (by simp [dynTags]) heq
      simp at ht
    have hlbl : lblNames (compileSR tab fl pfx lblId brkLbl retLbl isTail (.copy64 d di src si n)).1 =
        [loopLbl, doneLbl] := by
      simp only [compileSR, lblNames_append, evalWArrTierToTempR_lblNames, compileETo_lblNames,
        lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
        lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append, List.append_nil]
      rfl
    have hsnd : (compileSR tab fl pfx lblId brkLbl retLbl isTail (.copy64 d di src si n)).2 = lblId + 1 := rfl
    refine ⟨by rw [hsnd]; omega, ?_, ?_⟩
    · rw [hlbl]; simp [hne]
    · intro s hs; rw [hlbl] at hs; rw [hsnd]
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact ⟨"c64", by simp [dynTags], lblId, Nat.le_refl _, by omega, hloop⟩
      · simp only [List.mem_singleton] at hs'; subst hs'
        exact ⟨"c64_done", by simp [dynTags], lblId, Nat.le_refl _, by omega, hdone⟩
  | copy8w d di src si n =>
    intro lblId brkLbl isTail
    let loopLbl := toString pfx ++ toString "_c8w_" ++ toString lblId
    let doneLbl := toString pfx ++ toString "_c8w_done_" ++ toString lblId
    have hloop : loopLbl = pfx ++ "_" ++ "c8w" ++ "_" ++ Nat.repr lblId := by
      dsimp only [loopLbl]; change pfx ++ ("_" ++ "c8w" ++ "_") ++ Nat.repr lblId = _; simp only [String.append_assoc]
    have hdone : doneLbl = pfx ++ "_" ++ "c8w_done" ++ "_" ++ Nat.repr lblId := by
      dsimp only [doneLbl]; change pfx ++ ("_" ++ "c8w_done" ++ "_") ++ Nat.repr lblId = _; simp only [String.append_assoc]
    have hne : loopLbl ≠ doneLbl := by
      intro heq
      rw [hloop, hdone] at heq
      have ⟨_, ht⟩ := dynLbl_inj (pfx := pfx) (t₁ := "c8w") (t₂ := "c8w_done")
        (by simp [dynTags]) (by simp [dynTags]) heq
      simp at ht
    have hlbl : lblNames (compileSR tab fl pfx lblId brkLbl retLbl isTail (.copy8w d di src si n)).1 =
        [loopLbl, doneLbl] := by
      cases src
      · simp only [compileSR, lblNames_append, evalWArrTierToTempR_lblNames, compileETo_lblNames,
          lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append, List.append_nil]
        rfl
      · simp only [compileSR, lblNames_append, evalWArrTierToTempR_lblNames, compileETo_lblNames,
          lblNames_of_allInstrs (li_allInstrs _ _),
          lblNames_of_allInstrs (addImmOff_allInstrs _ _ _ _),
          lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
          lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append, List.append_nil]
        rfl
    have hsnd : (compileSR tab fl pfx lblId brkLbl retLbl isTail (.copy8w d di src si n)).2 = lblId + 1 := rfl
    refine ⟨by rw [hsnd]; omega, ?_, ?_⟩
    · rw [hlbl]; simp [hne]
    · intro s hs; rw [hlbl] at hs; rw [hsnd]
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact ⟨"c8w", by simp [dynTags], lblId, Nat.le_refl _, by omega, hloop⟩
      · simp only [List.mem_singleton] at hs'; subst hs'
        exact ⟨"c8w_done", by simp [dynTags], lblId, Nat.le_refl _, by omega, hdone⟩
  | scan8 x src i e c =>
    intro lblId brkLbl isTail
    let loopLbl := toString pfx ++ toString "_scan_" ++ toString lblId
    let doneLbl := toString pfx ++ toString "_scan_done_" ++ toString lblId
    have hloop : loopLbl = pfx ++ "_" ++ "scan" ++ "_" ++ Nat.repr lblId := by
      dsimp only [loopLbl]; change pfx ++ ("_" ++ "scan" ++ "_") ++ Nat.repr lblId = _; simp only [String.append_assoc]
    have hdone : doneLbl = pfx ++ "_" ++ "scan_done" ++ "_" ++ Nat.repr lblId := by
      dsimp only [doneLbl]; change pfx ++ ("_" ++ "scan_done" ++ "_") ++ Nat.repr lblId = _; simp only [String.append_assoc]
    have hne : loopLbl ≠ doneLbl := by
      intro heq
      rw [hloop, hdone] at heq
      have ⟨_, ht⟩ := dynLbl_inj (pfx := pfx) (t₁ := "scan") (t₂ := "scan_done")
        (by simp [dynTags]) (by simp [dynTags]) heq
      simp at ht
    have hlbl : lblNames (compileSR tab fl pfx lblId brkLbl retLbl isTail (.scan8 x src i e c)).1 =
        [loopLbl, doneLbl] := by
      have hjoin : ∀ (a b c1 d e1 f : List String),
          a = [] → b = [] → c1 = [] → d = [] → e1 = [loopLbl, doneLbl] → f = [] →
          a ++ b ++ c1 ++ d ++ e1 ++ f = [loopLbl, doneLbl] := by
        rintro _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl; rfl
      dsimp only [compileSR]
      simp only [lblNames_append]
      refine hjoin _ _ _ _ _ _ ?_ ?_ rfl (lblNames_of_allInstrs (addImmOff_allInstrs _ _ _ _)) rfl ?_
      · cases he : emitSimpleExprR tab fl AbiReg.a0 AbiReg.t5 e with
        | some ce =>
          dsimp only
          cases exprReg? fl.alloc i with
          | some _ =>
            dsimp only; rw [lblNames_append, lblNames_of_allInstrs (emitSimpleExprR_allInstrs he)]; rfl
          | none =>
            dsimp only
            simp only [lblNames_append, compileETo_lblNames,
              lblNames_of_allInstrs (emitSimpleExprR_allInstrs he), List.nil_append, List.append_nil]; rfl
        | none =>
          dsimp only
          simp only [lblNames_append, compileETo_lblNames,
            lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _),
            lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append]
      · cases src with
        | arr _ =>
          dsimp only
          simp only [lblNames_append, lblNames_of_allInstrs (loadMemOff_allInstrs _ _ _ _ _), List.nil_append]
        | rom _ =>
          dsimp only
          simp only [lblNames_append, lblNames_of_allInstrs (li_allInstrs _ _),
            lblNames_of_allInstrs (addImmOff_allInstrs _ _ _ _), List.nil_append]
      · cases fl.alloc.lookup x with
        | some _ => rfl
        | none =>
          dsimp only
          split
          · rfl
          · exact lblNames_of_allInstrs (storeMemOff_allInstrs _ _ _ _ _)
    have hsnd : (compileSR tab fl pfx lblId brkLbl retLbl isTail (.scan8 x src i e c)).2 = lblId + 1 := rfl
    refine ⟨by rw [hsnd]; omega, ?_, ?_⟩
    · rw [hlbl]; simp [hne]
    · intro s hs; rw [hlbl] at hs; rw [hsnd]
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact ⟨"scan", by simp [dynTags], lblId, Nat.le_refl _, by omega, hloop⟩
      · simp only [List.mem_singleton] at hs'; subst hs'
        exact ⟨"scan_done", by simp [dynTags], lblId, Nat.le_refl _, by omega, hdone⟩

end CompileSRLblsSpec

/-- Fixed suffixes attached to `fnLabel f` by `compileFn`. -/
def fixedFnSuffixes : List String :=
  ["", "_ret0", "_epilogue", "_errstub", "_exhstub", "_abort0stub"]

/-- Valid suffixes of `"fn_" ++ f` for any label inside `compileFn tab f fd`. -/
def ValidFnSuffix (suff : String) : Prop :=
  suff ∈ fixedFnSuffixes ∨
    ∃ tag ∈ dynTags, ∃ k : Nat, suff = "_" ++ tag ++ "_" ++ Nat.repr k

private theorem fixed_append_ne_dyn {fa fb suf tag : String} {k : Nat}
    (hs : suf ∈ fixedFnSuffixes) (hne : suf ≠ "")
    (hc : fa.toList ++ suf.toList = fb.toList ++ ("_" ++ tag ++ "_" ++ Nat.repr k).toList) :
    False := by
  have hrev := congrArg List.reverse hc
  simp only [List.reverse_append, String.toList_append, List.append_assoc] at hrev
  have hd : ∀ c ∈ (Nat.repr k).toList.reverse, c.isDigit = true :=
    fun c hc => nat_repr_toList_isDigit k c (by simpa using hc)
  have hneK := nat_repr_toList_ne_nil k
  cases hkrev : (Nat.repr k).toList.reverse with
  | nil => exact hneK (List.reverse_eq_nil_iff.mp hkrev)
  | cons d₀ dr =>
    have hd0 : d₀.isDigit = true := hd d₀ (by rw [hkrev]; simp)
    rw [hkrev] at hrev
    simp only [fixedFnSuffixes, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · have hr : "_ret0".toList.reverse = ['0', 't', 'e', 'r', '_'] := rfl
      have h_ : "_".toList.reverse = ['_'] := rfl
      rw [hr, h_] at hrev
      cases dr with
      | nil =>
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at hrev
        have : 't' = '_' := hrev.2.1; contradiction
      | cons d₁ _ =>
        have hd1 : d₁.isDigit = true := hd d₁ (by rw [hkrev]; simp)
        simp only [List.cons_append, List.cons.injEq] at hrev
        have h' : 't' = d₁ := hrev.2.1
        rw [← h'] at hd1; simp at hd1
    · change ['e', 'u', 'g', 'o', 'l', 'i', 'p', 'e', '_'] ++ fa.toList.reverse = _ at hrev
      simp only [List.cons_append, List.cons.injEq] at hrev
      have h' : 'e' = d₀ := hrev.1
      subst h'; simp at hd0
    · change ['b', 'u', 't', 's', 'r', 'r', 'e', '_'] ++ fa.toList.reverse = _ at hrev
      simp only [List.cons_append, List.cons.injEq] at hrev
      have h' : 'b' = d₀ := hrev.1
      subst h'; simp at hd0
    · change ['b', 'u', 't', 's', 'h', 'x', 'e', '_'] ++ fa.toList.reverse = _ at hrev
      simp only [List.cons_append, List.cons.injEq] at hrev
      have h' : 'b' = d₀ := hrev.1
      subst h'; simp at hd0
    · change ['b', 'u', 't', 's', '0', 't', 'r', 'o', 'b', 'a', '_'] ++ fa.toList.reverse = _ at hrev
      simp only [List.cons_append, List.cons.injEq] at hrev
      have h' : 'b' = d₀ := hrev.1
      subst h'; simp at hd0

private theorem fixedFnSuffix_ne_dyn {suf : String} (hs : suf ∈ fixedFnSuffixes)
    {tag : String} (_ht : tag ∈ dynTags) (k : Nat) :
    suf ≠ "_" ++ tag ++ "_" ++ Nat.repr k := by
  intro heq
  by_cases hne : suf = ""
  · subst hne
    have h0 := congrArg String.toList heq
    simp [String.toList_append] at h0
  · exact fixed_append_ne_dyn (fa := "") (fb := "") hs hne (by simpa using congrArg String.toList heq)

theorem lblNames_map_retarget (o1 n1 o2 : String) (n2? : Option String)
    (xs : List AsmItem) :
    lblNames (xs.map (retargetBranchItem o1 n1 o2 n2?)) = lblNames xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    cases x with
    | label s =>
      change s :: lblNames (rest.map (retargetBranchItem o1 n1 o2 n2?)) = s :: lblNames rest
      rw [ih]
    | instr _ | j _ | «call» _ | br _ _ _ _ | brLong _ _ _ _ =>
      change lblNames (rest.map (retargetBranchItem o1 n1 o2 n2?)) = lblNames rest
      exact ih

theorem compileFn_lbls_spec (tab : Tab) (f : FnName) (fd : FunDecl) :
    (lblNames (compileFn tab f fd)).Nodup ∧
    (∀ s ∈ lblNames (compileFn tab f fd), ∃ suff, ValidFnSuffix suff ∧ s = fnLabel f ++ suff) := by
  let fl := fnFrameLayoutFor tab fd
  let pfx := fnLabel f
  let epilogue := pfx ++ "_epilogue"
  let canTailElide := !stmtMayFallthrough fd.body
  rcases hb : compileSR tab fl pfx 0 none epilogue canTailElide fd.body with ⟨bodyCode, idEnd⟩
  obtain ⟨_, hndBody, hspBody⟩ := compileSR_lbls_spec tab fl pfx epilogue fd.body 0 none canTailElide
  rw [hb] at hndBody hspBody
  dsimp only at hndBody hspBody
  have hfixedMem : ∀ x ∈ fixedFnSuffixes.map (pfx ++ ·), x ∉ lblNames bodyCode := by
    intro x hx hxb
    simp only [List.mem_map] at hx
    obtain ⟨suf, hsuf, rfl⟩ := hx
    obtain ⟨tag, htag, k, _, _, heq⟩ := hspBody (pfx ++ suf) hxb
    have hc : pfx.toList ++ suf.toList = pfx.toList ++ ("_" ++ tag ++ "_" ++ Nat.repr k).toList := by
      simpa [String.toList_append] using congrArg String.toList heq
    have hsf := String.toList_inj.mp (List.append_cancel_left hc)
    exact fixedFnSuffix_ne_dyn hsuf htag k hsf
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
  let prologue : List AsmItem :=
    [Asm.lbl pfx] ++ framePush ++ copyParamsR fl fd.nparams ++ zeroLocalsR fl fd ++ t5Init
  let hasErr := hasBranchTo errLabel prologue || hasBranchTo errLabel bodyCode
  let hasExh := hasBranchTo exhaustedLabel bodyCode
  let hasAb0 := stmtHasAbort0 fd.body
  let needRetarget := hasErr || hasExh
  let tailLbls : List String :=
    [pfx ++ "_ret0", pfx ++ "_epilogue"] ++
      (if needRetarget then [pfx ++ "_errstub"] else []) ++
      (if hasExh then [pfx ++ "_exhstub"] else []) ++
      (if hasAb0 then [pfx ++ "_abort0stub"] else [])
  have hpushLbl : lblNames framePush = [] := by
    dsimp only [framePush]
    split
    · rfl
    · have hra : lblNames (if fl.isLeaf = true then [] else [Asm.sd AbiReg.sp AbiReg.ra 0#12]) = [] := by
        split <;> rfl
      simp only [lblNames_append, lblNames_of_allInstrs (li_allInstrs _ _), hra,
        lblNames_of_allInstrs (saveCalleeRegs_allInstrs fl), List.nil_append, List.append_nil]
      rfl
  have ht5Lbl : lblNames t5Init = [] := by
    dsimp only [t5Init]; split <;> rfl
  have hproLbl : lblNames prologue = [pfx] := by
    dsimp only [prologue]
    simp only [lblNames_append, lblNames_singleton_lbl, hpushLbl, ht5Lbl,
      lblNames_of_allInstrs (copyParamsR_allInstrs fl fd.nparams),
      lblNames_of_allInstrs (zeroLocalsR_allInstrs fl fd), List.append_nil]
  have hftLbl : lblNames (if stmtMayFallthrough fd.body = true then copyTempsToResultsR tab fl 0 0 else []) = [] := by
    split
    · exact lblNames_of_allInstrs (copyTempsToResultsR_allInstrs _ _ _ _)
    · rfl
  have htotal : lblNames (compileFn tab f fd) =
      [pfx] ++ lblNames bodyCode ++ tailLbls := by
    have hb' : compileSR tab fl (fnLabel f) 0 none
        (toString (fnLabel f) ++ toString "_epilogue") (!stmtMayFallthrough fd.body) fd.body =
        (bodyCode, idEnd) := hb
    have hfnEq : compileFn tab f fd =
        (if needRetarget then
          prologue.map (retargetBranchItem errLabel (toString (fnLabel f) ++ toString "_errstub") exhaustedLabel (if hasExh then some (toString (fnLabel f) ++ toString "_exhstub") else none)) ++
          bodyCode.map (retargetBranchItem errLabel (toString (fnLabel f) ++ toString "_errstub") exhaustedLabel (if hasExh then some (toString (fnLabel f) ++ toString "_exhstub") else none))
         else prologue ++ bodyCode) ++
        ([Asm.lbl (toString (fnLabel f) ++ toString "_ret0")] ++
          (if stmtMayFallthrough fd.body then copyTempsToResultsR tab fl 0 0 else [])) ++
        ([Asm.lbl (toString (fnLabel f) ++ toString "_epilogue")] ++ framePopItems fl ++ [Asm.ret]) ++
        ((if needRetarget then [Asm.lbl (toString (fnLabel f) ++ toString "_errstub"), Asm.j errLabel] else []) ++
         (if hasExh then [Asm.lbl (toString (fnLabel f) ++ toString "_exhstub"), Asm.j exhaustedLabel] else []) ++
         (if hasAb0 then [Asm.lbl (toString (fnLabel f) ++ toString "_abort0stub"), Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.j abortLabel] else [])) := by
      dsimp only [compileFn]
      change (if (hasBranchTo errLabel prologue ||
          hasBranchTo errLabel (compileSR tab fl (fnLabel f) 0 none (toString (fnLabel f) ++ toString "_epilogue") (!stmtMayFallthrough fd.body) fd.body).1 ||
          hasBranchTo exhaustedLabel (compileSR tab fl (fnLabel f) 0 none (toString (fnLabel f) ++ toString "_epilogue") (!stmtMayFallthrough fd.body) fd.body).1) then
        prologue.map (retargetBranchItem errLabel (toString (fnLabel f) ++ toString "_errstub") exhaustedLabel
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
       (if hasAb0 then [Asm.lbl (toString (fnLabel f) ++ toString "_abort0stub"), Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.j abortLabel] else [])) = _
      rw [hb']
    rw [hfnEq]
    have hmain : lblNames (if needRetarget = true then
        prologue.map (retargetBranchItem errLabel (toString (fnLabel f) ++ toString "_errstub") exhaustedLabel (if hasExh then some (toString (fnLabel f) ++ toString "_exhstub") else none)) ++
        bodyCode.map (retargetBranchItem errLabel (toString (fnLabel f) ++ toString "_errstub") exhaustedLabel (if hasExh then some (toString (fnLabel f) ++ toString "_exhstub") else none))
      else prologue ++ bodyCode) = [pfx] ++ lblNames bodyCode := by
      split
      · rw [lblNames_append, lblNames_map_retarget, lblNames_map_retarget, hproLbl]
      · rw [lblNames_append, hproLbl]
    have hstub1 : lblNames (if needRetarget = true then
        [Asm.lbl (toString (fnLabel f) ++ toString "_errstub"), Asm.j errLabel] else []) =
        (if needRetarget then [pfx ++ "_errstub"] else []) := by
      split <;> rfl
    have hstub2 : lblNames (if hasExh = true then
        [Asm.lbl (toString (fnLabel f) ++ toString "_exhstub"), Asm.j exhaustedLabel] else []) =
        (if hasExh then [pfx ++ "_exhstub"] else []) := by
      split <;> rfl
    have hstub3 : lblNames (if hasAb0 = true then
        [Asm.lbl (toString (fnLabel f) ++ toString "_abort0stub"), Asm.addi AbiReg.a0 AbiReg.zero 0#12, Asm.j abortLabel] else []) =
        (if hasAb0 then [pfx ++ "_abort0stub"] else []) := by
      split <;> rfl
    have hret : lblNames [Asm.ret] = [] := rfl
    simp only [lblNames_append, hmain, hftLbl, lblNames_of_allInstrs (framePopItems_allInstrs fl),
      hret, hstub1, hstub2, hstub3, lblNames_singleton_lbl, List.append_nil]
    simp only [List.append_assoc, tailLbls]
    rfl
  have hsub : ∀ {a b c : List String}, (a ++ c).Nodup → b.Nodup → (∀ x ∈ a ++ c, x ∉ b) →
      (a ++ b ++ c).Nodup := by
    intro a b c hac hb hdis
    rw [List.nodup_append] at hac
    refine nodup_append_disj (nodup_append_disj hac.1 hb (fun x hxa hxb => hdis x (by simp [hxa]) hxb))
      hac.2.1 (fun x hx hxc => ?_)
    · rcases List.mem_append.mp hx with hxa | hxb
      · exact hac.2.2 x hxa _ hxc rfl
      · exact hdis _ (by simp [hxc]) hxb
  have hsublist : ([pfx] ++ tailLbls).Sublist (fixedFnSuffixes.map (pfx ++ ·)) := by
    have hp0 : [pfx] = [pfx ++ ""] := by simp
    have hs1 : (if needRetarget = true then [pfx ++ "_errstub"] else []).Sublist [pfx ++ "_errstub"] := by
      split <;> simp
    have hs2 : (if hasExh = true then [pfx ++ "_exhstub"] else []).Sublist [pfx ++ "_exhstub"] := by
      split <;> simp
    have hs3 : (if hasAb0 = true then [pfx ++ "_abort0stub"] else []).Sublist [pfx ++ "_abort0stub"] := by
      split <;> simp
    have hfull : fixedFnSuffixes.map (pfx ++ ·) =
        ([pfx ++ "", pfx ++ "_ret0", pfx ++ "_epilogue"] ++ [pfx ++ "_errstub"] ++ [pfx ++ "_exhstub"] ++ [pfx ++ "_abort0stub"]) := by
      simp [fixedFnSuffixes]
    rw [hfull]
    have hrew : [pfx] ++ tailLbls =
        [pfx ++ "", pfx ++ "_ret0", pfx ++ "_epilogue"] ++
          (if needRetarget then [pfx ++ "_errstub"] else []) ++
          (if hasExh then [pfx ++ "_exhstub"] else []) ++
          (if hasAb0 then [pfx ++ "_abort0stub"] else []) := by
      dsimp only [tailLbls]; rw [hp0]; simp [List.append_assoc]
    rw [hrew]
    exact (((List.Sublist.refl _).append hs1).append hs2).append hs3
  refine ⟨?_, ?_⟩
  · rw [htotal]
    refine hsub (a := [pfx]) (b := lblNames bodyCode) (c := tailLbls) ?_ hndBody ?_
    · have hinj : Function.Injective (fun s => pfx ++ s) := fun s₁ s₂ heq => by
        have hchars : pfx.toList ++ s₁.toList = pfx.toList ++ s₂.toList := by
          simpa [String.toList_append] using congrArg String.toList heq
        exact String.toList_inj.mp (List.append_cancel_left hchars)
      have hndAll : (fixedFnSuffixes.map (pfx ++ ·)).Nodup :=
        nodup_map_inj hinj (by decide : fixedFnSuffixes.Nodup)
      exact hndAll.sublist hsublist
    · intro x hx hxb
      exact hfixedMem x (hsublist.subset hx) hxb
  · intro s hs
    rw [htotal] at hs
    simp only [List.mem_append] at hs
    rcases hs with (hsP | hsB) | hsT
    · have hmem : s ∈ fixedFnSuffixes.map (pfx ++ ·) := hsublist.subset (List.mem_append_left _ hsP)
      rw [List.mem_map] at hmem
      obtain ⟨suf, hsuf, rfl⟩ := hmem
      exact ⟨suf, Or.inl hsuf, rfl⟩
    · obtain ⟨tag, htag, k, _, _, heq⟩ := hspBody s hsB
      exact ⟨"_" ++ tag ++ "_" ++ Nat.repr k, Or.inr ⟨tag, htag, k, rfl⟩, by simpa [String.append_assoc] using heq⟩
    · have hmem : s ∈ fixedFnSuffixes.map (pfx ++ ·) := hsublist.subset (List.mem_append_right _ hsT)
      rw [List.mem_map] at hmem
      obtain ⟨suf, hsuf, rfl⟩ := hmem
      exact ⟨suf, Or.inl hsuf, rfl⟩

/-! ### Disjointness Across Distinct Safe Function Names -/

private def isPrefixChars : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | p :: ps, x :: xs => p == x && isPrefixChars ps xs

private def fixedSufRev : List (List Char) :=
  ["_ret0", "_epilogue", "_errstub", "_exhstub", "_abort0stub"].map (fun s => s.toList.reverse)

private def dynTagRev : List (List Char) :=
  ["_and_", "_or_", "_else_", "_endif_", "_while_", "_endw_",
   "_c64_", "_c64_done_", "_c8w_", "_c8w_done_", "_scan_", "_scan_done_"].map (fun s => s.toList.reverse)

private def dropDigitsRev : List Char → Bool → List Char × Bool
  | c :: cs, seen => if c.isDigit then dropDigitsRev cs true else (c :: cs, seen)
  | [], seen => ([], seen)

/-- Fast single-pass kernel check ensuring no function name ends with any `compileFn` label suffix. -/
def fnCharsSafeFast (cs : List Char) : Bool :=
  match cs with
  | [] => false
  | _ =>
    let rev := cs.reverse
    if fixedSufRev.any (fun sr => isPrefixChars sr rev) then false
    else
      let (rest, seenDigit) := dropDigitsRev rev false
      !seenDigit || !(dynTagRev.any (fun tr => isPrefixChars tr rest))

private theorem isPrefixChars_eq_true {p x : List Char} (h : isPrefixChars p x = true) :
    ∃ r, x = p ++ r := by
  induction p generalizing x with
  | nil => exact ⟨x, rfl⟩
  | cons a ps ih =>
    cases x with
    | nil => simp [isPrefixChars] at h
    | cons b xs =>
      simp only [isPrefixChars, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨r, hr⟩ := ih h.2
      exact ⟨r, by simp [h.1, hr]⟩

private theorem dropDigitsRev_append_digits {a d : List Char}
    (ha : match a with | [] => True | c :: _ => c.isDigit = false)
    (hd : ∀ c ∈ d, c.isDigit = true) :
    ∀ seen, dropDigitsRev (d ++ a) seen = (a, seen || !d.isEmpty) := by
  induction d with
  | nil =>
    intro seen
    cases a with
    | nil => simp [dropDigitsRev]
    | cons x xs =>
      have hx : x.isDigit = false := ha
      simp [dropDigitsRev, hx]
  | cons x xs ih =>
    intro seen
    have hx : x.isDigit = true := hd x (by simp)
    simp only [List.cons_append, dropDigitsRev, hx, ↓reduceIte]
    rw [ih (fun y hy => hd y (by simp [hy])) true]
    simp

private theorem isPrefixChars_of_append_eq {p q r s : List Char} (h : p ++ r = q ++ s) :
    (p.length ≤ q.length → isPrefixChars p q = true) ∧
    (q.length ≤ p.length → isPrefixChars q p = true) := by
  induction p generalizing q with
  | nil => exact ⟨fun _ => rfl, fun hlen => by cases q with | nil => rfl | cons _ _ => simp at hlen⟩
  | cons a p ih =>
    cases q with
    | nil => exact ⟨fun hlen => by simp at hlen, fun _ => rfl⟩
    | cons b q' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, htail⟩ := h
      have ⟨h1, h2⟩ := ih htail
      exact ⟨fun hlen => by simpa [isPrefixChars] using h1 (Nat.le_of_succ_le_succ hlen),
             fun hlen => by simpa [isPrefixChars] using h2 (Nat.le_of_succ_le_succ hlen)⟩

private theorem fnCharsSafeFast_no_suffix {f suff : String}
    (hf : fnCharsSafeFast f.toList = true) (hsuf : ValidFnSuffix suff) (hne : suff ≠ "") :
    ¬ (∃ g : String, f = g ++ suff) := by
  intro ⟨g, hg⟩
  have hf_ne : f.toList ≠ [] := by
    intro he
    simp [he, fnCharsSafeFast] at hf
  have hfn : (if fixedSufRev.any (fun sr => isPrefixChars sr f.toList.reverse) = true then false
      else !(dropDigitsRev f.toList.reverse false).2 ||
           !(dynTagRev.any (fun tr => isPrefixChars tr (dropDigitsRev f.toList.reverse false).1))) = true := by
    cases hcs : f.toList with
    | nil => exact absurd hcs hf_ne
    | cons c cs =>
      have hf' := hf
      dsimp only [fnCharsSafeFast] at hf'
      rw [hcs] at hf'
      exact hf'
  have hfrev : f.toList.reverse = suff.toList.reverse ++ g.toList.reverse := by
    have := congrArg (fun x => x.toList.reverse) hg
    simpa [String.toList_append, List.reverse_append] using this
  rcases hsuf with hfix | ⟨tag, htag, k, rfl⟩
  · have hpre : isPrefixChars suff.toList.reverse f.toList.reverse = true := by
      rw [hfrev]
      clear hf hf_ne hfn hg hfrev hne hfix
      induction suff.toList.reverse with
      | nil => rfl
      | cons c cs ih => simp [isPrefixChars, ih]
    have hany : fixedSufRev.any (fun sr => isPrefixChars sr f.toList.reverse) = true := by
      rw [List.any_eq_true]
      refine ⟨suff.toList.reverse, ?_, hpre⟩
      simp only [fixedFnSuffixes, List.mem_cons, List.not_mem_nil, or_false] at hfix
      rcases hfix with rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl hne
      all_goals simp [fixedSufRev]
    rw [hany] at hfn
    cases hfn
  · have hdig : ∀ c ∈ (Nat.repr k).toList.reverse, c.isDigit = true := by
      intro c hc
      exact nat_repr_toList_isDigit k c (by simpa using hc)
    have hneK : (Nat.repr k).toList.reverse ≠ [] := by
      simp
    have htagEnd : (("_" ++ tag ++ "_").toList.reverse ++ g.toList.reverse) =
        '_' :: (tag.toList.reverse ++ '_' :: g.toList.reverse) := by
      simp [String.toList_append, List.reverse_append, List.append_assoc]
    have hdrop : dropDigitsRev f.toList.reverse false =
        (("_" ++ tag ++ "_").toList.reverse ++ g.toList.reverse, true) := by
      have hfrev' : f.toList.reverse =
          (Nat.repr k).toList.reverse ++ ("_" ++ tag ++ "_").toList.reverse ++ g.toList.reverse := by
        have := congrArg (fun x => x.toList.reverse) hg
        simpa [String.toList_append, List.reverse_append, List.append_assoc] using this
      rw [hfrev', List.append_assoc, dropDigitsRev_append_digits]
      · simp
      · rw [htagEnd]; rfl
      · exact hdig
    have hpre : isPrefixChars ("_" ++ tag ++ "_").toList.reverse
        (("_" ++ tag ++ "_").toList.reverse ++ g.toList.reverse) = true := by
      have go : ∀ (xs ys : List Char), isPrefixChars xs (xs ++ ys) = true := by
        intro xs ys; induction xs with | nil => rfl | cons x xs ih => simp [isPrefixChars, ih]
      exact go _ _
    have hanyDyn : dynTagRev.any (fun tr =>
        isPrefixChars tr (("_" ++ tag ++ "_").toList.reverse ++ g.toList.reverse)) = true := by
      rw [List.any_eq_true]
      refine ⟨("_" ++ tag ++ "_").toList.reverse, ?_, hpre⟩
      simp only [dynTagRev, List.mem_map]
      refine ⟨"_" ++ tag ++ "_", ?_, rfl⟩
      simp only [dynTags, List.mem_cons, List.not_mem_nil, or_false] at htag
      rcases htag with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp
    by_cases hfixAny : fixedSufRev.any (fun sr => isPrefixChars sr f.toList.reverse) = true
    · rw [hfixAny] at hfn; cases hfn
    · rw [List.any_eq_true] at hanyDyn
      obtain ⟨tr, htrM, htrP⟩ := hanyDyn
      simp [hfixAny, hdrop] at hfn
      rw [htagEnd] at htrP
      exact Bool.false_ne_true ((hfn tr htrM).symm.trans htrP)

private theorem tag_no_underscore_suffix {t₁ t₂ : String} (ht1 : t₁ ∈ dynTags) (ht2 : t₂ ∈ dynTags)
    {xs₁ xs₂ : List Char} (heq : xs₁ ++ ('_' :: t₁.toList) = xs₂ ++ ('_' :: t₂.toList)) :
    t₁ = t₂ := by
  have hrev := congrArg List.reverse heq
  have hrev' : ('_' :: t₁.toList).reverse ++ xs₁.reverse =
      ('_' :: t₂.toList).reverse ++ xs₂.reverse := by
    simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using hrev
  have hcheck : dynTags.all (fun a => dynTags.all (fun b =>
      a == b || (!isPrefixChars ('_' :: a.toList).reverse ('_' :: b.toList).reverse &&
                 !isPrefixChars ('_' :: b.toList).reverse ('_' :: a.toList).reverse))) = true := by
    decide
  rw [List.all_eq_true] at hcheck
  have h1 := hcheck t₁ ht1
  rw [List.all_eq_true] at h1
  have h2 := h1 t₂ ht2
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true'] at h2
  rcases h2 with rfl | ⟨hnp1, hnp2⟩
  · rfl
  · exfalso
    have hsplit := isPrefixChars_of_append_eq hrev'
    rcases Nat.le_total ('_' :: t₁.toList).reverse.length ('_' :: t₂.toList).reverse.length with hle | hle
    · have hp := hsplit.1 hle; rw [hnp1] at hp; cases hp
    · have hp := hsplit.2 hle; rw [hnp2] at hp; cases hp

theorem validFnSuffix_suffix_inj {f₁ f₂ s₁ s₂ : String}
    (hf1 : fnCharsSafeFast f₁.toList = true) (hf2 : fnCharsSafeFast f₂.toList = true)
    (hs1 : ValidFnSuffix s₁) (hs2 : ValidFnSuffix s₂)
    (heq : fnLabel f₁ ++ s₁ = fnLabel f₂ ++ s₂) :
    f₁ = f₂ := by
  have hf_eq : f₁ ++ s₁ = f₂ ++ s₂ := by
    have hc : ("fn_".toList ++ f₁.toList ++ s₁.toList) = ("fn_".toList ++ f₂.toList ++ s₂.toList) := by
      simpa [fnLabel, String.toList_append] using congrArg String.toList heq
    rw [List.append_assoc, List.append_assoc] at hc
    have := List.append_cancel_left hc
    simpa [String.toList_append] using String.toList_inj.mp (by simpa [String.toList_append] using this)
  by_cases h1 : s₁ = ""
  · subst h1
    by_cases h2 : s₂ = ""
    · subst h2; simpa using hf_eq
    · exfalso; exact fnCharsSafeFast_no_suffix hf1 hs2 h2 ⟨f₂, by simpa using hf_eq⟩
  · by_cases h2 : s₂ = ""
    · subst h2
      exfalso; exact fnCharsSafeFast_no_suffix hf2 hs1 h1 ⟨f₁, by simpa using hf_eq.symm⟩
    · have hne_both : ∀ (suf₁ suf₂ : String), suf₁ ∈ fixedFnSuffixes → suf₁ ≠ "" →
          suf₂ ∈ fixedFnSuffixes → suf₂ ≠ "" →
          f₁.toList ++ suf₁.toList = f₂.toList ++ suf₂.toList → suf₁ = suf₂ := by
        intro suf₁ suf₂ ha hna hb hnb hc
        have hrev : suf₁.toList.reverse ++ f₁.toList.reverse =
            suf₂.toList.reverse ++ f₂.toList.reverse := by
          simpa [List.reverse_append] using congrArg List.reverse hc
        have hcheck : fixedFnSuffixes.all (fun a => fixedFnSuffixes.all (fun b =>
            a == "" || b == "" || a == b ||
            (!isPrefixChars a.toList.reverse b.toList.reverse &&
             !isPrefixChars b.toList.reverse a.toList.reverse))) = true := by
          decide
        rw [List.all_eq_true] at hcheck
        have h1' := hcheck suf₁ ha
        rw [List.all_eq_true] at h1'
        have h2' := h1' suf₂ hb
        simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true'] at h2'
        rcases h2' with ((rfl | rfl) | rfl) | ⟨hnp1, hnp2⟩
        · exact absurd rfl hna
        · exact absurd rfl hnb
        · rfl
        · exfalso
          have hsplit := isPrefixChars_of_append_eq hrev
          rcases Nat.le_total suf₁.toList.reverse.length suf₂.toList.reverse.length with hle | hle
          · have hp := hsplit.1 hle; rw [hnp1] at hp; cases hp
          · have hp := hsplit.2 hle; rw [hnp2] at hp; cases hp
      have hc0 := congrArg String.toList hf_eq
      simp only [String.toList_append] at hc0
      rcases hs1 with hs1fix | ⟨t1, ht1, k1, rfl⟩
      · rcases hs2 with hs2fix | ⟨t2, ht2, k2, rfl⟩
        · have hsuf := hne_both s₁ s₂ hs1fix h1 hs2fix h2 hc0
          subst hsuf
          exact String.toList_inj.mp (List.append_cancel_right hc0)
        · exact False.elim (fixed_append_ne_dyn hs1fix h1 hc0)
      · rcases hs2 with hs2fix | ⟨t2, ht2, k2, rfl⟩
        · exact False.elim (fixed_append_ne_dyn hs2fix h2 hc0.symm)
        · have hc1 : (f₁.toList ++ ('_' :: t1.toList)) ++ '_' :: (Nat.repr k1).toList =
              (f₂.toList ++ ('_' :: t2.toList)) ++ '_' :: (Nat.repr k2).toList := by
            simpa [String.toList_append, List.append_assoc] using hc0
          obtain ⟨hft, _⟩ := list_eq_append_sep_right
            (nat_repr_not_mem_underscore k1) (nat_repr_not_mem_underscore k2) hc1
          have ht : t1 = t2 := tag_no_underscore_suffix ht1 ht2 hft
          subst ht
          have hft' : f₁.toList = f₂.toList := List.append_cancel_right hft
          exact String.toList_inj.mp hft'


end ConAgua.RISCV.Bridge
