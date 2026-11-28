-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaBlockCensus
public import Intel.TlaBlock2dPlain
public import Intel.TlaMainloopDpas
public import Intel.TlaAlu

@[expose] public section

/-!
# Instruction schedule of the SYCL-TLA mainloop

This module classifies every mainloop instruction into one of ten kinds and
records where the barrier and the jumps sit:

* 152 moves, 8 predicated ALU ops, 130 predicated block2d ops, 7 plain
  block2d loads, 32 DPAS, 102 `sync.nop`, 1 `sync.bar`, 2 jumps, 4 labels and
  7 other scalar forms (445 total),
* the single barrier is at PC 1396 and every DPAS precedes it,
* the in-block jumps are at PCs 991 and 1401, and the unique back-edge is the
  jump at PC 1404, immediately after the block, targeting PC 959.

The 7 other forms are the `send.gtwy`, plain `and`/`add`, `cmp`, `bfn` pair
and `cmp`/`add` around the loop tail; they are listed, not executed.
-/

namespace IntelGpu

/-- The instruction classes of the mainloop schedule. -/
inductive TlaKind where
  | mov
  | alu
  | b2d
  | b2dPlain
  | dpas
  | syncNop
  | syncBar
  | jmp
  | label
  | other
  deriving Repr, DecidableEq

/-- Total classification of a decoded instruction. -/
def TlaInstr.kind (i : TlaInstr) : TlaKind :=
  match i with
  | .dpas _ _ _ _ _ _ => .dpas
  | .label _ => .label
  | .plain "sync.nop" _ => .syncNop
  | .predicated "(W) sync.bar" _ => .syncBar
  | i =>
      match parseTlaMovInstr i with
      | some _ => .mov
      | none =>
          match parseTlaAluInstr i with
          | some _ => .alu
          | none =>
              match parseTlaBlock2dInstr i with
              | some _ => .b2d
              | none =>
                  match parseTlaBlock2dPlain i with
                  | some _ => .b2dPlain
                  | none =>
                      match parseTlaJmpInstr i with
                      | some _ => .jmp
                      | none => .other

/-- The classified mainloop schedule with program counters. -/
def blockKindList : List (Nat × TlaKind) :=
  blockInstrs.map (fun p => (p.1, p.2.kind))

/-- The schedule without program counters. -/
def blockKinds : List TlaKind := blockKindList.map (fun p => p.2)

set_option maxRecDepth 100000 in
/-- The schedule has one entry per block instruction. -/
theorem blockKinds_length : blockKinds.length = 445 := by decide

set_option maxRecDepth 100000 in
/-- 152 moves. -/
theorem blockKinds_mov : (blockKinds.filter (fun k => k = .mov)).length = 152 := by
  decide

set_option maxRecDepth 100000 in
/-- 8 predicated ALU ops. -/
theorem blockKinds_alu : (blockKinds.filter (fun k => k = .alu)).length = 8 := by
  decide

set_option maxRecDepth 100000 in
/-- 130 predicated block2d ops. -/
theorem blockKinds_b2d : (blockKinds.filter (fun k => k = .b2d)).length = 130 := by
  decide

set_option maxRecDepth 100000 in
/-- 7 plain block2d loads. -/
theorem blockKinds_b2dPlain :
    (blockKinds.filter (fun k => k = .b2dPlain)).length = 7 := by decide

set_option maxRecDepth 100000 in
/-- 32 DPAS instructions. -/
theorem blockKinds_dpas : (blockKinds.filter (fun k => k = .dpas)).length = 32 := by
  decide

set_option maxRecDepth 100000 in
/-- 102 `sync.nop` waits. -/
theorem blockKinds_syncNop :
    (blockKinds.filter (fun k => k = .syncNop)).length = 102 := by decide

set_option maxRecDepth 100000 in
/-- One `sync.bar`. -/
theorem blockKinds_syncBar :
    (blockKinds.filter (fun k => k = .syncBar)).length = 1 := by decide

set_option maxRecDepth 100000 in
/-- Two jumps inside the block. -/
theorem blockKinds_jmp : (blockKinds.filter (fun k => k = .jmp)).length = 2 := by
  decide

set_option maxRecDepth 100000 in
/-- Four labels inside the block. -/
theorem blockKinds_label :
    (blockKinds.filter (fun k => k = .label)).length = 4 := by decide

set_option maxRecDepth 100000 in
/-- Seven other scalar forms. -/
theorem blockKinds_other :
    (blockKinds.filter (fun k => k = .other)).length = 7 := by decide

set_option maxRecDepth 100000 in
/-- The single barrier is at PC 1396. -/
theorem blockKind_syncBar_pcs :
    (blockKindList.filter (fun p => p.2 = .syncBar)).map (fun p => p.1) = [1396] := by
  decide

set_option maxRecDepth 100000 in
/-- The in-block jumps are at PCs 991 and 1401. -/
theorem blockKind_jmp_pcs :
    (blockKindList.filter (fun p => p.2 = .jmp)).map (fun p => p.1) = [991, 1401] := by
  decide

set_option maxRecDepth 100000 in
/-- The in-block labels are at PCs 959, 992, 1007 and 1402. -/
theorem blockKind_label_pcs :
    (blockKindList.filter (fun p => p.2 = .label)).map (fun p => p.1) =
      [959, 992, 1007, 1402] := by
  decide

set_option maxRecDepth 100000 in
/-- Every DPAS precedes the barrier. -/
theorem blockKind_dpas_before_bar :
    blockKindList.all (fun p => if p.2 = .dpas then decide (p.1 < 1396) else true) = true := by
  decide

set_option maxRecDepth 100000 in
/-- The unique back-edge is the jump at PC 1404. -/
theorem backEdges_pcs : backEdges.map (fun p => p.1) = [1404] := by decide

set_option maxRecDepth 100000 in
/-- The back-edge is the instruction right after the block. -/
theorem backEdges_head : backEdges.head? = some (1404, ⟨"(W) jmpi", "_0_119"⟩) := by
  decide

end IntelGpu
