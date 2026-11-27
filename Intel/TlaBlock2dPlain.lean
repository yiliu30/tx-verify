-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaBlock2d
public import Intel.TlaBlockCensus
public import Intel.TlaDpasExec
public import Intel.TlaAddr

@[expose] public section

/-!
# Unprefixed block2d loads in the SYCL-TLA mainloop

The mainloop also contains seven `load_block2d.ugm.*` instructions without the
`(W) ` predicate prefix. They are the loads that fill the DPAS operand
registers, so the mainloop reconstruction has to see them:

* `r64:16`, `r80:16`, `r96:16`, `r112:16` cover the eight B operand bases
  `64, 72, ..., 120`, and
* `r30:31` covers the eight A operand bases `30, 34, ..., 58`.

This module decodes the 27 plain `load_block2d` forms in the dump (7 of them in
the mainloop block) into the same `TlaBlock2d` structure and proves the four B
windows and the A window cover every DPAS operand base.
-/

namespace IntelGpu

/-- Structural prefix check on character lists. -/
def listHasPrefix : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | c :: cs, d :: ds => (c = d) && listHasPrefix cs ds

/-- The plain `load_block2d.ugm.*` spelling. -/
def isPlainB2dOp (op : String) : Bool :=
  listHasPrefix "load_block2d.ugm".toList op.toList

/-- The unprefixed block2d load form: execution control, data region and
address. -/
def parseTlaBlock2dPlain : TlaInstr → Option TlaBlock2d
  | .plain op (e :: a :: b :: _) =>
      if isPlainB2dOp op then
        (parseTlaExec e).map (fun ex => ⟨op, ex, a, b⟩)
      else none
  | _ => none

theorem parseTlaBlock2dPlain_example :
    parseTlaBlock2dPlain (.plain "load_block2d.ugm.d16v.a64"
      ["(1|M0)", "r64:16", "[r7:1]", "{I@2,$3}"]) =
      some ⟨"load_block2d.ugm.d16v.a64", ⟨1, 0, true⟩, "r64:16", "[r7:1]"⟩ := by
  decide

/-- The data-register window `rN:M`, if the operand has that shape. -/
def TlaBlock2d.regWindow? (b : TlaBlock2d) : Option (Nat × Nat) :=
  match numRuns b.reg with
  | [n, m] => some (n, m)
  | _ => none

/-- The decoded plain block2d forms. -/
def realTlaGemmBlock2dPlain : List TlaBlock2d :=
  (decodeTlaProgram realTlaGemm).filterMap parseTlaBlock2dPlain

/-- The plain block2d forms inside the mainloop block. -/
def blockPlainB2d : List (Nat × TlaBlock2d) :=
  blockInstrs.filterMap (fun p => (parseTlaBlock2dPlain p.2).map (fun b => (p.1, b)))

/-- The data-register windows written by the block's plain loads. -/
def blockPlainB2dWindows : List (Nat × Nat) :=
  blockPlainB2d.filterMap (fun p => TlaBlock2d.regWindow? p.2)

set_option maxRecDepth 100000 in
/-- There are 27 plain block2d loads in the dump. -/
theorem realTlaGemmBlock2dPlain_length :
    realTlaGemmBlock2dPlain.length = 27 := by decide

set_option maxRecDepth 100000 in
/-- 7 plain block2d loads are inside the mainloop block. -/
theorem blockPlainB2d_length : blockPlainB2d.length = 7 := by decide

set_option maxRecDepth 100000 in
/-- The five data windows of the block's plain loads, in program order. -/
theorem blockPlainB2dWindows_eq :
    blockPlainB2dWindows = [(64, 16), (80, 16), (30, 31), (96, 16), (112, 16)] := by
  decide

set_option maxRecDepth 100000 in
/-- Every plain block2d address parses. -/
theorem realTlaGemmBlock2dPlain_addr_parse :
    realTlaGemmBlock2dPlain.all (fun b => (parseTlaAddr b.addr).isSome) = true := by
  decide

set_option maxRecDepth 100000 in
/-- The predicated and plain forms together number 420. -/
theorem realTlaGemmBlock2dAll_length :
    (realTlaGemmBlock2d ++ realTlaGemmBlock2dPlain).length = 420 := by decide

set_option maxRecDepth 100000 in
/-- The four 16-register windows cover all eight B operand bases
`64, 72, ..., 120`. -/
theorem dpasB_window_cover :
    ([64, 72, 80, 88, 96, 104, 112, 120].all (fun b =>
      blockPlainB2dWindows.any (fun w => decide (w.1 ≤ b ∧ b < w.1 + w.2)))) = true := by
  decide

set_option maxRecDepth 100000 in
/-- The 31-register `r30` window covers all eight A operand bases
`30, 34, ..., 58`. -/
theorem dpasA_window_cover :
    ([30, 34, 38, 42, 46, 50, 54, 58].all (fun a =>
      blockPlainB2dWindows.any (fun w => decide (w.1 ≤ a ∧ a < w.1 + w.2)))) = true := by
  decide

end IntelGpu
