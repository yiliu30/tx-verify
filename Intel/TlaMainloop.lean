-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaCfg

@[expose] public section

/-!
# The SYCL-TLA mainloop block

The decoded program has one loop back-edge: the jump at PC 1404 targets the
label at PC 959. All 32 DPAS instructions lie inside that block, at PCs
1018..1393. This module records those bounds and the back-edge, which is the
skeleton for the mainloop reconstruction.
-/

namespace IntelGpu

def withPcGo : List TlaInstr → Nat → List (Nat × TlaInstr)
  | [], _ => []
  | x :: xs, n => (n, x) :: withPcGo xs (n + 1)

/-- The decoded program with program counters. -/
def withPc : List (Nat × TlaInstr) := withPcGo tlaCode 0

def isDpas : TlaInstr → Bool
  | .dpas _ _ _ _ _ _ => true
  | _ => false

/-- The program counters of the DPAS instructions. -/
def dpasPcs : List Nat :=
  (withPc.filter (fun p => isDpas p.2)).map (fun p => p.1)

/-- The predicated jumps with their program counters. -/
def jmpWithPc : List (Nat × TlaJmp) :=
  withPc.filterMap (fun p =>
    match parseTlaJmpInstr p.2 with
    | some j => some (p.1, j)
    | none => none)

/-- Jumps whose target is at or before the jump itself. -/
def backEdges : List (Nat × TlaJmp) :=
  jmpWithPc.filter (fun p =>
    match tlaLabelPc tlaCode p.2.target with
    | some t => t ≤ p.1
    | none => false)

set_option maxRecDepth 100000 in
/-- There are 32 DPAS instructions. -/
theorem dpasPcs_length : dpasPcs.length = 32 := by decide

set_option maxRecDepth 100000 in
/-- The first DPAS is at PC 1018. -/
theorem dpasPcs_first : dpasPcs.head? = some 1018 := by decide

set_option maxRecDepth 100000 in
/-- The last DPAS is at PC 1393. -/
theorem dpasPcs_last : dpasPcs.getLast? = some 1393 := by decide

set_option maxRecDepth 1000000 in
/-- The back-edge target label is at PC 959. -/
theorem backEdge_target : tlaLabelPc tlaCode "_0_119" = some 959 := by decide

set_option maxRecDepth 100000 in
/-- Every DPAS lies inside the mainloop block `[959, 1404)`. -/
theorem dpasPcs_in_block :
    dpasPcs.all (fun p => decide (959 ≤ p ∧ p < 1404)) = true := by decide

end IntelGpu
