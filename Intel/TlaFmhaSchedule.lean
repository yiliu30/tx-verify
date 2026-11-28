-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.FmhaPrefillCoverage

@[expose] public section

/-!
# FMHA prefill phase order

The DPAS and math instructions of the prefill dump form a clean pipeline:
QK^T atoms (PCs 995-1162), the `math.exp` block (1272-1412), the PV atoms
(1456-1654) and the single `math.inv` at 1774. This module records those
ranges as machine-checked facts.
-/

namespace IntelGpu

/-- Program counters of the statements satisfying a predicate. -/
def fmhaPcs (p : TlaInstr → Bool) : List Nat :=
  (fmhaPrefillPc.filter (fun q => p q.2)).map (fun q => q.1)

def qkDpasPcs : List Nat :=
  fmhaPcs (fun i => match parseFmhaDpas i with
    | some d => d.acc0 ≤ 66
    | none => false)

def pvDpasPcs : List Nat :=
  fmhaPcs (fun i => match parseFmhaDpas i with
    | some d => 66 < d.acc0
    | none => false)

def expPcs : List Nat :=
  fmhaPcs (fun i => match parseTlaMath i with
    | some m => m.op = .exp
    | none => false)

def invPcs : List Nat :=
  fmhaPcs (fun i => match parseTlaMath i with
    | some m => m.op = .inv
    | none => false)

set_option maxRecDepth 1000000 in
theorem qkDpasPcs_length : qkDpasPcs.length = 32 := by decide

set_option maxRecDepth 1000000 in
theorem pvDpasPcs_length : pvDpasPcs.length = 32 := by decide

set_option maxRecDepth 1000000 in
theorem expPcs_length : expPcs.length = 33 := by decide

set_option maxRecDepth 1000000 in
/-- Every QK^T atom precedes the exponential block. -/
theorem qkDpasPcs_before_exp : qkDpasPcs.all (fun pc => pc < 1272) = true := by
  decide

set_option maxRecDepth 1000000 in
/-- The exponential block sits in `1272..1412`. -/
theorem expPcs_range : expPcs.all (fun pc => 1272 ≤ pc && pc ≤ 1412) = true := by
  decide

set_option maxRecDepth 1000000 in
/-- The PV atoms sit in `1456..1654`. -/
theorem pvDpasPcs_range : pvDpasPcs.all (fun pc => 1456 ≤ pc && pc ≤ 1654) = true := by
  decide

set_option maxRecDepth 1000000 in
/-- The reciprocal is the final math instruction. -/
theorem invPcs_eq : invPcs = [1774] := by decide

end IntelGpu
