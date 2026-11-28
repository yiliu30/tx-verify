-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaControlDecode

@[expose] public section

/-!
# Control-flow targets of the SYCL-TLA GEMM

`Intel.TlaControlDecode` inventories the 58 predicated jumps. This module
checks that every target resolves to a decoded label and records the label
count and program length. The lookup is the decoded-program analogue of
`Intel.RealSemantics.labelIndex`.
-/

namespace IntelGpu

def tlaLabelPcGo : List TlaInstr → String → Nat → Option Nat
  | [], _, _ => none
  | .label n :: rest, name, i =>
      if n = name then some i else tlaLabelPcGo rest name (i + 1)
  | _ :: rest, name, i => tlaLabelPcGo rest name (i + 1)

/-- The program counter of a label in the decoded program. -/
def tlaLabelPc (code : List TlaInstr) (name : String) : Option Nat :=
  tlaLabelPcGo code name 0

/-- The decoded program. -/
def tlaCode : List TlaInstr := decodeTlaProgram realTlaGemm

/-- All decoded labels. -/
def tlaLabels : List String :=
  tlaCode.filterMap (fun i => match i with | .label n => some n | _ => none)

set_option maxRecDepth 100000 in
/-- The decoded program has 2252 statements. -/
theorem tlaCode_length : tlaCode.length = 2252 := by decide

set_option maxRecDepth 100000 in
/-- The decoded program has 87 labels. -/
theorem tlaLabels_length : tlaLabels.length = 87 := by decide

set_option maxRecDepth 100000 in
/-- Every jump target resolves to a label. -/
theorem realTlaGemmJmps_resolve :
    realTlaGemmJmps.all (fun j => (tlaLabelPc tlaCode j.target).isSome) = true := by
  decide

/-- The first jump's target resolves to its decoded PC. -/
theorem realTlaGemmJmps_first_target :
    (realTlaGemmJmps.head?).bind (fun j => tlaLabelPc tlaCode j.target) = some 27 := by
  decide

end IntelGpu
