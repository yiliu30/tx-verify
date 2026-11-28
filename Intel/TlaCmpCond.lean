-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaCmp
public import Intel.TlaPlain

@[expose] public section

/-!
# Conditional comparison forms

Eight of the 28 predicated `cmp` forms carry an extra predicate flag beyond
`(W)`: `(W&f0.0) cmp`, `(W&f1.1) cmp`, `(W&f0.1) cmp`, `(W&f3.0) cmp`,
`(W&f2.0) cmp`, `(W&f2.1) cmp` and `(W&f1.0) cmp` (one of them twice). The
`TlaCmp.cond` field keeps the full predicate text. The flag write is not yet
gated on `cond`; this is recorded as a modelling gap for the conditional
comparisons, while the loop comparison uses the unconditional `(W) cmp`.
-/

namespace IntelGpu

set_option maxRecDepth 1000000 in
/-- 8 comparisons carry an extra predicate flag. -/
theorem realTlaGemmCmp_conditional_count :
    (realTlaGemmCmp.filter (fun c => c.cond ≠ "(W) cmp")).length = 8 := by
  decide

set_option maxRecDepth 1000000 in
/-- The distinct comparison predicates, in program order. -/
theorem realTlaGemmCmp_conds :
    (realTlaGemmCmp.map (fun c => c.cond)).eraseDups =
      ["(W) cmp", "(W&f0.0) cmp", "(W&f1.1) cmp", "(W&f0.1) cmp",
       "(W&f3.0) cmp", "(W&f2.0) cmp", "(W&f2.1) cmp", "(W&f1.0) cmp"] := by
  decide

set_option maxRecDepth 1000000 in
/-- Every comparison predicate starts with `(W`. -/
theorem realTlaGemmCmp_cond_prefix :
    realTlaGemmCmp.all (fun c => listHasPrefix "(W".toList c.cond.toList) = true := by
  decide

set_option maxRecDepth 100000 in
/-- PC 1408 is a conditional comparison. -/
theorem progInstr1408 :
    progInstrAt 1408 = some (.predicated "(W&f0.0) cmp"
      ["(16|M0)", "(eq)f0.0", "null<1>:d", "r1.11<0;1,0>:d", "0:w"]) := by
  decide

set_option maxRecDepth 100000 in
/-- PC 1408 records its predicate text in `cond`. -/
theorem parseTlaCmp_1408 :
    (progInstrAt 1408).bind parseTlaCmpInstr =
      some ⟨"(W&f0.0) cmp", ⟨16, 0, true⟩, "eq", 0, 0,
        .reg ⟨1, 0, 11, 0, 1, 0⟩, .imm (0 : Int) .w16⟩ := by
  decide

end IntelGpu
