-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.RealGemmCoverage
public import Intel.Examples.RealVectorAdd

@[expose] public section

/-!
# What the decoder does with a real SIMD vector add

The vector-add dump introduces masked and predicated forms: `(M5, 16)` moves,
`cmp` against a register, predicate `and`/`or`, `sel`, and scaled
`flat(base)[0x4*index]` memory operands. After the scaled-memory extension and
the predicated `sel`, the loads, store and selects decode; the remaining
refusals are the M5 masks, the predicate ops and the predicated `goto`s.
-/

namespace IntelGpu

theorem realVectorAdd_accepted :
    acceptedReal realVectorAdd =
      ["or", "mov", "mul", "mov", "add", "mov", "add", "mov", "mov", "mov",
       "lsc_load.ugm", "lsc_load.ugm", "add", "lsc_store.ugm", "add", "mov",
       "mov", "(P6) sel", "(P6) sel", "mov", "mov", "goto", "ret"] := by
  unfold acceptedReal realVectorAdd
  decide

theorem realVectorAdd_rejectedOps :
    rejectedOps realVectorAdd =
      ["mov", "mov", "cmp.lt", "cmp.eq", "and", "cmp.lt", "or", "(!P3) goto",
       "mov", "mov", "cmp.lt", "cmp.eq", "and", "cmp.lt", "or", "(!P6) goto",
       "mov", "mov"] := by
  unfold rejectedOps realVectorAdd
  decide

theorem realVectorAdd_rejectedLabels :
    rejectedLabels realVectorAdd = [] := by
  unfold rejectedLabels realVectorAdd
  decide

/-- A masked `(M5, 16)` move is refused; only M1/M1_NM masks are modelled. -/
theorem masked_mov_rejected :
    decodeReal (.instruction "mov"
      ["(M5, 16)", "V0062(1,0)<1>", "V0061(2,0)<2;1,0>"]) = none := by
  decide

theorem realVectorAdd_not_decoded :
    decodeRealProgram realVectorAdd = none := by
  unfold decodeRealProgram decodeRealStmts realVectorAdd
  decide

end IntelGpu
