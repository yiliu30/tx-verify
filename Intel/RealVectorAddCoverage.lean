-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.RealGemmCoverage
public import Intel.Examples.RealVectorAdd

@[expose] public section

/-!
# What the decoder does with a real SIMD vector add

The vector-add dump introduces masked and predicated forms: `(M5, 16)` moves,
`cmp` against a register, predicate `and`/`or`, `sel`, and scaled
`flat(base)[0x4*index]` memory operands. After decoding the execution masks,
the scaled memory operands, the predicated `sel`, predicate `and`/`or` and the
register comparisons and both predicated `goto`s, the whole dump decodes.
-/

namespace IntelGpu

theorem realVectorAdd_accepted :
    acceptedReal realVectorAdd =
      ["or", "mov", "mul", "mov", "add", "mov", "add", "mov", "mov", "mov",
       "mov", "cmp.lt", "cmp.eq", "and", "cmp.lt", "or", "(!P3) goto", "mov",
       "lsc_load.ugm", "lsc_load.ugm", "add", "lsc_store.ugm", "add", "mov",
       "mov", "mov", "mov", "cmp.lt", "cmp.eq", "and", "cmp.lt", "or",
       "(!P6) goto", "(P6) sel", "(P6) sel", "mov", "mov", "mov", "mov",
       "goto", "ret"] := by
  unfold acceptedReal realVectorAdd
  decide

theorem realVectorAdd_rejectedOps : rejectedOps realVectorAdd = [] := by
  unfold rejectedOps realVectorAdd
  decide

theorem realVectorAdd_rejectedLabels :
    rejectedLabels realVectorAdd = [] := by
  unfold rejectedLabels realVectorAdd
  decide

/-- The M5 mask decodes with its 16-channel offset. -/
theorem execMask_M5 : execMaskOffset 5 = some 16 := by decide

/-- A masked `(M5, 16)` move decodes with the mask kept, not silently dropped. -/
theorem masked_mov_decodes :
    decodeReal (.instruction "mov"
      ["(M5, 16)", "V0062(1,0)<1>", "V0061(2,0)<2;1,0>"]) =
    some (.mov ⟨16, 16, false⟩ ⟨62, 1, 0, 1, 1, 0⟩ ⟨61, 2, 0, 2, 1, 0⟩) := by
  decide

/-- Mask names outside M1-M8 are refused. -/
theorem parseExec_rejects_M9 : parseExec "(M9, 16)" = none := by decide

/-- Both predicated gotos decode with their predicate and polarity kept. -/
theorem predicated_gotos_decode :
    decodeReal (.instruction "(!P3) goto" ["(M1, 32)", "_0_007"]) =
      some (.gotoIf 32 3 true "_0_007") ∧
    decodeReal (.instruction "(!P6) goto" ["(M1, 32)", "_0_007"]) =
      some (.gotoIf 32 6 true "_0_007") := by
  decide

theorem realVectorAdd_decodes :
    (decodeRealProgram realVectorAdd).isSome = true := by
  unfold decodeRealProgram decodeRealStmts realVectorAdd
  decide

/-- All 46 statements (41 instructions and five labels) decode. -/
theorem realVectorAdd_decoded_length :
    (decodeRealProgram realVectorAdd).map List.length = some 46 := by
  unfold decodeRealProgram decodeRealStmts realVectorAdd
  decide

end IntelGpu
