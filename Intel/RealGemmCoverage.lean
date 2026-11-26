-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.RealDecode
public import Intel.Examples.RealGemm

@[expose] public section

/-!
# What the stage-63 decoder does with a real GEMM

The stage-63 decoder was written for the add-one kernel's forms. This module
measures exactly how far it gets through the real 64x64x64 integer GEMM dump
imported in `Intel.Examples.RealGemm`, so the next stage has a concrete list to
close.

`realGemm_accepted`, `realGemm_rejectedOps` and `realGemm_rejectedLabels` are
`decide`-checked lists in program order. The decoder reads 27 of the 33
instructions: all the register arithmetic, both loads, the store and `ret`.
It refuses the two `mov`-immediate zeroing instructions, the loop's non-prologue
`or`, `cmp.lt`, both `goto` forms, and every label.
-/

namespace IntelGpu

/-- Opcodes the stage-63 decoder accepts, in program order (labels omitted). -/
def acceptedReal (p : Program) : List String :=
  p.statements.filterMap fun s =>
    match s, decodeReal s with
    | .instruction op _, some _ => some op
    | _, _ => none

/-- Opcodes the stage-63 decoder refuses, in program order. -/
def rejectedOps (p : Program) : List String :=
  p.statements.filterMap fun s =>
    match s, decodeReal s with
    | .instruction op _, none => some op
    | _, _ => none

/-- Labels the stage-63 decoder refuses. It refuses every label. -/
def rejectedLabels (p : Program) : List String :=
  p.statements.filterMap fun s =>
    match s, decodeReal s with
    | .label name, none => some name
    | _, _ => none

theorem realGemm_accepted :
    acceptedReal realGemm =
      ["or", "mul", "mov", "add3", "mul", "mov", "add", "shl", "mov", "shl",
       "add", "lsc_load.ugm", "shl", "add3", "mov", "shl", "add",
       "lsc_load.ugm", "mul", "add", "add", "add3", "mov", "shl", "add",
       "lsc_store.ugm", "ret"] := by
  unfold acceptedReal realGemm
  decide

theorem realGemm_rejectedOps :
    rejectedOps realGemm =
      ["mov", "mov", "or", "cmp.lt", "(!P1) goto", "goto"] := by
  unfold rejectedOps realGemm
  decide

theorem realGemm_rejectedLabels :
    rejectedLabels realGemm = ["_main_0", "_0_004", "_0_006", "_0_005"] := by
  unfold rejectedLabels realGemm
  decide

/-- Because the decoder is all-or-nothing, the real GEMM does not decode. -/
theorem realGemm_not_decoded : decodeRealProgram realGemm = none := by
  unfold decodeRealProgram decodeRealStmts realGemm
  decide

end IntelGpu
