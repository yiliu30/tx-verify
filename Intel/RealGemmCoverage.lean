-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.RealSemantics
public import Intel.Examples.RealGemm

@[expose] public section

/-!
# The stage-63 decoder now reads the real GEMM

Stage 65 measured the gap: the decoder accepted 27 of the 33 instructions in
the real 64x64x64 integer GEMM and refused the control-flow shell. This module
records the closure:

- `mov` with an immediate source (`mov dst 0x0:d`),
- the loop's three-operand `or`,
- `cmp.lt` into predicate `P1`,
- `goto` and the predicated `(!P1) goto`,
- labels.

`realGemm_decodes` and `realGemm_decoded_length` are `decide`-checked: all 37
statements, labels included, decode, and `rejectedOps`/`rejectedLabels` are
empty.
-/

namespace IntelGpu

/-- Opcodes the decoder accepts, in program order (labels omitted). -/
def acceptedReal (p : Program) : List String :=
  p.statements.filterMap fun s =>
    match s, decodeReal s with
    | .instruction op _, some _ => some op
    | _, _ => none

/-- Opcodes the decoder refuses, in program order. -/
def rejectedOps (p : Program) : List String :=
  p.statements.filterMap fun s =>
    match s, decodeReal s with
    | .instruction op _, none => some op
    | _, _ => none

/-- Labels the decoder refuses. -/
def rejectedLabels (p : Program) : List String :=
  p.statements.filterMap fun s =>
    match s, decodeReal s with
    | .label name, none => some name
    | _, _ => none

theorem realGemm_accepted :
    acceptedReal realGemm =
      ["or", "mul", "mov", "add3", "mul", "mov", "add", "shl", "mov", "mov",
       "or", "mov", "shl", "add", "lsc_load.ugm", "shl", "add3", "mov", "shl",
       "add", "lsc_load.ugm", "mul", "add", "cmp.lt", "(!P1) goto", "add",
       "goto", "add3", "mov", "shl", "add", "lsc_store.ugm", "ret"] := by
  unfold acceptedReal realGemm
  decide

/-- Nothing in the real GEMM is refused any more. -/
theorem realGemm_rejectedOps : rejectedOps realGemm = [] := by
  unfold rejectedOps realGemm
  decide

/-- Every label decodes. -/
theorem realGemm_rejectedLabels : rejectedLabels realGemm = [] := by
  unfold rejectedLabels realGemm
  decide

/-- The whole real GEMM decodes, labels included. -/
theorem realGemm_decodes : (decodeRealProgram realGemm).isSome = true := by
  unfold decodeRealProgram decodeRealStmts realGemm
  decide

/-- Four labels and 33 instructions. -/
theorem realGemm_decoded_length :
    (decodeRealProgram realGemm).map List.length = some 37 := by
  unfold decodeRealProgram decodeRealStmts realGemm
  decide

/-- The branch targets resolve in the decoded statement list. -/
theorem realGemm_label_main :
    (decodeRealProgram realGemm).bind (fun is => labelIndex is "_main_0") = some 0 := by
  unfold decodeRealProgram decodeRealStmts realGemm labelIndex labelIndexGo
  decide

theorem realGemm_label_loop :
    (decodeRealProgram realGemm).bind (fun is => labelIndex is "_0_004") = some 11 := by
  unfold decodeRealProgram decodeRealStmts realGemm labelIndex labelIndexGo
  decide

theorem realGemm_label_step :
    (decodeRealProgram realGemm).bind (fun is => labelIndex is "_0_006") = some 27 := by
  unfold decodeRealProgram decodeRealStmts realGemm labelIndex labelIndexGo
  decide

theorem realGemm_label_exit :
    (decodeRealProgram realGemm).bind (fun is => labelIndex is "_0_005") = some 30 := by
  unfold decodeRealProgram decodeRealStmts realGemm labelIndex labelIndexGo
  decide

end IntelGpu
