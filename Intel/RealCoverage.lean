-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Decode
public import Intel.Examples.RealAddOne

@[expose] public section

/-!
# What the current decoder does with a real kernel

The stage-5 decoder was written against the GEMM-loop fixture: register
spellings like `r22:2`, immediates like `1`, and five opcodes. A real IGC dump
looks nothing like that, and the review of PRs #2–#62 (issue #63) asks that
unsupported instructions be **rejected explicitly** rather than dropped.

`rejected` lists every statement the decoder refuses, by opcode, and
`realAddOne_rejected` states the list for the real add-one kernel as a
`decide`-checked theorem.

The answer is not flattering: the current decoder reads none of it. That is the
gap the next stages have to close, and it is now a theorem rather than an
impression.
-/

namespace IntelGpu

/-- Opcodes the decoder refuses, in program order. -/
def rejected (p : Program) : List String :=
  p.statements.filterMap fun s =>
    match s, decodeInstr s with
    | _, some _ => none
    | .instruction op _, none => some op
    | .label name, none => some ("label " ++ name)

/-- Every instruction in the real add-one kernel is refused by the stage-5
decoder, for region syntax, arity, or an unknown opcode. -/
theorem realAddOne_rejected :
    rejected realAddOne =
      ["or", "mul", "mov", "add3", "mov", "shl", "add", "lsc_load.ugm", "add",
       "lsc_store.ugm", "ret"] := by
  decide

/-- The decoder accepts nothing at all in the real kernel. -/
theorem realAddOne_unsupported : decodeProgram realAddOne = none := by
  decide

end IntelGpu
