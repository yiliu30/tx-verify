-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Examples.RealTlaGemm
public import Intel.RealDpas

@[expose] public section

/-!
# A first decoder for the SYCL-TLA GEMM dump

`Intel.RealDecode` is deliberately fail-closed: it rejects any instruction form
that is not in the small verified subset. The SYCL-TLA GEMM dump needs a wider
front end before it can be connected to that subset. This module provides a
total, lossless first decoder:

- `TlaInstr` separates labels, predicated forms such as `(W) mov`, the
  `dpas.8x8` instruction, and plain instructions;
- `decodeTla` is total and never drops a statement;
- the census proves the 2252 statements, the 968 predicated forms and the 32
  BF16 DPAS instructions.

This is a decoding layer, not a semantics. Execution still goes through
`Intel.RealSemantics` for the verified subset; connecting `TlaInstr` to it is
the next stage.
-/

namespace IntelGpu

/-- A decoded SYCL-TLA statement. -/
inductive TlaInstr where
  | label (name : String)
  /-- A predicate-prefixed form, e.g. `(W) mov` or `(W&~f3.0) add`. -/
  | predicated (opcode : String) (operands : List String)
  /-- A DPAS instruction: exec, two FP32 accumulators, B source, A source and
  the trailing modifiers. -/
  | dpas (exec acc0 acc1 srcB srcA : String) (mods : List String)
  /-- Any other instruction, kept verbatim. -/
  | plain (opcode : String) (operands : List String)
  deriving Repr, DecidableEq

/-- An opcode that begins with a parenthesised predicate. -/
def isPredPrefix (op : String) : Bool :=
  match op.toList with
  | '(' :: _ => true
  | _ => false

/-- Decode one statement, preserving every label and instruction. -/
def decodeTla : Stmt → TlaInstr
  | .label name => .label name
  | .instruction "dpas.8x8" [e, d0, d1, b, a, m] => .dpas e d0 d1 b a [m]
  | .instruction "dpas.8x8" [e, d0, d1, b, a] => .dpas e d0 d1 b a []
  | .instruction op ops =>
      if isPredPrefix op then .predicated op ops else .plain op ops

/-- Decode a whole program. -/
def decodeTlaProgram (p : Program) : List TlaInstr := p.statements.map decodeTla

/-- A DPAS statement. -/
def TlaInstr.isDpas : TlaInstr → Bool
  | .dpas _ _ _ _ _ _ => true
  | _ => false

/-- A predicated statement. -/
def TlaInstr.isPredicated : TlaInstr → Bool
  | .predicated _ _ => true
  | _ => false

/-- The DPAS form used by this kernel: 8x8, 16 lanes, two FP32 accumulators and
two BF16 sources. -/
def TlaInstr.isBf16Dpas : TlaInstr → Bool
  | .dpas e d0 d1 b a _ =>
      (parseDpasExec e == some 16) &&
      (afterColon d0.toList == some ['f']) &&
      (afterColon d1.toList == some ['f']) &&
      (afterColon b.toList == some ['b', 'f']) &&
      (afterColon a.toList == some ['b', 'f'])
  | _ => false

set_option maxRecDepth 100000 in
/-- The decoder preserves the statement count. -/
theorem tlaDecoded_length : (decodeTlaProgram realTlaGemm).length = 2252 := by
  decide

set_option maxRecDepth 100000 in
/-- The dump has 968 predicate-prefixed instructions. -/
theorem tlaDecoded_predicated_count :
    ((decodeTlaProgram realTlaGemm).filter TlaInstr.isPredicated).length = 968 := by
  decide

set_option maxRecDepth 100000 in
/-- The dump has 32 DPAS instructions. -/
theorem tlaDecoded_dpas_count :
    ((decodeTlaProgram realTlaGemm).filter TlaInstr.isDpas).length = 32 := by
  decide

set_option maxRecDepth 100000 in
/-- Every DPAS is 8x8, 16 lanes, two FP32 accumulators and two BF16 sources. -/
theorem tlaDecoded_dpas_all_bf16 :
    ((decodeTlaProgram realTlaGemm).filter TlaInstr.isDpas).all
      TlaInstr.isBf16Dpas = true := by
  decide

set_option maxRecDepth 100000 in
/-- The second statement is the predicated prologue move. -/
theorem tlaDecoded_second :
    (decodeTlaProgram realTlaGemm)[1]? =
      some (.predicated "(W) mov" ["(16|M0)", "r127.0<1>:ud", "0x0:ud"]) := by
  decide

end IntelGpu
