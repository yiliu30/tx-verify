-- SPDX-License-Identifier: Apache-2.0
module

public import Std

@[expose] public section

/-!
# IGC assembly syntax

A deliberately small, raw syntax for the IGC assembly subset used by the
GEMM loop. Operands are kept as strings at this stage; a later decoder maps
them to registers, addresses, and literals.
-/

namespace IntelGpu

inductive Stmt where
  | label (name : String)
  | instruction (opcode : String) (operands : List String)
  deriving Repr, Inhabited

structure Program where
  statements : List Stmt
  deriving Repr, Inhabited

end IntelGpu
