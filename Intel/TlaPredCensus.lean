-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaDecode

@[expose] public section

/-!
# Census of the SYCL-TLA predicated forms

The SYCL-TLA GEMM dump has 968 predicate-prefixed statements. This module
inventories their exact opcode spellings, so the next decoder stages can be
scoped to a finite list instead of the whole instruction set.

`isPredStmt` recognizes an opcode whose first character is `(`. `predOpcodes`
collects the opcodes of all such statements. The census proves the total count,
the `(W) mov` count, and that every opcode is in the documented list.
-/

namespace IntelGpu

def isPredStmt : Stmt → Bool
  | .instruction op _ =>
      match op.toList with
      | '(' :: _ => true
      | _ => false
  | _ => false

def stmtOpcode : Stmt → Option String
  | .instruction op _ => some op
  | _ => none

/-- The opcodes of all predicate-prefixed statements. -/
def predOpcodes : List String :=
  (realTlaGemm.statements.filter isPredStmt).filterMap stmtOpcode

/-- The predicated opcode spellings used by this kernel. -/
def knownPredOpcodes : List String :=
  [
   "(W&f0.0) cmp", "(W&f0.0) jmpi", "(W&f0.1) cmp", "(W&f0.1) jmpi",
   "(W&f1.0) cmp", "(W&f1.0) jmpi", "(W&f1.1) cmp", "(W&f1.1) jmpi",
   "(W&f2.0) cmp", "(W&f2.0) jmpi", "(W&f2.1) cmp", "(W&f2.1) jmpi",
   "(W&f3.0) cmp", "(W&f3.0) jmpi", "(W&f3.1) jmpi", "(W&~f0.0) jmpi",
   "(W&~f0.1) jmpi", "(W&~f1.0) jmpi", "(W&~f1.1) jmpi", "(W&~f2.1) jmpi",
   "(W&~f3.0) jmpi", "(W&~f3.1) jmpi", "(W) add", "(W) and",
   "(W) asr", "(W) cmp", "(W) jmpi", "(W) load.ugm.d32x16t.a32",
   "(W) load.ugm.d32x16t.a32.ca.cc", "(W) load.ugm.d32x1t.a64", "(W) load.ugm.d32x32t.a32", "(W) load.ugm.d32x32t.a32.ca.cc",
   "(W) load.ugm.d32x64t.a32", "(W) load.ugm.d32x64t.a32.ca.cc", "(W) load.ugm.d32x8t.a64.ca.cc", "(W) mach",
   "(W) macl", "(W) mad", "(W) mov", "(W) mul",
   "(W) or", "(W) send.gtwy", "(W) shl", "(W) shr",
   "(W) store.ugm.d32x16t.a32", "(W) store.ugm.d32x32t.a32", "(W) store.ugm.d32x64t.a32", "(W) sync.bar"
  ]

set_option maxRecDepth 100000 in
/-- The dump has 968 predicate-prefixed statements. -/
theorem predOpcodes_length : predOpcodes.length = 968 := by decide

set_option maxRecDepth 100000 in
/-- The dump has 377 predicated moves. -/
theorem predOpcodes_mov_count : predOpcodes.count "(W) mov" = 377 := by decide

set_option maxRecDepth 100000 in
/-- Every predicated opcode is in the documented list. -/
theorem predOpcodes_all_known :
    predOpcodes.all (fun op => op ∈ knownPredOpcodes) = true := by decide

end IntelGpu
