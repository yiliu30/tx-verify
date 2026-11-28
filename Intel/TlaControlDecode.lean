-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaDecode

@[expose] public section

/-!
# Decoding the SYCL-TLA control forms

The SYCL-TLA GEMM's control flow uses predicated `jmpi` labels and the
`sync.nop`/`sync.allrd`/`sync.bar` scoreboard forms. This module gives both a
structured representation and censuses them.

The dump has 58 `jmpi` instructions and 284 `sync` instructions (243
`sync.nop`, 40 `sync.allrd`, 1 `sync.bar`).
-/

namespace IntelGpu

/-- A predicated jump to a label. -/
structure TlaJmp where
  predicate : String
  target : String
  deriving Repr, DecidableEq

def isJmpiOp (op : String) : Bool :=
  match op.toList.reverse with
  | 'i' :: 'p' :: 'm' :: 'j' :: _ => true
  | _ => false

/-- Does the opcode end in ` goto`? -/
def isGotoOp (op : String) : Bool :=
  match op.toList.reverse with
  | 'o' :: 't' :: 'o' :: 'g' :: ' ' :: _ => true
  | _ => false

def parseTlaJmpInstr : TlaInstr → Option TlaJmp
  | .predicated op [target] =>
      if isJmpiOp op then some ⟨op, target⟩ else none
  | .predicated op (_e :: target :: _) =>
      if isJmpiOp op || isGotoOp op then some ⟨op, target⟩ else none
  | _ => none

def realTlaGemmJmps : List TlaJmp :=
  (decodeTlaProgram realTlaGemm).filterMap parseTlaJmpInstr

/-- A `sync.*` scoreboard instruction. -/
structure TlaSync where
  opcode : String
  operands : List String
  deriving Repr, DecidableEq

def parseTlaSyncInstr : TlaInstr → Option TlaSync
  | .predicated "(W) sync.bar" ops => some ⟨"sync.bar", ops⟩
  | .plain "sync.nop" ops => some ⟨"sync.nop", ops⟩
  | .plain "sync.allrd" ops => some ⟨"sync.allrd", ops⟩
  | .plain "sync.bar" ops => some ⟨"sync.bar", ops⟩
  | _ => none

def realTlaGemmSyncs : List TlaSync :=
  (decodeTlaProgram realTlaGemm).filterMap parseTlaSyncInstr

theorem parseTlaJmp_example :
    parseTlaJmpInstr (.predicated "(W&~f2.1) jmpi" ["_0_110"]) =
      some ⟨"(W&~f2.1) jmpi", "_0_110"⟩ := by decide

theorem parseTlaSync_example :
    parseTlaSyncInstr (.plain "sync.nop"
      ["null", "{Compacted,$11.src}"]) =
      some ⟨"sync.nop", ["null", "{Compacted,$11.src}"]⟩ := by decide

set_option maxRecDepth 100000 in
/-- The dump has 58 predicated jumps. -/
theorem realTlaGemmJmps_length : realTlaGemmJmps.length = 58 := by decide

set_option maxRecDepth 100000 in
/-- The dump has 243 `sync.nop` forms. -/
theorem realTlaGemmSync_nop_count :
    (realTlaGemmSyncs.filter (fun s => s.opcode = "sync.nop")).length = 243 := by
  decide

set_option maxRecDepth 100000 in
/-- The dump has 40 `sync.allrd` forms. -/
theorem realTlaGemmSync_allrd_count :
    (realTlaGemmSyncs.filter (fun s => s.opcode = "sync.allrd")).length = 40 := by
  decide

set_option maxRecDepth 100000 in
/-- The dump has 1 `sync.bar` form. -/
theorem realTlaGemmSync_bar_count :
    (realTlaGemmSyncs.filter (fun s => s.opcode = "sync.bar")).length = 1 := by
  decide

end IntelGpu
