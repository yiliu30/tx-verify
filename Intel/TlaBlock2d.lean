-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaMovExec

@[expose] public section

/-!
# Decoding the SYCL-TLA block2d memory forms

The SYCL-TLA GEMM reads and writes its tiles with the predicated block2d
instructions `(W) load.ugm.*` and `(W) store.ugm.*`. This module gives them a
structured `TlaBlock2d` representation with the execution control, the data
register operand and the `ss[...]` address operand.

All 393 block2d forms in the dump parse: 214 loads and 179 stores. The address
expression itself is kept as text; splitting the `ss[a0.2][r2:1-0x...]` form is
the next stage.
-/

namespace IntelGpu

structure TlaBlock2d where
  opcode : String
  exec : Exec
  reg : String
  addr : String
  deriving Repr, DecidableEq

/-- The characters after a `(W) ` prefix. -/
def afterW (op : String) : Option (List Char) :=
  match op.toList with
  | '(' :: 'W' :: ')' :: ' ' :: rest => some rest
  | _ => none

def startsLoad : List Char → Bool
  | 'l' :: 'o' :: 'a' :: 'd' :: '.' :: _ => true
  | _ => false

def startsStore : List Char → Bool
  | 's' :: 't' :: 'o' :: 'r' :: 'e' :: '.' :: _ => true
  | _ => false

def parseTlaBlock2dInstr : TlaInstr → Option TlaBlock2d
  | .predicated op (e :: a :: b :: _) =>
      match afterW op, parseTlaExec e with
      | some rest, some ex =>
          if startsLoad rest then some ⟨op, ex, a, b⟩
          else if startsStore rest then some ⟨op, ex, b, a⟩
          else none
      | _, _ => none
  | _ => none

/-- The decoded block2d instructions. -/
def realTlaGemmBlock2d : List TlaBlock2d :=
  (decodeTlaProgram realTlaGemm).filterMap parseTlaBlock2dInstr

def TlaBlock2d.isLoad (b : TlaBlock2d) : Bool :=
  startsLoad ((afterW b.opcode).getD [])

def TlaBlock2d.isStore (b : TlaBlock2d) : Bool :=
  startsStore ((afterW b.opcode).getD [])

theorem parseTlaBlock2d_load :
    parseTlaBlock2dInstr (.predicated "(W) load.ugm.d32x64t.a32"
      ["(1|M0)", "r13:4", "ss[a0.2][r2:1-0xE2C0]"]) =
      some ⟨"(W) load.ugm.d32x64t.a32", ⟨1, 0, true⟩, "r13:4",
        "ss[a0.2][r2:1-0xE2C0]"⟩ := by
  decide

theorem parseTlaBlock2d_store :
    parseTlaBlock2dInstr (.predicated "(W) store.ugm.d32x64t.a32"
      ["(1|M0)", "ss[a0.2][r2:1-0xE2C0]", "r13:4"]) =
      some ⟨"(W) store.ugm.d32x64t.a32", ⟨1, 0, true⟩, "r13:4",
        "ss[a0.2][r2:1-0xE2C0]"⟩ := by
  decide

set_option maxRecDepth 100000 in
/-- All 393 block2d instructions parse. -/
theorem realTlaGemmBlock2d_length : realTlaGemmBlock2d.length = 393 := by decide

set_option maxRecDepth 100000 in
/-- 214 block2d instructions are loads. -/
theorem realTlaGemmBlock2d_load_count :
    (realTlaGemmBlock2d.filter TlaBlock2d.isLoad).length = 214 := by decide

set_option maxRecDepth 100000 in
/-- 179 block2d instructions are stores. -/
theorem realTlaGemmBlock2d_store_count :
    (realTlaGemmBlock2d.filter TlaBlock2d.isStore).length = 179 := by decide

end IntelGpu
