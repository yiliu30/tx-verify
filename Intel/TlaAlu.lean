-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaMovExec

@[expose] public section

/-!
# Decoding the predicated SYCL-TLA ALU forms

The dump uses predicated `and`/`add`/`mad`/`mul`/`shr`/`shl`/`or`/`asr`/
`mach`/`macl` instructions. This module gives the register-destination forms a
structured `TlaAlu` representation: operation, execution control, destination,
two sources and an optional third source for `mad`.

The parser is fail-closed: non-`r` destinations (`acc0`, `a0`, `cr0`) are not
accepted yet. The census records how many of each form parse.
-/

namespace IntelGpu

inductive TlaAluOp where
  | and | add | mul | shr | shl | or | asr | mad | mach | macl
  deriving Repr, DecidableEq

structure TlaAlu where
  op : TlaAluOp
  exec : Exec
  dst : Grf
  src1 : TlaSrc
  src2 : TlaSrc
  src3 : Option TlaSrc := none
  deriving Repr, DecidableEq

def parseTlaAluOp : String → Option TlaAluOp
  | "(W) and" => some .and
  | "(W) add" => some .add
  | "(W) mul" => some .mul
  | "(W) shr" => some .shr
  | "(W) shl" => some .shl
  | "(W) or" => some .or
  | "(W) asr" => some .asr
  | "(W) mad" => some .mad
  | "(W) mach" => some .mach
  | "(W) macl" => some .macl
  | _ => none

/-- An operand with the `r` register prefix. -/
def isRReg (s : String) : Bool :=
  match (operandCore s).toList with
  | 'r' :: _ => true
  | _ => false

/-- The `<v;h>` source shorthand used by some ALU operands. -/
def parseTlaSrcAlu (s : String) : Option TlaSrc :=
  if isRReg s then
    match numRuns (operandCore s) with
    | [n, sub, v, h] => some (.reg ⟨n, 0, sub, v, 1, h⟩)
    | _ => parseTlaSrc s
  else parseTlaSrc s

def parseTlaAluInstr : TlaInstr → Option TlaAlu
  | .predicated "(W) mad" (e :: dst :: s1 :: s2 :: s3 :: _) =>
      if isRReg dst then
        match parseTlaExec e, parseTlaDstGrf dst, parseTlaSrcAlu s1, parseTlaSrcAlu s2,
          parseTlaSrcAlu s3 with
        | some ex, some d, some a, some b, some c =>
            some ⟨.mad, ex, d, a, b, some c⟩
        | _, _, _, _, _ => none
      else none
  | .predicated op (e :: dst :: s1 :: s2 :: _) =>
      if isRReg dst then
        match parseTlaAluOp op, parseTlaExec e, parseTlaDstGrf dst,
          parseTlaSrcAlu s1, parseTlaSrcAlu s2 with
        | some o, some ex, some d, some a, some b => some ⟨o, ex, d, a, b, none⟩
        | _, _, _, _, _ => none
      else none
  | _ => none

/-- The decoded register-destination ALU instructions. -/
def realTlaGemmAlu : List TlaAlu :=
  (decodeTlaProgram realTlaGemm).filterMap parseTlaAluInstr

theorem parseTlaAlu_and :
    parseTlaAluInstr (.predicated "(W) and"
      ["(1|M0)", "r127.2<1>:ud", "r0.0<0;1,0>:ud", "0xFFFFFFC0:ud"]) =
      some ⟨.and, ⟨1, 0, true⟩, ⟨127, 0, 2, 1, 1, 1⟩,
        .reg ⟨0, 0, 0, 0, 1, 0⟩, .imm (0xFFFFFFC0 : Int) .ud, none⟩ := by
  decide

theorem parseTlaAlu_add :
    parseTlaAluInstr (.predicated "(W) add"
      ["(1|M0)", "r127.2<1>:ud", "r127.2<0;1,0>:ud", "0x280:ud"]) =
      some ⟨.add, ⟨1, 0, true⟩, ⟨127, 0, 2, 1, 1, 1⟩,
        .reg ⟨127, 0, 2, 0, 1, 0⟩, .imm (0x280 : Int) .ud, none⟩ := by
  decide

theorem parseTlaAlu_mad :
    parseTlaAluInstr (.predicated "(W) mad"
      ["(1|M0)", "r127.0<1>:ud", "r127.2<0;0>:ud", "r127.0<0;0>:uw", "0x40:uw"]) =
      some ⟨.mad, ⟨1, 0, true⟩, ⟨127, 0, 0, 1, 1, 1⟩,
        .reg ⟨127, 0, 2, 0, 1, 0⟩, .reg ⟨127, 0, 0, 0, 1, 0⟩,
        some (.imm (0x40 : Int) .w16)⟩ := by
  decide

set_option maxRecDepth 100000 in
/-- The number of decoded `and` forms with `r` destinations. -/
theorem realTlaGemmAlu_and_count :
    (realTlaGemmAlu.filter (fun a => a.op = .and)).length = 4 := by
  decide

set_option maxRecDepth 100000 in
/-- The number of decoded `add` forms. -/
theorem realTlaGemmAlu_add_count :
    (realTlaGemmAlu.filter (fun a => a.op = .add)).length = 31 := by
  decide

set_option maxRecDepth 100000 in
/-- The number of decoded `mad` forms. -/
theorem realTlaGemmAlu_mad_count :
    (realTlaGemmAlu.filter (fun a => a.op = .mad)).length = 1 := by
  decide

end IntelGpu
