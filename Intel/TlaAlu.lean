-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaMovExec

@[expose] public section

/-!
# Decoding the predicated SYCL-TLA ALU forms

The dump uses predicated `and`/`add`/`mad`/`mul`/`shr`/`shl`/`or`/`asr`/
`mach`/`macl` instructions. This module gives all of them a structured
`TlaAlu` representation: operation, execution control, destination class
(`r`, `acc`, `a` or `cr`), two sources and an optional third source for `mad`.

All 109 ALU instructions in the dump parse. Execution currently handles the
`r`-destination `and`/`add`/`mad` subset; the other classes are decoded but
not executed yet.
-/

namespace IntelGpu

inductive TlaAluOp where
  | and | add | mul | shr | shl | or | asr | not | mad | mach | macl
  deriving Repr, DecidableEq

/-- An ALU destination: a GRF, an accumulator, an address register or a
control register. -/
inductive TlaAluDst where
  | r (g : Grf)
  | acc (num sub : Nat)
  | addr (num sub : Nat)
  | cr (num sub : Nat)
  | flag (num sub : Nat)
  deriving Repr, DecidableEq

structure TlaAlu where
  op : TlaAluOp
  exec : Exec
  dst : TlaAluDst
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
  | "(W) not" => some .not
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
  match (operandCore s).toList with
  | 'c' :: 'r' :: _ =>
      match numRuns (operandCore s) with
      | [n, sub, _] => some (.cr n sub)
      | [n, sub, _v, _w, _h] => some (.cr n sub)
      | _ => none
  | 'r' :: _ =>
      match numRuns (operandCore s) with
      | [n, sub, v, h] => some (.reg ⟨n, 0, sub, v, 1, h⟩)
      | _ => parseTlaSrc s
  | _ => parseTlaSrc s

/-- Parse an ALU destination class. -/
def parseTlaAluDst (s : String) : Option TlaAluDst :=
  match (operandCore s).toList with
  | 'r' :: _ => (parseTlaDstGrf s).map .r
  | 'a' :: 'c' :: 'c' :: _ =>
      match numRuns (operandCore s) with
      | [n, sub, _] => some (.acc n sub)
      | _ => none
  | 'a' :: _ =>
      match numRuns (operandCore s) with
      | [n, sub, _] => some (.addr n sub)
      | _ => none
  | 'c' :: 'r' :: _ =>
      match numRuns (operandCore s) with
      | [n, sub, _] => some (.cr n sub)
      | [n, sub, _v, _w, _h] => some (.cr n sub)
      | _ => none
  | 'f' :: _ =>
      match numRuns (operandCore s) with
      | [n, sub, _] => some (.flag n sub)
      | _ => none
  | _ => none

def parseTlaAluInstr : TlaInstr → Option TlaAlu
  | .predicated "(W) not" (e :: dst :: s1 :: _) =>
      match parseTlaExec e, parseTlaAluDst dst, parseTlaSrcAlu s1 with
      | some ex, some d, some a => some ⟨.not, ex, d, a, .imm 0 .d32, none⟩
      | _, _, _ => none
  | .predicated "(W) mad" (e :: dst :: s1 :: s2 :: s3 :: _) =>
      match parseTlaExec e, parseTlaAluDst dst, parseTlaSrcAlu s1, parseTlaSrcAlu s2,
        parseTlaSrcAlu s3 with
      | some ex, some d, some a, some b, some c =>
          some ⟨.mad, ex, d, a, b, some c⟩
      | _, _, _, _, _ => none
  | .predicated op (e :: dst :: s1 :: s2 :: _) =>
      match parseTlaAluOp op, parseTlaExec e, parseTlaAluDst dst,
        parseTlaSrcAlu s1, parseTlaSrcAlu s2 with
      | some o, some ex, some d, some a, some b => some ⟨o, ex, d, a, b, none⟩
      | _, _, _, _, _ => none
  | _ => none

/-- The decoded ALU instructions. -/
def realTlaGemmAlu : List TlaAlu :=
  (decodeTlaProgram realTlaGemm).filterMap parseTlaAluInstr

theorem parseTlaAlu_and :
    parseTlaAluInstr (.predicated "(W) and"
      ["(1|M0)", "r127.2<1>:ud", "r0.0<0;1,0>:ud", "0xFFFFFFC0:ud"]) =
      some ⟨.and, ⟨1, 0, true⟩, .r ⟨127, 0, 2, 1, 1, 1⟩,
        .reg ⟨0, 0, 0, 0, 1, 0⟩, .imm (0xFFFFFFC0 : Int) .ud, none⟩ := by
  decide

theorem parseTlaAlu_add :
    parseTlaAluInstr (.predicated "(W) add"
      ["(1|M0)", "r127.2<1>:ud", "r127.2<0;1,0>:ud", "0x280:ud"]) =
      some ⟨.add, ⟨1, 0, true⟩, .r ⟨127, 0, 2, 1, 1, 1⟩,
        .reg ⟨127, 0, 2, 0, 1, 0⟩, .imm (0x280 : Int) .ud, none⟩ := by
  decide

theorem parseTlaAlu_mad :
    parseTlaAluInstr (.predicated "(W) mad"
      ["(1|M0)", "r127.0<1>:ud", "r127.2<0;0>:ud", "r127.0<0;0>:uw", "0x40:uw"]) =
      some ⟨.mad, ⟨1, 0, true⟩, .r ⟨127, 0, 0, 1, 1, 1⟩,
        .reg ⟨127, 0, 2, 0, 1, 0⟩, .reg ⟨127, 0, 0, 0, 1, 0⟩,
        some (.imm (0x40 : Int) .w16)⟩ := by
  decide

set_option maxRecDepth 100000 in
/-- All 109 ALU instructions parse. -/
theorem realTlaGemmAlu_total : realTlaGemmAlu.length = 109 := by decide

set_option maxRecDepth 100000 in
/-- The number of decoded `and` forms. -/
theorem realTlaGemmAlu_and_count :
    (realTlaGemmAlu.filter (fun a => a.op = .and)).length = 5 := by decide

set_option maxRecDepth 100000 in
/-- The number of decoded `add` forms. -/
theorem realTlaGemmAlu_add_count :
    (realTlaGemmAlu.filter (fun a => a.op = .add)).length = 31 := by decide

set_option maxRecDepth 100000 in
/-- The number of decoded `mul` forms. -/
theorem realTlaGemmAlu_mul_count :
    (realTlaGemmAlu.filter (fun a => a.op = .mul)).length = 14 := by decide

set_option maxRecDepth 100000 in
/-- The number of decoded `shr` forms. -/
theorem realTlaGemmAlu_shr_count :
    (realTlaGemmAlu.filter (fun a => a.op = .shr)).length = 25 := by decide

set_option maxRecDepth 100000 in
/-- The number of decoded `or` forms. -/
theorem realTlaGemmAlu_or_count :
    (realTlaGemmAlu.filter (fun a => a.op = .or)).length = 1 := by decide

end IntelGpu
