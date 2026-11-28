-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaRegions
public import Intel.TlaMovExec
public import Intel.TlaAluState
public import Intel.TlaBlock2dPlain

@[expose] public section

/-!
# The plain (unpredicated) instruction forms

Most of the prologue and epilogue is written without the `(W) ` predicate
prefix: 531 plain `mov` forms and 288 plain ALU forms (`and` 6, `add` 4,
`mul` 128, `mad` 128, `or` 16, `shl` 3, `shr` 3), plus 32 plain
`store_block2d.ugm.*` forms. This
module decodes them into the same `TlaMov`, `TlaAlu` and `TlaBlock2d`
structures, so the stage 185/189/194 semantics apply unchanged.
-/

namespace IntelGpu

/-- A plain `mov` form. -/
def parseTlaMovPlain : TlaInstr → Option TlaMov
  | .plain "mov" (e :: dst :: src :: _) =>
      match parseTlaExec e, parseTlaDst dst, parseTlaSrc src with
      | some ex, some d, some s => some ⟨ex, d, s⟩
      | _, _, _ => none
  | _ => none

/-- The decoded plain moves. -/
def realTlaGemmMovsPlain : List TlaMov :=
  (decodeTlaProgram realTlaGemm).filterMap parseTlaMovPlain

/-- A plain ALU opcode. -/
def parseTlaAluOpPlain : String → Option TlaAluOp
  | "and" => some .and
  | "add" => some .add
  | "mul" => some .mul
  | "shr" => some .shr
  | "shl" => some .shl
  | "or" => some .or
  | "asr" => some .asr
  | "mad" => some .mad
  | "mach" => some .mach
  | "macl" => some .macl
  | _ => none

/-- A plain ALU form; `mad` has a third source. -/
def parseTlaAluPlain : TlaInstr → Option TlaAlu
  | .plain "mad" (e :: dst :: s1 :: s2 :: s3 :: _) =>
      match parseTlaExec e, parseTlaAluDst dst, parseTlaSrcAlu s1,
        parseTlaSrcAlu s2, parseTlaSrcAlu s3 with
      | some ex, some d, some a, some b, some c => some ⟨.mad, ex, d, a, b, some c⟩
      | _, _, _, _, _ => none
  | .plain op (e :: dst :: s1 :: s2 :: _) =>
      match parseTlaAluOpPlain op, parseTlaExec e, parseTlaAluDst dst,
        parseTlaSrcAlu s1, parseTlaSrcAlu s2 with
      | some o, some ex, some d, some a, some b => some ⟨o, ex, d, a, b, none⟩
      | _, _, _, _, _ => none
  | _ => none

/-- The decoded plain ALU forms. -/
def realTlaGemmAluPlain : List TlaAlu :=
  (decodeTlaProgram realTlaGemm).filterMap parseTlaAluPlain

/-- A plain `store_block2d.ugm.*` opcode. -/
def isPlainStoreOp (op : String) : Bool :=
  listHasPrefix "store_block2d.ugm".toList op.toList

/-- A plain block2d store form; the printed order is address then data. -/
def parseTlaBlock2dPlainStore : TlaInstr → Option TlaBlock2d
  | .plain op (e :: a :: b :: _) =>
      if isPlainStoreOp op then
        (parseTlaExec e).map (fun ex => ⟨op, ex, b, a⟩)
      else none
  | _ => none

/-- The decoded plain block2d stores. -/
def realTlaGemmBlock2dPlainStore : List TlaBlock2d :=
  (decodeTlaProgram realTlaGemm).filterMap parseTlaBlock2dPlainStore

set_option maxRecDepth 1000000 in
/-- There are 531 plain moves. -/
theorem realTlaGemmMovsPlain_length : realTlaGemmMovsPlain.length = 531 := by
  decide

set_option maxRecDepth 1000000 in
/-- There are 288 plain ALU forms. -/
theorem realTlaGemmAluPlain_length : realTlaGemmAluPlain.length = 288 := by
  decide

set_option maxRecDepth 1000000 in
/-- There are 32 plain block2d stores. -/
theorem realTlaGemmBlock2dPlainStore_length :
    realTlaGemmBlock2dPlainStore.length = 32 := by decide

set_option maxRecDepth 1000000 in
/-- The plain ALU opcodes are `and`, `add`, `mul`, `mad`, `or`, `shl`, `shr`. -/
theorem realTlaGemmAluPlain_ops :
    realTlaGemmAluPlain.all (fun a =>
      a.op = .and || a.op = .add || a.op = .mul || a.op = .mad ||
      a.op = .or || a.op = .shl || a.op = .shr) = true := by
  decide

/-- PC 48 is the first plain move. -/
def progInstrAt (pc : Nat) : Option TlaInstr :=
  (withPc.find? (fun p => p.1 = pc)).map (fun p => p.2)

set_option maxRecDepth 100000 in
theorem progInstr48 :
    progInstrAt 48 = some (.plain "mov" ["(16|M0)", "r3.0<1>:d", "r1.0<1;1,0>:uw"]) := by
  decide

set_option maxRecDepth 100000 in
theorem progInstr1622 :
    progInstrAt 1622 = some (.plain "mul"
      ["(16|M0)", "r14.0<1>:f", "r23.0<0;1,0>:f", "r3.0<1;1,0>:f", "{Compacted,@5,$0.dst}"]) := by
  decide

set_option maxRecDepth 100000 in
theorem progInstr1646 :
    progInstrAt 1646 = some (.plain "store_block2d.ugm.d32.a64"
      ["(1|M0)", "[r4:1]", "r15:8", "{A@1,$5}"]) := by
  decide

set_option maxRecDepth 100000 in
/-- PC 48 decodes to an unmasked 16-lane move. -/
theorem parseTlaMovPlain_48 :
    (progInstrAt 48).bind parseTlaMovPlain =
      some ⟨⟨16, 0, true⟩, .reg ⟨3, 0, 0, 1, 1, 1⟩, .reg ⟨1, 0, 0, 1, 1, 0⟩⟩ := by
  decide

set_option maxRecDepth 100000 in
/-- PC 1622 decodes to the plain multiply. -/
theorem parseTlaAluPlain_1622 :
    (progInstrAt 1622).bind parseTlaAluPlain =
      some ⟨.mul, ⟨16, 0, true⟩, .r ⟨14, 0, 0, 1, 1, 1⟩,
        .reg ⟨23, 0, 0, 0, 1, 0⟩, .reg ⟨3, 0, 0, 1, 1, 0⟩, none⟩ := by
  decide

set_option maxRecDepth 100000 in
/-- PC 1646 decodes to a `r15:8` block2d store at `[r4:1]`. -/
theorem parseTlaBlock2dPlainStore_1646 :
    (progInstrAt 1646).bind parseTlaBlock2dPlainStore =
      some ⟨"store_block2d.ugm.d32.a64", ⟨1, 0, true⟩, "r15:8", "[r4:1]"⟩ := by
  decide

/-- The plain multiply at PC 1622 has the usual ALU semantics. -/
theorem plainMul_value (st : TlaState) :
    ∃ st', tlaAluStateStep? st ⟨.mul, ⟨16, 0, true⟩, .r ⟨14, 0, 0, 1, 1, 1⟩,
        .reg ⟨23, 0, 0, 0, 1, 0⟩, .reg ⟨3, 0, 0, 1, 1, 0⟩, none⟩ = some st' ∧
      st'.regs 14 0 = st.regs 23 0 * st.regs 3 0 := by
  refine ⟨_, rfl, ?_⟩
  simp [tlaAluFun, readTlaSrcState, srcIndex, writeTlaMasked,
    Exec.laneActive, Grf.dstIndex]

end IntelGpu
