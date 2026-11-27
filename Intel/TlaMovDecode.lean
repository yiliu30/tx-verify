-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaDecode

@[expose] public section

/-!
# Decoding the predicated SYCL-TLA moves

The SYCL-TLA GEMM has 377 `(W) mov` statements. This module gives them a
structured form: execution control, destination GRF and source (GRF or
immediate). The `(N|M0)` execution control and the `rN.M<...>` operand syntax
are parsed directly; unsupported forms return `none`.

The census proves that all 377 moves parse, and the two prologue moves are
worked examples.
-/

namespace IntelGpu

/-- A TLA destination: a GRF region or the null register. -/
inductive TlaDst where
  | reg (g : Grf)
  | null
  deriving Repr, DecidableEq

/-- A TLA source operand: a GRF region or an immediate. -/
inductive TlaSrc where
  | reg (g : Grf)
  | imm (v : Int) (w : Width)
  deriving Repr, DecidableEq

/-- A decoded predicated move. -/
structure TlaMov where
  exec : Exec
  dst : TlaDst
  src : TlaSrc
  deriving Repr, DecidableEq

/-- `(16|M0)` is an unmasked execution of size 16. -/
def parseTlaExec (s : String) : Option Exec :=
  match s.toList with
  | '(' :: rest =>
      let digits := rest.takeWhile isDigit
      if digits.isEmpty then none
      else
        match rest.dropWhile isDigit with
        | '|' :: _ => some ⟨digitsToNat digits, 0, true⟩
        | _ => none
  | _ => none

/-- The `rN.M<...>` destination form: one field is the hstride. -/
def parseTlaDstGrf (s : String) : Option Grf :=
  match numRuns (operandCore s) with
  | [n, sub, h] => some ⟨n, 0, sub, 1, 1, h⟩
  | [n, sub, v, w, h] => some ⟨n, 0, sub, v, w, h⟩
  | _ => none

/-- The `rN.M<...>` source form: one field is `<vstride;1,0>`. -/
def parseTlaSrcGrf (s : String) : Option Grf :=
  match numRuns (operandCore s) with
  | [n, sub, v] => some ⟨n, 0, sub, v, 1, 0⟩
  | [n, sub, v, w, h] => some ⟨n, 0, sub, v, w, h⟩
  | _ => none

/-- A width suffix, including the `uw`, `f` and `hf` spellings used by
immediates. -/
def parseTlaWidth (s : String) : Option Width :=
  match afterColon s.toList with
  | some ['u', 'w'] => some .w16
  | some ['f'] => some .d32
  | some ['h', 'f'] => some .d32
  | _ => parseWidth s

/-- A signed immediate. -/
def parseIntLit (s : String) : Option Int :=
  match (operandCore s).toList with
  | '-' :: rest =>
      match parseLit (String.ofList rest) with
      | some n => some (-(Int.ofNat n))
      | none => none
  | _ =>
      match parseLit s with
      | some n => some (Int.ofNat n)
      | none => none

/-- The `null` operand, with or without a region suffix. -/
def isNullOperand (s : String) : Bool :=
  match (operandCore s).toList with
  | 'n' :: 'u' :: 'l' :: 'l' :: _ => true
  | _ => false

/-- A null destination or a GRF destination. -/
def parseTlaDst (s : String) : Option TlaDst :=
  if isNullOperand s then some .null
  else
    match parseTlaDstGrf s with
    | some g => some (.reg g)
    | none => none

def parseTlaSrc (s : String) : Option TlaSrc :=
  match parseTlaSrcGrf s with
  | some g => some (.reg g)
  | none =>
      match parseIntLit s, parseTlaWidth s with
      | some v, some w => some (.imm v w)
      | _, _ => none

/-- Decode a `(W) mov` statement. -/
def parseTlaMovInstr : TlaInstr → Option TlaMov
  | .predicated "(W) mov" (e :: dst :: src :: _) =>
      match parseTlaExec e, parseTlaDst dst, parseTlaSrc src with
      | some ex, some d, some s => some ⟨ex, d, s⟩
      | _, _, _ => none
  | _ => none

/-- The decoded predicated moves. -/
def realTlaGemmMovs : List TlaMov :=
  (decodeTlaProgram realTlaGemm).filterMap parseTlaMovInstr

theorem parseTlaMov_prologue :
    parseTlaMovInstr (.predicated "(W) mov"
      ["(16|M0)", "r127.0<1>:ud", "0x0:ud"]) =
      some ⟨⟨16, 0, true⟩, .reg ⟨127, 0, 0, 1, 1, 1⟩, .imm (0 : Int) .ud⟩ := by
  decide

theorem parseTlaMov_id :
    parseTlaMovInstr (.predicated "(W) mov"
      ["(8|M0)", "r2.0<1>:ud", "r1.0<1;1,0>:ud"]) =
      some ⟨⟨8, 0, true⟩, .reg ⟨2, 0, 0, 1, 1, 1⟩, .reg ⟨1, 0, 0, 1, 1, 0⟩⟩ := by
  decide

set_option maxRecDepth 100000 in
/-- All 377 predicated moves parse. -/
theorem realTlaGemmMovs_length : realTlaGemmMovs.length = 377 := by decide

end IntelGpu
