-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaBlock2d

@[expose] public section

/-!
# Parsing the SYCL-TLA block2d addresses

The block2d instructions use `ss[a0.2][r2:1-0x...]` for shared/global tiles and
`bti[255][r127:1]` for binding-table addresses. This module parses those forms
into a `TlaAddr` structure and proves that all 393 block2d address operands in
the dump parse.
-/

namespace IntelGpu

structure TlaAddr where
  space : String
  reg : Nat
  sub : Nat
  base : Nat
  baseSub : Nat
  offset : Nat
  deriving Repr, DecidableEq

def splitAtChar (c : Char) : List Char → Option (List Char × List Char)
  | [] => none
  | x :: xs =>
      if x = c then some ([], xs)
      else
        match splitAtChar c xs with
        | some (l, r) => some (x :: l, r)
        | none => none

/-- The two bracketed fields of an `ss[...][...]` operand. -/
def parseBrackets : List Char → Option (List Char × List Char)
  | '[' :: rest =>
      match splitAtChar ']' rest with
      | some (a, '[' :: rest2) =>
          match splitAtChar ']' rest2 with
          | some (b, _) => some (a, b)
          | none => none
      | _ => none
  | _ => none

/-- A single bracketed field, used by the `[rN:M]` flat forms. -/
def parseSingleBracket : List Char → Option (List Char)
  | '[' :: rest =>
      match splitAtChar ']' rest with
      | some (a, _) => some a
      | none => none
  | _ => none

/-- The address-space prefix. -/
def parseSpace : List Char → Option (String × List Char)
  | 's' :: 's' :: rest => some ("ss", rest)
  | 'b' :: 't' :: 'i' :: rest => some ("bti", rest)
  | _ => none

/-- The first bracket: an `aN.M` address register or a numeric binding-table
index. -/
def parseAddrFirst (s : List Char) : Option (Nat × Nat) :=
  match s with
  | 'a' :: rest =>
      match numRuns (String.ofList rest) with
      | [n, sub] => some (n, sub)
      | _ => none
  | _ =>
      match parseLit (String.ofList s) with
      | some n => some (n, 0)
      | none => none

/-- The second bracket: `rN:M` with an optional `-offset`. -/
def parseAddrSecond (s : List Char) : Option (Nat × Nat × Nat) :=
  let (before, off) :=
    match splitAtChar '-' s with
    | some (b, o) => (b, o)
    | none => (s, [])
  let (baseStr, subStr) :=
    match splitAtChar ':' before with
    | some (b, r) => (b, r)
    | none => (before, [])
  match numRuns (String.ofList baseStr) with
  | [n] =>
      match parseLit (String.ofList subStr) with
      | some sub => some (n, sub, (parseLit (String.ofList off)).getD 0)
      | none => some (n, 0, (parseLit (String.ofList off)).getD 0)
  | _ => none

def parseTlaAddr (s : String) : Option TlaAddr :=
  match parseSpace s.toList with
  | some (space, rest) =>
      match parseBrackets rest with
      | some (first, second) =>
          match parseAddrFirst first, parseAddrSecond second with
          | some (reg, sub), some (base, baseSub, offset) =>
              some ⟨space, reg, sub, base, baseSub, offset⟩
          | _, _ => none
      | none => none
  | none =>
      match parseSingleBracket s.toList with
      | some content =>
          match parseAddrSecond content with
          | some (base, baseSub, offset) =>
              some ⟨"flat", 0, 0, base, baseSub, offset⟩
          | none => none
      | none => none

theorem parseTlaAddr_ss :
    parseTlaAddr "ss[a0.2][r2:1-0xE2C0]" =
      some ⟨"ss", 0, 2, 2, 1, 0xE2C0⟩ := by decide

theorem parseTlaAddr_bti :
    parseTlaAddr "bti[255][r127:1]" =
      some ⟨"bti", 255, 0, 127, 1, 0⟩ := by decide

theorem parseTlaAddr_flat :
    parseTlaAddr "[r4:1]" =
      some ⟨"flat", 0, 0, 4, 1, 0⟩ := by decide

set_option maxRecDepth 100000 in
/-- Every block2d address operand parses. -/
theorem realTlaGemmBlock2d_addr_parse :
    realTlaGemmBlock2d.all (fun b => (parseTlaAddr b.addr).isSome) = true := by
  decide

end IntelGpu
