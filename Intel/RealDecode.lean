-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Decode
public import Intel.Examples.RealAddOne

@[expose] public section

/-!
# Decoding the real kernel

Stage 62 showed that the stage-5 decoder reads none of a real IGC dump. This
module adds a decoder for *exactly* the forms that kernel uses, and fails closed
on everything else:

- `Grf`: a GRF operand as its numeric fields — register number, region row and
  column offsets, vertical stride, region width, horizontal stride. A region
  printed as `<v>` is the IGC shorthand for `<v;1,0>`, and is normalised to
  that. Any other spelling is refused.
- `Width`: the typed suffix (`d32`, `a64`, `q`, `w`, `ud`), read literally
  after the colon.
- `RInstr`: the decoded instruction, with execution size kept. `lsc_load.ugm`
  and `lsc_store.ugm` name their payload register without a region, so those
  operands are bare register numbers.
- `decodeReal` / `decodeRealProgram`: the decoder, `Option`-valued.

Parsing works on `List Char` with structural recursion rather than
`String.splitOn`, so the `decide` proofs below reduce in the kernel.

`decodeRealProgram realAddOne` is a kernel-checked theorem (unfold the two
decoder definitions, then `decide`), so the correspondence between the dump and
the Lean program is a fact, not a claim.
The `or` prologue that sets `%cr0` is matched as one literal instruction and
otherwise refused: it is not needed for the kernel's effect and decoding it
would mean modelling the control register.
-/

namespace IntelGpu

/-- Numeric fields of a GRF operand. `width` is the number between `;` and
`,` in `<vstride;width,hstride>`. -/
structure Grf where
  num : Nat
  row : Nat
  col : Nat
  vstride : Nat
  width : Nat
  hstride : Nat
  deriving Repr, DecidableEq

/-- Typed suffix on an operand. -/
inductive Width where
  | d32
  | a64
  | q
  | w16
  | ud
  deriving Repr, DecidableEq

/-- The decoded instruction. Load and store payloads are bare registers, as
IGC prints them. -/
inductive RInstr where
  | mul (exec : Nat) (dst a b : Grf)
  | mov (exec : Nat) (dst src : Grf)
  | add3 (exec : Nat) (dst a b c : Grf)
  | shl (exec : Nat) (dst src : Grf) (amount : Nat)
  | add (exec : Nat) (dst a b : Grf)
  | addImm (exec : Nat) (dst src : Grf) (imm : Nat) (w : Width)
  | load (exec : Nat) (dst : Nat) (w : Width) (addrReg : Nat)
  | store (exec : Nat) (addrReg : Nat) (w : Width) (src : Nat)
  | ret (exec : Nat)
  /-- The `%cr0` prologue, matched exactly. -/
  | prologue
  deriving Repr, DecidableEq

/-- Every decimal run in a list, in order. Structural on the fuel; each step
consumes at least one character, so `runs cs` with fuel `cs.length` is exact. -/
def runsGo : Nat → List Char → List Nat
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, c :: rest =>
      if isDigit c then
        digitsToNat (c :: rest.takeWhile isDigit) :: runsGo n (rest.dropWhile isDigit)
      else runsGo n rest

def runs (cs : List Char) : List Nat := runsGo cs.length cs

def numRuns (s : String) : List Nat := runs s.toList

/-- Characters before the first colon, i.e. an operand without its typed
suffix. -/
def beforeColon : List Char → List Char
  | [] => []
  | ':' :: _ => []
  | c :: rest => c :: beforeColon rest

def operandCore (s : String) : String := String.ofList (beforeColon s.toList)

/-- The characters after the first colon. -/
def afterColon : List Char → Option (List Char)
  | [] => none
  | ':' :: rest => some rest
  | _ :: rest => afterColon rest

/-- The typed suffix, read literally: exactly the characters after the colon. -/
def parseWidth (s : String) : Option Width :=
  match afterColon s.toList with
  | some ['d', '3', '2'] => some .d32
  | some ['a', '6', '4'] => some .a64
  | some ['u', 'd'] => some .ud
  | some ['q'] => some .q
  | some ['w'] => some .w16
  | _ => none

def isSpace (c : Char) : Bool := c = ' ' || c = '\t'

def dropSpaces : List Char → List Char
  | [] => []
  | c :: cs => if isSpace c then dropSpaces cs else c :: cs

def allDigits : List Char → Bool
  | [] => true
  | c :: cs => isDigit c && allDigits cs

/-- The characters after the first comma. -/
def afterComma : List Char → Option (List Char)
  | [] => none
  | ',' :: rest => some rest
  | _ :: rest => afterComma rest

/-- Execution size, printed as `(M1, 32)` or `(M1_NM, 1)`. The execution mode
may contain digits, so the size is read from after the comma. -/
def parseExec (s : String) : Option Nat :=
  let cs := s.toList
  match cs with
  | '(' :: 'M' :: _ =>
      match afterComma cs, cs.getLast? with
      | some tail, some ')' =>
          let body := dropSpaces tail.dropLast
          if body.isEmpty then none
          else if allDigits body then some (digitsToNat body) else none
      | _, _ => none
  | _ => none

/-- A GRF operand: `V0045(0,0)<1>` or `V0045(0,0)<1;1,0>`. -/
def parseGrf (s : String) : Option Grf :=
  match numRuns (operandCore s) with
  | [n, r, c, v] => some ⟨n, r, c, v, 1, 0⟩
  | [n, r, c, v, w, h] => some ⟨n, r, c, v, w, h⟩
  | _ => none

def isHexDigit (c : Char) : Bool :=
  isDigit c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def allHexDigits : List Char → Bool
  | [] => true
  | c :: cs => isHexDigit c && allHexDigits cs

def hexDigitVal (c : Char) : Nat :=
  if isDigit c then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def hexDigitsToNat : List Char → Nat
  | [] => 0
  | c :: cs => hexDigitVal c * 16 ^ cs.length + hexDigitsToNat cs

/-- An integer literal with optional typed suffix: `0x2`, `0x1:w`, `7`. -/
def parseLit (s : String) : Option Nat :=
  match (operandCore s).toList with
  | '0' :: 'x' :: rest =>
      if rest.isEmpty then none
      else if allHexDigits rest then some (hexDigitsToNat rest) else none
  | cs =>
      if cs.isEmpty then none
      else if allDigits cs then some (digitsToNat cs) else none

/-- A bare register operand: `V0054`, with any typed suffix ignored. -/
def parsePlainReg (s : String) : Option Nat :=
  match numRuns (operandCore s) with
  | [n] => some n
  | _ => none

/-- A memory operand `flat[V0053]:a64`: a register number, no region. -/
def parseMem (s : String) : Option Nat := parsePlainReg s

def decodeReal : Stmt → Option RInstr
  | .label _ => none
  | .instruction op operands =>
      match op, operands with
      | "mul", [e, d, a, b] =>
          match parseExec e, parseGrf d, parseGrf a, parseGrf b with
          | some n, some x, some y, some z => some (.mul n x y z)
          | _, _, _, _ => none
      | "mov", [e, d, s] =>
          match parseExec e, parseGrf d, parseGrf s with
          | some n, some x, some y => some (.mov n x y)
          | _, _, _ => none
      | "add3", [e, d, a, b, c] =>
          match parseExec e, parseGrf d, parseGrf a, parseGrf b, parseGrf c with
          | some n, some w, some x, some y, some z => some (.add3 n w x y z)
          | _, _, _, _, _ => none
      | "shl", [e, d, s, k] =>
          match parseExec e, parseGrf d, parseGrf s, parseLit k with
          | some n, some x, some y, some m => some (.shl n x y m)
          | _, _, _, _ => none
      | "add", [e, d, a, b] =>
          match parseExec e, parseGrf d, parseGrf a with
          | some n, some x, some y =>
              match parseGrf b with
              | some z => some (.add n x y z)
              | none =>
                  match parseLit b, parseWidth b with
                  | some v, some wd => some (.addImm n x y v wd)
                  | _, _ => none
          | _, _, _ => none
      | "lsc_load.ugm", [e, d, a] =>
          match parseExec e, parsePlainReg d, parseWidth d, parseMem a with
          | some n, some x, some wd, some y => some (.load n x wd y)
          | _, _, _, _ => none
      | "lsc_store.ugm", [e, a, s] =>
          match parseExec e, parseMem a, parsePlainReg s, parseWidth s with
          | some n, some x, some y, some wd => some (.store n x wd y)
          | _, _, _, _ => none
      | "or", ["(M1_NM, 1)", "%cr0(0,0)<1>", "%cr0(0,0)<0;1,0>", "0x400004c0:ud"] =>
          some .prologue
      | "ret", [e] =>
          match parseExec e with
          | some n => some (.ret n)
          | none => none
      | _, _ => none

def decodeRealStmts : List Stmt → Option (List RInstr)
  | [] => some []
  | s :: rest =>
      match decodeReal s, decodeRealStmts rest with
      | some i, some is => some (i :: is)
      | _, _ => none

def decodeRealProgram (p : Program) : Option (List RInstr) :=
  decodeRealStmts p.statements

/-- The real kernel decodes. -/
theorem realAddOne_decodes :
    (decodeRealProgram realAddOne).isSome = true := by
  unfold decodeRealProgram decodeRealStmts realAddOne
  decide

/-- All eleven instructions are accounted for: the prologue plus ten. -/
theorem realAddOne_decoded_length :
    (decodeRealProgram realAddOne).map List.length = some 11 := by
  unfold decodeRealProgram decodeRealStmts realAddOne
  decide

/-- The load reads `V0053`'s target into bare register `V0054` as d32. -/
theorem realAddOne_load :
    (decodeRealProgram realAddOne).bind (fun is => is[7]?) =
      some (.load 32 54 .d32 53) := by
  unfold decodeRealProgram decodeRealStmts realAddOne
  decide

/-- The add-after-load is an add-immediate with the `:w` suffix kept. -/
theorem realAddOne_addImm :
    (decodeRealProgram realAddOne).bind (fun is => is[8]?) =
      some (.addImm 32 ⟨55, 0, 0, 1, 1, 0⟩ ⟨54, 0, 0, 1, 1, 0⟩ 1 .w16) := by
  unfold decodeRealProgram decodeRealStmts realAddOne
  decide

/-- The store writes bare register `V0055` back to `V0053`'s target as d32. -/
theorem realAddOne_store :
    (decodeRealProgram realAddOne).bind (fun is => is[9]?) =
      some (.store 32 53 .d32 55) := by
  unfold decodeRealProgram decodeRealStmts realAddOne
  decide

/-- A malformed execution size is refused. -/
theorem parseExec_rejects_extra_field : parseExec "(M1, 32, 7)" = none := by decide

/-- The decoder refuses a truncated instruction. -/
theorem decodeReal_rejects_truncated :
    decodeReal (.instruction "add" ["(M1, 32)", "V0055(0,0)<1>"]) = none := by decide

/-- A load payload must be a bare register; a region spelling is refused
rather than guessed at. -/
theorem decodeReal_rejects_region_payload :
    decodeReal (.instruction "lsc_load.ugm"
      ["(M1, 32)", "V0054(0,0)<1>", "flat[V0053]:a64"]) = none := by decide

end IntelGpu
