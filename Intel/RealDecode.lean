-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Decode
public import Intel.Examples.RealAddOne

@[expose] public section

/-!
# Decoding the real kernel

Stage 62 showed that the stage-5 decoder reads none of a real IGC dump. This
module adds a decoder for the forms used by the real add-one kernel and by the
GEMM's control-flow shell, and fails closed on everything else:

- `Grf`: a GRF operand as its numeric fields — register number, region row and
  column offsets, vertical stride, region width, horizontal stride. A region
  printed as `<v>` is the IGC shorthand for `<v;1,0>`, and is normalised to
  that. Any other spelling is refused.
- `Width`: the typed suffix (`d32`, `a64`, `q`, `w`, `ud`), read literally
  after the colon.
- `RInstr`: the decoded instruction. `Exec` keeps the execution size, the
  M1-M8 channel offset and the `_NM` flag instead of discarding the mask.
  A nonzero-offset move is kept as `movMasked` rather than being treated as a
  full-register write.
  `lsc_load.ugm` and `lsc_store.ugm` name their payload register without a
  region, so those operands are bare register numbers.
- `decodeReal` / `decodeRealProgram`: the decoder, `Option`-valued. Besides
  arithmetic, loads and stores it reads labels, `mov` with an immediate source,
  the three-operand `or`, predicate logic, both register comparisons, `goto`
  and a predicated `goto` for any predicate number and polarity. `parseWidth`
  accepts IGC's `:d` dword suffix as `d32`.

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

/-- The execution-size and execution-mask control printed on an instruction.
`offset` follows the vISA table: M1 starts at channel 0, M5 at 16, and so on.
`noMask` records the `_NM` spelling. -/
structure Exec where
  size : Nat
  offset : Nat
  noMask : Bool
  deriving Repr, DecidableEq

/-- Numeric execution sizes default to M1, which keeps the existing explicit
instruction lists readable. -/
instance : OfNat Exec n := ⟨n, 0, false⟩

instance : Coe Exec Nat := ⟨Exec.size⟩

/-- An explicit `M1_NM` execution control. -/
def Exec.nm (size : Nat) : Exec := ⟨size, 0, true⟩

/-- Typed suffix on an operand. -/
inductive Width where
  | d32
  | a64
  | q
  | w16
  | ud
  | v
  deriving Repr, DecidableEq

/-- The decoded instruction. Load and store payloads are bare registers, as
IGC prints them. -/
inductive RInstr where
  | mul (exec : Exec) (dst a b : Grf)
  | mov (exec : Exec) (dst src : Grf)
  /-- A masked move: only the instruction's active lanes write. -/
  | movMasked (exec : Exec) (dst src : Grf)
  | add3 (exec : Exec) (dst a b c : Grf)
  | shl (exec : Exec) (dst src : Grf) (amount : Nat)
  | add (exec : Exec) (dst a b : Grf)
  | addImm (exec : Exec) (dst src : Grf) (imm : Nat) (w : Width)
  | load (exec : Exec) (dst : Nat) (w : Width) (addrReg : Nat)
  | store (exec : Exec) (addrReg : Nat) (w : Width) (src : Nat)
  | ret (exec : Exec)
  /-- The `%cr0` prologue, matched exactly. -/
  | prologue
  /-- A label. -/
  | label (name : String)
  /-- `mov dst imm:w`, the loop's zero initialisers. -/
  | movImm (exec : Exec) (dst : Grf) (imm : Nat) (w : Width)
  /-- Three-operand bitwise `or` (`dst = a ||| b`). -/
  | or (exec : Exec) (dst a b : Grf)
  /-- `cmp.lt` into a predicate register. -/
  | cmpLt (exec : Exec) (pred : Nat) (src : Grf) (imm : Nat) (w : Width)
  /-- Register-register `cmp.lt` into a predicate register. -/
  | cmpLtReg (exec : Exec) (pred : Nat) (a b : Grf)
  /-- Register-register `cmp.eq` into a predicate register. -/
  | cmpEqReg (exec : Exec) (pred : Nat) (a b : Grf)
  /-- Predicate `and`: `dst = a && b` per lane. -/
  | predAnd (exec : Exec) (dst a b : Nat)
  /-- Predicate `or`: `dst = a || b` per lane. -/
  | predOr (exec : Exec) (dst a b : Nat)
  /-- An unconditional `goto`. -/
  | goto (exec : Exec) (label : String)
  /-- A predicated `goto`; `negated` records the `(!P1)` spelling. -/
  | gotoIf (exec : Exec) (pred : Nat) (negated : Bool) (label : String)
  /-- A scaled global load `flat(base)[4*index]`: scalar base plus a per-lane
  32-bit index, byte scale four. -/
  | loadScaled (exec : Exec) (dst : Nat) (w : Width) (base idx : Nat)
  /-- A scaled global store `flat(base)[4*index]`. -/
  | storeScaled (exec : Exec) (base idx : Nat) (w : Width) (src : Nat)
  /-- A predicated select `(Pp) sel`: `dst = pred ? a : b` per lane. -/
  | sel (exec : Exec) (pred : Nat) (dst a b : Grf)
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
  | some ['d'] => some .d32
  | some ['d', '3', '2'] => some .d32
  | some ['a', '6', '4'] => some .a64
  | some ['u', 'd'] => some .ud
  | some ['q'] => some .q
  | some ['w'] => some .w16
  | some ['v'] => some .v
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

/-- The channel offset of the vISA execution masks M1 through M8. -/
def execMaskOffset : Nat → Option Nat
  | 1 => some 0
  | 2 => some 4
  | 3 => some 8
  | 4 => some 12
  | 5 => some 16
  | 6 => some 20
  | 7 => some 24
  | 8 => some 28
  | _ => none

/-- The suffix after an `M<n>` mask: either a comma or `_NM,`. -/
def parseMaskSuffix : List Char → Option Bool
  | ',' :: _ => some false
  | '_' :: 'N' :: 'M' :: ',' :: _ => some true
  | _ => none

/-- Execution size and mask, printed as `(M1, 32)`, `(M1_NM, 1)` or
`(M5, 16)`. The size is read from after the comma, so digits in the mask name
do not confuse it. -/
def parseExec (s : String) : Option Exec :=
  let cs := s.toList
  match cs with
  | '(' :: 'M' :: rest =>
      let digits := rest.takeWhile isDigit
      if digits.isEmpty then none
      else
        match parseMaskSuffix (rest.dropWhile isDigit), afterComma cs, cs.getLast? with
        | some noMask, some tail, some ')' =>
            match execMaskOffset (digitsToNat digits) with
            | some offset =>
                let body := dropSpaces tail.dropLast
                if body.isEmpty then none
                else if allDigits body then some ⟨digitsToNat body, offset, noMask⟩ else none
            | none => none
        | _, _, _ => none
  | _ => none

/-- A source GRF operand: `V0045(0,0)<1>` or `V0045(0,0)<1;1,0>`. The
one-field form is the source shorthand `<vstride;1,0>`. -/
def parseGrf (s : String) : Option Grf :=
  match numRuns (operandCore s) with
  | [n, r, c, v] => some ⟨n, r, c, v, 1, 0⟩
  | [n, r, c, v, w, h] => some ⟨n, r, c, v, w, h⟩
  | _ => none

/-- A destination GRF operand. The one-field form is `<hstride>`, not the
source shorthand `<vstride;1,0>`. This distinction matters for strided
destinations such as `V0081(2,0)<2>`. -/
def parseDstGrf (s : String) : Option Grf :=
  match numRuns (operandCore s) with
  | [n, r, c, h] => some ⟨n, r, c, 1, 1, h⟩
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

/-- A scaled memory operand `flat(V0056)[0x4*V0055]:a32u`: base register and
index register. Only the four-byte scale is accepted. -/
def parseScaledMem (s : String) : Option (Nat × Nat) :=
  match numRuns (operandCore s) with
  | [b, 0, 4, i] => some (b, i)
  | _ => none

/-- The predicate of a `(Pp) sel` mnemonic. -/
def parseSelPred (s : String) : Option Nat :=
  match s.toList with
  | '(' :: 'P' :: rest =>
      let digits := rest.takeWhile isDigit
      if digits.isEmpty then none
      else if rest.dropWhile isDigit = [')', ' ', 's', 'e', 'l'] then
        some (digitsToNat digits)
      else none
  | _ => none

/-- A predicate operand `P1`. -/
def parsePred (s : String) : Option Nat :=
  match s.toList with
  | 'P' :: rest =>
      match numRuns (String.ofList rest) with
      | [n] => some n
      | _ => none
  | _ => none

/-- A predicated goto mnemonic, `(!P3) goto` or `(P3) goto`. -/
def parsePredGoto (s : String) : Option (Nat × Bool) :=
  match s.toList with
  | '(' :: '!' :: 'P' :: rest =>
      let digits := rest.takeWhile isDigit
      if digits.isEmpty then none
      else if rest.dropWhile isDigit = [')', ' ', 'g', 'o', 't', 'o'] then
        some (digitsToNat digits, true)
      else none
  | '(' :: 'P' :: rest =>
      let digits := rest.takeWhile isDigit
      if digits.isEmpty then none
      else if rest.dropWhile isDigit = [')', ' ', 'g', 'o', 't', 'o'] then
        some (digitsToNat digits, false)
      else none
  | _ => none

def decodeReal : Stmt → Option RInstr
  | .label name => some (.label name)
  | .instruction op operands =>
      match op, operands with
      | "mul", [e, d, a, b] =>
          match parseExec e, parseDstGrf d, parseGrf a, parseGrf b with
          | some n, some x, some y, some z => some (.mul n x y z)
          | _, _, _, _ => none
      | "mov", [e, d, s] =>
          match parseExec e, parseDstGrf d with
          | some n, some x =>
              match parseGrf s with
              | some y =>
                  if n.noMask || n.offset == 0 then some (.mov n x y)
                  else some (.movMasked n x y)
              | none =>
                  match parseLit s, parseWidth s with
                  | some v, some wd => some (.movImm n x v wd)
                  | _, _ => none
          | _, _ => none
      | "add3", [e, d, a, b, c] =>
          match parseExec e, parseDstGrf d, parseGrf a, parseGrf b, parseGrf c with
          | some n, some w, some x, some y, some z => some (.add3 n w x y z)
          | _, _, _, _, _ => none
      | "shl", [e, d, s, k] =>
          match parseExec e, parseDstGrf d, parseGrf s, parseLit k with
          | some n, some x, some y, some m => some (.shl n x y m)
          | _, _, _, _ => none
      | "add", [e, d, a, b] =>
          match parseExec e, parseDstGrf d, parseGrf a with
          | some n, some x, some y =>
              match parseGrf b with
              | some z => some (.add n x y z)
              | none =>
                  match parseLit b, parseWidth b with
                  | some v, some wd => some (.addImm n x y v wd)
                  | _, _ => none
          | _, _, _ => none
      | "lsc_load.ugm", [e, d, a] =>
          match parseExec e, parsePlainReg d, parseWidth d with
          | some n, some x, some wd =>
              match parseMem a with
              | some y => some (.load n x wd y)
              | none =>
                  match parseScaledMem a with
                  | some (b, i) => some (.loadScaled n x wd b i)
                  | none => none
          | _, _, _ => none
      | "lsc_store.ugm", [e, a, s] =>
          match parseExec e, parsePlainReg s, parseWidth s with
          | some n, some y, some wd =>
              match parseMem a with
              | some x => some (.store n x wd y)
              | none =>
                  match parseScaledMem a with
                  | some (b, i) => some (.storeScaled n b i wd y)
                  | none => none
          | _, _, _ => none
      | "or", ["(M1_NM, 1)", "%cr0(0,0)<1>", "%cr0(0,0)<0;1,0>", "0x400004c0:ud"] =>
          some .prologue
      | "or", [e, d, a, b] =>
          match parseExec e, parseDstGrf d, parseGrf a, parseGrf b with
          | some n, some x, some y, some z => some (.or n x y z)
          | _, _, _, _ =>
              match parseExec e, parsePred d, parsePred a, parsePred b with
              | some n, some x, some y, some z => some (.predOr n x y z)
              | _, _, _, _ => none
      | "and", [e, d, a, b] =>
          match parseExec e, parsePred d, parsePred a, parsePred b with
          | some n, some x, some y, some z => some (.predAnd n x y z)
          | _, _, _, _ => none
      | "cmp.lt", [e, p, a, b] =>
          match parseExec e, parsePred p, parseGrf a, parseLit b, parseWidth b with
          | some n, some q, some x, some v, some wd => some (.cmpLt n q x v wd)
          | _, _, _, _, _ =>
              match parseExec e, parsePred p, parseGrf a, parseGrf b with
              | some n, some q, some x, some y => some (.cmpLtReg n q x y)
              | _, _, _, _ => none
      | "cmp.eq", [e, p, a, b] =>
          match parseExec e, parsePred p, parseGrf a, parseGrf b with
          | some n, some q, some x, some y => some (.cmpEqReg n q x y)
          | _, _, _, _ => none
      | "goto", [e, l] =>
          match parseExec e with
          | some n => some (.goto n l)
          | none => none
      | op, [e, l] =>
          match parseExec e, parsePredGoto op with
          | some n, some (p, negated) => some (.gotoIf n p negated l)
          | _, _ => none
      | op, [e, d, a, b] =>
          match parseSelPred op, parseExec e, parseDstGrf d, parseGrf a, parseGrf b with
          | some p, some n, some x, some y, some z => some (.sel n p x y z)
          | _, _, _, _, _ => none
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
      some (.addImm 32 ⟨55, 0, 0, 1, 1, 1⟩ ⟨54, 0, 0, 1, 1, 0⟩ 1 .w16) := by
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
