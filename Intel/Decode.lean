-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Asm
public import Intel.Syntax

@[expose] public section

/-!
# IGC operand decoding

Decodes the raw stage-4 syntax into typed instructions for the GEMM loop
subset. Register names such as `r22:2` and `r14.0` decode to their numeric
index; address operands such as `[r18:4]` decode to the base register.
-/

namespace IntelGpu

inductive IInstr where
  | label (name : String)
  | load32 (dst addrReg : Nat)
  | add (dst src1 src2 : Nat)
  | mul (dst src1 src2 : Nat)
  | addImm (dst src : Nat) (imm : Word)
  | cmpLt (dst src : Nat) (rhs : Word)
  | jmpi (label : String)
  | jmpiIf (pred : Nat) (label : String)
  deriving Repr, Inhabited

def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def digitVal (c : Char) : Nat := c.toNat - '0'.toNat

def digitsToNat : List Char → Nat
  | [] => 0
  | c :: cs => digitVal c * 10 ^ cs.length + digitsToNat cs

/-- First decimal run in a register spelling: `r22:2`, `r14.0`, `[r18:4]`. -/
def parseReg (s : String) : Option Nat :=
  let digits := (s.toList.dropWhile (fun c => !isDigit c)).takeWhile isDigit
  if digits.isEmpty then none else some (digitsToNat digits)

def parseAddr (s : String) : Option Nat := parseReg s

def parseImm (s : String) : Option Word :=
  let digits := s.toList.takeWhile isDigit
  if digits.isEmpty then none else some (BitVec.ofNat 32 (digitsToNat digits))

def isRegSpelling (s : String) : Bool :=
  match s.toList with
  | 'r' :: _ => true
  | '[' :: 'r' :: _ => true
  | _ => false

def decodeInstr : Stmt → Option IInstr
  | .label name => some (IInstr.label name)
  | .instruction op operands =>
      match op, operands with
      | "load.ugm.d32.a64", [dst, addr] =>
          match parseReg dst, parseAddr addr with
          | some d, some a => some (IInstr.load32 d a)
          | _, _ => none
      | "mul", [dst, a, b] =>
          match parseReg dst, parseReg a, parseReg b with
          | some d, some x, some y => some (IInstr.mul d x y)
          | _, _, _ => none
      | "add", [dst, a, b] =>
          if isRegSpelling b then
            match parseReg dst, parseReg a, parseReg b with
            | some d, some x, some y => some (IInstr.add d x y)
            | _, _, _ => none
          else
            match parseReg dst, parseReg a, parseImm b with
            | some d, some x, some v => some (IInstr.addImm d x v)
            | _, _, _ => none
      | "cmp.lt", [dst, src, rhs] =>
          match parseReg dst, parseReg src, parseImm rhs with
          | some d, some x, some v => some (IInstr.cmpLt d x v)
          | _, _, _ => none
      | "jmpi", [label] => some (IInstr.jmpi label)
      | "jmpi.cond", [pred, label] =>
          match parseReg pred with
          | some p => some (IInstr.jmpiIf p label)
          | none => none
      | _, _ => none

def decodeStmts : List Stmt → Option (List IInstr)
  | [] => some []
  | stmt :: rest =>
      match decodeInstr stmt, decodeStmts rest with
      | some i, some is => some (i :: is)
      | _, _ => none

def decodeProgram (p : Program) : Option (List IInstr) :=
  decodeStmts p.statements

end IntelGpu
