-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaCmpGate
public import Intel.TlaControlDecode

@[expose] public section

/-!
# Jump predicate evaluation

The decoded jumps carry predicate text such as `(W)`, `(W&f3.1)` or
`(W&~f3.1)`. This module parses that text into a `TlaCond` and evaluates it on
the flag state. The mainloop's exit jump at PC 1401 is `(W&~f3.1)`: it is
taken exactly when `f3.1` is clear, which by `loopCmp_exit_iff` is exactly
when the incremented counter has reached the bound. The back-edge at PC 1404
is unconditional.
-/

namespace IntelGpu

/-- A jump predicate: unconditional, or a flag test with optional negation. -/
inductive TlaCond where
  | always
  | flag (n m : Nat) (neg : Bool)
  deriving Repr, DecidableEq

/-- Parse the predicate text of a jump. -/
def parseTlaCond (s : String) : TlaCond :=
  match splitAtChar '&' s.toList with
  | none => .always
  | some (_, rest) =>
      match rest with
      | '~' :: rest' =>
          match numRuns (String.ofList rest') with
          | [n, m] => .flag n m true
          | _ => .always
      | _ =>
          match numRuns (String.ofList rest) with
          | [n, m] => .flag n m false
          | _ => .always

/-- Evaluate a jump predicate on the flag state. -/
def TlaCond.taken (st : TlaState) : TlaCond → Bool
  | .always => true
  | .flag n m neg => if neg then st.flags n m = 0 else st.flags n m ≠ 0

/-- The mainloop exit jump: `(W&~f3.1) jmpi _0_118`. -/
def exitJmp : TlaJmp := ⟨"(W&~f3.1) jmpi", "_0_118"⟩

/-- The back-edge: `(W) jmpi _0_119`. -/
def backJmp : TlaJmp := ⟨"(W) jmpi", "_0_119"⟩

/-- The early guard jump: `(W&~f0.0) jmpi _0_120`. -/
def earlyJmp : TlaJmp := ⟨"(W&~f0.0) jmpi", "_0_120"⟩

theorem exitJmp_cond : parseTlaCond exitJmp.predicate = .flag 3 1 true := by decide

theorem backJmp_cond : parseTlaCond backJmp.predicate = .always := by decide

theorem earlyJmp_cond : parseTlaCond earlyJmp.predicate = .flag 0 0 true := by decide

theorem exitJmp_taken (st : TlaState) :
    (parseTlaCond exitJmp.predicate).taken st = true ↔ st.flags 3 1 = 0 := by
  rw [exitJmp_cond]
  simp [TlaCond.taken]

theorem backJmp_taken (st : TlaState) :
    (parseTlaCond backJmp.predicate).taken st = true := by
  rw [backJmp_cond]
  rfl

theorem earlyJmp_taken (st : TlaState) :
    (parseTlaCond earlyJmp.predicate).taken st = true ↔ st.flags 0 0 = 0 := by
  rw [earlyJmp_cond]
  simp [TlaCond.taken]

/-- The exit jump after the loop comparison is taken exactly when the
incremented counter has reached the bound. -/
theorem exitJmp_taken_iff (st : TlaState) :
    (parseTlaCond exitJmp.predicate).taken (loopCmp.step st) = true ↔
      ¬ (st.regs 1 11 < st.regs 1 15) := by
  rw [exitJmp_taken, loopCmp_exit_iff]

end IntelGpu
