-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Fp16Bits

@[expose] public section

/-!
# A value domain with NaN and infinities

Stage 43 decodes the finite fragment and returns `none` for everything else.
This module gives those classes values and proves how they behave in the
accumulation:

- `Fval`: `NaN`, a signed infinity, or a finite `Fixed`.
- `vstep`: NaN absorbs; infinities follow the same-sign/opposite-sign rule;
  finite operands go to the verified fixed-point step.
- `foldVal_fin`: **all-finite operands give exactly `maccDot`** — the value
  domain does not change the numeric results.
- `vstep_ne_fin`, `foldVal_ne_fin`: a non-finite operand never yields a finite
  result, so the finite fragment is closed.

Not modeled: NaN payloads and subnormal values — those are classes here, not
numbers.
-/

namespace IntelGpu

inductive Fval where
  | nan
  | inf (neg : Bool)
  | fin (v : Fixed)
  deriving Repr, DecidableEq

/-- The accumulation step on values. -/
def vstep (stepF : Fixed → Fixed → Fixed → Fixed) (acc x y : Fval) : Fval :=
  match acc, x, y with
  | .nan, _, _ => .nan
  | _, .nan, _ => .nan
  | _, _, .nan => .nan
  | .inf p, .inf r, _ => if p = r then .inf p else .nan
  | .inf p, _, _ => .inf p
  | _, .inf r, _ => .inf r
  | .fin _, .fin _, .inf r => .inf r
  | .fin c, .fin a, .fin b => .fin (stepF c a b)

/-- The same accumulation on bare `Fixed` values. -/
def foldFixed (stepF : Fixed → Fixed → Fixed → Fixed) (a b : Nat → Fixed) (acc : Fixed) :
    Nat → Fixed
  | 0 => acc
  | n + 1 => foldFixed stepF a b (stepF acc (a n) (b n)) n

/-- Value-depth accumulation. -/
def foldVal (stepF : Fixed → Fixed → Fixed → Fixed) (a b : Nat → Fval) (acc : Fval) :
    Nat → Fval
  | 0 => acc
  | n + 1 => foldVal stepF a b (vstep stepF acc (a n) (b n)) n

theorem vstep_fin (stepF : Fixed → Fixed → Fixed → Fixed) (c a b : Fixed) :
    vstep stepF (.fin c) (.fin a) (.fin b) = .fin (stepF c a b) := rfl

theorem vstep_nan_acc (stepF : Fixed → Fixed → Fixed → Fixed) (x y : Fval) :
    vstep stepF .nan x y = .nan := by
  cases x <;> cases y <;> rfl

theorem vstep_ne_fin_acc (stepF : Fixed → Fixed → Fixed → Fixed) (acc x y : Fval)
    (h : ¬ ∃ c, acc = .fin c) (v : Fixed) : vstep stepF acc x y ≠ .fin v := by
  rcases acc with _ | p | c
  · cases x <;> cases y <;> simp [vstep]
  · cases x <;> cases y <;> simp [vstep]
    · split <;> simp
    · split <;> simp
  · exact absurd ⟨c, rfl⟩ h

/-- A non-finite accumulator is absorbing: once it is non-finite it stays
non-finite for every further step. -/
theorem foldVal_ne_fin (stepF : Fixed → Fixed → Fixed → Fixed) (a b : Nat → Fval) :
    ∀ (n : Nat) (acc : Fval), (¬ ∃ c, acc = .fin c) →
      ∀ v, foldVal stepF a b acc n ≠ .fin v := by
  intro n
  induction n with
  | zero => intro acc h v hv; exact absurd ⟨v, hv⟩ h
  | succ n ih =>
      intro acc h v hv
      exact ih (vstep stepF acc (a n) (b n)) (by
        rintro ⟨c, hc⟩
        exact vstep_ne_fin_acc stepF acc (a n) (b n) h c hc) v hv

/-- All-finite operands give exactly the verified machine accumulation. -/
theorem foldVal_fin (stepF : Fixed → Fixed → Fixed → Fixed) (a b : Nat → Fixed)
    (acc : Fixed) :
    ∀ n, foldVal stepF (fun k => .fin (a k)) (fun k => .fin (b k)) (.fin acc) n =
      .fin (foldFixed stepF a b acc n) := by
  intro n
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
      simp only [foldVal, foldFixed, vstep_fin]
      exact ih (stepF acc (a n) (b n))

end IntelGpu
