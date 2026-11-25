-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.RoundingEven

@[expose] public section

/-!
# From word arithmetic to the numeric bound

Stages 27-31 bound the error of an accumulation over `Int`. The machines in
this development compute over `Word`. This module connects them.

`wpDot` is the same depth-ordered accumulation as `maccDot`, but over words.
The bridge has two pieces:

- `wpDot_toInt`: if the word step implements ties-to-even rounding on the
  signed reading of the accumulator, then the integer reading of the word
  accumulation *is* the machine accumulation of stage 31. This is an
  equality, not a bound.
- `wpDot_error`: consequently the word accumulation is within
  `n * (q / 2)` of the exact dot of the signed readings.

The only hypothesis is `hstep`: the hardware multiply-add implements
nearest-ties-to-even rounding to the accumulator quantum, read through `toInt`.
That is the fp32 accumulator contract. It is stated, not derived — deriving it
needs bit-level IEEE-754 semantics.
-/

namespace IntelGpu

/-- Depth-ordered accumulation over words, with an abstract machine step. -/
def wpDot (step : Word → Word → Word → Word) (a b : Nat → Word) (acc : Word) :
    Nat → Word
  | 0 => acc
  | n + 1 => wpDot step a b (step acc (a n) (b n)) n

/-- The integer reading of a word accumulation is the stage-31 machine
accumulation, provided the word step rounds as `stepEven` does. -/
theorem wpDot_toInt (step : Word → Word → Word → Word) (q : Nat)
    (hstep : ∀ c x y : Word,
      toInt (step c x y) = stepEven q (toInt c) (toInt x) (toInt y))
    (n : Nat) (acc : Word) (a b : Nat → Word) :
    toInt (wpDot step a b acc n) =
      maccDot (stepEven q) (fun k => toInt (a k)) (fun k => toInt (b k))
        (toInt acc) n := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
      rw [wpDot, maccDot, ih (step acc (a n) (b n)), hstep]

/-- Error bound for word accumulation: within `n * (q / 2)` of the exact dot
of the signed readings. -/
theorem wpDot_error (step : Word → Word → Word → Word) (q : Nat) (hq : 0 < q)
    (hstep : ∀ c x y : Word,
      toInt (step c x y) = stepEven q (toInt c) (toInt x) (toInt y))
    (n : Nat) (acc : Word) (a b : Nat → Word) :
    (toInt (wpDot step a b acc n)
        - accDot (fun k => toInt (a k)) (fun k => toInt (b k)) (toInt acc) n).natAbs
      ≤ n * (q / 2) := by
  rw [wpDot_toInt step q hstep]
  exact evenDot_error q hq n (toInt acc) (fun k => toInt (a k)) (fun k => toInt (b k))

/-- The DPAS-shaped chain: `T` slabs of `d` depth each, error at most
`T * d * (q / 2)`. -/
theorem dpasWord_error (step : Word → Word → Word → Word) (q : Nat) (hq : 0 < q)
    (hstep : ∀ c x y : Word,
      toInt (step c x y) = stepEven q (toInt c) (toInt x) (toInt y))
    (T d : Nat) (acc : Word) (a b : Nat → Word) :
    (toInt (wpDot step a b acc (T * d))
        - accDot (fun k => toInt (a k)) (fun k => toInt (b k)) (toInt acc) (T * d)).natAbs
      ≤ T * d * (q / 2) :=
  wpDot_error step q hq hstep (T * d) acc a b

/-- Sanity: the signed reading agrees with the word value on small positives. -/
example : toInt (5 : Word) = 5 := by decide
example : toInt (0 : Word) = 0 := by decide

end IntelGpu
