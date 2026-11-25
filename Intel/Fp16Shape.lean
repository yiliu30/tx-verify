-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Exactness

@[expose] public section

/-!
# fp16-shaped values and the shared grid

Stage 34 proves that values on a common quantum grid accumulate exactly, but it
takes the grid as a hypothesis. This module supplies the hypothesis from an
fp16-shaped representation.

An fp16 value is `sign * mantissa * 2 ^ exponent`, with an 11-bit significand
and a biased exponent. When the exponent is nonnegative the value is an
integer, and when every operand's exponent is at least `e0` the value is a
multiple of `2 ^ e0` — exactly stage 34's grid, with `q = 2 ^ e0`.

So: fp16 operands whose exponents share a floor `e0`, accumulated on the same
grid, compute the exact integer dot product with no rounding at all.

Out of scope here: negative exponents (subnormals and fractional values),
NaN/Inf, and exponent overflow. Those need a real IEEE-754 value semantics.
-/

namespace IntelGpu

/-- An fp16-shaped value: sign, 11-bit significand, unbiased exponent. -/
structure Fixed where
  sign : Bool
  mant : Nat
  exp : Nat
  deriving Repr

/-- Magnitude of the value when the exponent is nonnegative. -/
def Fixed.mag (v : Fixed) : Nat := v.mant * 2 ^ v.exp

/-- A value whose exponent is at least `e0` is an explicit multiple of
`2 ^ e0`, so it sits on the shared grid. -/
theorem Fixed.mag_eq (v : Fixed) (e0 : Nat) (h : e0 ≤ v.exp) :
    v.mag = v.mant * 2 ^ (v.exp - e0) * 2 ^ e0 := by
  unfold Fixed.mag
  rw [Nat.mul_assoc, ← Nat.pow_add]
  congr 2
  omega

/-- The same fact in existential form. -/
theorem Fixed.mag_grid (v : Fixed) (e0 : Nat) (h : e0 ≤ v.exp) :
    ∃ k, v.mag = k * 2 ^ e0 :=
  ⟨_, Fixed.mag_eq v e0 h⟩

/-- The main statement: if every value sits on the `2 ^ e0` grid, the rounded
accumulation is exact. The multipliers `c0`, `ca`, `cb` witness the grid. -/
theorem fp16_grid_exact (e0 : Nat) (n : Nat) (c0 : Nat) (ca cb : Nat → Nat)
    (acc : Fixed) (a b : Nat → Fixed)
    (hacc : acc.mag = c0 * 2 ^ e0)
    (ha : ∀ k, (a k).mag = ca k * 2 ^ e0)
    (hb : ∀ k, (b k).mag = cb k * 2 ^ e0) :
    maccDot (stepEven (2 ^ e0))
        (fun k => ((a k).mag : Int)) (fun k => ((b k).mag : Int)) ((acc.mag : Int)) n
      = accDot (fun k => ((a k).mag : Int)) (fun k => ((b k).mag : Int))
          ((acc.mag : Int)) n := by
  have hq : 0 < 2 ^ e0 := Nat.two_pow_pos e0
  simp only [ha, hb, hacc, Int.natCast_mul]
  exact evenDot_exact_on_grid (2 ^ e0) hq n c0 ca cb

/-- The same, with the grid witnesses derived from the exponent floor: fp16
operands whose exponents are all at least `e0`, accumulated on the same grid,
compute the exact integer dot product. -/
theorem fp16_grid_exact_of_exp (e0 : Nat) (n : Nat) (acc : Fixed) (a b : Nat → Fixed)
    (hacc : e0 ≤ acc.exp) (ha : ∀ k, e0 ≤ (a k).exp) (hb : ∀ k, e0 ≤ (b k).exp) :
    maccDot (stepEven (2 ^ e0))
        (fun k => ((a k).mag : Int)) (fun k => ((b k).mag : Int)) ((acc.mag : Int)) n
      = accDot (fun k => ((a k).mag : Int)) (fun k => ((b k).mag : Int))
          ((acc.mag : Int)) n :=
  fp16_grid_exact e0 n
    (acc.mant * 2 ^ (acc.exp - e0))
    (fun k => (a k).mant * 2 ^ ((a k).exp - e0))
    (fun k => (b k).mant * 2 ^ ((b k).exp - e0))
    acc a b
    (Fixed.mag_eq acc e0 hacc)
    (fun k => Fixed.mag_eq (a k) e0 (ha k))
    (fun k => Fixed.mag_eq (b k) e0 (hb k))

/-- Sanity: a small fp16-shaped value lands on its grid. -/
example : (Fixed.mag { sign := false, mant := 3, exp := 2 }) = 12 := by decide
example : ∃ k, (Fixed.mag { sign := false, mant := 5, exp := 3 }) = k * 2 ^ 1 :=
  Fixed.mag_grid _ 1 (by decide)

end IntelGpu
