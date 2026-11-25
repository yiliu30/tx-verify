-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.RoundingEven

@[expose] public section

/-!
# Exactness on a shared quantization grid

The numeric layer bounds the error of a rounded accumulation. This module
gives the case where there is no error at all: if the operands and the
accumulator all sit on the same quantum grid — the usual "shared exponent
window" situation for fp16 inputs with an fp32 accumulator — then every
product and every partial sum is exactly representable, so rounding is the
identity.

That connects the numeric layer back to the exact-integer theorems: on the
grid, the machine accumulation equals `accDot`, so the results of stages 1-28
apply verbatim.

- `roundEvenNat_mul`: rounding a multiple of `q` changes nothing.
- `roundEven_fixed`: the signed version, for nonnegative multiples.
- `stepEven_grid`: a multiply-add of grid values is exact.
- `evenDot_exact_on_grid`: so is an `n`-deep accumulation.
-/

namespace IntelGpu

theorem roundEvenNat_mul (q k : Nat) (hq : 0 < q) : roundEvenNat q (k * q) = k * q := by
  by_cases h : q % 2 = 0 ∧ (k * q) % q = q / 2
  · have hmod : (k * q) % q = 0 := Nat.mul_mod_left k q
    omega
  · rw [roundEvenNat_notie q (k * q) h]
    have hlt : q / 2 < q := by
      have := Nat.div_lt_self hq (by decide : 1 < 2)
      exact this
    have hdiv : (k * q + q / 2) / q = k := by
      have hmul : k * q + q / 2 = q * k + q / 2 := by rw [Nat.mul_comm]
      rw [hmul, Nat.mul_add_div hq, Nat.div_eq_of_lt hlt, Nat.add_zero]
    rw [hdiv]

theorem roundEven_fixed (q k : Nat) (hq : 0 < q) :
    roundEven q ((k : Int) * (q : Int)) = (k : Int) * (q : Int) := by
  have hcast : (k : Int) * (q : Int) = ((k * q : Nat) : Int) := Int.natCast_mul k q
  rw [hcast]
  have h0 : (0 : Int) ≤ ((k * q : Nat) : Int) := Int.natCast_nonneg _
  have htoNat : ((((k * q : Nat) : Int)).toNat) = k * q := rfl
  rw [roundEven_of_nonneg q h0, htoNat, roundEvenNat_mul q k hq]

/-- A multiply-add of grid values is exact: the product is a multiple of `q`
and so is the sum. -/
theorem stepEven_grid (q : Nat) (hq : 0 < q) (ca a b : Nat) :
    stepEven q ((ca : Int) * (q : Int)) ((a : Int) * (q : Int)) ((b : Int) * (q : Int)) =
      (ca : Int) * (q : Int) + ((a : Int) * (q : Int)) * ((b : Int) * (q : Int)) := by
  unfold stepEven
  have hgrid : (ca : Int) * (q : Int) + ((a : Int) * (q : Int)) * ((b : Int) * (q : Int))
      = ((ca + a * b * q : Nat) : Int) * (q : Int) := by
    simp only [Int.natCast_add, Int.natCast_mul]
    rw [Int.add_mul]
    ac_rfl
  rw [hgrid]
  exact roundEven_fixed q (ca + a * b * q) hq

/-- On the grid, an `n`-deep accumulation is exact: the machine result equals
the exact dot of the same values. -/
theorem evenDot_exact_on_grid (q : Nat) (hq : 0 < q) (n : Nat) (ca : Nat)
    (a b : Nat → Nat) :
    maccDot (stepEven q) (fun k => (a k : Int) * (q : Int)) (fun k => (b k : Int) * (q : Int))
        ((ca : Int) * (q : Int)) n
      = accDot (fun k => (a k : Int) * (q : Int)) (fun k => (b k : Int) * (q : Int))
        ((ca : Int) * (q : Int)) n := by
  induction n generalizing ca with
  | zero => rfl
  | succ n ih =>
      rw [maccDot, accDot]
      congr 1
      rw [stepEven_grid q hq ca (a n) (b n)]
      have hgrid : (ca : Int) * (q : Int) + ((a n : Int) * (q : Int)) * ((b n : Int) * (q : Int))
          = ((ca + a n * b n * q : Nat) : Int) * (q : Int) := by
        simp only [Int.natCast_add, Int.natCast_mul]
        rw [Int.add_mul]
        ac_rfl
      rw [hgrid]
      exact ih (ca + a n * b n * q)

end IntelGpu
