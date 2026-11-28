-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.RoundingNearest

@[expose] public section

/-!
# Round to nearest, ties to even

Stage 30 rounds to nearest with ties toward zero. IEEE-754 rounds ties to the
even multiple instead, which is what fp16/fp32 hardware does. This module
models that rule and proves the same `q / 2` bound.

- `roundEvenNat q n`: nearest multiple of `q`, ties to the even quotient.
- `roundEven q x`: the signed version.
- `roundEven_bound`: the error is at most `q / 2`.
- `stepEven` / `stepEven_contract` / `evenDot_error`: the stage-27 contract
  and the accumulated bound, now for the hardware tie rule.
-/

namespace IntelGpu

/-- Nearest multiple of `q` to `n`; a tie goes to the multiple with the even
quotient. -/
def roundEvenNat (q n : Nat) : Nat :=
  if q % 2 = 0 ∧ n % q = q / 2 then
    (if (n / q) % 2 = 0 then (n / q) * q else (n / q) * q + q)
  else (n + q / 2) / q * q

theorem roundEvenNat_notie (q n : Nat) (h : ¬ (q % 2 = 0 ∧ n % q = q / 2)) :
    roundEvenNat q n = (n + q / 2) / q * q := by
  unfold roundEvenNat
  split
  · rename_i hpos
    exact absurd hpos h
  · rfl

theorem roundEvenNat_tie (q n : Nat) (h : q % 2 = 0 ∧ n % q = q / 2) :
    roundEvenNat q n =
      (if (n / q) % 2 = 0 then (n / q) * q else (n / q) * q + q) := by
  unfold roundEvenNat
  split
  · rfl
  · rename_i hneg
    exact absurd h hneg

/-- Round to nearest with ties to even, on signed values. -/
def roundEven (q : Nat) (x : Int) : Int :=
  if 0 ≤ x then (roundEvenNat q x.toNat : Int)
  else -(roundEvenNat q (-x).toNat : Int)

theorem roundEven_of_nonneg (q : Nat) {z : Int} (hz : 0 ≤ z) :
    roundEven q z = (roundEvenNat q z.toNat : Int) := by
  unfold roundEven
  split
  · rfl
  · omega

theorem roundEven_of_neg (q : Nat) {z : Int} (hz : ¬ 0 ≤ z) :
    roundEven q z = -(roundEvenNat q (-z).toNat : Int) := by
  unfold roundEven
  split
  · omega
  · rfl

theorem roundEven_bound_nat (q : Nat) (hq : 0 < q) (n : Nat) :
    (roundEven q ((n : Int)) - ((n : Int))).natAbs ≤ q / 2 := by
  have h0 : (0 : Int) ≤ ((n : Int)) := Int.natCast_nonneg n
  have htoNat : (((n : Int)).toNat) = n := rfl
  by_cases h : q % 2 = 0 ∧ n % q = q / 2
  · have hdec : n / q * q + q / 2 = n := by
      have hmod := Nat.div_add_mod n q
      rw [Nat.mul_comm] at hmod
      have := h.2
      omega
    have hcases : roundEvenNat q n = n - q / 2 ∨ roundEvenNat q n = n + q / 2 := by
      rw [roundEvenNat_tie q n h]
      split
      · left; omega
      · right; omega
    rw [roundEven_of_nonneg q h0, htoNat]
    rcases hcases with hv | hv
    · rw [hv]
      have hcast : ((n - q / 2 : Nat) : Int) = (n : Int) - ((q / 2 : Nat) : Int) :=
        Int.ofNat_sub (by omega)
      rw [hcast]
      have hzero : (n : Int) - ((q / 2 : Nat) : Int) - (n : Int) =
          -((q / 2 : Nat) : Int) := by omega
      rw [hzero, Int.natAbs_neg]
      exact Nat.le_refl _
    · rw [hv]
      have hcast : ((n + q / 2 : Nat) : Int) = (n : Int) + ((q / 2 : Nat) : Int) :=
        Int.natCast_add n (q / 2)
      rw [hcast]
      have hzero : (n : Int) + ((q / 2 : Nat) : Int) - (n : Int) =
          ((q / 2 : Nat) : Int) := by omega
      rw [hzero]
      exact Nat.le_refl _
  · have hround : roundEven q ((n : Int)) = roundQ q ((n : Int)) := by
      rw [roundEven_of_nonneg q h0, htoNat, roundEvenNat_notie q n h]
      rw [roundQ_of_nonneg q h0, htoNat]
    rw [hround]
    exact roundQ_bound_nat q hq n

theorem roundEven_bound (q : Nat) (hq : 0 < q) (x : Int) :
    (roundEven q x - x).natAbs ≤ q / 2 := by
  by_cases hx : 0 ≤ x
  · have hx' : ((x.toNat : Int)) = x := Int.toNat_of_nonneg hx
    have hnat := roundEven_bound_nat q hq x.toNat
    rwa [hx'] at hnat
  · have h0 : 0 ≤ -x := by omega
    have hx' : (((-x).toNat : Int)) = -x := Int.toNat_of_nonneg h0
    have hneg' : roundEven q x = -roundEven q (-x) := by
      rw [roundEven_of_neg q hx, roundEven_of_nonneg q h0]
    have hnat := roundEven_bound_nat q hq (-x).toNat
    rw [hx'] at hnat
    have hdiff : -roundEven q (-x) - x = -(roundEven q (-x) - (-x)) := by omega
    rw [hneg', hdiff, Int.natAbs_neg]
    exact hnat

/-- A machine multiply-add that rounds to nearest, ties to even. -/
def stepEven (q : Nat) (c x y : Int) : Int := roundEven q (c + x * y)

theorem stepEven_contract (q : Nat) (hq : 0 < q) (c x y : Int) :
    (stepEven q c x y - (c + x * y)).natAbs ≤ q / 2 :=
  roundEven_bound q hq (c + x * y)

/-- Accumulating with ties-to-even rounding stays within `n * (q / 2)`. -/
theorem evenDot_error (q : Nat) (hq : 0 < q) (n : Nat) (acc : Int) (a b : Nat → Int) :
    (maccDot (stepEven q) a b acc n - accDot a b acc n).natAbs ≤ n * (q / 2) :=
  maccDot_error (stepEven q) (q / 2) (stepEven_contract q hq) n acc a b

/-- The tie rule is visible: with quantum `8`, `35` ties between `32` and `40`
and goes to the even quotient. -/
example : roundEven (8 : Nat) (35 : Int) = 32 := by decide
example : roundEven (8 : Nat) (45 : Int) = 48 := by decide

end IntelGpu
