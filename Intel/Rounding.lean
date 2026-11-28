-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Numeric

@[expose] public section

/-!
# A concrete rounding and its contract

Stage 27 states the per-step rounding contract as a hypothesis. This module
supplies a concrete rounding and *derives* that contract from it, so the only
remaining assumption is "the hardware truncates to the accumulator quantum".

- `truncQ q x`: `x` truncated toward zero to a multiple of `q`.
- `truncQ_bound`: the error is strictly below `q`.
- `stepTrunc`: a machine multiply-add that truncates its exact result.
- `truncDot_error`: the accumulated error is at most `n * (q - 1)`.
- `truncDot_exact`: with `q = 1` truncation loses nothing and the machine
  result is exact.
-/

namespace IntelGpu

/-- `z.natAbs ≤ b` from two-sided bounds. -/
theorem natAbs_le_of_bounds {z : Int} {b : Nat} (h1 : -((b : Int)) ≤ z)
    (h2 : z ≤ (b : Int)) : z.natAbs ≤ b := by
  rcases Int.natAbs_eq z with h | h
  · have h2' : ((z.natAbs : Int)) ≤ (b : Int) := by rw [← h]; exact h2
    exact Int.ofNat_le.mp h2'
  · have h1' : -((b : Int)) ≤ -((z.natAbs : Int)) := by rw [← h]; exact h1
    exact Int.ofNat_le.mp (Int.neg_le_neg_iff.mp h1')

/-- Truncate `x` toward zero to a multiple of `q`. -/
def truncQ (q : Nat) (x : Int) : Int :=
  if 0 ≤ x then ((x.toNat / q) * q : Nat) else -(((-x).toNat / q) * q : Nat)

theorem truncQ_of_nonneg (q : Nat) {z : Int} (hz : 0 ≤ z) :
    truncQ q z = (((z.toNat / q) * q : Nat) : Int) := by
  simp [truncQ, hz]

theorem truncQ_bound_nat (q : Nat) (hq : 0 < q) (n : Nat) :
    (truncQ q ((n : Int)) - ((n : Int))).natAbs < q := by
  have h0 : (0 : Int) ≤ ((n : Int)) := Int.natCast_nonneg n
  rw [truncQ_of_nonneg q h0]
  have htoNat : (((n : Int)).toNat) = n := rfl
  rw [htoNat]
  have htle : (n / q) * q ≤ n := by
    have h := Nat.div_mul_le_self n q
    simpa [Nat.mul_comm] using h
  have hsub : ((n - (n / q) * q : Nat) : Int) = (n : Int) - (((n / q) * q : Nat) : Int) :=
    Int.ofNat_sub htle
  have hz : (((n / q) * q : Nat) : Int) - (n : Int) =
      -(((n - (n / q) * q : Nat)) : Int) := by
    omega
  rw [hz, Int.natAbs_neg]
  have hmod : n - (n / q) * q = n % q := by
    have h := Nat.div_add_mod n q
    rw [Nat.mul_comm] at h
    omega
  rw [hmod]
  exact Nat.mod_lt _ hq

theorem truncQ_bound (q : Nat) (hq : 0 < q) (x : Int) :
    (truncQ q x - x).natAbs < q := by
  by_cases hx : 0 ≤ x
  · have hx' : ((x.toNat : Int)) = x := Int.toNat_of_nonneg hx
    have hnat := truncQ_bound_nat q hq x.toNat
    rwa [hx'] at hnat
  · have h0 : 0 ≤ -x := by omega
    have hx' : (((-x).toNat : Int)) = -x := Int.toNat_of_nonneg h0
    have hneg' : truncQ q x = -truncQ q (-x) := by
      have h1 : truncQ q x = -(((((-x).toNat / q) * q : Nat)) : Int) := by
        simp [truncQ, hx]
      have h2 : truncQ q (-x) = ((((-x).toNat / q) * q : Nat) : Int) :=
        truncQ_of_nonneg q h0
      rw [h1, h2]
    have hnat := truncQ_bound_nat q hq (-x).toNat
    rw [hx'] at hnat
    have hdiff : -truncQ q (-x) - x = -(truncQ q (-x) - (-x)) := by omega
    rw [hneg', hdiff, Int.natAbs_neg]
    exact hnat

/-- With quantum `1` truncation changes nothing. -/
theorem truncQ_one (z : Int) : truncQ 1 z = z := by
  by_cases hz : 0 ≤ z
  · have hval : truncQ 1 z = (((z.toNat / 1) * 1 : Nat) : Int) := by
      simp [truncQ, hz]
    rw [hval, Nat.div_one, Nat.mul_one]
    exact Int.toNat_of_nonneg hz
  · have hval : truncQ 1 z = -(((((-z).toNat / 1) * 1 : Nat)) : Int) := by
      simp [truncQ, hz]
    rw [hval, Nat.div_one, Nat.mul_one]
    have h : (((-z).toNat : Int)) = -z :=
      Int.toNat_of_nonneg (by omega)
    rw [h]
    omega

/-- A machine multiply-add that truncates its exact result to the accumulator
quantum. -/
def stepTrunc (q : Nat) (c x y : Int) : Int := truncQ q (c + x * y)

/-- The truncating step meets the stage-27 contract with `eps = q - 1`. -/
theorem stepTrunc_contract (q : Nat) (hq : 0 < q) (c x y : Int) :
    (stepTrunc q c x y - (c + x * y)).natAbs ≤ q - 1 := by
  have h := truncQ_bound q hq (c + x * y)
  simp only [stepTrunc]
  omega

/-- Accumulating with the truncating step stays within `n * (q - 1)` of the
exact dot. -/
theorem truncDot_error (q : Nat) (hq : 0 < q) (n : Nat) (acc : Int) (a b : Nat → Int) :
    (maccDot (stepTrunc q) a b acc n - accDot a b acc n).natAbs ≤ n * (q - 1) :=
  maccDot_error (stepTrunc q) (q - 1) (stepTrunc_contract q hq) n acc a b

/-- With quantum `1` truncation loses nothing: the machine accumulation is
exact. -/
theorem truncDot_exact (n : Nat) (acc : Int) (a b : Nat → Int) :
    maccDot (stepTrunc 1) a b acc n = accDot a b acc n :=
  maccDot_zero_error (stepTrunc 1) (by
    intro c x y
    simp [stepTrunc, truncQ_one]) n acc a b

end IntelGpu
