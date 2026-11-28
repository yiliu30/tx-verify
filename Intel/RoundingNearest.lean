-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Rounding

@[expose] public section

/-!
# Round to nearest

Stage 29 showed that truncating to the accumulator quantum `q` loses at most
`q - 1`. Real hardware rounds to nearest instead, which halves that.

- `roundQ q x`: nearest multiple of `q`, ties toward zero.
- `roundQ_bound`: the error is at most `q / 2`.
- `stepRound` / `stepRound_contract`: the machine multiply-add meets the
  stage-27 contract with `eps = q / 2`.
- `roundDot_error`: `n` steps stay within `n * (q / 2)` of the exact dot.
-/

namespace IntelGpu

/-- Round `x` to the nearest multiple of `q`, ties toward zero. -/
def roundQ (q : Nat) (x : Int) : Int :=
  if 0 ≤ x then (((x.toNat + q / 2) / q) * q : Nat)
  else -(((((-x).toNat + q / 2) / q) * q : Nat))

theorem roundQ_of_nonneg (q : Nat) {z : Int} (hz : 0 ≤ z) :
    roundQ q z = (((z.toNat + q / 2) / q) * q : Nat) := by
  unfold roundQ
  split
  · rfl
  · omega

theorem roundQ_of_neg (q : Nat) {z : Int} (hz : ¬ 0 ≤ z) :
    roundQ q z = -(((((-z).toNat + q / 2) / q) * q : Nat)) := by
  unfold roundQ
  split
  · omega
  · rfl

theorem roundQ_bound_nat (q : Nat) (hq : 0 < q) (n : Nat) :
    (roundQ q ((n : Int)) - ((n : Int))).natAbs ≤ q / 2 := by
  have h0 : (0 : Int) ≤ ((n : Int)) := Int.natCast_nonneg n
  have htoNat : (((n : Int)).toNat) = n := rfl
  rw [roundQ_of_nonneg q h0, htoNat]
  obtain ⟨qq, hqq⟩ : ∃ qq : Nat, qq = (n + q / 2) / q := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : Nat, r = (n + q / 2) % q := ⟨_, rfl⟩
  have hdiv : qq * q + r = n + q / 2 := by
    rw [hqq, hr, Nat.mul_comm]
    exact Nat.div_add_mod (n + q / 2) q
  have hr_lt : r < q := by rw [hr]; exact Nat.mod_lt _ hq
  have hcast : ((qq * q : Nat) : Int) + ((r : Nat) : Int)
      = (n : Int) + ((q / 2 : Nat) : Int) := by
    rw [← Int.natCast_add, hdiv, Int.natCast_add]
  have hdiff : ((qq * q : Nat) : Int) - ((n : Int))
      = ((q / 2 : Nat) : Int) - ((r : Nat) : Int) := by
    omega
  rw [← hqq, hdiff]
  apply natAbs_le_of_bounds
  · omega
  · omega

theorem roundQ_bound (q : Nat) (hq : 0 < q) (x : Int) :
    (roundQ q x - x).natAbs ≤ q / 2 := by
  by_cases hx : 0 ≤ x
  · have hx' : ((x.toNat : Int)) = x := Int.toNat_of_nonneg hx
    have hnat := roundQ_bound_nat q hq x.toNat
    rwa [hx'] at hnat
  · have h0 : 0 ≤ -x := by omega
    have hx' : (((-x).toNat : Int)) = -x := Int.toNat_of_nonneg h0
    have hneg' : roundQ q x = -roundQ q (-x) := by
      rw [roundQ_of_neg q hx, roundQ_of_nonneg q h0]
    have hnat := roundQ_bound_nat q hq (-x).toNat
    rw [hx'] at hnat
    have hdiff : -roundQ q (-x) - x = -(roundQ q (-x) - (-x)) := by omega
    rw [hneg', hdiff, Int.natAbs_neg]
    exact hnat

/-- With quantum `1` nearest rounding changes nothing. -/
theorem roundQ_one (z : Int) : roundQ 1 z = z := by
  by_cases hz : 0 ≤ z
  · rw [roundQ_of_nonneg 1 hz]
    rw [show (1 : Nat) / 2 = 0 from rfl, Nat.add_zero, Nat.div_one, Nat.mul_one]
    exact Int.toNat_of_nonneg hz
  · rw [roundQ_of_neg 1 hz]
    rw [show (1 : Nat) / 2 = 0 from rfl, Nat.add_zero, Nat.div_one, Nat.mul_one]
    have h : (((-z).toNat : Int)) = -z := Int.toNat_of_nonneg (by omega)
    rw [h]
    omega

/-- A machine multiply-add that rounds its exact result to nearest. -/
def stepRound (q : Nat) (c x y : Int) : Int := roundQ q (c + x * y)

theorem stepRound_contract (q : Nat) (hq : 0 < q) (c x y : Int) :
    (stepRound q c x y - (c + x * y)).natAbs ≤ q / 2 :=
  roundQ_bound q hq (c + x * y)

/-- Accumulating with nearest rounding stays within `n * (q / 2)` of the exact
dot — half the truncation bound of stage 29. -/
theorem roundDot_error (q : Nat) (hq : 0 < q) (n : Nat) (acc : Int) (a b : Nat → Int) :
    (maccDot (stepRound q) a b acc n - accDot a b acc n).natAbs ≤ n * (q / 2) :=
  maccDot_error (stepRound q) (q / 2) (stepRound_contract q hq) n acc a b

/-- With quantum `1` the machine accumulation is exact. -/
theorem roundDot_exact (n : Nat) (acc : Int) (a b : Nat → Int) :
    maccDot (stepRound 1) a b acc n = accDot a b acc n :=
  maccDot_zero_error (stepRound 1) (by
    intro c x y
    simp [stepRound, roundQ_one]) n acc a b

end IntelGpu
