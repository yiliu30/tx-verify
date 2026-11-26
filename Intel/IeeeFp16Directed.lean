-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.IeeeFp16Special

@[expose] public section

/-!
# Directed rounding for fp16 addition

Stages 149 and 156 prove an exact-grid fp16 addition and a total value-level
model `addFull` that rounds ties to even. That leaves the directed IEEE modes
unmodelled. This module adds them on the same `2 ^ -24` grid as
`Intel.IeeeFp16Special`: every finite operand and every exact sum is an integer
in units of `2 ^ -24`, and the result is rounded once to the destination
binade.

- `roundDown` / `roundUp` / `roundTowardZero`: directed rounding of a signed
  integer to a multiple of the destination quantum.
- `roundScaledMode`: the analogue of `roundScaled` that uses a directed mode.
- `addDirected`: the analogue of `addFull`; the special-value rules are
  unchanged, only the final rounding differs.
- `addDirected_fin_subnormal_eq_addFull`: on the subnormal/crossing class the
  two subnormal operands add exactly, so all four rounding rules agree.
- `roundScaledMode_binade2`: in the second normal binade the quantum is two,
  and the exact tie cases split the modes.
- the overflow table: toward zero always saturates at the largest finite
  magnitude, while overflow to infinity happens exactly when the direction
  points away from zero and the magnitude exceeds `65504`.

## Proved class

Every theorem is about the `2 ^ -24` scaled integers of
`Intel.IeeeFp16Special`, so finite operands may be normal or subnormal. The
addition model is proved for:

- the basic directed-rounding bounds and fixed points on any quantum;
- agreement with `roundEven` on the same grid: the ties-to-even result always
  lies between the two directed results;
- subnormal addition: two operands of magnitude at most `1023` units add
  exactly under every mode, including the crossing into the first normal
  binade;
- the binade-2 tie cases where down, up and even differ, at the bit level;
- overflow: overflow to infinity happens exactly when the direction points
  away from zero and the magnitude exceeds `65504 * 2 ^ 24`; the saturating
  directions stay at `65504 * 2 ^ 24`, including at and above `2 ^ 40`, where
  every mode takes its overflow branch.  A worked example shows that
  `65504 + 1` already overflows upward.

## Outside the proved class

The general `roundScaledMode` implementation is not proved correct for every
binade and every operand pair; only the subnormal/crossing cases, the tie
cases, the rounding laws and the overflow thresholds are proved. There are no
exception flags (inexact, underflow, overflow, invalid), no tininess detection
and no fused multiply-add. NaN payload handling is inherited unchanged from
`addFull`: the left operand wins, its low nine payload bits are preserved, the
quiet bit is forced and its sign is kept.
-/

namespace IntelGpu

/-! ## Directed rounding on the scaled integer grid -/

/-- The three IEEE directed rounding directions. -/
inductive RMode where
  | towardZero
  | up
  | down
  deriving Repr, DecidableEq

/-- Floor a magnitude to a multiple of `q`. -/
def roundDownNat (q n : Nat) : Nat := n / q * q

/-- Ceil a magnitude to a multiple of `q`. -/
def roundUpNat (q n : Nat) : Nat := n / q * q + if n % q = 0 then 0 else q

/-- Truncate a magnitude to a multiple of `q`. -/
def roundTowardZeroNat (q n : Nat) : Nat := n / q * q

/-- Round a signed integer toward `-inf` to a multiple of `q`. -/
def roundDown (q : Nat) (x : Int) : Int :=
  if 0 ≤ x then (roundDownNat q x.toNat : Int)
  else -((roundUpNat q (-x).toNat : Int))

/-- Round a signed integer toward `+inf` to a multiple of `q`. -/
def roundUp (q : Nat) (x : Int) : Int :=
  if 0 ≤ x then (roundUpNat q x.toNat : Int)
  else -((roundDownNat q (-x).toNat : Int))

/-- Round a signed integer toward zero to a multiple of `q`. -/
def roundTowardZero (q : Nat) (x : Int) : Int :=
  if 0 ≤ x then (roundTowardZeroNat q x.toNat : Int)
  else -((roundDownNat q (-x).toNat : Int))

/-- Dispatch the rounding rule on the mode. -/
def roundMode : RMode → Nat → Int → Int
  | .towardZero, q, x => roundTowardZero q x
  | .up, q, x => roundUp q x
  | .down, q, x => roundDown q x

/-! ## Bounds at the magnitude level -/

theorem roundDownNat_le (q n : Nat) : roundDownNat q n ≤ n :=
  Nat.div_mul_le_self n q

theorem le_roundUpNat (q n : Nat) (hq : 0 < q) : n ≤ roundUpNat q n := by
  unfold roundUpNat
  have h := Nat.div_add_mod n q
  rw [Nat.mul_comm q (n / q)] at h
  have hr := Nat.mod_lt n hq
  conv =>
    lhs
    rw [← h]
  split <;> omega

theorem roundDownNat_le_roundUpNat (q n : Nat) :
    roundDownNat q n ≤ roundUpNat q n := by
  unfold roundDownNat roundUpNat
  split <;> omega

theorem roundDownNat_eq_self_of_dvd (q n : Nat) (h : q ∣ n) :
    roundDownNat q n = n :=
  Nat.div_mul_cancel h

theorem roundUpNat_eq_self_of_dvd (q n : Nat) (h : q ∣ n) :
    roundUpNat q n = n := by
  unfold roundUpNat
  rw [Nat.mod_eq_zero_of_dvd h, ite_eq_left rfl]
  exact Nat.div_mul_cancel h

theorem roundDownNat_mul_add (q k r : Nat) (_hq : 0 < q) (hr : r < q) :
    roundDownNat q (k * q + r) = k * q := by
  unfold roundDownNat
  have hdiv : (k * q + r) / q = k := by
    apply Nat.div_eq_of_lt_le
    · omega
    · have hs : (k + 1) * q = k * q + q := Nat.succ_mul k q
      omega
  rw [hdiv]

theorem roundUpNat_mul_add (q k r : Nat) (_hq : 0 < q) (hr : r < q) :
    roundUpNat q (k * q + r) = k * q + (if r = 0 then 0 else q) := by
  unfold roundUpNat
  have hdiv : (k * q + r) / q = k := by
    apply Nat.div_eq_of_lt_le
    · omega
    · have hs : (k + 1) * q = k * q + q := Nat.succ_mul k q
      omega
  have hmod : (k * q + r) % q = r := by
    rw [Nat.mul_comm k q, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  rw [hdiv, hmod]

/-- A halfway grid point rounds down to the lower endpoint. -/
theorem roundDownNat_halfway (q k : Nat) (hq : 0 < q) :
    roundDownNat q (k * q + q / 2) = k * q := by
  apply roundDownNat_mul_add q k (q / 2) hq
  exact Nat.div_lt_self hq (by decide)

/-- With an even quantum, a halfway grid point rounds up to the upper endpoint. -/
theorem roundUpNat_halfway (q k : Nat) (hq : 0 < q) (hqe : q % 2 = 0) :
    roundUpNat q (k * q + q / 2) = (k + 1) * q := by
  rw [roundUpNat_mul_add q k (q / 2) hq (Nat.div_lt_self hq (by decide))]
  have hne : q / 2 ≠ 0 := by omega
  rw [ite_eq_right hne, Nat.succ_mul]

/-- At a halfway point the three rules split exactly as expected: down is the
lower endpoint, up is the upper endpoint, and even picks by the parity of the
quotient. -/
theorem tie_down_up_even (q k : Nat) (hq : 0 < q) (hqe : q % 2 = 0) :
    roundDownNat q (k * q + q / 2) = k * q ∧
      roundUpNat q (k * q + q / 2) = (k + 1) * q ∧
      roundEvenNat q (k * q + q / 2) =
        (if k % 2 = 0 then k * q else (k + 1) * q) :=
  ⟨roundDownNat_halfway q k hq, roundUpNat_halfway q k hq hqe,
    roundEvenNat_halfway_even q k hq hqe⟩

theorem roundDownNat_dvd (q n : Nat) : ∃ k : Nat, roundDownNat q n = k * q :=
  ⟨n / q, rfl⟩

theorem roundUpNat_dvd (q n : Nat) :
    ∃ k : Nat, roundUpNat q n = k * q := by
  by_cases h : n % q = 0
  · rw [roundUpNat, ite_eq_left h]
    exact ⟨n / q, rfl⟩
  · refine ⟨n / q + 1, ?_⟩
    rw [roundUpNat, ite_eq_right h, Nat.succ_mul]

theorem roundDownNat_zero (q : Nat) : roundDownNat q 0 = 0 := by
  unfold roundDownNat
  simp

theorem roundUpNat_zero (q : Nat) : roundUpNat q 0 = 0 := by
  unfold roundUpNat
  simp

theorem roundTowardZeroNat_zero (q : Nat) : roundTowardZeroNat q 0 = 0 := by
  unfold roundTowardZeroNat
  simp

theorem roundDownNat_one (n : Nat) : roundDownNat 1 n = n := by
  unfold roundDownNat
  simp

theorem roundUpNat_one (n : Nat) : roundUpNat 1 n = n := by
  unfold roundUpNat
  simp [Nat.mod_one]

/-! ## The signed directed roundings -/

theorem roundDown_le (q : Nat) (hq : 0 < q) (x : Int) : roundDown q x ≤ x := by
  unfold roundDown
  split
  · rename_i hx
    have ht : ((x.toNat : Int)) = x := Int.toNat_of_nonneg hx
    have h := roundDownNat_le q x.toNat
    omega
  · rename_i hx
    have hx0 : 0 ≤ -x := by omega
    have ht : (((-x).toNat : Int)) = -x := Int.toNat_of_nonneg hx0
    have h := le_roundUpNat q (-x).toNat hq
    omega

theorem le_roundUp (q : Nat) (hq : 0 < q) (x : Int) : x ≤ roundUp q x := by
  unfold roundUp
  split
  · rename_i hx
    have ht : ((x.toNat : Int)) = x := Int.toNat_of_nonneg hx
    have h := le_roundUpNat q x.toNat hq
    omega
  · rename_i hx
    have hx0 : 0 ≤ -x := by omega
    have ht : (((-x).toNat : Int)) = -x := Int.toNat_of_nonneg hx0
    have h := roundDownNat_le q (-x).toNat
    omega

theorem roundDown_le_roundUp (q : Nat) (hq : 0 < q) (x : Int) :
    roundDown q x ≤ roundUp q x := by
  have h1 := roundDown_le q hq x
  have h2 := le_roundUp q hq x
  omega

theorem roundDown_neg (q : Nat) (x : Int) : roundDown q (-x) = -roundUp q x := by
  by_cases hneg : x < 0
  · have hx : ¬ 0 ≤ x := Int.not_le_of_gt hneg
    have hx0 : 0 ≤ -x := Int.neg_nonneg_of_nonpos (Int.le_of_lt hneg)
    unfold roundDown roundUp
    rw [ite_eq_right hx, ite_eq_left hx0]
    simp
  · have hx : 0 ≤ x := Int.le_of_not_gt hneg
    by_cases hzero : x = 0
    · subst hzero
      change roundDown q (0 : Int) = -roundUp q 0
      have h0 : (0 : Int) ≤ 0 := Int.le_refl 0
      unfold roundDown roundUp
      rw [ite_eq_left h0, ite_eq_left h0]
      change ((roundDownNat q 0 : Nat) : Int) = -((roundUpNat q 0 : Nat) : Int)
      rw [roundDownNat_zero, roundUpNat_zero]
      rfl
    · have hnx : ¬ 0 ≤ -x := by
        intro h
        have hle : -x ≤ 0 := Int.neg_nonpos_of_nonneg hx
        exact hzero (Int.neg_eq_zero.mp (Int.le_antisymm hle h))
      unfold roundDown roundUp
      rw [ite_eq_right hnx, ite_eq_left hx]
      simp

theorem roundUp_neg (q : Nat) (x : Int) : roundUp q (-x) = -roundDown q x := by
  by_cases hneg : x < 0
  · have hx : ¬ 0 ≤ x := Int.not_le_of_gt hneg
    have hx0 : 0 ≤ -x := Int.neg_nonneg_of_nonpos (Int.le_of_lt hneg)
    unfold roundUp roundDown
    rw [ite_eq_right hx, ite_eq_left hx0]
    simp
  · have hx : 0 ≤ x := Int.le_of_not_gt hneg
    by_cases hzero : x = 0
    · subst hzero
      change roundUp q (0 : Int) = -roundDown q 0
      have h0 : (0 : Int) ≤ 0 := Int.le_refl 0
      unfold roundUp roundDown
      rw [ite_eq_left h0, ite_eq_left h0]
      change ((roundUpNat q 0 : Nat) : Int) = -((roundDownNat q 0 : Nat) : Int)
      rw [roundDownNat_zero, roundUpNat_zero]
      rfl
    · have hnx : ¬ 0 ≤ -x := by
        intro h
        have hle : -x ≤ 0 := Int.neg_nonpos_of_nonneg hx
        exact hzero (Int.neg_eq_zero.mp (Int.le_antisymm hle h))
      unfold roundUp roundDown
      rw [ite_eq_right hnx, ite_eq_left hx]
      simp

theorem roundTowardZero_neg (q : Nat) (x : Int) :
    roundTowardZero q (-x) = -roundTowardZero q x := by
  by_cases hneg : x < 0
  · have hx : ¬ 0 ≤ x := Int.not_le_of_gt hneg
    have hx0 : 0 ≤ -x := Int.neg_nonneg_of_nonpos (Int.le_of_lt hneg)
    unfold roundTowardZero
    rw [ite_eq_right hx, ite_eq_left hx0]
    simp [roundTowardZeroNat, roundDownNat]
  · have hx : 0 ≤ x := Int.le_of_not_gt hneg
    by_cases hzero : x = 0
    · subst hzero
      change roundTowardZero q (0 : Int) = -roundTowardZero q 0
      have h0 : (0 : Int) ≤ 0 := Int.le_refl 0
      unfold roundTowardZero
      rw [ite_eq_left h0]
      change ((roundTowardZeroNat q 0 : Nat) : Int) =
        -((roundTowardZeroNat q 0 : Nat) : Int)
      rw [roundTowardZeroNat_zero]
      rfl
    · have hnx : ¬ 0 ≤ -x := by
        intro h
        have hle : -x ≤ 0 := Int.neg_nonpos_of_nonneg hx
        exact hzero (Int.neg_eq_zero.mp (Int.le_antisymm hle h))
      unfold roundTowardZero
      rw [ite_eq_right hnx, ite_eq_left hx]
      simp [roundTowardZeroNat, roundDownNat]

theorem roundTowardZero_eq_roundDown_of_nonneg (q : Nat) {x : Int} (hx : 0 ≤ x) :
    roundTowardZero q x = roundDown q x := by
  simp [roundTowardZero, roundDown, roundTowardZeroNat, roundDownNat, hx]

theorem roundTowardZero_eq_roundUp_of_neg (q : Nat) {x : Int} (hx : ¬ 0 ≤ x) :
    roundTowardZero q x = roundUp q x := by
  simp [roundTowardZero, roundDownNat, roundUp, hx]

theorem roundDown_le_roundTowardZero (q : Nat) (hq : 0 < q) (x : Int) :
    roundDown q x ≤ roundTowardZero q x := by
  by_cases hx : 0 ≤ x
  · rw [roundTowardZero_eq_roundDown_of_nonneg q hx]
    omega
  · rw [roundTowardZero_eq_roundUp_of_neg q hx]
    exact roundDown_le_roundUp q hq x

theorem roundTowardZero_le_roundUp (q : Nat) (hq : 0 < q) (x : Int) :
    roundTowardZero q x ≤ roundUp q x := by
  by_cases hx : 0 ≤ x
  · rw [roundTowardZero_eq_roundDown_of_nonneg q hx]
    exact roundDown_le_roundUp q hq x
  · rw [roundTowardZero_eq_roundUp_of_neg q hx]
    omega

/-! ## Fixed points on the grid -/

theorem roundDown_eq_self_of_natAbs_dvd (q : Nat) (x : Int) (h : q ∣ x.natAbs) :
    roundDown q x = x := by
  by_cases hx : 0 ≤ x
  · have htoNat : x.toNat = x.natAbs := by
      have h1 : (x.toNat : Int) = x := Int.toNat_of_nonneg hx
      have h2 : (x.natAbs : Int) = x := Int.natAbs_of_nonneg hx
      exact Int.ofNat.inj (h1.trans h2.symm)
    unfold roundDown
    rw [ite_eq_left hx, htoNat, roundDownNat_eq_self_of_dvd q x.natAbs h]
    exact Int.natAbs_of_nonneg hx
  · have hx0 : 0 ≤ -x := by omega
    have htoNat : (-x).toNat = x.natAbs := by
      have h1 : (((-x).toNat : Int)) = -x := Int.toNat_of_nonneg hx0
      have h2 : ((x.natAbs : Int)) = -x := by
        rw [← Int.natAbs_neg x]
        exact Int.natAbs_of_nonneg hx0
      omega
    unfold roundDown
    rw [ite_eq_right hx, htoNat, roundUpNat_eq_self_of_dvd q x.natAbs h]
    have h2 : ((x.natAbs : Int)) = -x := by
      rw [← Int.natAbs_neg x]
      exact Int.natAbs_of_nonneg hx0
    omega

theorem roundUp_eq_self_of_natAbs_dvd (q : Nat) (x : Int) (h : q ∣ x.natAbs) :
    roundUp q x = x := by
  by_cases hx : 0 ≤ x
  · have htoNat : x.toNat = x.natAbs := by
      have h1 : (x.toNat : Int) = x := Int.toNat_of_nonneg hx
      have h2 : (x.natAbs : Int) = x := Int.natAbs_of_nonneg hx
      exact Int.ofNat.inj (h1.trans h2.symm)
    unfold roundUp
    rw [ite_eq_left hx, htoNat, roundUpNat_eq_self_of_dvd q x.natAbs h]
    exact Int.natAbs_of_nonneg hx
  · have hx0 : 0 ≤ -x := by omega
    have htoNat : (-x).toNat = x.natAbs := by
      have h1 : (((-x).toNat : Int)) = -x := Int.toNat_of_nonneg hx0
      have h2 : ((x.natAbs : Int)) = -x := by
        rw [← Int.natAbs_neg x]
        exact Int.natAbs_of_nonneg hx0
      omega
    unfold roundUp
    rw [ite_eq_right hx, htoNat, roundDownNat_eq_self_of_dvd q x.natAbs h]
    have h2 : ((x.natAbs : Int)) = -x := by
      rw [← Int.natAbs_neg x]
      exact Int.natAbs_of_nonneg hx0
    omega

theorem roundTowardZero_eq_self_of_natAbs_dvd (q : Nat) (x : Int)
    (h : q ∣ x.natAbs) : roundTowardZero q x = x := by
  by_cases hx : 0 ≤ x
  · rw [roundTowardZero_eq_roundDown_of_nonneg q hx]
    exact roundDown_eq_self_of_natAbs_dvd q x h
  · rw [roundTowardZero_eq_roundUp_of_neg q hx]
    exact roundUp_eq_self_of_natAbs_dvd q x h

theorem roundMode_eq_self_of_natAbs_dvd (mode : RMode) (q : Nat) (x : Int)
    (h : q ∣ x.natAbs) : roundMode mode q x = x := by
  cases mode
  · exact roundTowardZero_eq_self_of_natAbs_dvd q x h
  · exact roundUp_eq_self_of_natAbs_dvd q x h
  · exact roundDown_eq_self_of_natAbs_dvd q x h

/-! ## Agreement with ties-to-even -/

/-- Nearest-even and directed rounding differ only in the choice between the
two adjacent grid points: the even result is always the floor or the ceiling. -/
theorem roundEvenNat_eq_down_or_up (q n : Nat) (hq : 0 < q) :
    roundEvenNat q n = roundDownNat q n ∨
      roundEvenNat q n = roundUpNat q n := by
  have hqhalf : q / 2 < q := Nat.div_lt_self hq (by decide)
  obtain ⟨k, hk⟩ : ∃ k : Nat, n / q = k := ⟨n / q, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : Nat, n % q = r := ⟨n % q, rfl⟩
  have hrlt : r < q := by rw [← hr]; exact Nat.mod_lt n hq
  have hdiv : k * q + r = n := by
    have h := Nat.div_add_mod n q
    rw [hk, hr] at h
    rw [Nat.mul_comm q k] at h
    exact h
  have hdown : roundDownNat q n = k * q := by
    rw [roundDownNat, hk]
  have hup : roundUpNat q n = k * q + (if r = 0 then 0 else q) := by
    rw [roundUpNat, hk, hr]
  rw [hdown, hup]
  by_cases htie : q % 2 = 0 ∧ n % q = q / 2
  · rw [roundEvenNat_tie q n htie, hk]
    have hne : r ≠ 0 := by
      have h1 := htie.1
      have h2 := htie.2
      omega
    rw [ite_eq_right hne]
    by_cases hk2 : k % 2 = 0
    · rw [ite_eq_left hk2]
      exact Or.inl rfl
    · rw [ite_eq_right hk2]
      exact Or.inr rfl
  · rw [roundEvenNat_notie q n htie]
    have hq2 : 2 * (q / 2) ≤ q := by
      rw [Nat.mul_comm]
      exact Nat.div_mul_le_self q 2
    by_cases hlt : r + q / 2 < q
    · left
      have hquot : (n + q / 2) / q = k := by
        rw [← hdiv, Nat.add_assoc, Nat.mul_comm k q, Nat.mul_add_div hq,
          Nat.div_eq_of_lt hlt, Nat.add_zero]
      rw [hquot]
    · right
      have hrne : r ≠ 0 := by
        intro h0
        subst h0
        exact hlt (by omega)
      rw [ite_eq_right hrne]
      have hdiv1 : (r + q / 2) / q = 1 := by
        apply Nat.div_eq_of_lt_le
        · omega
        · omega
      have hquot : (n + q / 2) / q = k + 1 := by
        rw [← hdiv, Nat.add_assoc, Nat.mul_comm k q, Nat.mul_add_div hq,
          hdiv1]
      rw [hquot, Nat.succ_mul]

theorem roundDownNat_le_roundEvenNat (q n : Nat) (hq : 0 < q) :
    roundDownNat q n ≤ roundEvenNat q n := by
  rcases roundEvenNat_eq_down_or_up q n hq with h | h
  · rw [h]
    exact Nat.le_refl _
  · rw [h]
    exact roundDownNat_le_roundUpNat q n

theorem roundEvenNat_le_roundUpNat (q n : Nat) (hq : 0 < q) :
    roundEvenNat q n ≤ roundUpNat q n := by
  rcases roundEvenNat_eq_down_or_up q n hq with h | h
  · rw [h]
    exact roundDownNat_le_roundUpNat q n
  · rw [h]
    exact Nat.le_refl _

theorem roundDown_le_roundEven (q : Nat) (hq : 0 < q) (x : Int) :
    roundDown q x ≤ roundEven q x := by
  by_cases hx : 0 ≤ x
  · have ht : ((x.toNat : Int)) = x := Int.toNat_of_nonneg hx
    have h := roundDownNat_le_roundEvenNat q x.toNat hq
    rw [roundDown, ite_eq_left hx, roundEven_of_nonneg q hx]
    omega
  · have hx0 : 0 ≤ -x := by omega
    have ht : (((-x).toNat : Int)) = -x := Int.toNat_of_nonneg hx0
    have h := roundEvenNat_le_roundUpNat q (-x).toNat hq
    rw [roundDown, ite_eq_right hx, roundEven_of_neg q hx]
    omega

theorem roundEven_le_roundUp (q : Nat) (hq : 0 < q) (x : Int) :
    roundEven q x ≤ roundUp q x := by
  by_cases hx : 0 ≤ x
  · have ht : ((x.toNat : Int)) = x := Int.toNat_of_nonneg hx
    have h := roundEvenNat_le_roundUpNat q x.toNat hq
    rw [roundUp, ite_eq_left hx, roundEven_of_nonneg q hx]
    omega
  · have hx0 : 0 ≤ -x := by omega
    have ht : (((-x).toNat : Int)) = -x := Int.toNat_of_nonneg hx0
    have h := roundDownNat_le_roundEvenNat q (-x).toNat hq
    rw [roundUp, ite_eq_right hx, roundEven_of_neg q hx]
    omega

/-- At any quantum, the ties-to-even result lies between the two directed
results.  This is what the subnormal/crossing class below collapses. -/
theorem roundEven_between_directed (q : Nat) (hq : 0 < q) (x : Int) :
    roundDown q x ≤ roundEven q x ∧ roundEven q x ≤ roundUp q x :=
  ⟨roundDown_le_roundEven q hq x, roundEven_le_roundUp q hq x⟩

/-! ## The value-level directed addition -/

/-- The result of overflow for a directed mode.  Toward zero saturates at the
largest finite magnitude in both signs; toward `+inf` keeps a negative value
finite and sends a positive one to `+inf`; toward `-inf` is the mirror image. -/
def overflowMode (mode : RMode) (neg : Bool) : Fp16Val :=
  match mode with
  | .towardZero => .fin ⟨neg, maxFiniteScaled⟩
  | .up => if neg then .fin ⟨true, maxFiniteScaled⟩ else .inf false
  | .down => if neg then .inf true else .fin ⟨false, maxFiniteScaled⟩

/-- The analogue of `roundScaled` for a directed mode: the destination binade
is chosen from `Nat.log2`, the exact magnitude is rounded to its quantum, and
a quotient of `2048` is the next binade.  Binades above `30` overflow. -/
def roundScaledMode (mode : RMode) (z : Int) (sa sb : Bool) : Fp16Val :=
  if z = 0 then
    .fin { sign := zeroSign sa sb, mag := 0 }
  else if z.natAbs < 1024 then
    .fin { sign := z < 0, mag := z.natAbs }
  else
    let q := 2 ^ (Nat.log2 z.natAbs - 10)
    let e := Nat.log2 z.natAbs - 9
    let mant := (roundMode mode q z).natAbs / q
    if 2048 ≤ mant then
      if e + 1 ≤ 30 then .fin { sign := z < 0, mag := 1024 * 2 ^ e }
      else overflowMode mode (z < 0)
    else if e ≤ 30 then
      .fin { sign := z < 0, mag := mant * 2 ^ (e - 1) }
    else overflowMode mode (z < 0)

/-- Value-level fp16 addition under a directed mode.  The special-value rules
are exactly those of `addFull`; only the final rounding of a finite sum
differs. -/
def addDirected : RMode → Fp16Val → Fp16Val → Fp16Val
  | _, .nan ng p _q, _ => .nan ng p true
  | _, _, .nan ng p _q => .nan ng p true
  | _, .inf a, .inf b => if a = b then .inf a else .nan false 0 true
  | _, .inf a, .fin _ => .inf a
  | _, .fin _, .inf b => .inf b
  | mode, .fin a, .fin b => roundScaledMode mode (a.signed + b.signed) a.sign b.sign

theorem addDirected_fin_fin (mode : RMode) (x y : SVal) :
    addDirected mode (.fin x) (.fin y) =
      roundScaledMode mode (x.signed + y.signed) x.sign y.sign := rfl

/-- Signed zero follows the same rule under every directed mode. -/
theorem addDirected_zero_zero (mode : RMode) (sa sb : Bool) :
    addDirected mode (.fin ⟨sa, 0⟩) (.fin ⟨sb, 0⟩) =
      .fin ⟨zeroSign sa sb, 0⟩ := by
  rw [addDirected_fin_fin]
  simp [SVal.signed, roundScaledMode]

theorem addDirected_nan_left (mode : RMode) (ng : Bool) (p : Nat) (q : Bool)
    (v : Fp16Val) :
    addDirected mode (.nan ng p q) v = .nan ng p true := by
  cases v <;> rfl

theorem addDirected_fin_nan (mode : RMode) (v : SVal) (ng : Bool)
    (p : Nat) (q : Bool) :
    addDirected mode (.fin v) (.nan ng p q) = .nan ng p true := rfl

theorem addDirected_nan_nan (mode : RMode) (ng ng' : Bool) (p p' : Nat)
    (q q' : Bool) :
    addDirected mode (.nan ng p q) (.nan ng' p' q') = .nan ng p true := rfl

theorem addDirected_inf_same (mode : RMode) (a : Bool) :
    addDirected mode (.inf a) (.inf a) = .inf a := by
  cases mode <;> cases a <;> decide

theorem addDirected_inf_opposite (mode : RMode) (a : Bool) :
    addDirected mode (.inf a) (.inf (!a)) = .nan false 0 true := by
  cases mode <;> cases a <;> decide

theorem addDirected_inf_fin (mode : RMode) (a : Bool) (v : SVal) :
    addDirected mode (.inf a) (.fin v) = .inf a := by
  cases mode <;> rfl

theorem addDirected_fin_inf (mode : RMode) (v : SVal) (a : Bool) :
    addDirected mode (.fin v) (.inf a) = .inf a := by
  cases mode <;> rfl

/-! ## The magnitude of a directed rounding is on its grid -/

theorem roundDown_natAbs_dvd (q : Nat) (x : Int) :
    ∃ k : Nat, (roundDown q x).natAbs = k * q := by
  by_cases hx : 0 ≤ x
  · rw [roundDown, ite_eq_left hx]
    exact ⟨x.toNat / q, by rw [Int.natAbs_natCast]; rfl⟩
  · rw [roundDown, ite_eq_right hx]
    obtain ⟨k, hk⟩ := roundUpNat_dvd q (-x).toNat
    exact ⟨k, by rw [Int.natAbs_neg, Int.natAbs_natCast, hk]⟩

theorem roundUp_natAbs_dvd (q : Nat) (x : Int) :
    ∃ k : Nat, (roundUp q x).natAbs = k * q := by
  by_cases hx : 0 ≤ x
  · rw [roundUp, ite_eq_left hx]
    obtain ⟨k, hk⟩ := roundUpNat_dvd q x.toNat
    exact ⟨k, by rw [Int.natAbs_natCast, hk]⟩
  · rw [roundUp, ite_eq_right hx]
    obtain ⟨k, hk⟩ := roundDownNat_dvd q (-x).toNat
    exact ⟨k, by rw [Int.natAbs_neg, Int.natAbs_natCast, hk]⟩

theorem roundTowardZero_natAbs_dvd (q : Nat) (x : Int) :
    ∃ k : Nat, (roundTowardZero q x).natAbs = k * q := by
  by_cases hx : 0 ≤ x
  · rw [roundTowardZero, ite_eq_left hx]
    exact ⟨x.toNat / q, by rw [Int.natAbs_natCast]; rfl⟩
  · rw [roundTowardZero, ite_eq_right hx]
    obtain ⟨k, hk⟩ := roundDownNat_dvd q (-x).toNat
    exact ⟨k, by rw [Int.natAbs_neg, Int.natAbs_natCast, hk]⟩

theorem roundMode_natAbs_dvd (mode : RMode) (q : Nat) (x : Int) :
    ∃ k : Nat, (roundMode mode q x).natAbs = k * q := by
  cases mode
  · exact roundTowardZero_natAbs_dvd q x
  · exact roundUp_natAbs_dvd q x
  · exact roundDown_natAbs_dvd q x

/-! ## The subnormal and crossing class -/

/-- A nonzero magnitude at most `2046` units lives in the subnormal grid or in
the first normal binade, whose quantum is one; every directed mode is exact. -/
theorem roundScaledMode_eq_fin_of_le_2046 (mode : RMode) (z : Int) (sa sb : Bool)
    (hz : z ≠ 0) (h : z.natAbs ≤ 2046) :
    roundScaledMode mode z sa sb = .fin ⟨z < 0, z.natAbs⟩ := by
  by_cases hsmall : z.natAbs < 1024
  · unfold roundScaledMode
    rw [ite_eq_right hz, ite_eq_left hsmall]
  · unfold roundScaledMode
    rw [ite_eq_right hz, ite_eq_right hsmall]
    have hm0 : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
    have hlog : Nat.log2 z.natAbs = 10 := by
      rw [Nat.log2_eq_iff hm0]
      have h1024 : (2 : Nat) ^ 10 = 1024 := by decide
      have h2048 : (2 : Nat) ^ 11 = 2048 := by decide
      constructor <;> omega
    have hq : 2 ^ (Nat.log2 z.natAbs - 10) = 1 := by rw [hlog]
    have he : Nat.log2 z.natAbs - 9 = 1 := by rw [hlog]
    have hone : roundMode mode 1 z = z :=
      roundMode_eq_self_of_natAbs_dvd mode 1 z ⟨z.natAbs, by rw [Nat.one_mul]⟩
    have hlt : ¬ 2048 ≤ z.natAbs := by omega
    simp [hq, he, hone, hlt]

/-- On the second normal binade `[2048, 4095]` the quantum is two, so a
directed mode differs from the exact sum exactly at the odd magnitudes. -/
theorem roundScaledMode_binade2 (mode : RMode) (z : Int) (sa sb : Bool)
    (h1 : 2048 ≤ z.natAbs) (h2 : z.natAbs ≤ 4095)
    (hno : (roundMode mode 2 z).natAbs < 4096) :
    roundScaledMode mode z sa sb = .fin ⟨z < 0, (roundMode mode 2 z).natAbs⟩ := by
  have hz : z ≠ 0 := by
    intro h0
    rw [h0] at h1
    simp at h1
  have hsmall : ¬ z.natAbs < 1024 := by omega
  have hm0 : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  have hlog : Nat.log2 z.natAbs = 11 := by
    rw [Nat.log2_eq_iff hm0]
    have h2048 : (2 : Nat) ^ 11 = 2048 := by decide
    have h4096 : (2 : Nat) ^ 12 = 4096 := by decide
    constructor <;> omega
  have hq : 2 ^ (Nat.log2 z.natAbs - 10) = 2 := by rw [hlog]
  have he : Nat.log2 z.natAbs - 9 = 2 := by rw [hlog]
  obtain ⟨k, hk⟩ := roundMode_natAbs_dvd mode 2 z
  have hdvd : 2 ∣ (roundMode mode 2 z).natAbs := ⟨k, by rw [hk, Nat.mul_comm]⟩
  have hmant : (roundMode mode 2 z).natAbs / 2 * 2 =
      (roundMode mode 2 z).natAbs := Nat.div_mul_cancel hdvd
  have hlt : ¬ 2048 ≤ (roundMode mode 2 z).natAbs / 2 := by
    have hlt' : (roundMode mode 2 z).natAbs / 2 < 2048 := by
      rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2)]
      omega
    omega
  have hval : roundScaledMode mode z sa sb =
      .fin ⟨z < 0, (roundMode mode 2 z).natAbs / 2 * 2 ^ (2 - 1)⟩ := by
    unfold roundScaledMode
    rw [ite_eq_right hz, ite_eq_right hsmall]
    simp [hq, he, hlt]
  rw [hval]
  simp [hmant]

/-- Two subnormal operands add exactly, so every directed mode agrees with the
ties-to-even model on the whole subnormal/crossing class. -/
theorem addDirected_fin_subnormal_eq_addFull (mode : RMode) (x y : SVal)
    (hx : x.mag ≤ 1023) (hy : y.mag ≤ 1023) :
    addDirected mode (.fin x) (.fin y) = addFull (.fin x) (.fin y) := by
  have hle := SVal.natAbs_add_signed_le_2046 x y hx hy
  rw [addDirected_fin_fin, addFull_fin_fin]
  by_cases h0 : x.signed + y.signed = 0
  · rw [h0]
    simp [roundScaledMode, roundScaled]
  · rw [roundScaledMode_eq_fin_of_le_2046 mode _ x.sign y.sign h0 hle]
    rw [← SVal.add_eq_mk_of_ne_zero x y h0]
    by_cases hlow : (x.signed + y.signed).natAbs ≤ 1023
    · have hfit : roundScaled (x.signed + y.signed) x.sign y.sign =
          .fin (x.add y) := by
        rw [← addFull_fin_fin]
        exact (addFull_fin_subnormal_fits x y hx hy hlow).1
      rw [hfit]
    · have hcross : 1024 ≤ (x.signed + y.signed).natAbs := by omega
      have hfit : roundScaled (x.signed + y.signed) x.sign y.sign =
          .fin (x.add y) := by
        rw [← addFull_fin_fin]
        exact addFull_fin_subnormal_cross x y hx hy hcross
      rw [hfit]

/-- The directed result on the exact-value form of the subnormal class. -/
theorem addDirected_fin_subnormal_value (mode : RMode) (x y : SVal)
    (hx : x.mag ≤ 1023) (hy : y.mag ≤ 1023) :
    ∃ r : SVal, addDirected mode (.fin x) (.fin y) = .fin r ∧
      r.signed = x.signed + y.signed ∧ r.mag ≤ 2046 := by
  rw [addDirected_fin_subnormal_eq_addFull mode x y hx hy]
  by_cases hlow : (x.signed + y.signed).natAbs ≤ 1023
  · obtain ⟨r, h1, h2, h3⟩ := addFull_fin_subnormal_fits_value x y hx hy hlow
    exact ⟨r, h1, h2, by omega⟩
  · have hcross : 1024 ≤ (x.signed + y.signed).natAbs := by omega
    obtain ⟨r, h1, h2, _h3, h4⟩ :=
      addFull_fin_subnormal_cross_value x y hx hy hcross
    exact ⟨r, h1, h2, by omega⟩

/-- The binade-2 tie behaviour at the value level. -/
theorem addDirected_fin_binade2 (mode : RMode) (x y : SVal)
    (h1 : 2048 ≤ (x.signed + y.signed).natAbs)
    (h2 : (x.signed + y.signed).natAbs ≤ 4095)
    (hno : (roundMode mode 2 (x.signed + y.signed)).natAbs < 4096) :
    addDirected mode (.fin x) (.fin y) =
      .fin ⟨x.signed + y.signed < 0,
        (roundMode mode 2 (x.signed + y.signed)).natAbs⟩ :=
  roundScaledMode_binade2 mode _ x.sign y.sign h1 h2 hno

/-! ## Overflow thresholds -/

theorem maxFiniteScaled_eq : maxFiniteScaled = 2047 * 2 ^ 29 := rfl

theorem two_pow_39_le_maxFiniteScaled : 2 ^ 39 ≤ maxFiniteScaled := by decide

theorem maxFiniteScaled_lt_two_pow_40 : maxFiniteScaled < 2 ^ 40 := by decide

theorem log2_eq_39_of_maxFiniteScaled_le (m : Nat)
    (h1 : maxFiniteScaled ≤ m) (h2 : m < 2 ^ 40) : Nat.log2 m = 39 := by
  have hm : m ≠ 0 := by
    have hpos : 0 < maxFiniteScaled := by decide
    omega
  rw [Nat.log2_eq_iff hm]
  constructor
  · have h39 : (2 : Nat) ^ 39 ≤ maxFiniteScaled := two_pow_39_le_maxFiniteScaled
    omega
  · have h40 : (2 : Nat) ^ (39 + 1) = 2 ^ 40 := by decide
    omega

theorem le_log2_of_two_pow_le (m k : Nat) (h : 2 ^ k ≤ m) : k ≤ Nat.log2 m := by
  have hm : m ≠ 0 := by
    have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
    omega
  rw [Nat.le_log2 hm]
  exact h

theorem roundDownNat_pow29_of_maxFiniteScaled_le (m : Nat)
    (h1 : maxFiniteScaled ≤ m) (h2 : m < 2 ^ 40) :
    roundDownNat (2 ^ 29) m = maxFiniteScaled := by
  have hdiv : m / 2 ^ 29 = 2047 := by
    apply Nat.div_eq_of_lt_le
    · exact h1
    · have hpow : (2047 + 1) * 2 ^ 29 = 2 ^ 40 := by decide
      omega
  unfold roundDownNat
  rw [hdiv]
  rfl

theorem roundUpNat_pow29_of_maxFiniteScaled_lt (m : Nat)
    (h1 : maxFiniteScaled < m) (h2 : m < 2 ^ 40) :
    roundUpNat (2 ^ 29) m = 2 ^ 40 := by
  have hdiv : m / 2 ^ 29 = 2047 := by
    apply Nat.div_eq_of_lt_le
    · exact Nat.le_of_lt h1
    · have hpow : (2047 + 1) * 2 ^ 29 = 2 ^ 40 := by decide
      omega
  have hdm := Nat.div_add_mod m (2 ^ 29)
  rw [hdiv, Nat.mul_comm (2 ^ 29) 2047] at hdm
  have hmod : m % 2 ^ 29 ≠ 0 := by
    intro h0
    have h1' : 2047 * 2 ^ 29 < m := h1
    rw [h0, Nat.add_zero] at hdm
    omega
  unfold roundUpNat
  rw [hdiv, ite_eq_right hmod]

theorem roundDown_natAbs_pow29_nonneg (z : Int) (hz : 0 ≤ z)
    (h1 : maxFiniteScaled ≤ z.natAbs) (h2 : z.natAbs < 2 ^ 40) :
    (roundDown (2 ^ 29) z).natAbs = maxFiniteScaled := by
  have htoNat : z.toNat = z.natAbs := by
    have h1' : (z.toNat : Int) = z := Int.toNat_of_nonneg hz
    have h2' : (z.natAbs : Int) = z := Int.natAbs_of_nonneg hz
    exact Int.ofNat.inj (h1'.trans h2'.symm)
  rw [roundDown, ite_eq_left hz, htoNat, Int.natAbs_natCast]
  exact roundDownNat_pow29_of_maxFiniteScaled_le z.natAbs h1 h2

theorem roundDown_natAbs_pow29_neg (z : Int) (hz : ¬ 0 ≤ z)
    (h1 : maxFiniteScaled < z.natAbs) (h2 : z.natAbs < 2 ^ 40) :
    (roundDown (2 ^ 29) z).natAbs = 2 ^ 40 := by
  have hz0 : 0 ≤ -z := by omega
  have htoNat : (-z).toNat = z.natAbs := by
    have h1' : (((-z).toNat : Int)) = -z := Int.toNat_of_nonneg hz0
    have h2' : ((z.natAbs : Int)) = -z := by
      rw [← Int.natAbs_neg z]
      exact Int.natAbs_of_nonneg hz0
    exact Int.ofNat.inj (h1'.trans h2'.symm)
  rw [roundDown, ite_eq_right hz, htoNat, Int.natAbs_neg, Int.natAbs_natCast]
  exact roundUpNat_pow29_of_maxFiniteScaled_lt z.natAbs h1 h2

theorem roundUp_natAbs_pow29_nonneg (z : Int) (hz : 0 ≤ z)
    (h1 : maxFiniteScaled < z.natAbs) (h2 : z.natAbs < 2 ^ 40) :
    (roundUp (2 ^ 29) z).natAbs = 2 ^ 40 := by
  have htoNat : z.toNat = z.natAbs := by
    have h1' : (z.toNat : Int) = z := Int.toNat_of_nonneg hz
    have h2' : (z.natAbs : Int) = z := Int.natAbs_of_nonneg hz
    exact Int.ofNat.inj (h1'.trans h2'.symm)
  rw [roundUp, ite_eq_left hz, htoNat, Int.natAbs_natCast]
  exact roundUpNat_pow29_of_maxFiniteScaled_lt z.natAbs h1 h2

theorem roundUp_natAbs_pow29_neg (z : Int) (hz : ¬ 0 ≤ z)
    (h1 : maxFiniteScaled ≤ z.natAbs) (h2 : z.natAbs < 2 ^ 40) :
    (roundUp (2 ^ 29) z).natAbs = maxFiniteScaled := by
  have hz0 : 0 ≤ -z := by omega
  have htoNat : (-z).toNat = z.natAbs := by
    have h1' : (((-z).toNat : Int)) = -z := Int.toNat_of_nonneg hz0
    have h2' : ((z.natAbs : Int)) = -z := by
      rw [← Int.natAbs_neg z]
      exact Int.natAbs_of_nonneg hz0
    exact Int.ofNat.inj (h1'.trans h2'.symm)
  rw [roundUp, ite_eq_right hz, htoNat, Int.natAbs_neg, Int.natAbs_natCast]
  exact roundDownNat_pow29_of_maxFiniteScaled_le z.natAbs h1 h2

theorem roundTowardZero_natAbs_pow29 (z : Int)
    (h1 : maxFiniteScaled ≤ z.natAbs) (h2 : z.natAbs < 2 ^ 40) :
    (roundTowardZero (2 ^ 29) z).natAbs = maxFiniteScaled := by
  by_cases hz : 0 ≤ z
  · rw [roundTowardZero_eq_roundDown_of_nonneg _ hz]
    exact roundDown_natAbs_pow29_nonneg z hz h1 h2
  · rw [roundTowardZero_eq_roundUp_of_neg _ hz]
    exact roundUp_natAbs_pow29_neg z hz h1 h2

/-- In binade 30, a rounded magnitude that is still below `2 ^ 40` is exactly
the largest finite magnitude, and the encoding returns it. -/
theorem roundScaledMode_binade30_fin (mode : RMode) (z : Int) (sa sb : Bool)
    (h1 : maxFiniteScaled ≤ z.natAbs) (h2 : z.natAbs < 2 ^ 40)
    (hm : (roundMode mode (2 ^ 29) z).natAbs = maxFiniteScaled) :
    roundScaledMode mode z sa sb = .fin ⟨z < 0, maxFiniteScaled⟩ := by
  have hz : z ≠ 0 := by
    intro h0
    rw [h0] at h1
    simp at h1
    have hpos : 0 < maxFiniteScaled := by decide
    omega
  have hsmall : ¬ z.natAbs < 1024 := by
    have h1024 : 1024 ≤ z.natAbs :=
      Nat.le_trans (by decide : 1024 ≤ maxFiniteScaled) h1
    omega
  have hlog : Nat.log2 z.natAbs = 39 := log2_eq_39_of_maxFiniteScaled_le _ h1 h2
  have hq : 2 ^ (Nat.log2 z.natAbs - 10) = 2 ^ 29 := by rw [hlog]
  have he : Nat.log2 z.natAbs - 9 = 30 := by rw [hlog]
  have hmant : (roundMode mode (2 ^ 29) z).natAbs / 2 ^ 29 = 2047 := by
    rw [hm, maxFiniteScaled_eq]
  have hlt : ¬ 2048 ≤ (roundMode mode (2 ^ 29) z).natAbs / 2 ^ 29 := by
    rw [hmant]
    omega
  have hval : roundScaledMode mode z sa sb =
      .fin ⟨z < 0,
        (roundMode mode (2 ^ 29) z).natAbs / 2 ^ 29 * 2 ^ (30 - 1)⟩ := by
    unfold roundScaledMode
    rw [ite_eq_right hz, ite_eq_right hsmall]
    simp [hq, he, hlt]
  rw [hval, hmant]
  rfl

/-- In binade 30, a rounded magnitude of `2 ^ 40` leaves the finite range. -/
theorem roundScaledMode_binade30_inf (mode : RMode) (z : Int) (sa sb : Bool)
    (h1 : maxFiniteScaled ≤ z.natAbs) (h2 : z.natAbs < 2 ^ 40)
    (hm : (roundMode mode (2 ^ 29) z).natAbs = 2 ^ 40) :
    roundScaledMode mode z sa sb = overflowMode mode (z < 0) := by
  have hz : z ≠ 0 := by
    intro h0
    rw [h0] at h1
    simp at h1
    have hpos : 0 < maxFiniteScaled := by decide
    omega
  have hsmall : ¬ z.natAbs < 1024 := by
    have h1024 : 1024 ≤ z.natAbs :=
      Nat.le_trans (by decide : 1024 ≤ maxFiniteScaled) h1
    omega
  have hlog : Nat.log2 z.natAbs = 39 := log2_eq_39_of_maxFiniteScaled_le _ h1 h2
  have hq : 2 ^ (Nat.log2 z.natAbs - 10) = 2 ^ 29 := by rw [hlog]
  have hmant : (roundMode mode (2 ^ 29) z).natAbs / 2 ^ 29 = 2048 := by
    rw [hm]
  have hge : 2048 ≤ (roundMode mode (2 ^ 29) z).natAbs / 2 ^ 29 := by
    rw [hmant]
    omega
  have he31 : ¬ (Nat.log2 z.natAbs - 9 + 1 ≤ 30) := by rw [hlog]; decide
  unfold roundScaledMode
  rw [ite_eq_right hz, ite_eq_right hsmall]
  simp [hq, hge, he31]

theorem roundUpNat_le_add (q n : Nat) : roundUpNat q n ≤ n + q := by
  unfold roundUpNat
  have h := Nat.div_add_mod n q
  rw [Nat.mul_comm q (n / q)] at h
  split <;> omega

/-- Truncation of a signed value has the magnitude of the floor of its
magnitude. -/
theorem roundTowardZero_natAbs_eq (q : Nat) (z : Int) :
    (roundTowardZero q z).natAbs = roundDownNat q z.natAbs := by
  by_cases hz : 0 ≤ z
  · have htoNat : z.toNat = z.natAbs := by
      have h1 : (z.toNat : Int) = z := Int.toNat_of_nonneg hz
      have h2 : (z.natAbs : Int) = z := Int.natAbs_of_nonneg hz
      exact Int.ofNat.inj (h1.trans h2.symm)
    rw [roundTowardZero_eq_roundDown_of_nonneg _ hz, roundDown,
      ite_eq_left hz, htoNat, Int.natAbs_natCast]
  · have hz0 : 0 ≤ -z := by omega
    have htoNat : (-z).toNat = z.natAbs := by
      have h1 : (((-z).toNat : Int)) = -z := Int.toNat_of_nonneg hz0
      have h2 : ((z.natAbs : Int)) = -z := by
        rw [← Int.natAbs_neg z]
        exact Int.natAbs_of_nonneg hz0
      exact Int.ofNat.inj (h1.trans h2.symm)
    rw [roundTowardZero_eq_roundUp_of_neg _ hz, roundUp,
      ite_eq_right hz, htoNat, Int.natAbs_neg, Int.natAbs_natCast]

theorem roundDownNat_dest_le_maxFiniteScaled (m : Nat) (h : m < 2 ^ 40) :
    roundDownNat (2 ^ (Nat.log2 m - 10)) m ≤ maxFiniteScaled := by
  by_cases hm : m ≤ maxFiniteScaled
  · exact Nat.le_trans (roundDownNat_le _ _) hm
  · have hmax : maxFiniteScaled < m := by omega
    have hlog : Nat.log2 m = 39 :=
      log2_eq_39_of_maxFiniteScaled_le m (by omega) h
    have hq : 2 ^ (Nat.log2 m - 10) = 2 ^ 29 := by rw [hlog]
    rw [hq]
    exact Nat.le_of_eq (roundDownNat_pow29_of_maxFiniteScaled_le m (by omega) h)

theorem roundUpNat_pow29_le_2047 (m : Nat) (hm : m ≤ 2047 * 2 ^ 29) :
    roundUpNat (2 ^ 29) m ≤ 2047 * 2 ^ 29 := by
  have hdm := Nat.div_add_mod m (2 ^ 29)
  rw [Nat.mul_comm (2 ^ 29) (m / 2 ^ 29)] at hdm
  have hk : m / 2 ^ 29 ≤ 2047 := Nat.div_le_of_le_mul hm
  unfold roundUpNat
  by_cases hmod : m % 2 ^ 29 = 0
  · rw [ite_eq_left hmod, Nat.add_zero]
    exact Nat.mul_le_mul_right _ hk
  · rw [ite_eq_right hmod]
    have hlt : m / 2 ^ 29 < 2047 := by
      rcases Nat.lt_or_eq_of_le hk with hlt | heq
      · exact hlt
      · exfalso
        rw [heq] at hdm
        have hpos : 0 < m % 2 ^ 29 := Nat.pos_of_ne_zero hmod
        omega
    have hk' : m / 2 ^ 29 + 1 ≤ 2047 := Nat.succ_le_of_lt hlt
    have hs : m / 2 ^ 29 * 2 ^ 29 + 2 ^ 29 = (m / 2 ^ 29 + 1) * 2 ^ 29 := by
      rw [Nat.succ_mul]
    rw [hs]
    exact Nat.mul_le_mul_right _ hk'

theorem roundUpNat_dest_le_maxFiniteScaled (m : Nat) (h1024 : 1024 ≤ m)
    (hm : m ≤ maxFiniteScaled) :
    roundUpNat (2 ^ (Nat.log2 m - 10)) m ≤ maxFiniteScaled := by
  have hm0 : m ≠ 0 := by omega
  by_cases hlog : Nat.log2 m = 39
  · have hq : 2 ^ (Nat.log2 m - 10) = 2 ^ 29 := by rw [hlog]
    rw [hq, maxFiniteScaled_eq]
    exact roundUpNat_pow29_le_2047 m hm
  · have hloglt : Nat.log2 m < 40 := by
      have hlt : Nat.log2 m < 40 ↔ m < 2 ^ 40 := Nat.log2_lt (k := 40) hm0
      have hm40 : m < 2 ^ 40 := by
        have hmlt : maxFiniteScaled < 2 ^ 40 := maxFiniteScaled_lt_two_pow_40
        omega
      exact hlt.mpr hm40
    have hlog38 : Nat.log2 m ≤ 38 := by omega
    have hqle : 2 ^ (Nat.log2 m - 10) ≤ 2 ^ 28 := by
      apply Nat.pow_le_pow_right (by decide)
      omega
    have hmlt39 : m < 2 ^ 39 := by
      have hlt : Nat.log2 m < 39 ↔ m < 2 ^ 39 := Nat.log2_lt (k := 39) hm0
      exact hlt.mp (by omega)
    have hle := roundUpNat_le_add (2 ^ (Nat.log2 m - 10)) m
    have hbound : m + 2 ^ 28 < 2047 * 2 ^ 29 := by
      have hpow : (2 : Nat) ^ 39 + 2 ^ 28 < 2047 * 2 ^ 29 := by decide
      omega
    rw [maxFiniteScaled_eq]
    exact Nat.le_of_lt (by omega)

/-- A nonzero word below the first normal binade is encoded exactly. -/
theorem roundScaledMode_fin_of_lt_1024 (mode : RMode) (z : Int) (sa sb : Bool)
    (h : z.natAbs < 1024) :
    ∃ v : SVal, roundScaledMode mode z sa sb = .fin v := by
  unfold roundScaledMode
  by_cases hz : z = 0
  · exact ⟨_, by rw [ite_eq_left hz]⟩
  · exact ⟨_, by rw [ite_eq_right hz, ite_eq_left h]⟩

/-- If the rounded magnitude is at most the largest finite magnitude and the
exact value is below `2 ^ 40`, the encoding is finite. -/
theorem roundScaledMode_fin_of_rounded_le (mode : RMode) (z : Int) (sa sb : Bool)
    (h1024 : 1024 ≤ z.natAbs) (h40 : z.natAbs < 2 ^ 40)
    (hm : (roundMode mode (2 ^ (Nat.log2 z.natAbs - 10)) z).natAbs ≤
      maxFiniteScaled) :
    ∃ v : SVal, roundScaledMode mode z sa sb = .fin v := by
  have hz : z ≠ 0 := by omega
  have hsmall : ¬ z.natAbs < 1024 := by omega
  have hm0 : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  have hloglt : Nat.log2 z.natAbs < 40 := (Nat.log2_lt hm0).mpr h40
  have he : Nat.log2 z.natAbs - 9 ≤ 30 := by omega
  unfold roundScaledMode
  rw [ite_eq_right hz, ite_eq_right hsmall]
  dsimp only
  by_cases hmant :
      2048 ≤ (roundMode mode (2 ^ (Nat.log2 z.natAbs - 10)) z).natAbs /
        2 ^ (Nat.log2 z.natAbs - 10)
  · have he1 : Nat.log2 z.natAbs - 9 + 1 ≤ 30 := by
      by_cases he30 : Nat.log2 z.natAbs - 9 = 30
      · have hexp : Nat.log2 z.natAbs - 10 = 29 := by omega
        have hq : 2 ^ (Nat.log2 z.natAbs - 10) = 2 ^ 29 := by rw [hexp]
        rw [hq] at hmant hm
        have hle := Nat.div_mul_le_self ((roundMode mode (2 ^ 29) z).natAbs) (2 ^ 29)
        have hmul : 2 ^ 40 ≤
            (roundMode mode (2 ^ 29) z).natAbs / 2 ^ 29 * 2 ^ 29 := by
          have h2 := Nat.mul_le_mul_right (2 ^ 29) hmant
          have h4096 : 2048 * 2 ^ 29 = 2 ^ 40 := by decide
          omega
        have hmax : maxFiniteScaled < 2 ^ 40 := maxFiniteScaled_lt_two_pow_40
        omega
      · omega
    rw [ite_eq_left hmant, ite_eq_left he1]
    exact ⟨_, rfl⟩
  · rw [ite_eq_right hmant, ite_eq_left he]
    exact ⟨_, rfl⟩

/-- At or above `2 ^ 40` every directed mode is already in its overflow
branch, whatever the rounded mantissa does. -/
theorem roundScaledMode_eq_overflowMode_of_ge (mode : RMode) (z : Int) (sa sb : Bool)
    (hge : 2 ^ 40 ≤ z.natAbs) :
    roundScaledMode mode z sa sb = overflowMode mode (z < 0) := by
  have hz : z ≠ 0 := by
    intro h0
    rw [h0] at hge
    simp at hge
  have hsmall : ¬ z.natAbs < 1024 := by omega
  have hlog : 40 ≤ Nat.log2 z.natAbs := le_log2_of_two_pow_le _ 40 hge
  have he31 : ¬ (Nat.log2 z.natAbs - 9 + 1 ≤ 30) := by omega
  have he30 : ¬ (Nat.log2 z.natAbs - 9 ≤ 30) := by omega
  unfold roundScaledMode
  rw [ite_eq_right hz, ite_eq_right hsmall]
  simp [he31, he30]

/-- Toward zero never leaves the finite range: an overflowing magnitude
saturates at the largest finite magnitude with the same sign. -/
theorem roundScaledMode_towardZero_of_maxFiniteScaled_le (z : Int) (sa sb : Bool)
    (h : maxFiniteScaled ≤ z.natAbs) :
    roundScaledMode .towardZero z sa sb = .fin ⟨z < 0, maxFiniteScaled⟩ := by
  by_cases hsmall : z.natAbs < 1024
  · exfalso
    have h1024 : 1024 ≤ z.natAbs :=
      Nat.le_trans (by decide : 1024 ≤ maxFiniteScaled) h
    omega
  · by_cases h40 : z.natAbs < 2 ^ 40
    · exact roundScaledMode_binade30_fin .towardZero z sa sb h h40
        (roundTowardZero_natAbs_pow29 z h h40)
    · have hge : 2 ^ 40 ≤ z.natAbs := by omega
      rw [roundScaledMode_eq_overflowMode_of_ge .towardZero z sa sb hge]
      simp [overflowMode]

theorem roundScaledMode_towardZero_fin (z : Int) (sa sb : Bool) :
    ∃ v : SVal, roundScaledMode .towardZero z sa sb = .fin v := by
  by_cases hbig : maxFiniteScaled ≤ z.natAbs
  · rw [roundScaledMode_towardZero_of_maxFiniteScaled_le z sa sb hbig]
    exact ⟨_, rfl⟩
  · by_cases hsmall : z.natAbs < 1024
    · exact roundScaledMode_fin_of_lt_1024 .towardZero z sa sb hsmall
    · have h1024 : 1024 ≤ z.natAbs := by omega
      have h40 : z.natAbs < 2 ^ 40 := by
        have hlt := maxFiniteScaled_lt_two_pow_40
        omega
      apply roundScaledMode_fin_of_rounded_le .towardZero z sa sb h1024 h40
      show (roundTowardZero (2 ^ (Nat.log2 z.natAbs - 10)) z).natAbs ≤
        maxFiniteScaled
      rw [roundTowardZero_natAbs_eq]
      exact Nat.le_trans (roundDownNat_le _ _) (by omega)

/-- Downward rounding of a nonnegative value saturates at `+65504`. -/
theorem roundScaledMode_down_of_maxFiniteScaled_le_nonneg (z : Int) (sa sb : Bool)
    (hz : ¬ z < 0) (h : maxFiniteScaled ≤ z.natAbs) :
    roundScaledMode .down z sa sb = .fin ⟨false, maxFiniteScaled⟩ := by
  have hz0 : 0 ≤ z := by omega
  by_cases h40 : z.natAbs < 2 ^ 40
  · have hres := roundScaledMode_binade30_fin .down z sa sb h h40
      (roundDown_natAbs_pow29_nonneg z hz0 h h40)
    simpa [hz] using hres
  · have hge : 2 ^ 40 ≤ z.natAbs := by omega
    rw [roundScaledMode_eq_overflowMode_of_ge .down z sa sb hge]
    simp [overflowMode, hz]

/-- Downward rounding of a negative value goes to `-inf` exactly when the
magnitude exceeds `65504`. -/
theorem roundScaledMode_down_of_maxFiniteScaled_lt_neg (z : Int) (sa sb : Bool)
    (hz : z < 0) (h : maxFiniteScaled < z.natAbs) :
    roundScaledMode .down z sa sb = .inf true := by
  have hz0 : ¬ 0 ≤ z := by omega
  by_cases h40 : z.natAbs < 2 ^ 40
  · have hle : maxFiniteScaled ≤ z.natAbs := Nat.le_of_lt h
    have hres := roundScaledMode_binade30_inf .down z sa sb hle h40
      (roundDown_natAbs_pow29_neg z hz0 h h40)
    simpa [overflowMode, hz] using hres
  · have hge : 2 ^ 40 ≤ z.natAbs := by omega
    rw [roundScaledMode_eq_overflowMode_of_ge .down z sa sb hge]
    simp [overflowMode, hz]

/-- Upward rounding of a nonnegative value goes to `+inf` exactly when the
magnitude exceeds `65504`. -/
theorem roundScaledMode_up_of_maxFiniteScaled_lt_nonneg (z : Int) (sa sb : Bool)
    (hz : ¬ z < 0) (h : maxFiniteScaled < z.natAbs) :
    roundScaledMode .up z sa sb = .inf false := by
  have hz0 : 0 ≤ z := by omega
  by_cases h40 : z.natAbs < 2 ^ 40
  · have hle : maxFiniteScaled ≤ z.natAbs := Nat.le_of_lt h
    have hres := roundScaledMode_binade30_inf .up z sa sb hle h40
      (roundUp_natAbs_pow29_nonneg z hz0 h h40)
    simpa [overflowMode, hz] using hres
  · have hge : 2 ^ 40 ≤ z.natAbs := by omega
    rw [roundScaledMode_eq_overflowMode_of_ge .up z sa sb hge]
    simp [overflowMode, hz]

/-- Upward rounding of a negative value saturates at `-65504`. -/
theorem roundScaledMode_up_of_maxFiniteScaled_le_neg (z : Int) (sa sb : Bool)
    (hz : z < 0) (h : maxFiniteScaled ≤ z.natAbs) :
    roundScaledMode .up z sa sb = .fin ⟨true, maxFiniteScaled⟩ := by
  have hz0 : ¬ 0 ≤ z := by omega
  by_cases h40 : z.natAbs < 2 ^ 40
  · have hres := roundScaledMode_binade30_fin .up z sa sb h h40
      (roundUp_natAbs_pow29_neg z hz0 h h40)
    simpa [hz] using hres
  · have hge : 2 ^ 40 ≤ z.natAbs := by omega
    rw [roundScaledMode_eq_overflowMode_of_ge .up z sa sb hge]
    simp [overflowMode, hz]

/-- Below the `65504` threshold, up and down are still finite.  Together with
the strict threshold lemmas this pins the threshold exactly. -/
theorem roundScaledMode_up_fin_of_le_maxFiniteScaled (z : Int) (sa sb : Bool)
    (h : z.natAbs ≤ maxFiniteScaled) :
    ∃ v : SVal, roundScaledMode .up z sa sb = .fin v := by
  by_cases hsmall : z.natAbs < 1024
  · exact roundScaledMode_fin_of_lt_1024 .up z sa sb hsmall
  · have h1024 : 1024 ≤ z.natAbs := by omega
    have h40 : z.natAbs < 2 ^ 40 := by
      have hlt := maxFiniteScaled_lt_two_pow_40
      omega
    apply roundScaledMode_fin_of_rounded_le .up z sa sb h1024 h40
    by_cases hz : 0 ≤ z
    · have htoNat : z.toNat = z.natAbs := by
        have h1 : (z.toNat : Int) = z := Int.toNat_of_nonneg hz
        have h2 : (z.natAbs : Int) = z := Int.natAbs_of_nonneg hz
        exact Int.ofNat.inj (h1.trans h2.symm)
      show (roundUp (2 ^ (Nat.log2 z.natAbs - 10)) z).natAbs ≤ maxFiniteScaled
      rw [roundUp, ite_eq_left hz, htoNat, Int.natAbs_natCast]
      exact roundUpNat_dest_le_maxFiniteScaled z.natAbs h1024 h
    · have hz0 : 0 ≤ -z := by omega
      have htoNat : (-z).toNat = z.natAbs := by
        have h1 : (((-z).toNat : Int)) = -z := Int.toNat_of_nonneg hz0
        have h2 : ((z.natAbs : Int)) = -z := by
          rw [← Int.natAbs_neg z]
          exact Int.natAbs_of_nonneg hz0
        exact Int.ofNat.inj (h1.trans h2.symm)
      show (roundUp (2 ^ (Nat.log2 z.natAbs - 10)) z).natAbs ≤ maxFiniteScaled
      rw [roundUp, ite_eq_right hz, htoNat, Int.natAbs_neg, Int.natAbs_natCast]
      exact Nat.le_trans (roundDownNat_le _ _) h

theorem roundScaledMode_down_fin_of_le_maxFiniteScaled (z : Int) (sa sb : Bool)
    (h : z.natAbs ≤ maxFiniteScaled) :
    ∃ v : SVal, roundScaledMode .down z sa sb = .fin v := by
  by_cases hsmall : z.natAbs < 1024
  · exact roundScaledMode_fin_of_lt_1024 .down z sa sb hsmall
  · have h1024 : 1024 ≤ z.natAbs := by omega
    have h40 : z.natAbs < 2 ^ 40 := by
      have hlt := maxFiniteScaled_lt_two_pow_40
      omega
    apply roundScaledMode_fin_of_rounded_le .down z sa sb h1024 h40
    by_cases hz : 0 ≤ z
    · have htoNat : z.toNat = z.natAbs := by
        have h1 : (z.toNat : Int) = z := Int.toNat_of_nonneg hz
        have h2 : (z.natAbs : Int) = z := Int.natAbs_of_nonneg hz
        exact Int.ofNat.inj (h1.trans h2.symm)
      show (roundDown (2 ^ (Nat.log2 z.natAbs - 10)) z).natAbs ≤ maxFiniteScaled
      rw [roundDown, ite_eq_left hz, htoNat, Int.natAbs_natCast]
      exact Nat.le_trans (roundDownNat_le _ _) h
    · have hz0 : 0 ≤ -z := by omega
      have htoNat : (-z).toNat = z.natAbs := by
        have h1 : (((-z).toNat : Int)) = -z := Int.toNat_of_nonneg hz0
        have h2 : ((z.natAbs : Int)) = -z := by
          rw [← Int.natAbs_neg z]
          exact Int.natAbs_of_nonneg hz0
        exact Int.ofNat.inj (h1.trans h2.symm)
      show (roundDown (2 ^ (Nat.log2 z.natAbs - 10)) z).natAbs ≤ maxFiniteScaled
      rw [roundDown, ite_eq_right hz, htoNat, Int.natAbs_neg, Int.natAbs_natCast]
      exact roundUpNat_dest_le_maxFiniteScaled z.natAbs h1024 h

/-! ## Overflow at the value level -/

theorem addDirected_fin_overflow_towardZero (x y : SVal)
    (h : maxFiniteScaled ≤ (x.signed + y.signed).natAbs) :
    addDirected .towardZero (.fin x) (.fin y) =
      .fin ⟨(x.signed + y.signed) < 0, maxFiniteScaled⟩ :=
  roundScaledMode_towardZero_of_maxFiniteScaled_le _ _ _ h

theorem addDirected_fin_overflow_down_nonneg (x y : SVal)
    (hz : ¬ (x.signed + y.signed) < 0)
    (h : maxFiniteScaled ≤ (x.signed + y.signed).natAbs) :
    addDirected .down (.fin x) (.fin y) = .fin ⟨false, maxFiniteScaled⟩ :=
  roundScaledMode_down_of_maxFiniteScaled_le_nonneg _ _ _ hz h

theorem addDirected_fin_overflow_down_neg (x y : SVal)
    (hz : (x.signed + y.signed) < 0)
    (h : maxFiniteScaled < (x.signed + y.signed).natAbs) :
    addDirected .down (.fin x) (.fin y) = .inf true :=
  roundScaledMode_down_of_maxFiniteScaled_lt_neg _ _ _ hz h

theorem addDirected_fin_overflow_up_nonneg (x y : SVal)
    (hz : ¬ (x.signed + y.signed) < 0)
    (h : maxFiniteScaled < (x.signed + y.signed).natAbs) :
    addDirected .up (.fin x) (.fin y) = .inf false :=
  roundScaledMode_up_of_maxFiniteScaled_lt_nonneg _ _ _ hz h

theorem addDirected_fin_overflow_up_neg (x y : SVal)
    (hz : (x.signed + y.signed) < 0)
    (h : maxFiniteScaled ≤ (x.signed + y.signed).natAbs) :
    addDirected .up (.fin x) (.fin y) = .fin ⟨true, maxFiniteScaled⟩ :=
  roundScaledMode_up_of_maxFiniteScaled_le_neg _ _ _ hz h

/-! ## Worked bit-level examples -/

/-- Downward rounding on the two positive binade-2 ties: `2049` stays at
`0x0800` and `2051` stays at `0x0801`. -/
theorem fp16_directed_down_tie_bits :
    addDirected .down (decodeFull (0x0800 : Fp16)) (decodeFull (0x0001 : Fp16)) =
        decodeFull (0x0800 : Fp16) ∧
      addDirected .down (decodeFull (0x0801 : Fp16)) (decodeFull (0x0001 : Fp16)) =
        decodeFull (0x0801 : Fp16) := by
  constructor <;> decide

/-- Toward zero on the same ties: the magnitude truncates, so `2049` is
`0x0800` and `2051` is `0x0801`. -/
theorem fp16_directed_towardZero_tie_bits :
    addDirected .towardZero (decodeFull (0x0800 : Fp16))
        (decodeFull (0x0001 : Fp16)) = decodeFull (0x0800 : Fp16) ∧
      addDirected .towardZero (decodeFull (0x0801 : Fp16))
        (decodeFull (0x0001 : Fp16)) = decodeFull (0x0801 : Fp16) := by
  constructor <;> decide

/-- Upward rounding on the same ties: `2049` moves to `0x0801` and `2051` to
`0x0802`. -/
theorem fp16_directed_up_tie_bits :
    addDirected .up (decodeFull (0x0800 : Fp16)) (decodeFull (0x0001 : Fp16)) =
        decodeFull (0x0801 : Fp16) ∧
      addDirected .up (decodeFull (0x0801 : Fp16)) (decodeFull (0x0001 : Fp16)) =
        decodeFull (0x0802 : Fp16) := by
  constructor <;> decide

/-- Ties-to-even on the same ties picks `0x0800` for the even quotient and
`0x0802` for the odd one, so it agrees with down in the first case and with up
in the second. -/
theorem fp16_directed_even_tie_bits :
    addFull (decodeFull (0x0800 : Fp16)) (decodeFull (0x0001 : Fp16)) =
        decodeFull (0x0800 : Fp16) ∧
      addFull (decodeFull (0x0801 : Fp16)) (decodeFull (0x0001 : Fp16)) =
        decodeFull (0x0802 : Fp16) := by
  constructor <;> decide

/-- The smaller binade-2 tie: `0x0800 + 0x0001` is `2049`, which rounds down
and to even at `0x0800`, while upward rounding reaches `0x0801`. -/
theorem fp16_directed_tie_even_favours_down_bits :
    addDirected .down (decodeFull (0x0800 : Fp16)) (decodeFull (0x0001 : Fp16)) =
        decodeFull (0x0800 : Fp16) ∧
      addDirected .towardZero (decodeFull (0x0800 : Fp16))
          (decodeFull (0x0001 : Fp16)) = decodeFull (0x0800 : Fp16) ∧
      addDirected .up (decodeFull (0x0800 : Fp16)) (decodeFull (0x0001 : Fp16)) =
        decodeFull (0x0801 : Fp16) ∧
      addFull (decodeFull (0x0800 : Fp16)) (decodeFull (0x0001 : Fp16)) =
        decodeFull (0x0800 : Fp16) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The larger binade-2 tie: `0x0801 + 0x0001` is `2051`, which rounds down to
`0x0801`, while upward rounding and ties-to-even reach `0x0802`. -/
theorem fp16_directed_tie_even_favours_up_bits :
    addDirected .down (decodeFull (0x0801 : Fp16)) (decodeFull (0x0001 : Fp16)) =
        decodeFull (0x0801 : Fp16) ∧
      addDirected .towardZero (decodeFull (0x0801 : Fp16))
          (decodeFull (0x0001 : Fp16)) = decodeFull (0x0801 : Fp16) ∧
      addDirected .up (decodeFull (0x0801 : Fp16)) (decodeFull (0x0001 : Fp16)) =
        decodeFull (0x0802 : Fp16) ∧
      addFull (decodeFull (0x0801 : Fp16)) (decodeFull (0x0001 : Fp16)) =
        decodeFull (0x0802 : Fp16) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The negative tie `0x8801 + 0x8001` is `-2051`: downward rounding moves away
from zero to `0x8802`, while upward and toward-zero stay at `0x8801`. -/
theorem fp16_directed_tie_negative_bits :
    addDirected .down (decodeFull (0x8801 : Fp16)) (decodeFull (0x8001 : Fp16)) =
        decodeFull (0x8802 : Fp16) ∧
      addDirected .towardZero (decodeFull (0x8801 : Fp16))
          (decodeFull (0x8001 : Fp16)) = decodeFull (0x8801 : Fp16) ∧
      addDirected .up (decodeFull (0x8801 : Fp16)) (decodeFull (0x8001 : Fp16)) =
        decodeFull (0x8801 : Fp16) ∧
      addFull (decodeFull (0x8801 : Fp16)) (decodeFull (0x8001 : Fp16)) =
        decodeFull (0x8802 : Fp16) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- `65504 + 65504` overflows upward but saturates under toward-zero and
downward rounding. -/
theorem fp16_directed_overflow_positive_bits :
    addDirected .towardZero (decodeFull (0x7BFF : Fp16))
        (decodeFull (0x7BFF : Fp16)) = decodeFull (0x7BFF : Fp16) ∧
      addDirected .down (decodeFull (0x7BFF : Fp16))
          (decodeFull (0x7BFF : Fp16)) = decodeFull (0x7BFF : Fp16) ∧
      addDirected .up (decodeFull (0x7BFF : Fp16)) (decodeFull (0x7BFF : Fp16)) =
        decodeFull (0x7C00 : Fp16) ∧
      addFull (decodeFull (0x7BFF : Fp16)) (decodeFull (0x7BFF : Fp16)) =
        decodeFull (0x7C00 : Fp16) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The negative overflow is the mirror image: downward rounding goes to
`-inf`, while upward and toward-zero saturate at `0xFBFF`. -/
theorem fp16_directed_overflow_negative_bits :
    addDirected .towardZero (decodeFull (0xFBFF : Fp16))
        (decodeFull (0xFBFF : Fp16)) = decodeFull (0xFBFF : Fp16) ∧
      addDirected .up (decodeFull (0xFBFF : Fp16))
          (decodeFull (0xFBFF : Fp16)) = decodeFull (0xFBFF : Fp16) ∧
      addDirected .down (decodeFull (0xFBFF : Fp16))
          (decodeFull (0xFBFF : Fp16)) = decodeFull (0xFC00 : Fp16) ∧
      addFull (decodeFull (0xFBFF : Fp16)) (decodeFull (0xFBFF : Fp16)) =
        decodeFull (0xFC00 : Fp16) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The directed threshold is `65504`, not the ties-to-even threshold
`65520`: `65504 + 1` is finite under ties-to-even but overflows upward. -/
theorem fp16_directed_up_threshold_bits :
    addDirected .up (decodeFull (0x7BFF : Fp16)) (decodeFull (0x0001 : Fp16)) =
        decodeFull (0x7C00 : Fp16) ∧
      addDirected .down (decodeFull (0x7BFF : Fp16)) (decodeFull (0x0001 : Fp16)) =
        decodeFull (0x7BFF : Fp16) ∧
      addDirected .towardZero (decodeFull (0x7BFF : Fp16))
          (decodeFull (0x0001 : Fp16)) = decodeFull (0x7BFF : Fp16) ∧
      addFull (decodeFull (0x7BFF : Fp16)) (decodeFull (0x0001 : Fp16)) =
        decodeFull (0x7BFF : Fp16) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Counterexamples to natural claims -/

/-- Downward and toward-zero rounding differ on negative values: at quantum
`8`, `-5` goes to `-8` and to `0` respectively. -/
theorem roundDown_ne_roundTowardZero_neg :
    roundDown 8 (-5) = -8 ∧ roundTowardZero 8 (-5) = 0 := by
  constructor <;> decide

/-- Ties-to-even is not downward rounding: at quantum `8`, `45` goes to `48`
under ties-to-even and to `40` downward. -/
theorem roundEven_ne_roundDown :
    roundEven 8 45 = 48 ∧ roundDown 8 45 = 40 := by
  constructor <;> decide

/-- Ties-to-even is not upward rounding: at quantum `8`, `35` goes to `32`
under ties-to-even and to `40` upward. -/
theorem roundEven_ne_roundUp :
    roundEven 8 35 = 32 ∧ roundUp 8 35 = 40 := by
  constructor <;> decide

/-- Directed rounding is not the ties-to-even result in general: on
`0x0801 + 0x0001` downward rounding stays at `0x0801`. -/
theorem directed_down_ne_addFull :
    addDirected .down (decodeFull (0x0801 : Fp16)) (decodeFull (0x0001 : Fp16)) ≠
      addFull (decodeFull (0x0801 : Fp16)) (decodeFull (0x0001 : Fp16)) := by
  decide
