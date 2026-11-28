-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.IeeeFp16Fma
public import Intel.IeeeFp16Directed

@[expose] public section

/-!
# Directed-rounding fused multiply-add for fp16

Stage 170 proves the finite fp16 fused multiply-add value model with one
round-to-nearest-even rounding and states explicitly that directed rounding is
not modelled. This module closes that gap: the exact fused sum

`fmaScaled x y c = x.signed * y.signed + c.signed * 2 ^ 24`

is already an integer in units of `2 ^ -48`, and stage-170's selector
`fmaDestQuantum` gives the destination quantum at that scale. Applying
stage-159's `roundMode` at that quantum gives directed fused results.

- `fmaRoundedFineMode` / `fmaRoundMagMode`: stage-159 directed rounding of the
  exact fused sum at the stage-170 destination quantum, before and after the
  scale `2 ^ 24` is divided out.
- `roundFmaScaledMode`: one directed rounding of the exact fused sum, with
  stage-159's `overflowMode` table for results at or above `2 ^ 64`.
- `fmaDirected`: value-level fp16 FMA under a directed mode. The special-value
  rules are exactly stage-170's `fma`; only the final finite rounding differs.
- `fmaDirectedThreshold = maxFiniteScaled * 2 ^ 24 = 2047 * 2 ^ 53`: the exact
  fine-scale threshold at which a directed mode can leave the finite range.
- `fmaDirected_fixed_of_dest_dvd`: exact destination-grid fused sums are fixed
  by every mode and agree with stage-170's ties-to-even `fma`.
- `fmaDirected_tie_*_bits`: bit-level ties where down, up and even split.
- the overflow table: toward zero and the directions pointing toward zero
  saturate at `±65504`; up on a positive sum and down on a negative sum go to
  `±inf` exactly above `65504 * 2 ^ 24`.
- `fmaDirected_product_zero_eq_addDirected`: when the product is zero the
  directed FMA agrees with stage-159's directed addition.
- `fmaDirected_up_ne_split`: directed FMA is not "round the product, then add
  directed", mirroring the stage-170 double-rounding counterexample.

## Proved class

All three operands are finite `SVal`s. The directed finite-value theorems are
proved for exact fused sums with magnitude at most `fmaDirectedThreshold`;
overflow theorems are proved for every integer magnitude, including the
stage-170 product-dominated range up to `maxFmaScaled < 2 ^ 81`. Subnormal and
zero operands are included. Ties-to-even agreement uses stage-170's `fma_fin`
below `fmaOverflowThreshold`.

## Outside the model

Exception traps and masks, sticky per-lane state, tininess-before-rounding,
flush-to-zero and denormals-are-zero are not modelled. Directed rounding is
proved on the single-rounding value semantics; hardware timing and fusion
across instructions are out of scope. NaN payload choice is stage-170's
left-biased quieting convention.

There are no new axioms, no `native_decide` and no `sorry`.
-/

namespace IntelGpu

/-! ## The directed fused threshold -/

/-- The exact fine-scale threshold for directed fused rounding: the largest
finite fp16 magnitude `65504` translated from `2 ^ -24` to `2 ^ -48` units. -/
def fmaDirectedThreshold : Nat := maxFiniteScaled * 2 ^ 24

theorem fmaDirectedThreshold_value :
    fmaDirectedThreshold = 2047 * 2 ^ 53 := by
  unfold fmaDirectedThreshold maxFiniteScaled
  decide

theorem fmaDirectedThreshold_lt_fmaOverflowThreshold :
    fmaDirectedThreshold < fmaOverflowThreshold := by
  rw [fmaDirectedThreshold_value, fmaOverflowThreshold_value]
  decide

theorem fmaDirectedThreshold_lt_two_pow64 :
    fmaDirectedThreshold < 2 ^ 64 := by
  rw [fmaDirectedThreshold_value]
  have h : (2 : Nat) ^ 64 = 2048 * 2 ^ 53 := by decide
  omega

theorem two_pow64_eq_2048_mul_two_pow53 :
    (2 : Nat) ^ 64 = 2048 * 2 ^ 53 := by decide

/-! ## Directed rounding at the fused destination quantum -/

/-- Directed rounding of the exact fused sum at stage-170's destination
quantum, still in units of `2 ^ -48`.  The sign-aware stage-159 `roundMode`
handles negative sums, so down rounds away from zero and up toward zero. -/
def fmaRoundedFineMode (mode : RMode) (Z : Int) : Nat :=
  (roundMode mode (fmaDestQuantum Z.natAbs) Z).natAbs

/-- The directed fp16 magnitude of a fused sum in units of `2 ^ -24`. -/
def fmaRoundMagMode (mode : RMode) (Z : Int) : Nat :=
  fmaRoundedFineMode mode Z / 2 ^ 24

theorem fmaRoundedFineMode_dvd_two_pow24 (mode : RMode) (Z : Int) :
    (2 ^ 24 : Nat) ∣ fmaRoundedFineMode mode Z := by
  obtain ⟨k, hk⟩ := roundMode_natAbs_dvd mode (fmaDestQuantum Z.natAbs) Z
  rw [fmaRoundedFineMode, hk]
  exact Nat.dvd_trans (fmaDestQuantum_dvd_two_pow24 Z.natAbs) (Nat.dvd_mul_left _ _)

theorem fmaRoundMagMode_mul_two_pow24 (mode : RMode) (Z : Int) :
    fmaRoundMagMode mode Z * 2 ^ 24 = fmaRoundedFineMode mode Z := by
  unfold fmaRoundMagMode
  exact Nat.div_mul_cancel (fmaRoundedFineMode_dvd_two_pow24 mode Z)

/-- One directed rounding of the exact fused sum.  The result is finite when
the directed fine value is below the first unrepresentable fp16 magnitude
`2 ^ 64`; otherwise stage-159's per-mode overflow table is used. -/
def roundFmaScaledMode (mode : RMode) (Z : Int) (sm sc : Bool) : Fp16Val :=
  if Z = 0 then
    .fin { sign := zeroSign sm sc, mag := 0 }
  else if fmaRoundedFineMode mode Z < 2 ^ 64 then
    .fin { sign := Z < 0, mag := fmaRoundMagMode mode Z }
  else overflowMode mode (Z < 0)

/-! ## Scaling by `2 ^ 24` and signs -/

theorem zeroSign_comm (a b : Bool) : zeroSign a b = zeroSign b a := by
  unfold zeroSign
  rw [Bool.and_comm]

theorem mul_two_pow24_nonneg_iff (z : Int) :
    0 ≤ z * (2 ^ 24 : Nat) ↔ 0 ≤ z := by
  have hS : (0 : Int) < (2 ^ 24 : Nat) := by decide
  constructor
  · intro h
    by_cases hz : 0 ≤ z
    · exact hz
    · have hneg : z < 0 := by omega
      have hprod : z * (2 ^ 24 : Nat) < 0 := Int.mul_neg_of_neg_of_pos hneg hS
      omega
  · intro h
    exact Int.mul_nonneg h (Int.le_of_lt hS)

theorem mul_two_pow24_lt_zero_iff (z : Int) :
    z * (2 ^ 24 : Nat) < 0 ↔ z < 0 := by
  have hS : (0 : Int) < (2 ^ 24 : Nat) := by decide
  constructor
  · intro h
    by_cases hz : 0 ≤ z
    · have hprod : 0 ≤ z * (2 ^ 24 : Nat) := Int.mul_nonneg hz (Int.le_of_lt hS)
      omega
    · omega
  · intro h
    exact Int.mul_neg_of_neg_of_pos h hS

theorem mul_two_pow24_ne_zero (z : Int) :
    z * (2 ^ 24 : Nat) ≠ 0 ↔ z ≠ 0 := by
  constructor
  · intro h hz
    exact h (by rw [hz, Int.zero_mul])
  · intro hz hmul
    rcases (Int.mul_eq_zero.mp hmul) with h | h
    · exact hz h
    · exact absurd h (by decide)

theorem natAbs_mul_two_pow24 (z : Int) :
    (z * (2 ^ 24 : Nat)).natAbs = z.natAbs * 2 ^ 24 := by
  rw [Int.natAbs_mul, Int.natAbs_natCast]

/-- The sign of stage-159's directed rounding is the sign of its argument. -/
theorem SVal.signed_mk_roundMode (mode : RMode) (q : Nat) (z : Int) :
    (⟨z < 0, (roundMode mode q z).natAbs⟩ : SVal).signed =
      roundMode mode q z := by
  by_cases hz : 0 ≤ z
  · have hdec : decide (z < 0) = false := by simp [show ¬ z < 0 by omega]
    have hnonneg : 0 ≤ roundMode mode q z := by
      cases mode
      · show 0 ≤ roundTowardZero q z
        unfold roundTowardZero
        rw [ite_eq_left hz]
        exact Int.natCast_nonneg _
      · show 0 ≤ roundUp q z
        unfold roundUp
        rw [ite_eq_left hz]
        exact Int.natCast_nonneg _
      · show 0 ≤ roundDown q z
        unfold roundDown
        rw [ite_eq_left hz]
        exact Int.natCast_nonneg _
    rw [SVal.signed_mk]
    simp only [hdec, Bool.false_eq_true, ite_false]
    exact Int.natAbs_of_nonneg hnonneg
  · have hneg : z < 0 := by omega
    have hdec : decide (z < 0) = true := by simp [hneg]
    have hnonpos : roundMode mode q z ≤ 0 := by
      cases mode
      · show roundTowardZero q z ≤ 0
        unfold roundTowardZero
        rw [ite_eq_right (by omega : ¬ 0 ≤ z)]
        exact Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _)
      · show roundUp q z ≤ 0
        unfold roundUp
        rw [ite_eq_right (by omega : ¬ 0 ≤ z)]
        exact Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _)
      · show roundDown q z ≤ 0
        unfold roundDown
        rw [ite_eq_right (by omega : ¬ 0 ≤ z)]
        exact Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _)
    rw [SVal.signed_mk]
    simp only [hdec, ite_true]
    exact (Int.eq_neg_natAbs_of_nonpos hnonpos).symm

theorem roundMode_zero (mode : RMode) (q : Nat) : roundMode mode q 0 = 0 := by
  cases mode
  · show roundTowardZero q 0 = 0
    unfold roundTowardZero
    rw [ite_eq_left (show (0 : Int) ≤ 0 from Int.le_refl 0)]
    simp [roundTowardZeroNat_zero]
  · show roundUp q 0 = 0
    unfold roundUp
    rw [ite_eq_left (show (0 : Int) ≤ 0 from Int.le_refl 0)]
    simp [roundUpNat_zero]
  · show roundDown q 0 = 0
    unfold roundDown
    rw [ite_eq_left (show (0 : Int) ≤ 0 from Int.le_refl 0)]
    simp [roundDownNat_zero]

theorem fmaRoundedFineMode_zero (mode : RMode) :
    fmaRoundedFineMode mode 0 = 0 := by
  unfold fmaRoundedFineMode
  rw [roundMode_zero]
  rfl

/-- A nonzero fused sum below `2 ^ 64` is finite, and its signed coarse value
scaled back by `2 ^ 24` is exactly stage-159's directed rounding of the exact
fine sum. -/
theorem roundFmaScaledMode_fin_signed (mode : RMode) (Z : Int) (sm sc : Bool)
    (hz : Z ≠ 0) (hlt : fmaRoundedFineMode mode Z < 2 ^ 64) :
    roundFmaScaledMode mode Z sm sc =
        .fin ⟨Z < 0, fmaRoundMagMode mode Z⟩ ∧
      (⟨Z < 0, fmaRoundMagMode mode Z⟩ : SVal).signed * (2 ^ 24 : Nat) =
        roundMode mode (fmaDestQuantum Z.natAbs) Z := by
  constructor
  · unfold roundFmaScaledMode
    rw [ite_eq_right hz, ite_eq_left hlt]
  · have hmul := fmaRoundMagMode_mul_two_pow24 mode Z
    have hscale := SVal.signed_scale_mul (Z < 0) (fmaRoundMagMode mode Z)
      (fmaRoundedFineMode mode Z) hmul
    rw [hscale]
    exact SVal.signed_mk_roundMode mode (fmaDestQuantum Z.natAbs) Z

/-- Any fused sum whose directed fine rounding stays below `2 ^ 64` is finite,
and its signed value is the directed rounding of the exact fused sum. -/
theorem roundFmaScaledMode_fin_signed_of_lt_two_pow64 (mode : RMode) (Z : Int)
    (sm sc : Bool) (hlt : fmaRoundedFineMode mode Z < 2 ^ 64) :
    ∃ v : SVal, roundFmaScaledMode mode Z sm sc = .fin v ∧
      v.signed * (2 ^ 24 : Nat) =
        roundMode mode (fmaDestQuantum Z.natAbs) Z := by
  by_cases hz : Z = 0
  · subst hz
    refine ⟨⟨zeroSign sm sc, 0⟩, ?_, ?_⟩
    · unfold roundFmaScaledMode
      rw [ite_eq_left rfl]
    · rw [SVal.signed_mk]
      simp [roundMode_zero]
  · obtain ⟨hv, hsv⟩ := roundFmaScaledMode_fin_signed mode Z sm sc hz hlt
    exact ⟨_, hv, hsv⟩

/-- An exact destination-grid fused sum is fixed by every directed mode: the
rounding is the identity, so the signed value is the exact `2 ^ -48` sum. -/
theorem roundFmaScaledMode_fixed_of_dest_dvd (mode : RMode) (Z : Int)
    (sm sc : Bool) (hq : fmaDestQuantum Z.natAbs ∣ Z.natAbs)
    (hfin : Z.natAbs < 2 ^ 64) :
    ∃ v : SVal, roundFmaScaledMode mode Z sm sc = .fin v ∧
      v.signed * (2 ^ 24 : Nat) = Z := by
  have hfix : roundMode mode (fmaDestQuantum Z.natAbs) Z = Z :=
    roundMode_eq_self_of_natAbs_dvd mode _ Z hq
  have hR : fmaRoundedFineMode mode Z = Z.natAbs := by
    unfold fmaRoundedFineMode
    rw [hfix]
  have hlt : fmaRoundedFineMode mode Z < 2 ^ 64 := by
    rw [hR]
    exact hfin
  obtain ⟨v, hv, hsv⟩ :=
    roundFmaScaledMode_fin_signed_of_lt_two_pow64 mode Z sm sc hlt
  exact ⟨v, hv, by rw [hsv, hfix]⟩

/-! ## Value-level directed fused multiply-add -/

/-- Value-level fp16 fused multiply-add under a directed rounding mode.  The
NaN, infinity and `0 * inf` rules are stage-170's `fma` unchanged; only the
final rounding of a finite fused sum is directed. -/
def fmaDirected : RMode → Fp16Val → Fp16Val → Fp16Val → Fp16Val
  | _, .nan ng p _, _, _ => .nan ng p true
  | _, _, .nan ng p _, _ => .nan ng p true
  | _, _, _, .nan ng p _ => .nan ng p true
  | _, .inf a, .inf b, c => addInfProduct (a != b) c
  | _, .inf a, .fin y, c =>
      if y.mag = 0 then .nan false 0 true else addInfProduct (a != y.sign) c
  | _, .fin x, .inf b, c =>
      if x.mag = 0 then .nan false 0 true else addInfProduct (x.sign != b) c
  | _, .fin _, .fin _, .inf c => .inf c
  | mode, .fin x, .fin y, .fin c =>
      roundFmaScaledMode mode (fmaScaled x y c) (productSign x y) c.sign

theorem fmaDirected_fin_fin (mode : RMode) (x y c : SVal) :
    fmaDirected mode (.fin x) (.fin y) (.fin c) =
      roundFmaScaledMode mode (fmaScaled x y c) (productSign x y) c.sign := rfl

/-! ## Bounds, fixed points and ties-to-even agreement -/

theorem roundEvenNat_eq_self_of_dvd (q n : Nat) (hq : 0 < q) (h : q ∣ n) :
    roundEvenNat q n = n := by
  rcases roundEvenNat_eq_down_or_up q n hq with hd | hu
  · rw [hd, roundDownNat_eq_self_of_dvd q n h]
  · rw [hu, roundUpNat_eq_self_of_dvd q n h]

/-- Downward rounding never exceeds the exact fused sum. -/
theorem fmaRoundMode_down_le (Z : Int) :
    roundMode .down (fmaDestQuantum Z.natAbs) Z ≤ Z :=
  roundDown_le _ (fmaDestQuantum_pos Z.natAbs) Z

/-- Upward rounding never falls below the exact fused sum. -/
theorem fmaRoundMode_le_up (Z : Int) :
    Z ≤ roundMode .up (fmaDestQuantum Z.natAbs) Z :=
  le_roundUp _ (fmaDestQuantum_pos Z.natAbs) Z

/-- Toward-zero rounding sits between downward and upward rounding. -/
theorem fmaRoundMode_towardZero_between (Z : Int) :
    roundMode .down (fmaDestQuantum Z.natAbs) Z ≤
        roundMode .towardZero (fmaDestQuantum Z.natAbs) Z ∧
      roundMode .towardZero (fmaDestQuantum Z.natAbs) Z ≤
        roundMode .up (fmaDestQuantum Z.natAbs) Z :=
  ⟨roundDown_le_roundTowardZero _ (fmaDestQuantum_pos Z.natAbs) Z,
    roundTowardZero_le_roundUp _ (fmaDestQuantum_pos Z.natAbs) Z⟩

/-- Ties-to-even is bracketed by the directed results at the fused quantum. -/
theorem fmaRoundMode_even_between (Z : Int) :
    roundDown (fmaDestQuantum Z.natAbs) Z ≤
        roundEven (fmaDestQuantum Z.natAbs) Z ∧
      roundEven (fmaDestQuantum Z.natAbs) Z ≤
        roundUp (fmaDestQuantum Z.natAbs) Z :=
  roundEven_between_directed _ (fmaDestQuantum_pos Z.natAbs) Z

/-- On the destination grid every mode fixes the exact fused sum, and hence
agrees with stage-170's ties-to-even `fma` below the overflow threshold. -/
theorem fmaDirected_eq_fma_of_dest_dvd (mode : RMode) (x y c : SVal)
    (hq : fmaDestQuantum (fmaScaled x y c).natAbs ∣ (fmaScaled x y c).natAbs)
    (hfin : (fmaScaled x y c).natAbs < fmaOverflowThreshold) :
    fmaDirected mode (.fin x) (.fin y) (.fin c) =
      fma (.fin x) (.fin y) (.fin c) := by
  let Z := fmaScaled x y c
  have hqpos : 0 < fmaDestQuantum Z.natAbs := fmaDestQuantum_pos Z.natAbs
  have hfix : roundMode mode (fmaDestQuantum Z.natAbs) Z = Z :=
    roundMode_eq_self_of_natAbs_dvd mode _ Z hq
  have hRfix : fmaRoundedFineMode mode Z = Z.natAbs := by
    unfold fmaRoundedFineMode
    rw [hfix]
  have hEven : fmaRoundedFine Z.natAbs = Z.natAbs := by
    unfold fmaRoundedFine
    exact roundEvenNat_eq_self_of_dvd _ _ hqpos hq
  rw [fmaDirected_fin_fin, fma_fin_fin_fin]
  by_cases hz : Z = 0
  · unfold roundFmaScaledMode rneFmaScaled
    rw [ite_eq_left hz, ite_eq_left hz]
  · have hlt : fmaRoundedFineMode mode Z < 2 ^ 64 := by
      rw [hRfix]
      change (fmaScaled x y c).natAbs < 2 ^ 64
      exact Nat.lt_trans hfin fmaOverflowThreshold_lt_two_pow64
    unfold roundFmaScaledMode rneFmaScaled
    rw [ite_eq_right hz, ite_eq_right hz, ite_eq_left hlt,
      ite_eq_left hfin]
    unfold fmaRoundMagMode fmaRoundMag
    rw [hRfix, hEven]

/-! ## Overflow arithmetic at the fused scale -/

theorem fmaDestQuantum_mul_1024_eq_two_pow_log2 (m : Nat) (h : 2 ^ 34 ≤ m) :
    1024 * fmaDestQuantum m = 2 ^ Nat.log2 m := by
  rw [fmaDestQuantum_of_ge h]
  have hm0 : m ≠ 0 := by omega
  have hlog : 10 ≤ Nat.log2 m := by
    have := le_log2_of_two_pow34_le h
    omega
  calc
    1024 * 2 ^ (Nat.log2 m - 10) =
        2 ^ 10 * 2 ^ (Nat.log2 m - 10) := by
      rw [show (1024 : Nat) = 2 ^ 10 by decide]
    _ = 2 ^ (10 + (Nat.log2 m - 10)) := by rw [Nat.pow_add]
    _ = 2 ^ Nat.log2 m := by
      congr 1
      omega

theorem le_roundDownNat_of_1024_mul_le (q m : Nat) (hq : 0 < q)
    (h : 1024 * q ≤ m) :
    1024 * q ≤ roundDownNat q m := by
  unfold roundDownNat
  exact Nat.mul_le_mul_right q ((Nat.le_div_iff_mul_le hq).mpr h)

theorem le_roundUpNat_of_1024_mul_le (q m : Nat) (hq : 0 < q)
    (h : 1024 * q ≤ m) :
    1024 * q ≤ roundUpNat q m :=
  Nat.le_trans (le_roundDownNat_of_1024_mul_le q m hq h)
    (roundDownNat_le_roundUpNat q m)

theorem toNat_eq_natAbs_of_nonneg {z : Int} (hz : 0 ≤ z) :
    z.toNat = z.natAbs := by
  apply Int.ofNat_inj.mp
  rw [Int.toNat_of_nonneg hz, Int.natAbs_of_nonneg hz]

theorem toNat_neg_eq_natAbs_of_neg {z : Int} (hz : ¬ 0 ≤ z) :
    (-z).toNat = z.natAbs := by
  have hz0 : 0 ≤ -z := by omega
  apply Int.ofNat_inj.mp
  rw [Int.toNat_of_nonneg hz0, ← Int.natAbs_of_nonneg hz0, Int.natAbs_neg]

/-- Every directed mode rounds by at least `1024` destination quanta when the
magnitude already reaches that many quanta. -/
theorem le_roundMode_natAbs_of_1024_mul_le (mode : RMode) (q : Nat) (hq : 0 < q)
    (z : Int) (h : 1024 * q ≤ z.natAbs) :
    1024 * q ≤ (roundMode mode q z).natAbs := by
  by_cases hz : 0 ≤ z
  · have hto := toNat_eq_natAbs_of_nonneg hz
    cases mode
    · show 1024 * q ≤ (roundTowardZero q z).natAbs
      unfold roundTowardZero
      rw [ite_eq_left hz, hto, Int.natAbs_natCast]
      exact le_roundDownNat_of_1024_mul_le q z.natAbs hq h
    · show 1024 * q ≤ (roundUp q z).natAbs
      unfold roundUp
      rw [ite_eq_left hz, hto, Int.natAbs_natCast]
      exact le_roundUpNat_of_1024_mul_le q z.natAbs hq h
    · show 1024 * q ≤ (roundDown q z).natAbs
      unfold roundDown
      rw [ite_eq_left hz, hto, Int.natAbs_natCast]
      exact le_roundDownNat_of_1024_mul_le q z.natAbs hq h
  · have hto := toNat_neg_eq_natAbs_of_neg hz
    cases mode
    · show 1024 * q ≤ (roundTowardZero q z).natAbs
      unfold roundTowardZero
      rw [ite_eq_right hz, hto, Int.natAbs_neg, Int.natAbs_natCast]
      exact le_roundDownNat_of_1024_mul_le q z.natAbs hq h
    · show 1024 * q ≤ (roundUp q z).natAbs
      unfold roundUp
      rw [ite_eq_right hz, hto, Int.natAbs_neg, Int.natAbs_natCast]
      exact le_roundDownNat_of_1024_mul_le q z.natAbs hq h
    · show 1024 * q ≤ (roundDown q z).natAbs
      unfold roundDown
      rw [ite_eq_right hz, hto, Int.natAbs_neg, Int.natAbs_natCast]
      exact le_roundUpNat_of_1024_mul_le q z.natAbs hq h

/-- Above `2 ^ 64` every direction is already in its overflow branch. -/
theorem two_pow64_le_fmaRoundedFineMode_of_ge (mode : RMode) (Z : Int)
    (hge : 2 ^ 64 ≤ Z.natAbs) :
    2 ^ 64 ≤ fmaRoundedFineMode mode Z := by
  have h34 : 2 ^ 34 ≤ Z.natAbs := by
    have hpow : (2 : Nat) ^ 34 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  have hqpos := fmaDestQuantum_pos Z.natAbs
  have hpow := fmaDestQuantum_mul_1024_eq_two_pow_log2 Z.natAbs h34
  have hlog : 64 ≤ Nat.log2 Z.natAbs := le_log2_of_two_pow_le _ 64 hge
  have hbig : 2 ^ 64 ≤ 1024 * fmaDestQuantum Z.natAbs := by
    rw [hpow]
    exact Nat.pow_le_pow_right (by decide) hlog
  have hle := le_roundMode_natAbs_of_1024_mul_le mode _ hqpos Z
    (fmaDestQuantum_mul_1024_le Z.natAbs h34)
  unfold fmaRoundedFineMode
  omega

theorem roundFmaScaledMode_eq_overflowMode_of_ge (mode : RMode) (Z : Int)
    (sm sc : Bool) (hge : 2 ^ 64 ≤ Z.natAbs) :
    roundFmaScaledMode mode Z sm sc = overflowMode mode (Z < 0) := by
  have hz : Z ≠ 0 := by
    intro h
    rw [h] at hge
    simp at hge
  have hnot : ¬ fmaRoundedFineMode mode Z < 2 ^ 64 := by
    have := two_pow64_le_fmaRoundedFineMode_of_ge mode Z hge
    omega
  unfold roundFmaScaledMode
  rw [ite_eq_right hz, ite_eq_right hnot]

theorem fmaDestQuantum_of_threshold_le_lt_two_pow64 {m : Nat}
    (hlo : fmaDirectedThreshold ≤ m) (hhi : m < 2 ^ 64) :
    fmaDestQuantum m = 2 ^ 53 := by
  have h34 : 2 ^ 34 ≤ m := by
    have h : (2 : Nat) ^ 34 ≤ fmaDirectedThreshold := by
      rw [fmaDirectedThreshold_value]
      decide
    omega
  rw [fmaDestQuantum_of_ge h34]
  have hm0 : m ≠ 0 := by omega
  have hlog : Nat.log2 m = 63 := by
    rw [Nat.log2_eq_iff hm0]
    constructor
    · have h63 : (2 : Nat) ^ 63 ≤ fmaDirectedThreshold := by
        rw [fmaDirectedThreshold_value]
        decide
      omega
    · simpa using hhi
  rw [hlog]

theorem roundDownNat_two_pow53_of_threshold_le_lt_two_pow64 {m : Nat}
    (hlo : fmaDirectedThreshold ≤ m) (hhi : m < 2 ^ 64) :
    roundDownNat (2 ^ 53) m = fmaDirectedThreshold := by
  have hdiv : m / 2 ^ 53 = 2047 := by
    apply Nat.div_eq_of_lt_le
    · rw [fmaDirectedThreshold_value] at hlo
      exact hlo
    · rw [← two_pow64_eq_2048_mul_two_pow53]
      exact hhi
  unfold roundDownNat
  rw [hdiv]
  exact fmaDirectedThreshold_value.symm

theorem roundUpNat_two_pow53_of_threshold_lt_lt_two_pow64 {m : Nat}
    (hlo : fmaDirectedThreshold < m) (hhi : m < 2 ^ 64) :
    roundUpNat (2 ^ 53) m = 2 ^ 64 := by
  have hle : fmaDirectedThreshold ≤ m := Nat.le_of_lt hlo
  have hdiv : m / 2 ^ 53 = 2047 := by
    apply Nat.div_eq_of_lt_le
    · rw [fmaDirectedThreshold_value] at hle
      exact hle
    · rw [← two_pow64_eq_2048_mul_two_pow53]
      exact hhi
  have hdm := Nat.div_add_mod m (2 ^ 53)
  rw [hdiv, Nat.mul_comm (2 ^ 53) 2047] at hdm
  have hmod : m % 2 ^ 53 ≠ 0 := by
    intro h0
    rw [h0, Nat.add_zero] at hdm
    rw [fmaDirectedThreshold_value] at hlo
    omega
  unfold roundUpNat
  rw [hdiv, ite_eq_right hmod]

theorem roundUpNat_two_pow53_threshold :
    roundUpNat (2 ^ 53) fmaDirectedThreshold = fmaDirectedThreshold := by
  rw [fmaDirectedThreshold_value]
  exact roundUpNat_eq_self_of_dvd _ _ ⟨2047, by rw [Nat.mul_comm]⟩

theorem fmaRoundMagMode_eq_maxFinite_of_fine_eq_threshold (mode : RMode)
    (Z : Int) (h : fmaRoundedFineMode mode Z = fmaDirectedThreshold) :
    fmaRoundMagMode mode Z = maxFiniteScaled := by
  unfold fmaRoundMagMode
  rw [show fmaRoundedFineMode mode Z = maxFiniteScaled * 2 ^ 24 from h]
  exact Nat.mul_div_cancel maxFiniteScaled (by decide : 0 < 2 ^ 24)

theorem fmaRoundedFineMode_towardZero_top (Z : Int)
    (hlo : fmaDirectedThreshold ≤ Z.natAbs) (hhi : Z.natAbs < 2 ^ 64) :
    fmaRoundedFineMode .towardZero Z = fmaDirectedThreshold := by
  have hq := fmaDestQuantum_of_threshold_le_lt_two_pow64 hlo hhi
  have hfloor := roundDownNat_two_pow53_of_threshold_le_lt_two_pow64 hlo hhi
  unfold fmaRoundedFineMode
  rw [hq]
  by_cases hz : 0 ≤ Z
  · have hto := toNat_eq_natAbs_of_nonneg hz
    show (roundTowardZero (2 ^ 53) Z).natAbs = fmaDirectedThreshold
    unfold roundTowardZero
    rw [ite_eq_left hz, hto, Int.natAbs_natCast]
    simpa [roundTowardZeroNat, roundDownNat] using hfloor
  · have hto := toNat_neg_eq_natAbs_of_neg hz
    show (roundTowardZero (2 ^ 53) Z).natAbs = fmaDirectedThreshold
    unfold roundTowardZero
    rw [ite_eq_right hz, hto, Int.natAbs_neg, Int.natAbs_natCast]
    simpa [roundTowardZeroNat, roundDownNat] using hfloor

theorem fmaRoundedFineMode_down_top_nonneg (Z : Int) (hz : ¬ Z < 0)
    (hlo : fmaDirectedThreshold ≤ Z.natAbs) (hhi : Z.natAbs < 2 ^ 64) :
    fmaRoundedFineMode .down Z = fmaDirectedThreshold := by
  have hz0 : 0 ≤ Z := by omega
  have hq := fmaDestQuantum_of_threshold_le_lt_two_pow64 hlo hhi
  have hfloor := roundDownNat_two_pow53_of_threshold_le_lt_two_pow64 hlo hhi
  unfold fmaRoundedFineMode
  rw [hq]
  show (roundDown (2 ^ 53) Z).natAbs = fmaDirectedThreshold
  unfold roundDown
  rw [ite_eq_left hz0, toNat_eq_natAbs_of_nonneg hz0, Int.natAbs_natCast, hfloor]

theorem fmaRoundedFineMode_down_top_neg_lt (Z : Int) (hz : Z < 0)
    (hlo : fmaDirectedThreshold < Z.natAbs) (hhi : Z.natAbs < 2 ^ 64) :
    fmaRoundedFineMode .down Z = 2 ^ 64 := by
  have hz0 : ¬ 0 ≤ Z := by omega
  have hq := fmaDestQuantum_of_threshold_le_lt_two_pow64 (Nat.le_of_lt hlo) hhi
  have hceil := roundUpNat_two_pow53_of_threshold_lt_lt_two_pow64 hlo hhi
  unfold fmaRoundedFineMode
  rw [hq]
  show (roundDown (2 ^ 53) Z).natAbs = 2 ^ 64
  unfold roundDown
  rw [ite_eq_right hz0, toNat_neg_eq_natAbs_of_neg hz0, Int.natAbs_neg,
    Int.natAbs_natCast, hceil]

theorem fmaRoundedFineMode_up_top_nonneg_lt (Z : Int) (hz : ¬ Z < 0)
    (hlo : fmaDirectedThreshold < Z.natAbs) (hhi : Z.natAbs < 2 ^ 64) :
    fmaRoundedFineMode .up Z = 2 ^ 64 := by
  have hz0 : 0 ≤ Z := by omega
  have hq := fmaDestQuantum_of_threshold_le_lt_two_pow64 (Nat.le_of_lt hlo) hhi
  have hceil := roundUpNat_two_pow53_of_threshold_lt_lt_two_pow64 hlo hhi
  unfold fmaRoundedFineMode
  rw [hq]
  show (roundUp (2 ^ 53) Z).natAbs = 2 ^ 64
  unfold roundUp
  rw [ite_eq_left hz0, toNat_eq_natAbs_of_nonneg hz0, Int.natAbs_natCast, hceil]

theorem fmaRoundedFineMode_up_top_neg (Z : Int) (hz : Z < 0)
    (hlo : fmaDirectedThreshold ≤ Z.natAbs) (hhi : Z.natAbs < 2 ^ 64) :
    fmaRoundedFineMode .up Z = fmaDirectedThreshold := by
  have hz0 : ¬ 0 ≤ Z := by omega
  have hq := fmaDestQuantum_of_threshold_le_lt_two_pow64 hlo hhi
  have hfloor := roundDownNat_two_pow53_of_threshold_le_lt_two_pow64 hlo hhi
  unfold fmaRoundedFineMode
  rw [hq]
  show (roundUp (2 ^ 53) Z).natAbs = fmaDirectedThreshold
  unfold roundUp
  rw [ite_eq_right hz0, toNat_neg_eq_natAbs_of_neg hz0, Int.natAbs_neg,
    Int.natAbs_natCast, hfloor]

theorem roundFmaScaledMode_towardZero_top (Z : Int) (sm sc : Bool)
    (hlo : fmaDirectedThreshold ≤ Z.natAbs) (hhi : Z.natAbs < 2 ^ 64) :
    roundFmaScaledMode .towardZero Z sm sc =
      .fin ⟨Z < 0, maxFiniteScaled⟩ := by
  have hpos : 0 < fmaDirectedThreshold := by
    rw [fmaDirectedThreshold_value]
    decide
  have hz : Z ≠ 0 := by
    intro h
    rw [h] at hlo
    simp at hlo
    omega
  have hfine := fmaRoundedFineMode_towardZero_top Z hlo hhi
  have hlt : fmaRoundedFineMode .towardZero Z < 2 ^ 64 := by
    rw [hfine]
    exact fmaDirectedThreshold_lt_two_pow64
  unfold roundFmaScaledMode
  rw [ite_eq_right hz, ite_eq_left hlt,
    fmaRoundMagMode_eq_maxFinite_of_fine_eq_threshold _ _ hfine]

theorem roundFmaScaledMode_down_nonneg_top (Z : Int) (sm sc : Bool)
    (hz : ¬ Z < 0) (hlo : fmaDirectedThreshold ≤ Z.natAbs)
    (hhi : Z.natAbs < 2 ^ 64) :
    roundFmaScaledMode .down Z sm sc =
      .fin ⟨false, maxFiniteScaled⟩ := by
  have hpos : 0 < fmaDirectedThreshold := by
    rw [fmaDirectedThreshold_value]
    decide
  have hz' : Z ≠ 0 := by
    intro h
    rw [h] at hlo
    simp at hlo
    omega
  have hfine := fmaRoundedFineMode_down_top_nonneg Z hz hlo hhi
  have hlt : fmaRoundedFineMode .down Z < 2 ^ 64 := by
    rw [hfine]
    exact fmaDirectedThreshold_lt_two_pow64
  unfold roundFmaScaledMode
  rw [ite_eq_right hz', ite_eq_left hlt,
    fmaRoundMagMode_eq_maxFinite_of_fine_eq_threshold _ _ hfine]
  simp [hz]

theorem roundFmaScaledMode_down_neg_top (Z : Int) (sm sc : Bool)
    (hz : Z < 0) (hlo : fmaDirectedThreshold < Z.natAbs)
    (hhi : Z.natAbs < 2 ^ 64) :
    roundFmaScaledMode .down Z sm sc = .inf true := by
  have hpos : 0 < fmaDirectedThreshold := by
    rw [fmaDirectedThreshold_value]
    decide
  have hz' : Z ≠ 0 := by
    intro h
    rw [h] at hlo
    simp at hlo
  have hfine := fmaRoundedFineMode_down_top_neg_lt Z hz hlo hhi
  have hnot : ¬ fmaRoundedFineMode .down Z < 2 ^ 64 := by
    rw [hfine]
    omega
  unfold roundFmaScaledMode
  rw [ite_eq_right hz', ite_eq_right hnot]
  simp [overflowMode, hz]

theorem roundFmaScaledMode_up_nonneg_top (Z : Int) (sm sc : Bool)
    (hz : ¬ Z < 0) (hlo : fmaDirectedThreshold < Z.natAbs)
    (hhi : Z.natAbs < 2 ^ 64) :
    roundFmaScaledMode .up Z sm sc = .inf false := by
  have hpos : 0 < fmaDirectedThreshold := by
    rw [fmaDirectedThreshold_value]
    decide
  have hz' : Z ≠ 0 := by
    intro h
    rw [h] at hlo
    simp at hlo
  have hfine := fmaRoundedFineMode_up_top_nonneg_lt Z hz hlo hhi
  have hnot : ¬ fmaRoundedFineMode .up Z < 2 ^ 64 := by
    rw [hfine]
    omega
  unfold roundFmaScaledMode
  rw [ite_eq_right hz', ite_eq_right hnot]
  simp [overflowMode, hz]

theorem roundFmaScaledMode_up_neg_top (Z : Int) (sm sc : Bool)
    (hz : Z < 0) (hlo : fmaDirectedThreshold ≤ Z.natAbs)
    (hhi : Z.natAbs < 2 ^ 64) :
    roundFmaScaledMode .up Z sm sc =
      .fin ⟨true, maxFiniteScaled⟩ := by
  have hpos : 0 < fmaDirectedThreshold := by
    rw [fmaDirectedThreshold_value]
    decide
  have hz' : Z ≠ 0 := by
    intro h
    rw [h] at hlo
    simp at hlo
    omega
  have hfine := fmaRoundedFineMode_up_top_neg Z hz hlo hhi
  have hlt : fmaRoundedFineMode .up Z < 2 ^ 64 := by
    rw [hfine]
    exact fmaDirectedThreshold_lt_two_pow64
  unfold roundFmaScaledMode
  rw [ite_eq_right hz', ite_eq_left hlt,
    fmaRoundMagMode_eq_maxFinite_of_fine_eq_threshold _ _ hfine]
  simp [hz]

/-- At the exact directed threshold every mode is finite and saturates at
`±65504`; the threshold itself is a destination-grid point. -/
theorem roundFmaScaledMode_of_natAbs_eq_threshold (mode : RMode) (Z : Int)
    (sm sc : Bool) (h : Z.natAbs = fmaDirectedThreshold) :
    roundFmaScaledMode mode Z sm sc =
      .fin ⟨Z < 0, maxFiniteScaled⟩ := by
  have hq : fmaDestQuantum Z.natAbs = 2 ^ 53 := by
    rw [h]
    exact fmaDestQuantum_of_threshold_le_lt_two_pow64 (Nat.le_refl _)
      fmaDirectedThreshold_lt_two_pow64
  have hdvd : fmaDestQuantum Z.natAbs ∣ Z.natAbs := by
    rw [hq, h]
    exact ⟨2047, by rw [fmaDirectedThreshold_value, Nat.mul_comm]⟩
  have hfix : roundMode mode (fmaDestQuantum Z.natAbs) Z = Z :=
    roundMode_eq_self_of_natAbs_dvd mode _ Z hdvd
  have hfine : fmaRoundedFineMode mode Z = fmaDirectedThreshold := by
    unfold fmaRoundedFineMode
    rw [hfix, h]
  have hpos : 0 < fmaDirectedThreshold := by
    rw [fmaDirectedThreshold_value]
    decide
  have hz : Z ≠ 0 := by
    intro hz0
    rw [hz0] at h
    simp at h
    omega
  have hlt : fmaRoundedFineMode mode Z < 2 ^ 64 := by
    rw [hfine]
    exact fmaDirectedThreshold_lt_two_pow64
  unfold roundFmaScaledMode
  rw [ite_eq_right hz, ite_eq_left hlt,
    fmaRoundMagMode_eq_maxFinite_of_fine_eq_threshold _ _ hfine]

/-- Toward zero never leaves the finite range: any fused magnitude at or above
`65504 * 2 ^ 24` saturates at the largest finite value of the same sign. -/
theorem roundFmaScaledMode_towardZero_of_threshold_le (Z : Int) (sm sc : Bool)
    (h : fmaDirectedThreshold ≤ Z.natAbs) :
    roundFmaScaledMode .towardZero Z sm sc =
      .fin ⟨Z < 0, maxFiniteScaled⟩ := by
  by_cases h64 : Z.natAbs < 2 ^ 64
  · exact roundFmaScaledMode_towardZero_top Z sm sc h h64
  · have hge : 2 ^ 64 ≤ Z.natAbs := by omega
    rw [roundFmaScaledMode_eq_overflowMode_of_ge .towardZero Z sm sc hge]
    rfl

/-- Downward rounding of a nonnegative fused sum saturates at `+65504`. -/
theorem roundFmaScaledMode_down_nonneg_of_threshold_le (Z : Int) (sm sc : Bool)
    (hz : ¬ Z < 0) (h : fmaDirectedThreshold ≤ Z.natAbs) :
    roundFmaScaledMode .down Z sm sc =
      .fin ⟨false, maxFiniteScaled⟩ := by
  by_cases h64 : Z.natAbs < 2 ^ 64
  · exact roundFmaScaledMode_down_nonneg_top Z sm sc hz h h64
  · have hge : 2 ^ 64 ≤ Z.natAbs := by omega
    rw [roundFmaScaledMode_eq_overflowMode_of_ge .down Z sm sc hge]
    simp [overflowMode, hz]

/-- Downward rounding of a negative fused sum above the directed threshold
goes to `-inf`. -/
theorem roundFmaScaledMode_down_neg_of_threshold_lt (Z : Int) (sm sc : Bool)
    (hz : Z < 0) (h : fmaDirectedThreshold < Z.natAbs) :
    roundFmaScaledMode .down Z sm sc = .inf true := by
  by_cases h64 : Z.natAbs < 2 ^ 64
  · exact roundFmaScaledMode_down_neg_top Z sm sc hz h h64
  · have hge : 2 ^ 64 ≤ Z.natAbs := by omega
    rw [roundFmaScaledMode_eq_overflowMode_of_ge .down Z sm sc hge]
    simp [overflowMode, hz]

/-- Upward rounding of a nonnegative fused sum above the directed threshold
goes to `+inf`. -/
theorem roundFmaScaledMode_up_nonneg_of_threshold_lt (Z : Int) (sm sc : Bool)
    (hz : ¬ Z < 0) (h : fmaDirectedThreshold < Z.natAbs) :
    roundFmaScaledMode .up Z sm sc = .inf false := by
  by_cases h64 : Z.natAbs < 2 ^ 64
  · exact roundFmaScaledMode_up_nonneg_top Z sm sc hz h h64
  · have hge : 2 ^ 64 ≤ Z.natAbs := by omega
    rw [roundFmaScaledMode_eq_overflowMode_of_ge .up Z sm sc hge]
    simp [overflowMode, hz]

/-- Upward rounding of a negative fused sum saturates at `-65504`. -/
theorem roundFmaScaledMode_up_neg_of_threshold_le (Z : Int) (sm sc : Bool)
    (hz : Z < 0) (h : fmaDirectedThreshold ≤ Z.natAbs) :
    roundFmaScaledMode .up Z sm sc =
      .fin ⟨true, maxFiniteScaled⟩ := by
  by_cases h64 : Z.natAbs < 2 ^ 64
  · exact roundFmaScaledMode_up_neg_top Z sm sc hz h h64
  · have hge : 2 ^ 64 ≤ Z.natAbs := by omega
    rw [roundFmaScaledMode_eq_overflowMode_of_ge .up Z sm sc hge]
    simp [overflowMode, hz]

/-- At stage-170's exact ties-to-even threshold, the directions pointing away
from zero overflow and the other directions saturate at `±65504`. -/
theorem roundFmaScaledMode_at_fmaOverflowThreshold (sm sc : Bool) :
    roundFmaScaledMode .up (fmaOverflowThreshold : Int) sm sc = .inf false ∧
      roundFmaScaledMode .down (-(fmaOverflowThreshold : Int)) sm sc = .inf true ∧
      roundFmaScaledMode .down (fmaOverflowThreshold : Int) sm sc =
        .fin ⟨false, maxFiniteScaled⟩ ∧
      roundFmaScaledMode .up (-(fmaOverflowThreshold : Int)) sm sc =
        .fin ⟨true, maxFiniteScaled⟩ ∧
      roundFmaScaledMode .towardZero (fmaOverflowThreshold : Int) sm sc =
        .fin ⟨false, maxFiniteScaled⟩ ∧
      roundFmaScaledMode .towardZero (-(fmaOverflowThreshold : Int)) sm sc =
        .fin ⟨true, maxFiniteScaled⟩ := by
  have hlt : fmaDirectedThreshold < fmaOverflowThreshold :=
    fmaDirectedThreshold_lt_fmaOverflowThreshold
  have h64 : fmaOverflowThreshold < 2 ^ 64 := fmaOverflowThreshold_lt_two_pow64
  have hpos : (fmaOverflowThreshold : Int).natAbs = fmaOverflowThreshold :=
    Int.natAbs_natCast _
  have hneg : (-(fmaOverflowThreshold : Int)).natAbs = fmaOverflowThreshold := by
    rw [Int.natAbs_neg, Int.natAbs_natCast]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact roundFmaScaledMode_up_nonneg_of_threshold_lt _ sm sc (by decide)
      (by rw [hpos]; exact hlt)
  · exact roundFmaScaledMode_down_neg_of_threshold_lt _ sm sc (by decide)
      (by rw [hneg]; exact hlt)
  · exact roundFmaScaledMode_down_nonneg_of_threshold_le _ sm sc (by decide)
      (by rw [hpos]; exact Nat.le_of_lt hlt)
  · exact roundFmaScaledMode_up_neg_of_threshold_le _ sm sc (by decide)
      (by rw [hneg]; exact Nat.le_of_lt hlt)
  · exact roundFmaScaledMode_towardZero_of_threshold_le _ sm sc
      (by rw [hpos]; exact Nat.le_of_lt hlt)
  · exact roundFmaScaledMode_towardZero_of_threshold_le _ sm sc
      (by rw [hneg]; exact Nat.le_of_lt hlt)

/-! ### Overflow at the operand level -/

theorem fmaDirected_fin_overflow_towardZero (x y c : SVal)
    (h : fmaDirectedThreshold ≤ (fmaScaled x y c).natAbs) :
    fmaDirected .towardZero (.fin x) (.fin y) (.fin c) =
      .fin ⟨fmaScaled x y c < 0, maxFiniteScaled⟩ := by
  rw [fmaDirected_fin_fin]
  exact roundFmaScaledMode_towardZero_of_threshold_le _ _ _ h

theorem fmaDirected_fin_overflow_down_nonneg (x y c : SVal)
    (hz : ¬ fmaScaled x y c < 0)
    (h : fmaDirectedThreshold ≤ (fmaScaled x y c).natAbs) :
    fmaDirected .down (.fin x) (.fin y) (.fin c) =
      .fin ⟨false, maxFiniteScaled⟩ := by
  rw [fmaDirected_fin_fin]
  exact roundFmaScaledMode_down_nonneg_of_threshold_le _ _ _ hz h

theorem fmaDirected_fin_overflow_down_neg (x y c : SVal)
    (hz : fmaScaled x y c < 0)
    (h : fmaDirectedThreshold < (fmaScaled x y c).natAbs) :
    fmaDirected .down (.fin x) (.fin y) (.fin c) = .inf true := by
  rw [fmaDirected_fin_fin]
  exact roundFmaScaledMode_down_neg_of_threshold_lt _ _ _ hz h

theorem fmaDirected_fin_overflow_up_nonneg (x y c : SVal)
    (hz : ¬ fmaScaled x y c < 0)
    (h : fmaDirectedThreshold < (fmaScaled x y c).natAbs) :
    fmaDirected .up (.fin x) (.fin y) (.fin c) = .inf false := by
  rw [fmaDirected_fin_fin]
  exact roundFmaScaledMode_up_nonneg_of_threshold_lt _ _ _ hz h

theorem fmaDirected_fin_overflow_up_neg (x y c : SVal)
    (hz : fmaScaled x y c < 0)
    (h : fmaDirectedThreshold ≤ (fmaScaled x y c).natAbs) :
    fmaDirected .up (.fin x) (.fin y) (.fin c) =
      .fin ⟨true, maxFiniteScaled⟩ := by
  rw [fmaDirected_fin_fin]
  exact roundFmaScaledMode_up_neg_of_threshold_le _ _ _ hz h

/-! ### The finite directed class -/

theorem roundMode_natAbs_le_roundUpNat (mode : RMode) (q : Nat) (Z : Int) :
    (roundMode mode q Z).natAbs ≤ roundUpNat q Z.natAbs := by
  by_cases hz : 0 ≤ Z
  · have hto := toNat_eq_natAbs_of_nonneg hz
    cases mode
    · show (roundTowardZero q Z).natAbs ≤ roundUpNat q Z.natAbs
      unfold roundTowardZero
      rw [ite_eq_left hz, hto, Int.natAbs_natCast]
      exact roundDownNat_le_roundUpNat q Z.natAbs
    · show (roundUp q Z).natAbs ≤ roundUpNat q Z.natAbs
      unfold roundUp
      rw [ite_eq_left hz, hto, Int.natAbs_natCast]
      exact Nat.le_refl _
    · show (roundDown q Z).natAbs ≤ roundUpNat q Z.natAbs
      unfold roundDown
      rw [ite_eq_left hz, hto, Int.natAbs_natCast]
      exact roundDownNat_le_roundUpNat q Z.natAbs
  · have hto := toNat_neg_eq_natAbs_of_neg hz
    cases mode
    · show (roundTowardZero q Z).natAbs ≤ roundUpNat q Z.natAbs
      unfold roundTowardZero
      rw [ite_eq_right hz, hto, Int.natAbs_neg, Int.natAbs_natCast]
      exact roundDownNat_le_roundUpNat q Z.natAbs
    · show (roundUp q Z).natAbs ≤ roundUpNat q Z.natAbs
      unfold roundUp
      rw [ite_eq_right hz, hto, Int.natAbs_neg, Int.natAbs_natCast]
      exact roundDownNat_le_roundUpNat q Z.natAbs
    · show (roundDown q Z).natAbs ≤ roundUpNat q Z.natAbs
      unfold roundDown
      rw [ite_eq_right hz, hto, Int.natAbs_neg, Int.natAbs_natCast]
      exact Nat.le_refl _

theorem roundMode_natAbs_le_add (mode : RMode) (q : Nat) (_hq : 0 < q) (Z : Int) :
    (roundMode mode q Z).natAbs ≤ Z.natAbs + q := by
  by_cases hz : 0 ≤ Z
  · have hto := toNat_eq_natAbs_of_nonneg hz
    cases mode
    · show (roundTowardZero q Z).natAbs ≤ Z.natAbs + q
      unfold roundTowardZero
      rw [ite_eq_left hz, hto, Int.natAbs_natCast]
      exact Nat.le_trans (roundDownNat_le q Z.natAbs) (Nat.le_add_right _ _)
    · show (roundUp q Z).natAbs ≤ Z.natAbs + q
      unfold roundUp
      rw [ite_eq_left hz, hto, Int.natAbs_natCast]
      exact roundUpNat_le_add q Z.natAbs
    · show (roundDown q Z).natAbs ≤ Z.natAbs + q
      unfold roundDown
      rw [ite_eq_left hz, hto, Int.natAbs_natCast]
      exact Nat.le_trans (roundDownNat_le q Z.natAbs) (Nat.le_add_right _ _)
  · have hto := toNat_neg_eq_natAbs_of_neg hz
    cases mode
    · show (roundTowardZero q Z).natAbs ≤ Z.natAbs + q
      unfold roundTowardZero
      rw [ite_eq_right hz, hto, Int.natAbs_neg, Int.natAbs_natCast]
      exact Nat.le_trans (roundDownNat_le q Z.natAbs) (Nat.le_add_right _ _)
    · show (roundUp q Z).natAbs ≤ Z.natAbs + q
      unfold roundUp
      rw [ite_eq_right hz, hto, Int.natAbs_neg, Int.natAbs_natCast]
      exact Nat.le_trans (roundDownNat_le q Z.natAbs) (Nat.le_add_right _ _)
    · show (roundDown q Z).natAbs ≤ Z.natAbs + q
      unfold roundDown
      rw [ite_eq_right hz, hto, Int.natAbs_neg, Int.natAbs_natCast]
      exact roundUpNat_le_add q Z.natAbs

theorem fmaDestQuantum_le_two_pow52_of_lt_two_pow63 {m : Nat} (h : m < 2 ^ 63) :
    fmaDestQuantum m ≤ 2 ^ 52 := by
  by_cases h34 : m < 2 ^ 34
  · rw [fmaDestQuantum_of_lt h34]
    decide
  · rw [fmaDestQuantum_of_ge (by omega)]
    apply Nat.pow_le_pow_right (by decide)
    have hm0 : m ≠ 0 := by omega
    have hloglt : Nat.log2 m < 63 := (Nat.log2_lt hm0).mpr (by simpa using h)
    omega

theorem fmaDestQuantum_of_two_pow63_le_lt_threshold {m : Nat}
    (hlo : 2 ^ 63 ≤ m) (hhi : m < fmaDirectedThreshold) :
    fmaDestQuantum m = 2 ^ 53 := by
  have h64 : m < 2 ^ 64 := Nat.lt_trans hhi fmaDirectedThreshold_lt_two_pow64
  have h34 : 2 ^ 34 ≤ m := by omega
  rw [fmaDestQuantum_of_ge h34]
  have hm0 : m ≠ 0 := by omega
  have hlog : Nat.log2 m = 63 := by
    rw [Nat.log2_eq_iff hm0]
    constructor
    · exact hlo
    · simpa using h64
  rw [hlog]

theorem roundUpNat_two_pow53_le_threshold_of_lt {m : Nat}
    (_hlo : 2 ^ 63 ≤ m) (hhi : m < fmaDirectedThreshold) :
    roundUpNat (2 ^ 53) m ≤ fmaDirectedThreshold := by
  have hqpos : 0 < 2 ^ 53 := by decide
  have hdivlt : m / 2 ^ 53 < 2047 := by
    apply (Nat.div_lt_iff_lt_mul hqpos).mpr
    rw [fmaDirectedThreshold_value] at hhi
    exact hhi
  have hdivle : m / 2 ^ 53 ≤ 2046 := by omega
  unfold roundUpNat
  by_cases hmod : m % 2 ^ 53 = 0
  · rw [ite_eq_left hmod, Nat.add_zero]
    calc
      m / 2 ^ 53 * 2 ^ 53 ≤ 2046 * 2 ^ 53 := Nat.mul_le_mul_right _ hdivle
      _ ≤ 2047 * 2 ^ 53 := Nat.mul_le_mul_right _ (by decide)
      _ = fmaDirectedThreshold := fmaDirectedThreshold_value.symm
  · rw [ite_eq_right hmod]
    rw [← Nat.succ_mul]
    calc
      (m / 2 ^ 53 + 1) * 2 ^ 53 ≤ 2047 * 2 ^ 53 :=
        Nat.mul_le_mul_right _ (by omega)
      _ = fmaDirectedThreshold := fmaDirectedThreshold_value.symm

/-- Every directed rounding of a fused magnitude at most the directed
threshold stays below the first unrepresentable fp16 magnitude. -/
theorem fmaRoundedFineMode_lt_two_pow64_of_le_threshold (mode : RMode) (Z : Int)
    (h : Z.natAbs ≤ fmaDirectedThreshold) :
    fmaRoundedFineMode mode Z < 2 ^ 64 := by
  by_cases heq : Z.natAbs = fmaDirectedThreshold
  · have hq : fmaDestQuantum Z.natAbs = 2 ^ 53 := by
      rw [heq]
      exact fmaDestQuantum_of_threshold_le_lt_two_pow64 (Nat.le_refl _)
        fmaDirectedThreshold_lt_two_pow64
    have hdvd : fmaDestQuantum Z.natAbs ∣ Z.natAbs := by
      rw [hq, heq]
      exact ⟨2047, by rw [fmaDirectedThreshold_value, Nat.mul_comm]⟩
    have hfix : roundMode mode (fmaDestQuantum Z.natAbs) Z = Z :=
      roundMode_eq_self_of_natAbs_dvd mode _ Z hdvd
    unfold fmaRoundedFineMode
    rw [hfix, heq]
    exact fmaDirectedThreshold_lt_two_pow64
  · have hlt : Z.natAbs < fmaDirectedThreshold := Nat.lt_of_le_of_ne h heq
    by_cases htop : 2 ^ 63 ≤ Z.natAbs
    · have hq := fmaDestQuantum_of_two_pow63_le_lt_threshold htop hlt
      have hceil := roundUpNat_two_pow53_le_threshold_of_lt htop hlt
      have hle := roundMode_natAbs_le_roundUpNat mode (fmaDestQuantum Z.natAbs) Z
      rw [hq] at hle
      have hT := fmaDirectedThreshold_lt_two_pow64
      unfold fmaRoundedFineMode
      rw [hq]
      omega
    · have hlt63 : Z.natAbs < 2 ^ 63 := by omega
      have hqle := fmaDestQuantum_le_two_pow52_of_lt_two_pow63 hlt63
      have hbound := roundMode_natAbs_le_add mode (fmaDestQuantum Z.natAbs)
        (fmaDestQuantum_pos _) Z
      unfold fmaRoundedFineMode
      omega

theorem roundFmaScaledMode_fin_signed_of_le_threshold (mode : RMode) (Z : Int)
    (sm sc : Bool) (h : Z.natAbs ≤ fmaDirectedThreshold) :
    ∃ v : SVal, roundFmaScaledMode mode Z sm sc = .fin v ∧
      v.signed * (2 ^ 24 : Nat) =
        roundMode mode (fmaDestQuantum Z.natAbs) Z :=
  roundFmaScaledMode_fin_signed_of_lt_two_pow64 mode Z sm sc
    (fmaRoundedFineMode_lt_two_pow64_of_le_threshold mode Z h)

theorem fmaDirected_fin_of_le_threshold (mode : RMode) (x y c : SVal)
    (h : (fmaScaled x y c).natAbs ≤ fmaDirectedThreshold) :
    ∃ v : SVal, fmaDirected mode (.fin x) (.fin y) (.fin c) = .fin v ∧
      v.signed * (2 ^ 24 : Nat) =
        roundMode mode (fmaDestQuantum (fmaScaled x y c).natAbs)
          (fmaScaled x y c) := by
  rw [fmaDirected_fin_fin]
  exact roundFmaScaledMode_fin_signed_of_le_threshold mode _ _ _ h

/-- Stage-170's ties-to-even `fma` lies between the downward and upward
directed results whenever the exact fused sum is within the finite directed
class.  The middle value is exactly the `fma_fin` witness. -/
theorem fma_fin_between_directed (x y c : SVal)
    (hx : x.mag ≤ maxFiniteScaled) (hy : y.mag ≤ maxFiniteScaled)
    (hc : c.mag ≤ maxFiniteScaled)
    (h : (fmaScaled x y c).natAbs ≤ fmaDirectedThreshold) :
    ∃ vd ve vu : SVal,
      fmaDirected .down (.fin x) (.fin y) (.fin c) = .fin vd ∧
      fma (.fin x) (.fin y) (.fin c) = .fin ve ∧
      fmaDirected .up (.fin x) (.fin y) (.fin c) = .fin vu ∧
      vd.signed ≤ ve.signed ∧ ve.signed ≤ vu.signed := by
  let Z := fmaScaled x y c
  have hZ : Z.natAbs ≤ fmaDirectedThreshold := h
  have hfin : Z.natAbs < fmaOverflowThreshold :=
    Nat.lt_of_le_of_lt hZ fmaDirectedThreshold_lt_fmaOverflowThreshold
  obtain ⟨vd, hvd, hvds⟩ :=
    roundFmaScaledMode_fin_signed_of_le_threshold .down Z (productSign x y)
      c.sign hZ
  obtain ⟨vu, hvu, hvus⟩ :=
    roundFmaScaledMode_fin_signed_of_le_threshold .up Z (productSign x y)
      c.sign hZ
  obtain ⟨ve, hve, _hmag, hves⟩ := (fma_fin x y c hx hy hc hfin).2
  have hqpos : 0 < fmaDestQuantum Z.natAbs := fmaDestQuantum_pos Z.natAbs
  have hd : roundDown (fmaDestQuantum Z.natAbs) Z ≤
      roundEven (fmaDestQuantum Z.natAbs) Z :=
    roundDown_le_roundEven _ hqpos Z
  have hu : roundEven (fmaDestQuantum Z.natAbs) Z ≤
      roundUp (fmaDestQuantum Z.natAbs) Z :=
    roundEven_le_roundUp _ hqpos Z
  have hvds' : vd.signed * (2 ^ 24 : Nat) =
      roundDown (fmaDestQuantum Z.natAbs) Z := by
    simpa [roundMode] using hvds
  have hvus' : vu.signed * (2 ^ 24 : Nat) =
      roundUp (fmaDestQuantum Z.natAbs) Z := by
    simpa [roundMode] using hvus
  have hdle : vd.signed ≤ ve.signed := by
    apply Int.le_of_mul_le_mul_right _ (by decide : (0 : Int) < (2 ^ 24 : Nat))
    rw [hvds', hves]
    exact hd
  have hule : ve.signed ≤ vu.signed := by
    apply Int.le_of_mul_le_mul_right _ (by decide : (0 : Int) < (2 ^ 24 : Nat))
    rw [hves, hvus']
    exact hu
  refine ⟨vd, ve, vu, ?_, ?_, ?_, hdle, hule⟩
  · rw [fmaDirected_fin_fin]
    exact hvd
  · exact hve
  · rw [fmaDirected_fin_fin]
    exact hvu

/-! ## Commuting directed rounding with the `2 ^ 24` scale -/

theorem roundDownNat_mul_two_pow24 (q m : Nat) :
    roundDownNat (q * 2 ^ 24) (m * 2 ^ 24) = roundDownNat q m * 2 ^ 24 := by
  unfold roundDownNat
  rw [Nat.mul_div_mul_right m q (by decide : 0 < 2 ^ 24)]
  rw [Nat.mul_assoc]

theorem roundUpNat_mul_two_pow24 (q m : Nat) :
    roundUpNat (q * 2 ^ 24) (m * 2 ^ 24) = roundUpNat q m * 2 ^ 24 := by
  unfold roundUpNat
  rw [Nat.mul_div_mul_right m q (by decide : 0 < 2 ^ 24)]
  rw [Nat.mul_mod_mul_right (2 ^ 24) m q]
  by_cases h : m % q = 0
  · have h0 : (m % q) * 2 ^ 24 = 0 := by rw [h, Nat.zero_mul]
    rw [ite_eq_left h0, ite_eq_left h, Nat.add_zero, Nat.add_zero]
    rw [Nat.mul_assoc]
  · have h0 : (m % q) * 2 ^ 24 ≠ 0 :=
      Nat.mul_ne_zero_iff.mpr ⟨h, by decide⟩
    rw [ite_eq_right h0, ite_eq_right h]
    rw [Nat.add_mul, Nat.mul_assoc]

theorem roundTowardZeroNat_mul_two_pow24 (q m : Nat) :
    roundTowardZeroNat (q * 2 ^ 24) (m * 2 ^ 24) =
      roundTowardZeroNat q m * 2 ^ 24 := by
  unfold roundTowardZeroNat
  rw [Nat.mul_div_mul_right m q (by decide : 0 < 2 ^ 24)]
  rw [Nat.mul_assoc]

theorem roundDown_mul_two_pow24 (q : Nat) (z : Int) :
    roundDown (q * 2 ^ 24) (z * (2 ^ 24 : Nat)) =
      roundDown q z * (2 ^ 24 : Nat) := by
  by_cases hz : 0 ≤ z
  · have hzS : 0 ≤ z * (2 ^ 24 : Nat) := (mul_two_pow24_nonneg_iff z).mpr hz
    have hto : (z * (2 ^ 24 : Nat)).toNat = z.toNat * 2 ^ 24 := by
      rw [Int.toNat_mul hz (by decide), Int.toNat_natCast]
    unfold roundDown
    rw [ite_eq_left hz, ite_eq_left hzS, hto, roundDownNat_mul_two_pow24]
    rw [Int.natCast_mul]
  · have hzS : ¬ 0 ≤ z * (2 ^ 24 : Nat) := by
      intro h
      exact hz ((mul_two_pow24_nonneg_iff z).mp h)
    have hneg : -(z * (2 ^ 24 : Nat)) = (-z) * (2 ^ 24 : Nat) := by
      rw [Int.neg_mul]
    have hz0 : 0 ≤ -z := by omega
    have hto : ((-z) * (2 ^ 24 : Nat)).toNat = (-z).toNat * 2 ^ 24 := by
      rw [Int.toNat_mul hz0 (by decide), Int.toNat_natCast]
    unfold roundDown
    rw [ite_eq_right hz, ite_eq_right hzS, hneg, hto, roundUpNat_mul_two_pow24]
    rw [Int.natCast_mul]
    rw [Int.neg_mul]

theorem roundUp_mul_two_pow24 (q : Nat) (z : Int) :
    roundUp (q * 2 ^ 24) (z * (2 ^ 24 : Nat)) =
      roundUp q z * (2 ^ 24 : Nat) := by
  by_cases hz : 0 ≤ z
  · have hzS : 0 ≤ z * (2 ^ 24 : Nat) := (mul_two_pow24_nonneg_iff z).mpr hz
    have hto : (z * (2 ^ 24 : Nat)).toNat = z.toNat * 2 ^ 24 := by
      rw [Int.toNat_mul hz (by decide), Int.toNat_natCast]
    unfold roundUp
    rw [ite_eq_left hz, ite_eq_left hzS, hto, roundUpNat_mul_two_pow24]
    rw [Int.natCast_mul]
  · have hzS : ¬ 0 ≤ z * (2 ^ 24 : Nat) := by
      intro h
      exact hz ((mul_two_pow24_nonneg_iff z).mp h)
    have hneg : -(z * (2 ^ 24 : Nat)) = (-z) * (2 ^ 24 : Nat) := by
      rw [Int.neg_mul]
    have hz0 : 0 ≤ -z := by omega
    have hto : ((-z) * (2 ^ 24 : Nat)).toNat = (-z).toNat * 2 ^ 24 := by
      rw [Int.toNat_mul hz0 (by decide), Int.toNat_natCast]
    unfold roundUp
    rw [ite_eq_right hz, ite_eq_right hzS, hneg, hto, roundDownNat_mul_two_pow24]
    rw [Int.natCast_mul]
    rw [Int.neg_mul]

theorem roundTowardZero_mul_two_pow24 (q : Nat) (z : Int) :
    roundTowardZero (q * 2 ^ 24) (z * (2 ^ 24 : Nat)) =
      roundTowardZero q z * (2 ^ 24 : Nat) := by
  by_cases hz : 0 ≤ z
  · have hzS : 0 ≤ z * (2 ^ 24 : Nat) := (mul_two_pow24_nonneg_iff z).mpr hz
    have hto : (z * (2 ^ 24 : Nat)).toNat = z.toNat * 2 ^ 24 := by
      rw [Int.toNat_mul hz (by decide), Int.toNat_natCast]
    unfold roundTowardZero
    rw [ite_eq_left hz, ite_eq_left hzS, hto, roundTowardZeroNat_mul_two_pow24]
    rw [Int.natCast_mul]
  · have hzS : ¬ 0 ≤ z * (2 ^ 24 : Nat) := by
      intro h
      exact hz ((mul_two_pow24_nonneg_iff z).mp h)
    have hneg : -(z * (2 ^ 24 : Nat)) = (-z) * (2 ^ 24 : Nat) := by
      rw [Int.neg_mul]
    have hz0 : 0 ≤ -z := by omega
    have hto : ((-z) * (2 ^ 24 : Nat)).toNat = (-z).toNat * 2 ^ 24 := by
      rw [Int.toNat_mul hz0 (by decide), Int.toNat_natCast]
    unfold roundTowardZero
    rw [ite_eq_right hz, ite_eq_right hzS, hneg, hto, roundDownNat_mul_two_pow24]
    rw [Int.natCast_mul]
    rw [Int.neg_mul]

theorem roundMode_mul_two_pow24 (mode : RMode) (q : Nat) (z : Int) :
    roundMode mode (q * 2 ^ 24) (z * (2 ^ 24 : Nat)) =
      roundMode mode q z * (2 ^ 24 : Nat) := by
  cases mode
  · exact roundTowardZero_mul_two_pow24 q z
  · exact roundUp_mul_two_pow24 q z
  · exact roundDown_mul_two_pow24 q z

/-- Stage-159's destination quantum in `2 ^ -24` units; below the first normal
binade the grid is exact, so the quantum is one. -/
def coarseDestQuantum (m : Nat) : Nat :=
  if m < 1024 then 1 else 2 ^ (Nat.log2 m - 10)

/-- Stage-159's directed rounded magnitude at its destination quantum. -/
def coarseRoundedFine (mode : RMode) (z : Int) : Nat :=
  (roundMode mode (coarseDestQuantum z.natAbs) z).natAbs

theorem coarseDestQuantum_of_lt_1024 {m : Nat} (h : m < 1024) :
    coarseDestQuantum m = 1 := by
  unfold coarseDestQuantum
  rw [ite_eq_left h]

theorem coarseDestQuantum_of_1024_le {m : Nat} (h : 1024 ≤ m) :
    coarseDestQuantum m = 2 ^ (Nat.log2 m - 10) := by
  unfold coarseDestQuantum
  rw [ite_eq_right (by omega)]

/-- Stage-159's directed addition result in closed form: below the overflow
threshold it is exactly the directed rounding at `coarseDestQuantum`. -/
theorem roundScaledMode_eq_closed (mode : RMode) (z : Int) (sa sb : Bool)
    (hz : z ≠ 0) :
    roundScaledMode mode z sa sb =
      if coarseRoundedFine mode z < 2 ^ 40 then
        .fin ⟨z < 0, coarseRoundedFine mode z⟩
      else overflowMode mode (z < 0) := by
  by_cases hsmall : z.natAbs < 1024
  · have hq : coarseDestQuantum z.natAbs = 1 := coarseDestQuantum_of_lt_1024 hsmall
    have hR : coarseRoundedFine mode z = z.natAbs := by
      unfold coarseRoundedFine
      rw [hq, roundMode_eq_self_of_natAbs_dvd mode 1 z
        ⟨z.natAbs, by rw [Nat.one_mul]⟩]
    have hRlt : coarseRoundedFine mode z < 2 ^ 40 := by
      rw [hR]
      omega
    unfold roundScaledMode
    rw [ite_eq_right hz, ite_eq_left hsmall]
    rw [ite_eq_left hRlt, hR]
  · have h1024 : 1024 ≤ z.natAbs := by omega
    have hm0 : z.natAbs ≠ 0 := by omega
    unfold roundScaledMode
    rw [ite_eq_right hz, ite_eq_right (by omega : ¬ z.natAbs < 1024)]
    dsimp only
    generalize hL : Nat.log2 z.natAbs = L
    generalize hR : (roundMode mode (2 ^ (L - 10)) z).natAbs = R
    have hqC : coarseDestQuantum z.natAbs = 2 ^ (L - 10) := by
      rw [coarseDestQuantum_of_1024_le h1024, hL]
    have hCR : coarseRoundedFine mode z = R := by
      unfold coarseRoundedFine
      rw [hqC, hR]
    rw [hCR]
    have hbounds := (Nat.log2_eq_iff hm0).mp hL
    have hpowL : 2 ^ L ≤ z.natAbs := hbounds.1
    have hpowU : z.natAbs < 2 ^ (L + 1) := hbounds.2
    have hL10 : 10 ≤ L := by
      have hle := le_log2_of_two_pow_le z.natAbs 10 (by simpa using h1024)
      omega
    have hqpos : 0 < 2 ^ (L - 10) := Nat.two_pow_pos _
    have h1024q : 1024 * 2 ^ (L - 10) ≤ z.natAbs := by
      calc
        1024 * 2 ^ (L - 10) = 2 ^ 10 * 2 ^ (L - 10) := by
          rw [show (1024 : Nat) = 2 ^ 10 by decide]
        _ = 2 ^ (10 + (L - 10)) := by rw [Nat.pow_add]
        _ = 2 ^ L := by
          congr 1
          omega
        _ ≤ z.natAbs := hpowL
    have hm_lt : z.natAbs < 2048 * 2 ^ (L - 10) := by
      calc
        z.natAbs < 2 ^ (L + 1) := hpowU
        _ = 2 ^ (11 + (L - 10)) := by
          congr 1
          omega
        _ = 2 ^ 11 * 2 ^ (L - 10) := by rw [Nat.pow_add]
        _ = 2048 * 2 ^ (L - 10) := by
          rw [show (2048 : Nat) = 2 ^ 11 by decide]
    have hRle : R ≤ z.natAbs + 2 ^ (L - 10) := by
      rw [← hR]
      exact roundMode_natAbs_le_add mode _ hqpos z
    have hdvd : 2 ^ (L - 10) ∣ R := by
      rw [← hR]
      obtain ⟨k, hk⟩ := roundMode_natAbs_dvd mode (2 ^ (L - 10)) z
      exact ⟨k, by rw [hk, Nat.mul_comm]⟩
    have hRdecomp : R / 2 ^ (L - 10) * 2 ^ (L - 10) = R :=
      Nat.div_mul_cancel hdvd
    have hmantle : R / 2 ^ (L - 10) ≤ 2048 := by
      have hRlt : R < 2049 * 2 ^ (L - 10) := by
        have hsum : z.natAbs + 2 ^ (L - 10) < 2049 * 2 ^ (L - 10) := by
          omega
        exact Nat.lt_of_le_of_lt hRle hsum
      have := (Nat.div_lt_iff_lt_mul hqpos).mpr hRlt
      omega
    by_cases hL38 : L ≤ 38
    · have he1 : L - 9 + 1 ≤ 30 := by omega
      have hRlt : R < 2 ^ 40 := by
        have hmul : R ≤ 2048 * 2 ^ (L - 10) := by
          rw [← hRdecomp]
          exact Nat.mul_le_mul_right _ hmantle
        have hpow : 2048 * 2 ^ (L - 10) = 2 ^ (L + 1) := by
          rw [show (2048 : Nat) = 2 ^ 11 by decide, ← Nat.pow_add]
          congr 1
          omega
        have hle : 2 ^ (L + 1) ≤ 2 ^ 39 :=
          Nat.pow_le_pow_right (by decide) (by omega)
        have h39 : (2 : Nat) ^ 39 < 2 ^ 40 := by decide
        omega
      rw [ite_eq_left hRlt]
      by_cases hmant : 2048 ≤ R / 2 ^ (L - 10)
      · have hmantEq : R / 2 ^ (L - 10) = 2048 := by omega
        have hmag : R = 1024 * 2 ^ (L - 9) := by
          rw [← hRdecomp, hmantEq]
          rw [show (2048 : Nat) = 2 ^ 11 by decide, ← Nat.pow_add]
          rw [show (1024 : Nat) = 2 ^ 10 by decide, ← Nat.pow_add]
          congr 1
          omega
        rw [ite_eq_left hmant, ite_eq_left he1, hmag]
      · have hmantle' : R / 2 ^ (L - 10) ≤ 2047 := by omega
        have he : L - 9 ≤ 30 := by omega
        have hmag : R = R / 2 ^ (L - 10) * 2 ^ (L - 9 - 1) := by
          rw [← hRdecomp]
          congr 2
          omega
        rw [ite_eq_right hmant, ite_eq_left he]
        rw [← hmag]
    · have hL39 : 39 ≤ L := by omega
      by_cases hL39eq : L = 39
      · have hq : 2 ^ (L - 10) = 2 ^ 29 := by rw [hL39eq]
        have he1 : ¬ L - 9 + 1 ≤ 30 := by omega
        have he : L - 9 ≤ 30 := by omega
        by_cases hmant : 2048 ≤ R / 2 ^ (L - 10)
        · have hmantEq : R / 2 ^ (L - 10) = 2048 := by omega
          have hRge : 2 ^ 40 ≤ R := by
            rw [← hRdecomp, hmantEq, hq]
            decide
          rw [ite_eq_right (by omega : ¬ R < 2 ^ 40)]
          rw [ite_eq_left hmant, ite_eq_right he1]
        · have hmantle' : R / 2 ^ (L - 10) ≤ 2047 := by omega
          have hRlt : R < 2 ^ 40 := by
            have hmul : R ≤ 2047 * 2 ^ (L - 10) := by
              rw [← hRdecomp]
              exact Nat.mul_le_mul_right _ hmantle'
            rw [hq] at hmul
            have hlt : 2047 * 2 ^ 29 < 2 ^ 40 := by decide
            omega
          rw [ite_eq_left hRlt]
          rw [ite_eq_right hmant, ite_eq_left he]
          have hmag : R = R / 2 ^ (L - 10) * 2 ^ (L - 9 - 1) := by
            rw [← hRdecomp]
            congr 2
            omega
          rw [← hmag]
      · have hL40 : 40 ≤ L := by omega
        have he1 : ¬ L - 9 + 1 ≤ 30 := by omega
        have he : ¬ L - 9 ≤ 30 := by omega
        have hRge : 2 ^ 40 ≤ R := by
          have hlow := le_roundMode_natAbs_of_1024_mul_le mode
            (2 ^ (L - 10)) hqpos z h1024q
          rw [hR] at hlow
          have hpow : 1024 * 2 ^ (L - 10) = 2 ^ L := by
            calc
              1024 * 2 ^ (L - 10) = 2 ^ 10 * 2 ^ (L - 10) := by
                rw [show (1024 : Nat) = 2 ^ 10 by decide]
              _ = 2 ^ (10 + (L - 10)) := by rw [Nat.pow_add]
              _ = 2 ^ L := by
                congr 1
                omega
          rw [hpow] at hlow
          have hle : 2 ^ 40 ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) hL40
          omega
        rw [ite_eq_right (by omega : ¬ R < 2 ^ 40)]
        by_cases hmant : 2048 ≤ R / 2 ^ (L - 10)
        · rw [ite_eq_left hmant, ite_eq_right he1]
        · rw [ite_eq_right hmant, ite_eq_right he]

theorem nat_log2_mul_two_pow24 (m : Nat) (hm : m ≠ 0) :
    Nat.log2 (m * 2 ^ 24) = Nat.log2 m + 24 := by
  have hS : (0 : Nat) < 2 ^ 24 := by decide
  have hM : m * 2 ^ 24 ≠ 0 := Nat.mul_ne_zero hm (by decide)
  have hbounds := (Nat.log2_eq_iff hm).mp rfl
  rw [Nat.log2_eq_iff hM]
  constructor
  · calc
      2 ^ (Nat.log2 m + 24) = 2 ^ Nat.log2 m * 2 ^ 24 := by rw [Nat.pow_add]
      _ ≤ m * 2 ^ 24 := Nat.mul_le_mul_right _ hbounds.1
  · calc
      m * 2 ^ 24 < 2 ^ (Nat.log2 m + 1) * 2 ^ 24 :=
        Nat.mul_lt_mul_of_pos_right hbounds.2 hS
      _ = 2 ^ (Nat.log2 m + 1 + 24) := by rw [← Nat.pow_add]
      _ = 2 ^ (Nat.log2 m + 24 + 1) := by
        rw [show Nat.log2 m + 1 + 24 = Nat.log2 m + 24 + 1 by omega]

/-- Stage-170's fine destination quantum at a scaled coarse magnitude is the
scaled stage-159 destination quantum. -/
theorem fmaDestQuantum_mul_two_pow24 (m : Nat) (hm : m ≠ 0) :
    fmaDestQuantum (m * 2 ^ 24) = coarseDestQuantum m * 2 ^ 24 := by
  by_cases hsmall : m < 1024
  · have hMsmall : m * 2 ^ 24 < 2 ^ 34 := by
      have hle : m * 2 ^ 24 ≤ 1023 * 2 ^ 24 :=
        Nat.mul_le_mul_right _ (by omega)
      have hlt : 1023 * 2 ^ 24 < 2 ^ 34 := by decide
      exact Nat.lt_of_le_of_lt hle hlt
    rw [fmaDestQuantum_of_lt hMsmall, coarseDestQuantum_of_lt_1024 hsmall,
      Nat.one_mul]
  · have h1024 : 1024 ≤ m := by omega
    have hL10 : 10 ≤ Nat.log2 m := le_log2_of_two_pow_le m 10 (by simpa using h1024)
    have hMge : 2 ^ 34 ≤ m * 2 ^ 24 := by
      have hle : 1024 * 2 ^ 24 ≤ m * 2 ^ 24 := Nat.mul_le_mul_right _ h1024
      have hpow : 1024 * 2 ^ 24 = 2 ^ 34 := by decide
      omega
    rw [fmaDestQuantum_of_ge hMge, coarseDestQuantum_of_1024_le h1024,
      nat_log2_mul_two_pow24 m hm]
    rw [show Nat.log2 m + 24 - 10 = Nat.log2 m - 10 + 24 by omega]
    rw [Nat.pow_add]

/-- Directed fine rounding of a scaled coarse sum is the scaled stage-159
directed rounding. -/
theorem fmaRoundedFineMode_mul_two_pow24 (mode : RMode) (z : Int) :
    fmaRoundedFineMode mode (z * (2 ^ 24 : Nat)) =
      coarseRoundedFine mode z * 2 ^ 24 := by
  by_cases hz : z = 0
  · subst hz
    simp [coarseRoundedFine, fmaRoundedFineMode_zero, roundMode_zero]
  · have hm : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
    unfold fmaRoundedFineMode coarseRoundedFine
    rw [natAbs_mul_two_pow24, fmaDestQuantum_mul_two_pow24 z.natAbs hm,
      roundMode_mul_two_pow24]
    rw [Int.natAbs_mul, Int.natAbs_natCast]

/-- One directed rounding of the exact fine fused sum commutes with the
`2 ^ 24` scale: it is stage-159's directed addition rounding of the coarse
sum. -/
theorem nat_lt_of_mul_lt_mul_right {a b c : Nat} (h : a * c < b * c)
    (_hc : 0 < c) : a < b := by
  by_cases hab : a < b
  · exact hab
  · have hba : b ≤ a := by omega
    have hle : b * c ≤ a * c := Nat.mul_le_mul_right c hba
    omega

theorem roundFmaScaledMode_mul_two_pow24 (mode : RMode) (z : Int) (sa sb : Bool) :
    roundFmaScaledMode mode (z * (2 ^ 24 : Nat)) sa sb =
      roundScaledMode mode z sa sb := by
  by_cases hz : z = 0
  · subst hz
    simp [roundFmaScaledMode, roundScaledMode]
  · have hZ : z * (2 ^ 24 : Nat) ≠ 0 := (mul_two_pow24_ne_zero z).mpr hz
    have hsign : decide (z * (2 ^ 24 : Nat) < 0) = decide (z < 0) :=
      (decide_eq_decide).mpr (mul_two_pow24_lt_zero_iff z)
    have hfine := fmaRoundedFineMode_mul_two_pow24 mode z
    rw [roundScaledMode_eq_closed mode z sa sb hz]
    unfold roundFmaScaledMode
    rw [ite_eq_right hZ]
    by_cases hR : coarseRoundedFine mode z < 2 ^ 40
    · have hRf : fmaRoundedFineMode mode (z * (2 ^ 24 : Nat)) < 2 ^ 64 := by
        rw [hfine]
        have h64 : (2 : Nat) ^ 64 = 2 ^ 40 * 2 ^ 24 := by decide
        rw [h64]
        exact Nat.mul_lt_mul_of_pos_right hR (by decide : 0 < 2 ^ 24)
      rw [ite_eq_left hR, ite_eq_left hRf, hsign]
      unfold fmaRoundMagMode
      rw [hfine, Nat.mul_div_cancel _ (by decide : 0 < 2 ^ 24)]
    · have hRf : ¬ fmaRoundedFineMode mode (z * (2 ^ 24 : Nat)) < 2 ^ 64 := by
        rw [hfine]
        intro hlt
        have h64 : (2 : Nat) ^ 64 = 2 ^ 40 * 2 ^ 24 := by decide
        rw [h64] at hlt
        exact hR (nat_lt_of_mul_lt_mul_right hlt (by decide : 0 < 2 ^ 24))
      rw [ite_eq_right hR, ite_eq_right hRf, hsign]

theorem SVal.signed_eq_zero_of_mag_eq_zero (v : SVal) (h : v.mag = 0) :
    v.signed = 0 := by
  unfold SVal.signed
  rw [h]
  split <;> rfl

theorem roundScaledMode_zero_args_comm (mode : RMode) (z : Int) (sa sb : Bool) :
    roundScaledMode mode z sa sb = roundScaledMode mode z sb sa := by
  by_cases hz : z = 0
  · subst hz
    simp [roundScaledMode, zeroSign_comm]
  · unfold roundScaledMode
    rw [ite_eq_right hz, ite_eq_right hz]

/-- When the product is zero, directed FMA is exactly stage-159's directed
addition of the addend and a signed zero carrying the product sign.  The sign
of that zero makes the equality hold even when the addend is zero. -/
theorem fmaDirected_product_zero_eq_addDirected (mode : RMode) (x y c : SVal)
    (hxy : x.mag = 0 ∨ y.mag = 0) :
    fmaDirected mode (.fin x) (.fin y) (.fin c) =
      addDirected mode (.fin c) (.fin ⟨productSign x y, 0⟩) := by
  have hprod : productScaled x y = 0 := by
    unfold productScaled
    rcases hxy with hx | hy
    · rw [SVal.signed_eq_zero_of_mag_eq_zero x hx, Int.zero_mul]
    · rw [SVal.signed_eq_zero_of_mag_eq_zero y hy, Int.mul_zero]
  have hZ : fmaScaled x y c = c.signed * (2 ^ 24 : Nat) := by
    unfold fmaScaled
    rw [hprod, Int.zero_add]
  rw [fmaDirected_fin_fin, addDirected_fin_fin, hZ]
  have hzero : (⟨productSign x y, 0⟩ : SVal).signed = 0 :=
    SVal.signed_eq_zero_of_mag_eq_zero _ rfl
  rw [hzero, Int.add_zero]
  rw [roundScaledMode_zero_args_comm mode c.signed c.sign (productSign x y)]
  simpa using
    roundFmaScaledMode_mul_two_pow24 mode c.signed (productSign x y) c.sign

/-! ## Bit-level tie examples -/

/-- `1 * 1 + 2 ^ -11` is the tie between `1` and `1 + 2 ^ -10`.  Downward and
toward-zero rounding stay at `0x3C00`, upward rounding reaches `0x3C01`, and
ties-to-even picks the even lower endpoint `0x3C00`. -/
theorem fmaDirected_tie_even_favours_down_bits :
    fmaDirected .down (decodeFull (0x3C00 : Fp16)) (decodeFull (0x3C00 : Fp16))
        (decodeFull (0x1000 : Fp16)) = decodeFull (0x3C00 : Fp16) ∧
      fmaDirected .towardZero (decodeFull (0x3C00 : Fp16))
          (decodeFull (0x3C00 : Fp16)) (decodeFull (0x1000 : Fp16)) =
        decodeFull (0x3C00 : Fp16) ∧
      fmaDirected .up (decodeFull (0x3C00 : Fp16)) (decodeFull (0x3C00 : Fp16))
          (decodeFull (0x1000 : Fp16)) = decodeFull (0x3C01 : Fp16) ∧
      fma (decodeFull (0x3C00 : Fp16)) (decodeFull (0x3C00 : Fp16))
          (decodeFull (0x1000 : Fp16)) = decodeFull (0x3C00 : Fp16) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- `(1 + 2 ^ -10) * 1 + 2 ^ -11` is the tie between `0x3C01` and `0x3C02`.
Downward rounding stays at `0x3C01`, upward rounding and ties-to-even both
reach the even upper endpoint `0x3C02`. -/
theorem fmaDirected_tie_even_favours_up_bits :
    fmaDirected .down (decodeFull (0x3C01 : Fp16)) (decodeFull (0x3C00 : Fp16))
        (decodeFull (0x1000 : Fp16)) = decodeFull (0x3C01 : Fp16) ∧
      fmaDirected .towardZero (decodeFull (0x3C01 : Fp16))
          (decodeFull (0x3C00 : Fp16)) (decodeFull (0x1000 : Fp16)) =
        decodeFull (0x3C01 : Fp16) ∧
      fmaDirected .up (decodeFull (0x3C01 : Fp16)) (decodeFull (0x3C00 : Fp16))
          (decodeFull (0x1000 : Fp16)) = decodeFull (0x3C02 : Fp16) ∧
      fma (decodeFull (0x3C01 : Fp16)) (decodeFull (0x3C00 : Fp16))
          (decodeFull (0x1000 : Fp16)) = decodeFull (0x3C02 : Fp16) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The negative tie `-(1 + 2 ^ -10) * 1 - 2 ^ -11`: downward rounding moves
away from zero to `0xBC02`, while upward and toward-zero stay at `0xBC01`;
ties-to-even picks the even `0xBC02`. -/
theorem fmaDirected_tie_negative_bits :
    fmaDirected .down (decodeFull (0xBC01 : Fp16)) (decodeFull (0x3C00 : Fp16))
        (decodeFull (0x9000 : Fp16)) = decodeFull (0xBC02 : Fp16) ∧
      fmaDirected .up (decodeFull (0xBC01 : Fp16)) (decodeFull (0x3C00 : Fp16))
          (decodeFull (0x9000 : Fp16)) = decodeFull (0xBC01 : Fp16) ∧
      fmaDirected .towardZero (decodeFull (0xBC01 : Fp16))
          (decodeFull (0x3C00 : Fp16)) (decodeFull (0x9000 : Fp16)) =
        decodeFull (0xBC01 : Fp16) ∧
      fma (decodeFull (0xBC01 : Fp16)) (decodeFull (0x3C00 : Fp16))
          (decodeFull (0x9000 : Fp16)) = decodeFull (0xBC02 : Fp16) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## A counterexample to directed product-then-add -/

/-- The directed analogue of stage-170's `roundProductScaled`: round the exact
product under the same mode, using the product sign on both zero slots. -/
def roundProductDirected (mode : RMode) (x y : SVal) : Fp16Val :=
  roundFmaScaledMode mode (productScaled x y) (productSign x y)
    (productSign x y)

/-- Round the product directed, then add the addend directed. -/
def fmaSplitDirected (mode : RMode) (x y c : SVal) : Fp16Val :=
  addDirected mode (roundProductDirected mode x y) (.fin c)

/-- Directed FMA is not "round the product, then add directed".  With stage
170's operands the exact product is `1 + 2 ^ -8 + 3 * 2 ^ -20`; downward
rounding the product discards the tail, while the fused sum
`2 ^ -8 + 3 * 2 ^ -20` rounds upward to `2 ^ -8 + 2 ^ -18`.  The split path
rounds the product up first to `1 + 2 ^ -8 + 2 ^ -10`, and subtracting one
gives `0x1D00`, not the fused `0x1C01`. -/
theorem fmaDirected_up_ne_split :
    fmaDirected .up (decodeFull (0x3C01 : Fp16)) (decodeFull (0x3C03 : Fp16))
        (decodeFull (0xBC00 : Fp16)) = decodeFull (0x1C01 : Fp16) ∧
      fmaSplitDirected .up ⟨false, 16793600⟩ ⟨false, 16826368⟩
          ⟨true, 16777216⟩ = decodeFull (0x1D00 : Fp16) ∧
      fmaDirected .up (decodeFull (0x3C01 : Fp16)) (decodeFull (0x3C03 : Fp16))
          (decodeFull (0xBC00 : Fp16)) ≠
        fmaSplitDirected .up ⟨false, 16793600⟩ ⟨false, 16826368⟩
          ⟨true, 16777216⟩ := by
  have hfused : fmaDirected .up (decodeFull (0x3C01 : Fp16))
      (decodeFull (0x3C03 : Fp16)) (decodeFull (0xBC00 : Fp16)) =
        decodeFull (0x1C01 : Fp16) := by decide
  have hsplit : fmaSplitDirected .up ⟨false, 16793600⟩ ⟨false, 16826368⟩
      ⟨true, 16777216⟩ = decodeFull (0x1D00 : Fp16) := by decide
  exact ⟨hfused, hsplit, by rw [hfused, hsplit]; decide⟩

end IntelGpu

