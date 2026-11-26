-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.FpExceptionFlags

@[expose] public section

/-!
# Fused multiply-add for fp16

Stage 156's `addFull` and stage 164's `roundScaled_eq_rne` round one fp16
addition; stage 166 adds sticky exception flags, but the review item "P1
numerical semantics" still lists "not a full IEEE FMA". This module supplies
the finite fused multiply-add value model and its single-rounding theorem.

- `productScaled`: exact signed product of two finite `SVal`s in units of
  `2 ^ -48`; `productScaled_spec` records the sign, magnitude and bound.
- `fmaScaled`: exact product-plus-add, with the addend shifted by `2 ^ 24`;
  `maxFmaScaled_lt_pow81` bounds every legal fused sum.
- `fmaDestExp` / `fmaDestQuantum`: the fused destination-binade selector,
  chosen from the fused sum rather than the addend. The product can dominate
  the addend; `fmaDestExp_product_dominates_addend` is a concrete witness.
- `fmaOverflowThreshold = overflowThreshold * 2 ^ 24 = 4095 * 2 ^ 52`: the
  exact fine-scale overflow threshold. `roundFmaScaled_fin_iff` proves that a
  one-rounding result is finite exactly below this threshold, and
  `fmaRoundedFine_threshold` shows the tie rounds to infinity.
- `roundFmaScaled` / `rneFmaScaled`: the hardware single-rounding model and
  the IEEE RNE value at the selected fine binade. `fmaScaled_eq_rne` is the
  required equality, and `rneFmaScaled_signed` records the tie-to-even
  rounding at the selected quantum.
- `fma`: value-level fp16 FMA with NaN quieting, `0 * inf` invalid, signed
  infinities, and one finite rounding. `fma_fin` states the finite result,
  its `2 ^ 40` magnitude bound, and agreement with `roundFmaScaled`.
- `fma_double_rounding_counterexample`: a bit-level example where rounding
  the product before adding differs from the fused result (`0x1C01` versus
  `0x1C00`).
- `fmaFlags`: sticky `FpExceptionFlags.Flags` for the whole value domain.
  NaN operands and `0 * inf` are invalid; a finite fused overflow sets
  `overflow` and `inexact`; below the threshold `inexact` is the fine-grid
  rounding test. `fmaFlags_smallest_product_underflow` shows that, unlike
  addition, a fused subnormal product can raise underflow.

## Proved class

All three operands are finite `SVal`s with magnitude at most
`maxFiniteScaled`; NaN and infinity operands are outside the rounding theorem.
The exact fused sum must lie below `fmaOverflowThreshold`, which covers the
whole finite range. Subnormal and zero operands are included. The finite
rounding theorem is one `roundEvenNat` at `fmaDestQuantum`; ties-to-even is
inherited from `Intel.RoundingEven` and exposed by `rneFmaScaled_signed`.

## Outside the model

Exception traps, masks, sticky per-lane state and trap delivery are not
modeled; `fmaFlags` is only a per-operation flag summary. Hardware FMA timing,
latency, pipelining and fusion across instruction boundaries are not modeled.
Directed rounding, tininess-before-rounding, flush-to-zero and
denormals-are-zero are not modeled. NaN payload choice is the left-biased
quieting convention of `addFull`, not an IEEE-mandated payload. This is not a
bit-level hardware implementation: `roundFmaScaled` is the specified
single-rounding value semantics.

There are no new axioms, no `native_decide` and no `sorry`.
-/

namespace IntelGpu

/-! ## Exact products at the `2 ^ -48` scale -/

/-- Exact signed product of two finite fp16 values, in units of `2 ^ -48`. -/
def productScaled (x y : SVal) : Int := x.signed * y.signed

/-- The sign of a product is the exclusive-or of the operand signs. -/
def productSign (x y : SVal) : Bool := x.sign != y.sign

theorem productScaled_natAbs (x y : SVal) :
    (productScaled x y).natAbs = x.mag * y.mag := by
  unfold productScaled
  rw [Int.natAbs_mul, SVal.natAbs_signed, SVal.natAbs_signed]

theorem productScaled_eq_sign_mul (x y : SVal) :
    productScaled x y =
      if productSign x y then -((x.mag * y.mag : Nat) : Int)
      else ((x.mag * y.mag : Nat) : Int) := by
  unfold productScaled productSign
  cases hx : x.sign <;> cases hy : y.sign <;>
    simp [SVal.signed, hx, hy, Int.mul_neg, Int.neg_mul]

theorem productScaled_neg_iff (x y : SVal) (hpos : 0 < x.mag * y.mag) :
    productScaled x y < 0 ↔ productSign x y = true := by
  rw [productScaled_eq_sign_mul]
  have hcast : (0 : Int) < ((x.mag * y.mag : Nat) : Int) := by
    exact_mod_cast hpos
  cases h : productSign x y
  · simp
    exact Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  · simp
    push_cast at hcast
    omega

theorem productSign_true_iff (x y : SVal) :
    productSign x y = true ↔ x.sign ≠ y.sign := by
  unfold productSign
  cases x.sign <;> cases y.sign <;> simp

/-- The largest magnitude a finite fp16 operand can have, in `2 ^ -24`
units. -/
def maxProductScaled : Nat := maxFiniteScaled * maxFiniteScaled

theorem productScaled_natAbs_le (x y : SVal)
    (hx : x.mag ≤ maxFiniteScaled) (hy : y.mag ≤ maxFiniteScaled) :
    (productScaled x y).natAbs ≤ maxProductScaled := by
  rw [productScaled_natAbs]
  exact Nat.mul_le_mul hx hy

/-- Exact-product specification: the signed value, its magnitude, its bound,
and its sign when the magnitude is nonzero. -/
theorem productScaled_spec (x y : SVal)
    (hx : x.mag ≤ maxFiniteScaled) (hy : y.mag ≤ maxFiniteScaled)
    (hpos : 0 < x.mag * y.mag) :
    productScaled x y = x.signed * y.signed ∧
      (productScaled x y).natAbs = x.mag * y.mag ∧
      (productScaled x y).natAbs ≤ maxProductScaled ∧
      (productScaled x y < 0 ↔ productSign x y = true) := by
  exact ⟨rfl, productScaled_natAbs x y,
    productScaled_natAbs_le x y hx hy, productScaled_neg_iff x y hpos⟩

/-! ## Exact product plus addend at the FMA scale -/

/-- Exact fused multiply-add in units of `2 ^ -48`: the product is exact and
the addend is shifted from its `2 ^ -24` representation. -/
def fmaScaled (x y c : SVal) : Int :=
  productScaled x y + c.signed * (2 ^ 24 : Nat)

theorem fmaScaled_eq (x y c : SVal) :
    fmaScaled x y c = x.signed * y.signed + c.signed * (2 ^ 24 : Nat) := rfl

/-- Largest fused-sum magnitude of three bounded finite operands. -/
def maxFmaScaled : Nat := maxProductScaled + maxFiniteScaled * 2 ^ 24

theorem fmaScaled_natAbs_le (x y c : SVal)
    (hx : x.mag ≤ maxFiniteScaled) (hy : y.mag ≤ maxFiniteScaled)
    (hc : c.mag ≤ maxFiniteScaled) :
    (fmaScaled x y c).natAbs ≤ maxFmaScaled := by
  unfold fmaScaled maxFmaScaled
  calc
    (productScaled x y + c.signed * (2 ^ 24 : Nat)).natAbs ≤
        (productScaled x y).natAbs + (c.signed * (2 ^ 24 : Nat)).natAbs :=
      Int.natAbs_add_le _ _
    _ = (productScaled x y).natAbs + c.mag * 2 ^ 24 := by
      rw [Int.natAbs_mul, SVal.natAbs_signed, Int.natAbs_natCast]
    _ ≤ maxProductScaled + maxFiniteScaled * 2 ^ 24 := by
      exact Nat.add_le_add (productScaled_natAbs_le x y hx hy)
        (Nat.mul_le_mul_right _ hc)

theorem maxFmaScaled_lt_pow81 : maxFmaScaled < 2 ^ 81 := by
  unfold maxFmaScaled maxProductScaled maxFiniteScaled
  decide

theorem fmaScaled_natAbs_lt_pow81 (x y c : SVal)
    (hx : x.mag ≤ maxFiniteScaled) (hy : y.mag ≤ maxFiniteScaled)
    (hc : c.mag ≤ maxFiniteScaled) :
    (fmaScaled x y c).natAbs < 2 ^ 81 :=
  Nat.lt_of_le_of_lt (fmaScaled_natAbs_le x y c hx hy hc) maxFmaScaled_lt_pow81

/-! ## A destination-binade selector at the FMA scale -/

/-- Biased destination exponent (the fp16 exponent field) of a fused
magnitude in units of `2 ^ -48`: zero below the minimum normal,
`log2 m - 33` above. -/
def fmaDestExp (m : Nat) : Nat :=
  if m < 2 ^ 34 then 0 else Nat.log2 m - 33

/-- Destination quantum of a fused magnitude in units of `2 ^ -48`: one
`2 ^ -24` unit in the subnormal range, `2 ^ (log2 m - 10)` above. -/
def fmaDestQuantum (m : Nat) : Nat :=
  if m < 2 ^ 34 then 2 ^ 24 else 2 ^ (Nat.log2 m - 10)

theorem fmaDestExp_of_lt {m : Nat} (h : m < 2 ^ 34) : fmaDestExp m = 0 := by
  unfold fmaDestExp
  rw [ite_eq_left h]

theorem fmaDestExp_of_ge {m : Nat} (h : 2 ^ 34 ≤ m) :
    fmaDestExp m = Nat.log2 m - 33 := by
  unfold fmaDestExp
  rw [ite_eq_right (by omega)]

theorem fmaDestQuantum_of_lt {m : Nat} (h : m < 2 ^ 34) :
    fmaDestQuantum m = 2 ^ 24 := by
  unfold fmaDestQuantum
  rw [ite_eq_left h]

theorem fmaDestQuantum_of_ge {m : Nat} (h : 2 ^ 34 ≤ m) :
    fmaDestQuantum m = 2 ^ (Nat.log2 m - 10) := by
  unfold fmaDestQuantum
  rw [ite_eq_right (by omega)]

theorem le_log2_of_two_pow34_le {m : Nat} (h : 2 ^ 34 ≤ m) :
    34 ≤ Nat.log2 m := by
  have hm0 : m ≠ 0 := by omega
  rw [Nat.le_log2 hm0]
  exact h

theorem fmaDestQuantum_pos (m : Nat) : 0 < fmaDestQuantum m := by
  by_cases h : m < 2 ^ 34
  · rw [fmaDestQuantum_of_lt h]
    exact Nat.two_pow_pos _
  · rw [fmaDestQuantum_of_ge (by omega)]
    exact Nat.two_pow_pos _

/-- The fine destination quantum is always a whole number of `2 ^ -24`
units, so a rounded fine integer scales back onto the coarse grid. -/
theorem fmaDestQuantum_dvd_two_pow24 (m : Nat) :
    (2 ^ 24 : Nat) ∣ fmaDestQuantum m := by
  by_cases h : m < 2 ^ 34
  · rw [fmaDestQuantum_of_lt h]
    exact Nat.dvd_refl _
  · rw [fmaDestQuantum_of_ge (by omega)]
    apply Nat.pow_dvd_pow
    have hlog : 34 ≤ Nat.log2 m := le_log2_of_two_pow34_le (by omega)
    omega

/-- The raw binade bound: exponent at most `30` exactly below `2 ^ 64`. -/
theorem fmaDestExp_le_30_iff (m : Nat) :
    fmaDestExp m ≤ 30 ↔ m < 2 ^ 64 := by
  by_cases hsmall : m < 2 ^ 34
  · rw [fmaDestExp_of_lt hsmall]
    constructor
    · intro _
      have h34 : (2 : Nat) ^ 34 < 2 ^ 64 := by decide
      omega
    · intro _
      omega
  · have hge : 2 ^ 34 ≤ m := by omega
    rw [fmaDestExp_of_ge hge]
    have hm0 : m ≠ 0 := by omega
    have hlog34 : 34 ≤ Nat.log2 m := le_log2_of_two_pow34_le hge
    constructor
    · intro h
      have hlog : Nat.log2 m < 64 := by omega
      have hlt := (Nat.log2_lt hm0).mp hlog
      simpa using hlt
    · intro h
      have hlog : Nat.log2 m < 64 := (Nat.log2_lt hm0).mpr (by simpa using h)
      omega

theorem fmaDestExp_le_30_of_lt_two_pow64 (m : Nat) (h : m < 2 ^ 64) :
    fmaDestExp m ≤ 30 :=
  (fmaDestExp_le_30_iff m).mpr h

/-- Lower bound for a normal fused destination: `1024 * q ≤ m`. -/
theorem fmaDestQuantum_mul_1024_le (m : Nat) (h : 2 ^ 34 ≤ m) :
    1024 * fmaDestQuantum m ≤ m := by
  rw [fmaDestQuantum_of_ge h]
  have hm0 : m ≠ 0 := by omega
  have hlog : 10 ≤ Nat.log2 m := by
    have := le_log2_of_two_pow34_le h
    omega
  have hle := ((Nat.log2_eq_iff hm0).mp rfl).1
  calc
    1024 * 2 ^ (Nat.log2 m - 10) =
        2 ^ 10 * 2 ^ (Nat.log2 m - 10) := by
      rw [show (1024 : Nat) = 2 ^ 10 by decide]
    _ = 2 ^ (10 + (Nat.log2 m - 10)) := by rw [Nat.pow_add]
    _ = 2 ^ Nat.log2 m := by
      congr 1
      omega
    _ ≤ m := hle

/-- Upper bound for a normal fused destination: `m < 2048 * q`. -/
theorem lt_fmaDestQuantum_mul_2048 (m : Nat) (h : 2 ^ 34 ≤ m) :
    m < 2048 * fmaDestQuantum m := by
  rw [fmaDestQuantum_of_ge h]
  have hm0 : m ≠ 0 := by omega
  have hlog : 10 ≤ Nat.log2 m := by
    have := le_log2_of_two_pow34_le h
    omega
  have hlt := ((Nat.log2_eq_iff hm0).mp rfl).2
  calc
    m < 2 ^ (Nat.log2 m + 1) := hlt
    _ = 2 ^ (11 + (Nat.log2 m - 10)) := by
      congr 1
      omega
    _ = 2 ^ 11 * 2 ^ (Nat.log2 m - 10) := by rw [Nat.pow_add]
    _ = 2048 * 2 ^ (Nat.log2 m - 10) := by
      rw [show (2048 : Nat) = 2 ^ 11 by decide]

/-- The destination selector reads the fused sum, not the addend: with
`64 * 64 = 4096` as the product and `2 ^ -24` as the addend, the product
dominates and the selector lands in the product binade. -/
theorem fmaDestExp_product_dominates_addend :
    fmaDestExp (fmaScaled ⟨false, 2 ^ 30⟩ ⟨false, 2 ^ 30⟩
      ⟨false, 1⟩).natAbs = 27 ∧
      fmaDestQuantum (fmaScaled ⟨false, 2 ^ 30⟩ ⟨false, 2 ^ 30⟩
        ⟨false, 1⟩).natAbs = 2 ^ 50 ∧
      destExp 1 = 0 := by
  decide


/-! ## The exact overflow threshold at the FMA scale -/

/-- The exact fp16 fused-overflow threshold in units of `2 ^ -48`: the
stage-156 threshold `4095 * 2 ^ 28` multiplied by the FMA scale `2 ^ 24`. -/
def fmaOverflowThreshold : Nat := overflowThreshold * 2 ^ 24

theorem fmaOverflowThreshold_value :
    fmaOverflowThreshold = 4095 * 2 ^ 52 := by
  unfold fmaOverflowThreshold overflowThreshold
  decide

theorem fmaOverflowThreshold_eq_two_pow64_sub_two_pow52 :
    fmaOverflowThreshold = 2 ^ 64 - 2 ^ 52 := by
  rw [fmaOverflowThreshold_value]

theorem fmaOverflowThreshold_lt_two_pow64 :
    fmaOverflowThreshold < 2 ^ 64 := by
  rw [fmaOverflowThreshold_eq_two_pow64_sub_two_pow52]
  have h : (2 : Nat) ^ 52 ≤ 2 ^ 64 := by decide
  omega

theorem fmaDestExp_le_30_of_lt_threshold {m : Nat}
    (h : m < fmaOverflowThreshold) : fmaDestExp m ≤ 30 :=
  fmaDestExp_le_30_of_lt_two_pow64 m
    (Nat.lt_trans h fmaOverflowThreshold_lt_two_pow64)

/-! ## Rounding a fused magnitude at the fine destination binade -/

/-- The fine-scale rounded magnitude before the scale is divided out. -/
def fmaRoundedFine (m : Nat) : Nat :=
  roundEvenNat (fmaDestQuantum m) m

/-- The fp16 magnitude (in `2 ^ -24` units) obtained by rounding at the
selected fine quantum. -/
def fmaRoundMag (m : Nat) : Nat :=
  fmaRoundedFine m / 2 ^ 24

theorem fmaRoundedFine_dvd_two_pow24 (m : Nat) :
    (2 ^ 24 : Nat) ∣ fmaRoundedFine m := by
  exact Nat.dvd_trans (fmaDestQuantum_dvd_two_pow24 m)
    (roundEvenNat_dvd (fmaDestQuantum m) m)

theorem fmaRoundMag_mul_two_pow24 (m : Nat) :
    fmaRoundMag m * 2 ^ 24 = fmaRoundedFine m := by
  unfold fmaRoundMag
  exact Nat.div_mul_cancel (fmaRoundedFine_dvd_two_pow24 m)

/-- A rounded fine value selects a quotient in `[1024, 2048]` whenever the
exact magnitude lies in the selected normal binade. -/
theorem roundEvenNat_div_mem_of_bounds (q m : Nat) (hq : 0 < q)
    (hlo : 1024 * q ≤ m) (hhi : m < 2048 * q) :
    1024 ≤ roundEvenNat q m / q ∧ roundEvenNat q m / q ≤ 2048 := by
  have hr := roundEvenNat_div_mul q m
  have hhalf : q / 2 < q := Nat.div_lt_self hq (by decide)
  constructor
  · exact Nat.le_of_not_lt (by
      intro hlt
      have hk : roundEvenNat q m / q ≤ 1023 := by omega
      have hkq : roundEvenNat q m / q * q ≤ 1023 * q :=
        Nat.mul_le_mul_right _ hk
      have hle := le_roundEvenNat_add_half q m hq
      rw [← hr] at hle
      omega)
  · apply Nat.le_of_lt_succ
    exact Nat.lt_of_not_le (by
      intro hk
      have hkq : 2049 * q ≤ roundEvenNat q m / q * q :=
        Nat.mul_le_mul_right _ hk
      have hle := roundEvenNat_le_add_half q m hq
      rw [← hr] at hle
      omega)

/-- The coarse magnitude is the rounded fine value divided by the scale. -/
theorem fmaRoundMag_eq_div (m : Nat) :
    fmaRoundMag m = fmaRoundedFine m / 2 ^ 24 := rfl

theorem fmaRoundMag_le_1024_of_lt {m : Nat} (h : m < 2 ^ 34) :
    fmaRoundMag m ≤ 1024 := by
  unfold fmaRoundMag fmaRoundedFine
  rw [fmaDestQuantum_of_lt h]
  have hq : 0 < 2 ^ 24 := by decide
  have hle := roundEvenNat_le_add_half (2 ^ 24) m hq
  have hhalf : 2 ^ 24 / 2 = 2 ^ 23 := by decide
  rw [hhalf] at hle
  apply Nat.le_of_lt_succ
  rw [Nat.div_lt_iff_lt_mul hq]
  have hpow : (2 : Nat) ^ 34 = 1024 * 2 ^ 24 := by decide
  have hsucc : (1025 : Nat) * 2 ^ 24 = 1024 * 2 ^ 24 + 2 ^ 24 := by
    rw [Nat.succ_mul]
  omega

/-- If the exact fused magnitude is below the overflow threshold, the rounded
fine integer is below `2 ^ 64`, i.e. below the first unrepresentable fp16
value. -/
theorem fmaRoundedFine_lt_two_pow64_of_lt_threshold (m : Nat)
    (hm : m < fmaOverflowThreshold) : fmaRoundedFine m < 2 ^ 64 := by
  unfold fmaRoundedFine
  by_cases hsmall : m < 2 ^ 34
  · rw [fmaDestQuantum_of_lt hsmall]
    have hq : 0 < 2 ^ 24 := by decide
    have hle := roundEvenNat_le_add_half (2 ^ 24) m hq
    have hhalf : 2 ^ 24 / 2 = 2 ^ 23 := by decide
    rw [hhalf] at hle
    have h34 : (2 : Nat) ^ 34 < 2 ^ 64 := by decide
    omega
  · have hge : 2 ^ 34 ≤ m := by omega
    rw [fmaDestQuantum_of_ge hge]
    have hm0 : m ≠ 0 := by omega
    have hm64 : m < 2 ^ 64 :=
      Nat.lt_trans hm fmaOverflowThreshold_lt_two_pow64
    have hlog : Nat.log2 m < 64 := (Nat.log2_lt hm0).mpr hm64
    have hlog10 : 10 ≤ Nat.log2 m := by
      have := le_log2_of_two_pow34_le hge
      omega
    have hqle : 2 ^ (Nat.log2 m - 10) ≤ 2 ^ 53 := by
      apply Nat.pow_le_pow_right (by decide)
      omega
    have hhalfle : 2 ^ (Nat.log2 m - 10) / 2 ≤ 2 ^ 52 := by
      have hdiv : 2 ^ 53 / 2 = 2 ^ 52 := by decide
      rw [← hdiv]
      exact Nat.div_le_div_right hqle
    have hle := roundEvenNat_le_add_half (2 ^ (Nat.log2 m - 10)) m
      (Nat.two_pow_pos _)
    have hthr : fmaOverflowThreshold = 2 ^ 64 - 2 ^ 52 :=
      fmaOverflowThreshold_eq_two_pow64_sub_two_pow52
    have h52 : (2 : Nat) ^ 52 ≤ 2 ^ 64 := by decide
    omega

/-- The rounded coarse magnitude is below `2 ^ 40` (the first overflowing
fp16 magnitude) whenever the exact fused sum is below the threshold. -/
theorem fmaRoundMag_lt_two_pow40_of_lt_threshold (m : Nat)
    (hm : m < fmaOverflowThreshold) : fmaRoundMag m < 2 ^ 40 := by
  have hR := fmaRoundedFine_lt_two_pow64_of_lt_threshold m hm
  have hmul := fmaRoundMag_mul_two_pow24 m
  have hpow : (2 : Nat) ^ 64 = 2 ^ 40 * 2 ^ 24 := by decide
  rw [hpow, ← hmul] at hR
  have hle : fmaRoundMag m ≤ 2 ^ 40 :=
    Nat.le_of_mul_le_mul_right (Nat.le_of_lt hR) (by decide)
  exact Nat.lt_of_le_of_ne hle (by
    intro heq
    rw [heq] at hR
    exact Nat.lt_irrefl _ hR)

/-! ## One rounding of the exact fused sum -/

/-- Hardware-style single rounding: round the exact `2 ^ -48` fused sum at
the destination quantum, then accept the result exactly when the rounded
fine integer is below `2 ^ 64` (the first unrepresentable fp16 magnitude). -/
def roundFmaScaled (Z : Int) (sm sc : Bool) : Fp16Val :=
  if Z = 0 then
    .fin { sign := zeroSign sm sc, mag := 0 }
  else if fmaRoundedFine Z.natAbs < 2 ^ 64 then
    .fin { sign := Z < 0, mag := fmaRoundMag Z.natAbs }
  else .inf (Z < 0)

/-- The IEEE round-to-nearest-even value at the destination binade, with the
exact finite-range threshold made explicit. -/
def rneFmaScaled (Z : Int) (sm sc : Bool) : Fp16Val :=
  if Z = 0 then
    .fin { sign := zeroSign sm sc, mag := 0 }
  else if Z.natAbs < fmaOverflowThreshold then
    .fin { sign := Z < 0, mag := fmaRoundMag Z.natAbs }
  else .inf (Z < 0)

theorem roundFmaScaled_eq_rne (Z : Int) (sm sc : Bool)
    (hfin : Z.natAbs < fmaOverflowThreshold) :
    roundFmaScaled Z sm sc = rneFmaScaled Z sm sc := by
  by_cases hz : Z = 0
  · subst hz
    simp [roundFmaScaled, rneFmaScaled]
  · unfold roundFmaScaled rneFmaScaled
    rw [ite_eq_right hz, ite_eq_right hz, ite_eq_left hfin]
    rw [ite_eq_left (fmaRoundedFine_lt_two_pow64_of_lt_threshold _ hfin)]

/-- Scaling a finite value's magnitude scales its signed integer. -/
theorem SVal.signed_scale_mul (s : Bool) (a b : Nat) (h : a * 2 ^ 24 = b) :
    (⟨s, a⟩ : SVal).signed * (2 ^ 24 : Nat) =
      (⟨s, b⟩ : SVal).signed := by
  have hpow : ((2 ^ 24 : Nat) : Int) = (16777216 : Int) := by decide
  cases s
  · simp [SVal.signed]
    rw [← hpow, ← Int.natCast_mul, h]
  · simp [SVal.signed]
    rw [Int.neg_mul]
    congr 1
    rw [← hpow, ← Int.natCast_mul, h]

/-- The rounded value's signed integer, multiplied back by `2 ^ 24`, is exactly
`roundEven` of the fused sum at the selected fine quantum. -/
theorem rneFmaScaled_signed (Z : Int) (sm sc : Bool)
    (hfin : Z.natAbs < fmaOverflowThreshold) :
    ∃ v : SVal, rneFmaScaled Z sm sc = .fin v ∧
      v.signed * (2 ^ 24 : Nat) =
        roundEven (fmaDestQuantum Z.natAbs) Z := by
  by_cases hz : Z = 0
  · subst hz
    refine ⟨⟨zeroSign sm sc, 0⟩, ?_, ?_⟩
    · simp [rneFmaScaled]
    · simp [SVal.signed, roundEven_zero]
  · refine ⟨⟨Z < 0, fmaRoundMag Z.natAbs⟩, ?_, ?_⟩
    · unfold rneFmaScaled
      rw [ite_eq_right hz, ite_eq_left hfin]
    · have hmul := fmaRoundMag_mul_two_pow24 Z.natAbs
      have hscale := SVal.signed_scale_mul (Z < 0) (fmaRoundMag Z.natAbs)
        (fmaRoundedFine Z.natAbs) hmul
      rw [hscale]
      simpa [fmaRoundedFine] using
        (SVal.signed_mk_roundEvenNat (fmaDestQuantum Z.natAbs) Z)

/-- The fused rounding theorem at the operand level: for three finite fp16
values whose exact fused sum is below the overflow threshold, one rounding of
the exact product-plus-add equals IEEE RNE at the selected destination binade.
The zero branch uses the product sign and the addend sign. -/
theorem fmaScaled_eq_rne (x y c : SVal)
    (_hx : x.mag ≤ maxFiniteScaled) (_hy : y.mag ≤ maxFiniteScaled)
    (_hc : c.mag ≤ maxFiniteScaled)
    (hfin : (fmaScaled x y c).natAbs < fmaOverflowThreshold) :
    roundFmaScaled (fmaScaled x y c) (productSign x y) c.sign =
      rneFmaScaled (fmaScaled x y c) (productSign x y) c.sign :=
  roundFmaScaled_eq_rne _ _ _ hfin

/-- The finite fused result below the overflow threshold has a representable
coarse magnitude below `2 ^ 40`, and its signed integer is IEEE RNE of the
exact fused sum at the selected fine quantum (after scaling back by
`2 ^ 24`). -/
theorem fmaScaled_fin (x y c : SVal)
    (hx : x.mag ≤ maxFiniteScaled) (hy : y.mag ≤ maxFiniteScaled)
    (hc : c.mag ≤ maxFiniteScaled)
    (hfin : (fmaScaled x y c).natAbs < fmaOverflowThreshold) :
    ∃ v : SVal,
      roundFmaScaled (fmaScaled x y c) (productSign x y) c.sign = .fin v ∧
      v.mag < 2 ^ 40 ∧
      v.signed * (2 ^ 24 : Nat) =
        roundEven (fmaDestQuantum (fmaScaled x y c).natAbs)
          (fmaScaled x y c) := by
  have hrne := rneFmaScaled_signed (fmaScaled x y c) (productSign x y) c.sign hfin
  obtain ⟨v, hv, hvs⟩ := hrne
  refine ⟨v, ?_, ?_, hvs⟩
  · rw [fmaScaled_eq_rne x y c hx hy hc hfin, hv]
  · unfold rneFmaScaled at hv
    by_cases hz : fmaScaled x y c = 0
    · rw [ite_eq_left hz] at hv
      have hvz : v = ⟨zeroSign (productSign x y) c.sign, 0⟩ :=
        (Fp16Val.fin.inj hv).symm
      rw [hvz]
      have h40 : (0 : Nat) < 2 ^ 40 := Nat.two_pow_pos 40
      exact h40
    · rw [ite_eq_right hz, ite_eq_left hfin] at hv
      have hveq : v = ⟨fmaScaled x y c < 0, fmaRoundMag (fmaScaled x y c).natAbs⟩ :=
        (Fp16Val.fin.inj hv).symm
      rw [hveq]
      exact fmaRoundMag_lt_two_pow40_of_lt_threshold _ hfin

/-! ## Value-level fused multiply-add -/

/-- Multiply by an infinity with product sign `s`, then add the third operand.
NaN addends are quieted by the outer `fma` match; this helper is total. -/
def addInfProduct (s : Bool) : Fp16Val → Fp16Val
  | .inf c => if s = c then .inf s else .nan false 0 true
  | .fin _ => .inf s
  | .nan ng p _ => .nan ng p true

/-- Value-level IEEE fp16 fused multiply-add. NaNs propagate left-to-right and
are quieted, `0 * inf` is invalid, the product sign is the xor of the operand
signs, and three finite operands round the exact product-plus-add once. -/
def fma : Fp16Val → Fp16Val → Fp16Val → Fp16Val
  | .nan ng p _, _, _ => .nan ng p true
  | _, .nan ng p _, _ => .nan ng p true
  | _, _, .nan ng p _ => .nan ng p true
  | .inf a, .inf b, c => addInfProduct (a != b) c
  | .inf a, .fin y, c =>
      if y.mag = 0 then .nan false 0 true else addInfProduct (a != y.sign) c
  | .fin x, .inf b, c =>
      if x.mag = 0 then .nan false 0 true else addInfProduct (x.sign != b) c
  | .fin _, .fin _, .inf c => .inf c
  | .fin x, .fin y, .fin c =>
      rneFmaScaled (fmaScaled x y c) (productSign x y) c.sign

theorem fma_fin_fin_fin (x y c : SVal) :
    fma (.fin x) (.fin y) (.fin c) =
      rneFmaScaled (fmaScaled x y c) (productSign x y) c.sign := rfl

/-- The finite fused result: below the overflow threshold, the value-level
`fma` agrees with the hardware single-rounding model, is finite, has magnitude
below `2 ^ 40`, and its signed integer is IEEE RNE of the exact fused sum. -/
theorem fma_fin (x y c : SVal)
    (hx : x.mag ≤ maxFiniteScaled) (hy : y.mag ≤ maxFiniteScaled)
    (hc : c.mag ≤ maxFiniteScaled)
    (hfin : (fmaScaled x y c).natAbs < fmaOverflowThreshold) :
    fma (.fin x) (.fin y) (.fin c) =
        roundFmaScaled (fmaScaled x y c) (productSign x y) c.sign ∧
      ∃ v : SVal,
        fma (.fin x) (.fin y) (.fin c) = .fin v ∧
        v.mag < 2 ^ 40 ∧
        v.signed * (2 ^ 24 : Nat) =
          roundEven (fmaDestQuantum (fmaScaled x y c).natAbs)
            (fmaScaled x y c) := by
  have hrne := fmaScaled_eq_rne x y c hx hy hc hfin
  have hround := fmaScaled_fin x y c hx hy hc hfin
  constructor
  · rw [fma_fin_fin_fin, ← hrne]
  · obtain ⟨v, hv, hmag, hvs⟩ := hround
    refine ⟨v, ?_, hmag, hvs⟩
    rw [fma_fin_fin_fin, ← hrne, hv]

/-- Rounding the exact product first, then adding the addend. The zero sign is
the product sign on both slots, so a zero product keeps its xor sign. -/
def roundProductScaled (x y : SVal) : Fp16Val :=
  roundFmaScaled (productScaled x y) (productSign x y) (productSign x y)

/-! ## A double-rounding counterexample -/

/-- `1 + 2 ^ -10`, `1 + 3 * 2 ^ -10` and `-1`, chosen so the product is
`1 + 2 ^ -8 + 3 * 2 ^ -20`. The separate path rounds the product to
`1 + 2 ^ -8` and then subtracts one, giving `2 ^ -8 = 0x1C00`. The fused path
retains `3 * 2 ^ -20`, which is three quarters of the next binade's quantum,
and rounds to `2 ^ -8 + 2 ^ -18 = 0x1C01`. -/
theorem fma_double_rounding_counterexample :
    decodeFull (0x3C01 : Fp16) = .fin ⟨false, 16793600⟩ ∧
      decodeFull (0x3C03 : Fp16) = .fin ⟨false, 16826368⟩ ∧
      decodeFull (0xBC00 : Fp16) = .fin ⟨true, 16777216⟩ ∧
      decodeFull (0x1C00 : Fp16) = .fin ⟨false, 65536⟩ ∧
      decodeFull (0x1C01 : Fp16) = .fin ⟨false, 65600⟩ ∧
      fma (decodeFull (0x3C01 : Fp16)) (decodeFull (0x3C03 : Fp16))
        (decodeFull (0xBC00 : Fp16)) = decodeFull (0x1C01 : Fp16) ∧
      addGeneral (roundProductScaled ⟨false, 16793600⟩ ⟨false, 16826368⟩)
        (.fin ⟨true, 16777216⟩) = decodeFull (0x1C00 : Fp16) ∧
      decodeFull (0x1C01 : Fp16) ≠ decodeFull (0x1C00 : Fp16) := by
  decide

/-! ## Exception flags for fused multiply-add -/

/-- Whether rounding the exact fused sum at its fine destination quantum
changes it. -/
def fmaInexactAt (Z : Int) : Bool :=
  decide (roundEven (fmaDestQuantum Z.natAbs) Z ≠ Z)

/-- Tininess after rounding on the `2 ^ -48` grid: the rounded magnitude is
below the minimum normal `1024 * 2 ^ 24` fine units. -/
def fmaTinyAfter (Z : Int) : Bool :=
  decide ((roundEven (fmaDestQuantum Z.natAbs) Z).natAbs < 1024 * 2 ^ 24)

/-- Flags for the finite fused branch. Overflow is the exact FMA threshold and
also sets inexact; otherwise the after-rounding underflow rule is used. -/
def fmaFiniteFlags (Z : Int) : Flags :=
  if fmaOverflowThreshold ≤ Z.natAbs then
    Flags.overflowInexact
  else
    { invalid := false
      divByZero := false
      overflow := false
      underflow := fmaInexactAt Z && fmaTinyAfter Z
      inexact := fmaInexactAt Z }

/-- Flags for an infinite product: an opposite-sign infinite addend is invalid,
and every finite addend plus an infinite product is exact. -/
def fmaInfProductFlags (s : Bool) : Fp16Val → Flags
  | .inf c => if s = c then Flags.none else Flags.invalidOnly
  | _ => Flags.none

/-- Exception flags for value-level fp16 FMA. NaN operands and `0 * inf` are
invalid; infinite products with a finite addend raise nothing; finite
operands use `fmaFiniteFlags`. -/
def fmaFlags : Fp16Val → Fp16Val → Fp16Val → Flags
  | .nan _ _ _, _, _ => Flags.invalidOnly
  | _, .nan _ _ _, _ => Flags.invalidOnly
  | _, _, .nan _ _ _ => Flags.invalidOnly
  | .inf a, .inf b, c => fmaInfProductFlags (a != b) c
  | .inf a, .fin y, c =>
      if y.mag = 0 then Flags.invalidOnly
      else fmaInfProductFlags (a != y.sign) c
  | .fin x, .inf b, c =>
      if x.mag = 0 then Flags.invalidOnly
      else fmaInfProductFlags (x.sign != b) c
  | .fin _, .fin _, .inf _ => Flags.none
  | .fin x, .fin y, .fin c => fmaFiniteFlags (fmaScaled x y c)

/-! ### Special-value flags -/

theorem fmaFlags_nan_left (ng : Bool) (p : Nat) (q : Bool) (y c : Fp16Val) :
    (fmaFlags (.nan ng p q) y c).invalid = true := by
  cases y <;> cases c <;> rfl

theorem fmaFlags_nan_mid (x : Fp16Val) (ng : Bool) (p : Nat) (q : Bool)
    (c : Fp16Val) :
    (fmaFlags x (.nan ng p q) c).invalid = true := by
  cases x <;> cases c <;> rfl

theorem fmaFlags_nan_addend (x y : Fp16Val) (ng : Bool) (p : Nat) (q : Bool) :
    (fmaFlags x y (.nan ng p q)).invalid = true := by
  cases x <;> cases y <;> rfl

/-- `0 * inf` is invalid in either operand order, whatever the addend is. -/
theorem fmaFlags_zero_inf (a : Bool) (c : Fp16Val) :
    (fmaFlags (.fin ⟨false, 0⟩) (.inf a) c).invalid = true := by
  cases c <;> rfl

theorem fmaFlags_inf_zero (a : Bool) (c : Fp16Val) :
    (fmaFlags (.inf a) (.fin ⟨false, 0⟩) c).invalid = true := by
  cases c <;> rfl

theorem fma_zero_inf_of_not_nan (a : Bool) (c : Fp16Val)
    (hc : c.isNan = false) :
    fma (.fin ⟨false, 0⟩) (.inf a) c = .nan false 0 true := by
  cases c with
  | nan ng p q => simp [Fp16Val.isNan] at hc
  | fin z => simp [fma]
  | inf b => simp [fma]

theorem fma_inf_zero_of_not_nan (a : Bool) (c : Fp16Val)
    (hc : c.isNan = false) :
    fma (.inf a) (.fin ⟨false, 0⟩) c = .nan false 0 true := by
  cases c with
  | nan ng p q => simp [Fp16Val.isNan] at hc
  | fin z => simp [fma]
  | inf b => simp [fma]

theorem fmaFlags_inf_fin_none (a : Bool) (y z : SVal) (hy : y.mag ≠ 0) :
    fmaFlags (.inf a) (.fin y) (.fin z) = Flags.none := by
  simp [fmaFlags, hy, fmaInfProductFlags]

/-! ### Overflow and inexactness -/

theorem fmaFiniteFlags_overflow (Z : Int)
    (h : fmaOverflowThreshold ≤ Z.natAbs) :
    fmaFiniteFlags Z = Flags.overflowInexact := by
  simp [fmaFiniteFlags, h]

theorem fmaFiniteFlags_overflow_bits (Z : Int)
    (h : fmaOverflowThreshold ≤ Z.natAbs) :
    (fmaFiniteFlags Z).overflow = true ∧
      (fmaFiniteFlags Z).inexact = true := by
  rw [fmaFiniteFlags_overflow Z h]
  exact ⟨rfl, rfl⟩

theorem fmaFiniteFlags_inexact_iff (Z : Int)
    (hfin : Z.natAbs < fmaOverflowThreshold) :
    (fmaFiniteFlags Z).inexact = true ↔
      roundEven (fmaDestQuantum Z.natAbs) Z ≠ Z := by
  have hnot : ¬ fmaOverflowThreshold ≤ Z.natAbs := by omega
  simp only [fmaFiniteFlags, hnot, ite_false, fmaInexactAt]
  constructor
  · exact of_decide_eq_true
  · exact decide_eq_true

/-- The finite fused branch reports overflow and inexact exactly when the
exact fused sum reaches the FMA threshold. -/
theorem fmaFlags_fin_overflow (x y c : SVal)
    (h : fmaOverflowThreshold ≤ (fmaScaled x y c).natAbs) :
    fmaFlags (.fin x) (.fin y) (.fin c) = Flags.overflowInexact := by
  rw [show fmaFlags (.fin x) (.fin y) (.fin c) =
      fmaFiniteFlags (fmaScaled x y c) from rfl]
  exact fmaFiniteFlags_overflow _ h

/-- At or above the exact threshold the finite fused branch returns infinity
with the sign of the exact sum. -/
theorem fma_fin_overflow_result (x y c : SVal)
    (h : fmaOverflowThreshold ≤ (fmaScaled x y c).natAbs) :
    fma (.fin x) (.fin y) (.fin c) = .inf (fmaScaled x y c < 0) := by
  rw [fma_fin_fin_fin]
  unfold rneFmaScaled
  have hpos : 0 < fmaOverflowThreshold := by decide
  have hz : fmaScaled x y c ≠ 0 := by
    intro hzero
    rw [hzero] at h
    simp at h
    omega
  rw [ite_eq_right hz, ite_eq_right (by omega : ¬ (fmaScaled x y c).natAbs <
    fmaOverflowThreshold)]
/-- Overflow and inexact are both raised for a finite fused sum at or above
the exact threshold. -/
theorem fmaFlags_fin_overflow_bits (x y c : SVal)
    (h : fmaOverflowThreshold ≤ (fmaScaled x y c).natAbs) :
    (fmaFlags (.fin x) (.fin y) (.fin c)).overflow = true ∧
      (fmaFlags (.fin x) (.fin y) (.fin c)).inexact = true := by
  rw [fmaFlags_fin_overflow x y c h]
  exact ⟨rfl, rfl⟩

/-- Below the threshold, the fused branch is inexact exactly when the exact
product-plus-add is not on the selected fine quantum grid. -/
theorem fmaFlags_fin_inexact_iff (x y c : SVal)
    (hfin : (fmaScaled x y c).natAbs < fmaOverflowThreshold) :
    (fmaFlags (.fin x) (.fin y) (.fin c)).inexact = true ↔
      roundEven (fmaDestQuantum (fmaScaled x y c).natAbs)
        (fmaScaled x y c) ≠ fmaScaled x y c := by
  rw [show fmaFlags (.fin x) (.fin y) (.fin c) =
      fmaFiniteFlags (fmaScaled x y c) from rfl]
  exact fmaFiniteFlags_inexact_iff _ hfin


/-- A tiny fused product can raise underflow, unlike decoded fp16 addition:
the product of two smallest subnormals is `2 ^ -48`, one fine unit, which
rounds to zero at the subnormal quantum `2 ^ -24`. -/
theorem fmaFlags_smallest_product_underflow :
    (fmaFlags (.fin ⟨false, 1⟩) (.fin ⟨false, 1⟩) (.fin ⟨false, 0⟩)).underflow
      = true := by
  decide

/-! ## The exact finite range, in both directions -/

/-- In the top finite binade, any magnitude from the overflow threshold up to
`2 ^ 64` rounds to `2 ^ 64`: the threshold is the tie and ties-to-even selects
the even upper endpoint. -/
theorem fmaRoundedFine_top_binade (m : Nat)
    (hlo : fmaOverflowThreshold ≤ m) (hhi : m < 2 ^ 64) :
    fmaRoundedFine m = 2 ^ 64 := by
  unfold fmaRoundedFine
  have h34 : 2 ^ 34 ≤ m := by
    have hT : (2 : Nat) ^ 34 < fmaOverflowThreshold := by decide
    omega
  rw [fmaDestQuantum_of_ge h34]
  have hm0 : m ≠ 0 := by omega
  have hlog : Nat.log2 m = 63 := by
    rw [Nat.log2_eq_iff hm0]
    constructor
    · have h63 : (2 : Nat) ^ 63 ≤ fmaOverflowThreshold := by decide
      omega
    · simpa using hhi
  rw [hlog]
  have hq : (2 : Nat) ^ 53 % 2 = 0 := by decide
  have hk : 2047 % 2 = 1 := by decide
  have hT : fmaOverflowThreshold = 2047 * 2 ^ 53 + 2 ^ 52 := by
    rw [fmaOverflowThreshold_value]
  have hhalf : (2 : Nat) ^ 53 / 2 = 2 ^ 52 := by decide
  have hr1 : (2 : Nat) ^ 53 / 2 ≤ m - 2047 * 2 ^ 53 := by omega
  have hr2 : m - 2047 * 2 ^ 53 < 2 ^ 53 := by
    have h64 : (2 : Nat) ^ 64 = 2048 * 2 ^ 53 := by decide
    omega
  have hsum : 2047 * 2 ^ 53 + (m - 2047 * 2 ^ 53) = m := by omega
  rw [← hsum]
  rw [roundEvenNat_eq_succ_mul_of_half_le (2 ^ 53) 2047
    (m - 2047 * 2 ^ 53) (by decide) hq hk hr1 hr2]

/-- At and above the exact threshold the rounded fine value reaches the first
unrepresentable fp16 magnitude `2 ^ 64`. -/
theorem fmaRoundedFine_ge_two_pow64_of_threshold_le (m : Nat)
    (h : fmaOverflowThreshold ≤ m) : 2 ^ 64 ≤ fmaRoundedFine m := by
  by_cases htop : m < 2 ^ 64
  · rw [fmaRoundedFine_top_binade m h htop]
    exact Nat.le_refl _
  · have hm64 : 2 ^ 64 ≤ m := by omega
    unfold fmaRoundedFine
    have h34 : 2 ^ 34 ≤ m := by omega
    rw [fmaDestQuantum_of_ge h34]
    have hm0 : m ≠ 0 := by omega
    have hlog : 64 ≤ Nat.log2 m := by
      rw [Nat.le_log2 hm0]
      exact hm64
    have hqpos : 0 < 2 ^ (Nat.log2 m - 10) := Nat.two_pow_pos _
    have hlo : 1024 * 2 ^ (Nat.log2 m - 10) ≤ m := by
      simpa [fmaDestQuantum_of_ge h34] using fmaDestQuantum_mul_1024_le m h34
    have hhi : m < 2048 * 2 ^ (Nat.log2 m - 10) := by
      simpa [fmaDestQuantum_of_ge h34] using lt_fmaDestQuantum_mul_2048 m h34
    have hmem := (roundEvenNat_div_mem_of_bounds (2 ^ (Nat.log2 m - 10)) m
      hqpos hlo hhi).1
    have hr := roundEvenNat_div_mul (2 ^ (Nat.log2 m - 10)) m
    have hpow : 1024 * 2 ^ (Nat.log2 m - 10) = 2 ^ Nat.log2 m := by
      calc
        1024 * 2 ^ (Nat.log2 m - 10) =
            2 ^ 10 * 2 ^ (Nat.log2 m - 10) := by
          rw [show (1024 : Nat) = 2 ^ 10 by decide]
        _ = 2 ^ (10 + (Nat.log2 m - 10)) := by rw [Nat.pow_add]
        _ = 2 ^ Nat.log2 m := by
          congr 1
          omega
    calc
      2 ^ 64 ≤ 1024 * 2 ^ (Nat.log2 m - 10) := by
        rw [hpow]
        exact Nat.pow_le_pow_right (by decide) hlog
      _ ≤ (roundEvenNat (2 ^ (Nat.log2 m - 10)) m /
            2 ^ (Nat.log2 m - 10)) * 2 ^ (Nat.log2 m - 10) :=
        Nat.mul_le_mul_right _ hmem
      _ = roundEvenNat (2 ^ (Nat.log2 m - 10)) m := hr

theorem fmaRoundedFine_threshold :
    fmaRoundedFine fmaOverflowThreshold = 2 ^ 64 :=
  fmaRoundedFine_top_binade _ (Nat.le_refl _) fmaOverflowThreshold_lt_two_pow64

/-- The exact finite-range criterion for one-rounding fp16 FMA: the result is
finite exactly when the exact fused sum is below the threshold. -/
theorem roundFmaScaled_fin_iff (Z : Int) (sm sc : Bool) :
    (∃ v : SVal, roundFmaScaled Z sm sc = .fin v) ↔
      Z.natAbs < fmaOverflowThreshold := by
  by_cases hz : Z = 0
  · subst hz
    have hpos : 0 < fmaOverflowThreshold := by decide
    constructor
    · intro _; exact hpos
    · intro _
      exact ⟨⟨zeroSign sm sc, 0⟩, by simp [roundFmaScaled]⟩
  · unfold roundFmaScaled
    rw [ite_eq_right hz]
    constructor
    · rintro ⟨v, hv⟩
      by_cases hlt : Z.natAbs < fmaOverflowThreshold
      · exact hlt
      · exfalso
        have hge : fmaOverflowThreshold ≤ Z.natAbs := by omega
        have hRge := fmaRoundedFine_ge_two_pow64_of_threshold_le _ hge
        have hnotlt : ¬ fmaRoundedFine Z.natAbs < 2 ^ 64 := by omega
        rw [ite_eq_right hnotlt] at hv
        cases hv
    · intro hlt
      refine ⟨⟨Z < 0, fmaRoundMag Z.natAbs⟩, ?_⟩
      rw [ite_eq_left (fmaRoundedFine_lt_two_pow64_of_lt_threshold _ hlt)]

end IntelGpu
