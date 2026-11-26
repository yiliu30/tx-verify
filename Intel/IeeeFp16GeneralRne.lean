-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.IeeeFp16Special

@[expose] public section

/-!
# General per-binade round-to-nearest-even for fp16 addition

Stage 156 (`Intel.IeeeFp16Special`) rounds an exact `2 ^ -24` integer with
`roundScaled`, which picks its destination binade from `Nat.log2`, but proves
that implementation only for the subnormal/crossing class, the binade-2 tie
cases and the overflow threshold. This module closes the "general per-binade
RNE" gap for every finite result.

- `destExp` / `destQuantum` / `destMant`: the destination-binade selector.
  Subnormal magnitudes below `1024` use exponent zero and quantum one; a
  magnitude `m` with `1024 ≤ m < 2 ^ 40` uses exponent `Nat.log2 m - 9` and
  quantum `2 ^ (Nat.log2 m - 10)`.
- `destExp_le_30_iff`: the exact no-overflow bound, `destExp m ≤ 30 ↔
  m < 2 ^ 40`; `destQuantum_mul_1024_le` / `lt_destQuantum_mul_2048` are the
  exact binade bounds, and `destMant_mem` shows the truncated significand is
  an 11-bit value in `[1024, 2047]`.
- `roundEvenNat_destQuantum_div_mem`: the rounded quotient is also in
  `[1024, 2048]`; `2048` is the next binade.
- `rneScaled`: IEEE round-to-nearest-even at the selected destination binade.
- `roundScaled_eq_rne`: for every exact sum magnitude below the stage-156
  overflow threshold `4095 * 2 ^ 28`, `roundScaled` is exactly `rneScaled`.
  This covers every finite binade, subnormal through exponent 30, not just
  subnormal/binade 2.
- `addGeneral`: the value-level addition whose finite clause uses `rneScaled`.
  `addGeneral_eq_addFull_of_lt_threshold` proves it agrees with stage 156's
  `addFull` on the entire finite range; `addGeneral_fin` records the general
  finite result and its signed IEEE value.
- `addGeneral_zero_zero`, `addGeneral_nan_left`, `addGeneral_inf_same`,
  `addGeneral_inf_opposite`, `addGeneral_inf_fin`, `addGeneral_fin_inf`: the
  NaN/Inf/signed-zero rules are restated and proved identical to stage 156.
- `rounding_without_alignment_counterexample`: rounding `2049` units at the
  global `2 ^ -24` quantum gives `2049`, which is not a binade-2 significand;
  the destination quantum is `2` and RNE gives `2048`.

The finite-range hypothesis is exact. At and above `overflowThreshold` the
stage-156 theorem `roundScaled_overflow` already sends the result to infinity;
this module does not duplicate that branch and makes no claim about it beyond
the existing theorem. There are no new axioms, no `native_decide` and no
`sorry`; the proofs use only the core library and stage 149/156 lemmas.
-/

namespace IntelGpu

/-! ## The destination-binade selector -/

/-- Unbiased destination exponent of a scaled magnitude: zero for the
subnormal/first-normal quantum, `Nat.log2 m - 9` above it. -/
def destExp (m : Nat) : Nat :=
  if m < 1024 then 0 else Nat.log2 m - 9

/-- Destination quantum in units of `2 ^ -24`. -/
def destQuantum (m : Nat) : Nat :=
  if m < 1024 then 1 else 2 ^ (Nat.log2 m - 10)

/-- Truncated destination significand before rounding. -/
def destMant (m : Nat) : Nat :=
  m / destQuantum m

theorem destExp_of_lt {m : Nat} (h : m < 1024) : destExp m = 0 := by
  unfold destExp
  rw [ite_eq_left h]

theorem destExp_of_ge {m : Nat} (h : 1024 ≤ m) : destExp m = Nat.log2 m - 9 := by
  unfold destExp
  rw [ite_eq_right (by omega)]

theorem destQuantum_of_lt {m : Nat} (h : m < 1024) : destQuantum m = 1 := by
  unfold destQuantum
  rw [ite_eq_left h]

theorem destQuantum_of_ge {m : Nat} (h : 1024 ≤ m) :
    destQuantum m = 2 ^ (Nat.log2 m - 10) := by
  unfold destQuantum
  rw [ite_eq_right (by omega)]

theorem le_log2_of_1024_le {m : Nat} (h : 1024 ≤ m) : 10 ≤ Nat.log2 m := by
  have hm0 : m ≠ 0 := by omega
  rw [Nat.le_log2 hm0]
  simpa [show (2 : Nat) ^ 10 = 1024 by decide] using h

theorem destQuantum_pos (m : Nat) : 0 < destQuantum m := by
  by_cases h : m < 1024
  · rw [destQuantum_of_lt h]
    decide
  · rw [destQuantum_of_ge (by omega)]
    exact Nat.two_pow_pos _

/-- The exponent and quantum selectors agree: `q = 2 ^ (e - 1)`. -/
theorem destQuantum_eq_two_pow_destExp_sub_one (m : Nat) :
    destQuantum m = 2 ^ (destExp m - 1) := by
  by_cases h : m < 1024
  · rw [destQuantum_of_lt h, destExp_of_lt h]
  · have hge : 1024 ≤ m := by omega
    rw [destQuantum_of_ge hge, destExp_of_ge hge]
    congr 1

/-- Subnormals are exactly the selector's exponent-zero class. -/
theorem destExp_eq_zero_iff (m : Nat) : destExp m = 0 ↔ m < 1024 := by
  constructor
  · intro h
    exact Nat.lt_of_not_le (by
      intro h1024
      rw [destExp_of_ge h1024] at h
      have hlog : 10 ≤ Nat.log2 m := le_log2_of_1024_le h1024
      omega)
  · intro h
    exact destExp_of_lt h

/-- Exact no-overflow bound for the destination exponent: it is at most `30`
exactly when the magnitude is below `2 ^ 40`. -/
theorem destExp_le_30_iff (m : Nat) : destExp m ≤ 30 ↔ m < 2 ^ 40 := by
  constructor
  · intro h
    exact Nat.lt_of_not_le (by
      intro hge
      have h1024 : 1024 ≤ m := by
        have h40 : (1024 : Nat) ≤ 2 ^ 40 := by decide
        omega
      rw [destExp_of_ge h1024] at h
      have hm0 : m ≠ 0 := by omega
      have hlog : 40 ≤ Nat.log2 m := (Nat.le_log2 hm0).mpr hge
      omega)
  · intro h
    by_cases hsmall : m < 1024
    · rw [destExp_of_lt hsmall]
      omega
    · have hge : 1024 ≤ m := by omega
      rw [destExp_of_ge hge]
      have hm0 : m ≠ 0 := by omega
      have hlog : Nat.log2 m < 40 := (Nat.log2_lt hm0).mpr h
      omega

theorem destExp_le_30_of_lt_pow40 (m : Nat) (h : m < 2 ^ 40) :
    destExp m ≤ 30 :=
  (destExp_le_30_iff m).mpr h

/-- Lower binade bound: `1024 * q ≤ m`. -/
theorem destQuantum_mul_1024_le (m : Nat) (h : 1024 ≤ m) :
    1024 * destQuantum m ≤ m := by
  rw [destQuantum_of_ge h]
  have hm0 : m ≠ 0 := by omega
  have hlog : 10 ≤ Nat.log2 m := le_log2_of_1024_le h
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

/-- Upper binade bound: `m < 2048 * q`. -/
theorem lt_destQuantum_mul_2048 (m : Nat) (h : 1024 ≤ m) :
    m < 2048 * destQuantum m := by
  rw [destQuantum_of_ge h]
  have hm0 : m ≠ 0 := by omega
  have hlog : 10 ≤ Nat.log2 m := le_log2_of_1024_le h
  have hlt := ((Nat.log2_eq_iff hm0).mp rfl).2
  calc
    m < 2 ^ (Nat.log2 m + 1) := hlt
    _ = 2 ^ (11 + (Nat.log2 m - 10)) := by
      congr 1
      omega
    _ = 2 ^ 11 * 2 ^ (Nat.log2 m - 10) := by rw [Nat.pow_add]
    _ = 2048 * 2 ^ (Nat.log2 m - 10) := by
      rw [show (2048 : Nat) = 2 ^ 11 by decide]

/-- The pre-rounding significand of a normal destination binade is exactly
11 bits: it lies in `[1024, 2047]`. -/
theorem destMant_ge_1024 (m : Nat) (h : 1024 ≤ m) : 1024 ≤ destMant m := by
  unfold destMant
  rw [Nat.le_div_iff_mul_le (destQuantum_pos m)]
  exact destQuantum_mul_1024_le m h

theorem destMant_le_2047 (m : Nat) (h : m < 2 ^ 40) : destMant m ≤ 2047 := by
  by_cases hsmall : m < 1024
  · unfold destMant
    rw [destQuantum_of_lt hsmall]
    simp
    omega
  · have hge : 1024 ≤ m := by omega
    have hqpos : 0 < 2 ^ (Nat.log2 m - 10) := Nat.two_pow_pos _
    have hup := lt_destQuantum_mul_2048 m hge
    rw [destQuantum_of_ge hge] at hup
    unfold destMant
    rw [destQuantum_of_ge hge]
    have hdiv : m / 2 ^ (Nat.log2 m - 10) < 2048 :=
      (Nat.div_lt_iff_lt_mul hqpos).mpr hup
    omega

theorem destMant_mem (m : Nat) (h1024 : 1024 ≤ m) (h40 : m < 2 ^ 40) :
    1024 ≤ destMant m ∧ destMant m ≤ 2047 :=
  ⟨destMant_ge_1024 m h1024, destMant_le_2047 m h40⟩

/-- A rounded value is always a multiple of its quantum. -/
theorem roundEvenNat_dvd (q m : Nat) : q ∣ roundEvenNat q m := by
  obtain ⟨k, hk⟩ := roundEvenNat_grid q m
  exact ⟨k, by rw [hk, Nat.mul_comm]⟩

theorem roundEvenNat_div_mul (q m : Nat) :
    roundEvenNat q m / q * q = roundEvenNat q m :=
  Nat.div_mul_cancel (roundEvenNat_dvd q m)

/-- The rounded destination significand stays in `[1024, 2048]`; a quotient
of `2048` is exactly a carry into the next binade. -/
theorem roundEvenNat_destQuantum_div_mem (m : Nat) (h : 1024 ≤ m) :
    1024 ≤ roundEvenNat (destQuantum m) m / destQuantum m ∧
      roundEvenNat (destQuantum m) m / destQuantum m ≤ 2048 := by
  have hqpos := destQuantum_pos m
  have hlow := destQuantum_mul_1024_le m h
  have hup := lt_destQuantum_mul_2048 m h
  have hr := roundEvenNat_div_mul (destQuantum m) m
  have hhalf : destQuantum m / 2 < destQuantum m :=
    Nat.div_lt_self hqpos (by decide)
  constructor
  · exact Nat.le_of_not_lt (by
      intro hlt
      have hk : roundEvenNat (destQuantum m) m / destQuantum m ≤ 1023 := by
        omega
      have hkq : roundEvenNat (destQuantum m) m / destQuantum m * destQuantum m ≤
          1023 * destQuantum m :=
        Nat.mul_le_mul_right _ hk
      have hle := le_roundEvenNat_add_half (destQuantum m) m hqpos
      rw [← hr] at hle
      omega)
  · apply Nat.le_of_lt_succ
    exact Nat.lt_of_not_le (by
      intro hk
      have hkq : 2049 * destQuantum m ≤
          roundEvenNat (destQuantum m) m / destQuantum m * destQuantum m :=
        Nat.mul_le_mul_right _ hk
      have hle := roundEvenNat_le_add_half (destQuantum m) m hqpos
      rw [← hr] at hle
      omega)

/-! ## IEEE round-to-nearest-even at the selected binade -/

/-- IEEE RNE of an exact `2 ^ -24` integer at the destination binade chosen by
its magnitude; zero keeps the stage-156 signed-zero rule. -/
def rneScaled (z : Int) (sa sb : Bool) : Fp16Val :=
  if z = 0 then
    .fin { sign := zeroSign sa sb, mag := 0 }
  else
    .fin { sign := z < 0, mag := roundEvenNat (destQuantum z.natAbs) z.natAbs }

theorem SVal.signed_mk_roundEvenNat (q : Nat) (z : Int) :
    (⟨z < 0, roundEvenNat q z.natAbs⟩ : SVal).signed = roundEven q z := by
  by_cases hz : 0 ≤ z
  · have hdec : decide (z < 0) = false := by simp [show ¬ z < 0 by omega]
    have hto : z.toNat = z.natAbs := by
      apply Int.ofNat_inj.mp
      rw [Int.toNat_of_nonneg hz, Int.natAbs_of_nonneg hz]
    rw [SVal.signed_mk]
    simp only [hdec, Bool.false_eq_true, ite_false]
    rw [roundEven_of_nonneg q hz, hto]
  · have hdec : decide (z < 0) = true := by simp [show z < 0 by omega]
    have hneg : 0 ≤ -z := by omega
    have hto : (-z).toNat = z.natAbs := by
      apply Int.ofNat_inj.mp
      rw [Int.toNat_of_nonneg hneg, ← Int.natAbs_of_nonneg hneg, Int.natAbs_neg]
    rw [SVal.signed_mk]
    simp only [hdec, ite_true]
    rw [roundEven_of_neg q hz, hto]

/-- The selected-binade RNE value has signed integer `roundEven q z`. -/
theorem rneScaled_signed (z : Int) (sa sb : Bool) :
    ∃ v : SVal, rneScaled z sa sb = .fin v ∧
      v.signed = roundEven (destQuantum z.natAbs) z := by
  by_cases hz : z = 0
  · refine ⟨⟨zeroSign sa sb, 0⟩, ?_, ?_⟩
    · unfold rneScaled
      rw [ite_eq_left hz]
    · subst hz
      simp [SVal.signed, roundEven_zero]
  · refine ⟨⟨z < 0, roundEvenNat (destQuantum z.natAbs) z.natAbs⟩, ?_, ?_⟩
    · unfold rneScaled
      rw [ite_eq_right hz]
    · exact SVal.signed_mk_roundEvenNat _ z

/-- The general finite rounding equality.  For any exact scaled sum below the
stage-156 overflow threshold, `roundScaled` is IEEE round-to-nearest-even at
the destination binade selected by `destExp`/`destQuantum`. -/
theorem roundScaled_eq_fin_rne (z : Int) (sa sb : Bool)
    (hz : z ≠ 0) (hfin : z.natAbs < overflowThreshold) :
    roundScaled z sa sb =
      .fin { sign := z < 0,
             mag := roundEvenNat (destQuantum z.natAbs) z.natAbs } := by
  by_cases hsmall : z.natAbs < 1024
  · dsimp only [roundScaled]
    rw [ite_eq_right hz, ite_eq_left hsmall]
    rw [destQuantum_of_lt hsmall, roundEvenNat_one]
  · have hge : 1024 ≤ z.natAbs := by omega
    have hqpos := destQuantum_pos z.natAbs
    have hqraw : destQuantum z.natAbs = 2 ^ (Nat.log2 z.natAbs - 10) :=
      destQuantum_of_ge hge
    have heraw : destExp z.natAbs = Nat.log2 z.natAbs - 9 :=
      destExp_of_ge hge
    have hqpow : destQuantum z.natAbs = 2 ^ (destExp z.natAbs - 1) :=
      destQuantum_eq_two_pow_destExp_sub_one _
    have hepos : 1 ≤ destExp z.natAbs := by
      rw [heraw]
      have hlog : 10 ≤ Nat.log2 z.natAbs := le_log2_of_1024_le hge
      omega
    have hfin40 : z.natAbs < 2 ^ 40 := by
      have hT : overflowThreshold < 2 ^ 40 := by decide
      omega
    have he30 : destExp z.natAbs ≤ 30 := destExp_le_30_of_lt_pow40 _ hfin40
    have hmem := roundEvenNat_destQuantum_div_mem z.natAbs hge
    have hdivmul := roundEvenNat_div_mul (destQuantum z.natAbs) z.natAbs
    dsimp only [roundScaled]
    rw [ite_eq_right hz, ite_eq_right hsmall, ← hqraw, ← heraw]
    by_cases hbig : 2048 ≤
        roundEvenNat (destQuantum z.natAbs) z.natAbs / destQuantum z.natAbs
    · have hk2048 :
          roundEvenNat (destQuantum z.natAbs) z.natAbs / destQuantum z.natAbs =
            2048 := by
        omega
      have hr2048 : roundEvenNat (destQuantum z.natAbs) z.natAbs =
          2048 * destQuantum z.natAbs := by
        rw [← hdivmul, hk2048]
      rw [ite_eq_left hbig]
      by_cases hbranch : destExp z.natAbs + 1 ≤ 30
      · rw [ite_eq_left hbranch]
        have hmag : 1024 * 2 ^ destExp z.natAbs =
            roundEvenNat (destQuantum z.natAbs) z.natAbs := by
          calc
            1024 * 2 ^ destExp z.natAbs =
                2 ^ 10 * 2 ^ destExp z.natAbs := by
              rw [show (1024 : Nat) = 2 ^ 10 by decide]
            _ = 2 ^ (10 + destExp z.natAbs) := by rw [Nat.pow_add]
            _ = 2 ^ (11 + (destExp z.natAbs - 1)) := by
              congr 1
              omega
            _ = 2 ^ 11 * 2 ^ (destExp z.natAbs - 1) := by rw [Nat.pow_add]
            _ = 2048 * destQuantum z.natAbs := by
              rw [show (2048 : Nat) = 2 ^ 11 by decide, ← hqpow]
            _ = roundEvenNat (destQuantum z.natAbs) z.natAbs := hr2048.symm
        rw [hmag]
      · rw [ite_eq_right hbranch]
        exfalso
        have heq30 : destExp z.natAbs = 30 := by omega
        have hq29 : destQuantum z.natAbs = 2 ^ 29 := by
          rw [hqraw]
          congr 1
          rw [heraw] at heq30
          omega
        have hrge : 2 ^ 40 ≤ roundEvenNat (destQuantum z.natAbs) z.natAbs := by
          have hmul := (Nat.le_div_iff_mul_le hqpos).mp hbig
          rw [hq29] at hmul
          rw [show (2048 : Nat) * 2 ^ 29 = 2 ^ 40 by decide] at hmul
          rw [hq29]
          exact hmul
        have hrle : roundEvenNat (destQuantum z.natAbs) z.natAbs ≤
            z.natAbs + 2 ^ 28 := by
          have h := roundEvenNat_le_add_half (destQuantum z.natAbs) z.natAbs hqpos
          rw [hq29, show (2 : Nat) ^ 29 / 2 = 2 ^ 28 by decide] at h
          rw [hq29]
          exact h
        have hT : overflowThreshold = 2 ^ 40 - 2 ^ 28 := by decide
        omega
    · rw [ite_eq_right hbig]
      rw [ite_eq_left he30]
      have hmag : roundEvenNat (destQuantum z.natAbs) z.natAbs /
          destQuantum z.natAbs * 2 ^ (destExp z.natAbs - 1) =
            roundEvenNat (destQuantum z.natAbs) z.natAbs := by
        rw [← hqpow]
        exact hdivmul
      rw [hmag]

/-- `roundScaled` agrees with the selected-binade IEEE RNE model on the whole
finite range. -/
theorem roundScaled_eq_rne (z : Int) (sa sb : Bool)
    (hfin : z.natAbs < overflowThreshold) :
    roundScaled z sa sb = rneScaled z sa sb := by
  by_cases hz : z = 0
  · subst hz
    simp [roundScaled, rneScaled]
  · rw [roundScaled_eq_fin_rne z sa sb hz hfin]
    unfold rneScaled
    rw [ite_eq_right hz]

/-- Operand-level form of the general rounding theorem. -/
theorem addFull_fin_eq_rne (x y : SVal)
    (hfin : (x.signed + y.signed).natAbs < overflowThreshold) :
    addFull (.fin x) (.fin y) =
      rneScaled (x.signed + y.signed) x.sign y.sign := by
  rw [addFull_fin_fin]
  exact roundScaled_eq_rne _ x.sign y.sign hfin

/-! ## Representative binade instances -/

theorem destQuantum_binade2 (m : Nat) (h1 : 2048 ≤ m) (h2 : m ≤ 4095) :
    destQuantum m = 2 := by
  rw [destQuantum_of_ge (by omega)]
  have hm0 : m ≠ 0 := by omega
  have hlog : Nat.log2 m = 11 := by
    rw [Nat.log2_eq_iff hm0]
    constructor
    · rw [show (2 : Nat) ^ 11 = 2048 by decide]
      exact h1
    · rw [show (2 : Nat) ^ (11 + 1) = 4096 by decide]
      omega
  rw [hlog]

theorem destQuantum_binade30 (m : Nat) (h1 : 2 ^ 39 ≤ m) (h2 : m < 2 ^ 40) :
    destQuantum m = 2 ^ 29 := by
  rw [destQuantum_of_ge (by omega)]
  have hm0 : m ≠ 0 := by omega
  have hlog : Nat.log2 m = 39 := by
    rw [Nat.log2_eq_iff hm0]
    constructor
    · exact h1
    · rw [show (2 : Nat) ^ (39 + 1) = 2 ^ 40 by decide]
      exact h2
  rw [hlog]

/-- Binade 2 is covered by the general theorem, not by a separate proof. -/
theorem roundScaled_eq_rne_binade2 (z : Int) (sa sb : Bool)
    (h1 : 2048 ≤ z.natAbs) (h2 : z.natAbs ≤ 4095) :
    roundScaled z sa sb =
      .fin { sign := z < 0, mag := roundEvenNat 2 z.natAbs } := by
  have hT : (4095 : Nat) < overflowThreshold := by decide
  have hfin : z.natAbs < overflowThreshold := by omega
  rw [roundScaled_eq_fin_rne z sa sb (by omega) hfin,
    destQuantum_binade2 z.natAbs h1 h2]

/-- The top finite binade is covered as well. -/
theorem roundScaled_eq_rne_binade30 (z : Int) (sa sb : Bool)
    (h1 : 2 ^ 39 ≤ z.natAbs) (h2 : z.natAbs < overflowThreshold) :
    roundScaled z sa sb =
      .fin { sign := z < 0, mag := roundEvenNat (2 ^ 29) z.natAbs } := by
  rw [roundScaled_eq_fin_rne z sa sb (by omega) h2,
    destQuantum_binade30 z.natAbs h1 (by
      have hT : overflowThreshold < 2 ^ 40 := by decide
      omega)]

/-! ## The general finite addition -/

/-- Value-level addition with the general finite clause `rneScaled`.  The
special-value clauses are exactly those of stage 156's `addFull`. -/
def addGeneral : Fp16Val → Fp16Val → Fp16Val
  | .nan ng p _q, _ => .nan ng p true
  | _, .nan ng p _q => .nan ng p true
  | .inf a, .inf b => if a = b then .inf a else .nan false 0 true
  | .inf a, .fin _ => .inf a
  | .fin _, .inf b => .inf b
  | .fin a, .fin b => rneScaled (a.signed + b.signed) a.sign b.sign

theorem addGeneral_fin_fin (x y : SVal) :
    addGeneral (.fin x) (.fin y) =
      rneScaled (x.signed + y.signed) x.sign y.sign := rfl

/-- On the whole finite range the general model agrees with stage 156. -/
theorem addGeneral_eq_addFull_of_lt_threshold (x y : SVal)
    (hfin : (x.signed + y.signed).natAbs < overflowThreshold) :
    addGeneral (.fin x) (.fin y) = addFull (.fin x) (.fin y) := by
  rw [addGeneral_fin_fin, addFull_fin_fin]
  exact (roundScaled_eq_rne _ x.sign y.sign hfin).symm

/-- Subnormal/crossing agreement with stage 156 is a special case. -/
theorem addGeneral_fin_subnormal_eq_addFull (x y : SVal)
    (hx : x.mag ≤ 1023) (hy : y.mag ≤ 1023) :
    addGeneral (.fin x) (.fin y) = addFull (.fin x) (.fin y) := by
  apply addGeneral_eq_addFull_of_lt_threshold
  have hle := SVal.natAbs_add_signed_le_2046 x y hx hy
  have hT : (2046 : Nat) < overflowThreshold := by decide
  omega

/-- Binade-2 agreement with stage 156 is a higher-binade special case. -/
theorem addGeneral_fin_binade2_eq_addFull (x y : SVal)
    (h2 : (x.signed + y.signed).natAbs ≤ 4095) :
    addGeneral (.fin x) (.fin y) = addFull (.fin x) (.fin y) := by
  apply addGeneral_eq_addFull_of_lt_threshold
  have hT : (4095 : Nat) < overflowThreshold := by decide
  omega

/-- The general finite addition result: on legal finite operands below the
overflow threshold the result is stage 156's finite `addFull`, and its signed
integer is IEEE RNE at the selected destination binade. -/
theorem addGeneral_fin (x y : SVal)
    (_hx : x.mag ≤ maxFiniteScaled) (_hy : y.mag ≤ maxFiniteScaled)
    (hfin : (x.signed + y.signed).natAbs < overflowThreshold) :
    addGeneral (.fin x) (.fin y) = addFull (.fin x) (.fin y) ∧
      ∃ v : SVal,
        addGeneral (.fin x) (.fin y) = .fin v ∧
        v.signed = roundEven (destQuantum (x.signed + y.signed).natAbs)
          (x.signed + y.signed) := by
  refine ⟨addGeneral_eq_addFull_of_lt_threshold x y hfin, ?_⟩
  rw [addGeneral_fin_fin]
  exact rneScaled_signed _ _ _

/-- The destination exponent of a finite sum never exceeds the top finite
binade. -/
theorem destExp_fin_sum_le_30 (x y : SVal)
    (_hx : x.mag ≤ maxFiniteScaled) (_hy : y.mag ≤ maxFiniteScaled)
    (hfin : (x.signed + y.signed).natAbs < overflowThreshold) :
    destExp (x.signed + y.signed).natAbs ≤ 30 := by
  apply destExp_le_30_of_lt_pow40
  have hT : overflowThreshold < 2 ^ 40 := by decide
  omega

/-- A nonzero finite result takes the sign of the exact sum. -/
theorem addGeneral_fin_sign_ne_zero (x y : SVal)
    (hz : x.signed + y.signed ≠ 0) :
    ∃ v : SVal, addGeneral (.fin x) (.fin y) = .fin v ∧
      v.sign = decide (x.signed + y.signed < 0) := by
  refine ⟨⟨x.signed + y.signed < 0,
    roundEvenNat (destQuantum (x.signed + y.signed).natAbs)
      (x.signed + y.signed).natAbs⟩, ?_, rfl⟩
  rw [addGeneral_fin_fin]
  unfold rneScaled
  rw [ite_eq_right hz]

/-! ## NaN, infinity and signed zero are unchanged -/

theorem addGeneral_nan_left (ng : Bool) (p : Nat) (q : Bool) (v : Fp16Val) :
    addGeneral (.nan ng p q) v = .nan ng p true := by
  cases v <;> rfl

theorem addGeneral_fin_nan (v : SVal) (ng : Bool) (p : Nat) (q : Bool) :
    addGeneral (.fin v) (.nan ng p q) = .nan ng p true := rfl

theorem addGeneral_nan_nan (ng ng' : Bool) (p p' : Nat) (q q' : Bool) :
    addGeneral (.nan ng p q) (.nan ng' p' q') = .nan ng p true := rfl

theorem addGeneral_inf_same (a : Bool) :
    addGeneral (.inf a) (.inf a) = .inf a := by
  cases a <;> rfl

theorem addGeneral_inf_opposite (a : Bool) :
    addGeneral (.inf a) (.inf (!a)) = .nan false 0 true := by
  cases a <;> rfl

theorem addGeneral_inf_fin (a : Bool) (v : SVal) :
    addGeneral (.inf a) (.fin v) = .inf a := rfl

theorem addGeneral_fin_inf (v : SVal) (a : Bool) :
    addGeneral (.fin v) (.inf a) = .inf a := rfl

/-- Signed zero is stage 156's rule: negative only when both summands are
negative zeros. -/
theorem addGeneral_zero_zero (sa sb : Bool) :
    addGeneral (.fin ⟨sa, 0⟩) (.fin ⟨sb, 0⟩) = .fin ⟨zeroSign sa sb, 0⟩ := by
  rw [addGeneral_fin_fin]
  unfold rneScaled
  simp [SVal.signed]

/-- Any exact finite cancellation uses the same signed-zero rule, including
the `+x + -x = +0` case. -/
theorem addGeneral_fin_cancel (x y : SVal) (h : x.signed + y.signed = 0) :
    addGeneral (.fin x) (.fin y) = .fin ⟨zeroSign x.sign y.sign, 0⟩ := by
  rw [addGeneral_fin_fin]
  unfold rneScaled
  rw [ite_eq_left h]

theorem addGeneral_pos_zero_pos_zero :
    addGeneral (.fin ⟨false, 0⟩) (.fin ⟨false, 0⟩) = .fin ⟨false, 0⟩ := by
  decide

theorem addGeneral_pos_zero_neg_zero :
    addGeneral (.fin ⟨false, 0⟩) (.fin ⟨true, 0⟩) = .fin ⟨false, 0⟩ := by
  decide

theorem addGeneral_neg_zero_neg_zero :
    addGeneral (.fin ⟨true, 0⟩) (.fin ⟨true, 0⟩) = .fin ⟨true, 0⟩ := by
  decide

/-! ## A natural claim that is false -/

theorem destQuantum_2049 : destQuantum 2049 = 2 :=
  destQuantum_binade2 2049 (by decide) (by decide)

/-- Rounding `2049` units at the global `2 ^ -24` quantum keeps `2049`. -/
theorem roundEven_one_2049 : roundEven 1 (2049 : Int) = 2049 := by
  decide

/-- The correctly rounded binade-2 result is `2048`, an even significand. -/
theorem roundScaled_2049 :
    roundScaled 2049 false false = .fin ⟨false, 2048⟩ := by
  have hfin : (2049 : Int).natAbs < overflowThreshold := by decide
  have habs : (2049 : Int).natAbs = 2049 := by decide
  rw [roundScaled_eq_fin_rne 2049 false false (by decide) hfin, habs,
    destQuantum_2049]
  decide

/-- Rounding without first choosing the destination binade is not IEEE RNE:
at `2049` units the global quantum gives an 11-bit significand of `2049`,
which binade 2 cannot represent, while the destination quantum `2` gives
`2048`. -/
theorem rounding_without_alignment_counterexample :
    roundScaled 2049 false false ≠
      .fin ⟨false, (roundEven 1 (2049 : Int)).natAbs⟩ := by
  rw [roundScaled_2049, roundEven_one_2049]
  decide

end IntelGpu
