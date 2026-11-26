-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.IeeeFp16GeneralRne

@[expose] public section

/-!
# IEEE exception flags for fp16 addition

Stages 149, 156, 159 and 164 model exact-grid fp16 addition, special values,
overflow, directed rounding and general round-to-nearest-even, but they leave
the IEEE exception flags outside the proved class. This module adds a sticky
flag model for the decoded value domain of `Intel.IeeeFp16Special`.

- `Flags`: the five IEEE exception bits `invalid`, `divByZero`, `overflow`,
  `underflow` and `inexact`, with `none`, `all`, bitwise `union` (also exposed
  as `or`), associativity and idempotence.
- `addFlags`: the flag result of adding two `Fp16Val`s. NaN operands and
  opposite infinities are invalid, equal infinities and infinity plus a finite
  value are exact, and finite operands use `finAddFlags` on the exact scaled
  integer `x.signed + y.signed` in units of `2 ^ -24`.
- `foldFlags`: sticky accumulation over a list of instruction results. It is
  monotone, and the final accumulator is the union of the initial flags and
  all per-step flags (`foldFlags_eq_union`, `foldFlags_eq_foldr`).
- Negative tests: exact subnormal results are not inexact, and choosing
  tininess before rather than after rounding changes the underflow bit.

## Conventions

- The exact finite sum is `z = x.signed + y.signed`, an integer in units of
  `2 ^ -24`. Rounding is one `roundEven` at the destination quantum
  `destQuantum |z|`, matching the finite branch of `addGeneral` below the
  stage-156 overflow threshold.
- `invalid` is raised for every NaN operand, including a quiet NaN. This is
  the convention requested for this model; IEEE-754 only requires invalid for
  signaling NaNs. It is also raised for opposite-signed infinities.
- `divByZero` is never raised by addition. It is present so the flag set can
  be reused by other operations.
- `overflow` is raised exactly when the finite exact sum has magnitude at or
  above `overflowThreshold = 4095 * 2 ^ 28`, the stage-156 rounding threshold.
  The result is infinity and `inexact` is also set, as IEEE-754 requires for
  overflow.
- For a finite non-overflow sum, `inexact` is raised exactly when
  `roundEven (destQuantum |z|) z != z`. `addFlags_inexact_iff` states this.
- Tininess uses the **after-rounding** convention: the rounded result has
  magnitude below the minimum normal `1024 * 2 ^ -24` (zero included), and
  `underflow` additionally requires inexactness. Thus exact subnormal results
  set no flags.
- Consequently, a decoded fp16 addition can never raise underflow. Both
  operands lie on the `2 ^ -24` grid, and below the minimum normal the
  destination quantum is one, so a tiny sum is exact. The theorem
  `finAddFlags_underflow_false` proves this. The underflow branch is still
  exercised on a finer grid by `roundingFlags_underflow_subnormal`: one and a
  half minimum subnormals round to a nonzero subnormal and are inexact.

## Outside the model

The flags are an abstract per-operation summary. Hardware timing, pipelining,
trap delivery, exception masks, per-lane versus per-instruction sticky state,
flush-to-zero and denormals-are-zero modes are not modeled. Directed rounding
modes (`Intel.IeeeFp16Directed`) do not get a separate flag function here.
The special-value rules follow `addGeneral`/`addFull`, including left-biased
NaN payload propagation. Fused multiply-add is outside the proved class.

There are no new axioms, no `native_decide` and no `sorry`.
-/

namespace IntelGpu

/-! ## The sticky flag set -/

/-- The five IEEE exception flags as independent sticky bits. -/
structure Flags where
  invalid : Bool
  divByZero : Bool
  overflow : Bool
  underflow : Bool
  inexact : Bool
  deriving Repr, DecidableEq

namespace Flags

@[ext] theorem ext {a b : Flags}
    (hi : a.invalid = b.invalid) (hz : a.divByZero = b.divByZero)
    (ho : a.overflow = b.overflow) (hu : a.underflow = b.underflow)
    (hx : a.inexact = b.inexact) : a = b := by
  cases a
  cases b
  simp_all

/-- No exception is raised. -/
def none : Flags :=
  { invalid := false, divByZero := false, overflow := false,
    underflow := false, inexact := false }

/-- Every exception bit is set. -/
def all : Flags :=
  { invalid := true, divByZero := true, overflow := true,
    underflow := true, inexact := true }

/-- Only the invalid bit is set. -/
def invalidOnly : Flags :=
  { invalid := true, divByZero := false, overflow := false,
    underflow := false, inexact := false }

/-- Only the inexact bit is set. -/
def inexactOnly : Flags :=
  { invalid := false, divByZero := false, overflow := false,
    underflow := false, inexact := true }

/-- Overflow and inexact are both set, as on an overflowing rounded add. -/
def overflowInexact : Flags :=
  { invalid := false, divByZero := false, overflow := true,
    underflow := false, inexact := true }

/-- Sticky union of two flag summaries. -/
def union (a b : Flags) : Flags :=
  { invalid := a.invalid || b.invalid
    divByZero := a.divByZero || b.divByZero
    overflow := a.overflow || b.overflow
    underflow := a.underflow || b.underflow
    inexact := a.inexact || b.inexact }

/-- Alias for `Flags.union`, emphasizing accumulation by bitwise or. -/
def or (a b : Flags) : Flags := union a b

@[simp] theorem union_none_left (a : Flags) : none.union a = a := by
  ext <;> simp [union, none]

@[simp] theorem union_none_right (a : Flags) : a.union none = a := by
  ext <;> simp [union, none]

@[simp] theorem union_all_left (a : Flags) : all.union a = all := by
  ext <;> simp [union, all]

@[simp] theorem union_all_right (a : Flags) : a.union all = all := by
  ext <;> simp [union, all]

theorem union_comm (a b : Flags) : a.union b = b.union a := by
  ext <;> simp [union, Bool.or_comm]

theorem union_assoc (a b c : Flags) :
    (a.union b).union c = a.union (b.union c) := by
  ext <;> simp [union, Bool.or_assoc]

theorem union_idempotent (a : Flags) : a.union a = a := by
  ext <;> simp [union]

theorem or_eq_union (a b : Flags) : a.or b = a.union b := rfl

/-- Sticky containment: `a` is contained in `b` when their union is `b`. -/
def le (a b : Flags) : Prop := a.union b = b

theorem le_refl (a : Flags) : le a a := union_idempotent a

theorem le_union_left (a b : Flags) : le a (a.union b) := by
  unfold le
  rw [← union_assoc, union_idempotent]

theorem le_union_right (a b : Flags) : le b (a.union b) := by
  unfold le
  rw [← union_assoc, union_comm b a, union_assoc, union_idempotent]

theorem le_trans {a b c : Flags} (hab : le a b) (hbc : le b c) : le a c := by
  unfold le at *
  rw [← hbc, ← union_assoc, hab, hbc]

/-! ## Sticky accumulation over a fold -/

/-- Accumulate a list of flag summaries into an initial sticky set. -/
def foldFlags : Flags → List Flags → Flags
  | acc, [] => acc
  | acc, f :: fs => foldFlags (acc.union f) fs

theorem foldFlags_append (init : Flags) (xs ys : List Flags) :
    foldFlags init (xs ++ ys) = foldFlags (foldFlags init xs) ys := by
  induction xs generalizing init with
  | nil => rfl
  | cons f fs ih => simp [foldFlags, ih]

theorem foldFlags_monotone (init : Flags) (steps : List Flags) :
    le init (foldFlags init steps) := by
  induction steps generalizing init with
  | nil => exact le_refl init
  | cons f fs ih =>
      exact le_trans (le_union_left init f) (ih (init.union f))

theorem foldFlags_prefix_monotone (init : Flags) (xs ys : List Flags) :
    le (foldFlags init xs) (foldFlags init (xs ++ ys)) := by
  rw [foldFlags_append]
  exact foldFlags_monotone (foldFlags init xs) ys

theorem foldFlags_eq_union (init : Flags) (steps : List Flags) :
    foldFlags init steps = init.union (foldFlags none steps) := by
  induction steps generalizing init with
  | nil => simp [foldFlags]
  | cons f fs ih =>
      rw [foldFlags, ih, foldFlags]
      simp only [union_none_left]
      rw [ih f, union_assoc]

/-- The final accumulator is the union of all per-step flags. -/
theorem foldFlags_eq_foldr (steps : List Flags) :
    foldFlags none steps = steps.foldr union none := by
  induction steps with
  | nil => rfl
  | cons f fs ih =>
      rw [foldFlags, foldFlags_eq_union, ih]
      simp

theorem foldFlags_two_step_example :
    foldFlags none [inexactOnly, overflowInexact] = overflowInexact := by
  decide

end Flags

/-! ## Rounding, tininess and the finite-sum flag rule -/

/-- The two IEEE tininess conventions. This model uses after rounding. -/
inductive Tininess where
  | beforeRounding
  | afterRounding
  deriving Repr, DecidableEq

/-- Round an exact scaled integer to a quantum. -/
def roundedAt (q : Nat) (z : Int) : Int := roundEven q z

/-- Whether rounding at quantum `q` changes the exact scaled sum. -/
def inexactAt (q : Nat) (z : Int) : Bool :=
  decide (roundedAt q z ≠ z)

/-- Tininess before rounding: the exact sum is below the minimum normal. -/
def tinyBefore (z : Int) : Bool := decide (z.natAbs < 1024)

/-- Tininess after rounding: the rounded result is below the minimum normal.
Zero is included. -/
def tinyAfter (q : Nat) (z : Int) : Bool :=
  decide ((roundedAt q z).natAbs < 1024)

/-- Select the tininess predicate for a convention. -/
def tinyAt : Tininess → Nat → Int → Bool
  | .beforeRounding, _, z => tinyBefore z
  | .afterRounding, q, z => tinyAfter q z

/-- Flags for rounding an exact scaled sum at quantum `q`, without the
overflow branch. Underflow is tiny and inexact; inexact means that the
rounded integer differs from the exact sum. -/
def roundingFlags (t : Tininess) (q : Nat) (z : Int) : Flags :=
  { invalid := false
    divByZero := false
    overflow := false
    underflow := inexactAt q z && tinyAt t q z
    inexact := inexactAt q z }

/-- Round an exact `2 ^ -24` integer at the destination-binade quantum selected
by its magnitude. -/
def roundedScaled (z : Int) : Int := roundedAt (destQuantum z.natAbs) z

/-- Flags for the finite branch of fp16 addition. Overflow is the stage-156
threshold and also sets inexact. Otherwise the after-rounding rule is used. -/
def finAddFlags (z : Int) : Flags :=
  if overflowThreshold ≤ z.natAbs then
    Flags.overflowInexact
  else
    roundingFlags .afterRounding (destQuantum z.natAbs) z

/-- Exception flags for addition on decoded fp16 values. -/
def addFlags : Fp16Val → Fp16Val → Flags
  | .nan _ _ _, _ => Flags.invalidOnly
  | _, .nan _ _ _ => Flags.invalidOnly
  | .inf a, .inf b => if a = b then Flags.none else Flags.invalidOnly
  | .inf _, .fin _ => Flags.none
  | .fin _, .inf _ => Flags.none
  | .fin a, .fin b => finAddFlags (a.signed + b.signed)

/-! ## Special-value flags -/

theorem addFlags_invalid_nan (ng : Bool) (p : Nat) (q : Bool) (v : Fp16Val) :
    (addFlags (.nan ng p q) v).invalid = true := by
  cases v <;> rfl

theorem addFlags_nan_right (v : Fp16Val) (ng : Bool) (p : Nat) (q : Bool) :
    (addFlags v (.nan ng p q)).invalid = true := by
  cases v <;> rfl

theorem addFlags_invalid_inf_opposite (a : Bool) :
    (addFlags (.inf a) (.inf (!a))).invalid = true := by
  cases a <;> rfl

theorem addFlags_inf_same_none (a : Bool) :
    addFlags (.inf a) (.inf a) = Flags.none := by
  cases a <;> rfl

theorem addFlags_inf_fin_none (a : Bool) (v : SVal) :
    addFlags (.inf a) (.fin v) = Flags.none := rfl

theorem addFlags_fin_inf_none (v : SVal) (a : Bool) :
    addFlags (.fin v) (.inf a) = Flags.none := rfl

/-! ## Exactness, inexactness and overflow -/

/-- Below the overflow threshold, the finite branch of `addFlags` is exactly
the after-rounding rule at the destination quantum. -/
theorem addFlags_fin_eq_roundingFlags (x y : SVal)
    (hfin : (x.signed + y.signed).natAbs < overflowThreshold) :
    addFlags (.fin x) (.fin y) =
      roundingFlags .afterRounding
        (destQuantum (x.signed + y.signed).natAbs) (x.signed + y.signed) := by
  have hnot : ¬ overflowThreshold ≤ (x.signed + y.signed).natAbs := by omega
  simp [addFlags, finAddFlags, hnot]

theorem addFlags_inexact_iff (x y : SVal)
    (hfin : (x.signed + y.signed).natAbs < overflowThreshold) :
    (addFlags (.fin x) (.fin y)).inexact = true ↔
      roundedScaled (x.signed + y.signed) ≠ x.signed + y.signed := by
  have hnot : ¬ overflowThreshold ≤ (x.signed + y.signed).natAbs := by omega
  simp only [addFlags, finAddFlags, hnot, ite_false, roundingFlags, inexactAt,
    roundedAt, roundedScaled]
  constructor
  · exact of_decide_eq_true
  · exact decide_eq_true

/-- An exactly representable finite sum below the overflow threshold sets no
flags. -/
theorem addFlags_exact_none (x y : SVal)
    (hfin : (x.signed + y.signed).natAbs < overflowThreshold)
    (hex : roundedScaled (x.signed + y.signed) = x.signed + y.signed) :
    addFlags (.fin x) (.fin y) = Flags.none := by
  have hnot : ¬ overflowThreshold ≤ (x.signed + y.signed).natAbs := by omega
  have hex' : roundEven (destQuantum (x.signed + y.signed).natAbs)
      (x.signed + y.signed) = x.signed + y.signed := by
    simpa [roundedScaled, roundedAt] using hex
  have hinex : inexactAt (destQuantum (x.signed + y.signed).natAbs)
      (x.signed + y.signed) = false := by
    simp [inexactAt, roundedAt, hex']
  have hflags : addFlags (.fin x) (.fin y) =
      roundingFlags .afterRounding
        (destQuantum (x.signed + y.signed).natAbs) (x.signed + y.signed) := by
    simp [addFlags, finAddFlags, hnot]
  rw [hflags]
  apply Flags.ext <;> simp [roundingFlags, hinex, Flags.none]

/-- At or above the stage-156 threshold, overflow and inexact are both set and
`addFull` returns the correctly signed infinity. -/
theorem addFlags_overflow (x y : SVal)
    (hx : x.mag ≤ maxFiniteScaled) (hy : y.mag ≤ maxFiniteScaled)
    (h : overflowThreshold ≤ (x.signed + y.signed).natAbs) :
    (addFlags (.fin x) (.fin y)).overflow = true ∧
      (addFlags (.fin x) (.fin y)).inexact = true ∧
      addFull (.fin x) (.fin y) = .inf ((x.signed + y.signed) < 0) := by
  refine ⟨?_, ?_, addFull_fin_overflow_of_ge_threshold x y hx hy h⟩
  · simp [addFlags, finAddFlags, h, Flags.overflowInexact]
  · simp [addFlags, finAddFlags, h, Flags.overflowInexact]

theorem addFlags_overflow_iff (x y : SVal) :
    (addFlags (.fin x) (.fin y)).overflow = true ↔
      overflowThreshold ≤ (x.signed + y.signed).natAbs := by
  by_cases h : overflowThreshold ≤ (x.signed + y.signed).natAbs
  · simp [addFlags, finAddFlags, h, Flags.overflowInexact]
  · simp [addFlags, finAddFlags, h, roundingFlags]

/-! ## Underflow and its grid limitation -/

theorem roundedScaled_eq_self_of_lt_1024 (z : Int) (h : z.natAbs < 1024) :
    roundedScaled z = z := by
  unfold roundedScaled roundedAt
  rw [destQuantum_of_lt h]
  by_cases hz : 0 ≤ z
  · rw [roundEven_of_nonneg 1 hz]
    have hto : z.toNat = z.natAbs := by
      apply Int.ofNat_inj.mp
      rw [Int.toNat_of_nonneg hz]
      exact (Int.natAbs_of_nonneg hz).symm
    rw [hto, roundEvenNat_one]
    exact Int.natAbs_of_nonneg hz
  · rw [roundEven_of_neg 1 hz]
    have hto : (-z).toNat = z.natAbs := by
      have hzneg : z ≤ 0 := by omega
      apply Int.ofNat_inj.mp
      rw [Int.toNat_of_nonneg (by omega)]
      have hz_eq := Int.eq_neg_natAbs_of_nonpos hzneg
      omega
    rw [hto, roundEvenNat_one]
    exact (Int.eq_neg_natAbs_of_nonpos (by omega)).symm

theorem roundedScaled_natAbs_ge_1024 (z : Int) (h : 1024 ≤ z.natAbs) :
    1024 ≤ (roundedScaled z).natAbs := by
  unfold roundedScaled roundedAt
  have hqpos := destQuantum_pos z.natAbs
  have hmem := (roundEvenNat_destQuantum_div_mem z.natAbs h).1
  have hdivmul := roundEvenNat_div_mul (destQuantum z.natAbs) z.natAbs
  have hmul : 1024 ≤
      roundEvenNat (destQuantum z.natAbs) z.natAbs := by
    calc
      1024 ≤ 1024 * destQuantum z.natAbs :=
        Nat.le_mul_of_pos_right 1024 hqpos
      _ ≤ (roundEvenNat (destQuantum z.natAbs) z.natAbs /
            destQuantum z.natAbs) * destQuantum z.natAbs :=
        Nat.mul_le_mul_right (destQuantum z.natAbs) hmem
      _ = roundEvenNat (destQuantum z.natAbs) z.natAbs := hdivmul
  by_cases hz : 0 ≤ z
  · rw [roundEven_of_nonneg _ hz]
    have hto : z.toNat = z.natAbs := by
      apply Int.ofNat_inj.mp
      rw [Int.toNat_of_nonneg hz]
      exact (Int.natAbs_of_nonneg hz).symm
    rw [hto]
    simpa using hmul
  · rw [roundEven_of_neg _ hz]
    have hto : (-z).toNat = z.natAbs := by
      have hzneg : z ≤ 0 := by omega
      apply Int.ofNat_inj.mp
      rw [Int.toNat_of_nonneg (by omega)]
      have hz_eq := Int.eq_neg_natAbs_of_nonpos hzneg
      omega
    rw [hto]
    simp only [Int.natAbs_neg]
    simpa using hmul

/-- The finite branch of decoded fp16 addition never raises underflow: below
the minimum normal the quantum is one and the sum is exact; above it the
rounded magnitude is at least the minimum normal. -/
theorem finAddFlags_underflow_false (z : Int) :
    (finAddFlags z).underflow = false := by
  unfold finAddFlags
  by_cases hov : overflowThreshold ≤ z.natAbs
  · simp [hov, Flags.overflowInexact]
  · rw [ite_eq_right hov]
    unfold roundingFlags
    by_cases hsmall : z.natAbs < 1024
    · have hex : roundedAt (destQuantum z.natAbs) z = z := by
        simpa [roundedScaled] using roundedScaled_eq_self_of_lt_1024 z hsmall
      simp [inexactAt, hex]
    · have hge : 1024 ≤ (roundedAt (destQuantum z.natAbs) z).natAbs := by
        simpa [roundedScaled] using
          roundedScaled_natAbs_ge_1024 z (by omega)
      have htiny : tinyAt .afterRounding (destQuantum z.natAbs) z = false := by
        simp [tinyAt, tinyAfter, hge]
      simp [htiny]

/-- No decoded finite fp16 addition raises underflow. -/
theorem addFlags_underflow_false (x y : SVal) :
    (addFlags (.fin x) (.fin y)).underflow = false := by
  simp [addFlags, finAddFlags_underflow_false]

/-- A concrete subnormal underflow witness for the rule used by `addFlags`, on
a grid twice as fine as `2 ^ -24`: `3` is one and a half minimum subnormals,
and quantum `2` is one `2 ^ -24` unit. Ties-to-even rounds `3` to `4`, a
nonzero subnormal, and the result is inexact. -/
theorem roundingFlags_underflow_subnormal :
    (roundingFlags .afterRounding 2 3).underflow = true ∧
      (roundingFlags .afterRounding 2 3).inexact = true ∧
      roundEven 2 (3 : Int) = 4 := by
  decide

/-! ## Negative tests -/

/-- A naive rule treating every subnormal result as inexact. -/
def naiveSubnormalInexact : Fp16Val → Bool
  | .fin v => decide (v.mag < 1024)
  | _ => false

/-- `1 + 1` units is the subnormal `2` and is exact, so the naive
subnormal-result rule is wrong. -/
theorem exact_subnormal_not_inexact_counterexample :
    (addFlags (.fin ⟨false, 1⟩) (.fin ⟨false, 1⟩)).inexact = false ∧
      naiveSubnormalInexact
        (addGeneral (.fin ⟨false, 1⟩) (.fin ⟨false, 1⟩)) = true := by
  decide

/-- Before-rounding tininess would raise underflow for the inexact sum `1023`
at quantum `2`, which rounds up to the minimum normal `1024`. The
after-rounding convention used here does not. -/
theorem tininess_before_vs_after_counterexample :
    (roundingFlags .beforeRounding 2 1023).underflow = true ∧
      (roundingFlags .afterRounding 2 1023).underflow = false ∧
      roundEven 2 (1023 : Int) = 1024 := by
  decide

end IntelGpu
