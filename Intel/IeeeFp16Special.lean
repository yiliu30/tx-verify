-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.IeeeFp16Add
public import Intel.Fp16Scaled

@[expose] public section

/-!
# fp16 special values: subnormals, signed zero, overflow and NaN

Stage 149 proves a restricted round-to-nearest-even addition on the normalized
fragment with exponent field at least the bias. This module widens the value
domain to every finite fp16 word by fixing the global scale `2 ^ -24` from
`Intel.Fp16Scaled`, and tags infinities and NaNs instead of dropping them.

- `SVal`: sign plus an integer magnitude in units of `2 ^ -24`; `SVal.signed`
  is the signed integer value, so `+0` and `-0` are distinct.
- `Fp16Val`: finite `SVal`, signed infinity, or NaN with sign, a nine-bit
  payload and a quiet bit.
- `decodeFull`: total decoder. Subnormals decode to their fraction; normals
  decode to `(1024 + mantissa) * 2 ^ (expField - 1)`; zero keeps its sign;
  exponent field 31 becomes `inf` or `nan`.
- `roundScaled`: round an exact `2 ^ -24` integer to the fp16 grid, choosing
  the destination binade from `Nat.log2` and rounding ties to even.
- `addFull`: the value-level addition. NaN is left-biased and quieted,
  infinities follow the usual same/opposite-sign rules (opposite infinities
  give the canonical quiet NaN with payload zero and positive sign), and
  finite operands add their exact scaled integers and round once.

## Proved class

Every one of the `2 ^ 16` words is decoded (finite, infinity or NaN). The
addition model is proved for:

- agreement with `Intel.Fp16Bits.decode` on its normalized subset, including
  the value identity `decodeFull.signed = 2 ^ 14 * decode.signed`;
- signed zero: a zero sum is negative only when both summands are negative
  zeros, so `(+0) + (+0) = (+0) + (-0) = +0` and `(-0) + (-0) = -0`;
- subnormals: two subnormal operands whose exact sum is at most `1023` units
  add exactly on the `2 ^ -24` grid; a sum in `[1024, 2046]` crosses into the
  first normal binade, which has the same quantum, so it is exact as well and
  the result is the normal with fraction `sum - 1024`. A coarser binade does
  round: `roundEvenNat_eq_succ_mul_of_half_le` and
  `roundEvenNat_eq_mul_of_lt_half` are the two sides of the ties-to-even
  rule, with worked up/down examples where a subnormal is added to a
  binade-2 normal;
- overflow: the exact threshold is `4095 * 2 ^ 28 = 65520 * 2 ^ 24`. A sum
  below it has a finite result; at or above it the model returns infinity.
  This is exactly `fp16_add_overflow_not_representable`'s bound, half an
  ulp below `2 ^ 16` (the midpoint between `65504` and `65536`);
- NaN and infinity propagation, with the payload convention stated below.

## Outside the proved class

The general `roundScaled` implementation is not proved correct for every
binade and every operand pair; only the subnormal/crossing cases, the
ties-to-even lemmas, and the overflow threshold are proved here. The model
also omits IEEE exception flags (inexact, underflow, overflow, invalid),
tininess detection, directed rounding modes and fused multiply-add. NaN
payload selection is a convention: the left operand wins, its low nine
payload bits are preserved, the quiet bit is forced, and its sign is kept;
IEEE-754 does not mandate a payload choice. A signaling NaN is therefore
quieted rather than preserved verbatim, and flush-to-zero is proved to differ
from the IEEE behavior.
-/

namespace IntelGpu

/-! ## Finite values at the `2 ^ -24` scale -/

/-- A finite fp16 value: sign and integer magnitude in units of `2 ^ -24`. -/
structure SVal where
  sign : Bool
  mag : Nat
  deriving Repr, DecidableEq

/-- The signed integer value in units of `2 ^ -24`. -/
def SVal.signed (v : SVal) : Int :=
  if v.sign then -(v.mag : Int) else (v.mag : Int)

/-- The sign does not change the magnitude. -/
theorem SVal.natAbs_signed (v : SVal) : v.signed.natAbs = v.mag := by
  unfold SVal.signed
  split <;> simp

/-- The sign of a zero sum under round-to-nearest: negative only when both
summands are negative zeros. -/
def zeroSign (a b : Bool) : Bool := a && b

/-- The sign rule, stated as an iff. -/
theorem zeroSign_true_iff (a b : Bool) :
    zeroSign a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [zeroSign]

/-- Signed addition on finite values, including the signed-zero rule. -/
def SVal.add (x y : SVal) : SVal :=
  let z := x.signed + y.signed
  if z = 0 then ⟨zeroSign x.sign y.sign, 0⟩ else ⟨z < 0, z.natAbs⟩

theorem SVal.signed_mk (s : Bool) (m : Nat) :
    (⟨s, m⟩ : SVal).signed = if s then -(m : Int) else (m : Int) := rfl

theorem SVal.add_eq_mk_of_ne_zero (x y : SVal)
    (h : x.signed + y.signed ≠ 0) :
    x.add y = ⟨x.signed + y.signed < 0, (x.signed + y.signed).natAbs⟩ := by
  unfold SVal.add
  rw [ite_eq_right h]

theorem SVal.add_eq_mk_of_eq_zero (x y : SVal)
    (h : x.signed + y.signed = 0) :
    x.add y = ⟨zeroSign x.sign y.sign, 0⟩ := by
  unfold SVal.add
  rw [ite_eq_left h]

/-- `SVal.add` computes the exact signed sum; the zero branch only fixes the
sign of a zero result. -/
theorem SVal.add_signed (x y : SVal) :
    (x.add y).signed = x.signed + y.signed := by
  by_cases h0 : x.signed + y.signed = 0
  · rw [SVal.add_eq_mk_of_eq_zero x y h0]
    rw [h0]
    simp [SVal.signed, zeroSign]
  · rw [SVal.add_eq_mk_of_ne_zero x y h0, SVal.signed_mk]
    by_cases hneg : x.signed + y.signed < 0
    · simp [hneg]
      exact (Int.eq_neg_natAbs_of_nonpos (by omega)).symm
    · simp [hneg]
      exact Int.natAbs_of_nonneg (by omega)

/-- The triangle inequality for two finite values. -/
theorem SVal.natAbs_add_signed_le (x y : SVal) :
    (x.signed + y.signed).natAbs ≤ x.mag + y.mag := by
  have h := Int.natAbs_add_le x.signed y.signed
  rwa [SVal.natAbs_signed, SVal.natAbs_signed] at h

/-- Two subnormal operands cannot exceed the first normal binade. -/
theorem SVal.natAbs_add_signed_le_2046 (x y : SVal) (hx : x.mag ≤ 1023)
    (hy : y.mag ≤ 1023) : (x.signed + y.signed).natAbs ≤ 2046 := by
  have hle := SVal.natAbs_add_signed_le x y
  omega

/-! ## The tagged value domain -/

/-- A value with the non-finite classes kept as tags.  The NaN payload is the
low nine fraction bits; the quiet bit is stored separately. -/
inductive Fp16Val where
  | fin (v : SVal)
  | inf (neg : Bool)
  | nan (neg : Bool) (payload : Nat) (quiet : Bool)
  deriving Repr, DecidableEq

def Fp16Val.isNan : Fp16Val → Bool
  | .nan _ _ _ => true
  | _ => false

def Fp16Val.signed? : Fp16Val → Option Int
  | .fin v => some v.signed
  | _ => none

/-! ## Total decoding -/

/-- Decode every fp16 word.  Finite words use the `2 ^ -24` scale; exponent
field 31 is split into infinity and NaN, keeping the NaN payload and quiet
bit and the sign. -/
def decodeFull (w : Fp16) : Fp16Val :=
  if expField w = 31 then
    if mantField w = 0 then .inf (signBit w)
    else .nan (signBit w) (mantField w &&& 0x1FF) (decide (512 ≤ mantField w))
  else
    .fin { sign := signBit w, mag := scaled w }

/-- Every word lands in exactly one of the three classes. -/
theorem decodeFull_total_fin_or_special (w : Fp16) :
    (∃ v : SVal, decodeFull w = .fin v) ∨
      (∃ ng : Bool, decodeFull w = .inf ng) ∨
      (∃ ng p q, decodeFull w = .nan ng p q) := by
  unfold decodeFull
  split
  · split
    · exact Or.inr (Or.inl ⟨_, rfl⟩)
    · exact Or.inr (Or.inr ⟨_, _, _, rfl⟩)
  · exact Or.inl ⟨_, rfl⟩

/-- The total decoder agrees with `Intel.Fp16Bits.decode` on that decoder's
normalized fragment, up to the global `2 ^ 14` scale change. -/
theorem decodeFull_of_decode (w : Fp16) (f : Fixed) (h : decode w = some f) :
    decodeFull w = .fin { sign := f.sign, mag := f.mag * 2 ^ 14 } := by
  have hne31 : expField w ≠ 31 := decode_exp_ne w f h
  have hne0 : expField w ≠ 0 := by
    intro h0
    simp [decode, h0] at h
  have hge : ¬ expField w < 15 := by
    intro hlt
    simp [decode, hne31, hne0, hlt] at h
  obtain ⟨hmant, hexp, hsign⟩ := decode_some w f h
  have hscaled : scaled w = (1024 + mantField w) * 2 ^ (expField w - 1) := by
    unfold scaled
    rw [ite_eq_right hne0]
  have hfmag : f.mag = (1024 + mantField w) * 2 ^ (expField w - 15) := by
    unfold Fixed.mag
    rw [hmant, hexp]
  have hpow : 2 ^ (expField w - 15) * 2 ^ 14 = 2 ^ (expField w - 1) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  unfold decodeFull
  rw [ite_eq_right hne31]
  rw [hscaled, hsign, hfmag, Nat.mul_assoc, hpow]

/-- The same agreement at the level of signed integer values. -/
theorem decodeFull_signed_of_decode (w : Fp16) (f : Fixed)
    (h : decode w = some f) :
    Fp16Val.signed? (decodeFull w) = some (f.signed * 2 ^ 14) := by
  rw [decodeFull_of_decode w f h]
  simp only [Fp16Val.signed?, SVal.signed, Fixed.signed]
  by_cases hs : f.sign <;> simp [hs, Int.natCast_mul] <;> omega

/-- The converse agreement on the normalized subset: a finite full decode
with an exponent field at least the bias is exactly what `decode` returns. -/
theorem decode_of_decodeFull_normal (w : Fp16) (v : SVal)
    (h : decodeFull w = .fin v) (hge : 15 ≤ expField w) :
    decode w = some
      { sign := v.sign, mant := 1024 + mantField w, exp := expField w - 15 } := by
  have hne31 : expField w ≠ 31 := by
    intro h31
    unfold decodeFull at h
    rw [ite_eq_left h31] at h
    split at h <;> cases h
  have hne0 : expField w ≠ 0 := by omega
  unfold decodeFull at h
  rw [ite_eq_right hne31] at h
  simp only [Fp16Val.fin.injEq] at h
  subst h
  unfold decode
  rw [ite_eq_right hne31, ite_eq_right hne0,
    ite_eq_right (by omega : ¬ expField w < 15)]

/-! ## Decoding the special words -/

theorem decodeFull_pos_zero : decodeFull (0x0000 : Fp16) = .fin ⟨false, 0⟩ := by
  decide

theorem decodeFull_neg_zero : decodeFull (0x8000 : Fp16) = .fin ⟨true, 0⟩ := by
  decide

theorem decodeFull_smallest_subnormal :
    decodeFull (0x0001 : Fp16) = .fin ⟨false, 1⟩ := by
  decide

theorem decodeFull_largest_subnormal :
    decodeFull (0x03FF : Fp16) = .fin ⟨false, 1023⟩ := by
  decide

theorem decodeFull_smallest_normal :
    decodeFull (0x0400 : Fp16) = .fin ⟨false, 1024⟩ := by
  decide

theorem decodeFull_maxFinite :
    decodeFull (0x7BFF : Fp16) = .fin ⟨false, 2047 * 2 ^ 29⟩ := by
  decide

theorem decodeFull_pos_inf : decodeFull (0x7C00 : Fp16) = .inf false := by
  decide

theorem decodeFull_neg_inf : decodeFull (0xFC00 : Fp16) = .inf true := by
  decide

theorem decodeFull_qnan : decodeFull (0x7E00 : Fp16) = .nan false 0 true := by
  decide

theorem decodeFull_snan : decodeFull (0x7C01 : Fp16) = .nan false 1 false := by
  decide

/-! ## Rounding an exact `2 ^ -24` integer -/

theorem roundEvenNat_one (n : Nat) : roundEvenNat 1 n = n := by
  unfold roundEvenNat
  simp

/-- A remainder strictly below half a quantum rounds down. -/
theorem roundEvenNat_eq_mul_of_lt_half (q k r : Nat) (hq : 0 < q)
    (hr : r < q / 2) : roundEvenNat q (k * q + r) = k * q := by
  have hrq : r < q := by
    have hlt2 : q / 2 < q := Nat.div_lt_self hq (by decide)
    omega
  have hmod : (k * q + r) % q = r := by
    rw [Nat.mul_comm k q, Nat.mul_add_mod, Nat.mod_eq_of_lt hrq]
  have hne : ¬ (q % 2 = 0 ∧ (k * q + r) % q = q / 2) := by
    intro hc
    rw [hmod] at hc
    omega
  rw [roundEvenNat_notie q _ hne]
  have hdiv : (k * q + r + q / 2) / q = k := by
    rw [Nat.div_eq_of_lt_le]
    · omega
    · have hexp : (k + 1) * q = k * q + q := by rw [Nat.succ_mul]
      omega
  rw [hdiv]

/-- A remainder at or above half a quantum rounds up; at an exact tie the
odd quotient selects the even one. -/
theorem roundEvenNat_eq_succ_mul_of_half_le (q k r : Nat) (hq : 0 < q)
    (hqe : q % 2 = 0) (hk : k % 2 = 1) (hr1 : q / 2 ≤ r) (hr2 : r < q) :
    roundEvenNat q (k * q + r) = (k + 1) * q := by
  by_cases htie : r = q / 2
  · subst htie
    rw [roundEvenNat_halfway_even q k hq hqe]
    have hk1 : k % 2 ≠ 0 := by omega
    simp [hk1]
  · have hmod : (k * q + r) % q = r := by
      rw [Nat.mul_comm k q, Nat.mul_add_mod, Nat.mod_eq_of_lt hr2]
    have hne : ¬ (q % 2 = 0 ∧ (k * q + r) % q = q / 2) := by
      intro hc
      rw [hmod] at hc
      omega
    rw [roundEvenNat_notie q _ hne]
    have hdiv : (k * q + r + q / 2) / q = k + 1 := by
      rw [Nat.div_eq_of_lt_le]
      · have h2q : 2 * (q / 2) = q := by
          have h := Nat.div_add_mod q 2
          omega
        have hexp : (k + 1) * q = k * q + q := by rw [Nat.succ_mul]
        omega
      · have hlt2 : q / 2 < q := Nat.div_lt_self hq (by decide)
        have hexp1 : (k + 1) * q = k * q + q := by rw [Nat.succ_mul]
        have hexp2 : (k + 1 + 1) * q = k * q + q + q := by
          rw [Nat.succ_mul, hexp1]
        omega
    rw [hdiv]

theorem roundEvenNat_le_add_half (q n : Nat) (hq : 0 < q) :
    roundEvenNat q n ≤ n + q / 2 := by
  by_cases h : q % 2 = 0 ∧ n % q = q / 2
  · rw [roundEvenNat_tie q n h]
    have hdiv := Nat.div_add_mod n q
    rw [h.2, Nat.mul_comm q (n / q)] at hdiv
    split <;> omega
  · rw [roundEvenNat_notie q n h]
    exact Nat.div_mul_le_self (n + q / 2) q

theorem le_roundEvenNat_add_half (q n : Nat) (hq : 0 < q) :
    n ≤ roundEvenNat q n + q / 2 := by
  by_cases h : q % 2 = 0 ∧ n % q = q / 2
  · rw [roundEvenNat_tie q n h]
    have hdiv := Nat.div_add_mod n q
    rw [h.2, Nat.mul_comm q (n / q)] at hdiv
    split <;> omega
  · rw [roundEvenNat_notie q n h]
    have hdiv := Nat.div_add_mod (n + q / 2) q
    have hr := Nat.mod_lt (n + q / 2) hq
    rw [Nat.mul_comm q ((n + q / 2) / q)] at hdiv
    omega

/-- Round an exact `2 ^ -24` integer to the fp16 grid.  The binade is
`Nat.log2 m - 9`, its quantum `2 ^ (Nat.log2 m - 10)`, and the mantissa is the
rounded quotient; a quotient of `2048` is the next binade, and binades above
`30` overflow to infinity. -/
def roundScaled (z : Int) (sa sb : Bool) : Fp16Val :=
  if z = 0 then
    .fin { sign := zeroSign sa sb, mag := 0 }
  else if z.natAbs < 1024 then
    .fin { sign := z < 0, mag := z.natAbs }
  else
    let m := z.natAbs
    let e := Nat.log2 m - 9
    let q := 2 ^ (Nat.log2 m - 10)
    let mant := roundEvenNat q m / q
    if 2048 ≤ mant then
      if e + 1 ≤ 30 then .fin { sign := z < 0, mag := 1024 * 2 ^ e }
      else .inf (z < 0)
    else if e ≤ 30 then
      .fin { sign := z < 0, mag := mant * 2 ^ (e - 1) }
    else .inf (z < 0)

/-! ## The addition model -/

/-- Value-level fp16 addition: leftmost NaN wins and is quieted; infinities
follow the same-sign/opposite-sign rule; finite operands add exactly and
round once. -/
def addFull : Fp16Val → Fp16Val → Fp16Val
  | .nan ng p _q, _ => .nan ng p true
  | _, .nan ng p _q => .nan ng p true
  | .inf a, .inf b => if a = b then .inf a else .nan false 0 true
  | .inf a, .fin _ => .inf a
  | .fin _, .inf b => .inf b
  | .fin a, .fin b => roundScaled (a.signed + b.signed) a.sign b.sign

theorem addFull_fin_fin (x y : SVal) :
    addFull (.fin x) (.fin y) =
      roundScaled (x.signed + y.signed) x.sign y.sign := rfl

/-! ## Signed zero -/

/-- A zero sum keeps a negative sign only when both summands are `-0`. -/
theorem addFull_zero_zero (sa sb : Bool) :
    addFull (.fin ⟨sa, 0⟩) (.fin ⟨sb, 0⟩) = .fin ⟨zeroSign sa sb, 0⟩ := by
  cases sa <;> cases sb <;> decide

theorem addFull_pos_zero_pos_zero :
    addFull (.fin ⟨false, 0⟩) (.fin ⟨false, 0⟩) = .fin ⟨false, 0⟩ := by
  decide

theorem addFull_pos_zero_neg_zero :
    addFull (.fin ⟨false, 0⟩) (.fin ⟨true, 0⟩) = .fin ⟨false, 0⟩ := by
  decide

theorem addFull_neg_zero_neg_zero :
    addFull (.fin ⟨true, 0⟩) (.fin ⟨true, 0⟩) = .fin ⟨true, 0⟩ := by
  decide

theorem fp16_add_pos_zero_pos_zero_bits :
    addFull (decodeFull (0x0000 : Fp16)) (decodeFull (0x0000 : Fp16)) =
      decodeFull (0x0000 : Fp16) := by
  decide

theorem fp16_add_pos_zero_neg_zero_bits :
    addFull (decodeFull (0x0000 : Fp16)) (decodeFull (0x8000 : Fp16)) =
      decodeFull (0x0000 : Fp16) := by
  decide

theorem fp16_add_neg_zero_neg_zero_bits :
    addFull (decodeFull (0x8000 : Fp16)) (decodeFull (0x8000 : Fp16)) =
      decodeFull (0x8000 : Fp16) := by
  decide

/-! ## Subnormal addition -/

/-- Any finite pair whose exact sum is at most `1023` units adds exactly on
the subnormal grid. -/
theorem addFull_fin_small_exact (x y : SVal)
    (h : (x.signed + y.signed).natAbs ≤ 1023) :
    addFull (.fin x) (.fin y) = .fin (x.add y) := by
  rw [addFull_fin_fin]
  by_cases h0 : x.signed + y.signed = 0
  · rw [SVal.add_eq_mk_of_eq_zero x y h0]
    unfold roundScaled
    rw [ite_eq_left h0]
  · rw [SVal.add_eq_mk_of_ne_zero x y h0]
    have hlt : (x.signed + y.signed).natAbs < 1024 := by omega
    unfold roundScaled
    rw [ite_eq_right h0, ite_eq_left hlt]

/-- Two subnormal operands stay in the first two binades, and when their sum
fits `1023` units it is exact. -/
theorem addFull_fin_subnormal_fits (x y : SVal) (hx : x.mag ≤ 1023)
    (hy : y.mag ≤ 1023) (h : (x.signed + y.signed).natAbs ≤ 1023) :
    addFull (.fin x) (.fin y) = .fin (x.add y) ∧
      (x.signed + y.signed).natAbs ≤ 2046 :=
  ⟨addFull_fin_small_exact x y h, SVal.natAbs_add_signed_le_2046 x y hx hy⟩

/-- The exact-value form of the subnormal case: the result's signed integer
is the exact sum and its magnitude stays on the subnormal grid. -/
theorem addFull_fin_subnormal_fits_value (x y : SVal) (hx : x.mag ≤ 1023)
    (hy : y.mag ≤ 1023) (h : (x.signed + y.signed).natAbs ≤ 1023) :
    ∃ r : SVal, addFull (.fin x) (.fin y) = .fin r ∧
      r.signed = x.signed + y.signed ∧ r.mag ≤ 1023 := by
  refine ⟨x.add y, (addFull_fin_subnormal_fits x y hx hy h).1,
    SVal.add_signed x y, ?_⟩
  by_cases h0 : x.signed + y.signed = 0
  · rw [SVal.add_eq_mk_of_eq_zero x y h0]
    simp
  · rw [SVal.add_eq_mk_of_ne_zero x y h0]
    simp
    omega

/-- A sum in the first normal binade `[1024, 2047]` is exact: that binade has
the same `2 ^ -24` quantum as the subnormal grid. -/
theorem addFull_fin_cross_aux (x y : SVal)
    (hlo : 1024 ≤ (x.signed + y.signed).natAbs)
    (hhi : (x.signed + y.signed).natAbs ≤ 2047) :
    addFull (.fin x) (.fin y) = .fin (x.add y) := by
  have hz : x.signed + y.signed ≠ 0 := by omega
  have hlog : Nat.log2 (x.signed + y.signed).natAbs = 10 := by
    have hm : (x.signed + y.signed).natAbs ≠ 0 := by omega
    rw [Nat.log2_eq_iff hm]
    have h1024 : (2 : Nat) ^ 10 = 1024 := by decide
    have h2048 : (2 : Nat) ^ 11 = 2048 := by decide
    constructor <;> omega
  rw [addFull_fin_fin, SVal.add_eq_mk_of_ne_zero x y hz]
  unfold roundScaled
  rw [ite_eq_right hz]
  rw [ite_eq_right (by omega : ¬ (x.signed + y.signed).natAbs < 1024)]
  have h2048 : ¬ 2048 ≤ (x.signed + y.signed).natAbs := by omega
  simp [hlog, roundEvenNat_one, h2048]

/-- Two subnormal operands whose sum crosses `1024` add exactly, and the
result is the first-binade normal with fraction `sum - 1024`. -/
theorem addFull_fin_subnormal_cross (x y : SVal) (hx : x.mag ≤ 1023)
    (hy : y.mag ≤ 1023) (h : 1024 ≤ (x.signed + y.signed).natAbs) :
    addFull (.fin x) (.fin y) = .fin (x.add y) := by
  have hle := SVal.natAbs_add_signed_le x y
  have hhi : (x.signed + y.signed).natAbs ≤ 2046 := by omega
  exact addFull_fin_cross_aux x y h (by omega)

/-- The exact-value form of the crossing case: the result's signed integer is
the exact sum and its magnitude lies in `[1024, 2046]`. -/
theorem addFull_fin_subnormal_cross_value (x y : SVal) (hx : x.mag ≤ 1023)
    (hy : y.mag ≤ 1023) (h : 1024 ≤ (x.signed + y.signed).natAbs) :
    ∃ r : SVal, addFull (.fin x) (.fin y) = .fin r ∧
      r.signed = x.signed + y.signed ∧ 1024 ≤ r.mag ∧ r.mag ≤ 2046 := by
  have hle := SVal.natAbs_add_signed_le x y
  have hmax : (x.signed + y.signed).natAbs ≤ 2046 := by omega
  have hz : x.signed + y.signed ≠ 0 := by omega
  refine ⟨x.add y, addFull_fin_subnormal_cross x y hx hy h,
    SVal.add_signed x y, ?_, ?_⟩
  · rw [SVal.add_eq_mk_of_ne_zero x y hz]
    simp
    omega
  · rw [SVal.add_eq_mk_of_ne_zero x y hz]
    simp
    omega

/-- The destination quantum of a crossing sum is one, so its round-to-even
step is the identity; no tie can occur in the first normal binade. -/
theorem subnormal_cross_destination_step (m : Nat) (h1 : 1024 ≤ m)
    (h2 : m ≤ 2047) : roundEvenNat (2 ^ (Nat.log2 m - 10)) m = m := by
  have hlog : Nat.log2 m = 10 := by
    have hm : m ≠ 0 := by omega
    rw [Nat.log2_eq_iff hm]
    have h1024 : (2 : Nat) ^ 10 = 1024 := by decide
    have h2048 : (2 : Nat) ^ 11 = 2048 := by decide
    constructor <;> omega
  rw [hlog, roundEvenNat_one]

theorem fp16_add_subnormal_fits_bits :
    addFull (decodeFull (0x0001 : Fp16)) (decodeFull (0x0002 : Fp16)) =
      decodeFull (0x0003 : Fp16) := by
  decide

theorem fp16_add_subnormal_cross_bits :
    addFull (decodeFull (0x03FF : Fp16)) (decodeFull (0x0001 : Fp16)) =
      decodeFull (0x0400 : Fp16) := by
  decide

theorem fp16_add_subnormal_cross_max_bits :
    addFull (decodeFull (0x03FF : Fp16)) (decodeFull (0x03FF : Fp16)) =
      decodeFull (0x07FE : Fp16) := by
  decide

theorem fp16_add_subnormal_cancel_bits :
    addFull (decodeFull (0x8001 : Fp16)) (decodeFull (0x0001 : Fp16)) =
      decodeFull (0x0000 : Fp16) := by
  decide

/-- Adding the smallest subnormal to a binade-2 normal with an odd mantissa is
an exact tie and rounds to the even mantissa `1026`. -/
theorem fp16_add_subnormal_tie_up_bits :
    addFull (decodeFull (0x0801 : Fp16)) (decodeFull (0x0001 : Fp16)) =
      decodeFull (0x0802 : Fp16) := by
  decide

/-- The same tie with an even mantissa rounds back down to `2048`. -/
theorem fp16_add_subnormal_tie_down_bits :
    addFull (decodeFull (0x0800 : Fp16)) (decodeFull (0x0001 : Fp16)) =
      decodeFull (0x0800 : Fp16) := by
  decide

/-! ## Overflow -/

/-- The largest finite magnitude in units of `2 ^ -24`: `65504`. -/
def maxFiniteScaled : Nat := 2047 * 2 ^ 29

/-- The round-to-nearest overflow threshold in units of `2 ^ -24`: `65520`,
halfway between `65504` and `65536`. -/
def overflowThreshold : Nat := 4095 * 2 ^ 28

theorem maxFiniteScaled_value : maxFiniteScaled = 65504 * 2 ^ 24 := by
  decide

theorem overflowThreshold_value : overflowThreshold = 65520 * 2 ^ 24 := by
  decide

theorem maxFinite_lt_overflowThreshold : maxFiniteScaled < overflowThreshold := by
  decide

/-- Rounding a magnitude in `[65520, 65536)` with the binade-30 quantum
`2 ^ 29` produces `2 ^ 40`, one binade above the largest finite value. -/
theorem roundEvenNat_pow29_eq_pow40 (m : Nat) (h1 : overflowThreshold ≤ m)
    (h2 : m < 2 ^ 40) : roundEvenNat (2 ^ 29) m = 2 ^ 40 := by
  have hq : 0 < 2 ^ 29 := by decide
  have hqe : (2 ^ 29) % 2 = 0 := by decide
  have hk : 2047 % 2 = 1 := by decide
  have hT : overflowThreshold = 1099243192320 := by decide
  have hM : 2047 * (2 : Nat) ^ 29 = 1098974756864 := by decide
  have hHalf : (2 : Nat) ^ 29 / 2 = 268435456 := by decide
  have h40 : (2 : Nat) ^ 40 = 1099511627776 := by decide
  have h2048 : (2047 + 1) * 2 ^ 29 = 2 ^ 40 := by decide
  rw [hT] at h1
  rw [h40] at h2
  have hr1 : 2 ^ 29 / 2 ≤ m - 2047 * 2 ^ 29 := by omega
  have hr2 : m - 2047 * 2 ^ 29 < 2 ^ 29 := by omega
  have hsum : 2047 * 2 ^ 29 + (m - 2047 * 2 ^ 29) = m := by omega
  rw [← hsum]
  rw [roundEvenNat_eq_succ_mul_of_half_le (2 ^ 29) 2047
    (m - 2047 * 2 ^ 29) hq hqe hk hr1 hr2]

theorem log2_eq_39_of_threshold_le (m : Nat) (h1 : overflowThreshold ≤ m)
    (h2 : m < 2 ^ 40) : Nat.log2 m = 39 := by
  have hm : m ≠ 0 := by
    have hT : overflowThreshold = 1099243192320 := by decide
    omega
  rw [Nat.log2_eq_iff hm]
  constructor
  · have h39 : (2 : Nat) ^ 39 ≤ overflowThreshold := by decide
    exact Nat.le_trans h39 h1
  · exact h2

/-- A scaled magnitude at or above the threshold and below `2 ^ 41` makes
`roundScaled` overflow to the correctly signed infinity. -/
theorem roundScaled_overflow (z : Int) (sa sb : Bool)
    (h1 : overflowThreshold ≤ z.natAbs) (h2 : z.natAbs < 2 ^ 41) :
    roundScaled z sa sb = .inf (z < 0) := by
  have hm0 : z ≠ 0 := by
    intro hz
    rw [hz] at h1
    simp at h1
    have hT : overflowThreshold = 1099243192320 := by decide
    omega
  have hm1024 : ¬ z.natAbs < 1024 := by
    have hT : overflowThreshold = 1099243192320 := by decide
    omega
  unfold roundScaled
  rw [ite_eq_right hm0, ite_eq_right hm1024]
  by_cases hlt : z.natAbs < 2 ^ 40
  · have hlog : Nat.log2 z.natAbs = 39 := log2_eq_39_of_threshold_le _ h1 hlt
    have hr : roundEvenNat (2 ^ 29) z.natAbs = 2 ^ 40 :=
      roundEvenNat_pow29_eq_pow40 _ h1 hlt
    have hmant : roundEvenNat (2 ^ 29) z.natAbs / 2 ^ 29 = 2048 := by
      rw [hr]
    simp [hlog, hmant]
  · have hge : 2 ^ 40 ≤ z.natAbs := by omega
    have hlog : Nat.log2 z.natAbs = 40 := by
      have hm : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hm0
      rw [Nat.log2_eq_iff hm]
      exact ⟨hge, h2⟩
    simp [hlog]

/-- Every scaled magnitude below the threshold has a finite `roundScaled`
result.  The only rejected branch would round to `2 ^ 40`, which needs the
exact sum to be at least `2 ^ 40 - 2 ^ 28`, i.e. the threshold. -/
theorem roundScaled_fin_of_lt_threshold (z : Int) (sa sb : Bool)
    (h : z.natAbs < overflowThreshold) :
    ∃ v : SVal, roundScaled z sa sb = .fin v := by
  unfold roundScaled
  by_cases hz : z = 0
  · exact ⟨⟨zeroSign sa sb, 0⟩, by rw [ite_eq_left hz]⟩
  · rw [ite_eq_right hz]
    by_cases hsmall : z.natAbs < 1024
    · exact ⟨⟨z < 0, z.natAbs⟩, by rw [ite_eq_left hsmall]⟩
    · rw [ite_eq_right hsmall]
      have hT40 : overflowThreshold < 2 ^ 40 := by decide
      have hm40 : z.natAbs < 2 ^ 40 := by omega
      have hm0 : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
      have hlogle : Nat.log2 z.natAbs < 40 := by
        rw [Nat.log2_lt hm0]
        exact hm40
      by_cases hbig : 2048 ≤
          roundEvenNat (2 ^ (Nat.log2 z.natAbs - 10)) z.natAbs /
            2 ^ (Nat.log2 z.natAbs - 10)
      · have hlogne : Nat.log2 z.natAbs ≠ 39 := by
          intro h39
          have hbig' : 2048 ≤ roundEvenNat (2 ^ 29) z.natAbs / 2 ^ 29 := by
            simpa [h39] using hbig
          have hrge : 2 ^ 40 ≤ roundEvenNat (2 ^ 29) z.natAbs := by
            have := (Nat.le_div_iff_mul_le (by decide : 0 < 2 ^ 29)).mp hbig'
            simpa [show 2048 * (2 : Nat) ^ 29 = 2 ^ 40 by decide] using this
          have hrle : roundEvenNat (2 ^ 29) z.natAbs ≤ z.natAbs + 2 ^ 28 := by
            have := roundEvenNat_le_add_half (2 ^ 29) z.natAbs (by decide)
            simpa [show (2 : Nat) ^ 29 / 2 = 2 ^ 28 by decide] using this
          have hthr : overflowThreshold = 2 ^ 40 - 2 ^ 28 := by decide
          omega
        have he1 : Nat.log2 z.natAbs - 9 + 1 ≤ 30 := by omega
        refine ⟨⟨z < 0, 1024 * 2 ^ (Nat.log2 z.natAbs - 9)⟩, ?_⟩
        simp [hbig, he1]
      · have he : Nat.log2 z.natAbs - 9 ≤ 30 := by omega
        refine ⟨⟨z < 0,
          roundEvenNat (2 ^ (Nat.log2 z.natAbs - 10)) z.natAbs /
            2 ^ (Nat.log2 z.natAbs - 10) * 2 ^ (Nat.log2 z.natAbs - 9 - 1)⟩, ?_⟩
        simp [hbig, he]

/-- At or above the threshold the finite sum overflows to infinity. -/
theorem addFull_fin_overflow_of_ge_threshold (x y : SVal)
    (hx : x.mag ≤ maxFiniteScaled) (hy : y.mag ≤ maxFiniteScaled)
    (h : overflowThreshold ≤ (x.signed + y.signed).natAbs) :
    addFull (.fin x) (.fin y) = .inf ((x.signed + y.signed) < 0) := by
  rw [addFull_fin_fin]
  apply roundScaled_overflow
  · exact h
  · have hle := Int.natAbs_add_le x.signed y.signed
    rw [SVal.natAbs_signed, SVal.natAbs_signed] at hle
    have hconst : 2 * maxFiniteScaled < 2 ^ 41 := by decide
    omega

theorem addFull_maxFinite_add_maxFinite :
    addFull (.fin ⟨false, maxFiniteScaled⟩) (.fin ⟨false, maxFiniteScaled⟩) =
      .inf false := by
  rw [addFull_fin_fin]
  have h1 : overflowThreshold ≤ ((⟨false, maxFiniteScaled⟩ : SVal).signed +
      (⟨false, maxFiniteScaled⟩ : SVal).signed).natAbs := by
    decide
  have h2 : ((⟨false, maxFiniteScaled⟩ : SVal).signed +
      (⟨false, maxFiniteScaled⟩ : SVal).signed).natAbs < 2 ^ 41 := by decide
  exact roundScaled_overflow _ false false h1 h2

theorem addFull_neg_maxFinite_add_neg_maxFinite :
    addFull (.fin ⟨true, maxFiniteScaled⟩) (.fin ⟨true, maxFiniteScaled⟩) =
      .inf true := by
  rw [addFull_fin_fin]
  have h1 : overflowThreshold ≤ ((⟨true, maxFiniteScaled⟩ : SVal).signed +
      (⟨true, maxFiniteScaled⟩ : SVal).signed).natAbs := by
    decide
  have h2 : ((⟨true, maxFiniteScaled⟩ : SVal).signed +
      (⟨true, maxFiniteScaled⟩ : SVal).signed).natAbs < 2 ^ 41 := by decide
  exact roundScaled_overflow _ true true h1 h2

/-- For legal finite operands, overflow is exactly the threshold: the result
is finite iff the exact scaled sum is below `4095 * 2 ^ 28`. -/
theorem addFull_fin_overflow_iff (x y : SVal)
    (hx : x.mag ≤ maxFiniteScaled) (hy : y.mag ≤ maxFiniteScaled) :
    (x.signed + y.signed).natAbs < overflowThreshold ↔
      ∃ v : SVal, addFull (.fin x) (.fin y) = .fin v := by
  constructor
  · intro h
    rw [addFull_fin_fin]
    exact roundScaled_fin_of_lt_threshold _ _ _ h
  · rintro ⟨v, hv⟩
    by_cases hge : overflowThreshold ≤ (x.signed + y.signed).natAbs
    · have hov := addFull_fin_overflow_of_ge_threshold x y hx hy hge
      rw [hov] at hv
      cases hv
    · omega

/-- The overflowing `65504 + 65504` sum is exactly the value that stage 149
proved unrepresentable in the normal fragment; here it becomes infinity. -/
theorem fp16_add_maxFinite_overflow_exact :
    addFull (.fin ⟨false, maxFiniteScaled⟩) (.fin ⟨false, maxFiniteScaled⟩) =
        .inf false ∧
      ¬ ∃ f : Fixed, f.mant ≤ 2047 ∧ f.exp + 15 ≤ 30 ∧
        f.mag = 4094 * 2 ^ 15 :=
  ⟨addFull_maxFinite_add_maxFinite, fp16_add_overflow_not_representable⟩

theorem fp16_add_maxFinite_bits :
    addFull (decodeFull (0x7BFF : Fp16)) (decodeFull (0x7BFF : Fp16)) =
      decodeFull (0x7C00 : Fp16) := by
  decide

theorem fp16_add_neg_maxFinite_bits :
    addFull (decodeFull (0xFBFF : Fp16)) (decodeFull (0xFBFF : Fp16)) =
      decodeFull (0xFC00 : Fp16) := by
  decide

/-- `65504 + 16 = 65520` is the exact tie at the overflow threshold. -/
theorem fp16_add_maxFinite_sixteen_bits :
    addFull (decodeFull (0x7BFF : Fp16)) (decodeFull (0x4C00 : Fp16)) =
      decodeFull (0x7C00 : Fp16) := by
  decide

/-- `65504 + 15 = 65519` is below the threshold and rounds back to the
largest finite value. -/
theorem fp16_add_maxFinite_fifteen_bits :
    addFull (decodeFull (0x7BFF : Fp16)) (decodeFull (0x4B80 : Fp16)) =
      decodeFull (0x7BFF : Fp16) := by
  decide

/-- `65504 + 1 = 65505` is above the maximum finite value but below the
threshold, so it does not overflow.  This is why the threshold is `65520`,
not `65504`. -/
theorem fp16_add_maxFinite_one_bits :
    addFull (decodeFull (0x7BFF : Fp16)) (decodeFull (0x3C00 : Fp16)) =
      decodeFull (0x7BFF : Fp16) := by
  decide

/-! ## NaN and infinity propagation -/

theorem addFull_nan_left (ng : Bool) (p : Nat) (q : Bool) (v : Fp16Val) :
    addFull (.nan ng p q) v = .nan ng p true := by
  cases v <;> rfl

theorem addFull_nan_finite (ng : Bool) (p : Nat) (q : Bool) (v : SVal) :
    addFull (.nan ng p q) (.fin v) = .nan ng p true := rfl

theorem addFull_finite_nan (v : SVal) (ng : Bool) (p : Nat) (q : Bool) :
    addFull (.fin v) (.nan ng p q) = .nan ng p true := rfl

theorem addFull_nan_nan (ng ng' : Bool) (p p' : Nat) (q q' : Bool) :
    addFull (.nan ng p q) (.nan ng' p' q') = .nan ng p true := rfl

theorem addFull_inf_same (a : Bool) :
    addFull (.inf a) (.inf a) = .inf a := by
  cases a <;> decide

theorem addFull_inf_opposite (a : Bool) :
    addFull (.inf a) (.inf (!a)) = .nan false 0 true := by
  cases a <;> decide

theorem addFull_inf_fin (a : Bool) (v : SVal) :
    addFull (.inf a) (.fin v) = .inf a := rfl

theorem addFull_fin_inf (v : SVal) (a : Bool) :
    addFull (.fin v) (.inf a) = .inf a := rfl

theorem fp16_add_nan_finite_bits :
    addFull (decodeFull (0x7E00 : Fp16)) (decodeFull (0x3C00 : Fp16)) =
      decodeFull (0x7E00 : Fp16) := by
  decide

/-- A signaling NaN is quieted, keeping its payload and sign. -/
theorem fp16_add_snan_finite_bits :
    addFull (decodeFull (0x7C01 : Fp16)) (decodeFull (0x3C00 : Fp16)) =
      .nan false 1 true := by
  decide

theorem decodeFull_quieted_snan : decodeFull (0x7E01 : Fp16) = .nan false 1 true := by
  decide

theorem fp16_add_nan_nan_bits :
    addFull (decodeFull (0x7E02 : Fp16)) (decodeFull (0x7E01 : Fp16)) =
      .nan false 2 true := by
  decide

theorem fp16_add_nan_nan_reverse_bits :
    addFull (decodeFull (0x7E01 : Fp16)) (decodeFull (0x7E02 : Fp16)) =
      .nan false 1 true := by
  decide

theorem fp16_add_inf_finite_bits :
    addFull (decodeFull (0x7C00 : Fp16)) (decodeFull (0x7BFF : Fp16)) =
      decodeFull (0x7C00 : Fp16) := by
  decide

theorem fp16_add_inf_opposite_bits :
    addFull (decodeFull (0x7C00 : Fp16)) (decodeFull (0xFC00 : Fp16)) =
      decodeFull (0x7E00 : Fp16) := by
  decide

/-! ## Counterexamples -/

/-- The smallest subnormals add exactly: `0x0001 + 0x0001 = 0x0002`. -/
theorem fp16_add_smallest_subnormal_double_bits :
    addFull (decodeFull (0x0001 : Fp16)) (decodeFull (0x0001 : Fp16)) =
      decodeFull (0x0002 : Fp16) := by
  decide

/-- A flush-to-zero model: every subnormal becomes a signed zero. -/
def flushSubnormal : Fp16Val → Fp16Val
  | .fin v => if v.mag < 1024 then .fin ⟨v.sign, 0⟩ else .fin v
  | v => v

/-- Flush-to-zero sends that exact sum to zero. -/
theorem flush_subnormal_zeroes :
    flushSubnormal (addFull (decodeFull (0x0001 : Fp16))
        (decodeFull (0x0001 : Fp16))) = decodeFull (0x0000 : Fp16) := by
  decide

/-- Flush-to-zero is not IEEE: it differs from the exact result on
`0x0001 + 0x0001`. -/
theorem flush_subnormal_differs :
    flushSubnormal (addFull (decodeFull (0x0001 : Fp16))
        (decodeFull (0x0001 : Fp16))) ≠
      addFull (decodeFull (0x0001 : Fp16)) (decodeFull (0x0001 : Fp16)) := by
  decide

/-- A signaling NaN is not preserved verbatim: its quiet bit is set. -/
theorem snan_not_preserved_verbatim :
    decodeFull (0x7C01 : Fp16) = .nan false 1 false ∧
      addFull (decodeFull (0x7C01 : Fp16)) (decodeFull (0x3C00 : Fp16)) =
        .nan false 1 true := by
  constructor <;> decide

/-- A sum of subnormals can be normal, so "subnormal plus subnormal is
subnormal" is false at the boundary. -/
theorem subnormal_add_can_be_normal :
    addFull (decodeFull (0x03FF : Fp16)) (decodeFull (0x0001 : Fp16)) =
      decodeFull (0x0400 : Fp16) := by
  decide

end IntelGpu
