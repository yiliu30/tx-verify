-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Fp16Bits
public import Intel.RoundingEven

@[expose] public section

/-!
# A restricted IEEE-754 fp16 addition

`Intel.Fp16Bits` decodes the finite normal fragment of fp16 into `Fixed`
values, `Fixed.mag = mant * 2 ^ exp`, with `mant` the 11-bit significand. In
units of `2 ^ -10` a decoded value is the signed integer `Fixed.signed`, so an
exact sum of two decoded values is an integer at that scale.

This module proves the restricted round-to-nearest-even addition result:

- `decoded_add_single_rounding` / `fp16_add_single_rounding`: when the exact
  sum is on the destination grid `2 ^ e0`, one rounding is the identity.
- `fp16_add_halfway_even` and `fp16_add_halfway_even_mantissa`: an exact
  halfway sum selects the endpoint with the even quotient (even mantissa),
  which is the IEEE round-to-nearest-even tie rule. The negative-sum version
  is `fp16_add_halfway_even_neg`.
- `decode_encodeFixed`: the local normal encoder round-trips through `decode`.
- `fp16_add_no_double_rounding`: decoding both operands, rounding the exact
  sum once, and encoding the rounded result decodes back to exactly that one
  rounding; re-rounding the encoded value is the identity.
- `fp16_add_zero_cancellation` / `fp16_add_zero_encode_none`: exact
  cancellation produces zero, and zero has no word in the decoded fragment.
- `fp16_add_overflow_not_representable`: a sum beyond the finite range has no
  normal `Fixed` representation; overflow to infinity is not modeled.

## Proved class

The proof covers two words that `decode` accepts: normalized finite fp16
operands with exponent field in `[15, 30]` (unbiased exponent `0..15`).
Values are exact signed integers in units of `2 ^ -10`. The destination
exponent `e0` is a hypothesis, not computed: it must satisfy `e0 ≤` both
operand exponents, and encoding additionally requires the rounded quotient to
be an 11-bit significand in `[1024, 2047]` at exponent `e0 ≤ 15`. Thus this is
**addition on a common no-overflow grid**, not a full IEEE fp16 adder.

Outside the proved class: subnormal operands and results, signed zero bits,
NaN payloads, overflow to infinity, renormalization after rounding up to
`2048`, and any fused multiply-add. In particular this is **not a full IEEE
FMA**; it is one correctly rounded addition path for the decoded normal
fragment. The neighbouring `Intel.Fp16Value` module keeps NaN/infinity as
classes, and `decode` returns `none` for both.

The tempting general statement `roundEven q2 (roundEven q1 x) = roundEven q2 x`
is false even for nested grids; `double_rounding_counterexample` records the
counterexample `q1 = 2`, `q2 = 8`, `x = 5`. The no-double-rounding theorem
below is therefore about this addition path doing exactly one rounding, not
about arbitrary nested rounding.
-/

namespace IntelGpu

/-! ## Signed scaled values -/

/-- The signed value in units of `2 ^ -10`. -/
def Fixed.signed (v : Fixed) : Int :=
  if v.sign then -(v.mag : Int) else (v.mag : Int)

/-- The sign bit does not change the magnitude. -/
theorem Fixed.natAbs_signed (v : Fixed) : v.signed.natAbs = v.mag := by
  unfold Fixed.signed
  split <;> simp

/-! ## Rounding multiples and signed values -/

theorem roundEvenNat_zero (q : Nat) : roundEvenNat q 0 = 0 := by
  unfold roundEvenNat
  split
  · rename_i h
    split
    · simp
    · rename_i hc
      simp [Nat.zero_div] at hc
  · rename_i h
    have hq : q ≠ 0 := by
      intro hq
      subst hq
      simp at h
    have hlt : q / 2 < q :=
      Nat.div_lt_self (Nat.pos_of_ne_zero hq) (by decide)
    rw [Nat.zero_add, Nat.div_eq_of_lt hlt]
    simp

theorem roundEven_zero (q : Nat) : roundEven q 0 = 0 := by
  unfold roundEven
  rw [ite_eq_left (show (0 : Int) ≤ 0 by decide)]
  rw [show ((0 : Int).toNat) = 0 from rfl, roundEvenNat_zero]
  rfl

/-- Negating the input negates the rounded result, including at ties. -/
theorem roundEven_neg (q : Nat) (x : Int) :
    roundEven q (-x) = -roundEven q x := by
  by_cases hx : 0 ≤ x
  · by_cases hx0 : x = 0
    · subst hx0
      rw [Int.neg_zero, roundEven_zero, Int.neg_zero]
    · have hneg : ¬ 0 ≤ -x := by omega
      rw [roundEven_of_neg q hneg, roundEven_of_nonneg q hx, Int.neg_neg]
  · have hneg : 0 ≤ -x := by omega
    rw [roundEven_of_neg q hx, roundEven_of_nonneg q hneg, Int.neg_neg]

/-- Rounding a signed multiple of `q` is the identity. -/
theorem roundEven_mul (q : Nat) (hq : 0 < q) (k : Int) :
    roundEven q (k * (q : Int)) = k * (q : Int) := by
  by_cases hk : 0 ≤ k
  · have hk' : ((k.toNat : Int)) = k := Int.toNat_of_nonneg hk
    rw [← hk']
    rw [show ((k.toNat : Int) * (q : Int)) = ((k.toNat * q : Nat) : Int) by
      rw [Int.natCast_mul]]
    rw [roundEven_of_nonneg q (Int.natCast_nonneg _), Int.toNat_natCast,
      roundEvenNat_mul q k.toNat hq]
  · have hk' : ((-k).toNat : Int) = -k := Int.toNat_of_nonneg (by omega)
    have hz : k * (q : Int) = -(((-k).toNat : Int) * (q : Int)) := by
      rw [hk']
      rw [Int.neg_mul, Int.neg_neg]
    have hcast : ((-k).toNat : Int) * (q : Int) = (((-k).toNat * q : Nat) : Int) := by
      rw [Int.natCast_mul]
    rw [hz, roundEven_neg, hcast, roundEven_of_nonneg q (Int.natCast_nonneg _),
      Int.toNat_natCast, roundEvenNat_mul q (-k).toNat hq]

/-- A value that is an integer multiple of `q` is unchanged by rounding. -/
theorem roundEven_exact_of_dvd (q : Nat) (hq : 0 < q) (x : Int)
    (h : (q : Int) ∣ x) : roundEven q x = x := by
  rcases h with ⟨k, hk⟩
  rw [hk, Int.mul_comm]
  exact roundEven_mul q hq k

/-- A sum of two grid multiples is unchanged by one rounding. -/
theorem roundEven_add_exact (q : Nat) (hq : 0 < q) (x y : Int)
    (hx : (q : Int) ∣ x) (hy : (q : Int) ∣ y) :
    roundEven q (x + y) = x + y := by
  apply roundEven_exact_of_dvd q hq
  exact Int.dvd_add hx hy

/-- A decoded value is a multiple of `2 ^ e0` when its exponent is at least
`e0`. -/
theorem Fixed.dvd_signed_of_exp (v : Fixed) (e0 : Nat) (h : e0 ≤ v.exp) :
    ((2 ^ e0 : Nat) : Int) ∣ v.signed := by
  obtain ⟨k, hk⟩ := Fixed.mag_grid v e0 h
  refine ⟨if v.sign then -(k : Int) else (k : Int), ?_⟩
  unfold Fixed.signed
  split
  · rw [hk]
    push_cast
    rw [Int.mul_neg, Int.mul_comm]
  · rw [hk]
    push_cast
    rw [Int.mul_comm]

/-- The main single-rounding statement: two decoded finite values whose
exponents are at least `e0` have an exact sum on the `2 ^ e0` grid, so rounding
that sum once is the identity. -/
theorem decoded_add_single_rounding (e0 : Nat) (fa fb : Fixed)
    (ha : e0 ≤ fa.exp) (hb : e0 ≤ fb.exp) :
    roundEven (2 ^ e0) (fa.signed + fb.signed) = fa.signed + fb.signed := by
  apply roundEven_add_exact (2 ^ e0) (Nat.two_pow_pos e0)
  · exact Fixed.dvd_signed_of_exp fa e0 ha
  · exact Fixed.dvd_signed_of_exp fb e0 hb

/-- The bit-level form of `decoded_add_single_rounding`, with the exponent
floor read from the decoded fields. -/
theorem fp16_add_single_rounding (e0 : Nat) (wa wb : Fp16) (fa fb : Fixed)
    (ha : decode wa = some fa) (hb : decode wb = some fb)
    (hea : e0 ≤ expField wa - 15) (heb : e0 ≤ expField wb - 15) :
    roundEven (2 ^ e0) (fa.signed + fb.signed) = fa.signed + fb.signed := by
  apply decoded_add_single_rounding e0 fa fb
  · rw [(decode_some wa fa ha).2.1]; exact hea
  · rw [(decode_some wb fb hb).2.1]; exact heb

/-! ## Ties to even -/

/-- A halfway Nat case selects the even-quotient endpoint. -/
theorem roundEvenNat_halfway_even (q k : Nat) (hq : 0 < q) (hqe : q % 2 = 0) :
    roundEvenNat q (k * q + q / 2) =
      if k % 2 = 0 then k * q else (k + 1) * q := by
  have hlt : q / 2 < q := Nat.div_lt_self hq (by decide)
  have hmod : (k * q + q / 2) % q = q / 2 :=
    Nat.mul_add_mod_of_lt (a := k) (b := q) (c := q / 2) hlt
  have hdiv : (k * q + q / 2) / q = k := by
    rw [Nat.mul_comm k q, Nat.mul_add_div hq, Nat.div_eq_of_lt hlt, Nat.add_zero]
  rw [roundEvenNat_tie q _ ⟨hqe, hmod⟩, hdiv]
  split <;> simp [Nat.succ_mul]

/-- At a tie the chosen Nat result is one of the two adjacent grid points. -/
theorem roundEvenNat_halfway_nearest (q k : Nat) (hq : 0 < q) (hqe : q % 2 = 0) :
    roundEvenNat q (k * q + q / 2) = k * q ∨
      roundEvenNat q (k * q + q / 2) = (k + 1) * q := by
  rw [roundEvenNat_halfway_even q k hq hqe]
  split
  · exact Or.inl rfl
  · exact Or.inr (by rw [Nat.succ_mul])

/-- At a tie the chosen Nat result has even quotient, i.e. even mantissa. -/
theorem roundEvenNat_halfway_quotient_even (q k : Nat) (hq : 0 < q)
    (hqe : q % 2 = 0) :
    ∃ j, j % 2 = 0 ∧ roundEvenNat q (k * q + q / 2) = j * q := by
  rw [roundEvenNat_halfway_even q k hq hqe]
  split
  · rename_i hk
    exact ⟨k, hk, rfl⟩
  · rename_i hk
    refine ⟨k + 1, ?_, ?_⟩
    · omega
    · rw [Nat.succ_mul]

/-- The signed nonnegative halfway case. -/
theorem roundEven_halfway_even (q k : Nat) (hq : 0 < q) (hqe : q % 2 = 0) :
    roundEven q ((k : Int) * (q : Int) + ((q / 2 : Nat) : Int)) =
      if k % 2 = 0 then (k : Int) * (q : Int)
      else ((k + 1 : Nat) : Int) * (q : Int) := by
  have hz : (k : Int) * (q : Int) + ((q / 2 : Nat) : Int) =
      ((k * q + q / 2 : Nat) : Int) := by
    push_cast
    rfl
  rw [hz, roundEven_of_nonneg q (Int.natCast_nonneg _), Int.toNat_natCast,
    roundEvenNat_halfway_even q k hq hqe]
  split <;> push_cast <;> rfl

/-- The negative halfway case is the negation of the positive one. -/
theorem roundEven_halfway_even_neg (q k : Nat) (hq : 0 < q) (hqe : q % 2 = 0) :
    roundEven q (-((k : Int) * (q : Int) + ((q / 2 : Nat) : Int))) =
      -(if k % 2 = 0 then (k : Int) * (q : Int)
        else ((k + 1 : Nat) : Int) * (q : Int)) := by
  rw [roundEven_neg, roundEven_halfway_even q k hq hqe]

/-- The chosen signed result at a tie has even mantissa. -/
theorem roundEven_halfway_even_mantissa (q k : Nat) (hq : 0 < q)
    (hqe : q % 2 = 0) :
    ∃ j : Nat, j % 2 = 0 ∧
      roundEven q ((k : Int) * (q : Int) + ((q / 2 : Nat) : Int)) =
        (j : Int) * (q : Int) := by
  obtain ⟨j, hje, hj⟩ := roundEvenNat_halfway_quotient_even q k hq hqe
  refine ⟨j, hje, ?_⟩
  have hz : (k : Int) * (q : Int) + ((q / 2 : Nat) : Int) =
      ((k * q + q / 2 : Nat) : Int) := by
    push_cast
    rfl
  rw [hz, roundEven_of_nonneg q (Int.natCast_nonneg _), Int.toNat_natCast, hj]
  push_cast
  rfl

/-- fp16-grid halfway case: destination quantum `2 ^ e0`, with `e0 > 0` so a
halfway integer exists. -/
theorem fp16_add_halfway_even (e0 k : Nat) (he0 : 0 < e0) :
    roundEven (2 ^ e0) ((k : Int) * (2 ^ e0 : Int) + ((2 ^ e0 / 2 : Nat) : Int)) =
      if k % 2 = 0 then (k : Int) * (2 ^ e0 : Int)
      else ((k + 1 : Nat) : Int) * (2 ^ e0 : Int) := by
  have hqe : (2 ^ e0) % 2 = 0 := by
    rw [Nat.two_pow_mod_two_eq_zero]
    exact he0
  exact roundEven_halfway_even (2 ^ e0) k (Nat.two_pow_pos e0) hqe

/-- fp16-grid halfway case for a negative exact sum. -/
theorem fp16_add_halfway_even_neg (e0 k : Nat) (he0 : 0 < e0) :
    roundEven (2 ^ e0)
        (-((k : Int) * (2 ^ e0 : Int) + ((2 ^ e0 / 2 : Nat) : Int))) =
      -(if k % 2 = 0 then (k : Int) * (2 ^ e0 : Int)
        else ((k + 1 : Nat) : Int) * (2 ^ e0 : Int)) := by
  have hqe : (2 ^ e0) % 2 = 0 := by
    rw [Nat.two_pow_mod_two_eq_zero]
    exact he0
  exact roundEven_halfway_even_neg (2 ^ e0) k (Nat.two_pow_pos e0) hqe

/-- fp16-grid halfway case with an explicit even mantissa. -/
theorem fp16_add_halfway_even_mantissa (e0 k : Nat) (he0 : 0 < e0) :
    ∃ j : Nat, j % 2 = 0 ∧
      roundEven (2 ^ e0) ((k : Int) * (2 ^ e0 : Int) + ((2 ^ e0 / 2 : Nat) : Int)) =
        (j : Int) * (2 ^ e0 : Int) := by
  have hqe : (2 ^ e0) % 2 = 0 := by
    rw [Nat.two_pow_mod_two_eq_zero]
    exact he0
  exact roundEven_halfway_even_mantissa (2 ^ e0) k (Nat.two_pow_pos e0) hqe

/-! ## Rounding idempotence and grid membership -/

theorem roundEvenNat_grid (q n : Nat) : ∃ k : Nat, roundEvenNat q n = k * q := by
  unfold roundEvenNat
  split
  · split
    · exact ⟨n / q, rfl⟩
    · exact ⟨n / q + 1, by rw [Nat.succ_mul]⟩
  · exact ⟨(n + q / 2) / q, rfl⟩

theorem roundEven_grid (q : Nat) (x : Int) :
    ∃ k : Int, roundEven q x = k * (q : Int) := by
  by_cases hx : 0 ≤ x
  · rw [roundEven_of_nonneg q hx]
    obtain ⟨k, hk⟩ := roundEvenNat_grid q x.toNat
    refine ⟨(k : Int), ?_⟩
    rw [hk]
    push_cast
    rfl
  · rw [roundEven_of_neg q hx]
    obtain ⟨k, hk⟩ := roundEvenNat_grid q (-x).toNat
    refine ⟨-(k : Int), ?_⟩
    rw [hk]
    push_cast
    rw [Int.neg_mul]

/-- Re-rounding an already rounded value changes nothing. -/
theorem roundEven_idem (q : Nat) (hq : 0 < q) (x : Int) :
    roundEven q (roundEven q x) = roundEven q x := by
  obtain ⟨k, hk⟩ := roundEven_grid q x
  rw [hk]
  exact roundEven_mul q hq k

/-! ## A local normal encoder

The core `Nat.and_two_pow_sub_one_eq_mod` proof depends on `Classical.choice`
in this toolchain (as the analogous note in `Intel.SbidEncoding` records), so
the mask facts used by the field extraction are proved locally without it. -/

theorem testBit_two_pow_sub_one_noClassical (n i : Nat) :
    Nat.testBit (2 ^ n - 1) i = decide (i < n) := by
  induction n generalizing i with
  | zero =>
      cases i <;> simp
  | succ n ih =>
      cases i with
      | zero =>
          rw [Nat.testBit_zero]
          have hmod : (2 ^ (n + 1) - 1) % 2 = 1 := by
            rw [Nat.pow_succ]
            have hp : 0 < 2 ^ n := Nat.two_pow_pos _
            omega
          simp [hmod]
      | succ j =>
          rw [Nat.testBit_succ]
          have hdiv : (2 ^ (n + 1) - 1) / 2 = 2 ^ n - 1 := by
            rw [Nat.pow_succ]
            have hp : 0 < 2 ^ n := Nat.two_pow_pos _
            omega
          rw [hdiv, ih j]
          simp

theorem and_two_pow_sub_one_eq_mod_noClassical (x n : Nat) :
    x &&& (2 ^ n - 1) = x % 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_mod_two_pow, testBit_two_pow_sub_one_noClassical]
  simp [Bool.and_comm]

theorem signBit_eq_true_iff (w : Fp16) :
    signBit w = true ↔ 2 ^ 15 ≤ w.toNat := by
  unfold signBit
  rw [bne_iff_ne, BitVec.toNat_ne,
    show BitVec.toNat (0 : Fp16) = 0 by decide,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow]
  constructor
  · intro h
    apply Nat.le_of_not_lt
    intro hlt
    exact h (Nat.div_eq_of_lt hlt)
  · intro h
    exact Nat.pos_iff_ne_zero.mp (Nat.div_pos h (by decide))

theorem signBit_eq_decide (w : Fp16) :
    signBit w = decide (2 ^ 15 ≤ w.toNat) := by
  by_cases h : 2 ^ 15 ≤ w.toNat
  · have hb : signBit w = true := (signBit_eq_true_iff w).mpr h
    rw [hb]
    exact (decide_eq_true h).symm
  · have hb : signBit w = false := by
      cases hs : signBit w with
      | false => rfl
      | true => exact absurd ((signBit_eq_true_iff w).mp hs) h
    rw [hb]
    exact (decide_eq_false h).symm

theorem expField_ofNat (n : Nat) (h : n < 2 ^ 16) :
    expField (BitVec.ofNat 16 n) = n / 2 ^ 10 % 2 ^ 5 := by
  unfold expField
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h, Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow]
  rw [show BitVec.toNat 31 = 2 ^ 5 - 1 by decide]
  rw [and_two_pow_sub_one_eq_mod_noClassical]

theorem mantField_ofNat (n : Nat) (h : n < 2 ^ 16) :
    mantField (BitVec.ofNat 16 n) = n % 2 ^ 10 := by
  unfold mantField
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  simp only [Nat.reducePow]
  rw [show BitVec.toNat 1023 = 2 ^ 10 - 1 by decide]
  rw [and_two_pow_sub_one_eq_mod_noClassical]

/-- Encode a normal `Fixed` as a 16-bit word. The round-trip theorem below
states the exact field range where this is a right inverse of `decode`. -/
def encodeFixed (f : Fixed) : Fp16 :=
  BitVec.ofNat 16
    ((if f.sign then 32768 else 0) + (f.exp + 15) * 1024 + (f.mant - 1024))

theorem encodeFixed_toNat (f : Fixed)
    (hm : 1024 ≤ f.mant) (hm2 : f.mant ≤ 2047) (he : f.exp + 15 ≤ 30) :
    (encodeFixed f).toNat =
      (if f.sign then 32768 else 0) + (f.exp + 15) * 1024 + (f.mant - 1024) := by
  unfold encodeFixed
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hmle : f.mant - 1024 ≤ 1023 := by omega
  have hs : (if f.sign then 32768 else 0) ≤ 32768 := by split <;> omega
  omega

theorem signBit_encodeFixed (f : Fixed)
    (hm : 1024 ≤ f.mant) (hm2 : f.mant ≤ 2047) (he : f.exp + 15 ≤ 30) :
    signBit (encodeFixed f) = f.sign := by
  let n := (if f.sign then 32768 else 0) + (f.exp + 15) * 1024 + (f.mant - 1024)
  have hn : (encodeFixed f).toNat = n := encodeFixed_toNat f hm hm2 he
  rw [signBit_eq_decide, hn]
  by_cases hs : f.sign
  · have hge : 2 ^ 15 ≤ n := by
      dsimp [n]
      rw [ite_eq_left hs]
      have hmle : f.mant - 1024 ≤ 1023 := by omega
      omega
    simp [hs, hge]
  · have hlt : ¬ 2 ^ 15 ≤ n := by
      dsimp [n]
      rw [ite_eq_right hs]
      have hmle : f.mant - 1024 ≤ 1023 := by omega
      omega
    simp [hs, hlt]

theorem expField_encodeFixed (f : Fixed)
    (hm : 1024 ≤ f.mant) (hm2 : f.mant ≤ 2047) (he : f.exp + 15 ≤ 30) :
    expField (encodeFixed f) = f.exp + 15 := by
  let n := (if f.sign then 32768 else 0) + (f.exp + 15) * 1024 + (f.mant - 1024)
  have hn : (encodeFixed f).toNat = n := encodeFixed_toNat f hm hm2 he
  have hnlt : n < 2 ^ 16 := by rw [← hn]; exact BitVec.isLt _
  have hdef : encodeFixed f = BitVec.ofNat 16 n := rfl
  rw [hdef, expField_ofNat n hnlt]
  have hmle : f.mant - 1024 ≤ 1023 := by omega
  have hdiv : n / 1024 = (if f.sign then 32 else 0) + (f.exp + 15) := by
    dsimp [n]
    have hnum : (if f.sign then 32768 else 0) + (f.exp + 15) * 1024 +
        (f.mant - 1024) =
        1024 * ((if f.sign then 32 else 0) + (f.exp + 15)) + (f.mant - 1024) := by
      split <;> omega
    rw [hnum, Nat.mul_add_div (by decide : 0 < 1024),
      Nat.div_eq_of_lt (by omega : f.mant - 1024 < 1024), Nat.add_zero]
  rw [hdiv]
  have hmod : ((if f.sign then 32 else 0) + (f.exp + 15)) % 32 = f.exp + 15 := by
    split <;> omega
  rw [show (2 : Nat) ^ 5 = 32 by decide, hmod]

theorem mantField_encodeFixed (f : Fixed)
    (hm : 1024 ≤ f.mant) (hm2 : f.mant ≤ 2047) (he : f.exp + 15 ≤ 30) :
    mantField (encodeFixed f) = f.mant - 1024 := by
  let n := (if f.sign then 32768 else 0) + (f.exp + 15) * 1024 + (f.mant - 1024)
  have hn : (encodeFixed f).toNat = n := encodeFixed_toNat f hm hm2 he
  have hnlt : n < 2 ^ 16 := by rw [← hn]; exact BitVec.isLt _
  have hdef : encodeFixed f = BitVec.ofNat 16 n := rfl
  rw [hdef, mantField_ofNat n hnlt]
  have hmle : f.mant - 1024 ≤ 1023 := by omega
  dsimp [n]
  split <;> omega

/-- Encoding a normal `Fixed` and decoding it returns the same value. -/
theorem decode_encodeFixed (f : Fixed)
    (hm : 1024 ≤ f.mant) (hm2 : f.mant ≤ 2047) (he : f.exp + 15 ≤ 30) :
    decode (encodeFixed f) = some f := by
  have hs := signBit_encodeFixed f hm hm2 he
  have hf := expField_encodeFixed f hm hm2 he
  have hmf := mantField_encodeFixed f hm hm2 he
  have hne31 : expField (encodeFixed f) ≠ 31 := by rw [hf]; omega
  have hne0 : expField (encodeFixed f) ≠ 0 := by rw [hf]; omega
  have hge : 15 ≤ expField (encodeFixed f) := by rw [hf]; omega
  unfold decode
  rw [ite_eq_right hne31, ite_eq_right hne0,
    ite_eq_right (by omega : ¬ expField (encodeFixed f) < 15)]
  rw [hs, hf, hmf]
  have hmant : 1024 + (f.mant - 1024) = f.mant := by omega
  have hexp : f.exp + 15 - 15 = f.exp := by omega
  rw [hmant, hexp]

/-! ## Encoding a rounded scaled value -/

/-- Encode a scaled integer at a chosen destination exponent, or `none` when
the quotient is not an 11-bit significand or the exponent is out of range. -/
def encodeScaled (e : Nat) (x : Int) : Option Fixed :=
  if x.natAbs % 2 ^ e = 0 ∧ 1024 ≤ x.natAbs / 2 ^ e ∧
      x.natAbs / 2 ^ e ≤ 2047 ∧ e ≤ 15 then
    some { sign := x < 0, mant := x.natAbs / 2 ^ e, exp := e }
  else none

theorem encodeScaled_spec (e : Nat) (x : Int) (f : Fixed)
    (h : encodeScaled e x = some f) :
    f.mant = x.natAbs / 2 ^ e ∧ f.exp = e ∧
      1024 ≤ f.mant ∧ f.mant ≤ 2047 ∧ e ≤ 15 := by
  unfold encodeScaled at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, hc.2.1, hc.2.2.1, hc.2.2.2⟩
  · simp at h

theorem encodeScaled_signed_of_some (e : Nat) (x : Int) (f : Fixed)
    (h : encodeScaled e x = some f) : f.signed = x := by
  unfold encodeScaled at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    subst h
    have hdvd : 2 ^ e ∣ x.natAbs := Nat.dvd_of_mod_eq_zero hc.1
    have hmul : x.natAbs / 2 ^ e * 2 ^ e = x.natAbs := Nat.div_mul_cancel hdvd
    unfold Fixed.signed Fixed.mag
    rw [hmul]
    by_cases hx : x < 0
    · simp [hx]
      exact (Int.eq_neg_natAbs_of_nonpos (by omega)).symm
    · simp [hx]
      exact Int.natAbs_of_nonneg (by omega)
  · simp at h

/-- If the rounded value is a multiple of `2 ^ e` with an 11-bit quotient,
`encodeScaled` succeeds and preserves the value. -/
theorem encodeScaled_signed (e : Nat) (x : Int)
    (hdiv : ((2 ^ e : Nat) : Int) ∣ x)
    (hge : 1024 ≤ x.natAbs / 2 ^ e) (hle : x.natAbs / 2 ^ e ≤ 2047)
    (he : e ≤ 15) :
    ∃ f, encodeScaled e x = some f ∧ f.signed = x := by
  have hnat : 2 ^ e ∣ x.natAbs := by
    rcases hdiv with ⟨k, hk⟩
    refine ⟨k.natAbs, ?_⟩
    rw [hk, Int.natAbs_mul]
    simp
  have hmod : x.natAbs % 2 ^ e = 0 := Nat.mod_eq_zero_of_dvd hnat
  refine ⟨{ sign := x < 0, mant := x.natAbs / 2 ^ e, exp := e }, ?_, ?_⟩
  · unfold encodeScaled
    rw [ite_eq_left ⟨hmod, hge, hle, he⟩]
  · exact encodeScaled_signed_of_some e x _ (by
      unfold encodeScaled
      rw [ite_eq_left ⟨hmod, hge, hle, he⟩])

/-- Zero is not encodable in the decoded normal fragment. -/
theorem encodeScaled_zero (e : Nat) : encodeScaled e 0 = none := by
  unfold encodeScaled
  rw [ite_eq_right]
  simp

/-! ## The addition path and no double rounding -/

/-- Restricted addition path: decode both words, add the exact scaled values,
round once to the destination grid, and encode the rounded result. -/
def fp16AddPath (e0 : Nat) (wa wb : Fp16) : Option Fp16 :=
  match decode wa, decode wb with
  | some fa, some fb =>
      match encodeScaled e0 (roundEven (2 ^ e0) (fa.signed + fb.signed)) with
      | some f => some (encodeFixed f)
      | none => none
  | _, _ => none

/-- The path computes the encoded rounded sum. -/
theorem fp16AddPath_eq_encode
    (e0 : Nat) (wa wb : Fp16) (fa fb f : Fixed) (w : Fp16)
    (ha : decode wa = some fa) (hb : decode wb = some fb)
    (henc : encodeScaled e0 (roundEven (2 ^ e0) (fa.signed + fb.signed)) = some f)
    (hbits : encodeFixed f = w) :
    fp16AddPath e0 wa wb = some w := by
  unfold fp16AddPath
  rw [ha, hb]
  simp [henc, hbits]

/-- One rounding, not two: the encoded path decodes to the single rounded sum,
and re-rounding that value is the identity. -/
theorem fp16_add_no_double_rounding
    (e0 : Nat) (wa wb : Fp16) (fa fb f : Fixed) (w : Fp16)
    (ha : decode wa = some fa) (hb : decode wb = some fb)
    (henc : encodeScaled e0 (roundEven (2 ^ e0) (fa.signed + fb.signed)) = some f)
    (hbits : encodeFixed f = w) :
    fp16AddPath e0 wa wb = some w ∧
      decode w = some f ∧
      f.signed = roundEven (2 ^ e0) (fa.signed + fb.signed) ∧
      roundEven (2 ^ e0) f.signed = f.signed := by
  obtain ⟨hmant, hexp, hmge, hmle, hle⟩ := encodeScaled_spec e0 _ f henc
  have hm : 1024 ≤ f.mant := hmge
  have hm2 : f.mant ≤ 2047 := hmle
  have he : f.exp + 15 ≤ 30 := by rw [hexp]; omega
  have hval : f.signed = roundEven (2 ^ e0) (fa.signed + fb.signed) :=
    encodeScaled_signed_of_some e0 _ f henc
  have hdec : decode w = some f := by
    rw [← hbits]
    exact decode_encodeFixed f hm hm2 he
  have hpath : fp16AddPath e0 wa wb = some w :=
    fp16AddPath_eq_encode e0 wa wb fa fb f w ha hb henc hbits
  refine ⟨hpath, hdec, hval, ?_⟩
  rw [hval]
  exact roundEven_idem (2 ^ e0) (Nat.two_pow_pos e0) _

/-! ## Sign, zero, subnormal and overflow edges -/

/-- Exact cancellation rounds to zero. -/
theorem fp16_add_zero_cancellation (q : Nat) (x : Int) :
    roundEven q (x + -x) = 0 := by
  have h : x + -x = 0 := by omega
  rw [h, roundEven_zero]

/-- The rounded zero of an exact cancellation has no encoded normal word. -/
theorem fp16_add_zero_encode_none (e : Nat) (x : Int) :
    encodeScaled e (x + -x) = none := by
  have h : x + -x = 0 := by omega
  rw [h, encodeScaled_zero]

/-- Zero itself is outside `decode`'s finite normal fragment. -/
theorem decode_zero_none : decode (0x0000 : Fp16) = none := by decide

/-- Negative zero is outside the fragment as well; sign is handled on values,
not on a signed-zero bit. -/
theorem decode_neg_zero_none : decode (0x8000 : Fp16) = none := by decide

/-- The smallest positive subnormal is outside `decode`'s fragment. -/
theorem decode_subnormal_none : decode (0x0001 : Fp16) = none := by decide

/-- Positive infinity is outside `decode`'s fragment. -/
theorem decode_inf_none : decode (0x7C00 : Fp16) = none := by decide

/-- A NaN with a nonzero payload is outside `decode`'s fragment; payloads are
not modeled by this addition path. -/
theorem decode_nan_none : decode (0x7E00 : Fp16) = none := by decide

/-- The largest finite magnitude with a finite exponent field. -/
theorem Fixed.mag_le_max (f : Fixed) (hm : f.mant ≤ 2047) (he : f.exp + 15 ≤ 30) :
    f.mag ≤ 2047 * 2 ^ 15 := by
  have hexp : f.exp ≤ 15 := by omega
  unfold Fixed.mag
  calc
    f.mant * 2 ^ f.exp ≤ 2047 * 2 ^ f.exp := Nat.mul_le_mul_right _ hm
    _ ≤ 2047 * 2 ^ 15 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 0 < 2) hexp)

/-- The exact sum `65504 + 65504` is `4094 * 2 ^ 15` in scaled units, which no
finite normal `Fixed` with exponent field at most 30 represents. Overflow to
infinity is therefore outside this model rather than encoded. -/
theorem fp16_add_overflow_not_representable :
    ¬ ∃ f : Fixed, f.mant ≤ 2047 ∧ f.exp + 15 ≤ 30 ∧ f.mag = 4094 * 2 ^ 15 := by
  rintro ⟨f, hm, he, hmag⟩
  have hbound := Fixed.mag_le_max f hm he
  rw [hmag] at hbound
  have hpow : 2 ^ 15 = 32768 := by decide
  rw [hpow] at hbound
  omega

/-- The naive nested-rounding identity is false even for nested grids. -/
theorem double_rounding_counterexample :
    roundEven (8 : Nat) (roundEven (2 : Nat) 5) ≠ roundEven (8 : Nat) 5 := by decide

example : roundEven (2 : Nat) 5 = 4 := by decide
example : roundEven (8 : Nat) 5 = 8 := by decide
example : roundEven (8 : Nat) 4 = 0 := by decide

end IntelGpu
