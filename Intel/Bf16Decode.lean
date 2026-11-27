-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Fp16Shape
public import Intel.Fp16Bits
public meta import Std.Tactic.BVDecide.Reflect

@[expose] public section

/-!
# A bit-level BF16 decode

The SYCL-TLA GEMM's DPAS sources are `:bf` registers: each 32-bit register
holds two BF16 values (sign, 8-bit biased exponent, 7-bit mantissa). This
module grounds the source bits in the same `Fixed` value model used for FP16.

`decodeBf16` mirrors `Intel.Fp16Bits.decode`: it accepts finite normalized
values with a biased exponent at least the bias and rejects NaN, infinity,
subnormals and fractional values. The scale is `2^-7` (`Fixed.mag` is the
significand times `2^exp`), so the existing exact-grid results apply unchanged.

`bf16ToWord` embeds the 16-bit pattern in the high half of a 32-bit word, which
is the bit-level BF16-to-FP32 relationship.
-/

namespace IntelGpu

/-- The BF16 bit pattern. -/
abbrev Bf16 := BitVec 16

def bf16Sign (w : Bf16) : Bool := (w >>> 15) != 0

def bf16Exp (w : Bf16) : Nat := ((w >>> 7) &&& 0xFF).toNat

def bf16Mant (w : Bf16) : Nat := (w &&& 0x7F).toNat

/-- Decode a BF16 word into a `Fixed` value, or `none` outside the normalized
finite fragment. -/
def decodeBf16 (w : Bf16) : Option Fixed :=
  if bf16Exp w = 255 then none
  else if bf16Exp w = 0 then none
  else if bf16Exp w < 127 then none
  else
    some { sign := bf16Sign w, mant := 128 + bf16Mant w, exp := bf16Exp w - 127 }

/-- A successful decode pins down the fields. -/
theorem decodeBf16_some (w : Bf16) (v : Fixed) (h : decodeBf16 w = some v) :
    v.mant = 128 + bf16Mant w ∧ v.exp = bf16Exp w - 127 ∧ v.sign = bf16Sign w := by
  unfold decodeBf16 at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Option.some.injEq] at h
        subst h
        exact ⟨rfl, rfl, rfl⟩

/-- A decoded word is never NaN or infinite. -/
theorem decodeBf16_exp_ne (w : Bf16) (v : Fixed) (h : decodeBf16 w = some v) :
    bf16Exp w ≠ 255 := by
  intro hc
  simp [decodeBf16, hc] at h

/-- The BF16 bit pattern embedded in the high half of a 32-bit word. -/
def bf16ToWord (w : Bf16) : Word := (w.zeroExtend 32) <<< 16

/-- Two BF16 values packed in one 32-bit register: low half first. -/
def bf16Pair (lo hi : Bf16) : Word :=
  (lo.zeroExtend 32) ||| ((hi.zeroExtend 32) <<< 16)

theorem bf16ToWord_one : bf16ToWord 0x3F80 = 0x3F800000 := by decide

theorem bf16ToWord_neg_one : bf16ToWord 0xBF80 = 0xBF800000 := by decide

theorem bf16ToWord_two : bf16ToWord 0x4000 = 0x40000000 := by decide

theorem bf16Pair_low (lo hi : Bf16) :
    bf16Pair lo hi &&& 0xFFFF = lo.zeroExtend 32 := by
  unfold bf16Pair
  bv_decide

theorem bf16Pair_high (lo hi : Bf16) :
    (bf16Pair lo hi >>> 16) &&& 0xFFFF = hi.zeroExtend 32 := by
  unfold bf16Pair
  bv_decide

theorem decodeBf16_one : decodeBf16 0x3F80 = some ⟨false, 128, 0⟩ := by decide

theorem decodeBf16_neg_one : decodeBf16 0xBF80 = some ⟨true, 128, 0⟩ := by decide

theorem decodeBf16_two : decodeBf16 0x4000 = some ⟨false, 128, 1⟩ := by decide

theorem decodeBf16_four : decodeBf16 0x4080 = some ⟨false, 128, 2⟩ := by decide

theorem decodeBf16_nan : decodeBf16 0x7FC0 = none := by decide

theorem decodeBf16_inf : decodeBf16 0x7F80 = none := by decide

theorem decodeBf16_subnormal : decodeBf16 0x0001 = none := by decide

theorem decodeBf16_fractional : decodeBf16 0x3F00 = none := by decide

end IntelGpu
