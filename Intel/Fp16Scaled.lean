-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Fp16Bits

@[expose] public section

/-!
# Every finite fp16 has an integer value in units of `2 ^ -24`

Stage 43 decodes the fragment with exponent at least the bias; everything
smaller came back as `none`. This module gives *every* finite word a concrete
value by fixing a global scale: a 16-bit value is an integer multiple of
`2 ^ -24`, so `scaled w` is that multiple.

- normal (`expField ≠ 0`): `(1024 + mantissa) * 2 ^ (expField - 1)`
- subnormal (`expField = 0`): `mantissa`

So subnormals and fractional values are now numbers, not classes. What is still
outside is NaN and infinity, which have no finite value — that is what
`Intel/Fp16Value.lean` models as classes.

The relation between this scale and the `Fixed` scale used by the numeric
layer (`scaled = mag * 2 ^ 14` on the decoded fragment) is stated in the
module comment; I did not prove it here because elaborating through `decode`
timed out and I would rather ship the verified vectors than a half-proved
gluing lemma.

Known vectors are checked with `decide`, which is what catches an off-by-one in
the bias.
-/

namespace IntelGpu

/-- The value of a finite fp16 word in units of `2 ^ -24`. -/
def scaled (w : Fp16) : Nat :=
  if expField w = 0 then mantField w
  else (1024 + mantField w) * 2 ^ (expField w - 1)

theorem scaled_subnormal (w : Fp16) (h : expField w = 0) :
    scaled w = mantField w := by
  simp [scaled, h]

theorem scaled_normal (w : Fp16) (h : expField w ≠ 0) :
    scaled w = (1024 + mantField w) * 2 ^ (expField w - 1) := by
  simp [scaled, h]

/-- 1.0 is `0x3C00`. -/
example : scaled (0x3C00 : Fp16) = 2 ^ 24 := by decide

/-- 2.0 is `0x4000`. -/
example : scaled (0x4000 : Fp16) = 2 ^ 25 := by decide

/-- 0.5 is `0x3800` — below the bias, so stage 43 returns `none` for it. -/
example : scaled (0x3800 : Fp16) = 2 ^ 23 := by decide
example : decode (0x3800 : Fp16) = none := by decide

/-- The largest finite value, `65504`, is `0x7BFF`. -/
example : scaled (0x7BFF : Fp16) = 65504 * 2 ^ 24 := by decide

/-- The smallest positive normal, `2 ^ -14`, is `0x0400`. -/
example : scaled (0x0400 : Fp16) = 2 ^ 10 := by decide

/-- The smallest positive subnormal, `2 ^ -24`, is `0x0001`. -/
example : scaled (0x0001 : Fp16) = 1 := by decide

end IntelGpu
