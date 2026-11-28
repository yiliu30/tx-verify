-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Fp16Scaled

@[expose] public section

/-!
# The bit scale and the numeric scale agree

Stage 43 decodes the fragment with exponent at least the bias into a `Fixed`;
stage 46 gives every finite word a value in units of `2 ^ -24`. This module
proves the two agree: on the decoded fragment

    scaled w = v.mant * 2 ^ v.exp * 2 ^ 14

The `2 ^ 14` is the whole difference between the scales, and having it as a
theorem means exactness results proved for `Fixed` values transfer to words
decoded from bits without redoing the arithmetic.

The field conditions (`expField w ≠ 0`, `15 ≤ expField w`) are hypotheses rather
than derived: deriving them from `decode w = some v` needs the decoder's branch
structure, which is where two earlier attempts ran into elaboration problems.
They are exactly what `decode`'s branches guarantee, and the module says so
instead of pretending they are free.
-/

namespace IntelGpu

theorem pow_shift (e : Nat) (h : 15 ≤ e) :
    2 ^ (e - 1) = 2 ^ (e - 15) * 2 ^ 14 := by
  rw [← Nat.pow_add]
  congr 1
  omega

theorem scaled_eq_mag (w : Fp16) (v : Fixed) (h : decode w = some v)
    (hne : expField w ≠ 0) (hge : 15 ≤ expField w) :
    scaled w = v.mant * 2 ^ v.exp * 2 ^ 14 := by
  obtain ⟨hmant, hexp, _⟩ := decode_some w v h
  rw [scaled_normal w hne, hmant, hexp, pow_shift (expField w) hge, Nat.mul_assoc]

/-- The same fact at the level the numeric layer uses: a decoded word's scaled
value is the `Fixed` magnitude times `2 ^ 14`, so the grid results of stages 34
and 38 apply to decoded operands. -/
theorem scaled_eq_mag' (w : Fp16) (v : Fixed) (h : decode w = some v)
    (hne : expField w ≠ 0) (hge : 15 ≤ expField w) :
    scaled w = v.mag * 2 ^ 14 := by
  rw [scaled_eq_mag w v h hne hge]
  rfl

/-- `1.0`: both readings agree, `2 ^ 24 = 1024 * 2 ^ 0 * 2 ^ 14`. -/
example : scaled (0x3C00 : Fp16) = 1024 * 2 ^ 0 * 2 ^ 14 := by decide

end IntelGpu
