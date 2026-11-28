-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Fp16Shape

@[expose] public section

/-!
# A bit-level fp16 encoding

Stage 38 models a value as `sign * mantissa * 2 ^ exponent` and takes that
shape on faith. This module grounds it in the actual 16-bit layout: sign bit,
5-bit biased exponent, 10-bit mantissa.

`decode` returns `none` for everything outside the fragment the development
models — NaN, infinities, subnormals, and values whose biased exponent is below
the bias (fractional values). Everything else decodes to a `Fixed` with the
implicit leading significand bit restored.

Scale note: `Fixed.mag` is the significand times `2 ^ exp`, i.e. the value in
units of `2 ^ -10`. A common scale does not affect exactness, so the grid
results of stages 34 and 38 apply unchanged.

- `signBit`, `expField`, `mantField`: the three fields.
- `decode`: `Option Fixed`, `none` for the out-of-scope classes.
- `decode_some`: what a successful decode tells you about the fields.
- `fp16_bits_exact`: decoded fp16 operands on a shared grid accumulate exactly.
-/

namespace IntelGpu

/-- The fp16 bit pattern. -/
abbrev Fp16 := BitVec 16

def signBit (w : Fp16) : Bool := (w >>> 15) != 0

def expField (w : Fp16) : Nat := ((w >>> 10) &&& 0x1F).toNat

def mantField (w : Fp16) : Nat := (w &&& 0x3FF).toNat

/-- Decode a 16-bit word into a `Fixed` value, or `none` when the word is
outside the modeled fragment. -/
def decode (w : Fp16) : Option Fixed :=
  if expField w = 31 then none
  else if expField w = 0 then none
  else if expField w < 15 then none
  else
    some { sign := signBit w, mant := 1024 + mantField w, exp := expField w - 15 }

/-- A successful decode pins down the fields. -/
theorem decode_some (w : Fp16) (v : Fixed) (h : decode w = some v) :
    v.mant = 1024 + mantField w ∧ v.exp = expField w - 15 ∧ v.sign = signBit w := by
  unfold decode at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Option.some.injEq] at h
        subst h
        exact ⟨rfl, rfl, rfl⟩

/-- The fragment is finite: a decoded word is never NaN or infinite. -/
theorem decode_exp_ne (w : Fp16) (v : Fixed) (h : decode w = some v) :
    expField w ≠ 31 := by
  intro hc
  simp [decode, hc] at h

/-- Decoded fp16 operands on a shared grid accumulate exactly. -/
theorem fp16_bits_exact (e0 : Nat) (n : Nat) (acc : Fixed) (a b : Nat → Fp16)
    (fa fb : Nat → Fixed)
    (ha : ∀ k, decode (a k) = some (fa k)) (hb : ∀ k, decode (b k) = some (fb k))
    (hacc : e0 ≤ acc.exp)
    (hea : ∀ k, e0 ≤ expField (a k) - 15) (heb : ∀ k, e0 ≤ expField (b k) - 15) :
    maccDot (stepEven (2 ^ e0))
        (fun k => ((fa k).mag : Int)) (fun k => ((fb k).mag : Int)) ((acc.mag : Int)) n
      = accDot (fun k => ((fa k).mag : Int)) (fun k => ((fb k).mag : Int))
          ((acc.mag : Int)) n :=
  fp16_grid_exact_of_exp e0 n acc fa fb hacc
    (fun k => by rw [(decode_some (a k) (fa k) (ha k)).2.1]; exact hea k)
    (fun k => by rw [(decode_some (b k) (fb k) (hb k)).2.1]; exact heb k)

/-- `1.0` in fp16 is `0x3C00`: exponent field 15, mantissa 0. -/
example : expField (0x3C00 : Fp16) = 15 := by decide
example : mantField (0x3C00 : Fp16) = 0 := by decide
example : decode (0x3C00 : Fp16) = some { sign := false, mant := 1024, exp := 0 } := by decide

/-- `0x7C00` is `+inf`, which is outside the fragment. -/
example : decode (0x7C00 : Fp16) = none := by decide

/-- `0x0001` is a subnormal, also outside the fragment. -/
example : decode (0x0001 : Fp16) = none := by decide

end IntelGpu
