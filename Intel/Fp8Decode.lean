-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.RealDpas

@[expose] public section

/-!
# fp8 E4M3 elements for the coded FMHA atom

`Intel.RealDpas` decodes the compiled FMHA `dpas.8x8` as the 8x8x32 fp8 atom
`fmhaFp8Atom` and defines its word-level operation `fmhaAtom`. This module
supplies the missing element path: an exact E4M3 decode and a wrapper that feeds
decoded A/B elements to the existing atom.

## Value model

An fp8 byte is laid out as one sign bit, a four-bit biased exponent, and a
three-bit mantissa. The bias is 7. Finite values are represented exactly as
signed fixed-point integers in units of `2^-9`:

- subnormal (`expField = 0`): significand `mantField`, quantum `2^-9`;
- normal (`1 <= expField <= 15`): significand `8 + mantField`, and
  `value = (8 + mantField) * 2^(expField - 10)`;
- zero has `expField = 0` and `mantField = 0`; both signs are retained.

`E4M3Value.scaled` is the exact value multiplied by `2^9`. Thus every finite
E4M3 value is an integer in that scale. `E4M3Value.toWord` embeds that signed
integer in a 32-bit word with `BitVec.ofInt`.

## NaN and infinity assumptions

This is the no-infinity E4M3FN model, as used at value level here:

- the all-ones exponent is **not** an infinity;
- `S.1111.111` is NaN, while exponent-15 patterns with mantissa below seven
  remain finite (`0x7E` is the largest finite value, 448);
- there is no saturation to infinity and no infinity value in the decode.

A system that instead reserves every exponent-15 pattern for NaN is not modeled
by `decodeE4M3`. This module makes no hardware-conformance claim: it is an exact
value-level decode, not a claim about a particular IGC or Xe fp8 conversion.

## Word scale

A decoded operand is an integer multiple of `2^-9`, so a DPAS product of two
decoded operands is in units of `2^-18`. Accumulator inputs to `fmhaAtomFp8`
must be supplied in the same `2^-18` scale. Word arithmetic is modulo `2^32`;
the concrete all-ones theorems below stay inside that range.

## Main results

- `decodeE4M3`, `encodeE4M3`: decode and its finite round-trip.
- `decodeE4M3_lt`: finite decoded magnitudes are below `2^18` in the `2^-9`
  scale, i.e. below 512 as values.
- `fmhaAtomFp8_eq_fmhaAtom`: under explicit per-element success hypotheses,
  the fp8 wrapper is exactly `fmhaAtom` over the decoded words.
- `fmhaAtomFp8_ones_zero`/`fmhaAtomFp8_ones_acc`: concrete 8x8x32 value
  theorems at every accumulator position.
-/

namespace IntelGpu

/-- An 8-bit fp8 word. -/
abbrev Fp8 := BitVec 8

/-- The sign bit of an fp8 word. -/
def fp8SignBit (w : Fp8) : Bool := (w >>> 7) != 0

/-- The four-bit biased exponent field. -/
def fp8ExpField (w : Fp8) : Nat := ((w >>> 3) &&& 0xF).toNat

/-- The three-bit mantissa field. -/
def fp8MantField (w : Fp8) : Nat := (w &&& 0x7).toNat

/-- A decoded E4M3 value: either the sole NaN class or finite fields. -/
inductive E4M3Value where
  | nan
  | fin (sign : Bool) (expField : Nat) (mantField : Nat)
  deriving Repr, DecidableEq

/-- Decode an fp8 word. The all-ones exponent with all-ones mantissa is NaN;
there is no infinity. -/
def decodeE4M3 (w : Fp8) : E4M3Value :=
  if fp8ExpField w = 15 ∧ fp8MantField w = 7 then .nan
  else .fin (fp8SignBit w) (fp8ExpField w) (fp8MantField w)

/-- The exact magnitude of a finite value in units of `2^-9`; NaN maps to zero. -/
def E4M3Value.magScaled : E4M3Value → Nat
  | .nan => 0
  | .fin _ e m =>
      (if e = 0 then m else 8 + m) * 2 ^ (if e = 0 then 0 else e - 1)

/-- The exact signed value in units of `2^-9`; NaN maps to zero. -/
def E4M3Value.scaled : E4M3Value → Int
  | .nan => 0
  | .fin s e m =>
      let mag : Int :=
        ((if e = 0 then m else 8 + m) * 2 ^ (if e = 0 then 0 else e - 1))
      if s then -mag else mag

/-- Embed a decoded fixed-point value as a signed 32-bit word. -/
def E4M3Value.toWord : E4M3Value → Word
  | .nan => 0
  | v => BitVec.ofInt 32 v.scaled

/-- Pack an E4M3 value's fields into a byte. -/
def packE4M3 (s : Bool) (e m : Nat) : Fp8 :=
  BitVec.ofNat 8 ((if s then 128 else 0) + e * 8 + m)

/-- Encode a decoded value, rejecting NaN and out-of-field fields. -/
def encodeE4M3 : E4M3Value → Option Fp8
  | .nan => none
  | .fin s e m =>
      if e < 16 ∧ m < 8 ∧ ¬ (e = 15 ∧ m = 7) then
        some (packE4M3 s e m)
      else none

/-- NaN encodes to no word. -/
theorem encodeE4M3_nan : encodeE4M3 .nan = none := rfl

/-- A finite decode exposes the original fields. -/
theorem decodeE4M3_fin (w : Fp8)
    (h : ¬ (fp8ExpField w = 15 ∧ fp8MantField w = 7)) :
    decodeE4M3 w = .fin (fp8SignBit w) (fp8ExpField w) (fp8MantField w) := by
  simp [decodeE4M3, h]

/-- The all-ones exponent with all-ones mantissa is the NaN case. -/
theorem decodeE4M3_all_ones_nan (w : Fp8)
    (he : fp8ExpField w = 15) (hm : fp8MantField w = 7) :
    decodeE4M3 w = .nan := by
  simp [decodeE4M3, he, hm]

/-- Both fp8 signs of the all-ones NaN pattern decode to NaN. -/
theorem decodeE4M3_nan_7f : decodeE4M3 (0x7F : Fp8) = .nan := by
  decide

theorem decodeE4M3_nan_ff : decodeE4M3 (0xFF : Fp8) = .nan := by
  decide

/-- Every non-NaN word round-trips through decode and encode. -/
theorem encodeE4M3_decodeE4M3 (w : Fp8) (h : decodeE4M3 w ≠ .nan) :
    encodeE4M3 (decodeE4M3 w) = some w := by
  decide +revert

/-- Finite decoded magnitudes are below `2^18` in the `2^-9` scale. -/
theorem decodeE4M3_lt (w : Fp8) (h : decodeE4M3 w ≠ .nan) :
    (decodeE4M3 w).magScaled < 2 ^ 18 := by
  decide +revert

/-- The signed fixed-point reading has the same finite bound. -/
theorem decodeE4M3_abs_lt (w : Fp8) (h : decodeE4M3 w ≠ .nan) :
    Int.natAbs (decodeE4M3 w).scaled < 2 ^ 18 := by
  decide +revert

/-- `1.0` is `0x38`: exponent field 7, mantissa zero, scaled value 512. -/
theorem decodeE4M3_one :
    decodeE4M3 (0x38 : Fp8) = .fin false 7 0 ∧
      (decodeE4M3 (0x38 : Fp8)).scaled = 512 := by
  decide

/-- `1.5` is `0x3C`: exponent field 7, mantissa 4, scaled value 768. -/
theorem decodeE4M3_one_point_five :
    decodeE4M3 (0x3C : Fp8) = .fin false 7 4 ∧
      (decodeE4M3 (0x3C : Fp8)).scaled = 768 := by
  decide

/-- `2.0` is `0x40`: exponent field 8, mantissa zero, scaled value 1024. -/
theorem decodeE4M3_two :
    decodeE4M3 (0x40 : Fp8) = .fin false 8 0 ∧
      (decodeE4M3 (0x40 : Fp8)).scaled = 1024 := by
  decide

/-- `0.5` is `0x30`: exponent field 6, mantissa zero, scaled value 256. -/
theorem decodeE4M3_half :
    decodeE4M3 (0x30 : Fp8) = .fin false 6 0 ∧
      (decodeE4M3 (0x30 : Fp8)).scaled = 256 := by
  decide

/-- Positive zero is `0x00`, with sign `false` and scaled value zero. -/
theorem decodeE4M3_zero :
    decodeE4M3 (0x00 : Fp8) = .fin false 0 0 ∧
      (decodeE4M3 (0x00 : Fp8)).scaled = 0 := by
  decide

/-- Negative zero is `0x80`: the sign is retained even though the value is zero. -/
theorem decodeE4M3_neg_zero :
    decodeE4M3 (0x80 : Fp8) = .fin true 0 0 ∧
      (decodeE4M3 (0x80 : Fp8)).scaled = 0 := by
  decide

/-- The smallest positive subnormal is `0x01`, one `2^-9` quantum. -/
theorem decodeE4M3_min_subnormal :
    decodeE4M3 (0x01 : Fp8) = .fin false 0 1 ∧
      (decodeE4M3 (0x01 : Fp8)).magScaled = 1 := by
  decide

/-- `0x7E` is the largest finite E4M3FN value: 448, scaled to 229376. -/
theorem decodeE4M3_max_finite :
    decodeE4M3 (0x7E : Fp8) = .fin false 15 6 ∧
      (decodeE4M3 (0x7E : Fp8)).scaled = 229376 := by
  decide

/-- Decode a word to an optional signed fixed-point word; NaN has no value. -/
def fp8Word? (w : Fp8) : Option Word :=
  match decodeE4M3 w with
  | .nan => none
  | v => some v.toWord

/-- Total decoding used by the atom: a failed (NaN) decode contributes zero.
The equality theorem below rules out this case on the atom's read window. -/
def fp8Word (w : Fp8) : Word := (fp8Word? w).getD 0

/-- `1.0` feeds the word-level atom as 512, its `2^9`-scaled value. -/
theorem fp8Word_one : fp8Word (0x38 : Fp8) = (512 : Word) := by
  decide

/-- The NaN sentinel contributes zero in the total wrapper. -/
theorem fp8Word_nan : fp8Word (0x7F : Fp8) = 0 := by
  decide

/-- Decode A/B elements and apply the existing 8x8x32 `fmhaAtom`. A and B are
indexed by global row/column and depth; `C` is the incoming accumulator. -/
def fmhaAtomFp8 (A B : Nat → Nat → Fp8) (C : Nat → Nat → Word)
    (i j : Nat) : Nat → Nat → Word :=
  fmhaAtom (fun m k => fp8Word (A m k)) (fun k n => fp8Word (B k n)) C i j

/-- The wrapper is one depth-32 `dpas` over decoded A/B slices. -/
theorem fmhaAtomFp8_eq_dpas (A B : Nat → Nat → Fp8) (C : Nat → Nat → Word)
    (i j : Nat) :
    fmhaAtomFp8 A B C i j =
      dpas 32 (fun k m => fp8Word (A (i + m) k))
        (fun k n => fp8Word (B k (j + n))) (fun m n => C (i + m) (j + n)) := by
  rfl

/-- If every A/B element read by the atom decodes successfully, the wrapper is
exactly the existing `fmhaAtom` over the decoded fixed-point words. -/
theorem fmhaAtomFp8_eq_fmhaAtom
    (A B : Nat → Nat → Fp8) (C : Nat → Nat → Word) (i j : Nat)
    (hA : ∀ m k, decodeE4M3 (A (i + m) k) ≠ .nan)
    (hB : ∀ k n, decodeE4M3 (B k (j + n)) ≠ .nan) :
    fmhaAtomFp8 A B C i j =
      fmhaAtom (fun m k => (decodeE4M3 (A m k)).toWord)
        (fun k n => (decodeE4M3 (B k n)).toWord) C i j := by
  have hAw : ∀ m k, fp8Word? (A (i + m) k) =
      some ((decodeE4M3 (A (i + m) k)).toWord) := by
    intro m k
    cases hd : decodeE4M3 (A (i + m) k) with
    | nan => exact absurd hd (hA m k)
    | fin s e m' => simp [fp8Word?, hd]
  have hBw : ∀ k n, fp8Word? (B k (j + n)) =
      some ((decodeE4M3 (B k (j + n))).toWord) := by
    intro k n
    cases hd : decodeE4M3 (B k (j + n)) with
    | nan => exact absurd hd (hB k n)
    | fin s e n' => simp [fp8Word?, hd]
  funext m n
  unfold fmhaAtomFp8 fmhaAtom fp8Word
  simp only [hAw, hBw, Option.getD_some]

/-- All-ones A/B with a zero accumulator: every one of the 64 output positions
gets the 32-term sum `32 * 512 * 512` in the `2^-9`-scaled word model. -/
theorem fmhaAtomFp8_ones_zero (i j m n : Nat) :
    fmhaAtomFp8 (fun _ _ => 0x38) (fun _ _ => 0x38) (fun _ _ => 0) i j m n =
      (32 * 512 * 512 : Word) := by
  unfold fmhaAtomFp8
  rw [fmhaAtom_correct]
  simp [dotMatFrom, fp8Word, fp8Word?, decodeE4M3, E4M3Value.toWord,
    E4M3Value.scaled]
  decide

/-- The raw byte `0x01` is one `2^-9` quantum. With every A/B byte `0x01`, each
product is one scaled unit, so the 32-term sum is exactly 32. -/
theorem fmhaAtomFp8_unit_ones_zero (i j m n : Nat) :
    fmhaAtomFp8 (fun _ _ => 0x01) (fun _ _ => 0x01) (fun _ _ => 0) i j m n =
      (32 : Word) := by
  unfold fmhaAtomFp8
  rw [fmhaAtom_correct]
  simp [dotMatFrom, fp8Word, fp8Word?, decodeE4M3, E4M3Value.toWord,
    E4M3Value.scaled]
  decide

/-- The same 32-term fp8 sum accumulates onto a nonzero C value at every
position. -/
theorem fmhaAtomFp8_ones_acc (i j m n : Nat) :
    fmhaAtomFp8 (fun _ _ => 0x38) (fun _ _ => 0x38) (fun _ _ => 5) i j m n =
      (5 : Word) + 32 * 512 * 512 := by
  unfold fmhaAtomFp8
  rw [fmhaAtom_correct]
  simp [dotMatFrom, fp8Word, fp8Word?, decodeE4M3, E4M3Value.toWord,
    E4M3Value.scaled]
  decide

end IntelGpu
