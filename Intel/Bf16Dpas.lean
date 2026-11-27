-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Bf16Decode
public import Intel.IeeeFp16Add

@[expose] public section

/-!
# BF16 sources in the DPAS slab model

`Intel.Bf16Decode` decodes a BF16 word to the `Fixed` value model.
`Intel.IeeeFp16Add` exposes the signed integer `Fixed.signed` on the `2^-7`
grid used by BF16. This module embeds that signed integer into a `Word` and
uses it as the numeric A/B value of the existing `dpasSlab 16` model.

`tlaSlabBf16` is the BF16 instantiation of the DPAS slab. Exact examples
(`1.0 * 1.0` and `1.0 * 2.0` over depth 16) check the decode-to-word path.
The embedding is modulo `2^32`; it is the same algebraic word model used by
the rest of the DPAS development, not a floating-point rounding model.
-/

namespace IntelGpu

/-- The signed integer value of a decodable BF16 word. -/
def bf16Signed (w : Bf16) : Option Int := (decodeBf16 w).map Fixed.signed

/-- The BF16 value as a 32-bit word, or `none` outside the decoded fragment. -/
def bf16Word? (w : Bf16) : Option Word := (bf16Signed w).map (BitVec.ofInt 32)

/-- The BF16 value as a 32-bit word, with a zero fallback outside the
fragment. -/
def bf16Word (w : Bf16) : Word := (bf16Word? w).getD 0

theorem bf16Word_one : bf16Word 0x3F80 = 128 := by decide

theorem bf16Word_neg_one : bf16Word 0xBF80 = BitVec.ofInt 32 (-128) := by decide

theorem bf16Word_two : bf16Word 0x4000 = 256 := by decide

theorem bf16Word_four : bf16Word 0x4080 = 512 := by decide

/-- A BF16 A/B tile in the DPAS slab model. -/
def tlaSlabBf16 (A B : Nat → Nat → Bf16) (C : Nat → Nat → Word)
    (m n : Nat) : Word :=
  C m n + dpasSlab 16 (fun m k => bf16Word (A m k))
    (fun k n => bf16Word (B k n)) m n

theorem tlaSlabBf16_eq (A B : Nat → Nat → Bf16) (C : Nat → Nat → Word)
    (m n : Nat) :
    tlaSlabBf16 A B C m n =
      C m n + dpasSlab 16 (fun m k => bf16Word (A m k))
        (fun k n => bf16Word (B k n)) m n := rfl

/-- Sixteen products of `1.0 * 1.0` on the `2^-7` grid. -/
theorem tlaSlabBf16_ones :
    tlaSlabBf16 (fun _ _ => 0x3F80) (fun _ _ => 0x3F80) (fun _ _ => 0) 0 0 =
      262144 := by
  decide

/-- Sixteen products of `1.0 * 2.0` on the `2^-7` grid. -/
theorem tlaSlabBf16_one_two :
    tlaSlabBf16 (fun _ _ => 0x3F80) (fun _ _ => 0x4000) (fun _ _ => 0) 0 0 =
      524288 := by
  decide

/-- An initial accumulator is added to the slab. -/
theorem tlaSlabBf16_acc :
    tlaSlabBf16 (fun _ _ => 0x3F80) (fun _ _ => 0x3F80)
      (fun _ _ => 7) 0 0 = 262151 := by
  decide

end IntelGpu
