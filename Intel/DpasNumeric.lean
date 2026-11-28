-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Bf16Dpas

@[expose] public section

/-!
# The DPAS slab as an exact integer dot product

`dpasSlab` is a `Word` (mod `2^32`) fold. This module proves that whenever the
exact natural-number dot product fits below `2^32`, the slab's `toNat` is
exactly that dot product. The same is done for the BF16 instantiation
`tlaSlabBf16`, including the initial accumulator.

This is the no-wraparound regime of the algebraic model; it does not model
FP32 rounding of the products.
-/

namespace IntelGpu

/-- The exact natural-number depth dot product of two tiles. -/
def dotNat : Nat → (Nat → Nat → Word) → (Nat → Nat → Word) → Nat → Nat → Nat
  | 0, _, _, _, _ => 0
  | d + 1, A, B, m, n =>
      (A 0 m).toNat * (B 0 n).toNat +
        dotNat d (fun k m' => A (k + 1) m') (fun k n' => B (k + 1) n') m n

theorem dpasSlab_toNat (d : Nat) (A B : Nat → Nat → Word) (m n : Nat)
    (h : dotNat d A B m n < 2 ^ 32) :
    (dpasSlab d A B m n).toNat = dotNat d A B m n := by
  induction d generalizing A B with
  | zero => rfl
  | succ d ih =>
      have hprod : (A 0 m).toNat * (B 0 n).toNat < 2 ^ 32 := by
        simp only [dotNat] at h
        omega
      have hrest : dotNat d (fun k m' => A (k + 1) m') (fun k n' => B (k + 1) n') m n < 2 ^ 32 := by
        simp only [dotNat] at h
        omega
      have hsum : (A 0 m).toNat * (B 0 n).toNat +
          dotNat d (fun k m' => A (k + 1) m') (fun k n' => B (k + 1) n') m n < 2 ^ 32 := by
        simp only [dotNat] at h
        exact h
      simp only [dpasSlab, dotNat]
      rw [BitVec.toNat_add, BitVec.toNat_mul]
      rw [ih (fun k m' => A (k + 1) m') (fun k n' => B (k + 1) n') hrest]
      rw [Nat.mod_eq_of_lt hprod, Nat.mod_eq_of_lt hsum]

/-- The BF16 slab's `toNat` is the exact integer dot product of the decoded
values plus the initial accumulator, when it fits below `2^32`. -/
theorem tlaSlabBf16_toNat (A B : Nat → Nat → Bf16) (C : Nat → Nat → Word)
    (m n : Nat)
    (h : (C m n).toNat +
      dotNat 16 (fun m k => bf16Word (A m k)) (fun k n => bf16Word (B k n)) m n < 2 ^ 32) :
    (tlaSlabBf16 A B C m n).toNat =
      (C m n).toNat +
        dotNat 16 (fun m k => bf16Word (A m k)) (fun k n => bf16Word (B k n)) m n := by
  have hdot : dotNat 16 (fun m k => bf16Word (A m k)) (fun k n => bf16Word (B k n)) m n < 2 ^ 32 := by
    omega
  have hd := dpasSlab_toNat 16 (fun m k => bf16Word (A m k))
    (fun k n => bf16Word (B k n)) m n hdot
  simp only [tlaSlabBf16]
  rw [BitVec.toNat_add, hd, Nat.mod_eq_of_lt h]

/-- The all-ones BF16 slab is exactly sixteen `1.0 * 1.0` products: `262144`
on the `2^-7` grid. -/
theorem tlaSlabBf16_ones_nat :
    (tlaSlabBf16 (fun _ _ => 0x3F80) (fun _ _ => 0x3F80) (fun _ _ => 0) 0 0).toNat =
      262144 := by
  rw [tlaSlabBf16_toNat]
  · decide
  · decide

end IntelGpu
