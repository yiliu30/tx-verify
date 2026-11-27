-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Bf16Dpas
public meta import Std.Tactic.BVDecide.Reflect

@[expose] public section

/-!
# Packed BF16 register halves

A 32-bit DPAS source register holds two BF16 values. `Intel.Bf16Decode` and
`Intel.Bf16Dpas` model the values; this module adds the bit-level packing:
`bf16Lo` and `bf16Hi` extract the two halves, `bf16Pair` packs them, and the
round-trip theorems show the two views are inverse. `tlaSlabBf16Packed` is the
slab read directly from packed 32-bit words, and agrees definitionally with
the value-level BF16 slab on the extracted halves.
-/

namespace IntelGpu

/-- The low BF16 half of a packed 32-bit register. -/
def bf16Lo (w : Word) : Bf16 := (w &&& 0xFFFF).truncate 16

/-- The high BF16 half of a packed 32-bit register. -/
def bf16Hi (w : Word) : Bf16 := ((w >>> 16) &&& 0xFFFF).truncate 16

theorem bf16Lo_pair (lo hi : Bf16) : bf16Lo (bf16Pair lo hi) = lo := by
  unfold bf16Lo bf16Pair
  bv_decide

theorem bf16Hi_pair (lo hi : Bf16) : bf16Hi (bf16Pair lo hi) = hi := by
  unfold bf16Hi bf16Pair
  bv_decide

theorem bf16Pair_lo_hi (w : Word) : bf16Pair (bf16Lo w) (bf16Hi w) = w := by
  unfold bf16Lo bf16Hi bf16Pair
  bv_decide

/-- A DPAS slab read directly from packed 32-bit source words. -/
def tlaSlabBf16Packed (A B : Nat → Nat → Word) (C : Nat → Nat → Word)
    (m n : Nat) : Word :=
  C m n + dpasSlab 16 (fun m k => bf16Word (bf16Lo (A m k)))
    (fun k n => bf16Word (bf16Lo (B k n))) m n

theorem tlaSlabBf16Packed_eq (A B : Nat → Nat → Word) (C : Nat → Nat → Word)
    (m n : Nat) :
    tlaSlabBf16Packed A B C m n =
      C m n + dpasSlab 16 (fun m k => bf16Word (bf16Lo (A m k)))
        (fun k n => bf16Word (bf16Lo (B k n))) m n := rfl

/-- Sixteen `1.0 * 1.0` products from packed `(1.0, 1.0)` registers. -/
theorem tlaSlabBf16Packed_ones :
    tlaSlabBf16Packed (fun _ _ => 0x3F803F80) (fun _ _ => 0x3F803F80)
      (fun _ _ => 0) 0 0 = 262144 := by
  decide

end IntelGpu
