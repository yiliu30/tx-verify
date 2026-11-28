-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.LaneStaging

@[expose] public section

/-!
# Interleaved copies

Stage 37 models staging as a block distribution: lane `l` takes a contiguous
chunk. SYCL-TLA's copy atoms interleave instead — lane `l` takes words
`l, l + L, l + 2L, ...` — which needs a copy whose *destination* is strided too.

- `copyInterleaved`: one lane's strided-to-strided copy.
- `copyInterleaved_value`: every word it writes comes from the matching offset.
- `copyInterleaved_frame`: nothing else moves.

Composing lanes into a workgroup copy, and proving that the lanes cover the
slab, is not done here — the mod-`L` coverage argument is the next step and this
module stops at the primitive.

Ledger assumption 8 is therefore discharged in part.
-/

namespace IntelGpu

/-- Copy `n` words, `stride` apart in both source and destination. -/
def copyInterleaved (dstMem srcMem : Nat → Word) (dst src stride : Nat) : Nat → Nat → Word
  | 0 => dstMem
  | n + 1 =>
      update (copyInterleaved dstMem srcMem dst src stride n)
        (dst + n * stride) (srcMem (src + n * stride))

theorem copyInterleaved_value (dstMem srcMem : Nat → Word) (dst src stride : Nat)
    (hs : 0 < stride) :
    ∀ (n t : Nat), t < n →
      copyInterleaved dstMem srcMem dst src stride n (dst + t * stride) =
        srcMem (src + t * stride) := by
  intro n
  induction n with
  | zero => intro t ht; omega
  | succ n ih =>
      intro t ht
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with hlt | heq
      · have hne : dst + t * stride ≠ dst + n * stride := by
          have hlt' := Nat.mul_lt_mul_of_pos_right hlt hs
          omega
        rw [copyInterleaved, update_away _ _ _ _ hne]
        exact ih t hlt
      · rw [heq, copyInterleaved, update_at]

theorem copyInterleaved_frame (dstMem srcMem : Nat → Word) (dst src stride : Nat) :
    ∀ (n a : Nat), (∀ t < n, a ≠ dst + t * stride) →
      copyInterleaved dstMem srcMem dst src stride n a = dstMem a := by
  intro n
  induction n with
  | zero => intro a _; rfl
  | succ n ih =>
      intro a h
      rw [copyInterleaved, update_away _ _ _ _ (h n (Nat.lt_succ_self n))]
      exact ih a (by intro t ht; exact h t (by omega))

/-- A lane's four interleaved words land where they should. -/
example :
    copyInterleaved (fun _ => 0) (fun k => k + 100) 3 1 4 4 (3 + 2 * 4) = 100 + 1 + 2 * 4 := by
  decide

end IntelGpu
