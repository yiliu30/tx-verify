-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Interleaved

@[expose] public section

/-!
# Lanes covering a slab, interleaved

Stage 50 gave one lane's interleaved copy. This composes the lanes and proves
they cover the slab: after lanes `0 .. L-1` each move `n` words at stride `L`,
every word of `[dst, dst + L * n)` holds the matching source word.

- `lane_mod`: two lanes below `L` write different residue classes, so an
  interleaved copy can never have two lanes collide.
- `lanesInterleaved`: the workgroup copy, folded over lanes.

Not proved here: that the fold covers the slab (`k < L * n` ⇒ word `k` is in
place). `lane_mod` is the mathematical core of that argument — every earlier
attempt died on exactly this residue-class step — but the fold induction that
consumes it is still open. Assumption 8 is therefore discharged as far as the
residue argument, not further.
-/

namespace IntelGpu

/-- Two lanes below `L` write different residue classes. -/
theorem lane_mod (L : Nat) :
    ∀ (l l' t t' : Nat), l < L → l' < L → l + t * L = l' + t' * L → l = l' := by
  intro l l' t t' hl hl' heq
  have h1 : (l + t * L) % L = l := by
    rw [Nat.mul_comm t L, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
  have h2 : (l' + t' * L) % L = l' := by
    rw [Nat.mul_comm t' L, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl']
  rw [heq] at h1
  omega

/-- The workgroup copy: lane `l` moves its residue class. -/
def lanesInterleaved (dstMem srcMem : Nat → Word) (dst src L n : Nat) : Nat → Nat → Word
  | 0 => dstMem
  | l + 1 =>
      lanesInterleaved (copyInterleaved dstMem srcMem (dst + l) (src + l) L n) srcMem
        dst src L n l

end IntelGpu
