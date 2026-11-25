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
- `lanesInterleaved_frame`: the fold leaves words outside every lane's set
  alone.
- `lanesInterleaved_value`: lane `l`'s word `t` holds the matching source word.
- `lanesInterleaved_covers`: `L` lanes of `n` words at stride `L` fill
  `[dst, dst + L * n)` — the slab is completely covered.

That completes assumption 8: staging can be a per-lane block distribution
(stage 37) or an interleaved distribution (here), both with proven coverage.
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

theorem lanesInterleaved_frame (srcMem : Nat → Word) (dst src L n : Nat) :
    ∀ (lanes : Nat), ∀ (m : Nat → Word), ∀ (a : Nat),
      (∀ l < lanes, ∀ t < n, a ≠ dst + (l + t * L)) →
      lanesInterleaved m srcMem dst src L n lanes a = m a := by
  intro lanes
  induction lanes with
  | zero => intro m a _; rfl
  | succ lanes ih =>
      intro m a h
      show lanesInterleaved (copyInterleaved m srcMem (dst + lanes) (src + lanes) L n)
        srcMem dst src L n lanes a = m a
      rw [ih (copyInterleaved m srcMem (dst + lanes) (src + lanes) L n) a (by
        intro l hl t ht
        exact h l (by omega) t ht)]
      exact copyInterleaved_frame m srcMem (dst + lanes) (src + lanes) L n a (by
        intro t ht
        simpa [Nat.add_assoc] using h lanes (Nat.lt_succ_self lanes) t ht)

theorem lanesInterleaved_value (srcMem : Nat → Word) (dst src L n : Nat)
    (hL : 0 < L) :
    ∀ (lanes : Nat), ∀ (m : Nat → Word), ∀ (l t : Nat),
      l < lanes → lanes ≤ L → t < n →
      lanesInterleaved m srcMem dst src L n lanes (dst + (l + t * L)) =
        srcMem (src + (l + t * L)) := by
  intro lanes
  induction lanes with
  | zero => intro m l t hl _ _; omega
  | succ lanes ih =>
      intro m l t hl hle ht
      show lanesInterleaved (copyInterleaved m srcMem (dst + lanes) (src + lanes) L n)
        srcMem dst src L n lanes (dst + (l + t * L)) = srcMem (src + (l + t * L))
      by_cases hlt : l < lanes
      · exact ih (copyInterleaved m srcMem (dst + lanes) (src + lanes) L n) l t hlt
          (by omega) ht
      · have heq : l = lanes := by omega
        rw [heq]
        have hnotin : ∀ l' < lanes, ∀ t' < n,
            dst + (lanes + t * L) ≠ dst + (l' + t' * L) := by
          intro l' hl' t' ht'
          intro hc
          have hcore : l' + t' * L = lanes + t * L := by omega
          have hlm := lane_mod L l' lanes t' t (by omega) (by omega) hcore
          omega
        rw [lanesInterleaved_frame srcMem dst src L n lanes
          (copyInterleaved m srcMem (dst + lanes) (src + lanes) L n)
          (dst + (lanes + t * L)) hnotin]
        simpa [Nat.add_assoc] using
          copyInterleaved_value m srcMem (dst + lanes) (src + lanes) L hL n t ht

/-- Every word of the slab is covered by exactly one lane: `L` lanes of `n`
words at stride `L` fill `[dst, dst + L * n)`. -/
theorem lanesInterleaved_covers (dstMem srcMem : Nat → Word) (dst src L n : Nat)
    (hL : 0 < L) :
    ∀ k < L * n,
      lanesInterleaved dstMem srcMem dst src L n L (dst + k) = srcMem (src + k) := by
  intro k hk
  have hdiv : k / L < n := by
    rw [Nat.div_lt_iff_lt_mul hL]
    rwa [Nat.mul_comm] at hk
  have hmod : k % L < L := Nat.mod_lt _ hL
  have hdec : k % L + k / L * L = k := by
    have h := Nat.div_add_mod k L
    rw [Nat.mul_comm] at h
    omega
  rw [← hdec]
  exact lanesInterleaved_value srcMem dst src L n hL L dstMem (k % L) (k / L) hmod
    (Nat.le_refl L) hdiv

end IntelGpu
