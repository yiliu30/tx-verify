-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Mainloop

@[expose] public section

/-!
# Distributed staging across lanes

Stages 24/25 stage a slab with one workgroup-wide copy. Real kernels
distribute that copy over work-items, lane `l` owning the contiguous chunk
`[l * c, (l + 1) * c)`.

A block distribution with chunk width `c` is exactly a strided copy with row
stride `c` and row length `c`, so rather than reprove the copy this module
identifies the per-lane fold with stage 25's `copyStrided` and inherits its
value and frame laws.

The fold nests copies inside-out — lane 0 first, lane `l` last — which is what
makes the identification definitional. A fold that applied lane `l` first
would write the same memory but would not line up with the strided copy's
recursion.
-/

namespace IntelGpu

/-- The workgroup copy with a block distribution: lane `l` moves the `c` words
at `slm[dst + l * c]` from `mem[src + l * c]`. -/
def laneBlockFold (dstMem srcMem : Nat → Word) (dst src c : Nat) : Nat → Nat → Word
  | 0 => dstMem
  | l + 1 =>
      copyN (laneBlockFold dstMem srcMem dst src c l) srcMem (dst + l * c) (src + l * c) c

/-- A block distribution is a strided copy with stride and width `c`. -/
theorem laneBlockFold_eq_copyStrided (dstMem srcMem : Nat → Word) (dst src c : Nat) :
    ∀ rows,
      laneBlockFold dstMem srcMem dst src c rows = copyStrided dstMem srcMem dst src c c rows := by
  intro rows
  induction rows with
  | zero => rfl
  | succ rows ih =>
      simp only [laneBlockFold, copyStrided]
      rw [ih]

/-- Every word of the slab is in place: lane `j` owns the chunk starting at
`j * c`, and its word `i` comes from the same offset in the source. -/
theorem laneBlock_value (dstMem srcMem : Nat → Word) (dst src c : Nat) :
    ∀ (rows j i : Nat), j < rows → i < c →
      laneBlockFold dstMem srcMem dst src c rows (dst + (j * c + i)) =
        srcMem (src + (j * c + i)) := by
  intro rows j i hj hi
  rw [laneBlockFold_eq_copyStrided]
  have h := copyStrided_value dstMem srcMem dst src c c rows j i hj hi
  simpa [Nat.add_assoc] using h

/-- Words outside the slab are untouched. -/
theorem laneBlock_frame (dstMem srcMem : Nat → Word) (dst src c : Nat) :
    ∀ (rows a : Nat), (∀ j < rows, ∀ i < c, a ≠ dst + (j * c + i)) →
      laneBlockFold dstMem srcMem dst src c rows a = dstMem a := by
  intro rows a h
  rw [laneBlockFold_eq_copyStrided]
  apply copyStrided_frame
  intro r hr i hi
  simpa [Nat.add_assoc] using h r hr i hi

/-- An earlier lane's chunk cannot be touched by a later lane: chunk `j`'s word
`i` sits below chunk `j'`'s first word. -/
theorem laneBlock_disjoint (dst c j j' i i' : Nat) (hj : j < j') (hi : i < c) :
    dst + (j * c + i) ≠ dst + (j' * c + i') := by
  intro heq
  have hcore : j * c + i = j' * c + i' := by omega
  have hb : j * c + c ≤ j' * c := by
    have hle := Nat.mul_le_mul_right c (by omega : j + 1 ≤ j')
    rwa [Nat.succ_mul] at hle
  omega

end IntelGpu
