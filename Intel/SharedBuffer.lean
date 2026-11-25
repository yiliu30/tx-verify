-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.EpilogueFrame
public import Intel.GemmScheduler

@[expose] public section

/-!
# One output buffer for all tiles

Stage 23 stitches tiles by reading each element from *its own tile's* memory.
Stage 39 gives the epilogue a frame law. Together they let the tiles share one
`C` buffer: writing tiles in sequence, each keeps its block and disturbs
nothing else.

- `sliceAddr`: the address of element `(m, n)` in tile `p`'s block.
- `writeTiles`: fold the per-tile epilogues over a list of tile origins.
- `writeTiles_frame`: a word outside every block is left alone by the whole
  fold.

`Separated` states that different tile origins never share a block address; it
is a hypothesis here. Deriving it from the tile arithmetic needs the matrix
width (`p.2 * BN + BN ≤ N ≤ ldC`), and stating that a word *inside* a block
holds that tile's accumulator is the next step — neither is claimed yet.
-/

namespace IntelGpu

/-- Address of element `(m, n)` of the block of tile `p`. -/
def sliceAddr (base ldC BM BN : Nat) (p : Nat × Nat) (m n : Nat) : Nat :=
  base + (p.1 * BM + m) * ldC + (p.2 * BN + n)

/-- The block address in the form the epilogue uses. -/
theorem sliceAddr_eq (base ldC BM BN : Nat) (q : Nat × Nat) (m n : Nat) :
    sliceAddr base ldC BM BN q m n =
      base + q.1 * BM * ldC + q.2 * BN + m * ldC + n := by
  simp only [sliceAddr]
  rw [Nat.add_mul]
  omega

/-- Run tile `p`'s epilogue on `mem`. -/
def tileEpilogue (base ldC BM BN : Nat) (acc : Nat → Nat → Nat → Nat → Word)
    (mem : Nat → Word) (p : Nat × Nat) : Nat → Word :=
  (lrun (base + p.1 * BM * ldC + p.2 * BN) ldC BN (epilogueProg (BM * BN))
    (5 * (BM * BN) + 3) (eHead mem (acc p.1 p.2))).mem

/-- Write every tile's block into one buffer, in list order. -/
def writeTiles (base ldC BM BN : Nat) (acc : Nat → Nat → Nat → Nat → Word)
    (origins : List (Nat × Nat)) (mem : Nat → Word) : Nat → Word :=
  origins.foldl (tileEpilogue base ldC BM BN acc) mem

/-- Blocks of two different origins never overlap. -/
def Separated (base ldC BM BN : Nat) (origins : List (Nat × Nat)) : Prop :=
  ∀ p ∈ origins, ∀ q ∈ origins, p ≠ q → ∀ m < BM, ∀ n < BN, ∀ m' < BM, ∀ n' < BN,
    sliceAddr base ldC BM BN p m n ≠ sliceAddr base ldC BM BN q m' n'

/-- A word outside every block is left alone by the whole fold. -/
theorem writeTiles_frame (base ldC BM BN : Nat) (hBN : 0 < BN)
    (hldC : BN ≤ ldC) (acc : Nat → Nat → Nat → Nat → Word) (origins : List (Nat × Nat)) :
    ∀ (mem : Nat → Word) (a : Nat),
      (∀ p ∈ origins, ∀ m < BM, ∀ n < BN, a ≠ sliceAddr base ldC BM BN p m n) →
      writeTiles base ldC BM BN acc origins mem a = mem a := by
  intro mem a
  induction origins generalizing mem with
  | nil => intro _; rfl
  | cons q rest ih =>
      intro h
      have hstep : writeTiles base ldC BM BN acc (q :: rest) mem =
          writeTiles base ldC BM BN acc rest (tileEpilogue base ldC BM BN acc mem q) := rfl
      rw [hstep]
      have hhead : tileEpilogue base ldC BM BN acc mem q a = mem a :=
        epilogueLd_frame (base + q.1 * BM * ldC + q.2 * BN) ldC BN BM hBN hldC mem
          (acc q.1 q.2) a (by
            intro m hm n hn
            simpa [sliceAddr_eq base ldC BM BN q m n] using
              (h q List.mem_cons_self m hm n hn))
      rw [ih (tileEpilogue base ldC BM BN acc mem q) (by
        intro p hp m hm n hn
        exact h p (List.mem_cons_of_mem q hp) m hm n hn)]
      exact hhead

end IntelGpu
