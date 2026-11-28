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

`Separated` states that different tile origins never share a block address.
`separated_of_width` derives it from the matrix width: a matrix of width `N`
with `N ≤ ldC` whose tile blocks fit inside `N`.

Still open, and stated as such: that a word *inside* a block ends up holding
that tile's accumulator (`writeTiles_block`). That proof is in progress and is
not claimed here.
-/

namespace IntelGpu

/-- Address of element `(m, n)` of the block of tile `p`. -/
def sliceAddr (base ldC BM BN : Nat) (p : Nat × Nat) (m n : Nat) : Nat :=
  base + ((p.1 * BM + m) * ldC + (p.2 * BN + n))

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


/-- `BM`-ary carries are injective below `BM`. -/
theorem mul_add_inj (BM m m' r r' : Nat) (hm : m < BM) (hm' : m' < BM)
    (h : r * BM + m = r' * BM + m') : r = r' ∧ m = m' := by
  have hr : r = r' := by
    rcases Nat.lt_trichotomy r r' with hlt | heq | hgt
    · have hb : r * BM + BM ≤ r' * BM := by
        have hmul : (r + 1) * BM ≤ r' * BM := Nat.mul_le_mul_right BM (by omega)
        rwa [Nat.succ_mul] at hmul
      omega
    · exact heq
    · have hb : r' * BM + BM ≤ r * BM := by
        have hmul : (r' + 1) * BM ≤ r * BM := Nat.mul_le_mul_right BM (by omega)
        rwa [Nat.succ_mul] at hmul
      omega
  subst hr
  exact ⟨rfl, by omega⟩

/-- Row-major addresses are injective when the column fits in the leading
dimension. -/
theorem addr_inj (ldC r1 c1 r2 c2 : Nat) (h1 : c1 < ldC) (h2 : c2 < ldC)
    (h : r1 * ldC + c1 = r2 * ldC + c2) : r1 = r2 := by
  rcases Nat.lt_trichotomy r1 r2 with hlt | heq | hgt
  · have hb : r1 * ldC + ldC ≤ r2 * ldC := by
      have hmul : (r1 + 1) * ldC ≤ r2 * ldC := Nat.mul_le_mul_right ldC (by omega)
      rwa [Nat.succ_mul] at hmul
    omega
  · exact heq
  · have hb : r2 * ldC + ldC ≤ r1 * ldC := by
      have hmul : (r2 + 1) * ldC ≤ r1 * ldC := Nat.mul_le_mul_right ldC (by omega)
      rwa [Nat.succ_mul] at hmul
    omega

/-- Blocks are separated once the matrix width fits the leading dimension and
every origin's block fits the width. -/
theorem separated_of_width (base ldC BM BN N : Nat)
    (hldC : N ≤ ldC) (origins : List (Nat × Nat))
    (hfit : ∀ p ∈ origins, p.2 * BN + BN ≤ N) :
    Separated base ldC BM BN origins := by
  intro p hp q hq hpq m hm n hn m' hm' n' hn' heq
  have hcore : (p.1 * BM + m) * ldC + (p.2 * BN + n) =
      (q.1 * BM + m') * ldC + (q.2 * BN + n') := by
    simp only [sliceAddr] at heq
    exact Nat.add_left_cancel heq
  have hcol : p.2 * BN + n < ldC := by
    have := hfit p hp
    omega
  have hcol' : q.2 * BN + n' < ldC := by
    have := hfit q hq
    omega
  have hrow : p.1 * BM + m = q.1 * BM + m' := addr_inj ldC _ _ _ _ hcol hcol' hcore
  obtain ⟨hr, _⟩ := mul_add_inj BM m m' p.1 q.1 hm hm' hrow
  have hcols : p.2 * BN + n = q.2 * BN + n' := by
    rw [hrow] at hcore
    omega
  obtain ⟨hc, _⟩ := mul_add_inj BN n n' p.2 q.2 hn hn' hcols
  exact hpq (Prod.ext hr hc)


end IntelGpu
