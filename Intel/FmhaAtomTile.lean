-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.DpasAtom
public import Intel.RealDpas

@[expose] public section

/-!
# FMHA 8x8x32 atom: value refinement and tile composition

`Intel.RealDpas` decodes the compiled FMHA `dpas.8x8` to the coded 8x8x32 atom
`fmhaFp8Atom` and defines `fmhaAtom`, one depth-32 accumulation into the 8x8
accumulator block at tile origin `(i, j)`. This module supplies the value-level
refinement used by review item "P1 DPAS refinement":

- `fmhaAtom_eq_slab`/`fmhaAtom_eq_dpas` state the exact relationship at the
  same origin: the atom is one `dpas` of depth 32 over the row-sliced `A` and
  column-sliced `B`, with the accumulator argument being the `C` slice at
  `(i, j)`. `fmhaAtom_eq_dpasRun` identifies it with one mainloop step.
- `fmhaAtom_eq_sum_halves`/`fmhaAtom_eq_two_dpas` split the single K=32 step
  into two K=16 halves whose sum is the K=32 result, the second half reading
  operands shifted by 16. This is `dpasSlab_split` at `16 + 16`, so the coded
  atom composes with the existing slab machinery.
- `fmhaGrid2x1`/`fmhaGrid2x2` write a 2x1 or 2x2 grid of atoms into disjoint
  accumulator blocks (the `8 x 8` block of each origin). The per-cell lemmas
  show each atom owns its block, and `fmhaGrid2x1_eq_pointwise_sum`/
  `fmhaGrid2x2_eq_pointwise_sum` show the combined update is the pointwise sum
  of the atoms' depth-32 deltas.

All statements are value-level equalities over `Word = BitVec 32`. The fp8
element encoding stays the assumption recorded in `Intel.RealDpas`.
-/

namespace IntelGpu

/-- The atom's depth-32 slab, without the accumulator: the value the coded
DPAS adds into the 8x8 accumulator block at tile origin `(i, j)`. -/
def fmhaAtomDelta (A B : Nat → Nat → Word) (i j : Nat) : Nat → Nat → Word :=
  fun m n =>
    dpasSlab 32 (fun k m' => A (i + m') k) (fun k n' => B k (j + n')) m n

/-- Value form: the atom is the incoming accumulator plus its depth-32 delta. -/
theorem fmhaAtom_eq_delta (A B C : Nat → Nat → Word) (i j m n : Nat) :
    fmhaAtom A B C i j m n = C (i + m) (j + n) + fmhaAtomDelta A B i j m n :=
  rfl

/-- At the same origin `(i, j)`, the atom is exactly one depth-32 slab of the
row-sliced `A` and the column-sliced `B`. -/
theorem fmhaAtom_eq_slab (A B C : Nat → Nat → Word) (i j m n : Nat) :
    fmhaAtom A B C i j m n =
      C (i + m) (j + n) +
        dpasSlab 32 (fun k m' => A (i + m') k) (fun k n' => B k (j + n')) m n :=
  rfl

/-- At the same origin `(i, j)`, the atom is one `dpas` of depth 32 whose
accumulator argument is the `C` slice at `(i, j)`. -/
theorem fmhaAtom_eq_dpas (A B C : Nat → Nat → Word) (i j : Nat) :
    fmhaAtom A B C i j =
      dpas 32 (fun k m' => A (i + m') k) (fun k n' => B k (j + n'))
        (fun m n => C (i + m) (j + n)) :=
  rfl

/-- The atom is exactly one step of the tile mainloop `dpasRun`. -/
theorem fmhaAtom_eq_dpasRun (A B C : Nat → Nat → Word) (i j : Nat) :
    fmhaAtom A B C i j =
      dpasRun A B i j 32 1 (fun m n => C (i + m) (j + n)) :=
  rfl

/-- The atom adds the full depth-32 matrix dot product at its coordinates. -/
theorem fmhaAtom_eq_dotMat (A B C : Nat → Nat → Word) (i j m n : Nat) :
    fmhaAtom A B C i j m n = C (i + m) (j + n) + dotMat A B (i + m) (j + n) 32 := by
  simpa [dotMat] using fmhaAtom_correct A B C i j m n

/-- One depth-16 half of the atom, without the accumulator: the slab over the
depth window `[t, t + 16)`. -/
def fmhaHalfDelta (A B : Nat → Nat → Word) (i j t : Nat) : Nat → Nat → Word :=
  fun m n =>
    dpasSlab 16 (fun k m' => A (i + m') (k + t)) (fun k n' => B (k + t) (j + n')) m n

/-- The first K=16 half instruction, accumulated onto the `C` slice at
`(i, j)`. -/
def fmhaHalf (A B C : Nat → Nat → Word) (i j t : Nat) : Nat → Nat → Word :=
  fun m n => C (i + m) (j + n) + fmhaHalfDelta A B i j t m n

/-- A depth-16 half is one `dpas` instruction over the depth-shifted operands. -/
theorem fmhaHalf_eq_dpas (A B C : Nat → Nat → Word) (i j t : Nat) :
    fmhaHalf A B C i j t =
      dpas 16 (fun k m' => A (i + m') (k + t)) (fun k n' => B (k + t) (j + n'))
        (fun m n => C (i + m) (j + n)) :=
  rfl

/-- Each half is the corresponding depth-16 slice of the matrix spec. -/
theorem fmhaHalfDelta_eq_dotMatFrom (A B : Nat → Nat → Word) (i j t m n : Nat) :
    fmhaHalfDelta A B i j t m n = dotMatFrom A B (i + m) (j + n) t 16 := by
  simpa [fmhaHalfDelta, Nat.add_comm] using dpasSlab_eq_dotMatFrom A B i j t 16 m n

/-- The K=32 atom is the sum of its two K=16 halves: `dpasSlab_split` at
`16 + 16`, with the second half over operands shifted by 16. -/
theorem fmhaAtom_eq_sum_halves (A B C : Nat → Nat → Word) (i j m n : Nat) :
    fmhaAtom A B C i j m n =
      C (i + m) (j + n) + fmhaHalfDelta A B i j 0 m n +
        fmhaHalfDelta A B i j 16 m n := by
  have hsplit := dpasSlab_split 16 16
    (fun k m' => A (i + m') k) (fun k n' => B k (j + n')) m n
  rw [show (16 : Nat) + 16 = 32 by omega] at hsplit
  simp only [fmhaAtom, fmhaHalfDelta, Nat.add_zero]
  rw [hsplit, ← BitVec.add_assoc]

/-- The single K=32 instruction is two K=16 instructions: the second reads the
operands shifted by 16 and accumulates onto the first half's result. -/
theorem fmhaAtom_eq_two_dpas (A B C : Nat → Nat → Word) (i j : Nat) :
    fmhaAtom A B C i j =
      dpas 16 (fun k m' => A (i + m') (k + 16)) (fun k n' => B (k + 16) (j + n'))
        (fmhaHalf A B C i j 0) := by
  funext m n
  rw [fmhaAtom_eq_sum_halves]
  rfl

/-- Spec form of the split: the two halves are the `[0, 16)` and `[16, 32)`
depth slices of `dotMatFrom`. -/
theorem fmhaAtom_eq_dotMatFrom_halves (A B C : Nat → Nat → Word) (i j m n : Nat) :
    fmhaAtom A B C i j m n =
      C (i + m) (j + n) + dotMatFrom A B (i + m) (j + n) 0 16 +
        dotMatFrom A B (i + m) (j + n) 16 16 := by
  rw [fmhaAtom_eq_sum_halves, fmhaHalfDelta_eq_dotMatFrom,
    fmhaHalfDelta_eq_dotMatFrom]

/-- One atom as a write into a global accumulator: inside its `8 x 8` output
block it adds the depth-32 delta, elsewhere it leaves the accumulator
unchanged. -/
def fmhaPatch (A B C : Nat → Nat → Word) (i j x y : Nat) : Word :=
  if i ≤ x ∧ x < i + 8 ∧ j ≤ y ∧ y < j + 8 then
    C x y + fmhaAtomDelta A B i j (x - i) (y - j)
  else C x y

/-- Inside its block, a patch is the atom at the block-local coordinates. -/
theorem fmhaPatch_eq_atom {A B C : Nat → Nat → Word} {i j x y : Nat}
    (hx0 : i ≤ x) (hx1 : x < i + 8) (hy0 : j ≤ y) (hy1 : y < j + 8) :
    fmhaPatch A B C i j x y = fmhaAtom A B C i j (x - i) (y - j) := by
  unfold fmhaPatch fmhaAtom
  rw [ite_eq_left ⟨hx0, hx1, hy0, hy1⟩]
  have hx : i + (x - i) = x := by omega
  have hy : j + (y - j) = y := by omega
  rw [hx, hy]
  rfl

/-- Outside its block, a patch is the identity on the accumulator. -/
theorem fmhaPatch_eq_self {A B C : Nat → Nat → Word} {i j x y : Nat}
    (h : ¬ (i ≤ x ∧ x < i + 8 ∧ j ≤ y ∧ y < j + 8)) :
    fmhaPatch A B C i j x y = C x y := by
  unfold fmhaPatch
  rw [ite_eq_right h]

/-- A 2x1 grid along M: the atom at `(i, j)` followed by the atom at
`(i + 8, j)`. The stride 8 is the coded atom's M extent. -/
def fmhaGrid2x1 (A B C : Nat → Nat → Word) (i j : Nat) : Nat → Nat → Word :=
  fun x y => fmhaPatch A B (fmhaPatch A B C i j) (i + 8) j x y

/-- The top cell of the 2x1 grid is the atom at `(i, j)`; the bottom atom
leaves it unchanged. -/
theorem fmhaGrid2x1_eq_atom_top {A B C : Nat → Nat → Word} {i j x y : Nat}
    (hx0 : i ≤ x) (hx1 : x < i + 8) (hy0 : j ≤ y) (hy1 : y < j + 8) :
    fmhaGrid2x1 A B C i j x y = fmhaAtom A B C i j (x - i) (y - j) := by
  unfold fmhaGrid2x1
  rw [fmhaPatch_eq_self (i := i + 8) (j := j) (x := x) (y := y) (by omega),
    fmhaPatch_eq_atom hx0 hx1 hy0 hy1]

/-- The bottom cell of the 2x1 grid is the atom at `(i + 8, j)`; the top atom
leaves it unchanged. -/
theorem fmhaGrid2x1_eq_atom_bottom {A B C : Nat → Nat → Word} {i j x y : Nat}
    (hx0 : i + 8 ≤ x) (hx1 : x < i + 8 + 8) (hy0 : j ≤ y) (hy1 : y < j + 8) :
    fmhaGrid2x1 A B C i j x y = fmhaAtom A B C (i + 8) j (x - (i + 8)) (y - j) := by
  unfold fmhaGrid2x1
  rw [fmhaPatch_eq_atom (C := fmhaPatch A B C i j) hx0 hx1 hy0 hy1]
  simp only [fmhaAtom_eq_delta]
  have hx : i + 8 + (x - (i + 8)) = x := by omega
  have hy : j + (y - j) = y := by omega
  rw [hx, hy, fmhaPatch_eq_self (i := i) (j := j) (x := x) (y := y) (by omega)]

/-- 2x1 grid composition: with disjoint accumulator rows, the combined update
is the pointwise sum of the two atoms' depth-32 deltas. -/
theorem fmhaGrid2x1_eq_pointwise_sum (A B C : Nat → Nat → Word) (i j x y : Nat)
    (hx0 : i ≤ x) (hx1 : x < i + 16) (hy0 : j ≤ y) (hy1 : y < j + 8) :
    fmhaGrid2x1 A B C i j x y =
      C x y +
        (if x < i + 8 then fmhaAtomDelta A B i j (x - i) (y - j) else 0) +
        (if i + 8 ≤ x then
          fmhaAtomDelta A B (i + 8) j (x - (i + 8)) (y - j) else 0) := by
  by_cases hx : x < i + 8
  · rw [ite_eq_left hx, ite_eq_right (by omega),
      fmhaGrid2x1_eq_atom_top hx0 hx hy0 hy1, fmhaAtom_eq_delta]
    have hx' : i + (x - i) = x := by omega
    have hy' : j + (y - j) = y := by omega
    rw [hx', hy']
    simp
  · rw [ite_eq_right hx, ite_eq_left (by omega),
      fmhaGrid2x1_eq_atom_bottom (by omega) hx1 hy0 hy1, fmhaAtom_eq_delta]
    have hx' : i + 8 + (x - (i + 8)) = x := by omega
    have hy' : j + (y - j) = y := by omega
    rw [hx', hy']
    simp

/-- A 2x2 grid: atoms at `(i, j)`, `(i + 8, j)`, `(i, j + 8)` and
`(i + 8, j + 8)`, each own its `8 x 8` accumulator block. -/
def fmhaGrid2x2 (A B C : Nat → Nat → Word) (i j : Nat) : Nat → Nat → Word :=
  fun x y =>
    fmhaPatch A B
      (fmhaPatch A B (fmhaPatch A B (fmhaPatch A B C i j) (i + 8) j) i (j + 8))
      (i + 8) (j + 8) x y

/-- The top-left cell of the 2x2 grid is the atom at `(i, j)`; the other three
atoms leave it unchanged. -/
theorem fmhaGrid2x2_eq_atom_top_left {A B C : Nat → Nat → Word} {i j x y : Nat}
    (hx0 : i ≤ x) (hx1 : x < i + 8) (hy0 : j ≤ y) (hy1 : y < j + 8) :
    fmhaGrid2x2 A B C i j x y = fmhaAtom A B C i j (x - i) (y - j) := by
  unfold fmhaGrid2x2
  rw [fmhaPatch_eq_self (i := i + 8) (j := j + 8) (x := x) (y := y) (by omega),
    fmhaPatch_eq_self (i := i) (j := j + 8) (x := x) (y := y) (by omega),
    fmhaPatch_eq_self (i := i + 8) (j := j) (x := x) (y := y) (by omega),
    fmhaPatch_eq_atom hx0 hx1 hy0 hy1]

/-- The top-right cell of the 2x2 grid is the atom at `(i + 8, j)`; the other
three atoms leave it unchanged. -/
theorem fmhaGrid2x2_eq_atom_top_right {A B C : Nat → Nat → Word} {i j x y : Nat}
    (hx0 : i + 8 ≤ x) (hx1 : x < i + 8 + 8) (hy0 : j ≤ y) (hy1 : y < j + 8) :
    fmhaGrid2x2 A B C i j x y =
      fmhaAtom A B C (i + 8) j (x - (i + 8)) (y - j) := by
  unfold fmhaGrid2x2
  rw [fmhaPatch_eq_self (i := i + 8) (j := j + 8) (x := x) (y := y) (by omega),
    fmhaPatch_eq_self (i := i) (j := j + 8) (x := x) (y := y) (by omega),
    fmhaPatch_eq_atom (i := i + 8) (j := j) (x := x) (y := y) hx0 hx1 hy0 hy1]
  simp only [fmhaAtom_eq_delta]
  have hx : i + 8 + (x - (i + 8)) = x := by omega
  have hy : j + (y - j) = y := by omega
  rw [hx, hy, fmhaPatch_eq_self (i := i) (j := j) (x := x) (y := y) (by omega)]

/-- The bottom-left cell of the 2x2 grid is the atom at `(i, j + 8)`; the
other three atoms leave it unchanged. -/
theorem fmhaGrid2x2_eq_atom_bottom_left {A B C : Nat → Nat → Word} {i j x y : Nat}
    (hx0 : i ≤ x) (hx1 : x < i + 8) (hy0 : j + 8 ≤ y) (hy1 : y < j + 8 + 8) :
    fmhaGrid2x2 A B C i j x y =
      fmhaAtom A B C i (j + 8) (x - i) (y - (j + 8)) := by
  unfold fmhaGrid2x2
  rw [fmhaPatch_eq_self (i := i + 8) (j := j + 8) (x := x) (y := y) (by omega),
    fmhaPatch_eq_atom (i := i) (j := j + 8) (x := x) (y := y) hx0 hx1 hy0 hy1]
  simp only [fmhaAtom_eq_delta]
  have hx : i + (x - i) = x := by omega
  have hy : j + 8 + (y - (j + 8)) = y := by omega
  rw [hx, hy, fmhaPatch_eq_self (i := i + 8) (j := j) (x := x) (y := y) (by omega),
    fmhaPatch_eq_self (i := i) (j := j) (x := x) (y := y) (by omega)]

/-- The bottom-right cell of the 2x2 grid is the atom at `(i + 8, j + 8)`; the
other three atoms leave it unchanged. -/
theorem fmhaGrid2x2_eq_atom_bottom_right {A B C : Nat → Nat → Word} {i j x y : Nat}
    (hx0 : i + 8 ≤ x) (hx1 : x < i + 8 + 8) (hy0 : j + 8 ≤ y)
    (hy1 : y < j + 8 + 8) :
    fmhaGrid2x2 A B C i j x y =
      fmhaAtom A B C (i + 8) (j + 8) (x - (i + 8)) (y - (j + 8)) := by
  unfold fmhaGrid2x2
  rw [fmhaPatch_eq_atom (i := i + 8) (j := j + 8) (x := x) (y := y) hx0 hx1 hy0 hy1]
  simp only [fmhaAtom_eq_delta]
  have hx : i + 8 + (x - (i + 8)) = x := by omega
  have hy : j + 8 + (y - (j + 8)) = y := by omega
  rw [hx, hy, fmhaPatch_eq_self (i := i) (j := j + 8) (x := x) (y := y) (by omega),
    fmhaPatch_eq_self (i := i + 8) (j := j) (x := x) (y := y) (by omega),
    fmhaPatch_eq_self (i := i) (j := j) (x := x) (y := y) (by omega)]

/-- 2x2 grid composition: with disjoint accumulator blocks, the combined
update is the pointwise sum of the four atoms' depth-32 deltas. -/
theorem fmhaGrid2x2_eq_pointwise_sum (A B C : Nat → Nat → Word) (i j x y : Nat)
    (hx0 : i ≤ x) (hx1 : x < i + 16) (hy0 : j ≤ y) (hy1 : y < j + 16) :
    fmhaGrid2x2 A B C i j x y =
      C x y +
        (if x < i + 8 ∧ y < j + 8 then
          fmhaAtomDelta A B i j (x - i) (y - j) else 0) +
        (if i + 8 ≤ x ∧ y < j + 8 then
          fmhaAtomDelta A B (i + 8) j (x - (i + 8)) (y - j) else 0) +
        (if x < i + 8 ∧ j + 8 ≤ y then
          fmhaAtomDelta A B i (j + 8) (x - i) (y - (j + 8)) else 0) +
        (if i + 8 ≤ x ∧ j + 8 ≤ y then
          fmhaAtomDelta A B (i + 8) (j + 8) (x - (i + 8)) (y - (j + 8)) else 0) := by
  by_cases hx : x < i + 8
  · by_cases hy : y < j + 8
    · rw [ite_eq_left ⟨hx, hy⟩, ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), fmhaGrid2x2_eq_atom_top_left hx0 hx hy0 hy,
        fmhaAtom_eq_delta]
      have hx' : i + (x - i) = x := by omega
      have hy' : j + (y - j) = y := by omega
      rw [hx', hy']
      simp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left ⟨hx, by omega⟩, ite_eq_right (by omega),
        fmhaGrid2x2_eq_atom_bottom_left hx0 hx (by omega) hy1, fmhaAtom_eq_delta]
      have hx' : i + (x - i) = x := by omega
      have hy' : j + 8 + (y - (j + 8)) = y := by omega
      rw [hx', hy']
      simp
  · by_cases hy : y < j + 8
    · rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, hy⟩,
        ite_eq_right (by omega), ite_eq_right (by omega),
        fmhaGrid2x2_eq_atom_top_right (by omega) hx1 hy0 hy, fmhaAtom_eq_delta]
      have hx' : i + 8 + (x - (i + 8)) = x := by omega
      have hy' : j + (y - j) = y := by omega
      rw [hx', hy']
      simp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left ⟨by omega, by omega⟩,
        fmhaGrid2x2_eq_atom_bottom_right (by omega) hx1 (by omega) hy1,
        fmhaAtom_eq_delta]
      have hx' : i + 8 + (x - (i + 8)) = x := by omega
      have hy' : j + 8 + (y - (j + 8)) = y := by omega
      rw [hx', hy']
      simp

end IntelGpu
