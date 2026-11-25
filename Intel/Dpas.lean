-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.GemmMatrix

@[expose] public section

/-!
# DPAS / XMX tiled accumulation

Intel Xe `dpas` updates a whole output tile in one instruction:

    C[m][n] += Σ_{k < d} A[k][m] * B[k][n]

where `d` is the systolic depth (8 on Xe-HPC XMX). A GEMM tile of depth `K`
is then `T = K / d` DPAS instructions, each fed the next depth slab of A and B.

This module gives the tile algebra:

- `dpasSlab`: the systolic dot over one depth slab.
- `dpas`: one instruction, accumulating a slab into the C tile.
- `dpasRun`: `T` back-to-back DPAS instructions over consecutive slabs.
- `dotMatFrom_append`: splitting the GEMM spec at a depth boundary.
- `dpasRun_correct`: `T` DPAS instructions accumulate exactly `dotMat` at
  depth `T * d`.

The depth remainder (`K` not a multiple of `d`) is handled at the kernel
instance stage, where the last slab is masked.
-/

namespace IntelGpu

/-- Xe-HPC XMX systolic depth. -/
def systolicDepth : Nat := 8

/-- Systolic dot over one depth slab: `Σ_{k<d} A[k][m] * B[k][n]`. -/
def dpasSlab : Nat → (Nat → Nat → Word) → (Nat → Nat → Word) → Nat → Nat → Word
  | 0, _, _, _, _ => 0
  | d + 1, A, B, m, n =>
      A 0 m * B 0 n +
        dpasSlab d (fun k m' => A (k + 1) m') (fun k n' => B (k + 1) n') m n

/-- One DPAS instruction: accumulate a depth slab into the C tile. -/
def dpas (d : Nat) (A B : Nat → Nat → Word) (C : Nat → Nat → Word) : Nat → Nat → Word :=
  fun m n => C m n + dpasSlab d A B m n

/-- `T` DPAS instructions over consecutive depth slabs of `A`/`B`, starting at
row `i` and column `j`. Slab `T` is issued last. -/
def dpasRun (A B : Nat → Nat → Word) (i j d : Nat) :
    Nat → (Nat → Nat → Word) → (Nat → Nat → Word)
  | 0, C => C
  | T + 1, C =>
      dpas d (fun k m => A (i + m) (T * d + k)) (fun k n => B (T * d + k) (j + n))
        (dpasRun A B i j d T C)

theorem dpasSlab_eq_dotMatFrom (A B : Nat → Nat → Word) (i j : Nat) :
    ∀ (t d m n : Nat),
      dpasSlab d (fun k m' => A (i + m') (t + k)) (fun k n' => B (t + k) (j + n')) m n =
        dotMatFrom A B (i + m) (j + n) t d := by
  intro t d
  induction d generalizing t with
  | zero => intro m n; rfl
  | succ d ih =>
      intro m n
      rw [dpasSlab, dotMatFrom]
      have hA : (fun k m' => A (i + m') (t + (k + 1))) =
          fun k m' => A (i + m') (t + 1 + k) := by
        funext k m'
        rw [show t + (k + 1) = t + 1 + k by omega]
      have hB : (fun k n' => B (t + (k + 1)) (j + n')) =
          fun k n' => B (t + 1 + k) (j + n') := by
        funext k n'
        rw [show t + (k + 1) = t + 1 + k by omega]
      rw [hA, hB, ih (t + 1) m n]
      simp

theorem dotMatFrom_append (A B : Nat → Nat → Word) (i j : Nat) :
    ∀ (m k n : Nat),
      dotMatFrom A B i j k (m + n) =
        dotMatFrom A B i j k m + dotMatFrom A B i j (k + m) n := by
  intro m
  induction m with
  | zero => intro k n; simp [dotMatFrom]
  | succ m ih =>
      intro k n
      rw [Nat.succ_add, dotMatFrom, ih (k + 1) n, dotMatFrom]
      rw [← BitVec.add_assoc]
      rw [show k + 1 + m = k + (m + 1) by omega]

theorem dpasRun_acc (A B : Nat → Nat → Word) (i j d : Nat) :
    ∀ (T : Nat) (C : Nat → Nat → Word) (m n : Nat),
      dpasRun A B i j d T C m n =
        C m n + dotMatFrom A B (i + m) (j + n) 0 (T * d) := by
  intro T
  induction T with
  | zero => intro C m n; simp [dpasRun, dotMatFrom]
  | succ T ih =>
      intro C m n
      simp only [dpasRun, dpas]
      rw [ih C m n, dpasSlab_eq_dotMatFrom A B i j (T * d) d m n, Nat.succ_mul,
        dotMatFrom_append]
      rw [show 0 + T * d = T * d by omega]
      rw [← BitVec.add_assoc]

theorem dpasRun_correct (A B : Nat → Nat → Word) (i j d T m n : Nat) :
    dpasRun A B i j d T (fun _ _ => 0) m n = dotMat A B (i + m) (j + n) (T * d) := by
  rw [dpasRun_acc]
  simp [dotMat]

/-- With the Xe-HPC systolic depth, `T` DPAS instructions cover depth `8 * T`. -/
theorem dpasRun_systolic (A B : Nat → Nat → Word) (i j T m n : Nat) :
    dpasRun A B i j systolicDepth T (fun _ _ => 0) m n =
      dotMat A B (i + m) (j + n) (T * 8) := by
  simpa [systolicDepth] using dpasRun_correct A B i j 8 T m n

end IntelGpu
