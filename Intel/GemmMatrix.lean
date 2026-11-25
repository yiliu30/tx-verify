-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.GemmMemoryLoop

@[expose] public section

/-!
# Matrix GEMM specification

Defines the matrix-level dot product and GEMM specification, and connects the
word-indexed memory loop to the dot product for one materialized row/column.
-/

namespace IntelGpu

def dotMatFrom (A B : Nat → Nat → Word) (i j : Nat) (k : Nat) : Nat → Word
  | 0 => 0
  | n + 1 => A i k * B k j + dotMatFrom A B i j (k + 1) n

def dotMat (A B : Nat → Nat → Word) (i j K : Nat) : Word :=
  dotMatFrom A B i j 0 K

def GemmSpecW (A B C : Nat → Nat → Word) (M N K : Nat) : Prop :=
  ∀ i < M, ∀ j < N, C i j = dotMat A B i j K

def matrixMem (A B : Nat → Nat → Word) (i j K n : Nat) : Word :=
  if n < K then A i n else B (n - K) j

theorem matrixMem_A (A B : Nat → Nat → Word) (i j K k : Nat) (h : k < K) :
    matrixMem A B i j K k = A i k := by
  simp [matrixMem, h]

theorem matrixMem_B (A B : Nat → Nat → Word) (i j K k : Nat) :
    matrixMem A B i j K (K + k) = B k j := by
  have hlt : ¬ K + k < K := by omega
  simp [matrixMem, hlt, Nat.add_sub_cancel_left]

theorem dotRange_matrixMem_gen (A B : Nat → Nat → Word) (i j K k n : Nat)
    (h : k + n ≤ K) :
    dotRange (fun t => matrixMem A B i j K t)
             (fun t => matrixMem A B i j K (K + t)) k n =
      dotMatFrom A B i j k n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
      have hk : k < K := by omega
      have hnext : k + 1 + n ≤ K := by omega
      simp [dotRange, dotMatFrom, matrixMem_A A B i j K k hk,
            matrixMem_B A B i j K k, ih (k + 1) hnext]

theorem mProgram_matrix (A B : Nat → Nat → Word) (i j K : Nat) :
    let s := mrun (mProgram K) (10 * K + 3) (mLoopHead (matrixMem A B i j K) K 0 0)
    s.halted = true ∧ s.k = K ∧ s.sum = dotMat A B i j K := by
  have h := mProgram_correct (matrixMem A B i j K) K
  dsimp at h
  have hdot := dotRange_matrixMem_gen A B i j K 0 K (by omega)
  rw [hdot] at h
  simpa [dotMat] using h

end IntelGpu
