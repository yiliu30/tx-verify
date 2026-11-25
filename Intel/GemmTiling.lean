-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.GemmMatrix

@[expose] public section

/-!
# GEMM tiling specification

Tile coordinates, per-tile correctness, tile coverage, and the theorem that
per-tile correctness implies the matrix-level GEMM specification.
-/

namespace IntelGpu

def TileSpec (A B C : Nat → Nat → Word) (M N K BM BN ti tj : Nat) : Prop :=
  ∀ i < BM, ∀ j < BN,
    ti * BM + i < M →
    tj * BN + j < N →
    C (ti * BM + i) (tj * BN + j) =
      dotMat A B (ti * BM + i) (tj * BN + j) K

theorem tile_row_cover (BM i : Nat) (hBM : 0 < BM) :
    ∃ ti, ti * BM ≤ i ∧ i < ti * BM + BM := by
  refine ⟨i / BM, Nat.div_mul_le_self i BM, ?_⟩
  have hmod : i % BM < BM := Nat.mod_lt _ hBM
  have hdecomp : i / BM * BM + i % BM = i := by
    simpa [Nat.mul_comm] using Nat.div_add_mod i BM
  omega

theorem tile_col_cover (BN j : Nat) (hBN : 0 < BN) :
    ∃ tj, tj * BN ≤ j ∧ j < tj * BN + BN := by
  refine ⟨j / BN, Nat.div_mul_le_self j BN, ?_⟩
  have hmod : j % BN < BN := Nat.mod_lt _ hBN
  have hdecomp : j / BN * BN + j % BN = j := by
    simpa [Nat.mul_comm] using Nat.div_add_mod j BN
  omega

theorem gemmSpecW_of_tiles (A B C : Nat → Nat → Word) (M N K BM BN : Nat)
    (hBM : 0 < BM) (hBN : 0 < BN)
    (hTiles : ∀ ti tj, TileSpec A B C M N K BM BN ti tj) :
    GemmSpecW A B C M N K := by
  intro i hi j hj
  obtain ⟨ti, hti0, hti1⟩ := tile_row_cover BM i hBM
  obtain ⟨tj, htj0, htj1⟩ := tile_col_cover BN j hBN
  have hrow : i = ti * BM + (i - ti * BM) := by omega
  have hcol : j = tj * BN + (j - tj * BN) := by omega
  have hile : i - ti * BM < BM := by omega
  have hjle : j - tj * BN < BN := by omega
  have hspec := hTiles ti tj (i - ti * BM) hile (j - tj * BN) hjle
    (by omega) (by omega)
  rw [← hrow, ← hcol] at hspec
  exact hspec

end IntelGpu
