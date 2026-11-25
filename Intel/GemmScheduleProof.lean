-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.GemmScheduler

@[expose] public section

/-!
# Scheduled-tile correctness composition

If every scheduled tile satisfies `TileSpec`, then every output element is
covered by a scheduled tile and the matrix-level GEMM specification holds.
-/

namespace IntelGpu

theorem le_numTiles_mul (M BM : Nat) (hBM : 0 < BM) :
    M ≤ numTiles M BM * BM := by
  unfold numTiles
  have hmod : (M + BM - 1) % BM < BM := Nat.mod_lt _ hBM
  have hdecomp : (M + BM - 1) / BM * BM + (M + BM - 1) % BM = M + BM - 1 := by
    simpa [Nat.mul_comm] using Nat.div_add_mod (M + BM - 1) BM
  omega

theorem div_lt_numTiles (M BM i : Nat) (hBM : 0 < BM) (hi : i < M) :
    i / BM < numTiles M BM := by
  apply (Nat.div_lt_iff_lt_mul hBM).2
  exact Nat.lt_of_lt_of_le hi (le_numTiles_mul M BM hBM)

theorem gemmSpecW_of_schedule (A B C : Nat → Nat → Word) (M N K BM BN : Nat)
    (hBM : 0 < BM) (hBN : 0 < BN)
    (hTiles : ∀ ti tj, (ti, tj) ∈ tileSchedule M N BM BN →
      TileSpec A B C M N K BM BN ti tj) :
    GemmSpecW A B C M N K := by
  intro i hi j hj
  have hmodi : i % BM < BM := Nat.mod_lt _ hBM
  have hmodj : j % BN < BN := Nat.mod_lt _ hBN
  have hdecompi : i / BM * BM + i % BM = i := by
    simpa [Nat.mul_comm] using Nat.div_add_mod i BM
  have hdecompj : j / BN * BN + j % BN = j := by
    simpa [Nat.mul_comm] using Nat.div_add_mod j BN
  have hti : i / BM < numTiles M BM := div_lt_numTiles M BM i hBM hi
  have htj : j / BN < numTiles N BN := div_lt_numTiles N BN j hBN hj
  have hmem : (i / BM, j / BN) ∈ tileSchedule M N BM BN :=
    mem_tileSchedule_of_lt M N BM BN _ _ hti htj
  have hspec := hTiles (i / BM) (j / BN) hmem (i % BM) hmodi (j % BN) hmodj
    (by omega) (by omega)
  rw [hdecompi, hdecompj] at hspec
  exact hspec

end IntelGpu
