-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.GemmTiling

@[expose] public section

/-!
# GEMM tile scheduler enumeration

Number of tiles in each dimension, the scheduled tile list, and membership /
completeness lemmas. Persistent work distribution is a later stage.
-/

namespace IntelGpu

def numTiles (M BM : Nat) : Nat := (M + BM - 1) / BM

def tileSchedule (M N BM BN : Nat) : List (Nat × Nat) :=
  (List.range (numTiles M BM)).flatMap fun ti =>
    (List.range (numTiles N BN)).map fun tj => (ti, tj)

theorem mem_tileSchedule (M N BM BN ti tj : Nat) :
    (ti, tj) ∈ tileSchedule M N BM BN ↔
      ti < numTiles M BM ∧ tj < numTiles N BN := by
  unfold tileSchedule
  simp only [List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl, rfl⟩
    exact ⟨ha, hb⟩
  · rintro ⟨hti, htj⟩
    exact ⟨ti, hti, tj, htj, rfl, rfl⟩

theorem mem_tileSchedule_of_lt (M N BM BN ti tj : Nat)
    (hti : ti < numTiles M BM) (htj : tj < numTiles N BN) :
    (ti, tj) ∈ tileSchedule M N BM BN :=
  (mem_tileSchedule M N BM BN ti tj).2 ⟨hti, htj⟩

end IntelGpu
