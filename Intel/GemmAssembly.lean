-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.EpilogueLd
public import Intel.GemmScheduleProof

@[expose] public section

/-!
# Assembling the tiles into one output

Stages 18-22 verify one output tile end to end: DPAS mainloop, then the strided
epilogue. This module puts the tiles back together.

- `gemmTile_end_to_end_ld`: one tile's mainloop plus strided epilogue leaves
  `dotMat` in memory at the tile's block.
- `gemmSpecW_of_tilesExecuted`: if every scheduled tile's block holds `dotMat`,
  the stitched matrix satisfies `GemmSpecW`. Each element `(x, y)` is read from
  the memory of its owning tile, which the stage-15 scheduler shows exists.
- `tlaXeF16_gemm_executed`: the same statement at the SYCL-TLA `256 x 256`
  workgroup shape.
-/

namespace IntelGpu

/-- One output tile, end to end with a leading dimension. -/
theorem gemmTile_end_to_end_ld (A B : Nat → Nat → Word) (d T BM BN ldC : Nat)
    (hBN : 0 < BN) (hldC : BN ≤ ldC) (base ti tj : Nat) (mem0 : Nat → Word)
    (s : XState) (hInit : XInv A B (ti * BM) (tj * BN) d 0 s) :
    let s1 := xrun A B (ti * BM) (tj * BN) d (dpasProg T) (7 * T + 3) s
    let e := lrun (base + ti * BM * ldC + tj * BN) ldC BN (epilogueProg (BM * BN))
      (5 * (BM * BN) + 3) (eHead mem0 s1.acc)
    s1.halted = true ∧ e.halted = true ∧
      ∀ m < BM, ∀ n < BN,
        e.mem (base + ti * BM * ldC + tj * BN + m * ldC + n) =
          dotMat A B (ti * BM + m) (tj * BN + n) (T * d) := by
  have hloop := dpasProg_correct A B (ti * BM) (tj * BN) d T s hInit
  have hepi := epilogueLd_correct (base + ti * BM * ldC + tj * BN) ldC BN BM hBN hldC
    mem0 (xrun A B (ti * BM) (tj * BN) d (dpasProg T) (7 * T + 3) s).acc
  dsimp only at hepi ⊢
  refine ⟨hloop.1, hepi.1, ?_⟩
  intro m hm n hn
  rw [hepi.2 m hm n hn, hloop.2 m n]

/-- If every scheduled tile's C block holds `dotMat`, the stitched matrix
satisfies the GEMM specification. -/
theorem gemmSpecW_of_tilesExecuted (A B : Nat → Nat → Word) (M N K BM BN ldC : Nat)
    (hBM : 0 < BM) (hBN : 0 < BN) (base : Nat)
    (memOf : Nat → Nat → Nat → Word)
    (hTiles : ∀ ti tj, (ti, tj) ∈ tileSchedule M N BM BN →
      ∀ m < BM, ∀ n < BN,
        memOf ti tj (base + ti * BM * ldC + tj * BN + m * ldC + n) =
          dotMat A B (ti * BM + m) (tj * BN + n) K) :
    GemmSpecW A B (fun x y => memOf (x / BM) (y / BN) (base + x * ldC + y)) M N K := by
  intro x hx y hy
  dsimp only
  have hti : x / BM < numTiles M BM := div_lt_numTiles M BM x hBM hx
  have htj : y / BN < numTiles N BN := div_lt_numTiles N BN y hBN hy
  have hmem : (x / BM, y / BN) ∈ tileSchedule M N BM BN :=
    mem_tileSchedule_of_lt M N BM BN (x / BM) (y / BN) hti htj
  have hxle : x % BM < BM := Nat.mod_lt _ hBM
  have hyle : y % BN < BN := Nat.mod_lt _ hBN
  have hxdec : x / BM * BM + x % BM = x := by
    simpa [Nat.mul_comm] using Nat.div_add_mod x BM
  have hydec : y / BN * BN + y % BN = y := by
    simpa [Nat.mul_comm] using Nat.div_add_mod y BN
  have h := hTiles (x / BM) (y / BN) hmem (x % BM) hxle (y % BN) hyle
  rw [hxdec, hydec] at h
  have haddr : x / BM * BM * ldC + x % BM * ldC = x * ldC := by
    rw [← Nat.add_mul, hxdec]
  have hmemEq : memOf (x / BM) (y / BN) (base + x * ldC + y) =
      memOf (x / BM) (y / BN)
        (base + x / BM * BM * ldC + y / BN * BN + x % BM * ldC + y % BN) := by
    congr 1
    omega
  rw [hmemEq]
  exact h

/-- The SYCL-TLA `256 x 256` workgroup shape: executed tiles cover the whole
GEMM and the stitched output satisfies `GemmSpecW`. -/
theorem tlaXeF16_gemm_executed (A B : Nat → Nat → Word) (M N K : Nat) (base ldC : Nat)
    (memOf : Nat → Nat → Nat → Word)
    (hTiles : ∀ ti tj, (ti, tj) ∈ tileSchedule M N 256 256 →
      ∀ m < 256, ∀ n < 256,
        memOf ti tj (base + ti * 256 * ldC + tj * 256 + m * ldC + n) =
          dotMat A B (ti * 256 + m) (tj * 256 + n) K) :
    GemmSpecW A B (fun x y => memOf (x / 256) (y / 256) (base + x * ldC + y)) M N K :=
  gemmSpecW_of_tilesExecuted A B M N K 256 256 ldC (by decide) (by decide) base memOf hTiles

end IntelGpu
