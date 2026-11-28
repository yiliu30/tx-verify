-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaInstance

@[expose] public section

/-!
# Partial K tail in the DPAS mainloop

A GEMM whose depth is not a multiple of the atom depth ends with a partial
slab: the last K tile only has `r` live depth slots. On Xe that is the same
instruction with the remaining slots masked off, so the tail is a `dpas` of
live depth `r` rather than a separate masked datapath.

- `dpasTail`: `T` full atom-depth slabs followed by one `r`-deep slab.
- `dpasTail_correct`: the run lands exactly on `dotMat` at depth `T * d + r`.
- `tileSpec_of_dpasTail`, `tla_gemm_spec_tail`: the instance layer without the
  "K is a multiple of the atom depth" assumption.
- `tlaXeF16_gemm_spec_tail`: every K, using `K / 16` full slabs and `K % 16`
  live tail slots.
-/

namespace IntelGpu

/-- `T` full depth slabs followed by one slab with `r` live slots. -/
def dpasTail (A B : Nat → Nat → Word) (i j d T r : Nat) (C : Nat → Nat → Word) :
    Nat → Nat → Word :=
  dpas r (fun k m => A (i + m) (T * d + k)) (fun k n => B (T * d + k) (j + n))
    (dpasRun A B i j d T C)

theorem dpasTail_correct (A B : Nat → Nat → Word) (i j d T r m n : Nat) :
    dpasTail A B i j d T r (fun _ _ => 0) m n = dotMat A B (i + m) (j + n) (T * d + r) := by
  unfold dpasTail dpas
  rw [dpasRun_acc, dpasSlab_eq_dotMatFrom A B i j (T * d) r m n]
  simp only [dotMat]
  rw [dotMatFrom_append]
  rw [show 0 + T * d = T * d by omega]
  simp

/-- A tile whose C block was produced by `T` full slabs plus an `r`-deep tail
satisfies `TileSpec` when `K = T * d + r`, with no divisibility requirement. -/
theorem tileSpec_of_dpasTail (A B C : Nat → Nat → Word) (M N K d T r BM BN ti tj : Nat)
    (hK : K = T * d + r)
    (hC : ∀ m n,
      C (ti * BM + m) (tj * BN + n) =
        dpasTail A B (ti * BM) (tj * BN) d T r (fun _ _ => 0) m n) :
    TileSpec A B C M N K BM BN ti tj := by
  intro m _ n _ _ _
  rw [hC m n, dpasTail_correct A B (ti * BM) (tj * BN) d T r m n, ← hK]

/-- Composing the partial-tail tile proof with the stage-15 scheduler. -/
theorem tla_gemm_spec_tail (A B C : Nat → Nat → Word) (M N K d T r BM BN : Nat)
    (hBM : 0 < BM) (hBN : 0 < BN) (hK : K = T * d + r)
    (hTiles : ∀ ti tj, (ti, tj) ∈ tileSchedule M N BM BN →
      ∀ m n,
        C (ti * BM + m) (tj * BN + n) =
          dpasTail A B (ti * BM) (tj * BN) d T r (fun _ _ => 0) m n) :
    GemmSpecW A B C M N K :=
  gemmSpecW_of_schedule A B C M N K BM BN hBM hBN
    (fun ti tj hmem => tileSpec_of_dpasTail A B C M N K d T r BM BN ti tj hK
      (hTiles ti tj hmem))

/-- The `256 x 256 x 32` instance for an arbitrary depth `K`: `K / 16` full
atom-depth slabs plus a tail with `K % 16` live slots. -/
theorem tlaXeF16_gemm_spec_tail (A B C : Nat → Nat → Word) (M N K : Nat)
    (hTiles : ∀ ti tj, (ti, tj) ∈ tileSchedule M N tlaXeF16.wgM tlaXeF16.wgN →
      ∀ m n,
        C (ti * tlaXeF16.wgM + m) (tj * tlaXeF16.wgN + n) =
          dpasTail A B (ti * tlaXeF16.wgM) (tj * tlaXeF16.wgN) tlaXeF16.atomK
            (K / tlaXeF16.atomK) (K % tlaXeF16.atomK) (fun _ _ => 0) m n) :
    GemmSpecW A B C M N K := by
  have hK : K = K / tlaXeF16.atomK * tlaXeF16.atomK + K % tlaXeF16.atomK := by
    have h := Nat.div_add_mod K tlaXeF16.atomK
    rw [Nat.mul_comm] at h
    exact h.symm
  exact tla_gemm_spec_tail A B C M N K tlaXeF16.atomK (K / tlaXeF16.atomK)
    (K % tlaXeF16.atomK) tlaXeF16.wgM tlaXeF16.wgN (by decide) (by decide) hK hTiles

end IntelGpu
