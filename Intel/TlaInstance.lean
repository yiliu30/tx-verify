-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.GemmScheduleProof
public import Intel.GemmDpasLoop

@[expose] public section

/-!
# SYCL-TLA Xe GEMM instance

The tile shape of the Xe DPAS path in SYCL-TLA, taken from
`test/unit/gemm/device/default_gemm_configuration.hpp`:

```
using TileShape = Shape<_256, _256, _32>;
using TiledMma  = TiledMMAHelper<MMA_Atom<XE_8x16x16_F32F16F16F32_TT>, ...>::TiledMMA;
```

so one workgroup tile is `256 x 256` with a K tile of `32`, and one atom is
`8 x 16` with an atom depth of `16` (two atoms deep per K tile).

This module instantiates the verified layers on that shape:

- `tlaXeF16`/`tlaXeBF16`: the shape as data, with atom-count facts.
- `tla_kernelShape`: mainloop budget per workgroup tile.
- `tileSpec_of_dpas`: a tile whose C was produced by a `T`-step DPAS mainloop
  satisfies `TileSpec`.
- `tla_gemm_spec`: composing with the stage-15 scheduler gives `GemmSpecW`
  for the whole GEMM.

Assumptions, stated explicitly rather than modeled:

- K is a multiple of the atom depth, so the last slab needs no masking.
- Global-memory staging into SLM/registers is the stage-16/17 model; the
  instance treats the operands as already in the DPAS tile registers.
- Element types are modeled as 32-bit words, so fp16/bf16 rounding and
  tolerance are out of scope for this statement.
-/

namespace IntelGpu

/-- A SYCL-TLA GEMM tile shape: workgroup tile, K tile, and atom. -/
structure TlaShape where
  wgM : Nat
  wgN : Nat
  kTile : Nat
  atomM : Nat
  atomN : Nat
  atomK : Nat
  deriving Repr

/-- `XE_8x16x16_F32F16F16F32_TT` on a `256 x 256 x 32` workgroup tile. -/
def tlaXeF16 : TlaShape :=
  { wgM := 256, wgN := 256, kTile := 32, atomM := 8, atomN := 16, atomK := 16 }

/-- `XE_8x16x16_F32BF16BF16F32_TT` on the same workgroup tile. -/
def tlaXeBF16 : TlaShape :=
  { wgM := 256, wgN := 256, kTile := 32, atomM := 8, atomN := 16, atomK := 16 }

theorem tlaXeF16_mAtoms : tlaXeF16.wgM = 32 * tlaXeF16.atomM := by decide

theorem tlaXeF16_nAtoms : tlaXeF16.wgN = 16 * tlaXeF16.atomN := by decide

theorem tlaXeF16_kAtoms : tlaXeF16.kTile = 2 * tlaXeF16.atomK := by decide

/-- DPAS instructions issued per workgroup tile: M atoms times N atoms times
K atoms. -/
def tlaDpasPerTile (s : TlaShape) : Nat :=
  (s.wgM / s.atomM) * (s.wgN / s.atomN) * (s.kTile / s.atomK)

theorem tlaXeF16_dpasPerTile : tlaDpasPerTile tlaXeF16 = 1024 := by decide

/-- A tile whose C block was produced by a `T`-step DPAS mainloop at atom depth
`d` satisfies `TileSpec`, provided `K = T * d`. -/
theorem tileSpec_of_dpas (A B C : Nat → Nat → Word) (M N K d T BM BN ti tj : Nat)
    (hK : K = T * d)
    (hC : ∀ m n,
      C (ti * BM + m) (tj * BN + n) =
        dpasRun A B (ti * BM) (tj * BN) d T (fun _ _ => 0) m n) :
    TileSpec A B C M N K BM BN ti tj := by
  intro m _ n _ _ _
  rw [hC m n, dpasRun_correct A B (ti * BM) (tj * BN) d T m n, ← hK]

/-- Every scheduled tile of the SYCL-TLA shape, produced by a DPAS mainloop,
composes to the matrix GEMM specification. -/
theorem tla_gemm_spec (A B C : Nat → Nat → Word) (M N K d T BM BN : Nat)
    (hBM : 0 < BM) (hBN : 0 < BN) (hK : K = T * d)
    (hTiles : ∀ ti tj, (ti, tj) ∈ tileSchedule M N BM BN →
      ∀ m n,
        C (ti * BM + m) (tj * BN + n) =
          dpasRun A B (ti * BM) (tj * BN) d T (fun _ _ => 0) m n) :
    GemmSpecW A B C M N K :=
  gemmSpecW_of_schedule A B C M N K BM BN hBM hBN
    (fun ti tj hmem => tileSpec_of_dpas A B C M N K d T BM BN ti tj hK (hTiles ti tj hmem))

/-- The instance at the SYCL-TLA `256 x 256 x 32` shape: when K is a multiple
of the atom depth `16`, DPAS-produced tiles cover the whole GEMM. -/
theorem tlaXeF16_gemm_spec (A B C : Nat → Nat → Word) (M N K : Nat)
    (hDiv : K % tlaXeF16.atomK = 0)
    (hTiles : ∀ ti tj, (ti, tj) ∈ tileSchedule M N tlaXeF16.wgM tlaXeF16.wgN →
      ∀ m n,
        C (ti * tlaXeF16.wgM + m) (tj * tlaXeF16.wgN + n) =
          dpasRun A B (ti * tlaXeF16.wgM) (tj * tlaXeF16.wgN) tlaXeF16.atomK
            (K / tlaXeF16.atomK) (fun _ _ => 0) m n) :
    GemmSpecW A B C M N K := by
  have hK : K = (K / tlaXeF16.atomK) * tlaXeF16.atomK := by
    have h := Nat.div_add_mod K tlaXeF16.atomK
    rw [hDiv, Nat.add_zero, Nat.mul_comm] at h
    exact h.symm
  exact tla_gemm_spec A B C M N K tlaXeF16.atomK (K / tlaXeF16.atomK)
    tlaXeF16.wgM tlaXeF16.wgN (by decide) (by decide) hK hTiles

/-- One SYCL-TLA K tile is two atom-deep DPAS steps: the executed mainloop
halts after `7 * 2 + 3 = 17` steps with the accumulator at depth `32`. -/
theorem tlaXeF16_kTile_mainloop (A B : Nat → Nat → Word) (i j : Nat) (s : XState)
    (h : XInv A B i j 16 0 s) :
    (xrun A B i j 16 (dpasProg 2) 17 s).halted = true ∧
      ∀ m n, (xrun A B i j 16 (dpasProg 2) 17 s).acc m n =
        dotMat A B (i + m) (j + n) tlaXeF16.kTile := by
  have hres := dpasProg_correct A B i j 16 2 s h
  refine ⟨hres.1, ?_⟩
  intro m n
  rw [hres.2 m n]
  simp [tlaXeF16]

end IntelGpu
