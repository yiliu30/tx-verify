-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Mainloop
public import Intel.EpilogueLd
public import Intel.TlaInstance

@[expose] public section

/-!
# One output tile, fully executed

The mainloop of stage 25 and the strided epilogue of stage 22 are separate
programs with separate proofs. This module runs them back to back, so a single
output tile goes from global memory to its C block in one executed pipeline.

- `mainloop_epilogue`: mainloop, then epilogue, leaves `dotMat` in the tile's C
  block.
- `tileSpec_of_mainloop`: the same fact as `TileSpec`, so the stage-15/23
  assembly applies.
-/

namespace IntelGpu

/-- A full tile: mainloop over `T` slabs, then the strided epilogue. -/
theorem mainloop_epilogue (g : Geom) (A B : Nat → Nat → Word) (mem : Nat → Word)
    (hA : ∀ row col, mem (g.aBase + row * g.ldA + col) = A row col)
    (hB : ∀ row col, mem (g.bBase + row * g.ldB + col) = B row col)
    (T : Nat) (epBase ldC : Nat) (mem0 : Nat → Word)
    (hN : 0 < g.N) (hldC : g.N ≤ ldC) :
    let s1 := krun g (mainloopProg T) (8 * T + 3) (kHead mem (fun _ _ => 0))
    let e := lrun (epBase + g.i * ldC + g.j) ldC g.N (epilogueProg (g.M * g.N))
      (5 * (g.M * g.N) + 3) (eHead mem0 s1.acc)
    s1.halted = true ∧ e.halted = true ∧
      ∀ m < g.M, ∀ n < g.N,
        e.mem (epBase + (g.i + m) * ldC + (g.j + n)) =
          dotMat A B (g.i + m) (g.j + n) (T * g.d) := by
  have hloop := mainloop_correct g A B mem hA hB T
  have hepi := epilogueLd_correct (epBase + g.i * ldC + g.j) ldC g.N g.M hN hldC mem0
    (krun g (mainloopProg T) (8 * T + 3) (kHead mem (fun _ _ => 0))).acc
  dsimp only at hloop hepi ⊢
  refine ⟨hloop.1, hepi.1, ?_⟩
  intro m hm n hn
  have hraw := hepi.2 m hm n hn
  have hbase : epBase + g.i * ldC + g.j + m * ldC + n =
      epBase + (g.i + m) * ldC + (g.j + n) := by
    rw [Nat.add_mul]
    omega
  rw [hbase] at hraw
  rw [hraw, hloop.2.2 m hm n hn]

/-- The executed tile satisfies `TileSpec`, so the tile assembly of stages 15
and 23 applies to it. -/
theorem tileSpec_of_mainloop (g : Geom) (A B : Nat → Nat → Word)
    (T : Nat) (C : Nat → Nat → Word) (ti tj : Nat)
    (hi : g.i = ti * g.M) (hj : g.j = tj * g.N)
    (hC : ∀ m < g.M, ∀ n < g.N,
      C (g.i + m) (g.j + n) = dotMat A B (g.i + m) (g.j + n) (T * g.d)) :
    TileSpec A B C (ti * g.M + g.M) (tj * g.N + g.N) (T * g.d) g.M g.N ti tj := by
  intro m hm n hn _ _
  have h := hC m hm n hn
  rw [← hi, ← hj]
  exact h

end IntelGpu
