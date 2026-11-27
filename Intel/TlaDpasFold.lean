-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaDpasExec

@[expose] public section

/-!
# Composing SYCL-TLA DPAS steps

`Intel.TlaDpasExec` executes one DPAS as an 8x8 depth-16 slab on each of the
two accumulator blocks. This module composes two real steps of the SYCL-TLA
GEMM chain. The first two instructions are

```
dpas.8x8 (16|M0) r21:f r13:f r64:bf r30.0:bf
dpas.8x8 (16|M0) r21:f r13:f r64:bf r34.0:bf
```

so the second step reads A at `r34` and B at `r64` after the first step wrote
the accumulator blocks `r21..r28` and `r13..r20`. Those blocks are disjoint
from the source registers, so the second step's operands are unchanged. The
`tlaDpasRun_two_acc0` proves the first accumulator receives the
initial block plus the two slabs, in order.
-/

namespace IntelGpu

/-- The first real DPAS: `r21/r13` accumulate, B is `r64`, A is `r30`. -/
def tlaDpas1 : TlaDpas := ⟨21, 13, 64, 30⟩

/-- The second real DPAS: same accumulators and B, A advances to `r34`. -/
def tlaDpas2 : TlaDpas := ⟨21, 13, 64, 34⟩

theorem tileCDisjoint_21_13 : TileCDisjoint 21 13 := by
  intro r e h
  unfold inTileC at h
  omega

theorem tileCDisjoint_13_21 : TileCDisjoint 13 21 :=
  TileCDisjoint_symm tileCDisjoint_21_13

/-- A read above a written C block is unchanged. -/
theorem readTileA_writeTileC_above (rf : RegFile) (C : Nat → Nat → Word)
    (readBase writeBase m k : Nat) (h : writeBase + 8 ≤ readBase + k) :
    readTileA (writeTileC rf writeBase C) readBase m k =
      readTileA rf readBase m k := by
  unfold readTileA writeTileC inTileC
  have hnot : ¬ (writeBase ≤ readBase + k ∧
      readBase + k < writeBase + 8 ∧ m < 8) := by
    omega
  simp [hnot]

/-- The same for a B read. -/
theorem readTileB_writeTileC_above (rf : RegFile) (C : Nat → Nat → Word)
    (readBase sub writeBase k n : Nat) (h : writeBase + 8 ≤ readBase + n) :
    readTileB (writeTileC rf writeBase C) readBase sub k n =
      readTileB rf readBase sub k n := by
  unfold readTileB writeTileC inTileC
  have hnot : ¬ (writeBase ≤ readBase + n ∧
      readBase + n < writeBase + 8 ∧ sub + k < 8) := by
    omega
  simp [hnot]

/-- A source read above the two accumulator blocks is unchanged by one step. -/
theorem readTileA_tlaDpasStep (rf : RegFile) (srcB srcA readBase m k : Nat)
    (h : 29 ≤ readBase + k) :
    readTileA (tlaDpasStep rf 21 13 srcB srcA) readBase m k =
      readTileA rf readBase m k := by
  unfold tlaDpasStep
  rw [readTileA_writeTileC_above _ _ readBase 13 m k (by omega)]
  rw [readTileA_writeTileC_above _ _ readBase 21 m k (by omega)]

/-- The same for the B source. -/
theorem readTileB_tlaDpasStep (rf : RegFile) (srcB srcA readBase sub k n : Nat)
    (h : 29 ≤ readBase + n) :
    readTileB (tlaDpasStep rf 21 13 srcB srcA) readBase sub k n =
      readTileB rf readBase sub k n := by
  unfold tlaDpasStep
  rw [readTileB_writeTileC_above _ _ readBase sub 13 k n (by omega)]
  rw [readTileB_writeTileC_above _ _ readBase sub 21 k n (by omega)]

/-- Function-level form of the A frame. -/
theorem readTileA_tlaDpasStep_fun (rf : RegFile) (srcB srcA readBase : Nat)
    (h : 29 ≤ readBase) :
    readTileA (tlaDpasStep rf 21 13 srcB srcA) readBase =
      readTileA rf readBase := by
  funext m k
  exact readTileA_tlaDpasStep rf srcB srcA readBase m k (by omega)

/-- Function-level form of the B frame. -/
theorem readTileB_tlaDpasStep_fun (rf : RegFile) (srcB srcA readBase sub : Nat)
    (h : 29 ≤ readBase) :
    readTileB (tlaDpasStep rf 21 13 srcB srcA) readBase sub =
      readTileB rf readBase sub := by
  funext k n
  exact readTileB_tlaDpasStep rf srcB srcA readBase sub k n (by omega)

/-- The first accumulator after the first two real DPAS steps. -/
theorem tlaDpasRun_two_acc0 (rf : RegFile) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (tlaDpasRun [tlaDpas1, tlaDpas2] rf) 21 m n =
      readTileC rf 21 m n +
        dpasSlab 16 (readTileA rf 30) (readTileB rf 64 0) m n +
        dpasSlab 16 (readTileA rf 34) (readTileB rf 64 0) m n := by
  unfold tlaDpasRun tlaDpasStepOf tlaDpas1 tlaDpas2
  simp only [List.foldl_cons, List.foldl_nil]
  rw [tlaDpasStep_acc0 _ _ _ _ _ tileCDisjoint_21_13 m n hm hn]
  simp only [tlaSlab]
  rw [tlaDpasStep_acc0 _ _ _ _ _ tileCDisjoint_21_13 m n hm hn]
  rw [readTileA_tlaDpasStep_fun _ _ _ 34 (by omega)]
  rw [readTileB_tlaDpasStep_fun _ _ _ 64 0 (by omega)]
  simp [tlaSlab, BitVec.add_assoc]

/-- The second accumulator after the first two real DPAS steps. -/
theorem tlaDpasRun_two_acc1 (rf : RegFile) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (tlaDpasRun [tlaDpas1, tlaDpas2] rf) 13 m n =
      readTileC rf 13 m n +
        dpasSlab 16 (readTileA rf 30) (readTileB rf 64 0) m n +
        dpasSlab 16 (readTileA rf 34) (readTileB rf 64 0) m n := by
  unfold tlaDpasRun tlaDpasStepOf tlaDpas1 tlaDpas2
  simp only [List.foldl_cons, List.foldl_nil]
  rw [tlaDpasStep_acc1 _ _ _ _ _ m n hm hn]
  simp only [tlaSlab]
  rw [tlaDpasStep_acc1 _ _ _ _ _ m n hm hn]
  rw [readTileA_tlaDpasStep_fun _ _ _ 34 (by omega)]
  rw [readTileB_tlaDpasStep_fun _ _ _ 64 0 (by omega)]
  simp [tlaSlab, BitVec.add_assoc]

end IntelGpu
