-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaSchedule
public import Intel.TlaLoopCounter
public import Intel.SlmAliasing

@[expose] public section

/-!
# Barrier placement in the mainloop

The mainloop's single `sync.bar` is at PC 1396. This module proves that every
predicated block2d memory operation of the block precedes it and that no
memory operation follows it. Together with the SLM barrier model of stage 139
(`producer_consumer_with_barrier`), this is the schedule fact behind "the
accumulator stores are visible to the next iteration's loads": the block's
stores at PCs 1394/1395 are followed by the barrier, and the tail contains no
further memory traffic.

The concrete exchange pattern is instantiated at the first accumulator store
address `0xF900`.
-/

namespace IntelGpu

set_option maxRecDepth 1000000 in
/-- No predicated block2d operation of the block follows the barrier at
PC 1396. -/
theorem block_b2d_before_bar :
    (blockInstrs.filter (fun p => decide (1396 ≤ p.1) && isB2d p.2)).length = 0 := by
  decide

set_option maxRecDepth 1000000 in
/-- The last predicated block2d operation of the block is at PC 1395. -/
theorem block_b2d_last_pc :
    List.getLast? ((blockInstrs.filter (fun p => isB2d p.2)).map (fun p => p.1)) =
      some 1395 := by
  decide

set_option maxRecDepth 1000000 in
/-- The two accumulator stores sit at PCs 1394 and 1395, before the barrier. -/
theorem block_acc_stores_before_bar :
    blockInstrAt 1394 = some (.predicated "(W) store.ugm.d32x64t.a32"
      ["(1|M0)", "ss[a0.2][r2:1-0xF900]", "r21:4", "{$11}"])
      ∧ blockInstrAt 1395 = some (.predicated "(W) store.ugm.d32x64t.a32"
      ["(1|M0)", "ss[a0.2][r2:1-0xF800]", "r25:4", "{$12}"])
      ∧ blockInstrAt 1396 = some (.predicated "(W) sync.bar" ["0x0"]) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The barrier exchange pattern at the first accumulator store address. -/
theorem mainloop_store_barrier_pattern (ginit sinit : Nat → Word)
    (tileReg dst : Nat) (tile : Word) :
    (wgRun (producerConsumerInitial ginit sinit tileReg tile)
      (producerConsumerProg 0xF900 tileReg dst)).regs 0 dst = tile :=
  producer_consumer_with_barrier ginit sinit 0xF900 tileReg dst tile

/-- Without the barrier the same exchange reads the stale value. -/
theorem mainloop_store_without_barrier_stale (ginit sinit : Nat → Word)
    (tileReg dst : Nat) (tile : Word) :
    (wgRun (producerConsumerInitial ginit sinit tileReg tile)
      (producerConsumerProgNoBarrier 0xF900 tileReg dst)).regs 0 dst =
        sinit 0xF900 :=
  producer_consumer_without_barrier_stale ginit sinit 0xF900 tileReg dst tile

end IntelGpu
