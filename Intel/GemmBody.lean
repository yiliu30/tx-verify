-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Gemm

@[expose] public section

/-!
# GEMM loop body (one lane)

The modeled IGC GEMM loop body has the shape:

```
load.ugm.d32.a64  A
load.ugm.d32.a64  B
mul/add           sum += A * B
```

This module models the straight-line body for one lane and proves that it
updates the accumulator by exactly `A * B`. Loop control and pointer
increment are added in the next stage.
-/

namespace IntelGpu

/-- One GEMM body: load A, load B, multiply, accumulate into register 4. -/
def gemmBody : List Instr :=
  [.load32 1 0, .load32 2 1, .mul 3 1 2, .add 4 4 3]

structure GemmBodyPre (s : State) (aPtr bPtr : Addr) (sum a b : Word) : Prop where
  aAddr : s.addrRegs 0 = aPtr
  bAddr : s.addrRegs 1 = bPtr
  sumReg : s.regs 4 = sum
  aMem : load32 s.mem aPtr.toNat = a
  bMem : load32 s.mem bPtr.toNat = b
  running : s.halted = false

theorem gemmBody_correct (s : State) (aPtr bPtr : Addr) (sum a b : Word)
    (h : GemmBodyPre s aPtr bPtr sum a b) :
    let s' := run s gemmBody
    s'.regs 4 = sum + a * b ∧ s'.mem = s.mem ∧ s'.halted = s.halted := by
  unfold gemmBody run
  simp [step, h.aAddr, h.bAddr, h.sumReg, h.aMem, h.bMem, h.running]

end IntelGpu
