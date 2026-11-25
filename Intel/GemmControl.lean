-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.ControlData
public import Intel.GemmBody

@[expose] public section

/-!
# GEMM body through the data/control layer

The stage-3 `gemmBody` is replayed through `DInstr`/`DState`. This proves that
the data/control execution layer refines the straight-line GEMM body before
the full loop invariant is added.
-/

namespace IntelGpu

def gemmBodyD : List DInstr :=
  [.data (.load32 1 0), .data (.load32 2 1),
   .data (.mul 3 1 2), .data (.add 4 4 3)]

structure GemmBodyDPre (s : DState) (aPtr bPtr : Addr) (sum a b : Word) : Prop where
  pc0 : s.pc = 0
  aAddr : s.data.addrRegs 0 = aPtr
  bAddr : s.data.addrRegs 1 = bPtr
  sumReg : s.data.regs 4 = sum
  aMem : load32 s.data.mem aPtr.toNat = a
  bMem : load32 s.data.mem bPtr.toNat = b

theorem gemmBodyD_correct (s : DState) (aPtr bPtr : Addr) (sum a b : Word)
    (h : GemmBodyDPre s aPtr bPtr sum a b) :
    let s' := drun gemmBodyD 4 s
    s'.data.regs 4 = sum + a * b ∧
    s'.data.mem = s.data.mem ∧ s'.data.halted = s.data.halted := by
  unfold gemmBodyD drun
  simp [dstep, step, h.pc0, h.aAddr, h.bAddr, h.sumReg, h.aMem, h.bMem]

end IntelGpu
