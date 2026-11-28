-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Asm

@[expose] public section

/-!
# GEMM memory body with pointer advance

Adds an address-register immediate instruction and proves one memory GEMM
body: load A, load B, multiply, accumulate, then advance both pointers.
-/

namespace IntelGpu

theorem addAddrImm_addr (s : State) (dst : Nat) (imm : Addr) :
    (step s (.addAddrImm dst imm)).addrRegs dst = s.addrRegs dst + imm := by
  simp [step]

theorem addAddrImm_mem (s : State) (dst : Nat) (imm : Addr) :
    (step s (.addAddrImm dst imm)).mem = s.mem := rfl

def gemmMemoryBody : List Instr :=
  [.load32 1 0, .load32 2 1, .mul 3 1 2, .add 4 4 3,
   .addAddrImm 0 4, .addAddrImm 1 4]

structure GemmMemoryBodyPre (s : State) (aPtr bPtr : Addr) (sum a b : Word) : Prop where
  aAddr : s.addrRegs 0 = aPtr
  bAddr : s.addrRegs 1 = bPtr
  sumReg : s.regs 4 = sum
  aMem : load32 s.mem aPtr.toNat = a
  bMem : load32 s.mem bPtr.toNat = b

theorem gemmMemoryBody_correct (s : State) (aPtr bPtr : Addr) (sum a b : Word)
    (h : GemmMemoryBodyPre s aPtr bPtr sum a b) :
    let s' := run s gemmMemoryBody
    s'.regs 4 = sum + a * b ∧
    s'.addrRegs 0 = aPtr + 4 ∧
    s'.addrRegs 1 = bPtr + 4 ∧
    s'.mem = s.mem := by
  unfold gemmMemoryBody run
  simp [step, h.aAddr, h.bAddr, h.sumReg, h.aMem, h.bMem]

end IntelGpu
