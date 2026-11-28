-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.VectorAddLoopProgram
public import Intel.LoopDwordStep

@[expose] public section

/-!
# The increment add

At PC 25 the loop adds the work-size stride to every carried 64-bit ID.
-/

namespace IntelGpu

noncomputable section

def vaLoopIncAdd : List RInstr :=
  [ .add 32 ⟨72, 0, 0, 1, 1, 1⟩ ⟨59, 0, 0, 1, 1, 0⟩ ⟨67, 0, 0, 0, 1, 0⟩ ]

theorem vaLoopIncAdd_prefix :
    vaLoopProgram[25]? = some (.add 32 ⟨72, 0, 0, 1, 1, 1⟩
      ⟨59, 0, 0, 1, 1, 0⟩ ⟨67, 0, 0, 0, 1, 0⟩) := by decide

structure VaLoopIncPre (s : RealState) (old : Nat → Addr) (stride : Addr) : Prop where
  oldReg : ∀ l, s.regs 59 l = old l
  strideReg : s.regs 67 0 = stride

theorem vaLoopIncAdd_value (s : RealState) (old : Nat → Addr) (stride : Addr)
    (h : VaLoopIncPre s old stride) (l : Nat) :
    (runRealWith stepLoop s vaLoopIncAdd).regs 72 l = old l + stride := by
  unfold vaLoopIncAdd runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  simp [stepLoop, stepVAL, stepWith, writeVecWith, setReg, readSrcWith,
    readRegWith, srcIndex, vaLoopAlias, vaLoopRegType, isWideOf, RegType.is64, binOpWide,
    h.oldReg, h.strideReg]

theorem vaLoopIncAdd_preserves49 (s : RealState) (j : Nat) :
    (runRealWith stepLoop s vaLoopIncAdd).regs 49 j = s.regs 49 j := by
  unfold vaLoopIncAdd runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  simp [stepLoop, stepVAL, stepWith, writeVecWith, setReg, vaLoopAlias]

end
end IntelGpu
