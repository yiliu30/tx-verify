-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.VectorAddLoopBody
public meta import Std.Tactic.BVDecide.Reflect

@[expose] public section

/-!
# The loop vector add's first continuation predicate

The five instructions at PCs 12-16 combine low/high comparisons into the
64-bit `id < globalSize` guard. This module proves that composition from the
packed register halves.
-/

namespace IntelGpu

noncomputable section

/-- The five guard instructions after the initial pack. -/
def vaGuardBlock : List RInstr :=
  [ .cmpLtReg 32 1 ⟨64, 0, 0, 1, 1, 0⟩ ⟨65, 0, 0, 0, 1, 0⟩,
    .cmpEqReg 32 2 ⟨63, 0, 0, 1, 1, 0⟩ ⟨49, 0, 1, 0, 1, 0⟩,
    .predAnd 32 2 2 1,
    .cmpLtReg 32 3 ⟨66, 0, 0, 1, 1, 0⟩ ⟨65, 0, 1, 0, 1, 0⟩,
    .predOr 32 3 3 2 ]

/-- Lexicographic 32-bit comparison used by the assembly. -/
def vaGuard32 (lo hi sizeLo sizeHi : Word) : Bool :=
  decide (hi < sizeHi) || (decide (hi = sizeHi) && decide (lo < sizeLo))

theorem vaLoopP3 (s : RealState) (lane : Nat) (lo hi sizeLo sizeHi : Word)
    (hl : lane < 32)
    (hlo : low32 (s.regs 62 lane) = lo)
    (hhi : low32 (s.regs 63 lane) = hi)
    (hslo : low32 (s.regs 49 0) = sizeLo)
    (hshi : low32 (s.regs 49 1) = sizeHi) :
    (runVAL s vaGuardBlock).preds 3 lane = vaGuard32 lo hi sizeLo sizeHi := by
  unfold vaGuardBlock runVAL stepVAL
  have h32 : (32 : Exec).size = 32 := rfl
  simp [runRealWith, stepWith, h32, hl, readRegWith, readSrcWith, srcIndex,
    vaLoopAlias, vaGuard32, hlo, hhi, hslo, hshi]

theorem vaGuard32_eq (lo hi sizeLo sizeHi : Word) :
    vaGuard32 lo hi sizeLo sizeHi =
      vaLoopGuard (vaLoopSize lo hi) (vaLoopSize sizeLo sizeHi) := by
  unfold vaGuard32 vaLoopGuard vaLoopSize
  bv_decide

theorem vaLoopP3_guard (s : RealState) (lane : Nat) (lo hi sizeLo sizeHi : Word)
    (hl : lane < 32)
    (hlo : low32 (s.regs 62 lane) = lo)
    (hhi : low32 (s.regs 63 lane) = hi)
    (hslo : low32 (s.regs 49 0) = sizeLo)
    (hshi : low32 (s.regs 49 1) = sizeHi) :
    (runVAL s vaGuardBlock).preds 3 lane =
      vaLoopGuard (vaLoopSize lo hi) (vaLoopSize sizeLo sizeHi) := by
  rw [vaLoopP3 s lane lo hi sizeLo sizeHi hl hlo hhi hslo hshi, vaGuard32_eq]

end
end IntelGpu
