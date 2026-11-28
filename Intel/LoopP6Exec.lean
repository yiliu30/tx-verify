-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.LoopP6
public import Intel.VectorAddLoopProgram

@[expose] public section

/-!
# Executing the decoded P6 prefix

The nine decoded instructions at PCs 26-34 are the two increment packs followed
by the second guard block. This module connects that program slice to the
packed predicate result in `Intel.LoopP6`.
-/

namespace IntelGpu

noncomputable section

/-- The decoded PCs 26-34 of the loop vector add. -/
def vaLoopP6Prefix : List RInstr :=
  vaPackIncLow ++ vaPackIncHigh ++ vaGuardBlock2

theorem vaLoopProgram_p6_prefix_eq :
    (vaLoopProgram.drop 26).take 9 = vaLoopP6Prefix := by
  unfold vaLoopProgram vaLoopP6Prefix vaPackIncLow vaPackIncHigh vaGuardBlock2
  decide

/-- Running the decoded P6 prefix computes the second continuation predicate. -/
theorem vaLoopP6_exec (s : RealState) (ids : Nat → Addr) (sizeLo sizeHi : Word)
    (j : Nat) (hj : j < 24) (hid : ∀ l, s.regs 72 l = ids l)
    (hslo : low32 (s.regs 49 0) = sizeLo) (hshi : low32 (s.regs 49 1) = sizeHi) :
    (runRealWith stepLoop s vaLoopP6Prefix).preds 6 j =
      vaLoopGuard (ids j) (vaLoopSize sizeLo sizeHi) := by
  rw [vaLoopP6Prefix, runRealWith_append, runRealWith_append]
  exact vaLoopP6_packed_full s ids sizeLo sizeHi j hj hid hslo hshi

/-- The same fact, stated directly on the decoded loop program. -/
theorem vaLoopP6_program_exec (s : RealState) (ids : Nat → Addr) (sizeLo sizeHi : Word)
    (j : Nat) (hj : j < 24) (hid : ∀ l, s.regs 72 l = ids l)
    (hslo : low32 (s.regs 49 0) = sizeLo) (hshi : low32 (s.regs 49 1) = sizeHi) :
    (runRealWith stepLoop s ((vaLoopProgram.drop 26).take 9)).preds 6 j =
      vaLoopGuard (ids j) (vaLoopSize sizeLo sizeHi) := by
  rw [vaLoopProgram_p6_prefix_eq]
  exact vaLoopP6_exec s ids sizeLo sizeHi j hj hid hslo hshi

end
end IntelGpu
