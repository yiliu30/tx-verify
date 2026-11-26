-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.LoopP3
public import Intel.VectorAddLoopProgram

@[expose] public section

/-!
# Executing the decoded PC 8..16 prefix

`vaLoopProgram` starts with the prologue and the address computation, then
carries the real M1/M5 packs and the first guard block at PC 8..16. This module
connects that concrete slice of the decoded program to `vaLoopP3_packed_full`,
so the per-lane predicate `P3` is proved for the actual instructions rather
than only for a hand-written list.
-/

namespace IntelGpu

noncomputable section

/-- The nine decoded instructions at PC 8..16: both packs plus the first guard. -/
def vaLoopP3Prefix : List RInstr :=
  vaPackLow ++ vaPackHigh ++ vaGuardBlock

/-- The decoded slice at PC 8..16 is exactly the pack/guard prefix. -/
theorem vaLoopProgram_prefix_eq :
    (vaLoopProgram.drop 8).take 9 = vaLoopP3Prefix := by
  decide

/-- Running the decoded prefix sets `P3` to the lexicographic loop guard. -/
theorem vaLoopP3_exec (s : RealState) (ids : Nat → Addr) (sizeLo sizeHi : Word)
    (j : Nat) (hj : j < 24) (hid : ∀ l, s.regs 59 l = ids l)
    (hslo : low32 (s.regs 49 0) = sizeLo) (hshi : low32 (s.regs 49 1) = sizeHi) :
    (runRealWith stepLoop s vaLoopP3Prefix).preds 3 j =
      vaLoopGuard (ids j) (vaLoopSize sizeLo sizeHi) := by
  simp only [vaLoopP3Prefix, runRealWith_append]
  exact vaLoopP3_packed_full s ids sizeLo sizeHi j hj hid hslo hshi

/-- The same fact stated on the decoded program slice itself. -/
theorem vaLoopProgram_prefix_exec (s : RealState) (ids : Nat → Addr)
    (sizeLo sizeHi : Word) (j : Nat) (hj : j < 24)
    (hid : ∀ l, s.regs 59 l = ids l)
    (hslo : low32 (s.regs 49 0) = sizeLo) (hshi : low32 (s.regs 49 1) = sizeHi) :
    (runRealWith stepLoop s ((vaLoopProgram.drop 8).take 9)).preds 3 j =
      vaLoopGuard (ids j) (vaLoopSize sizeLo sizeHi) := by
  rw [vaLoopProgram_prefix_eq]
  exact vaLoopP3_exec s ids sizeLo sizeHi j hj hid hslo hshi

end
end IntelGpu
