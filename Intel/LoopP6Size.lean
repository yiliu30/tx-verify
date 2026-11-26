-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.LoopPackIncBoth

@[expose] public section

/-!
# The increment packs leave the work size alone

`vaPackIncLow` writes only `V0075` and `vaPackIncHigh` only `V0076`. The P6
guard reads the work size from `V0049`, so composing the two increment packs
must leave every dword of that register untouched. This module proves the
per-instruction frames, the composed frame, and its `low32` corollary for the
size dwords the guard consumes.
-/

namespace IntelGpu

noncomputable section

theorem inc_low1_preserves49 (s : RealState) (j : Nat) :
    (stepLoop s (.mov e1Loop dst75a src74a)).regs 49 j = s.regs 49 j := by
  simpa [vaLoopAlias] using stepLoop_mov_preserves_reg (s := s) (e := e1Loop) (dst := dst75a)
    (src := src74a) (r := 49) (j := j) (by decide)

theorem inc_low2_preserves49 (s : RealState) (j : Nat) :
    (stepLoop s (.movMasked e2Loop dst75b src74b)).regs 49 j = s.regs 49 j := by
  simpa [vaLoopAlias] using stepLoop_movMasked_preserves_reg (s := s) (e := e2Loop) (dst := dst75b)
    (src := src74b) (r := 49) (j := j) (by decide)

theorem inc_high1_preserves49 (s : RealState) (j : Nat) :
    (stepLoop s (.mov e1Loop dst76a src74aHigh)).regs 49 j = s.regs 49 j := by
  simpa [vaLoopAlias] using stepLoop_mov_preserves_reg (s := s) (e := e1Loop) (dst := dst76a)
    (src := src74aHigh) (r := 49) (j := j) (by decide)

theorem inc_high2_preserves49 (s : RealState) (j : Nat) :
    (stepLoop s (.movMasked e2Loop dst76b src74bHigh)).regs 49 j = s.regs 49 j := by
  simpa [vaLoopAlias] using stepLoop_movMasked_preserves_reg (s := s) (e := e2Loop) (dst := dst76b)
    (src := src74bHigh) (r := 49) (j := j) (by decide)

/-- Composing both increment packs leaves every dword of `V0049` intact. -/
theorem vaPackIncBoth_preserves49 (s : RealState) (j : Nat) :
    (runRealWith stepLoop (runRealWith stepLoop s vaPackIncLow) vaPackIncHigh).regs 49 j =
      s.regs 49 j := by
  unfold vaPackIncLow vaPackIncHigh runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  rw [inc_high2_preserves49, inc_high1_preserves49, inc_low2_preserves49,
    inc_low1_preserves49]

/-- The guard's `low32` size dwords survive the increment packs. -/
theorem vaPackIncBoth_preserves49_low32 (s : RealState) (d : Nat) :
    low32 ((runRealWith stepLoop (runRealWith stepLoop s vaPackIncLow) vaPackIncHigh).regs 49 d) =
      low32 (s.regs 49 d) := by
  rw [vaPackIncBoth_preserves49]

end
end IntelGpu
