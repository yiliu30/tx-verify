-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.LoopPackIncHigh

@[expose] public section

/-!
# Both increment packs

Composes the increment low/high packs and proves their halves coexist.
-/

namespace IntelGpu

noncomputable section

theorem inc_low_second_preserves72 (s : RealState) (j : Nat) :
    (stepLoop s (.movMasked e2Loop dst75b src74b)).regs 72 j = s.regs 72 j := by
  have h := stepLoop_movMasked_preserves_reg (s := s) (e := e2Loop) (dst := dst75b)
    (src := src74b) (r := 72) (j := j) (by decide)
  simpa [vaLoopAlias] using h

theorem vaPackIncLow_preserves72 (s : RealState) (j : Nat) :
    (runRealWith stepLoop s vaPackIncLow).regs 72 j = s.regs 72 j := by
  unfold vaPackIncLow runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  rw [inc_low_second_preserves72]
  have h := stepLoop_mov_preserves_reg (s := s) (e := e1Loop) (dst := dst75a)
    (src := src74a) (r := 72) (j := j) (by decide)
  simpa [vaLoopAlias] using h

theorem inc_high_first_preserves75 (s : RealState) (j : Nat) :
    (stepLoop s (.mov e1Loop dst76a src74aHigh)).regs 75 j = s.regs 75 j := by
  have h := stepLoop_mov_preserves_reg (s := s) (e := e1Loop) (dst := dst76a)
    (src := src74aHigh) (r := 75) (j := j) (by decide)
  simpa [vaLoopAlias] using h

theorem inc_high_second_preserves75 (s : RealState) (j : Nat) :
    (stepLoop s (.movMasked e2Loop dst76b src74bHigh)).regs 75 j = s.regs 75 j := by
  have h := stepLoop_movMasked_preserves_reg (s := s) (e := e2Loop) (dst := dst76b)
    (src := src74bHigh) (r := 75) (j := j) (by decide)
  simpa [vaLoopAlias] using h

theorem vaPackIncHigh_preserves75 (s : RealState) (j : Nat) :
    (runRealWith stepLoop s vaPackIncHigh).regs 75 j = s.regs 75 j := by
  unfold vaPackIncHigh runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  rw [inc_high_second_preserves75]
  exact inc_high_first_preserves75 s j

theorem vaPackIncBoth_value (s : RealState) (ids : Nat → Addr) (j : Nat) (hj : j < 24)
    (hid : ∀ l, s.regs 72 l = ids l) :
    low32 ((runRealWith stepLoop (runRealWith stepLoop s vaPackIncLow) vaPackIncHigh).regs 75 j) =
        (ids j).truncate 32 ∧
    low32 ((runRealWith stepLoop (runRealWith stepLoop s vaPackIncLow) vaPackIncHigh).regs 76 j) =
        ((ids j) >>> 32).truncate 32 := by
  let s1 := runRealWith stepLoop s vaPackIncLow
  have hlow : low32 (s1.regs 75 j) = (ids j).truncate 32 := by
    dsimp [s1]
    exact vaPackIncLow_value s ids j hj hid
  have h72 : ∀ k, s1.regs 72 k = ids k := by
    intro k
    dsimp [s1]
    rw [vaPackIncLow_preserves72]
    exact hid k
  have hhigh : low32 ((runRealWith stepLoop s1 vaPackIncHigh).regs 76 j) =
      ((ids j) >>> 32).truncate 32 := by
    exact vaPackIncHigh_value s1 ids j hj h72
  have hpres : (runRealWith stepLoop s1 vaPackIncHigh).regs 75 j = s1.regs 75 j := by
    exact vaPackIncHigh_preserves75 s1 j
  refine ⟨?_, hhigh⟩
  dsimp [s1] at hlow ⊢
  rw [hpres]
  exact hlow

end
end IntelGpu
