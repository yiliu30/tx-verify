-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.LoopPackHigh

@[expose] public section

/-!
# Executing both real packs

Composes the low and high M1/M5 packs and proves both register halves survive.
-/

namespace IntelGpu

noncomputable section

theorem low_second_preserves59 (s : RealState) (j : Nat) :
    (stepLoop s (.movMasked e2Loop dst62b src61b)).regs 59 j = s.regs 59 j := by
  change (writeMaskedWith vaLoopAlias s dst62b e2Loop
    (fun i => zext (dwordAtQ s 59 (srcIndexRegion src61b i)))).regs 59 j = s.regs 59 j
  exact writeMaskedWith_other_reg vaLoopAlias s dst62b e2Loop _ 59 j (by decide)

theorem vaPackLow_preserves59 (s : RealState) (j : Nat) :
    (runRealWith stepLoop s vaPackLow).regs 59 j = s.regs 59 j := by
  unfold vaPackLow runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  rw [low_second_preserves59]
  exact stepLoop_first_preserves59 s j

theorem high_first_preserves62 (s : RealState) (j : Nat) :
    (stepLoop s (.mov e1Loop dst63a src61aHigh)).regs 62 j = s.regs 62 j := by
  change (writeMaskedWith vaLoopAlias s dst63a e1Loop
    (fun i => zext (dwordAtQ s 59 (srcIndexRegion src61aHigh i)))).regs 62 j = s.regs 62 j
  exact writeMaskedWith_other_reg vaLoopAlias s dst63a e1Loop _ 62 j (by decide)

theorem high_second_preserves62 (s : RealState) (j : Nat) :
    (stepLoop s (.movMasked e2Loop dst63b src61bHigh)).regs 62 j = s.regs 62 j := by
  change (writeMaskedWith vaLoopAlias s dst63b e2Loop
    (fun i => zext (dwordAtQ s 59 (srcIndexRegion src61bHigh i)))).regs 62 j = s.regs 62 j
  exact writeMaskedWith_other_reg vaLoopAlias s dst63b e2Loop _ 62 j (by decide)

theorem vaPackHigh_preserves62 (s : RealState) (j : Nat) :
    (runRealWith stepLoop s vaPackHigh).regs 62 j = s.regs 62 j := by
  unfold vaPackHigh runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  rw [high_second_preserves62]
  exact high_first_preserves62 s j

/-- Running both packs yields the low and high dwords of the carried IDs. -/
theorem vaPackBoth_value (s : RealState) (ids : Nat → Addr) (j : Nat) (hj : j < 24)
    (hid : ∀ l, s.regs 59 l = ids l) :
    low32 ((runRealWith stepLoop (runRealWith stepLoop s vaPackLow) vaPackHigh).regs 62 j) =
        (ids j).truncate 32 ∧
    low32 ((runRealWith stepLoop (runRealWith stepLoop s vaPackLow) vaPackHigh).regs 63 j) =
        ((ids j) >>> 32).truncate 32 := by
  let s1 := runRealWith stepLoop s vaPackLow
  have hlow : low32 (s1.regs 62 j) = (ids j).truncate 32 := by
    dsimp [s1]
    exact vaPackLow_value s ids j hj hid
  have h59 : ∀ k, s1.regs 59 k = ids k := by
    intro k
    dsimp [s1]
    rw [vaPackLow_preserves59]
    exact hid k
  have hhigh : low32 ((runRealWith stepLoop s1 vaPackHigh).regs 63 j) =
      ((ids j) >>> 32).truncate 32 := by
    exact vaPackHigh_value s1 ids j hj h59
  have hpres : (runRealWith stepLoop s1 vaPackHigh).regs 62 j = s1.regs 62 j := by
    exact vaPackHigh_preserves62 s1 j
  refine ⟨?_, hhigh⟩
  dsimp [s1] at hlow ⊢
  rw [hpres]
  exact hlow

end
end IntelGpu
