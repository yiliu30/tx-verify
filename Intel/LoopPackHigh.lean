-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.LoopPackExec

@[expose] public section

/-!
# Executing the real M1/M5 high pack

The high-half counterpart of `LoopPackExec`: the M1+M5 moves writing `V0063`
produce the high dwords of the carried IDs for lanes 0..23.
-/

namespace IntelGpu

noncomputable section

def dst63a : Grf := ⟨63, 0, 0, 1, 1, 1⟩
def dst63b : Grf := ⟨63, 1, 0, 1, 1, 1⟩
def src61aHigh : Grf := ⟨61, 0, 1, 2, 1, 0⟩
def src61bHigh : Grf := ⟨61, 2, 1, 2, 1, 0⟩

def vaPackHigh : List RInstr :=
  [ .mov e1Loop dst63a src61aHigh, .movMasked e2Loop dst63b src61bHigh ]

theorem stepLoop_first_high_preserves59 (s : RealState) (j : Nat) :
    (stepLoop s (.mov e1Loop dst63a src61aHigh)).regs 59 j = s.regs 59 j := by
  change (writeMaskedWith vaLoopAlias s dst63a e1Loop
    (fun i => zext (dwordAtQ s 59 (srcIndexRegion src61aHigh i)))).regs 59 j = s.regs 59 j
  exact writeMaskedWith_other_reg vaLoopAlias s dst63a e1Loop _ 59 j (by decide)

theorem stepLoop_second_high_below8 (s : RealState) (j : Nat) (h8 : j < 8) :
    (stepLoop s (.movMasked e2Loop dst63b src61bHigh)).regs 63 j = s.regs 63 j := by
  change (writeMaskedWith vaLoopAlias s dst63b e2Loop
    (fun i => zext (dwordAtQ s 59 (srcIndexRegion src61bHigh i)))).regs 63 j = s.regs 63 j
  unfold writeMaskedWith
  have hnot : ¬ 8 ≤ j := by omega
  simp [dst63b, vaLoopAlias, hnot]

theorem vaPackHigh_value (s : RealState) (ids : Nat → Addr) (j : Nat) (hj : j < 24)
    (hid : ∀ l, s.regs 59 l = ids l) :
    low32 ((runRealWith stepLoop s vaPackHigh).regs 63 j) =
      ((ids j) >>> 32).truncate 32 := by
  unfold vaPackHigh runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  let s1 := stepLoop s (.mov e1Loop dst63a src61aHigh)
  change low32 ((stepLoop s1 (.movMasked e2Loop dst63b src61bHigh)).regs 63 j) =
    ((ids j) >>> 32).truncate 32
  have h59 : ∀ k, s1.regs 59 k = ids k := by
    intro k
    rw [stepLoop_first_high_preserves59 s k]
    exact hid k
  by_cases h8 : j < 8
  · rw [stepLoop_second_high_below8 s1 j h8]
    have hval := stepLoop_mov61_unit s e1Loop dst63a src61aHigh rfl rfl rfl j (by
      simp [e1Loop, Exec.laneActive]; omega)
    have hdst : dst63a.dstIndex (e1Loop.laneIndex j) = j := by
      rw [e1_laneIndex]; simp [dst63a, Grf.dstIndex]
    rw [hdst] at hval
    have hsrc : srcIndexRegion src61aHigh (e1Loop.laneIndex j) = 2 * j + 1 := by
      rw [e1_laneIndex]; simp [src61aHigh, srcIndexRegion]; omega
    rw [hsrc] at hval
    have hhigh : dwordAtQ s 59 (2 * j + 1) = ((ids j) >>> 32).truncate 32 := by
      have h2 : (2 * j + 1) % 2 = 1 := by omega
      have hd : (2 * j + 1) / 2 = j := by omega
      simp [dwordAtQ, h2, hd, hid j]
    dsimp [s1] at *
    have hval63 : (stepLoop s (.mov e1Loop dst63a src61aHigh)).regs 63 j =
        zext (dwordAtQ s 59 (2 * j + 1)) := by
      simpa [dst63a, vaLoopAlias] using hval
    rw [hval63, hhigh]
    simp
  · have hge : 8 ≤ j := by omega
    let l := j + 8
    have hactive : e2Loop.laneActive l = true := by
      rw [e2_active]; simp; omega
    have hval := stepLoop_movMasked61_unit s1 e2Loop dst63b src61bHigh rfl rfl rfl l hactive
    have hdst : dst63b.dstIndex (e2Loop.laneIndex l) = j := by
      rw [e2_laneIndex]; simp [dst63b, Grf.dstIndex]; omega
    rw [hdst] at hval
    have hsrc : srcIndexRegion src61bHigh (e2Loop.laneIndex l) = 2 * j + 1 := by
      rw [e2_laneIndex]; simp [src61bHigh, srcIndexRegion]; omega
    rw [hsrc] at hval
    have hhigh : dwordAtQ s1 59 (2 * j + 1) = ((ids j) >>> 32).truncate 32 := by
      have h2 : (2 * j + 1) % 2 = 1 := by omega
      have hd : (2 * j + 1) / 2 = j := by omega
      simp [dwordAtQ, h2, hd, h59 j]
    dsimp [s1] at *
    have hval63 : (stepLoop (stepLoop s (.mov e1Loop dst63a src61aHigh))
        (.movMasked e2Loop dst63b src61bHigh)).regs 63 j =
        zext (dwordAtQ (stepLoop s (.mov e1Loop dst63a src61aHigh)) 59 (2 * j + 1)) := by
      simpa [dst63b, vaLoopAlias] using hval
    rw [hval63, hhigh]
    simp

end
end IntelGpu
