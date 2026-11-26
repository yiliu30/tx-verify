-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.LoopDwordStep

@[expose] public section

/-!
# Executing the real M1/M5 low pack

Explicit execution controls and specialized rewrite lemmas make the real
two-move low pack reproducible without relying on generic `Exec` normalization.
-/

namespace IntelGpu

noncomputable section

def e1Loop : Exec := ⟨16, 0, false⟩
def e2Loop : Exec := ⟨16, 16, false⟩
def dst62a : Grf := ⟨62, 0, 0, 1, 1, 1⟩
def dst62b : Grf := ⟨62, 1, 0, 1, 1, 1⟩
def src61a : Grf := ⟨61, 0, 0, 2, 1, 0⟩
def src61b : Grf := ⟨61, 2, 0, 2, 1, 0⟩

theorem e1_laneIndex (l : Nat) : e1Loop.laneIndex l = l := by
  simp [e1Loop, Exec.laneIndex]

theorem e2_laneIndex (l : Nat) : e2Loop.laneIndex l = l - 16 := by
  simp [e2Loop, Exec.laneIndex]

theorem e2_active (l : Nat) :
    e2Loop.laneActive l = decide (16 ≤ l ∧ l < 32) := by
  unfold e2Loop Exec.laneActive
  by_cases h1 : 16 ≤ l <;> by_cases h2 : l < 32 <;> simp [h1, h2]

def vaPackLow : List RInstr :=
  [ .mov e1Loop dst62a src61a, .movMasked e2Loop dst62b src61b ]

theorem stepLoop_first_preserves59 (s : RealState) (j : Nat) :
    (stepLoop s (.mov e1Loop dst62a src61a)).regs 59 j = s.regs 59 j := by
  change (writeMaskedWith vaLoopAlias s dst62a e1Loop
    (fun i => zext (dwordAtQ s 59 (srcIndexRegion src61a i)))).regs 59 j = s.regs 59 j
  exact writeMaskedWith_other_reg vaLoopAlias s dst62a e1Loop _ 59 j (by decide)

theorem stepLoop_second_below8 (s : RealState) (j : Nat) (h8 : j < 8) :
    (stepLoop s (.movMasked e2Loop dst62b src61b)).regs 62 j = s.regs 62 j := by
  change (writeMaskedWith vaLoopAlias s dst62b e2Loop
    (fun i => zext (dwordAtQ s 59 (srcIndexRegion src61b i)))).regs 62 j = s.regs 62 j
  unfold writeMaskedWith
  have hnot : ¬ 8 ≤ j := by omega
  simp [dst62b, vaLoopAlias, hnot]

theorem vaPackLow_value (s : RealState) (ids : Nat → Addr) (j : Nat) (hj : j < 24)
    (hid : ∀ l, s.regs 59 l = ids l) :
    low32 ((runRealWith stepLoop s vaPackLow).regs 62 j) = (ids j).truncate 32 := by
  unfold vaPackLow runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  let s1 := stepLoop s (.mov e1Loop dst62a src61a)
  change low32 ((stepLoop s1 (.movMasked e2Loop dst62b src61b)).regs 62 j) =
    (ids j).truncate 32
  have h59 : ∀ k, s1.regs 59 k = ids k := by
    intro k
    rw [stepLoop_first_preserves59 s k]
    exact hid k
  by_cases h8 : j < 8
  · rw [stepLoop_second_below8 s1 j h8]
    have hval := stepLoop_mov61_unit s e1Loop dst62a src61a rfl rfl rfl j (by
      simp [e1Loop, Exec.laneActive]; omega)
    have hdst : dst62a.dstIndex (e1Loop.laneIndex j) = j := by
      rw [e1_laneIndex]; simp [dst62a, Grf.dstIndex]
    rw [hdst] at hval
    have hsrc : srcIndexRegion src61a (e1Loop.laneIndex j) = 2 * j := by
      rw [e1_laneIndex]; simp [src61a, srcIndexRegion]; omega
    rw [hsrc] at hval
    have hlow : dwordAtQ s 59 (2 * j) = (ids j).truncate 32 := by
      have h2 : (2 * j) % 2 = 0 := by omega
      have hd : (2 * j) / 2 = j := by omega
      simp [dwordAtQ, h2, hd, hid j]
    dsimp [s1] at *
    have hval62 : (stepLoop s (.mov e1Loop dst62a src61a)).regs 62 j =
        zext (dwordAtQ s 59 (2 * j)) := by
      simpa [dst62a, vaLoopAlias] using hval
    rw [hval62, hlow]
    simp
  · have hge : 8 ≤ j := by omega
    let l := j + 8
    have hactive : e2Loop.laneActive l = true := by
      rw [e2_active]; simp; omega
    have hval := stepLoop_movMasked61_unit s1 e2Loop dst62b src61b rfl rfl rfl l hactive
    have hdst : dst62b.dstIndex (e2Loop.laneIndex l) = j := by
      rw [e2_laneIndex]; simp [dst62b, Grf.dstIndex]; omega
    rw [hdst] at hval
    have hsrc : srcIndexRegion src61b (e2Loop.laneIndex l) = 2 * j := by
      rw [e2_laneIndex]; simp [src61b, srcIndexRegion]; omega
    rw [hsrc] at hval
    have hlow : dwordAtQ s1 59 (2 * j) = (ids j).truncate 32 := by
      have h2 : (2 * j) % 2 = 0 := by omega
      have hd : (2 * j) / 2 = j := by omega
      simp [dwordAtQ, h2, hd, h59 j]
    dsimp [s1] at *
    have hval62 : (stepLoop (stepLoop s (.mov e1Loop dst62a src61a))
        (.movMasked e2Loop dst62b src61b)).regs 62 j =
        zext (dwordAtQ (stepLoop s (.mov e1Loop dst62a src61a)) 59 (2 * j)) := by
      simpa [dst62b, vaLoopAlias] using hval
    rw [hval62, hlow]
    simp

end
end IntelGpu
