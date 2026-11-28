-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.LoopPackBoth

@[expose] public section

/-!
# The increment's real low pack

Executes the M1/M5 moves from `V0074` (the dword view of `V0072`) into
`V0075`, producing the low dwords of the next IDs.
-/

namespace IntelGpu

noncomputable section

def dst75a : Grf := ⟨75, 0, 0, 1, 1, 1⟩
def dst75b : Grf := ⟨75, 1, 0, 1, 1, 1⟩
def src74a : Grf := ⟨74, 0, 0, 2, 1, 0⟩
def src74b : Grf := ⟨74, 2, 0, 2, 1, 0⟩

def vaPackIncLow : List RInstr :=
  [ .mov e1Loop dst75a src74a, .movMasked e2Loop dst75b src74b ]

theorem stepLoop_inc_second_below8 (s : RealState) (j : Nat) (h8 : j < 8) :
    (stepLoop s (.movMasked e2Loop dst75b src74b)).regs 75 j = s.regs 75 j := by
  change (writeMaskedWith vaLoopAlias s dst75b e2Loop
    (fun i => zext (dwordAtQ s 72 (srcIndexRegion src74b i)))).regs 75 j = s.regs 75 j
  unfold writeMaskedWith
  have hnot : ¬ 8 ≤ j := by omega
  simp [dst75b, vaLoopAlias, hnot]

theorem vaPackIncLow_value (s : RealState) (ids : Nat → Addr) (j : Nat) (hj : j < 24)
    (hid : ∀ l, s.regs 72 l = ids l) :
    low32 ((runRealWith stepLoop s vaPackIncLow).regs 75 j) = (ids j).truncate 32 := by
  unfold vaPackIncLow runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  let s1 := stepLoop s (.mov e1Loop dst75a src74a)
  change low32 ((stepLoop s1 (.movMasked e2Loop dst75b src74b)).regs 75 j) =
    (ids j).truncate 32
  have h72 : ∀ k, s1.regs 72 k = ids k := by
    intro k
    dsimp [s1]
    have hframe := stepLoop_mov_preserves_reg (s := s) (e := e1Loop) (dst := dst75a)
      (src := src74a) (r := 72) (j := k) (by decide)
    rw [show (stepLoop s (.mov e1Loop dst75a src74a)).regs 72 k = s.regs 72 k by
      simpa [vaLoopAlias] using hframe]
    exact hid k
  by_cases h8 : j < 8
  · rw [stepLoop_inc_second_below8 s1 j h8]
    have hval := stepLoop_mov74_unit s e1Loop dst75a src74a rfl rfl rfl j (by
      simp [e1Loop, Exec.laneActive]; omega)
    have hdst : dst75a.dstIndex (e1Loop.laneIndex j) = j := by
      rw [e1_laneIndex]; simp [dst75a, Grf.dstIndex]
    rw [hdst] at hval
    have hsrc : srcIndexRegion src74a (e1Loop.laneIndex j) = 2 * j := by
      rw [e1_laneIndex]; simp [src74a, srcIndexRegion]; omega
    rw [hsrc] at hval
    have hlow : dwordAtQ s 72 (2 * j) = (ids j).truncate 32 := by
      have h2 : (2 * j) % 2 = 0 := by omega
      have hd : (2 * j) / 2 = j := by omega
      simp [dwordAtQ, h2, hd, hid j]
    dsimp [s1] at *
    have hval75 : (stepLoop s (.mov e1Loop dst75a src74a)).regs 75 j =
        zext (dwordAtQ s 72 (2 * j)) := by
      simpa [dst75a, vaLoopAlias] using hval
    rw [hval75, hlow]
    simp
  · have hge : 8 ≤ j := by omega
    let l := j + 8
    have hactive : e2Loop.laneActive l = true := by
      rw [e2_active]; simp; omega
    have hval := stepLoop_movMasked74_unit s1 e2Loop dst75b src74b rfl rfl rfl l hactive
    have hdst : dst75b.dstIndex (e2Loop.laneIndex l) = j := by
      rw [e2_laneIndex]; simp [dst75b, Grf.dstIndex]; omega
    rw [hdst] at hval
    have hsrc : srcIndexRegion src74b (e2Loop.laneIndex l) = 2 * j := by
      rw [e2_laneIndex]; simp [src74b, srcIndexRegion]; omega
    rw [hsrc] at hval
    have hlow : dwordAtQ s1 72 (2 * j) = (ids j).truncate 32 := by
      have h2 : (2 * j) % 2 = 0 := by omega
      have hd : (2 * j) / 2 = j := by omega
      simp [dwordAtQ, h2, hd, h72 j]
    dsimp [s1] at *
    have hval75 : (stepLoop (stepLoop s (.mov e1Loop dst75a src74a))
        (.movMasked e2Loop dst75b src74b)).regs 75 j =
        zext (dwordAtQ (stepLoop s (.mov e1Loop dst75a src74a)) 72 (2 * j)) := by
      simpa [dst75b, vaLoopAlias] using hval
    rw [hval75, hlow]
    simp

end
end IntelGpu
