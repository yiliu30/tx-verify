-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.LoopPackIncLow

@[expose] public section

/-!
# The increment's real high pack

The high-half counterpart of `LoopPackIncLow`, writing `V0076`.
-/

namespace IntelGpu

noncomputable section

def dst76a : Grf := ⟨76, 0, 0, 1, 1, 1⟩
def dst76b : Grf := ⟨76, 1, 0, 1, 1, 1⟩
def src74aHigh : Grf := ⟨74, 0, 1, 2, 1, 0⟩
def src74bHigh : Grf := ⟨74, 2, 1, 2, 1, 0⟩

def vaPackIncHigh : List RInstr :=
  [ .mov e1Loop dst76a src74aHigh, .movMasked e2Loop dst76b src74bHigh ]

theorem stepLoop_inc_first_high_preserves72 (s : RealState) (j : Nat) :
    (stepLoop s (.mov e1Loop dst76a src74aHigh)).regs 72 j = s.regs 72 j := by
  have h := stepLoop_mov_preserves_reg (s := s) (e := e1Loop) (dst := dst76a)
    (src := src74aHigh) (r := 72) (j := j) (by decide)
  simpa [vaLoopAlias] using h

theorem stepLoop_inc_second_high_preserves72 (s : RealState) (j : Nat) :
    (stepLoop s (.movMasked e2Loop dst76b src74bHigh)).regs 72 j = s.regs 72 j := by
  have h := stepLoop_movMasked_preserves_reg (s := s) (e := e2Loop) (dst := dst76b)
    (src := src74bHigh) (r := 72) (j := j) (by decide)
  simpa [vaLoopAlias] using h

theorem stepLoop_inc_second_high_below8 (s : RealState) (j : Nat) (h8 : j < 8) :
    (stepLoop s (.movMasked e2Loop dst76b src74bHigh)).regs 76 j = s.regs 76 j := by
  change (writeMaskedWith vaLoopAlias s dst76b e2Loop
    (fun i => zext (dwordAtQ s 72 (srcIndexRegion src74bHigh i)))).regs 76 j = s.regs 76 j
  unfold writeMaskedWith
  have hnot : ¬ 8 ≤ j := by omega
  simp [dst76b, vaLoopAlias, hnot]

theorem vaPackIncHigh_value (s : RealState) (ids : Nat → Addr) (j : Nat) (hj : j < 24)
    (hid : ∀ l, s.regs 72 l = ids l) :
    low32 ((runRealWith stepLoop s vaPackIncHigh).regs 76 j) =
      ((ids j) >>> 32).truncate 32 := by
  unfold vaPackIncHigh runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  let s1 := stepLoop s (.mov e1Loop dst76a src74aHigh)
  change low32 ((stepLoop s1 (.movMasked e2Loop dst76b src74bHigh)).regs 76 j) =
    ((ids j) >>> 32).truncate 32
  have h72 : ∀ k, s1.regs 72 k = ids k := by
    intro k
    dsimp [s1]
    rw [stepLoop_inc_first_high_preserves72, hid k]
  by_cases h8 : j < 8
  · rw [stepLoop_inc_second_high_below8 s1 j h8]
    have hval := stepLoop_mov74_unit s e1Loop dst76a src74aHigh rfl rfl rfl j (by
      simp [e1Loop, Exec.laneActive]; omega)
    have hdst : dst76a.dstIndex (e1Loop.laneIndex j) = j := by
      rw [e1_laneIndex]; simp [dst76a, Grf.dstIndex]
    rw [hdst] at hval
    have hsrc : srcIndexRegion src74aHigh (e1Loop.laneIndex j) = 2 * j + 1 := by
      rw [e1_laneIndex]; simp [src74aHigh, srcIndexRegion]; omega
    rw [hsrc] at hval
    have hhigh : dwordAtQ s 72 (2 * j + 1) = ((ids j) >>> 32).truncate 32 := by
      have h2 : (2 * j + 1) % 2 = 1 := by omega
      have hd : (2 * j + 1) / 2 = j := by omega
      simp [dwordAtQ, h2, hd, hid j]
    dsimp [s1] at *
    have hval76 : (stepLoop s (.mov e1Loop dst76a src74aHigh)).regs 76 j =
        zext (dwordAtQ s 72 (2 * j + 1)) := by
      simpa [dst76a, vaLoopAlias] using hval
    rw [hval76, hhigh]
    simp
  · have hge : 8 ≤ j := by omega
    let l := j + 8
    have hactive : e2Loop.laneActive l = true := by
      rw [e2_active]; simp; omega
    have hval := stepLoop_movMasked74_unit s1 e2Loop dst76b src74bHigh rfl rfl rfl l hactive
    have hdst : dst76b.dstIndex (e2Loop.laneIndex l) = j := by
      rw [e2_laneIndex]; simp [dst76b, Grf.dstIndex]; omega
    rw [hdst] at hval
    have hsrc : srcIndexRegion src74bHigh (e2Loop.laneIndex l) = 2 * j + 1 := by
      rw [e2_laneIndex]; simp [src74bHigh, srcIndexRegion]; omega
    rw [hsrc] at hval
    have hhigh : dwordAtQ s1 72 (2 * j + 1) = ((ids j) >>> 32).truncate 32 := by
      have h2 : (2 * j + 1) % 2 = 1 := by omega
      have hd : (2 * j + 1) / 2 = j := by omega
      simp [dwordAtQ, h2, hd, h72 j]
    dsimp [s1] at *
    have hval76 : (stepLoop (stepLoop s (.mov e1Loop dst76a src74aHigh))
        (.movMasked e2Loop dst76b src74bHigh)).regs 76 j =
        zext (dwordAtQ (stepLoop s (.mov e1Loop dst76a src74aHigh)) 72 (2 * j + 1)) := by
      simpa [dst76b, vaLoopAlias] using hval
    rw [hval76, hhigh]
    simp

end
end IntelGpu
