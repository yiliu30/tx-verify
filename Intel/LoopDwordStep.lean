-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.LoopGuard
public import Intel.LoopPack

@[expose] public section

/-!
# Dword-view execution for the loop vector add

The loop's `mov`/`movMasked` instructions read `V0061` and `V0074`, which are
dword views of qword-per-lane registers. `stepLoop` gives those reads the
correct dword view while delegating every other instruction to `stepVAL`.
-/

namespace IntelGpu

noncomputable section

/-- Dword `d` of a qword-per-lane register `reg`. -/
def dwordAtQ (s : RealState) (reg d : Nat) : Word :=
  if d % 2 = 0 then (s.regs reg (d / 2)).truncate 32
  else ((s.regs reg (d / 2)) >>> 32).truncate 32

/-- The loop-vector-add step: dword-view moves, unified semantics elsewhere. -/
def stepLoop (s : RealState) : RInstr → RealState
  | .mov e dst src =>
      if src.num = 61 then
        writeMaskedWith vaLoopAlias s dst e
          (fun i => zext (dwordAtQ s 59 (srcIndexRegion src i)))
      else if src.num = 74 then
        writeMaskedWith vaLoopAlias s dst e
          (fun i => zext (dwordAtQ s 72 (srcIndexRegion src i)))
      else writeMaskedWith vaLoopAlias s dst e (fun i => readSrcWith vaLoopAlias s src i)
  | .movMasked e dst src =>
      if src.num = 61 then
        writeMaskedWith vaLoopAlias s dst e
          (fun i => zext (dwordAtQ s 59 (srcIndexRegion src i)))
      else if src.num = 74 then
        writeMaskedWith vaLoopAlias s dst e
          (fun i => zext (dwordAtQ s 72 (srcIndexRegion src i)))
      else writeMaskedWith vaLoopAlias s dst e (fun i => readSrcWith vaLoopAlias s src i)
  | i => stepVAL s i

/-- A dword-view move from `V0061` writes the selected dword at the active
destination-region element. -/
theorem stepLoop_mov61_unit (s : RealState) (e : Exec) (dst src : Grf)
    (hsrc : src.num = 61) (hnm : e.noMask = false) (hdst : dst.hstride = 1)
    (l : Nat) (hactive : e.laneActive l = true) :
    (stepLoop s (.mov e dst src)).regs (vaLoopAlias dst.num)
        (dst.dstIndex (e.laneIndex l)) =
      zext (dwordAtQ s 59 (srcIndexRegion src (e.laneIndex l))) := by
  have hle : e.offset ≤ l := by
    have h := hactive
    simp [Exec.laneActive, hnm] at h
    exact h.1
  simp [stepLoop, hsrc, writeMaskedWith, Grf.dstIndex, Exec.laneIndex, hnm, hdst,
    Nat.add_sub_of_le hle, hactive]

/-- The same for the second dword-view source `V0074`. -/
theorem stepLoop_mov74_unit (s : RealState) (e : Exec) (dst src : Grf)
    (hsrc : src.num = 74)
    (hnm : e.noMask = false) (hdst : dst.hstride = 1)
    (l : Nat) (hactive : e.laneActive l = true) :
    (stepLoop s (.mov e dst src)).regs (vaLoopAlias dst.num)
        (dst.dstIndex (e.laneIndex l)) =
      zext (dwordAtQ s 72 (srcIndexRegion src (e.laneIndex l))) := by
  have hle : e.offset ≤ l := by
    have h := hactive
    simp [Exec.laneActive, hnm] at h
    exact h.1
  simp [stepLoop, hsrc, writeMaskedWith, Grf.dstIndex, Exec.laneIndex, hnm,
    hdst, Nat.add_sub_of_le hle, hactive]

theorem stepLoop_movMasked61_unit (s : RealState) (e : Exec) (dst src : Grf)
    (hsrc : src.num = 61) (hnm : e.noMask = false) (hdst : dst.hstride = 1)
    (l : Nat) (hactive : e.laneActive l = true) :
    (stepLoop s (.movMasked e dst src)).regs (vaLoopAlias dst.num)
        (dst.dstIndex (e.laneIndex l)) =
      zext (dwordAtQ s 59 (srcIndexRegion src (e.laneIndex l))) := by
  have hle : e.offset ≤ l := by
    have h := hactive
    simp [Exec.laneActive, hnm] at h
    exact h.1
  simp [stepLoop, hsrc, writeMaskedWith, Grf.dstIndex, Exec.laneIndex, hnm, hdst,
    Nat.add_sub_of_le hle, hactive]

theorem stepLoop_movMasked74_unit (s : RealState) (e : Exec) (dst src : Grf)
    (hsrc : src.num = 74) (hnm : e.noMask = false) (hdst : dst.hstride = 1)
    (l : Nat) (hactive : e.laneActive l = true) :
    (stepLoop s (.movMasked e dst src)).regs (vaLoopAlias dst.num)
        (dst.dstIndex (e.laneIndex l)) =
      zext (dwordAtQ s 72 (srcIndexRegion src (e.laneIndex l))) := by
  have hle : e.offset ≤ l := by
    have h := hactive
    simp [Exec.laneActive, hnm] at h
    exact h.1
  simp [stepLoop, hsrc, writeMaskedWith, Grf.dstIndex, Exec.laneIndex, hnm, hdst,
    Nat.add_sub_of_le hle, hactive]

end
end IntelGpu
