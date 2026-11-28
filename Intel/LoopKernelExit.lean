-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.LoopKernelEntry
public import Intel.LoopKernelInactive

@[expose] public section

/-!
# Reaching `ret`: the kernel exits with `halted = true`

`Intel/LoopKernelEntry` stops at the PC 44 exit label. This module executes the
exit label and the decoded `ret`, then combines the halted flag with the
memory effect. The result `vaLoop_kernel_pc0_effect` is the full per-lane
statement: from PC 0, every active lane halts with `C[id] = A[id] + B[id]`.
-/

namespace IntelGpu

noncomputable section

/-! ## The exit block -/

/-- From PC 44, the exit label and `ret` set the halt flag. -/
theorem vaLoopCFLane_exit_halted (s : RealState) (lane fuel : Nat) (h : 2 ≤ fuel) :
    (runRealCFLaneWith stepLoop vaLoopProgram s 44 fuel lane).halted = true := by
  obtain ⟨g, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [show 2 + g = (g + 1) + 1 from by omega]
  rw [runRealCFLaneWith_label stepLoop vaLoopProgram s lane 44 (g + 1) "_0_007"
    (by decide)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram s lane 45 g (.ret 1)
    (by decide) (by trivial)]
  cases g with
  | zero => rfl
  | succ k =>
      simp [runRealCFLaneWith,
        (by decide : vaLoopProgram[46]? = (none : Option RInstr)),
        stepLoop, stepVAL, stepWith]

/-- The PC 17 exit path reaches `ret` with `halted = true`, with the second
guard supplied by the range form. -/
theorem vaLoop_lane_exit_halted (s : RealState) (lane fuel : Nat)
    (ids : Nat → Addr) (sizeLo sizeHi : Word)
    (hP3 : s.preds 3 lane = true) (hj : lane < 24)
    (hid : ∀ l, (vaLoopPreP6 s).regs 72 l = ids l)
    (hslo : low32 ((vaLoopPreP6 s).regs 49 0) = sizeLo)
    (hshi : low32 ((vaLoopPreP6 s).regs 49 1) = sizeHi)
    (hguard : vaLoopGuard (ids lane) (vaLoopSize sizeLo sizeHi) = false) :
    (runRealCFLaneWith stepLoop vaLoopProgram s 17 (fuel + 21) lane).halted = true := by
  rw [show fuel + 21 = (fuel + 2) + 19 from by omega,
    vaLoop_lane_body_exit_with_guard s lane (fuel + 2) ids sizeLo sizeHi hP3 hj hid hslo
      hshi hguard]
  exact vaLoopCFLane_exit_halted _ lane (fuel + 2) (by omega)

/-! ## The halted kernel -/

/-- The PC 8 path reaches `ret` with `halted = true`. -/
theorem vaLoop_pc8_exit_halted (s : RealState) (lane fuel : Nat)
    (ids : Nat → Addr) (sizeLo sizeHi : Word)
    (hid : ∀ l, s.regs 59 l = ids l)
    (hslo : low32 (s.regs 49 0) = sizeLo)
    (hshi : low32 (s.regs 49 1) = sizeHi)
    (hstride : s.regs 37 0 = vaLoopSize sizeLo sizeHi)
    (hguard : vaLoopGuard (ids lane) (vaLoopSize sizeLo sizeHi) = true)
    (hj : lane < 24)
    (hbound : (ids lane).toNat + (vaLoopSize sizeLo sizeHi).toNat < 2 ^ 64) :
    (runRealCFLaneWith stepLoop vaLoopProgram s 8 (fuel + 30) lane).halted = true := by
  have hp3 : (runRealWith stepLoop s vaLoopP3Prefix).preds 3 lane = true := by
    rw [vaLoopP3_exec s ids sizeLo sizeHi lane hj hid hslo hshi]
    exact hguard
  have h72 : ∀ k, (vaLoopPreP6 (runRealWith stepLoop s vaLoopP3Prefix)).regs 72 k =
      ids k + vaLoopSize sizeLo sizeHi := by
    intro k
    rw [vaLoopPreP6_regs72, vaLoopP3Prefix_preserves59, hid k,
      vaLoopP3Prefix_preserves37, hstride]
  have hslo' : low32
      ((vaLoopPreP6 (runRealWith stepLoop s vaLoopP3Prefix)).regs 49 0) = sizeLo := by
    rw [vaLoopPreP6_preserves49, vaLoopP3Prefix_preserves49]
    exact hslo
  have hshi' : low32
      ((vaLoopPreP6 (runRealWith stepLoop s vaLoopP3Prefix)).regs 49 1) = sizeHi := by
    rw [vaLoopPreP6_preserves49, vaLoopP3Prefix_preserves49]
    exact hshi
  have hguard' : vaLoopGuard (ids lane + vaLoopSize sizeLo sizeHi)
      (vaLoopSize sizeLo sizeHi) = false :=
    vaLoopNext_guard_false (ids lane) (vaLoopSize sizeLo sizeHi) hbound
  rw [show fuel + 30 = (fuel + 21) + 9 from by omega, vaLoopCFP3 s lane (fuel + 21)]
  exact vaLoop_lane_exit_halted (runRealWith stepLoop s vaLoopP3Prefix) lane fuel
    (fun k => ids k + vaLoopSize sizeLo sizeHi) sizeLo sizeHi hp3 hj h72 hslo' hshi' hguard'

/-- The kernel reaches `ret` with `halted = true` on the active path. -/
theorem vaLoop_kernel_pc0_halted (s : RealState) (lane fuel : Nat)
    (localSize r0 globalOffset : Word) (localId : Nat → BitVec 16)
    (sizeLo sizeHi : Word)
    (hlaunch : VaLoopLaunch s localSize r0 globalOffset localId)
    (hsize : VaLoopSizePre s sizeLo sizeHi)
    (h37 : s.regs 37 0 = vaLoopSize sizeLo sizeHi) (hj : lane < 24)
    (hP3 : vaLoopGuard (vaLoopId localSize r0 globalOffset localId lane)
      (vaLoopSize sizeLo sizeHi) = true)
    (hbound : (vaLoopId localSize r0 globalOffset localId lane).toNat +
      (vaLoopSize sizeLo sizeHi).toNat < 2 ^ 64) :
    (runRealCFLaneWith stepLoop vaLoopProgram s 0 (fuel + 38) lane).halted = true := by
  let idxFull : Nat → Addr := fun k =>
    if k < 32 then vaLoopId localSize r0 globalOffset localId k
    else (runRealWith stepLoop s vaLoopPreamble).regs 59 k
  have hidx : ∀ k, (runRealWith stepLoop s vaLoopPreamble).regs 59 k = idxFull k := by
    intro k
    by_cases hk : k < 32
    · simp [idxFull, hk,
        vaLoopPreamble_stepLoop_id s localSize r0 globalOffset localId k hk hlaunch]
    · simp [idxFull, hk]
  have hslo : low32 ((runRealWith stepLoop s vaLoopPreamble).regs 49 0) = sizeLo := by
    rw [(vaLoopPreamble_stepLoop_size s sizeLo sizeHi hsize).1]
    simp
  have hshi : low32 ((runRealWith stepLoop s vaLoopPreamble).regs 49 1) = sizeHi := by
    rw [(vaLoopPreamble_stepLoop_size s sizeLo sizeHi hsize).2]
    simp
  have h37' : (runRealWith stepLoop s vaLoopPreamble).regs 37 0 =
      vaLoopSize sizeLo sizeHi := by
    rw [vaLoopPreamble_stepLoop_preserves_reg s 37 0 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
    exact h37
  have hP3' : vaLoopGuard (idxFull lane) (vaLoopSize sizeLo sizeHi) = true := by
    simp [idxFull, show lane < 32 from by omega, hP3]
  have hbound' : (idxFull lane).toNat + (vaLoopSize sizeLo sizeHi).toNat < 2 ^ 64 := by
    simpa [idxFull, show lane < 32 from by omega] using hbound
  rw [show fuel + 38 = (fuel + 30) + 8 from by omega,
    vaLoopCFPreamble s lane (fuel + 30)]
  exact vaLoop_pc8_exit_halted (runRealWith stepLoop s vaLoopPreamble) lane fuel idxFull
    sizeLo sizeHi hidx hslo hshi h37' hP3' hj hbound'

/-- The full per-lane kernel effect: the active lane halts at `ret` and its
store satisfies `C[id] = A[id] + B[id]`. -/
theorem vaLoop_kernel_pc0_effect (s : RealState) (lane fuel : Nat)
    (localSize r0 globalOffset : Word) (localId : Nat → BitVec 16)
    (aPtr bPtr cPtr : Addr) (sizeLo sizeHi : Word) (l : Nat)
    (hlaunch : VaLoopLaunch s localSize r0 globalOffset localId)
    (hsize : VaLoopSizePre s sizeLo sizeHi)
    (h47 : s.regs 47 0 = aPtr) (h48 : s.regs 48 0 = bPtr)
    (h46 : s.regs 46 0 = cPtr) (h37 : s.regs 37 0 = vaLoopSize sizeLo sizeHi)
    (hl : l < 32) (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0)
    (hc : cPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (vaLoopId localSize r0 globalOffset localId l).toNat < 2 ^ 64)
    (hbb : bPtr.toNat + 4 * (vaLoopId localSize r0 globalOffset localId l).toNat < 2 ^ 64)
    (hcb : cPtr.toNat + 4 * (vaLoopId localSize r0 globalOffset localId l).toNat < 2 ^ 64)
    (hboundC : ∀ k, k < 32 →
      cPtr.toNat + 4 * (vaLoopId localSize r0 globalOffset localId k).toNat < 2 ^ 64)
    (hdistinct : ∀ k, k < 32 → k ≠ l →
      cPtr.toNat / 4 + (vaLoopId localSize r0 globalOffset localId k).toNat ≠
        cPtr.toNat / 4 + (vaLoopId localSize r0 globalOffset localId l).toNat)
    (hP3 : vaLoopGuard (vaLoopId localSize r0 globalOffset localId lane)
      (vaLoopSize sizeLo sizeHi) = true)
    (hj : lane < 24)
    (hbound : (vaLoopId localSize r0 globalOffset localId lane).toNat +
      (vaLoopSize sizeLo sizeHi).toNat < 2 ^ 64) :
    (runRealCFLaneWith stepLoop vaLoopProgram s 0 (fuel + 38) lane).halted = true ∧
    (runRealCFLaneWith stepLoop vaLoopProgram s 0 (fuel + 38) lane).mem
        (cPtr.toNat / 4 + (vaLoopId localSize r0 globalOffset localId l).toNat) =
      s.mem (aPtr.toNat / 4 + (vaLoopId localSize r0 globalOffset localId l).toNat) +
        s.mem (bPtr.toNat / 4 + (vaLoopId localSize r0 globalOffset localId l).toNat) := by
  refine ⟨vaLoop_kernel_pc0_halted s lane fuel localSize r0 globalOffset localId sizeLo
    sizeHi hlaunch hsize h37 hj hP3 hbound, ?_⟩
  have h := vaLoop_kernel_pc0_mem s lane (fuel + 2) localSize r0 globalOffset localId
    aPtr bPtr cPtr sizeLo sizeHi l hlaunch hsize h47 h48 h46 h37 hl ha hb hc hab hbb hcb
    hboundC hdistinct hP3 hj hbound
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

end

end IntelGpu
