-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.LoopKernelEntry

@[expose] public section

/-!
# Predicated lanes: a false first guard writes nothing

`Intel/LoopKernelEntry` follows the lane that passes the first guard. This
module covers the other side of the decoded `gotoIf` at PC 17: a lane whose
real P3 guard is false jumps straight to PC 44. Both the preamble and the
PC 8--16 pack/guard prefix are register/predicate-only, so such a lane leaves
memory exactly as it found it, independent of the pointers and of any memory
aliasing.
-/

namespace IntelGpu

noncomputable section

/-- The pack/guard prefix at PC 8--16 does not touch memory. -/
theorem vaLoopP3Prefix_mem (s : RealState) :
    (runRealWith stepLoop s vaLoopP3Prefix).mem = s.mem := by
  unfold vaLoopP3Prefix vaPackLow vaPackHigh vaGuardBlock runRealWith
  simp [stepLoop, stepVAL, stepWith, writeMaskedWith, e1Loop, e2Loop,
    dst62a, dst62b, src61a, src61b, dst63a, dst63b, src61aHigh, src61bHigh]

/-- A lane whose real P3 guard is false runs to PC 44 and leaves memory
unchanged. No pointer or aliasing hypothesis is needed: the lane never reaches
the body. -/
theorem vaLoop_lane_inactive_mem (s : RealState) (lane fuel : Nat)
    (localSize r0 globalOffset : Word) (localId : Nat → BitVec 16)
    (sizeLo sizeHi : Word)
    (hlaunch : VaLoopLaunch s localSize r0 globalOffset localId)
    (hsize : VaLoopSizePre s sizeLo sizeHi) (hj : lane < 24)
    (hP3 : vaLoopGuard (vaLoopId localSize r0 globalOffset localId lane)
      (vaLoopSize sizeLo sizeHi) = false) :
    (runRealCFLaneWith stepLoop vaLoopProgram s 0 (fuel + 18) lane).mem = s.mem := by
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
  have hp : (runRealWith stepLoop (runRealWith stepLoop s vaLoopPreamble)
        vaLoopP3Prefix).preds 3 lane =
      vaLoopGuard (idxFull lane) (vaLoopSize sizeLo sizeHi) :=
    vaLoopP3_exec (runRealWith stepLoop s vaLoopPreamble) idxFull sizeLo sizeHi lane
      (by omega) hidx hslo hshi
  have hguard : vaLoopGuard (idxFull lane) (vaLoopSize sizeLo sizeHi) = false := by
    simpa [idxFull, show lane < 32 from by omega] using hP3
  rw [show fuel + 18 = (fuel + 10) + 8 from by omega,
    vaLoopCFPreamble s lane (fuel + 10)]
  rw [show fuel + 10 = (fuel + 1) + 9 from by omega,
    vaLoopCFP3 (runRealWith stepLoop s vaLoopPreamble) lane (fuel + 1)]
  rw [vaLoopP3_branch_exit
    (runRealWith stepLoop (runRealWith stepLoop s vaLoopPreamble) vaLoopP3Prefix)
    lane fuel (idxFull lane) (vaLoopSize sizeLo sizeHi) hp hguard]
  rw [vaLoopCFLane_exit_mem, vaLoopP3Prefix_mem, vaLoopPreamble_stepLoop_mem]

end

end IntelGpu
