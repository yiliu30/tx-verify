-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.VectorAddLoopProgram
public import Intel.LoopP3
public import Intel.LoopP6

@[expose] public section

/-!
# Conditional branches of the decoded loop vector add

This module composes the decoded branch sites at PCs 17 and 35 with the guard
values proved for `P3` and `P6`. The branch instruction does not invoke the
step function, so the same decoded transitions are restated for `stepLoop`,
which is the step used by the executed loop body. It stops at the target PCs;
executing the loop body is deliberately out of scope here.
-/

namespace IntelGpu

noncomputable section

/-- At PC 17, a false `P3` guard takes the decoded exit branch to PC 44. -/
theorem vaLoopP3_branch_exit (s : RealState) (lane fuel : Nat) (id size : Addr)
    (hp : s.preds 3 lane = vaLoopGuard id size)
    (hguard : vaLoopGuard id size = false) :
    runRealCFLaneWith stepLoop vaLoopProgram s 17 (fuel + 1) lane =
      runRealCFLaneWith stepLoop vaLoopProgram s 44 fuel lane := by
  apply runRealCFLane_gotoIf_taken stepLoop vaLoopProgram s 17 fuel lane 32 3 true
    "_0_007" 44
  · exact vaLoopProgram_gotoIf_first
  · simp [hp, hguard]
  · exact vaLoopProgram_label_exit

/-- At PC 17, a true `P3` guard falls through to the loop body at PC 18. -/
theorem vaLoopP3_branch_fallthrough (s : RealState) (lane fuel : Nat) (id size : Addr)
    (hp : s.preds 3 lane = vaLoopGuard id size)
    (hguard : vaLoopGuard id size = true) :
    runRealCFLaneWith stepLoop vaLoopProgram s 17 (fuel + 1) lane =
      runRealCFLaneWith stepLoop vaLoopProgram s 18 fuel lane := by
  apply runRealCFLane_gotoIf_not_taken stepLoop vaLoopProgram s 17 fuel lane 32 3 true
    "_0_007"
  · exact vaLoopProgram_gotoIf_first
  · simp [hp, hguard]

/-- At PC 35, a false `P6` guard takes the decoded exit branch to PC 44. -/
theorem vaLoopP6_branch_exit (s : RealState) (lane fuel : Nat) (nextId size : Addr)
    (hp : s.preds 6 lane = vaLoopGuard nextId size)
    (hguard : vaLoopGuard nextId size = false) :
    runRealCFLaneWith stepLoop vaLoopProgram s 35 (fuel + 1) lane =
      runRealCFLaneWith stepLoop vaLoopProgram s 44 fuel lane := by
  apply runRealCFLane_gotoIf_taken stepLoop vaLoopProgram s 35 fuel lane 32 6 true
    "_0_007" 44
  · exact vaLoopProgram_gotoIf_second
  · simp [hp, hguard]
  · exact vaLoopProgram_label_exit

/-- At PC 35, a true `P6` guard falls through to the select/writeback at PC 36. -/
theorem vaLoopP6_branch_fallthrough (s : RealState) (lane fuel : Nat) (nextId size : Addr)
    (hp : s.preds 6 lane = vaLoopGuard nextId size)
    (hguard : vaLoopGuard nextId size = true) :
    runRealCFLaneWith stepLoop vaLoopProgram s 35 (fuel + 1) lane =
      runRealCFLaneWith stepLoop vaLoopProgram s 36 fuel lane := by
  apply runRealCFLane_gotoIf_not_taken stepLoop vaLoopProgram s 35 fuel lane 32 6 true
    "_0_007"
  · exact vaLoopProgram_gotoIf_second
  · simp [hp, hguard]

/-- Both decoded continuation branches, parameterised by the proved guard
values for `P3` and `P6`. Each guard case yields its exact next PC. -/
theorem vaLoop_branch_paths (s : RealState) (lane fuel : Nat)
    (id nextId size : Addr)
    (hp3 : s.preds 3 lane = vaLoopGuard id size)
    (hp6 : s.preds 6 lane = vaLoopGuard nextId size) :
    (vaLoopGuard id size = false ->
      runRealCFLaneWith stepLoop vaLoopProgram s 17 (fuel + 1) lane =
        runRealCFLaneWith stepLoop vaLoopProgram s 44 fuel lane) ∧
    (vaLoopGuard id size = true ->
      runRealCFLaneWith stepLoop vaLoopProgram s 17 (fuel + 1) lane =
        runRealCFLaneWith stepLoop vaLoopProgram s 18 fuel lane) ∧
    (vaLoopGuard nextId size = false ->
      runRealCFLaneWith stepLoop vaLoopProgram s 35 (fuel + 1) lane =
        runRealCFLaneWith stepLoop vaLoopProgram s 44 fuel lane) ∧
    (vaLoopGuard nextId size = true ->
      runRealCFLaneWith stepLoop vaLoopProgram s 35 (fuel + 1) lane =
        runRealCFLaneWith stepLoop vaLoopProgram s 36 fuel lane) := by
  exact ⟨vaLoopP3_branch_exit s lane fuel id size hp3,
    vaLoopP3_branch_fallthrough s lane fuel id size hp3,
    vaLoopP6_branch_exit s lane fuel nextId size hp6,
    vaLoopP6_branch_fallthrough s lane fuel nextId size hp6⟩

end
end IntelGpu
