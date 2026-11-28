-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.VectorAddLoopBody

@[expose] public section

/-!
# The decoded loop-vector-add program and its branch sites

This module materializes the 46 instruction/label entries decoded from
`realVectorAdd`, proves the decode equality, and exposes the two real
predicated branch sites for the per-lane control-flow interpreter.
-/

namespace IntelGpu

noncomputable section

/-- The exact decoded statement list of the loop vector add. -/
def vaLoopProgram : List RInstr :=
  [ .label "_main_0", .prologue,
    .mov (Exec.nm 2) ⟨49, 0, 0, 1, 1, 1⟩ ⟨50, 0, 0, 1, 1, 0⟩,
    .mul (Exec.nm 1) ⟨51, 0, 0, 1, 1, 1⟩ ⟨52, 0, 0, 0, 1, 0⟩ ⟨53, 0, 1, 0, 1, 0⟩,
    .mov 32 ⟨54, 0, 0, 1, 1, 1⟩ ⟨55, 0, 0, 1, 1, 0⟩,
    .add 32 ⟨56, 0, 0, 1, 1, 1⟩ ⟨51, 0, 0, 0, 1, 0⟩ ⟨54, 0, 0, 1, 1, 0⟩,
    .mov (Exec.nm 1) ⟨57, 0, 0, 1, 1, 1⟩ ⟨58, 0, 0, 0, 1, 0⟩,
    .add 32 ⟨59, 0, 0, 1, 1, 1⟩ ⟨56, 0, 0, 1, 1, 0⟩ ⟨57, 0, 0, 0, 1, 0⟩,
    .mov 16 ⟨62, 0, 0, 1, 1, 1⟩ ⟨61, 0, 0, 2, 1, 0⟩,
    .movMasked ⟨16, 16, false⟩ ⟨62, 1, 0, 1, 1, 1⟩ ⟨61, 2, 0, 2, 1, 0⟩,
    .mov 16 ⟨63, 0, 0, 1, 1, 1⟩ ⟨61, 0, 1, 2, 1, 0⟩,
    .movMasked ⟨16, 16, false⟩ ⟨63, 1, 0, 1, 1, 1⟩ ⟨61, 2, 1, 2, 1, 0⟩,
    .cmpLtReg 32 1 ⟨64, 0, 0, 1, 1, 0⟩ ⟨65, 0, 0, 0, 1, 0⟩,
    .cmpEqReg 32 2 ⟨63, 0, 0, 1, 1, 0⟩ ⟨49, 0, 1, 0, 1, 0⟩,
    .predAnd 32 2 2 1,
    .cmpLtReg 32 3 ⟨66, 0, 0, 1, 1, 0⟩ ⟨65, 0, 1, 0, 1, 0⟩,
    .predOr 32 3 3 2,
    .gotoIf 32 3 true "_0_007", .label "_0_008",
    .mov (Exec.nm 1) ⟨67, 0, 0, 1, 1, 1⟩ ⟨68, 0, 0, 0, 1, 0⟩,
    .label "_0_009", .loadScaled 32 69 .d32 47 59,
    .loadScaled 32 70 .d32 48 59,
    .add 32 ⟨71, 0, 0, 1, 1, 1⟩ ⟨69, 0, 0, 1, 1, 0⟩ ⟨70, 0, 0, 1, 1, 0⟩,
    .storeScaled 32 46 59 .d32 71,
    .add 32 ⟨72, 0, 0, 1, 1, 1⟩ ⟨59, 0, 0, 1, 1, 0⟩ ⟨67, 0, 0, 0, 1, 0⟩,
    .mov 16 ⟨75, 0, 0, 1, 1, 1⟩ ⟨74, 0, 0, 2, 1, 0⟩,
    .movMasked ⟨16, 16, false⟩ ⟨75, 1, 0, 1, 1, 1⟩ ⟨74, 2, 0, 2, 1, 0⟩,
    .mov 16 ⟨76, 0, 0, 1, 1, 1⟩ ⟨74, 0, 1, 2, 1, 0⟩,
    .movMasked ⟨16, 16, false⟩ ⟨76, 1, 0, 1, 1, 1⟩ ⟨74, 2, 1, 2, 1, 0⟩,
    .cmpLtReg 32 4 ⟨77, 0, 0, 1, 1, 0⟩ ⟨65, 0, 0, 0, 1, 0⟩,
    .cmpEqReg 32 5 ⟨76, 0, 0, 1, 1, 0⟩ ⟨49, 0, 1, 0, 1, 0⟩,
    .predAnd 32 5 5 4,
    .cmpLtReg 32 6 ⟨78, 0, 0, 1, 1, 0⟩ ⟨65, 0, 1, 0, 1, 0⟩,
    .predOr 32 6 6 5,
    .gotoIf 32 6 true "_0_007", .label "_0_010",
    .sel 32 6 ⟨79, 0, 0, 1, 1, 1⟩ ⟨75, 0, 0, 1, 1, 0⟩ ⟨62, 0, 0, 1, 1, 0⟩,
    .sel 32 6 ⟨80, 0, 0, 1, 1, 1⟩ ⟨76, 0, 0, 1, 1, 0⟩ ⟨63, 0, 0, 1, 1, 0⟩,
    .mov 16 ⟨81, 0, 0, 1, 1, 2⟩ ⟨82, 0, 0, 1, 1, 0⟩,
    .movMasked ⟨16, 16, false⟩ ⟨81, 2, 0, 1, 1, 2⟩ ⟨82, 1, 0, 1, 1, 0⟩,
    .mov 16 ⟨81, 0, 1, 1, 1, 2⟩ ⟨83, 0, 0, 1, 1, 0⟩,
    .movMasked ⟨16, 16, false⟩ ⟨81, 2, 1, 1, 1, 2⟩ ⟨83, 1, 0, 1, 1, 0⟩,
    .goto 1 "_0_009", .label "_0_007", .ret 1 ]

theorem realVectorAdd_decoded_eq :
    decodeRealProgram realVectorAdd = some vaLoopProgram := by
  unfold decodeRealProgram decodeRealStmts realVectorAdd vaLoopProgram
  decide

theorem vaLoopProgram_label_exit : labelIndex vaLoopProgram "_0_007" = some 44 := by decide
theorem vaLoopProgram_label_loop : labelIndex vaLoopProgram "_0_009" = some 20 := by decide
theorem vaLoopProgram_label_step : labelIndex vaLoopProgram "_0_010" = some 36 := by decide

theorem vaLoopProgram_gotoIf_first :
    vaLoopProgram[17]? = some (.gotoIf 32 3 true "_0_007") := by decide
theorem vaLoopProgram_gotoIf_second :
    vaLoopProgram[35]? = some (.gotoIf 32 6 true "_0_007") := by decide

/-- At the first branch site, a lane with `P3 = false` exits. -/
theorem vaLoop_first_exit (s : RealState) (lane fuel : Nat)
    (hp : s.preds 3 lane = false) :
    runRealCFLaneWith stepVAL vaLoopProgram s 17 (fuel + 1) lane =
      runRealCFLaneWith stepVAL vaLoopProgram s 44 fuel lane := by
  apply runRealCFLane_gotoIf_taken stepVAL vaLoopProgram s 17 fuel lane 32 3 true
    "_0_007" 44
  · exact vaLoopProgram_gotoIf_first
  · simp [hp]
  · exact vaLoopProgram_label_exit

/-- At the first branch site, a lane with `P3 = true` falls through to the body. -/
theorem vaLoop_first_body (s : RealState) (lane fuel : Nat)
    (hp : s.preds 3 lane = true) :
    runRealCFLaneWith stepVAL vaLoopProgram s 17 (fuel + 1) lane =
      runRealCFLaneWith stepVAL vaLoopProgram s 18 fuel lane := by
  apply runRealCFLane_gotoIf_not_taken stepVAL vaLoopProgram s 17 fuel lane 32 3 true
    "_0_007"
  · exact vaLoopProgram_gotoIf_first
  · simp [hp]

/-- At the second branch site, a lane with `P6 = false` exits. -/
theorem vaLoop_second_exit (s : RealState) (lane fuel : Nat)
    (hp : s.preds 6 lane = false) :
    runRealCFLaneWith stepVAL vaLoopProgram s 35 (fuel + 1) lane =
      runRealCFLaneWith stepVAL vaLoopProgram s 44 fuel lane := by
  apply runRealCFLane_gotoIf_taken stepVAL vaLoopProgram s 35 fuel lane 32 6 true
    "_0_007" 44
  · exact vaLoopProgram_gotoIf_second
  · simp [hp]
  · exact vaLoopProgram_label_exit

/-- At the second branch site, a lane with `P6 = true` falls through to select/writeback. -/
theorem vaLoop_second_select (s : RealState) (lane fuel : Nat)
    (hp : s.preds 6 lane = true) :
    runRealCFLaneWith stepVAL vaLoopProgram s 35 (fuel + 1) lane =
      runRealCFLaneWith stepVAL vaLoopProgram s 36 fuel lane := by
  apply runRealCFLane_gotoIf_not_taken stepVAL vaLoopProgram s 35 fuel lane 32 6 true
    "_0_007"
  · exact vaLoopProgram_gotoIf_second
  · simp [hp]

end
end IntelGpu
