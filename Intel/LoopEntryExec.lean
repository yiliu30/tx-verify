-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.VectorAddLoopProgram
public import Intel.LoopDwordStep

@[expose] public section

/-!
# Executing the decoded loop-entry slice

At PCs 18--20 the loop vector add falls through from the first guard into the
body.  The three entries are the `_0_008` label, the stride move into
`V0067`, and the `_0_009` body label.  This module proves the decoded slice,
its memory and state frames, and the value written by the move.
-/

namespace IntelGpu

noncomputable section

/-- The three decoded entries at PCs 18--20. -/
def vaLoopEntryPrefix : List RInstr :=
  [ .label "_0_008",
    .mov (Exec.nm 1) ⟨67, 0, 0, 1, 1, 1⟩ ⟨68, 0, 0, 0, 1, 0⟩,
    .label "_0_009" ]

/-- The decoded program slice at PCs 18--20 is the loop-entry prefix. -/
theorem vaLoopEntrySlice_eq :
    (vaLoopProgram.drop 18).take 3 = vaLoopEntryPrefix := by
  decide

/-- Labels are the identity instruction under the loop step. -/
theorem stepLoop_label (s : RealState) (name : String) :
    stepLoop s (.label name) = s := by
  simp [stepLoop, stepVAL, stepWith]

/-- The entry prefix does not change memory. -/
theorem vaLoopEntryPrefix_mem (s : RealState) :
    (runRealWith stepLoop s vaLoopEntryPrefix).mem = s.mem := by
  unfold vaLoopEntryPrefix runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  simp [stepLoop, stepVAL, stepWith, writeMaskedWith]

/-- The move writes the lane-zero value of `V0067` from `V0068`, which aliases
`V0037`. -/
theorem vaLoopEntryPrefix_reg67 (s : RealState) :
    (runRealWith stepLoop s vaLoopEntryPrefix).regs 67 0 = s.regs 37 0 := by
  unfold vaLoopEntryPrefix runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  simp [stepLoop, stepVAL, stepWith, writeMaskedWith, Exec.nm, vaLoopAlias,
    Exec.laneActive, readSrcWith, readRegWith, srcIndex]

/-- The entry prefix leaves every element of `V0059` unchanged. -/
theorem vaLoopEntryPrefix_preserves59 (s : RealState) (j : Nat) :
    (runRealWith stepLoop s vaLoopEntryPrefix).regs 59 j = s.regs 59 j := by
  unfold vaLoopEntryPrefix runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  simp [stepLoop, stepVAL, stepWith, writeMaskedWith, Exec.nm, vaLoopAlias]

/-- The entry prefix leaves every physical register other than `V0067`
unchanged. -/
theorem vaLoopEntryPrefix_preserves_reg (s : RealState) (r j : Nat)
    (h : vaLoopAlias r ≠ 67) :
    (runRealWith stepLoop s vaLoopEntryPrefix).regs (vaLoopAlias r) j =
      s.regs (vaLoopAlias r) j := by
  have hmov : (stepLoop s (.mov (Exec.nm 1) ⟨67, 0, 0, 1, 1, 1⟩
      ⟨68, 0, 0, 0, 1, 0⟩)).regs (vaLoopAlias r) j =
      s.regs (vaLoopAlias r) j := by
    apply stepLoop_mov_preserves_reg
    simpa [vaLoopAlias] using (Ne.symm h)
  unfold vaLoopEntryPrefix runRealWith
  simp only [List.foldl_cons, List.foldl_nil, stepLoop_label]
  exact hmov

/-- The entry prefix keeps the source register `V0037` intact. -/
theorem vaLoopEntryPrefix_preserves37 (s : RealState) (j : Nat) :
    (runRealWith stepLoop s vaLoopEntryPrefix).regs 37 j = s.regs 37 j := by
  simpa [vaLoopAlias] using vaLoopEntryPrefix_preserves_reg s 37 j (by decide)

/-- The entry prefix leaves predicates unchanged. -/
theorem vaLoopEntryPrefix_preds (s : RealState) (p j : Nat) :
    (runRealWith stepLoop s vaLoopEntryPrefix).preds p j = s.preds p j := by
  unfold vaLoopEntryPrefix runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  simp [stepLoop, stepVAL, stepWith, writeMaskedWith, Exec.nm]

/-- The entry prefix leaves the halt flag unchanged. -/
theorem vaLoopEntryPrefix_halted (s : RealState) :
    (runRealWith stepLoop s vaLoopEntryPrefix).halted = s.halted := by
  unfold vaLoopEntryPrefix runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  simp [stepLoop, stepVAL, stepWith, writeMaskedWith, Exec.nm]

/-- The decoded PCs 18--20 leave memory unchanged. -/
theorem vaLoopEntrySlice_mem (s : RealState) :
    (runRealWith stepLoop s ((vaLoopProgram.drop 18).take 3)).mem = s.mem := by
  rw [vaLoopEntrySlice_eq]
  exact vaLoopEntryPrefix_mem s

/-- The decoded PCs 18--20 move `V0068` (alias `V0037`) into `V0067` lane 0. -/
theorem vaLoopEntrySlice_reg67 (s : RealState) :
    (runRealWith stepLoop s ((vaLoopProgram.drop 18).take 3)).regs 67 0 =
      s.regs 37 0 := by
  rw [vaLoopEntrySlice_eq]
  exact vaLoopEntryPrefix_reg67 s

/-- The decoded PCs 18--20 leave `V0059` unchanged. -/
theorem vaLoopEntrySlice_preserves59 (s : RealState) (j : Nat) :
    (runRealWith stepLoop s ((vaLoopProgram.drop 18).take 3)).regs 59 j =
      s.regs 59 j := by
  rw [vaLoopEntrySlice_eq]
  exact vaLoopEntryPrefix_preserves59 s j

end
end IntelGpu
