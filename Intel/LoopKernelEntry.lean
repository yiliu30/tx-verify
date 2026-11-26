-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.LoopGuardPath
public import Intel.VectorAddLoop

@[expose] public section

/-!
# The decoded kernel entry from PC 0

`Intel/LoopGuardPath` proves the memory effect from PC 8. This module runs the
eight decoded instructions at PC 0--7, shows that `stepLoop` agrees with the
uniform `stepVAL` semantics there, and composes the launch facts with the
guarded path.

The resulting theorem `vaLoop_kernel_pc0_mem` starts at PC 0 with the launch
registers, the size constant and the three pointers, and concludes the
`C[id] = A[id] + B[id]` effect on the PC 44 state.
-/

namespace IntelGpu

noncomputable section

/-! ## Running the preamble -/

/-- SC 0--7 run to PC 8 with the preamble state. -/
theorem vaLoopCFPreamble (s : RealState) (lane fuel : Nat) :
    runRealCFLaneWith stepLoop vaLoopProgram s 0 (fuel + 8) lane =
      runRealCFLaneWith stepLoop vaLoopProgram
        (runRealWith stepLoop s vaLoopPreamble) 8 fuel lane := by
  rw [runRealCFLaneWith_label stepLoop vaLoopProgram s lane 0 (fuel + 7)
    "_main_0" (by decide)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram s lane 1 (fuel + 6)
    .prologue (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop s .prologue) lane 2 (fuel + 5)
    (.mov (Exec.nm 2) ⟨49, 0, 0, 1, 1, 1⟩ ⟨50, 0, 0, 1, 1, 0⟩)
    (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop s .prologue)
      (.mov (Exec.nm 2) ⟨49, 0, 0, 1, 1, 1⟩ ⟨50, 0, 0, 1, 1, 0⟩))
    lane 3 (fuel + 4)
    (.mul (Exec.nm 1) ⟨51, 0, 0, 1, 1, 1⟩ ⟨52, 0, 0, 0, 1, 0⟩
      ⟨53, 0, 1, 0, 1, 0⟩) (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop (stepLoop s .prologue)
      (.mov (Exec.nm 2) ⟨49, 0, 0, 1, 1, 1⟩ ⟨50, 0, 0, 1, 1, 0⟩))
      (.mul (Exec.nm 1) ⟨51, 0, 0, 1, 1, 1⟩ ⟨52, 0, 0, 0, 1, 0⟩
        ⟨53, 0, 1, 0, 1, 0⟩))
    lane 4 (fuel + 3)
    (.mov 32 ⟨54, 0, 0, 1, 1, 1⟩ ⟨55, 0, 0, 1, 1, 0⟩)
    (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop (stepLoop (stepLoop s .prologue)
      (.mov (Exec.nm 2) ⟨49, 0, 0, 1, 1, 1⟩ ⟨50, 0, 0, 1, 1, 0⟩))
      (.mul (Exec.nm 1) ⟨51, 0, 0, 1, 1, 1⟩ ⟨52, 0, 0, 0, 1, 0⟩
        ⟨53, 0, 1, 0, 1, 0⟩))
      (.mov 32 ⟨54, 0, 0, 1, 1, 1⟩ ⟨55, 0, 0, 1, 1, 0⟩))
    lane 5 (fuel + 2)
    (.add 32 ⟨56, 0, 0, 1, 1, 1⟩ ⟨51, 0, 0, 0, 1, 0⟩ ⟨54, 0, 0, 1, 1, 0⟩)
    (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop s .prologue)
      (.mov (Exec.nm 2) ⟨49, 0, 0, 1, 1, 1⟩ ⟨50, 0, 0, 1, 1, 0⟩))
      (.mul (Exec.nm 1) ⟨51, 0, 0, 1, 1, 1⟩ ⟨52, 0, 0, 0, 1, 0⟩
        ⟨53, 0, 1, 0, 1, 0⟩))
      (.mov 32 ⟨54, 0, 0, 1, 1, 1⟩ ⟨55, 0, 0, 1, 1, 0⟩))
      (.add 32 ⟨56, 0, 0, 1, 1, 1⟩ ⟨51, 0, 0, 0, 1, 0⟩ ⟨54, 0, 0, 1, 1, 0⟩))
    lane 6 (fuel + 1)
    (.mov (Exec.nm 1) ⟨57, 0, 0, 1, 1, 1⟩ ⟨58, 0, 0, 0, 1, 0⟩)
    (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop s .prologue)
      (.mov (Exec.nm 2) ⟨49, 0, 0, 1, 1, 1⟩ ⟨50, 0, 0, 1, 1, 0⟩))
      (.mul (Exec.nm 1) ⟨51, 0, 0, 1, 1, 1⟩ ⟨52, 0, 0, 0, 1, 0⟩
        ⟨53, 0, 1, 0, 1, 0⟩))
      (.mov 32 ⟨54, 0, 0, 1, 1, 1⟩ ⟨55, 0, 0, 1, 1, 0⟩))
      (.add 32 ⟨56, 0, 0, 1, 1, 1⟩ ⟨51, 0, 0, 0, 1, 0⟩ ⟨54, 0, 0, 1, 1, 0⟩))
      (.mov (Exec.nm 1) ⟨57, 0, 0, 1, 1, 1⟩ ⟨58, 0, 0, 0, 1, 0⟩))
    lane 7 fuel
    (.add 32 ⟨59, 0, 0, 1, 1, 1⟩ ⟨56, 0, 0, 1, 1, 0⟩ ⟨57, 0, 0, 0, 1, 0⟩)
    (by decide) (by trivial)]
  rfl

/-! ## Preamble registers under `stepLoop` -/

/-- The preamble writes only `V0049`, `V0051`, `V0054`, `V0056`, `V0057` and
`V0059`. -/
theorem vaLoopPreamble_stepLoop_preserves_reg (s : RealState) (r j : Nat)
    (h49 : r ≠ 49) (h51 : r ≠ 51) (h54 : r ≠ 54) (h56 : r ≠ 56)
    (h57 : r ≠ 57) (h59 : r ≠ 59) :
    (runRealWith stepLoop s vaLoopPreamble).regs r j = s.regs r j := by
  unfold vaLoopPreamble runRealWith
  simp [stepLoop, stepVAL, stepWith, writeMaskedWith, writeVecWith, setReg,
    readSrcWith, srcIndex, vaLoopAlias, vaLoopRegType, isWideOf, RegType.is64,
    binOpWide, Exec.nm, Exec.laneActive, h49, h51, h54, h56, h57, h59]

/-- The preamble's two size dwords. -/
theorem vaLoopPreamble_stepLoop_size (s : RealState) (sizeLo sizeHi : Word)
    (h : VaLoopSizePre s sizeLo sizeHi) :
    (runRealWith stepLoop s vaLoopPreamble).regs 49 0 = zext sizeLo ∧
    (runRealWith stepLoop s vaLoopPreamble).regs 49 1 = zext sizeHi := by
  have hnm : (Exec.nm 2).noMask = true := rfl
  have h0 : (Exec.nm 2).laneActive 0 = true := by decide
  have h1 : (Exec.nm 2).laneActive 1 = true := by decide
  unfold vaLoopPreamble runRealWith
  simp [stepLoop, stepVAL, stepWith, writeMaskedWith, writeVecWith, setReg,
    readSrcWith, readRegWith, srcIndex, vaLoopAlias, vaLoopRegType, isWideOf,
    RegType.is64, binOpWide, hnm, h0, h1, h.loReg, h.hiReg]

/-- The preamble's per-lane index, for the lanes the final add writes. -/
theorem vaLoopPreamble_stepLoop_id (s : RealState) (localSize r0 globalOffset : Word)
    (localId : Nat → BitVec 16) (l : Nat) (hl : l < 32)
    (h : VaLoopLaunch s localSize r0 globalOffset localId) :
    (runRealWith stepLoop s vaLoopPreamble).regs 59 l =
      vaLoopId localSize r0 globalOffset localId l := by
  have hnm : (32 : Exec).noMask = false := rfl
  have hoff : (32 : Exec).offset = 0 := rfl
  have hsz : (32 : Exec).size = 32 := rfl
  have hactive : (32 : Exec).laneActive l = true := by
    simp [Exec.laneActive, hnm, hoff, hsz, hl]
  have hnm1 : (Exec.nm 1).noMask = true := rfl
  have h0 : (Exec.nm 1).laneActive 0 = true := by decide
  unfold vaLoopPreamble runRealWith
  simp [stepLoop, stepVAL, stepWith, writeMaskedWith, writeVecWith, setReg,
    readSrcWith, readRegWith, srcIndex, vaLoopAlias, vaLoopRegType, isWideOf,
    RegType.is64, binOpWide, hnm, hoff, hactive, hnm1, h0,
    h.localSizeReg, h.r0Reg, h.localIdReg, h.offsetReg, vaLoopId]

/-! ## Size halves -/

/-- Truncating the packed size recovers the low half. -/
theorem vaLoopSize_truncate (lo hi : Word) :
    (vaLoopSize lo hi).truncate 32 = lo := by
  unfold vaLoopSize
  bv_decide

/-- Shifting and truncating the packed size recovers the high half. -/
theorem vaLoopSize_shift_truncate (lo hi : Word) :
    ((vaLoopSize lo hi) >>> 32).truncate 32 = hi := by
  unfold vaLoopSize
  bv_decide

/-- The preamble leaves memory unchanged under `stepLoop`. -/
theorem vaLoopPreamble_stepLoop_mem (s : RealState) :
    (runRealWith stepLoop s vaLoopPreamble).mem = s.mem := by
  unfold vaLoopPreamble runRealWith
  simp [stepLoop, stepVAL, stepWith, writeMaskedWith, writeVecWith]

/-! ## The whole kernel entry -/

/-- The decoded kernel writes `C[id] = A[id] + B[id]` starting at PC 0.

The launch facts produce the index, the size constant gives the two guard
halves, and the range bound makes the second guard false. The remaining
hypotheses are the body's memory-safety conditions. -/
theorem vaLoop_kernel_pc0_mem (s : RealState) (lane fuel : Nat)
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
    (runRealCFLaneWith stepLoop vaLoopProgram s 0 (fuel + 8 + 28) lane).mem
        (cPtr.toNat / 4 + (vaLoopId localSize r0 globalOffset localId l).toNat) =
      s.mem (aPtr.toNat / 4 + (vaLoopId localSize r0 globalOffset localId l).toNat) +
        s.mem (bPtr.toNat / 4 + (vaLoopId localSize r0 globalOffset localId l).toNat) := by
  let idxFull : Nat → Addr := fun k =>
    if k < 32 then vaLoopId localSize r0 globalOffset localId k
    else (runRealWith stepLoop s vaLoopPreamble).regs 59 k
  have hidx : ∀ k, (runRealWith stepLoop s vaLoopPreamble).regs 59 k = idxFull k := by
    intro k
    by_cases hk : k < 32
    · simp [idxFull, hk,
        vaLoopPreamble_stepLoop_id s localSize r0 globalOffset localId k hk hlaunch]
    · simp [idxFull, hk]
  have hpre : VaLoopBodyPre (runRealWith stepLoop s vaLoopPreamble)
      aPtr bPtr cPtr idxFull := by
    refine ⟨?_, ?_, ?_, hidx⟩
    · simpa using (vaLoopPreamble_stepLoop_preserves_reg s 47 0 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)).trans h47
    · simpa using (vaLoopPreamble_stepLoop_preserves_reg s 48 0 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)).trans h48
    · simpa using (vaLoopPreamble_stepLoop_preserves_reg s 46 0 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)).trans h46
  have hslo : low32 ((runRealWith stepLoop s vaLoopPreamble).regs 49 0) =
      (vaLoopSize sizeLo sizeHi).truncate 32 := by
    rw [(vaLoopPreamble_stepLoop_size s sizeLo sizeHi hsize).1, vaLoopSize_truncate]
    simp
  have hshi : low32 ((runRealWith stepLoop s vaLoopPreamble).regs 49 1) =
      ((vaLoopSize sizeLo sizeHi) >>> 32).truncate 32 := by
    rw [(vaLoopPreamble_stepLoop_size s sizeLo sizeHi hsize).2, vaLoopSize_shift_truncate]
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
  have hboundC' : ∀ k, k < 32 →
      cPtr.toNat + 4 * (idxFull k).toNat < 2 ^ 64 := by
    intro k hk
    simpa [idxFull, hk] using hboundC k hk
  have hab' : aPtr.toNat + 4 * (idxFull l).toNat < 2 ^ 64 := by
    simpa [idxFull, hl] using hab
  have hbb' : bPtr.toNat + 4 * (idxFull l).toNat < 2 ^ 64 := by
    simpa [idxFull, hl] using hbb
  have hcb' : cPtr.toNat + 4 * (idxFull l).toNat < 2 ^ 64 := by
    simpa [idxFull, hl] using hcb
  have hdistinct' : ∀ k, k < 32 → k ≠ l →
      cPtr.toNat / 4 + (idxFull k).toNat ≠
        cPtr.toNat / 4 + (idxFull l).toNat := by
    intro k hk hne
    simpa [idxFull, hk, hl] using hdistinct k hk hne
  rw [show fuel + 8 + 28 = (fuel + 28) + 8 from by omega,
    vaLoopCFPreamble s lane (fuel + 28)]
  have hmain := vaLoop_lane_body_exit_pc8_mem (runRealWith stepLoop s vaLoopPreamble)
    lane fuel aPtr bPtr cPtr idxFull (vaLoopSize sizeLo sizeHi) hpre l hl ha hb hc
    hab' hbb' hcb' hboundC' hdistinct' h37' hslo hshi hP3' hj hbound'
  simpa [idxFull, hl, vaLoopPreamble_stepLoop_mem s] using hmain

end

end IntelGpu
