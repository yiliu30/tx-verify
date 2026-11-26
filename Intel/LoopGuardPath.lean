-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.LoopMemoryTransport
public import Intel.LoopP3Exec
public import Intel.LoopP6Size

@[expose] public section

/-!
# Deriving the loop path's guards from the decoded prefix

`Intel.LoopMemoryTransport` proves the per-lane memory effect on the PC 17
path, but it takes `P3 = true` from the entry state and the second-guard
premises as hypotheses. This module removes those hypotheses:

- `runRealCFLaneWith_straight` executes any list of non-control instructions
  starting at a program counter, so a decoded slice can be run from PC 8;
- `vaLoopCFP3` runs the nine decoded instructions at PC 8--16 and lands at
  PC 17 with the exact `runRealWith` state;
- `vaLoopP3Prefix_preserves_reg` and the body frames show which registers the
  packs, body and increment leave alone;
- `vaLoopPreP6_regs72` computes the pre-guard index as `V59 + V37`, and
  `vaLoopPreP6_preserves49` keeps the bound registers intact;
- `vaLoop_lane_body_exit_pc8_mem` therefore starts at PC 8 and needs only the
  real P3 guard, the range bound, and the body's memory-safety hypotheses.
-/

namespace IntelGpu

noncomputable section

/-! ## The decoded PC 8--16 slice -/

/-- The nine decoded instructions at PC 8--16 run to PC 17, where the state is
the fold of the pack/guard prefix. -/
theorem vaLoopCFP3 (s : RealState) (lane fuel : Nat) :
    runRealCFLaneWith stepLoop vaLoopProgram s 8 (fuel + 9) lane =
      runRealCFLaneWith stepLoop vaLoopProgram
        (runRealWith stepLoop s vaLoopP3Prefix) 17 fuel lane := by
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram s lane 8 (fuel + 8)
    (.mov e1Loop dst62a src61a) (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop s (.mov e1Loop dst62a src61a)) lane 9 (fuel + 7)
    (.movMasked e2Loop dst62b src61b) (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop s (.mov e1Loop dst62a src61a))
      (.movMasked e2Loop dst62b src61b)) lane 10 (fuel + 6)
    (.mov e1Loop dst63a src61aHigh) (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop (stepLoop s (.mov e1Loop dst62a src61a))
      (.movMasked e2Loop dst62b src61b)) (.mov e1Loop dst63a src61aHigh))
    lane 11 (fuel + 5) (.movMasked e2Loop dst63b src61bHigh) (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop (stepLoop (stepLoop s (.mov e1Loop dst62a src61a))
      (.movMasked e2Loop dst62b src61b)) (.mov e1Loop dst63a src61aHigh))
      (.movMasked e2Loop dst63b src61bHigh)) lane 12 (fuel + 4)
    (.cmpLtReg 32 1 ⟨64, 0, 0, 1, 1, 0⟩ ⟨65, 0, 0, 0, 1, 0⟩)
    (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop s (.mov e1Loop dst62a src61a))
      (.movMasked e2Loop dst62b src61b)) (.mov e1Loop dst63a src61aHigh))
      (.movMasked e2Loop dst63b src61bHigh))
      (.cmpLtReg 32 1 ⟨64, 0, 0, 1, 1, 0⟩ ⟨65, 0, 0, 0, 1, 0⟩))
    lane 13 (fuel + 3) (.cmpEqReg 32 2 ⟨63, 0, 0, 1, 1, 0⟩ ⟨49, 0, 1, 0, 1, 0⟩)
    (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop s
      (.mov e1Loop dst62a src61a)) (.movMasked e2Loop dst62b src61b))
      (.mov e1Loop dst63a src61aHigh)) (.movMasked e2Loop dst63b src61bHigh))
      (.cmpLtReg 32 1 ⟨64, 0, 0, 1, 1, 0⟩ ⟨65, 0, 0, 0, 1, 0⟩))
      (.cmpEqReg 32 2 ⟨63, 0, 0, 1, 1, 0⟩ ⟨49, 0, 1, 0, 1, 0⟩))
    lane 14 (fuel + 2) (.predAnd 32 2 2 1) (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop s
      (.mov e1Loop dst62a src61a)) (.movMasked e2Loop dst62b src61b))
      (.mov e1Loop dst63a src61aHigh)) (.movMasked e2Loop dst63b src61bHigh))
      (.cmpLtReg 32 1 ⟨64, 0, 0, 1, 1, 0⟩ ⟨65, 0, 0, 0, 1, 0⟩))
      (.cmpEqReg 32 2 ⟨63, 0, 0, 1, 1, 0⟩ ⟨49, 0, 1, 0, 1, 0⟩))
      (.predAnd 32 2 2 1))
    lane 15 (fuel + 1) (.cmpLtReg 32 3 ⟨66, 0, 0, 1, 1, 0⟩ ⟨65, 0, 1, 0, 1, 0⟩)
    (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop s
      (.mov e1Loop dst62a src61a)) (.movMasked e2Loop dst62b src61b))
      (.mov e1Loop dst63a src61aHigh)) (.movMasked e2Loop dst63b src61bHigh))
      (.cmpLtReg 32 1 ⟨64, 0, 0, 1, 1, 0⟩ ⟨65, 0, 0, 0, 1, 0⟩))
      (.cmpEqReg 32 2 ⟨63, 0, 0, 1, 1, 0⟩ ⟨49, 0, 1, 0, 1, 0⟩))
      (.predAnd 32 2 2 1))
      (.cmpLtReg 32 3 ⟨66, 0, 0, 1, 1, 0⟩ ⟨65, 0, 1, 0, 1, 0⟩))
    lane 16 fuel (.predOr 32 3 3 2) (by decide) (by trivial)]
  rfl

/-! ## Frames for the prefix and the body -/

/-- The pack/guard prefix writes only `V0062`, `V0063` and predicates. -/
theorem vaLoopP3Prefix_preserves_reg (s : RealState) (r j : Nat)
    (h62 : vaLoopAlias r ≠ 62) (h63 : vaLoopAlias r ≠ 63) :
    (runRealWith stepLoop s vaLoopP3Prefix).regs (vaLoopAlias r) j =
      s.regs (vaLoopAlias r) j := by
  unfold vaLoopP3Prefix vaPackLow vaPackHigh vaGuardBlock runRealWith
  have h62' : vaLoopAlias r ≠ vaLoopAlias 62 := by
    rw [show vaLoopAlias 62 = 62 from rfl]
    exact h62
  have h63' : vaLoopAlias r ≠ vaLoopAlias 63 := by
    rw [show vaLoopAlias 63 = 63 from rfl]
    exact h63
  simp [stepLoop, stepVAL, stepWith, writeMaskedWith, e1Loop, e2Loop, dst62a, dst62b,
    src61a, src61b, dst63a, dst63b, src61aHigh, src61bHigh, h62', h63']

/-- The body slice writes only `V0069`, `V0070` and `V0071`. -/
theorem vaLoopBodySlice_preserves_reg (s : RealState) (r j : Nat)
    (h69 : r ≠ 69) (h70 : r ≠ 70) (h71 : r ≠ 71) :
    (runRealWith stepLoop s vaLoopBodySlice).regs r j = s.regs r j := by
  rw [vaLoopBodySlice_eq, vaLoopBody_stepLoop_eq]
  unfold vaLoopBody runVAL stepVAL
  simp [runRealWith, stepWith, writeVecWith, setReg, readRegWith, readSrcWith, srcIndex,
    vaLoopAlias, h69, h70, h71]

/-- The prefix keeps the index register `V0059`. -/
theorem vaLoopP3Prefix_preserves59 (s : RealState) (j : Nat) :
    (runRealWith stepLoop s vaLoopP3Prefix).regs 59 j = s.regs 59 j := by
  simpa [vaLoopAlias] using vaLoopP3Prefix_preserves_reg s 59 j (by decide) (by decide)

/-- The prefix keeps the stride register `V0037`. -/
theorem vaLoopP3Prefix_preserves37 (s : RealState) (j : Nat) :
    (runRealWith stepLoop s vaLoopP3Prefix).regs 37 j = s.regs 37 j := by
  simpa [vaLoopAlias] using vaLoopP3Prefix_preserves_reg s 37 j (by decide) (by decide)

/-- The prefix keeps the bound register `V0049`. -/
theorem vaLoopP3Prefix_preserves49 (s : RealState) (j : Nat) :
    (runRealWith stepLoop s vaLoopP3Prefix).regs 49 j = s.regs 49 j := by
  simpa [vaLoopAlias] using vaLoopP3Prefix_preserves_reg s 49 j (by decide) (by decide)

/-! ## The state just before the second guard -/

/-- The increment produces `V72 = V59 + V67`, and the entry slice set `V67`
from `V68`, which is the canonical `V37`. -/
theorem vaLoopPreP6_regs72 (s : RealState) (l : Nat) :
    (vaLoopPreP6 s).regs 72 l = s.regs 59 l + s.regs 37 0 := by
  unfold vaLoopPreP6
  have hpre : VaLoopIncPre
      (runRealWith stepLoop (runRealWith stepLoop s vaLoopEntryPrefix) vaLoopBodySlice)
      (fun k => s.regs 59 k) (s.regs 37 0) := by
    refine ⟨?_, ?_⟩
    · intro k
      rw [vaLoopBodySlice_preserves_reg _ _ k (by decide) (by decide) (by decide)]
      simpa [vaLoopAlias] using vaLoopEntryPrefix_preserves_reg s 59 k (by decide)
    · rw [vaLoopBodySlice_preserves_reg _ _ 0 (by decide) (by decide) (by decide)]
      simpa [vaLoopAlias] using vaLoopEntryPrefix_reg67 s
  simpa using vaLoopIncAdd_value _ (fun k => s.regs 59 k) (s.regs 37 0) hpre l

/-- The second guard's bound registers are untouched by the entry, body and
increment slices. -/
theorem vaLoopPreP6_preserves49 (s : RealState) (d : Nat) :
    (vaLoopPreP6 s).regs 49 d = s.regs 49 d := by
  unfold vaLoopPreP6
  rw [vaLoopIncAdd_preserves49,
    vaLoopBodySlice_preserves_reg _ _ d (by decide) (by decide) (by decide)]
  simpa [vaLoopAlias] using vaLoopEntryPrefix_preserves_reg s 49 d (by decide)

/-! ## The guarded path from PC 8 -/

/-- The PC 44 memory effect starting at PC 8: the P3 guard is the real decoded
prefix result, and the P6 guard is false by the range bound. -/
theorem vaLoop_lane_body_exit_pc8_mem (s : RealState) (lane fuel : Nat)
    (aPtr bPtr cPtr : Addr) (idx : Nat → Addr) (size : Addr)
    (h : VaLoopBodyPre s aPtr bPtr cPtr idx) (l : Nat)
    (hl : l < 32) (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0)
    (hc : cPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (idx l).toNat < 2 ^ 64)
    (hbb : bPtr.toNat + 4 * (idx l).toNat < 2 ^ 64)
    (hcb : cPtr.toNat + 4 * (idx l).toNat < 2 ^ 64)
    (hboundC : ∀ k, k < 32 → cPtr.toNat + 4 * (idx k).toNat < 2 ^ 64)
    (hdistinct : ∀ k, k < 32 → k ≠ l → cPtr.toNat / 4 + (idx k).toNat ≠
      cPtr.toNat / 4 + (idx l).toNat)
    (hstride : s.regs 37 0 = size)
    (hslo : low32 (s.regs 49 0) = size.truncate 32)
    (hshi : low32 (s.regs 49 1) = (size >>> 32).truncate 32)
    (hP3 : vaLoopGuard (idx lane) size = true) (hj : lane < 24)
    (hbound : (idx lane).toNat + size.toNat < 2 ^ 64) :
    (runRealCFLaneWith stepLoop vaLoopProgram s 8 (fuel + 28) lane).mem
        (cPtr.toNat / 4 + (idx l).toNat) =
      s.mem (aPtr.toNat / 4 + (idx l).toNat) +
        s.mem (bPtr.toNat / 4 + (idx l).toNat) := by
  have hP3' : (runRealWith stepLoop s vaLoopP3Prefix).preds 3 lane = true := by
    rw [vaLoopP3_exec s idx (size.truncate 32) ((size >>> 32).truncate 32) lane hj
      h.idxReg hslo hshi, vaLoopSize_id]
    exact hP3
  have hpre : VaLoopBodyPre (runRealWith stepLoop s vaLoopP3Prefix)
      aPtr bPtr cPtr idx := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [vaLoopAlias] using
        (vaLoopP3Prefix_preserves_reg s 47 0 (by decide) (by decide)).trans h.aReg
    · simpa [vaLoopAlias] using
        (vaLoopP3Prefix_preserves_reg s 48 0 (by decide) (by decide)).trans h.bReg
    · simpa [vaLoopAlias] using
        (vaLoopP3Prefix_preserves_reg s 46 0 (by decide) (by decide)).trans h.cReg
    · intro k
      simpa [vaLoopAlias] using
        (vaLoopP3Prefix_preserves_reg s 59 k (by decide) (by decide)).trans (h.idxReg k)
  have h72 : ∀ k, (vaLoopPreP6 (runRealWith stepLoop s vaLoopP3Prefix)).regs 72 k =
      idx k + size := by
    intro k
    rw [vaLoopPreP6_regs72, vaLoopP3Prefix_preserves59, vaLoopP3Prefix_preserves37,
      h.idxReg k, hstride]
  have hslo' : low32
      ((vaLoopPreP6 (runRealWith stepLoop s vaLoopP3Prefix)).regs 49 0) =
      size.truncate 32 := by
    rw [vaLoopPreP6_preserves49, vaLoopP3Prefix_preserves49]
    exact hslo
  have hshi' : low32
      ((vaLoopPreP6 (runRealWith stepLoop s vaLoopP3Prefix)).regs 49 1) =
      (size >>> 32).truncate 32 := by
    rw [vaLoopPreP6_preserves49, vaLoopP3Prefix_preserves49]
    exact hshi
  have hguard : vaLoopGuard (idx lane + size)
      (vaLoopSize (size.truncate 32) ((size >>> 32).truncate 32)) = false := by
    rw [vaLoopSize_id]
    exact vaLoopNext_guard_false (idx lane) size hbound
  rw [show fuel + 28 = (fuel + 19) + 9 from by omega,
    vaLoopCFP3 s lane (fuel + 19)]
  exact vaLoop_lane_body_exit_with_guard_mem (runRealWith stepLoop s vaLoopP3Prefix)
    lane fuel aPtr bPtr cPtr idx hpre l hl ha hb hc hab hbb hcb hboundC hdistinct
    (fun k => idx k + size) (size.truncate 32) ((size >>> 32).truncate 32)
    hP3' hj h72 hslo' hshi' hguard

end

end IntelGpu
