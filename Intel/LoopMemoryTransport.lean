-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.LoopEndToEnd
public import Intel.LoopBodyExec
public import Intel.LoopP6Exec
public import Intel.LoopIncExec

@[expose] public section

/-!
# Transporting the loop body's memory effect through the decoded path

`Intel.LoopBodyExec` proves that the four decoded body instructions store each
lane's `A[id] + B[id]` at `C[id]`. `Intel.LoopEndToEnd` proves that a lane which
enters at PC 17 and has `P3 = true` reaches PC 44 after the decoded entry, body,
increment and second-guard slices. This module joins the two facts: the
increment and second-guard slices are register/predicate-only, so they preserve
the post-body memory, and the entry slice preserves the body's pointer
registers and index.
-/

namespace IntelGpu

noncomputable section

/-! ## Post-body memory frames -/

/-- The increment add writes `V0072` only and therefore leaves memory alone. -/
theorem vaLoopIncAdd_mem (s : RealState) :
    (runRealWith stepLoop s vaLoopIncAdd).mem = s.mem := by
  unfold vaLoopIncAdd runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  simp [stepLoop, stepVAL, stepWith, writeVecWith]

/-- A plain move, including the dword-view branches, never touches memory. -/
theorem stepLoop_mov_mem (s : RealState) (e : Exec) (dst src : Grf) :
    (stepLoop s (.mov e dst src)).mem = s.mem := by
  by_cases h61 : src.num = 61 <;> by_cases h74 : src.num = 74 <;>
    simp [stepLoop, h61, h74, writeMaskedWith]

/-- A masked move, including the dword-view branches, never touches memory. -/
theorem stepLoop_movMasked_mem (s : RealState) (e : Exec) (dst src : Grf) :
    (stepLoop s (.movMasked e dst src)).mem = s.mem := by
  by_cases h61 : src.num = 61 <;> by_cases h74 : src.num = 74 <;>
    simp [stepLoop, h61, h74, writeMaskedWith]

/-- The low increment pack preserves memory. -/
theorem vaPackIncLow_mem (s : RealState) :
    (runRealWith stepLoop s vaPackIncLow).mem = s.mem := by
  unfold vaPackIncLow runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  rw [stepLoop_movMasked_mem, stepLoop_mov_mem]

/-- The high increment pack preserves memory. -/
theorem vaPackIncHigh_mem (s : RealState) :
    (runRealWith stepLoop s vaPackIncHigh).mem = s.mem := by
  unfold vaPackIncHigh runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  rw [stepLoop_movMasked_mem, stepLoop_mov_mem]

/-- The second guard block only writes predicate registers. -/
theorem vaGuardBlock2_mem (s : RealState) :
    (runRealWith stepLoop s vaGuardBlock2).mem = s.mem := by
  unfold vaGuardBlock2 runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  simp [stepLoop, stepVAL, stepWith]

/-- The two increment packs and the second guard block contain no store. -/
theorem vaLoopP6Prefix_mem (s : RealState) :
    (runRealWith stepLoop s vaLoopP6Prefix).mem = s.mem := by
  rw [vaLoopP6Prefix, runRealWith_append, runRealWith_append]
  rw [vaGuardBlock2_mem, vaPackIncHigh_mem, vaPackIncLow_mem]

/-! ## Entry-state transport -/

/-- The entry slice changes only `V0067`, so it preserves the body's three
pointer registers and carried index. -/
theorem vaLoopEntryPrefix_bodyPre (s : RealState) (aPtr bPtr cPtr : Addr)
    (idx : Nat → Addr) (h : VaLoopBodyPre s aPtr bPtr cPtr idx) :
    VaLoopBodyPre (runRealWith stepLoop s vaLoopEntryPrefix) aPtr bPtr cPtr idx := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [vaLoopAlias] using
      (vaLoopEntryPrefix_preserves_reg s 47 0 (by decide)).trans h.aReg
  · simpa [vaLoopAlias] using
      (vaLoopEntryPrefix_preserves_reg s 48 0 (by decide)).trans h.bReg
  · simpa [vaLoopAlias] using
      (vaLoopEntryPrefix_preserves_reg s 46 0 (by decide)).trans h.cReg
  · intro l
    simpa [vaLoopAlias] using
      (vaLoopEntryPrefix_preserves_reg s 59 l (by decide)).trans (h.idxReg l)

/-! ## Whole-path memory -/

/-- The whole decoded path has the same memory as the state immediately after
the body: the entry slice preserves memory, while the increment and second
guard slices only write registers and predicates. -/
theorem vaLoopPathPrefix_mem (s : RealState) :
    (runRealWith stepLoop s vaLoopPathPrefix).mem =
      (runRealWith stepLoop
        (runRealWith stepLoop s vaLoopEntryPrefix) vaLoopBodySlice).mem := by
  simp only [vaLoopPathPrefix, runRealWith_append]
  simp only [vaLoopIncAdd_mem, vaLoopP6Prefix_mem]

/-- The decoded path's memory stores the lane sum at `C[id]`. -/
theorem vaLoop_lane_path_mem (s : RealState) (aPtr bPtr cPtr : Addr)
    (idx : Nat → Addr) (h : VaLoopBodyPre s aPtr bPtr cPtr idx) (l : Nat)
    (hl : l < 32) (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0)
    (hc : cPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (idx l).toNat < 2 ^ 64)
    (hbb : bPtr.toNat + 4 * (idx l).toNat < 2 ^ 64)
    (hcb : cPtr.toNat + 4 * (idx l).toNat < 2 ^ 64)
    (hboundC : ∀ k, k < 32 → cPtr.toNat + 4 * (idx k).toNat < 2 ^ 64)
    (hdistinct : ∀ k, k < 32 → k ≠ l → cPtr.toNat / 4 + (idx k).toNat ≠
      cPtr.toNat / 4 + (idx l).toNat) :
    (runRealWith stepLoop s vaLoopPathPrefix).mem
        (cPtr.toNat / 4 + (idx l).toNat) =
      s.mem (aPtr.toNat / 4 + (idx l).toNat) +
        s.mem (bPtr.toNat / 4 + (idx l).toNat) := by
  have hpre := vaLoopEntryPrefix_bodyPre s aPtr bPtr cPtr idx h
  have hstore := vaLoopBodySlice_store_at (runRealWith stepLoop s vaLoopEntryPrefix)
    aPtr bPtr cPtr idx hpre l hl ha hb hc hab hbb hcb hboundC hdistinct
  rw [vaLoopEntryPrefix_mem s] at hstore
  rw [vaLoopPathPrefix_mem s]
  exact hstore

/-! ## PC 44 target states -/

/-- The same memory fact on the PC 44 state reached by the per-lane exit path. -/
theorem vaLoop_lane_body_exit_mem (s : RealState) (lane fuel : Nat)
    (aPtr bPtr cPtr : Addr) (idx : Nat → Addr)
    (h : VaLoopBodyPre s aPtr bPtr cPtr idx) (l : Nat)
    (hl : l < 32) (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0)
    (hc : cPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (idx l).toNat < 2 ^ 64)
    (hbb : bPtr.toNat + 4 * (idx l).toNat < 2 ^ 64)
    (hcb : cPtr.toNat + 4 * (idx l).toNat < 2 ^ 64)
    (hboundC : ∀ k, k < 32 → cPtr.toNat + 4 * (idx k).toNat < 2 ^ 64)
    (hdistinct : ∀ k, k < 32 → k ≠ l → cPtr.toNat / 4 + (idx k).toNat ≠
      cPtr.toNat / 4 + (idx l).toNat)
    (hP3 : s.preds 3 lane = true)
    (hP6 : (runRealWith stepLoop s vaLoopPathPrefix).preds 6 lane = false) :
    (runRealCFLaneWith stepLoop vaLoopProgram s 17 (fuel + 19) lane).mem
        (cPtr.toNat / 4 + (idx l).toNat) =
      s.mem (aPtr.toNat / 4 + (idx l).toNat) +
        s.mem (bPtr.toNat / 4 + (idx l).toNat) := by
  rw [vaLoop_lane_body_exit s lane fuel hP3 hP6]
  rw [vaLoopCFLane_exit_mem]
  exact vaLoop_lane_path_mem s aPtr bPtr cPtr idx h l hl ha hb hc hab hbb hcb
    hboundC hdistinct

/-- The PC 44 memory fact with the exit condition supplied by the real second
guard instead of an abstract `P6 = false`. -/
theorem vaLoop_lane_body_exit_with_guard_mem (s : RealState) (lane fuel : Nat)
    (aPtr bPtr cPtr : Addr) (idx : Nat → Addr)
    (h : VaLoopBodyPre s aPtr bPtr cPtr idx) (l : Nat)
    (hl : l < 32) (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0)
    (hc : cPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (idx l).toNat < 2 ^ 64)
    (hbb : bPtr.toNat + 4 * (idx l).toNat < 2 ^ 64)
    (hcb : cPtr.toNat + 4 * (idx l).toNat < 2 ^ 64)
    (hboundC : ∀ k, k < 32 → cPtr.toNat + 4 * (idx k).toNat < 2 ^ 64)
    (hdistinct : ∀ k, k < 32 → k ≠ l → cPtr.toNat / 4 + (idx k).toNat ≠
      cPtr.toNat / 4 + (idx l).toNat)
    (ids : Nat → Addr) (sizeLo sizeHi : Word)
    (hP3 : s.preds 3 lane = true) (hj : lane < 24)
    (hid : ∀ k, (vaLoopPreP6 s).regs 72 k = ids k)
    (hslo : low32 ((vaLoopPreP6 s).regs 49 0) = sizeLo)
    (hshi : low32 ((vaLoopPreP6 s).regs 49 1) = sizeHi)
    (hguard : vaLoopGuard (ids lane) (vaLoopSize sizeLo sizeHi) = false) :
    (runRealCFLaneWith stepLoop vaLoopProgram s 17 (fuel + 19) lane).mem
        (cPtr.toNat / 4 + (idx l).toNat) =
      s.mem (aPtr.toNat / 4 + (idx l).toNat) +
        s.mem (bPtr.toNat / 4 + (idx l).toNat) := by
  rw [vaLoop_lane_body_exit_with_guard s lane fuel ids sizeLo sizeHi hP3 hj hid
    hslo hshi hguard]
  rw [vaLoopCFLane_exit_mem]
  exact vaLoop_lane_path_mem s aPtr bPtr cPtr idx h l hl ha hb hc hab hbb hcb
    hboundC hdistinct

end

end IntelGpu
