-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.LoopGridStrideControl
public import Intel.LoopBodyExec

@[expose] public section

/-!
# Dword/qword coalescing at the loop vector add's loop-back

Stage 158 executes the decoded loop-back block at PCs 36--43 and proves that
the qword view of `V0059` becomes the selected grid-stride id:
`vaLoop_loopBack_id`. The raw `RealState` slots, however, hold the 24-lane
dword pack: for `l < 24`, `regs 59 l` is dword slot `l`, while the body at
PC 21 reads `regs 59 l` as one qword lane. This gap is recorded at the end of
`Intel/LoopGridStrideControl`.

This module supplies the explicit hardware interpretation. `coalesceDword`
merges dword slots `2*l` and `2*l+1` into qword lane `l`, and `coalesceReg59`
applies that view to `V0059`. Coalescing is an adapter over the existing
`RealState` model, not a new decoded instruction: it changes only register 59
and leaves every other register, the predicates, memory and the halt flag
unchanged (`coalesceReg59_regs_other`, `coalesceReg59_mem`,
`coalesceReg59_preds`, `coalesceReg59_halted`).

`coalesce_writeback` shows that the adapted `V0059` lane is exactly
`selectId old (old + stride) takeNew` for `l < 24`, with
`takeNew = s.preds 6`. `coalesced_bodyPre` shows that the adapted state
satisfies the body preconditions with the coalesced lanes as its index.
`vaLoop_lane_second_body_literal` composes the decoded second iteration: a
lane with `P6` true falls through to the loop-back, the adapter reconstructs
its qword lane, and the body at PC 21 stores `C[idx] = A[idx] + B[idx]`.

The adapter does not make the raw dword slots equal to qword lanes:
`coalesce_raw_counterexample` exhibits a state where the writeback's raw slot
and the coalesced lane disagree. The coalescing step is therefore the explicit
model boundary, exactly as recorded in stage 158.

The adapter and its frame laws are choice-free. Every theorem that mentions
`stepLoop` inherits `Classical.choice` from its existing `storeVec` branch,
which picks an aliasing lane with `Classical.choose`; this is the same
dependency as stage 158.
-/

namespace IntelGpu

noncomputable section

/-! ## The coalescing adapter -/

/-- Merge dword slots `2*l` and `2*l+1` into qword lane `l`. Only the low 32
bits of each slot are read, matching `dwordReg` and the IGC dword view. -/
def coalesceDword (f : Nat → Addr) (l : Nat) : Addr :=
  ((f (2 * l)).truncate 32).zeroExtend 64 |||
    (((f (2 * l + 1)).truncate 32).zeroExtend 64 <<< 32)

/-- Coalescing a `RealState` register is exactly its `qwordOf` dword view. -/
theorem coalesceDword_qword (s : RealState) (r l : Nat) :
    coalesceDword (fun d => s.regs r d) l = qwordOf (dwordReg s r) l := by
  rfl

/-- If the two dword slots hold the halves of a 64-bit value, coalescing
reconstructs that value; this is `qword_merge` for the adapter. -/
theorem coalesceDword_of_halves (v : Addr) (f : Nat → Addr) (l : Nat)
    (h0 : f (2 * l) = (v.truncate 32).zeroExtend 64)
    (h1 : f (2 * l + 1) = ((v >>> 32).truncate 32).zeroExtend 64) :
    coalesceDword f l = v := by
  simp [coalesceDword, h0, h1]
  exact qword_merge v

/-- Replace every element of register `r` with the qword lane assembled from
its dword slots. -/
def coalesceReg (s : RealState) (r : Nat) : RealState :=
  { s with regs := fun r' e =>
      if r' = r then coalesceDword (fun d => s.regs r d) e else s.regs r' e }

/-- The coalescing adapter for the loop's `V0059`. -/
abbrev coalesceReg59 (s : RealState) : RealState := coalesceReg s 59

/-- The adapted register holds the merged qwords. -/
theorem coalesceReg_regs_self (s : RealState) (r e : Nat) :
    (coalesceReg s r).regs r e = coalesceDword (fun d => s.regs r d) e := by
  simp [coalesceReg]

/-- Every other register is untouched. -/
theorem coalesceReg_regs_other (s : RealState) (r r' e : Nat) (h : r' ≠ r) :
    (coalesceReg s r).regs r' e = s.regs r' e := by
  simp [coalesceReg, h]

/-- Coalescing leaves memory unchanged. -/
theorem coalesceReg_mem (s : RealState) (r : Nat) :
    (coalesceReg s r).mem = s.mem := rfl

/-- Coalescing leaves the predicate file unchanged. -/
theorem coalesceReg_preds (s : RealState) (r p e : Nat) :
    (coalesceReg s r).preds p e = s.preds p e := rfl

/-- Coalescing leaves the halt flag unchanged. -/
theorem coalesceReg_halted (s : RealState) (r : Nat) :
    (coalesceReg s r).halted = s.halted := rfl

/-- The adapted `V0059` lane is the `qwordOf` view of its dword slots. -/
theorem coalesceReg59_qword (s : RealState) (l : Nat) :
    (coalesceReg59 s).regs 59 l = qwordOf (dwordReg s 59) l := by
  rfl

/-- The adapted `V0059` lane is the merged dword pair. -/
theorem coalesceReg59_regs_self (s : RealState) (e : Nat) :
    (coalesceReg59 s).regs 59 e = coalesceDword (fun d => s.regs 59 d) e := by
  simp [coalesceReg59, coalesceReg]

/-- Every register other than 59 is untouched. -/
theorem coalesceReg59_regs_other (s : RealState) (r e : Nat) (h : r ≠ 59) :
    (coalesceReg59 s).regs r e = s.regs r e := by
  simp [coalesceReg59, coalesceReg, h]

/-- The adapted state keeps memory. -/
theorem coalesceReg59_mem (s : RealState) :
    (coalesceReg59 s).mem = s.mem := rfl

/-- The adapted state keeps the predicates. -/
theorem coalesceReg59_preds (s : RealState) (p e : Nat) :
    (coalesceReg59 s).preds p e = s.preds p e := rfl

/-- The adapted state keeps the halt flag. -/
theorem coalesceReg59_halted (s : RealState) :
    (coalesceReg59 s).halted = s.halted := rfl

/-! ## Pointer frame through the decoded loop-back -/

/-- PC 37 writes `V0079` only. -/
theorem vaLoopSelLow_preserves_reg (s : RealState) (r j : Nat) (h : r ≠ 79) :
    (stepLoop s vaLoopSelLow).regs r j = s.regs r j := by
  unfold vaLoopSelLow
  simp [stepLoop, stepVAL, stepWith, writeVecWith, setReg, vaLoopAlias, h]

/-- PC 38 writes `V0080` only. -/
theorem vaLoopSelHigh_preserves_reg (s : RealState) (r j : Nat) (h : r ≠ 80) :
    (stepLoop s vaLoopSelHigh).regs r j = s.regs r j := by
  unfold vaLoopSelHigh
  simp [stepLoop, stepVAL, stepWith, writeVecWith, setReg, vaLoopAlias, h]

/-- PC 39 writes `V0059` only. -/
theorem vaLoopMovLowA_preserves_reg (s : RealState) (r j : Nat) (h : r ≠ 59) :
    (stepLoop s vaLoopMovLowA).regs r j = s.regs r j := by
  unfold vaLoopMovLowA
  simp [stepLoop, (by decide : src79Even.num ≠ 61),
    (by decide : src79Even.num ≠ 74), writeMaskedWith, dst81Even, vaLoopAlias, h]

/-- PC 40 writes `V0059` only. -/
theorem vaLoopMovLowB_preserves_reg (s : RealState) (r j : Nat) (h : r ≠ 59) :
    (stepLoop s vaLoopMovLowB).regs r j = s.regs r j := by
  unfold vaLoopMovLowB
  simp [stepLoop, (by decide : src79EvenM5.num ≠ 61),
    (by decide : src79EvenM5.num ≠ 74), writeMaskedWith, dst81EvenM5, vaLoopAlias, h]

/-- PC 41 writes `V0059` only. -/
theorem vaLoopMovHighA_preserves_reg (s : RealState) (r j : Nat) (h : r ≠ 59) :
    (stepLoop s vaLoopMovHighA).regs r j = s.regs r j := by
  unfold vaLoopMovHighA
  simp [stepLoop, (by decide : src80Odd.num ≠ 61),
    (by decide : src80Odd.num ≠ 74), writeMaskedWith, dst81Odd, vaLoopAlias, h]

/-- PC 42 writes `V0059` only. -/
theorem vaLoopMovHighB_preserves_reg (s : RealState) (r j : Nat) (h : r ≠ 59) :
    (stepLoop s vaLoopMovHighB).regs r j = s.regs r j := by
  unfold vaLoopMovHighB
  simp [stepLoop, (by decide : src80OddM5.num ≠ 61),
    (by decide : src80OddM5.num ≠ 74), writeMaskedWith, dst81OddM5, vaLoopAlias, h]

theorem vaLoopLowPack_preserves_reg (s : RealState) (r j : Nat) (h : r ≠ 59) :
    (runRealWith stepLoop s vaLoopLowPack).regs r j = s.regs r j := by
  unfold vaLoopLowPack runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  rw [vaLoopMovLowB_preserves_reg _ r j h, vaLoopMovLowA_preserves_reg _ r j h]

theorem vaLoopHighPack_preserves_reg (s : RealState) (r j : Nat) (h : r ≠ 59) :
    (runRealWith stepLoop s vaLoopHighPack).regs r j = s.regs r j := by
  unfold vaLoopHighPack runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  rw [vaLoopMovHighB_preserves_reg _ r j h, vaLoopMovHighA_preserves_reg _ r j h]

theorem vaLoopWriteBack_preserves_reg (s : RealState) (r j : Nat) (h : r ≠ 59) :
    (runRealWith stepLoop s vaLoopWriteBackSlice).regs r j = s.regs r j := by
  rw [vaLoopWriteBackSlice, runRealWith_append,
    vaLoopHighPack_preserves_reg _ r j h, vaLoopLowPack_preserves_reg _ r j h]

theorem vaLoopSelects_preserves_reg (s : RealState) (r j : Nat)
    (h79 : r ≠ 79) (h80 : r ≠ 80) :
    (runRealWith stepLoop s [vaLoopSelLow, vaLoopSelHigh]).regs r j = s.regs r j := by
  unfold runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  rw [vaLoopSelHigh_preserves_reg _ r j h80, vaLoopSelLow_preserves_reg _ r j h79]

/-- The decoded PCs 37--42 change only registers 59, 79 and 80. -/
theorem vaLoopLoopBack_preserves_reg (s : RealState) (r j : Nat)
    (h59 : r ≠ 59) (h79 : r ≠ 79) (h80 : r ≠ 80) :
    (runRealWith stepLoop s vaLoopLoopBackSlice).regs r j = s.regs r j := by
  rw [vaLoopLoopBackSlice, runRealWith_append,
    vaLoopWriteBack_preserves_reg _ r j h59, vaLoopSelects_preserves_reg _ r j h79 h80]

/-- The A pointer is preserved by the loop-back. -/
theorem vaLoopLoopBack_preserves47 (s : RealState) (j : Nat) :
    (runRealWith stepLoop s vaLoopLoopBackSlice).regs 47 j = s.regs 47 j :=
  vaLoopLoopBack_preserves_reg s 47 j (by decide) (by decide) (by decide)

/-- The B pointer is preserved by the loop-back. -/
theorem vaLoopLoopBack_preserves48 (s : RealState) (j : Nat) :
    (runRealWith stepLoop s vaLoopLoopBackSlice).regs 48 j = s.regs 48 j :=
  vaLoopLoopBack_preserves_reg s 48 j (by decide) (by decide) (by decide)

/-- The C pointer is preserved by the loop-back. -/
theorem vaLoopLoopBack_preserves46 (s : RealState) (j : Nat) :
    (runRealWith stepLoop s vaLoopLoopBackSlice).regs 46 j = s.regs 46 j :=
  vaLoopLoopBack_preserves_reg s 46 j (by decide) (by decide) (by decide)

/-! ## Coalescing the decoded loop-back -/

/-- The post-loop-back state with `V0059` reinterpreted as qword lanes. -/
def vaLoopCoalesced (s : RealState) : RealState :=
  coalesceReg59 (runRealWith stepLoop s vaLoopLoopBackSlice)

/-- The coalesced lane is the `qwordOf` view of the raw writeback. -/
theorem vaLoopCoalesced_regs59 (s : RealState) (l : Nat) :
    (vaLoopCoalesced s).regs 59 l =
      qwordOf (dwordReg (runRealWith stepLoop s vaLoopLoopBackSlice) 59) l := by
  rfl

/-- Coalescing the loop-back does not touch memory. -/
theorem vaLoopCoalesced_mem (s : RealState) :
    (vaLoopCoalesced s).mem = s.mem := by
  rw [vaLoopCoalesced, coalesceReg59_mem, vaLoopLoopBack_mem]

/-- The qword lanes carried by `V0059` after the raw dword writeback. -/
def coalescedLoopBackId (s : RealState) : Nat → Addr :=
  fun l => qwordOf (dwordReg (runRealWith stepLoop s vaLoopLoopBackSlice) 59) l

/-- On lanes below 24 the coalesced lane is the selected grid-stride id. -/
theorem coalescedLoopBackId_eq_select (s : RealState) (stride : Addr) (l : Nat)
    (hl : l < 24) (h : VaLoopLoopBackPre s stride) :
    coalescedLoopBackId s l =
      selectId (fun k => s.regs 59 k) (fun k => s.regs 59 k + stride)
        (fun k => s.preds 6 k) l :=
  vaLoop_loopBack_id s stride l hl h

/-- On lanes 24--31 the 24-lane pack does not touch dword slots `2*l` and
`2*l+1`, so the coalesced lane is the pre-loop-back qword view. -/
theorem coalescedLoopBackId_ge24 (s : RealState) (l : Nat) (hl : 24 ≤ l) :
    coalescedLoopBackId s l = qwordOf (dwordReg s 59) l :=
  vaLoop_loopBack_qword_frame_ge24 s l hl

/-- After the PC 36--43 loop-back, coalescing register 59 gives the selected
grid-stride id on lanes below 24. -/
theorem coalesce_writeback (s : RealState) (stride : Addr) (l : Nat) (hl : l < 24)
    (h : VaLoopLoopBackPre s stride) :
    (vaLoopCoalesced s).regs 59 l =
      selectId (fun k => s.regs 59 k) (fun k => s.regs 59 k + stride)
        (fun k => s.preds 6 k) l := by
  rw [vaLoopCoalesced_regs59]
  exact vaLoop_loopBack_id s stride l hl h

/-- On a taken lane the coalesced index is exactly the next grid-stride
address `old + stride`. -/
theorem coalescedLoopBackId_eq_add (s : RealState) (old : Nat → Addr) (stride : Addr)
    (l : Nat) (hl : l < 24) (hidx : ∀ k, s.regs 59 k = old k)
    (htake : s.preds 6 l = true) (h : VaLoopLoopBackPre s stride) :
    coalescedLoopBackId s l = old l + stride := by
  rw [coalescedLoopBackId_eq_select s stride l hl h]
  rw [selectId_true _ _ _ l htake, hidx l]

/-- The coalesced state satisfies the body preconditions, with the coalesced
`V0059` lanes as the carried index. Below lane 24 that index is
`selectId old (old + stride) takeNew`; `coalesced_bodyPre_select` states the
piecewise form explicitly. -/
theorem coalesced_bodyPre (s : RealState) (aPtr bPtr cPtr : Addr) (idx : Nat → Addr)
    (h : VaLoopBodyPre s aPtr bPtr cPtr idx) :
    VaLoopBodyPre (vaLoopCoalesced s) aPtr bPtr cPtr (coalescedLoopBackId s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [vaLoopCoalesced, coalesceReg59_regs_other _ 47 0 (by decide),
      vaLoopLoopBack_preserves47]
    exact h.aReg
  · rw [vaLoopCoalesced, coalesceReg59_regs_other _ 48 0 (by decide),
      vaLoopLoopBack_preserves48]
    exact h.bReg
  · rw [vaLoopCoalesced, coalesceReg59_regs_other _ 46 0 (by decide),
      vaLoopLoopBack_preserves46]
    exact h.cReg
  · intro l
    rw [vaLoopCoalesced_regs59]
    rfl

/-- The body-precondition index in `selectId` form below lane 24. The pack
writes only dword slots 0..47, so lanes 24--31 keep the raw coalesced lane;
`coalesced_all_select_counterexample` shows that extending `selectId` to all
32 lanes is false. -/
theorem coalesced_bodyPre_select (s : RealState) (aPtr bPtr cPtr : Addr)
    (old : Nat → Addr) (stride : Addr)
    (h : VaLoopBodyPre s aPtr bPtr cPtr old)
    (hloop : VaLoopLoopBackPre s stride) :
    VaLoopBodyPre (vaLoopCoalesced s) aPtr bPtr cPtr
      (fun l => if l < 24 then
        selectId old (fun k => old k + stride) (fun k => s.preds 6 k) l
      else coalescedLoopBackId s l) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [vaLoopCoalesced, coalesceReg59_regs_other _ 47 0 (by decide),
      vaLoopLoopBack_preserves47]
    exact h.aReg
  · rw [vaLoopCoalesced, coalesceReg59_regs_other _ 48 0 (by decide),
      vaLoopLoopBack_preserves48]
    exact h.bReg
  · rw [vaLoopCoalesced, coalesceReg59_regs_other _ 46 0 (by decide),
      vaLoopLoopBack_preserves46]
    exact h.cReg
  · intro l
    by_cases hl : l < 24
    · rw [vaLoopCoalesced_regs59, vaLoop_loopBack_id s stride l hl hloop]
      simp [selectId, hl, h.idxReg]
    · simp [coalescedLoopBackId, hl, vaLoopCoalesced_regs59]

/-! ## Literal second iteration -/

theorem vaLoopProgram_20 : vaLoopProgram[20]? = some (.label "_0_009") := by decide

/-- The decoder's re-entry from the loop label at PC 20 to the body at PC 21,
on the coalesced state. -/
theorem vaLoop_coalesced_reentry (s : RealState) (lane fuel : Nat) :
    runRealCFLaneWith stepLoop vaLoopProgram (vaLoopCoalesced s) 20 (fuel + 1) lane =
      runRealCFLaneWith stepLoop vaLoopProgram (vaLoopCoalesced s) 21 fuel lane := by
  exact runRealCFLaneWith_label stepLoop vaLoopProgram (vaLoopCoalesced s) lane 20 fuel
    "_0_009" vaLoopProgram_20

/-- The literal second grid-stride iteration. If `P6` is true at PC 35, the
lane falls through to the decoded loop-back and reaches PC 21. The adapter
then coalesces the raw dword slots into qword lanes, re-enters the body at
PC 20/21, and the body stores `C[idx] = A[idx] + B[idx]` for
`idx = selectId old (old + stride) takeNew` on lanes below 24. The
memory-safety hypotheses are for the coalesced index. -/
theorem vaLoop_lane_second_body_literal (s : RealState) (lane fuel : Nat)
    (aPtr bPtr cPtr : Addr) (old : Nat → Addr) (stride : Addr)
    (h : VaLoopBodyPre s aPtr bPtr cPtr old)
    (hP6 : s.preds 6 lane = true) (hl : lane < 24)
    (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0)
    (hc : cPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (coalescedLoopBackId s lane).toNat < 2 ^ 64)
    (hbb : bPtr.toNat + 4 * (coalescedLoopBackId s lane).toNat < 2 ^ 64)
    (hcb : cPtr.toNat + 4 * (coalescedLoopBackId s lane).toNat < 2 ^ 64)
    (hboundC : ∀ k, k < 32 →
      cPtr.toNat + 4 * (coalescedLoopBackId s k).toNat < 2 ^ 64)
    (hdistinct : ∀ k, k < 32 → k ≠ lane →
      cPtr.toNat / 4 + (coalescedLoopBackId s k).toNat ≠
        cPtr.toNat / 4 + (coalescedLoopBackId s lane).toNat)
    (hloop : VaLoopLoopBackPre s stride) :
    (runRealCFLaneWith stepLoop vaLoopProgram s 35 (fuel + 10) lane =
      runRealCFLaneWith stepLoop vaLoopProgram
        (runRealWith stepLoop s vaLoopLoopBackSlice) 21 fuel lane) ∧
    (runRealCFLaneWith stepLoop vaLoopProgram (vaLoopCoalesced s) 20 (fuel + 1) lane =
      runRealCFLaneWith stepLoop vaLoopProgram (vaLoopCoalesced s) 21 fuel lane) ∧
    ((vaLoopCoalesced s).regs 59 lane =
      selectId old (fun k => old k + stride) (fun k => s.preds 6 k) lane) ∧
    ((runRealWith stepLoop (vaLoopCoalesced s) vaLoopBodySlice).mem
        (cPtr.toNat / 4 + (selectId old (fun k => old k + stride)
          (fun k => s.preds 6 k) lane).toNat) =
      s.mem (aPtr.toNat / 4 + (selectId old (fun k => old k + stride)
          (fun k => s.preds 6 k) lane).toNat) +
        s.mem (bPtr.toNat / 4 + (selectId old (fun k => old k + stride)
          (fun k => s.preds 6 k) lane).toNat)) := by
  have hpath : runRealCFLaneWith stepLoop vaLoopProgram s 35 (fuel + 10) lane =
      runRealCFLaneWith stepLoop vaLoopProgram
        (runRealWith stepLoop s vaLoopLoopBackSlice) 21 fuel lane := by
    rw [show fuel + 10 = (fuel + 9) + 1 from rfl]
    rw [vaLoopP6_fallthrough_stepLoop s lane (fuel + 9) hP6]
    rw [show fuel + 9 = (fuel + 1) + 8 from rfl]
    rw [vaLoopCFLoopBack s lane (fuel + 1)]
    rw [runRealCFLaneWith_label stepLoop vaLoopProgram _ lane 20 fuel "_0_009"
      (by decide)]
  have hreentry := vaLoop_coalesced_reentry s lane fuel
  have hidx : (vaLoopCoalesced s).regs 59 lane =
      selectId old (fun k => old k + stride) (fun k => s.preds 6 k) lane := by
    rw [coalesce_writeback s stride lane hl hloop]
    simp [selectId, h.idxReg]
  have hpre : VaLoopBodyPre (vaLoopCoalesced s) aPtr bPtr cPtr
      (coalescedLoopBackId s) :=
    coalesced_bodyPre s aPtr bPtr cPtr old h
  have hstore := vaLoopBodySlice_store_at (vaLoopCoalesced s) aPtr bPtr cPtr
    (coalescedLoopBackId s) hpre lane (by omega) ha hb hc hab hbb hcb hboundC hdistinct
  have hidx' : coalescedLoopBackId s lane =
      selectId old (fun k => old k + stride) (fun k => s.preds 6 k) lane := by
    rw [coalescedLoopBackId_eq_select s stride lane hl hloop]
    simp [selectId, h.idxReg]
  refine ⟨hpath, hreentry, hidx, ?_⟩
  rwa [vaLoopCoalesced_mem, hidx'] at hstore

/-! ## The raw dword slots are not qword lanes -/

/-- A state that exposes the dword-slot boundary: `V0059` lane 0 is
`2 ^ 32`, and `V0063` lane 0 holds its high dword. -/
def coalesceCounterState : RealState where
  regs := fun r e =>
    if r = 59 ∧ e = 0 then 4294967296
    else if r = 63 ∧ e = 0 then 1
    else if r = 76 ∧ e = 0 then 1
    else 0
  preds := fun _ _ => false
  mem := fun _ => 0
  halted := false

/-- The counterexample state meets the loop-back preconditions with stride 0. -/
theorem coalesceCounter_state_pre : VaLoopLoopBackPre coalesceCounterState 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro l <;> by_cases h : l = 0 <;>
    simp [coalesceCounterState, h]

/-- The raw writeback does not reconstruct qword lanes: at lane 0 the raw
dword slot is 0 while the coalesced lane is `2 ^ 32`. Coalescing is therefore
the explicit adapter, not a property of the raw `RealState` state. -/
theorem coalesce_raw_counterexample :
    ∃ s : RealState, ∃ l : Nat, l < 24 ∧
      (runRealWith stepLoop s vaLoopLoopBackSlice).regs 59 l ≠
        (vaLoopCoalesced s).regs 59 l := by
  refine ⟨coalesceCounterState, 0, by omega, ?_⟩
  rw [vaLoopLoopBack_low coalesceCounterState 0 (by omega)]
  rw [vaLoopCoalesced_regs59]
  unfold qwordOf dwordReg
  rw [vaLoopLoopBack_low coalesceCounterState 0 (by omega),
    vaLoopLoopBack_high coalesceCounterState 0 (by omega)]
  simp [coalesceCounterState]

/-- A state showing why the `selectId` index cannot be extended to lane 24:
the 24-lane pack leaves dword slots 48 and 49 (qword lane 24) alone, while
`P6` is true at lane 24. -/
def coalesceAllLaneState : RealState where
  regs := fun r _ => if r = 75 then 1 else 0
  preds := fun p e => decide (p = 6 ∧ e = 24)
  mem := fun _ => 0
  halted := false

theorem coalesceAllLaneState_bodyPre :
    VaLoopBodyPre coalesceAllLaneState 0 0 0 (fun _ => 0) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro l
  simp [coalesceAllLaneState]

theorem coalesceAllLaneState_loopBackPre :
    VaLoopLoopBackPre coalesceAllLaneState 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro l <;>
    simp [coalesceAllLaneState]

/-- The natural all-lane `selectId` pre-state is false: on lane 24 the
coalesced lane stays `0`, while `selectId` would return `old 24 + 1 = 1`. -/
theorem coalesced_all_select_counterexample :
    ∃ s : RealState, ∃ aPtr bPtr cPtr old stride,
      VaLoopBodyPre s aPtr bPtr cPtr old ∧ VaLoopLoopBackPre s stride ∧
      (vaLoopCoalesced s).regs 59 24 ≠
        selectId old (fun k => old k + stride) (fun k => s.preds 6 k) 24 := by
  refine ⟨coalesceAllLaneState, 0, 0, 0, (fun _ => 0), 1,
    coalesceAllLaneState_bodyPre, coalesceAllLaneState_loopBackPre, ?_⟩
  rw [vaLoopCoalesced_regs59]
  unfold qwordOf dwordReg
  simp only [show 2 * 24 = 48 from rfl, show 2 * 24 + 1 = 49 from rfl]
  rw [vaLoopLoopBack_frame_ge48 _ 48 (by omega),
    vaLoopLoopBack_frame_ge48 _ 49 (by omega)]
  simp [coalesceAllLaneState, selectId]

end

end IntelGpu

