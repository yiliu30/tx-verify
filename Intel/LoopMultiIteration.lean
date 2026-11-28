-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.DwordCoalesce
public import Intel.LoopGuardPath

@[expose] public section

/-!
# The coalesced grid-stride loop: n iterations

Stage 158 executes the decoded loop-back and stage 160 coalesces its dword
writeback into qword lanes. `vaLoop_lane_second_body_literal` composes the
*literal second* iteration: from a body pre-state it runs the body at PCs
21--24, the increment at PC 25, the P6 packs at PCs 26--34, falls through
PC 35, executes the loop-back at PCs 36--43 and re-enters at PC 20/21 on the
coalesced state. This module lifts that single step to a grid-stride
induction over `n` iterations and composes the stores
`C[id_k] = A[id_k] + B[id_k]`.

## The iteration

`vaLoopIterPrefix` is the decoded tail of one iteration
(`vaLoopBodySlice ++ vaLoopIncAdd ++ vaLoopP6Prefix`). `vaLoopIterNext s` is
the coalesced state after executing that tail and the PC 36--43 loop-back,
and `vaLoopIterState s k` is the body pre-state at PC 20/21 after `k`
iterations. The decoded path from PC 21 back to PC 21 consumes exactly 24
fuel: PCs 21--24 body (4), PC 25 increment (1), PCs 26--34 P6 packs (9),
PC 35 P6 branch (1), PCs 36--43 loop-back (8) and the PC 20 label (1).

`vaLoop_coalesced_iteration_step` states that path with the P6-true
hypothesis and proves that the next body pre-state carries the body
preconditions and that the lane's index advances by `stride`.
`vaLoop_coalesced_iteration_step_store` records this iteration's store in the
next state's memory.

## The induction

`vaLoop_coalesced_iteration` starts from a coalesced body pre-state whose
lane holds `id`. The only guard hypothesis is the real decoded guard of the
P6 block, stated for the lane:

```
vaLoopGuard (strideId id stride k + stride) size = true     (k < n)
```

`vaLoopIterPrefix_p6_guard` derives the state-level `preds 6 lane = true`
from it through the executed P6 prefix (stage 129/133/138), and
`coalescedLoopBackId_eq_add_of_halves` uses the exact taken-lane writeback
halves produced by the increment packs. `vaLoop_coalesced_iteration_p6`
states the same result with those state-level P6 predicates as hypotheses,
avoiding the guard bridge. After `n` iterations the state again
satisfies the body preconditions (in the self-index form, with the coalesced
lanes as the index), the observed lane's index is `strideId id stride n`, and
every earlier store survives: `C[strideId id stride k] = A[...] + B[...]`
for `k < n`.

The memory composition is stated with explicit disjointness
(`VaLoopIterMemorySafe`): the 32 body stores of an iteration are pairwise
distinct, later iterations do not overwrite earlier results, and C stores do
not alias the A/B reads. This is the same shape as
`Intel.GridStride.gridStore_correct`, but the decoded C base is not zero, so
the word indices are `cPtr.toNat / 4 + id` rather than `id`.

## Lane bound and the coalescing adapter

The writeback pack writes only dword slots 0..47, i.e. qword lanes `0..23`.
All statements here use `lane < 24`; lanes 24--31 keep the raw pre-loop dword
slots (`coalescedLoopBackId_ge24`), and `coalesced_all_select_counterexample`
in `Intel.DwordCoalesce` proves that extending the `selectId` form to lane 24
is false. Coalescing remains the explicit adapter `vaLoopCoalesced` of stage
160: it is applied once per iteration to `V0059` only and leaves every other
register, the predicates, memory and the halt flag unchanged.

The full `VaLoopLoopBackPre` of stage 158 requires `V0062/V0063` to hold the
current id halves. The decoded loop-back block does not rewrite those
registers, so the induction uses the weaker, exact taken-lane facts
`V0075/V0076 = old + stride` produced by the P6 packs. The corollary
`vaLoop_coalesced_iteration_two_literal` recovers stage 160's literal
`selectId old (old + stride) takeNew` index on the second body's pre-state.

## Negative path

`vaLoop_coalesced_iteration_branch` gives both decoded PC 35 branches from
the real guard value, and `vaLoop_coalesced_iteration_exit` shows that a
false P6 reaches PC 44 instead of the loop-back. This is the same exit path
as stage 136's `vaLoop_lane_body_exit`.

The theorems that unfold the decoded store inherit `Classical.choice` from
`storeVec`'s aliasing-lane choice, exactly as stages 158 and 160. The
guard-shaped theorems also inherit the existing `bv_decide` axioms of
`vaGuard32_eq` and `vaLoopSize_id` through stage 129/133's `vaLoopP6_exec`;
they are not introduced here. The state-level variant
`vaLoop_coalesced_iteration_p6` avoids that bridge and depends only on
`propext`, `Classical.choice` and `Quot.sound`. No new axioms, no
`native_decide` and no `sorry` are added by this module.
-/

namespace IntelGpu

noncomputable section

/-! ## The per-iteration decoded slices -/

/-- The decoded tail of one grid-stride iteration: the body, the increment
and the second guard's packs. -/
def vaLoopIterPrefix : List RInstr :=
  vaLoopBodySlice ++ vaLoopIncAdd ++ vaLoopP6Prefix

/-- The body and increment, i.e. everything before the P6 packs. -/
def vaLoopIterBodyInc : List RInstr := vaLoopBodySlice ++ vaLoopIncAdd

/-- The iteration prefix is the body/increment prefix followed by the P6
packs. -/
theorem vaLoopIterPrefix_eq_append :
    vaLoopIterPrefix = vaLoopIterBodyInc ++ vaLoopP6Prefix := by
  simp [vaLoopIterPrefix, vaLoopIterBodyInc, List.append_assoc]

/-- The coalesced body pre-state after one iteration and its loop-back. -/
def vaLoopIterNext (s : RealState) : RealState :=
  vaLoopCoalesced (runRealWith stepLoop s vaLoopIterPrefix)

/-- The body pre-state at PC 20/21 after `k` iterations. -/
def vaLoopIterState (s : RealState) : Nat → RealState
  | 0 => s
  | k + 1 => vaLoopIterNext (vaLoopIterState s k)

theorem vaLoopIterState_zero (s : RealState) : vaLoopIterState s 0 = s := rfl

theorem vaLoopIterState_succ (s : RealState) (k : Nat) :
    vaLoopIterState s (k + 1) = vaLoopIterNext (vaLoopIterState s k) := rfl

/-! ## Register frames -/

/-- The increment add writes `V0072` only. -/
theorem vaLoopIncAdd_preserves_reg (s : RealState) (r j : Nat) (h72 : r ≠ 72) :
    (runRealWith stepLoop s vaLoopIncAdd).regs r j = s.regs r j := by
  unfold vaLoopIncAdd runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  simp [stepLoop, stepVAL, stepWith, writeVecWith, setReg, vaLoopAlias, h72]

/-- The second guard block touches only the predicate file. -/
theorem vaGuardBlock2_preserves_reg (s : RealState) (r j : Nat) :
    (runRealWith stepLoop s vaGuardBlock2).regs r j = s.regs r j := by
  unfold vaGuardBlock2 runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  simp [stepLoop, stepVAL, stepWith]

/-- The P6 packs write only `V0075` and `V0076`. -/
theorem vaLoopP6Prefix_preserves_reg (s : RealState) (r j : Nat)
    (h75 : r ≠ 75) (h76 : r ≠ 76) :
    (runRealWith stepLoop s vaLoopP6Prefix).regs r j = s.regs r j := by
  rw [vaLoopP6Prefix, runRealWith_append, runRealWith_append]
  unfold vaGuardBlock2 vaPackIncHigh vaPackIncLow
  simp only [runRealWith, List.foldl_cons, List.foldl_nil]
  simp [stepLoop, stepVAL, stepWith, writeMaskedWith, vaLoopAlias, h75, h76,
    dst75a, dst75b, dst76a, dst76b, src74a, src74b, src74aHigh, src74bHigh,
    e1Loop, e2Loop, Exec.laneActive]

/-- The whole iteration prefix preserves every register outside the body's
`V0069/V0070/V0071`, the increment's `V0072` and the packs' `V0075/V0076`. -/
theorem vaLoopIterPrefix_preserves_reg (s : RealState) (r j : Nat)
    (h69 : r ≠ 69) (h70 : r ≠ 70) (h71 : r ≠ 71) (h72 : r ≠ 72)
    (h75 : r ≠ 75) (h76 : r ≠ 76) :
    (runRealWith stepLoop s vaLoopIterPrefix).regs r j = s.regs r j := by
  unfold vaLoopIterPrefix
  rw [runRealWith_append, runRealWith_append]
  rw [vaLoopP6Prefix_preserves_reg _ r j h75 h76,
    vaLoopIncAdd_preserves_reg _ r j h72,
    vaLoopBodySlice_preserves_reg _ r j h69 h70 h71]

/-- Executing the body, increment and P6 packs preserves the body
preconditions, including the carried index. -/
theorem vaLoopIterPrefix_bodyPre (s : RealState) (aPtr bPtr cPtr : Addr)
    (idx : Nat → Addr) (h : VaLoopBodyPre s aPtr bPtr cPtr idx) :
    VaLoopBodyPre (runRealWith stepLoop s vaLoopIterPrefix) aPtr bPtr cPtr idx := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [vaLoopIterPrefix_preserves_reg _ 47 0 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact h.aReg
  · rw [vaLoopIterPrefix_preserves_reg _ 48 0 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact h.bReg
  · rw [vaLoopIterPrefix_preserves_reg _ 46 0 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact h.cReg
  · intro l
    rw [vaLoopIterPrefix_preserves_reg _ 59 l (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact h.idxReg l

/-- The body/increment prefix preserves registers outside the body and
increment destinations. -/
theorem vaLoopIterBodyInc_preserves_reg (s : RealState) (r j : Nat)
    (h69 : r ≠ 69) (h70 : r ≠ 70) (h71 : r ≠ 71) (h72 : r ≠ 72) :
    (runRealWith stepLoop s vaLoopIterBodyInc).regs r j = s.regs r j := by
  unfold vaLoopIterBodyInc
  rw [runRealWith_append, vaLoopIncAdd_preserves_reg _ r j h72,
    vaLoopBodySlice_preserves_reg _ r j h69 h70 h71]

/-- The increment produces `V0072 = V0059 + stride` after the body. -/
theorem vaLoopIterBodyInc_inc (s : RealState) (stride : Addr)
    (hstride : s.regs 67 0 = stride) (l : Nat) :
    (runRealWith stepLoop s vaLoopIterBodyInc).regs 72 l = s.regs 59 l + stride := by
  unfold vaLoopIterBodyInc
  rw [runRealWith_append]
  apply vaLoopIncAdd_value
  refine ⟨?_, ?_⟩
  · intro k
    rw [vaLoopBodySlice_preserves_reg _ 59 k (by decide) (by decide) (by decide)]
  · rw [vaLoopBodySlice_preserves_reg _ 67 0 (by decide) (by decide) (by decide)]
    exact hstride

/-- The iteration prefix leaves the post-body memory unchanged. -/
theorem vaLoopIterPrefix_mem (s : RealState) :
    (runRealWith stepLoop s vaLoopIterPrefix).mem =
      (runRealWith stepLoop s vaLoopBodySlice).mem := by
  unfold vaLoopIterPrefix
  rw [runRealWith_append, runRealWith_append, vaLoopP6Prefix_mem, vaLoopIncAdd_mem]

/-! ## The real P6 guard and the taken-lane writeback -/

/-- The state-level P6 of the iteration prefix is the real decoded guard
applied to `V0059 + stride`. This is stage 129/133/138's executed P6 prefix,
with the increment and size dwords supplied. -/
theorem vaLoopIterPrefix_p6_guard (s : RealState) (lane : Nat) (stride : Addr)
    (sizeLo sizeHi : Word) (hl : lane < 24)
    (hstride : s.regs 67 0 = stride)
    (hslo : low32 (s.regs 49 0) = sizeLo)
    (hshi : low32 (s.regs 49 1) = sizeHi) :
    (runRealWith stepLoop s vaLoopIterPrefix).preds 6 lane =
      vaLoopGuard (s.regs 59 lane + stride) (vaLoopSize sizeLo sizeHi) := by
  rw [vaLoopIterPrefix_eq_append, runRealWith_append]
  apply vaLoopP6_exec
  · exact hl
  · intro l
    exact vaLoopIterBodyInc_inc s stride hstride l
  · rw [vaLoopIterBodyInc_preserves_reg _ 49 0 (by decide) (by decide) (by decide)
      (by decide)]
    exact hslo
  · rw [vaLoopIterBodyInc_preserves_reg _ 49 1 (by decide) (by decide) (by decide)
      (by decide)]
    exact hshi

/-- The P6 packs write the low dword of `V0059 + stride` into `V0075`. -/
theorem vaLoopP6Prefix_75 (s : RealState) (ids : Nat → Addr) (l : Nat)
    (hl : l < 24) (hid : ∀ k, s.regs 72 k = ids k) :
    low32 ((runRealWith stepLoop s vaLoopP6Prefix).regs 75 l) = (ids l).truncate 32 := by
  rw [vaLoopP6Prefix, runRealWith_append, runRealWith_append]
  rw [vaGuardBlock2_preserves_reg]
  exact (vaPackIncBoth_value s ids l hl hid).1

/-- The P6 packs write the high dword of `V0059 + stride` into `V0076`. -/
theorem vaLoopP6Prefix_76 (s : RealState) (ids : Nat → Addr) (l : Nat)
    (hl : l < 24) (hid : ∀ k, s.regs 72 k = ids k) :
    low32 ((runRealWith stepLoop s vaLoopP6Prefix).regs 76 l) =
      ((ids l) >>> 32).truncate 32 := by
  rw [vaLoopP6Prefix, runRealWith_append, runRealWith_append]
  rw [vaGuardBlock2_preserves_reg]
  exact (vaPackIncBoth_value s ids l hl hid).2

/-- The iteration prefix writes the low dword of `V0059 + stride` into
`V0075` on lanes below 24. -/
theorem vaLoopIterPrefix_75 (s : RealState) (stride : Addr) (lane : Nat)
    (hl : lane < 24) (hstride : s.regs 67 0 = stride) :
    low32 ((runRealWith stepLoop s vaLoopIterPrefix).regs 75 lane) =
      (s.regs 59 lane + stride).truncate 32 := by
  rw [vaLoopIterPrefix_eq_append, runRealWith_append]
  exact vaLoopP6Prefix_75 _ (fun l => s.regs 59 l + stride) lane hl
    (fun l => vaLoopIterBodyInc_inc s stride hstride l)

/-- The iteration prefix writes the high dword of `V0059 + stride` into
`V0076` on lanes below 24. -/
theorem vaLoopIterPrefix_76 (s : RealState) (stride : Addr) (lane : Nat)
    (hl : lane < 24) (hstride : s.regs 67 0 = stride) :
    low32 ((runRealWith stepLoop s vaLoopIterPrefix).regs 76 lane) =
      ((s.regs 59 lane + stride) >>> 32).truncate 32 := by
  rw [vaLoopIterPrefix_eq_append, runRealWith_append]
  exact vaLoopP6Prefix_76 _ (fun l => s.regs 59 l + stride) lane hl
    (fun l => vaLoopIterBodyInc_inc s stride hstride l)

/-- On a taken lane, the loop-back writeback is the incremented id as soon as
`V0075/V0076` hold its two halves. This is the exact taken-lane part of
stage 158's `VaLoopLoopBackPre`; the stale old-id halves `V0062/V0063` are
not needed because `P6` selects the new-id branch. -/
theorem coalescedLoopBackId_eq_add_of_halves (s : RealState) (stride : Addr) (l : Nat)
    (hl : l < 24)
    (hnewLow : (s.regs 75 l).truncate 32 = ((s.regs 59 l + stride).truncate 32))
    (hnewHigh : (s.regs 76 l).truncate 32 =
      (((s.regs 59 l + stride) >>> 32).truncate 32))
    (htake : s.preds 6 l = true) :
    coalescedLoopBackId s l = s.regs 59 l + stride := by
  unfold coalescedLoopBackId qwordOf dwordReg
  rw [vaLoopLoopBack_low s l hl, vaLoopLoopBack_high s l hl]
  simp [htake, hnewLow, hnewHigh, qword_merge]

/-! ## One iteration: the decoded path and the next pre-state -/

/-- One decoded iteration from PC 21 back to PC 21, with exact fuel. The P6
branch falls through and the loop-back lands on the `_0_009` label. -/
theorem vaLoop_coalesced_iteration_path (s : RealState) (lane fuel : Nat)
    (hP6 : (runRealWith stepLoop s vaLoopIterPrefix).preds 6 lane = true) :
    runRealCFLaneWith stepLoop vaLoopProgram s 21 (fuel + 24) lane =
      runRealCFLaneWith stepLoop vaLoopProgram
        (runRealWith stepLoop (runRealWith stepLoop s vaLoopIterPrefix)
          vaLoopLoopBackSlice) 21 fuel lane := by
  have ht : runRealWith stepLoop s vaLoopIterPrefix =
      runRealWith stepLoop
        (runRealWith stepLoop
          (runRealWith stepLoop s vaLoopBodySlice) vaLoopIncAdd) vaLoopP6Prefix := by
    simp only [vaLoopIterPrefix, runRealWith_append]
  rw [show fuel + 24 = (fuel + 20) + 3 + 1 from rfl]
  rw [vaLoopCFBody s lane (fuel + 20)]
  rw [show fuel + 20 = (fuel + 19) + 1 from rfl]
  rw [vaLoopCFInc (runRealWith stepLoop s vaLoopBodySlice) lane (fuel + 19)]
  rw [show fuel + 19 = (fuel + 10) + 8 + 1 from rfl]
  rw [vaLoopCFP6 (runRealWith stepLoop
    (runRealWith stepLoop s vaLoopBodySlice) vaLoopIncAdd) lane (fuel + 10)]
  rw [← ht]
  rw [show fuel + 10 = (fuel + 9) + 1 from rfl]
  rw [vaLoopP6_fallthrough_stepLoop _ lane (fuel + 9) hP6]
  rw [show fuel + 9 = (fuel + 1) + 8 from rfl]
  rw [vaLoopCFLoopBack _ lane (fuel + 1)]
  rw [runRealCFLaneWith_label stepLoop vaLoopProgram _ lane 20 fuel "_0_009"
    (by decide)]

/-- The step lemma for the coalesced grid-stride iteration. From a body
pre-state with index `idx`, a true P6 and the taken-lane writeback halves,
the decoded path reaches the loop-back at PC 21, the coalesced state
re-enters at PC 20/21, carries the body preconditions, and the lane's index
advances by `stride`. -/
theorem vaLoop_coalesced_iteration_step (s : RealState) (lane fuel : Nat)
    (aPtr bPtr cPtr : Addr) (idx : Nat → Addr) (stride : Addr)
    (h : VaLoopBodyPre s aPtr bPtr cPtr idx)
    (hP6 : (runRealWith stepLoop s vaLoopIterPrefix).preds 6 lane = true)
    (hnewLow : ((runRealWith stepLoop s vaLoopIterPrefix).regs 75 lane).truncate 32 =
      (((runRealWith stepLoop s vaLoopIterPrefix).regs 59 lane + stride).truncate 32))
    (hnewHigh : ((runRealWith stepLoop s vaLoopIterPrefix).regs 76 lane).truncate 32 =
      ((((runRealWith stepLoop s vaLoopIterPrefix).regs 59 lane + stride) >>> 32).truncate 32))
    (hl : lane < 24) :
    (runRealCFLaneWith stepLoop vaLoopProgram s 21 (fuel + 24) lane =
      runRealCFLaneWith stepLoop vaLoopProgram
        (runRealWith stepLoop (runRealWith stepLoop s vaLoopIterPrefix)
          vaLoopLoopBackSlice) 21 fuel lane) ∧
    (runRealCFLaneWith stepLoop vaLoopProgram (vaLoopIterNext s) 20 (fuel + 1) lane =
      runRealCFLaneWith stepLoop vaLoopProgram (vaLoopIterNext s) 21 fuel lane) ∧
    VaLoopBodyPre (vaLoopIterNext s) aPtr bPtr cPtr
      (fun l => (vaLoopIterNext s).regs 59 l) ∧
    ((vaLoopIterNext s).regs 59 lane = idx lane + stride) := by
  have hpath := vaLoop_coalesced_iteration_path s lane fuel hP6
  have hreentry : runRealCFLaneWith stepLoop vaLoopProgram (vaLoopIterNext s) 20
      (fuel + 1) lane =
      runRealCFLaneWith stepLoop vaLoopProgram (vaLoopIterNext s) 21 fuel lane :=
    vaLoop_coalesced_reentry (runRealWith stepLoop s vaLoopIterPrefix) lane fuel
  have hpreT := vaLoopIterPrefix_bodyPre s aPtr bPtr cPtr idx h
  have hpreNext := coalesced_bodyPre (runRealWith stepLoop s vaLoopIterPrefix)
    aPtr bPtr cPtr idx hpreT
  have hpreNext' : VaLoopBodyPre (vaLoopIterNext s) aPtr bPtr cPtr
      (fun l => (vaLoopIterNext s).regs 59 l) :=
    ⟨hpreNext.aReg, hpreNext.bReg, hpreNext.cReg, fun l => rfl⟩
  have h59 : ∀ k, (runRealWith stepLoop s vaLoopIterPrefix).regs 59 k = idx k := by
    intro k
    rw [vaLoopIterPrefix_preserves_reg _ 59 k (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact h.idxReg k
  have hidx : (vaLoopIterNext s).regs 59 lane = idx lane + stride := by
    have hval := coalescedLoopBackId_eq_add_of_halves
      (runRealWith stepLoop s vaLoopIterPrefix) stride lane hl hnewLow hnewHigh hP6
    rw [vaLoopIterNext]
    rw [show (vaLoopCoalesced (runRealWith stepLoop s vaLoopIterPrefix)).regs 59 lane =
      coalescedLoopBackId (runRealWith stepLoop s vaLoopIterPrefix) lane from rfl]
    rw [hval, h59 lane]
  exact ⟨hpath, hreentry, hpreNext', hidx⟩

/-- The iteration's store survives in the next state's memory. This is the
body store of `vaLoopBodySlice_store_at` transported through the increment,
the P6 packs, the loop-back and the coalescing adapter. -/
theorem vaLoop_coalesced_iteration_step_store (s : RealState) (lane : Nat)
    (aPtr bPtr cPtr : Addr) (idx : Nat → Addr)
    (h : VaLoopBodyPre s aPtr bPtr cPtr idx) (hl : lane < 32)
    (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0) (hc : cPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (idx lane).toNat < 2 ^ 64)
    (hbb : bPtr.toNat + 4 * (idx lane).toNat < 2 ^ 64)
    (hcb : cPtr.toNat + 4 * (idx lane).toNat < 2 ^ 64)
    (hboundC : ∀ k, k < 32 → cPtr.toNat + 4 * (idx k).toNat < 2 ^ 64)
    (hdistinct : ∀ k, k < 32 → k ≠ lane →
      cPtr.toNat / 4 + (idx k).toNat ≠
        cPtr.toNat / 4 + (idx lane).toNat) :
    (vaLoopIterNext s).mem (cPtr.toNat / 4 + (idx lane).toNat) =
      s.mem (aPtr.toNat / 4 + (idx lane).toNat) +
        s.mem (bPtr.toNat / 4 + (idx lane).toNat) := by
  unfold vaLoopIterNext
  rw [vaLoopCoalesced_mem, vaLoopIterPrefix_mem]
  exact vaLoopBodySlice_store_at s aPtr bPtr cPtr idx h lane hl ha hb hc hab hbb hcb
    hboundC hdistinct

/-- The step lemma together with this iteration's store. -/
theorem vaLoop_coalesced_iteration_step_with_store (s : RealState) (lane fuel : Nat)
    (aPtr bPtr cPtr : Addr) (idx : Nat → Addr) (stride : Addr)
    (h : VaLoopBodyPre s aPtr bPtr cPtr idx)
    (hP6 : (runRealWith stepLoop s vaLoopIterPrefix).preds 6 lane = true)
    (hnewLow : ((runRealWith stepLoop s vaLoopIterPrefix).regs 75 lane).truncate 32 =
      (((runRealWith stepLoop s vaLoopIterPrefix).regs 59 lane + stride).truncate 32))
    (hnewHigh : ((runRealWith stepLoop s vaLoopIterPrefix).regs 76 lane).truncate 32 =
      ((((runRealWith stepLoop s vaLoopIterPrefix).regs 59 lane + stride) >>> 32).truncate 32))
    (hl : lane < 24)
    (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0) (hc : cPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (idx lane).toNat < 2 ^ 64)
    (hbb : bPtr.toNat + 4 * (idx lane).toNat < 2 ^ 64)
    (hcb : cPtr.toNat + 4 * (idx lane).toNat < 2 ^ 64)
    (hboundC : ∀ k, k < 32 → cPtr.toNat + 4 * (idx k).toNat < 2 ^ 64)
    (hdistinct : ∀ k, k < 32 → k ≠ lane →
      cPtr.toNat / 4 + (idx k).toNat ≠
        cPtr.toNat / 4 + (idx lane).toNat) :
    (runRealCFLaneWith stepLoop vaLoopProgram s 21 (fuel + 24) lane =
      runRealCFLaneWith stepLoop vaLoopProgram
        (runRealWith stepLoop (runRealWith stepLoop s vaLoopIterPrefix)
          vaLoopLoopBackSlice) 21 fuel lane) ∧
    (vaLoopIterNext s).mem (cPtr.toNat / 4 + (idx lane).toNat) =
      s.mem (aPtr.toNat / 4 + (idx lane).toNat) +
        s.mem (bPtr.toNat / 4 + (idx lane).toNat) :=
  ⟨(vaLoop_coalesced_iteration_step s lane fuel aPtr bPtr cPtr idx stride h hP6
      hnewLow hnewHigh hl).1,
    vaLoop_coalesced_iteration_step_store s lane aPtr bPtr cPtr idx h (by omega)
      ha hb hc hab hbb hcb hboundC hdistinct⟩

/-! ## Frames through whole iterations -/

/-- The coalesced iteration changes only `V0059`, `V0079` and `V0080`, plus
the body/increment/pack destinations, so it preserves every other register. -/
theorem vaLoopIterNext_preserves_reg (s : RealState) (r j : Nat)
    (h59 : r ≠ 59) (h79 : r ≠ 79) (h80 : r ≠ 80)
    (h69 : r ≠ 69) (h70 : r ≠ 70) (h71 : r ≠ 71) (h72 : r ≠ 72)
    (h75 : r ≠ 75) (h76 : r ≠ 76) :
    (vaLoopIterNext s).regs r j = s.regs r j := by
  unfold vaLoopIterNext vaLoopCoalesced
  rw [coalesceReg59_regs_other _ r j h59,
    vaLoopLoopBack_preserves_reg _ r j h59 h79 h80,
    vaLoopIterPrefix_preserves_reg _ r j h69 h70 h71 h72 h75 h76]

/-- Whole iterations preserve every register outside the iteration's
destination set. In particular they preserve `V0049` and `V0067`. -/
theorem vaLoopIterState_preserves_reg (s : RealState) (r j : Nat)
    (h59 : r ≠ 59) (h79 : r ≠ 79) (h80 : r ≠ 80)
    (h69 : r ≠ 69) (h70 : r ≠ 70) (h71 : r ≠ 71) (h72 : r ≠ 72)
    (h75 : r ≠ 75) (h76 : r ≠ 76) (k : Nat) :
    (vaLoopIterState s k).regs r j = s.regs r j := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [vaLoopIterState,
        vaLoopIterNext_preserves_reg _ r j h59 h79 h80 h69 h70 h71 h72 h75 h76, ih]

/-! ## The state induction -/

/-- The grid-stride state induction. Starting from the coalesced body
pre-state whose lane holds `id`, if the real P6 guard
`vaLoopGuard (strideId id stride k + stride) size` is true for every
`k < n`, then after `n` iterations the state is the coalesced body pre-state
with lane index `strideId id stride n`. -/
theorem vaLoop_coalesced_iteration_state (s : RealState) (lane : Nat)
    (aPtr bPtr cPtr : Addr) (stride : Addr) (sizeLo sizeHi : Word)
    (id : Addr) (n : Nat)
    (hpre : VaLoopBodyPre s aPtr bPtr cPtr (fun l => s.regs 59 l))
    (hid : s.regs 59 lane = id) (hl : lane < 24)
    (hstride : s.regs 67 0 = stride)
    (hslo : low32 (s.regs 49 0) = sizeLo)
    (hshi : low32 (s.regs 49 1) = sizeHi)
    (hguard : ∀ k, k < n →
      vaLoopGuard (strideId id stride k + stride) (vaLoopSize sizeLo sizeHi) = true) :
    VaLoopBodyPre (vaLoopIterState s n) aPtr bPtr cPtr
      (fun l => (vaLoopIterState s n).regs 59 l) ∧
    (vaLoopIterState s n).regs 59 lane = strideId id stride n := by
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · simpa [vaLoopIterState] using hpre
      · simp [vaLoopIterState, hid, strideId_zero]
  | succ n ih =>
      have hguardRestr : ∀ k, k < n →
          vaLoopGuard (strideId id stride k + stride) (vaLoopSize sizeLo sizeHi) = true :=
        fun k hk => hguard k (by omega)
      obtain ⟨hpreN, hidxN⟩ := ih hguardRestr
      have h67 : (vaLoopIterState s n).regs 67 0 = stride := by
        rw [vaLoopIterState_preserves_reg _ 67 0 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hstride
      have h49lo : low32 ((vaLoopIterState s n).regs 49 0) = sizeLo := by
        rw [vaLoopIterState_preserves_reg _ 49 0 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hslo
      have h49hi : low32 ((vaLoopIterState s n).regs 49 1) = sizeHi := by
        rw [vaLoopIterState_preserves_reg _ 49 1 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hshi
      have hP6 : (runRealWith stepLoop (vaLoopIterState s n)
          vaLoopIterPrefix).preds 6 lane = true := by
        rw [vaLoopIterPrefix_p6_guard (vaLoopIterState s n) lane stride sizeLo sizeHi
          hl h67 h49lo h49hi, hidxN]
        exact hguard n (Nat.lt_succ_self n)
      have h59t : (runRealWith stepLoop (vaLoopIterState s n)
          vaLoopIterPrefix).regs 59 lane = strideId id stride n := by
        rw [vaLoopIterPrefix_preserves_reg _ 59 lane (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)]
        exact hidxN
      have h59frame : (runRealWith stepLoop (vaLoopIterState s n)
          vaLoopIterPrefix).regs 59 lane = (vaLoopIterState s n).regs 59 lane := by
        rw [vaLoopIterPrefix_preserves_reg _ 59 lane (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)]
      have h75 := vaLoopIterPrefix_75 (vaLoopIterState s n) stride lane hl h67
      have h76 := vaLoopIterPrefix_76 (vaLoopIterState s n) stride lane hl h67
      have hnewLow : ((runRealWith stepLoop (vaLoopIterState s n)
          vaLoopIterPrefix).regs 75 lane).truncate 32 =
          (((runRealWith stepLoop (vaLoopIterState s n) vaLoopIterPrefix).regs 59 lane
            + stride).truncate 32) := by
        rw [show ((runRealWith stepLoop (vaLoopIterState s n)
          vaLoopIterPrefix).regs 75 lane).truncate 32 =
            (((vaLoopIterState s n).regs 59 lane + stride).truncate 32) from h75,
          ← h59frame]
      have hnewHigh : ((runRealWith stepLoop (vaLoopIterState s n)
          vaLoopIterPrefix).regs 76 lane).truncate 32 =
          ((((runRealWith stepLoop (vaLoopIterState s n) vaLoopIterPrefix).regs 59 lane
            + stride) >>> 32).truncate 32) := by
        rw [show ((runRealWith stepLoop (vaLoopIterState s n)
          vaLoopIterPrefix).regs 76 lane).truncate 32 =
            ((((vaLoopIterState s n).regs 59 lane + stride) >>> 32).truncate 32) from h76,
          ← h59frame]
      have hstep := vaLoop_coalesced_iteration_step (vaLoopIterState s n) lane 0
        aPtr bPtr cPtr (fun l => (vaLoopIterState s n).regs 59 l) stride
        hpreN hP6 hnewLow hnewHigh hl
      obtain ⟨-, -, hpreNext, hidxNext⟩ := hstep
      refine ⟨?_, ?_⟩
      · simpa [vaLoopIterState] using hpreNext
      · rw [show vaLoopIterState s (n + 1) = vaLoopIterNext (vaLoopIterState s n) from rfl]
        rw [hidxNext, strideId_succ]
        simp [hidxN]

/-- The state induction with the state-level P6 and writeback hypotheses.
This is the exact form produced by the decoded P6 packs, without routing
through the `vaLoopGuard` bridge. -/
theorem vaLoop_coalesced_iteration_state_p6 (s : RealState) (lane : Nat)
    (aPtr bPtr cPtr : Addr) (stride : Addr) (id : Addr) (n : Nat)
    (hpre : VaLoopBodyPre s aPtr bPtr cPtr (fun l => s.regs 59 l))
    (hid : s.regs 59 lane = id) (hl : lane < 24)
    (hP6 : ∀ k, k < n →
      (runRealWith stepLoop (vaLoopIterState s k) vaLoopIterPrefix).preds 6 lane = true)
    (hnewLow : ∀ k, k < n →
      ((runRealWith stepLoop (vaLoopIterState s k)
        vaLoopIterPrefix).regs 75 lane).truncate 32 =
      (((runRealWith stepLoop (vaLoopIterState s k) vaLoopIterPrefix).regs 59 lane
        + stride).truncate 32))
    (hnewHigh : ∀ k, k < n →
      ((runRealWith stepLoop (vaLoopIterState s k)
        vaLoopIterPrefix).regs 76 lane).truncate 32 =
      ((((runRealWith stepLoop (vaLoopIterState s k) vaLoopIterPrefix).regs 59 lane
        + stride) >>> 32).truncate 32)) :
    VaLoopBodyPre (vaLoopIterState s n) aPtr bPtr cPtr
      (fun l => (vaLoopIterState s n).regs 59 l) ∧
    (vaLoopIterState s n).regs 59 lane = strideId id stride n := by
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · simpa [vaLoopIterState] using hpre
      · simp [vaLoopIterState, hid, strideId_zero]
  | succ n ih =>
      obtain ⟨hpreN, hidxN⟩ := ih (fun k hk => hP6 k (by omega))
        (fun k hk => hnewLow k (by omega)) (fun k hk => hnewHigh k (by omega))
      have hstep := vaLoop_coalesced_iteration_step (vaLoopIterState s n) lane 0
        aPtr bPtr cPtr (fun l => (vaLoopIterState s n).regs 59 l) stride
        hpreN (hP6 n (Nat.lt_succ_self n)) (hnewLow n (Nat.lt_succ_self n))
        (hnewHigh n (Nat.lt_succ_self n)) hl
      obtain ⟨-, -, hpreNext, hidxNext⟩ := hstep
      refine ⟨?_, ?_⟩
      · simpa [vaLoopIterState] using hpreNext
      · rw [show vaLoopIterState s (n + 1) = vaLoopIterNext (vaLoopIterState s n) from rfl]
        rw [hidxNext, strideId_succ]
        simp [hidxN]

/-! ## Memory composition -/

/-- The next coalesced state's memory is exactly the body's `storeVec`. -/
theorem vaLoopIterNext_mem_storeVec (s : RealState) (aPtr bPtr cPtr : Addr)
    (idx : Nat → Addr) (h : VaLoopBodyPre s aPtr bPtr cPtr idx) :
    (vaLoopIterNext s).mem =
      storeVec s.mem 32 (fun l => cPtr + (idx l) <<< 2)
        (fun l => low32 ((runRealWith stepLoop s vaLoopBodySlice).regs 71 l)) := by
  unfold vaLoopIterNext
  rw [vaLoopCoalesced_mem, vaLoopIterPrefix_mem, vaLoopBodySlice_eq,
    vaLoopBody_stepLoop_eq s]
  exact vaLoopBody_mem s aPtr bPtr cPtr idx h

/-- An iteration leaves memory untouched at a word outside its 32 C stores. -/
theorem vaLoopIterNext_mem_frame (s : RealState) (aPtr bPtr cPtr : Addr)
    (idx : Nat → Addr) (h : VaLoopBodyPre s aPtr bPtr cPtr idx)
    (hc : cPtr.toNat % 4 = 0)
    (hboundC : ∀ l, l < 32 → cPtr.toNat + 4 * (idx l).toNat < 2 ^ 64)
    (w : Nat) (hfresh : ∀ l, l < 32 → cPtr.toNat / 4 + (idx l).toNat ≠ w) :
    (vaLoopIterNext s).mem w = s.mem w := by
  rw [vaLoopIterNext_mem_storeVec s aPtr bPtr cPtr idx h]
  rw [storeVec_frame]
  intro l hl
  rw [vaLoopWordBitVec cPtr (idx l) hc (hboundC l hl)]
  exact hfresh l hl

/-- Every iteration up to `n` avoids a fixed word. -/
theorem vaLoopIterState_mem_frame (s : RealState) (aPtr bPtr cPtr : Addr)
    (n : Nat)
    (hpre : ∀ j, j < n → VaLoopBodyPre (vaLoopIterState s j) aPtr bPtr cPtr
      (fun l => (vaLoopIterState s j).regs 59 l))
    (hc : cPtr.toNat % 4 = 0)
    (hboundC : ∀ j, j < n → ∀ l, l < 32 →
      cPtr.toNat + 4 * ((vaLoopIterState s j).regs 59 l).toNat < 2 ^ 64)
    (w : Nat)
    (havoid : ∀ j, j < n → ∀ l, l < 32 →
      cPtr.toNat / 4 + ((vaLoopIterState s j).regs 59 l).toNat ≠ w) :
    (vaLoopIterState s n).mem w = s.mem w := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [vaLoopIterState]
      rw [vaLoopIterNext_mem_frame (vaLoopIterState s n) aPtr bPtr cPtr
        (fun l => (vaLoopIterState s n).regs 59 l) (hpre n (Nat.lt_succ_self n)) hc
        (fun l hl => hboundC n (Nat.lt_succ_self n) l hl) w
        (fun l hl => havoid n (Nat.lt_succ_self n) l hl)]
      exact ih (fun j hj => hpre j (by omega))
        (fun j hj l hl => hboundC j (by omega) l hl)
        (fun j hj l hl => havoid j (by omega) l hl)

/-- The explicit disjointness conditions for the `n`-iteration memory
composition. Each iteration's 32 C stores are distinct, later iterations do
not overwrite earlier results, and no C store aliases an A/B read. -/
structure VaLoopIterMemorySafe (s : RealState) (aPtr bPtr cPtr : Addr)
    (stride : Addr) (id : Addr) (lane : Nat) (n : Nat) : Prop where
  laneLt : lane < 32
  aAlign : aPtr.toNat % 4 = 0
  bAlign : bPtr.toNat % 4 = 0
  cAlign : cPtr.toNat % 4 = 0
  aBound : ∀ k, k < n → aPtr.toNat + 4 * (strideId id stride k).toNat < 2 ^ 64
  bBound : ∀ k, k < n → bPtr.toNat + 4 * (strideId id stride k).toNat < 2 ^ 64
  cBound : ∀ k, k < n → cPtr.toNat + 4 * (strideId id stride k).toNat < 2 ^ 64
  cBoundAll : ∀ j, j < n → ∀ l, l < 32 →
    cPtr.toNat + 4 * ((vaLoopIterState s j).regs 59 l).toNat < 2 ^ 64
  distinct : ∀ j, j < n → ∀ l, l < 32 → l ≠ lane →
    cPtr.toNat / 4 + ((vaLoopIterState s j).regs 59 l).toNat ≠
      cPtr.toNat / 4 + (strideId id stride j).toNat
  freshC : ∀ j, j < n → ∀ k, k < j → ∀ l, l < 32 →
    cPtr.toNat / 4 + ((vaLoopIterState s j).regs 59 l).toNat ≠
      cPtr.toNat / 4 + (strideId id stride k).toNat
  sepA : ∀ j, j < n → ∀ k, k < n → ∀ l, l < 32 →
    cPtr.toNat / 4 + ((vaLoopIterState s j).regs 59 l).toNat ≠
      aPtr.toNat / 4 + (strideId id stride k).toNat
  sepB : ∀ j, j < n → ∀ k, k < n → ∀ l, l < 32 →
    cPtr.toNat / 4 + ((vaLoopIterState s j).regs 59 l).toNat ≠
      bPtr.toNat / 4 + (strideId id stride k).toNat

/-- The store composition over `n` iterations: after the induction state is
reached, every earlier `C[id_k]` still holds `A[id_k] + B[id_k]`. -/
theorem vaLoop_coalesced_iteration_memory (s : RealState) (lane : Nat)
    (aPtr bPtr cPtr : Addr) (stride : Addr) (id : Addr) (n : Nat)
    (hl : lane < 32)
    (hstate : ∀ k, k < n → (vaLoopIterState s k).regs 59 lane = strideId id stride k)
    (hpre : ∀ j, j < n → VaLoopBodyPre (vaLoopIterState s j) aPtr bPtr cPtr
      (fun l => (vaLoopIterState s j).regs 59 l))
    (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0) (hc : cPtr.toNat % 4 = 0)
    (hboundA : ∀ k, k < n → aPtr.toNat + 4 * (strideId id stride k).toNat < 2 ^ 64)
    (hboundB : ∀ k, k < n → bPtr.toNat + 4 * (strideId id stride k).toNat < 2 ^ 64)
    (hboundCk : ∀ k, k < n → cPtr.toNat + 4 * (strideId id stride k).toNat < 2 ^ 64)
    (hboundC : ∀ j, j < n → ∀ l, l < 32 →
      cPtr.toNat + 4 * ((vaLoopIterState s j).regs 59 l).toNat < 2 ^ 64)
    (hdistinct : ∀ j, j < n → ∀ l, l < 32 → l ≠ lane →
      cPtr.toNat / 4 + ((vaLoopIterState s j).regs 59 l).toNat ≠
        cPtr.toNat / 4 + (strideId id stride j).toNat)
    (hfreshC : ∀ j, j < n → ∀ k, k < j → ∀ l, l < 32 →
      cPtr.toNat / 4 + ((vaLoopIterState s j).regs 59 l).toNat ≠
        cPtr.toNat / 4 + (strideId id stride k).toNat)
    (hsepA : ∀ j, j < n → ∀ k, k < n → ∀ l, l < 32 →
      cPtr.toNat / 4 + ((vaLoopIterState s j).regs 59 l).toNat ≠
        aPtr.toNat / 4 + (strideId id stride k).toNat)
    (hsepB : ∀ j, j < n → ∀ k, k < n → ∀ l, l < 32 →
      cPtr.toNat / 4 + ((vaLoopIterState s j).regs 59 l).toNat ≠
        bPtr.toNat / 4 + (strideId id stride k).toNat) :
    ∀ k, k < n →
      (vaLoopIterState s n).mem (cPtr.toNat / 4 + (strideId id stride k).toNat) =
        s.mem (aPtr.toNat / 4 + (strideId id stride k).toNat) +
          s.mem (bPtr.toNat / 4 + (strideId id stride k).toNat) := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
      intro k hk
      have hpreN := hpre n (Nat.lt_succ_self n)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hkn | hkeq
      · rw [vaLoopIterState]
        rw [vaLoopIterNext_mem_frame (vaLoopIterState s n) aPtr bPtr cPtr
          (fun l => (vaLoopIterState s n).regs 59 l) hpreN hc
          (fun l hl => hboundC n (Nat.lt_succ_self n) l hl)
          (cPtr.toNat / 4 + (strideId id stride k).toNat)
          (fun l hl => hfreshC n (Nat.lt_succ_self n) k hkn l hl)]
        exact ih (fun j hj => hstate j (by omega))
          (fun j hj => hpre j (by omega)) (fun j hj => hboundA j (by omega))
          (fun j hj => hboundB j (by omega)) (fun j hj => hboundCk j (by omega))
          (fun j hj l hl => hboundC j (by omega) l hl)
          (fun j hj l hl hne => hdistinct j (by omega) l hl hne)
          (fun j hj k' hk' l hl => hfreshC j (by omega) k' hk' l hl)
          (fun j hj k' hk' l hl => hsepA j (by omega) k' (by omega) l hl)
          (fun j hj k' hk' l hl => hsepB j (by omega) k' (by omega) l hl)
          k hkn
      · subst k
        rw [vaLoopIterState]
        have hstep := vaLoop_coalesced_iteration_step_store (vaLoopIterState s n) lane
          aPtr bPtr cPtr (fun l => (vaLoopIterState s n).regs 59 l) hpreN hl
          ha hb hc
          (by rw [hstate n (Nat.lt_succ_self n)];
              exact hboundA n (Nat.lt_succ_self n))
          (by rw [hstate n (Nat.lt_succ_self n)];
              exact hboundB n (Nat.lt_succ_self n))
          (by rw [hstate n (Nat.lt_succ_self n)];
              exact hboundCk n (Nat.lt_succ_self n))
          (fun l hl' => hboundC n (Nat.lt_succ_self n) l hl')
          (fun l hl' hne => by
            rw [hstate n (Nat.lt_succ_self n)]
            exact hdistinct n (Nat.lt_succ_self n) l hl' hne)
        rw [hstate n (Nat.lt_succ_self n)] at hstep
        rw [hstep]
        rw [vaLoopIterState_mem_frame s aPtr bPtr cPtr n
          (fun j hj => hpre j (by omega)) hc
          (fun j hj l hl' => hboundC j (by omega) l hl')
          (aPtr.toNat / 4 + (strideId id stride n).toNat)
          (fun j hj l hl' => hsepA j (by omega) n (Nat.lt_succ_self n) l hl')]
        rw [vaLoopIterState_mem_frame s aPtr bPtr cPtr n
          (fun j hj => hpre j (by omega)) hc
          (fun j hj l hl' => hboundC j (by omega) l hl')
          (bPtr.toNat / 4 + (strideId id stride n).toNat)
          (fun j hj l hl' => hsepB j (by omega) n (Nat.lt_succ_self n) l hl')]

/-! ## The main induction -/

/-- The `n`-iteration coalesced grid-stride theorem. From the coalesced body
pre-state with lane index `id`, if the real P6 guard is true for every
iteration, then after `n` iterations the state carries the body
preconditions with index `strideId id stride n`, and every earlier store
`C[id_k] = A[id_k] + B[id_k]` is present. -/
theorem vaLoop_coalesced_iteration (s : RealState) (lane : Nat)
    (aPtr bPtr cPtr : Addr) (stride : Addr) (sizeLo sizeHi : Word)
    (id : Addr) (n : Nat)
    (hpre : VaLoopBodyPre s aPtr bPtr cPtr (fun l => s.regs 59 l))
    (hid : s.regs 59 lane = id) (hl : lane < 24)
    (hstride : s.regs 67 0 = stride)
    (hslo : low32 (s.regs 49 0) = sizeLo)
    (hshi : low32 (s.regs 49 1) = sizeHi)
    (hguard : ∀ k, k < n →
      vaLoopGuard (strideId id stride k + stride) (vaLoopSize sizeLo sizeHi) = true)
    (hSafe : VaLoopIterMemorySafe s aPtr bPtr cPtr stride id lane n) :
    VaLoopBodyPre (vaLoopIterState s n) aPtr bPtr cPtr
      (fun l => (vaLoopIterState s n).regs 59 l) ∧
    (vaLoopIterState s n).regs 59 lane = strideId id stride n ∧
    ∀ k, k < n →
      (vaLoopIterState s n).mem (cPtr.toNat / 4 + (strideId id stride k).toNat) =
        s.mem (aPtr.toNat / 4 + (strideId id stride k).toNat) +
          s.mem (bPtr.toNat / 4 + (strideId id stride k).toNat) := by
  have hstateAll : ∀ j, j ≤ n →
      VaLoopBodyPre (vaLoopIterState s j) aPtr bPtr cPtr
        (fun l => (vaLoopIterState s j).regs 59 l) ∧
      (vaLoopIterState s j).regs 59 lane = strideId id stride j := by
    intro j hj
    exact vaLoop_coalesced_iteration_state s lane aPtr bPtr cPtr stride sizeLo sizeHi id j
      hpre hid hl hstride hslo hshi (fun k hk => hguard k (by omega))
  obtain ⟨hpreN, hidxN⟩ := hstateAll n (by omega)
  refine ⟨hpreN, hidxN, ?_⟩
  exact vaLoop_coalesced_iteration_memory s lane aPtr bPtr cPtr stride id n hSafe.laneLt
    (fun k hk => (hstateAll k (by omega)).2)
    (fun j hj => (hstateAll j (by omega)).1)
    hSafe.aAlign hSafe.bAlign hSafe.cAlign hSafe.aBound hSafe.bBound hSafe.cBound
    hSafe.cBoundAll hSafe.distinct hSafe.freshC hSafe.sepA hSafe.sepB

/-- The `n`-iteration theorem with the state-level P6 and writeback
hypotheses. It avoids the `vaLoopGuard` decoder bridge, so its axiom
footprint is only `propext`, `Classical.choice` and `Quot.sound`. -/
theorem vaLoop_coalesced_iteration_p6 (s : RealState) (lane : Nat)
    (aPtr bPtr cPtr : Addr) (stride : Addr) (id : Addr) (n : Nat)
    (hpre : VaLoopBodyPre s aPtr bPtr cPtr (fun l => s.regs 59 l))
    (hid : s.regs 59 lane = id) (hl : lane < 24)
    (hP6 : ∀ k, k < n →
      (runRealWith stepLoop (vaLoopIterState s k) vaLoopIterPrefix).preds 6 lane = true)
    (hnewLow : ∀ k, k < n →
      ((runRealWith stepLoop (vaLoopIterState s k)
        vaLoopIterPrefix).regs 75 lane).truncate 32 =
      (((runRealWith stepLoop (vaLoopIterState s k) vaLoopIterPrefix).regs 59 lane
        + stride).truncate 32))
    (hnewHigh : ∀ k, k < n →
      ((runRealWith stepLoop (vaLoopIterState s k)
        vaLoopIterPrefix).regs 76 lane).truncate 32 =
      ((((runRealWith stepLoop (vaLoopIterState s k) vaLoopIterPrefix).regs 59 lane
        + stride) >>> 32).truncate 32))
    (hSafe : VaLoopIterMemorySafe s aPtr bPtr cPtr stride id lane n) :
    VaLoopBodyPre (vaLoopIterState s n) aPtr bPtr cPtr
      (fun l => (vaLoopIterState s n).regs 59 l) ∧
    (vaLoopIterState s n).regs 59 lane = strideId id stride n ∧
    ∀ k, k < n →
      (vaLoopIterState s n).mem (cPtr.toNat / 4 + (strideId id stride k).toNat) =
        s.mem (aPtr.toNat / 4 + (strideId id stride k).toNat) +
          s.mem (bPtr.toNat / 4 + (strideId id stride k).toNat) := by
  have hstateAll : ∀ j, j ≤ n →
      VaLoopBodyPre (vaLoopIterState s j) aPtr bPtr cPtr
        (fun l => (vaLoopIterState s j).regs 59 l) ∧
      (vaLoopIterState s j).regs 59 lane = strideId id stride j := by
    intro j hj
    exact vaLoop_coalesced_iteration_state_p6 s lane aPtr bPtr cPtr stride id j
      hpre hid hl (fun k hk => hP6 k (by omega))
      (fun k hk => hnewLow k (by omega)) (fun k hk => hnewHigh k (by omega))
  obtain ⟨hpreN, hidxN⟩ := hstateAll n (by omega)
  refine ⟨hpreN, hidxN, ?_⟩
  exact vaLoop_coalesced_iteration_memory s lane aPtr bPtr cPtr stride id n hSafe.laneLt
    (fun k hk => (hstateAll k (by omega)).2)
    (fun j hj => (hstateAll j (by omega)).1)
    hSafe.aAlign hSafe.bAlign hSafe.cAlign hSafe.aBound hSafe.bBound hSafe.cBound
    hSafe.cBoundAll hSafe.distinct hSafe.freshC hSafe.sepA hSafe.sepB

/-- The `n = 0` base case: no iterations, the state is the given coalesced
body pre-state and the lane still holds `id`. -/
theorem vaLoop_coalesced_iteration_zero (s : RealState) (lane : Nat)
    (aPtr bPtr cPtr : Addr) (stride : Addr) (id : Addr)
    (hpre : VaLoopBodyPre s aPtr bPtr cPtr (fun l => s.regs 59 l))
    (hid : s.regs 59 lane = id) :
    VaLoopBodyPre (vaLoopIterState s 0) aPtr bPtr cPtr
      (fun l => (vaLoopIterState s 0).regs 59 l) ∧
    (vaLoopIterState s 0).regs 59 lane = strideId id stride 0 := by
  refine ⟨?_, ?_⟩
  · simpa [vaLoopIterState] using hpre
  · simp [vaLoopIterState, hid, strideId_zero]

/-- The `n + 1` recurrence: one more step takes the state to the next
coalesced body pre-state and advances the lane index by `stride`. -/
theorem vaLoop_coalesced_iteration_succ (s : RealState) (lane : Nat)
    (aPtr bPtr cPtr : Addr) (stride : Addr) (idx : Nat → Addr) (id : Addr)
    (n : Nat)
    (hpre : VaLoopBodyPre (vaLoopIterState s n) aPtr bPtr cPtr idx)
    (hidx : (vaLoopIterState s n).regs 59 lane = id)
    (hP6 : (runRealWith stepLoop (vaLoopIterState s n) vaLoopIterPrefix).preds 6 lane
      = true)
    (hnewLow : ((runRealWith stepLoop (vaLoopIterState s n)
      vaLoopIterPrefix).regs 75 lane).truncate 32 =
      (((runRealWith stepLoop (vaLoopIterState s n) vaLoopIterPrefix).regs 59 lane
        + stride).truncate 32))
    (hnewHigh : ((runRealWith stepLoop (vaLoopIterState s n)
      vaLoopIterPrefix).regs 76 lane).truncate 32 =
      ((((runRealWith stepLoop (vaLoopIterState s n) vaLoopIterPrefix).regs 59 lane
        + stride) >>> 32).truncate 32))
    (hl : lane < 24) :
    VaLoopBodyPre (vaLoopIterState s (n + 1)) aPtr bPtr cPtr
      (fun l => (vaLoopIterState s (n + 1)).regs 59 l) ∧
    (vaLoopIterState s (n + 1)).regs 59 lane = id + stride := by
  have hstep := vaLoop_coalesced_iteration_step (vaLoopIterState s n) lane 0
    aPtr bPtr cPtr idx stride hpre hP6 hnewLow hnewHigh hl
  obtain ⟨-, -, hpreNext, hidxNext⟩ := hstep
  refine ⟨?_, ?_⟩
  · simpa [vaLoopIterState] using hpreNext
  · rw [vaLoopIterState]
    exact hidxNext.trans (by rw [← hpre.idxReg lane, hidx])

/-! ## Agreement with stage 160 and `n = 2` -/

/-- The state after one iteration is exactly stage 160's coalesced re-entry
state. -/
theorem vaLoopIterState_one_eq_stage160 (s : RealState) :
    vaLoopIterState s 1 =
      vaLoopCoalesced (runRealWith stepLoop s vaLoopIterPrefix) := rfl

/-- On the second body's pre-state, the lane index is stage 160's literal
`selectId old (old + stride) takeNew`. -/
theorem vaLoopIterState_one_index_stage160 (s : RealState) (stride : Addr)
    (lane : Nat) (idx : Nat → Addr) (hl : lane < 24)
    (hidx : ∀ k, (runRealWith stepLoop s vaLoopIterPrefix).regs 59 k = idx k)
    (hloop : VaLoopLoopBackPre (runRealWith stepLoop s vaLoopIterPrefix) stride) :
    (vaLoopIterState s 1).regs 59 lane =
      selectId idx (fun k => idx k + stride)
        (fun k => (runRealWith stepLoop s vaLoopIterPrefix).preds 6 k) lane := by
  rw [vaLoopIterState_one_eq_stage160]
  rw [coalesce_writeback (runRealWith stepLoop s vaLoopIterPrefix) stride lane hl hloop]
  simp [selectId, hidx]

/-- The `n = 2` specialization: two iterations advance the lane index to
`strideId id stride 2` and keep both `C[id]` and `C[id + stride]`. -/
theorem vaLoop_coalesced_iteration_two (s : RealState) (lane : Nat)
    (aPtr bPtr cPtr : Addr) (stride : Addr) (sizeLo sizeHi : Word) (id : Addr)
    (hpre : VaLoopBodyPre s aPtr bPtr cPtr (fun l => s.regs 59 l))
    (hid : s.regs 59 lane = id) (hl : lane < 24)
    (hstride : s.regs 67 0 = stride)
    (hslo : low32 (s.regs 49 0) = sizeLo)
    (hshi : low32 (s.regs 49 1) = sizeHi)
    (hguard : ∀ k, k < 2 →
      vaLoopGuard (strideId id stride k + stride) (vaLoopSize sizeLo sizeHi) = true)
    (hSafe : VaLoopIterMemorySafe s aPtr bPtr cPtr stride id lane 2) :
    (vaLoopIterState s 2).regs 59 lane = strideId id stride 2 ∧
    (vaLoopIterState s 2).mem (cPtr.toNat / 4 + id.toNat) =
      s.mem (aPtr.toNat / 4 + id.toNat) + s.mem (bPtr.toNat / 4 + id.toNat) ∧
    (vaLoopIterState s 2).mem (cPtr.toNat / 4 + (strideId id stride 1).toNat) =
      s.mem (aPtr.toNat / 4 + (strideId id stride 1).toNat) +
        s.mem (bPtr.toNat / 4 + (strideId id stride 1).toNat) := by
  have hmain := vaLoop_coalesced_iteration s lane aPtr bPtr cPtr stride sizeLo sizeHi id 2
    hpre hid hl hstride hslo hshi hguard hSafe
  obtain ⟨-, hidx2, hmem⟩ := hmain
  refine ⟨hidx2, ?_, ?_⟩
  · simpa [strideId_zero] using hmem 0 (by omega)
  · simpa [strideId_one] using hmem 1 (by omega)

/-- The second iteration's pre-state index agrees with stage 160's literal
second body: it is both the `selectId` expression and `old + stride`. -/
theorem vaLoop_coalesced_iteration_two_literal (s : RealState) (stride : Addr)
    (lane : Nat) (idx : Nat → Addr) (hl : lane < 24)
    (hidx : ∀ k, (runRealWith stepLoop s vaLoopIterPrefix).regs 59 k = idx k)
    (hloop : VaLoopLoopBackPre (runRealWith stepLoop s vaLoopIterPrefix) stride)
    (hP6 : (runRealWith stepLoop s vaLoopIterPrefix).preds 6 lane = true) :
    (vaLoopIterState s 1).regs 59 lane =
      selectId idx (fun k => idx k + stride)
        (fun k => (runRealWith stepLoop s vaLoopIterPrefix).preds 6 k) lane ∧
    (vaLoopIterState s 1).regs 59 lane = idx lane + stride := by
  have hsel := vaLoopIterState_one_index_stage160 s stride lane idx hl hidx hloop
  refine ⟨hsel, ?_⟩
  rw [hsel]
  exact selectId_true _ _ _ lane hP6

/-! ## The negative path -/

/-- At PC 35, a false `P6` takes stage 136's exit branch to PC 44. -/
theorem vaLoopP6_exit_stepLoop (s : RealState) (lane fuel : Nat)
    (h : s.preds 6 lane = false) :
    runRealCFLaneWith stepLoop vaLoopProgram s 35 (fuel + 1) lane =
      runRealCFLaneWith stepLoop vaLoopProgram s 44 fuel lane := by
  apply runRealCFLane_gotoIf_taken stepLoop vaLoopProgram s 35 fuel lane 32 6 true
    "_0_007" 44
  · exact vaLoopProgram_gotoIf_second
  · simp [h]
  · exact vaLoopProgram_label_exit

/-- Both decoded PC 35 branches, parameterised by the real guard value. -/
theorem vaLoop_coalesced_iteration_branch (s : RealState) (lane fuel : Nat)
    (nextId size : Addr)
    (hguard : (runRealWith stepLoop s vaLoopIterPrefix).preds 6 lane =
      vaLoopGuard nextId size) :
    (vaLoopGuard nextId size = true →
      runRealCFLaneWith stepLoop vaLoopProgram
          (runRealWith stepLoop s vaLoopIterPrefix) 35 (fuel + 1) lane =
        runRealCFLaneWith stepLoop vaLoopProgram
          (runRealWith stepLoop s vaLoopIterPrefix) 36 fuel lane) ∧
    (vaLoopGuard nextId size = false →
      runRealCFLaneWith stepLoop vaLoopProgram
          (runRealWith stepLoop s vaLoopIterPrefix) 35 (fuel + 1) lane =
        runRealCFLaneWith stepLoop vaLoopProgram
          (runRealWith stepLoop s vaLoopIterPrefix) 44 fuel lane) :=
  ⟨fun h => vaLoopP6_branch_fallthrough
      (runRealWith stepLoop s vaLoopIterPrefix) lane fuel nextId size hguard h,
    fun h => vaLoopP6_branch_exit
      (runRealWith stepLoop s vaLoopIterPrefix) lane fuel nextId size hguard h⟩

/-- If an iteration's real P6 is false, the decoded path from PC 21 takes
the exit branch instead of the loop-back and reaches PC 44. -/
theorem vaLoop_coalesced_iteration_exit (s : RealState) (lane fuel : Nat)
    (hP6 : (runRealWith stepLoop s vaLoopIterPrefix).preds 6 lane = false) :
    runRealCFLaneWith stepLoop vaLoopProgram s 21 (fuel + 15) lane =
      runRealCFLaneWith stepLoop vaLoopProgram
        (runRealWith stepLoop s vaLoopIterPrefix) 44 fuel lane := by
  have ht : runRealWith stepLoop s vaLoopIterPrefix =
      runRealWith stepLoop
        (runRealWith stepLoop
          (runRealWith stepLoop s vaLoopBodySlice) vaLoopIncAdd) vaLoopP6Prefix := by
    simp only [vaLoopIterPrefix, runRealWith_append]
  rw [show fuel + 15 = (fuel + 11) + 3 + 1 from rfl]
  rw [vaLoopCFBody s lane (fuel + 11)]
  rw [show fuel + 11 = (fuel + 10) + 1 from rfl]
  rw [vaLoopCFInc (runRealWith stepLoop s vaLoopBodySlice) lane (fuel + 10)]
  rw [show fuel + 10 = (fuel + 1) + 8 + 1 from rfl]
  rw [vaLoopCFP6 (runRealWith stepLoop
    (runRealWith stepLoop s vaLoopBodySlice) vaLoopIncAdd) lane (fuel + 1)]
  rw [← ht]
  exact vaLoopP6_exit_stepLoop _ lane fuel hP6

/-- The same negative fact on stage 136's full PC 17 entry path: a false P6
exits at PC 44. -/
theorem vaLoop_coalesced_iteration_exit_entry (s : RealState) (lane fuel : Nat)
    (hP3 : s.preds 3 lane = true)
    (hP6 : (runRealWith stepLoop s vaLoopPathPrefix).preds 6 lane = false) :
    runRealCFLaneWith stepLoop vaLoopProgram s 17 (fuel + 19) lane =
      runRealCFLaneWith stepLoop vaLoopProgram
        (runRealWith stepLoop s vaLoopPathPrefix) 44 fuel lane :=
  vaLoop_lane_body_exit s lane fuel hP3 hP6

end

end IntelGpu
