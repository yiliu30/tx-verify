-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.LoopControl
public import Intel.LoopEntryExec
public import Intel.LoopBodyExec
public import Intel.LoopIncExec
public import Intel.LoopP6Exec
public import Intel.LoopP3Exec
public import Intel.VectorAddLoopBody

@[expose] public section

/-!
# End-to-end decoded lane path through the loop vector add

This module composes the per-lane decoded control path of the loop vector add:

```
PC 17  (P3 false?)  --true--> PC 18..20   entry  (label, V67 <- V68, label)
                              PC 21..24   body   (load A, load B, add, store C)
                              PC 25       inc    (V72 <- V59 + V67)
                              PC 26..34   packs + second guard block (P6)
                              PC 35  (P6 false?) --true--> PC 44  _0_007
```

The two branch sites are the ones proved in `Intel.LoopControl`; the four
straight-line slices are the ones proved in `Intel.LoopEntryExec`,
`Intel.LoopBodyExec`, `Intel.LoopIncExec` and `Intel.LoopP6Exec`. This module
adds the missing bridge between the straight-line fold `runRealWith` and the
per-lane interpreter `runRealCFLaneWith`, then packages the composition.

The end-to-end theorem `vaLoop_lane_body_exit` states the exact control path.
The exit guard `P6 = false` is supplied as a hypothesis; `vaLoopP6_false`
derives it from the real second-guard result of `Intel.LoopP6Exec`,
`vaLoopP6_false_of_range` derives it from the range-completion fact used by the
one-body range kernel, and `vaLoop_lane_body_exit_with_guard` composes the two.

The body's memory effect `C[id] = A[id] + B[id]` is not included here yet: the
store result lives in `Intel.LoopBodyExec`, but transporting it through the
other slices needs memory-frame lemmas for `stepLoop` over the pack/guard
lists, whose `if src.num = 61/74` branches do not reduce under `simp` without
unfolding every register definition.

Everything here is stated for the already-decoded program `vaLoopProgram`, the
lane step `stepLoop`, and the per-lane interpreter `runRealCFLaneWith`.
-/

namespace IntelGpu

noncomputable section

/-! ## Straight-line bridge -/

/-- Instruction classes that `runRealCFLaneWith` executes through `step`
without consulting the predicate file. Labels, `goto` and `gotoIf` are the
three special cases. -/
def laneStraight : RInstr → Prop
  | .label _ => False
  | .goto _ _ => False
  | .gotoIf _ _ _ _ => False
  | _ => True

/-- A label advances the program counter without changing the state. -/
theorem runRealCFLaneWith_label (step : RealState → RInstr → RealState)
    (code : List RInstr) (s : RealState) (lane pc fuel : Nat) (name : String)
    (hcode : code[pc]? = some (.label name)) :
    runRealCFLaneWith step code s pc (fuel + 1) lane =
      runRealCFLaneWith step code s (pc + 1) fuel lane := by
  simp [runRealCFLaneWith, hcode]

/-- A non-control instruction fetches, runs `step`, and advances the program
counter by one. -/
theorem runRealCFLaneWith_plain (step : RealState → RInstr → RealState)
    (code : List RInstr) (s : RealState) (lane pc fuel : Nat) (ins : RInstr)
    (hcode : code[pc]? = some ins) (hstraight : laneStraight ins) :
    runRealCFLaneWith step code s pc (fuel + 1) lane =
      runRealCFLaneWith step code (step s ins) (pc + 1) fuel lane := by
  cases ins <;> simp_all [laneStraight, runRealCFLaneWith]

/-- The four decoded slices a lane executes between the two branch sites. -/
def vaLoopPathPrefix : List RInstr :=
  vaLoopEntryPrefix ++ vaLoopBodySlice ++ vaLoopIncAdd ++ vaLoopP6Prefix

/-- The parsed state just before the second guard block. -/
def vaLoopPreP6 (s : RealState) : RealState :=
  runRealWith stepLoop
    (runRealWith stepLoop
      (runRealWith stepLoop s vaLoopEntryPrefix) vaLoopBodySlice) vaLoopIncAdd

/-! ## Per-slice execution -/

/-- PCs 18--20 execute the decoded entry prefix and stop at PC 21. -/
theorem vaLoopCFEntry (s : RealState) (lane fuel : Nat) :
    runRealCFLaneWith stepLoop vaLoopProgram s 18 ((fuel + 2) + 1) lane =
      runRealCFLaneWith stepLoop vaLoopProgram
        (runRealWith stepLoop s vaLoopEntryPrefix) 21 fuel lane := by
  rw [runRealCFLaneWith_label stepLoop vaLoopProgram s lane 18 (fuel + 2)
    "_0_008" (by decide)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram s lane 19 (fuel + 1)
    (.mov (Exec.nm 1) ⟨67, 0, 0, 1, 1, 1⟩ ⟨68, 0, 0, 0, 1, 0⟩) (by decide)
    (by trivial)]
  rw [runRealCFLaneWith_label stepLoop vaLoopProgram
    (stepLoop s (.mov (Exec.nm 1) ⟨67, 0, 0, 1, 1, 1⟩ ⟨68, 0, 0, 0, 1, 0⟩))
    lane 20 fuel "_0_009" (by decide)]
  simp [vaLoopEntryPrefix, runRealWith, stepLoop_label]

/-- PCs 21--24 execute the decoded body and stop at PC 25. -/
theorem vaLoopCFBody (s : RealState) (lane fuel : Nat) :
    runRealCFLaneWith stepLoop vaLoopProgram s 21 (fuel + 3 + 1) lane =
      runRealCFLaneWith stepLoop vaLoopProgram
        (runRealWith stepLoop s vaLoopBodySlice) 25 fuel lane := by
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram s lane 21 (fuel + 3)
    (.loadScaled 32 69 .d32 47 59) (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop s (.loadScaled 32 69 .d32 47 59)) lane 22 (fuel + 2)
    (.loadScaled 32 70 .d32 48 59) (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop s (.loadScaled 32 69 .d32 47 59))
      (.loadScaled 32 70 .d32 48 59)) lane 23 (fuel + 1)
    (.add 32 ⟨71, 0, 0, 1, 1, 1⟩ ⟨69, 0, 0, 1, 1, 0⟩ ⟨70, 0, 0, 1, 1, 0⟩)
    (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop (stepLoop s (.loadScaled 32 69 .d32 47 59))
      (.loadScaled 32 70 .d32 48 59))
      (.add 32 ⟨71, 0, 0, 1, 1, 1⟩ ⟨69, 0, 0, 1, 1, 0⟩ ⟨70, 0, 0, 1, 1, 0⟩))
    lane 24 fuel (.storeScaled 32 46 59 .d32 71) (by decide) (by trivial)]
  rfl

/-- PC 25 executes the increment add and stops at PC 26. -/
theorem vaLoopCFInc (s : RealState) (lane fuel : Nat) :
    runRealCFLaneWith stepLoop vaLoopProgram s 25 (fuel + 1) lane =
      runRealCFLaneWith stepLoop vaLoopProgram
        (runRealWith stepLoop s vaLoopIncAdd) 26 fuel lane := by
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram s lane 25 fuel
    (.add 32 ⟨72, 0, 0, 1, 1, 1⟩ ⟨59, 0, 0, 1, 1, 0⟩ ⟨67, 0, 0, 0, 1, 0⟩)
    (by decide) (by trivial)]
  rfl

/-- PCs 26--34 execute the increment packs and the second guard block and stop
at PC 35. -/
theorem vaLoopCFP6 (s : RealState) (lane fuel : Nat) :
    runRealCFLaneWith stepLoop vaLoopProgram s 26 (fuel + 8 + 1) lane =
      runRealCFLaneWith stepLoop vaLoopProgram
        (runRealWith stepLoop s vaLoopP6Prefix) 35 fuel lane := by
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram s lane 26 (fuel + 8)
    (.mov 16 ⟨75, 0, 0, 1, 1, 1⟩ ⟨74, 0, 0, 2, 1, 0⟩) (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop s (.mov 16 ⟨75, 0, 0, 1, 1, 1⟩ ⟨74, 0, 0, 2, 1, 0⟩)) lane 27 (fuel + 7)
    (.movMasked ⟨16, 16, false⟩ ⟨75, 1, 0, 1, 1, 1⟩ ⟨74, 2, 0, 2, 1, 0⟩)
    (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop s (.mov 16 ⟨75, 0, 0, 1, 1, 1⟩ ⟨74, 0, 0, 2, 1, 0⟩))
      (.movMasked ⟨16, 16, false⟩ ⟨75, 1, 0, 1, 1, 1⟩ ⟨74, 2, 0, 2, 1, 0⟩))
    lane 28 (fuel + 6) (.mov 16 ⟨76, 0, 0, 1, 1, 1⟩ ⟨74, 0, 1, 2, 1, 0⟩)
    (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop (stepLoop s (.mov 16 ⟨75, 0, 0, 1, 1, 1⟩ ⟨74, 0, 0, 2, 1, 0⟩))
      (.movMasked ⟨16, 16, false⟩ ⟨75, 1, 0, 1, 1, 1⟩ ⟨74, 2, 0, 2, 1, 0⟩))
      (.mov 16 ⟨76, 0, 0, 1, 1, 1⟩ ⟨74, 0, 1, 2, 1, 0⟩))
    lane 29 (fuel + 5)
    (.movMasked ⟨16, 16, false⟩ ⟨76, 1, 0, 1, 1, 1⟩ ⟨74, 2, 1, 2, 1, 0⟩)
    (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop (stepLoop (stepLoop s
      (.mov 16 ⟨75, 0, 0, 1, 1, 1⟩ ⟨74, 0, 0, 2, 1, 0⟩))
      (.movMasked ⟨16, 16, false⟩ ⟨75, 1, 0, 1, 1, 1⟩ ⟨74, 2, 0, 2, 1, 0⟩))
      (.mov 16 ⟨76, 0, 0, 1, 1, 1⟩ ⟨74, 0, 1, 2, 1, 0⟩))
      (.movMasked ⟨16, 16, false⟩ ⟨76, 1, 0, 1, 1, 1⟩ ⟨74, 2, 1, 2, 1, 0⟩))
    lane 30 (fuel + 4) (.cmpLtReg 32 4 ⟨77, 0, 0, 1, 1, 0⟩ ⟨65, 0, 0, 0, 1, 0⟩)
    (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop s
      (.mov 16 ⟨75, 0, 0, 1, 1, 1⟩ ⟨74, 0, 0, 2, 1, 0⟩))
      (.movMasked ⟨16, 16, false⟩ ⟨75, 1, 0, 1, 1, 1⟩ ⟨74, 2, 0, 2, 1, 0⟩))
      (.mov 16 ⟨76, 0, 0, 1, 1, 1⟩ ⟨74, 0, 1, 2, 1, 0⟩))
      (.movMasked ⟨16, 16, false⟩ ⟨76, 1, 0, 1, 1, 1⟩ ⟨74, 2, 1, 2, 1, 0⟩))
      (.cmpLtReg 32 4 ⟨77, 0, 0, 1, 1, 0⟩ ⟨65, 0, 0, 0, 1, 0⟩))
    lane 31 (fuel + 3) (.cmpEqReg 32 5 ⟨76, 0, 0, 1, 1, 0⟩ ⟨49, 0, 1, 0, 1, 0⟩)
    (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop s
      (.mov 16 ⟨75, 0, 0, 1, 1, 1⟩ ⟨74, 0, 0, 2, 1, 0⟩))
      (.movMasked ⟨16, 16, false⟩ ⟨75, 1, 0, 1, 1, 1⟩ ⟨74, 2, 0, 2, 1, 0⟩))
      (.mov 16 ⟨76, 0, 0, 1, 1, 1⟩ ⟨74, 0, 1, 2, 1, 0⟩))
      (.movMasked ⟨16, 16, false⟩ ⟨76, 1, 0, 1, 1, 1⟩ ⟨74, 2, 1, 2, 1, 0⟩))
      (.cmpLtReg 32 4 ⟨77, 0, 0, 1, 1, 0⟩ ⟨65, 0, 0, 0, 1, 0⟩))
      (.cmpEqReg 32 5 ⟨76, 0, 0, 1, 1, 0⟩ ⟨49, 0, 1, 0, 1, 0⟩))
    lane 32 (fuel + 2) (.predAnd 32 5 5 4) (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop s
      (.mov 16 ⟨75, 0, 0, 1, 1, 1⟩ ⟨74, 0, 0, 2, 1, 0⟩))
      (.movMasked ⟨16, 16, false⟩ ⟨75, 1, 0, 1, 1, 1⟩ ⟨74, 2, 0, 2, 1, 0⟩))
      (.mov 16 ⟨76, 0, 0, 1, 1, 1⟩ ⟨74, 0, 1, 2, 1, 0⟩))
      (.movMasked ⟨16, 16, false⟩ ⟨76, 1, 0, 1, 1, 1⟩ ⟨74, 2, 1, 2, 1, 0⟩))
      (.cmpLtReg 32 4 ⟨77, 0, 0, 1, 1, 0⟩ ⟨65, 0, 0, 0, 1, 0⟩))
      (.cmpEqReg 32 5 ⟨76, 0, 0, 1, 1, 0⟩ ⟨49, 0, 1, 0, 1, 0⟩))
      (.predAnd 32 5 5 4))
    lane 33 (fuel + 1) (.cmpLtReg 32 6 ⟨78, 0, 0, 1, 1, 0⟩ ⟨65, 0, 1, 0, 1, 0⟩)
    (by decide) (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop s
      (.mov 16 ⟨75, 0, 0, 1, 1, 1⟩ ⟨74, 0, 0, 2, 1, 0⟩))
      (.movMasked ⟨16, 16, false⟩ ⟨75, 1, 0, 1, 1, 1⟩ ⟨74, 2, 0, 2, 1, 0⟩))
      (.mov 16 ⟨76, 0, 0, 1, 1, 1⟩ ⟨74, 0, 1, 2, 1, 0⟩))
      (.movMasked ⟨16, 16, false⟩ ⟨76, 1, 0, 1, 1, 1⟩ ⟨74, 2, 1, 2, 1, 0⟩))
      (.cmpLtReg 32 4 ⟨77, 0, 0, 1, 1, 0⟩ ⟨65, 0, 0, 0, 1, 0⟩))
      (.cmpEqReg 32 5 ⟨76, 0, 0, 1, 1, 0⟩ ⟨49, 0, 1, 0, 1, 0⟩))
      (.predAnd 32 5 5 4))
      (.cmpLtReg 32 6 ⟨78, 0, 0, 1, 1, 0⟩ ⟨65, 0, 1, 0, 1, 0⟩))
    lane 34 fuel (.predOr 32 6 6 5) (by decide) (by trivial)]
  rfl

/-! ## The exit path -/

/-- From PC 44 the exit label and the final `ret` leave memory unchanged. -/
theorem vaLoopCFLane_exit_mem (s : RealState) (lane fuel : Nat) :
    (runRealCFLaneWith stepLoop vaLoopProgram s 44 fuel lane).mem = s.mem := by
  cases fuel with
  | zero => rfl
  | succ f =>
    rw [runRealCFLaneWith_label stepLoop vaLoopProgram s lane 44 f "_0_007"
      (by decide)]
    cases f with
    | zero => rfl
    | succ g =>
      rw [runRealCFLaneWith_plain stepLoop vaLoopProgram s lane 45 g (.ret 1)
        (by decide) (by trivial)]
      cases g with
      | zero => rfl
      | succ h =>
        simp [runRealCFLaneWith,
          (by decide : vaLoopProgram[46]? = (none : Option RInstr)),
          stepLoop, stepVAL, stepWith]

/-- PCs 18--35: the three entry instructions, the four body instructions, the
increment add, and the nine increment-pack/guard instructions, stopping at the
second branch site. -/
theorem vaLoop_lane_body_step (s : RealState) (lane fuel : Nat) :
    runRealCFLaneWith stepLoop vaLoopProgram s 18 (fuel + 18) lane =
      runRealCFLaneWith stepLoop vaLoopProgram
        (runRealWith stepLoop s vaLoopPathPrefix) 35 (fuel + 1) lane := by
  simp only [vaLoopPathPrefix, runRealWith_append]
  rw [show fuel + 18 = (fuel + 15) + 2 + 1 from rfl]
  rw [vaLoopCFEntry s lane (fuel + 15)]
  rw [show fuel + 15 = (fuel + 11) + 3 + 1 from rfl]
  rw [vaLoopCFBody (runRealWith stepLoop s vaLoopEntryPrefix) lane (fuel + 11)]
  rw [show fuel + 11 = (fuel + 10) + 1 from rfl]
  rw [vaLoopCFInc (runRealWith stepLoop
    (runRealWith stepLoop s vaLoopEntryPrefix) vaLoopBodySlice) lane (fuel + 10)]
  rw [show fuel + 10 = (fuel + 1) + 8 + 1 from rfl]
  rw [vaLoopCFP6 (runRealWith stepLoop (runRealWith stepLoop
    (runRealWith stepLoop s vaLoopEntryPrefix) vaLoopBodySlice) vaLoopIncAdd)
    lane (fuel + 1)]

/-- End-to-end per-lane path: a lane entering the body at PC 17 with `P3`
true runs the decoded entry, body, increment and second-guard slices and
exits at PC 44 when the second guard `P6` is false. -/
theorem vaLoop_lane_body_exit (s : RealState) (lane fuel : Nat)
    (hP3 : s.preds 3 lane = true)
    (hP6 : (runRealWith stepLoop s vaLoopPathPrefix).preds 6 lane = false) :
    runRealCFLaneWith stepLoop vaLoopProgram s 17 (fuel + 19) lane =
      runRealCFLaneWith stepLoop vaLoopProgram
        (runRealWith stepLoop s vaLoopPathPrefix) 44 fuel lane := by
  rw [show fuel + 19 = (fuel + 18) + 1 from rfl]
  rw [vaLoopP3_branch_fallthrough s lane (fuel + 18) 0 1
    (by simpa [vaLoopGuard] using hP3) (by rfl)]
  rw [vaLoop_lane_body_step s lane fuel]
  exact vaLoopP6_branch_exit (runRealWith stepLoop s vaLoopPathPrefix) lane fuel 1 0
    (by simpa [vaLoopGuard] using hP6) (by rfl)

/-! ## Deriving the exit guard from the real second guard -/

/-- The `P6 = false` hypothesis of the path theorem is exactly the second
guard value computed by the decoded increment packs, once the pre-guard
register facts are supplied. -/
theorem vaLoopP6_false (s : RealState) (lane : Nat) (ids : Nat → Addr)
    (sizeLo sizeHi : Word)
    (hj : lane < 24)
    (hid : ∀ l, (vaLoopPreP6 s).regs 72 l = ids l)
    (hslo : low32 ((vaLoopPreP6 s).regs 49 0) = sizeLo)
    (hshi : low32 ((vaLoopPreP6 s).regs 49 1) = sizeHi)
    (hguard : vaLoopGuard (ids lane) (vaLoopSize sizeLo sizeHi) = false) :
    (runRealWith stepLoop s vaLoopPathPrefix).preds 6 lane = false := by
  have h := vaLoopP6_exec (vaLoopPreP6 s) ids sizeLo sizeHi lane hj hid hslo hshi
  simpa [vaLoopPathPrefix, vaLoopPreP6, runRealWith_append, hguard] using h

/-- Range-completion form: when the incremented id is `old + size` and the
64-bit sum does not wrap, the real second guard is false. -/
theorem vaLoopP6_false_of_range (s : RealState) (lane : Nat)
    (old : Nat → Addr) (size : Addr)
    (hj : lane < 24)
    (hid : ∀ l, (vaLoopPreP6 s).regs 72 l = old l + size)
    (hslo : low32 ((vaLoopPreP6 s).regs 49 0) = size.truncate 32)
    (hshi : low32 ((vaLoopPreP6 s).regs 49 1) = (size >>> 32).truncate 32)
    (hbound : (old lane).toNat + size.toNat < 2 ^ 64) :
    (runRealWith stepLoop s vaLoopPathPrefix).preds 6 lane = false := by
  apply vaLoopP6_false s lane (fun l => old l + size) (size.truncate 32)
    ((size >>> 32).truncate 32) hj hid hslo hshi
  rw [vaLoopSize_id]
  exact vaLoopNext_guard_false (old lane) size hbound

/-- The path theorem with the exit condition supplied by the real second
guard instead of an abstract `P6 = false`. -/
theorem vaLoop_lane_body_exit_with_guard (s : RealState) (lane fuel : Nat)
    (ids : Nat → Addr) (sizeLo sizeHi : Word)
    (hP3 : s.preds 3 lane = true)
    (hj : lane < 24)
    (hid : ∀ l, (vaLoopPreP6 s).regs 72 l = ids l)
    (hslo : low32 ((vaLoopPreP6 s).regs 49 0) = sizeLo)
    (hshi : low32 ((vaLoopPreP6 s).regs 49 1) = sizeHi)
    (hguard : vaLoopGuard (ids lane) (vaLoopSize sizeLo sizeHi) = false) :
    runRealCFLaneWith stepLoop vaLoopProgram s 17 (fuel + 19) lane =
      runRealCFLaneWith stepLoop vaLoopProgram
        (runRealWith stepLoop s vaLoopPathPrefix) 44 fuel lane :=
  vaLoop_lane_body_exit s lane fuel hP3
    (vaLoopP6_false s lane ids sizeLo sizeHi hj hid hslo hshi hguard)

end

end IntelGpu
