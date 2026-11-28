-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.FpExceptionFlags
public import Intel.IeeeFp16Fma

@[expose] public section

/-!
# Sticky per-lane fp exception flags

Stage 166 models the five IEEE exception bits as a sticky per-operation summary
(`Flags`, `addFlags`, `fmaFlags`). The P1 numerical row in `Intel/REVIEW_63.md`
still lists "sticky lane state" as outside the proved class. This module adds
the architectural per-lane view.

- `LaneFlags` is a total function `Nat -> Flags`. Lanes outside an explicitly
  listed group are still represented, but `warpFlags` only unions the group.
- `LaneFlags.setLane`, `getLane` and `orLane` replace, read and stickily update
  one lane. `orLane` is the read-modify-write operation used by the model.
- `LaneFlags.sticky_set` records that an update cannot clear the addressed
  lane. `LaneFlags.sticky_monotone` records that every lane only grows.
- `warpFlags` unions a finite list of lane indices. It agrees with
  `Flags.foldFlags` on the mapped lane states, and
  `warpFlags_eq_lane_of_mem_of_others_none` recovers one lane's flags exactly
  when every other listed lane is clear.
- `iterateLaneFlags` accumulates a per-iteration per-lane flag function.
  `warpFlags_iterate` proves the two-level fold commutes: accumulating per
  lane and then taking the warp union equals accumulating the warp union of
  each iteration. `warpFlags_iterate_zero` and `warpFlags_iterate_succ` expose
  the `0` and `n + 1` recurrences.
- `kernelFlags` is the final warp view after `n` iterations. Its equality with
  the explicit iteration fold is `kernelFlags_eq_iteration_union`, and
  `warpFlagsIterate_eq_foldFlags` writes that fold as a `Flags.foldFlags` over
  `List.range n`.

The concrete examples cover an overflowing inexact lane, an invalid lane and a
two-lane/two-iteration fold. The last-write-wins comparison is a negative test:
destructive replacement drops an earlier inexact flag, while `orLane` keeps it.

## Modeled assumptions

- A lane's architectural sticky state is a `Flags` value. A per-operation
  summary from `addFlags` or `fmaFlags` is supplied by the caller's `step`
  function, one such summary per iteration and lane.
- Lane groups are explicit finite `List Nat`s. Repetition is harmless because
  `Flags.union` is idempotent, while the projection theorem assumes `Nodup` so
  that each lane is represented once.
- Sticky accumulation is sequential read-modify-write. The model does not
  describe arbitration between concurrent writes to the same physical flag
  register; the union operation is the architectural result.

## Outside the model

Hardware trap/mask behavior, trap delivery and per-lane physical flag registers
are not modeled. Bank conflicts, predicate masks, flush-to-zero,
denormals-are-zero and instruction replay are also outside the model. This is
the architectural sticky-flag view, not a register-transfer-level model of the
flag file. Timing, pipelining and cross-instruction scheduling are not modeled.

There are no new axioms, no `native_decide` and no `sorry`. The lane and fold
proofs audit to `propext` only; the concrete examples are axiom-free.
-/

namespace IntelGpu

/-- Architectural exception state for each lane, indexed by lane number. -/
abbrev LaneFlags : Type := Nat → Flags

namespace LaneFlags

/-- Read one lane's sticky flag state. -/
def getLane (state : LaneFlags) (lane : Nat) : Flags :=
  state lane

/-- Destructive lane replacement. This is not the sticky update. -/
def setLane (state : LaneFlags) (lane : Nat) (flags : Flags) : LaneFlags :=
  fun i => if i = lane then flags else state i

/-- Sticky read-modify-write: union an operation's flags into one lane. -/
def orLane (state : LaneFlags) (lane : Nat) (flags : Flags) : LaneFlags :=
  fun i => if i = lane then (state i).union flags else state i

/-- The all-clear lane state. -/
def none : LaneFlags :=
  fun _ => Flags.none

/-- One lane carrying `flags` and every other lane clear. -/
def singleLane (lane : Nat) (flags : Flags) : LaneFlags :=
  fun i => if i = lane then flags else Flags.none

/-- Pointwise sticky union of two lane states. -/
def union (a b : LaneFlags) : LaneFlags :=
  fun lane => (a lane).union (b lane)

/-- Pointwise sticky containment of lane states. -/
def le (a b : LaneFlags) : Prop :=
  ∀ lane, Flags.le (a lane) (b lane)

@[simp] theorem getLane_setLane_same (state : LaneFlags) (lane : Nat)
    (flags : Flags) :
    getLane (setLane state lane flags) lane = flags := by
  simp [getLane, setLane]

@[simp] theorem getLane_setLane_ne {state : LaneFlags} {lane i : Nat}
    (h : i ≠ lane) (flags : Flags) :
    getLane (setLane state lane flags) i = getLane state i := by
  simp [getLane, setLane, h]

@[simp] theorem getLane_orLane_same (state : LaneFlags) (lane : Nat)
    (flags : Flags) :
    getLane (orLane state lane flags) lane =
      (getLane state lane).union flags := by
  simp [getLane, orLane]

@[simp] theorem getLane_orLane_ne {state : LaneFlags} {lane i : Nat}
    (h : i ≠ lane) (flags : Flags) :
    getLane (orLane state lane flags) i = getLane state i := by
  simp [getLane, orLane, h]

@[simp] theorem getLane_none (lane : Nat) :
    getLane none lane = Flags.none := rfl

@[simp] theorem getLane_singleLane_same (lane : Nat) (flags : Flags) :
    getLane (singleLane lane flags) lane = flags := by
  simp [getLane, singleLane]

@[simp] theorem getLane_singleLane_ne {lane i : Nat} (h : i ≠ lane)
    (flags : Flags) :
    getLane (singleLane lane flags) i = Flags.none := by
  simp [getLane, singleLane, h]

@[simp] theorem getLane_union (a b : LaneFlags) (lane : Nat) :
    getLane (union a b) lane = (a lane).union (b lane) := rfl

theorem le_refl (a : LaneFlags) : le a a := by
  intro lane
  exact Flags.le_refl _

theorem le_trans {a b c : LaneFlags} (hab : le a b) (hbc : le b c) :
    le a c := by
  intro lane
  exact Flags.le_trans (hab lane) (hbc lane)

theorem sticky_set (state : LaneFlags) (lane : Nat) (flags : Flags) :
    Flags.le (getLane state lane) (getLane (orLane state lane flags) lane) := by
  simpa [getLane, orLane] using Flags.le_union_left (state lane) flags

theorem sticky_monotone (state : LaneFlags) (lane : Nat) (flags : Flags) :
    le state (orLane state lane flags) := by
  intro i
  by_cases h : i = lane
  · subst i
    simpa [getLane, orLane] using Flags.le_union_left (state lane) flags
  · simpa [getLane, orLane, h] using Flags.le_refl (state i)

end LaneFlags

namespace Flags

/-- The four-way interchange law used by the warp-union distributivity proof. -/
theorem union_union_union (a b c d : Flags) :
    (a.union b).union (c.union d) =
      (a.union c).union (b.union d) := by
  ext <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp only [Flags.union, Bool.or_comm, Bool.or_left_comm]

end Flags

/-- Union the sticky flag states of an explicit finite lane group. -/
def warpFlags : List Nat → LaneFlags → Flags
  | [], _ => Flags.none
  | lane :: lanes, state =>
      (state lane).union (warpFlags lanes state)

@[simp] theorem warpFlags_nil (state : LaneFlags) :
    warpFlags [] state = Flags.none := rfl

@[simp] theorem warpFlags_cons (lane : Nat) (lanes : List Nat)
    (state : LaneFlags) :
    warpFlags (lane :: lanes) state =
      (state lane).union (warpFlags lanes state) := rfl

@[simp] theorem warpFlags_none (lanes : List Nat) :
    warpFlags lanes LaneFlags.none = Flags.none := by
  induction lanes with
  | nil => rfl
  | cons lane lanes ih => simp [warpFlags, LaneFlags.none, ih]

theorem warpFlags_eq_foldr (lanes : List Nat) (state : LaneFlags) :
    warpFlags lanes state =
      (lanes.map state).foldr Flags.union Flags.none := by
  induction lanes with
  | nil => rfl
  | cons lane lanes ih =>
      rw [warpFlags_cons, ih]
      rfl

theorem warpFlags_eq_foldFlags (lanes : List Nat) (state : LaneFlags) :
    warpFlags lanes state =
      Flags.foldFlags Flags.none (lanes.map state) := by
  rw [warpFlags_eq_foldr, Flags.foldFlags_eq_foldr]

theorem warpFlags_eq_none_of_forall_none (lanes : List Nat)
    (state : LaneFlags)
    (h : ∀ lane ∈ lanes, state lane = Flags.none) :
    warpFlags lanes state = Flags.none := by
  induction lanes with
  | nil => rfl
  | cons lane lanes ih =>
      rw [warpFlags_cons, h lane (by simp)]
      simp only [Flags.union_none_left]
      exact ih (fun j hj => h j (List.mem_cons_of_mem _ hj))

/-- With a `Nodup` lane group, a lane that is the only contributor projects
back out of the warp union exactly. -/
theorem warpFlags_eq_lane_of_mem_of_others_none {lanes : List Nat}
    {state : LaneFlags} {lane : Nat} (hnd : lanes.Nodup) (hmem : lane ∈ lanes)
    (hother : ∀ j ∈ lanes, j ≠ lane → state j = Flags.none) :
    warpFlags lanes state = state lane := by
  induction lanes with
  | nil => simp at hmem
  | cons head tail ih =>
      rw [warpFlags_cons]
      by_cases hhead : head = lane
      · subst head
        have hnot : lane ∉ tail := (List.nodup_cons.mp hnd).1
        have htail : warpFlags tail state = Flags.none :=
          warpFlags_eq_none_of_forall_none tail state (by
            intro j hj
            exact hother j (List.mem_cons_of_mem _ hj) (by
              intro hjl
              exact hnot (hjl ▸ hj)))
        rw [htail, Flags.union_none_right]
      · have hget : state head = Flags.none :=
          hother head (by simp) hhead
        rw [hget, Flags.union_none_left]
        exact ih (List.nodup_cons.mp hnd).2 (by
          rcases List.mem_cons.mp hmem with h | h
          · exact absurd h.symm hhead
          · exact h) (by
            intro j hj hjne
            exact hother j (List.mem_cons_of_mem _ hj) hjne)

theorem warpFlags_union (lanes : List Nat) (a b : LaneFlags) :
    warpFlags lanes (a.union b) =
      (warpFlags lanes a).union (warpFlags lanes b) := by
  induction lanes with
  | nil => simp [warpFlags]
  | cons lane lanes ih =>
      rw [warpFlags_cons, warpFlags_cons, warpFlags_cons, ih]
      change (((a lane).union (b lane)).union
          ((warpFlags lanes a).union (warpFlags lanes b))) =
        (((a lane).union (warpFlags lanes a)).union
          ((b lane).union (warpFlags lanes b)))
      exact Flags.union_union_union _ _ _ _

/-- Sticky accumulation of a per-iteration per-lane flag function. -/
def iterateLaneFlags (step : Nat → LaneFlags) : Nat → LaneFlags
  | 0 => LaneFlags.none
  | n + 1 => (iterateLaneFlags step n).union (step n)

/-- The explicit two-level fold: union each iteration's warp flags. -/
def warpFlagsIterate (lanes : List Nat) (step : Nat → LaneFlags) : Nat → Flags
  | 0 => Flags.none
  | n + 1 =>
      (warpFlagsIterate lanes step n).union (warpFlags lanes (step n))

@[simp] theorem iterateLaneFlags_zero (step : Nat → LaneFlags) :
    iterateLaneFlags step 0 = LaneFlags.none := rfl

@[simp] theorem iterateLaneFlags_succ (step : Nat → LaneFlags) (n : Nat) :
    iterateLaneFlags step (n + 1) =
      (iterateLaneFlags step n).union (step n) := rfl

@[simp] theorem warpFlagsIterate_zero (lanes : List Nat)
    (step : Nat → LaneFlags) :
    warpFlagsIterate lanes step 0 = Flags.none := rfl

@[simp] theorem warpFlagsIterate_succ (lanes : List Nat)
    (step : Nat → LaneFlags) (n : Nat) :
    warpFlagsIterate lanes step (n + 1) =
      (warpFlagsIterate lanes step n).union
        (warpFlags lanes (step n)) := rfl

theorem warpFlagsIterate_eq_foldFlags (lanes : List Nat)
    (step : Nat → LaneFlags) (n : Nat) :
    warpFlagsIterate lanes step n =
      Flags.foldFlags Flags.none
        ((List.range n).map (fun i => warpFlags lanes (step i))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [warpFlagsIterate_succ, ih, List.range_succ, List.map_append,
        Flags.foldFlags_append]
      simp [Flags.foldFlags]

/-- The final warp flags after the first `n` iterations. -/
def kernelFlags (lanes : List Nat) (step : Nat → LaneFlags) (n : Nat) : Flags :=
  warpFlags lanes (iterateLaneFlags step n)

@[simp] theorem warpFlags_iterate_zero (lanes : List Nat)
    (step : Nat → LaneFlags) :
    warpFlags lanes (iterateLaneFlags step 0) = Flags.none := by
  simp [iterateLaneFlags, warpFlags_none]

theorem warpFlags_iterate_succ (lanes : List Nat) (step : Nat → LaneFlags)
    (n : Nat) :
    warpFlags lanes (iterateLaneFlags step (n + 1)) =
      (warpFlags lanes (iterateLaneFlags step n)).union
        (warpFlags lanes (step n)) := by
  rw [iterateLaneFlags_succ, warpFlags_union]

/-- The per-lane fold and the per-iteration fold commute. -/
theorem warpFlags_iterate (lanes : List Nat) (step : Nat → LaneFlags) :
    ∀ n, warpFlags lanes (iterateLaneFlags step n) =
      warpFlagsIterate lanes step n
  | 0 => by simp [warpFlagsIterate]
  | n + 1 => by
      rw [warpFlags_iterate_succ, warpFlags_iterate lanes step n,
        warpFlagsIterate_succ]

theorem kernelFlags_eq_iteration_union (lanes : List Nat)
    (step : Nat → LaneFlags) (n : Nat) :
    kernelFlags lanes step n = warpFlagsIterate lanes step n :=
  warpFlags_iterate lanes step n

theorem kernelFlags_eq_foldFlags (lanes : List Nat)
    (step : Nat → LaneFlags) (n : Nat) :
    kernelFlags lanes step n =
      Flags.foldFlags Flags.none
        ((List.range n).map (fun i => warpFlags lanes (step i))) := by
  rw [kernelFlags_eq_iteration_union, warpFlagsIterate_eq_foldFlags]

/-- One lane with overflow and inexact set, as produced by an overflowing
rounded operation. -/
theorem example_overflow_inexact_lane :
    LaneFlags.getLane (LaneFlags.singleLane 0 Flags.overflowInexact) 0 =
      Flags.overflowInexact := by
  decide

theorem example_overflow_inexact_bits :
    (LaneFlags.getLane (LaneFlags.singleLane 0 Flags.overflowInexact) 0).overflow =
        true ∧
      (LaneFlags.getLane
        (LaneFlags.singleLane 0 Flags.overflowInexact) 0).inexact = true := by
  decide

/-- One lane with invalid set. -/
theorem example_invalid_lane :
    LaneFlags.getLane (LaneFlags.singleLane 1 Flags.invalidOnly) 1 =
      Flags.invalidOnly := by
  decide

theorem example_invalid_bit :
    (LaneFlags.getLane
      (LaneFlags.singleLane 1 Flags.invalidOnly) 1).invalid = true := by
  decide

/-- Iteration 0 marks lane 0 inexact; iteration 1 adds overflow to lane 0 and
invalid to lane 1. -/
def twoLaneTwoIterationStep : Nat → LaneFlags
  | 0 => LaneFlags.singleLane 0 Flags.inexactOnly
  | 1 => (LaneFlags.singleLane 0 Flags.overflowInexact).union
           (LaneFlags.singleLane 1 Flags.invalidOnly)
  | _ => LaneFlags.none

theorem example_two_lane_two_iteration_lane0 :
    LaneFlags.getLane (iterateLaneFlags twoLaneTwoIterationStep 2) 0 =
      Flags.overflowInexact := by
  decide

theorem example_two_lane_two_iteration_lane1 :
    LaneFlags.getLane (iterateLaneFlags twoLaneTwoIterationStep 2) 1 =
      Flags.invalidOnly := by
  decide

theorem example_two_lane_two_iteration_warp :
    kernelFlags [0, 1] twoLaneTwoIterationStep 2 =
      Flags.overflowInexact.union Flags.invalidOnly := by
  decide

/-- Damaging replacement used only for the negative comparison. -/
def lastWriteLane (state : LaneFlags) (lane : Nat) (flags : Flags) : LaneFlags :=
  LaneFlags.setLane state lane flags

/-- Last-write-wins loses the earlier inexact flag. -/
theorem lastWrite_loses_earlier_inexact :
    (LaneFlags.getLane (lastWriteLane
      (LaneFlags.singleLane 0 Flags.inexactOnly) 0 Flags.none) 0).inexact =
        false := by
  decide

/-- The sticky update preserves the earlier inexact flag. -/
theorem sticky_preserves_earlier_inexact :
    (LaneFlags.getLane (LaneFlags.orLane
      (LaneFlags.singleLane 0 Flags.inexactOnly) 0 Flags.none) 0).inexact =
        true := by
  decide

/-- The negative and positive halves of the last-write comparison together. -/
theorem lastWrite_vs_sticky_inexact :
    (LaneFlags.getLane (lastWriteLane
      (LaneFlags.singleLane 0 Flags.inexactOnly) 0 Flags.none) 0).inexact =
        false ∧
      (LaneFlags.getLane (LaneFlags.orLane
        (LaneFlags.singleLane 0 Flags.inexactOnly) 0 Flags.none) 0).inexact =
          true := by
  decide

/-- The unique contributing lane projects out of the warp union. -/
theorem warpFlags_projects_lane {lanes : List Nat} {state : LaneFlags}
    {lane : Nat} (hnd : lanes.Nodup) (hmem : lane ∈ lanes)
    (hother : ∀ j ∈ lanes, j ≠ lane → state j = Flags.none) :
    warpFlags lanes state = LaneFlags.getLane state lane :=
  warpFlags_eq_lane_of_mem_of_others_none hnd hmem hother

end IntelGpu
