-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.SlmLatency

@[expose] public section

/-!
# Divergence and the barrier

Assumption 3 in the ledger says control flow is uniform across the workgroup.
Stages 16/17 get that for free by giving the workgroup a single predicate. This
module states what uniform control flow *buys*: a barrier retires only when
every lane has parked at it, so a lane that skipped it leaves the workgroup
stuck rather than silently proceeding.

- `allTrue`: a decidable "every lane below `n` satisfies `f`".
- `barrier_needs_all_lanes`: one lane missing ⇒ the barrier does not retire.
- `barrier_retires`: every lane parked ⇒ the phase advances.

That is the hazard the uniform-control-flow assumption rules out.
-/

namespace IntelGpu

/-- `allTrue f n` is `true` exactly when `f k` holds for every `k < n`. -/
def allTrue (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => f n && allTrue f n

theorem allTrue_eq_true (f : Nat → Bool) :
    ∀ n, allTrue f n = true ↔ ∀ k < n, f k = true := by
  intro n
  induction n with
  | zero => simp [allTrue]
  | succ n ih =>
      rw [allTrue, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h1, h2⟩ k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
        · exact h2 k hlt
        · exact h1
      · intro h
        exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (by omega)⟩

/-- A workgroup parked at a barrier: one flag per lane, plus the phase count. -/
structure Parked where
  lanes : Nat
  atBarrier : Nat → Bool
  phase : Nat

/-- The barrier retires only when every lane is parked. -/
def arrive (w : Parked) : Option Parked :=
  if allTrue w.atBarrier w.lanes then some { w with phase := w.phase + 1 } else none

/-- One lane missing is enough to wedge the barrier: this is the hazard that
uniform control flow rules out. -/
theorem barrier_needs_all_lanes (w : Parked) (h : ∃ l < w.lanes, w.atBarrier l = false) :
    arrive w = none := by
  obtain ⟨l, hl, hf⟩ := h
  have hnot : allTrue w.atBarrier w.lanes = false := by
    cases hall : allTrue w.atBarrier w.lanes with
    | false => rfl
    | true =>
        have := (allTrue_eq_true w.atBarrier w.lanes).mp hall l hl
        rw [hf] at this
        exact absurd this (by simp)
  simp [arrive, hnot]

/-- Every lane parked: the barrier retires and the phase advances. -/
theorem barrier_retires (w : Parked) (h : ∀ l < w.lanes, w.atBarrier l = true) :
    arrive w = some { w with phase := w.phase + 1 } := by
  have hall : allTrue w.atBarrier w.lanes = true :=
    (allTrue_eq_true w.atBarrier w.lanes).mpr h
  simp [arrive, hall]

/-- Two lanes: one parked, one not ⇒ stuck. -/
example :
    (arrive { lanes := 2, atBarrier := fun l => if l = 0 then true else false, phase := 0 }).isNone
      = true := by decide

/-- Two lanes, both parked ⇒ the phase advances to 1. -/
example :
    (arrive { lanes := 2, atBarrier := fun _ => true, phase := 0 }).map (fun w => w.phase)
      = some 1 := by decide

end IntelGpu
