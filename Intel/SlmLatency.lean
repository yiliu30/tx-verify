-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.GemmSlm

@[expose] public section

/-!
# Why the barrier is necessary

The workgroup machine of stage 13 makes an SLM write visible as soon as it
retires, so a barrier is only an ordering annotation there. On real hardware an
SLM write is not visible to other lanes immediately. This module models that
minimal hazard — a write lands in a pending buffer, reads see the committed
copy, and the barrier commits — and proves the two facts that justify the
barrier:

- `stale_without_barrier`: a lane that reads before the barrier sees the *old*
  value, so skipping the barrier is a correctness bug, not a style choice.
- `fresh_with_barrier`: after the barrier the write is visible.

Nothing here is new machinery for the GEMM proof; it is the argument that the
barrier in stages 13-17 is doing work.
-/

namespace IntelGpu

/-- SLM with a committed copy and a pending write buffer. -/
structure Staged where
  committed : Nat → Word
  pending : Nat → Word

/-- A lane writes: the value lands in the pending buffer. -/
def stagedWrite (s : Staged) (a v : Nat) : Staged :=
  { s with pending := fun n => if n = a then (v : Word) else s.pending n }

/-- A read sees the committed copy only. -/
def stagedRead (s : Staged) (a : Nat) : Word := s.committed a

/-- The barrier commits the pending writes. -/
def stagedBarrier (s : Staged) : Staged :=
  { s with committed := s.pending }

/-- Reading before the barrier sees the old value: the write is not visible. -/
theorem stale_without_barrier (s : Staged) (a v : Nat) :
    stagedRead (stagedWrite s a v) a = s.committed a := rfl

/-- After the barrier the write is visible. -/
theorem fresh_with_barrier (s : Staged) (a v : Nat) :
    stagedRead (stagedBarrier (stagedWrite s a v)) a = (v : Word) := by
  simp [stagedRead, stagedBarrier, stagedWrite]

/-- A barrier commits *every* pending write, not just the one at `a`. So after
the sync another address reads its pending value — which is what the GEMM tile
needs: lane 1's staged word is readable by lane 0.

I first stated this as `= s.committed b`, which is false: the barrier exposes
the pending buffer wholesale. -/
theorem cross_lane_after_barrier (s : Staged) (a v b : Nat) (hne : b ≠ a) :
    stagedRead (stagedBarrier (stagedWrite s a v)) b = s.pending b := by
  simp [stagedRead, stagedBarrier, stagedWrite, hne]

end IntelGpu
