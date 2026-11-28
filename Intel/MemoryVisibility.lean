-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.MemoryLaws

@[expose] public section

/-!
# Visibility and release/acquire synchronization

This module extends the per-lane frame laws with a deliberately small memory
model. It is not a model of the full Xe memory system.

`VisState` keeps, for each location, an oldest-to-newest `storeLog` and a
`visibleCount` prefix. `mem` is the latest visible value. A `write` appends to
the log but leaves it pending; `releaseFence` publishes the whole log; and
`acquireFence` is the identity in this cacheless model. `read` returns `mem`.

The model assumptions are:

- no caches: each location has one globally visible value;
- stores at a location are totally ordered by `storeLog`;
- visibility is a prefix of that order, and a read sees the latest visible
  entry;
- a plain store is pending until a release fence; fences are full barriers;
- release/acquire synchronization orders the producer's stores before the
  consumer's reads.

Proved here, not assumed:

- `Coherent` is preserved by initialization, writes, release and acquire;
- `read_write_same`: a released write is read back at the same location;
- `write_write_order`: same-location writes retain program order;
- `read_never_unwritten`: a coherent read returns a value in its store log;
- `release_acquire_message_passing`: after release/acquire, observing
  `flag = true` returns the published data, never the stale pre-publication
  value (`release_acquire_no_stale`).

Not modelled: cache-coherence traffic, relaxed atomics, partial visibility,
cross-thread interleavings, byte addressing, and SLM aliasing. The theorem is
therefore a proof of the synchronization pattern under these assumptions, not
a hardware-conformance claim.
-/

namespace IntelGpu

/-- The word used for a set flag. -/
def flagTrue : Word := 1

/-- A per-location store history with a visible prefix. -/
structure VisState where
  /-- The latest globally visible value at each location. -/
  mem : Nat → Word
  /-- Stores at each location, oldest first. -/
  storeLog : Nat → List Word
  /-- How many entries of `storeLog` are visible. -/
  visibleCount : Nat → Nat

/-- The initial state: each log starts with its visible initial value. -/
def initial (init : Nat → Word) : VisState where
  mem := init
  storeLog := fun a => [init a]
  visibleCount := fun _ => 1

/-- A read observes the latest visible value. -/
def read (s : VisState) (a : Nat) : Word :=
  s.mem a

/-- A pending store: append to the per-location log without publishing it. -/
def write (s : VisState) (a : Nat) (v : Word) : VisState :=
  { s with storeLog := fun i => if i = a then s.storeLog i ++ [v] else s.storeLog i }

/-- Last element, or the fallback for an empty log. -/
def lastOr (xs : List Word) (fallback : Word) : Word :=
  xs.getLast?.getD fallback

/-- A release publishes every pending store. -/
def releaseFence (s : VisState) : VisState :=
  { s with
    mem := fun a => lastOr (s.storeLog a) (s.mem a)
    visibleCount := fun a => (s.storeLog a).length }

/-- An acquire is identity: there is no cache to invalidate in this model. -/
def acquireFence (s : VisState) : VisState :=
  s

/-- Per-location coherence: the read value is the latest visible log entry. -/
structure Coherent (s : VisState) : Prop where
  /-- A visible prefix is nonempty. -/
  visible_pos : ∀ a, 0 < s.visibleCount a
  /-- The visible prefix does not run past the log. -/
  visible_le : ∀ a, s.visibleCount a ≤ (s.storeLog a).length
  /-- `mem` is exactly the last entry of the visible prefix. -/
  mem_latest : ∀ a, (s.storeLog a)[s.visibleCount a - 1]? = some (s.mem a)

/-- Initialization satisfies per-location coherence. -/
theorem coherent_initial (init : Nat → Word) : Coherent (initial init) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [initial]

/-- A write to one location leaves every other location unchanged. -/
theorem write_storeLog_other (s : VisState) (a : Nat) (v : Word) (b : Nat)
    (h : a ≠ b) :
    (write s a v).storeLog b = s.storeLog b := by
  by_cases hba : b = a
  · exact (h hba.symm).elim
  · simp [write, hba]

/-- Same-location writes are appended in program order. -/
theorem write_write_order (s : VisState) (a : Nat) (v w : Word) :
    (write (write s a v) a w).storeLog a = s.storeLog a ++ [v, w] := by
  simp [write, List.append_assoc]

/-- A write does not publish any pending entry. -/
theorem write_visibleCount (s : VisState) (a : Nat) (v : Word) :
    (write s a v).visibleCount a = s.visibleCount a := by
  simp [write]

/-- Writing preserves coherence. -/
theorem coherent_write (s : VisState) (hs : Coherent s) (a : Nat) (v : Word) :
    Coherent (write s a v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b
    by_cases hb : b = a
    · subst b
      simp [write]
      exact hs.visible_pos a
    · simpa [write, hb] using hs.visible_pos b
  · intro b
    by_cases hb : b = a
    · subst b
      have hle := hs.visible_le a
      simp [write, List.length_append]
      omega
    · simpa [write, hb] using hs.visible_le b
  · intro b
    by_cases hb : b = a
    · subst b
      rcases List.getElem?_eq_some_iff.mp (hs.mem_latest a) with ⟨hlt, heq⟩
      have happ : (s.storeLog a ++ [v])[s.visibleCount a - 1]? =
          (s.storeLog a)[s.visibleCount a - 1]? :=
        List.getElem?_append_left hlt
      simp [write]
      rw [happ, hs.mem_latest a]
    · simpa [write, hb] using hs.mem_latest b

/-- Releasing publishes the full log at every location. -/
theorem releaseFence_visibleCount (s : VisState) (a : Nat) :
    (releaseFence s).visibleCount a = (s.storeLog a).length := by
  rfl

/-- The value left by a release at a location is the log's last entry. -/
theorem releaseFence_mem (s : VisState) (a : Nat) :
    (releaseFence s).mem a = lastOr (s.storeLog a) (s.mem a) := by
  rfl

/-- Releasing preserves coherence. -/
theorem coherent_releaseFence (s : VisState) (hs : Coherent s) :
    Coherent (releaseFence s) := by
  have hnonempty : ∀ a, s.storeLog a ≠ [] := by
    intro a
    exact List.ne_nil_of_length_pos (Nat.lt_of_lt_of_le (hs.visible_pos a)
      (hs.visible_le a))
  refine ⟨?_, ?_, ?_⟩
  · intro a
    have hpos := hs.visible_pos a
    have hle := hs.visible_le a
    simp [releaseFence]
    omega
  · intro a
    simp [releaseFence]
  · intro a
    have hne := hnonempty a
    have hlast : (s.storeLog a).getLast? =
        some ((s.storeLog a).getLast hne) :=
      List.getLast?_eq_some_getLast hne
    have hidx : (s.storeLog a)[(s.storeLog a).length - 1]? =
        some ((s.storeLog a).getLast hne) := by
      rw [← List.getLast?_eq_getElem?, hlast]
    simp [releaseFence, lastOr, hlast, hidx]

/-- Acquiring preserves coherence. -/
theorem coherent_acquireFence (s : VisState) (hs : Coherent s) :
    Coherent (acquireFence s) := by
  simpa [acquireFence] using hs

/-- A read after a released same-location write returns that write. -/
theorem read_write_same (s : VisState) (a : Nat) (v : Word) :
    read (releaseFence (write s a v)) a = v := by
  simp [read, releaseFence, write, lastOr, List.getLast?_append]

/-- A write to a different location does not disturb a read. -/
theorem read_write_other (s : VisState) (a b : Nat) (v : Word) (h : a ≠ b) :
    read (write s a v) b = read s b := by
  by_cases hba : b = a
  · exact (h hba.symm).elim
  · simp [read, write]

/-- Every coherent read is a value that was actually written at that location. -/
theorem read_never_unwritten (s : VisState) (hs : Coherent s) (a : Nat) :
    read s a ∈ s.storeLog a := by
  rcases List.getElem?_eq_some_iff.mp (hs.mem_latest a) with ⟨hidx, heq⟩
  rw [read, ← heq]
  exact List.getElem_mem hidx

/-- The latest visible log entry is exactly the value returned by a read. -/
theorem read_is_latest_visible (s : VisState) (hs : Coherent s) (a : Nat) :
    (s.storeLog a)[s.visibleCount a - 1]? = some (read s a) := by
  simpa [read] using hs.mem_latest a

/-- The producer publishes data, then the flag, then synchronizes. -/
def messagePassing (s : VisState) (dataAddr flagAddr : Nat) (data : Word) :
    VisState :=
  acquireFence (releaseFence (write (write s dataAddr data) flagAddr flagTrue))

/-- The consumer reads the flag first, and the data only if the flag is true. -/
def observeAfterFlag (s : VisState) (dataAddr flagAddr : Nat) : Option Word :=
  if read s flagAddr = flagTrue then some (read s dataAddr) else none

/-- After release/acquire, a true flag makes the consumer observe the published
data. -/
theorem release_acquire_message_passing (s : VisState) (dataAddr flagAddr : Nat)
    (data : Word) (hne : dataAddr ≠ flagAddr) :
    observeAfterFlag (messagePassing s dataAddr flagAddr data) dataAddr flagAddr =
      some data := by
  simp [observeAfterFlag, messagePassing, acquireFence, releaseFence, write,
    read, lastOr, List.getLast?_append, hne, Ne.symm hne]

/-- Starting from the initial memory, a true flag cannot expose the stale
pre-publication data value. -/
theorem release_acquire_no_stale (init : Nat → Word) (dataAddr flagAddr : Nat)
    (data : Word) (hne : dataAddr ≠ flagAddr) (hstale : data ≠ init dataAddr) :
    observeAfterFlag (messagePassing (initial init) dataAddr flagAddr data)
        dataAddr flagAddr ≠ some (init dataAddr) := by
  rw [release_acquire_message_passing (initial init) dataAddr flagAddr data hne]
  simp [hstale]

/-- A negative test: without the release, a flag that is already set can expose
the stale data value. -/
theorem without_release_stale_observable (init : Nat → Word) (dataAddr flagAddr : Nat)
    (data : Word) (hflag : init flagAddr = flagTrue) :
    observeAfterFlag (write (write (initial init) dataAddr data) flagAddr flagTrue)
        dataAddr flagAddr = some (init dataAddr) := by
  simp [observeAfterFlag, write, initial, read, hflag]

end IntelGpu
