-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.MemoryVisibility

@[expose] public section

/-!
# Relaxed atomics and store-buffer ordering

`Intel.MemoryVisibility` models release and acquire with a per-location store
log but has no notion of a memory order attached to an individual access:
every store happens on the releasing thread's schedule. This module adds the
missing distinction between relaxed and ordered accesses.

`MemOrd` is the memory-order mode of one access: `relaxed`, `release`,
`acquire`, `acqRel` or `seqCst`.

`SBState` is a cacheless global memory with a per-location store buffer. Each
location has an initial `base` value, a FIFO `pending` queue of stores issued
but not yet globally visible, and a FIFO `published` log of stores that are
globally visible. `sbStore` appends a relaxed store to `pending`, `publishAt`
drains one location's pending queue into its published log, `sbReleaseFence`
drains every location, and `sbAcquireFence` is the identity because there is
no cache to invalidate. `sbRead` returns the last published value, or the base
value if nothing has been published.

The mode dispatch `sbStoreWith` gives the modeled semantics:

- `relaxed` appends to the pending queue;
- `release` appends and then drains the whole buffer (a release store plus a
  full release barrier);
- `acquire` appends like a relaxed store; the acquire half only orders later
  loads, which is the identity in this cacheless model;
- `acqRel` is the release case, since its acquire half is again identity;
- `seqCst` appends and immediately publishes that location, modeling a
  sequentially consistent store as visible at issue.

Proved here, not assumed:

- `later_store_observed_earlier_pending`: an earlier relaxed store can remain
  pending while a later relaxed store at another location is observed;
- `relaxed_message_passing_stale`, `relaxed_observe_stale` and
  `relaxed_stale_outcome`: the relaxed message-passing counterexample is an
  explicit `SBState` execution in which the consumer reads `flag = true` and
  the stale pre-publication data value;
- `releaseAcquire_message_passing` and `releaseAcquire_no_stale`: release on
  both producer stores and an acquire load of the flag return the published
  data, never the stale value;
- `releaseAcquire_outcome_iff`: every execution of the release/acquire
  program, after any further per-location drains, has exactly the outcome
  `some data`;
- `seqCstProgram_eq_releaseAcquireProgram`: the exact strengthening relation,
  the final store-buffer state of the seq_cst program equals that of the
  release/acquire program; consequently `seqCst_message_passing`,
  `seqCst_outcome_iff` and `seqCst_outcomes_subset_releaseAcquire` hold;
- `publishAt_published_pending`, `sbRead_publishAt_of_pending`,
  `sbReleaseFence_published` and `sbRead_sbReleaseFence`: draining publishes
  the pending stores in FIFO order and exposes the newest one;
- `publishAt_comm`, `sbReleaseFence_publishAt` and `sbReleaseFence_idem`: a
  fence orders and absorbs per-location drains;
- `published_mono_publishAt`, `pending_length_publishAt_le`,
  `published_length_publishAt_ge`, `allStores_publishAt` and
  `allStores_sbReleaseFence`: visibility is monotone, the per-location history
  is preserved, and a drain neither reorders nor drops stores;
- `drains_drained_eq`: once a state is fully drained, no further drain
  changes it.

Modeled assumptions:

- per-location order: each location has one FIFO pending queue and one FIFO
  published log; stores at a location are ordered by issue order, and
  `allStores` is never reordered or dropped;
- no caches: global memory is the published log, and an acquire is the
  identity; the `Drains` relation is the cacheless drain model;
- no store-to-load forwarding: a thread does not read its own pending stores;
  a pending store is invisible until published, which is why the counterexample
  uses a separate consumer observation;
- fences are full barriers: `sbReleaseFence` drains every location, and
  `publishAt` is the per-location drain step;
- `seqCst` is immediate per-location publication; no global total order across
  locations beyond the publication order is modeled, but for this
  message-passing program the final state agrees with release/acquire;
- no weak atomics beyond the five `MemOrd` modes: all other accesses are
  modeled as plain accesses with no ordering;
- no partial granularity: word-addressed locations, no byte addressing, no
  SLM, and no partial cache-line visibility.

Not modelled: caches, coherence traffic, request queues, write-back lines,
hardware address aliasing, and a full axiomatic memory model. The theorems are
proofs of the ordering patterns under these assumptions, not hardware
conformance claims.
-/

namespace IntelGpu

/-- The memory-order mode of one access or fence. -/
inductive MemOrd where
  /-- No ordering constraints: the store can stay pending. -/
  | relaxed
  /-- Release ordering: prior stores are drained before the store is visible. -/
  | release
  /-- Acquire ordering: later loads observe the released state. -/
  | acquire
  /-- Both release and acquire ordering. -/
  | acqRel
  /-- Sequentially consistent ordering, modeled as immediate publication. -/
  | seqCst
  deriving DecidableEq, Repr

/-- A cacheless global memory with a per-location store buffer.

`base` is the initial value, `pending` the FIFO queue of issued but not yet
globally visible stores, and `published` the FIFO log of globally visible
stores. A read sees the last published value, falling back to `base`. -/
structure SBState where
  /-- The initial value used before anything is published. -/
  base : Nat → Word
  /-- Stores at each location that are globally visible, oldest first. -/
  published : Nat → List Word
  /-- Stores at each location that are pending, oldest first. -/
  pending : Nat → List Word

/-- The initial state: only each location's base value exists. -/
def sbInitial (init : Nat → Word) : SBState where
  base := init
  published := fun _ => []
  pending := fun _ => []

/-- A read observes the last published store, or the base value. -/
def sbRead (s : SBState) (a : Nat) : Word :=
  lastOr (s.published a) (s.base a)

/-- The full per-location history: published prefix followed by pending suffix. -/
def allStores (s : SBState) (a : Nat) : List Word :=
  s.published a ++ s.pending a

/-- A relaxed store: append to the pending queue without publishing. -/
def sbStore (s : SBState) (a : Nat) (v : Word) : SBState where
  base := s.base
  published := s.published
  pending := fun i => if i = a then s.pending i ++ [v] else s.pending i

/-- Drain one location's pending queue into its published log, FIFO order. -/
def publishAt (s : SBState) (a : Nat) : SBState where
  base := s.base
  published := fun i => if i = a then s.published i ++ s.pending i else s.published i
  pending := fun i => if i = a then [] else s.pending i

/-- A release fence: drain every location's pending queue. -/
def sbReleaseFence (s : SBState) : SBState where
  base := s.base
  published := fun a => s.published a ++ s.pending a
  pending := fun _ => []

/-- An acquire fence: identity, because the model has no caches to invalidate. -/
def sbAcquireFence (s : SBState) : SBState := s

/-- An acquire load: acquire fence followed by a read. -/
def sbAcquireRead (s : SBState) (a : Nat) : Word :=
  sbRead (sbAcquireFence s) a

/-- Read the flag, then read the data only when the flag is set. -/
def sbObserveAfterFlag (s : SBState) (dataAddr flagAddr : Nat) : Option Word :=
  if sbRead s flagAddr = flagTrue then some (sbRead s dataAddr) else none

/-- The same observation using acquire loads for both reads. -/
def sbObserveAfterAcquireFlag (s : SBState) (dataAddr flagAddr : Nat) : Option Word :=
  if sbAcquireRead s flagAddr = flagTrue then some (sbAcquireRead s dataAddr) else none

/-- Every pending store has been published. -/
def Drained (s : SBState) : Prop := ∀ a, s.pending a = []

/-- Issue a store with the given memory-order mode. -/
def sbStoreWith (s : SBState) : MemOrd → Nat → Word → SBState
  | .relaxed, a, v => sbStore s a v
  | .release, a, v => sbReleaseFence (sbStore s a v)
  | .acquire, a, v => sbStore s a v
  | .acqRel, a, v => sbReleaseFence (sbStore s a v)
  | .seqCst, a, v => publishAt (sbStore s a v) a

theorem lastOr_cons (x : Word) (xs : List Word) (v : Word) :
    lastOr (x :: xs) v = lastOr xs x := by
  simp [lastOr, List.getLast?_cons]

theorem lastOr_append (xs ys : List Word) (v : Word) :
    lastOr (xs ++ ys) v = lastOr ys (lastOr xs v) := by
  simp only [lastOr, List.getLast?_append]
  cases ys <;> simp

theorem lastOr_eq_getLast (xs : List Word) (h : xs ≠ []) (v : Word) :
    lastOr xs v = xs.getLast h := by
  simp [lastOr, List.getLast?_eq_some_getLast h]

theorem sbState_ext {s t : SBState} (hbase : s.base = t.base)
    (hpub : s.published = t.published) (hpend : s.pending = t.pending) :
    s = t := by
  rcases s with ⟨b, p, q⟩
  rcases t with ⟨b', p', q'⟩
  simp_all

@[simp] theorem sbRead_initial (init : Nat → Word) (a : Nat) :
    sbRead (sbInitial init) a = init a := by
  simp [sbRead, sbInitial, lastOr]

@[simp] theorem sbRead_sbStore (s : SBState) (a : Nat) (v : Word) (b : Nat) :
    sbRead (sbStore s a v) b = sbRead s b := by
  simp [sbRead, sbStore]

@[simp] theorem sbStore_pending_same (s : SBState) (a : Nat) (v : Word) :
    (sbStore s a v).pending a = s.pending a ++ [v] := by
  simp [sbStore]

@[simp] theorem sbStore_pending_other (s : SBState) (a : Nat) (v : Word) (b : Nat)
    (h : b ≠ a) : (sbStore s a v).pending b = s.pending b := by
  simp [sbStore, h]

@[simp] theorem publishAt_published_same (s : SBState) (a : Nat) :
    (publishAt s a).published a = s.published a ++ s.pending a := by
  simp [publishAt]

@[simp] theorem publishAt_published_other (s : SBState) (a b : Nat) (h : b ≠ a) :
    (publishAt s a).published b = s.published b := by
  simp [publishAt, h]

@[simp] theorem publishAt_pending_same (s : SBState) (a : Nat) :
    (publishAt s a).pending a = [] := by
  simp [publishAt]

@[simp] theorem publishAt_pending_other (s : SBState) (a b : Nat) (h : b ≠ a) :
    (publishAt s a).pending b = s.pending b := by
  simp [publishAt, h]

theorem sbRead_publishAt (s : SBState) (a : Nat) :
    sbRead (publishAt s a) a = lastOr (s.pending a) (sbRead s a) := by
  simp [sbRead, publishAt, lastOr_append]

/-- Draining a nonempty pending queue exposes its newest store. -/
theorem sbRead_publishAt_of_pending (s : SBState) (a : Nat)
    (h : s.pending a ≠ []) :
    sbRead (publishAt s a) a = (s.pending a).getLast h := by
  rw [sbRead_publishAt, lastOr_eq_getLast]

theorem sbRead_publishAt_other (s : SBState) (a b : Nat) (h : b ≠ a) :
    sbRead (publishAt s a) b = sbRead s b := by
  simp [sbRead, publishAt, h]

theorem publishAt_published_pending (s : SBState) (a : Nat) :
    (publishAt s a).published a = allStores s a := by
  simp [publishAt, allStores]

theorem allStores_sbStore_same (s : SBState) (a : Nat) (v : Word) :
    allStores (sbStore s a v) a = allStores s a ++ [v] := by
  simp [allStores, sbStore, List.append_assoc]

theorem allStores_sbStore_other (s : SBState) (a b : Nat) (v : Word) (h : b ≠ a) :
    allStores (sbStore s a v) b = allStores s b := by
  simp [allStores, sbStore, h]

theorem allStores_publishAt (s : SBState) (a b : Nat) :
    allStores (publishAt s a) b = allStores s b := by
  by_cases hb : b = a
  · subst b
    simp [allStores, publishAt]
  · simp [allStores, publishAt, hb]

theorem allStores_sbReleaseFence (s : SBState) (a : Nat) :
    allStores (sbReleaseFence s) a = allStores s a := by
  simp [allStores, sbReleaseFence]

/-- Visibility is monotone: publishing only extends the published prefix. -/
theorem published_mono_publishAt (s : SBState) (a b : Nat) :
    ∃ t : List Word, (publishAt s a).published b = s.published b ++ t := by
  by_cases hb : b = a
  · subst b
    exact ⟨s.pending a, by simp [publishAt]⟩
  · exact ⟨[], by simp [publishAt, hb]⟩

theorem pending_length_publishAt_le (s : SBState) (a b : Nat) :
    ((publishAt s a).pending b).length ≤ (s.pending b).length := by
  by_cases hb : b = a
  · subst b
    simp [publishAt]
  · simp [publishAt, hb]

theorem published_length_publishAt_ge (s : SBState) (a b : Nat) :
    (s.published b).length ≤ ((publishAt s a).published b).length := by
  by_cases hb : b = a
  · subst b
    simp [publishAt]
  · simp [publishAt, hb]

theorem publishAt_idem (s : SBState) (a : Nat) :
    publishAt (publishAt s a) a = publishAt s a := by
  rcases s with ⟨b, pub, pend⟩
  simp only [publishAt]
  refine sbState_ext rfl ?_ ?_ <;> funext i
  · by_cases hi : i = a <;> simp [hi]
  · by_cases hi : i = a <;> simp [hi]

/-- Draining two locations commutes, so a fence is order-independent. -/
theorem publishAt_comm (s : SBState) {a b : Nat} (h : a ≠ b) :
    publishAt (publishAt s a) b = publishAt (publishAt s b) a := by
  rcases s with ⟨base, pub, pend⟩
  simp only [publishAt]
  refine sbState_ext rfl ?_ ?_ <;> funext i
  · by_cases hia : i = a <;> by_cases hib : i = b <;> simp_all
  · by_cases hia : i = a <;> by_cases hib : i = b <;> simp_all

/-- A release fence publishes the whole per-location history, in order. -/
@[simp] theorem sbReleaseFence_published (s : SBState) (a : Nat) :
    (sbReleaseFence s).published a = allStores s a := by
  simp [sbReleaseFence, allStores]

@[simp] theorem sbReleaseFence_pending (s : SBState) (a : Nat) :
    (sbReleaseFence s).pending a = [] := by
  simp [sbReleaseFence]

theorem sbRead_sbReleaseFence (s : SBState) (a : Nat) :
    sbRead (sbReleaseFence s) a = lastOr (s.pending a) (sbRead s a) := by
  simp [sbRead, sbReleaseFence, lastOr_append]

theorem sbReleaseFence_drained (s : SBState) : Drained (sbReleaseFence s) := by
  intro a
  simp [sbReleaseFence]

theorem sbInitial_drained (init : Nat → Word) : Drained (sbInitial init) := by
  intro a
  simp [sbInitial]

theorem sbReleaseFence_idem (s : SBState) :
    sbReleaseFence (sbReleaseFence s) = sbReleaseFence s := by
  rcases s with ⟨b, pub, pend⟩
  simp only [sbReleaseFence]
  refine sbState_ext rfl ?_ ?_ <;> funext i
  · simp
  · simp

theorem sbReleaseFence_publishAt (s : SBState) (a : Nat) :
    sbReleaseFence (publishAt s a) = sbReleaseFence s := by
  rcases s with ⟨b, pub, pend⟩
  simp only [publishAt, sbReleaseFence]
  refine sbState_ext rfl ?_ ?_ <;> funext i
  · by_cases hi : i = a <;> simp [hi]
  · by_cases hi : i = a <;> simp

theorem drained_publishAt {s : SBState} (h : Drained s) (a : Nat) :
    publishAt s a = s := by
  rcases s with ⟨b, pub, pend⟩
  simp only [Drained] at h
  simp only [publishAt]
  refine sbState_ext rfl ?_ ?_ <;> funext i
  · by_cases hi : i = a
    · subst i
      simp [h a]
    · simp [hi]
  · by_cases hi : i = a
    · subst i
      simp [h a]
    · simp [hi]

/-- A state reachable by any sequence of per-location drains, including none. -/
inductive Drains : SBState → SBState → Prop where
  | refl (s : SBState) : Drains s s
  | publish {s t : SBState} (h : Drains s t) (a : Nat) : Drains s (publishAt t a)

/-- Further drains cannot change a fully drained state. -/
theorem drains_drained_eq {s t : SBState} (hs : Drained s) (h : Drains s t) :
    t = s := by
  induction h with
  | refl => rfl
  | publish hd a ih =>
      rw [ih]
      exact drained_publishAt hs a

/-- Both producer stores are relaxed: data first, then the flag. -/
def relaxedProgram (init : Nat → Word) (dataAddr flagAddr : Nat) (data : Word) : SBState :=
  sbStore (sbStore (sbInitial init) dataAddr data) flagAddr flagTrue

/-- The relaxed execution that publishes only the flag location. -/
def relaxedFlagPublished (init : Nat → Word) (dataAddr flagAddr : Nat)
    (data : Word) : SBState :=
  publishAt (relaxedProgram init dataAddr flagAddr data) flagAddr

/-- In the relaxed program the data store is still in the pending queue. -/
theorem relaxed_data_pending (init : Nat → Word) (dataAddr flagAddr : Nat)
    (data : Word) (hne : dataAddr ≠ flagAddr) :
    (relaxedProgram init dataAddr flagAddr data).pending dataAddr = [data] := by
  simp [relaxedProgram, sbStore, sbInitial, hne]

/-- Explicit relaxed message-passing counterexample: a true flag is visible
while the data location still reads its base value. -/
theorem relaxed_message_passing_stale (init : Nat → Word) (dataAddr flagAddr : Nat)
    (data : Word) (hne : dataAddr ≠ flagAddr) :
    sbRead (relaxedFlagPublished init dataAddr flagAddr data) flagAddr = flagTrue ∧
      sbRead (relaxedFlagPublished init dataAddr flagAddr data) dataAddr = init dataAddr ∧
      (relaxedFlagPublished init dataAddr flagAddr data).pending dataAddr = [data] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [relaxedFlagPublished, relaxedProgram, publishAt, sbStore, sbRead, sbInitial,
      lastOr]
  · simp [relaxedFlagPublished, relaxedProgram, publishAt, sbStore, sbRead, sbInitial,
      lastOr, hne]
  · simp [relaxedFlagPublished, relaxedProgram, publishAt, sbStore, sbInitial, hne]

/-- The relaxed consumer observes the stale data value after a true flag. -/
theorem relaxed_observe_stale (init : Nat → Word) (dataAddr flagAddr : Nat)
    (data : Word) (hne : dataAddr ≠ flagAddr) :
    sbObserveAfterFlag (relaxedFlagPublished init dataAddr flagAddr data)
        dataAddr flagAddr = some (init dataAddr) := by
  have h := relaxed_message_passing_stale init dataAddr flagAddr data hne
  simp [sbObserveAfterFlag, h.1, h.2.1]

/-- A later relaxed store to `b` can be observed while the earlier relaxed
store to `a` is still pending. -/
theorem later_store_observed_earlier_pending (s : SBState) {a b : Nat} (h : a ≠ b)
    (v w : Word) :
    sbRead (publishAt (sbStore (sbStore s a v) b w) b) b = w ∧
      (publishAt (sbStore (sbStore s a v) b w) b).pending a = s.pending a ++ [v] := by
  constructor
  · rw [sbRead_publishAt]
    have hb : (sbStore (sbStore s a v) b w).pending b = s.pending b ++ [w] := by
      simp [sbStore, Ne.symm h]
    rw [hb]
    simp [lastOr, List.getLast?_append]
  · simp [sbStore, publishAt, h]

/-- Both producer stores are release-ordered, and the consumer loads acquire. -/
def releaseAcquireProgram (init : Nat → Word) (dataAddr flagAddr : Nat)
    (data : Word) : SBState :=
  sbAcquireFence
    (sbStoreWith (sbStoreWith (sbInitial init) .release dataAddr data)
      .release flagAddr flagTrue)

theorem releaseAcquire_drained (init : Nat → Word) (dataAddr flagAddr : Nat)
    (data : Word) : Drained (releaseAcquireProgram init dataAddr flagAddr data) := by
  intro a
  simp [releaseAcquireProgram, sbStoreWith, sbAcquireFence, sbReleaseFence]

/-- Release stores plus an acquire load make the consumer see the published
data after reading a true flag. -/
theorem releaseAcquire_message_passing (init : Nat → Word) (dataAddr flagAddr : Nat)
    (data : Word) (hne : dataAddr ≠ flagAddr) :
    sbObserveAfterAcquireFlag (releaseAcquireProgram init dataAddr flagAddr data)
        dataAddr flagAddr = some data := by
  simp [sbObserveAfterAcquireFlag, sbAcquireRead, releaseAcquireProgram, sbStoreWith,
    sbAcquireFence, sbReleaseFence, sbStore, sbRead, sbInitial, lastOr, hne]

/-- The release/acquire consumer never observes the stale data value. -/
theorem releaseAcquire_no_stale (init : Nat → Word) (dataAddr flagAddr : Nat)
    (data : Word) (hne : dataAddr ≠ flagAddr) (hstale : data ≠ init dataAddr) :
    sbObserveAfterAcquireFlag (releaseAcquireProgram init dataAddr flagAddr data)
        dataAddr flagAddr ≠ some (init dataAddr) := by
  rw [releaseAcquire_message_passing init dataAddr flagAddr data hne]
  simp [hstale]

/-- Both producer stores are seq_cst, so each is published at issue. -/
def seqCstProgram (init : Nat → Word) (dataAddr flagAddr : Nat) (data : Word) : SBState :=
  sbAcquireFence
    (sbStoreWith (sbStoreWith (sbInitial init) .seqCst dataAddr data)
      .seqCst flagAddr flagTrue)

/-- Exact seq_cst strengthening: the final seq_cst store-buffer state is the
release/acquire final state. -/
theorem seqCstProgram_eq_releaseAcquireProgram (init : Nat → Word)
    (dataAddr flagAddr : Nat) (data : Word) (hne : dataAddr ≠ flagAddr) :
    seqCstProgram init dataAddr flagAddr data =
      releaseAcquireProgram init dataAddr flagAddr data := by
  simp only [seqCstProgram, releaseAcquireProgram, sbStoreWith, sbAcquireFence,
    sbReleaseFence, publishAt, sbStore, sbInitial]
  refine sbState_ext rfl ?_ ?_ <;> funext i
  · by_cases hiData : i = dataAddr <;> by_cases hiFlag : i = flagAddr <;>
      simp_all
  · by_cases hiData : i = dataAddr <;> by_cases hiFlag : i = flagAddr <;>
      simp_all

theorem seqCst_drained (init : Nat → Word) (dataAddr flagAddr : Nat) (data : Word)
    (hne : dataAddr ≠ flagAddr) : Drained (seqCstProgram init dataAddr flagAddr data) := by
  rw [seqCstProgram_eq_releaseAcquireProgram init dataAddr flagAddr data hne]
  exact releaseAcquire_drained init dataAddr flagAddr data

/-- seq_cst also returns the published data after a true flag. -/
theorem seqCst_message_passing (init : Nat → Word) (dataAddr flagAddr : Nat)
    (data : Word) (hne : dataAddr ≠ flagAddr) :
    sbObserveAfterAcquireFlag (seqCstProgram init dataAddr flagAddr data)
        dataAddr flagAddr = some data := by
  rw [seqCstProgram_eq_releaseAcquireProgram init dataAddr flagAddr data hne]
  exact releaseAcquire_message_passing init dataAddr flagAddr data hne

/-- An outcome reachable from `s` by some sequence of per-location drains. -/
def sbPossibleOutcome (s : SBState) (dataAddr flagAddr : Nat) (o : Option Word) : Prop :=
  ∃ t : SBState, Drains s t ∧ sbObserveAfterAcquireFlag t dataAddr flagAddr = o

/-- The stale data value is a possible relaxed execution outcome. -/
theorem relaxed_stale_outcome (init : Nat → Word) (dataAddr flagAddr : Nat)
    (data : Word) (hne : dataAddr ≠ flagAddr) :
    sbPossibleOutcome (relaxedProgram init dataAddr flagAddr data) dataAddr flagAddr
      (some (init dataAddr)) := by
  refine ⟨relaxedFlagPublished init dataAddr flagAddr data, ?_, ?_⟩
  · exact Drains.publish (Drains.refl _) flagAddr
  · exact relaxed_observe_stale init dataAddr flagAddr data hne

/-- Every drain of the release/acquire program has exactly the fresh outcome. -/
theorem releaseAcquire_outcome_iff (init : Nat → Word) (dataAddr flagAddr : Nat)
    (data : Word) (hne : dataAddr ≠ flagAddr) (o : Option Word) :
    sbPossibleOutcome (releaseAcquireProgram init dataAddr flagAddr data) dataAddr flagAddr o ↔
      o = some data := by
  constructor
  · rintro ⟨t, hd, ho⟩
    have ht : t = releaseAcquireProgram init dataAddr flagAddr data :=
      drains_drained_eq (releaseAcquire_drained init dataAddr flagAddr data) hd
    subst t
    rw [releaseAcquire_message_passing init dataAddr flagAddr data hne] at ho
    exact ho.symm
  · intro ho
    subst o
    exact ⟨releaseAcquireProgram init dataAddr flagAddr data, Drains.refl _,
      releaseAcquire_message_passing init dataAddr flagAddr data hne⟩

/-- Every drain of the seq_cst program has exactly the fresh outcome. -/
theorem seqCst_outcome_iff (init : Nat → Word) (dataAddr flagAddr : Nat)
    (data : Word) (hne : dataAddr ≠ flagAddr) (o : Option Word) :
    sbPossibleOutcome (seqCstProgram init dataAddr flagAddr data) dataAddr flagAddr o ↔
      o = some data := by
  rw [seqCstProgram_eq_releaseAcquireProgram init dataAddr flagAddr data hne]
  exact releaseAcquire_outcome_iff init dataAddr flagAddr data hne o

/-- seq_cst outcomes are a subset of the release/acquire-visible outcomes. -/
theorem seqCst_outcomes_subset_releaseAcquire (init : Nat → Word)
    (dataAddr flagAddr : Nat) (data : Word) (hne : dataAddr ≠ flagAddr) :
    ∀ o : Option Word,
      sbPossibleOutcome (seqCstProgram init dataAddr flagAddr data) dataAddr flagAddr o →
        sbPossibleOutcome (releaseAcquireProgram init dataAddr flagAddr data)
          dataAddr flagAddr o := by
  rw [seqCstProgram_eq_releaseAcquireProgram init dataAddr flagAddr data hne]
  intro o ho
  exact ho

end IntelGpu
