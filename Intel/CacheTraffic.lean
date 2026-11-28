-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.CacheCoherence

@[expose] public section

/-!
# Coherence traffic between two workgroup caches

`Intel.CacheCoherence` models one write-through workgroup cache and explicitly
leaves coherence traffic out. This module adds the smallest traffic mechanism:
two workgroup caches over one shared global `VisState`, and a synchronous
broadcast invalidation sent by the producer's write to the consumer's cache.

`TwoCache` has a producer cache and a consumer cache, each with one `CacheLine`
per word address. `producerStore` is write-through and no-write-allocate. After
that store, `broadcastInvalidate` drops the consumer's line at the written
address, and `writeThroughBroadcast` combines the two steps.

Proved here, not assumed:

- `twoCacheCoherent_initial`, `twoCacheCoherent_invalidateOther` and
  `twoCacheCoherent_writeThroughBroadcast`: the two-cache invariant is
  preserved, including every valid line in either cache equaling the visible
  global value;
- `producer_write_broadcast_consumer_observes`: a consumer with a stale valid
  line observes the new value after the producer writes through and broadcasts
  the invalidation;
- `producer_write_without_broadcast_stale` and
  `producer_write_without_broadcast_not_fresh`: without the broadcast, the
  consumer's stale line remains observable;
- `producerPublishBroadcast_invalidates_both` and
  `producerPublishBroadcast_publishes_both`: data and flag lines are both
  invalidated, and both values are published in data-then-flag order;
- `producerPublishBroadcast_message_passing`: after that pair of invalidations,
  observing the published flag returns the published data;
- `producerPublishNoBroadcast_stale`: without the broadcasts, the consumer can
  observe the stale data line even after the producer publishes the flag.

Modeled assumptions:

- stores are write-through: the producer's global store is visible before the
  store returns, and the producer's local line is updated without allocation;
- stores do not write-allocate: `producerStore` leaves the valid bit alone;
- each cache has exactly one line per word location, represented by a function
  from addresses to `CacheLine`;
- broadcast invalidation is synchronous and per location: the consumer's copy
  is already invalid when `broadcastInvalidate` returns, with no latency,
  buffering, or lost-message case;
- there is no directory or ownership protocol; the producer's write is the
  trigger for the invalidation, and no sharer or dirty-owner state is tracked;
- there are no relaxed atomics: stores are ordered by construction, so the
  data write and invalidation precede the flag write and invalidation;
- global memory keeps the per-location log and visible prefix of
  `Intel.MemoryVisibility`, and the invariant records that the log is settled.

Not modelled: write-back dirty lines, write-allocate, multiple cache levels,
per-lane private caches, partial visibility, byte addressing, directory or
ownership protocols, invalidation latency, relaxed atomics, or SLM. This is a
proof of the coherence-traffic pattern under these assumptions, not a
hardware-conformance claim.
-/

namespace IntelGpu

/-- An invalid cache line. Its data word is dead and must not be returned. -/
def invalidLine : CacheLine := { data := 0, valid := false }

/-- Two workgroup caches in front of one shared global memory. -/
structure TwoCache where
  /-- Shared global memory and its per-location visibility history. -/
  global : VisState
  /-- The producer workgroup's cache, one line per word address. -/
  producer : Nat → CacheLine
  /-- The consumer workgroup's cache, one line per word address. -/
  consumer : Nat → CacheLine

/-- Two caches with all lines invalid. -/
def twoCacheInitial (init : Nat → Word) : TwoCache where
  global := initial init
  producer := fun _ => invalidLine
  consumer := fun _ => invalidLine

/-- A consumer cache with a valid line at `a` holding the initial value. -/
def initialWithConsumerCached (init : Nat → Word) (a : Nat) : TwoCache where
  global := initial init
  producer := fun _ => invalidLine
  consumer := fun i =>
    if i = a then { data := init a, valid := true } else invalidLine

/-- A load from the producer cache: a hit returns the line, a miss reads global
memory. Loads do not fill here because the traffic theorems only need hits and
invalidated misses. -/
def producerLoad (s : TwoCache) (a : Nat) : Word :=
  if (s.producer a).valid then (s.producer a).data else read s.global a

/-- A load from the consumer cache: a hit returns the line, a miss reads global
memory. -/
def consumerLoad (s : TwoCache) (a : Nat) : Word :=
  if (s.consumer a).valid then (s.consumer a).data else read s.global a

/-- A write-through, no-write-allocate store in the producer's cache. The store
publishes the value to global memory and updates the producer's data field,
leaving its valid bit unchanged. The consumer's cache is untouched. -/
def producerStore (s : TwoCache) (a : Nat) (v : Word) : TwoCache where
  global := writeThroughGlobal s.global a v
  producer := fun i =>
    if i = a then { data := v, valid := (s.producer a).valid } else s.producer i
  consumer := s.consumer

/-- Drop the consumer's copy of one written location. This is the coherence
message that the producer sends to the other workgroup. -/
def invalidateOther (s : TwoCache) (a : Nat) : TwoCache where
  global := s.global
  producer := s.producer
  consumer := fun i => if i = a then invalidLine else s.consumer i

/-- Broadcast invalidation of one written location to the other workgroup. -/
def broadcastInvalidate (s : TwoCache) (a : Nat) : TwoCache :=
  invalidateOther s a

/-- A producer write-through followed by its synchronous broadcast invalidation. -/
def writeThroughBroadcast (s : TwoCache) (a : Nat) (v : Word) : TwoCache :=
  broadcastInvalidate (producerStore s a v) a

/-- A global read at a write-through store address returns the stored value. -/
@[simp] theorem read_writeThroughGlobal_same (s : VisState) (a : Nat) (v : Word) :
    read (writeThroughGlobal s a v) a = v := by
  simp [writeThroughGlobal, read]

/-- A write-through store leaves global reads at other addresses unchanged. -/
@[simp] theorem read_writeThroughGlobal_other (s : VisState) (a b : Nat) (v : Word)
    (h : a ≠ b) : read (writeThroughGlobal s a v) b = read s b := by
  simp [writeThroughGlobal, read, h.symm]

/-- Both caches are coherent with the same shared global memory. -/
structure TwoCacheCoherent (s : TwoCache) : Prop where
  /-- Global memory satisfies per-location coherence. -/
  global : Coherent s.global
  /-- The global log is fully published. -/
  settled : GlobalSettled s.global
  /-- Every valid producer line holds the visible global value. -/
  producerLine : ∀ a, (s.producer a).valid = true →
    (s.producer a).data = read s.global a
  /-- Every valid consumer line holds the visible global value. -/
  consumerLine : ∀ a, (s.consumer a).valid = true →
    (s.consumer a).data = read s.global a

theorem twoCacheCoherent_initial (init : Nat → Word) :
    TwoCacheCoherent (twoCacheInitial init) := by
  refine ⟨coherent_initial init, globalSettled_initial init, ?_, ?_⟩
  · intro a h
    simp [twoCacheInitial, invalidLine] at h
  · intro a h
    simp [twoCacheInitial, invalidLine] at h

/-- Invalidation of the other cache preserves two-cache coherence. -/
theorem twoCacheCoherent_invalidateOther (s : TwoCache) (hs : TwoCacheCoherent s)
    (a : Nat) : TwoCacheCoherent (invalidateOther s a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [invalidateOther] using hs.global
  · simpa [invalidateOther] using hs.settled
  · intro b hb
    have hval : (s.producer b).valid = true := by
      simpa [invalidateOther] using hb
    simpa [invalidateOther] using hs.producerLine b hval
  · intro b hb
    by_cases hba : b = a
    · subst b
      simp [invalidateOther, invalidLine] at hb
    · have hval : (s.consumer b).valid = true := by
        simpa [invalidateOther, hba] using hb
      have hdata : ((invalidateOther s a).consumer b).data = (s.consumer b).data := by
        simp [invalidateOther, hba]
      have hglobal : read (invalidateOther s a).global b = read s.global b := by
        simp [invalidateOther]
      rw [hdata, hglobal]
      exact hs.consumerLine b hval

/-- A broadcast invalidation preserves the two-cache invariant. -/
theorem twoCacheCoherent_broadcastInvalidate (s : TwoCache) (hs : TwoCacheCoherent s)
    (a : Nat) : TwoCacheCoherent (broadcastInvalidate s a) := by
  simpa [broadcastInvalidate] using twoCacheCoherent_invalidateOther s hs a

/-- A write-through broadcast preserves the two-cache invariant: every valid line
in either cache still equals the visible global value. -/
theorem twoCacheCoherent_writeThroughBroadcast (s : TwoCache) (hs : TwoCacheCoherent s)
    (a : Nat) (v : Word) : TwoCacheCoherent (writeThroughBroadcast s a v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [writeThroughBroadcast, broadcastInvalidate, invalidateOther, producerStore]
      using coherent_writeThroughGlobal s.global hs.global a v
  · simpa [writeThroughBroadcast, broadcastInvalidate, invalidateOther, producerStore]
      using globalSettled_writeThroughGlobal s.global hs.settled a v
  · intro b hb
    by_cases hba : b = a
    · subst b
      have hdata : ((writeThroughBroadcast s a v).producer a).data = v := by
        simp [writeThroughBroadcast, broadcastInvalidate, invalidateOther, producerStore]
      have hread : read (writeThroughBroadcast s a v).global a = v := by
        simp [writeThroughBroadcast, broadcastInvalidate, invalidateOther, producerStore,
          writeThroughGlobal, read]
      rw [hdata, hread]
    · have hval : (s.producer b).valid = true := by
        simpa [writeThroughBroadcast, broadcastInvalidate, invalidateOther, producerStore,
          hba] using hb
      have hdata : ((writeThroughBroadcast s a v).producer b).data = (s.producer b).data := by
        simp [writeThroughBroadcast, broadcastInvalidate, invalidateOther, producerStore, hba]
      have hread : read (writeThroughBroadcast s a v).global b = read s.global b := by
        simp [writeThroughBroadcast, broadcastInvalidate, invalidateOther, producerStore,
          read_writeThroughGlobal_other s.global a b v (fun h => hba h.symm)]
      rw [hdata, hread]
      exact hs.producerLine b hval
  · intro b hb
    by_cases hba : b = a
    · subst b
      simp [writeThroughBroadcast, broadcastInvalidate, invalidateOther, producerStore,
        invalidLine] at hb
    · have hval : (s.consumer b).valid = true := by
        simpa [writeThroughBroadcast, broadcastInvalidate, invalidateOther, producerStore,
          hba] using hb
      have hdata : ((writeThroughBroadcast s a v).consumer b).data = (s.consumer b).data := by
        simp [writeThroughBroadcast, broadcastInvalidate, invalidateOther, producerStore, hba]
      have hread : read (writeThroughBroadcast s a v).global b = read s.global b := by
        simp [writeThroughBroadcast, broadcastInvalidate, invalidateOther, producerStore,
          read_writeThroughGlobal_other s.global a b v (fun h => hba h.symm)]
      rw [hdata, hread]
      exact hs.consumerLine b hval

/-- After a broadcast invalidation, a consumer load at that address reads the
visible global value. -/
@[simp] theorem consumerLoad_broadcastInvalidate_same (s : TwoCache) (a : Nat) :
    consumerLoad (broadcastInvalidate s a) a = read s.global a := by
  simp [consumerLoad, broadcastInvalidate, invalidateOther, invalidLine]

/-- A producer write-through plus broadcast is read back by the consumer at the
written address. -/
@[simp] theorem consumerLoad_writeThroughBroadcast_same (s : TwoCache) (a : Nat)
    (v : Word) : consumerLoad (writeThroughBroadcast s a v) a = v := by
  simp [writeThroughBroadcast, consumerLoad, broadcastInvalidate, invalidateOther,
    invalidLine, producerStore, writeThroughGlobal, read]

/-- Without a broadcast, a consumer's valid stale line hides the producer's new
global value. -/
@[simp] theorem consumerLoad_producerStore_self_cached (init : Nat → Word) (a : Nat)
    (v : Word) :
    consumerLoad (producerStore (initialWithConsumerCached init a) a v) a = init a := by
  simp [consumerLoad, producerStore, initialWithConsumerCached]

/-- The core positive result: a producer writes through and broadcasts the
invalidation, so a consumer that had the old line cached observes the new value. -/
theorem producer_write_broadcast_consumer_observes (init : Nat → Word) (a : Nat)
    (v : Word) :
    consumerLoad (writeThroughBroadcast (initialWithConsumerCached init a) a v) a = v := by
  exact consumerLoad_writeThroughBroadcast_same (initialWithConsumerCached init a) a v

/-- The core negative result: without the broadcast, the stale cached line is
observable even though global memory already holds the new value. -/
theorem producer_write_without_broadcast_stale (init : Nat → Word) (a : Nat)
    (v : Word) :
    consumerLoad (producerStore (initialWithConsumerCached init a) a v) a = init a :=
  consumerLoad_producerStore_self_cached init a v

/-- If the stale value differs from the new value, the uninvalidated consumer does
not observe the new value. -/
theorem producer_write_without_broadcast_not_fresh (init : Nat → Word) (a : Nat)
    (v : Word) (hfresh : v ≠ init a) :
    consumerLoad (producerStore (initialWithConsumerCached init a) a v) a ≠ v := by
  rw [producer_write_without_broadcast_stale]
  exact fun h => hfresh h.symm

/-- With the broadcast, a consumer that had a stale value does not observe that
stale value after the write. -/
theorem producer_write_broadcast_not_stale (init : Nat → Word) (a : Nat) (v : Word)
    (hfresh : v ≠ init a) :
    consumerLoad (writeThroughBroadcast (initialWithConsumerCached init a) a v) a ≠
      init a := by
  rw [producer_write_broadcast_consumer_observes]
  exact hfresh

/-- Producer writes data and broadcasts its invalidation, then writes the flag and
broadcasts its invalidation. The order is explicit in the composition. -/
def producerPublishBroadcast (s : TwoCache) (dataAddr flagAddr : Nat) (data : Word) :
    TwoCache :=
  writeThroughBroadcast (writeThroughBroadcast s dataAddr data) flagAddr flagTrue

/-- Producer writes data and the flag without any coherence traffic. -/
def producerPublishNoBroadcast (s : TwoCache) (dataAddr flagAddr : Nat) (data : Word) :
    TwoCache :=
  producerStore (producerStore s dataAddr data) flagAddr flagTrue

/-- The consumer reads the flag first, and the data only if the flag is true. -/
def consumerObserveAfterFlag (s : TwoCache) (dataAddr flagAddr : Nat) : Option Word :=
  if consumerLoad s flagAddr = flagTrue then some (consumerLoad s dataAddr) else none

/-- Both the data line and the flag line are invalidated in the consumer cache. -/
theorem producerPublishBroadcast_invalidates_both (s : TwoCache) (dataAddr flagAddr : Nat)
    (data : Word) (hne : dataAddr ≠ flagAddr) :
    ((producerPublishBroadcast s dataAddr flagAddr data).consumer dataAddr).valid = false ∧
    ((producerPublishBroadcast s dataAddr flagAddr data).consumer flagAddr).valid = false := by
  simp [producerPublishBroadcast, writeThroughBroadcast, broadcastInvalidate,
    invalidateOther, invalidLine, producerStore, hne, Ne.symm hne]

/-- Both the data and the flag are visible in global memory after the ordered
write-through sequence. -/
theorem producerPublishBroadcast_publishes_both (s : TwoCache) (dataAddr flagAddr : Nat)
    (data : Word) (hne : dataAddr ≠ flagAddr) :
    read (producerPublishBroadcast s dataAddr flagAddr data).global dataAddr = data ∧
    read (producerPublishBroadcast s dataAddr flagAddr data).global flagAddr = flagTrue := by
  constructor
  · simp [producerPublishBroadcast, writeThroughBroadcast, broadcastInvalidate,
      invalidateOther, producerStore, writeThroughGlobal, read, hne]
  · simp [producerPublishBroadcast, writeThroughBroadcast, broadcastInvalidate,
      invalidateOther, producerStore, writeThroughGlobal, read, flagTrue]

/-- After the ordered publish, the consumer's flag load reads the new flag. -/
theorem consumerLoad_producerPublishBroadcast_flag (s : TwoCache) (dataAddr flagAddr : Nat)
    (data : Word) :
    consumerLoad (producerPublishBroadcast s dataAddr flagAddr data) flagAddr = flagTrue := by
  simp [consumerLoad, producerPublishBroadcast, writeThroughBroadcast,
    broadcastInvalidate, invalidateOther, invalidLine, producerStore, writeThroughGlobal,
    read, flagTrue]

/-- After the ordered publish, the consumer's data load reads the new data. -/
theorem consumerLoad_producerPublishBroadcast_data (s : TwoCache) (dataAddr flagAddr : Nat)
    (data : Word) (hne : dataAddr ≠ flagAddr) :
    consumerLoad (producerPublishBroadcast s dataAddr flagAddr data) dataAddr = data := by
  simp [consumerLoad, producerPublishBroadcast, writeThroughBroadcast,
    broadcastInvalidate, invalidateOther, invalidLine, producerStore, writeThroughGlobal,
    read, hne, Ne.symm hne]

/-- Message passing with coherence traffic: after both broadcast invalidations,
observing the published flag returns the published data. -/
theorem producerPublishBroadcast_message_passing (init : Nat → Word) (dataAddr flagAddr : Nat)
    (data : Word) (hne : dataAddr ≠ flagAddr) :
    consumerObserveAfterFlag
        (producerPublishBroadcast (initialWithConsumerCached init dataAddr)
          dataAddr flagAddr data) dataAddr flagAddr = some data := by
  have hflag := consumerLoad_producerPublishBroadcast_flag
    (initialWithConsumerCached init dataAddr) dataAddr flagAddr data
  have hdata := consumerLoad_producerPublishBroadcast_data
    (initialWithConsumerCached init dataAddr) dataAddr flagAddr data hne
  simp [consumerObserveAfterFlag, hflag, hdata]

/-- Negative message-passing result: without broadcasts, the consumer's stale data
line is observable after the producer publishes the flag. -/
theorem producerPublishNoBroadcast_stale (init : Nat → Word) (dataAddr flagAddr : Nat)
    (data : Word) (hne : dataAddr ≠ flagAddr) :
    consumerObserveAfterFlag
        (producerPublishNoBroadcast (initialWithConsumerCached init dataAddr)
          dataAddr flagAddr data) dataAddr flagAddr = some (init dataAddr) := by
  have hflag : consumerLoad
      (producerPublishNoBroadcast (initialWithConsumerCached init dataAddr)
        dataAddr flagAddr data) flagAddr = flagTrue := by
    simp [consumerLoad, producerPublishNoBroadcast, producerStore,
      initialWithConsumerCached, invalidLine, writeThroughGlobal, read, flagTrue,
      Ne.symm hne]
  have hdata : consumerLoad
      (producerPublishNoBroadcast (initialWithConsumerCached init dataAddr)
        dataAddr flagAddr data) dataAddr = init dataAddr := by
    simp [consumerLoad, producerPublishNoBroadcast, producerStore,
      initialWithConsumerCached]
  simp [consumerObserveAfterFlag, hflag, hdata]

/-- If the stale data differs from the published data, the no-traffic consumer does
not observe the fresh data even though it observes the new flag. -/
theorem producerPublishNoBroadcast_not_fresh (init : Nat → Word) (dataAddr flagAddr : Nat)
    (data : Word) (hne : dataAddr ≠ flagAddr) (hstale : init dataAddr ≠ data) :
    consumerObserveAfterFlag
        (producerPublishNoBroadcast (initialWithConsumerCached init dataAddr)
          dataAddr flagAddr data) dataAddr flagAddr ≠ some data := by
  rw [producerPublishNoBroadcast_stale init dataAddr flagAddr data hne]
  simp [hstale]

end IntelGpu
