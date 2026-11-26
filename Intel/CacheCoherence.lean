-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.MemoryVisibility

@[expose] public section

/-!
# A write-through cache model for global memory

`Intel.MemoryVisibility` models a cacheless global memory: a read always sees
the latest visible store. This module adds the smallest cache that explains
why an acquire fence is needed. It is not a model of the Xe cache hierarchy.

`CacheState` pairs the shared global `VisState` with one workgroup's cache:
each word address has a `CacheLine` containing a data word and a valid bit.
A `store` is write-through and does not allocate: it publishes the new value
to global memory, updates the data field of the line at that address, and
leaves the valid bit alone. A `load` returns the line when it is valid and
otherwise reads global memory; `loadFill` records the fetched word in the
line.

`flush` publishes any pending global log entries. `cacheReleaseFence` is
`flush`, and `cacheAcquireFence` is `invalidate`, which drops every line.
The two fences are full barriers and are the only synchronization primitives
in the model.

Proved here, not assumed:

- `load_store_same`: a write-through store is read back at the same address;
- `store_other_frame`: a store does not disturb a load at another address;
- `invalidate_load_global`: after invalidation a load reads global memory;
- `flush_global`: a store followed by a flush is visible in global memory;
- `cacheCoherent_initial`, `cacheCoherent_store`, `cacheCoherent_loadFill`,
  `cacheCoherent_invalidate`, `cacheCoherent_flush` and
  `cacheCoherent_cacheAcquireFence`: the cache invariant is preserved;
- `cache_message_passing`: a producer stores data and a flag, releases, and a
  consumer that acquires observes the fresh data;
- `cache_message_passing_without_invalidate_stale`: without the acquire
  invalidation the consumer's valid line returns the stale pre-publication
  value;
- `cache_message_passing_without_invalidate_not_fresh`: when that stale value
  differs from the published data, the consumer does not observe the fresh
  data.

Modeled assumptions:

- stores are write-through: they update global memory and the local line at
  the store address before the store returns;
- stores do not write-allocate: a store to an invalid line leaves it invalid;
- there is one cache per workgroup, shared by all lanes; `CacheState` holds
  one such cache, and message passing uses one `CacheState` per workgroup;
- there is no coherence traffic: another workgroup's stores never update this
  cache, and `syncGlobal` changes only the shared global field. A stale valid
  line survives until the workgroup invalidates it;
- release and acquire fences are full barriers: release publishes the whole
  global log, acquire invalidates the whole cache;
- global memory is word-addressed and keeps the per-location `storeLog` and
  visible prefix of `Intel.MemoryVisibility`; the cache invariant also records
  that the global log is fully published;
- loads allocate on a miss (`loadFill`), while stores do not.

Not modelled: dirty write-back lines, write-allocate, multiple cache levels,
snooping or coherence traffic, per-lane private caches, relaxed atomics,
partial visibility, byte addressing, and SLM. SLM remains workgroup-private as
in `Intel.SlmAliasing` and bypasses this global cache.

The message-passing theorem is a proof of the release/acquire pattern under
these assumptions, not a hardware-conformance claim.
-/

namespace IntelGpu

/-- One cache line: a data word and a valid bit. Data in an invalid line is
dead and must not be returned by a load. -/
structure CacheLine where
  /-- The cached data word. -/
  data : Word
  /-- Whether the line may be used for loads. -/
  valid : Bool

/-- One workgroup's cache in front of the shared global memory. -/
structure CacheState where
  /-- The shared global memory and its per-location visibility history. -/
  global : VisState
  /-- This workgroup's cache, one line per word address. -/
  cache : Nat → CacheLine

/-- The initial cache state: global memory as given, every line invalid. -/
def cacheInitial (init : Nat → Word) : CacheState where
  global := initial init
  cache := fun _ => { data := 0, valid := false }

/-- A write-through global store at one location: append the value to that
location's log, publish the whole log there, and leave other locations alone. -/
def writeThroughGlobal (s : VisState) (a : Nat) (v : Word) : VisState where
  mem := fun i => if i = a then v else s.mem i
  storeLog := fun i => if i = a then s.storeLog i ++ [v] else s.storeLog i
  visibleCount := fun i =>
    if i = a then (s.storeLog i).length + 1 else s.visibleCount i

/-- A write-through, no-write-allocate store. The store updates global memory
and the data field at the store address; the valid bit is unchanged. -/
def store (s : CacheState) (a : Nat) (v : Word) : CacheState where
  global := writeThroughGlobal s.global a v
  cache := fun i =>
    if i = a then { data := v, valid := (s.cache a).valid } else s.cache i

/-- A load: a hit returns the cached value, a miss reads global memory. -/
def load (s : CacheState) (a : Nat) : Word :=
  if (s.cache a).valid then (s.cache a).data else read s.global a

/-- The state change of a load: fill the line on a miss. -/
def loadFill (s : CacheState) (a : Nat) : CacheState :=
  if (s.cache a).valid then s
  else
    { s with cache := fun i =>
        if i = a then { data := read s.global a, valid := true } else s.cache i }

/-- A load step returns the loaded word and the filled cache state. -/
def loadStep (s : CacheState) (a : Nat) : Word × CacheState :=
  (load s a, loadFill s a)

/-- Drop every cached line. -/
def invalidate (s : CacheState) : CacheState where
  global := s.global
  cache := fun _ => { data := 0, valid := false }

/-- Publish every pending global store. Write-through stores leave no dirty
lines, so this is the write barrier rather than a cache writeback. -/
def flush (s : CacheState) : CacheState where
  global := releaseFence s.global
  cache := s.cache

/-- A release fence: publish pending global writes. -/
def cacheReleaseFence (s : CacheState) : CacheState := flush s

/-- An acquire fence: invalidate every cached line. -/
def cacheAcquireFence (s : CacheState) : CacheState := invalidate s

/-- Every global log entry is already visible. -/
def GlobalSettled (s : VisState) : Prop :=
  ∀ a, s.visibleCount a = (s.storeLog a).length

theorem globalSettled_initial (init : Nat → Word) :
    GlobalSettled (initial init) := by
  intro a
  simp [initial]

theorem globalSettled_writeThroughGlobal (s : VisState) (h : GlobalSettled s)
    (a : Nat) (v : Word) : GlobalSettled (writeThroughGlobal s a v) := by
  intro b
  by_cases hb : b = a
  · subst b
    simp [writeThroughGlobal, List.length_append]
  · simpa [writeThroughGlobal, hb] using h b

theorem globalSettled_releaseFence (s : VisState) :
    GlobalSettled (releaseFence s) := by
  intro a
  rfl

theorem globalSettled_flush (s : CacheState) : GlobalSettled (flush s).global :=
  globalSettled_releaseFence s.global

/-- The cache invariant: global memory is coherent and settled, and every valid
line holds the visible global value. -/
structure CacheCoherent (s : CacheState) : Prop where
  /-- Global memory satisfies per-location coherence. -/
  global : Coherent s.global
  /-- The global log is fully published. -/
  settled : GlobalSettled s.global
  /-- Every valid line holds the visible global value. -/
  line : ∀ a, (s.cache a).valid = true → (s.cache a).data = read s.global a

theorem visState_ext {s t : VisState} (hmem : s.mem = t.mem)
    (hlog : s.storeLog = t.storeLog) (hvis : s.visibleCount = t.visibleCount) :
    s = t := by
  cases s
  cases t
  simp_all

/-- A write-through store preserves per-location global coherence. -/
theorem coherent_writeThroughGlobal (s : VisState) (hs : Coherent s) (a : Nat)
    (v : Word) : Coherent (writeThroughGlobal s a v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b
    by_cases hb : b = a
    · subst b
      simp [writeThroughGlobal]
    · simpa [writeThroughGlobal, hb] using hs.visible_pos b
  · intro b
    by_cases hb : b = a
    · subst b
      simp [writeThroughGlobal, List.length_append]
    · simpa [writeThroughGlobal, hb] using hs.visible_le b
  · intro b
    by_cases hb : b = a
    · subst b
      simp [writeThroughGlobal]
    · simpa [writeThroughGlobal, hb] using hs.mem_latest b

/-- A cache store preserves per-location global coherence. -/
theorem coherent_store (s : CacheState) (hs : Coherent s.global) (a : Nat)
    (v : Word) : Coherent (store s a v).global :=
  coherent_writeThroughGlobal s.global hs a v

/-- A load fill leaves global coherence unchanged. -/
theorem coherent_loadFill (s : CacheState) (hs : Coherent s.global) (a : Nat) :
    Coherent (loadFill s a).global := by
  by_cases hv : (s.cache a).valid = true <;> simpa [loadFill, hv] using hs

/-- Invalidation leaves global coherence unchanged. -/
theorem coherent_invalidate (s : CacheState) (hs : Coherent s.global) :
    Coherent (invalidate s).global := by
  simpa [invalidate] using hs

/-- A flush preserves per-location global coherence. -/
theorem coherent_flush (s : CacheState) (hs : Coherent s.global) :
    Coherent (flush s).global := by
  simpa [flush] using coherent_releaseFence s.global hs

theorem cacheCoherent_initial (init : Nat → Word) :
    CacheCoherent (cacheInitial init) := by
  refine ⟨coherent_initial init, globalSettled_initial init, ?_⟩
  intro a h
  simp [cacheInitial] at h

theorem cacheCoherent_store (s : CacheState) (hs : CacheCoherent s) (a : Nat)
    (v : Word) : CacheCoherent (store s a v) := by
  refine ⟨coherent_store s hs.global a v, ?_, ?_⟩
  · simpa [store] using globalSettled_writeThroughGlobal s.global hs.settled a v
  · intro b hb
    by_cases hba : b = a
    · subst b
      simp [store, writeThroughGlobal, read]
    · have hvb : ((store s a v).cache b).valid = (s.cache b).valid := by
        simp [store, hba]
      have hdb : ((store s a v).cache b).data = (s.cache b).data := by
        simp [store, hba]
      have hmb : read (store s a v).global b = read s.global b := by
        simp [store, writeThroughGlobal, read, hba]
      rw [hdb, hmb]
      exact hs.line b (by rwa [hvb] at hb)

theorem cacheCoherent_loadFill (s : CacheState) (hs : CacheCoherent s) (a : Nat) :
    CacheCoherent (loadFill s a) := by
  by_cases hv : (s.cache a).valid = true
  · simpa [loadFill, hv] using hs
  · refine ⟨coherent_loadFill s hs.global a, ?_, ?_⟩
    · simpa [loadFill, hv] using hs.settled
    · intro b hb
      by_cases hba : b = a
      · subst b
        simp [loadFill, hv, read]
      · have hmb : read (loadFill s a).global b = read s.global b := by
          simp [loadFill, hv]
        have hdb : ((loadFill s a).cache b).data = (s.cache b).data := by
          simp [loadFill, hv, hba]
        have hvb : ((loadFill s a).cache b).valid = (s.cache b).valid := by
          simp [loadFill, hv, hba]
        rw [hdb, hmb]
        exact hs.line b (by rwa [hvb] at hb)

theorem cacheCoherent_invalidate (s : CacheState) (hs : CacheCoherent s) :
    CacheCoherent (invalidate s) := by
  refine ⟨coherent_invalidate s hs.global, ?_, ?_⟩
  · simpa [invalidate] using hs.settled
  · intro a h
    simp [invalidate] at h

/-- When the global log is settled, a release does not change the visible
global value. -/
theorem releaseFence_mem_eq_of_settled (s : VisState) (hs : Coherent s)
    (hset : GlobalSettled s) (a : Nat) : (releaseFence s).mem a = s.mem a := by
  have hpos := hs.visible_pos a
  have hseta := hset a
  have hlen : 0 < (s.storeLog a).length := by omega
  have hne : s.storeLog a ≠ [] := List.ne_nil_of_length_pos hlen
  have hlast : (s.storeLog a).getLast? = some ((s.storeLog a).getLast hne) :=
    List.getLast?_eq_some_getLast hne
  have hidx : (s.storeLog a)[(s.storeLog a).length - 1]? =
      some ((s.storeLog a).getLast hne) := by
    rw [← List.getLast?_eq_getElem?, hlast]
  have hmem : (s.storeLog a)[(s.storeLog a).length - 1]? = some (s.mem a) := by
    simpa [hseta] using hs.mem_latest a
  have hlast_eq : (s.storeLog a).getLast hne = s.mem a := by
    have : some ((s.storeLog a).getLast hne) = some (s.mem a) := by
      rw [← hidx, hmem]
    exact Option.some.inj this
  simp [releaseFence, lastOr, hlast, hlast_eq]

/-- A release is a no-op on a global state whose log is settled and coherent. -/
theorem releaseFence_eq_self_of_settled (s : VisState) (hs : Coherent s)
    (hset : GlobalSettled s) : releaseFence s = s := by
  apply visState_ext
  · funext a
    exact releaseFence_mem_eq_of_settled s hs hset a
  · rfl
  · funext a
    rw [releaseFence_visibleCount, hset a]

theorem cacheCoherent_flush (s : CacheState) (hs : CacheCoherent s) :
    CacheCoherent (flush s) := by
  refine ⟨coherent_flush s hs.global, globalSettled_flush s, ?_⟩
  intro a h
  have hmem : read (flush s).global a = read s.global a := by
    simpa [flush, read] using
      releaseFence_mem_eq_of_settled s.global hs.global hs.settled a
  rw [hmem]
  exact hs.line a h

/-- On a coherent cache, the release fence leaves both the cache and global
memory unchanged. -/
theorem cacheReleaseFence_eq_self (s : CacheState) (hs : CacheCoherent s) :
    cacheReleaseFence s = s := by
  cases s with
  | mk global cache =>
    simp only [cacheReleaseFence, flush]
    rw [releaseFence_eq_self_of_settled global hs.global hs.settled]

theorem cacheCoherent_cacheAcquireFence (s : CacheState) (hs : CacheCoherent s) :
    CacheCoherent (cacheAcquireFence s) := by
  simpa [cacheAcquireFence] using cacheCoherent_invalidate s hs

theorem cacheCoherent_loadStep (s : CacheState) (hs : CacheCoherent s) (a : Nat) :
    CacheCoherent (loadStep s a).2 :=
  cacheCoherent_loadFill s hs a

/-- A write-through store is read back at the same address. -/
@[simp] theorem load_store_same (s : CacheState) (a : Nat) (v : Word) :
    load (store s a v) a = v := by
  by_cases h : (s.cache a).valid <;> simp [load, store, writeThroughGlobal, read, h]

/-- A store does not disturb a load at a different address. -/
@[simp] theorem store_other_frame (s : CacheState) (a b : Nat) (v : Word)
    (h : a ≠ b) : load (store s a v) b = load s b := by
  have hb : b ≠ a := h.symm
  simp [load, store, writeThroughGlobal, read, hb]

/-- After invalidation every load reads global memory. -/
@[simp] theorem invalidate_load_global (s : CacheState) (a : Nat) :
    load (invalidate s) a = read s.global a := by
  simp [load, invalidate, read]

/-- A write-through store followed by a flush is visible in global memory. -/
@[simp] theorem flush_global (s : CacheState) (a : Nat) (v : Word) :
    read (flush (store s a v)).global a = v := by
  simp [flush, store, writeThroughGlobal, releaseFence, read, lastOr, List.getLast?_append]

/-- Flushing publishes the last logged value at every location. -/
theorem flush_publishes (s : CacheState) (a : Nat) :
    read (flush s).global a = lastOr (s.global.storeLog a) (read s.global a) := rfl

/-- A store is visible in global memory at its own address. -/
@[simp] theorem read_store_same (s : CacheState) (a : Nat) (v : Word) :
    read (store s a v).global a = v := by
  simp [store, writeThroughGlobal, read]

/-- A store leaves global memory at other addresses unchanged. -/
@[simp] theorem read_store_other (s : CacheState) (a b : Nat) (v : Word) (h : a ≠ b) :
    read (store s a v).global b = read s.global b := by
  simp [store, writeThroughGlobal, read, h.symm]

/-- Give the consumer the provider's shared global memory while keeping the
consumer's own cache. This models the absence of coherence traffic. -/
def syncGlobal (provider consumer : CacheState) : CacheState where
  global := provider.global
  cache := consumer.cache

/-- The producer stores data, then the flag, then releases. -/
def producerPublish (s : CacheState) (dataAddr flagAddr : Nat) (data : Word) :
    CacheState :=
  cacheReleaseFence (store (store s dataAddr data) flagAddr flagTrue)

/-- The consumer takes the shared global state and acquires. -/
def consumerAcquire (provider consumer : CacheState) : CacheState :=
  cacheAcquireFence (syncGlobal provider consumer)

/-- The full producer/consumer exchange over global memory. -/
def cacheMessagePassing (producer consumer : CacheState) (dataAddr flagAddr : Nat)
    (data : Word) : CacheState :=
  consumerAcquire (producerPublish producer dataAddr flagAddr data) consumer

/-- A consumer state whose line at `a` is valid and holds the initial value. -/
def initialWithCached (init : Nat → Word) (a : Nat) : CacheState where
  global := initial init
  cache := fun i =>
    if i = a then { data := init a, valid := true } else { data := 0, valid := false }

/-- The consumer reads the flag first, and the data only if the flag is true. -/
def cacheObserveAfterFlag (s : CacheState) (dataAddr flagAddr : Nat) : Option Word :=
  if load s flagAddr = flagTrue then some (load s dataAddr) else none

/-- An acquire after synchronizing with the producer restores cache coherence,
even when the consumer's old cache was stale. -/
theorem cacheCoherent_syncGlobal_acquire (provider consumer : CacheState)
    (hp : CacheCoherent provider) :
    CacheCoherent (cacheAcquireFence (syncGlobal provider consumer)) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [cacheAcquireFence, invalidate, syncGlobal] using hp.global
  · simpa [cacheAcquireFence, invalidate, syncGlobal] using hp.settled
  · intro a h
    simp [cacheAcquireFence, invalidate] at h

/-- After release/acquire, a true flag makes the consumer observe the published
data through the cache. -/
theorem cache_message_passing (init : Nat → Word) (dataAddr flagAddr : Nat)
    (data : Word) (hne : dataAddr ≠ flagAddr) :
    cacheObserveAfterFlag
        (cacheMessagePassing (cacheInitial init) (initialWithCached init dataAddr)
          dataAddr flagAddr data) dataAddr flagAddr = some data := by
  have hcc : CacheCoherent
      (store (store (cacheInitial init) dataAddr data) flagAddr flagTrue) :=
    cacheCoherent_store _ (cacheCoherent_store _ (cacheCoherent_initial init) dataAddr data)
      flagAddr flagTrue
  have hrel : producerPublish (cacheInitial init) dataAddr flagAddr data =
      store (store (cacheInitial init) dataAddr data) flagAddr flagTrue := by
    simpa [producerPublish, cacheReleaseFence] using cacheReleaseFence_eq_self _ hcc
  have hflag : load (cacheMessagePassing (cacheInitial init)
      (initialWithCached init dataAddr) dataAddr flagAddr data) flagAddr = flagTrue := by
    simp [cacheMessagePassing, consumerAcquire, cacheAcquireFence, invalidate_load_global,
      syncGlobal, hrel, read_store_same]
  have hdata : load (cacheMessagePassing (cacheInitial init)
      (initialWithCached init dataAddr) dataAddr flagAddr data) dataAddr = data := by
    simp [cacheMessagePassing, consumerAcquire, cacheAcquireFence, invalidate_load_global,
      syncGlobal, hrel, read_store_other, read_store_same, Ne.symm hne]
  simp [cacheObserveAfterFlag, hflag, hdata]

/-- Without the acquire invalidation, the consumer's valid cache line returns
the stale pre-publication value even though the flag was published. -/
theorem cache_message_passing_without_invalidate_stale (init : Nat → Word)
    (dataAddr flagAddr : Nat) (data : Word) (hne : dataAddr ≠ flagAddr) :
    cacheObserveAfterFlag
        (syncGlobal (producerPublish (cacheInitial init) dataAddr flagAddr data)
          (initialWithCached init dataAddr)) dataAddr flagAddr = some (init dataAddr) := by
  have hcc : CacheCoherent
      (store (store (cacheInitial init) dataAddr data) flagAddr flagTrue) :=
    cacheCoherent_store _ (cacheCoherent_store _ (cacheCoherent_initial init) dataAddr data)
      flagAddr flagTrue
  have hrel : producerPublish (cacheInitial init) dataAddr flagAddr data =
      store (store (cacheInitial init) dataAddr data) flagAddr flagTrue := by
    simpa [producerPublish, cacheReleaseFence] using cacheReleaseFence_eq_self _ hcc
  have hflagLoad : load (syncGlobal (producerPublish (cacheInitial init) dataAddr flagAddr data)
      (initialWithCached init dataAddr)) flagAddr = flagTrue := by
    simp [syncGlobal, hrel, load, initialWithCached, Ne.symm hne, read_store_same]
  have hdataLoad : load (syncGlobal (producerPublish (cacheInitial init) dataAddr flagAddr data)
      (initialWithCached init dataAddr)) dataAddr = init dataAddr := by
    simp [syncGlobal, load, initialWithCached]
  simp [cacheObserveAfterFlag, hflagLoad, hdataLoad]

/-- If the stale value differs from the published data, the uninvalidated
consumer does not observe the fresh data. -/
theorem cache_message_passing_without_invalidate_not_fresh (init : Nat → Word)
    (dataAddr flagAddr : Nat) (data : Word) (hne : dataAddr ≠ flagAddr)
    (hstale : init dataAddr ≠ data) :
    cacheObserveAfterFlag
        (syncGlobal (producerPublish (cacheInitial init) dataAddr flagAddr data)
          (initialWithCached init dataAddr)) dataAddr flagAddr ≠ some data := by
  rw [cache_message_passing_without_invalidate_stale init dataAddr flagAddr data hne]
  simp [hstale]

end IntelGpu
