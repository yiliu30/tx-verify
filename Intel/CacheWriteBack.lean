-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.CacheCoherence

@[expose] public section

/-!
# Write-back dirty lines and request queues

`Intel.CacheCoherence` models a write-through cache with no dirty state. This
module extends that model with a dirty bit, write-back eviction, line and
whole-cache flushes, and a FIFO request queue. It is still one workgroup cache
over the shared `VisState`; it is not a model of the Xe cache hierarchy.

`CacheLineWB` adds `dirty` to the `CacheLine` fields. `CacheStateWB` pairs the
shared global `VisState` with one such line per word address. `writeBack` is a
write-allocate store into the local line: it makes the line valid and dirty and
leaves global memory unchanged. A `wbLoad` hits any valid line, clean or dirty,
and otherwise reads global memory; `wbLoadFill` allocates a clean line on a
miss. `evict` drops a line, publishing its data first when it is dirty.
`flushLine` publishes one dirty line and marks it clean; `flushAll` publishes
every dirty line and leaves every line clean. `dropLine` and
`flushIgnoringDirty` are the negative-test controls that discard dirty state
without publishing it.

Proved here, not assumed:

- `load_dirty_same`: a load after a write-back store hits the dirty line;
- `writeBack_evict_publishes`: evicting a dirty line publishes its data to
  global memory;
- `flushAll_publishes`: flushing all dirty lines publishes their data;
- `evict_clean_frame`: evicting a clean line leaves global memory and loads at
  other addresses unchanged;
- `wbCoherent_initial`, `wbCoherent_writeBack`, `wbCoherent_loadFill`,
  `wbCoherent_evict`, `wbCoherent_flushLine`, `wbCoherent_flushAll` and
  `wbCoherent_drainQueue`: the write-back invariant is preserved;
- `flushAll_cleanLine`: after `flushAll`, every valid line is clean and equals
  the visible global value;
- `dirty_only_divergence`: if a valid line differs from visible global memory,
  it is dirty and therefore owned by this cache;
- `queue_drain_preserves`: draining a FIFO queue from head to tail equals the
  direct sequential execution of its requests;
- `dropLine_dirty_loses_write` and `flushIgnoringDirty_stale`: dropping or
  clearing dirty state without write-back loses the write and leaves global
  memory stale.

Modeled assumptions:

- write-back: `writeBack` updates only the local line; global memory changes
  only on `evict` of a dirty line or on `flushLine`/`flushAll`;
- write-allocate: a store to an invalid line allocates a valid dirty line, and
  a load miss allocates a valid clean line;
- one line per word address: `cache : Nat → CacheLineWB` has no capacity
  eviction and no conflict misses;
- eviction is synchronous: `evict` completes its write-back before returning,
  with no buffering, retry, or latency;
- request queues are FIFO and synchronous: `enqueue` appends at the tail,
  `drainQueue` executes from the head, and no request is reordered, merged or
  lost;
- request execution is non-faulting: every read returns a word and every write
  succeeds; queues have no capacity bound and never evict implicitly;
- there is no directory traffic, snooping, or ownership transfer in this
  module: a dirty line is owned by this single cache until it is published.
  `Intel.CacheDirectory` (stage 162) models directory ownership and sharer
  invalidation instead;
- global memory is the word-addressed `VisState` of `Intel.MemoryVisibility`,
  and the invariant records that its log is fully published;
- there are no relaxed atomics, per-lane private caches, multiple cache levels,
  partial visibility, byte addressing, or SLM.

The invariant is a single-cache ownership invariant, not a hardware-conformance
claim. Cross-cache write-back and directory interaction remain outside it.
-/

namespace IntelGpu

/-- One write-back cache line. `dirty` says the line holds the newest value and
must be published before it is dropped. -/
structure CacheLineWB where
  /-- The cached data word. -/
  data : Word
  /-- Whether the line may be used for loads. -/
  valid : Bool
  /-- Whether the line differs from global memory and needs write-back. -/
  dirty : Bool

/-- An invalid, clean write-back line. Its data word is dead. -/
def invalidLineWB : CacheLineWB :=
  { data := 0, valid := false, dirty := false }

/-- A valid line whose data has not been written back. -/
abbrev Dirty (line : CacheLineWB) : Prop :=
  line.valid = true ∧ line.dirty = true

/-- One write-back cache in front of the shared global memory. -/
structure CacheStateWB where
  /-- The shared global memory and its visibility history. -/
  global : VisState
  /-- This cache's lines, one per word address. -/
  cache : Nat → CacheLineWB

/-- This cache owns the dirty line at `a`. With one cache and no directory,
ownership is exactly the valid-and-dirty condition. -/
abbrev OwnsDirty (s : CacheStateWB) (a : Nat) : Prop :=
  Dirty (s.cache a)

/-- The initial state: global memory as given and every line invalid. -/
def wbInitial (init : Nat → Word) : CacheStateWB where
  global := initial init
  cache := fun _ => invalidLineWB

/-- A load: a valid line, dirty or clean, supplies the value; a miss reads
global memory. -/
def wbLoad (s : CacheStateWB) (a : Nat) : Word :=
  if (s.cache a).valid then (s.cache a).data else read s.global a

/-- The state change of a load: fill a clean line on a miss. -/
def wbLoadFill (s : CacheStateWB) (a : Nat) : CacheStateWB :=
  if (s.cache a).valid then s
  else
    { s with cache := fun i =>
        if i = a then
          { data := read s.global a, valid := true, dirty := false }
        else s.cache i }

/-- A load step returns the loaded word and the filled state. -/
def wbLoadStep (s : CacheStateWB) (a : Nat) : Word × CacheStateWB :=
  (wbLoad s a, wbLoadFill s a)

/-- Write-allocate store into the local line. It updates only the line, marks
it valid and dirty, and leaves global memory unchanged. -/
def writeBack (s : CacheStateWB) (a : Nat) (v : Word) : CacheStateWB where
  global := s.global
  cache := fun i =>
    if i = a then { data := v, valid := true, dirty := true } else s.cache i

/-- Drop one line. A dirty line is written back to global memory first; a clean
or invalid line is dropped without touching global memory. -/
def evict (s : CacheStateWB) (a : Nat) : CacheStateWB :=
  if OwnsDirty s a then
    { global := writeThroughGlobal s.global a (s.cache a).data
      cache := fun i => if i = a then invalidLineWB else s.cache i }
  else
    { global := s.global
      cache := fun i => if i = a then invalidLineWB else s.cache i }

/-- Publish one dirty line and mark it clean. A clean or invalid line is
unchanged. -/
def flushLine (s : CacheStateWB) (a : Nat) : CacheStateWB :=
  if OwnsDirty s a then
    { global := writeThroughGlobal s.global a (s.cache a).data
      cache := fun i =>
        if i = a then
          { data := (s.cache a).data, valid := true, dirty := false }
        else s.cache i }
  else s

/-- The global state after publishing every dirty line. Each dirty line appends
one visible entry at its own address; distinct addresses are independent, so
this is simultaneous flush-all write-back. -/
def flushAllGlobal (s : CacheStateWB) : VisState where
  mem := fun a => if OwnsDirty s a then (s.cache a).data else s.global.mem a
  storeLog := fun a =>
    if OwnsDirty s a then s.global.storeLog a ++ [(s.cache a).data]
    else s.global.storeLog a
  visibleCount := fun a =>
    if OwnsDirty s a then (s.global.storeLog a).length + 1
    else s.global.visibleCount a

/-- Publish all dirty lines and mark every line clean. -/
def flushAll (s : CacheStateWB) : CacheStateWB where
  global := flushAllGlobal s
  cache := fun a => { s.cache a with dirty := false }

/-- Drop one line without write-back. This is the negative-test control. -/
def dropLine (s : CacheStateWB) (a : Nat) : CacheStateWB where
  global := s.global
  cache := fun i => if i = a then invalidLineWB else s.cache i

/-- Clear every dirty bit without publishing the data. This is the
negative-test control for a flush that ignores dirty lines. -/
def flushIgnoringDirty (s : CacheStateWB) : CacheStateWB where
  global := s.global
  cache := fun a => { s.cache a with dirty := false }

/-- A pending read or write request. -/
inductive WBRequest where
  /-- Read the word at an address. -/
  | read (a : Nat)
  /-- Write a word at an address. -/
  | write (a : Nat) (v : Word)

/-- A FIFO queue of pending write-back cache requests. -/
structure RequestQueueWB where
  /-- Oldest request first. -/
  pending : List WBRequest

/-- The empty queue. -/
def emptyQueue : RequestQueueWB := { pending := [] }

/-- Append a request at the tail. -/
def enqueue (q : RequestQueueWB) (r : WBRequest) : RequestQueueWB :=
  { pending := q.pending ++ [r] }

/-- Execute one request: reads fill on a miss, writes allocate and mark dirty. -/
def executeRequest (s : CacheStateWB) : WBRequest → CacheStateWB
  | .read a => (wbLoadStep s a).2
  | .write a v => writeBack s a v

/-- Execute a list of requests from front to back. -/
def runRequests (s : CacheStateWB) : List WBRequest → CacheStateWB
  | [] => s
  | r :: rs => runRequests (executeRequest s r) rs

/-- Drain a queue from its head to its tail. -/
def drainQueue (s : CacheStateWB) (q : RequestQueueWB) : CacheStateWB :=
  q.pending.foldl (fun st r => executeRequest st r) s

/-- Writing back allocates a valid dirty line at the written address. -/
@[simp] theorem writeBack_line (s : CacheStateWB) (a : Nat) (v : Word) :
    (writeBack s a v).cache a = { data := v, valid := true, dirty := true } := by
  simp [writeBack]

/-- Writing back does not change global memory. -/
@[simp] theorem writeBack_global (s : CacheStateWB) (a : Nat) (v : Word) :
    (writeBack s a v).global = s.global := rfl

/-- A load after a write-back store hits the dirty line. -/
@[simp] theorem load_dirty_same (s : CacheStateWB) (a : Nat) (v : Word) :
    wbLoad (writeBack s a v) a = v := by
  simp [wbLoad, writeBack]

/-- Writing back at one address leaves the line at another address alone. -/
@[simp] theorem writeBack_line_other (s : CacheStateWB) (a b : Nat) (v : Word)
    (h : b ≠ a) : (writeBack s a v).cache b = s.cache b := by
  simp [writeBack, h]

/-- A write-through global write leaves reads at other addresses unchanged. -/
@[simp] theorem read_writeThroughGlobal_frame (s : VisState) (a b : Nat) (v : Word)
    (h : b ≠ a) : read (writeThroughGlobal s a v) b = read s b := by
  simp [writeThroughGlobal, read, h]

/-- A write-through global write leaves other locations' logs unchanged. -/
@[simp] theorem writeThroughGlobal_storeLog_frame (s : VisState) (a b : Nat)
    (v : Word) (h : b ≠ a) :
    (writeThroughGlobal s a v).storeLog b = s.storeLog b := by
  simp [writeThroughGlobal, h]

/-- A write-through global write leaves other locations' visible values alone. -/
@[simp] theorem writeThroughGlobal_mem_frame (s : VisState) (a b : Nat) (v : Word)
    (h : b ≠ a) : (writeThroughGlobal s a v).mem b = s.mem b := by
  simp [writeThroughGlobal, h]

/-- A load that hits an already valid line does not change the state. -/
theorem wbLoadFill_hit (s : CacheStateWB) (a : Nat)
    (h : (s.cache a).valid = true) : wbLoadFill s a = s := by
  simp only [wbLoadFill]
  rw [ite_eq_left h]

/-- A load miss installs one clean line filled from visible global memory. -/
theorem wbLoadFill_miss (s : CacheStateWB) (a : Nat)
    (h : ¬ (s.cache a).valid = true) :
    wbLoadFill s a =
      { s with cache := fun i =>
          if i = a then
            { data := read s.global a, valid := true, dirty := false }
          else s.cache i } := by
  simp only [wbLoadFill]
  rw [ite_eq_right h]

/-- Evicting a dirty line publishes its data first. -/
theorem evict_global_of_dirty (s : CacheStateWB) (a : Nat) (h : OwnsDirty s a) :
    (evict s a).global = writeThroughGlobal s.global a (s.cache a).data := by
  simp only [evict]
  rw [ite_eq_left h]

/-- Evicting a clean or invalid line leaves global memory unchanged. -/
theorem evict_global_of_clean (s : CacheStateWB) (a : Nat)
    (h : ¬ OwnsDirty s a) : (evict s a).global = s.global := by
  simp only [evict]
  rw [ite_eq_right h]

/-- Eviction always invalidates the evicted line. -/
@[simp] theorem evict_cache_same (s : CacheStateWB) (a : Nat) :
    (evict s a).cache a = invalidLineWB := by
  by_cases hd : OwnsDirty s a
  · simp only [evict]
    rw [ite_eq_left hd]
    simp
  · simp only [evict]
    rw [ite_eq_right hd]
    simp

/-- Eviction leaves every other line unchanged. -/
@[simp] theorem evict_cache_other (s : CacheStateWB) (a b : Nat) (h : b ≠ a) :
    (evict s a).cache b = s.cache b := by
  by_cases hd : OwnsDirty s a
  · simp only [evict]
    rw [ite_eq_left hd]
    simp [h]
  · simp only [evict]
    rw [ite_eq_right hd]
    simp [h]

/-- Eviction leaves reads at other addresses unchanged. -/
theorem read_evict_global_other (s : CacheStateWB) (a b : Nat) (h : b ≠ a) :
    read (evict s a).global b = read s.global b := by
  by_cases hd : OwnsDirty s a
  · rw [evict_global_of_dirty s a hd]
    simp [read, writeThroughGlobal, h]
  · rw [evict_global_of_clean s a hd]

/-- Eviction leaves other locations' logs unchanged. -/
theorem evict_storeLog_other (s : CacheStateWB) (a b : Nat) (h : b ≠ a) :
    (evict s a).global.storeLog b = s.global.storeLog b := by
  by_cases hd : OwnsDirty s a
  · rw [evict_global_of_dirty s a hd]
    simp [writeThroughGlobal, h]
  · rw [evict_global_of_clean s a hd]

/-- Eviction leaves other locations' visible values unchanged. -/
theorem evict_mem_other (s : CacheStateWB) (a b : Nat) (h : b ≠ a) :
    (evict s a).global.mem b = s.global.mem b := by
  by_cases hd : OwnsDirty s a
  · rw [evict_global_of_dirty s a hd]
    simp [writeThroughGlobal, h]
  · rw [evict_global_of_clean s a hd]

/-- Flushing a dirty line publishes its data first. -/
theorem flushLine_global_of_dirty (s : CacheStateWB) (a : Nat)
    (h : OwnsDirty s a) :
    (flushLine s a).global = writeThroughGlobal s.global a (s.cache a).data := by
  simp only [flushLine]
  rw [ite_eq_left h]

/-- Flushing a clean or invalid line is a no-op. -/
theorem flushLine_self_of_clean (s : CacheStateWB) (a : Nat)
    (h : ¬ OwnsDirty s a) : flushLine s a = s := by
  simp only [flushLine]
  rw [ite_eq_right h]

/-- Flushing a dirty line leaves it valid, clean and unchanged in data. -/
@[simp] theorem flushLine_cache_same_of_dirty (s : CacheStateWB) (a : Nat)
    (h : OwnsDirty s a) :
    (flushLine s a).cache a =
      { data := (s.cache a).data, valid := true, dirty := false } := by
  simp only [flushLine]
  rw [ite_eq_left h]
  simp

/-- Flushing one line leaves every other line unchanged. -/
@[simp] theorem flushLine_cache_other (s : CacheStateWB) (a b : Nat) (h : b ≠ a) :
    (flushLine s a).cache b = s.cache b := by
  by_cases hd : OwnsDirty s a
  · simp only [flushLine]
    rw [ite_eq_left hd]
    simp [h]
  · rw [flushLine_self_of_clean s a hd]

/-- Flushing one line leaves reads at other addresses unchanged. -/
theorem read_flushLine_global_other (s : CacheStateWB) (a b : Nat) (h : b ≠ a) :
    read (flushLine s a).global b = read s.global b := by
  by_cases hd : OwnsDirty s a
  · rw [flushLine_global_of_dirty s a hd]
    simp [read, writeThroughGlobal, h]
  · rw [flushLine_self_of_clean s a hd]

/-- Flushing one line leaves other locations' logs unchanged. -/
theorem flushLine_storeLog_other (s : CacheStateWB) (a b : Nat) (h : b ≠ a) :
    (flushLine s a).global.storeLog b = s.global.storeLog b := by
  by_cases hd : OwnsDirty s a
  · rw [flushLine_global_of_dirty s a hd]
    simp [writeThroughGlobal, h]
  · rw [flushLine_self_of_clean s a hd]

/-- Flushing one line leaves other locations' visible values unchanged. -/
theorem flushLine_mem_other (s : CacheStateWB) (a b : Nat) (h : b ≠ a) :
    (flushLine s a).global.mem b = s.global.mem b := by
  by_cases hd : OwnsDirty s a
  · rw [flushLine_global_of_dirty s a hd]
    simp [writeThroughGlobal, h]
  · rw [flushLine_self_of_clean s a hd]

/-- The `mem` field of `flushAllGlobal` at a dirty line. -/
theorem flushAllGlobal_mem_of_dirty (s : CacheStateWB) (a : Nat)
    (h : OwnsDirty s a) :
    (flushAllGlobal s).mem a = (s.cache a).data := by
  simp only [flushAllGlobal]
  rw [ite_eq_left h]

/-- The `mem` field of `flushAllGlobal` outside dirty lines. -/
theorem flushAllGlobal_mem_of_clean (s : CacheStateWB) (a : Nat)
    (h : ¬ OwnsDirty s a) :
    (flushAllGlobal s).mem a = s.global.mem a := by
  simp only [flushAllGlobal]
  rw [ite_eq_right h]

/-- The `storeLog` field of `flushAllGlobal` at a dirty line. -/
theorem flushAllGlobal_storeLog_of_dirty (s : CacheStateWB) (a : Nat)
    (h : OwnsDirty s a) :
    (flushAllGlobal s).storeLog a = s.global.storeLog a ++ [(s.cache a).data] := by
  simp only [flushAllGlobal]
  rw [ite_eq_left h]

/-- The `storeLog` field of `flushAllGlobal` outside dirty lines. -/
theorem flushAllGlobal_storeLog_of_clean (s : CacheStateWB) (a : Nat)
    (h : ¬ OwnsDirty s a) :
    (flushAllGlobal s).storeLog a = s.global.storeLog a := by
  simp only [flushAllGlobal]
  rw [ite_eq_right h]

/-- The `visibleCount` field of `flushAllGlobal` at a dirty line. -/
theorem flushAllGlobal_visibleCount_of_dirty (s : CacheStateWB) (a : Nat)
    (h : OwnsDirty s a) :
    (flushAllGlobal s).visibleCount a = (s.global.storeLog a).length + 1 := by
  simp only [flushAllGlobal]
  rw [ite_eq_left h]

/-- The `visibleCount` field of `flushAllGlobal` outside dirty lines. -/
theorem flushAllGlobal_visibleCount_of_clean (s : CacheStateWB) (a : Nat)
    (h : ¬ OwnsDirty s a) :
    (flushAllGlobal s).visibleCount a = s.global.visibleCount a := by
  simp only [flushAllGlobal]
  rw [ite_eq_right h]

/-- Reading a dirty line after `flushAll` returns its data. -/
theorem read_flushAll_of_dirty (s : CacheStateWB) (a : Nat) (h : OwnsDirty s a) :
    read (flushAll s).global a = (s.cache a).data := by
  simpa [flushAll, read] using flushAllGlobal_mem_of_dirty s a h

/-- Reading a clean line after `flushAll` returns the prior global value. -/
theorem read_flushAll_of_clean (s : CacheStateWB) (a : Nat)
    (h : ¬ OwnsDirty s a) : read (flushAll s).global a = read s.global a := by
  simpa [flushAll, read] using flushAllGlobal_mem_of_clean s a h

/-- `flushAll` reads at one address only depend on that address's line and
visible global value. -/
theorem read_flushAll_frame {s t : CacheStateWB} {a : Nat}
    (hcache : t.cache a = s.cache a)
    (hmem : t.global.mem a = s.global.mem a) :
    read (flushAll t).global a = read (flushAll s).global a := by
  by_cases ht : OwnsDirty t a
  · have hs : OwnsDirty s a := by
      simpa [OwnsDirty, hcache] using ht
    rw [read_flushAll_of_dirty t a ht, read_flushAll_of_dirty s a hs, hcache]
  · have hs : ¬ OwnsDirty s a := by
      intro hs
      exact ht (by simpa [OwnsDirty, hcache] using hs)
    rw [read_flushAll_of_clean t a ht, read_flushAll_of_clean s a hs]
    simpa [read] using hmem

/-- Evicting a dirty line publishes its data to global memory. -/
theorem writeBack_evict_publishes (s : CacheStateWB) (a : Nat)
    (h : OwnsDirty s a) : read (evict s a).global a = (s.cache a).data := by
  rw [evict_global_of_dirty s a h]
  simp [writeThroughGlobal, read]

/-- Flushing one dirty line publishes its data to global memory. -/
theorem flushLine_publishes (s : CacheStateWB) (a : Nat)
    (h : OwnsDirty s a) : read (flushLine s a).global a = (s.cache a).data := by
  rw [flushLine_global_of_dirty s a h]
  simp [writeThroughGlobal, read]

/-- Flushing all dirty lines publishes every dirty line's data. -/
theorem flushAll_publishes (s : CacheStateWB) (a : Nat)
    (h : OwnsDirty s a) : read (flushAll s).global a = (s.cache a).data :=
  read_flushAll_of_dirty s a h

/-- Evicting a clean line leaves global memory and other loads unchanged. -/
theorem evict_clean_frame (s : CacheStateWB) (a : Nat)
    (hclean : (s.cache a).dirty = false) :
    (evict s a).global = s.global ∧
      ∀ b, b ≠ a → wbLoad (evict s a) b = wbLoad s b := by
  have hnot : ¬ OwnsDirty s a := by
    simp [OwnsDirty, Dirty, hclean]
  constructor
  · exact evict_global_of_clean s a hnot
  · intro b hne
    have hcache := evict_cache_other s a b hne
    have hread := read_evict_global_other s a b hne
    simp [wbLoad, hcache, hread]

/-- After `flushAll`, every line is clean. -/
@[simp] theorem flushAll_clean (s : CacheStateWB) (a : Nat) :
    ((flushAll s).cache a).dirty = false := by
  simp [flushAll]

/-- `flushAll` preserves the valid bit of every line. -/
@[simp] theorem flushAll_valid (s : CacheStateWB) (a : Nat) :
    ((flushAll s).cache a).valid = (s.cache a).valid := by
  simp [flushAll]

/-- `flushAll` preserves the data of every line. -/
@[simp] theorem flushAll_data (s : CacheStateWB) (a : Nat) :
    ((flushAll s).cache a).data = (s.cache a).data := by
  simp [flushAll]

/-- Flushing all dirty lines preserves per-location global coherence. -/
theorem coherent_flushAllGlobal (s : CacheStateWB) (hs : Coherent s.global) :
    Coherent (flushAllGlobal s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    by_cases hd : OwnsDirty s a
    · rw [flushAllGlobal_visibleCount_of_dirty s a hd]
      omega
    · rw [flushAllGlobal_visibleCount_of_clean s a hd]
      exact hs.visible_pos a
  · intro a
    by_cases hd : OwnsDirty s a
    · rw [flushAllGlobal_visibleCount_of_dirty s a hd,
        flushAllGlobal_storeLog_of_dirty s a hd, List.length_append]
      simp
    · rw [flushAllGlobal_visibleCount_of_clean s a hd,
        flushAllGlobal_storeLog_of_clean s a hd]
      exact hs.visible_le a
  · intro a
    by_cases hd : OwnsDirty s a
    · rw [flushAllGlobal_storeLog_of_dirty s a hd,
        flushAllGlobal_visibleCount_of_dirty s a hd,
        flushAllGlobal_mem_of_dirty s a hd]
      simp
    · rw [flushAllGlobal_storeLog_of_clean s a hd,
        flushAllGlobal_visibleCount_of_clean s a hd,
        flushAllGlobal_mem_of_clean s a hd]
      exact hs.mem_latest a

/-- Flushing all dirty lines keeps the global log fully published. -/
theorem globalSettled_flushAllGlobal (s : CacheStateWB)
    (hs : GlobalSettled s.global) : GlobalSettled (flushAllGlobal s) := by
  intro a
  by_cases hd : OwnsDirty s a
  · rw [flushAllGlobal_visibleCount_of_dirty s a hd,
      flushAllGlobal_storeLog_of_dirty s a hd, List.length_append]
    simp
  · rw [flushAllGlobal_visibleCount_of_clean s a hd,
      flushAllGlobal_storeLog_of_clean s a hd]
    exact hs a

/-- The write-back coherence invariant. Global memory is coherent and settled.
Every valid clean line equals the visible global value; a dirty line is the
only kind of line that may diverge, and its data is exactly the value that
`flushAll` publishes, so this cache owns it. -/
structure WBCoherent (s : CacheStateWB) : Prop where
  /-- Global memory satisfies per-location coherence. -/
  global : Coherent s.global
  /-- The global log is fully published. -/
  settled : GlobalSettled s.global
  /-- Every valid clean line holds the visible global value. -/
  cleanLine : ∀ a, (s.cache a).valid = true → (s.cache a).dirty = false →
    (s.cache a).data = read s.global a
  /-- Every valid dirty line is owned by this cache: its data is exactly what a
  flush-all would publish at its address. -/
  dirtyOwned : ∀ a, OwnsDirty s a →
    (s.cache a).data = read (flushAll s).global a

theorem wbInitial_not_dirty (init : Nat → Word) (a : Nat) :
    ¬ OwnsDirty (wbInitial init) a := by
  simp [wbInitial, invalidLineWB, OwnsDirty, Dirty]

/-- A valid line that is not owned as dirty must be clean. -/
theorem dirty_false_of_not_ownsDirty {s : CacheStateWB} {a : Nat}
    (hvalid : (s.cache a).valid = true) (h : ¬ OwnsDirty s a) :
    (s.cache a).dirty = false := by
  cases hbit : (s.cache a).dirty
  · rfl
  · exact (h ⟨hvalid, hbit⟩).elim

theorem wbCoherent_initial (init : Nat → Word) :
    WBCoherent (wbInitial init) := by
  refine ⟨coherent_initial init, globalSettled_initial init, ?_, ?_⟩
  · intro a hvalid
    simp [wbInitial, invalidLineWB] at hvalid
  · intro a hdirty
    exact (wbInitial_not_dirty init a hdirty).elim

/-- A write-back store preserves the invariant. -/
theorem wbCoherent_writeBack (s : CacheStateWB) (hs : WBCoherent s) (a : Nat)
    (v : Word) : WBCoherent (writeBack s a v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [writeBack] using hs.global
  · simpa [writeBack] using hs.settled
  · intro b hvalid hclean
    by_cases hba : b = a
    · subst b
      simp [writeBack] at hclean
    · have hcache : (writeBack s a v).cache b = s.cache b :=
        writeBack_line_other s a b v hba
      have hvalid' : (s.cache b).valid = true := by
        simpa [hcache] using hvalid
      have hclean' : (s.cache b).dirty = false := by
        simpa [hcache] using hclean
      rw [hcache]
      simpa [writeBack] using hs.cleanLine b hvalid' hclean'
  · intro b hdirty
    by_cases hba : b = a
    · subst b
      have hown : OwnsDirty (writeBack s a v) a := by
        simp [OwnsDirty, Dirty, writeBack]
      rw [read_flushAll_of_dirty (writeBack s a v) a hown]
    · have hcache : (writeBack s a v).cache b = s.cache b :=
        writeBack_line_other s a b v hba
      have hdirty' : OwnsDirty s b := by
        simpa [OwnsDirty, Dirty, hcache] using hdirty
      have hframe : read (flushAll (writeBack s a v)).global b =
          read (flushAll s).global b :=
        read_flushAll_frame (t := writeBack s a v) hcache rfl
      rw [hcache, hframe]
      exact hs.dirtyOwned b hdirty'

/-- A load fill preserves the invariant. -/
theorem wbCoherent_loadFill (s : CacheStateWB) (hs : WBCoherent s) (a : Nat) :
    WBCoherent (wbLoadFill s a) := by
  by_cases hv : (s.cache a).valid = true
  · rw [wbLoadFill_hit s a hv]
    exact hs
  · have hstate := wbLoadFill_miss s a hv
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hstate]
      exact hs.global
    · rw [hstate]
      exact hs.settled
    · intro b hvalid hclean
      by_cases hba : b = a
      · subst b
        rw [hstate]
        simp [read]
      · have hcache : (wbLoadFill s a).cache b = s.cache b := by
          rw [hstate]
          simp [hba]
        have hvalid' : (s.cache b).valid = true := by
          simpa [hcache] using hvalid
        have hclean' : (s.cache b).dirty = false := by
          simpa [hcache] using hclean
        rw [hcache]
        simpa [hstate] using hs.cleanLine b hvalid' hclean'
    · intro b hdirty
      by_cases hba : b = a
      · subst b
        rw [hstate] at hdirty
        simp [OwnsDirty, Dirty] at hdirty
      · have hcache : (wbLoadFill s a).cache b = s.cache b := by
          rw [hstate]
          simp [hba]
        have hdirty' : OwnsDirty s b := by
          simpa [OwnsDirty, Dirty, hcache] using hdirty
        have hframe : read (flushAll (wbLoadFill s a)).global b =
            read (flushAll s).global b :=
          read_flushAll_frame (t := wbLoadFill s a) hcache (by rw [hstate])
        rw [hcache, hframe]
        exact hs.dirtyOwned b hdirty'

/-- Evicting one line preserves the invariant, whether or not it was dirty. -/
theorem wbCoherent_evict (s : CacheStateWB) (hs : WBCoherent s) (a : Nat) :
    WBCoherent (evict s a) := by
  by_cases hd : OwnsDirty s a
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [evict_global_of_dirty s a hd]
      exact coherent_writeThroughGlobal s.global hs.global a (s.cache a).data
    · rw [evict_global_of_dirty s a hd]
      exact globalSettled_writeThroughGlobal s.global hs.settled a (s.cache a).data
    · intro b hvalid hclean
      by_cases hba : b = a
      · subst b
        rw [evict_cache_same] at hvalid
        simp [invalidLineWB] at hvalid
      · have hcache : (evict s a).cache b = s.cache b :=
          evict_cache_other s a b hba
        have hvalid' : (s.cache b).valid = true := by
          simpa [hcache] using hvalid
        have hclean' : (s.cache b).dirty = false := by
          simpa [hcache] using hclean
        rw [hcache, read_evict_global_other s a b hba]
        exact hs.cleanLine b hvalid' hclean'
    · intro b hdirty
      by_cases hba : b = a
      · subst b
        simp [OwnsDirty, Dirty, evict_cache_same, invalidLineWB] at hdirty
      · have hcache : (evict s a).cache b = s.cache b :=
          evict_cache_other s a b hba
        have hdirty' : OwnsDirty s b := by
          simpa [OwnsDirty, Dirty, hcache] using hdirty
        have hframe : read (flushAll (evict s a)).global b =
            read (flushAll s).global b :=
          read_flushAll_frame (t := evict s a) hcache (evict_mem_other s a b hba)
        rw [hcache, hframe]
        exact hs.dirtyOwned b hdirty'
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [evict_global_of_clean s a hd]
      exact hs.global
    · rw [evict_global_of_clean s a hd]
      exact hs.settled
    · intro b hvalid hclean
      by_cases hba : b = a
      · subst b
        rw [evict_cache_same] at hvalid
        simp [invalidLineWB] at hvalid
      · have hcache : (evict s a).cache b = s.cache b :=
          evict_cache_other s a b hba
        have hvalid' : (s.cache b).valid = true := by
          simpa [hcache] using hvalid
        have hclean' : (s.cache b).dirty = false := by
          simpa [hcache] using hclean
        rw [hcache, read_evict_global_other s a b hba]
        exact hs.cleanLine b hvalid' hclean'
    · intro b hdirty
      by_cases hba : b = a
      · subst b
        simp [OwnsDirty, Dirty, evict_cache_same, invalidLineWB] at hdirty
      · have hcache : (evict s a).cache b = s.cache b :=
          evict_cache_other s a b hba
        have hdirty' : OwnsDirty s b := by
          simpa [OwnsDirty, Dirty, hcache] using hdirty
        have hframe : read (flushAll (evict s a)).global b =
            read (flushAll s).global b :=
          read_flushAll_frame (t := evict s a) hcache (evict_mem_other s a b hba)
        rw [hcache, hframe]
        exact hs.dirtyOwned b hdirty'

/-- Flushing one line preserves the invariant. -/
theorem wbCoherent_flushLine (s : CacheStateWB) (hs : WBCoherent s) (a : Nat) :
    WBCoherent (flushLine s a) := by
  by_cases hd : OwnsDirty s a
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [flushLine_global_of_dirty s a hd]
      exact coherent_writeThroughGlobal s.global hs.global a (s.cache a).data
    · rw [flushLine_global_of_dirty s a hd]
      exact globalSettled_writeThroughGlobal s.global hs.settled a (s.cache a).data
    · intro b hvalid hclean
      by_cases hba : b = a
      · subst b
        rw [flushLine_cache_same_of_dirty s a hd, flushLine_global_of_dirty s a hd]
        simp [read, writeThroughGlobal]
      · have hcache : (flushLine s a).cache b = s.cache b :=
          flushLine_cache_other s a b hba
        have hvalid' : (s.cache b).valid = true := by
          simpa [hcache] using hvalid
        have hclean' : (s.cache b).dirty = false := by
          simpa [hcache] using hclean
        rw [hcache, read_flushLine_global_other s a b hba]
        exact hs.cleanLine b hvalid' hclean'
    · intro b hdirty
      by_cases hba : b = a
      · subst b
        simp [OwnsDirty, Dirty, flushLine_cache_same_of_dirty s a hd] at hdirty
      · have hcache : (flushLine s a).cache b = s.cache b :=
          flushLine_cache_other s a b hba
        have hdirty' : OwnsDirty s b := by
          simpa [OwnsDirty, Dirty, hcache] using hdirty
        have hframe : read (flushAll (flushLine s a)).global b =
            read (flushAll s).global b :=
          read_flushAll_frame (t := flushLine s a) hcache (flushLine_mem_other s a b hba)
        rw [hcache, hframe]
        exact hs.dirtyOwned b hdirty'
  · rw [flushLine_self_of_clean s a hd]
    exact hs

/-- Flushing all lines preserves the invariant and leaves every line clean. -/
theorem wbCoherent_flushAll (s : CacheStateWB) (hs : WBCoherent s) :
    WBCoherent (flushAll s) := by
  refine ⟨coherent_flushAllGlobal s hs.global,
    globalSettled_flushAllGlobal s hs.settled, ?_, ?_⟩
  · intro a hvalid _hclean
    by_cases hd : OwnsDirty s a
    · rw [read_flushAll_of_dirty s a hd]
      exact flushAll_data s a
    · have hvalid' : (s.cache a).valid = true := by
        simpa [flushAll] using hvalid
      have hclean' : (s.cache a).dirty = false :=
        dirty_false_of_not_ownsDirty hvalid' hd
      rw [read_flushAll_of_clean s a hd, flushAll_data s a]
      exact hs.cleanLine a hvalid' hclean'
  · intro a hdirty
    have hnot : ¬ OwnsDirty (flushAll s) a := by
      simp [flushAll, OwnsDirty, Dirty]
    exact (hnot hdirty).elim

/-- After `flushAll`, every valid line equals the visible global value. -/
theorem flushAll_cleanLine (s : CacheStateWB) (hs : WBCoherent s) (a : Nat)
    (hvalid : ((flushAll s).cache a).valid = true) :
    ((flushAll s).cache a).data = read (flushAll s).global a := by
  have hclean : ((flushAll s).cache a).dirty = false := flushAll_clean s a
  exact (wbCoherent_flushAll s hs).cleanLine a hvalid hclean

/-- If a valid line differs from visible global memory, it is dirty. -/
theorem dirty_only_divergence (s : CacheStateWB) (hs : WBCoherent s) (a : Nat)
    (hvalid : (s.cache a).valid = true)
    (hne : (s.cache a).data ≠ read s.global a) : OwnsDirty s a := by
  by_cases h : OwnsDirty s a
  · exact h
  · exact (hne (hs.cleanLine a hvalid
      (dirty_false_of_not_ownsDirty hvalid h))).elim

/-- Draining a queue from head to tail equals direct sequential execution of
the same list of requests. -/
theorem queue_drain_preserves (s : CacheStateWB) (q : RequestQueueWB) :
    drainQueue s q = runRequests s q.pending := by
  cases q with
  | mk pending =>
    show pending.foldl (fun st r => executeRequest st r) s =
      runRequests s pending
    induction pending generalizing s with
    | nil => rfl
    | cons r rs ih =>
      simp only [List.foldl, runRequests]
      rw [ih (executeRequest s r)]

/-- Executing two lists in sequence is executing the concatenation. -/
theorem runRequests_append (s : CacheStateWB) (xs ys : List WBRequest) :
    runRequests s (xs ++ ys) = runRequests (runRequests s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    simp [runRequests, ih]

/-- An enqueued request executes after every request already in the queue. -/
theorem drainQueue_enqueue (s : CacheStateWB) (q : RequestQueueWB)
    (r : WBRequest) :
    drainQueue s (enqueue q r) = executeRequest (drainQueue s q) r := by
  calc
    drainQueue s (enqueue q r) = runRequests s (q.pending ++ [r]) := by
      simpa [enqueue] using queue_drain_preserves s (enqueue q r)
    _ = runRequests (runRequests s q.pending) [r] :=
      runRequests_append s q.pending [r]
    _ = executeRequest (runRequests s q.pending) r := by
      simp [runRequests]
    _ = executeRequest (drainQueue s q) r := by
      rw [queue_drain_preserves]

/-- A queued write followed by a queued read returns the written value. -/
theorem queue_write_then_read (s : CacheStateWB) (a : Nat) (v : Word) :
    wbLoad (drainQueue s
      (enqueue (enqueue emptyQueue (.write a v)) (.read a))) a = v := by
  have hdrain : drainQueue s
      (enqueue (enqueue emptyQueue (.write a v)) (.read a)) =
      wbLoadFill (writeBack s a v) a := by
    simp [drainQueue, enqueue, emptyQueue, executeRequest, wbLoadStep]
  rw [hdrain, wbLoadFill_hit (writeBack s a v) a (by simp [writeBack])]
  simp [wbLoad, writeBack]

/-- Negative test: dropping a dirty line without write-back loses the write. -/
theorem dropLine_dirty_loses_write (init : Nat → Word) (a : Nat) (v : Word) :
    wbLoad (dropLine (writeBack (wbInitial init) a v) a) a = init a := by
  simp [wbLoad, dropLine, writeBack, wbInitial, initial, invalidLineWB, read]

/-- Negative test: the dropped write is not observable at the address. -/
theorem dropLine_dirty_not_fresh (init : Nat → Word) (a : Nat) (v : Word)
    (hstale : init a ≠ v) :
    wbLoad (dropLine (writeBack (wbInitial init) a v) a) a ≠ v := by
  rw [dropLine_dirty_loses_write init a v]
  exact hstale

/-- Negative test: a flush that clears dirty bits without write-back leaves
global memory stale. -/
theorem flushIgnoringDirty_stale (init : Nat → Word) (a : Nat) (v : Word) :
    read (flushIgnoringDirty (writeBack (wbInitial init) a v)).global a = init a := by
  simp [flushIgnoringDirty, writeBack, wbInitial, initial, read]

/-- Negative test: the ignored dirty value is not published. -/
theorem flushIgnoringDirty_not_fresh (init : Nat → Word) (a : Nat) (v : Word)
    (hstale : init a ≠ v) :
    read (flushIgnoringDirty (writeBack (wbInitial init) a v)).global a ≠ v := by
  rw [flushIgnoringDirty_stale init a v]
  exact hstale

/-- Negative test: a flush that ignores dirty lines breaks the invariant. -/
theorem flushIgnoringDirty_not_coherent (init : Nat → Word) (a : Nat) (v : Word)
    (hstale : init a ≠ v) :
    ¬ WBCoherent (flushIgnoringDirty (writeBack (wbInitial init) a v)) := by
  intro hc
  have hvalid : ((flushIgnoringDirty (writeBack (wbInitial init) a v)).cache a).valid =
      true := by
    simp [flushIgnoringDirty, writeBack]
  have hclean : ((flushIgnoringDirty (writeBack (wbInitial init) a v)).cache a).dirty =
      false := by
    simp [flushIgnoringDirty]
  have hline := hc.cleanLine a hvalid hclean
  simp [flushIgnoringDirty, writeBack, wbInitial, initial, read] at hline
  exact hstale hline.symm

/-- Draining a queue preserves the invariant when it starts from one. -/
theorem wbCoherent_drainQueue (s : CacheStateWB) (hs : WBCoherent s)
    (q : RequestQueueWB) : WBCoherent (drainQueue s q) := by
  rw [queue_drain_preserves]
  induction q.pending generalizing s with
  | nil => exact hs
  | cons r rs ih =>
    exact ih (executeRequest s r) (by
      cases r with
      | read a => exact wbCoherent_loadFill s hs a
      | write a v => exact wbCoherent_writeBack s hs a v)

end IntelGpu
