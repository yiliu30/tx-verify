-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.CacheTraffic

@[expose] public section

/-!
# A directory and ownership protocol for two workgroup caches

`Intel.CacheTraffic` models two caches with synchronous broadcast invalidation,
but it has no directory state: the producer's write itself is the trigger for
invalidation. This module adds the missing directory/ownership layer.

`DirectoryEntry` records, per word location, whether the location is uncached
(`none`), shared by a list of cache ids, or owned exclusively by one cache id.
`DirectoryState` combines that directory with the shared global `VisState` and
an indexed family of caches (the two-cache model uses `producerId` and
`consumerId`).

A `readRequest` shares the location, downgrading an owner when necessary, and
fills every listed sharer from visible global memory. A `writeRequest` acquires
exclusive ownership and invalidates every other cache copy at that location.
`writeWithOwnership` combines the write request with the write-through global
store and installs the new value in the owner's line.

Proved here, not assumed:

- `directoryInvariant_initial`, `directoryInvariant_readRequest`,
  `directoryInvariant_writeRequest` and
  `directoryInvariant_writeWithOwnership`: the directory invariant is preserved,
  including owner uniqueness, read-only sharers, and every valid line equalling
  the visible global value;
- `writeWithOwnership_invalidates_sharers`: an ownership transfer invalidates
  every old sharer other than the new owner;
- `readAfterWrite_fresh`: a directory read after an ownership transfer returns
  the newly written value;
- `no_stale_after_ownership_transfer`: if the old visible value differs from the
  new value, the post-transfer directory read is not stale;
- `writeWithOwnership_message_passing`: after data-then-flag writes with
  ownership transfer, observing the flag returns the published data;
- `writeWithoutOwnership_stale` and `readIgnoringDirectory_stale`: negative
  tests showing that bypassing the ownership transfer or the directory leaves a
  sharer's stale line observable.

Modeled assumptions:

- the directory is synchronous: requests and invalidation complete before the
  operation returns;
- each location has at most one owner, and `shared` entries are read-only;
- there is no message loss, buffering, latency, or retry path;
- there are no relaxed atomics: data then flag writes are ordered by the
  composition of `writeWithOwnership` steps;
- there are no directory races: directory updates are atomic per operation;
- stores are write-through and no-write-allocate, reusing
  `Intel.CacheTraffic.writeThroughGlobal`;
- caches are one line per word address, and all valid lines hold the visible
  global value after every protocol step.

Not modelled: directory request queues, network ordering, write-back dirty
lines, multiple cache levels, per-lane private caches, partial visibility, byte
addressing, relaxed atomics, or SLM. This is a proof of the directory protocol
pattern under these assumptions, not a hardware-conformance claim.
-/

namespace IntelGpu

/-- The producer cache id in the two-cache instantiation. -/
def producerId : Nat := 0

/-- The consumer cache id in the two-cache instantiation. -/
def consumerId : Nat := 1

/-- Per-location directory state. -/
inductive DirectoryEntry where
  /-- The location is not cached. -/
  | none
  /-- The location is clean and shared by the listed cache ids. -/
  | shared (sharers : List Nat)
  /-- The location is owned exclusively by one cache id. -/
  | owned (owner : Nat)
deriving DecidableEq, Repr

namespace DirectoryEntry

/-- The cache ids listed as sharers. -/
def sharers : DirectoryEntry → List Nat
  | shared ss => ss
  | _ => []

/-- The cache ids listed as owners. -/
def owners : DirectoryEntry → List Nat
  | owned o => [o]
  | _ => []

/-- The unique owner, if the location is owned. -/
def owner? : DirectoryEntry → Option Nat
  | owned o => some o
  | _ => Option.none

/-- Write permission: only the owner may write the location. -/
def canWrite (e : DirectoryEntry) (cacheId : Nat) : Prop :=
  match e with
  | owned owner => cacheId = owner
  | _ => False

/-- A request by `cacheId` turns the location into a shared entry. An existing
owner is downgraded to a sharer. -/
def share : DirectoryEntry → Nat → DirectoryEntry
  | none, cacheId => shared [cacheId]
  | shared ss, cacheId => shared (if cacheId ∈ ss then ss else cacheId :: ss)
  | owned owner, cacheId => shared (if cacheId = owner then [owner] else [owner, cacheId])

theorem owners_length_le_one (e : DirectoryEntry) : e.owners.length ≤ 1 := by
  cases e <;> simp [owners]

theorem owner?_unique {e : DirectoryEntry} {owner₁ owner₂ : Nat}
    (h₁ : e.owner? = some owner₁) (h₂ : e.owner? = some owner₂) : owner₁ = owner₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

theorem sharer_not_canWrite {e : DirectoryEntry} {cacheId : Nat}
    (h : cacheId ∈ e.sharers) : ¬ e.canWrite cacheId := by
  cases e with
  | none => simp [sharers] at h
  | shared _ => simp [canWrite]
  | owned _ => simp [sharers] at h

theorem mem_share_self (e : DirectoryEntry) (cacheId : Nat) :
    cacheId ∈ (e.share cacheId).sharers := by
  cases e with
  | none => simp [share, sharers]
  | shared ss =>
      by_cases hmem : cacheId ∈ ss
      · simp [share, sharers, hmem]
      · simp [share, sharers, hmem]
  | owned owner =>
      by_cases howner : cacheId = owner
      · simp [share, sharers, howner]
      · simp [share, sharers, howner]

end DirectoryEntry

/-- Shared memory, an indexed cache per cache id, and a per-location directory. -/
structure DirectoryState where
  /-- Shared global memory and its per-location visibility history. -/
  global : VisState
  /-- Cache `cacheId` has one line per word address. -/
  caches : Nat → Nat → CacheLine
  /-- The directory entry at each word address. -/
  directory : Nat → DirectoryEntry

/-- A local cache load. It does not consult the directory; `directoryRead` is the
protocol-respecting read. -/
def cacheLoad (s : DirectoryState) (cacheId a : Nat) : Word :=
  if (s.caches cacheId a).valid then (s.caches cacheId a).data else read s.global a

/-- The initial directory state: all locations uncached and all lines invalid. -/
def directoryInitial (init : Nat → Word) : DirectoryState where
  global := initial init
  caches := fun _ _ => invalidLine
  directory := fun _ => .none

/-- An initial state with one location shared by `sharer` and cached there. -/
def initialWithSharer (init : Nat → Word) (sharer a : Nat) : DirectoryState where
  global := initial init
  caches := fun cacheId i =>
    if cacheId = sharer ∧ i = a then { data := init a, valid := true } else invalidLine
  directory := fun i => if i = a then .shared [sharer] else .none

/-- The directory invariant: global memory is coherent and settled, owners are
unique, sharers are read-only and hold the visible value, and every valid line
holds the visible value. -/
structure DirectoryInvariant (s : DirectoryState) : Prop where
  /-- Global memory satisfies per-location coherence. -/
  global : Coherent s.global
  /-- The global log is fully published. -/
  settled : GlobalSettled s.global
  /-- A location has at most one owner. -/
  atMostOneOwner : ∀ a owner₁ owner₂,
    (s.directory a).owner? = some owner₁ →
    (s.directory a).owner? = some owner₂ → owner₁ = owner₂
  /-- A sharer has no write permission. -/
  sharersReadOnly : ∀ a cacheId, cacheId ∈ (s.directory a).sharers →
    ¬ (s.directory a).canWrite cacheId
  /-- Every listed sharer has a valid line holding the visible global value. -/
  sharerLine : ∀ a cacheId, cacheId ∈ (s.directory a).sharers →
    (s.caches cacheId a).valid = true ∧
      (s.caches cacheId a).data = read s.global a
  /-- Every valid cache line holds the visible global value. -/
  lineFresh : ∀ cacheId a, (s.caches cacheId a).valid = true →
    (s.caches cacheId a).data = read s.global a

theorem directoryInvariant_initial (init : Nat → Word) :
    DirectoryInvariant (directoryInitial init) := by
  refine ⟨coherent_initial init, globalSettled_initial init, ?_, ?_, ?_, ?_⟩
  · intro a owner₁ owner₂ h₁ h₂
    exact DirectoryEntry.owner?_unique h₁ h₂
  · intro a cacheId hmem
    simp [directoryInitial, DirectoryEntry.sharers] at hmem
  · intro a cacheId hmem
    simp [directoryInitial, DirectoryEntry.sharers] at hmem
  · intro cacheId a hvalid
    simp [directoryInitial, invalidLine] at hvalid

theorem directoryInvariant_initialWithSharer (init : Nat → Word) (sharer a : Nat) :
    DirectoryInvariant (initialWithSharer init sharer a) := by
  refine ⟨coherent_initial init, globalSettled_initial init, ?_, ?_, ?_, ?_⟩
  · intro b owner₁ owner₂ h₁ h₂
    exact DirectoryEntry.owner?_unique h₁ h₂
  · intro b cacheId hmem
    by_cases hba : b = a
    · subst b
      have hsame : cacheId = sharer := by
        simpa [initialWithSharer, DirectoryEntry.sharers] using hmem
      subst cacheId
      simp [initialWithSharer, DirectoryEntry.canWrite]
    · simp [initialWithSharer, DirectoryEntry.sharers, hba] at hmem
  · intro b cacheId hmem
    by_cases hba : b = a
    · subst b
      have hsame : cacheId = sharer := by
        simpa [initialWithSharer, DirectoryEntry.sharers] using hmem
      subst cacheId
      constructor <;> simp [initialWithSharer, read, initial]
    · simp [initialWithSharer, DirectoryEntry.sharers, hba] at hmem
  · intro cacheId b hvalid
    by_cases hba : b = a
    · subst b
      by_cases hsame : cacheId = sharer
      · subst cacheId
        simp [initialWithSharer, read, initial]
      · simp [initialWithSharer, invalidLine, hsame] at hvalid
    · simp [initialWithSharer, invalidLine, hba] at hvalid

/-- A read request shares the location, downgrading an owner if needed, and
fills every listed sharer from visible global memory. Every other cache copy at
that location is invalidated. -/
def readRequest (s : DirectoryState) (cacheId a : Nat) : DirectoryState :=
  let entry := (s.directory a).share cacheId
  { global := s.global
    caches := fun other i =>
      if i = a then
        if other ∈ entry.sharers then
          { data := read s.global a, valid := true }
        else invalidLine
      else s.caches other i
    directory := fun i => if i = a then entry else s.directory i }

/-- A directory-respecting read: request sharing, then load from the filled
cache. -/
def directoryRead (s : DirectoryState) (cacheId a : Nat) : Word :=
  cacheLoad (readRequest s cacheId a) cacheId a

theorem directoryInvariant_readRequest (s : DirectoryState) (hs : DirectoryInvariant s)
    (cacheId a : Nat) : DirectoryInvariant (readRequest s cacheId a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [readRequest] using hs.global
  · simpa [readRequest] using hs.settled
  · intro b owner₁ owner₂ h₁ h₂
    exact DirectoryEntry.owner?_unique h₁ h₂
  · intro b other hmem
    by_cases hba : b = a
    · subst b
      simpa [readRequest] using DirectoryEntry.sharer_not_canWrite hmem
    · have hmem' : other ∈ (s.directory b).sharers := by
        simpa [readRequest, hba] using hmem
      simpa [readRequest, hba] using hs.sharersReadOnly b other hmem'
  · intro b other hmem
    by_cases hba : b = a
    · subst b
      have hmemShare : other ∈ ((s.directory a).share cacheId).sharers := by
        simpa [readRequest] using hmem
      have hline : (readRequest s cacheId a).caches other a =
          { data := read s.global a, valid := true } := by
        simp [readRequest, hmemShare]
      have hglobal : read (readRequest s cacheId a).global a = read s.global a := by
        simp [readRequest]
      constructor
      · rw [hline]
      · rw [hline, hglobal]
    · have hmem' : other ∈ (s.directory b).sharers := by
        simpa [readRequest, hba] using hmem
      have hcache : (readRequest s cacheId a).caches other b = s.caches other b := by
        simp [readRequest, hba]
      have hglobal : read (readRequest s cacheId a).global b = read s.global b := by
        simp [readRequest]
      have hold := hs.sharerLine b other hmem'
      constructor
      · rw [hcache]
        exact hold.1
      · rw [hcache, hglobal]
        exact hold.2
  · intro other b hvalid
    by_cases hba : b = a
    · subst b
      by_cases hmem : other ∈ ((s.directory a).share cacheId).sharers
      · have hline : (readRequest s cacheId a).caches other a =
            { data := read s.global a, valid := true } := by
          simp [readRequest, hmem]
        have hglobal : read (readRequest s cacheId a).global a = read s.global a := by
          simp [readRequest]
        rw [hline, hglobal]
      · have hinvalid : ((readRequest s cacheId a).caches other a).valid = false := by
          simp [readRequest, hmem, invalidLine]
        rw [hinvalid] at hvalid
        cases hvalid
    · have hcache : (readRequest s cacheId a).caches other b = s.caches other b := by
        simp [readRequest, hba]
      have hglobal : read (readRequest s cacheId a).global b = read s.global b := by
        simp [readRequest]
      rw [hcache, hglobal]
      exact hs.lineFresh other b (by rwa [hcache] at hvalid)

/-- A write request acquires exclusive ownership and invalidates every other
cache copy at the location. -/
def writeRequest (s : DirectoryState) (cacheId a : Nat) : DirectoryState where
  global := s.global
  caches := fun other i =>
    if i = a ∧ other ≠ cacheId then invalidLine else s.caches other i
  directory := fun i => if i = a then .owned cacheId else s.directory i

theorem writeRequest_invalidates_sharers (s : DirectoryState) (cacheId a : Nat)
    (sharer : Nat) (_hsh : sharer ∈ (s.directory a).sharers)
    (hne : sharer ≠ cacheId) :
    ((writeRequest s cacheId a).caches sharer a).valid = false := by
  simp [writeRequest, hne, invalidLine]

theorem directoryInvariant_writeRequest (s : DirectoryState) (hs : DirectoryInvariant s)
    (cacheId a : Nat) : DirectoryInvariant (writeRequest s cacheId a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [writeRequest] using hs.global
  · simpa [writeRequest] using hs.settled
  · intro b owner₁ owner₂ h₁ h₂
    exact DirectoryEntry.owner?_unique h₁ h₂
  · intro b other hmem
    by_cases hba : b = a
    · subst b
      simp [writeRequest, DirectoryEntry.sharers] at hmem
    · have hmem' : other ∈ (s.directory b).sharers := by
        simpa [writeRequest, hba] using hmem
      simpa [writeRequest, hba] using hs.sharersReadOnly b other hmem'
  · intro b other hmem
    by_cases hba : b = a
    · subst b
      simp [writeRequest, DirectoryEntry.sharers] at hmem
    · have hmem' : other ∈ (s.directory b).sharers := by
        simpa [writeRequest, hba] using hmem
      have hcache : (writeRequest s cacheId a).caches other b = s.caches other b := by
        simp [writeRequest, hba]
      have hglobal : read (writeRequest s cacheId a).global b = read s.global b := by
        simp [writeRequest]
      have hold := hs.sharerLine b other hmem'
      constructor
      · rw [hcache]
        exact hold.1
      · rw [hcache, hglobal]
        exact hold.2
  · intro other b hvalid
    by_cases hba : b = a
    · subst b
      by_cases hsame : other = cacheId
      · subst other
        have hcache : (writeRequest s cacheId a).caches cacheId a = s.caches cacheId a := by
          simp [writeRequest]
        have hglobal : read (writeRequest s cacheId a).global a = read s.global a := by
          simp [writeRequest]
        rw [hcache, hglobal]
        exact hs.lineFresh cacheId a (by rwa [hcache] at hvalid)
      · have hinvalid : ((writeRequest s cacheId a).caches other a).valid = false := by
          simp [writeRequest, hsame, invalidLine]
        rw [hinvalid] at hvalid
        cases hvalid
    · have hcache : (writeRequest s cacheId a).caches other b = s.caches other b := by
        simp [writeRequest, hba]
      have hglobal : read (writeRequest s cacheId a).global b = read s.global b := by
        simp [writeRequest]
      rw [hcache, hglobal]
      exact hs.lineFresh other b (by rwa [hcache] at hvalid)

/-- A directory-driven write: acquire exclusive ownership, invalidate every other
cache copy, publish the new value globally, and install it in the owner's line. -/
def writeWithOwnership (s : DirectoryState) (cacheId a : Nat) (v : Word) :
    DirectoryState :=
  let requested := writeRequest s cacheId a
  { global := writeThroughGlobal requested.global a v
    caches := fun other i =>
      if other = cacheId ∧ i = a then { data := v, valid := true }
      else requested.caches other i
    directory := requested.directory }

@[simp] theorem read_writeWithOwnership_same (s : DirectoryState) (cacheId a : Nat)
    (v : Word) : read (writeWithOwnership s cacheId a v).global a = v := by
  simp [writeWithOwnership, writeRequest, writeThroughGlobal, read]

theorem read_writeWithOwnership_other (s : DirectoryState) (cacheId a b : Nat)
    (v : Word) (h : a ≠ b) : read (writeWithOwnership s cacheId a v).global b =
      read s.global b := by
  simp [writeWithOwnership, writeRequest, writeThroughGlobal, read, h.symm]

theorem directoryInvariant_writeWithOwnership (s : DirectoryState)
    (hs : DirectoryInvariant s) (cacheId a : Nat) (v : Word) :
    DirectoryInvariant (writeWithOwnership s cacheId a v) := by
  have hw := directoryInvariant_writeRequest s hs cacheId a
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [writeWithOwnership, writeRequest] using
      coherent_writeThroughGlobal s.global hs.global a v
  · simpa [writeWithOwnership, writeRequest] using
      globalSettled_writeThroughGlobal s.global hs.settled a v
  · intro b owner₁ owner₂ h₁ h₂
    exact DirectoryEntry.owner?_unique h₁ h₂
  · intro b other hmem
    have hmem' : other ∈ ((writeRequest s cacheId a).directory b).sharers := by
      simpa [writeWithOwnership] using hmem
    simpa [writeWithOwnership] using hw.sharersReadOnly b other hmem'
  · intro b other hmem
    by_cases hba : b = a
    · subst b
      have hmem' : other ∈ ((writeRequest s cacheId a).directory a).sharers := by
        simpa [writeWithOwnership] using hmem
      simp [writeRequest, DirectoryEntry.sharers] at hmem'
    · have hmem' : other ∈ ((writeRequest s cacheId a).directory b).sharers := by
        simpa [writeWithOwnership, hba] using hmem
      have hcache : (writeWithOwnership s cacheId a v).caches other b =
          (writeRequest s cacheId a).caches other b := by
        simp [writeWithOwnership, hba]
      have hglobal : read (writeWithOwnership s cacheId a v).global b =
          read (writeRequest s cacheId a).global b := by
        simp [writeWithOwnership, writeRequest, read_writeThroughGlobal_other
          s.global a b v (Ne.symm hba)]
      have hold := hw.sharerLine b other hmem'
      constructor
      · rw [hcache]
        exact hold.1
      · rw [hcache, hglobal]
        exact hold.2
  · intro other b hvalid
    by_cases hba : b = a
    · subst b
      by_cases hsame : other = cacheId
      · subst other
        have hline : (writeWithOwnership s cacheId a v).caches cacheId a =
            { data := v, valid := true } := by
          simp [writeWithOwnership]
        have hglobal : read (writeWithOwnership s cacheId a v).global a = v := by
          simp [writeWithOwnership, writeRequest, writeThroughGlobal, read]
        rw [hline, hglobal]
      · have hinvalid : ((writeWithOwnership s cacheId a v).caches other a).valid = false := by
          simp [writeWithOwnership, writeRequest, hsame, invalidLine]
        rw [hinvalid] at hvalid
        cases hvalid
    · have hcache : (writeWithOwnership s cacheId a v).caches other b =
          (writeRequest s cacheId a).caches other b := by
        simp [writeWithOwnership, hba]
      have hglobal : read (writeWithOwnership s cacheId a v).global b =
          read (writeRequest s cacheId a).global b := by
        simp [writeWithOwnership, writeRequest, read_writeThroughGlobal_other
          s.global a b v (Ne.symm hba)]
      rw [hcache, hglobal]
      exact hw.lineFresh other b (by rwa [hcache] at hvalid)

/-- The old owner or sharer is invalidated when another cache acquires
ownership, except when it is the new owner. -/
theorem writeWithOwnership_invalidates_sharers (s : DirectoryState) (cacheId a : Nat)
    (v : Word) (sharer : Nat) (_hsh : sharer ∈ (s.directory a).sharers)
    (hne : sharer ≠ cacheId) :
    ((writeWithOwnership s cacheId a v).caches sharer a).valid = false := by
  simp [writeWithOwnership, writeRequest, hne, invalidLine]

@[simp] theorem cacheLoad_readRequest_same (s : DirectoryState) (cacheId a : Nat) :
    cacheLoad (readRequest s cacheId a) cacheId a = read s.global a := by
  have hmem : cacheId ∈ ((s.directory a).share cacheId).sharers :=
    DirectoryEntry.mem_share_self _ _
  have hline : (readRequest s cacheId a).caches cacheId a =
      { data := read s.global a, valid := true } := by
    simp [readRequest, hmem]
  simp [cacheLoad, hline]

@[simp] theorem directoryRead_eq_read (s : DirectoryState) (cacheId a : Nat) :
    directoryRead s cacheId a = read s.global a := by
  simp [directoryRead]

/-- A directory read after an ownership transfer returns the new value. -/
theorem readAfterWrite_fresh (s : DirectoryState) (writer reader a : Nat) (v : Word) :
    directoryRead (writeWithOwnership s writer a v) reader a = v := by
  simp [directoryRead, writeWithOwnership, writeRequest, writeThroughGlobal, read]

/-- If the pre-transfer visible value differs from the new value, the read after
the ownership transfer is not stale. -/
theorem no_stale_after_ownership_transfer (s : DirectoryState) (writer reader a : Nat)
    (v : Word) (hstale : read s.global a ≠ v) :
    directoryRead (writeWithOwnership s writer a v) reader a ≠ read s.global a := by
  rw [readAfterWrite_fresh]
  exact fun h => hstale h.symm

/-- A plain write: it publishes globally and updates the writer's line, but does
not request ownership or invalidate sharers. This is the negative-test control. -/
def writeWithoutOwnership (s : DirectoryState) (cacheId a : Nat) (v : Word) :
    DirectoryState where
  global := writeThroughGlobal s.global a v
  caches := fun other i =>
    if other = cacheId ∧ i = a then { data := v, valid := true } else s.caches other i
  directory := s.directory

/-- Negative test: writing without ownership transfer leaves a sharer's stale
line in place. -/
theorem writeWithoutOwnership_stale (init : Nat → Word) (writer sharer a : Nat)
    (v : Word) (hne : sharer ≠ writer) :
    cacheLoad (writeWithoutOwnership (initialWithSharer init sharer a) writer a v)
      sharer a = init a := by
  simp [cacheLoad, writeWithoutOwnership, initialWithSharer, hne]

theorem writeWithoutOwnership_not_fresh (init : Nat → Word) (writer sharer a : Nat)
    (v : Word) (hne : sharer ≠ writer) (hfresh : init a ≠ v) :
    cacheLoad (writeWithoutOwnership (initialWithSharer init sharer a) writer a v)
      sharer a ≠ v := by
  rw [writeWithoutOwnership_stale init writer sharer a v hne]
  exact hfresh

/-- A local read that ignores the directory and consults only the cache line. -/
def readIgnoringDirectory (s : DirectoryState) (cacheId a : Nat) : Word :=
  cacheLoad s cacheId a

/-- Negative test: a read that ignores the directory can return the stale sharer
line even though global memory already holds the new value. -/
theorem readIgnoringDirectory_stale (init : Nat → Word) (writer sharer a : Nat)
    (v : Word) (hne : sharer ≠ writer) (hfresh : init a ≠ v) :
    readIgnoringDirectory
        (writeWithoutOwnership (initialWithSharer init sharer a) writer a v) sharer a ≠
      v := by
  rw [readIgnoringDirectory, writeWithoutOwnership_stale init writer sharer a v hne]
  exact hfresh

/-- Producer writes data and then the flag, acquiring ownership for each write. -/
def producerPublishWithOwnership (s : DirectoryState) (producer dataAddr flagAddr : Nat)
    (data : Word) : DirectoryState :=
  writeWithOwnership (writeWithOwnership s producer dataAddr data) producer flagAddr flagTrue

/-- The consumer reads the flag through the directory, then reads the data only if
the flag is true. The data read is a second directory request. -/
def observeAfterFlagWithDirectory (s : DirectoryState) (reader dataAddr flagAddr : Nat) :
    Option Word :=
  let afterFlag := readRequest s reader flagAddr
  if directoryRead s reader flagAddr = flagTrue then
    some (directoryRead afterFlag reader dataAddr)
  else none

/-- Message passing under the directory protocol: data and flag are written with
ownership transfer, so observing the flag returns the published data. -/
theorem writeWithOwnership_message_passing (init : Nat → Word) (dataAddr flagAddr : Nat)
    (data : Word) (hne : dataAddr ≠ flagAddr) :
    observeAfterFlagWithDirectory
        (producerPublishWithOwnership (initialWithSharer init consumerId dataAddr)
          producerId dataAddr flagAddr data)
        consumerId dataAddr flagAddr = some data := by
  have hflag : directoryRead
      (producerPublishWithOwnership (initialWithSharer init consumerId dataAddr)
        producerId dataAddr flagAddr data) consumerId flagAddr = flagTrue := by
    simp [directoryRead, producerPublishWithOwnership, writeWithOwnership, writeRequest,
      writeThroughGlobal, read]
  have hdata : directoryRead
      (readRequest
        (producerPublishWithOwnership (initialWithSharer init consumerId dataAddr)
          producerId dataAddr flagAddr data) consumerId flagAddr)
      consumerId dataAddr = data := by
    simp [directoryRead, cacheLoad, readRequest, producerPublishWithOwnership,
      writeWithOwnership, writeRequest, writeThroughGlobal, read, DirectoryEntry.share,
      DirectoryEntry.sharers, producerId, consumerId, hne]
  dsimp [observeAfterFlagWithDirectory]
  rw [hflag, hdata]
  simp

end IntelGpu
