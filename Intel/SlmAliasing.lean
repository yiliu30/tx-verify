-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.MemoryVisibility
public import Intel.Slm

@[expose] public section

/-!
# Global/SLM aliasing and workgroup barriers

This module refines the immediate-visibility SLM model of `Intel.Slm` with the
per-location visibility model of `Intel.MemoryVisibility`. A `MixedState` has
two address spaces: global memory and workgroup-private SLM. Each space has its
own `VisState`, so stores are pending until a barrier releases them.

Proved here, not assumed:

- `gaddr_ne_saddr`: global and SLM addresses are tagged by their address space,
  so no numeric index aliases one space onto the other;
- `gstore_slm_frame`, `sstore_global_frame`, `sload_gstore`, `gload_sstore`: the
  disjointness frames;
- `wgBarrier_slmInvariant`: after a barrier, every pre-barrier SLM log entry is
  inside the visible prefix (`visibleCount = storeLog.length`), and the visible
  value is the last logged value;
- `sload_wgBarrier_sstore`: a store followed by a barrier is read back;
- `producer_consumer_with_barrier`: lane 1 stores a tile and lane 0 reads it
  after a barrier;
- `producer_consumer_without_barrier_stale`: without the barrier, lane 0 can
  observe the stale pre-store SLM value;
- `producer_consumer_without_barrier_not_fresh`: when that stale value differs
  from the tile, the consumer observes a value that is not the fresh tile.

Modeled assumptions:

- memory is word-addressed and cacheless, as in `Intel.MemoryVisibility`;
- SLM is private to one workgroup, so `MixedState` has no workgroup id and no
  cross-workgroup SLM visibility;
- global and SLM are separate address spaces; hardware aliasing between them is
  not modelled;
- no bank conflicts or SLM partitioning are modelled;
- a workgroup barrier is a full release/acquire fence over both spaces. It is
  assumed that every lane reaches the barrier (divergence/deadlock is modelled
  separately in `Intel.Slm`), and the global release only covers this cacheless
  workgroup's view, not cross-workgroup publication.
- stores at one location are totally ordered by the per-space `storeLog`, and a
  read returns the latest visible entry.

Not modelled: caches, relaxed atomics, partial visibility, bank conflicts,
cross-workgroup synchronization, and hardware address aliasing.
-/

namespace IntelGpu

/-- The two disjoint address spaces of a mixed memory state. -/
inductive AddressSpace where
  | global
  | slm
  deriving DecidableEq, Repr

/-- An address tagged with the space it belongs to. -/
structure MixedAddr where
  space : AddressSpace
  word : Nat
  deriving DecidableEq, Repr

/-- A global word address, tagged as global. -/
def gaddr (a : Nat) : MixedAddr :=
  ⟨.global, a⟩

/-- An SLM word address, tagged as SLM. -/
def saddr (a : Nat) : MixedAddr :=
  ⟨.slm, a⟩

/-- Global and SLM addresses never coincide, even at the same word index. -/
theorem gaddr_ne_saddr (a b : Nat) : gaddr a ≠ saddr b := by
  intro h
  have hs : AddressSpace.global = AddressSpace.slm := congrArg MixedAddr.space h
  cases hs

/-- A workgroup state with separate global and SLM visibility histories. -/
structure MixedState where
  /-- Global memory: one visibility log per word address. -/
  global : VisState
  /-- Workgroup-private shared local memory. -/
  slm : VisState
  /-- Number of completed workgroup barriers. -/
  phase : Nat

/-- Initial mixed memory with the supplied global and SLM values. -/
def mixedInitial (ginit sinit : Nat → Word) : MixedState where
  global := initial ginit
  slm := initial sinit
  phase := 0

/-- The visible global contents, as the word-addressed memory used elsewhere. -/
def globalContents (s : MixedState) : Nat → Word :=
  s.global.mem

/-- The visible SLM contents, refining the `SLM` abbreviation of `Intel.Slm`. -/
def slmContents (s : MixedState) : SLM :=
  s.slm.mem

/-- A pending global store. -/
def gstore (s : MixedState) (a : Nat) (v : Word) : MixedState :=
  { s with global := write s.global a v }

/-- A pending SLM store. -/
def sstore (s : MixedState) (a : Nat) (v : Word) : MixedState :=
  { s with slm := write s.slm a v }

/-- A global load: the latest visible global value. -/
def gload (s : MixedState) (a : Nat) : Word :=
  read s.global a

/-- An SLM load: the latest visible workgroup-private value. -/
def sload (s : MixedState) (a : Nat) : Word :=
  read s.slm a

@[simp] theorem sload_mixedInitial (ginit sinit : Nat → Word) (a : Nat) :
    sload (mixedInitial ginit sinit) a = sinit a := rfl

@[simp] theorem gload_mixedInitial (ginit sinit : Nat → Word) (a : Nat) :
    gload (mixedInitial ginit sinit) a = ginit a := rfl

/-- A full workgroup barrier: release and acquire both address spaces, then
advance the barrier phase. -/
def wgBarrier (s : MixedState) : MixedState where
  global := acquireFence (releaseFence s.global)
  slm := acquireFence (releaseFence s.slm)
  phase := s.phase + 1

@[simp] theorem wgBarrier_phase (s : MixedState) : (wgBarrier s).phase = s.phase + 1 :=
  rfl

/-- Both spaces of a mixed state satisfy per-location coherence. -/
structure MixedCoherent (s : MixedState) : Prop where
  /-- Global memory is coherent. -/
  global : Coherent s.global
  /-- SLM is coherent. -/
  slm : Coherent s.slm

theorem mixedCoherent_initial (ginit sinit : Nat → Word) :
    MixedCoherent (mixedInitial ginit sinit) :=
  ⟨coherent_initial ginit, coherent_initial sinit⟩

theorem mixedCoherent_gstore (s : MixedState) (h : MixedCoherent s) (a : Nat)
    (v : Word) : MixedCoherent (gstore s a v) :=
  ⟨coherent_write s.global h.global a v, h.slm⟩

theorem mixedCoherent_sstore (s : MixedState) (h : MixedCoherent s) (a : Nat)
    (v : Word) : MixedCoherent (sstore s a v) :=
  ⟨h.global, coherent_write s.slm h.slm a v⟩

theorem mixedCoherent_wgBarrier (s : MixedState) (h : MixedCoherent s) :
    MixedCoherent (wgBarrier s) := by
  refine ⟨?_, ?_⟩
  · simpa [wgBarrier, acquireFence] using coherent_releaseFence s.global h.global
  · simpa [wgBarrier, acquireFence] using coherent_releaseFence s.slm h.slm

/-- A global store does not change SLM. -/
@[simp] theorem gstore_slm_frame (s : MixedState) (a : Nat) (v : Word) :
    (gstore s a v).slm = s.slm := rfl

/-- A global store does not change the visible SLM contents. -/
@[simp] theorem gstore_slmContents_frame (s : MixedState) (a : Nat) (v : Word) :
    slmContents (gstore s a v) = slmContents s := rfl

/-- An SLM store does not change global memory. -/
@[simp] theorem sstore_global_frame (s : MixedState) (a : Nat) (v : Word) :
    (sstore s a v).global = s.global := rfl

/-- An SLM store does not change the visible global contents. -/
@[simp] theorem sstore_globalContents_frame (s : MixedState) (a : Nat) (v : Word) :
    globalContents (sstore s a v) = globalContents s := rfl

/-- An SLM store does not disturb any global load. -/
@[simp] theorem gload_sstore (s : MixedState) (a b : Nat) (v : Word) :
    gload (sstore s a v) b = gload s b := rfl

/-- A global store does not disturb any SLM load. -/
@[simp] theorem sload_gstore (s : MixedState) (a b : Nat) (v : Word) :
    sload (gstore s a v) b = sload s b := rfl

/-- A pending store does not change the visible value at its own location. -/
@[simp] theorem sload_sstore_pending (s : MixedState) (a : Nat) (v : Word) :
    sload (sstore s a v) a = sload s a := rfl

/-- A pending global store does not change the visible value at its location. -/
@[simp] theorem gload_gstore_pending (s : MixedState) (a : Nat) (v : Word) :
    gload (gstore s a v) a = gload s a := rfl

/-- The exact SLM state after a workgroup barrier. -/
structure SlmBarrierInvariant (before after : MixedState) : Prop where
  /-- `after` is exactly the result of the barrier. -/
  after_eq : after = wgBarrier before
  /-- The barrier does not edit or reorder the SLM store log. -/
  log_frame : after.slm.storeLog = before.slm.storeLog
  /-- Every pre-barrier SLM store lies in the visible prefix. -/
  visible_eq_length : ∀ a,
    after.slm.visibleCount a = (before.slm.storeLog a).length
  /-- The visible SLM value is the last value logged before the barrier. -/
  mem_latest : ∀ a,
    after.slm.mem a = lastOr (before.slm.storeLog a) (before.slm.mem a)

theorem wgBarrier_slmInvariant (s : MixedState) :
    SlmBarrierInvariant s (wgBarrier s) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro a
    rfl
  · intro a
    rfl

/-- Any store index present before the barrier is visible after it. -/
theorem wgBarrier_visible_prefix (s : MixedState) (a i : Nat)
    (hi : i < (s.slm.storeLog a).length) :
    i < (wgBarrier s).slm.visibleCount a := by
  rw [(wgBarrier_slmInvariant s).visible_eq_length a]
  exact hi

/-- An SLM store followed by a workgroup barrier is visible to the next load. -/
@[simp] theorem sload_wgBarrier_sstore (s : MixedState) (a : Nat) (v : Word) :
    sload (wgBarrier (sstore s a v)) a = v := by
  simpa [sload, wgBarrier, sstore, acquireFence] using read_write_same s.slm a v

/-- A global store followed by a workgroup barrier is visible to the next load. -/
@[simp] theorem gload_wgBarrier_gstore (s : MixedState) (a : Nat) (v : Word) :
    gload (wgBarrier (gstore s a v)) a = v := by
  simpa [gload, wgBarrier, gstore, acquireFence] using read_write_same s.global a v

/-- Two-lane machine state over mixed memory. -/
structure WGState where
  /-- Shared global/SLM memory. -/
  mem : MixedState
  /-- Per-lane data registers. -/
  regs : Nat → Nat → Word

/-- Overwrite one data register of one lane. -/
def wgSetReg (s : WGState) (lane reg : Nat) (v : Word) : WGState :=
  { s with regs := fun l r => if l = lane ∧ r = reg then v else s.regs l r }

@[simp] theorem wgSetReg_self (s : WGState) (lane reg : Nat) (v : Word) :
    (wgSetReg s lane reg v).regs lane reg = v := by
  simp [wgSetReg]

theorem wgSetReg_other (s : WGState) (lane reg l r : Nat) (v : Word)
    (h : ¬ (l = lane ∧ r = reg)) :
    (wgSetReg s lane reg v).regs l r = s.regs l r := by
  simp [wgSetReg, h]

/-- The mixed-memory workgroup instructions. Store sources and load
destinations are lane registers; addresses are immediate word indices. -/
inductive WGInstr where
  | gstore (lane reg addr : Nat)
  | gload (lane reg addr : Nat)
  | sstore (lane reg addr : Nat)
  | sload (lane reg addr : Nat)
  | barrier
  deriving Repr

def wgStep (s : WGState) : WGInstr → WGState
  | .gstore lane reg addr =>
      { s with mem := gstore s.mem addr (s.regs lane reg) }
  | .gload lane reg addr =>
      wgSetReg s lane reg (gload s.mem addr)
  | .sstore lane reg addr =>
      { s with mem := sstore s.mem addr (s.regs lane reg) }
  | .sload lane reg addr =>
      wgSetReg s lane reg (sload s.mem addr)
  | .barrier => { s with mem := wgBarrier s.mem }

def wgRun (s : WGState) (is : List WGInstr) : WGState :=
  is.foldl wgStep s

@[simp] theorem wgRun_nil (s : WGState) : wgRun s [] = s := rfl

@[simp] theorem wgRun_cons (s : WGState) (i : WGInstr) (is : List WGInstr) :
    wgRun s (i :: is) = wgRun (wgStep s i) is := rfl

theorem wgRun_append (s : WGState) (as bs : List WGInstr) :
    wgRun s (as ++ bs) = wgRun (wgRun s as) bs := by
  simp [wgRun, List.foldl_append]

/-- Lane 1 stores the tile, the workgroup barriers, then lane 0 loads it. -/
def producerConsumerProg (tileAddr tileReg dst : Nat) : List WGInstr :=
  [.sstore 1 tileReg tileAddr, .barrier, .sload 0 dst tileAddr]

/-- The same exchange without the workgroup barrier. -/
def producerConsumerProgNoBarrier (tileAddr tileReg dst : Nat) : List WGInstr :=
  [.sstore 1 tileReg tileAddr, .sload 0 dst tileAddr]

/-- Initial register file for the exchange: lane 1 holds the tile in `tileReg`,
and every other register is zero. -/
def producerConsumerRegs (tileReg : Nat) (tile : Word) : Nat → Nat → Word :=
  fun lane reg => if lane = 1 ∧ reg = tileReg then tile else 0

/-- Initial two-lane state for the exchange. -/
def producerConsumerInitial (ginit sinit : Nat → Word) (tileReg : Nat)
    (tile : Word) : WGState where
  mem := mixedInitial ginit sinit
  regs := producerConsumerRegs tileReg tile

/-- With a barrier, the consumer lane observes the tile stored by the producer. -/
theorem producer_consumer_with_barrier (ginit sinit : Nat → Word)
    (tileAddr tileReg dst : Nat) (tile : Word) :
    (wgRun (producerConsumerInitial ginit sinit tileReg tile)
      (producerConsumerProg tileAddr tileReg dst)).regs 0 dst = tile := by
  simp [wgRun, producerConsumerProg, producerConsumerInitial, producerConsumerRegs,
    wgStep, wgSetReg]

/-- Without the barrier, the consumer observes the stale initial SLM value. -/
theorem producer_consumer_without_barrier_stale (ginit sinit : Nat → Word)
    (tileAddr tileReg dst : Nat) (tile : Word) :
    (wgRun (producerConsumerInitial ginit sinit tileReg tile)
      (producerConsumerProgNoBarrier tileAddr tileReg dst)).regs 0 dst =
        sinit tileAddr := by
  simp [wgRun, producerConsumerProgNoBarrier, producerConsumerInitial,
    producerConsumerRegs, wgStep, wgSetReg]

/-- If the initial SLM value was not the tile, the unbarriered consumer does not
observe the fresh tile: the barrier is load-bearing for this exchange. -/
theorem producer_consumer_without_barrier_not_fresh (ginit sinit : Nat → Word)
    (tileAddr tileReg dst : Nat) (tile : Word) (hstale : sinit tileAddr ≠ tile) :
    (wgRun (producerConsumerInitial ginit sinit tileReg tile)
      (producerConsumerProgNoBarrier tileAddr tileReg dst)).regs 0 dst ≠ tile := by
  rw [producer_consumer_without_barrier_stale]
  exact hstale

end IntelGpu
