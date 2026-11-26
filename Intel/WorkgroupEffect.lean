-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.KernelRaceFree
public import Intel.MemoryLaws

@[expose] public section

/-!
# Composing the 32 lane stores

`Intel/KernelRaceFree` proves that the 32 lanes of the loop vector add write
disjoint C words. This module composes those writes: `laneStoresAt` applies one
store per lane id, and `laneStoresAt_correct` proves that every written word
holds `A[id] + B[id]` while every other word keeps its initial value. The
workgroup theorem instantiates the ids with `vaLoopId` and discharges
distinctness from launch-id injectivity.

The composition is a sequential fold over the lanes. It models the observable
result of the per-lane stores once race freedom is known; it is not a new
concurrent semantics.
-/

namespace IntelGpu

/-- One `C[id] = A[id] + B[id]` store per lane id, newest id first. -/
def laneStoresAt (sMem : Nat → Word) (aBase bBase base : Nat) :
    List Nat → (Nat → Word) → Nat → Word
  | [], cMem, w => cMem w
  | i :: is, cMem, w =>
      if w = base + i then sMem (aBase + i) + sMem (bBase + i)
      else laneStoresAt sMem aBase bBase base is cMem w

/-- The nil equation of the lane-store fold. -/
@[simp] theorem laneStoresAt_nil (sMem : Nat → Word) (aBase bBase base : Nat)
    (cMem : Nat → Word) (w : Nat) :
    laneStoresAt sMem aBase bBase base [] cMem w = cMem w := rfl

/-- The cons equation of the lane-store fold. -/
@[simp] theorem laneStoresAt_cons (sMem : Nat → Word) (aBase bBase base : Nat)
    (i : Nat) (is : List Nat) (cMem : Nat → Word) (w : Nat) :
    laneStoresAt sMem aBase bBase base (i :: is) cMem w =
      if w = base + i then sMem (aBase + i) + sMem (bBase + i)
      else laneStoresAt sMem aBase bBase base is cMem w := rfl

/-- A list of ids writes no word outside its images. -/
theorem laneStoresAt_frame (sMem : Nat → Word) (aBase bBase base : Nat)
    (ids : List Nat) (w : Nat) (h : ∀ i, i ∈ ids → w ≠ base + i) :
    laneStoresAt sMem aBase bBase base ids (fun _ => 0) w = 0 := by
  induction ids generalizing w with
  | nil => rfl
  | cons i is ih =>
      have hne : w ≠ base + i := h i (List.mem_cons_self)
      rw [laneStoresAt_cons, ite_eq_right hne]
      exact ih w (fun j hj => h j (List.mem_cons_of_mem i hj))

/-- Every written id keeps its sum, and the frame law holds away from the
written images. -/
theorem laneStoresAt_correct (sMem : Nat → Word) (aBase bBase : Nat)
    (base : Nat) (cMem : Nat → Word) (ids : List Nat) (hnd : ids.Nodup) :
    (∀ t, t ∈ ids →
      laneStoresAt sMem aBase bBase base ids cMem (base + t) =
        sMem (aBase + t) + sMem (bBase + t)) ∧
    (∀ w, (∀ i, i ∈ ids → w ≠ base + i) →
      laneStoresAt sMem aBase bBase base ids cMem w = cMem w) := by
  induction ids with
  | nil => exact ⟨by simp, by simp [laneStoresAt]⟩
  | cons i is ih =>
      have hnot : i ∉ is := (List.nodup_cons.mp hnd).1
      have hnd' : is.Nodup := (List.nodup_cons.mp hnd).2
      obtain ⟨hval, hframe⟩ := ih hnd'
      constructor
      · intro t ht
        by_cases hti : t = i
        · subst t
          rw [laneStoresAt_cons, ite_eq_left rfl]
        · have ht' : t ∈ is := by
            rcases List.mem_cons.mp ht with h | h
            · exact (hti h).elim
            · exact h
          have hne : base + t ≠ base + i := by omega
          rw [laneStoresAt_cons, ite_eq_right hne]
          exact hval t ht'
      · intro w hw
        have hne : w ≠ base + i := hw i (List.mem_cons_self)
        rw [laneStoresAt_cons, ite_eq_right hne]
        exact hframe w (fun j hj => hw j (List.mem_cons_of_mem i hj))

/-- The 32 lane ids of the loop vector add. -/
def laneIds (localSize r0 globalOffset : Word) (localId : Nat → BitVec 16) :
    List Nat :=
  (List.range 32).map (fun l => (vaLoopId localSize r0 globalOffset localId l).toNat)

/-- Launch-id injectivity makes the 32 lane ids duplicate-free. -/
theorem laneIds_nodup (localSize r0 globalOffset : Word)
    (localId : Nat → BitVec 16) (h : LaneIdsDistinct localId) :
    (laneIds localSize r0 globalOffset localId).Nodup := by
  unfold laneIds
  have hnd := vaLoopId_pairwise_distinct localSize r0 globalOffset localId h
  rw [List.nodup_iff_pairwise_ne] at hnd
  rw [List.pairwise_map] at hnd
  rw [List.nodup_iff_pairwise_ne]
  rw [List.pairwise_map]
  exact List.Pairwise.imp (fun {a b} hab hc => hab (BitVec.eq_of_toNat_eq hc)) hnd

/-- The workgroup result: after all 32 lane stores, every lane's C word holds
its sum and every other word keeps its initial value. -/
theorem vaLoop_workgroup_correct (sMem : Nat → Word) (cPtr : Addr)
    (localSize r0 globalOffset : Word) (localId : Nat → BitVec 16)
    (aBase bBase : Nat) (h : LaneIdsDistinct localId) :
    (∀ l, l < 32 →
      laneStoresAt sMem aBase bBase (cPtr.toNat / 4)
        (laneIds localSize r0 globalOffset localId) sMem
        (cPtr.toNat / 4 + (vaLoopId localSize r0 globalOffset localId l).toNat) =
        sMem (aBase + (vaLoopId localSize r0 globalOffset localId l).toNat) +
          sMem (bBase + (vaLoopId localSize r0 globalOffset localId l).toNat)) ∧
    (∀ w, (∀ l, l < 32 →
        w ≠ cPtr.toNat / 4 + (vaLoopId localSize r0 globalOffset localId l).toNat) →
      laneStoresAt sMem aBase bBase (cPtr.toNat / 4)
        (laneIds localSize r0 globalOffset localId) sMem w = sMem w) := by
  have hnd := laneIds_nodup localSize r0 globalOffset localId h
  obtain ⟨hval, hframe⟩ := laneStoresAt_correct sMem aBase bBase (cPtr.toNat / 4)
    sMem (laneIds localSize r0 globalOffset localId) hnd
  refine ⟨?_, ?_⟩
  · intro l hl
    apply hval
    unfold laneIds
    exact List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩
  · intro w hw
    exact hframe w (fun i hi => by
      unfold laneIds at hi
      rcases List.mem_map.mp hi with ⟨l, hl, rfl⟩
      exact hw l (List.mem_range.mp hl))

end IntelGpu
