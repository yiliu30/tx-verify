-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.RealSemantics

@[expose] public section

/-!
# Generic execution-mask laws

The loop vector add's masked moves already execute with their M1--M8 channel
offset, but the rest of `stepWith` still ignores execution masks. This module
supplies the reusable laws behind masked execution: the active hardware lanes,
their operand indices, the destination footprint of a masked write, and when
two masked writes compose.

The active-lane set is a duplicate-free `List Nat` rather than a `Finset`, so
this module keeps the `Std`-only import style of the surrounding development.

## A correction to the requested `_NM` statement

`Exec.laneActive` treats `_NM` as *no channel mask*: every lane `l < size` is
active and the printed channel offset is ignored. It is not the empty mask.
The decoder maps `_NM` moves to `.mov`, not `.movMasked`, so this distinction is
invisible in the decoded real kernels. The true `_NM` laws are
`laneActive_noMask`, `writeMaskedWith_noMask_offset` (the offset has no effect)
and `writeMaskedWith_noMask_zero` (a zero-size `_NM` write is the identity).
-/

namespace IntelGpu

/-! ## Active lanes and operand indices -/

/-- Under a real channel mask, a lane is active exactly in the execution window. -/
theorem Exec.laneActive_not_noMask (e : Exec) (hnm : e.noMask = false) (l : Nat) :
    (e.laneActive l = true) ↔ (e.offset ≤ l ∧ l < e.offset + e.size) := by
  simp [Exec.laneActive, hnm]

/-- Under `_NM`, the channel offset is ignored and the first `size` lanes run. -/
theorem Exec.laneActive_noMask (e : Exec) (hnm : e.noMask = true) (l : Nat) :
    (e.laneActive l = true) ↔ l < e.size := by
  simp [Exec.laneActive, hnm]

/-- An `_NM` execution control is insensitive to its channel offset. -/
theorem Exec.laneActive_noMask_offset (size off1 off2 l : Nat) :
    Exec.laneActive ⟨size, off1, true⟩ l = Exec.laneActive ⟨size, off2, true⟩ l := by
  simp [Exec.laneActive]

/-- A masked lane's operand index is its lane minus the channel offset. -/
theorem Exec.laneIndex_not_noMask (e : Exec) (hnm : e.noMask = false) (l : Nat) :
    e.laneIndex l = l - e.offset := by
  simp [Exec.laneIndex, hnm]

/-- An `_NM` lane's operand index is the lane itself. -/
theorem Exec.laneIndex_noMask (e : Exec) (hnm : e.noMask = true) (l : Nat) :
    e.laneIndex l = l := by
  simp [Exec.laneIndex, hnm]

/-- An active lane's operand index is inside the execution size. -/
theorem Exec.laneIndex_lt_size (e : Exec) (l : Nat) (hactive : e.laneActive l = true) :
    e.laneIndex l < e.size := by
  by_cases hnm : e.noMask
  · have hl : l < e.size := by simpa [Exec.laneActive, hnm] using hactive
    simpa [Exec.laneIndex, hnm] using hl
  · have hwin : e.offset ≤ l ∧ l < e.offset + e.size := by
      simpa [Exec.laneActive, hnm] using hactive
    simp [Exec.laneIndex, hnm]
    omega

/-- On a real channel mask, an active lane is recovered from its operand index. -/
theorem Exec.offset_add_laneIndex (e : Exec) (hnm : e.noMask = false) (l : Nat)
    (hactive : e.laneActive l = true) :
    e.offset + e.laneIndex l = l := by
  have hwin : e.offset ≤ l ∧ l < e.offset + e.size := by
    simpa [Exec.laneActive, hnm] using hactive
  simp [Exec.laneIndex, hnm]
  omega

/-- The operand-index map is injective on the active lanes of a real mask. -/
theorem Exec.laneIndex_injective_on_active (e : Exec) (hnm : e.noMask = false)
    {l1 l2 : Nat} (h1 : e.laneActive l1 = true) (h2 : e.laneActive l2 = true)
    (h : e.laneIndex l1 = e.laneIndex l2) : l1 = l2 := by
  have w1 : e.offset ≤ l1 ∧ l1 < e.offset + e.size := by
    simpa [Exec.laneActive, hnm] using h1
  have w2 : e.offset ≤ l2 ∧ l2 < e.offset + e.size := by
    simpa [Exec.laneActive, hnm] using h2
  simp [Exec.laneIndex, hnm] at h
  omega

namespace Exec

/-- The hardware lanes enabled by an execution control, as a duplicate-free list. -/
def activeLanes (e : Exec) : List Nat :=
  if e.noMask then List.range e.size
  else (List.range e.size).map (fun i => e.offset + i)

/-- `_NM` enables exactly the first `size` lanes, irrespective of the offset. -/
theorem activeLanes_noMask (e : Exec) (hnm : e.noMask = true) :
    e.activeLanes = List.range e.size := by
  simp [activeLanes, hnm]

/-- A real mask enables exactly the execution window, shifted by the offset. -/
theorem activeLanes_not_noMask (e : Exec) (hnm : e.noMask = false) :
    e.activeLanes = (List.range e.size).map (fun i => e.offset + i) := by
  simp [activeLanes, hnm]

/-- Membership in `activeLanes` is exactly `laneActive`. -/
theorem activeLanes_mem (e : Exec) (l : Nat) :
    l ∈ e.activeLanes ↔ e.laneActive l = true := by
  by_cases hnm : e.noMask
  · simp [activeLanes, hnm, Exec.laneActive]
  · simp only [activeLanes, hnm]
    simp only [List.mem_map, List.mem_range, Exec.laneActive, hnm,
      Bool.false_eq_true, ite_false, decide_eq_true_eq]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨Nat.le_add_right e.offset i, Nat.add_lt_add_left hi e.offset⟩
    · intro h
      exact ⟨l - e.offset, Nat.sub_lt_left_of_lt_add h.1 h.2,
        Nat.add_sub_of_le h.1⟩

/-- Every execution control enables exactly `size` hardware lanes. -/
theorem activeLanes_length (e : Exec) : e.activeLanes.length = e.size := by
  by_cases hnm : e.noMask <;> simp [activeLanes, hnm]

/-- `List.range` is duplicate-free; this local proof avoids the
`Classical.choice` dependency of core's `List.nodup_range`. -/
theorem range_nodup (n : Nat) : (List.range n).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.nodup_append]
    refine ⟨ih, by simp, ?_⟩
    intro a ha b hb
    simp at hb
    subst b
    have ha' : a < n := by simpa using ha
    exact Nat.ne_of_lt ha'

/-- The active-lane list has no duplicates, so its length is its cardinality. -/
theorem activeLanes_nodup (e : Exec) : e.activeLanes.Nodup := by
  by_cases hnm : e.noMask
  · simpa [activeLanes, hnm] using range_nodup e.size
  · rw [activeLanes]
    simp only [hnm]
    exact List.Pairwise.map (fun i => e.offset + i)
      (by intro a b h hEq; exact h (Nat.add_left_cancel hEq))
      (range_nodup e.size)

end Exec

/-! ## Masked destination coverage -/

/-- A masked write leaves a physical register other than its destination alone. -/
theorem writeMaskedWith_at_ne (alias : Nat → Nat) (s : RealState) (dst : Grf)
    (e : Exec) (f : Nat → Addr) (r j : Nat) (h : r ≠ alias dst.num) :
    (writeMaskedWith alias s dst e f).regs r j = s.regs r j := by
  simp [writeMaskedWith, h]

/-- A masked write only reads the prior state at the element it may overwrite. -/
theorem writeMaskedWith_congr (alias : Nat → Nat) (s s' : RealState) (dst : Grf)
    (e : Exec) (f : Nat → Addr) (r j : Nat) (h : s.regs r j = s'.regs r j) :
    (writeMaskedWith alias s dst e f).regs r j =
      (writeMaskedWith alias s' dst e f).regs r j := by
  unfold writeMaskedWith
  by_cases hr : r = alias dst.num
  · subst r
    simp [h]
  · simp [hr]
    exact h

/-- An active lane of a unit-stride destination writes its own value. -/
theorem writeMaskedWith_unit_active (alias : Nat → Nat) (s : RealState) (dst : Grf)
    (e : Exec) (f : Nat → Addr) (hdst : dst.hstride = 1) (l : Nat)
    (hactive : e.laneActive l = true) :
    (writeMaskedWith alias s dst e f).regs (alias dst.num)
        (dst.dstIndex (e.laneIndex l)) = f (e.laneIndex l) := by
  by_cases hnm : e.noMask
  · have hli : e.laneIndex l = l := by simp [Exec.laneIndex, hnm]
    simp [writeMaskedWith, hdst, Grf.dstIndex, hli, hnm, hactive]
  · have hle : e.offset ≤ l := by
      have h := hactive
      simp [Exec.laneActive, hnm] at h
      exact h.1
    have hli : e.laneIndex l = l - e.offset := by simp [Exec.laneIndex, hnm]
    simp [writeMaskedWith, hdst, Grf.dstIndex, hli, hnm, hactive,
      Nat.add_sub_of_le hle]

/-- A destination element that no active lane writes is left untouched. -/
theorem writeMaskedWith_unit_frame (alias : Nat → Nat) (s : RealState) (dst : Grf)
    (e : Exec) (f : Nat → Addr) (hdst : dst.hstride = 1) (j : Nat)
    (hframe : ∀ l, e.laneActive l = true → j ≠ dst.dstIndex (e.laneIndex l)) :
    (writeMaskedWith alias s dst e f).regs (alias dst.num) j =
      s.regs (alias dst.num) j := by
  by_cases hb : dst.row * 8 + dst.col ≤ j
  · by_cases hnm : e.noMask
    · simp [writeMaskedWith, hdst, hb, hnm]
      intro hact
      let i := j - (dst.row * 8 + dst.col)
      have hli : e.laneIndex i = i := by simp [Exec.laneIndex, hnm]
      have hEq : j = dst.dstIndex (e.laneIndex i) := by
        simp [Grf.dstIndex, hli, hdst, i, Nat.add_sub_of_le hb]
      exact (hframe i (by simpa [hnm] using hact) hEq).elim
    · simp [writeMaskedWith, hdst, hb, hnm]
      intro hact
      let b := dst.row * 8 + dst.col
      let i := j - b
      let l := e.offset + i
      have hli : e.laneIndex l = i := by
        simp [Exec.laneIndex, hnm, l, i]
      have hEq : j = dst.dstIndex (e.laneIndex l) := by
        simp [Grf.dstIndex, hli, hdst, i, b, Nat.add_sub_of_le hb]
      exact (hframe l hact hEq).elim
  · simp [writeMaskedWith, hdst, hb]

/-- For a unit-stride destination, a masked write covers exactly the images
`dstIndex (laneIndex l)` of the active lanes and fixes every other element. -/
theorem writeMaskedWith_unit_coverage (alias : Nat → Nat) (s : RealState) (dst : Grf)
    (e : Exec) (f : Nat → Addr) (hdst : dst.hstride = 1) :
    (∀ l, e.laneActive l = true →
      (writeMaskedWith alias s dst e f).regs (alias dst.num)
          (dst.dstIndex (e.laneIndex l)) = f (e.laneIndex l)) ∧
    (∀ j, (∀ l, e.laneActive l = true → j ≠ dst.dstIndex (e.laneIndex l)) →
      (writeMaskedWith alias s dst e f).regs (alias dst.num) j =
        s.regs (alias dst.num) j) :=
  ⟨fun l hactive => writeMaskedWith_unit_active alias s dst e f hdst l hactive,
   fun j hframe => writeMaskedWith_unit_frame alias s dst e f hdst j hframe⟩

/-- The hardware lane whose unit-stride write would hit destination element `j`. -/
def Exec.laneAtDst (e : Exec) (dst : Grf) (j : Nat) : Nat :=
  if e.noMask then j - (dst.row * 8 + dst.col)
  else e.offset + (j - (dst.row * 8 + dst.col))

/-- Pointwise normal form of a unit-stride masked write. -/
theorem writeMaskedWith_unit_at (alias : Nat → Nat) (s : RealState) (dst : Grf)
    (e : Exec) (f : Nat → Addr) (j : Nat) (hdst : dst.hstride = 1) :
    (writeMaskedWith alias s dst e f).regs (alias dst.num) j =
      if dst.row * 8 + dst.col ≤ j then
        if e.laneActive (e.laneAtDst dst j) = true then
          f (j - (dst.row * 8 + dst.col))
        else s.regs (alias dst.num) j
      else s.regs (alias dst.num) j := by
  simp [writeMaskedWith, hdst, Exec.laneAtDst]
  rfl

/-- The lane selected by `laneAtDst` writes exactly destination element `j`. -/
theorem dstIndex_laneIndex_laneAtDst (dst : Grf) (e : Exec) (j : Nat)
    (hdst : dst.hstride = 1) (hb : dst.row * 8 + dst.col ≤ j) :
    dst.dstIndex (e.laneIndex (e.laneAtDst dst j)) = j := by
  unfold Exec.laneAtDst
  by_cases hnm : e.noMask
  · simp [Exec.laneIndex, Grf.dstIndex, hdst, hnm, Nat.add_sub_of_le hb]
  · simp [Exec.laneIndex, Grf.dstIndex, hdst, hnm, Nat.add_sub_of_le hb]

/-! ## Composition -/

/-- `RealState` is determined by its four fields. -/
theorem RealState.ext_regs {s1 s2 : RealState} (h : s1.regs = s2.regs)
    (hp : s1.preds = s2.preds) (hm : s1.mem = s2.mem) (hh : s1.halted = s2.halted) :
    s1 = s2 := by
  cases s1
  cases s2
  simp_all

/-- Masked writes to distinct destination registers commute. -/
theorem writeMaskedWith_commute_ne (alias : Nat → Nat) (s : RealState)
    (dst1 dst2 : Grf) (e1 e2 : Exec) (f g : Nat → Addr)
    (h : alias dst1.num ≠ alias dst2.num) :
    writeMaskedWith alias (writeMaskedWith alias s dst1 e1 f) dst2 e2 g =
    writeMaskedWith alias (writeMaskedWith alias s dst2 e2 g) dst1 e1 f := by
  have hregs : (writeMaskedWith alias (writeMaskedWith alias s dst1 e1 f) dst2 e2 g).regs =
      (writeMaskedWith alias (writeMaskedWith alias s dst2 e2 g) dst1 e1 f).regs := by
    funext r j
    by_cases hr1 : r = alias dst1.num
    · have hne2 : r ≠ alias dst2.num := by
        intro hc
        exact h (hr1.symm.trans hc)
      rw [writeMaskedWith_at_ne alias _ dst2 e2 g r j hne2]
      have hframe : (writeMaskedWith alias s dst2 e2 g).regs r j = s.regs r j :=
        writeMaskedWith_at_ne alias s dst2 e2 g r j hne2
      rw [writeMaskedWith_congr alias (writeMaskedWith alias s dst2 e2 g) s
        dst1 e1 f r j hframe]
    · by_cases hr2 : r = alias dst2.num
      · have hne1 : r ≠ alias dst1.num := by
          intro hc
          exact h (hc.symm.trans hr2)
        have hframe : (writeMaskedWith alias s dst1 e1 f).regs r j = s.regs r j :=
          writeMaskedWith_at_ne alias s dst1 e1 f r j hne1
        rw [writeMaskedWith_congr alias (writeMaskedWith alias s dst1 e1 f) s
          dst2 e2 g r j hframe]
        rw [writeMaskedWith_at_ne alias (writeMaskedWith alias s dst2 e2 g)
          dst1 e1 f r j hne1]
      · rw [writeMaskedWith_at_ne alias (writeMaskedWith alias s dst1 e1 f)
          dst2 e2 g r j hr2]
        rw [writeMaskedWith_at_ne alias s dst1 e1 f r j hr1]
        rw [writeMaskedWith_at_ne alias (writeMaskedWith alias s dst2 e2 g)
          dst1 e1 f r j hr1]
        rw [writeMaskedWith_at_ne alias s dst2 e2 g r j hr2]
  refine RealState.ext_regs hregs ?_ ?_ ?_
  · simp [writeMaskedWith]
  · simp [writeMaskedWith]
  · simp [writeMaskedWith]

/-- Two unit-stride masked writes to the same destination commute when their
written destination elements are disjoint. This is the footprint condition:
different channel offsets can map different hardware lanes onto the same
element, so disjoint hardware lanes alone are insufficient. -/
theorem writeMaskedWith_commute_unit (alias : Nat → Nat) (s : RealState) (dst : Grf)
    (e1 e2 : Exec) (f g : Nat → Addr) (hdst : dst.hstride = 1)
    (hdisj : ∀ l1 l2, e1.laneActive l1 = true → e2.laneActive l2 = true →
      dst.dstIndex (e1.laneIndex l1) ≠ dst.dstIndex (e2.laneIndex l2)) :
    writeMaskedWith alias (writeMaskedWith alias s dst e1 f) dst e2 g =
    writeMaskedWith alias (writeMaskedWith alias s dst e2 g) dst e1 f := by
  have hregs : (writeMaskedWith alias (writeMaskedWith alias s dst e1 f) dst e2 g).regs =
      (writeMaskedWith alias (writeMaskedWith alias s dst e2 g) dst e1 f).regs := by
    funext r j
    by_cases hr : r = alias dst.num
    · subst r
      by_cases hb : dst.row * 8 + dst.col ≤ j
      · rw [writeMaskedWith_unit_at alias (writeMaskedWith alias s dst e1 f)
          dst e2 g j hdst]
        rw [writeMaskedWith_unit_at alias (writeMaskedWith alias s dst e2 g)
          dst e1 f j hdst]
        simp only [hb, ite_true]
        by_cases a1 : e1.laneActive (e1.laneAtDst dst j) = true
        · by_cases a2 : e2.laneActive (e2.laneAtDst dst j) = true
          · exfalso
            exact hdisj (e1.laneAtDst dst j) (e2.laneAtDst dst j) a1 a2
              (by rw [dstIndex_laneIndex_laneAtDst dst e1 j hdst hb,
                      dstIndex_laneIndex_laneAtDst dst e2 j hdst hb])
          · simp [a1, a2, hb, writeMaskedWith_unit_at alias s dst e1 f j hdst]
        · by_cases a2 : e2.laneActive (e2.laneAtDst dst j) = true
          · simp [a1, a2, hb, writeMaskedWith_unit_at alias s dst e2 g j hdst]
          · simp [a1, a2, hb, writeMaskedWith_unit_at alias s dst e1 f j hdst,
              writeMaskedWith_unit_at alias s dst e2 g j hdst]
      · rw [writeMaskedWith_unit_at alias (writeMaskedWith alias s dst e1 f)
          dst e2 g j hdst]
        rw [writeMaskedWith_unit_at alias (writeMaskedWith alias s dst e2 g)
          dst e1 f j hdst]
        rw [writeMaskedWith_unit_at alias s dst e1 f j hdst]
        rw [writeMaskedWith_unit_at alias s dst e2 g j hdst]
        simp [hb]
    · rw [writeMaskedWith_at_ne alias (writeMaskedWith alias s dst e1 f)
        dst e2 g r j hr]
      rw [writeMaskedWith_at_ne alias s dst e1 f r j hr]
      rw [writeMaskedWith_at_ne alias (writeMaskedWith alias s dst e2 g)
        dst e1 f r j hr]
      rw [writeMaskedWith_at_ne alias s dst e2 g r j hr]
  refine RealState.ext_regs hregs ?_ ?_ ?_
  · simp [writeMaskedWith]
  · simp [writeMaskedWith]
  · simp [writeMaskedWith]

/-- The same commutation law with the disjointness stated on operand indices
instead of destination indices. -/
theorem writeMaskedWith_commute_unit_of_laneIndex_disjoint (alias : Nat → Nat)
    (s : RealState) (dst : Grf) (e1 e2 : Exec) (f g : Nat → Addr)
    (hdst : dst.hstride = 1)
    (hdisj : ∀ l1 l2, e1.laneActive l1 = true → e2.laneActive l2 = true →
      e1.laneIndex l1 ≠ e2.laneIndex l2) :
    writeMaskedWith alias (writeMaskedWith alias s dst e1 f) dst e2 g =
    writeMaskedWith alias (writeMaskedWith alias s dst e2 g) dst e1 f := by
  refine writeMaskedWith_commute_unit alias s dst e1 e2 f g hdst ?_
  intro l1 l2 a1 a2 hEq
  exact hdisj l1 l2 a1 a2 (by
    simp [Grf.dstIndex, hdst] at hEq
    omega)

/-! ## `_NM` robustness -/

/-- The channel offset of an `_NM` write has no effect on the result. -/
theorem writeMaskedWith_noMask_offset (alias : Nat → Nat) (s : RealState)
    (dst : Grf) (size off1 off2 : Nat) (f : Nat → Addr) :
    writeMaskedWith alias s dst ⟨size, off1, true⟩ f =
    writeMaskedWith alias s dst ⟨size, off2, true⟩ f := by
  simp [writeMaskedWith, Exec.laneActive]

/-- A zero-size `_NM` masked write is the identity on the whole state. -/
theorem writeMaskedWith_noMask_zero (alias : Nat → Nat) (s : RealState)
    (dst : Grf) (off : Nat) (f : Nat → Addr) :
    writeMaskedWith alias s dst ⟨0, off, true⟩ f = s := by
  unfold writeMaskedWith
  simp [Exec.laneActive]

/-- Pointwise normal form of an `_NM` unit-stride write: only the first
`size` destination elements, starting at the declared region base, can change. -/
theorem writeMaskedWith_noMask_at (alias : Nat → Nat) (s : RealState) (dst : Grf)
    (size off : Nat) (f : Nat → Addr) (j : Nat) (hdst : dst.hstride = 1) :
    (writeMaskedWith alias s dst ⟨size, off, true⟩ f).regs (alias dst.num) j =
      if dst.row * 8 + dst.col ≤ j then
        if j - (dst.row * 8 + dst.col) < size then
          f (j - (dst.row * 8 + dst.col))
        else s.regs (alias dst.num) j
      else s.regs (alias dst.num) j := by
  simp [writeMaskedWith, hdst, Exec.laneActive]

/-- An `_NM` write fixes every destination element outside its first-`size`
window, regardless of the printed channel offset. -/
theorem writeMaskedWith_noMask_frame (alias : Nat → Nat) (s : RealState) (dst : Grf)
    (size off : Nat) (f : Nat → Addr) (j : Nat) (hdst : dst.hstride = 1)
    (hj : j < dst.row * 8 + dst.col ∨ dst.row * 8 + dst.col + size ≤ j) :
    (writeMaskedWith alias s dst ⟨size, off, true⟩ f).regs (alias dst.num) j =
      s.regs (alias dst.num) j := by
  rw [writeMaskedWith_noMask_at alias s dst size off f j hdst]
  by_cases hb : dst.row * 8 + dst.col ≤ j
  · simp only [hb, ite_true]
    have hlt : ¬ j - (dst.row * 8 + dst.col) < size := by omega
    simp [hlt]
  · simp [hb]

/-- Negative control for the corrected `_NM` reading: lane zero of a one-lane
`_NM` execution is active even when the printed offset is nonzero. -/
theorem nm_lane_zero_active : Exec.laneActive ⟨1, 16, true⟩ 0 = true := by
  decide

end IntelGpu
