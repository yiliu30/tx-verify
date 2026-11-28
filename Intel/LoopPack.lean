-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.DwordView

@[expose] public section

/-!
# The loop vector add's 24-lane pack layout

The native IGC assembly confirms how the two 16-lane moves cover 24 active
lanes. For example the low-dword pack is

```
mov (16|M0)  r20.0<1>:d  r15.0<2;1,0>:d
mov (16|M16) r21.0<1>:d  r17.0<2;1,0>:d
```

The first writes dword 0..15 from source 0,2,...,30. The second writes dword
8..23 from source 16,18,...,46. The overlap 8..15 receives the same values, so
the combined result is `dst[j] = src[2*j]` for `j < 24`.

This module gives that layout as a pointwise dword function and proves the
corresponding writeback into a qword-per-lane register.
-/

namespace IntelGpu

/-- The two-move even-dword pack for 24 lanes. -/
def packEven24 (r : DRegs) (srcBase dstBase : Nat) : DRegs :=
  fun d =>
    if dstBase ≤ d ∧ d < dstBase + 24 then r (srcBase + 2 * (d - dstBase))
    else r d

/-- The two-move odd-dword pack for 24 lanes. -/
def packOdd24 (r : DRegs) (srcBase dstBase : Nat) : DRegs :=
  fun d =>
    if dstBase ≤ d ∧ d < dstBase + 24 then r (srcBase + 2 * (d - dstBase) + 1)
    else r d

theorem packEven24_value (r : DRegs) (srcBase dstBase j : Nat) (hj : j < 24) :
    packEven24 r srcBase dstBase (dstBase + j) = r (srcBase + 2 * j) := by
  simp [packEven24, hj]

theorem packOdd24_value (r : DRegs) (srcBase dstBase j : Nat) (hj : j < 24) :
    packOdd24 r srcBase dstBase (dstBase + j) = r (srcBase + 2 * j + 1) := by
  simp [packOdd24, hj]

/-- Write 24 lanes of low/high dwords into the qword-per-lane destination. -/
def writeId24 (r : DRegs) (low high : Nat → Word) : DRegs :=
  fun d =>
    if d < 48 ∧ d % 2 = 0 then low (d / 2)
    else if d < 48 ∧ d % 2 = 1 then high (d / 2)
    else r d

theorem writeId24_qword (r : DRegs) (low high : Nat → Word) (l : Nat) (hl : l < 24) :
    qwordOf (writeId24 r low high) l =
      (low l).zeroExtend 64 ||| ((high l).zeroExtend 64 <<< 32) := by
  have h2 : 2 * l < 48 := by omega
  have h2' : 2 * l + 1 < 48 := by omega
  have he : (2 * l) % 2 = 0 := by omega
  have ho : (2 * l + 1) % 2 = 1 := by omega
  have hdiv : (2 * l + 1) / 2 = l := by omega
  simp [qwordOf, writeId24, h2, h2', he, ho, hdiv]

/-- The loop-carried index after one iteration: take the new id when the
continuation predicate is true, otherwise keep the old id. -/
def selectId (old new : Nat → Addr) (takeNew : Nat → Bool) : Nat → Addr :=
  fun l => if takeNew l then new l else old l

theorem selectId_true (old new : Nat → Addr) (takeNew : Nat → Bool) (l : Nat)
    (h : takeNew l = true) :
    selectId old new takeNew l = new l := by
  simp [selectId, h]

theorem selectId_false (old new : Nat → Addr) (takeNew : Nat → Bool) (l : Nat)
    (h : takeNew l = false) :
    selectId old new takeNew l = old l := by
  simp [selectId, h]

/-- Writing the selected low/high dwords back into the qword register
reconstructs the selected 64-bit id. -/
theorem writeId24_selected_qword (r : DRegs) (old new : Nat → Addr)
    (takeNew : Nat → Bool) (l : Nat) (hl : l < 24) :
    qwordOf (writeId24 r
      (fun l => (selectId old new takeNew l).truncate 32)
      (fun l => ((selectId old new takeNew l) >>> 32).truncate 32)) l =
      selectId old new takeNew l := by
  rw [writeId24_qword r _ _ l hl]
  bv_decide

end IntelGpu
