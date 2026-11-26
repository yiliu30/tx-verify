-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.MemoryLaws
public import Intel.VectorAddLoopBody

@[expose] public section

/-!
# Grid-stride indices for the loop vector add

This module isolates the value-level grid-stride part of the loop vector add.
The address sequence is `strideId start stride k = start + k * stride` in
64-bit arithmetic, and the loop guard is the existing `vaLoopGuard`.

The guard results use the exact in-range hypothesis
`start + (n - 1) * stride < size`: it says that every index before `n` is still
in range, including the case where one stride jumps over `size`. The separate
no-wrap hypothesis `start + n * stride < 2 ^ 64` is what the closed-form
address calculation and the distinctness proof need.

The literal implication "`start < size` and `start + n * stride < 2 ^ 64`
imply every `k < n` is in range" is false: `start = 0`, `stride = 2`, `n = 3`
and `size = 1` satisfy both hypotheses, but `strideId 0 2 1 = 2` is out of
range. The lemmas below therefore state the in-range boundary explicitly.

- `strideId_zero`, `strideId_succ`, `strideId_toNat_of_noWrap`: the index
  recurrence and its closed form in natural numbers.
- `strideId_guard_true_before`, `strideId_guard_false_at_bound`: the two sides
  of the grid-stride loop's guard.
- `strideId_pairwise_distinct`: positive strides produce distinct addresses.
- `gridStore_value`, `gridStore_frame`, `gridStore_correct`: the store
  composition for `C[id_k] = A[id_k] + B[id_k]` and its unchanged-frame law.
- `strideId_size_next_guard_false`, `strideId_range_at_most_one`: the
  one-body range-kernel specialization matching stage 140.
-/

namespace IntelGpu

noncomputable section

/-! ## The index sequence -/

/-- The grid-stride index sequence, with address arithmetic modulo `2 ^ 64`. -/
def strideId (start stride : Addr) (k : Nat) : Addr :=
  start + (k : Addr) * stride

/-- The defining closed form for the `k`-th grid-stride index. -/
theorem strideId_closed (start stride : Addr) (k : Nat) :
    strideId start stride k = start + (k : Addr) * stride := rfl

theorem strideId_zero (start stride : Addr) : strideId start stride 0 = start := by
  simp [strideId]

theorem strideId_one (start stride : Addr) : strideId start stride 1 = start + stride := by
  simp [strideId]

theorem strideId_succ (start stride : Addr) (k : Nat) :
    strideId start stride (k + 1) = strideId start stride k + stride := by
  unfold strideId
  rw [BitVec.natCast_eq_ofNat, BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul,
    BitVec.natCast_eq_ofNat]
  rw [BitVec.add_assoc]

/-- When `k * stride` fits in 64 bits, the `k`-th address's natural value is the
ordinary natural-number closed form. -/
theorem strideId_toNat_of_noWrap (start stride : Addr) (k : Nat)
    (h : start.toNat + k * stride.toNat < 2 ^ 64) :
    (strideId start stride k).toNat = start.toNat + k * stride.toNat := by
  have hkval : (↑k : Addr).toNat = k % 2 ^ 64 := by
    rw [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
  have hmul : k * stride.toNat < 2 ^ 64 := by omega
  unfold strideId
  rw [BitVec.toNat_add, BitVec.toNat_mul, hkval, Nat.mod_mul_mod,
    Nat.mod_eq_of_lt hmul]
  exact Nat.mod_eq_of_lt h

/-! ## Guards -/

theorem vaLoopGuard_true_of_lt (id size : Addr) (h : id < size) :
    vaLoopGuard id size = true := by
  simp [vaLoopGuard, h]

theorem vaLoopGuard_false_of_not_lt (id size : Addr) (h : ¬ id < size) :
    vaLoopGuard id size = false := by
  simp [vaLoopGuard, h]

/-- An index whose natural value is below `size` passes the loop guard. -/
theorem strideId_guard_true_of_lt (start stride size : Addr) (k : Nat)
    (h : start.toNat + k * stride.toNat < size.toNat) :
    vaLoopGuard (strideId start stride k) size = true := by
  apply vaLoopGuard_true_of_lt
  rw [BitVec.lt_def, strideId_toNat_of_noWrap start stride k (by omega)]
  exact h

/-- If the last index before `n` is in range, every earlier grid-stride index
passes the guard. The hypothesis also covers a stride that jumps over `size`:
only the indices strictly before `n` are required to be in range. -/
theorem strideId_guard_true_before (start stride size : Addr) (n : Nat)
    (hlast : start.toNat + (n - 1) * stride.toNat < size.toNat) :
    ∀ k, k < n → vaLoopGuard (strideId start stride k) size = true := by
  intro k hk
  apply strideId_guard_true_of_lt
  have hmul : k * stride.toNat ≤ (n - 1) * stride.toNat :=
    Nat.mul_le_mul_right stride.toNat (Nat.le_pred_of_lt hk)
  omega

/-- Once the `n`-th index reaches `size`, its guard is false provided the
addition did not wrap. -/
theorem strideId_guard_false_at_bound (start stride size : Addr) (n : Nat)
    (hreach : size.toNat ≤ start.toNat + n * stride.toNat)
    (hnoWrap : start.toNat + n * stride.toNat < 2 ^ 64) :
    vaLoopGuard (strideId start stride n) size = false := by
  apply vaLoopGuard_false_of_not_lt
  rw [BitVec.lt_def, strideId_toNat_of_noWrap start stride n hnoWrap]
  omega

/-- The loop executes exactly `n` in-range iterations: all indices before `n`
pass, and the `n`-th index is the first one at or past `size`. -/
theorem strideId_guard_true_until_and_false (start stride size : Addr) (n : Nat)
    (_hstart : start.toNat < size.toNat)
    (hlast : start.toNat + (n - 1) * stride.toNat < size.toNat)
    (hreach : size.toNat ≤ start.toNat + n * stride.toNat)
    (hnoWrap : start.toNat + n * stride.toNat < 2 ^ 64) :
    (∀ k, k < n → vaLoopGuard (strideId start stride k) size = true) ∧
      vaLoopGuard (strideId start stride n) size = false := by
  exact ⟨strideId_guard_true_before start stride size n hlast,
    strideId_guard_false_at_bound start stride size n hreach hnoWrap⟩

/-! ## Distinctness -/

/-- A positive stride gives pairwise-distinct addresses while the final addition
does not wrap. -/
theorem strideId_pairwise_distinct (start stride : Addr) (n : Nat)
    (hstride : 0 < stride.toNat)
    (hnoWrap : start.toNat + n * stride.toNat < 2 ^ 64) :
    ∀ k, k < n → ∀ j, j < n →
      strideId start stride k = strideId start stride j → k = j := by
  intro k hk j hj heq
  have hkBound : start.toNat + k * stride.toNat < 2 ^ 64 := by
    have hmul : k * stride.toNat ≤ n * stride.toNat :=
      Nat.mul_le_mul_right stride.toNat (Nat.le_of_lt hk)
    omega
  have hjBound : start.toNat + j * stride.toNat < 2 ^ 64 := by
    have hmul : j * stride.toNat ≤ n * stride.toNat :=
      Nat.mul_le_mul_right stride.toNat (Nat.le_of_lt hj)
    omega
  have hnat : (strideId start stride k).toNat =
      (strideId start stride j).toNat := congrArg BitVec.toNat heq
  rw [strideId_toNat_of_noWrap start stride k hkBound,
    strideId_toNat_of_noWrap start stride j hjBound] at hnat
  exact Nat.mul_right_cancel hstride (by omega)

/-! ## Store composition -/

theorem store32_mul_four_at (m : Nat → Word) (a : Nat) (v : Word) :
    store32 m (4 * a) v a = v := by
  unfold store32 update
  rw [Nat.mul_div_right a (by decide : 0 < 4)]
  simp

theorem store32_mul_four_away (m : Nat → Word) (a w : Nat) (v : Word)
    (h : w ≠ a) : store32 m (4 * a) v w = m w := by
  unfold store32 update
  rw [Nat.mul_div_right a (by decide : 0 < 4)]
  simp [h]

/-- The value-level grid-stride loop. Iteration `k` stores
`A[id_k] + B[id_k]` into `C` at the word for `id_k`; `A` and `B` are read-only
snapshots of the input arrays. -/
def gridStore (aMem bMem cMem : Nat → Word) (start stride : Addr) :
    Nat → Nat → Word
  | 0 => cMem
  | n + 1 =>
      store32 (gridStore aMem bMem cMem start stride n)
        (4 * (strideId start stride n).toNat)
        (aMem (strideId start stride n).toNat +
          bMem (strideId start stride n).toNat)

/-- Each iteration's write survives later iterations when every new index is
disjoint from the earlier ones. The disjointness hypothesis is explicit. -/
theorem gridStore_value (aMem bMem cMem : Nat → Word) (start stride : Addr)
    (n t : Nat) (ht : t < n)
    (hdistinct : ∀ k, k < n → ∀ j, j < k →
      strideId start stride j ≠ strideId start stride k) :
    gridStore aMem bMem cMem start stride n (strideId start stride t).toNat =
      aMem (strideId start stride t).toNat +
        bMem (strideId start stride t).toNat := by
  induction n generalizing t with
  | zero => omega
  | succ n ih =>
      rw [gridStore]
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with hlt | heq
      · have hne : strideId start stride t ≠ strideId start stride n :=
          hdistinct n (Nat.lt_succ_self n) t hlt
        have hneNat : (strideId start stride t).toNat ≠
            (strideId start stride n).toNat := by
          intro h
          exact hne (BitVec.eq_of_toNat_eq h)
        rw [store32_mul_four_away _ _ _ _ hneNat]
        exact ih t hlt (by
          intro k hk j hj
          exact hdistinct k (by omega) j hj)
      · subst t
        exact store32_mul_four_at _ _ _

/-- Every word not written by the grid-stride loop keeps its initial `C` value.
The freshness hypothesis is explicit. -/
theorem gridStore_frame (aMem bMem cMem : Nat → Word) (start stride : Addr)
    (n w : Nat)
    (hfresh : ∀ k, k < n → w ≠ (strideId start stride k).toNat) :
    gridStore aMem bMem cMem start stride n w = cMem w := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [gridStore]
      rw [store32_mul_four_away _ _ _ _ (hfresh n (Nat.lt_succ_self n))]
      exact ih (by intro k hk; exact hfresh k (by omega))

/-- The composed store result under the positive-stride no-wrap bound: every
written `C[id_k]` holds its sum, and every other word keeps its initial value. -/
theorem gridStore_correct (aMem bMem cMem : Nat → Word) (start stride : Addr)
    (n : Nat) (hstride : 0 < stride.toNat)
    (hnoWrap : start.toNat + n * stride.toNat < 2 ^ 64) :
    (∀ t, t < n →
      gridStore aMem bMem cMem start stride n (strideId start stride t).toNat =
        aMem (strideId start stride t).toNat +
          bMem (strideId start stride t).toNat) ∧
    (∀ w, (∀ k, k < n → w ≠ (strideId start stride k).toNat) →
      gridStore aMem bMem cMem start stride n w = cMem w) := by
  refine ⟨?_, fun w hw =>
    gridStore_frame aMem bMem cMem start stride n w hw⟩
  intro t ht
  apply gridStore_value aMem bMem cMem start stride n t ht
  intro k hk j hj heq
  have hkj : j = k :=
    strideId_pairwise_distinct start stride n hstride hnoWrap j (by omega) k hk heq
  omega

/-! ## Range-kernel specialization -/

/-- When the grid stride is the work size, the next index is exactly the
stage-140 increment `id + size`, so the existing `vaLoopNext_guard_false`
discharges its guard. -/
theorem strideId_size_next_guard_false (id size : Addr)
    (hbound : id.toNat + size.toNat < 2 ^ 64) :
    vaLoopGuard (strideId id size 1) size = false := by
  rw [strideId_one]
  exact vaLoopNext_guard_false id size hbound

/-- A first stride that reaches `size` also makes the next guard false. -/
theorem strideId_one_guard_false_of_reach (start stride size : Addr)
    (hreach : size.toNat ≤ start.toNat + stride.toNat)
    (hnoWrap : start.toNat + stride.toNat < 2 ^ 64) :
    vaLoopGuard (strideId start stride 1) size = false := by
  simpa using strideId_guard_false_at_bound start stride size 1
    (by simpa using hreach) (by simpa using hnoWrap)

/-- The range-kernel guard pair: the initial index passes, and the next one is
already out of range, so the loop body runs at most once. -/
theorem strideId_range_at_most_one (start stride size : Addr)
    (hstart : start.toNat < size.toNat)
    (hreach : size.toNat ≤ start.toNat + stride.toNat)
    (hnoWrap : start.toNat + stride.toNat < 2 ^ 64) :
    vaLoopGuard start size = true ∧
      vaLoopGuard (strideId start stride 1) size = false := by
  refine ⟨?_, strideId_one_guard_false_of_reach start stride size hreach hnoWrap⟩
  apply vaLoopGuard_true_of_lt
  exact BitVec.lt_def.mpr hstart

/-- `stride >= size` gives the same one-body bound when the first addition does
not wrap. -/
theorem strideId_range_at_most_one_of_stride_ge (start stride size : Addr)
    (hstart : start.toNat < size.toNat) (hge : size.toNat ≤ stride.toNat)
    (hnoWrap : start.toNat + stride.toNat < 2 ^ 64) :
    vaLoopGuard start size = true ∧
      vaLoopGuard (strideId start stride 1) size = false :=
  strideId_range_at_most_one start stride size hstart (by omega) hnoWrap

end

end IntelGpu
