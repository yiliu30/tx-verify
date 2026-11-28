-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaMath

@[expose] public section

/-!
# Row softmax algebra

The prefill softmax needs a row maximum, `exp(x - max)` for every element,
a row sum and one reciprocal. This module proves the algebra over `Rat`:

* `rowMax` is an upper bound of every element of the row;
* `softmaxWeights` normalises the exponentials by their sum and sums to one
  when the model's reciprocal reference is the rational inverse.

The word-level execution is connected to this algebra in the later phase
stages; the MUFU error budget stays in `MufuModel.Spec`.
-/

namespace IntelGpu

/-- Two-element maximum on `Rat`. -/
def ratMax (a b : Rat) : Rat := if a ≤ b then b else a

theorem le_ratMax_left (a b : Rat) : a ≤ ratMax a b := by
  unfold ratMax
  by_cases h : a ≤ b
  · simp [h]
  · simp [h]

theorem le_ratMax_right (a b : Rat) : b ≤ ratMax a b := by
  unfold ratMax
  by_cases h : a ≤ b
  · simp [h]
  · simp [h]
    rcases Rat.le_total (a := a) (b := b) with hle | hle
    · exact absurd hle h
    · exact hle

/-- The row maximum; the empty row is `0`. -/
def rowMax : List Rat → Rat
  | [] => 0
  | x :: xs => ratMax x (rowMax xs)

/-- Every element of a row is at most the row maximum. -/
theorem rowMax_ge_mem {xs : List Rat} {x : Rat} (h : x ∈ xs) : x ≤ rowMax xs := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
      rcases List.mem_cons.mp h with heq | hb
      · rw [heq]
        exact le_ratMax_left y (rowMax ys)
      · exact Rat.le_trans (ih hb) (le_ratMax_right y (rowMax ys))

/-- The row exponentials `exp(x_i - max)`. -/
def rowExp (m : MufuModel) (xs : List Rat) : List Rat :=
  xs.map (fun x => m.expRef (x - rowMax xs))

/-- The row exponential sum. -/
def rowExpSum (m : MufuModel) (xs : List Rat) : Rat :=
  (rowExp m xs).sum

theorem rowExp_length (m : MufuModel) (xs : List Rat) :
    (rowExp m xs).length = xs.length := by
  simp [rowExp]

theorem rowExpSum_nil (m : MufuModel) : rowExpSum m [] = 0 := rfl

/-- The normalised row weights. -/
def softmaxWeights (m : MufuModel) (xs : List Rat) : List Rat :=
  (rowExp m xs).map (fun e => m.invRef (rowExpSum m xs) * e)

theorem softmaxWeights_length (m : MufuModel) (xs : List Rat) :
    (softmaxWeights m xs).length = xs.length := by
  simp [softmaxWeights, rowExp]

/-- Pull a common left factor out of a list sum. -/
theorem sum_map_mul_left (c : Rat) :
    ∀ xs : List Rat, (xs.map (fun x => c * x)).sum = c * xs.sum
  | [] => by simp [Rat.mul_zero]
  | x :: xs => by
      simp only [List.map, List.sum_cons]
      rw [sum_map_mul_left c xs, Rat.mul_add]

/-- The softmax weights sum to one when the model's reciprocal reference is
the rational inverse of the exponential sum. -/
theorem softmaxWeights_sum_one (m : MufuModel) (xs : List Rat)
    (hInv : m.invRef (rowExpSum m xs) = (rowExpSum m xs)⁻¹)
    (hne : rowExpSum m xs ≠ 0) :
    (softmaxWeights m xs).sum = 1 := by
  unfold softmaxWeights
  rw [sum_map_mul_left]
  change m.invRef (rowExpSum m xs) * rowExpSum m xs = 1
  rw [hInv]
  exact Rat.inv_mul_cancel _ hne

end IntelGpu
