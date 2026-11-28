-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaSoftmax

@[expose] public section

/-!
# Causal masking

The causal prefill mask keeps the key positions `k <= q` for query `q`. This
module proves the exact contribution set (`mem_causalRow_iff`), the diagonal
boundary (`causalRow_diag`, `causalRow_succ_dropped`), and that zeroing the
dropped weights gives the same row sum as summing the kept sublist
(`causalWeights_sum`).

Rows are lists of `(k, x)` pairs: key position and logit.
-/

namespace IntelGpu

/-- The causal mask: key `k` is visible to query `q`. -/
def causalKeep (q k : Nat) : Bool := k ≤ q

theorem causalKeep_iff (q k : Nat) : causalKeep q k = true ↔ k ≤ q :=
  decide_eq_true_iff

/-- The kept part of a row. -/
def causalRow (q : Nat) (ps : List (Nat × Rat)) : List (Nat × Rat) :=
  ps.filter (fun p => causalKeep q p.1)

/-- Exactly the pairs with `k <= q` are kept. -/
theorem mem_causalRow_iff {q : Nat} {p : Nat × Rat} {ps : List (Nat × Rat)} :
    p ∈ causalRow q ps ↔ p ∈ ps ∧ p.1 ≤ q := by
  rw [causalRow, List.mem_filter]
  constructor
  · rintro ⟨h, hk⟩
    exact ⟨h, (causalKeep_iff q p.1).mp hk⟩
  · rintro ⟨h, hk⟩
    exact ⟨h, (causalKeep_iff q p.1).mpr hk⟩

/-- The diagonal pair is kept. -/
theorem causalRow_diag (q : Nat) (v : Rat) :
    (q, v) ∈ causalRow q [(q, v)] := by
  rw [mem_causalRow_iff]
  exact ⟨List.mem_singleton.mpr rfl, Nat.le_refl q⟩

/-- The first pair beyond the diagonal is dropped. -/
theorem causalRow_succ_dropped (q : Nat) (v : Rat) :
    (q + 1, v) ∉ causalRow q [(q + 1, v)] := by
  rw [mem_causalRow_iff]
  rintro ⟨-, hk⟩
  exact Nat.not_succ_le_self q hk

/-- The masked weight: keep the exponential, or zero it. -/
def maskedWeight (q : Nat) (e : Rat → Rat) (p : Nat × Rat) : Rat :=
  if p.1 ≤ q then e p.2 else 0

theorem maskedWeight_kept (q : Nat) (e : Rat → Rat) (p : Nat × Rat)
    (h : p.1 ≤ q) : maskedWeight q e p = e p.2 := by
  unfold maskedWeight
  simp [h]

theorem maskedWeight_dropped (q : Nat) (e : Rat → Rat) (p : Nat × Rat)
    (h : ¬ p.1 ≤ q) : maskedWeight q e p = 0 := by
  unfold maskedWeight
  simp [h]

/-- Apply the mask to every weight of a row. -/
def causalWeights (q : Nat) (e : Rat → Rat) (ps : List (Nat × Rat)) : List Rat :=
  ps.map (maskedWeight q e)

theorem causalWeights_length (q : Nat) (e : Rat → Rat)
    (ps : List (Nat × Rat)) : (causalWeights q e ps).length = ps.length := by
  simp [causalWeights]

/-- Zeroing the dropped weights is the same as summing the kept sublist. -/
theorem causalWeights_sum (q : Nat) (e : Rat → Rat) (ps : List (Nat × Rat)) :
    (causalWeights q e ps).sum =
      ((causalRow q ps).map (fun p => e p.2)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      unfold causalRow at ih
      rw [causalWeights, List.map_cons, List.sum_cons, causalRow]
      by_cases h : p.1 ≤ q
      · rw [maskedWeight_kept q e p h]
        have hk : causalKeep q p.1 = true := (causalKeep_iff q p.1).mpr h
        rw [List.filter_cons_of_pos (p := fun r : Nat × Rat => causalKeep q r.1) hk, List.map_cons, List.sum_cons, ← ih]
        rfl
      · rw [maskedWeight_dropped q e p h]
        have hk : ¬ causalKeep q p.1 = true := by
          intro hc
          exact h ((causalKeep_iff q p.1).mp hc)
        rw [List.filter_cons_of_neg (p := fun r : Nat × Rat => causalKeep q r.1) hk, Rat.zero_add, ← ih]
        rfl

end IntelGpu
