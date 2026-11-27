-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.RoundingEven
public import Intel.Dpas

@[expose] public section

/-!
# Rounding-aware DPAS accumulation

`dpasSlab` accumulates in `Word` arithmetic without rounding. This module adds
a rounding-aware accumulator on exact integers: each step rounds
`C + A*B` to a quantum `q` with ties-to-even. On the unit grid (`q = 1`) the
accumulator is exactly the integer slab sum; on a coarser grid a tie rounds
away from the exact value.
-/

namespace IntelGpu

/-- The exact integer slab accumulation at tile position `(m, n)`. -/
def slabSum : Nat → (Nat → Nat → Int) → (Nat → Nat → Int) → Nat → Nat → Int → Int
  | 0, _, _, _, _, C => C
  | d + 1, A, B, m, n, C =>
      slabSum d (fun k m' => A (k + 1) m') (fun k n' => B (k + 1) n') m n
        (C + A 0 m * B 0 n)

/-- The rounding-aware accumulation at quantum `q`. -/
def dpasAccR (q : Nat) : Nat → (Nat → Nat → Int) → (Nat → Nat → Int) →
    Nat → Nat → Int → Int
  | 0, _, _, _, _, C => C
  | d + 1, A, B, m, n, C =>
      dpasAccR q d (fun k m' => A (k + 1) m') (fun k n' => B (k + 1) n') m n
        (roundEven q (C + A 0 m * B 0 n))

/-- Rounding at the unit quantum is the identity. -/
theorem roundEven_one (x : Int) : roundEven 1 x = x := by
  unfold roundEven
  by_cases h : 0 ≤ x
  · rw [ite_eq_left h]
    have hr : roundEvenNat 1 x.toNat = x.toNat := by
      rw [roundEvenNat_notie 1 x.toNat (by simp)]
      simp
    rw [hr, Int.toNat_of_nonneg h]
  · rw [ite_eq_right h]
    have hx : 0 ≤ -x := by omega
    have hr : roundEvenNat 1 (-x).toNat = (-x).toNat := by
      rw [roundEvenNat_notie 1 (-x).toNat (by simp)]
      simp
    rw [hr, Int.toNat_of_nonneg hx]
    omega

/-- On the unit grid the rounding-aware accumulator is the exact slab sum. -/
theorem dpasAccR_one (d : Nat) (A B : Nat → Nat → Int) (m n : Nat) (C : Int) :
    dpasAccR 1 d A B m n C = slabSum d A B m n C := by
  induction d generalizing A B C with
  | zero => rfl
  | succ d ih =>
      simp only [dpasAccR, slabSum]
      rw [roundEven_one]
      exact ih (fun k m' => A (k + 1) m') (fun k n' => B (k + 1) n') (C + A 0 m * B 0 n)

/-- On a quantum-2 grid a tie rounds away from the exact sum: `3` rounds to
`4`, while the exact slab is `3`. -/
theorem dpasAccR_quantum2_tie :
    dpasAccR 2 1 (fun _ _ => 3) (fun _ _ => 1) 0 0 0 = 4 ∧
      slabSum 1 (fun _ _ => 3) (fun _ _ => 1) 0 0 0 = 3 := by
  constructor <;> decide

/-- Two exact steps stay exact on the unit grid. -/
theorem slabSum_two :
    slabSum 2 (fun _ _ => 3) (fun _ _ => 5) 0 0 7 = 37 := by
  decide

end IntelGpu
