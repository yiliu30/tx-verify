-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Fp32Rounding

@[expose] public section

/-!
# The DPAS accumulator with FP32-quantum rounding

`dpasAccF32` rounds every partial sum to the FP32 quantum of its own
magnitude (`f32Round`). When the sum of the absolute products plus the
initial accumulator stays below `2 ^ 24`, every partial sum is on the unit
grid, and the accumulator equals the exact integer slab sum. Above that
bound rounding can change the result: a single product `2 ^ 24 + 3` rounds to
`2 ^ 24 + 4`.
-/

namespace IntelGpu

/-- The sum of the absolute products of a depth-`d` slab. -/
def prodAbsSum : Nat → (Nat → Nat → Int) → (Nat → Nat → Int) → Nat → Nat → Nat
  | 0, _, _, _, _ => 0
  | d + 1, A, B, m, n =>
      (A 0 m * B 0 n).natAbs +
        prodAbsSum d (fun k m' => A (k + 1) m') (fun k n' => B (k + 1) n') m n

/-- The accumulator with FP32-quantum rounding at every step. -/
def dpasAccF32 : Nat → (Nat → Nat → Int) → (Nat → Nat → Int) →
    Nat → Nat → Int → Int
  | 0, _, _, _, _, C => C
  | d + 1, A, B, m, n, C =>
      dpasAccF32 d (fun k m' => A (k + 1) m') (fun k n' => B (k + 1) n') m n
        (f32Round (C + A 0 m * B 0 n))

/-- Below `2 ^ 24` of total absolute magnitude the FP32-quantum accumulator is
the exact integer slab sum. -/
theorem dpasAccF32_eq_slab (d : Nat) (A B : Nat → Nat → Int) (m n : Nat) (C : Int)
    (h : C.natAbs + prodAbsSum d A B m n < 2 ^ 24) :
    dpasAccF32 d A B m n C = slabSum d A B m n C := by
  induction d generalizing A B C with
  | zero => rfl
  | succ d ih =>
      have htri : (C + A 0 m * B 0 n).natAbs ≤
          C.natAbs + (A 0 m * B 0 n).natAbs := Int.natAbs_add_le _ _
      have hsum1 : (C + A 0 m * B 0 n).natAbs < 2 ^ 24 := by
        simp only [prodAbsSum] at h
        omega
      have hIH : (C + A 0 m * B 0 n).natAbs +
          prodAbsSum d (fun k m' => A (k + 1) m') (fun k n' => B (k + 1) n') m n < 2 ^ 24 := by
        simp only [prodAbsSum] at h
        omega
      have hstep : f32Round (C + A 0 m * B 0 n) = C + A 0 m * B 0 n :=
        f32Round_small _ hsum1
      simp only [dpasAccF32, slabSum]
      rw [hstep]
      exact ih (fun k m' => A (k + 1) m') (fun k n' => B (k + 1) n')
        (C + A 0 m * B 0 n) hIH

/-- A single product above the FP32 grid rounds: `2 ^ 24 + 3` becomes
`2 ^ 24 + 4`. -/
theorem dpasAccF32_rounds_large :
    dpasAccF32 1 (fun _ _ => 1) (fun _ _ => (2 : Int) ^ 24 + 3) 0 0 0 =
        (2 : Int) ^ 24 + 4 ∧
      slabSum 1 (fun _ _ => 1) (fun _ _ => (2 : Int) ^ 24 + 3) 0 0 0 =
        (2 : Int) ^ 24 + 3 := by
  constructor <;> decide

/-- A small slab stays exact: two products of `2 * 3` plus `7` is `19`. -/
theorem dpasAccF32_small_exact :
    dpasAccF32 2 (fun _ _ => 2) (fun _ _ => 3) 0 0 7 = 19 ∧
      slabSum 2 (fun _ _ => 2) (fun _ _ => 3) 0 0 7 = 19 := by
  constructor
  · rw [dpasAccF32_eq_slab]
    · decide
    · decide
  · decide

end IntelGpu
