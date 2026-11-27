-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.DpasRounding

@[expose] public section

/-!
# FP32-style exponent-relative rounding

The DPAS accumulator is FP32: the rounding quantum shrinks with the
magnitude. This module models that quantum, `f32Quantum x = 2^(log2 x - 23)`
(with quantum one below `2^24`), and the induced rounding `f32Round`.

Below `2^24` the quantum is one and rounding is exact; at `2^24` the quantum
is two, and `2^24 + 3` rounds (ties-to-even) to `2^24 + 4`.
-/

namespace IntelGpu

/-- The FP32 spacing at magnitude `x`. -/
def f32Quantum (x : Nat) : Nat :=
  if x = 0 then 1
  else if x < 2 ^ 24 then 1
  else 2 ^ (x.log2 - 23)

theorem f32Quantum_small (x : Nat) (h : x < 2 ^ 24) : f32Quantum x = 1 := by
  unfold f32Quantum
  by_cases h0 : x = 0
  · simp [h0]
  · simp [h0, h]

/-- Round to the FP32 grid at the value's own magnitude. -/
def f32Round (x : Int) : Int := roundEven (f32Quantum x.natAbs) x

theorem f32Round_small (x : Int) (h : x.natAbs < 2 ^ 24) : f32Round x = x := by
  unfold f32Round
  rw [f32Quantum_small x.natAbs h, roundEven_one]

theorem f32Quantum_zero : f32Quantum 0 = 1 := by decide

theorem f32Quantum_large : f32Quantum (2 ^ 24 + 3) = 2 := by decide

/-- `2^24 + 3` is the odd multiple of the quantum two, so ties-to-even rounds
it up to `2^24 + 4`. -/
theorem f32Round_large : f32Round ((2 : Int) ^ 24 + 3) = (2 : Int) ^ 24 + 4 := by
  decide

/-- Small negative values round exactly too. -/
theorem f32Round_small_neg : f32Round (-((2 : Int) ^ 23 + 7)) = -((2 : Int) ^ 23 + 7) := by
  apply f32Round_small
  decide

end IntelGpu
