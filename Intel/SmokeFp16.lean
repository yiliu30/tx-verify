-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Fp16Scaled

@[expose] public section

/-!
# Executable checks for the fp16 path

The other smoke modules run the machines. This one runs the decoder and the
scaled value on real bit patterns, including the cases that a wrong
implementation gets wrong: the maximum finite value, the smallest normal, the
smallest subnormal, and a sum that mixes scales.

`decide` evaluates in the kernel, so these are checks on the definitions, not
on a hand-written expectation.
-/

namespace IntelGpu

/-- Signs do not change the magnitude. -/
example : scaled (0xBC00 : Fp16) = scaled (0x3C00 : Fp16) := by decide

/-- The scaled values of A = [1.0, 2.0] and B = [2.0, 1.0] as a depth-2 dot. -/
def bitsA : Nat → Fp16
  | 0 => 0x3C00
  | 1 => 0x4000
  | _ => 0

def bitsB : Nat → Fp16
  | 0 => 0x4000
  | 1 => 0x3C00
  | _ => 0

/-- The exact dot of the two scaled values is `2 ^ 49 + 2 ^ 49`. -/
example :
    accDot (fun k => (scaled (bitsA k) : Int)) (fun k => (scaled (bitsB k) : Int)) 0 2
      = ((2 ^ 24 * 2 ^ 25 : Nat) : Int) + ((2 ^ 25 * 2 ^ 24 : Nat) : Int) := by
  decide

/-- Mixing scales: `1.0` plus the smallest subnormal is `2 ^ 24 + 1` in scaled
units, so the `2 ^ -24` grid holds both without loss. -/
example : scaled (0x3C00 : Fp16) + scaled (0x0001 : Fp16) = 2 ^ 24 + 1 := by decide

/-- The largest finite value times `1.0` is itself. -/
example : scaled (0x7BFF : Fp16) * scaled (0x3C00 : Fp16) = 65504 * 2 ^ 48 := by decide

/-- Every value a normal word decodes to is a multiple of `2 ^ 14` in scaled
units — the numeric layer's grid. -/
example : scaled (0x3C00 : Fp16) % 2 ^ 14 = 0 := by decide
example : scaled (0x7BFF : Fp16) % 2 ^ 14 = 0 := by decide

/-- A subnormal lands below that grid, which is why it cannot be a `Fixed`. -/
example : scaled (0x0001 : Fp16) % 2 ^ 14 = 1 := by decide

end IntelGpu
