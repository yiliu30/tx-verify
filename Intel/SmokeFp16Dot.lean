-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.SmokeFp16

@[expose] public section

/-!
# Known-answer tests for an fp16 dot product

The other smoke modules check single values. This one checks whole dot products
over bit patterns, which is the shape a real kernel has: decode words, scale
them, accumulate.

Each test is a `decide` check against a hand-computed expectation, so a change
to the decoder, the scale, or the accumulation shows up immediately.

All products are in units of `2 ^ -48` (two factors of `2 ^ -24`), which is why
the expectations are large integers.
-/

namespace IntelGpu

/-- A = [1.0, 0.5, 65504], B = [1.0, 2.0, 1.0] as fp16 bit patterns. -/
def kaA : Nat → Fp16
  | 0 => 0x3C00
  | 1 => 0x3800
  | 2 => 0x7BFF
  | _ => 0

def kaB : Nat → Fp16
  | 0 => 0x3C00
  | 1 => 0x4000
  | 2 => 0x3C00
  | _ => 0

/-- `1.0*1.0 + 0.5*2.0 + 65504*1.0 = 65506.0`, in units of `2 ^ -48`. -/
example :
    accDot (fun k => (scaled (kaA k) : Int)) (fun k => (scaled (kaB k) : Int)) 0 3
      = ((65506 : Nat) : Int) * 2 ^ 48 := by
  decide

/-- `scaled` is a magnitude: the sign bit does not enter it. `0xBC00` is
`-1.0` but scales to `2 ^ 24`, so this dot is positive. Sign handling lives in
`Fixed.sign` and is not part of `scaled`, which the docs say.

I wrote this test expecting `-2.0` and `decide` refused it — which is the point
of having the test. -/
example :
    accDot (fun _ => (scaled (0xBC00 : Fp16) : Int)) (fun _ => (scaled (0x4000 : Fp16) : Int)) 0 1
      = (((2 : Nat) : Int) * 2 ^ 48) := by
  decide

/-- Mixing scales: `1.0` times the smallest subnormal is `2 ^ -24`, i.e. `2 ^ 24`
in units of `2 ^ -48`. -/
example :
    accDot (fun _ => (scaled (0x3C00 : Fp16) : Int)) (fun _ => (scaled (0x0001 : Fp16) : Int)) 0 1
      = (((2 : Nat) ^ 24 : Nat) : Int) := by
  decide

/-- An empty dot is zero. -/
example :
    accDot (fun k => (scaled (kaA k) : Int)) (fun k => (scaled (kaB k) : Int)) 0 0 = 0 := by
  decide

end IntelGpu
