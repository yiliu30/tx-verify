-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.MainloopTail
public import Intel.EpilogueLd
public import Intel.RoundingEven

@[expose] public section

/-!
# Executable smoke tests

Everything in this development is a `def`, so the machines can be run. These
examples execute the real definitions — staging, barrier, DPAS, tail, epilogue
— on tiny inputs and check the arithmetic, which is evidence that the model is
not vacuous.

`decide` evaluates the definitions in the kernel; no proof search is involved.
-/

namespace IntelGpu

/-- Memory holding `A = [3, 4]` at `0, 1` and `B = [5, 6]` at `2, 3`. -/
def smokeMem : Nat → Word
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 6
  | _ => 0

/-- One `1 x 1` output tile, depth `1` per slab, A row-major with `ldA = 1`,
B row-major with `ldB = 1`. -/
def smokeGeom : Geom :=
  { aBase := 0, ldA := 1, bBase := 2, ldB := 1, i := 0, j := 0,
    d := 1, M := 1, N := 1 }

/-- Two slabs of depth 1 accumulate `3 * 5 + 4 * 6 = 39`. -/
example :
    (krun smokeGeom (mainloopProg 2) (8 * 2 + 3) (kHead smokeMem (fun _ _ => 0))).acc 0 0 = 39 := by
  decide

/-- The same total through one full slab plus a depth-1 tail. -/
example :
    (krun smokeGeom (tailProg 1 1) 4
        { krun smokeGeom (mainloopProg 1) (8 * 1 + 3) (kHead smokeMem (fun _ _ => 0)) with
          pc := 0 }).acc 0 0 = 39 := by
  decide

/-- The epilogue writes the accumulator to the tile's C block. -/
example :
    (lrun 0 1 1 (epilogueProg 1) 8 (eHead (fun _ => 0) (fun _ _ => 39))).mem 0 = 39 := by
  decide

/-- Rounding: nearest, ties to even, on the quantum-8 grid. -/
example : truncQ 8 (37 : Int) = 32 := by decide
example : roundQ 8 (37 : Int) = 40 := by decide
example : roundEven 8 (35 : Int) = 32 := by decide

end IntelGpu
