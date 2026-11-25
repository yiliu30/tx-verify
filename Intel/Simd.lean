-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.AddOne
public import Intel.Divergence

@[expose] public section

/-!
# A SIMD lane dimension

The ledger's assumption 2 says the development has one lane per step: the
machines of stages 1-57 are scalar, and SIMD masks and GRF regions are not
modelled. This module adds the lane dimension on top of the scalar core, with
predication:

- `Simd`: per-lane scalar states, a width, and a mask.
- `simdRun`: each lane runs the program if its mask bit is set, otherwise it is
  untouched — predication, not branching.
- `simdRun_active` / `simdRun_masked`: an active lane sees exactly the scalar
  result; a masked lane is unchanged.
- `add_one_simd`: the stage-1 proof lifts to every active lane unchanged.

So the scalar theorems apply per lane rather than being re-derived, which is
what the scalar model was for. GRF regions and sub-group packing are still not
modelled, and the ledger says so.
-/

namespace IntelGpu

/-- A workgroup of `width` scalar lanes with an execution mask. -/
structure Simd where
  width : Nat
  lanes : Nat → State
  mask : Nat → Bool

/-- Run a program on every active lane. -/
def simdRun (is : List Instr) (s : Simd) : Simd :=
  { s with lanes := fun l => if s.mask l then run (s.lanes l) is else s.lanes l }

/-- An active lane sees exactly the scalar result. -/
theorem simdRun_active (is : List Instr) (s : Simd) (l : Nat) (h : s.mask l = true) :
    (simdRun is s).lanes l = run (s.lanes l) is := by
  simp [simdRun, h]

/-- A masked lane is untouched: predication, not a branch. -/
theorem simdRun_masked (is : List Instr) (s : Simd) (l : Nat) (h : s.mask l = false) :
    (simdRun is s).lanes l = s.lanes l := by
  simp [simdRun, h]

/-- `add_one` on the SIMD machine: every active lane writes its own `v + 1`, and
masked lanes are left alone. -/
theorem add_one_simd (s : Simd) (addr : Nat → Addr) (word : Nat → Word) (l : Nat)
    (h : s.mask l = true) (hpre : AddOnePre (s.lanes l) (addr l) (word l)) :
    ((simdRun core s).lanes l).halted = true ∧
      load32 ((simdRun core s).lanes l).mem (addr l).toNat = word l + 1 := by
  rw [simdRun_active core s l h]
  exact ⟨(core_correct (s.lanes l) (addr l) (word l) hpre).1,
    (core_correct (s.lanes l) (addr l) (word l) hpre).2.1⟩

/-- A masked lane keeps its old memory. -/
theorem add_one_simd_masked (s : Simd) (l : Nat) (h : s.mask l = false) :
    ((simdRun core s).lanes l).mem = (s.lanes l).mem := by
  rw [simdRun_masked core s l h]

end IntelGpu
