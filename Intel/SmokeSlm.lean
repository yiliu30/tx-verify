-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.GemmSlmCompute
public import Intel.Smoke

@[expose] public section

/-!
# Executable checks for the workgroup stages

`Intel/Smoke.lean` runs the mainloop, tail and epilogue machines. This module
runs the stage-16/17 workgroup machines — two-lane SLM staging, the barrier,
and the SLM compute loop — on the same tiny GEMM.

With `K = 2`, A rows `[3, 4]` and `[5, 6]` in memory at `0..3`, and the B
column `[12, 13]` at `4, 5`, lane 0 computes its own row's dot,
`3*12 + 4*13 = 88`, and lane 1 computes `5*12 + 6*13 = 138`.
-/

namespace IntelGpu

/-- Two lanes: lane 0 owns global/SLM words from 0, lane 1 from 2. -/
def smokeLanes : Nat → Lane
  | 0 => { regs := fun _ => 0, gidx := 0, sidx := 0, done := false }
  | _ => { regs := fun _ => 0, gidx := 2, sidx := 2, done := false }

/-- `mem` holds A = [3, 4] then [5, 6] at `0..3`, and B = [12, 13] at `4, 5`. -/
def smokeWMem : Nat → Word
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 6
  | 4 => 12
  | 5 => 13
  | _ => 0

def smokeW : WState :=
  { lanes := smokeLanes, mem := smokeWMem, slm := fun _ => 0, phase := 0 }

/-- Staging plus the barrier leaves both rows in SLM. -/
example : (wrun smokeW (stageProg 2 ++ [.barrier])).slm 0 = 3 := by decide
example : (wrun smokeW (stageProg 2 ++ [.barrier])).slm 1 = 4 := by decide
example : (wrun smokeW (stageProg 2 ++ [.barrier])).slm 2 = 5 := by decide
example : (wrun smokeW (stageProg 2 ++ [.barrier])).slm 3 = 6 := by decide
example : (wrun smokeW (stageProg 2 ++ [.barrier])).phase = 1 := by decide

/-- The stage-17 compute loop turns the staged tile into the dot product. -/
example :
    ((crun (computeProg 2) (10 * 2 + 3)
        (computeInit 2 (wrun smokeW (stageProg 2 ++ [.barrier])))).w.lanes 0).regs 4 = 88 := by
  decide

example :
    ((crun (computeProg 2) (10 * 2 + 3)
        (computeInit 2 (wrun smokeW (stageProg 2 ++ [.barrier])))).w.lanes 1).regs 4 = 138 := by
  decide

/-- The compute loop halts. -/
example :
    (crun (computeProg 2) (10 * 2 + 3)
      (computeInit 2 (wrun smokeW (stageProg 2 ++ [.barrier])))).halted = true := by
  decide

end IntelGpu
