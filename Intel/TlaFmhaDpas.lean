-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaFmhaDpasBase
public import Intel.Examples.RealFmhaPrefill

@[expose] public section

/-!
# FMHA prefill DPAS atoms

The prefill dump has 64 `dpas.8x8 (16|M0)` instructions. Their second
accumulator is either `null` (4 forms) or the same register block as the
first (60 forms), so every one of them accumulates once into `acc0`. This
module decodes that shape, splits the atoms into the 32 QK^T and 32 PV
atoms, and gives the single-accumulator step its slab value and frame.

The chain composition over the whole phase is the next stage.
-/

namespace IntelGpu

/-- The 64 DPAS atoms of the prefill dump. -/
def fmhaDpas : List FmhaDpas :=
  (decodeTlaProgram realFmhaPrefill).filterMap parseFmhaDpas

set_option maxRecDepth 1000000 in
theorem fmhaDpas_length : fmhaDpas.length = 64 := by decide

set_option maxRecDepth 1000000 in
/-- 4 atoms print `null` as the second accumulator. -/
theorem fmhaDpas_null_count :
    (fmhaDpas.filter (fun d => d.acc1 = none)).length = 4 := by decide

set_option maxRecDepth 1000000 in
/-- 60 atoms alias the second accumulator to the first. -/
theorem fmhaDpas_alias_count :
    (fmhaDpas.filter (fun d => d.acc1 = some d.acc0)).length = 60 := by decide

set_option maxRecDepth 1000000 in
/-- Every atom is either `null` or aliased. -/
theorem fmhaDpas_acc1_ok :
    fmhaDpas.all (fun d => d.acc1 = none || d.acc1 = some d.acc0) = true := by
  decide

/-- The QK^T atoms accumulate into `r42..r66`. -/
def qkDpas : List FmhaDpas := fmhaDpas.filter (fun d => d.acc0 ≤ 66)

/-- The PV atoms accumulate into `r74..r194`. -/
def pvDpas : List FmhaDpas := fmhaDpas.filter (fun d => 66 < d.acc0)

set_option maxRecDepth 1000000 in
theorem qkDpas_length : qkDpas.length = 32 := by decide

set_option maxRecDepth 1000000 in
theorem pvDpas_length : pvDpas.length = 32 := by decide

end IntelGpu
