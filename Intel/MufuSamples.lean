-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaMath

@[expose] public section

/-!
# Measured MUFU samples

Per-op maxima from a 2^20-point sweep on the lab GPU (oneAPI 2026.1,
`sycl::exp`, `1.0f/x`, `sycl::log`, checked against a double-precision host
reference; the dumped kernels contain `math.exp`, `math.inv` and `math.log`).

These are the measured budgets available to instantiate `MufuModel.expErr`,
`invErr` and `logErr`; they are relative-error maxima except for the absolute
columns.
-/

namespace IntelGpu

/-- The measured MUFU maxima, as exact rationals. -/
structure MufuSamples where
  expMaxAbs : Rat
  expMaxRel : Rat
  invMaxAbs : Rat
  invMaxRel : Rat
  logMaxAbs : Rat
  logMaxRel : Rat

/-- The 2^20-point lab-GPU sweep. -/
def labMufuSamples : MufuSamples where
  expMaxAbs := 1170085644 / 10000000000000000
  expMaxRel := 1984444714 / 10000000000000000
  invMaxAbs := 1495941174 / 100000000000000
  invMaxRel := 1153888151 / 10000000000000000
  logMaxAbs := 2737414819 / 10000000000000000
  logMaxRel := 7661312768 / 100000000000000000

theorem labMufuSamples_fields :
    labMufuSamples.expMaxAbs = 1170085644 / 10000000000000000 ∧
    labMufuSamples.expMaxRel = 1984444714 / 10000000000000000 ∧
    labMufuSamples.invMaxAbs = 1495941174 / 100000000000000 ∧
    labMufuSamples.invMaxRel = 1153888151 / 10000000000000000 ∧
    labMufuSamples.logMaxAbs = 2737414819 / 10000000000000000 ∧
    labMufuSamples.logMaxRel = 7661312768 / 100000000000000000 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end IntelGpu
