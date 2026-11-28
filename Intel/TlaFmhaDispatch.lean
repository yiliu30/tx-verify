-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaDispatch
public import Intel.TlaFmhaDpasBase

@[expose] public section

/-!
# The FMHA dispatcher

The generic classifier uses `parseTlaDpas`, which rejects the printed `null`
second accumulator. The FMHA prefill atoms use `parseFmhaDpas` instead, so
this module adds an FMHA classifier (DPAS first, generic classes otherwise)
and the corresponding step.
-/

namespace IntelGpu

/-- Classify an instruction with the null-tolerant FMHA DPAS parser first. -/
def classifyFmha (i : TlaInstr) : TlaOp :=
  match parseFmhaDpas i with
  | some d => .fmhaDpas d
  | none => classifyOp i

theorem classifyFmha_dpas (i : TlaInstr) (d : FmhaDpas)
    (h : parseFmhaDpas i = some d) : classifyFmha i = .fmhaDpas d := by
  simp [classifyFmha, h]

/-- Execute one instruction with the FMHA classifier. -/
def tlaStepFmha? (m : TlaFullMachine) (i : TlaInstr) :
    Option (TlaFullMachine × TlaCtl) :=
  tlaStepWith classifyFmha m i

theorem tlaStepFmha?_fmhaDpas (m : TlaFullMachine) (i : TlaInstr) (d : FmhaDpas)
    (h : classifyFmha i = .fmhaDpas d) :
    tlaStepFmha? m i =
      some ({ m with state := { m.state with regs := fmhaAtomStep m.state.regs d } },
        .next) := by
  simp [tlaStepFmha?, tlaStepWith, h]

end IntelGpu
