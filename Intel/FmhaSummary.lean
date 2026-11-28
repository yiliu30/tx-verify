-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.FmhaPrefillCoverage
public import Intel.TlaFmhaPv
public import Intel.TlaEpilogue
public import Intel.TlaMask

@[expose] public section

/-!
# FMHA prefill verification summary

A machine-checked checklist of what the stack proves about the real
SYCL-TLA FMHA prefill dump. Each conjunct is a theorem from the stage
modules; the HTML review artifact `visualization/fmha.html` renders the same
list with the open gaps.
-/

namespace IntelGpu

/-- Decoding is total and the math census is exact. -/
def FmhaDecodeSummary : Prop :=
    fmhaPrefillPc.all (fun p => decodedAll p.2) = true ∧
    fmhaMath.length = 34 ∧
    (fmhaMath.filter (fun m => m.op = .exp)).length = 33 ∧
    (fmhaMath.filter (fun m => m.op = .inv)).length = 1

theorem fmha_decode_summary : FmhaDecodeSummary :=
  ⟨fmhaPrefill_decoded_all, fmhaPrefill_math_count,
   fmhaPrefill_math_exp_count, fmhaPrefill_math_inv_count⟩

/-- The scalar-form census of the other stages. -/
def FmhaScalarSummary : Prop :=
    (fmhaPrefillPc.filter (fun p => (parseTlaSelInstr p.2).isSome)).length = 66 ∧
    fmhaSyncAllwr.length = 8 ∧
    (fmhaPrefillPc.filter (fun p => match p.2 with
      | .predicated "(W) bfn.(s0&s1|~s0&s2)" _ => true
      | _ => false)).length = 1

theorem fmha_scalar_summary : FmhaScalarSummary :=
  ⟨fmhaPrefill_sel_count, fmhaPrefill_syncAllwr_count,
   fmhaPrefill_bfnMux_count⟩

/-- The DPAS phase split and the PV chain instance. -/
def FmhaPhaseSummary : Prop :=
    fmhaDpas.length = 64 ∧
    (fmhaDpas.filter (fun d => d.acc1 = none)).length = 4 ∧
    (fmhaDpas.filter (fun d => d.acc1 = some d.acc0)).length = 60 ∧
    qkDpas.length = 32 ∧ pvDpas.length = 32 ∧ pv74.length = 2

theorem fmha_phase_summary : FmhaPhaseSummary :=
  ⟨fmhaDpas_length, fmhaDpas_null_count, fmhaDpas_alias_count,
   qkDpas_length, pvDpas_length, pv74_length⟩

/-- The headline checklist. -/
theorem fmha_prefill_summary :
    FmhaDecodeSummary ∧ FmhaScalarSummary ∧ FmhaPhaseSummary :=
  ⟨fmha_decode_summary, fmha_scalar_summary, fmha_phase_summary⟩

end IntelGpu
