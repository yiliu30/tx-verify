-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.FmhaPrefillCoverage
public import Intel.TlaFmhaPv
public import Intel.TlaFmhaQk
public import Intel.TlaBf16Rne
public import Intel.TlaFmhaPvCensus
public import Intel.TlaFmhaSchedule
public import Intel.FmhaLseCoverage
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

/-- The four QK^T accumulator groups and the PV group. -/
def FmhaQkSummary : Prop :=
  (qkGroup 42).length = 8 ∧ (qkGroup 50).length = 8 ∧
  (qkGroup 58).length = 8 ∧ (qkGroup 66).length = 8 ∧ pv74.length = 2

theorem fmha_qk_summary : FmhaQkSummary :=
  ⟨qk42_length, qk50_length, qk58_length, qk66_length, pv74_length⟩

/-- The P->BF16 conversion: idempotent, packed, and the RNE boundaries. -/
def FmhaConvertSummary : Prop :=
  (∀ b : Bf16, bf16RoundWord (bf16ToWord b) = bf16ToWord b) ∧
  (∀ w : Word, bf16RoundWord w = (w &&& 0xFFFF0000) ∨
    bf16RoundWord w = (w &&& 0xFFFF0000) + 0x10000) ∧
  bf16Round 0x3F808000 = 0x3F80 ∧
  bf16Round 0x3F818000 = 0x3F82 ∧
  bf16Round 0x3F80C000 = 0x3F81

theorem fmha_convert_summary : FmhaConvertSummary :=
  ⟨bf16RoundWord_packed, bf16RoundWord_trunc_or_succ,
   bf16Round_tie_even_down, bf16Round_tie_even_up, bf16Round_above_half⟩

/-- Every statement is classified and has a dispatcher step. -/
def FmhaExecSummary : Prop :=
  fmhaPrefillPc.all (fun p =>
    (match classifyFmha p.2 with | .other => false | _ => true)) = true ∧
  fmhaPrefillPc.all (fun p => (tlaStepFmha? canonMachine p.2).isSome) = true

theorem fmha_exec_summary : FmhaExecSummary :=
  ⟨fmhaPrefill_classified, fmhaPrefill_step_total⟩

/-- All 16 PV groups are covered by the chain theorem. -/
def FmhaPvCensusSummary : Prop :=
  pvAccs.length = 16 ∧ (pvDpas.all (fun d => decide (d.acc0 ∈ pvAccs))) = true ∧
  (∀ a : Nat, a ∈ pvAccs → (pvGroup a).length = 2)

theorem fmha_pv_census_summary : FmhaPvCensusSummary :=
  ⟨by decide, pvDpas_accs_mem, fun a ha => pvGroup_length_of_mem ha⟩

/-- The pipeline order: QK^T, exp, PV, inv. -/
def FmhaScheduleSummary : Prop :=
  qkDpasPcs.length = 32 ∧ pvDpasPcs.length = 32 ∧ expPcs.length = 33 ∧
  qkDpasPcs.all (fun pc => pc < 1272) = true ∧
  expPcs.all (fun pc => 1272 ≤ pc && pc ≤ 1412) = true ∧
  pvDpasPcs.all (fun pc => 1456 ≤ pc && pc ≤ 1654) = true ∧
  invPcs = [1774]

theorem fmha_schedule_summary : FmhaScheduleSummary :=
  ⟨qkDpasPcs_length, pvDpasPcs_length, expPcs_length, qkDpasPcs_before_exp,
   expPcs_range, pvDpasPcs_range, invPcs_eq⟩

/-- LSE model support: `math.log` parses and log inverts exp in the epilogue. -/
def FmhaLseSummary : Prop :=
  (∀ (logRef e : Rat → Rat), (∀ x, logRef (e x) = x) →
    ∀ m x, lseOut logRef m (e (x - m)) = x) ∧
  parseTlaMath (.plain "math.log"
    ["(16|M0)", "r4.0<1>:f", "r4.0<1;1,0>:f", "{F@1}"]) =
    some ⟨.log, ⟨16, 0, true⟩, ⟨4, 0, 0, 1, 1, 1⟩,
      .reg ⟨4, 0, 0, 1, 1, 0⟩⟩

theorem fmha_lse_summary : FmhaLseSummary :=
  ⟨lseOut_single, parseTlaMath_log⟩

/-- Every FMHA DPAS operand is BF16. -/
def FmhaBf16Summary : Prop :=
  (fmhaPrefillPc.filter (fun p => isDpas p.2)).all (fun p =>
    match p.2 with
    | .dpas _ _ _ b a _ => endsWithBf b && endsWithBf a
    | _ => false) = true

theorem fmha_bf16_summary : FmhaBf16Summary := fmhaPrefill_dpas_bf16

/-- The LSE dump is fully decoded and executable. -/
def FmhaLseDumpSummary : Prop :=
  lseCode.length = 2694 ∧
  (lsePc.filter (fun p => decodedAll p.2)).length = 2694 ∧
  lseUnclassified.length = 0 ∧
  (lsePc.filter (fun p => isDpas p.2)).length = 64 ∧
  (lsePc.filter (fun p => match parseTlaMath p.2 with
    | some m => m.op = .log | none => false)).length = 16 ∧
  lsePc.all (fun p => (tlaStepFmha? canonMachine p.2).isSome) = true

theorem fmha_lse_dump_summary : FmhaLseDumpSummary :=
  ⟨lseCode_length, lse_decoded_count, lse_unclassified_count, lse_dpas_count,
   lse_log_count, lse_step_total⟩

/-- The headline checklist. -/
theorem fmha_prefill_summary :
    FmhaDecodeSummary ∧ FmhaScalarSummary ∧ FmhaPhaseSummary ∧ FmhaQkSummary ∧
    FmhaConvertSummary ∧ FmhaExecSummary ∧ FmhaPvCensusSummary ∧
    FmhaScheduleSummary ∧ FmhaLseSummary ∧ FmhaBf16Summary ∧ FmhaLseDumpSummary :=
  ⟨fmha_decode_summary, fmha_scalar_summary, fmha_phase_summary, fmha_qk_summary,
   fmha_convert_summary, fmha_exec_summary, fmha_pv_census_summary,
   fmha_schedule_summary, fmha_lse_summary, fmha_bf16_summary,
   fmha_lse_dump_summary⟩

end IntelGpu
