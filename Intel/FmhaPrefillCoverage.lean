-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Examples.RealFmhaPrefill
public import Intel.TlaDispatch

@[expose] public section

/-!
# Decoder coverage of the SYCL-TLA FMHA prefill dump

`Intel/Examples/RealFmhaPrefill.lean` is the real prefill kernel (1946
instructions, 1965 statements). This module measures how much of it the
merged GEMM stack already decodes with the total classifier `decodedAll`:

- 1813 of 1965 statements decode (92.3%),
- the 152 that do not are `sel` 66, negated-source `mad` 40, `math.exp` 33,
  `sync.allwr` 8, and the singletons `mov`/`cmp`/`not`/`bfn`/`math.inv`,
- 64 `dpas.8x8 (16|M0)` instructions: 4 use `null` as the second
  accumulator and 60 alias it to the first accumulator.

These counts are the acceptance target for the FMHA stages (issue #250).
-/

namespace IntelGpu

/-- The decoded prefill program. -/
def fmhaPrefillCode : List TlaInstr := decodeTlaProgram realFmhaPrefill

/-- The prefill program with program counters. -/
def fmhaPrefillPc : List (Nat × TlaInstr) := withPcGo fmhaPrefillCode 0

/-- The statements the current stack does not decode. -/
def fmhaUnclassified : List (Nat × TlaInstr) :=
  fmhaPrefillPc.filter (fun p => !decodedAll p.2)

/-- The opcode text of a statement (DPAS and labels get fixed names). -/
def fmhaForm (i : TlaInstr) : String :=
  match i with
  | .predicated op _ => op
  | .plain op _ => op
  | .dpas _ _ _ _ _ _ => "dpas"
  | .label _ => "label"

/-- The per-form census of the unclassified statements. -/
def fmhaFormCensus : List (String × Nat) :=
  [("sel", (fmhaUnclassified.filter (fun p => fmhaForm p.2 = "sel" ||
      fmhaForm p.2 = "(W) sel" || fmhaForm p.2 = "(f3.1) sel")).length),
   ("mad-neg", (fmhaUnclassified.filter (fun p => fmhaForm p.2 = "mad")).length),
   ("math.exp", (fmhaUnclassified.filter (fun p => fmhaForm p.2 = "math.exp")).length),
   ("sync.allwr", (fmhaUnclassified.filter (fun p => fmhaForm p.2 = "sync.allwr")).length),
   ("mov", (fmhaUnclassified.filter (fun p => fmhaForm p.2 = "(W) mov")).length),
   ("cmp", (fmhaUnclassified.filter (fun p => fmhaForm p.2 = "cmp")).length),
   ("not", (fmhaUnclassified.filter (fun p => fmhaForm p.2 = "(W) not")).length),
   ("bfn", (fmhaUnclassified.filter (fun p => fmhaForm p.2 = "(W) bfn.(s0&s1|~s0&s2)")).length),
   ("math.inv", (fmhaUnclassified.filter (fun p => fmhaForm p.2 = "math.inv")).length)]

set_option maxRecDepth 1000000 in
/-- The prefill dump has 1965 statements. -/
theorem fmhaPrefillCode_length : fmhaPrefillCode.length = 1965 := by decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 8000000 in
/-- 1813 statements decode with the merged stack. -/
theorem fmhaPrefill_decoded_count :
    (fmhaPrefillPc.filter (fun p => decodedAll p.2)).length = 1813 := by decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 8000000 in
/-- 152 statements do not decode. -/
theorem fmhaPrefill_unclassified_count : fmhaUnclassified.length = 152 := by decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
/-- The unclassified forms and their counts. -/
theorem fmhaPrefill_unclassified_forms :
    fmhaFormCensus =
      [("sel", 66), ("mad-neg", 40), ("math.exp", 33), ("sync.allwr", 8),
       ("mov", 1), ("cmp", 1), ("not", 1), ("bfn", 1), ("math.inv", 1)] := by
  decide

set_option maxRecDepth 1000000 in
/-- The prefill dump has 64 DPAS instructions. -/
theorem fmhaPrefill_dpas_count :
    (fmhaPrefillPc.filter (fun p => isDpas p.2)).length = 64 := by decide

set_option maxRecDepth 1000000 in
/-- 4 DPAS instructions use `null` as the second accumulator. -/
theorem fmhaPrefill_dpas_null_acc1 :
    (fmhaPrefillPc.filter (fun p => match p.2 with
      | .dpas _ _ acc1 _ _ _ => acc1 = "null:f"
      | _ => false)).length = 4 := by decide

set_option maxRecDepth 1000000 in
/-- 60 DPAS instructions alias the second accumulator to the first. -/
theorem fmhaPrefill_dpas_alias_acc1 :
    (fmhaPrefillPc.filter (fun p => match p.2 with
      | .dpas _ acc0 acc1 _ _ _ => acc1 = acc0
      | _ => false)).length = 60 := by decide

end IntelGpu
