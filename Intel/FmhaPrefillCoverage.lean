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

- 1923 of 1965 statements decode (97.9%) after the `sel` decoder of stage
  249 and the plain `cmp`/`not`/`bfn` mux forms of stage 250 (and the
  negated-source and `.v` extensions of stage 248),
- the 42 that do not are `math.exp` 33, `sync.allwr` 8, and `math.inv`,
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

/-- The parsed instruction at a prefill program counter. -/
def fmhaParsedAt (n : Nat) : Option TlaInstr :=
  (fmhaPrefillPc.find? (fun p => p.1 = n)).map (fun p => p.2)

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
/-- 1923 statements decode with the merged stack. -/
theorem fmhaPrefill_decoded_count :
    (fmhaPrefillPc.filter (fun p => decodedAll p.2)).length = 1923 := by decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 8000000 in
/-- 42 statements do not decode. -/
theorem fmhaPrefill_unclassified_count : fmhaUnclassified.length = 42 := by decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
/-- The unclassified forms and their counts. -/
theorem fmhaPrefill_unclassified_forms :
    fmhaFormCensus =
      [("sel", 0), ("mad-neg", 0), ("math.exp", 33), ("sync.allwr", 8),
       ("mov", 0), ("cmp", 0), ("not", 0), ("bfn", 0), ("math.inv", 1)] := by
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

set_option maxRecDepth 1000000 in
/-- PC 1269 is a `mad` with a negated source. -/
theorem fmhaPrefill_madNeg_parsed :
    (fmhaParsedAt 1269).bind parseTlaAluPlain =
      some ⟨.mad, ⟨16, 0, true⟩, .r ⟨22, 0, 0, 1, 1, 1⟩,
        .negReg ⟨4, 0, 3, 0, 0, 0⟩, .reg ⟨69, 0, 0, 1, 1, 0⟩,
        some (.reg ⟨9, 0, 2, 0, 1, 0⟩)⟩ := by decide

set_option maxRecDepth 1000000 in
/-- PC 1165 is a move with a `.v` immediate. -/
theorem fmhaPrefill_movV_parsed :
    (fmhaParsedAt 1165).bind parseTlaMovInstr =
      some ⟨⟨8, 0, true⟩, .reg ⟨4, 0, 0, 1, 1, 1⟩,
        .imm 1985229328 .v⟩ := by decide

set_option maxRecDepth 1000000 in
/-- PC 523 is the `(W) sel` mask select. -/
theorem fmhaPrefill_selW_parsed :
    (fmhaParsedAt 487).bind parseTlaSelInstr =
      some ⟨"(W)", ⟨1, 0, true⟩, "(ge)f0.0", .r ⟨1, 0, 10, 1, 1, 1⟩,
        .src (.reg ⟨1, 0, 12, 0, 1, 0⟩), .src (.imm 0 .w16)⟩ := by decide

set_option maxRecDepth 1000000 in
/-- PC 1206 is the outer-predicated `(f3.1) sel`. -/
theorem fmhaPrefill_selOuter_parsed :
    (fmhaParsedAt 1170).bind parseTlaSelInstr =
      some ⟨"(f3.1)", ⟨16, 0, true⟩, "", .acc 0 0,
        .src (.reg ⟨2, 0, 2, 0, 1, 0⟩), .src (.imm 4286578688 .d32)⟩ := by decide

set_option maxRecDepth 1000000 in
/-- PC 1207 is a plain `sel` with an accumulator-bank source. -/
theorem fmhaPrefill_sel_parsed :
    (fmhaParsedAt 1171).bind parseTlaSelInstr =
      some ⟨"", ⟨16, 0, true⟩, "(lt)f0.0", .r ⟨66, 0, 0, 1, 1, 1⟩,
        .src (.reg ⟨66, 0, 0, 1, 1, 0⟩), .acc 0 0⟩ := by decide

set_option maxRecDepth 1000000 in
/-- 66 prefill statements are `sel`. -/
theorem fmhaPrefill_sel_count :
    (fmhaPrefillPc.filter (fun p => (parseTlaSelInstr p.2).isSome)).length = 66 := by decide

set_option maxRecDepth 1000000 in
/-- PC 23 is the `bfn` mux form. -/
theorem fmhaPrefill_bfnMux_parsed :
    (fmhaParsedAt 23).bind parseTlaBfn =
      some ⟨⟨1, 0, true⟩, .reg ⟨1, 0, 11, 1, 1, 1⟩,
        .reg ⟨1, 0, 10, 0, 0, 0⟩, .reg ⟨6, 0, 7, 0, 0, 0⟩,
        .reg ⟨1, 0, 11, 0, 1, 0⟩, .mux⟩ := by decide

set_option maxRecDepth 1000000 in
/-- PC 24 is the plain `not`. -/
theorem fmhaPrefill_not_parsed :
    (fmhaParsedAt 24).bind parseTlaAluInstr =
      some ⟨.not, ⟨1, 0, true⟩, .r ⟨1, 0, 10, 1, 1, 1⟩,
        .reg ⟨6, 0, 6, 0, 1, 0⟩, .imm 0 .d32, none⟩ := by decide

set_option maxRecDepth 1000000 in
/-- PC 1169 is the plain `cmp`. -/
theorem fmhaPrefill_plainCmp_parsed :
    (fmhaParsedAt 1169).bind parseTlaCmpInstr =
      some ⟨"", ⟨16, 0, true⟩, "lt", 3, 1,
        .reg ⟨4, 0, 0, 1, 1, 0⟩, .reg ⟨2, 0, 6, 0, 1, 0⟩⟩ := by decide

set_option maxRecDepth 1000000 in
/-- Exactly one prefill statement is the `bfn` mux form. -/
theorem fmhaPrefill_bfnMux_count :
    (fmhaPrefillPc.filter (fun p => match p.2 with
      | .predicated "(W) bfn.(s0&s1|~s0&s2)" _ => true
      | _ => false)).length = 1 := by decide

set_option maxRecDepth 1000000 in
/-- Exactly one prefill statement is a plain `not`. -/
theorem fmhaPrefill_not_count :
    (fmhaPrefillPc.filter (fun p => match p.2 with
      | .predicated "(W) not" _ => true
      | _ => false)).length = 1 := by decide

set_option maxRecDepth 1000000 in
/-- Exactly one prefill statement is a plain `cmp`. -/
theorem fmhaPrefill_plainCmp_count :
    (fmhaPrefillPc.filter (fun p => match p.2 with
      | .plain "cmp" _ => true
      | _ => false)).length = 1 := by decide

end IntelGpu
