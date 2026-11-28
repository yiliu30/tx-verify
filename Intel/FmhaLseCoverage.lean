-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Examples.RealFmhaLse
public import Intel.TlaFmhaDispatch

@[expose] public section

/-!
# Decoder coverage of the SYCL-TLA FMHA prefill LSE dump

`Intel/Examples/RealFmhaLse.lean` is the prefill kernel with the
sequence-parallel LSE epilogue (2581 instructions, 2694 statements). This
module proves that the extended stack decodes and executes every statement,
and records the LSE-specific counts: 64 DPAS, 33 `math.exp`, 16 `math.log`,
17 `math.inv`, 16 `join` and 32 plain `store.ugm` forms.
-/

namespace IntelGpu

def lseCode : List TlaInstr := decodeTlaProgram realFmhaLse

def lsePc : List (Nat × TlaInstr) := withPcGo lseCode 0

def lseUnclassified : List (Nat × TlaInstr) :=
  lsePc.filter (fun p => !decodedAll p.2)

set_option maxRecDepth 1000000 in
theorem lseCode_length : lseCode.length = 2694 := by decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 8000000 in
theorem lse_decoded_count :
    (lsePc.filter (fun p => decodedAll p.2)).length = 2694 := by decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 8000000 in
theorem lse_unclassified_count : lseUnclassified.length = 0 := by decide

set_option maxRecDepth 1000000 in
theorem lse_dpas_count : (lsePc.filter (fun p => isDpas p.2)).length = 64 := by
  decide

set_option maxRecDepth 1000000 in
theorem lse_exp_count :
    (lsePc.filter (fun p => match parseTlaMath p.2 with
      | some m => m.op = .exp | none => false)).length = 33 := by decide

set_option maxRecDepth 1000000 in
theorem lse_log_count :
    (lsePc.filter (fun p => match parseTlaMath p.2 with
      | some m => m.op = .log | none => false)).length = 16 := by decide

set_option maxRecDepth 1000000 in
theorem lse_inv_count :
    (lsePc.filter (fun p => match parseTlaMath p.2 with
      | some m => m.op = .inv | none => false)).length = 17 := by decide

set_option maxRecDepth 1000000 in
theorem lse_join_count :
    (lsePc.filter (fun p => match p.2 with
      | .plain "join" _ => true | _ => false)).length = 16 := by decide

set_option maxRecDepth 1000000 in
theorem lse_store_count :
    (lsePc.filter (fun p => match p.2 with
      | .plain op _ => isPlainStoreOp op | _ => false)).length = 32 := by decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 8000000 in
theorem lse_decoded_all : lsePc.all (fun p => decodedAll p.2) = true := by decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 8000000 in
theorem lse_classified :
    lsePc.all (fun p =>
      (match classifyFmha p.2 with | .other => false | _ => true)) = true := by
  decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 8000000 in
theorem lse_step_total :
    lsePc.all (fun p => (tlaStepFmha? canonMachine p.2).isSome) = true := by
  decide

end IntelGpu
