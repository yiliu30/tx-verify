-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaAlu
public import Intel.TlaPredCensus

@[expose] public section

/-!
# Census of the SYCL-TLA ALU forms

`Intel.TlaAlu` accepts register-destination ALU instructions. This module
records exactly how many forms parse and how many of each opcode the dump
contains, so the remaining non-`r` destination work (`acc0`, `a0`, `cr0`) is a
precise gap.

The parsed subset covers 68 instructions. The raw dump has 14 `mul`, 25 `shr`
and 1 `or` forms with non-`r` destinations, plus one `and` with a non-`r`
destination.
-/

namespace IntelGpu

set_option maxRecDepth 100000 in
/-- The parsed ALU subset has 68 instructions. -/
theorem realTlaGemmAlu_total : realTlaGemmAlu.length = 68 := by decide

set_option maxRecDepth 100000 in
/-- `and`: 4 reg-destination forms parse. -/
theorem alu_and_parsed :
    (realTlaGemmAlu.filter (fun a => a.op = .and)).length = 4 := by decide

set_option maxRecDepth 100000 in
/-- `add`: 31 forms parse. -/
theorem alu_add_parsed :
    (realTlaGemmAlu.filter (fun a => a.op = .add)).length = 31 := by decide

set_option maxRecDepth 100000 in
/-- `shl`: 17 forms parse. -/
theorem alu_shl_parsed :
    (realTlaGemmAlu.filter (fun a => a.op = .shl)).length = 17 := by decide

set_option maxRecDepth 100000 in
/-- `asr`: 1 form parses. -/
theorem alu_asr_parsed :
    (realTlaGemmAlu.filter (fun a => a.op = .asr)).length = 1 := by decide

set_option maxRecDepth 100000 in
/-- `mad`: 1 form parses. -/
theorem alu_mad_parsed :
    (realTlaGemmAlu.filter (fun a => a.op = .mad)).length = 1 := by decide

set_option maxRecDepth 100000 in
/-- `mach`: 4 forms parse. -/
theorem alu_mach_parsed :
    (realTlaGemmAlu.filter (fun a => a.op = .mach)).length = 4 := by decide

set_option maxRecDepth 100000 in
/-- `macl`: 10 forms parse. -/
theorem alu_macl_parsed :
    (realTlaGemmAlu.filter (fun a => a.op = .macl)).length = 10 := by decide

set_option maxRecDepth 100000 in
/-- The raw dump has 14 `mul` forms. -/
theorem pred_mul_count : predOpcodes.count "(W) mul" = 14 := by decide

set_option maxRecDepth 100000 in
/-- The raw dump has 25 `shr` forms. -/
theorem pred_shr_count : predOpcodes.count "(W) shr" = 25 := by decide

set_option maxRecDepth 100000 in
/-- The raw dump has 1 `or` form. -/
theorem pred_or_count : predOpcodes.count "(W) or" = 1 := by decide

set_option maxRecDepth 100000 in
/-- The raw dump has 5 `and` forms, so one has a non-`r` destination. -/
theorem pred_and_count : predOpcodes.count "(W) and" = 5 := by decide

end IntelGpu
