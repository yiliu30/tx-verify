-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaAlu

@[expose] public section

/-!
# Destination-class census of the SYCL-TLA ALU forms

`Intel.TlaAlu` now parses all 109 ALU instructions. This module counts them by
destination class: 68 write a GRF (`r`), 14 write an accumulator (`acc0`),
25 write an address register (`a0`), 1 writes a control register (`cr0`) and
1 writes a flag (`f3`). Execution currently models the 68 `r` forms.
-/

namespace IntelGpu

def TlaAluDst.isR : TlaAluDst → Bool
  | .r _ => true
  | _ => false

def TlaAluDst.isAcc : TlaAluDst → Bool
  | .acc _ _ => true
  | _ => false

def TlaAluDst.isAddr : TlaAluDst → Bool
  | .addr _ _ => true
  | _ => false

def TlaAluDst.isCr : TlaAluDst → Bool
  | .cr _ _ => true
  | _ => false

def TlaAluDst.isFlag : TlaAluDst → Bool
  | .flag _ _ => true
  | _ => false

set_option maxRecDepth 100000 in
/-- 68 ALU instructions write a GRF. -/
theorem tlaAlu_r_count :
    (realTlaGemmAlu.filter (fun a => a.dst.isR)).length = 68 := by decide

set_option maxRecDepth 100000 in
/-- 14 ALU instructions write an accumulator. -/
theorem tlaAlu_acc_count :
    (realTlaGemmAlu.filter (fun a => a.dst.isAcc)).length = 14 := by decide

set_option maxRecDepth 100000 in
/-- 25 ALU instructions write an address register. -/
theorem tlaAlu_addr_count :
    (realTlaGemmAlu.filter (fun a => a.dst.isAddr)).length = 25 := by decide

set_option maxRecDepth 100000 in
/-- One ALU instruction writes a control register. -/
theorem tlaAlu_cr_count :
    (realTlaGemmAlu.filter (fun a => a.dst.isCr)).length = 1 := by decide

set_option maxRecDepth 100000 in
/-- One ALU instruction writes a flag. -/
theorem tlaAlu_flag_count :
    (realTlaGemmAlu.filter (fun a => a.dst.isFlag)).length = 1 := by decide

end IntelGpu
