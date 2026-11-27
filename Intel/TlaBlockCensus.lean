-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaMainloop
public import Intel.TlaBlock2d

@[expose] public section

/-!
# Contents of the SYCL-TLA mainloop block

The decoded mainloop block is `[959, 1404)`. This module censuses it: 445
instructions, of which 130 are block2d loads/stores, 103 are sync forms, 32
are DPAS and 2 are jumps.
-/

namespace IntelGpu

def blockInstrs : List (Nat × TlaInstr) :=
  withPc.filter (fun p => decide (959 ≤ p.1 ∧ p.1 < 1404))

def inBlockDpas : List Nat :=
  (blockInstrs.filter (fun p => isDpas p.2)).map (fun p => p.1)

def isB2d : TlaInstr → Bool
  | .predicated op _ =>
      (afterW op).isSome &&
        (startsLoad ((afterW op).getD []) || startsStore ((afterW op).getD []))
  | _ => false

def isSync : TlaInstr → Bool
  | .plain "sync.nop" _ => true
  | .plain "sync.allrd" _ => true
  | .predicated "(W) sync.bar" _ => true
  | _ => false

def isJmp : TlaInstr → Bool
  | .predicated _ _ => false
  | _ => false

def isJmpI : TlaInstr → Bool
  | i => match parseTlaJmpInstr i with
    | some _ => true
    | none => false

set_option maxRecDepth 100000 in
/-- The block has 445 instructions. -/
theorem blockInstrs_length : blockInstrs.length = 445 := by decide

set_option maxRecDepth 100000 in
/-- The block has 32 DPAS instructions. -/
theorem blockDpas_length : inBlockDpas.length = 32 := by decide

set_option maxRecDepth 100000 in
/-- The block has 130 block2d loads/stores. -/
theorem blockB2d_length :
    (blockInstrs.filter (fun p => isB2d p.2)).length = 130 := by decide

set_option maxRecDepth 100000 in
/-- The block has 103 sync instructions. -/
theorem blockSync_length :
    (blockInstrs.filter (fun p => isSync p.2)).length = 103 := by decide

set_option maxRecDepth 100000 in
/-- The block has 2 jumps. -/
theorem blockJmp_length :
    (blockInstrs.filter (fun p => isJmpI p.2)).length = 2 := by decide

end IntelGpu
