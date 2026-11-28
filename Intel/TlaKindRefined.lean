-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaRegions
public import Intel.TlaCmpCond
public import Intel.TlaBfnExec

@[expose] public section

/-!
# The refined instruction classification

The stage-203 schedule classifier predates the `cmp`, `bfn`, `send` and
`sync.allrd` decoders, so it labels those forms `other`. This module gives a
refined classifier with one constructor per dispatcher class and proves the
instruction mix of all three regions, with **no** `other` left:

* block `[959, 1404)`: 32 DPAS, 152 mov, 10 ALU, 130 + 7 block2d, 2 cmp,
  2 bfn, 1 send, 102 `sync.nop`, 1 `sync.bar`, 2 jumps, 4 labels;
* prologue `[0, 959)`: 564 mov, 58 ALU, 193 + 4 block2d, 3 cmp, 1 bfn,
  84 `sync.nop`, 37 `sync.allrd`, 6 jumps, 9 labels;
* epilogue `[1404, 2252)`: 192 mov, 329 ALU, 70 + 48 block2d, 23 cmp, 1 bfn,
  1 send, 57 `sync.nop`, 3 `sync.allrd`, 50 jumps, 74 labels.
-/

namespace IntelGpu

/-- One constructor per dispatcher class. -/
inductive TlaKindR where
  | dpas
  | mov
  | alu
  | b2d
  | b2dPlain
  | cmp
  | bfn
  | send
  | syncNop
  | syncAllrd
  | syncBar
  | jmp
  | label
  | other
  deriving Repr, DecidableEq

/-- The refined total classifier. -/
def kindR (i : TlaInstr) : TlaKindR :=
  match i with
  | .dpas _ _ _ _ _ _ => .dpas
  | .label _ => .label
  | .plain "sync.nop" _ => .syncNop
  | .plain "sync.allrd" _ => .syncAllrd
  | .predicated "(W) sync.bar" _ => .syncBar
  | _ =>
    if (parseTlaMovInstr i).isSome || (parseTlaMovPlain i).isSome then .mov
    else if (parseTlaAluInstr i).isSome || (parseTlaAluPlain i).isSome then .alu
    else if (parseTlaBlock2dInstr i).isSome then .b2d
    else if (parseTlaBlock2dPlain i).isSome || (parseTlaBlock2dPlainStore i).isSome then .b2dPlain
    else if (parseTlaCmpInstr i).isSome then .cmp
    else if (parseTlaBfn i).isSome then .bfn
    else if (parseTlaSend i).isSome then .send
    else if (parseTlaJmpInstr i).isSome then .jmp
    else .other

/-- The refined instruction mix of a region. -/
def kindRCensus (l : List (Nat × TlaInstr)) : List (String × Nat) :=
  [("dpas", (l.filter (fun p => kindR p.2 = .dpas)).length),
   ("mov", (l.filter (fun p => kindR p.2 = .mov)).length),
   ("alu", (l.filter (fun p => kindR p.2 = .alu)).length),
   ("b2d", (l.filter (fun p => kindR p.2 = .b2d)).length),
   ("b2dPlain", (l.filter (fun p => kindR p.2 = .b2dPlain)).length),
   ("cmp", (l.filter (fun p => kindR p.2 = .cmp)).length),
   ("bfn", (l.filter (fun p => kindR p.2 = .bfn)).length),
   ("send", (l.filter (fun p => kindR p.2 = .send)).length),
   ("syncNop", (l.filter (fun p => kindR p.2 = .syncNop)).length),
   ("syncAllrd", (l.filter (fun p => kindR p.2 = .syncAllrd)).length),
   ("syncBar", (l.filter (fun p => kindR p.2 = .syncBar)).length),
   ("jmp", (l.filter (fun p => kindR p.2 = .jmp)).length),
   ("label", (l.filter (fun p => kindR p.2 = .label)).length),
   ("other", (l.filter (fun p => kindR p.2 = .other)).length)]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- The block's refined instruction mix. -/
theorem kindR_block :
    kindRCensus blockInstrs =
      [("dpas", 32), ("mov", 152), ("alu", 10), ("b2d", 130), ("b2dPlain", 7),
       ("cmp", 2), ("bfn", 2), ("send", 1), ("syncNop", 102), ("syncAllrd", 0),
       ("syncBar", 1), ("jmp", 2), ("label", 4), ("other", 0)] := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- The prologue's refined instruction mix. -/
theorem kindR_prologue :
    kindRCensus prologueInstrs =
      [("dpas", 0), ("mov", 564), ("alu", 58), ("b2d", 193), ("b2dPlain", 4),
       ("cmp", 3), ("bfn", 1), ("send", 0), ("syncNop", 84), ("syncAllrd", 37),
       ("syncBar", 0), ("jmp", 6), ("label", 9), ("other", 0)] := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- The epilogue's refined instruction mix. -/
theorem kindR_epilogue :
    kindRCensus epilogueInstrs =
      [("dpas", 0), ("mov", 192), ("alu", 329), ("b2d", 70), ("b2dPlain", 48),
       ("cmp", 23), ("bfn", 1), ("send", 1), ("syncNop", 57), ("syncAllrd", 3),
       ("syncBar", 0), ("jmp", 50), ("label", 74), ("other", 0)] := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- No instruction of the dump is left unclassified. -/
theorem kindR_no_other :
    withPc.all (fun p => decide (kindR p.2 ≠ .other)) = true := by
  decide

end IntelGpu
