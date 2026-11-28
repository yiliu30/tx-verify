-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaSchedule
public import Intel.TlaCmp

@[expose] public section

/-!
# The three regions of the SYCL-TLA kernel

The decoded program has 2252 statements. The verified mainloop block is
`[959, 1404)`; this module records the two remaining regions and their
instruction mix:

* prologue `[0, 959)`: 959 statements, no DPAS,
* epilogue `[1404, 2252)`: 848 statements, no DPAS.

The prologue and epilogue carry most of the scalar setup and output work; the
census makes the unmodeled residue explicit.
-/

namespace IntelGpu

/-- The 959 statements before the mainloop. -/
def prologueInstrs : List (Nat × TlaInstr) :=
  withPc.filter (fun p => p.1 < 959)

/-- The 848 statements after the mainloop. -/
def epilogueInstrs : List (Nat × TlaInstr) :=
  withPc.filter (fun p => 1404 ≤ p.1)

/-- The instruction mix of a region. -/
def kindCensus (l : List (Nat × TlaInstr)) : List (String × Nat) :=
  [("mov", (l.filter (fun p => p.2.kind = .mov)).length),
   ("alu", (l.filter (fun p => p.2.kind = .alu)).length),
   ("b2d", (l.filter (fun p => p.2.kind = .b2d)).length),
   ("b2dPlain", (l.filter (fun p => p.2.kind = .b2dPlain)).length),
   ("dpas", (l.filter (fun p => p.2.kind = .dpas)).length),
   ("syncNop", (l.filter (fun p => p.2.kind = .syncNop)).length),
   ("syncBar", (l.filter (fun p => p.2.kind = .syncBar)).length),
   ("jmp", (l.filter (fun p => p.2.kind = .jmp)).length),
   ("label", (l.filter (fun p => p.2.kind = .label)).length),
   ("other", (l.filter (fun p => p.2.kind = .other)).length)]

set_option maxRecDepth 1000000 in
/-- The prologue has 959 statements. -/
theorem prologue_length : prologueInstrs.length = 959 := by decide

set_option maxRecDepth 1000000 in
/-- The epilogue has 848 statements. -/
theorem epilogue_length : epilogueInstrs.length = 848 := by decide

set_option maxRecDepth 1000000 in
/-- The prologue instruction mix. -/
theorem prologueKinds :
    kindCensus prologueInstrs =
      [("mov", 49), ("alu", 46), ("b2d", 193), ("b2dPlain", 4), ("dpas", 0),
       ("syncNop", 84), ("syncBar", 0), ("jmp", 6), ("label", 9),
       ("other", 568)] := by
  decide

set_option maxRecDepth 1000000 in
/-- The epilogue instruction mix. -/
theorem epilogueKinds :
    kindCensus epilogueInstrs =
      [("mov", 176), ("alu", 55), ("b2d", 70), ("b2dPlain", 16), ("dpas", 0),
       ("syncNop", 57), ("syncBar", 0), ("jmp", 50), ("label", 74),
       ("other", 350)] := by
  decide

set_option maxRecDepth 100000 in
/-- The three regions add up to the whole program. -/
theorem region_lengths :
    prologueInstrs.length + blockInstrs.length + epilogueInstrs.length =
      tlaCode.length := by
  decide

set_option maxRecDepth 1000000 in
/-- The prologue and epilogue contain no DPAS. -/
theorem regions_no_dpas :
    (prologueInstrs ++ epilogueInstrs).all (fun p => p.2.kind ≠ .dpas) = true := by
  decide

end IntelGpu
