-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaCmpGate
public import Intel.TlaSel
public import Intel.TlaSyncAllwr
public import Intel.TlaMath
public import Intel.TlaBfnExec
public import Intel.TlaLoadPhase
public import Intel.TlaControlDecode

@[expose] public section

/-!
# A unified instruction dispatcher

`classifyOp` sorts every decoded instruction into one of the modelled classes
(DPAS, move, ALU, block2d, comparison, bit-field, send, sync, jump, label) and
`tlaStep?` executes it over a machine carrying the scalar state, tile memory,
binding table and message log.

Every class has a projection theorem saying the dispatcher agrees with the
class semantics, and with the `mach`/`macl` forms executed, every instruction
of the dump has a step.
-/

namespace IntelGpu

/-- The machine the dispatcher runs over. -/
structure TlaFullMachine where
  state : TlaState
  mem : TlaMem
  bti : Nat → Word
  log : List TlaMsg
  mufu : MufuModel

/-- The control effect of one instruction. -/
inductive TlaCtl where
  | next
  | jump (target : String)

/-- The instruction classes of the dispatcher. -/
inductive TlaOp where
  | dpas (d : TlaDpas)
  | mov (mv : TlaMov)
  | alu (a : TlaAlu)
  | b2d (b : TlaBlock2d)
  | cmp (c : TlaCmp)
  | sel (s : TlaSel)
  | syncAllwr (s : TlaSyncAllwr)
  | math (m : TlaMath)
  | bfn (b : TlaBfn)
  | send (s : TlaSend)
  | sync
  | jmp (j : TlaJmp)
  | label
  | other
  deriving Repr, DecidableEq

/-- Classify a decoded instruction, first matching parser wins. -/
def classifyOp (i : TlaInstr) : TlaOp :=
  match parseTlaDpas i with
  | some d => .dpas d
  | none =>
  match parseTlaMovInstr i with
  | some mv => .mov mv
  | none =>
  match parseTlaMovPlain i with
  | some mv => .mov mv
  | none =>
  match parseTlaAluInstr i with
  | some a => .alu a
  | none =>
  match parseTlaAluPlain i with
  | some a => .alu a
  | none =>
  match parseTlaBlock2dInstr i with
  | some b => .b2d b
  | none =>
  match parseTlaBlock2dPlain i with
  | some b => .b2d b
  | none =>
  match parseTlaBlock2dPlainStore i with
  | some b => .b2d b
  | none =>
  match parseTlaCmpInstr i with
  | some c => .cmp c
  | none =>
  match parseTlaSelInstr i with
  | some s => .sel s
  | none =>
  match parseTlaBfn i with
  | some b => .bfn b
  | none =>
  match parseTlaSend i with
  | some s => .send s
  | none =>
  match parseTlaJmpInstr i with
  | some j => .jmp j
  | none =>
  match parseTlaSyncAllwr i with
  | some s => .syncAllwr s
  | none =>
  match parseTlaMath i with
  | some mt => .math mt
  | none =>
  match i with
  | .label _ => .label
  | .plain "sync.nop" _ => .sync
  | .plain "sync.allrd" _ => .sync
  | .predicated "(W) sync.bar" _ => .sync
  | _ => .other

/-- Execute one instruction over the machine. -/
def tlaStep? (m : TlaFullMachine) (i : TlaInstr) : Option (TlaFullMachine × TlaCtl) :=
  match classifyOp i with
  | .dpas d =>
      some ({ m with state := { m.state with regs := tlaDpasStepOf d m.state.regs } }, .next)
  | .mov mv =>
      some ({ m with state := { m.state with regs := tlaMovStep m.state.regs mv } }, .next)
  | .alu a =>
      (tlaAluStateStep? m.state a).map (fun st => ({ m with state := st }, .next))
  | .b2d b =>
      (TlaBlock2d.loadStoreStep m.state m.mem m.bti b).map
        (fun p => ({ m with state := p.1, mem := p.2 }, .next))
  | .cmp c => some ({ m with state := c.step m.state }, .next)
  | .sel s => some ({ m with state := s.step m.state }, .next)
  | .bfn b =>
      some ({ m with state := { m.state with regs := b.step m.state.regs } }, .next)
  | .send s => some ({ m with log := tlaSendStep m.log s }, .next)
  | .sync => some (m, .next)
  | .syncAllwr _ => some (m, .next)
  | .math t =>
      some ({ m with state := { m.state with regs := t.step m.mufu m.state.regs } }, .next)
  | .jmp j => some (m, .jump j.target)
  | .label => some (m, .next)
  | .other => none

theorem tlaStep?_dpas (m : TlaFullMachine) (i : TlaInstr) (d : TlaDpas)
    (h : classifyOp i = .dpas d) :
    tlaStep? m i =
      some ({ m with state := { m.state with regs := tlaDpasStepOf d m.state.regs } }, .next) := by
  simp [tlaStep?, h]

theorem tlaStep?_mov (m : TlaFullMachine) (i : TlaInstr) (mv : TlaMov)
    (h : classifyOp i = .mov mv) :
    tlaStep? m i =
      some ({ m with state := { m.state with regs := tlaMovStep m.state.regs mv } }, .next) := by
  simp [tlaStep?, h]

theorem tlaStep?_alu (m : TlaFullMachine) (i : TlaInstr) (a : TlaAlu)
    (h : classifyOp i = .alu a) :
    tlaStep? m i =
      (tlaAluStateStep? m.state a).map (fun st => ({ m with state := st }, .next)) := by
  simp [tlaStep?, h]

theorem tlaStep?_b2d (m : TlaFullMachine) (i : TlaInstr) (b : TlaBlock2d)
    (h : classifyOp i = .b2d b) :
    tlaStep? m i =
      (TlaBlock2d.loadStoreStep m.state m.mem m.bti b).map
        (fun p => ({ m with state := p.1, mem := p.2 }, .next)) := by
  simp [tlaStep?, h]

theorem tlaStep?_cmp (m : TlaFullMachine) (i : TlaInstr) (c : TlaCmp)
    (h : classifyOp i = .cmp c) :
    tlaStep? m i = some ({ m with state := c.step m.state }, .next) := by
  simp [tlaStep?, h]

theorem tlaStep?_sel (m : TlaFullMachine) (i : TlaInstr) (s : TlaSel)
    (h : classifyOp i = .sel s) :
    tlaStep? m i = some ({ m with state := s.step m.state }, .next) := by
  simp [tlaStep?, h]

theorem tlaStep?_bfn (m : TlaFullMachine) (i : TlaInstr) (b : TlaBfn)
    (h : classifyOp i = .bfn b) :
    tlaStep? m i = some ({ m with state := { m.state with regs := b.step m.state.regs } }, .next) := by
  simp [tlaStep?, h]

theorem tlaStep?_send (m : TlaFullMachine) (i : TlaInstr) (s : TlaSend)
    (h : classifyOp i = .send s) :
    tlaStep? m i = some ({ m with log := tlaSendStep m.log s }, .next) := by
  simp [tlaStep?, h]

theorem tlaStep?_syncAllwr (m : TlaFullMachine) (i : TlaInstr) (s : TlaSyncAllwr)
    (h : classifyOp i = .syncAllwr s) :
    tlaStep? m i = some (m, .next) := by
  simp [tlaStep?, h]

/-- A wait leaves the machine, including memory, untouched. -/
theorem tlaStep?_syncAllwr_mem (m : TlaFullMachine) (i : TlaInstr) (s : TlaSyncAllwr)
    (h : classifyOp i = .syncAllwr s) :
    (tlaStep? m i).map (fun p => p.1.mem) = some m.mem := by
  rw [tlaStep?_syncAllwr m i s h]
  rfl

theorem tlaStep?_sync (m : TlaFullMachine) (i : TlaInstr) (h : classifyOp i = .sync) :
    tlaStep? m i = some (m, .next) := by
  simp [tlaStep?, h]

theorem tlaStep?_math (m : TlaFullMachine) (i : TlaInstr) (t : TlaMath)
    (h : classifyOp i = .math t) :
    tlaStep? m i =
      some ({ m with state := { m.state with regs := t.step m.mufu m.state.regs } }, .next) := by
  simp [tlaStep?, h]

theorem tlaStep?_jmp (m : TlaFullMachine) (i : TlaInstr) (j : TlaJmp)
    (h : classifyOp i = .jmp j) :
    tlaStep? m i = some (m, .jump j.target) := by
  simp [tlaStep?, h]

theorem tlaStep?_label (m : TlaFullMachine) (i : TlaInstr) (h : classifyOp i = .label) :
    tlaStep? m i = some (m, .next) := by
  simp [tlaStep?, h]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- Every program instruction is classified. -/
theorem realTlaGemm_classified :
    withPc.all (fun p => (match classifyOp p.2 with | .other => false | _ => true)) = true := by
  decide

/-- A canonical all-zero machine. -/
def canonMachine : TlaFullMachine :=
  ⟨⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0⟩,
    ⟨fun _ _ => 0⟩, fun _ => 0, [], idMufu⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- Every statement of the dump has a dispatcher step. -/
theorem realTlaGemm_step_total :
    withPc.all (fun p => (tlaStep? canonMachine p.2).isSome) = true := by
  decide

end IntelGpu
