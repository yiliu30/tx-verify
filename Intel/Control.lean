-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Asm

@[expose] public section

/-!
# IGC loop-control step semantics

A pc-based step relation for the loop-control subset: immediate add,
`cmp.lt`, unconditional jump, and conditional jump. The full loop invariant
is the next stage.
-/

namespace IntelGpu

inductive CInstr where
  | addImm (dst src : Nat) (imm : Word)
  | cmpLt (dst src : Nat) (rhs : Word)
  | jmpi (target : Nat)
  | jmpiIf (pred : Nat) (target : Nat)
  deriving Repr, Inhabited

structure CState where
  regs : Nat → Word
  preds : Nat → Bool
  pc : Nat
  halted : Bool

def cstep (prog : List CInstr) (s : CState) : CState :=
  match prog[s.pc]? with
  | none => { s with halted := true }
  | some (.addImm dst src imm) =>
      { s with
        regs := fun r => if r = dst then s.regs src + imm else s.regs r,
        pc := s.pc + 1 }
  | some (.cmpLt dst src rhs) =>
      { s with
        preds := fun r => if r = dst then decide (s.regs src < rhs) else s.preds r,
        pc := s.pc + 1 }
  | some (.jmpi target) => { s with pc := target }
  | some (.jmpiIf pred target) =>
      { s with pc := if s.preds pred then target else s.pc + 1 }

def crun (prog : List CInstr) : Nat → CState → CState
  | 0, s => s
  | n + 1, s => crun prog n (cstep prog s)

theorem cstep_jmpiIf_true (prog : List CInstr) (s : CState) (pred target : Nat)
    (hAt : prog[s.pc]? = some (.jmpiIf pred target)) (hPred : s.preds pred = true) :
    (cstep prog s).pc = target := by
  simp [cstep, hAt, hPred]

theorem cstep_jmpiIf_false (prog : List CInstr) (s : CState) (pred target : Nat)
    (hAt : prog[s.pc]? = some (.jmpiIf pred target)) (hPred : s.preds pred = false) :
    (cstep prog s).pc = s.pc + 1 := by
  simp [cstep, hAt, hPred]

end IntelGpu
