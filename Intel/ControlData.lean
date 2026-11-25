-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Asm
public import Intel.Control

@[expose] public section

/-!
# IGC data + control-flow step semantics

Combines the data/memory instructions from `Intel.Asm` with the pc-based
loop-control state from `Intel.Control`. This is the execution layer used by
the GEMM loop proof in the next stage.
-/

namespace IntelGpu

inductive DInstr where
  | data (instr : Instr)
  | cmpLt (dst src : Nat) (rhs : Word)
  | jmpi (target : Nat)
  | jmpiIf (pred : Nat) (target : Nat)
  deriving Repr, Inhabited

structure DState where
  data : State
  preds : Nat → Bool
  pc : Nat

def dstep (prog : List DInstr) (s : DState) : DState :=
  match prog[s.pc]? with
  | none => { s with data := { s.data with halted := true } }
  | some (.data i) => { s with data := step s.data i, pc := s.pc + 1 }
  | some (.cmpLt dst src rhs) =>
      { s with
        preds := fun r =>
          if r = dst then decide (s.data.regs src < rhs) else s.preds r,
        pc := s.pc + 1 }
  | some (.jmpi target) => { s with pc := target }
  | some (.jmpiIf pred target) =>
      { s with pc := if s.preds pred then target else s.pc + 1 }

def drun (prog : List DInstr) : Nat → DState → DState
  | 0, s => s
  | n + 1, s => drun prog n (dstep prog s)

@[simp] theorem drun_zero (prog : List DInstr) (s : DState) :
    drun prog 0 s = s := rfl

@[simp] theorem drun_succ (prog : List DInstr) (n : Nat) (s : DState) :
    drun prog (n + 1) s = drun prog n (dstep prog s) := rfl

theorem dstep_load32 (prog : List DInstr) (s : DState) (dst addrReg : Nat)
    (hAt : prog[s.pc]? = some (.data (.load32 dst addrReg))) :
    (dstep prog s).data.regs dst =
      load32 s.data.mem (s.data.addrRegs addrReg).toNat := by
  simp [dstep, step, hAt]

theorem dstep_mul (prog : List DInstr) (s : DState) (dst a b : Nat)
    (hAt : prog[s.pc]? = some (.data (.mul dst a b))) :
    (dstep prog s).data.regs dst = s.data.regs a * s.data.regs b := by
  simp [dstep, step, hAt]

theorem dstep_add (prog : List DInstr) (s : DState) (dst a b : Nat)
    (hAt : prog[s.pc]? = some (.data (.add dst a b))) :
    (dstep prog s).data.regs dst = s.data.regs a + s.data.regs b := by
  simp [dstep, step, hAt]

theorem dstep_jmpiIf_true (prog : List DInstr) (s : DState) (pred target : Nat)
    (hAt : prog[s.pc]? = some (.jmpiIf pred target)) (hPred : s.preds pred = true) :
    (dstep prog s).pc = target := by
  simp [dstep, hAt, hPred]

theorem dstep_jmpiIf_false (prog : List DInstr) (s : DState) (pred target : Nat)
    (hAt : prog[s.pc]? = some (.jmpiIf pred target)) (hPred : s.preds pred = false) :
    (dstep prog s).pc = s.pc + 1 := by
  simp [dstep, hAt, hPred]

end IntelGpu
