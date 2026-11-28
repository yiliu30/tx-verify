-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Slm

@[expose] public section

/-!
# Workgroup control flow

A pc-based program layer over the stage-16 workgroup machine. Control flow is
uniform across the workgroup: one `pred` flag and one `k` counter, which is the
lockstep requirement a barrier already imposes on SIMD lanes. Per-lane
predicates (the execution mask) are a later refinement.

`cstep` executes lane/SLM instructions through `wstep`, so the stage-16 SLM
behaviour is unchanged; control instructions only move the pc and the shared
counter.
-/

namespace IntelGpu

inductive CInstr where
  | w (i : WInstr)
  | cmpGe (K : Nat)
  | incK
  | jmpiIf (target : Nat)
  | jmpi (target : Nat)
  deriving Repr

structure CState where
  w : WState
  k : Nat
  pred : Bool
  pc : Nat
  halted : Bool

def cstep (prog : List CInstr) (s : CState) : CState :=
  match prog[s.pc]? with
  | none => { s with halted := true }
  | some (.w i) => { s with w := wstep s.w i, pc := s.pc + 1 }
  | some (.cmpGe K) => { s with pred := decide (K ≤ s.k), pc := s.pc + 1 }
  | some .incK => { s with k := s.k + 1, pc := s.pc + 1 }
  | some (.jmpiIf target) => { s with pc := if s.pred then target else s.pc + 1 }
  | some (.jmpi target) => { s with pc := target }

def crun (prog : List CInstr) : Nat → CState → CState
  | 0, s => s
  | n + 1, s => crun prog n (cstep prog s)

@[simp] theorem crun_zero (prog : List CInstr) (s : CState) : crun prog 0 s = s := rfl

@[simp] theorem crun_succ (prog : List CInstr) (n : Nat) (s : CState) :
    crun prog (n + 1) s = crun prog n (cstep prog s) := rfl

theorem crun_add (prog : List CInstr) (a b : Nat) (s : CState) :
    crun prog (a + b) s = crun prog b (crun prog a s) := by
  induction a generalizing s with
  | zero => simp
  | succ a ih =>
      calc
        crun prog (a + 1 + b) s = crun prog (a + b) (cstep prog s) := by
          rw [show a + 1 + b = (a + b) + 1 by omega]
          rfl
        _ = crun prog b (crun prog a (cstep prog s)) := ih (cstep prog s)
        _ = crun prog b (crun prog (a + 1) s) := rfl

theorem wstep_barrier_done (s : WState) (l : Nat) :
    ((wstep s .barrier).lanes l).done = (s.lanes l).done := by
  by_cases h : barrierOK s <;> simp [wstep, h]

/-- Point one lane's global pointer at a word index. -/
def setGidx (s : WState) (l i : Nat) : WState :=
  { s with lanes := fun l' => if l' = l then { s.lanes l with gidx := i } else s.lanes l' }

/-- Overwrite one data register of one lane. -/
def setReg (s : WState) (l r : Nat) (v : Word) : WState :=
  { s with
    lanes := fun l' =>
      if l' = l then
        { s.lanes l with regs := fun r' => if r' = r then v else (s.lanes l).regs r' }
      else s.lanes l' }

@[simp] theorem setGidx_self (s : WState) (l i : Nat) :
    ((setGidx s l i).lanes l).gidx = i := by
  simp [setGidx]

@[simp] theorem setReg_self (s : WState) (l r : Nat) (v : Word) :
    ((setReg s l r v).lanes l).regs r = v := by
  simp [setReg]

end IntelGpu
