-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Asm

@[expose] public section

/-!
# Word-indexed memory dot-product loop

A pc-level memory loop for one GEMM output element. A and B are contiguous
word arrays at indices `k` and `K + k`; the loop loads both, multiplies,
accumulates, advances both pointers, and branches back while `k < K`.
-/

namespace IntelGpu

structure MState where
  mem : Nat → Word
  aIdx : Nat
  bIdx : Nat
  k : Nat
  sum : Word
  a : Word
  b : Word
  prod : Word
  pred : Bool
  pc : Nat
  halted : Bool

inductive MInstr where
  | loadA
  | loadB
  | mul
  | add
  | incK
  | incA
  | incB
  | cmpGe (K : Nat)
  | jmpiIf (target : Nat)
  | jmpi (target : Nat)
  deriving Repr

def mstep (prog : List MInstr) (s : MState) : MState :=
  match prog[s.pc]? with
  | none => { s with halted := true }
  | some .loadA => { s with a := s.mem s.aIdx, pc := s.pc + 1 }
  | some .loadB => { s with b := s.mem s.bIdx, pc := s.pc + 1 }
  | some .mul => { s with prod := s.a * s.b, pc := s.pc + 1 }
  | some .add => { s with sum := s.sum + s.prod, pc := s.pc + 1 }
  | some .incK => { s with k := s.k + 1, pc := s.pc + 1 }
  | some .incA => { s with aIdx := s.aIdx + 1, pc := s.pc + 1 }
  | some .incB => { s with bIdx := s.bIdx + 1, pc := s.pc + 1 }
  | some (.cmpGe K) => { s with pred := decide (K ≤ s.k), pc := s.pc + 1 }
  | some (.jmpiIf target) =>
      { s with pc := if s.pred then target else s.pc + 1 }
  | some (.jmpi target) =>
      { s with pc := target, a := 0, b := 0, prod := 0 }

def mrun (prog : List MInstr) : Nat → MState → MState
  | 0, s => s
  | n + 1, s => mrun prog n (mstep prog s)

@[simp] theorem mrun_zero (prog : List MInstr) (s : MState) :
    mrun prog 0 s = s := rfl

@[simp] theorem mrun_succ (prog : List MInstr) (n : Nat) (s : MState) :
    mrun prog (n + 1) s = mrun prog n (mstep prog s) := rfl

theorem mrun_add (prog : List MInstr) (a b : Nat) (s : MState) :
    mrun prog (a + b) s = mrun prog b (mrun prog a s) := by
  induction a generalizing s with
  | zero => simp
  | succ a ih =>
      calc
        mrun prog (a + 1 + b) s = mrun prog (a + b) (mstep prog s) := by
          rw [show a + 1 + b = (a + b) + 1 by omega]
          rfl
        _ = mrun prog b (mrun prog a (mstep prog s)) := ih (mstep prog s)
        _ = mrun prog b (mrun prog (a + 1) s) := rfl

def mProgram (K : Nat) : List MInstr :=
  [.cmpGe K, .jmpiIf 10, .loadA, .loadB, .mul, .add,
   .incK, .incA, .incB, .jmpi 0]

def mLoopHead (mem : Nat → Word) (K k : Nat) (sum : Word) : MState :=
  { mem := mem, aIdx := k, bIdx := K + k, k := k, sum := sum,
    a := 0, b := 0, prod := 0, pred := false, pc := 0, halted := false }

def mExitState (mem : Nat → Word) (K : Nat) (sum : Word) : MState :=
  { mem := mem, aIdx := K, bIdx := 2 * K, k := K, sum := sum,
    a := 0, b := 0, prod := 0, pred := true, pc := 10, halted := true }

def dotRange (A B : Nat → Word) (k : Nat) : Nat → Word
  | 0 => 0
  | n + 1 => A k * B k + dotRange A B (k + 1) n

theorem mstep_iter (mem : Nat → Word) (K k : Nat) (sum : Word) (h : k < K) :
    mrun (mProgram K) 10 (mLoopHead mem K k sum) =
      mLoopHead mem K (k + 1) (sum + mem k * mem (K + k)) := by
  have hnot : ¬ K ≤ k := by omega
  unfold mProgram
  simp [mstep, mLoopHead, hnot, Nat.add_assoc, Nat.add_comm]

theorem mstep_exit (mem : Nat → Word) (K : Nat) (sum : Word) :
    mrun (mProgram K) 3 (mLoopHead mem K K sum) = mExitState mem K sum := by
  unfold mProgram
  simp [mstep, mLoopHead, mExitState]
  omega

theorem mProgram_run_aux (mem : Nat → Word) (K k : Nat) (sum : Word) (n : Nat)
    (hn : k + n = K) :
    mrun (mProgram K) (10 * n + 3) (mLoopHead mem K k sum) =
      mExitState mem K (sum + dotRange (fun j => mem j) (fun j => mem (K + j)) k n) := by
  induction n generalizing k sum with
  | zero =>
      have hk : k = K := by omega
      rw [hk]
      simpa [dotRange] using mstep_exit mem K sum
  | succ n ih =>
      have hlt : k < K := by omega
      have hnext : k + 1 + n = K := by omega
      rw [show 10 * (n + 1) + 3 = 10 + (10 * n + 3) by omega]
      rw [mrun_add]
      rw [mstep_iter mem K k sum hlt]
      rw [ih (k + 1) (sum + mem k * mem (K + k)) hnext]
      simp [dotRange, BitVec.add_assoc]

theorem mProgram_correct (mem : Nat → Word) (K : Nat) :
    let s := mrun (mProgram K) (10 * K + 3) (mLoopHead mem K 0 0)
    s.halted = true ∧ s.k = K ∧ s.sum =
      dotRange (fun j => mem j) (fun j => mem (K + j)) 0 K := by
  have h := mProgram_run_aux mem K 0 0 K (by omega)
  change (mrun (mProgram K) (10 * K + 3) (mLoopHead mem K 0 0)).halted = true ∧
    (mrun (mProgram K) (10 * K + 3) (mLoopHead mem K 0 0)).k = K ∧
    (mrun (mProgram K) (10 * K + 3) (mLoopHead mem K 0 0)).sum =
      dotRange (fun j => mem j) (fun j => mem (K + j)) 0 K
  rw [h]
  simp [mExitState]

end IntelGpu
