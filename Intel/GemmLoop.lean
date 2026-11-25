-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Asm

@[expose] public section

/-!
# Dot-product loop invariant

A pc-level loop over abstract A/B arrays. The loop body loads A[k], B[k],
multiplies, accumulates, increments k, and branches back while `k < K`.
The theorem proves termination, the final counter value, and the exact
BitVec dot product.
-/

namespace IntelGpu

structure GState where
  A : Nat → Word
  B : Nat → Word
  k : Nat
  sum : Word
  a : Word
  b : Word
  prod : Word
  pred : Bool
  pc : Nat
  halted : Bool

inductive GInstr where
  | loadA
  | loadB
  | mul
  | add
  | incK
  | cmpGe (K : Nat)
  | jmpiIf (target : Nat)
  | jmpi (target : Nat)
  deriving Repr

def gstep (prog : List GInstr) (s : GState) : GState :=
  match prog[s.pc]? with
  | none => { s with halted := true }
  | some .loadA => { s with a := s.A s.k, pc := s.pc + 1 }
  | some .loadB => { s with b := s.B s.k, pc := s.pc + 1 }
  | some .mul => { s with prod := s.a * s.b, pc := s.pc + 1 }
  | some .add => { s with sum := s.sum + s.prod, pc := s.pc + 1 }
  | some .incK => { s with k := s.k + 1, pc := s.pc + 1 }
  | some (.cmpGe K) => { s with pred := decide (K ≤ s.k), pc := s.pc + 1 }
  | some (.jmpiIf target) =>
      { s with pc := if s.pred then target else s.pc + 1 }
  | some (.jmpi target) =>
      { s with pc := target, a := 0, b := 0, prod := 0 }

def grun (prog : List GInstr) : Nat → GState → GState
  | 0, s => s
  | n + 1, s => grun prog n (gstep prog s)

@[simp] theorem grun_zero (prog : List GInstr) (s : GState) :
    grun prog 0 s = s := rfl

@[simp] theorem grun_succ (prog : List GInstr) (n : Nat) (s : GState) :
    grun prog (n + 1) s = grun prog n (gstep prog s) := rfl

theorem grun_add (prog : List GInstr) (a b : Nat) (s : GState) :
    grun prog (a + b) s = grun prog b (grun prog a s) := by
  induction a generalizing s with
  | zero => simp
  | succ a ih =>
      calc
        grun prog (a + 1 + b) s = grun prog (a + b) (gstep prog s) := by
          rw [show a + 1 + b = (a + b) + 1 by omega]
          rfl
        _ = grun prog b (grun prog a (gstep prog s)) := ih (gstep prog s)
        _ = grun prog b (grun prog (a + 1) s) := rfl

def dotProgram (K : Nat) : List GInstr :=
  [.cmpGe K, .jmpiIf 8, .loadA, .loadB, .mul, .add, .incK, .jmpi 0]

def loopHead (A B : Nat → Word) (k : Nat) (sum : Word) : GState :=
  { A := A, B := B, k := k, sum := sum, a := 0, b := 0, prod := 0,
    pred := false, pc := 0, halted := false }

def exitState (A B : Nat → Word) (K : Nat) (sum : Word) : GState :=
  { A := A, B := B, k := K, sum := sum, a := 0, b := 0, prod := 0,
    pred := true, pc := 8, halted := true }

def dotRange (A B : Nat → Word) (k : Nat) : Nat → Word
  | 0 => 0
  | n + 1 => A k * B k + dotRange A B (k + 1) n

theorem gstep_iter (A B : Nat → Word) (K k : Nat) (sum : Word) (h : k < K) :
    grun (dotProgram K) 8 (loopHead A B k sum) =
      loopHead A B (k + 1) (sum + A k * B k) := by
  have hnot : ¬ K ≤ k := by omega
  unfold dotProgram
  simp [gstep, loopHead, hnot]

theorem gstep_exit (A B : Nat → Word) (K : Nat) (sum : Word) :
    grun (dotProgram K) 3 (loopHead A B K sum) = exitState A B K sum := by
  unfold dotProgram
  simp [gstep, loopHead, exitState]

theorem dotProgram_run_aux (A B : Nat → Word) (K k : Nat) (sum : Word) (n : Nat)
    (hn : k + n = K) :
    grun (dotProgram K) (8 * n + 3) (loopHead A B k sum) =
      exitState A B K (sum + dotRange A B k n) := by
  induction n generalizing k sum with
  | zero =>
      have hk : k = K := by omega
      rw [hk]
      simpa [dotRange] using gstep_exit A B K sum
  | succ n ih =>
      have hlt : k < K := by omega
      have hnext : k + 1 + n = K := by omega
      rw [show 8 * (n + 1) + 3 = 8 + (8 * n + 3) by omega]
      rw [grun_add]
      rw [gstep_iter A B K k sum hlt]
      rw [ih (k + 1) (sum + A k * B k) hnext]
      simp [dotRange, BitVec.add_assoc]

theorem dotProgram_correct (A B : Nat → Word) (K : Nat) :
    let s := grun (dotProgram K) (8 * K + 3) (loopHead A B 0 0)
    s.halted = true ∧ s.k = K ∧ s.sum = dotRange A B 0 K := by
  have h := dotProgram_run_aux A B K 0 0 K (by omega)
  change (grun (dotProgram K) (8 * K + 3) (loopHead A B 0 0)).halted = true ∧
    (grun (dotProgram K) (8 * K + 3) (loopHead A B 0 0)).k = K ∧
    (grun (dotProgram K) (8 * K + 3) (loopHead A B 0 0)).sum = dotRange A B 0 K
  rw [h]
  simp [exitState]

end IntelGpu
