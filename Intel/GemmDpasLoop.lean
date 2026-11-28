-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Dpas

@[expose] public section

/-!
# Executed DPAS main loop

A pc-level machine that runs the DPAS mainloop of a GEMM tile: for each depth
slab it loads the A and B operands into the tile registers, issues `dpas`
against the accumulator tile, and branches back while `t < T`.

`dpasProg_correct` proves that `7 * T + 3` steps halt with the accumulator tile
equal to `dotMat` at depth `T * d` — the executable counterpart of
`dpasRun_correct`.
-/

namespace IntelGpu

structure XState where
  A : Nat → Nat → Word
  B : Nat → Nat → Word
  acc : Nat → Nat → Word
  t : Nat
  pred : Bool
  pc : Nat
  halted : Bool

inductive XInstr where
  | loadA
  | loadB
  | dpas
  | incT
  | cmpGe (T : Nat)
  | jmpiIf (target : Nat)
  | jmpi (target : Nat)
  deriving Repr

def xstep (A B : Nat → Nat → Word) (i j d : Nat) (prog : List XInstr) (s : XState) :
    XState :=
  match prog[s.pc]? with
  | none => { s with halted := true }
  | some .loadA => { s with A := fun k m => A (i + m) (s.t * d + k), pc := s.pc + 1 }
  | some .loadB => { s with B := fun k n => B (s.t * d + k) (j + n), pc := s.pc + 1 }
  | some .dpas => { s with acc := fun m n => s.acc m n + dpasSlab d s.A s.B m n, pc := s.pc + 1 }
  | some .incT => { s with t := s.t + 1, pc := s.pc + 1 }
  | some (.cmpGe T) => { s with pred := decide (T ≤ s.t), pc := s.pc + 1 }
  | some (.jmpiIf target) => { s with pc := if s.pred then target else s.pc + 1 }
  | some (.jmpi target) => { s with pc := target }

def xrun (A B : Nat → Nat → Word) (i j d : Nat) (prog : List XInstr) :
    Nat → XState → XState
  | 0, s => s
  | n + 1, s => xrun A B i j d prog n (xstep A B i j d prog s)

@[simp] theorem xrun_zero (A B : Nat → Nat → Word) (i j d : Nat) (prog : List XInstr)
    (s : XState) : xrun A B i j d prog 0 s = s := rfl

@[simp] theorem xrun_succ (A B : Nat → Nat → Word) (i j d : Nat) (prog : List XInstr)
    (n : Nat) (s : XState) :
    xrun A B i j d prog (n + 1) s = xrun A B i j d prog n (xstep A B i j d prog s) := rfl

theorem xrun_add (A B : Nat → Nat → Word) (i j d : Nat) (prog : List XInstr)
    (a b : Nat) (s : XState) :
    xrun A B i j d prog (a + b) s = xrun A B i j d prog b (xrun A B i j d prog a s) := by
  induction a generalizing s with
  | zero => simp
  | succ a ih =>
      calc
        xrun A B i j d prog (a + 1 + b) s =
            xrun A B i j d prog (a + b) (xstep A B i j d prog s) := by
          rw [show a + 1 + b = (a + b) + 1 by omega]
          rfl
        _ = xrun A B i j d prog b (xrun A B i j d prog a (xstep A B i j d prog s)) :=
          ih (xstep A B i j d prog s)
        _ = xrun A B i j d prog b (xrun A B i j d prog (a + 1) s) := rfl

def dpasProg (T : Nat) : List XInstr :=
  [.cmpGe T, .jmpiIf 7, .loadA, .loadB, .dpas, .incT, .jmpi 0]

structure XInv (Ag Bg : Nat → Nat → Word) (i j d t0 : Nat) (s : XState) : Prop where
  acc : ∀ m n, s.acc m n = dotMatFrom Ag Bg (i + m) (j + n) 0 (t0 * d)
  tEq : s.t = t0
  predF : s.pred = false
  pc0 : s.pc = 0
  haltF : s.halted = false

theorem xstep_iter (Ag Bg : Nat → Nat → Word) (i j d T t0 : Nat) (s : XState)
    (h : XInv Ag Bg i j d t0 s) (ht : t0 < T) :
    XInv Ag Bg i j d (t0 + 1) (xrun Ag Bg i j d (dpasProg T) 7 s) := by
  have hknot : ¬ T ≤ t0 := by omega
  have hA : ∀ m n, (xrun Ag Bg i j d (dpasProg T) 7 s).acc m n =
      s.acc m n + dpasSlab d (fun k m' => Ag (i + m') (t0 * d + k))
        (fun k n' => Bg (t0 * d + k) (j + n')) m n := by
    intro m n
    simp [dpasProg, xrun, xstep, h.pc0, h.tEq, hknot]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m n
    rw [hA m n, h.acc m n, dpasSlab_eq_dotMatFrom Ag Bg i j (t0 * d) d m n]
    rw [Nat.succ_mul, dotMatFrom_append]
    rw [show 0 + t0 * d = t0 * d by omega]
  · simp [dpasProg, xrun, xstep, h.pc0, h.tEq, hknot]
  · simp [dpasProg, xrun, xstep, h.pc0, h.tEq, hknot]
  · simp [dpasProg, xrun, xstep, h.pc0, h.tEq, hknot]
  · simp [dpasProg, xrun, xstep, h.pc0, h.tEq, hknot, h.haltF]

theorem dpasProg_exit (Ag Bg : Nat → Nat → Word) (i j d T : Nat) (s : XState)
    (h : XInv Ag Bg i j d T s) :
    (xrun Ag Bg i j d (dpasProg T) 3 s).halted = true := by
  have hle : T ≤ s.t := by rw [h.tEq]; omega
  simp [dpasProg, xrun, xstep, h.pc0, hle]

theorem dpasProg_run_aux (Ag Bg : Nat → Nat → Word) (i j d T : Nat) :
    ∀ (n : Nat), ∀ (t0 : Nat) (s : XState), t0 + n = T → XInv Ag Bg i j d t0 s →
      (xrun Ag Bg i j d (dpasProg T) (7 * n + 3) s).halted = true ∧
        ∀ m n', (xrun Ag Bg i j d (dpasProg T) (7 * n + 3) s).acc m n' =
          dotMatFrom Ag Bg (i + m) (j + n') 0 (T * d) := by
  intro n
  induction n with
  | zero =>
      intro t0 s ht h
      have ht0 : t0 = T := by omega
      have hT : XInv Ag Bg i j d T s := ht0 ▸ h
      refine ⟨?_, ?_⟩
      · simpa using dpasProg_exit Ag Bg i j d T s hT
      · intro m n'
        have hacc : (xrun Ag Bg i j d (dpasProg T) (7 * 0 + 3) s).acc m n' =
            s.acc m n' := by
          have hle : T ≤ s.t := by rw [hT.tEq]; omega
          simp [dpasProg, xrun, xstep, hT.pc0, hle]
        rw [hacc, hT.acc m n']
  | succ n ih =>
      intro t0 s ht h
      have hlt : t0 < T := by omega
      have hnext : t0 + 1 + n = T := by omega
      have hiter := xstep_iter Ag Bg i j d T t0 s h hlt
      have hrun : xrun Ag Bg i j d (dpasProg T) (7 * (n + 1) + 3) s =
          xrun Ag Bg i j d (dpasProg T) (7 * n + 3)
            (xrun Ag Bg i j d (dpasProg T) 7 s) := by
        rw [show 7 * (n + 1) + 3 = 7 + (7 * n + 3) by omega]
        exact xrun_add Ag Bg i j d (dpasProg T) 7 (7 * n + 3) s
      rw [hrun]
      exact ih (t0 + 1) (xrun Ag Bg i j d (dpasProg T) 7 s) hnext hiter

theorem dpasProg_correct (Ag Bg : Nat → Nat → Word) (i j d T : Nat)
    (s : XState) (h : XInv Ag Bg i j d 0 s) :
    let s' := xrun Ag Bg i j d (dpasProg T) (7 * T + 3) s
    s'.halted = true ∧
      ∀ m n, s'.acc m n = dotMat Ag Bg (i + m) (j + n) (T * d) := by
  have hres := dpasProg_run_aux Ag Bg i j d T T 0 s (by omega) h
  refine ⟨hres.1, ?_⟩
  intro m n
  rw [hres.2 m n]
  rfl

end IntelGpu
