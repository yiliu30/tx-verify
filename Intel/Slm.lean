-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Asm

@[expose] public section

/-!
# Workgroup SLM and barrier semantics

A two-lane workgroup machine over word-indexed global memory and shared local
memory (SLM). Each lane owns data registers, a global word pointer, an SLM
word pointer, and a `done` flag.

`barrier` is modeled as a workgroup-wide sync: it only advances when no lane
has finished early (`barrierOK`), and it bumps a `phase` counter that records
how many syncs the workgroup has completed. If a lane has already finished,
the barrier is stuck and the phase does not advance, which is the modeled
deadlock symptom for divergent exit.

The model deliberately does not encode memory-visibility timing: SLM writes
are visible to every lane as soon as they retire. What the barrier contributes
is the ordering guarantee that all lanes have finished the staging phase
before any lane starts the compute phase.
-/

namespace IntelGpu

abbrev SLM := Nat → Word

structure Lane where
  regs : Nat → Word
  gidx : Nat
  sidx : Nat
  done : Bool

structure WState where
  lanes : Nat → Lane
  mem : Nat → Word
  slm : SLM
  phase : Nat

inductive WInstr where
  | load (dst : Nat)
  | loadSlm (dst : Nat)
  | storeSlm (src : Nat)
  | mul (dst a b : Nat)
  | add (dst a b : Nat)
  | incG
  | incS
  | eot
  | barrier
  deriving Repr

/-- Simultaneous SLM store: lane 0 writes first, lane 1 last. -/
def slmStore (s : WState) (src : Nat) : SLM :=
  update (update s.slm (s.lanes 0).sidx ((s.lanes 0).regs src))
    (s.lanes 1).sidx ((s.lanes 1).regs src)

/-- Every lane is still running, so a barrier can retire. -/
def barrierOK (s : WState) : Bool := !(s.lanes 0).done && !(s.lanes 1).done

def wstep (s : WState) : WInstr → WState
  | .load dst =>
      { s with lanes := fun l =>
          { s.lanes l with regs := fun r =>
              if r = dst then s.mem (s.lanes l).gidx else (s.lanes l).regs r } }
  | .loadSlm dst =>
      { s with lanes := fun l =>
          { s.lanes l with regs := fun r =>
              if r = dst then s.slm (s.lanes l).sidx else (s.lanes l).regs r } }
  | .storeSlm src => { s with slm := slmStore s src }
  | .mul dst a b =>
      { s with lanes := fun l =>
          { s.lanes l with regs := fun r =>
              if r = dst then (s.lanes l).regs a * (s.lanes l).regs b
              else (s.lanes l).regs r } }
  | .add dst a b =>
      { s with lanes := fun l =>
          { s.lanes l with regs := fun r =>
              if r = dst then (s.lanes l).regs a + (s.lanes l).regs b
              else (s.lanes l).regs r } }
  | .incG =>
      { s with lanes := fun l => { s.lanes l with gidx := (s.lanes l).gidx + 1 } }
  | .incS =>
      { s with lanes := fun l => { s.lanes l with sidx := (s.lanes l).sidx + 1 } }
  | .eot =>
      { s with lanes := fun l => { s.lanes l with done := true } }
  | .barrier => if barrierOK s then { s with phase := s.phase + 1 } else s

def wrun (s : WState) (is : List WInstr) : WState := is.foldl wstep s

@[simp] theorem wrun_nil (s : WState) : wrun s [] = s := rfl

@[simp] theorem wrun_cons (s : WState) (i : WInstr) (is : List WInstr) :
    wrun s (i :: is) = wrun (wstep s i) is := rfl

theorem wrun_append (s : WState) (as bs : List WInstr) :
    wrun s (as ++ bs) = wrun (wrun s as) bs := by
  simp [wrun, List.foldl_append]

/-- Point one lane's SLM pointer at a word index. -/
def setSidx (s : WState) (l i : Nat) : WState :=
  { s with lanes := fun l' => if l' = l then { s.lanes l with sidx := i } else s.lanes l' }

@[simp] theorem wstep_load_regs (s : WState) (dst l : Nat) :
    ((wstep s (.load dst)).lanes l).regs dst = s.mem (s.lanes l).gidx := by
  simp [wstep]

@[simp] theorem wstep_loadSlm_regs (s : WState) (dst l : Nat) :
    ((wstep s (.loadSlm dst)).lanes l).regs dst = s.slm (s.lanes l).sidx := by
  simp [wstep]

@[simp] theorem wstep_mul_regs (s : WState) (dst a b l : Nat) :
    ((wstep s (.mul dst a b)).lanes l).regs dst =
      (s.lanes l).regs a * (s.lanes l).regs b := by
  simp [wstep]

@[simp] theorem wstep_add_regs (s : WState) (dst a b l : Nat) :
    ((wstep s (.add dst a b)).lanes l).regs dst =
      (s.lanes l).regs a + (s.lanes l).regs b := by
  simp [wstep]

@[simp] theorem wstep_incG (s : WState) (l : Nat) :
    ((wstep s .incG).lanes l).gidx = (s.lanes l).gidx + 1 := by
  simp [wstep]

@[simp] theorem wstep_incS (s : WState) (l : Nat) :
    ((wstep s .incS).lanes l).sidx = (s.lanes l).sidx + 1 := by
  simp [wstep]

@[simp] theorem wstep_eot_done (s : WState) (l : Nat) :
    ((wstep s .eot).lanes l).done = true := by
  simp [wstep]

@[simp] theorem setSidx_self (s : WState) (l i : Nat) :
    ((setSidx s l i).lanes l).sidx = i := by
  simp [setSidx]

theorem setSidx_other (s : WState) (l l' i : Nat) (h : l' ≠ l) :
    (setSidx s l i).lanes l' = s.lanes l' := by
  simp [setSidx, h]

end IntelGpu
