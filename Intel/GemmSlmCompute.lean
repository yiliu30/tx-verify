-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.WControl
public import Intel.GemmSlm

@[expose] public section

/-!
# Executed SLM GEMM tile

The stage-16 example stopped at the specification level: after the barrier the
staged tile was shown to compute `dotMat`. This stage runs the compute phase as
an actual loop over the workgroup machine.

`computeProg K` walks `k < K`: it loads `A` for the lane's row from SLM, loads
the `B` column from global memory, multiplies, accumulates into register 4, and
advances the SLM/global pointers and the shared counter.

Proved:

- `computeProg_correct`: from a state holding the staged tile, `10 * K + 3`
  steps halt with `regs 4 = dotMat A B l 0 K` for both lanes.
- `gemmTile_executed`: the stage-16 staging program, its barrier, and the
  compute loop compose into one executed GEMM tile.
-/

namespace IntelGpu

theorem dotRange_add_last (A B : Nat → Word) (k n : Nat) :
    dotRange A B k (n + 1) = dotRange A B k n + A (k + n) * B (k + n) := by
  induction n generalizing k with
  | zero => simp [dotRange, BitVec.add_zero]
  | succ n ih =>
      rw [dotRange, ih (k + 1), dotRange]
      rw [show k + 1 + n = k + (n + 1) by omega]
      rw [← BitVec.add_assoc]

theorem dotRange_eq_dotMatFrom (A B : Nat → Nat → Word) (i j : Nat) :
    ∀ (k n : Nat), dotRange (fun t => A i t) (fun t => B t j) k n =
      dotMatFrom A B i j k n := by
  intro k n
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp [dotRange, dotMatFrom, ih (k + 1)]

def computeProg (K : Nat) : List CInstr :=
  [.cmpGe K, .jmpiIf 10, .w (.loadSlm 1), .w (.load 2), .w (.mul 3 1 2),
   .w (.add 4 4 3), .w .incS, .w .incG, .incK, .jmpi 0]

/-- Loop-head invariant: `k0` columns accumulated, both lane pointers at their
`k0` offsets, and the staged tile still intact. -/
structure CRun (A B : Nat → Nat → Word) (K k0 : Nat) (slm : SLM) (mem : Nat → Word)
    (s : CState) : Prop where
  laneS : ∀ l < 2, (s.w.lanes l).sidx = l * K + k0
  laneG : ∀ l < 2, (s.w.lanes l).gidx = 2 * K + k0
  acc : ∀ l < 2, (s.w.lanes l).regs 4 = dotRange (fun t => A l t) (fun t => B t 0) 0 k0
  run : ∀ l < 2, (s.w.lanes l).done = false
  slmEq : s.w.slm = slm
  memEq : s.w.mem = mem
  phase1 : s.w.phase = 1
  pc0 : s.pc = 0
  kEq : s.k = k0
  predF : s.pred = false
  haltF : s.halted = false

theorem cstep_iter (A B : Nat → Nat → Word) (K k0 : Nat) (slm : SLM) (mem : Nat → Word)
    (s : CState) (h : CRun A B K k0 slm mem s) (hk : k0 < K)
    (hslm : ∀ l < 2, ∀ t < K, slm (l * K + t) = A l t)
    (hB : ∀ t < K, mem (2 * K + t) = B t 0) :
    CRun A B K (k0 + 1) slm mem (crun (computeProg K) 10 s) := by
  have hknot : ¬ K ≤ k0 := by omega
  have hS : ∀ l, ((crun (computeProg K) 10 s).w.lanes l).sidx =
      (s.w.lanes l).sidx + 1 := by
    intro l
    simp [computeProg, crun, cstep, wstep, h.pc0, h.kEq, hknot]
  have hG : ∀ l, ((crun (computeProg K) 10 s).w.lanes l).gidx =
      (s.w.lanes l).gidx + 1 := by
    intro l
    simp [computeProg, crun, cstep, wstep, h.pc0, h.kEq, hknot]
  have hDone : ∀ l, ((crun (computeProg K) 10 s).w.lanes l).done =
      (s.w.lanes l).done := by
    intro l
    simp [computeProg, crun, cstep, wstep, h.pc0, h.kEq, hknot]
  have hAcc : ∀ l, ((crun (computeProg K) 10 s).w.lanes l).regs 4 =
      (s.w.lanes l).regs 4 + s.w.slm ((s.w.lanes l).sidx) * s.w.mem ((s.w.lanes l).gidx) := by
    intro l
    simp [computeProg, crun, cstep, wstep, h.pc0, h.kEq, hknot]
  have hSlm : (crun (computeProg K) 10 s).w.slm = slm := by
    simp [computeProg, crun, cstep, wstep, h.pc0, h.kEq, hknot, h.slmEq]
  have hMem : (crun (computeProg K) 10 s).w.mem = mem := by
    simp [computeProg, crun, cstep, wstep, h.pc0, h.kEq, hknot, h.memEq]
  have hPhase : (crun (computeProg K) 10 s).w.phase = s.w.phase := by
    simp [computeProg, crun, cstep, wstep, h.pc0, h.kEq, hknot]
  have hPc : (crun (computeProg K) 10 s).pc = 0 := by
    simp [computeProg, crun, cstep, wstep, h.pc0, h.kEq, hknot]
  have hKk : (crun (computeProg K) 10 s).k = k0 + 1 := by
    simp [computeProg, crun, cstep, wstep, h.pc0, h.kEq, hknot]
  have hPred : (crun (computeProg K) 10 s).pred = false := by
    simp [computeProg, crun, cstep, wstep, h.pc0, h.kEq, hknot]
  have hHalt : (crun (computeProg K) 10 s).halted = s.halted := by
    simp [computeProg, crun, cstep, wstep, h.pc0, h.kEq, hknot]
  refine ⟨?_, ?_, ?_, ?_, hSlm, hMem, ?_, hPc, hKk, hPred, by rw [hHalt]; exact h.haltF⟩
  · intro l hl
    rw [hS l, h.laneS l hl]; omega
  · intro l hl
    rw [hG l, h.laneG l hl]; omega
  · intro l hl
    rw [hAcc l, h.laneS l hl, h.laneG l hl, h.slmEq, h.memEq, hslm l hl k0 hk, hB k0 hk,
      h.acc l hl]
    rw [dotRange_add_last]
    simp
  · intro l hl
    rw [hDone l]; exact h.run l hl
  · rw [hPhase]; exact h.phase1

theorem cstep_exit (A B : Nat → Nat → Word) (K : Nat) (slm : SLM) (mem : Nat → Word)
    (s : CState) (h : CRun A B K K slm mem s) :
    (crun (computeProg K) 3 s).halted = true := by
  have hle : K ≤ s.k := by rw [h.kEq]; omega
  simp [computeProg, crun, cstep, h.pc0, hle]

-- The three exit steps (`cmpGe`, `jmpiIf`, off-the-end halt) leave the lane
-- registers and the barrier phase untouched. `hle` is consumed by `decide`
-- reduction of the branch condition, which the unused-simp-argument linter
-- does not track.
set_option linter.unusedSimpArgs false in
theorem cstep_exit_frames (A B : Nat → Nat → Word) (K : Nat) (slm : SLM)
    (mem : Nat → Word) (s : CState) (h : CRun A B K K slm mem s) (l : Nat) :
    ((crun (computeProg K) 3 s).w.lanes l).regs 4 = (s.w.lanes l).regs 4 ∧
      (crun (computeProg K) 3 s).w.phase = s.w.phase := by
  have hle : K ≤ s.k := by rw [h.kEq]; omega
  constructor <;> simp [computeProg, crun, cstep, h.pc0, hle]

/-- Exit condition of the compute loop. -/
structure CExit (A B : Nat → Nat → Word) (K : Nat) (slm : SLM) (mem : Nat → Word)
    (s : CState) : Prop where
  acc : ∀ l < 2, (s.w.lanes l).regs 4 = dotRange (fun t => A l t) (fun t => B t 0) 0 K
  phase1 : s.w.phase = 1
  haltT : s.halted = true

theorem computeProg_run_aux (A B : Nat → Nat → Word) (K : Nat) (slm : SLM)
    (mem : Nat → Word) (hslm : ∀ l < 2, ∀ t < K, slm (l * K + t) = A l t)
    (hB : ∀ t < K, mem (2 * K + t) = B t 0) : ∀ (n : Nat), n ≤ K →
    ∀ (k0 : Nat) (s : CState), k0 + n = K → CRun A B K k0 slm mem s →
      CExit A B K slm mem (crun (computeProg K) (10 * n + 3) s) := by
  intro n
  induction n with
  | zero =>
      intro _ k0 s hk h
      have hk0 : k0 = K := by omega
      have hK : CRun A B K K slm mem s := hk0 ▸ h
      refine ⟨?_, ?_, ?_⟩
      · intro l hl
        have hf := cstep_exit_frames A B K slm mem s hK l
        rw [hf.1, hK.acc l hl]
      · have hf := cstep_exit_frames A B K slm mem s hK 0
        rw [hf.2]; exact hK.phase1
      · simpa using cstep_exit A B K slm mem s hK
  | succ n ih =>
      intro _ k0 s hk h
      have hlt : k0 < K := by omega
      have hnext : k0 + 1 + n = K := by omega
      have hiter := cstep_iter A B K k0 slm mem s h hlt hslm hB
      have hrun : crun (computeProg K) (10 * (n + 1) + 3) s =
          crun (computeProg K) (10 * n + 3) (crun (computeProg K) 10 s) := by
        rw [show 10 * (n + 1) + 3 = 10 + (10 * n + 3) by omega]
        exact crun_add (computeProg K) 10 (10 * n + 3) s
      rw [hrun]
      exact ih (by omega) (k0 + 1) (crun (computeProg K) 10 s) hnext hiter

theorem computeProg_correct (A B : Nat → Nat → Word) (K : Nat) (slm : SLM)
    (mem : Nat → Word) (hslm : ∀ l < 2, ∀ t < K, slm (l * K + t) = A l t)
    (hB : ∀ t < K, mem (2 * K + t) = B t 0) (s : CState)
    (h : CRun A B K 0 slm mem s) :
    let s' := crun (computeProg K) (10 * K + 3) s
    s'.halted = true ∧ s'.w.phase = 1 ∧
      ∀ l < 2, (s'.w.lanes l).regs 4 = dotMat A B l 0 K := by
  have hres := computeProg_run_aux A B K slm mem hslm hB K (Nat.le_refl K) 0 s
    (by omega) h
  refine ⟨hres.haltT, hres.phase1, ?_⟩
  intro l hl
  rw [hres.acc l hl]
  exact dotRange_eq_dotMatFrom A B l 0 0 K

/-- Reposition the post-barrier workgroup for the compute loop: lane `l` reads
its own staged A row from SLM word `l * K`, reads the B column from global word
`2 * K`, and starts its accumulator at zero. -/
def computeInit (K : Nat) (s : WState) : CState :=
  { w :=
      { s with
        lanes := fun l =>
          { s.lanes l with
            sidx := l * K
            gidx := 2 * K
            regs := fun r => if r = 4 then 0 else (s.lanes l).regs r } }
    k := 0
    pred := false
    pc := 0
    halted := false }

theorem computeInit_CRun (A B : Nat → Nat → Word) (K : Nat) (mem : Nat → Word)
    (s : WState) (hphase : s.phase = 1) (hmem : s.mem = mem)
    (hrun : ∀ l < 2, (s.lanes l).done = false) :
    CRun A B K 0 s.slm mem (computeInit K s) := by
  refine ⟨?_, ?_, ?_, ?_, rfl, hmem, hphase, rfl, rfl, rfl, rfl⟩
  · intro l _
    simp [computeInit]
  · intro l _
    simp [computeInit]
  · intro l _
    simp [computeInit, dotRange]
  · intro l hl
    simpa [computeInit] using hrun l hl

/-- The staged GEMM tile executes end to end: staging, barrier, then the SLM
compute loop, halting with `dotMat` in every lane's accumulator. -/
theorem gemmTile_executed (A B : Nat → Nat → Word) (K : Nat) (mem : Nat → Word)
    (s : WState) (h : StageStart K 0 mem s)
    (hA : ∀ l < 2, ∀ k < K, mem (l * K + k) = A l k)
    (hB : ∀ k < K, mem (2 * K + k) = B k 0) :
    let s1 := wrun s (stageProg K ++ [.barrier])
    let fin := crun (computeProg K) (10 * K + 3) (computeInit K s1)
    fin.halted = true ∧ fin.w.phase = 1 ∧
      ∀ l < 2, (fin.w.lanes l).regs 4 = dotMat A B l 0 K := by
  have hb := stageBarrier_correct K mem s h
  have hinv := stageProg_correct K mem s h
  dsimp only at hb ⊢
  have hslm : ∀ l < 2, ∀ t < K,
      (wrun s (stageProg K ++ [.barrier])).slm (l * K + t) = A l t := by
    intro l hl t ht
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · have hA0 : mem t = A 0 t := by simpa using hA 0 (by omega) t ht
      simpa using (hb.2.2.1 t ht).trans hA0
    · have hA1 : mem (K + t) = A 1 t := by simpa using hA 1 (by omega) t ht
      simpa using (hb.2.2.2 t ht).trans hA1
  have hdone : ∀ l, ((wrun s (stageProg K ++ [.barrier])).lanes l).done =
      ((wrun s (stageProg K)).lanes l).done := by
    intro l
    rw [wrun_append, wrun_cons, wrun_nil, wstep_barrier_done]
  have hrun : ∀ l < 2, ((wrun s (stageProg K ++ [.barrier])).lanes l).done = false := by
    intro l hl
    rw [hdone l]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · exact hinv.run0
    · exact hinv.run1
  exact computeProg_correct A B K _ mem hslm hB _
    (computeInit_CRun A B K mem _ hb.1 hb.2.1 hrun)

end IntelGpu
