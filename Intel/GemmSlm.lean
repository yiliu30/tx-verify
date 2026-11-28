-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Slm
public import Intel.GemmMatrix

@[expose] public section

/-!
# Two-lane GEMM tile staged through SLM

The workgroup example behind the SLM/barrier semantics: lane 0 stages A row 0
into SLM words `[0, K)` and lane 1 stages A row 1 into words `[K, 2K)`, then
the workgroup hits a barrier, and the compute phase reads the staged tile.

Proved here:

- `stageProg_correct`: after `K` staging iterations each lane's SLM slot holds
  its own row, and both lane pointers have advanced by `K`.
- `stageBarrier_correct`: the barrier retires (`phase = 1`) and the staged
  tile is readable as a whole.
- `lane0_reads_lane1`: after the barrier lane 0 reads lane 1's staged row.
- `gemmTile_slm_correct`: the staged SLM tile computes `dotMat`, i.e. the GEMM
  tile specification, for both output rows.

The compute loop itself (walking `k < K` over SLM with predicated control
flow) is the next stage; here the compute phase is specified against the SLM
contents produced by the staging phase.
-/

namespace IntelGpu

/-- One staging iteration: load `A[l][k]`, store it to the lane's SLM slot,
and advance both of the lane's pointers. -/
def stageStep : List WInstr := [.load 1, .storeSlm 1, .incG, .incS]

def stageProg : Nat → List WInstr
  | 0 => []
  | n + 1 => stageProg n ++ stageStep

@[simp] theorem stageProg_succ (n : Nat) :
    stageProg (n + 1) = stageProg n ++ stageStep := rfl

theorem stageProg_length (K : Nat) : (stageProg K).length = 4 * K := by
  induction K with
  | zero => rfl
  | succ n ih => simp [stageProg_succ, ih, stageStep]; omega

/-- Workgroup state before staging: lane 0 starts at global/SLM word `0`,
lane 1 at global/SLM word `K`, nothing has been staged, and no lane exited. -/
structure StageStart (K n : Nat) (mem : Nat → Word) (s : WState) : Prop where
  memEq : s.mem = mem
  g0 : (s.lanes 0).gidx = n
  g1 : (s.lanes 1).gidx = K + n
  s0 : (s.lanes 0).sidx = n
  s1 : (s.lanes 1).sidx = K + n
  phaseEq : s.phase = 0
  run0 : (s.lanes 0).done = false
  run1 : (s.lanes 1).done = false

/-- After `n` staging iterations: pointers advanced, and the first `n` words of
each lane's SLM slot hold that lane's row. -/
structure StageInv (K n : Nat) (mem : Nat → Word) (s : WState)
    extends StageStart K n mem s where
  low : ∀ k < n, s.slm k = mem k
  high : ∀ k < n, s.slm (K + k) = mem (K + k)

theorem stageStep_slm (s : WState) :
    (wrun s stageStep).slm =
      update (update s.slm (s.lanes 0).sidx (s.mem (s.lanes 0).gidx))
        (s.lanes 1).sidx (s.mem (s.lanes 1).gidx) := by
  simp [stageStep, wrun_cons, wstep, slmStore]

theorem update_chain_self (m : Nat → Word) (a b : Nat) (v w : Word) (h : a ≠ b) :
    update (update m a v) b w a = v := by
  simp [update, h]

theorem update_chain_last (m : Nat → Word) (a b : Nat) (v w : Word) :
    update (update m a v) b w b = w := by
  simp [update]

theorem update_chain_frame (m : Nat → Word) (a b k : Nat) (v w : Word)
    (ha : k ≠ a) (hb : k ≠ b) : update (update m a v) b w k = m k := by
  simp [update, ha, hb]

theorem stageStep_correct (K n : Nat) (mem : Nat → Word) (s : WState)
    (h : StageInv K n mem s) (hn : n < K) :
    StageInv K (n + 1) mem (wrun s stageStep) := by
  have hslm : (wrun s stageStep).slm =
      update (update s.slm n (mem n)) (K + n) (mem (K + n)) := by
    rw [stageStep_slm, h.s0, h.s1, h.g0, h.g1, h.memEq]
  refine ⟨⟨h.memEq, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [stageStep, wrun_cons, wstep, h.g0]
  · simp [stageStep, wrun_cons, wstep, h.g1]; omega
  · simp [stageStep, wrun_cons, wstep, h.s0]
  · simp [stageStep, wrun_cons, wstep, h.s1]; omega
  · simp [stageStep, wrun_cons, wstep, h.phaseEq]
  · simp [stageStep, wrun_cons, wstep, h.run0]
  · simp [stageStep, wrun_cons, wstep, h.run1]
  · intro k hk
    by_cases hkn : k = n
    · rw [hkn, hslm]
      exact update_chain_self _ _ _ _ _ (by omega)
    · have hklt : k < n := by omega
      rw [hslm]
      rw [update_chain_frame _ _ _ _ _ _ hkn (by omega)]
      exact h.low k hklt
  · intro k hk
    by_cases hkn : k = n
    · rw [hkn, hslm]
      exact update_chain_last _ _ _ _ _
    · have hklt : k < n := by omega
      rw [hslm]
      rw [update_chain_frame _ _ _ _ _ _ (by omega) (by omega)]
      exact h.high k hklt

theorem stageProg_aux (K : Nat) : ∀ (n : Nat), n ≤ K → ∀ (mem : Nat → Word) (s : WState),
    StageStart K 0 mem s → StageInv K n mem (wrun s (stageProg n)) := by
  intro n
  induction n with
  | zero =>
      intro _ mem s h
      change StageInv K 0 mem s
      exact ⟨h, by intro k hk; omega, by intro k hk; omega⟩
  | succ n ih =>
      intro hn mem s h
      have hlt : n < K := by omega
      have hInv := ih (by omega) mem s h
      rw [stageProg_succ, wrun_append]
      exact stageStep_correct K n mem (wrun s (stageProg n)) hInv hlt

theorem stageProg_correct (K : Nat) (mem : Nat → Word) (s : WState)
    (h : StageStart K 0 mem s) : StageInv K K mem (wrun s (stageProg K)) :=
  stageProg_aux K K (Nat.le_refl K) mem s h

theorem stage_barrier_ready (K : Nat) (mem : Nat → Word) (s : WState)
    (h : StageStart K 0 mem s) : barrierOK (wrun s (stageProg K)) = true := by
  have hInv := stageProg_correct K mem s h
  simp [barrierOK, hInv.run0, hInv.run1]

theorem stageBarrier_correct (K : Nat) (mem : Nat → Word) (s : WState)
    (h : StageStart K 0 mem s) :
    let s' := wrun s (stageProg K ++ [.barrier])
    s'.phase = 1 ∧ s'.mem = mem ∧
      (∀ k < K, s'.slm k = mem k) ∧
      (∀ k < K, s'.slm (K + k) = mem (K + k)) := by
  have hInv := stageProg_correct K mem s h
  have hok := stage_barrier_ready K mem s h
  dsimp only
  rw [wrun_append, wrun_cons, wrun_nil]
  rw [show wstep (wrun s (stageProg K)) .barrier =
      { wrun s (stageProg K) with phase := (wrun s (stageProg K)).phase + 1 } from by
    simp [wstep, hok]]
  exact ⟨by simp [hInv.phaseEq], hInv.memEq, hInv.low, hInv.high⟩

theorem lane0_reads_lane1 (K : Nat) (mem : Nat → Word) (s : WState) (k : Nat)
    (h : StageStart K 0 mem s) (hk : k < K) :
    ((wstep (setSidx (wrun s (stageProg K ++ [.barrier])) 0 (K + k)) (.loadSlm 1)).lanes 0).regs 1
      = mem (K + k) := by
  have hb := stageBarrier_correct K mem s h
  dsimp only at hb
  simp [wstep, setSidx, hb.2.2.2 k hk]

theorem dotRange_slm_eq_dotMatFrom (A B : Nat → Nat → Word) (slm : SLM) (l col K : Nat)
    (h : ∀ k < K, slm (l * K + k) = A l k) :
    ∀ (k n : Nat), k + n ≤ K →
      dotRange (fun t => slm (l * K + t)) (fun t => B t col) k n =
        dotMatFrom A B l col k n := by
  intro k n
  induction n generalizing k with
  | zero => intro _; rfl
  | succ n ih =>
      intro hk
      have hklt : k < K := by omega
      have hnext : k + 1 + n ≤ K := by omega
      simp [dotRange, dotMatFrom, h k hklt, ih (k + 1) hnext]

theorem dotRange_slm_eq_dotMat (A B : Nat → Nat → Word) (slm : SLM) (l col K : Nat)
    (h : ∀ k < K, slm (l * K + k) = A l k) :
    dotRange (fun t => slm (l * K + t)) (fun t => B t col) 0 K = dotMat A B l col K :=
  dotRange_slm_eq_dotMatFrom A B slm l col K h 0 K (by omega)

theorem gemmTile_slm_correct (A B : Nat → Nat → Word) (K : Nat) (mem : Nat → Word)
    (s : WState) (h : StageStart K 0 mem s)
    (hA : ∀ l < 2, ∀ k < K, mem (l * K + k) = A l k) :
    let s' := wrun s (stageProg K ++ [.barrier])
    s'.phase = 1 ∧
      ∀ l < 2, dotRange (fun t => s'.slm (l * K + t)) (fun t => B t 0) 0 K =
        dotMat A B l 0 K := by
  have hb := stageBarrier_correct K mem s h
  dsimp only at hb ⊢
  refine ⟨hb.1, ?_⟩
  intro l hl
  have hslm : ∀ k < K, (wrun s (stageProg K ++ [.barrier])).slm (l * K + k) = A l k := by
    intro k hk
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · have hA0 : mem k = A 0 k := by
        simpa using hA 0 (by omega) k hk
      simpa using (hb.2.2.1 k hk).trans hA0
    · have hA1 : mem (K + k) = A 1 k := by
        simpa using hA 1 (by omega) k hk
      simpa using (hb.2.2.2 k hk).trans hA1
  exact dotRange_slm_eq_dotMat A B _ l 0 K hslm

end IntelGpu
