-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Epilogue

@[expose] public section

/-!
# Epilogue with a leading dimension

Stage 21 wrote the accumulator tile packed at width `N`. Real GEMM epilogues
write with a leading dimension `ldC ≥ N`, so the tile lands in a row-major
`M x N` matrix at its own origin.

The only new ingredient is that two distinct tile indices may not alias once
strided by `ldC`: `packed_inj` shows `k ↦ (k / N) * ldC + k % N` is injective
on `k < M * N` when `N ≤ ldC`.
-/

namespace IntelGpu

/-- Strided tile indices do not alias: with `N ≤ ldC` and both remainders
below `N`, equal addresses force equal indices. -/
theorem packed_inj (N ldC : Nat) (hldC : N ≤ ldC) :
    ∀ k1 k2, k1 % N < N → k2 % N < N →
      k1 / N * ldC + k1 % N = k2 / N * ldC + k2 % N → k1 = k2 := by
  intro k1 k2 h1 h2 heq
  have hq : k1 / N = k2 / N := by
    rcases Nat.lt_trichotomy (k1 / N) (k2 / N) with hlt | heq' | hgt
    · have hlt' : k1 / N * ldC + k1 % N < k2 / N * ldC + k2 % N := by
        have hr : k1 % N < ldC := Nat.lt_of_lt_of_le h1 hldC
        have hstep1 : k1 / N * ldC + k1 % N < k1 / N * ldC + ldC :=
          Nat.add_lt_add_left hr (k1 / N * ldC)
        have hstep2 : k1 / N * ldC + ldC ≤ k2 / N * ldC := by
          have hmul : (k1 / N + 1) * ldC ≤ k2 / N * ldC := Nat.mul_le_mul_right ldC (by omega)
          rwa [Nat.succ_mul] at hmul
        have hstep3 : k2 / N * ldC ≤ k2 / N * ldC + k2 % N := Nat.le_add_right _ _
        omega
      omega
    · exact heq'
    · have hlt' : k2 / N * ldC + k2 % N < k1 / N * ldC + k1 % N := by
        have hr : k2 % N < ldC := Nat.lt_of_lt_of_le h2 hldC
        have hstep1 : k2 / N * ldC + k2 % N < k2 / N * ldC + ldC :=
          Nat.add_lt_add_left hr (k2 / N * ldC)
        have hstep2 : k2 / N * ldC + ldC ≤ k1 / N * ldC := by
          have hmul : (k2 / N + 1) * ldC ≤ k1 / N * ldC := Nat.mul_le_mul_right ldC (by omega)
          rwa [Nat.succ_mul] at hmul
        have hstep3 : k1 / N * ldC ≤ k1 / N * ldC + k1 % N := Nat.le_add_right _ _
        omega
      omega
  have hr : k1 % N = k2 % N := by
    rw [hq] at heq
    omega
  have hdec1 : k1 / N * N + k1 % N = k1 := by
    simpa [Nat.mul_comm] using Nat.div_add_mod k1 N
  have hdec2 : k2 / N * N + k2 % N = k2 := by
    simpa [Nat.mul_comm] using Nat.div_add_mod k2 N
  rw [hq, hr] at hdec1
  omega

/-- Epilogue step with a leading dimension: store at the strided address for
the current tile index. -/
def lstep (base ldC N : Nat) (prog : List EInstr) (s : EState) : EState :=
  match prog[s.pc]? with
  | none => { s with halted := true }
  | some .store =>
      { s with
        mem := update s.mem (base + (s.idx / N) * ldC + s.idx % N)
          (s.acc (s.idx / N) (s.idx % N)),
        pc := s.pc + 1 }
  | some .inc => { s with idx := s.idx + 1, pc := s.pc + 1 }
  | some (.cmpGe T) => { s with pred := decide (T ≤ s.idx), pc := s.pc + 1 }
  | some (.jmpiIf target) => { s with pc := if s.pred then target else s.pc + 1 }
  | some (.jmpi target) => { s with pc := target }

def lrun (base ldC N : Nat) (prog : List EInstr) : Nat → EState → EState
  | 0, s => s
  | n + 1, s => lrun base ldC N prog n (lstep base ldC N prog s)

@[simp] theorem lrun_zero (base ldC N : Nat) (prog : List EInstr) (s : EState) :
    lrun base ldC N prog 0 s = s := rfl

@[simp] theorem lrun_succ (base ldC N : Nat) (prog : List EInstr) (n : Nat) (s : EState) :
    lrun base ldC N prog (n + 1) s = lrun base ldC N prog n (lstep base ldC N prog s) := rfl

theorem lrun_add (base ldC N : Nat) (prog : List EInstr) (a b : Nat) (s : EState) :
    lrun base ldC N prog (a + b) s = lrun base ldC N prog b (lrun base ldC N prog a s) := by
  induction a generalizing s with
  | zero => simp
  | succ a ih =>
      calc
        lrun base ldC N prog (a + 1 + b) s =
            lrun base ldC N prog (a + b) (lstep base ldC N prog s) := by
          rw [show a + 1 + b = (a + b) + 1 by omega]
          rfl
        _ = lrun base ldC N prog b (lrun base ldC N prog a (lstep base ldC N prog s)) :=
          ih (lstep base ldC N prog s)
        _ = lrun base ldC N prog b (lrun base ldC N prog (a + 1) s) := rfl

/-- Loop-head invariant for the strided epilogue. -/
structure LInv (base ldC N t0 : Nat) (acc : Nat → Nat → Word) (s : EState) : Prop where
  written : ∀ k < t0, s.mem (base + (k / N) * ldC + k % N) = acc (k / N) (k % N)
  accEq : s.acc = acc
  idxEq : s.idx = t0
  predF : s.pred = false
  pc0 : s.pc = 0
  haltF : s.halted = false

theorem lstep_iter (base ldC N T t0 : Nat) (hN : 0 < N) (hldC : N ≤ ldC)
    (acc : Nat → Nat → Word) (s : EState) (h : LInv base ldC N t0 acc s) (ht : t0 < T) :
    LInv base ldC N (t0 + 1) acc (lrun base ldC N (epilogueProg T) 5 s) := by
  have hknot : ¬ T ≤ t0 := by omega
  have hmodt : t0 % N < N := Nat.mod_lt _ hN
  have hmem : ∀ k, (lrun base ldC N (epilogueProg T) 5 s).mem
      (base + (k / N) * ldC + k % N) =
      update s.mem (base + (t0 / N) * ldC + t0 % N) (acc (t0 / N) (t0 % N))
        (base + (k / N) * ldC + k % N) := by
    intro k
    simp [epilogueProg, lrun, lstep, h.pc0, h.idxEq, h.accEq, hknot]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [hmem k]
    by_cases hkt : k = t0
    · subst hkt
      rw [update_at]
    · have hmodk : k % N < N := Nat.mod_lt _ hN
      have hne : base + (k / N) * ldC + k % N ≠ base + (t0 / N) * ldC + t0 % N := by
        intro heq
        have hcore : (k / N) * ldC + k % N = (t0 / N) * ldC + t0 % N := by omega
        exact hkt (packed_inj N ldC hldC k t0 hmodk hmodt hcore)
      rw [update_away _ _ _ _ hne]
      exact h.written k (by omega)
  · simp [epilogueProg, lrun, lstep, h.pc0, h.idxEq, h.accEq, hknot]
  · simp [epilogueProg, lrun, lstep, h.pc0, h.idxEq, h.accEq, hknot]
  · simp [epilogueProg, lrun, lstep, h.pc0, h.idxEq, h.accEq, hknot]
  · simp [epilogueProg, lrun, lstep, h.pc0, h.idxEq, h.accEq, hknot]
  · simp [epilogueProg, lrun, lstep, h.pc0, h.idxEq, h.accEq, hknot, h.haltF]

theorem lstep_exit (base ldC N T : Nat) (acc : Nat → Nat → Word) (s : EState)
    (h : LInv base ldC N T acc s) :
    (lrun base ldC N (epilogueProg T) 3 s).halted = true := by
  have hle : T ≤ s.idx := by rw [h.idxEq]; omega
  simp [epilogueProg, lrun, lstep, h.pc0, hle]

theorem lrun_exit_mem (base ldC N T : Nat) (acc : Nat → Nat → Word) (s : EState)
    (h : LInv base ldC N T acc s) (k : Nat) :
    (lrun base ldC N (epilogueProg T) 3 s).mem (base + (k / N) * ldC + k % N) =
      s.mem (base + (k / N) * ldC + k % N) := by
  have hle : T ≤ s.idx := by rw [h.idxEq]; omega
  simp [epilogueProg, lrun, lstep, h.pc0, hle]

theorem epilogueLd_run_aux (base ldC N : Nat) (hN : 0 < N) (hldC : N ≤ ldC)
    (acc : Nat → Nat → Word) (T : Nat) :
    ∀ (n : Nat) (t0 : Nat) (s : EState), t0 + n = T → LInv base ldC N t0 acc s →
      (lrun base ldC N (epilogueProg T) (5 * n + 3) s).halted = true ∧
        ∀ k < T, (lrun base ldC N (epilogueProg T) (5 * n + 3) s).mem
          (base + (k / N) * ldC + k % N) = acc (k / N) (k % N) := by
  intro n
  induction n with
  | zero =>
      intro t0 s ht h
      have ht0 : t0 = T := by omega
      have hT : LInv base ldC N T acc s := ht0 ▸ h
      refine ⟨?_, ?_⟩
      · simpa using lstep_exit base ldC N T acc s hT
      · intro k hk
        rw [lrun_exit_mem base ldC N T acc s hT k]
        exact hT.written k (by omega)
  | succ n ih =>
      intro t0 s ht h
      have hlt : t0 < T := by omega
      have hnext : t0 + 1 + n = T := by omega
      have hiter := lstep_iter base ldC N T t0 hN hldC acc s h hlt
      have hrun : lrun base ldC N (epilogueProg T) (5 * (n + 1) + 3) s =
          lrun base ldC N (epilogueProg T) (5 * n + 3)
            (lrun base ldC N (epilogueProg T) 5 s) := by
        rw [show 5 * (n + 1) + 3 = 5 + (5 * n + 3) by omega]
        exact lrun_add base ldC N (epilogueProg T) 5 (5 * n + 3) s
      rw [hrun]
      exact ih (t0 + 1) (lrun base ldC N (epilogueProg T) 5 s) hnext hiter

/-- Strided epilogue: `5 * M * N + 3` steps write the whole accumulator tile
at leading dimension `ldC`. -/
theorem epilogueLd_correct (base ldC N M : Nat) (hN : 0 < N) (hldC : N ≤ ldC)
    (mem : Nat → Word) (acc : Nat → Nat → Word) :
    let s' := lrun base ldC N (epilogueProg (M * N)) (5 * (M * N) + 3) (eHead mem acc)
    s'.halted = true ∧ ∀ m < M, ∀ n < N, s'.mem (base + m * ldC + n) = acc m n := by
  have hinit : LInv base ldC N 0 acc (eHead mem acc) :=
    ⟨by intro k hk; omega, rfl, rfl, rfl, rfl, rfl⟩
  have hres := epilogueLd_run_aux base ldC N hN hldC acc (M * N) (M * N) 0
    (eHead mem acc) (by omega) hinit
  dsimp only
  refine ⟨hres.1, ?_⟩
  intro m hm n hn
  have hlt : m * N + n < M * N := by
    have h1 : m * N + n < m * N + N := Nat.add_lt_add_left hn (m * N)
    have h2 : m * N + N = (m + 1) * N := (Nat.succ_mul m N).symm
    have h3 : (m + 1) * N ≤ M * N := Nat.mul_le_mul_right N (by omega)
    omega
  have hk := hres.2 (m * N + n) hlt
  rw [mul_add_div hN m n hn, mul_add_mod m n N, Nat.mod_eq_of_lt hn] at hk
  exact hk

end IntelGpu
