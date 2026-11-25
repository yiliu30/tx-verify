-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.EpilogueLd

@[expose] public section

/-!
# The epilogue is a frame-preserving write

Stage 22 proves what the epilogue writes. This module proves what it does not
touch: every word outside the tile's `M x N` block keeps its old value.

That is what a shared output buffer needs — writing tile after tile into one
`C` cannot disturb a tile already written.

- `LInvF`: the stage-22 loop invariant with a frame field for the address `a`.
- `lstep_iter_frame`: one loop iteration preserves both the written block and
  the frame.
- `epilogueLd_frame`: the whole epilogue leaves `mem a` alone.
-/

namespace IntelGpu

/-- Loop-head invariant with an extra frame field: `a` is untouched. -/
structure LInvF (base ldC N t0 : Nat) (acc : Nat → Nat → Word) (mem : Nat → Word)
    (a : Nat) (s : EState) : Prop where
  written : ∀ k < t0, s.mem (base + (k / N) * ldC + k % N) = acc (k / N) (k % N)
  frame : s.mem a = mem a
  accEq : s.acc = acc
  idxEq : s.idx = t0
  predF : s.pred = false
  pc0 : s.pc = 0
  haltF : s.halted = false

theorem lstep_iter_frame (base ldC N M T t0 : Nat) (hN : 0 < N) (hldC : N ≤ ldC)
    (hT : T = M * N) (acc : Nat → Nat → Word) (mem : Nat → Word) (a : Nat)
    (hfar : ∀ m < M, ∀ n < N, a ≠ base + m * ldC + n)
    (s : EState) (h : LInvF base ldC N t0 acc mem a s) (ht : t0 < T) :
    LInvF base ldC N (t0 + 1) acc mem a (lrun base ldC N (epilogueProg T) 5 s) := by
  have hknot : ¬ T ≤ t0 := by omega
  have hmem : (lrun base ldC N (epilogueProg T) 5 s).mem =
      update s.mem (base + (t0 / N) * ldC + t0 % N) (acc (t0 / N) (t0 % N)) := by
    simp [epilogueProg, lrun, lstep, h.pc0, h.idxEq, h.accEq, hknot]
  have hmodN : t0 % N < N := Nat.mod_lt _ hN
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [hmem]
    by_cases hkt : k = t0
    · subst hkt
      rw [update_at]
    · have hne : base + (k / N) * ldC + k % N ≠ base + (t0 / N) * ldC + t0 % N := by
        intro heq
        have hcore : (k / N) * ldC + k % N = (t0 / N) * ldC + t0 % N := by omega
        exact hkt (packed_inj N ldC hldC k t0 (Nat.mod_lt _ hN) hmodN hcore)
      rw [update_away _ _ _ _ hne]
      exact h.written k (by omega)
  · rw [hmem]
    have hin : t0 / N < M := (Nat.div_lt_iff_lt_mul hN).2 (by rw [← hT]; exact ht)
    have hne : a ≠ base + (t0 / N) * ldC + t0 % N := hfar (t0 / N) hin (t0 % N) hmodN
    rw [update_away _ _ _ _ hne]
    exact h.frame
  · simp [epilogueProg, lrun, lstep, h.pc0, h.idxEq, h.accEq, hknot]
  · simp [epilogueProg, lrun, lstep, h.pc0, h.idxEq, h.accEq, hknot]
  · simp [epilogueProg, lrun, lstep, h.pc0, h.idxEq, h.accEq, hknot]
  · simp [epilogueProg, lrun, lstep, h.pc0, h.idxEq, h.accEq, hknot]
  · simp [epilogueProg, lrun, lstep, h.pc0, h.idxEq, h.accEq, hknot, h.haltF]

/-- The strided epilogue leaves `mem a` alone when `a` is outside the `M x N`
block at `base`. -/
theorem epilogueLd_frame (base ldC N M : Nat) (hN : 0 < N) (hldC : N ≤ ldC)
    (mem : Nat → Word) (acc : Nat → Nat → Word) (a : Nat)
    (hfar : ∀ m < M, ∀ n < N, a ≠ base + m * ldC + n) :
    (lrun base ldC N (epilogueProg (M * N)) (5 * (M * N) + 3) (eHead mem acc)).mem a =
      mem a := by
  have aux : ∀ (steps t0 : Nat) (s : EState), t0 + steps = M * N →
      LInvF base ldC N t0 acc mem a s →
      (lrun base ldC N (epilogueProg (M * N)) (5 * steps + 3) s).mem a = mem a := by
    intro steps
    induction steps with
    | zero =>
        intro t0 s ht h
        have ht0 : t0 = M * N := by omega
        have hT : LInvF base ldC N (M * N) acc mem a s := ht0 ▸ h
        have hle : M * N ≤ s.idx := by rw [hT.idxEq]; omega
        have hexit : (lrun base ldC N (epilogueProg (M * N)) 3 s).mem a = s.mem a := by
          simp [epilogueProg, lrun, lstep, hT.pc0, hle]
        simp only [Nat.mul_zero, Nat.zero_add]
        rw [hexit, hT.frame]
    | succ steps ih =>
        intro t0 s ht h
        have hlt : t0 < M * N := by omega
        have hiter := lstep_iter_frame base ldC N M (M * N) t0 hN hldC rfl acc mem a hfar s h hlt
        have hrun : lrun base ldC N (epilogueProg (M * N)) (5 * (steps + 1) + 3) s =
            lrun base ldC N (epilogueProg (M * N)) (5 * steps + 3)
              (lrun base ldC N (epilogueProg (M * N)) 5 s) := by
          rw [show 5 * (steps + 1) + 3 = 5 + (5 * steps + 3) by omega]
          exact lrun_add base ldC N (epilogueProg (M * N)) 5 (5 * steps + 3) s
        rw [hrun]
        exact ih (t0 + 1) _ (by omega) hiter
  have hinit : LInvF base ldC N 0 acc mem a (eHead mem acc) :=
    ⟨by intro k hk; omega, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact aux (M * N) 0 (eHead mem acc) (by omega) hinit

end IntelGpu
