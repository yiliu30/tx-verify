-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaMainloopFull
public import Intel.TlaLoopStructure

@[expose] public section

/-!
# Iterating the full mainloop

`mainloopLoopFull` runs `mainloopIterationFull` until the first exit, carrying
the tile memory along. Because every full iteration preserves the bound
register `r1.15`, the counter trajectory is exactly the one already proved for
the DPAS+tail loop: `n` continuing iterations advance both counters by `n`,
and `n` continues followed by a failing test exit with `r1.11` advanced by
`n+1` and `r1.14` by `n`.
-/

namespace IntelGpu

set_option maxRecDepth 10000000 in
/-- One full iteration preserves the bound register `r1.15`. -/
theorem mainloopIterationFull_preserves_15 (st : TlaState) (m : TlaMem)
    (bti : Nat → Word) (st1 : TlaState) (m1 : TlaMem)
    (st' : TlaState) (m' : TlaMem) (t : TlaTail)
    (hload : blockLoadPhase st m bti = some (st1, m1))
    (h : mainloopIterationFull st m bti = some (st', m', t)) :
    st'.regs 1 15 = st.regs 1 15 := by
  unfold mainloopIterationFull at h
  rw [hload] at h
  simp only at h
  cases hstep : mainloopIteration st1 with
  | none => simp [hstep] at h
  | some pair =>
      obtain ⟨st2, t2⟩ := pair
      simp [hstep] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have h1 := mainloopIteration_preserves_15 st1 st2 t2 hstep
      have hc := blockLoadPhase_preserves_counters st m bti st1 m1 hload
      rw [h1, hc.2.2]

/-- Run the full iteration until the first exit. -/
def mainloopLoopFull (bti : Nat → Word) : Nat → TlaState → TlaMem →
    Option (TlaState × TlaMem)
  | 0, st, m => some (st, m)
  | n + 1, st, m =>
      match mainloopIterationFull st m bti with
      | some (st', m', .continue) => mainloopLoopFull bti n st' m'
      | some (st', m', .exit) => some (st', m')
      | none => none

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 2000000 in
theorem mainloopLoopFull_cons_continue (bti : Nat → Word) (n : Nat)
    (st st' : TlaState) (m m' : TlaMem)
    (h : mainloopIterationFull st m bti = some (st', m', .continue)) :
    mainloopLoopFull bti (n + 1) st m = mainloopLoopFull bti n st' m' := by
  change (match mainloopIterationFull st m bti with
    | some (st', m', .continue) => mainloopLoopFull bti n st' m'
    | some (st', m', .exit) => some (st', m')
    | none => none) = mainloopLoopFull bti n st' m'
  rw [h]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 2000000 in
theorem mainloopLoopFull_cons_exit (bti : Nat → Word) (n : Nat)
    (st st' : TlaState) (m m' : TlaMem)
    (h : mainloopIterationFull st m bti = some (st', m', .exit)) :
    mainloopLoopFull bti (n + 1) st m = some (st', m') := by
  change (match mainloopIterationFull st m bti with
    | some (st', m', .continue) => mainloopLoopFull bti n st' m'
    | some (st', m', .exit) => some (st', m')
    | none => none) = some (st', m')
  rw [h]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 2000000 in
/-- `n` continuing full iterations advance both counters by `n`. -/
theorem mainloopLoopFull_continue (bti : Nat → Word) :
    ∀ (n : Nat) (st : TlaState) (m : TlaMem),
    (∀ k < n, wordAddN (st.regs 1 11) (k + 1) < st.regs 1 15) →
    ∃ st' m', mainloopLoopFull bti n st m = some (st', m') ∧
      st'.regs 1 11 = wordAddN (st.regs 1 11) n ∧
      st'.regs 1 14 = wordAddN (st.regs 1 14) n ∧
      st'.regs 1 15 = st.regs 1 15 := by
  intro n
  induction n with
  | zero => intro st m _; exact ⟨st, m, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
      intro st m h
      have h0 : st.regs 1 11 + 1 < st.regs 1 15 := h 0 (Nat.zero_lt_succ n)
      obtain ⟨st1, m1, hload⟩ : ∃ st1 m1, blockLoadPhase st m bti = some (st1, m1) := by
        have hs := blockLoadPhase_isSome st m bti
        cases hl : blockLoadPhase st m bti with
        | none => simp [hl] at hs
        | some pair => exact ⟨pair.1, pair.2, rfl⟩
      obtain ⟨st', m', t, hstep, ht, h11, h14⟩ :=
        mainloopIterationFull_continue_initial st m bti st1 m1 hload h0
      have h15 := mainloopIterationFull_preserves_15 st m bti st1 m1 st' m' t hload hstep
      have hIH : ∀ k < n, wordAddN (st'.regs 1 11) (k + 1) < st'.regs 1 15 := by
        intro k hk
        have hh := h (k + 1) (Nat.succ_lt_succ hk)
        have he : wordAddN (st'.regs 1 11) (k + 1) =
            wordAddN (st.regs 1 11) ((k + 1) + 1) := by
          rw [h11]
          exact (wordAddN_add_one (st.regs 1 11) (k + 1)).symm
        rw [he, h15]
        exact hh
      obtain ⟨st'', m'', hloop, hc, hd, h15'⟩ := ih st' m' hIH
      have hstep' : mainloopIterationFull st m bti = some (st', m', .continue) := by
        rw [← ht]
        exact hstep
      refine ⟨st'', m'', ?_, ?_, ?_, ?_⟩
      · rw [mainloopLoopFull_cons_continue bti n st st' m m' hstep']
        exact hloop
      · rw [hc, h11]
        exact (wordAddN_add_one (st.regs 1 11) n).symm
      · rw [hd, h14]
        exact (wordAddN_add_one (st.regs 1 14) n).symm
      · rw [h15', h15]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 2000000 in
/-- `n` continuing full iterations followed by one exiting iteration. -/
theorem mainloopLoopFull_exit (bti : Nat → Word) :
    ∀ (n : Nat) (st : TlaState) (m : TlaMem),
    (∀ k < n, wordAddN (st.regs 1 11) (k + 1) < st.regs 1 15) →
    ¬ wordAddN (st.regs 1 11) (n + 1) < st.regs 1 15 →
    ∃ st' m', mainloopLoopFull bti (n + 1) st m = some (st', m') ∧
      st'.regs 1 11 = wordAddN (st.regs 1 11) (n + 1) ∧
      st'.regs 1 14 = wordAddN (st.regs 1 14) n := by
  intro n
  induction n with
  | zero =>
      intro st m _ hbad
      obtain ⟨st1, m1, hload⟩ : ∃ st1 m1, blockLoadPhase st m bti = some (st1, m1) := by
        have hs := blockLoadPhase_isSome st m bti
        cases hl : blockLoadPhase st m bti with
        | none => simp [hl] at hs
        | some pair => exact ⟨pair.1, pair.2, rfl⟩
      obtain ⟨st', m', t, hstep, ht, h11, h14⟩ :=
        mainloopIterationFull_exit_initial st m bti st1 m1 hload hbad
      have hstep' : mainloopIterationFull st m bti = some (st', m', .exit) := by
        rw [← ht]
        exact hstep
      refine ⟨st', m', ?_, h11, h14⟩
      rw [mainloopLoopFull_cons_exit bti 0 st st' m m' hstep']
  | succ n ih =>
      intro st m h hbad
      have h0 : st.regs 1 11 + 1 < st.regs 1 15 := h 0 (Nat.zero_lt_succ n)
      obtain ⟨st1, m1, hload⟩ : ∃ st1 m1, blockLoadPhase st m bti = some (st1, m1) := by
        have hs := blockLoadPhase_isSome st m bti
        cases hl : blockLoadPhase st m bti with
        | none => simp [hl] at hs
        | some pair => exact ⟨pair.1, pair.2, rfl⟩
      obtain ⟨st', m', t, hstep, ht, h11, h14⟩ :=
        mainloopIterationFull_continue_initial st m bti st1 m1 hload h0
      have h15 := mainloopIterationFull_preserves_15 st m bti st1 m1 st' m' t hload hstep
      have hIH : ∀ k < n, wordAddN (st'.regs 1 11) (k + 1) < st'.regs 1 15 := by
        intro k hk
        have hh := h (k + 1) (Nat.succ_lt_succ hk)
        have he : wordAddN (st'.regs 1 11) (k + 1) =
            wordAddN (st.regs 1 11) ((k + 1) + 1) := by
          rw [h11]
          exact (wordAddN_add_one (st.regs 1 11) (k + 1)).symm
        rw [he, h15]
        exact hh
      have hbad' : ¬ wordAddN (st'.regs 1 11) (n + 1) < st'.regs 1 15 := by
        rw [h11, h15]
        exact (wordAddN_add_one (st.regs 1 11) (n + 1)).symm ▸ hbad
      obtain ⟨st'', m'', hloop, hc, hd⟩ := ih st' m' hIH hbad'
      have hstep' : mainloopIterationFull st m bti = some (st', m', .continue) := by
        rw [← ht]
        exact hstep
      refine ⟨st'', m'', ?_, ?_, ?_⟩
      · rw [mainloopLoopFull_cons_continue bti (n + 1) st st' m m' hstep']
        exact hloop
      · rw [hc, h11]
        exact (wordAddN_add_one (st.regs 1 11) (n + 1)).symm
      · rw [hd, h14]
        exact (wordAddN_add_one (st.regs 1 14) n).symm

end IntelGpu
