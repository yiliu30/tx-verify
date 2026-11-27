-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaLoopTail

@[expose] public section

/-!
# Iterating the SYCL-TLA loop tail

`tlaTailLoop n` runs the tail for `n` steps, stopping early on `exit`.
The counters are described by `wordAddN w n`, the `n`-fold successor of a
32-bit word. The two main theorems say

* if the first `n` exit tests succeed, the loop performs `n` continuing
  passes and both counters advance by `n`;
* if the first `n` tests succeed and the next one fails, the loop performs `n`
  continuing passes followed by an exiting pass.

`wordAddN` avoids any cast arithmetic in the statements; later stages can
connect it to `w + BitVec.ofNat 32 n` under a no-overflow hypothesis.
-/

namespace IntelGpu

/-- The `n`-fold successor of a word. -/
def wordAddN (w : Word) : Nat → Word
  | 0 => w
  | n + 1 => wordAddN w n + 1

theorem wordAddN_zero (w : Word) : wordAddN w 0 = w := rfl

theorem wordAddN_succ (w : Word) (n : Nat) :
    wordAddN w (n + 1) = wordAddN w n + 1 := rfl

theorem wordAddN_succ_word (w : Word) (n : Nat) :
    wordAddN (w + 1) n = wordAddN w n + 1 := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
      simp only [wordAddN]
      rw [ih]

theorem wordAddN_add (w : Word) (m n : Nat) :
    wordAddN w (m + n) = wordAddN (wordAddN w m) n := by
  induction m generalizing w with
  | zero => simp [wordAddN]
  | succ m ih =>
      rw [Nat.succ_add]
      simp only [wordAddN]
      rw [ih]
      exact (wordAddN_succ_word (wordAddN w m) n).symm

theorem wordAddN_add_one (w : Word) (n : Nat) :
    wordAddN w (n + 1) = wordAddN (w + 1) n := by
  rw [show n + 1 = 1 + n from by omega, wordAddN_add]
  simp [wordAddN]

/-- The tail never changes the bound register `r1.15`. -/
theorem tlaTail_preserves_15 (st st' : TlaState) (t : TlaTail)
    (h : tlaTailStep st = some (st', t)) : st'.regs 1 15 = st.regs 1 15 := by
  unfold tlaTailStep at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i s1 hs1
    obtain ⟨s1', hs1', _, hf11, _, _, _, _⟩ := counterAdd11_value st
    rw [hs1'] at hs1
    cases hs1
    split at h
    · cases h
      rw [loopCmp_step_regs]
      exact hf11 1 15 (Or.inr (by decide))
    · obtain ⟨s3', hs3', _, hf14, _, _, _, _⟩ := counterAdd14_value (loopCmp.step s1)
      rw [hs3'] at h
      cases h
      rw [hf14 1 15 (Or.inr (by decide)), loopCmp_step_regs]
      exact hf11 1 15 (Or.inr (by decide))

/-- Run the tail for `n` steps, stopping at the first exit. -/
def tlaTailLoop : Nat → TlaState → Option TlaState
  | 0, st => some st
  | n + 1, st =>
      match tlaTailStep st with
      | some (st', .continue) => tlaTailLoop n st'
      | some (st', .exit) => some st'
      | none => none

/-- `n` continuing passes advance both counters by `n`. -/
theorem tlaTailLoop_continue : ∀ (n : Nat) (st : TlaState),
    (∀ k < n, wordAddN (st.regs 1 11) (k + 1) < st.regs 1 15) →
    ∃ st', tlaTailLoop n st = some st' ∧
      st'.regs 1 11 = wordAddN (st.regs 1 11) n ∧
      st'.regs 1 14 = wordAddN (st.regs 1 14) n ∧
      st'.regs 1 15 = st.regs 1 15 := by
  intro n
  induction n with
  | zero => intro st _; exact ⟨st, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
      intro st h
      have h0 : st.regs 1 11 + 1 < st.regs 1 15 := h 0 (Nat.zero_lt_succ n)
      obtain ⟨st1, hstep, hc1, hd1, _, _, _⟩ := tlaTail_continue st h0
      have h15 := tlaTail_preserves_15 st st1 .continue hstep
      have hIH : ∀ k < n, wordAddN (st1.regs 1 11) (k + 1) < st1.regs 1 15 := by
        intro k hk
        have hh := h (k + 1) (Nat.succ_lt_succ hk)
        have he : wordAddN (st1.regs 1 11) (k + 1) =
            wordAddN (st.regs 1 11) ((k + 1) + 1) := by
          rw [hc1]
          exact (wordAddN_add_one (st.regs 1 11) (k + 1)).symm
        rw [he, h15]
        exact hh
      obtain ⟨st', hloop, hc, hd, h15'⟩ := ih st1 hIH
      refine ⟨st', ?_, ?_, ?_, ?_⟩
      · simp [tlaTailLoop, hstep, hloop]
      · rw [hc, hc1]
        exact (wordAddN_add_one (st.regs 1 11) n).symm
      · rw [hd, hd1]
        exact (wordAddN_add_one (st.regs 1 14) n).symm
      · rw [h15', h15]

/-- `n` continuing passes followed by one exiting pass. -/
theorem tlaTailLoop_exit : ∀ (n : Nat) (st : TlaState),
    (∀ k < n, wordAddN (st.regs 1 11) (k + 1) < st.regs 1 15) →
    ¬ wordAddN (st.regs 1 11) (n + 1) < st.regs 1 15 →
    ∃ st', tlaTailLoop (n + 1) st = some st' ∧
      st'.regs 1 11 = wordAddN (st.regs 1 11) (n + 1) ∧
      st'.regs 1 14 = wordAddN (st.regs 1 14) n := by
  intro n
  induction n with
  | zero =>
      intro st _ hbad
      obtain ⟨st', hstep, hc, hd, _, _, _⟩ := tlaTail_exit st hbad
      refine ⟨st', ?_, ?_, ?_⟩
      · simp [tlaTailLoop, hstep]
      · exact hc
      · exact hd
  | succ n ih =>
      intro st h hbad
      have h0 : st.regs 1 11 + 1 < st.regs 1 15 := h 0 (Nat.zero_lt_succ n)
      obtain ⟨st1, hstep, hc1, hd1, _, _, _⟩ := tlaTail_continue st h0
      have h15 := tlaTail_preserves_15 st st1 .continue hstep
      have hIH : ∀ k < n, wordAddN (st1.regs 1 11) (k + 1) < st1.regs 1 15 := by
        intro k hk
        have hh := h (k + 1) (Nat.succ_lt_succ hk)
        have he : wordAddN (st1.regs 1 11) (k + 1) =
            wordAddN (st.regs 1 11) ((k + 1) + 1) := by
          rw [hc1]
          exact (wordAddN_add_one (st.regs 1 11) (k + 1)).symm
        rw [he, h15]
        exact hh
      have hbad' : ¬ wordAddN (st1.regs 1 11) (n + 1) < st1.regs 1 15 := by
        rw [hc1, h15]
        have he : wordAddN (st.regs 1 11 + 1) (n + 1) =
            wordAddN (st.regs 1 11) ((n + 1) + 1) :=
          (wordAddN_add_one (st.regs 1 11) (n + 1)).symm
        rw [he]
        exact hbad
      obtain ⟨st', hloop, hc, hd⟩ := ih st1 hIH hbad'
      refine ⟨st', ?_, ?_, ?_⟩
      · simp only [tlaTailLoop, hstep]
        exact hloop
      · rw [hc, hc1]
        exact (wordAddN_add_one (st.regs 1 11) (n + 1)).symm
      · rw [hd, hd1]
        exact (wordAddN_add_one (st.regs 1 14) n).symm

end IntelGpu
