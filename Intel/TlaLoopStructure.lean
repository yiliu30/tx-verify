-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaMainloopIterate

@[expose] public section

/-!
# Control flow and iteration of the SYCL-TLA mainloop

The mainloop is a single back-edge loop:

* the body starts at the label `_0_119` at PC 959,
* the exit jump at PC 1401 targets `_0_118` at PC 1405,
* the unconditional back-edge at PC 1404 is exactly `959 + 445`, one past the
  445-instruction block, and targets `_0_119`.

`mainloopLoop n` iterates `mainloopIteration`. The two theorems lift the
tail-iteration results to the full iteration: the DPAS phase frames the scalar
counters, so the same counter arithmetic applies.
-/

namespace IntelGpu

set_option maxRecDepth 100000 in
/-- The loop-exit target `_0_118` is at PC 1405. -/
theorem loopExit_target : tlaLabelPc tlaCode "_0_118" = some 1405 := by decide

set_option maxRecDepth 100000 in
/-- The back-edge is one past the 445-instruction block. -/
theorem backEdge_after_block : 959 + blockInstrs.length = 1404 := by decide

set_option maxRecDepth 100000 in
/-- The block starts at the `_0_119` label. -/
theorem block_head :
    blockInstrs.head? = some (959, .label "_0_119") := by decide

set_option maxRecDepth 100000 in
/-- The exit jump at PC 1401 targets `_0_118`. -/
theorem blockExitJmp_target :
    (blockInstrAt 1401).bind (fun i =>
      match parseTlaJmpInstr i with
      | some j => some j.target
      | none => none) = some "_0_118" := by
  decide

/-- Iterate the full mainloop iteration, stopping at the first exit. -/
def mainloopLoop : Nat → TlaState → Option TlaState
  | 0, st => some st
  | n + 1, st =>
      match mainloopIteration st with
      | some (st', .continue) => mainloopLoop n st'
      | some (st', .exit) => some st'
      | none => none

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem mainloopLoop_cons_continue (n : Nat) (st st' : TlaState)
    (h : tlaTailStep (dpasState st) = some (st', .continue)) :
    mainloopLoop (n + 1) st = mainloopLoop n st' := by
  change (match tlaTailStep (dpasState st) with
    | some (st', .continue) => mainloopLoop n st'
    | some (st', .exit) => some st'
    | none => none) = mainloopLoop n st'
  rw [h]

set_option maxRecDepth 100000 in
theorem mainloopLoop_cons_exit (n : Nat) (st st' : TlaState)
    (h : tlaTailStep (dpasState st) = some (st', .exit)) :
    mainloopLoop (n + 1) st = some st' := by
  change (match tlaTailStep (dpasState st) with
    | some (st', .continue) => mainloopLoop n st'
    | some (st', .exit) => some st'
    | none => none) = some st'
  rw [h]

set_option maxRecDepth 10000000 in
/-- One mainloop iteration never changes the bound register `r1.15`. -/
theorem mainloopIteration_preserves_15 (st st' : TlaState) (t : TlaTail)
    (h : mainloopIteration st = some (st', t)) : st'.regs 1 15 = st.regs 1 15 := by
  have h' := tlaTail_preserves_15 (dpasState st) st' t h
  rw [h']
  rw [dpasState]
  exact mainloopDpasRun_frame st.regs 1 15 (Or.inl (by decide))

set_option maxRecDepth 10000000 in
/-- `n` continuing mainloop iterations advance both counters by `n`. -/
theorem mainloopLoop_continue : ∀ (n : Nat) (st : TlaState),
    (∀ k < n, wordAddN (st.regs 1 11) (k + 1) < st.regs 1 15) →
    ∃ st', mainloopLoop n st = some st' ∧
      st'.regs 1 11 = wordAddN (st.regs 1 11) n ∧
      st'.regs 1 14 = wordAddN (st.regs 1 14) n ∧
      st'.regs 1 15 = st.regs 1 15 := by
  intro n
  induction n with
  | zero => intro st _; exact ⟨st, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
      intro st h
      have h0 : st.regs 1 11 + 1 < st.regs 1 15 := h 0 (Nat.zero_lt_succ n)
      obtain ⟨st1, hstep, hc1, hd1⟩ := mainloopIteration_continue st h0
      have h15 := mainloopIteration_preserves_15 st st1 .continue hstep
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
      · rw [mainloopLoop_cons_continue n st st1 hstep]
        exact hloop
      · rw [hc, hc1]
        exact (wordAddN_add_one (st.regs 1 11) n).symm
      · rw [hd, hd1]
        exact (wordAddN_add_one (st.regs 1 14) n).symm
      · rw [h15', h15]

set_option maxRecDepth 10000000 in
/-- `n` continuing iterations followed by one exiting iteration. -/
theorem mainloopLoop_exit : ∀ (n : Nat) (st : TlaState),
    (∀ k < n, wordAddN (st.regs 1 11) (k + 1) < st.regs 1 15) →
    ¬ wordAddN (st.regs 1 11) (n + 1) < st.regs 1 15 →
    ∃ st', mainloopLoop (n + 1) st = some st' ∧
      st'.regs 1 11 = wordAddN (st.regs 1 11) (n + 1) ∧
      st'.regs 1 14 = wordAddN (st.regs 1 14) n := by
  intro n
  induction n with
  | zero =>
      intro st _ hbad
      obtain ⟨st', hstep, hc, hd⟩ := mainloopIteration_exit st hbad
      refine ⟨st', ?_, ?_, ?_⟩
      · rw [mainloopLoop_cons_exit 0 st st' hstep]
      · exact hc
      · exact hd
  | succ n ih =>
      intro st h hbad
      have h0 : st.regs 1 11 + 1 < st.regs 1 15 := h 0 (Nat.zero_lt_succ n)
      obtain ⟨st1, hstep, hc1, hd1⟩ := mainloopIteration_continue st h0
      have h15 := mainloopIteration_preserves_15 st st1 .continue hstep
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
        exact (wordAddN_add_one (st.regs 1 11) (n + 1)).symm ▸ hbad
      obtain ⟨st', hloop, hc, hd⟩ := ih st1 hIH hbad'
      refine ⟨st', ?_, ?_, ?_⟩
      · rw [mainloopLoop_cons_continue (n + 1) st st1 hstep]
        exact hloop
      · rw [hc, hc1]
        exact (wordAddN_add_one (st.regs 1 11) (n + 1)).symm
      · rw [hd, hd1]
        exact (wordAddN_add_one (st.regs 1 14) n).symm

end IntelGpu
