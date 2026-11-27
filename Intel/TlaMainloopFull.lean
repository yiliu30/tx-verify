-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaLoadPhase
public import Intel.TlaMainloopIterate
public import Intel.TlaLoopTail

@[expose] public section

/-!
# The full three-phase mainloop iteration

A mainloop iteration is: the block2d load/store phase, the DPAS phase and the
loop tail. `mainloopIterationFull` composes them over the tile memory. Because
the load phase leaves the scalar counters untouched, the tail's exit test and
the counter arithmetic are exactly the ones already proved for
`mainloopIteration`.
-/

namespace IntelGpu

/-- Loads/stores, then DPAS, then the loop tail. -/
def mainloopIterationFull (st : TlaState) (m : TlaMem) (bti : Nat → Word) :
    Option (TlaState × TlaMem × TlaTail) :=
  match blockLoadPhase st m bti with
  | none => none
  | some (st1, m1) =>
      match mainloopIteration st1 with
      | some (st2, t) => some (st2, m1, t)
      | none => none

set_option maxRecDepth 10000000 in
/-- A continuing full iteration increments both counters. -/
theorem mainloopIterationFull_continue (st : TlaState) (m : TlaMem)
    (bti : Nat → Word) (st1 : TlaState) (m1 : TlaMem)
    (hload : blockLoadPhase st m bti = some (st1, m1))
    (hcnt : (st1.regs 1 11 + 1) < st1.regs 1 15) :
    ∃ st' m' t, mainloopIterationFull st m bti = some (st', m', t) ∧
      t = .continue ∧
      st'.regs 1 11 = st1.regs 1 11 + 1 ∧
      st'.regs 1 14 = st1.regs 1 14 + 1 := by
  obtain ⟨st', hstep, hc, hd⟩ := mainloopIteration_continue st1 hcnt
  have hfull : mainloopIterationFull st m bti = some (st', m1, .continue) := by
    unfold mainloopIterationFull
    rw [hload]
    simp only
    rw [hstep]
  exact ⟨st', m1, .continue, hfull, rfl, hc, hd⟩

set_option maxRecDepth 10000000 in
/-- An exiting full iteration increments only the primary counter. -/
theorem mainloopIterationFull_exit (st : TlaState) (m : TlaMem)
    (bti : Nat → Word) (st1 : TlaState) (m1 : TlaMem)
    (hload : blockLoadPhase st m bti = some (st1, m1))
    (hcnt : ¬ (st1.regs 1 11 + 1) < st1.regs 1 15) :
    ∃ st' m' t, mainloopIterationFull st m bti = some (st', m', t) ∧
      t = .exit ∧
      st'.regs 1 11 = st1.regs 1 11 + 1 ∧
      st'.regs 1 14 = st1.regs 1 14 := by
  obtain ⟨st', hstep, hc, hd⟩ := mainloopIteration_exit st1 hcnt
  have hfull : mainloopIterationFull st m bti = some (st', m1, .exit) := by
    unfold mainloopIterationFull
    rw [hload]
    simp only
    rw [hstep]
  exact ⟨st', m1, .exit, hfull, rfl, hc, hd⟩

set_option maxRecDepth 10000000 in
/-- The continuation theorem with the test stated on the pre-load counters. -/
theorem mainloopIterationFull_continue_initial (st : TlaState) (m : TlaMem)
    (bti : Nat → Word) (st1 : TlaState) (m1 : TlaMem)
    (hload : blockLoadPhase st m bti = some (st1, m1))
    (hcnt : (st.regs 1 11 + 1) < st.regs 1 15) :
    ∃ st' m' t, mainloopIterationFull st m bti = some (st', m', t) ∧
      t = .continue ∧
      st'.regs 1 11 = st.regs 1 11 + 1 ∧
      st'.regs 1 14 = st.regs 1 14 + 1 := by
  have hc := blockLoadPhase_preserves_counters st m bti st1 m1 hload
  have hcnt' : (st1.regs 1 11 + 1) < st1.regs 1 15 := by
    rw [hc.1, hc.2.2]
    exact hcnt
  obtain ⟨st', m', t, hstep, ht, h11, h14⟩ :=
    mainloopIterationFull_continue st m bti st1 m1 hload hcnt'
  refine ⟨st', m', t, hstep, ht, ?_, ?_⟩
  · rw [h11, hc.1]
  · rw [h14, hc.2.1]

set_option maxRecDepth 10000000 in
/-- The exit theorem with the test stated on the pre-load counters. -/
theorem mainloopIterationFull_exit_initial (st : TlaState) (m : TlaMem)
    (bti : Nat → Word) (st1 : TlaState) (m1 : TlaMem)
    (hload : blockLoadPhase st m bti = some (st1, m1))
    (hcnt : ¬ (st.regs 1 11 + 1) < st.regs 1 15) :
    ∃ st' m' t, mainloopIterationFull st m bti = some (st', m', t) ∧
      t = .exit ∧
      st'.regs 1 11 = st.regs 1 11 + 1 ∧
      st'.regs 1 14 = st.regs 1 14 := by
  have hc := blockLoadPhase_preserves_counters st m bti st1 m1 hload
  have hcnt' : ¬ (st1.regs 1 11 + 1) < st1.regs 1 15 := by
    rw [hc.1, hc.2.2]
    exact hcnt
  obtain ⟨st', m', t, hstep, ht, h11, h14⟩ :=
    mainloopIterationFull_exit st m bti st1 m1 hload hcnt'
  refine ⟨st', m', t, hstep, ht, ?_, ?_⟩
  · rw [h11, hc.1]
  · rw [h14, hc.2.1]

end IntelGpu
