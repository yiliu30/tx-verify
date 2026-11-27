-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaCmp

@[expose] public section

/-!
# The SYCL-TLA loop tail

One pass over the mainloop tail is

* PC 1397: `add r1.11, r1.11, 1:w`,
* PC 1400: `cmp (lt)f3.1, null, r1.11, r1.15`,
* PC 1401: exit when `~f3.1`,
* PC 1403: `add r1.14, r1.14, 1:w`, then the back-edge.

`tlaTailStep` composes the measured pieces. The two theorems below cover both
outcomes: while `r1.11 + 1 < r1.15` the tail increments both counters and
continues; once the incremented counter reaches the bound it increments only
`r1.11` and exits.
-/

namespace IntelGpu

/-- The outcome of one loop-tail pass. -/
inductive TlaTail where
  | continue
  | exit
  deriving Repr, DecidableEq

/-- One pass over the mainloop tail. -/
def tlaTailStep (st : TlaState) : Option (TlaState × TlaTail) :=
  match tlaAluStateStep? st counterAdd11 with
  | none => none
  | some s1 =>
      let s2 := loopCmp.step s1
      if s2.flags 3 1 = 0 then
        some (s2, .exit)
      else
        (tlaAluStateStep? s2 counterAdd14).map (fun s3 => (s3, .continue))

/-- A continuing pass increments both counters. -/
theorem tlaTail_continue (st : TlaState)
    (h : (st.regs 1 11 + 1) < st.regs 1 15) :
    ∃ st', tlaTailStep st = some (st', .continue) ∧
      st'.regs 1 11 = st.regs 1 11 + 1 ∧
      st'.regs 1 14 = st.regs 1 14 + 1 ∧
      st'.acc = st.acc ∧ st'.addr = st.addr ∧ st'.cr = st.cr := by
  obtain ⟨s1, h1, hv11, hf11, ha1, hd1, hc1, _⟩ := counterAdd11_value st
  have h15 : s1.regs 1 15 = st.regs 1 15 := hf11 1 15 (Or.inr (by decide))
  have hlt : s1.regs 1 11 < s1.regs 1 15 := by
    rw [hv11, h15]
    exact h
  have hflag : (loopCmp.step s1).flags 3 1 ≠ 0 := by
    rw [loopCmp_step_flags]
    simp [hlt]
  obtain ⟨s3, h3, hv14, hf14, ha2, hd2, hc2, _⟩ := counterAdd14_value (loopCmp.step s1)
  refine ⟨s3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [tlaTailStep, h1]
    rw [ite_eq_right hflag]
    simp [h3]
  · rw [hf14 1 11 (Or.inr (by decide)), loopCmp_step_regs]
    exact hv11
  · rw [hv14, loopCmp_step_regs, hf11 1 14 (Or.inr (by decide))]
  · exact ha2.trans ha1
  · exact hd2.trans hd1
  · exact hc2.trans hc1

/-- An exiting pass increments only `r1.11`. -/
theorem tlaTail_exit (st : TlaState)
    (h : ¬ (st.regs 1 11 + 1) < st.regs 1 15) :
    ∃ st', tlaTailStep st = some (st', .exit) ∧
      st'.regs 1 11 = st.regs 1 11 + 1 ∧
      st'.regs 1 14 = st.regs 1 14 ∧
      st'.acc = st.acc ∧ st'.addr = st.addr ∧ st'.cr = st.cr := by
  obtain ⟨s1, h1, hv11, hf11, ha1, hd1, hc1, _⟩ := counterAdd11_value st
  have h15 : s1.regs 1 15 = st.regs 1 15 := hf11 1 15 (Or.inr (by decide))
  have hlt : ¬ s1.regs 1 11 < s1.regs 1 15 := by
    rw [hv11, h15]
    exact h
  have hflag : (loopCmp.step s1).flags 3 1 = 0 := by
    rw [loopCmp_step_flags]
    simp [hlt]
  refine ⟨loopCmp.step s1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [tlaTailStep, h1]
    rw [ite_eq_left hflag]
  · rw [loopCmp_step_regs, hv11]
  · rw [loopCmp_step_regs, hf11 1 14 (Or.inr (by decide))]
  · exact ha1
  · exact hd1
  · exact hc1

end IntelGpu
