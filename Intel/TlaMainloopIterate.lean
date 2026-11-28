-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaMainloopDpas
public import Intel.TlaLoopIterate

@[expose] public section

/-!
# One iteration of the SYCL-TLA mainloop

A mainloop iteration runs the DPAS phase and then the loop tail. The DPAS
phase only writes the accumulator blocks `r13..r28`; the scalar counters and
the bound live in register 1, so the tail's exit test is unaffected. This
module proves that frame (`tlaDpasRun_frame`, `mainloopDpasRun_frame`) and
composes the two phases into `mainloopIteration` with both outcomes.
-/

namespace IntelGpu

/-- One DPAS step whose accumulators are the real `r21`/`r13` blocks does not
touch a register outside those blocks. -/
theorem tlaDpasStepOf_frame (d : TlaDpas) (rf : RegFile) (r j : Nat)
    (h0 : d.acc0 = 21) (h1 : d.acc1 = 13)
    (h13 : ¬ inTileC 13 r j) (h21 : ¬ inTileC 21 r j) :
    tlaDpasStepOf d rf r j = rf r j := by
  unfold tlaDpasStepOf tlaDpasStep
  rw [h0, h1]
  rw [writeTileC_frame _ _ _ _ _ h13, writeTileC_frame _ _ _ _ _ h21]

/-- A DPAS run with the real accumulator blocks frames every register outside
`r13..r28`. -/
theorem tlaDpasRun_frame (steps : List TlaDpas) (rf : RegFile) (r j : Nat)
    (hacc : ∀ d, d ∈ steps → d.acc0 = 21 ∧ d.acc1 = 13)
    (h13 : ¬ inTileC 13 r j) (h21 : ¬ inTileC 21 r j) :
    tlaDpasRun steps rf r j = rf r j := by
  induction steps generalizing rf with
  | nil => rfl
  | cons d ds ih =>
      have hd := hacc d (by simp)
      have hstep : tlaDpasStepOf d rf r j = rf r j :=
        tlaDpasStepOf_frame d rf r j hd.1 hd.2 h13 h21
      show tlaDpasRun ds (tlaDpasStepOf d rf) r j = rf r j
      rw [ih (tlaDpasStepOf d rf) (fun e he => hacc e (by simp [he]))]
      exact hstep

/-- The decoded 32-step DPAS run frames every register outside `r13..r28`. -/
theorem realTlaGemmDpasRun_frame (rf : RegFile) (r j : Nat)
    (hr : r < 13 ∨ 28 < r) :
    tlaDpasRun realTlaGemmDpas rf r j = rf r j := by
  apply tlaDpasRun_frame
  · intro d hd
    simpa [Bool.and_eq_true] using (List.all_eq_true.mp realTlaGemmDpas_accs) d hd
  · intro h
    simp [inTileC] at h
    rcases hr with hr | hr <;> omega
  · intro h
    simp [inTileC] at h
    rcases hr with hr | hr <;> omega

/-- The mainloop DPAS phase frames every register outside `r13..r28`. -/
theorem mainloopDpasRun_frame (rf : RegFile) (r j : Nat)
    (hr : r < 13 ∨ 28 < r) :
    mainloopDpasRun rf r j = rf r j := by
  simp only [mainloopDpasRun]
  rw [blockDpasSeq_eq, tlaDpasRunSeq_eq]
  exact realTlaGemmDpasRun_frame rf r j hr

/-- One mainloop iteration: the DPAS phase followed by the loop tail. -/
def mainloopIteration (st : TlaState) : Option (TlaState × TlaTail) :=
  tlaTailStep { st with regs := mainloopDpasRun st.regs }

set_option maxRecDepth 100000 in
/-- A continuing iteration advances both scalar counters. -/
theorem mainloopIteration_continue (st : TlaState)
    (h : (st.regs 1 11 + 1) < st.regs 1 15) :
    ∃ st', mainloopIteration st = some (st', .continue) ∧
      st'.regs 1 11 = st.regs 1 11 + 1 ∧
      st'.regs 1 14 = st.regs 1 14 + 1 := by
  have h11 : mainloopDpasRun st.regs 1 11 = st.regs 1 11 :=
    mainloopDpasRun_frame st.regs 1 11 (Or.inl (by decide))
  have h14 : mainloopDpasRun st.regs 1 14 = st.regs 1 14 :=
    mainloopDpasRun_frame st.regs 1 14 (Or.inl (by decide))
  have h15 : mainloopDpasRun st.regs 1 15 = st.regs 1 15 :=
    mainloopDpasRun_frame st.regs 1 15 (Or.inl (by decide))
  have h' : (mainloopDpasRun st.regs 1 11 + 1) < mainloopDpasRun st.regs 1 15 := by
    rw [h11, h15]
    exact h
  let stD : TlaState := { st with regs := mainloopDpasRun st.regs }
  obtain ⟨st', hstep, hc, hd, _, _, _⟩ := tlaTail_continue stD h'
  refine ⟨st', hstep, ?_, ?_⟩
  · rw [hc]
    rw [show stD.regs 1 11 = mainloopDpasRun st.regs 1 11 from rfl, h11]
  · rw [hd]
    rw [show stD.regs 1 14 = mainloopDpasRun st.regs 1 14 from rfl, h14]

set_option maxRecDepth 100000 in
/-- An exiting iteration advances only the primary counter. -/
theorem mainloopIteration_exit (st : TlaState)
    (h : ¬ (st.regs 1 11 + 1) < st.regs 1 15) :
    ∃ st', mainloopIteration st = some (st', .exit) ∧
      st'.regs 1 11 = st.regs 1 11 + 1 ∧
      st'.regs 1 14 = st.regs 1 14 := by
  have h11 : mainloopDpasRun st.regs 1 11 = st.regs 1 11 :=
    mainloopDpasRun_frame st.regs 1 11 (Or.inl (by decide))
  have h14 : mainloopDpasRun st.regs 1 14 = st.regs 1 14 :=
    mainloopDpasRun_frame st.regs 1 14 (Or.inl (by decide))
  have h15 : mainloopDpasRun st.regs 1 15 = st.regs 1 15 :=
    mainloopDpasRun_frame st.regs 1 15 (Or.inl (by decide))
  have h' : ¬ (mainloopDpasRun st.regs 1 11 + 1) < mainloopDpasRun st.regs 1 15 := by
    rw [h11, h15]
    exact h
  let stD : TlaState := { st with regs := mainloopDpasRun st.regs }
  obtain ⟨st', hstep, hc, hd, _, _, _⟩ := tlaTail_exit stD h'
  refine ⟨st', hstep, ?_, ?_⟩
  · rw [hc]
    rw [show stD.regs 1 11 = mainloopDpasRun st.regs 1 11 from rfl, h11]
  · rw [hd]
    rw [show stD.regs 1 14 = mainloopDpasRun st.regs 1 14 from rfl, h14]

end IntelGpu
