-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaSchedule
public import Intel.TlaAluState

@[expose] public section

/-!
# Loop-carried counters of the SYCL-TLA mainloop

The mainloop tail increments two registers: PC 1397 does
`add r1.11, r1.11, 1:w` and PC 1403 does `add r1.14, r1.14, 1:w`. Both are
decoded by `parseTlaAluInstr`. This module proves their values and the
composition of the two increments, which is the loop-carried counter update
for one iteration.
-/

namespace IntelGpu

/-- The instruction at a program counter inside the mainloop block. -/
def blockInstrAt (pc : Nat) : Option TlaInstr :=
  (blockInstrs.find? (fun p => p.1 = pc)).map (fun p => p.2)

/-- `add r1.11, r1.11, 1:w`. -/
def counterAdd11 : TlaAlu :=
  ⟨.add, ⟨1, 0, true⟩, .r ⟨1, 0, 11, 1, 1, 1⟩,
    .reg ⟨1, 0, 11, 0, 1, 0⟩, .imm (1 : Int) .w16, none⟩

/-- `add r1.14, r1.14, 1:w`. -/
def counterAdd14 : TlaAlu :=
  ⟨.add, ⟨1, 0, true⟩, .r ⟨1, 0, 14, 1, 1, 1⟩,
    .reg ⟨1, 0, 14, 0, 1, 0⟩, .imm (1 : Int) .w16, none⟩

set_option maxRecDepth 100000 in
/-- PC 1397 is the first counter increment. -/
theorem blockAdd11_instr :
    blockInstrAt 1397 =
      some (.predicated "(W) add" ["(1|M0)", "r1.11<1>:d", "r1.11<0;1,0>:d", "1:w"]) := by
  decide

set_option maxRecDepth 100000 in
/-- PC 1397 decodes to `counterAdd11`. -/
theorem blockAdd11_parsed :
    (blockInstrAt 1397).bind parseTlaAluInstr = some counterAdd11 := by decide

set_option maxRecDepth 100000 in
/-- PC 1403 is the second counter increment. -/
theorem blockAdd14_instr :
    blockInstrAt 1403 =
      some (.predicated "(W) add" ["(1|M0)", "r1.14<1>:d", "r1.14<0;1,0>:d", "1:w"]) := by
  decide

set_option maxRecDepth 100000 in
/-- PC 1403 decodes to `counterAdd14`. -/
theorem blockAdd14_parsed :
    (blockInstrAt 1403).bind parseTlaAluInstr = some counterAdd14 := by decide

theorem counterAdd11_value (st : TlaState) :
    ∃ st', tlaAluStateStep? st counterAdd11 = some st' ∧
      st'.regs 1 11 = st.regs 1 11 + 1 ∧
      (∀ r j, r ≠ 1 ∨ j ≠ 11 → st'.regs r j = st.regs r j) ∧
      st'.acc = st.acc ∧ st'.addr = st.addr ∧ st'.cr = st.cr ∧
      st'.flags = st.flags := by
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp [counterAdd11, tlaAluStateStep?, tlaAluFun, readTlaSrcState, srcIndex,
      writeTlaMasked, Exec.laneActive, Grf.dstIndex]
  · intro r j h
    rcases h with hr | hj
    · simp [counterAdd11, tlaAluStateStep?, tlaAluFun, readTlaSrcState, srcIndex,
        writeTlaMasked, Exec.laneActive, Grf.dstIndex, hr]
    · by_cases hr : r = 1
      · subst hr
        by_cases hge : 11 ≤ j
        · have hk : ¬ (j - 11 < 1) := by omega
          simp [counterAdd11, tlaAluStateStep?, tlaAluFun, readTlaSrcState, srcIndex,
            writeTlaMasked, Exec.laneActive, Grf.dstIndex, hge, hk]
        · simp [counterAdd11, tlaAluStateStep?, tlaAluFun, readTlaSrcState, srcIndex,
            writeTlaMasked, Exec.laneActive, Grf.dstIndex, hge]
      · simp [counterAdd11, tlaAluStateStep?, tlaAluFun, readTlaSrcState, srcIndex,
          writeTlaMasked, Exec.laneActive, Grf.dstIndex, hr]

theorem counterAdd14_value (st : TlaState) :
    ∃ st', tlaAluStateStep? st counterAdd14 = some st' ∧
      st'.regs 1 14 = st.regs 1 14 + 1 ∧
      (∀ r j, r ≠ 1 ∨ j ≠ 14 → st'.regs r j = st.regs r j) ∧
      st'.acc = st.acc ∧ st'.addr = st.addr ∧ st'.cr = st.cr ∧
      st'.flags = st.flags := by
  refine ⟨_, rfl, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp [counterAdd14, tlaAluStateStep?, tlaAluFun, readTlaSrcState, srcIndex,
      writeTlaMasked, Exec.laneActive, Grf.dstIndex]
  · intro r j h
    rcases h with hr | hj
    · simp [counterAdd14, tlaAluStateStep?, tlaAluFun, readTlaSrcState, srcIndex,
        writeTlaMasked, Exec.laneActive, Grf.dstIndex, hr]
    · by_cases hr : r = 1
      · subst hr
        by_cases hge : 14 ≤ j
        · have hk : ¬ (j - 14 < 1) := by omega
          simp [counterAdd14, tlaAluStateStep?, tlaAluFun, readTlaSrcState, srcIndex,
            writeTlaMasked, Exec.laneActive, Grf.dstIndex, hge, hk]
        · simp [counterAdd14, tlaAluStateStep?, tlaAluFun, readTlaSrcState, srcIndex,
            writeTlaMasked, Exec.laneActive, Grf.dstIndex, hge]
      · simp [counterAdd14, tlaAluStateStep?, tlaAluFun, readTlaSrcState, srcIndex,
          writeTlaMasked, Exec.laneActive, Grf.dstIndex, hr]

/-- The loop tail: increment `r1.11`, then `r1.14`. -/
def tlaLoopCounterStep (st : TlaState) : Option TlaState :=
  (tlaAluStateStep? st counterAdd11).bind (fun s => tlaAluStateStep? s counterAdd14)

/-- One loop-tail execution increments both counters and leaves every other
register and bank unchanged. -/
theorem tlaLoopCounterStep_value (st : TlaState) :
    ∃ st', tlaLoopCounterStep st = some st' ∧
      st'.regs 1 11 = st.regs 1 11 + 1 ∧
      st'.regs 1 14 = st.regs 1 14 + 1 ∧
      (∀ r j, (r, j) ≠ (1, 11) → (r, j) ≠ (1, 14) → st'.regs r j = st.regs r j) ∧
      st'.acc = st.acc ∧ st'.addr = st.addr ∧ st'.cr = st.cr ∧
      st'.flags = st.flags := by
  obtain ⟨s1, h1, hv11, hf11, ha1, hd1, hc1, hfl1⟩ := counterAdd11_value st
  obtain ⟨s2, h2, hv14, hf14, ha2, hd2, hc2, hfl2⟩ := counterAdd14_value s1
  refine ⟨s2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [tlaLoopCounterStep, h1, h2]
  · rw [hf14 1 11 (Or.inr (by decide))]
    exact hv11
  · rw [hv14, hf11 1 14 (Or.inr (by decide))]
  · intro r j h11 h14
    have e11 : r ≠ 1 ∨ j ≠ 11 := by
      by_cases hr : r = 1
      · right
        intro hj
        exact h11 (by simp [hr, hj])
      · left
        exact hr
    have e14 : r ≠ 1 ∨ j ≠ 14 := by
      by_cases hr : r = 1
      · right
        intro hj
        exact h14 (by simp [hr, hj])
      · left
        exact hr
    rw [hf14 r j e14, hf11 r j e11]
  · rw [ha2, ha1]
  · rw [hd2, hd1]
  · rw [hc2, hc1]
  · rw [hfl2, hfl1]

end IntelGpu
