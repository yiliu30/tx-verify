-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaCmpCond

@[expose] public section

/-!
# Gating the conditional comparison flag write

`TlaCmp.step` now consults `TlaCmp.condFlag`: a conditional comparison leaves
the state unchanged when its guard flag is clear, and writes the result only
when the guard is set. The loop comparison `loopCmp` is unconditional, so its
theorems are unchanged. The PC-1408 instance is worked out: its guard is
`f0.0` and its result is `r1.11 == 0`.
-/

namespace IntelGpu

/-- The conditional comparison at PC 1408. -/
def cmp1408 : TlaCmp :=
  ⟨"(W&f0.0) cmp", ⟨16, 0, true⟩, "eq", 0, 0,
    .reg ⟨1, 0, 11, 0, 1, 0⟩, .imm (0 : Int) .w16⟩

theorem cmp1408_condFlag : cmp1408.condFlag = some (0, 0) := by decide

/-- With `f0.0` clear, PC 1408 leaves the state unchanged. -/
theorem cmp1408_clear (st : TlaState) (h : st.flags 0 0 = 0) :
    cmp1408.step st = st :=
  TlaCmp.step_cond_clear st cmp1408 0 0 cmp1408_condFlag h

/-- With `f0.0` set, PC 1408 writes `r1.11 == 0` into `f0.0`. -/
theorem cmp1408_set (st : TlaState) (h : st.flags 0 0 ≠ 0) :
    (cmp1408.step st).flags 0 0 =
      (if st.regs 1 11 = 0 then 1 else 0) := by
  unfold TlaCmp.step TlaCmp.writeFlag
  rw [cmp1408_condFlag]
  simp only
  rw [ite_eq_right h]
  simp [cmp1408, TlaCmp.holds, TlaCmp.valL, TlaCmp.valR, readTlaSrcState,
    srcIndex, writeBank]

set_option maxRecDepth 1000000 in
/-- Every conditional comparison has a guard flag. -/
theorem realTlaGemmCmp_conditional_flags :
    (realTlaGemmCmp.filter (fun c => c.cond ≠ "(W) cmp")).all
      (fun c => c.condFlag.isSome) = true := by
  decide

/-- The loop comparison stays unconditional. -/
theorem loopCmp_unconditional : loopCmp.condFlag = none := loopCmp_condFlag

end IntelGpu
