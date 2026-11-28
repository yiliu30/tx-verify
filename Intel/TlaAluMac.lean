-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaAluState
public import Intel.TlaPlain

@[expose] public section

/-!
# The 64-bit multiply high/low forms

`mach` and `macl` are the high and low 32 bits of the unsigned 64-bit product
of the two sources. With these two operations modelled, every ALU opcode of
the dump executes.

The signed-vs-unsigned interpretation is a documented modelling choice: the
14 forms occur in address computations where the signed and unsigned products
agree on the observed values.
-/

namespace IntelGpu

/-- The ALU executor is total now that all opcodes are modelled. -/
theorem tlaAluStateStep?_isSome (st : TlaState) (a : TlaAlu) :
    (tlaAluStateStep? st a).isSome = true := by
  cases a with
  | mk op exec dst src1 src2 src3 =>
      cases op <;> cases dst <;> simp [tlaAluStateStep?, tlaAluFun]

/-- `mach r8.0, r1.13, r1.10` from the prologue. -/
def machForm : TlaAlu :=
  ⟨.mach, ⟨1, 0, true⟩, .r ⟨8, 0, 0, 1, 1, 1⟩,
    .reg ⟨1, 0, 13, 0, 1, 0⟩, .reg ⟨1, 0, 10, 0, 1, 0⟩, none⟩

/-- `macl r7.0, r1.13, r1.10` from the prologue. -/
def maclForm : TlaAlu :=
  ⟨.macl, ⟨1, 0, true⟩, .r ⟨7, 0, 0, 1, 1, 1⟩,
    .reg ⟨1, 0, 13, 0, 1, 0⟩, .reg ⟨1, 0, 10, 0, 1, 0⟩, none⟩

/-- `mach` writes the high 32 bits of the product. -/
theorem mach_value (st : TlaState) :
    ∃ st', tlaAluStateStep? st machForm = some st' ∧
      st'.regs 8 0 =
        BitVec.ofNat 32 ((st.regs 1 13).toNat * (st.regs 1 10).toNat >>> 32) := by
  refine ⟨_, rfl, ?_⟩
  simp [machForm, tlaAluStateStep?, tlaAluFun, readTlaSrcState, srcIndex,
    writeTlaMasked, Exec.laneActive, Grf.dstIndex]

/-- `macl` writes the low 32 bits of the product. -/
theorem macl_value (st : TlaState) :
    ∃ st', tlaAluStateStep? st maclForm = some st' ∧
      st'.regs 7 0 =
        BitVec.ofNat 32 ((st.regs 1 13).toNat * (st.regs 1 10).toNat) := by
  refine ⟨_, rfl, ?_⟩
  simp [maclForm, tlaAluStateStep?, tlaAluFun, readTlaSrcState, srcIndex,
    writeTlaMasked, Exec.laneActive, Grf.dstIndex]

/-- A canonical all-zero state. -/
def zeroState : TlaState :=
  ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- Every decoded ALU form executes, predicated and plain. -/
theorem realTlaGemmAlu_all_executable :
    (realTlaGemmAlu ++ realTlaGemmAluPlain).all
      (fun a => (tlaAluStateStep? zeroState a).isSome) = true := by
  decide

end IntelGpu
