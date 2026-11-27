-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaLoopCounter

@[expose] public section

/-!
# The SYCL-TLA scalar comparisons

The mainloop exit condition is set by PC 1400,
`cmp (lt)f3.1, null, r1.11, r1.15`, and consumed by the predicated jump at
PC 1401, `(W&~f3.1) jmpi`. This module decodes the 20 predicated `cmp`
forms of the dump into a `TlaCmp` structure, gives them a flag-writing
semantics, and proves the loop instance: `f3.1` is set to `1` exactly when
`r1.11 < r1.15`.

`(eq)`, `(ne)`, `(lt)` and `(gt)` are modelled on the 32-bit words, with
`lt`/`gt` unsigned. The loop counters are non-negative, so signed and unsigned agree on the
instance proved here.
-/

namespace IntelGpu

structure TlaCmp where
  exec : Exec
  pred : String
  flag : Nat
  flagSub : Nat
  srcL : TlaSrc
  srcR : TlaSrc
  deriving Repr, DecidableEq

/-- Parse `(lt)f3.1` into the predicate and the flag location. -/
def parseCmpFlag (s : String) : Option (String × Nat × Nat) :=
  match splitAtChar ')' s.toList with
  | some ('(' :: cs, rest) =>
      match numRuns (String.ofList rest) with
      | [n, sub] => some (String.ofList cs, n, sub)
      | _ => none
  | _ => none

/-- The predicated `cmp` form: `(W) cmp (C|M) (op)fN.M null A B`. -/
def parseTlaCmpInstr : TlaInstr → Option TlaCmp
  | .predicated "(W) cmp" (e :: dst :: _null :: a :: b :: _) =>
      match parseTlaExec e, parseCmpFlag dst, parseTlaSrc a, parseTlaSrc b with
      | some ex, some (p, n, sub), some l, some r => some ⟨ex, p, n, sub, l, r⟩
      | _, _, _, _ => none
  | _ => none

/-- The decoded comparisons. -/
def realTlaGemmCmp : List TlaCmp :=
  (decodeTlaProgram realTlaGemm).filterMap parseTlaCmpInstr

def TlaCmp.valL (st : TlaState) (c : TlaCmp) : Word :=
  readTlaSrcState st c.srcL 0

def TlaCmp.valR (st : TlaState) (c : TlaCmp) : Word :=
  readTlaSrcState st c.srcR 0

/-- The predicate value of a comparison. -/
def TlaCmp.holds (st : TlaState) (c : TlaCmp) : Bool :=
  match c.pred with
  | "eq" => decide (c.valL st = c.valR st)
  | "ne" => decide (c.valL st ≠ c.valR st)
  | "lt" => decide (c.valL st < c.valR st)
  | "gt" => decide (c.valR st < c.valL st)
  | _ => false

/-- Write the comparison result into the destination flag. -/
def TlaCmp.step (st : TlaState) (c : TlaCmp) : TlaState :=
  let v : Word := if c.holds st then 1 else 0
  { st with flags := writeBank st.flags c.flag c.flagSub v }

/-- The loop-exit comparison at PC 1400. -/
def loopCmp : TlaCmp where
  exec := ⟨16, 0, true⟩
  pred := "lt"
  flag := 3
  flagSub := 1
  srcL := .reg ⟨1, 0, 11, 0, 1, 0⟩
  srcR := .reg ⟨1, 0, 15, 0, 1, 0⟩

set_option maxRecDepth 100000 in
/-- There are 20 predicated comparisons in the dump. -/
theorem realTlaGemmCmp_length : realTlaGemmCmp.length = 20 := by decide

set_option maxRecDepth 100000 in
/-- Every comparison predicate is one of `eq`, `ne`, `lt`, `gt`. -/
theorem realTlaGemmCmp_preds :
    realTlaGemmCmp.all (fun c => c.pred ∈ ["eq", "ne", "lt", "gt"]) = true := by decide

set_option maxRecDepth 100000 in
/-- PC 1400 is the loop-exit comparison. -/
theorem blockCmp1400 :
    blockInstrAt 1400 =
      some (.predicated "(W) cmp"
        ["(16|M0)", "(lt)f3.1", "null<1>:d", "r1.11<0;1,0>:d", "r1.15<0;1,0>:d", "{I@2}"]) := by
  decide

set_option maxRecDepth 100000 in
/-- PC 1400 decodes to `loopCmp`. -/
theorem blockCmp1400_parsed :
    (blockInstrAt 1400).bind parseTlaCmpInstr = some loopCmp := by decide

set_option maxRecDepth 100000 in
/-- PC 1401 is the predicated exit jump. -/
theorem blockExitJmp :
    blockInstrAt 1401 =
      some (.predicated "(W&~f3.1) jmpi" ["_0_118"]) := by decide

theorem loopCmp_holds (st : TlaState) :
    loopCmp.holds st = decide (st.regs 1 11 < st.regs 1 15) := by
  simp [loopCmp, TlaCmp.holds, TlaCmp.valL, TlaCmp.valR, readTlaSrcState, srcIndex]

theorem loopCmp_step_flags (st : TlaState) :
    (loopCmp.step st).flags 3 1 =
      (if st.regs 1 11 < st.regs 1 15 then 1 else 0) := by
  simp [TlaCmp.step, loopCmp, TlaCmp.holds, TlaCmp.valL, TlaCmp.valR,
    readTlaSrcState, srcIndex, writeBank]

theorem loopCmp_step_flags_other (st : TlaState) (r j : Nat)
    (h : (r, j) ≠ (3, 1)) :
    (loopCmp.step st).flags r j = st.flags r j := by
  simp only [TlaCmp.step, loopCmp, writeBank]
  by_cases hr : r = 3
  · by_cases hj : j = 1
    · exact absurd (by simp [hr, hj]) h
    · simp [hr, hj]
  · simp [hr]

theorem loopCmp_step_regs (st : TlaState) :
    (loopCmp.step st).regs = st.regs := rfl

/-- The exit flag is clear exactly when the counter has reached the bound. -/
theorem loopCmp_exit_iff (st : TlaState) :
    (loopCmp.step st).flags 3 1 = 0 ↔ ¬ (st.regs 1 11 < st.regs 1 15) := by
  rw [loopCmp_step_flags]
  by_cases h : st.regs 1 11 < st.regs 1 15 <;> simp [h]

end IntelGpu
